
import heapq, traceback, array, stat, struct
from types import NoneType
from stat import S_IFREG, S_IFDIR
from time import time, strftime, localtime

from zope.interface import implements
from twisted.python import components
from twisted.application import service, strports
from twisted.conch.ssh import factory, keys, session
from twisted.conch.ssh.filetransfer import FileTransferServer, SFTPError, \
     FX_NO_SUCH_FILE, FX_OP_UNSUPPORTED, FX_PERMISSION_DENIED, FX_EOF, \
     FX_BAD_MESSAGE, FX_FAILURE, FX_OK
from twisted.conch.ssh.filetransfer import FXF_READ, FXF_WRITE, FXF_APPEND, \
     FXF_CREAT, FXF_TRUNC, FXF_EXCL
from twisted.conch.interfaces import ISFTPServer, ISFTPFile, IConchUser, ISession
from twisted.conch.avatar import ConchUser
from twisted.conch.openssh_compat import primes
from twisted.cred import portal
from twisted.internet.error import ProcessDone, ProcessTerminated
from twisted.python.failure import Failure
from twisted.internet.interfaces import ITransport

from twisted.internet import defer
from twisted.internet.interfaces import IConsumer
from foolscap.api import eventually
from allmydata.util import deferredutil

from allmydata.util.assertutil import _assert, precondition
from allmydata.util.consumer import download_to_data
from allmydata.interfaces import IFileNode, IDirectoryNode, ExistingChildError, \
     NoSuchChildError, ChildOfWrongTypeError, DownloadStopped
from allmydata.mutable.common import NotWriteableError
from allmydata.mutable.publish import MutableFileHandle
from allmydata.immutable.upload import FileHandle
from allmydata.dirnode import update_metadata
from allmydata.util.fileutil import EncryptedTemporaryFile

noisy = True
use_foolscap_logging = True

from allmydata.util.log import NOISY, OPERATIONAL, WEIRD, \
    msg as _msg, err as _err, PrefixingLogMixin as _PrefixingLogMixin

if use_foolscap_logging:
    (logmsg, logerr, PrefixingLogMixin) = (_msg, _err, _PrefixingLogMixin)
else:  # pragma: no cover
    def logmsg(s, level=None):
        print s
    def logerr(s, level=None):
        print s
    class PrefixingLogMixin:
        def __init__(self, facility=None, prefix=''):
            self.prefix = prefix
        def log(self, s, level=None):
            print "%r %s" % (self.prefix, s)


def eventually_callback(d):
    return lambda res: eventually(d.callback, res)

def eventually_errback(d):
    return lambda err: eventually(d.errback, err)


def _utf8(x):
    if isinstance(x, unicode):
        return x.encode('utf-8')
    if isinstance(x, str):
        return x
    return repr(x)


def _to_sftp_time(t):
    """SFTP times are unsigned 32-bit integers representing UTC seconds
    (ignoring leap seconds) since the Unix epoch, January 1 1970 00:00 UTC.
    A Tahoe time is the corresponding float."""
    return long(t) & 0xFFFFFFFFL


def _convert_error(res, request):
    """If res is not a Failure, return it, otherwise reraise the appropriate
    SFTPError."""

    if not isinstance(res, Failure):
        logged_res = res
        if isinstance(res, str): logged_res = "<data of length %r>" % (len(res),)
        logmsg("SUCCESS %r %r" % (request, logged_res,), level=OPERATIONAL)
        return res

    err = res
    logmsg("RAISE %r %r" % (request, err.value), level=OPERATIONAL)
    try:
        if noisy: logmsg(traceback.format_exc(err.value), level=NOISY)
    except Exception:  # pragma: no cover
        pass

    # The message argument to SFTPError must not reveal information that
    # might compromise anonymity, if we are running over an anonymous network.

    if err.check(SFTPError):
        # original raiser of SFTPError has responsibility to ensure anonymity
        raise err
    if err.check(NoSuchChildError):
        childname = _utf8(err.value.args[0])
        raise SFTPError(FX_NO_SUCH_FILE, childname)
    if err.check(NotWriteableError) or err.check(ChildOfWrongTypeError):
        msg = _utf8(err.value.args[0])
        raise SFTPError(FX_PERMISSION_DENIED, msg)
    if err.check(ExistingChildError):
        # Versions of SFTP after v3 (which is what twisted.conch implements)
        # define a specific error code for this case: FX_FILE_ALREADY_EXISTS.
        # However v3 doesn't; instead, other servers such as sshd return
        # FX_FAILURE. The gvfs SFTP backend, for example, depends on this
        # to translate the error to the equivalent of POSIX EEXIST, which is
        # necessary for some picky programs (such as gedit).
        msg = _utf8(err.value.args[0])
        raise SFTPError(FX_FAILURE, msg)
    if err.check(NotImplementedError):
        raise SFTPError(FX_OP_UNSUPPORTED, _utf8(err.value))
    if err.check(EOFError):
        raise SFTPError(FX_EOF, "end of file reached")
    if err.check(defer.FirstError):
        _convert_error(err.value.subFailure, request)

    # We assume that the error message is not anonymity-sensitive.
    raise SFTPError(FX_FAILURE, _utf8(err.value))


def _repr_flags(flags):
    return "|".join([f for f in
                     [(flags & FXF_READ)   and "FXF_READ"   or None,
                      (flags & FXF_WRITE)  and "FXF_WRITE"  or None,
                      (flags & FXF_APPEND) and "FXF_APPEND" or None,
                      (flags & FXF_CREAT)  and "FXF_CREAT"  or None,
                      (flags & FXF_TRUNC)  and "FXF_TRUNC"  or None,
                      (flags & FXF_EXCL)   and "FXF_EXCL"   or None,
                     ]
                     if f])


def _lsLine(name, attrs):
    st_uid = "tahoe"
    st_gid = "tahoe"
    st_mtime = attrs.get("mtime", 0)
    st_mode = attrs["permissions"]

    # Some clients won't tolerate '?' in the size field (#1337).
    st_size = attrs.get("size", 0)

    # We don't know how many links there really are to this object.
    st_nlink = 1

    # Based on <https://twistedmatrix.com/trac/browser/trunk/twisted/conch/ls.py?rev=25412>.
    # We previously could not call the version in Twisted because we needed the change
    # <https://twistedmatrix.com/trac/changeset/25412> (released in Twisted v8.2).
    # Since we now depend on Twisted v10.1, consider calling Twisted's version.

    mode = st_mode
    perms = array.array('c', '-'*10)
    ft = stat.S_IFMT(mode)
    if   stat.S_ISDIR(ft): perms[0] = 'd'
    elif stat.S_ISREG(ft): perms[0] = '-'
    else: perms[0] = '?'
    # user
    if mode&stat.S_IRUSR: perms[1] = 'r'
    if mode&stat.S_IWUSR: perms[2] = 'w'
    if mode&stat.S_IXUSR: perms[3] = 'x'
    # group
    if mode&stat.S_IRGRP: perms[4] = 'r'
    if mode&stat.S_IWGRP: perms[5] = 'w'
    if mode&stat.S_IXGRP: perms[6] = 'x'
    # other
    if mode&stat.S_IROTH: perms[7] = 'r'
    if mode&stat.S_IWOTH: perms[8] = 'w'
    if mode&stat.S_IXOTH: perms[9] = 'x'
    # suid/sgid never set

    l = perms.tostring()
    l += str(st_nlink).rjust(5) + ' '
    un = str(st_uid)
    l += un.ljust(9)
    gr = str(st_gid)
    l += gr.ljust(9)
    sz = str(st_size)
    l += sz.rjust(8)
    l += ' '
    day = 60 * 60 * 24
    sixmo = day * 7 * 26
    now = time()
    if st_mtime + sixmo < now or st_mtime > now + day:
        # mtime is more than 6 months ago, or more than one day in the future
        l += strftime("%b %d  %Y ", localtime(st_mtime))
    else:
        l += strftime("%b %d %H:%M ", localtime(st_mtime))
    l += name
    return l


def _no_write(parent_readonly, child, metadata=None):
    """Whether child should be listed as having read-only permissions in parent."""

    if child.is_unknown():
        return True
    elif child.is_mutable():
        return child.is_readonly()
    elif parent_readonly or IDirectoryNode.providedBy(child):
        return True
    else:
        return metadata is not None and metadata.get('no-write', False)


def _populate_attrs(childnode, metadata, size=None):
    attrs = {}

    # The permissions must have the S_IFDIR (040000) or S_IFREG (0100000)
    # bits, otherwise the client may refuse to open a directory.
    # Also, sshfs run as a non-root user requires files and directories
    # to be world-readable/writeable.
    # It is important that we never set the executable bits on files.
    #
    # Directories and unknown nodes have no size, and SFTP doesn't
    # require us to make one up.
    #
    # childnode might be None, meaning that the file doesn't exist yet,
    # but we're going to write it later.

    if childnode and childnode.is_unknown():
        perms = 0
    elif childnode and IDirectoryNode.providedBy(childnode):
        perms = S_IFDIR | 0777
    else:
        # For files, omit the size if we don't immediately know it.
        if childnode and size is None:
            size = childnode.get_size()
        if size is not None:
            _assert(isinstance(size, (int, long)) and not isinstance(size, bool), size=size)
            attrs['size'] = size
        perms = S_IFREG | 0666

    if metadata:
        if metadata.get('no-write', False):
            perms &= S_IFDIR | S_IFREG | 0555  # clear 'w' bits

        # See webapi.txt for what these times mean.
        # We would prefer to omit atime, but SFTP version 3 can only
        # accept mtime if atime is also set.
        if 'linkmotime' in metadata.get('tahoe', {}):
            attrs['ctime'] = attrs['mtime'] = attrs['atime'] = _to_sftp_time(metadata['tahoe']['linkmotime'])
        elif 'mtime' in metadata:
            attrs['ctime'] = attrs['mtime'] = attrs['atime'] = _to_sftp_time(metadata['mtime'])

        if 'linkcrtime' in metadata.get('tahoe', {}):
            attrs['createtime'] = _to_sftp_time(metadata['tahoe']['linkcrtime'])

    attrs['permissions'] = perms

    # twisted.conch.ssh.filetransfer only implements SFTP version 3,
    # which doesn't include SSH_FILEXFER_ATTR_FLAGS.

    return attrs


def _attrs_to_metadata(attrs):
    metadata = {}

    for key in attrs:
        if key == "mtime" or key == "ctime" or key == "createtime":
            metadata[key] = long(attrs[key])
        elif key.startswith("ext_"):
            metadata[key] = str(attrs[key])

    perms = attrs.get('permissions', stat.S_IWUSR)
    if not (perms & stat.S_IWUSR):
        metadata['no-write'] = True

    return metadata


def _direntry_for(filenode_or_parent, childname, filenode=None):
    precondition(isinstance(childname, (unicode, NoneType)), childname=childname)

    if childname is None:
        filenode_or_parent = filenode

    if filenode_or_parent:
        rw_uri = filenode_or_parent.get_write_uri()
        if rw_uri and childname:
            return rw_uri + "/" + childname.encode('utf-8')
        else:
            return rw_uri

    return None


DOWNLOAD_BLOCK_SIZE = 131072


class OverwriteableFileConsumer(PrefixingLogMixin):
    implements(IConsumer)
    """I download original file contents from a file node as needed, and use
    BlockCachedFile for storing a cached copy that records the downloaded data
    and any overwrites. Caching logic is contained in BlockCachedFile. Before
    using me for read/write operations, the necessary data regions must be
    fetched using my when_cached method.

    I switch to a new download connection if the data to be read is too far from
    the position of the currently active download. If no read requests are
    pending, I stop or pause the download.

    This abstraction is mostly independent of SFTP. Consider moving it, if it is found
    useful for other frontends."""

    def __init__(self, file_version, tempfile_maker):
        PrefixingLogMixin.__init__(self, facility="tahoe.sftp")

        if file_version is not None:
            initial_size = file_version.get_size()
        else:
            initial_size = 0

        self.filenode_version = file_version
        self.cache_file = BlockCachedFile(tempfile_maker, initial_size)
        self.pending = []  # (offset, length, is_write, deferred)

        self.producer = None
        self.streaming = False
        self.paused = False

        self.data = []
        self.offset = 0
        self.size = 0

    def registerProducer(self, producer, streaming):
        if noisy:
            self.log('.registerProducer(%r, %r)' % (producer, streaming), level=NOISY)

        if self.producer is not None:
            raise RuntimeError("producer is already registered")

        self.producer = producer
        self.streaming = streaming
        self.paused = False
        self.data = []
        self.size = 0

        self.producer.resumeProducing()

    def unregisterProducer(self):
        if noisy:
            self.log('.unregisterProducer()', level=NOISY)
        self.producer = None
        self.data = []

    def write(self, data):
        if noisy:
            self.log('.write()', level=NOISY)

        self.data.append(data)
        self.size += len(data)
        self.offset, self.data = self.cache_file.receive_cached_data(self.offset, self.data)

        self._flush_pending()
        self._reschedule_pending()

        if self.producer is not None and not self.streaming:
            eventually(self._produce)

    def _produce(self):
        if self.producer is not None and not self.streaming:
            self.producer.resumeProducing()

    def _flush_pending(self):
        if noisy:
            self.log('._flush_pending() - %d pending' % (len(self.pending),), level=NOISY)

        while self.pending:
            offset, length, write, deferred = self.pending[0]

            if write:
                required = self.cache_file.pre_write(offset, length)
            else:
                required = self.cache_file.pre_read(offset, length)

            if required is None:
                # Cache ready
                self.pending.pop(0)
                deferred.callback(None)
            else:
                # Cache not ready. Retain the order of the pending operations.
                break

    def _reschedule_pending(self):
        if noisy:
            self.log('._reschedule_pending()', level=NOISY)

        if not self.pending:
            # No data needed currently
            if self.producer:
                if self.streaming:
                    self.producer.pauseProducing()
                    self.paused = True
                else:
                    self.producer.stopProducing()
                    self.unregisterProducer()
            return

        offset, length, write, deferred = self.pending[0]
        if write:
            offset, length = self.cache_file.pre_write(offset, length)
        else:
            offset, length = self.cache_file.pre_read(offset, length)

        if self.producer is not None:
            if offset < self.offset or offset > self.offset + self.size + DOWNLOAD_BLOCK_SIZE:
                # Negative or large positive seek in data: need to reposition
                self.producer.stopProducing()
                self.unregisterProducer()

        if self.producer is None:
            # Schedule new download
            self.offset = offset
            d = self.filenode_version.read(self, offset)
            d.addCallbacks(self._download_complete, self._download_error)
            # It is correct to drop d here

            if noisy:
                self.log('._reschedule_pending() - start reading at %d for (%d bytes @ %d)'
                         % (offset, length, offset), level=NOISY)
        else:
            # Continue using the current producer
            if noisy:
                self.log('._reschedule_pending() - continue reading for (%d bytes @ %d)'
                         % (length, offset), level=NOISY)

            if self.producer is not None and self.paused:
                self.producer.resumeProducing()
                self.paused = False

    def _download_error(self, err):
        if noisy:
            self.log('._download_error(%r)' % (err,), level=NOISY)

        if not isinstance(err.value, DownloadStopped):
            # stop reading and fail all pending operations
            if self.producer is not None:
                self.producer.stopProducing()
                self.unregisterProducer()

            pending = self.pending
            self.pending = []
            for _, _, _, deferred in pending:
                deferred.errback(err)

        return None

    def _download_complete(self, ign):
        if noisy:
            self.log('._download_complete()', level=NOISY)

        # Since we don't necessarily fetch all data in one go, downloads can
        # terminate before all pending operations are satisfied
        self._flush_pending()
        self._reschedule_pending()
        return None

    def when_cached(self, offset, length, write=False):
        d = defer.Deferred()
        self.pending.append((offset, length, write, d))
        self._flush_pending()
        self._reschedule_pending()
        return d

    def when_fully_cached(self):
        return self.when_cached(0, self.cache_file.cache_size, write=False)

    def close(self):
        if self.producer is not None:
            self.producer.stopProducing()
            self.unregisterProducer()

        err = Failure(IOError("file closed"))
        pending = self.pending
        self.pending = []
        for _, _, _, deferred in pending:
            deferred.errback(err)

        self.cache_file.close()

    def get_size(self):
        return self.cache_file.get_size()

    def get_file(self):
        return self.cache_file.get_file()

    def truncate(self, size):
        self.cache_file.truncate(size)

    def read(self, offset, length):
        return self.cache_file.read(offset, length)

    def overwrite(self, offset, data):
        self.cache_file.write(offset, data)


class BlockCachedFile(PrefixingLogMixin):
    """
    I am temporary file, caching data for a remote file. I support
    overwriting data. I cache remote data on a per-block basis and
    keep track of which blocks need still to be retrieved. Before each
    read/write operation, my pre_read or pre_write method needs to be
    called --- these give the ranges of data that need to be retrieved
    from the remote file and fed to me (via receive_cached_data)
    before the read/write operation can succeed. I am fully
    synchronous.
    """

    def __init__(self, tempfile_maker, initial_cache_size, block_size=None):
        PrefixingLogMixin.__init__(self, facility="tahoe.sftp")

        if block_size is None:
            block_size = DOWNLOAD_BLOCK_SIZE

        self.f = tempfile_maker()
        self.actual_size = 0
        self.block_size = block_size

        self.cache_size = initial_cache_size
        num_blocks, remainder = divmod(self.cache_size, self.block_size)
        if remainder != 0:
            num_blocks += 1
        self.cache_map = BitArray(num_blocks)
        self.first_uncached_block = 0

    def _get_block_range(self, offset, length, inner=False):
        """
        For inner=False: compute block range fully containing [offset, offset+length)
        For inner=True: compute block range fully contained in [offset, offset+length)
        """
        if offset >= self.cache_size:
            length = 0
        else:
            length = min(length, self.cache_size - offset)

        if length == 0:
            return 0, 0, 0, 0

        start_block, start_skip = divmod(offset, self.block_size)
        end_block, end_skip = divmod(offset + length, self.block_size)

        if inner:
            if start_skip > 0:
                start_block += 1
                start_skip = self.block_size - start_skip

            if offset + length == self.cache_size and end_skip > 0:
                # the last block can be partial
                end_skip = 0
                end_block += 1
        else:
            if end_skip > 0:
                end_block += 1
                if offset + length == self.cache_size:
                    # last block can be partial
                    end_skip = 0
                else:
                    end_skip = self.block_size - end_skip

        return start_block, end_block, start_skip, end_skip

    def _pad_file(self, new_size):
        """
        Append zero bytes to self.f so that its size grows to new_size
        """
        if new_size <= self.actual_size:
            return

        self.f.seek(0, 2)

        nblocks, remainder = divmod(new_size - self.actual_size, self.block_size)
        if nblocks > 0:
            blk = "\x00" * self.block_size
            for j in range(nblocks):
                self.f.write(blk)
        if remainder > 0:
            self.f.write("\x00" * remainder)

        self.actual_size = new_size

    def receive_cached_data(self, offset, data_list):
        """
        Write full data blocks to file, unless they were not written
        yet. Returns (new_offset, new_data_list) containing unused,
        possibly reuseable data. data_list is a list of strings.
        """
        if noisy:
            self.log(".receive_cached_data()", level=NOISY)

        data_size = sum(len(data) for data in data_list)

        start_block, end_block, start_skip, end_skip = self._get_block_range(
            offset, data_size, inner=True)

        if start_block == end_block:
            # not enough data
            return offset, data_list

        data = "".join(data_list)[start_skip:]

        if start_block < self.first_uncached_block:
            i = self.first_uncached_block - start_block
            start_block = self.first_uncached_block
        else:
            i = 0

        for j in xrange(start_block, end_block):
            if not self.cache_map[j]:
                pos = j * self.block_size
                block = data[i*self.block_size:(i+1)*self.block_size]
                block = block[:(self.cache_size - pos)]
                self._pad_file(pos)
                self.f.seek(pos)
                self.f.write(block)

                self.actual_size = max(self.actual_size, pos + len(block))
                self.cache_map[j] = True
            i += 1

        if start_block <= self.first_uncached_block:
            self.first_uncached_block = max(self.first_uncached_block, end_block)

        # Return trailing data for possible future use
        if end_skip > 0:
            data_list = [data[-end_skip:]]
            offset += data_size - len(data_list[0])
        else:
            data_list = []
            offset += data_size
        return (offset, data_list)

    def get_size(self):
        return max(self.actual_size, self.cache_size)

    def get_file(self):
        # Pad file to full size before returning file handle
        self._pad_file(self.get_size())
        return self.f

    def close(self):
        self.f.close()
        self.cache_map = BitArray(0)

    def truncate(self, size):
        if size < self.actual_size:
            self.f.truncate(size)
            self.actual_size = size
        elif size > self.actual_size:
            self._pad_file(size)

        self.cache_size = min(size, self.cache_size)

    def write(self, offset, data):
        if offset > self.actual_size:
            # Explicit POSIX behavior for write-past-end
            self._pad_file(offset)

        if len(data) == 0:
            # noop
            return

        # Sanity check cache status
        if self.pre_write(offset, len(data)) is not None:
            raise RuntimeError("attempt to write before caching")

        # Perform write
        self.f.seek(offset)
        self.f.write(data)
        self.actual_size = max(self.actual_size, offset + len(data))

        # Update cache status for completely overwritten blocks
        start_block, end_block, _, _ = self._get_block_range(offset, len(data), inner=True)
        for j in xrange(max(start_block, self.first_uncached_block), end_block):
            self.cache_map[j] = True
        if start_block <= self.first_uncached_block:
            self.first_uncached_block = max(self.first_uncached_block, end_block)

    def read(self, offset, length):
        if noisy:
            self.log(".read(%d, %d) (%d %d)" % (offset, length, self.actual_size, self.cache_size),
                     level=NOISY)
        if offset >= self.actual_size and offset >= self.cache_size:
            raise EOFError("read past end of file")

        # Sanity check cache status
        if self.pre_read(offset, length) is not None:
            raise RuntimeError("attempt to read before caching")

        # Perform read
        self.f.seek(offset)
        return self.f.read(length)

    def pre_read(self, offset, length):
        """
        Return (offset, length) of the first cache fetch that need to be
        performed and the results fed into `receive_cached_data` before a read
        operation can be performed. There may be more than one fetch
        necessary. Return None if no fetch is necessary.
        """
        start_block, end_block, _, _ = self._get_block_range(offset, length)

        if noisy:
            self.log(".pre_read(%d, %d) -> %d-%d" % (offset, length, start_block, end_block),
                     level=NOISY)

        # Combine consequent blocks into a single read
        j = start_block
        while j < end_block and self.cache_map[j]:
            j += 1
        if j >= end_block:
            return None

        for k in xrange(j+1, end_block):
            if self.cache_map[k]:
                end = k
                break
        else:
            end = end_block

        start_pos = j * self.block_size
        end_pos = end * self.block_size
        if start_pos < self.cache_size:
            return (start_pos, max(self.cache_size, end_pos) - start_pos)

        return None

    def pre_write(self, offset, length):
        """
        Similarly to pre_read, but for write operations.
        """
        start_block, end_block, start_skip, end_skip = self._get_block_range(offset, length)

        if noisy:
            self.log(".pre_write(%d, %d) -> %d-%d" % (offset, length, start_block, end_block),
                     level=NOISY)

        if start_block < end_block:
            if (offset % self.block_size) != 0 and not self.cache_map[start_block]:
                start_pos = start_block * self.block_size
                end_pos = (start_block + 1) * self.block_size
                if start_pos < self.cache_size:
                    return (start_pos, max(self.cache_size, end_pos) - start_pos)

            if ((offset + length) % self.block_size) != 0 and not self.cache_map[end_block - 1]:
                start_pos = (end_block - 1) * self.block_size
                end_pos = end_block * self.block_size
                if start_pos < self.cache_size:
                    return (start_pos, max(self.cache_size, end_pos) - start_pos)

        # No reads required
        return None


class BitArray(object):
    """
    Mutable array of n bits
    """
    def __init__(self, n):
        if n < 0:
            raise ValueError("must have n >= 0")
        self.n = n
        self.value = 0
        self.mask = 2**n - 1

    def __getitem__(self, i):
        if i < 0 or i >= self.n:
            raise ValueError("out of bounds get")
        return (self.value >> i) & 0x1

    def __setitem__(self, i, value):
        if i < 0 or i >= self.n:
            raise ValueError("out of bounds set")
        r = (0x1 << i)
        if value:
            self.value |= r
        else:
            r ^= self.mask
            self.value &= r

    def __repr__(self):
        r = "".join('1' if self[i] else '0' for i in range(self.n))
        return "<Bitarray %r>" % (r,)


SIZE_THRESHOLD = 1000


class ShortReadOnlySFTPFile(PrefixingLogMixin):
    implements(ISFTPFile)
    """I represent a file handle to a particular file on an SFTP connection.
    I am used only for short immutable files opened in read-only mode.
    When I am created, the file contents start to be downloaded to memory.
    self.async is used to delay read requests until the download has finished."""

    def __init__(self, userpath, filenode, metadata):
        PrefixingLogMixin.__init__(self, facility="tahoe.sftp", prefix=userpath)
        if noisy: self.log(".__init__(%r, %r, %r)" % (userpath, filenode, metadata), level=NOISY)

        precondition(isinstance(userpath, str) and IFileNode.providedBy(filenode),
                     userpath=userpath, filenode=filenode)
        self.filenode = filenode
        self.metadata = metadata
        self.async = download_to_data(filenode)
        self.closed = False

    def readChunk(self, offset, length):
        request = ".readChunk(%r, %r)" % (offset, length)
        self.log(request, level=OPERATIONAL)

        if self.closed:
            def _closed(): raise SFTPError(FX_BAD_MESSAGE, "cannot read from a closed file handle")
            return defer.execute(_closed)

        d = defer.Deferred()
        def _read(data):
            if noisy: self.log("_read(<data of length %r>) in readChunk(%r, %r)" % (len(data), offset, length), level=NOISY)

            # "In response to this request, the server will read as many bytes as it
            #  can from the file (up to 'len'), and return them in a SSH_FXP_DATA
            #  message.  If an error occurs or EOF is encountered before reading any
            #  data, the server will respond with SSH_FXP_STATUS.  For normal disk
            #  files, it is guaranteed that this will read the specified number of
            #  bytes, or up to end of file."
            #
            # i.e. we respond with an EOF error iff offset is already at EOF.

            if offset >= len(data):
                eventually_errback(d)(Failure(SFTPError(FX_EOF, "read at or past end of file")))
            else:
                eventually_callback(d)(data[offset:offset+length])  # truncated if offset+length > len(data)
            return data
        self.async.addCallbacks(_read, eventually_errback(d))
        d.addBoth(_convert_error, request)
        return d

    def writeChunk(self, offset, data):
        self.log(".writeChunk(%r, <data of length %r>) denied" % (offset, len(data)), level=OPERATIONAL)

        def _denied(): raise SFTPError(FX_PERMISSION_DENIED, "file handle was not opened for writing")
        return defer.execute(_denied)

    def close(self):
        self.log(".close()", level=OPERATIONAL)

        self.closed = True
        return defer.succeed(None)

    def getAttrs(self):
        request = ".getAttrs()"
        self.log(request, level=OPERATIONAL)

        if self.closed:
            def _closed(): raise SFTPError(FX_BAD_MESSAGE, "cannot get attributes for a closed file handle")
            return defer.execute(_closed)

        d = defer.execute(_populate_attrs, self.filenode, self.metadata)
        d.addBoth(_convert_error, request)
        return d

    def setAttrs(self, attrs):
        self.log(".setAttrs(%r) denied" % (attrs,), level=OPERATIONAL)
        def _denied(): raise SFTPError(FX_PERMISSION_DENIED, "file handle was not opened for writing")
        return defer.execute(_denied)


class GeneralSFTPFile(PrefixingLogMixin):
    implements(ISFTPFile)
    """I represent a file handle to a particular file on an SFTP connection.
    I wrap an instance of OverwriteableFileConsumer, which is responsible for
    storing the file contents. In order to allow write requests to be satisfied
    immediately, there is effectively a FIFO queue between requests made to this
    file handle, and requests to my OverwriteableFileConsumer. This queue is
    implemented by the callback chain of self.async.

    When first constructed, I am in an 'unopened' state that causes most
    operations to be delayed until 'open' is called."""

    def __init__(self, userpath, flags, close_notify, convergence):
        PrefixingLogMixin.__init__(self, facility="tahoe.sftp", prefix=userpath)
        if noisy: self.log(".__init__(%r, %r = %r, %r, <convergence censored>)" %
                           (userpath, flags, _repr_flags(flags), close_notify), level=NOISY)

        precondition(isinstance(userpath, str), userpath=userpath)
        self.userpath = userpath
        self.flags = flags
        self.close_notify = close_notify
        self.convergence = convergence
        self.async = defer.Deferred()
        # Creating or truncating the file is a change, but if FXF_EXCL is set, a zero-length file has already been created.
        self.has_changed = (flags & (FXF_CREAT | FXF_TRUNC)) and not (flags & FXF_EXCL)
        self.closed = False
        self.abandoned = False
        self.parent = None
        self.childname = None
        self.filenode = None
        self.metadata = None

        # self.consumer should only be relied on in callbacks for self.async, since it might
        # not be set before then.
        self.consumer = None
        self.write_error = None

    def open(self, parent=None, childname=None, filenode=None, metadata=None):
        self.log(".open(parent=%r, childname=%r, filenode=%r, metadata=%r)" %
                 (parent, childname, filenode, metadata), level=OPERATIONAL)

        precondition(isinstance(childname, (unicode, NoneType)), childname=childname)
        precondition(filenode is None or IFileNode.providedBy(filenode), filenode=filenode)
        precondition(not self.closed, sftpfile=self)

        # If the file has been renamed, the new (parent, childname) takes precedence.
        if self.parent is None:
            self.parent = parent
        if self.childname is None:
            self.childname = childname
        self.filenode = filenode
        self.metadata = metadata

        tempfile_maker = EncryptedTemporaryFile

        if (self.flags & FXF_TRUNC) or not filenode:
            # We're either truncating or creating the file, so we don't need the old contents.
            self.consumer = OverwriteableFileConsumer(None, tempfile_maker)
        else:
            self.async.addCallback(lambda ignored: filenode.get_best_readable_version())
            def _read(version):
                if noisy:
                    self.log(".open -> _read", level=NOISY)
                self.consumer = OverwriteableFileConsumer(version, tempfile_maker)
                return None
            self.async.addCallback(_read)

        eventually_callback(self.async)(None)

        if noisy: self.log("open done", level=NOISY)
        return self

    def get_userpath(self):
        return self.userpath

    def get_direntry(self):
        return _direntry_for(self.parent, self.childname)

    def rename(self, new_userpath, new_parent, new_childname):
        self.log(".rename(%r, %r, %r)" % (new_userpath, new_parent, new_childname), level=OPERATIONAL)

        precondition(isinstance(new_userpath, str) and isinstance(new_childname, unicode),
                     new_userpath=new_userpath, new_childname=new_childname)
        self.userpath = new_userpath
        self.parent = new_parent
        self.childname = new_childname

    def abandon(self):
        self.log(".abandon()", level=OPERATIONAL)

        self.abandoned = True

    def sync(self, ign=None):
        # The ign argument allows some_file.sync to be used as a callback.
        self.log(".sync()", level=OPERATIONAL)

        d = defer.Deferred()
        self.async.addBoth(eventually_callback(d))
        def _done(res):
            if noisy: self.log("_done(%r) in .sync()" % (res,), level=NOISY)
            return res
        d.addBoth(_done)
        return d

    def readChunk(self, offset, length):
        request = ".readChunk(%r, %r)" % (offset, length)
        self.log(request, level=OPERATIONAL)

        if not (self.flags & FXF_READ):
            def _denied(): raise SFTPError(FX_PERMISSION_DENIED, "file handle was not opened for reading")
            return defer.execute(_denied)

        if self.closed:
            def _closed(): raise SFTPError(FX_BAD_MESSAGE, "cannot read from a closed file handle")
            return defer.execute(_closed)

        d = defer.Deferred()
        def _read(ign):
            if noisy:
                self.log("_read in readChunk(%r, %r)" % (offset, length), level=NOISY)

            # Schedule caching
            d2 = self.consumer.when_cached(offset, length, write=False)
            def _do_read(ign):
                if noisy:
                    self.log("_do_read in readChunk(%r, %r)" % (offset, length), level=NOISY)
                # Cache is ready: read
                try:
                    data = self.consumer.read(offset, length)
                except EOFError, err:
                    return eventually_errback(d)(err)
                eventually_callback(d)(data)
                return None
            d2.addCallbacks(_do_read, eventually_errback(d))
            # It is correct to drop d2 here

            return None

        self.async.addCallbacks(_read, eventually_errback(d))
        d.addBoth(_convert_error, request)
        return d

    def writeChunk(self, offset, data):
        self.log(".writeChunk(%r, <data of length %r>)" % (offset, len(data)), level=OPERATIONAL)

        if not (self.flags & FXF_WRITE):
            def _denied(): raise SFTPError(FX_PERMISSION_DENIED, "file handle was not opened for writing")
            return defer.execute(_denied)

        if self.closed:
            def _closed(): raise SFTPError(FX_BAD_MESSAGE, "cannot write to a closed file handle")
            return defer.execute(_closed)

        self.has_changed = True

        # Note that we return without waiting for the write to occur. Reads and
        # close wait for prior writes, and will fail if any prior operation failed.
        # This is ok because SFTP makes no guarantee that the write completes
        # before the request does. In fact it explicitly allows write errors to be
        # delayed until close:
        #   "One should note that on some server platforms even a close can fail.
        #    This can happen e.g. if the server operating system caches writes,
        #    and an error occurs while flushing cached writes during the close."

        def _write(ign):
            if noisy: self.log("_write in .writeChunk(%r, <data of length %r>)" %
                               (offset, len(data)), level=NOISY)

            # Schedule caching
            d2 = self.consumer.when_cached(offset, len(data), write=True)
            def _do_write(ign):
                if noisy:
                    self.log("_do_write in writeChunk(%r, <data of length %r>)" %
                             (offset, len(data)), level=NOISY)
                # Cache is ready: write

                # FXF_APPEND means that we should always write at the current end of file.
                write_offset = offset
                if self.flags & FXF_APPEND:
                    write_offset = self.consumer.get_size()
                self.consumer.overwrite(write_offset, data)
                if noisy:
                    self.log("write done", level=NOISY)
                return None
            def _do_write_error(err):
                self.write_error = err
                return None
            d2.addCallbacks(_do_write, _do_write_error)
            # It is correct to drop d2 here

            return None
        self.async.addCallback(_write)
        # don't addErrback to self.async, just allow subsequent async ops to fail.
        return defer.succeed(None)

    def _do_close(self, res, d=None):
        if noisy: self.log("_do_close(%r)" % (res,), level=NOISY)

        if self.consumer:
            self.consumer.close()

        # We must close_notify before re-firing self.async.
        if self.close_notify:
            self.close_notify(self.userpath, self.parent, self.childname, self)

        if not isinstance(res, Failure) and isinstance(self.write_error, Failure):
            res = self.write_error

        if d:
            eventually_callback(d)(res)
        elif isinstance(res, Failure):
            self.log("suppressing %r" % (res,), level=OPERATIONAL)

    def close(self):
        request = ".close()"
        self.log(request, level=OPERATIONAL)

        if self.closed:
            return defer.succeed(None)

        # This means that close has been called, not that the close has succeeded.
        self.closed = True

        if not (self.flags & (FXF_WRITE | FXF_CREAT)):
            # We never fail a close of a handle opened only for reading, even if the file
            # failed to download. (We could not do so deterministically, because it would
            # depend on whether we reached the point of failure before abandoning the
            # download.) Any reads that depended on file content that could not be downloaded
            # will have failed. It is important that we don't close the consumer until
            # previous read operations have completed.
            self.async.addBoth(self._do_close)
            return defer.succeed(None)

        # We must capture the abandoned, parent, and childname variables synchronously
        # at the close call. This is needed by the correctness arguments in the comments
        # for _abandon_any_heisenfiles and _rename_heisenfiles.
        # Note that the file must have been opened before it can be closed.
        abandoned = self.abandoned
        parent = self.parent
        childname = self.childname

        # has_changed is set when writeChunk is called, not when the write occurs, so
        # it is correct to optimize out the commit if it is False at the close call.
        has_changed = self.has_changed

        def _commit(ign):
            # Full-file download
            d2 = self.consumer.when_fully_cached()
            if self.filenode and self.filenode.is_mutable():
                self.log("update mutable file %r childname=%r metadata=%r"
                         % (self.filenode, childname, self.metadata), level=OPERATIONAL)
                if self.metadata.get('no-write', False) and not self.filenode.is_readonly():
                    _assert(parent and childname, parent=parent, childname=childname, metadata=self.metadata)
                    d2.addCallback(lambda ign: parent.set_metadata_for(childname, self.metadata))

                d2.addCallback(lambda ign: self.filenode.overwrite(MutableFileHandle(self.consumer.get_file())))
            else:
                def _add_file(ign):
                    self.log("_add_file childname=%r" % (childname,), level=OPERATIONAL)
                    u = FileHandle(self.consumer.get_file(), self.convergence)
                    return parent.add_file(childname, u, metadata=self.metadata)
                d2.addCallback(_add_file)

            return d2

        # If the file has been abandoned, we don't want the close operation to get "stuck",
        # even if self.async fails to re-fire. Completing the close independently of self.async
        # in that case should ensure that dropping an ssh connection is sufficient to abandon
        # any heisenfiles that were not explicitly closed in that connection.
        if abandoned or not has_changed:
            d = defer.succeed(None)
            self.async.addBoth(self._do_close)
        else:
            d = defer.Deferred()
            self.async.addCallback(_commit)
            self.async.addBoth(self._do_close, d)
        d.addBoth(_convert_error, request)
        return d

    def getAttrs(self):
        request = ".getAttrs()"
        self.log(request, level=OPERATIONAL)

        if self.closed:
            def _closed(): raise SFTPError(FX_BAD_MESSAGE, "cannot get attributes for a closed file handle")
            return defer.execute(_closed)

        # Optimization for read-only handles, when we already know the metadata.
        if not (self.flags & (FXF_WRITE | FXF_CREAT)) and self.metadata and self.filenode and not self.filenode.is_mutable():
            return defer.succeed(_populate_attrs(self.filenode, self.metadata))

        d = defer.Deferred()
        def _get(ign):
            if noisy: self.log("_get(%r) in %r, filenode = %r, metadata = %r" % (ign, request, self.filenode, self.metadata), level=NOISY)

            # self.filenode might be None, but that's ok.
            attrs = _populate_attrs(self.filenode, self.metadata, size=self.consumer.get_size())
            eventually_callback(d)(attrs)
            return None
        self.async.addCallbacks(_get, eventually_errback(d))
        d.addBoth(_convert_error, request)
        return d

    def setAttrs(self, attrs, only_if_at=None):
        request = ".setAttrs(%r, only_if_at=%r)" % (attrs, only_if_at)
        self.log(request, level=OPERATIONAL)

        if not (self.flags & FXF_WRITE):
            def _denied(): raise SFTPError(FX_PERMISSION_DENIED, "file handle was not opened for writing")
            return defer.execute(_denied)

        if self.closed:
            def _closed(): raise SFTPError(FX_BAD_MESSAGE, "cannot set attributes for a closed file handle")
            return defer.execute(_closed)

        size = attrs.get("size", None)
        if size is not None and (not isinstance(size, (int, long)) or size < 0):
            def _bad(): raise SFTPError(FX_BAD_MESSAGE, "new size is not a valid nonnegative integer")
            return defer.execute(_bad)

        d = defer.Deferred()
        def _set(ign):
            if noisy: self.log("_set(%r) in %r" % (ign, request), level=NOISY)
            current_direntry = _direntry_for(self.parent, self.childname, self.filenode)
            if only_if_at and only_if_at != current_direntry:
                if noisy: self.log("not setting attributes: current_direntry=%r in %r" %
                                   (current_direntry, request), level=NOISY)
                return None

            now = time()
            self.metadata = update_metadata(self.metadata, _attrs_to_metadata(attrs), now)
            if size is not None:
                # TODO: should we refuse to truncate a file opened with FXF_APPEND?
                # <http://allmydata.org/trac/tahoe-lafs/ticket/1037#comment:20>
                self.consumer.truncate(size)
            eventually_callback(d)(None)
            return None
        self.async.addCallbacks(_set, eventually_errback(d))
        d.addBoth(_convert_error, request)
        return d


class StoppableList:
    def __init__(self, items):
        self.items = items
    def __iter__(self):
        for i in self.items:
            yield i
    def close(self):
        pass


class Reason:
    def __init__(self, value):
        self.value = value


# A "heisenfile" is a file that has been opened with write flags
# (FXF_WRITE and/or FXF_CREAT) and not yet close-notified.
# 'all_heisenfiles' maps from a direntry string to a list of
# GeneralSFTPFile.
#
# A direntry string is parent_write_uri + "/" + childname_utf8 for
# an immutable file, or file_write_uri for a mutable file.
# Updates to this dict are single-threaded.

all_heisenfiles = {}

def _reload():
    global all_heisenfiles
    all_heisenfiles = {}

class SFTPUserHandler(ConchUser, PrefixingLogMixin):
    implements(ISFTPServer)
    def __init__(self, client, rootnode, username):
        ConchUser.__init__(self)
        PrefixingLogMixin.__init__(self, facility="tahoe.sftp", prefix=username)
        if noisy: self.log(".__init__(%r, %r, %r)" % (client, rootnode, username), level=NOISY)

        self.channelLookup["session"] = session.SSHSession
        self.subsystemLookup["sftp"] = FileTransferServer

        self._client = client
        self._root = rootnode
        self._username = username
        self._convergence = client.convergence

        # maps from UTF-8 paths for this user, to files written and still open
        self._heisenfiles = {}

    def gotVersion(self, otherVersion, extData):
        self.log(".gotVersion(%r, %r)" % (otherVersion, extData), level=OPERATIONAL)

        # advertise the same extensions as the OpenSSH SFTP server
        # <http://www.openbsd.org/cgi-bin/cvsweb/src/usr.bin/ssh/PROTOCOL?rev=1.15>
        return {'posix-rename@openssh.com': '1',
                'statvfs@openssh.com': '2',
                'fstatvfs@openssh.com': '2',
               }

    def logout(self):
        self.log(".logout()", level=OPERATIONAL)

        for files in self._heisenfiles.itervalues():
            for f in files:
                f.abandon()

    def _add_heisenfile_by_path(self, file):
        self.log("._add_heisenfile_by_path(%r)" % (file,), level=OPERATIONAL)

        userpath = file.get_userpath()
        if userpath in self._heisenfiles:
            self._heisenfiles[userpath] += [file]
        else:
            self._heisenfiles[userpath] = [file]

    def _add_heisenfile_by_direntry(self, file):
        self.log("._add_heisenfile_by_direntry(%r)" % (file,), level=OPERATIONAL)

        direntry = file.get_direntry()
        if direntry:
            if direntry in all_heisenfiles:
                all_heisenfiles[direntry] += [file]
            else:
                all_heisenfiles[direntry] = [file]

    def _abandon_any_heisenfiles(self, userpath, direntry):
        request = "._abandon_any_heisenfiles(%r, %r)" % (userpath, direntry)
        self.log(request, level=OPERATIONAL)

        precondition(isinstance(userpath, str), userpath=userpath)

        # First we synchronously mark all heisenfiles matching the userpath or direntry
        # as abandoned, and remove them from the two heisenfile dicts. Then we .sync()
        # each file that we abandoned.
        #
        # For each file, the call to .abandon() occurs:
        #   * before the file is closed, in which case it will never be committed
        #     (uploaded+linked or published); or
        #   * after it is closed but before it has been close_notified, in which case the
        #     .sync() ensures that it has been committed (successfully or not) before we
        #     return.
        #
        # This avoids a race that might otherwise cause the file to be committed after
        # the remove operation has completed.
        #
        # We return a Deferred that fires with True if any files were abandoned (this
        # does not mean that they were not committed; it is used to determine whether
        # a NoSuchChildError from the attempt to delete the file should be suppressed).

        files = []
        if direntry in all_heisenfiles:
            files = all_heisenfiles[direntry]
            del all_heisenfiles[direntry]
        if userpath in self._heisenfiles:
            files += self._heisenfiles[userpath]
            del self._heisenfiles[userpath]

        if noisy: self.log("files = %r in %r" % (files, request), level=NOISY)

        for f in files:
            f.abandon()

        d = defer.succeed(None)
        for f in files:
            d.addBoth(f.sync)

        def _done(ign):
            self.log("done %r" % (request,), level=OPERATIONAL)
            return len(files) > 0
        d.addBoth(_done)
        return d

    def _rename_heisenfiles(self, from_userpath, from_parent, from_childname,
                            to_userpath, to_parent, to_childname, overwrite=True):
        request = ("._rename_heisenfiles(%r, %r, %r, %r, %r, %r, overwrite=%r)" %
                   (from_userpath, from_parent, from_childname, to_userpath, to_parent, to_childname, overwrite))
        self.log(request, level=OPERATIONAL)

        precondition((isinstance(from_userpath, str) and isinstance(from_childname, unicode) and
                      isinstance(to_userpath, str) and isinstance(to_childname, unicode)),
                     from_userpath=from_userpath, from_childname=from_childname, to_userpath=to_userpath, to_childname=to_childname)

        if noisy: self.log("all_heisenfiles = %r\nself._heisenfiles = %r" % (all_heisenfiles, self._heisenfiles), level=NOISY)

        # First we synchronously rename all heisenfiles matching the userpath or direntry.
        # Then we .sync() each file that we renamed.
        #
        # For each file, the call to .rename occurs:
        #   * before the file is closed, in which case it will be committed at the
        #     new direntry; or
        #   * after it is closed but before it has been close_notified, in which case the
        #     .sync() ensures that it has been committed (successfully or not) before we
        #     return.
        #
        # This avoids a race that might otherwise cause the file to be committed at the
        # old name after the rename operation has completed.
        #
        # Note that if overwrite is False, the caller should already have checked
        # whether a real direntry exists at the destination. It is possible that another
        # direntry (heisen or real) comes to exist at the destination after that check,
        # but in that case it is correct for the rename to succeed (and for the commit
        # of the heisenfile at the destination to possibly clobber the other entry, since
        # that can happen anyway when we have concurrent write handles to the same direntry).
        #
        # We return a Deferred that fires with True if any files were renamed (this
        # does not mean that they were not committed; it is used to determine whether
        # a NoSuchChildError from the rename attempt should be suppressed). If overwrite
        # is False and there were already heisenfiles at the destination userpath or
        # direntry, we return a Deferred that fails with SFTPError(FX_PERMISSION_DENIED).

        from_direntry = _direntry_for(from_parent, from_childname)
        to_direntry = _direntry_for(to_parent, to_childname)

        if noisy: self.log("from_direntry = %r, to_direntry = %r, len(all_heisenfiles) = %r, len(self._heisenfiles) = %r in %r" %
                           (from_direntry, to_direntry, len(all_heisenfiles), len(self._heisenfiles), request), level=NOISY)

        if not overwrite and (to_userpath in self._heisenfiles or to_direntry in all_heisenfiles):
            def _existing(): raise SFTPError(FX_PERMISSION_DENIED, "cannot rename to existing path " + to_userpath)
            if noisy: self.log("existing", level=NOISY)
            return defer.execute(_existing)

        from_files = []
        if from_direntry in all_heisenfiles:
            from_files = all_heisenfiles[from_direntry]
            del all_heisenfiles[from_direntry]
        if from_userpath in self._heisenfiles:
            from_files += self._heisenfiles[from_userpath]
            del self._heisenfiles[from_userpath]

        if noisy: self.log("from_files = %r in %r" % (from_files, request), level=NOISY)

        for f in from_files:
            f.rename(to_userpath, to_parent, to_childname)
            self._add_heisenfile_by_path(f)
            self._add_heisenfile_by_direntry(f)

        d = defer.succeed(None)
        for f in from_files:
            d.addBoth(f.sync)

        def _done(ign):
            if noisy: self.log("done: len(all_heisenfiles) = %r, len(self._heisenfiles) = %r in %r" %
                               (len(all_heisenfiles), len(self._heisenfiles), request), level=NOISY)
            return len(from_files) > 0
        d.addBoth(_done)
        return d

    def _update_attrs_for_heisenfiles(self, userpath, direntry, attrs):
        request = "._update_attrs_for_heisenfiles(%r, %r, %r)" % (userpath, direntry, attrs)
        self.log(request, level=OPERATIONAL)

        _assert(isinstance(userpath, str) and isinstance(direntry, str),
                userpath=userpath, direntry=direntry)

        files = []
        if direntry in all_heisenfiles:
            files = all_heisenfiles[direntry]
        if userpath in self._heisenfiles:
            files += self._heisenfiles[userpath]

        if noisy: self.log("files = %r in %r" % (files, request), level=NOISY)

        # We set the metadata for all heisenfiles at this path or direntry.
        # Since a direntry includes a write URI, we must have authority to
        # change the metadata of heisenfiles found in the all_heisenfiles dict.
        # However that's not necessarily the case for heisenfiles found by
        # path. Therefore we tell the setAttrs method of each file to only
        # perform the update if the file is at the correct direntry.

        d = defer.succeed(None)
        for f in files:
            d.addBoth(f.setAttrs, attrs, only_if_at=direntry)

        def _done(ign):
            self.log("done %r" % (request,), level=OPERATIONAL)
            # TODO: this should not return True if only_if_at caused all files to be skipped.
            return len(files) > 0
        d.addBoth(_done)
        return d

    def _sync_heisenfiles(self, userpath, direntry, ignore=None):
        request = "._sync_heisenfiles(%r, %r, ignore=%r)" % (userpath, direntry, ignore)
        self.log(request, level=OPERATIONAL)

        _assert(isinstance(userpath, str) and isinstance(direntry, (str, NoneType)),
                userpath=userpath, direntry=direntry)

        files = []
        if direntry in all_heisenfiles:
            files = all_heisenfiles[direntry]
        if userpath in self._heisenfiles:
            files += self._heisenfiles[userpath]

        if noisy: self.log("files = %r in %r" % (files, request), level=NOISY)

        d = defer.succeed(None)
        for f in files:
            if f is not ignore:
                d.addBoth(f.sync)

        def _done(ign):
            self.log("done %r" % (request,), level=OPERATIONAL)
            return None
        d.addBoth(_done)
        return d

    def _remove_heisenfile(self, userpath, parent, childname, file_to_remove):
        if noisy: self.log("._remove_heisenfile(%r, %r, %r, %r)" % (userpath, parent, childname, file_to_remove), level=NOISY)

        _assert(isinstance(userpath, str) and isinstance(childname, (unicode, NoneType)),
                userpath=userpath, childname=childname)

        direntry = _direntry_for(parent, childname)
        if direntry in all_heisenfiles:
            all_old_files = all_heisenfiles[direntry]
            all_new_files = [f for f in all_old_files if f is not file_to_remove]
            if len(all_new_files) > 0:
                all_heisenfiles[direntry] = all_new_files
            else:
                del all_heisenfiles[direntry]

        if userpath in self._heisenfiles:
            old_files = self._heisenfiles[userpath]
            new_files = [f for f in old_files if f is not file_to_remove]
            if len(new_files) > 0:
                self._heisenfiles[userpath] = new_files
            else:
                del self._heisenfiles[userpath]

        if noisy: self.log("all_heisenfiles = %r\nself._heisenfiles = %r" % (all_heisenfiles, self._heisenfiles), level=NOISY)

    def _make_file(self, existing_file, userpath, flags, parent=None, childname=None, filenode=None, metadata=None):
        if noisy: self.log("._make_file(%r, %r, %r = %r, parent=%r, childname=%r, filenode=%r, metadata=%r)" %
                           (existing_file, userpath, flags, _repr_flags(flags), parent, childname, filenode, metadata),
                           level=NOISY)

        _assert((isinstance(userpath, str) and isinstance(childname, (unicode, NoneType)) and
                (metadata is None or 'no-write' in metadata)),
                userpath=userpath, childname=childname, metadata=metadata)

        writing = (flags & (FXF_WRITE | FXF_CREAT)) != 0
        direntry = _direntry_for(parent, childname, filenode)

        d = self._sync_heisenfiles(userpath, direntry, ignore=existing_file)

        if not writing and (flags & FXF_READ) and filenode and not filenode.is_mutable() and filenode.get_size() <= SIZE_THRESHOLD:
            d.addCallback(lambda ign: ShortReadOnlySFTPFile(userpath, filenode, metadata))
        else:
            close_notify = None
            if writing:
                close_notify = self._remove_heisenfile

            d.addCallback(lambda ign: existing_file or GeneralSFTPFile(userpath, flags, close_notify, self._convergence))
            def _got_file(file):
                file.open(parent=parent, childname=childname, filenode=filenode, metadata=metadata)
                if writing:
                    self._add_heisenfile_by_direntry(file)
                return file
            d.addCallback(_got_file)
        return d

    def openFile(self, pathstring, flags, attrs, delay=None):
        request = ".openFile(%r, %r = %r, %r, delay=%r)" % (pathstring, flags, _repr_flags(flags), attrs, delay)
        self.log(request, level=OPERATIONAL)

        # This is used for both reading and writing.
        # First exclude invalid combinations of flags, and empty paths.

        if not (flags & (FXF_READ | FXF_WRITE)):
            def _bad_readwrite():
                raise SFTPError(FX_BAD_MESSAGE, "invalid file open flags: at least one of FXF_READ and FXF_WRITE must be set")
            return defer.execute(_bad_readwrite)

        if (flags & FXF_EXCL) and not (flags & FXF_CREAT):
            def _bad_exclcreat():
                raise SFTPError(FX_BAD_MESSAGE, "invalid file open flags: FXF_EXCL cannot be set without FXF_CREAT")
            return defer.execute(_bad_exclcreat)

        path = self._path_from_string(pathstring)
        if not path:
            def _emptypath(): raise SFTPError(FX_NO_SUCH_FILE, "path cannot be empty")
            return defer.execute(_emptypath)

        # The combination of flags is potentially valid.

        # To work around clients that have race condition bugs, a getAttr, rename, or
        # remove request following an 'open' request with FXF_WRITE or FXF_CREAT flags,
        # should succeed even if the 'open' request has not yet completed. So we now
        # synchronously add a file object into the self._heisenfiles dict, indexed
        # by its UTF-8 userpath. (We can't yet add it to the all_heisenfiles dict,
        # because we don't yet have a user-independent path for the file.) The file
        # object does not know its filenode, parent, or childname at this point.

        userpath = self._path_to_utf8(path)

        if flags & (FXF_WRITE | FXF_CREAT):
            file = GeneralSFTPFile(userpath, flags, self._remove_heisenfile, self._convergence)
            self._add_heisenfile_by_path(file)
        else:
            # We haven't decided which file implementation to use yet.
            file = None

        desired_metadata = _attrs_to_metadata(attrs)

        # Now there are two major cases:
        #
        #  1. The path is specified as /uri/FILECAP, with no parent directory.
        #     If the FILECAP is mutable and writeable, then we can open it in write-only
        #     or read/write mode (non-exclusively), otherwise we can only open it in
        #     read-only mode. The open should succeed immediately as long as FILECAP is
        #     a valid known filecap that grants the required permission.
        #
        #  2. The path is specified relative to a parent. We find the parent dirnode and
        #     get the child's URI and metadata if it exists. There are four subcases:
        #       a. the child does not exist: FXF_CREAT must be set, and we must be able
        #          to write to the parent directory.
        #       b. the child exists but is not a valid known filecap: fail
        #       c. the child is mutable: if we are trying to open it write-only or
        #          read/write, then we must be able to write to the file.
        #       d. the child is immutable: if we are trying to open it write-only or
        #          read/write, then we must be able to write to the parent directory.
        #
        # To reduce latency, open normally succeeds as soon as these conditions are
        # met, even though there might be a failure in downloading the existing file
        # or uploading a new one. However, there is an exception: if a file has been
        # written, then closed, and is now being reopened, then we have to delay the
        # open until the previous upload/publish has completed. This is necessary
        # because sshfs does not wait for the result of an FXF_CLOSE message before
        # reporting to the client that a file has been closed. It applies both to
        # mutable files, and to directory entries linked to an immutable file.
        #
        # Note that the permission checks below are for more precise error reporting on
        # the open call; later operations would fail even if we did not make these checks.

        d = delay or defer.succeed(None)
        d.addCallback(lambda ign: self._get_root(path))
        def _got_root( (root, path) ):
            if root.is_unknown():
                raise SFTPError(FX_PERMISSION_DENIED,
                                "cannot open an unknown cap (or child of an unknown object). "
                                "Upgrading the gateway to a later Tahoe-LAFS version may help")
            if not path:
                # case 1
                if noisy: self.log("case 1: root = %r, path[:-1] = %r" % (root, path[:-1]), level=NOISY)
                if not IFileNode.providedBy(root):
                    raise SFTPError(FX_PERMISSION_DENIED,
                                    "cannot open a directory cap")
                if (flags & FXF_WRITE) and root.is_readonly():
                    raise SFTPError(FX_PERMISSION_DENIED,
                                    "cannot write to a non-writeable filecap without a parent directory")
                if flags & FXF_EXCL:
                    raise SFTPError(FX_FAILURE,
                                    "cannot create a file exclusively when it already exists")

                # The file does not need to be added to all_heisenfiles, because it is not
                # associated with a directory entry that needs to be updated.

                metadata = update_metadata(None, desired_metadata, time())

                # We have to decide what to pass for the 'parent_readonly' argument to _no_write,
                # given that we don't actually have a parent. This only affects the permissions
                # reported by a getAttrs on this file handle in the case of an immutable file.
                # We choose 'parent_readonly=True' since that will cause the permissions to be
                # reported as r--r--r--, which is appropriate because an immutable file can't be
                # written via this path.

                metadata['no-write'] = _no_write(True, root)
                return self._make_file(file, userpath, flags, filenode=root, metadata=metadata)
            else:
                # case 2
                childname = path[-1]

                if noisy: self.log("case 2: root = %r, childname = %r, desired_metadata = %r, path[:-1] = %r" %
                                   (root, childname, desired_metadata, path[:-1]), level=NOISY)
                d2 = root.get_child_at_path(path[:-1])
                def _got_parent(parent):
                    if noisy: self.log("_got_parent(%r)" % (parent,), level=NOISY)
                    if parent.is_unknown():
                        raise SFTPError(FX_PERMISSION_DENIED,
                                        "cannot open a child of an unknown object. "
                                        "Upgrading the gateway to a later Tahoe-LAFS version may help")

                    parent_readonly = parent.is_readonly()
                    d3 = defer.succeed(None)
                    if flags & FXF_EXCL:
                        # FXF_EXCL means that the link to the file (not the file itself) must
                        # be created atomically wrt updates by this storage client.
                        # That is, we need to create the link before returning success to the
                        # SFTP open request (and not just on close, as would normally be the
                        # case). We make the link initially point to a zero-length LIT file,
                        # which is consistent with what might happen on a POSIX filesystem.

                        if parent_readonly:
                            raise SFTPError(FX_FAILURE,
                                            "cannot create a file exclusively when the parent directory is read-only")

                        # 'overwrite=False' ensures failure if the link already exists.
                        # FIXME: should use a single call to set_uri and return (child, metadata) (#1035)

                        zero_length_lit = "URI:LIT:"
                        if noisy: self.log("%r.set_uri(%r, None, readcap=%r, overwrite=False)" %
                                           (parent, zero_length_lit, childname), level=NOISY)
                        d3.addCallback(lambda ign: parent.set_uri(childname, None, readcap=zero_length_lit,
                                                                  metadata=desired_metadata, overwrite=False))
                        def _seturi_done(child):
                            if noisy: self.log("%r.get_metadata_for(%r)" % (parent, childname), level=NOISY)
                            d4 = parent.get_metadata_for(childname)
                            d4.addCallback(lambda metadata: (child, metadata))
                            return d4
                        d3.addCallback(_seturi_done)
                    else:
                        if noisy: self.log("%r.get_child_and_metadata(%r)" % (parent, childname), level=NOISY)
                        d3.addCallback(lambda ign: parent.get_child_and_metadata(childname))

                    def _got_child( (filenode, current_metadata) ):
                        if noisy: self.log("_got_child( (%r, %r) )" % (filenode, current_metadata), level=NOISY)

                        metadata = update_metadata(current_metadata, desired_metadata, time())

                        # Ignore the permissions of the desired_metadata in an open call. The permissions
                        # can only be set by setAttrs.
                        metadata['no-write'] = _no_write(parent_readonly, filenode, current_metadata)

                        if filenode.is_unknown():
                            raise SFTPError(FX_PERMISSION_DENIED,
                                            "cannot open an unknown cap. Upgrading the gateway "
                                            "to a later Tahoe-LAFS version may help")
                        if not IFileNode.providedBy(filenode):
                            raise SFTPError(FX_PERMISSION_DENIED,
                                            "cannot open a directory as if it were a file")
                        if (flags & FXF_WRITE) and metadata['no-write']:
                            raise SFTPError(FX_PERMISSION_DENIED,
                                            "cannot open a non-writeable file for writing")

                        return self._make_file(file, userpath, flags, parent=parent, childname=childname,
                                               filenode=filenode, metadata=metadata)
                    def _no_child(f):
                        if noisy: self.log("_no_child(%r)" % (f,), level=NOISY)
                        f.trap(NoSuchChildError)

                        if not (flags & FXF_CREAT):
                            raise SFTPError(FX_NO_SUCH_FILE,
                                            "the file does not exist, and was not opened with the creation (CREAT) flag")
                        if parent_readonly:
                            raise SFTPError(FX_PERMISSION_DENIED,
                                            "cannot create a file when the parent directory is read-only")

                        return self._make_file(file, userpath, flags, parent=parent, childname=childname)
                    d3.addCallbacks(_got_child, _no_child)
                    return d3

                d2.addCallback(_got_parent)
                return d2

        d.addCallback(_got_root)
        def _remove_on_error(err):
            if file:
                self._remove_heisenfile(userpath, None, None, file)
            return err
        d.addErrback(_remove_on_error)
        d.addBoth(_convert_error, request)
        return d

    def renameFile(self, from_pathstring, to_pathstring, overwrite=False):
        request = ".renameFile(%r, %r)" % (from_pathstring, to_pathstring)
        self.log(request, level=OPERATIONAL)

        from_path = self._path_from_string(from_pathstring)
        to_path = self._path_from_string(to_pathstring)
        from_userpath = self._path_to_utf8(from_path)
        to_userpath = self._path_to_utf8(to_path)

        # the target directory must already exist
        d = deferredutil.gatherResults([self._get_parent_or_node(from_path),
                                        self._get_parent_or_node(to_path)])
        def _got( (from_pair, to_pair) ):
            if noisy: self.log("_got( (%r, %r) ) in .renameFile(%r, %r, overwrite=%r)" %
                               (from_pair, to_pair, from_pathstring, to_pathstring, overwrite), level=NOISY)
            (from_parent, from_childname) = from_pair
            (to_parent, to_childname) = to_pair

            if from_childname is None:
                raise SFTPError(FX_NO_SUCH_FILE, "cannot rename a source object specified by URI")
            if to_childname is None:
                raise SFTPError(FX_NO_SUCH_FILE, "cannot rename to a destination specified by URI")

            # <http://tools.ietf.org/html/draft-ietf-secsh-filexfer-02#section-6.5>
            # "It is an error if there already exists a file with the name specified
            #  by newpath."
            # OpenSSH's SFTP server returns FX_PERMISSION_DENIED for this error.
            #
            # For the standard SSH_FXP_RENAME operation, overwrite=False.
            # We also support the posix-rename@openssh.com extension, which uses overwrite=True.

            d2 = defer.succeed(None)
            if not overwrite:
                d2.addCallback(lambda ign: to_parent.get(to_childname))
                def _expect_fail(res):
                    if not isinstance(res, Failure):
                        raise SFTPError(FX_PERMISSION_DENIED, "cannot rename to existing path " + to_userpath)

                    # It is OK if we fail for errors other than NoSuchChildError, since that probably
                    # indicates some problem accessing the destination directory.
                    res.trap(NoSuchChildError)
                d2.addBoth(_expect_fail)

            # If there are heisenfiles to be written at the 'from' direntry, then ensure
            # they will now be written at the 'to' direntry instead.
            d2.addCallback(lambda ign:
                           self._rename_heisenfiles(from_userpath, from_parent, from_childname,
                                                    to_userpath, to_parent, to_childname, overwrite=overwrite))

            def _move(renamed):
                # FIXME: use move_child_to_path to avoid possible data loss due to #943
                #d3 = from_parent.move_child_to_path(from_childname, to_root, to_path, overwrite=overwrite)

                d3 = from_parent.move_child_to(from_childname, to_parent, to_childname, overwrite=overwrite)
                def _check(err):
                    if noisy: self.log("_check(%r) in .renameFile(%r, %r, overwrite=%r)" %
                                       (err, from_pathstring, to_pathstring, overwrite), level=NOISY)

                    if not isinstance(err, Failure) or (renamed and err.check(NoSuchChildError)):
                        return None
                    if not overwrite and err.check(ExistingChildError):
                        raise SFTPError(FX_PERMISSION_DENIED, "cannot rename to existing path " + to_userpath)

                    return err
                d3.addBoth(_check)
                return d3
            d2.addCallback(_move)
            return d2
        d.addCallback(_got)
        d.addBoth(_convert_error, request)
        return d

    def makeDirectory(self, pathstring, attrs):
        request = ".makeDirectory(%r, %r)" % (pathstring, attrs)
        self.log(request, level=OPERATIONAL)

        path = self._path_from_string(pathstring)
        metadata = _attrs_to_metadata(attrs)
        if 'no-write' in metadata:
            def _denied(): raise SFTPError(FX_PERMISSION_DENIED, "cannot create a directory that is initially read-only")
            return defer.execute(_denied)

        d = self._get_root(path)
        d.addCallback(lambda (root, path):
                      self._get_or_create_directories(root, path, metadata))
        d.addBoth(_convert_error, request)
        return d

    def _get_or_create_directories(self, node, path, metadata):
        if not IDirectoryNode.providedBy(node):
            # TODO: provide the name of the blocking file in the error message.
            def _blocked(): raise SFTPError(FX_FAILURE, "cannot create directory because there "
                                                        "is a file in the way") # close enough
            return defer.execute(_blocked)

        if not path:
            return defer.succeed(node)
        d = node.get(path[0])
        def _maybe_create(f):
            f.trap(NoSuchChildError)
            return node.create_subdirectory(path[0])
        d.addErrback(_maybe_create)
        d.addCallback(self._get_or_create_directories, path[1:], metadata)
        return d

    def removeFile(self, pathstring):
        request = ".removeFile(%r)" % (pathstring,)
        self.log(request, level=OPERATIONAL)

        path = self._path_from_string(pathstring)
        d = self._remove_object(path, must_be_file=True)
        d.addBoth(_convert_error, request)
        return d

    def removeDirectory(self, pathstring):
        request = ".removeDirectory(%r)" % (pathstring,)
        self.log(request, level=OPERATIONAL)

        path = self._path_from_string(pathstring)
        d = self._remove_object(path, must_be_directory=True)
        d.addBoth(_convert_error, request)
        return d

    def _remove_object(self, path, must_be_directory=False, must_be_file=False):
        userpath = self._path_to_utf8(path)
        d = self._get_parent_or_node(path)
        def _got_parent( (parent, childname) ):
            if childname is None:
                raise SFTPError(FX_NO_SUCH_FILE, "cannot remove an object specified by URI")

            direntry = _direntry_for(parent, childname)
            d2 = defer.succeed(False)
            if not must_be_directory:
                d2.addCallback(lambda ign: self._abandon_any_heisenfiles(userpath, direntry))

            d2.addCallback(lambda abandoned:
                           parent.delete(childname, must_exist=not abandoned,
                                         must_be_directory=must_be_directory, must_be_file=must_be_file))
            return d2
        d.addCallback(_got_parent)
        return d

    def openDirectory(self, pathstring):
        request = ".openDirectory(%r)" % (pathstring,)
        self.log(request, level=OPERATIONAL)

        path = self._path_from_string(pathstring)
        d = self._get_parent_or_node(path)
        def _got_parent_or_node( (parent_or_node, childname) ):
            if noisy: self.log("_got_parent_or_node( (%r, %r) ) in openDirectory(%r)" %
                               (parent_or_node, childname, pathstring), level=NOISY)
            if childname is None:
                return parent_or_node
            else:
                return parent_or_node.get(childname)
        d.addCallback(_got_parent_or_node)
        def _list(dirnode):
            if dirnode.is_unknown():
                raise SFTPError(FX_PERMISSION_DENIED,
                                "cannot list an unknown cap as a directory. Upgrading the gateway "
                                "to a later Tahoe-LAFS version may help")
            if not IDirectoryNode.providedBy(dirnode):
                raise SFTPError(FX_PERMISSION_DENIED,
                                "cannot list a file as if it were a directory")

            d2 = dirnode.list()
            def _render(children):
                parent_readonly = dirnode.is_readonly()
                results = []
                for filename, (child, metadata) in children.iteritems():
                    # The file size may be cached or absent.
                    metadata['no-write'] = _no_write(parent_readonly, child, metadata)
                    attrs = _populate_attrs(child, metadata)
                    filename_utf8 = filename.encode('utf-8')
                    longname = _lsLine(filename_utf8, attrs)
                    results.append( (filename_utf8, longname, attrs) )
                return StoppableList(results)
            d2.addCallback(_render)
            return d2
        d.addCallback(_list)
        d.addBoth(_convert_error, request)
        return d

    def getAttrs(self, pathstring, followLinks):
        request = ".getAttrs(%r, followLinks=%r)" % (pathstring, followLinks)
        self.log(request, level=OPERATIONAL)

        # When asked about a specific file, report its current size.
        # TODO: the modification time for a mutable file should be
        # reported as the update time of the best version. But that
        # information isn't currently stored in mutable shares, I think.

        path = self._path_from_string(pathstring)
        userpath = self._path_to_utf8(path)
        d = self._get_parent_or_node(path)
        def _got_parent_or_node( (parent_or_node, childname) ):
            if noisy: self.log("_got_parent_or_node( (%r, %r) )" % (parent_or_node, childname), level=NOISY)

            # Some clients will incorrectly try to get the attributes
            # of a file immediately after opening it, before it has been put
            # into the all_heisenfiles table. This is a race condition bug in
            # the client, but we handle it anyway by calling .sync() on all
            # files matching either the path or the direntry.

            direntry = _direntry_for(parent_or_node, childname)
            d2 = self._sync_heisenfiles(userpath, direntry)

            if childname is None:
                node = parent_or_node
                d2.addCallback(lambda ign: node.get_current_size())
                d2.addCallback(lambda size:
                               _populate_attrs(node, {'no-write': node.is_unknown() or node.is_readonly()}, size=size))
            else:
                parent = parent_or_node
                d2.addCallback(lambda ign: parent.get_child_and_metadata_at_path([childname]))
                def _got( (child, metadata) ):
                    if noisy: self.log("_got( (%r, %r) )" % (child, metadata), level=NOISY)
                    _assert(IDirectoryNode.providedBy(parent), parent=parent)
                    metadata['no-write'] = _no_write(parent.is_readonly(), child, metadata)
                    d3 = child.get_current_size()
                    d3.addCallback(lambda size: _populate_attrs(child, metadata, size=size))
                    return d3
                def _nosuch(err):
                    if noisy: self.log("_nosuch(%r)" % (err,), level=NOISY)
                    err.trap(NoSuchChildError)
                    if noisy: self.log("checking open files:\nself._heisenfiles = %r\nall_heisenfiles = %r\ndirentry=%r" %
                                       (self._heisenfiles, all_heisenfiles, direntry), level=NOISY)
                    if direntry in all_heisenfiles:
                        files = all_heisenfiles[direntry]
                        if len(files) == 0:  # pragma: no cover
                            return err
                        # use the heisenfile that was most recently opened
                        return files[-1].getAttrs()
                    return err
                d2.addCallbacks(_got, _nosuch)
            return d2
        d.addCallback(_got_parent_or_node)
        d.addBoth(_convert_error, request)
        return d

    def setAttrs(self, pathstring, attrs):
        request = ".setAttrs(%r, %r)" % (pathstring, attrs)
        self.log(request, level=OPERATIONAL)

        if "size" in attrs:
            # this would require us to download and re-upload the truncated/extended
            # file contents
            def _unsupported(): raise SFTPError(FX_OP_UNSUPPORTED, "setAttrs wth size attribute unsupported")
            return defer.execute(_unsupported)

        path = self._path_from_string(pathstring)
        userpath = self._path_to_utf8(path)
        d = self._get_parent_or_node(path)
        def _got_parent_or_node( (parent_or_node, childname) ):
            if noisy: self.log("_got_parent_or_node( (%r, %r) )" % (parent_or_node, childname), level=NOISY)

            direntry = _direntry_for(parent_or_node, childname)
            d2 = self._update_attrs_for_heisenfiles(userpath, direntry, attrs)

            def _update(updated_heisenfiles):
                if childname is None:
                    if updated_heisenfiles:
                        return None
                    raise SFTPError(FX_NO_SUCH_FILE, userpath)
                else:
                    desired_metadata = _attrs_to_metadata(attrs)
                    if noisy: self.log("desired_metadata = %r" % (desired_metadata,), level=NOISY)

                    d3 = parent_or_node.set_metadata_for(childname, desired_metadata)
                    def _nosuch(err):
                        if updated_heisenfiles:
                            err.trap(NoSuchChildError)
                        else:
                            return err
                    d3.addErrback(_nosuch)
                    return d3
            d2.addCallback(_update)
            d2.addCallback(lambda ign: None)
            return d2
        d.addCallback(_got_parent_or_node)
        d.addBoth(_convert_error, request)
        return d

    def readLink(self, pathstring):
        self.log(".readLink(%r)" % (pathstring,), level=OPERATIONAL)

        def _unsupported(): raise SFTPError(FX_OP_UNSUPPORTED, "readLink")
        return defer.execute(_unsupported)

    def makeLink(self, linkPathstring, targetPathstring):
        self.log(".makeLink(%r, %r)" % (linkPathstring, targetPathstring), level=OPERATIONAL)

        # If this is implemented, note the reversal of arguments described in point 7 of
        # <http://www.openbsd.org/cgi-bin/cvsweb/src/usr.bin/ssh/PROTOCOL?rev=1.15>.

        def _unsupported(): raise SFTPError(FX_OP_UNSUPPORTED, "makeLink")
        return defer.execute(_unsupported)

    def extendedRequest(self, extensionName, extensionData):
        self.log(".extendedRequest(%r, <data of length %r>)" % (extensionName, len(extensionData)), level=OPERATIONAL)

        # We implement the three main OpenSSH SFTP extensions; see
        # <http://www.openbsd.org/cgi-bin/cvsweb/src/usr.bin/ssh/PROTOCOL?rev=1.15>

        if extensionName == 'posix-rename@openssh.com':
            def _bad(): raise SFTPError(FX_BAD_MESSAGE, "could not parse posix-rename@openssh.com request")

            if 4 > len(extensionData): return defer.execute(_bad)
            (fromPathLen,) = struct.unpack('>L', extensionData[0:4])
            if 8 + fromPathLen > len(extensionData): return defer.execute(_bad)

            (toPathLen,) = struct.unpack('>L', extensionData[(4 + fromPathLen):(8 + fromPathLen)])
            if 8 + fromPathLen + toPathLen != len(extensionData): return defer.execute(_bad)

            fromPathstring = extensionData[4:(4 + fromPathLen)]
            toPathstring = extensionData[(8 + fromPathLen):]
            d = self.renameFile(fromPathstring, toPathstring, overwrite=True)

            # Twisted conch assumes that the response from an extended request is either
            # an error, or an FXP_EXTENDED_REPLY. But it happens to do the right thing
            # (respond with an FXP_STATUS message) if we return a Failure with code FX_OK.
            def _succeeded(ign):
                raise SFTPError(FX_OK, "request succeeded")
            d.addCallback(_succeeded)
            return d

        if extensionName == 'statvfs@openssh.com' or extensionName == 'fstatvfs@openssh.com':
            # f_bsize and f_frsize should be the same to avoid a bug in 'df'
            return defer.succeed(struct.pack('>11Q',
                1024,         # uint64  f_bsize     /* file system block size */
                1024,         # uint64  f_frsize    /* fundamental fs block size */
                628318530,    # uint64  f_blocks    /* number of blocks (unit f_frsize) */
                314159265,    # uint64  f_bfree     /* free blocks in file system */
                314159265,    # uint64  f_bavail    /* free blocks for non-root */
                200000000,    # uint64  f_files     /* total file inodes */
                100000000,    # uint64  f_ffree     /* free file inodes */
                100000000,    # uint64  f_favail    /* free file inodes for non-root */
                0x1AF5,       # uint64  f_fsid      /* file system id */
                2,            # uint64  f_flag      /* bit mask = ST_NOSUID; not ST_RDONLY */
                65535,        # uint64  f_namemax   /* maximum filename length */
                ))

        def _unsupported(): raise SFTPError(FX_OP_UNSUPPORTED, "unsupported %r request <data of length %r>" %
                                                               (extensionName, len(extensionData)))
        return defer.execute(_unsupported)

    def realPath(self, pathstring):
        self.log(".realPath(%r)" % (pathstring,), level=OPERATIONAL)

        return self._path_to_utf8(self._path_from_string(pathstring))

    def _path_to_utf8(self, path):
        return (u"/" + u"/".join(path)).encode('utf-8')

    def _path_from_string(self, pathstring):
        if noisy: self.log("CONVERT %r" % (pathstring,), level=NOISY)

        _assert(isinstance(pathstring, str), pathstring=pathstring)

        # The home directory is the root directory.
        pathstring = pathstring.strip("/")
        if pathstring == "" or pathstring == ".":
            path_utf8 = []
        else:
            path_utf8 = pathstring.split("/")

        # <http://tools.ietf.org/html/draft-ietf-secsh-filexfer-02#section-6.2>
        # "Servers SHOULD interpret a path name component ".." as referring to
        #  the parent directory, and "." as referring to the current directory."
        path = []
        for p_utf8 in path_utf8:
            if p_utf8 == "..":
                # ignore excess .. components at the root
                if len(path) > 0:
                    path = path[:-1]
            elif p_utf8 != ".":
                try:
                    p = p_utf8.decode('utf-8', 'strict')
                except UnicodeError:
                    raise SFTPError(FX_NO_SUCH_FILE, "path could not be decoded as UTF-8")
                path.append(p)

        if noisy: self.log(" PATH %r" % (path,), level=NOISY)
        return path

    def _get_root(self, path):
        # return Deferred (root, remaining_path)
        d = defer.succeed(None)
        if path and path[0] == u"uri":
            d.addCallback(lambda ign: self._client.create_node_from_uri(path[1].encode('utf-8')))
            d.addCallback(lambda root: (root, path[2:]))
        else:
            d.addCallback(lambda ign: (self._root, path))
        return d

    def _get_parent_or_node(self, path):
        # return Deferred (parent, childname) or (node, None)
        d = self._get_root(path)
        def _got_root( (root, remaining_path) ):
            if not remaining_path:
                return (root, None)
            else:
                d2 = root.get_child_at_path(remaining_path[:-1])
                d2.addCallback(lambda parent: (parent, remaining_path[-1]))
                return d2
        d.addCallback(_got_root)
        return d


class FakeTransport:
    implements(ITransport)
    def write(self, data):
        logmsg("FakeTransport.write(<data of length %r>)" % (len(data),), level=NOISY)

    def writeSequence(self, data):
        logmsg("FakeTransport.writeSequence(...)", level=NOISY)

    def loseConnection(self):
        logmsg("FakeTransport.loseConnection()", level=NOISY)

    # getPeer and getHost can just raise errors, since we don't know what to return


class ShellSession(PrefixingLogMixin):
    implements(ISession)
    def __init__(self, userHandler):
        PrefixingLogMixin.__init__(self, facility="tahoe.sftp")
        if noisy: self.log(".__init__(%r)" % (userHandler), level=NOISY)

    def getPty(self, terminal, windowSize, attrs):
        self.log(".getPty(%r, %r, %r)" % (terminal, windowSize, attrs), level=OPERATIONAL)

    def openShell(self, protocol):
        self.log(".openShell(%r)" % (protocol,), level=OPERATIONAL)
        if hasattr(protocol, 'transport') and protocol.transport is None:
            protocol.transport = FakeTransport()  # work around Twisted bug

        return self._unsupported(protocol)

    def execCommand(self, protocol, cmd):
        self.log(".execCommand(%r, %r)" % (protocol, cmd), level=OPERATIONAL)
        if hasattr(protocol, 'transport') and protocol.transport is None:
            protocol.transport = FakeTransport()  # work around Twisted bug

        d = defer.succeed(None)
        if cmd == "df -P -k /":
            d.addCallback(lambda ign: protocol.write(
                          "Filesystem         1024-blocks      Used Available Capacity Mounted on\r\n"
                          "tahoe                628318530 314159265 314159265      50% /\r\n"))
            d.addCallback(lambda ign: protocol.processEnded(Reason(ProcessDone(None))))
        else:
            d.addCallback(lambda ign: self._unsupported(protocol))
        return d

    def _unsupported(self, protocol):
        d = defer.succeed(None)
        d.addCallback(lambda ign: protocol.errReceived(
                      "This server supports only the SFTP protocol. It does not support SCP,\r\n"
                      "interactive shell sessions, or commands other than one needed by sshfs.\r\n"))
        d.addCallback(lambda ign: protocol.processEnded(Reason(ProcessTerminated(exitCode=1))))
        return d

    def windowChanged(self, newWindowSize):
        self.log(".windowChanged(%r)" % (newWindowSize,), level=OPERATIONAL)

    def eofReceived(self):
        self.log(".eofReceived()", level=OPERATIONAL)

    def closed(self):
        self.log(".closed()", level=OPERATIONAL)


# If you have an SFTPUserHandler and want something that provides ISession, you get
# ShellSession(userHandler).
# We use adaptation because this must be a different object to the SFTPUserHandler.
components.registerAdapter(ShellSession, SFTPUserHandler, ISession)


from allmydata.frontends.auth import AccountURLChecker, AccountFileChecker, NeedRootcapLookupScheme

class Dispatcher:
    implements(portal.IRealm)
    def __init__(self, client):
        self._client = client

    def requestAvatar(self, avatarID, mind, interface):
        _assert(interface == IConchUser, interface=interface)
        rootnode = self._client.create_node_from_uri(avatarID.rootcap)
        handler = SFTPUserHandler(self._client, rootnode, avatarID.username)
        return (interface, handler, handler.logout)


class SFTPServer(service.MultiService):
    def __init__(self, client, accountfile, accounturl,
                 sftp_portstr, pubkey_file, privkey_file):
        service.MultiService.__init__(self)

        r = Dispatcher(client)
        p = portal.Portal(r)

        if accountfile:
            c = AccountFileChecker(self, accountfile)
            p.registerChecker(c)
        if accounturl:
            c = AccountURLChecker(self, accounturl)
            p.registerChecker(c)
        if not accountfile and not accounturl:
            # we could leave this anonymous, with just the /uri/CAP form
            raise NeedRootcapLookupScheme("must provide an account file or URL")

        pubkey = keys.Key.fromFile(pubkey_file)
        privkey = keys.Key.fromFile(privkey_file)
        class SSHFactory(factory.SSHFactory):
            publicKeys = {pubkey.sshType(): pubkey}
            privateKeys = {privkey.sshType(): privkey}
            def getPrimes(self):
                try:
                    # if present, this enables diffie-hellman-group-exchange
                    return primes.parseModuliFile("/etc/ssh/moduli")
                except IOError:
                    return None

        f = SSHFactory()
        f.portal = p

        s = strports.service(sftp_portstr, f)
        s.setServiceParent(self)
