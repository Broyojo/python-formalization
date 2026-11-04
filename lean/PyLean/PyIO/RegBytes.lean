import PyLean.Registry
import PyLean.PyIO.BytesShareProps
import PyLean.PyIO.BytesCallbacks
import PyLean.PyIO.BytesState

/-! Registry entries for `io.BytesIO`'s shared buffer (`PyIO/BytesShare.lean`,
`PyIO/BytesShareProps.lean`). -/

namespace PyLean.PyIO

open PyLean.Registry

def bytesShareEntries : List Entry := [
  { id := "pyio-bytesio-held-immutable", pyFile := "Modules/_io/bytesio.c"
    pyFns := ["unshare_buffer_lock_held", "resize_buffer_lock_held", "resize_unshared_buffer_lock_held",
      "write_bytes_lock_held", "_io_BytesIO_write_impl", "_io_BytesIO_getvalue_impl", "read_bytes_lock_held",
      "_io_BytesIO_read_impl", "_io_BytesIO_readline_impl", "_io_BytesIO_truncate_impl",
      "_io_BytesIO_getbuffer_impl", "bytesiobuf_getbuffer_lock_held", "bytesiobuf_getbuffer",
      "bytesiobuf_releasebuffer", "_io_BytesIO_close_impl"]
    statement := "In every state a program can reach (any initial value, kept or dropped, and any sequence of write, getvalue, read, readline, seek, tell, truncate, getbuffer, stores through and reads of views, release, close, hash, is and del), no io.BytesIO operation changes the contents of a bytes object the program holds."
    source := "invariant: bytes are immutable; the copy-on-write comment bytesio.c:40-45 and the unshares at :214-217, :264-269, :1243-1246"
    status := .proven, prop := ``Share.BytesIOHeldImmutable, thm := some ``Share.bytesIOHeldImmutable_proven
    notes := "Model: PyIO/BytesShare.lean, a heap of bytes objects with contents and cached hash, self->buf as a reference, getbuffer views over (object, length), and the program's references; SHARED_BUF is 'held by the program' or a singleton. An unshare that returned without copying, an export that skipped it, or a zero-copy getvalue/read that ignored exports would each let a write or a view store change a held object. Smoke-tested on 3.15.2: 0 changes over 330594 (object, operation) pairs of the share difftest generator. Scope: default build, whole memoryviews only." },
  { id := "pyio-bytesio-zero-copy", pyFile := "Modules/_io/bytesio.c"
    pyFns := ["_io_BytesIO_getvalue_impl", "read_bytes_lock_held", "_io_BytesIO_read_impl",
      "unshare_buffer_lock_held", "resize_unshared_buffer_lock_held"]
    statement := "With no live view and at least two bytes, getvalue() returns io.BytesIO's buffer object itself, sized to the contents; with a view, or at most one byte, it returns a new object (or a singleton) and the buffer stays. read() of the whole buffer from position 0 returns the buffer object itself with no view and a new object with one. Every result holds the contents."
    source := "the bodies bytesio.c:413-433, :468-494; invariant: getvalue returns the contents (Doc/library/io.rst BytesIO.getvalue)"
    status := .proven, prop := ``Share.BytesIOZeroCopy, thm := some ``Share.bytesIOZeroCopy_proven
    notes := "Hypotheses: a reachable state (Share.Inv), string_size within the allocation and below the allocation bound. Python-visible as identity: b.getvalue() is b.getvalue() is True without a view and False with one (smoke-tested on 3.15.2)." },
  { id := "pyio-bytesio-getbuffer-live", pyFile := "Modules/_io/bytesio.c"
    pyFns := ["_io_BytesIO_getbuffer_impl", "bytesiobuf_getbuffer_lock_held", "bytesiobuf_getbuffer",
      "bytesiobuf_releasebuffer", "check_exports", "_io_BytesIO_close_impl", "write_bytes_lock_held",
      "_io_BytesIO_truncate_impl"]
    statement := "On every reachable open io.BytesIO, getbuffer() returns a view that adds one export, reads the contents, and writes through: after view[i] = x for any i below the size and byte x, getvalue() is the contents with byte i replaced; view[i] = x past the end raises IndexError; while the view lives every write, truncate and close raises BufferError; releasing it gives the export back."
    source := "Doc/library/io.rst:741-753 (BytesIO.getbuffer: 'a readable and writable view over the contents of the buffer without copying them ... mutating the view will transparently update the contents'; 'As long as the view exists, the BytesIO object cannot be resized or closed')"
    status := .proven, prop := ``Share.BytesIOGetbufferLive, thm := some ``Share.bytesIOGetbufferLive_proven
    notes := "A getbuffer that returned a detached copy fails the write-through clause; one that skipped the unshare fails pyio-bytesio-held-immutable. bytesiobuf_getbuffer's view == NULL BufferError (:1259-1263) cannot be reached from Python: PyMemoryView_FromObject always passes a view. Hypotheses: a reachable state, size within the allocation and below the allocation bound." },
  { id := "pyio-bytesio-sizeof", pyFile := "Modules/_io/bytesio.c"
    pyFns := ["bytesio_sizeof_lock_held", "bytesio_sizeof"]
    statement := "io.BytesIO.__sizeof__() is 64 (the object alone) when the stream is closed or its buffer is shared with the program or a singleton, and otherwise 64 + 33 + the buffer's whole allocation, over-allocation included, which covers the contents."
    source := "the body bytesio.c:1117-1131 with Python/sysmodule.c:1932-1980; invariant: __sizeof__ counts what the object owns"
    status := .proven, prop := ``Share.BytesIOSizeof, thm := some ``Share.bytesIOSizeof_proven
    notes := "The share difftest compares __sizeof__() after every kind of operation (60000/60000 on seeds 1-3), which also pins the over-allocation policy of resize_buffer_lock_held (Share.newAlloc) byte for byte. A constant 64, a size that always counted the buffer, or one that counted string_size instead of the allocation fails. Hypothesis: string_size within the allocation (type invariant)." },
  { id := "pyio-bytesio-hash-consistent", pyFile := "Modules/_io/bytesio.c"
    pyFns := ["_io_BytesIO_getvalue_impl", "write_bytes_lock_held", "_io_BytesIO_write_impl",
      "resize_buffer_lock_held", "unshare_buffer_lock_held", "resize_unshared_buffer_lock_held",
      "_io_BytesIO_seek_impl"]
    statement := "Every bytes object a program gets from io.BytesIO hashes as its contents: for every initial value, operation sequence and kept object x, hash(x) == hash(bytes(bytearray(x)))."
    source := "invariant: a hashable object's hash never changes and equal objects hash equal (Doc/reference/datamodel.rst object.__hash__); bytes are immutable"
    status := .refuted, prop := ``Share.BytesIOHashConsistent, thm := some ``Share.bytesIOHashConsistent_refuted
    bug := some "pyio-bytesio-stale-shared-hash"
    notes := "b = BytesIO(); b.write(b'abcd'); hash(b.getvalue()); b.seek(0); b.write(b'efgh'); v = b.getvalue(): v == b'efgh' and v not in {b'efgh'} on 3.15.2 (SHARED_BUF tests only the reference count, bytesio.c:81); fixed on main by HASHED_BUF. Duplicate of gh-160181 (closed)." }
]

def bytesCallbackEntries : List Entry := [
  { id := "pyio-bytesio-write-callback", pyFile := "Modules/_io/bytesio.c"
    pyFns := ["write_bytes_lock_held", "_io_BytesIO_write_impl", "check_closed", "check_exports", "BytesIO.write"]
    statement := "write(x) where x.__buffer__ runs arbitrary stream actions (close, getbuffer, tell, seek, write) and then returns a buffer or raises: in both twins a raising __buffer__ propagates with its actions' effects kept and nothing written; the closed check (C ValueError('I/O operation on closed file.'), _pyio ValueError('write to closed file')), C's export check (BufferError) and the write position all come from the state the actions left; otherwise the data is written exactly as write(bytes) writes it on that state."
    source := "the bodies bytesio.c:236-297 (PyObject_GetBuffer at :242 before the checks at :246 and the position at :257) and _pyio.py:955-973 (memoryview(b) at :958 before :959 and :967); invariant: no operation on a closed or exported buffer"
    status := .proven, prop := ``BytesIOWriteCallback, thm := some ``bytesIOWriteCallback_proven
    notes := "A write that checked closed or read pos before asking for the buffer fails it. The actions are the Hook type with exceptions swallowed; difftest/pyio_callback_diff.py runs them through a class with __buffer__." },
  { id := "pyio-bytesio-writelines-iter", pyFile := "Modules/_io/bytesio.c"
    pyFns := ["_io_BytesIO_writelines_impl", "IOBase.writelines"]
    statement := "writelines(it) on every BytesIO and every iterator (whose __next__ may act on the stream and then yield an item or raise) is next(it) and write(item) one after another, stopping at the first exception, in both twins: an exception from __next__ propagates, a refused item (str, non-buffer, raising __buffer__) or a stream closed or exported by an earlier callback stops it with write's exception; a non-iterable raises TypeError(\"'T' object is not iterable\") and changes nothing; a closed stream raises the closed-file ValueError before iter() is called. For plain bytes items it is the list-based model of pyio-bytesio-writelines."
    source := "bytesio.c:845-846 ('This is equivalent to calling write() for each element'), Doc/library/io.rst IOBase.writelines; the bodies bytesio.c:850-876 and _pyio.py:583-591"
    status := .proven, prop := ``BytesIOWritelinesIter, thm := some ``bytesIOWritelinesIter_proven
    notes := "A writelines that swallowed the iterator's exception, kept going after a failed write, or called iter() before the closed check fails it. Smoke-tested on 3.15.2: writelines(it) and the next/write loop gave the same outcome, contents, position and closed flag on 10000 generated iterators, both twins." },
  { id := "pyio-bytesio-reinit-obj", pyFile := "Modules/_io/bytesio.c"
    pyFns := ["_io_BytesIO___init___impl", "BytesIO.__init__"]
    statement := "__init__(v) on an io.BytesIO with no view, for a bytes-like v that is not an exact bytes: on an open stream the contents become v, the position 0 and the stream stays open; on a closed one it raises the closed-file ValueError after emptying it, even for an empty v. With a __buffer__ that acts on the stream, C runs it on the reset stream, writes v where it left the position and rewinds; _pyio runs it on the old stream and then replaces the buffer and position, closed or not, dropping old views."
    source := "the bodies bytesio.c:1084-1114 (write then self->pos = 0 at :1103-1110) and _pyio.py:884-894"
    status := .proven, prop := ``BytesIOReinitObj, thm := some ``bytesIOReinitObj_proven
    notes := "An __init__ that forgot self->pos = 0 fails the open-stream clause. _pyio's bytearray += turns a raising __buffer__ into TypeError(\"can't concat Buf to bytearray\"); __init__(None) is the no-value path in both (bytesio.c:1097, _pyio.py:890). Smoke-tested on 3.15.2 (scratch probes, and the callback difftest's reinititem op)." },
  { id := "pyio-bytesio-seek-spec", pyFile := "Modules/_io/bytesio.c"
    pyFns := ["_io_BytesIO_seek_impl"]
    statement := "For every io.BytesIO whose position and size fit Py_ssize_t and every pos and whence in C range, seek raises OverflowError('new position too large') exactly when pos + position (whence 1) or pos + size (whence 2) exceeds sys.maxsize, and otherwise moves to that sum (pos for whence 0) clamped at 0 and returns it; the closed check, the negative whence-0 refusal and the bad whence refusal come in source order."
    source := "the body bytesio.c:774-815 (guards :789-793, :797-801); invariant: no silent wraparound of a Py_ssize_t position"
    status := .proven, prop := ``BytesIOSeekSpec, thm := some ``bytesIOSeekSpec_proven
    notes := "Stated with the mathematical sum, so a seek that wrapped pos instead of raising fails it. Smoke-tested on 3.15.2 over 20000 seeks with positions and offsets at sys.maxsize boundaries. The clinic conversions before it are pyio-bytesio-twins-same-class." },
  { id := "pyio-bytesio-seek-twins", pyFile := "Lib/_pyio.py"
    pyFns := ["_io_BytesIO_seek_impl", "BytesIO.seek"]
    statement := "For every open BytesIO and every pos and whence in C range, io.BytesIO.seek and _pyio.BytesIO.seek agree on the value or the exception class."
    source := "invariant: C accelerator vs pure-Python twin"
    status := .refuted, prop := ``BytesIOSeekTwins, thm := some ``bytesIOSeekTwins_refuted
    bug := some "pyio-bytesio-twin-argument-handling"
    notes := "seek(sys.maxsize), seek(sys.maxsize, 1): C OverflowError('new position too large') (bytesio.c:789-793), _pyio 2 * sys.maxsize (_pyio.py:988-990)." }
]

def bytesStateEntries : List Entry := [
  { id := "pyio-bytesio-setstate-checks", pyFile := "Modules/_io/bytesio.c"
    pyFns := ["bytesio_setstate_lock_held", "bytesio_setstate"]
    statement := "io.BytesIO.__setstate__(state) for every stream and every state object: a non-tuple or a tuple shorter than 3 raises TypeError('_io.BytesIO.__setstate__ argument should be 3-tuple, got T') and changes nothing, as does BufferError with a live view; otherwise the stream is emptied, a non-bytes-like first item raises its TypeError and leaves it empty, a bytes-like one becomes the contents; then a non-int second item raises TypeError('second item of state must be an integer, not T'), one outside Py_ssize_t OverflowError, a negative one ValueError('position value cannot be negative'), each with the position left at len(state[0]); a bool is an int; then the third item: None keeps the instance dict, a dict is merged into it or becomes it, anything else raises TypeError('third item of state should be a dict, got a T') with contents and position already set."
    source := "the body bytesio.c:948-1023 (checks :963-968, :986-999, :1005-1010; the dict :1011-1019); invariant: pickle state validation"
    status := .proven, prop := ``BytesIOSetstateChecks, thm := some ``bytesIOSetstateChecks_proven
    notes := "Probed on 3.15.2: f.__setstate__((b'xy', 'bad', None)) raises the position TypeError with getvalue() == b'xy' and tell() == 2, and (b'xy', 1, 5) the dict TypeError with tell() == 1: a bad later item leaves the earlier ones applied. Not filed: __setstate__ is the pickle protocol's, which always passes a well-formed state, and the reset comment (:970-971) and the 'Set carefully the position value' comment (:982-984) show the order is deliberate. self->dict = dict (:1018) stores the caller's dict object; the model keeps its contents. Scope: an exact io.BytesIO (tp_name in the first message)." },
  { id := "pyio-bytesio-pickle-dict", pyFile := "Modules/_io/bytesio.c"
    pyFns := ["bytesio_getstate", "bytesio_getstate_lock_held", "bytesio_setstate_lock_held", "bytesio_setstate"]
    statement := "io.BytesIO.__getstate__ on an open stream returns (contents, position, a copy of the instance dict or None while there is none) without changing the stream; __setstate__ of that state on any open io.BytesIO with no view restores contents and position and merges the dict into the target's, so into a fresh object it brings the dict over exactly."
    source := "the bodies bytesio.c:909-935 (PyDict_Copy or None, :921-930) and :948-1023; invariant: pickle round trip"
    status := .proven, prop := ``BytesIOPickleDict, thm := some ``bytesIOPickleDict_proven
    notes := "A getstate that always returned None for the dict loses it in the round trip and fails. The returned dict is a copy: the difftest mutates it after every __getstate__ and a later f.__dict__ shows no change (difftest/pyio_state_diff.py). PyDict_Copy's NULL return (:926-929) is a MemoryError, outside the allocation model. Hypotheses: position in Py_ssize_t, contents below the allocation bound." }
]

end PyLean.PyIO
