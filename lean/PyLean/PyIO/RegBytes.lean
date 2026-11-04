import PyLean.Registry
import PyLean.PyIO.BytesShareProps

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

end PyLean.PyIO
