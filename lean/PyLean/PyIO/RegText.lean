import PyLean.Registry
import PyLean.PyIO.ArgTwins
import PyLean.PyIO.NewlineProps
import PyLean.PyIO.TextTellStale

/-! Registry entries for the argument and check-order differences of the BytesIO and
StringIO twins (`PyIO/ArgTwins.lean`), and for TextIOWrapper, IncrementalNewlineDecoder,
TextIOBase. -/

namespace PyLean.PyIO

open PyLean.Registry

def textEntries : List Entry := [
  { id := "pyio-bytesio-index-arg-spec", pyFile := "Lib/_pyio.py"
    pyFns := ["BytesIO.read", "BytesIO.seek", "IOBase.readline", "BytesIO.read1"]
    statement := "read(a), readline(a) and seek(a, whence) of an object a that is not None or an int, on every BytesIO state. C converts first: an object without __index__ is refused by type name (TypeError(\"argument should be integer or None, not 'T'\") for read and readline, TypeError(\"'T' object cannot be interpreted as an integer\") for seek) with the stream unchanged; otherwise __index__ runs in every state and the method then runs, closed check included, on the state it left. _pyio checks closed first: a closed stream gives ValueError('read from closed file') or ValueError('seek on closed file') without calling __index__; an open one refuses an object without __index__ with TypeError(f\"{a!r} is not an integer\") (readline too), propagates an exception of __index__ after its actions, and runs the body with no second look at closed, so after an __index__ that closed the stream read(v) returns b'' and seek(v) (v >= 0) sets and returns v."
    source := "the bodies _pyio.py:513-553, :927-948, :975-996 and Python/modsupport.c:15-35, clinic/bytesio.c.h:239, :318, :471-482, bytesio.c:509-525, :561-571, :774-815"
    status := .proven, prop := ``BytesIOIndexArgSpec, thm := some ``bytesIOIndexArgSpec_proven
    notes := "The __index__ actions are the Hook type (close, getbuffer, tell, seek, write), each with its exceptions swallowed, in any order. read1 is read (_pyio.py:950-953). Smoke-tested on 3.15.2: read(x) with x.__index__ closing f gives b'' in _pyio and ValueError in C; seek gives 2 and ValueError; readline gives ValueError('read from closed file') and ValueError('I/O operation on closed file.')." },
  { id := "pyio-bytesio-read-index-twins", pyFile := "Lib/_pyio.py"
    pyFns := ["BytesIO.read", "_io_BytesIO_read_impl"]
    statement := "io.BytesIO.read and _pyio.BytesIO.read agree on the value or the exception class for every state and every argument object."
    source := "invariant: C accelerator vs pure-Python twin"
    status := .refuted, prop := ``BytesIOReadIndexTwins, thm := some ``bytesIOReadIndexTwins_refuted
    bug := some "pyio-bytesio-twin-argument-handling"
    notes := "f = BytesIO(b'abc'); f.read(x) where x.__index__ closes f and returns 1: C ValueError (the clinic converter runs __index__ before CHECK_CLOSED, bytesio.c:514), _pyio b'' (closed checked at _pyio.py:928, __index__ called at :938, no re-check)." },
  { id := "pyio-bytesio-seek-index-twins", pyFile := "Lib/_pyio.py"
    pyFns := ["BytesIO.seek", "_io_BytesIO_seek_impl"]
    statement := "io.BytesIO.seek and _pyio.BytesIO.seek agree on the value or the exception class for every state, argument object and whence."
    source := "invariant: C accelerator vs pure-Python twin"
    status := .refuted, prop := ``BytesIOSeekIndexTwins, thm := some ``bytesIOSeekIndexTwins_refuted
    bug := some "pyio-bytesio-twin-argument-handling"
    notes := "f.seek(x) where x.__index__ closes f and returns 2: C ValueError, _pyio sets _pos on the closed stream and returns 2 (_pyio.py:976-987)." },
  { id := "pyio-bytesio-readlines-float-twins", pyFile := "Lib/_pyio.py"
    pyFns := ["IOBase.readlines", "_io_BytesIO_readlines_impl"]
    statement := "io.BytesIO.readlines and _pyio.BytesIO.readlines agree on the value or the exception class for every open stream and every float hint."
    source := "invariant: C accelerator vs pure-Python twin"
    status := .refuted, prop := ``BytesIOReadlinesFloatTwins, thm := some ``bytesIOReadlinesFloatTwins_refuted
    bug := some "pyio-bytesio-twin-argument-handling"
    notes := "BytesIO(b'a\\nb\\n').readlines(0.5): C TypeError(\"integer argument expected, got 'float'\") (bytesio.c:605-608), _pyio [b'a\\n'] (0.5 <= 0 is False at _pyio.py:572, then n >= 0.5 at :579). The float comparisons are float_richcompare on the exact binary64 model, for every float." },
  { id := "pyio-bytesio-write-obj", pyFile := "Lib/_pyio.py"
    pyFns := ["BytesIO.write"]
    statement := "write(w) of a str or of an object without the buffer interface raises TypeError in both twins on every stream, open or closed, before looking at closed, and changes nothing: C TypeError(\"a bytes-like object is required, not 'T'\"), _pyio TypeError(\"can't write str to binary stream\") for a str and TypeError(\"memoryview: a bytes-like object is required, not 'T'\") otherwise."
    source := "the bodies _pyio.py:955-960 and bytesio.c:236-247, Objects/abstract.c:447-453, Objects/memoryobject.c:821-823"
    status := .proven, prop := ``BytesIOWriteObj, thm := some ``bytesIOWriteObj_proven
    notes := "The buffer path of write is pinned by pyio-bytesio-tell-after-write, -getvalue-zero-fill, -writes-concat and the core twin agreement." },
  { id := "pyio-bytesio-init-twins", pyFile := "Lib/_pyio.py"
    pyFns := ["BytesIO.__init__", "_io_BytesIO___init___impl", "bytesio_new"]
    statement := "Each constructor, from its own body, gives the initial bytes at position 0, open, with no view, and on those starts the twins agree on every value and exception class under the core hypotheses; a second __init__ with an int raises TypeError in both, _pyio (\"can't concat int to bytearray\") before touching the stream, C (\"a bytes-like object is required, not 'int'\") after emptying it."
    source := "the bodies _pyio.py:884-894 and bytesio.c:1054-1073, :1084-1114; invariant: C accelerator vs pure-Python twin"
    status := .proven, prop := ``BytesIOInitTwins, thm := some ``bytesIOInitTwins_proven
    notes := "The difftest constructs with bytes and calls __init__ again with bytes, bytearray or 1 (pyio_base_diff.py reinit, reinit_obj)." },
  { id := "pyio-bytesio-getstate", pyFile := "Lib/_pyio.py"
    pyFns := ["BytesIO.__getstate__", "bytesio_getstate", "bytesio_getstate_lock_held"]
    statement := "__getstate__ on a closed BytesIO raises ValueError('I/O operation on closed file.') in C and ValueError('__getstate__ on closed file') in _pyio; on an open one it returns the contents and the position ((bytes, pos, None) in C, the instance dict without _lock in _pyio); neither changes the stream."
    source := "the bodies _pyio.py:896-902 and bytesio.c:909-945"
    status := .proven, prop := ``BytesIOGetstate, thm := some ``bytesIOGetstate_proven },
  { id := "pyio-bytesio-getbuffer", pyFile := "Lib/_pyio.py"
    pyFns := ["BytesIO.getbuffer", "_io_BytesIO_getbuffer_impl", "bytesiobuf_getbuffer"]
    statement := "getbuffer() refuses a closed BytesIO (ValueError('getbuffer on closed file') in _pyio, ValueError('I/O operation on closed file.') in C); on an open one it returns a view that leaves contents and position unchanged and, while it lives, makes closing a non-empty stream, truncate(0) of it, and a write past the end raise BufferError, in both twins."
    source := "Doc/library/io.rst (BytesIO.getbuffer: 'As long as the view exists, the BytesIO object cannot be resized or closed'); the bodies _pyio.py:915-920, bytesio.c:386-403"
    status := .proven, prop := ``BytesIOGetbuffer, thm := some ``bytesIOGetbuffer_proven
    notes := "Scope: the view is an export count; that it reads and writes the live buffer is not modelled. Releasing it is pyio-bytesio-release-exports." },
  { id := "pyio-stringio-write-refusals", pyFile := "Lib/_pyio.py"
    pyFns := ["TextIOWrapper.write", "_io_StringIO_write_impl"]
    statement := "The refusals of StringIO.write on every state: C raises TypeError(\"string argument expected, got 'T'\") for a non-str whether or not the stream is closed, and ValueError('I/O operation on closed file') for a str on a closed stream; _pyio raises ValueError('write to closed file') for every argument on a closed stream and TypeError(\"can't write T to text stream\") for a non-str on an open one. No refusal changes the stream."
    source := "the bodies _pyio.py:2280-2286 and stringio.c:561-579"
    status := .proven, prop := ``StringIOWriteRefusals, thm := some ``stringIOWriteRefusals_proven },
  { id := "pyio-stringio-write-check-order-twins", pyFile := "Lib/_pyio.py"
    pyFns := ["TextIOWrapper.write", "_io_StringIO_write_impl"]
    statement := "io.StringIO.write and _pyio.StringIO.write raise exceptions of the same class for a non-str argument whenever both streams are open or both are closed."
    source := "invariant: C accelerator vs pure-Python twin"
    status := .refuted, prop := ``StringIOWriteCheckOrderTwins, thm := some ``stringIOWriteCheckOrderTwins_refuted
    bug := some "pyio-bytesio-twin-argument-handling"
    notes := "s.close(); s.write(1): C TypeError (type test at stringio.c:567 before CHECK_CLOSED at :572), _pyio ValueError (closed test at _pyio.py:2282 before the type test at :2284)." },
  { id := "pyio-stringio-newline-check", pyFile := "Lib/_pyio.py"
    pyFns := ["TextIOWrapper._check_newline"]
    statement := "In _pyio.StringIO(value, newline), TextIOWrapper._check_newline runs first: a newline that is not a str or None raises TypeError(\"illegal newline type: <class 'T'>\"), a str outside the five legal values raises ValueError(f\"illegal newline value: {newline!r}\") whatever the initial value, and only a legal newline lets a non-str initial value be refused with TypeError(\"initial_value must be str or None, not T\"); C checks in the same order, refusing the type with TypeError(\"newline must be str or None, not T\")."
    source := "Doc/library/io.rst:1001 (newline can be None, '', '\\n', '\\r' or '\\r\\n'); the bodies _pyio.py:2090-2092, :2122-2126, :2747-2759 and stringio.c:693-721"
    status := .proven, prop := ``PyStringIONewlineCheck, thm := some ``pyStringIONewlineCheck_proven
    notes := "Which newline values succeed is pyio-stringio-py-newline-legal; this entry pins the refusals' classes, messages and order. A repr with non-ASCII characters is compared as '~illegal newline value' by the difftest." },
  { id := "pyio-textio-c-tell-after-next-in-range", pyFile := "Modules/_io/textio.c"
    pyFns := ["_io_TextIOWrapper_tell_impl"]
    statement := "For every byte string, io.TextIOWrapper(io.BytesIO(data), encoding='utf-8') followed by f.seek(f.tell()), next(f), f.flush() and f.tell() returns a position no greater than len(data), or raises."
    source := "invariant: tell() returns a position in the stream (Doc/library/io.rst, TextIOBase.tell: 'Return the current stream position as an opaque number')"
    status := .refuted, prop := ``TextCTellAfterNextInRange, thm := some ``textCTellAfterNextInRange_refuted
    bug := some "pyio-textio-tell-after-next-stale-snapshot"
    notes := "b'\\nb\\xe2\\x82\\xac' (5 bytes): tell() returns 6. next() stops updating the snapshot, flush() re-enables tell(), and tell() asks for skip_bytes = 1 of the empty snapshot (textio.c:2949-2957), decoding the bytes object's terminating NUL. Found by pyio_text_diff seed 44 (coordinator run); the model now reads that NUL (TCm.snapBytes) and calls a longer over-read undefined behaviour." },
  { id := "pyio-nldec-chunks", pyFile := "Lib/_pyio.py"
    pyFns := ["IncrementalNewlineDecoder.decode", "IncrementalNewlineDecoder.__init__"]
    statement := "For _pyio.IncrementalNewlineDecoder(None, translate) and every split of a text into chunks, decoded with final=False and then decode('', final=True): the outputs concatenate to the text with \\r\\n and \\r translated to \\n when translate is set, and to the text itself otherwise; the recorded newline kinds are exactly those of the whole text, so a \\r\\n cut between two chunks counts as \\r\\n and never as \\r and \\n; nothing is left pending."
    source := "Lib/_pyio.py:1973-1977 (class docstring: 'translating \\r\\n and \\r into \\n ... ensures that the newline sequence is returned in one piece'); the body :1986-2015"
    status := .proven, prop := ``NDecodeChunks, thm := some ``nDecodeChunks_proven
    notes := "Smoke-tested on 3.15.2: 20000 random chunkings per twin (io and _pyio), alphabet a, b, \\r, \\n, both translate settings: concatenation, newlines and the pending flag as stated. The wrapped UTF-8 decoder is compared by the nldec difftest; this statement is about decoder None." },
  { id := "pyio-nldec-state", pyFile := "Lib/_pyio.py"
    pyFns := ["IncrementalNewlineDecoder.getstate", "IncrementalNewlineDecoder.setstate",
      "IncrementalNewlineDecoder.reset"]
    statement := "setstate(getstate()) of an IncrementalNewlineDecoder, restored into any decoder of the same kind and translate, makes every later decode return what the original would (the state is the wrapped decoder's buffer and pendingcr as the low bit of the flag); reset() makes the decoder a fresh one, with nothing pending, an empty buffer and newlines None."
    source := "the bodies _pyio.py:2017-2038; invariant: getstate/setstate round trip (codecs.IncrementalDecoder.getstate: 'Return the current state of the decoder')"
    status := .proven, prop := ``NDecState, thm := some ``nDecState_proven
    notes := "Smoke-tested on 3.15.2: 20000 random decoders per twin, setstate into a second decoder that had decoded other text, then the same decode; reset gives newlines None and getstate (b'', 0)." }
]

end PyLean.PyIO
