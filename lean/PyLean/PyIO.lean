import PyLean.Registry
import PyLean.PyIO.Diff
import PyLean.PyIO.BytesTwins
import PyLean.PyIO.BytesSim
import PyLean.PyIO.BytesDocs
import PyLean.PyIO.Readlines
import PyLean.PyIO.StringTwins
import PyLean.PyIO.StringProps
import PyLean.PyIO.BytesExtra
import PyLean.PyIO.StringExtra
import PyLean.PyIO.RegText
import PyLean.PyIO.RegBuffered
import PyLean.PyIO.RegFile

/-!
`Lib/_pyio.py` vs `Modules/_io/` (BytesIO, StringIO), CPython 3.14.7.

Models: `PyIO/BytesIO.lean` (both `BytesIO` twins), `PyIO/StringC.lean`
(`Modules/_io/stringio.c`), `PyIO/StringPy.lean` (`_pyio.StringIO`, a
`TextIOWrapper` over a UTF-8 `_pyio.BytesIO`, including chunked reads,
`tell()` cookies with the binary64 ratio of `PyIO/Double.lean`, and the
newline decoder). A test case is a constructor plus a sequence of
operations; every result (value or exception class and message) is
compared (`difftest/pyio_diff.py`).
-/

namespace PyLean.PyIO

open PyLean.Registry

def coreEntries : List Entry := [
  -- BytesIO: C vs Python, layered
  { id := "pyio-bytesio-twins-agree", pyFile := "Modules/_io/bytesio.c"
    pyFns := ["check_closed", "_io_BytesIO_close_impl", "_io_BytesIO_read_impl", "BytesIO.close",
      "BytesIO.read"]
    statement := "For every initial value and operation sequence, io.BytesIO and _pyio.BytesIO return the same values and raise the same exceptions (class and message)."
    source := "invariant: C accelerator vs pure-Python twin (Lib/_pyio.py docstring: Python implementation of the io module)"
    status := .refuted, prop := ``BytesIOTwinsAgree, thm := some ``bytesIOTwinsAgree_refuted
    bug := some "pyio-bytesio-twin-argument-handling"
    notes := "Closed-file and argument errors use different messages, e.g. read() on a closed stream." },
  { id := "pyio-bytesio-twins-same-class", pyFile := "Modules/_io/bytesio.c"
    pyFns := ["_io_BytesIO_seek_impl", "BytesIO.seek"]
    statement := "The twins agree on every value and exception class, for all int arguments."
    source := "invariant: C accelerator vs pure-Python twin"
    status := .refuted, prop := ``BytesIOTwinsSameClass, thm := some ``bytesIOTwinsSameClass_refuted
    bug := some "pyio-bytesio-twin-argument-handling"
    notes := "seek(2**63): C OverflowError at Py_ssize_t conversion, Python seeks. Same for readlines/read/readline/truncate hints above sys.maxsize, and for whence outside C int." },
  { id := "pyio-bytesio-twins-same-class-in-range", pyFile := "Modules/_io/bytesio.c"
    pyFns := ["check_exports", "_io_BytesIO_getbuffer_impl", "bytesiobuf_getbuffer_lock_held",
      "bytesiobuf_getbuffer", "BytesIO.getbuffer", "_io_BytesIO_write_impl",
      "write_bytes_lock_held", "BytesIO.write"]
    statement := "With every int argument in the range of its C converter, the twins agree on every value and exception class."
    source := "invariant: C accelerator vs pure-Python twin; Doc/library/io.rst getbuffer note"
    status := .refuted, prop := ``BytesIOTwinsSameClassInRange, thm := some ``bytesIOTwinsSameClassInRange_refuted
    bug := some "pyio-bytesio-getbuffer-blocks-overwrite"
    notes := "With a live getbuffer() view C refuses every write/truncate (BufferError), Python only those that resize." },
  { id := "pyio-bytesio-twins-same-class-no-export", pyFile := "Modules/_io/bytesio.c"
    pyFns := ["write_bytes_lock_held", "resize_buffer_lock_held", "resize_unshared_buffer_lock_held",
      "bytesio_get_closed", "BytesIO.write", "BytesIO.seek"]
    statement := "In range and without getbuffer(), the twins agree on every value and exception class."
    source := "invariant: C accelerator vs pure-Python twin"
    status := .refuted, prop := ``BytesIOTwinsSameClassNoExport, thm := some ``bytesIOTwinsSameClassNoExport_refuted
    bug := some "pyio-bytesio-write-near-maxsize-systemerror"
    notes := "seek(sys.maxsize - 1); write(b'x'): SystemError and the stream is closed (3.14.7); fixed on main (gh-160781, gh-157242)." },
  { id := "pyio-bytesio-twins-same-class-no-alloc-fail", pyFile := "Lib/_pyio.py"
    pyFns := ["IOBase.readline", "_io_BytesIO_readline_impl", "BytesIO.close", "_io_BytesIO_close_impl"]
    statement := "In range, without getbuffer() and without allocation failure (positions and write extents below the allocation bound), the twins agree on every value and exception class."
    source := "invariant: C accelerator vs pure-Python twin"
    status := .refuted, prop := ``BytesIOTwinsSameClassNoAllocFail, thm := some ``bytesIOTwinsSameClassNoAllocFail_refuted
    bug := some "pyio-bytesio-twin-argument-handling"
    notes := "readline(0) on a closed stream: C ValueError, Python b''." },
  { id := "pyio-bytesio-twins-same-class-core", pyFile := "Modules/_io/bytesio.c"
    pyFns := ["check_closed", "check_exports", "_io_BytesIO___init___impl", "BytesIO.__init__",
      "_io_BytesIO_read_impl", "_io_BytesIO_read1_impl", "_io_BytesIO_readline_impl",
      "_io_BytesIO_readlines_impl", "scan_eol_lock_held", "read_bytes_lock_held",
      "bytesio_iternext_lock_held", "bytesio_iternext", "BytesIO.read", "BytesIO.read1",
      "IOBase.readline", "IOBase.__iter__", "IOBase.__next__", "IOBase.readlines",
      "_io_BytesIO_readinto_impl", "BufferedIOBase.readinto", "BufferedIOBase._readinto",
      "_io_BytesIO_write_impl", "write_bytes_lock_held", "BytesIO.write",
      "_io_BytesIO_seek_impl", "BytesIO.seek", "_io_BytesIO_tell_impl", "BytesIO.tell",
      "_io_BytesIO_truncate_impl", "BytesIO.truncate", "_io_BytesIO_getvalue_impl",
      "BytesIO.getvalue", "_io_BytesIO_close_impl", "BytesIO.close", "bytesio_get_closed"]
    statement := "With int arguments in C range, no getbuffer(), no allocation failure and no readline(0) on a closed stream, io.BytesIO and _pyio.BytesIO return the same values and raise exceptions of the same classes for every initial value and operation sequence (read, read1, readline, readlines, readinto, write, seek, tell, truncate, getvalue, close, next, closed)."
    source := "invariant: C accelerator vs pure-Python twin"
    status := .proven, prop := ``BytesIOTwinsSameClassCore, thm := some ``bytesIOTwinsSameClassCore_proven
    notes := "Each hypothesis is exactly one of the refutations above; the allocation hypothesis also excludes seek(sys.maxsize) + seek(sys.maxsize, 1), where C raises 'new position too large' (listed in pyio-bytesio-twin-argument-handling). readline(0) on a closed stream is excluded by IOBase's 'calling any method on a closed stream is undefined' (_pyio.py:325-326). Proof: simulation, both twins keep the same buffer, position and closed flag; readline/readlines/next go through lineLen." },
  -- BytesIO: documented behaviour
  { id := "pyio-bytesio-tell-after-write", pyFile := "Modules/_io/bytesio.c"
    pyFns := ["_io_BytesIO_write_impl", "write_bytes_lock_held", "resize_buffer_lock_held",
      "unshare_buffer_lock_held", "resize_unshared_buffer_lock_held", "BytesIO.write"]
    statement := "Whenever write(b) succeeds (any state, any b) it returns len(b) and the position advances by exactly len(b), in both twins."
    source := "Doc/library/io.rst:654-657 (BufferedIOBase.write: 'return the number of bytes written (always equal to the length of b in bytes ...)'); Lib/_pyio.py:745"
    status := .proven, prop := ``TellAfterWrite, thm := some ``tellAfterWrite_proven },
  { id := "pyio-bytesio-read-after-seek", pyFile := "Modules/_io/bytesio.c"
    pyFns := ["_io_BytesIO_seek_impl", "_io_BytesIO_read_impl", "read_bytes_lock_held", "BytesIO.seek",
      "BytesIO.read", "_io_StringIO_seek_impl", "_io_StringIO_read_impl"]
    statement := "On an open BytesIO (both twins) or C StringIO, seek(p) followed by read(n) returns buf[p:p+n] for every p, n >= 0 (C: in Py_ssize_t), including p beyond the end."
    source := "Doc/library/io.rst:421 (IOBase.seek) and BufferedIOBase.read"
    status := .proven, prop := ``ReadAfterSeek, thm := some ``readAfterSeek_proven },
  { id := "pyio-truncate-keeps-position", pyFile := "Modules/_io/bytesio.c"
    pyFns := ["_io_BytesIO_truncate_impl", "BytesIO.truncate", "_io_StringIO_truncate_impl",
      "resize_buffer"]
    statement := "truncate(size) never moves the stream position, for every state and argument and whatever the outcome (C and Python BytesIO, C StringIO)."
    source := "Doc/library/io.rst:452-455 (IOBase.truncate: 'The current stream position isn't changed')"
    status := .proven, prop := ``TruncateKeepsPosition, thm := some ``truncateKeepsPosition_proven },
  { id := "pyio-bytesio-getvalue-zero-fill", pyFile := "Modules/_io/bytesio.c"
    pyFns := ["write_bytes_lock_held", "BytesIO.write", "_io_BytesIO_getvalue_impl", "BytesIO.getvalue"]
    statement := "After a successful non-empty write(b) on an open BytesIO, getvalue() is the old contents overwritten by b at the old position, with every byte between the old end and that position zero, and length max(old length, pos + len(b)); an empty write changes nothing (both twins)."
    source := "Code comments, not docs: bytesio.c:271 'In case of overseek, pad with null bytes', _pyio.py:954 'Pad buffer to pos with null bytes'; Doc/library/io.rst:458 only says this of truncate extending a file"
    status := .proven, prop := ``GetvalueZeroFill, thm := some ``getvalueZeroFill_proven },
  { id := "pyio-bytesio-writes-concat", pyFile := "Modules/_io/bytesio.c"
    pyFns := ["_io_BytesIO_write_impl", "write_bytes_lock_held", "BytesIO.write",
      "_io_BytesIO_getvalue_impl", "BytesIO.getvalue"]
    statement := "Writing any byte strings one after another into BytesIO() leaves exactly their concatenation in getvalue() (both twins), while the total stays below the allocation bound."
    source := "Doc/library/io.rst BytesIO.getvalue"
    status := .proven, prop := ``WritesConcat, thm := some ``writesConcat_proven },
  -- readlines(hint)
  { id := "pyio-bytesio-readlines-hint-doc", pyFile := "Modules/_io/bytesio.c"
    pyFns := ["_io_BytesIO_readlines_impl", "scan_eol_lock_held", "IOBase.readlines", "IOBase.__iter__",
      "IOBase.__next__", "IOBase.readline"]
    statement := "For hint > 0, BytesIO.readlines(hint) returns whole lines until their total length exceeds hint, i.e. the documented prefix of readlines() (both twins)."
    source := "Doc/library/io.rst:409-413 (IOBase.readlines: 'no more lines will be read if the total size (in bytes/characters) of all lines so far exceeds hint')"
    status := .refuted, prop := ``BytesIOReadlinesHintDoc, thm := some ``bytesIOReadlinesHintDoc_refuted
    bug := some "pyio-readlines-hint-stops-early"
    notes := "C BytesIO (bytesio.c:627) and _pyio IOBase (_pyio.py:579) stop when the total reaches hint; C _IOBase (iobase.c:765) stops when it exceeds hint." },
  { id := "pyio-stringio-c-readlines-hint-doc", pyFile := "Modules/_io/iobase.c"
    pyFns := ["_io__IOBase_readlines_impl", "iobase_iter", "stringio_iternext", "_stringio_readline",
      "_PyIO_find_line_ending", "find_control_char"]
    statement := "For every open C StringIO and hint > 0 (in Py_ssize_t), readlines(hint) returns the documented prefix of readlines(): whole lines until their total exceeds hint."
    source := "Doc/library/io.rst:409-413"
    status := .proven, prop := ``CStringIOReadlinesHintDoc, thm := some ``cStringIOReadlinesHintDoc_proven },
  -- StringIO: newline argument
  { id := "pyio-stringio-c-newline-legal", pyFile := "Modules/_io/stringio.c"
    pyFns := ["_io_StringIO___init___impl"]
    statement := "io.StringIO(newline=nl) succeeds exactly for nl in (None, '', '\\n', '\\r', '\\r\\n')."
    source := "Doc/library/io.rst:1019 (TextIOWrapper: newline can be None, '', '\\n', '\\r' or '\\r\\n') and :1142 (StringIO: works like TextIOWrapper)"
    status := .refuted, prop := ``CStringIONewlineLegal, thm := some ``cStringIONewlineLegal_refuted
    bug := some "pyio-stringio-newline-embedded-nul"
    notes := "newline='\\x00' is accepted (as ''); '\\n\\x00' as '\\n', '\\r\\x00junk' as '\\r'." },
  { id := "pyio-stringio-c-newline-legal-no-nul", pyFile := "Modules/_io/stringio.c"
    pyFns := ["_io_StringIO___init___impl"]
    statement := "For every newline string without NUL characters (and None), io.StringIO(newline=nl) succeeds exactly for the five legal values."
    source := "Doc/library/io.rst:1019, :1142"
    status := .proven, prop := ``CStringIONewlineLegalNoNul, thm := some ``cStringIONewlineLegalNoNul_proven
    notes := "The hypothesis is exactly the refuted case above; lone surrogates raise UnicodeEncodeError." },
  { id := "pyio-stringio-py-newline-legal", pyFile := "Lib/_pyio.py"
    pyFns := ["TextIOWrapper._check_newline", "TextIOWrapper._configure", "TextIOWrapper.__init__",
      "StringIO.__init__"]
    statement := "_pyio.StringIO(newline=nl) succeeds exactly for nl in (None, '', '\\n', '\\r', '\\r\\n')."
    source := "Doc/library/io.rst:1019, :1142"
    status := .proven, prop := ``PyStringIONewlineLegal, thm := some ``pyStringIONewlineLegal_proven },
  -- StringIO: C vs Python
  { id := "pyio-stringio-writes-twins", pyFile := "Modules/_io/stringio.c"
    pyFns := ["write_str", "_io_StringIO_write_impl", "_io_StringIO_getvalue_impl", "TextIOWrapper.write",
      "StringIO.getvalue", "IncrementalNewlineDecoder.decode",
      "_PyIncrementalNewlineDecoder_decode"]
    statement := "For every legal newline and every sequence of writes into StringIO(), io.StringIO and _pyio.StringIO agree on every result including getvalue()."
    source := "invariant: C accelerator vs pure-Python twin"
    status := .refuted, prop := ``StringIOWritesTwins, thm := some ``stringIOWritesTwins_refuted
    bug := some "pyio-stringio-newline-none-split-crlf"
    notes := "newline=None, write('a\\r'), write('\\nb'): C 'a\\n\\nb', Python 'a\\nb'." },
  { id := "pyio-stringio-writes-twins-not-none", pyFile := "Modules/_io/stringio.c"
    pyFns := ["write_str", "resize_buffer", "_io_StringIO_write_impl", "_io_StringIO_getvalue_impl",
      "_io_StringIO___init___impl", "TextIOWrapper.write", "TextIOWrapper.flush",
      "TextIOWrapper._get_decoder", "StringIO.__init__", "StringIO.getvalue",
      "IncrementalNewlineDecoder.decode", "IncrementalNewlineDecoder.getstate",
      "IncrementalNewlineDecoder.setstate", "IncrementalNewlineDecoder.reset"]
    statement := "For newline in ('', '\\n', '\\r', '\\r\\n') and every sequence of str writes into StringIO(), both twins return exactly the same results (write counts and getvalue())."
    source := "invariant: C accelerator vs pure-Python twin"
    status := .proven, prop := ``StringIOWritesTwinsNotNone, thm := some ``stringIOWritesTwinsNotNone_proven
    notes := "Hypotheses: code points below 0x110000 (str type invariant) and total length below the allocation bound. The newline=None exclusion is the refutation above. Uses UTF-8 (surrogatepass) decode(encode(s)) = s." },
  { id := "pyio-stringio-init-write-twins", pyFile := "Lib/_pyio.py"
    pyFns := ["StringIO.__init__", "TextIOWrapper.write", "TextIOWrapper.seek", "StringIO.getvalue",
      "_io_StringIO_getvalue_impl"]
    statement := "StringIO(value, newline) followed by write(s) gives the same results in both twins."
    source := "invariant: C accelerator vs pure-Python twin; Doc/library/io.rst:1136-1138 ('ready ... for a write that would overwrite the initial value')"
    status := .refuted, prop := ``StringIOInitWriteTwins, thm := some ``stringIOInitWriteTwins_refuted
    bug := some "pyio-stringio-pyio-byte-positions"
    notes := "StringIO('é').write('x'): C 'x', _pyio UnicodeDecodeError (byte positions in the UTF-8 buffer)." },
  { id := "pyio-stringio-read-write-twins", pyFile := "Lib/_pyio.py"
    pyFns := ["TextIOWrapper.read", "TextIOWrapper._read_chunk", "TextIOWrapper._get_decoded_chars",
      "TextIOWrapper._set_decoded_chars", "TextIOWrapper.write", "StringIO.getvalue",
      "_io_StringIO_read_impl", "_io_StringIO_write_impl"]
    statement := "For ASCII text, read(k) followed by write(s) gives the same results in both twins."
    source := "invariant: C accelerator vs pure-Python twin"
    status := .refuted, prop := ``StringIOReadWriteTwins, thm := some ``stringIOReadWriteTwins_refuted
    bug := some "pyio-stringio-pyio-write-after-read"
    notes := "StringIO('abcdef'), read(1), write('X'): C 'aXcdef', _pyio 'abcdefX' (read-ahead)." },
  { id := "pyio-stringio-tell-after-reads", pyFile := "Lib/_pyio.py"
    pyFns := ["TextIOWrapper.__next__", "TextIOWrapper.readline", "TextIOWrapper._rewind_decoded_chars",
      "TextIOWrapper.tell", "IOBase.readlines", "_io_StringIO_tell_impl"]
    statement := "After any sequence of reads (read, readline, readlines, next) on an open StringIO with a legal newline, tell() returns a position in both twins."
    source := "invariant: C accelerator vs pure-Python twin"
    status := .refuted, prop := ``StringIOTellAfterReads, thm := some ``stringIOTellAfterReads_refuted
    bug := some "pyio-stringio-pyio-tell-after-readlines"
    notes := "_pyio: readlines(1) breaks out of 'for line in self' and leaves _telling false; related to gh-81217." },
  { id := "pyio-stringio-newlines-attr", pyFile := "Lib/_pyio.py"
    pyFns := ["TextIOWrapper.newlines", "TextIOWrapper._get_decoder", "_io_StringIO_newlines_get_impl"]
    statement := "On an open StringIO with a legal newline, after any reads, the newlines attribute is None, a str or a tuple in both twins (it never raises)."
    source := "Doc/library/io.rst:918-922 (TextIOBase.newlines: 'A string, a tuple of strings, or None ... this may not be available'); twin behaviour"
    status := .refuted, prop := ``StringIONewlinesAttr, thm := some ``stringIONewlinesAttr_refuted
    bug := some "pyio-stringio-pyio-newlines-attributeerror"
    notes := "_pyio with newline '\\n', '\\r' or '\\r\\n': AttributeError once a decoder exists." },
  -- BytesIO: remaining methods (inquiries, writelines, pickle, getbuffer release)
  { id := "pyio-bytesio-inquiries", pyFile := "Modules/_io/bytesio.c"
    pyFns := ["_io_BytesIO_readable_impl", "_io_BytesIO_writable_impl", "_io_BytesIO_seekable_impl",
      "_io_BytesIO_flush_impl", "_io_BytesIO_isatty_impl", "BytesIO.readable", "BytesIO.writable",
      "BytesIO.seekable", "IOBase.flush", "IOBase.isatty", "IOBase._checkClosed"]
    statement := "On an open BytesIO readable(), writable(), seekable() return True, flush() returns None and isatty() False, none of them changing the object; on a closed BytesIO each raises ValueError('I/O operation on closed file.') (both twins, every state)."
    source := "Doc/library/io.rst (IOBase.readable/writable/seekable/isatty/flush); invariant: no state change, both twins agree"
    status := .proven, prop := ``BytesIOInquiries, thm := some ``bytesIOInquiries_proven },
  { id := "pyio-bytesio-writelines", pyFile := "Modules/_io/bytesio.c"
    pyFns := ["_io_BytesIO_writelines_impl", "IOBase.writelines"]
    statement := "writelines(ls) on an open BytesIO equals calling write() for each element in turn, stopping at the first failure: it reaches the same state and returns None when every write succeeds (both twins)."
    source := "Doc/library/io.rst (IOBase.writelines: 'equivalent to calling write() for each element'); bytesio.c:840-841"
    status := .proven, prop := ``BytesIOWritelines, thm := some ``bytesIOWritelines_proven },
  { id := "pyio-bytesio-pickle-roundtrip", pyFile := "Modules/_io/bytesio.c"
    pyFns := ["bytesio_getstate", "bytesio_setstate", "bytesio_setstate_lock_held", "BytesIO.__getstate__"]
    statement := "For a C BytesIO, __setstate__(__getstate__()) restores contents and position verbatim: with the position in Py_ssize_t and contents below the allocation bound, setstate into any open export-free BytesIO reproduces buf and pos."
    source := "invariant: pickle round trip (__reduce__/__setstate__)"
    status := .proven, prop := ``BytesIOPickleRoundTrip, thm := some ``bytesIOPickleRoundTrip_proven
    notes := "Hypotheses are C type invariants: pos fits Py_ssize_t, buffer below the allocation bound. _pyio BytesIO has no __setstate__, so this is the C object only." },
  { id := "pyio-bytesio-release-exports", pyFile := "Modules/_io/bytesio.c"
    pyFns := ["bytesiobuf_getbuffer", "bytesiobuf_getbuffer_lock_held", "bytesiobuf_releasebuffer"]
    statement := "getbuffer() raises the export count above zero (blocking resizes); releasing the view restores the previous count and leaves contents and position unchanged, so resizing is possible again (C object; _pyio memoryview over the bytearray)."
    source := "Doc/library/io.rst (BytesIO.getbuffer note); invariant: export count round trip"
    status := .proven, prop := ``BytesIOReleaseExports, thm := some ``bytesIOReleaseExports_proven },
  -- StringIO: remaining methods (inquiries, unsupported ops, pickle)
  { id := "pyio-stringio-inquiries", pyFile := "Modules/_io/stringio.c"
    pyFns := ["_io_StringIO_readable_impl", "_io_StringIO_writable_impl", "_io_StringIO_seekable_impl",
      "_io__IOBase_isatty_impl", "TextIOWrapper.readable", "TextIOWrapper.writable",
      "TextIOWrapper.seekable", "TextIOWrapper.isatty"]
    statement := "On an open StringIO readable(), writable(), seekable() return True and isatty() False; on a closed StringIO each raises ValueError (both twins, every state)."
    source := "Doc/library/io.rst (IOBase.readable/writable/seekable/isatty); invariant: both twins agree"
    status := .proven, prop := ``StringIOInquiries, thm := some ``stringIOInquiries_proven },
  { id := "pyio-stringio-unsupported", pyFile := "Modules/_io/textio.c"
    pyFns := ["_io__TextIOBase_detach_impl", "_io__TextIOBase_encoding_get_impl",
      "_io__TextIOBase_errors_get_impl", "_io__IOBase_fileno_impl", "TextIOWrapper.fileno",
      "StringIO.encoding", "StringIO.errors", "StringIO.detach"]
    statement := "On a StringIO (both twins), detach() and fileno() raise io.UnsupportedOperation, while the encoding and errors attributes are None (an in-memory text buffer has no underlying binary buffer, encoding or error handler)."
    source := "Doc/library/io.rst (TextIOBase.detach/fileno/encoding/errors: 'not supported by an in-memory text buffer')"
    status := .proven, prop := ``StringIOUnsupported, thm := some ``stringIOUnsupported_proven },
  { id := "pyio-stringio-pickle-roundtrip", pyFile := "Modules/_io/stringio.c"
    pyFns := ["_io_StringIO___getstate___impl", "_io_StringIO___setstate___impl", "_io_StringIO___init___impl"]
    statement := "For a C StringIO, whenever __init__ accepts the saved value and newline, __setstate__(__getstate__()) restores contents and position verbatim, applying no newline translation a second time (position in Py_ssize_t)."
    source := "invariant: pickle round trip"
    status := .proven, prop := ``StringIOPickleRoundTrip, thm := some ``stringIOPickleRoundTrip_proven }
]

def entries : List Entry := coreEntries ++ textEntries ++ bufferedEntries ++ fileEntries

end PyLean.PyIO
