import PyLean.Registry
import PyLean.PyIO.Diff
import PyLean.PyIO.BytesTwins
import PyLean.PyIO.BytesSim
import PyLean.PyIO.BytesDocs
import PyLean.PyIO.Readlines
import PyLean.PyIO.StringTwins
import PyLean.PyIO.StringProps

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

def entries : List Entry := [
  -- BytesIO: C vs Python, layered
  { id := "pyio-bytesio-twins-agree", pyFile := "Modules/_io/bytesio.c"
    pyFns := ["_io.BytesIO", "_pyio.BytesIO"]
    statement := "For every initial value and operation sequence, io.BytesIO and _pyio.BytesIO return the same values and raise the same exceptions (class and message)."
    source := "invariant: C accelerator vs pure-Python twin (Lib/_pyio.py docstring: Python implementation of the io module)"
    status := .refuted, prop := ``BytesIOTwinsAgree, thm := some ``bytesIOTwinsAgree_refuted
    bug := some "pyio-bytesio-twin-argument-handling"
    notes := "Closed-file and argument errors use different messages, e.g. read() on a closed stream." },
  { id := "pyio-bytesio-twins-same-class", pyFile := "Modules/_io/bytesio.c"
    pyFns := ["_io.BytesIO.seek", "_pyio.BytesIO.seek"]
    statement := "The twins agree on every value and exception class, for all int arguments."
    source := "invariant: C accelerator vs pure-Python twin"
    status := .refuted, prop := ``BytesIOTwinsSameClass, thm := some ``bytesIOTwinsSameClass_refuted
    bug := some "pyio-bytesio-twin-argument-handling"
    notes := "seek(2**63): C OverflowError at Py_ssize_t conversion, Python seeks. Same for readlines/read/readline/truncate hints above sys.maxsize, and for whence outside C int." },
  { id := "pyio-bytesio-twins-same-class-in-range", pyFile := "Modules/_io/bytesio.c"
    pyFns := ["_io.BytesIO.getbuffer", "_io.BytesIO.write", "_io.BytesIO.truncate", "_io.BytesIO.close"]
    statement := "With every int argument in the range of its C converter, the twins agree on every value and exception class."
    source := "invariant: C accelerator vs pure-Python twin; Doc/library/io.rst getbuffer note"
    status := .refuted, prop := ``BytesIOTwinsSameClassInRange, thm := some ``bytesIOTwinsSameClassInRange_refuted
    bug := some "pyio-bytesio-getbuffer-blocks-overwrite"
    notes := "With a live getbuffer() view C refuses every write/truncate (BufferError), Python only those that resize." },
  { id := "pyio-bytesio-twins-same-class-no-export", pyFile := "Modules/_io/bytesio.c"
    pyFns := ["write_bytes_lock_held", "resize_buffer_lock_held"]
    statement := "In range and without getbuffer(), the twins agree on every value and exception class."
    source := "invariant: C accelerator vs pure-Python twin"
    status := .refuted, prop := ``BytesIOTwinsSameClassNoExport, thm := some ``bytesIOTwinsSameClassNoExport_refuted
    bug := some "pyio-bytesio-write-near-maxsize-systemerror"
    notes := "seek(sys.maxsize - 1); write(b'x'): SystemError and the stream is closed (3.14.7); fixed on main (gh-160781, gh-157242)." },
  { id := "pyio-bytesio-twins-same-class-no-alloc-fail", pyFile := "Lib/_pyio.py"
    pyFns := ["IOBase.readline", "_io.BytesIO.readline"]
    statement := "In range, without getbuffer() and without allocation failure (positions and write extents below the allocation bound), the twins agree on every value and exception class."
    source := "invariant: C accelerator vs pure-Python twin"
    status := .refuted, prop := ``BytesIOTwinsSameClassNoAllocFail, thm := some ``bytesIOTwinsSameClassNoAllocFail_refuted
    bug := some "pyio-bytesio-twin-argument-handling"
    notes := "readline(0) on a closed stream: C ValueError, Python b''." },
  { id := "pyio-bytesio-twins-same-class-core", pyFile := "Modules/_io/bytesio.c"
    pyFns := ["_io.BytesIO", "_pyio.BytesIO"]
    statement := "With int arguments in C range, no getbuffer(), no allocation failure and no readline(0) on a closed stream, io.BytesIO and _pyio.BytesIO return the same values and raise exceptions of the same classes for every initial value and operation sequence (read, read1, readline, readlines, readinto, write, seek, tell, truncate, getvalue, close, next, closed)."
    source := "invariant: C accelerator vs pure-Python twin"
    status := .proven, prop := ``BytesIOTwinsSameClassCore, thm := some ``bytesIOTwinsSameClassCore_proven
    notes := "Each hypothesis is exactly one of the refutations above. readline(0) on a closed stream is excluded by IOBase's 'calling any method on a closed stream is undefined' (_pyio.py:323-324). Proof: simulation, both twins keep the same buffer, position and closed flag; readline/readlines/next go through lineLen." },
  -- BytesIO: documented behaviour
  { id := "pyio-bytesio-tell-after-write", pyFile := "Modules/_io/bytesio.c"
    pyFns := ["_io.BytesIO.write", "_pyio.BytesIO.write"]
    statement := "Whenever write(b) succeeds (any state, any b) it returns len(b) and the position advances by exactly len(b), in both twins."
    source := "Doc/library/io.rst BufferedIOBase.write ('Return the number of bytes written, which is always the length of b in bytes')"
    status := .proven, prop := ``TellAfterWrite, thm := some ``tellAfterWrite_proven },
  { id := "pyio-bytesio-read-after-seek", pyFile := "Modules/_io/bytesio.c"
    pyFns := ["_io.BytesIO.seek", "_io.BytesIO.read", "_pyio.BytesIO.seek", "_pyio.BytesIO.read"]
    statement := "On an open BytesIO, seek(p) followed by read(n) returns buf[p:p+n] for every p, n >= 0 (C: in Py_ssize_t), including p beyond the end, in both twins."
    source := "Doc/library/io.rst IOBase.seek / BufferedIOBase.read"
    status := .proven, prop := ``ReadAfterSeek, thm := some ``readAfterSeek_proven },
  { id := "pyio-truncate-keeps-position", pyFile := "Modules/_io/bytesio.c"
    pyFns := ["_io.BytesIO.truncate", "_pyio.BytesIO.truncate", "_io.StringIO.truncate"]
    statement := "truncate(size) never moves the stream position, for every state and argument and whatever the outcome (C and Python BytesIO, C StringIO)."
    source := "Doc/library/io.rst IOBase.truncate ('The current stream position isn't changed')"
    status := .proven, prop := ``TruncateKeepsPosition, thm := some ``truncateKeepsPosition_proven },
  { id := "pyio-bytesio-getvalue-zero-fill", pyFile := "Modules/_io/bytesio.c"
    pyFns := ["_io.BytesIO.write", "_pyio.BytesIO.write", "getvalue"]
    statement := "After a successful non-empty write(b) on an open BytesIO, getvalue() is the old contents overwritten by b at the old position, with every byte between the old end and that position zero, and length max(old length, pos + len(b)); an empty write changes nothing (both twins)."
    source := "Doc/library/io.rst IOBase.seek ('seeking past the end ... zero-filled') and BytesIO"
    status := .proven, prop := ``GetvalueZeroFill, thm := some ``getvalueZeroFill_proven },
  { id := "pyio-bytesio-writes-concat", pyFile := "Modules/_io/bytesio.c"
    pyFns := ["_io.BytesIO.write", "_pyio.BytesIO.write", "getvalue"]
    statement := "Writing any byte strings one after another into BytesIO() leaves exactly their concatenation in getvalue() (both twins), while the total stays below the allocation bound."
    source := "Doc/library/io.rst BytesIO.getvalue"
    status := .proven, prop := ``WritesConcat, thm := some ``writesConcat_proven },
  -- readlines(hint)
  { id := "pyio-bytesio-readlines-hint-doc", pyFile := "Modules/_io/bytesio.c"
    pyFns := ["_io.BytesIO.readlines", "_pyio.IOBase.readlines"]
    statement := "For hint > 0, BytesIO.readlines(hint) returns whole lines until their total length exceeds hint, i.e. the documented prefix of readlines() (both twins)."
    source := "Doc/library/io.rst IOBase.readlines ('no more lines will be read if the total size ... of all lines so far exceeds hint')"
    status := .refuted, prop := ``BytesIOReadlinesHintDoc, thm := some ``bytesIOReadlinesHintDoc_refuted
    bug := some "pyio-readlines-hint-stops-early"
    notes := "C BytesIO (bytesio.c:618) and _pyio IOBase (_pyio.py:577) stop when the total reaches hint; C _IOBase (iobase.c:765) stops when it exceeds hint." },
  { id := "pyio-stringio-c-readlines-hint-doc", pyFile := "Modules/_io/iobase.c"
    pyFns := ["_io._IOBase.readlines", "_io.StringIO"]
    statement := "For every open C StringIO and hint > 0 (in Py_ssize_t), readlines(hint) returns the documented prefix of readlines(): whole lines until their total exceeds hint."
    source := "Doc/library/io.rst IOBase.readlines"
    status := .proven, prop := ``CStringIOReadlinesHintDoc, thm := some ``cStringIOReadlinesHintDoc_proven },
  -- StringIO: newline argument
  { id := "pyio-stringio-c-newline-legal", pyFile := "Modules/_io/stringio.c"
    pyFns := ["_io_StringIO___init___impl"]
    statement := "io.StringIO(newline=nl) succeeds exactly for nl in (None, '', '\\n', '\\r', '\\r\\n')."
    source := "Doc/library/io.rst TextIOWrapper/StringIO ('newline can be None, '', '\\n', '\\r', and '\\r\\n')"
    status := .refuted, prop := ``CStringIONewlineLegal, thm := some ``cStringIONewlineLegal_refuted
    bug := some "pyio-stringio-newline-embedded-nul"
    notes := "newline='\\x00' is accepted (as ''); '\\n\\x00' as '\\n', '\\r\\x00junk' as '\\r'." },
  { id := "pyio-stringio-c-newline-legal-no-nul", pyFile := "Modules/_io/stringio.c"
    pyFns := ["_io_StringIO___init___impl"]
    statement := "For every newline string without NUL characters (and None), io.StringIO(newline=nl) succeeds exactly for the five legal values."
    source := "Doc/library/io.rst StringIO"
    status := .proven, prop := ``CStringIONewlineLegalNoNul, thm := some ``cStringIONewlineLegalNoNul_proven
    notes := "The hypothesis is exactly the refuted case above; lone surrogates raise UnicodeEncodeError." },
  { id := "pyio-stringio-py-newline-legal", pyFile := "Lib/_pyio.py"
    pyFns := ["TextIOWrapper._check_newline", "StringIO.__init__"]
    statement := "_pyio.StringIO(newline=nl) succeeds exactly for nl in (None, '', '\\n', '\\r', '\\r\\n')."
    source := "Doc/library/io.rst StringIO"
    status := .proven, prop := ``PyStringIONewlineLegal, thm := some ``pyStringIONewlineLegal_proven },
  -- StringIO: C vs Python
  { id := "pyio-stringio-writes-twins", pyFile := "Modules/_io/stringio.c"
    pyFns := ["write_str", "_pyio.StringIO.write", "getvalue"]
    statement := "For every legal newline and every sequence of writes into StringIO(), io.StringIO and _pyio.StringIO agree on every result including getvalue()."
    source := "invariant: C accelerator vs pure-Python twin"
    status := .refuted, prop := ``StringIOWritesTwins, thm := some ``stringIOWritesTwins_refuted
    bug := some "pyio-stringio-newline-none-split-crlf"
    notes := "newline=None, write('a\\r'), write('\\nb'): C 'a\\n\\nb', Python 'a\\nb'." },
  { id := "pyio-stringio-writes-twins-not-none", pyFile := "Modules/_io/stringio.c"
    pyFns := ["write_str", "_pyio.TextIOWrapper.write", "_pyio.StringIO.getvalue"]
    statement := "For newline in ('', '\\n', '\\r', '\\r\\n') and every sequence of str writes into StringIO(), both twins return exactly the same results (write counts and getvalue())."
    source := "invariant: C accelerator vs pure-Python twin"
    status := .proven, prop := ``StringIOWritesTwinsNotNone, thm := some ``stringIOWritesTwinsNotNone_proven
    notes := "Hypotheses: code points below 0x110000 (str type invariant) and total length below the allocation bound. The newline=None exclusion is the refutation above. Uses UTF-8 (surrogatepass) decode(encode(s)) = s." },
  { id := "pyio-stringio-init-write-twins", pyFile := "Lib/_pyio.py"
    pyFns := ["StringIO.__init__", "TextIOWrapper.write"]
    statement := "StringIO(value, newline) followed by write(s) gives the same results in both twins."
    source := "invariant: C accelerator vs pure-Python twin"
    status := .refuted, prop := ``StringIOInitWriteTwins, thm := some ``stringIOInitWriteTwins_refuted
    bug := some "pyio-stringio-pyio-byte-positions"
    notes := "StringIO('é').write('x'): C 'x', _pyio UnicodeDecodeError (byte positions in the UTF-8 buffer)." },
  { id := "pyio-stringio-read-write-twins", pyFile := "Lib/_pyio.py"
    pyFns := ["TextIOWrapper.read", "TextIOWrapper.write"]
    statement := "For ASCII text, read(k) followed by write(s) gives the same results in both twins."
    source := "invariant: C accelerator vs pure-Python twin"
    status := .refuted, prop := ``StringIOReadWriteTwins, thm := some ``stringIOReadWriteTwins_refuted
    bug := some "pyio-stringio-pyio-write-after-read"
    notes := "StringIO('abcdef'), read(1), write('X'): C 'aXcdef', _pyio 'abcdefX' (read-ahead)." },
  { id := "pyio-stringio-tell-after-reads", pyFile := "Lib/_pyio.py"
    pyFns := ["TextIOWrapper.__next__", "IOBase.readlines", "TextIOWrapper.tell"]
    statement := "After any sequence of reads (read, readline, readlines, next) on an open StringIO with a legal newline, tell() returns a position in both twins."
    source := "invariant: C accelerator vs pure-Python twin"
    status := .refuted, prop := ``StringIOTellAfterReads, thm := some ``stringIOTellAfterReads_refuted
    bug := some "pyio-stringio-pyio-tell-after-readlines"
    notes := "_pyio: readlines(1) breaks out of 'for line in self' and leaves _telling false; related to gh-81217." },
  { id := "pyio-stringio-newlines-attr", pyFile := "Lib/_pyio.py"
    pyFns := ["TextIOWrapper.newlines"]
    statement := "On an open StringIO with a legal newline, after any reads, the newlines attribute is None, a str or a tuple in both twins (it never raises)."
    source := "Doc/library/io.rst TextIOBase.newlines"
    status := .refuted, prop := ``StringIONewlinesAttr, thm := some ``stringIONewlinesAttr_refuted
    bug := some "pyio-stringio-pyio-newlines-attributeerror"
    notes := "_pyio with newline '\\n', '\\r' or '\\r\\n': AttributeError once a decoder exists." }
]

end PyLean.PyIO
