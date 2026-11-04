import PyLean.Registry
import PyLean.PyIO.BaseProps

/-! Registry entries for FileIO, IOBase, RawIOBase, open, text_encoding. -/

namespace PyLean.PyIO

open PyLean.Registry

def fileEntries : List Entry := [
  { id := "pyio-base-inquiries-false", pyFile := "Modules/_io/iobase.c"
    pyFns := ["_io__IOBase_seekable_impl", "_io__IOBase_readable_impl", "_io__IOBase_writable_impl"]
    statement := "On an IOBase object whose class does not override them, seekable(), readable() and writable() return False and leave the object unchanged (both twins)."
    source := "Doc/library/io.rst (IOBase.readable/seekable/writable); invariant: C and Python twins agree"
    status := .proven, prop := ``BaseInquiriesFalse, thm := some ``baseInquiriesFalse_proven
    notes := "The _pyio bodies are `return False` and are excluded as trivial in the inventory." },
  { id := "pyio-base-checks", pyFile := "Lib/_pyio.py"
    pyFns := ["IOBase._checkSeekable", "IOBase._checkReadable", "IOBase._checkWritable",
      "iobase_check_seekable", "iobase_check_readable", "iobase_check_writable",
      "_PyIOBase_check_seekable", "_PyIOBase_check_readable", "_PyIOBase_check_writable"]
    statement := "_checkSeekable, _checkReadable and _checkWritable, over an inquiry that may be overridden to answer any object or raise: each twin calls the object's own inquiry once and propagates its exception; _pyio tests the answer's truth, returns None for a truthy one and raises UnsupportedOperation(msg), or the default 'File or stream is not seekable./readable./writable.' when msg is None; C accepts only the object True and returns it, refuses anything else with the default message, and refuses a msg argument with TypeError('_IOBase._checkSeekable() takes no arguments (1 given)') before asking. With the base inquiries both raise the default message and change nothing."
    source := "the bodies _pyio.py:430-463 and iobase.c:414-494, :845-848; Doc/library/io.rst (IOBase.seekable: 'If False, seek(), tell() and truncate() will raise OSError')"
    status := .proven, prop := ``BaseChecks, thm := some ``baseChecks_proven
    notes := "Smoke-tested on 3.15.2: seekable() True gives True in C and None in _pyio; readable() 1 gives UnsupportedOperation in C and None in _pyio; _checkSeekable('m') gives TypeError in C and UnsupportedOperation('m') in _pyio." },
  { id := "pyio-base-checks-twins", pyFile := "Lib/_pyio.py"
    pyFns := ["IOBase._checkSeekable", "_PyIOBase_check_seekable"]
    statement := "For every answer of the object's seekable(), _checkSeekable() returns the same value or raises the same exception class in both twins."
    source := "invariant: C accelerator vs pure-Python twin"
    status := .refuted, prop := ``BaseChecksTwins, thm := some ``baseChecksTwins_refuted
    bug := some "pyio-buffered-init-inquiry-truthy"
    notes := "seekable() returning 1: iobase.c:419 refuses it (`res != Py_True`), _pyio.py:433 accepts it. The same check behind the Buffered* constructors." },
  { id := "pyio-base-unsupported-ops", pyFile := "Lib/_pyio.py"
    pyFns := ["iobase_unsupported", "_io__IOBase_seek_impl", "_io__IOBase_truncate_impl",
      "_io__IOBase_fileno_impl", "IOBase._unsupported", "IOBase.seek", "IOBase.truncate", "IOBase.fileno"]
    statement := "seek, truncate and fileno on a bare IOBase, and tell when seek is not overridden, leave the object unchanged and raise UnsupportedOperation with the method name in C ('seek', 'truncate', 'fileno') and with '<class name>.<method>() not supported' in _pyio, for every class name."
    source := "Doc/library/io.rst (IOBase: methods 'raise UnsupportedOperation'); the bodies iobase.c:87-91, :119-125, :153-159, :528-533 and _pyio.py:341-344, :348-376, :495-501"
    status := .proven, prop := ``BaseUnsupportedOps, thm := some ``baseUnsupportedOps_proven
    notes := "Smoke-tested on 3.15.2 with a subclass S: 'S.seek() not supported' and so on in _pyio, 'seek' in C." },
  { id := "pyio-base-tell-dispatch", pyFile := "Lib/_pyio.py"
    pyFns := ["IOBase.tell", "_io__IOBase_tell_impl"]
    statement := "tell() is self.seek(0, 1) in both twins: with an overriding seek it calls that seek exactly once with (0, 1) and returns what it returned, or raises what it raised; without one it raises the base seek's UnsupportedOperation."
    source := "Doc/library/io.rst (IOBase.tell: 'Return the current stream position'); the bodies _pyio.py:366-368 and iobase.c:134-138"
    status := .proven, prop := ``BaseTellDispatch, thm := some ``baseTellDispatch_proven },
  { id := "pyio-base-closed-protocol", pyFile := "Lib/_pyio.py"
    pyFns := ["iobase_is_closed", "iobase_closed_get", "iobase_check_closed", "_PyIOBase_check_closed",
      "iobase_enter", "iobase_iter", "_io__IOBase_isatty_impl", "IOBase._checkClosed",
      "IOBase.__enter__", "IOBase.__iter__", "IOBase.isatty"]
    statement := "Over a closed attribute that is the base property or an override answering any object or raising: __enter__ and __iter__ return self, _checkClosed None and isatty() False when closed is falsy; a truthy closed raises ValueError('I/O operation on closed file.'), or ValueError(msg) for _pyio's _checkClosed(msg); an exception from closed propagates, except that C counts an AttributeError as open; C's _checkClosed refuses a msg argument with TypeError. None of them changes the object."
    source := "Doc/library/io.rst (IOBase.closed; IOBase: 'calling any method on a closed stream ... ValueError'); the bodies _pyio.py:473-485, :503-509, :555-557 and iobase.c:197-226, :499-505, :544-550, :680-686"
    status := .proven, prop := ``BaseClosedProtocol, thm := some ``baseClosedProtocol_proven
    notes := "self is encoded as None for __enter__ and __iter__ (the difftest maps `f.__enter__() is f` to None). Smoke-tested on 3.15.2: closed returning 2 raises in both; closed raising AttributeError gives None in C and AttributeError in _pyio." },
  { id := "pyio-base-writelines", pyFile := "Lib/_pyio.py"
    pyFns := ["IOBase.writelines"]
    statement := "_pyio's IOBase.writelines(lines), over a fallible closed, fallible write calls and an iterator that may raise after its lines: if _checkClosed() fails its exception is raised before any write; otherwise write is called with each line in order until one raises, whose exception propagates with no later line written; if none raises, the iterator's exception propagates, or the result is None."
    source := "Doc/library/io.rst (IOBase.writelines: 'Write a list of lines to the stream'); the body _pyio.py:583-591"
    status := .proven, prop := ``BaseWritelines, thm := some ``baseWritelines_proven
    notes := "C's _io__IOBase_writelines (iobase.c:792-829) differs only by retrying a write that raised EINTR (iobase.c:816-818); the difftest compares both." },
  { id := "pyio-iobase-readline-readahead", pyFile := "Lib/_pyio.py"
    pyFns := ["IOBase.readline"]
    statement := "After a non-empty peek, IOBase.readline asks to read through the first newline of what peek returned, but no more than size - len(res) bytes, or simply through the first newline if size is negative; the C and Python twins compute the same number."
    source := "invariant: C accelerator vs pure-Python twin; Lib/_pyio.py:516 ('at most size bytes will be read'); iobase.c:612"
    status := .proven, prop := ``ReadlineReadahead, thm := some ``readlineReadahead_proven
    notes := "States the step 3.15 changed. The whole loop is bounded in pyio-bufferedreader-readline-bound." }
]

end PyLean.PyIO
