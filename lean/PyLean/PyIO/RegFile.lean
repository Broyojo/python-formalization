import PyLean.Registry
import PyLean.PyIO.BaseProps

/-! Registry entries for FileIO, IOBase, RawIOBase, open, text_encoding. -/

namespace PyLean.PyIO

open PyLean.Registry

def fileEntries : List Entry := [
  { id := "pyio-base-inquiries-false", pyFile := "Modules/_io/iobase.c"
    pyFns := ["_io__IOBase_seekable_impl", "_io__IOBase_readable_impl", "_io__IOBase_writable_impl",
      "IOBase.seekable", "IOBase.readable", "IOBase.writable"]
    statement := "On an IOBase object whose class does not override them, seekable(), readable() and writable() return False and leave the object unchanged (both twins)."
    source := "Doc/library/io.rst (IOBase.readable/seekable/writable); invariant: C and Python twins agree"
    status := .proven, prop := ``BaseInquiriesFalse, thm := some ``baseInquiriesFalse_proven },
  { id := "pyio-base-checks-unsupported", pyFile := "Modules/_io/iobase.c"
    pyFns := ["iobase_check_seekable", "iobase_check_readable", "iobase_check_writable",
      "_PyIOBase_check_seekable", "_PyIOBase_check_readable", "_PyIOBase_check_writable",
      "IOBase._checkSeekable", "IOBase._checkReadable", "IOBase._checkWritable"]
    statement := "With the default inquiries, _checkSeekable, _checkReadable and _checkWritable raise UnsupportedOperation with the same message in both twins and leave the object unchanged."
    source := "invariant: C and Python twins agree"
    status := .proven, prop := ``BaseChecksUnsupported, thm := some ``baseChecksUnsupported_proven },
  { id := "pyio-base-unsupported-ops", pyFile := "Modules/_io/iobase.c"
    pyFns := ["iobase_unsupported", "_io__IOBase_seek_impl", "_io__IOBase_tell_impl",
      "_io__IOBase_truncate_impl", "_io__IOBase_fileno_impl", "IOBase._unsupported", "IOBase.seek",
      "IOBase.tell", "IOBase.truncate", "IOBase.fileno"]
    statement := "seek, tell, truncate and fileno on a bare IOBase raise UnsupportedOperation in both twins and leave the object unchanged; only the exception class is shared, not the message."
    source := "Doc/library/io.rst (IOBase: methods 'raise UnsupportedOperation'); invariant: same class in both twins"
    status := .proven, prop := ``BaseUnsupportedOps, thm := some ``baseUnsupportedOps_proven },
  { id := "pyio-base-closed-protocol", pyFile := "Modules/_io/iobase.c"
    pyFns := ["iobase_is_closed", "iobase_closed_get", "iobase_check_closed", "_PyIOBase_check_closed",
      "iobase_enter", "iobase_iter", "_io__IOBase_isatty_impl", "IOBase.closed", "IOBase._checkClosed",
      "IOBase.__enter__", "IOBase.__iter__", "IOBase.isatty"]
    statement := "closed reports the closed flag. On an open object __enter__, __iter__ and _checkClosed succeed and isatty() is False; on a closed object each raises ValueError('I/O operation on closed file.') (both twins)."
    source := "Doc/library/io.rst (IOBase.closed, IOBase: 'calling any method on a closed stream ... ValueError'); invariant: C and Python twins agree"
    status := .proven, prop := ``BaseClosedProtocol, thm := some ``baseClosedProtocol_proven }
]

end PyLean.PyIO
