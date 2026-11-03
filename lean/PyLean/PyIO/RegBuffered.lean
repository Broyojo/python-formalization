import PyLean.Registry
import PyLean.PyIO.BufChecks

/-! Registry entries for BufferedReader/Writer/Random/RWPair, BufferedIOBase. -/

namespace PyLean.PyIO

open PyLean.Registry

def bufferedEntries : List Entry := [
  { id := "pyio-bufferedreader-readinto-twins", pyFile := "Lib/_pyio.py"
    pyFns := ["BufferedReader.__init__", "BufferedReader.read", "BufferedReader._read_unlocked",
      "BufferedReader._peek_unlocked", "BufferedReader._readinto", "BufferedIOBase.readinto",
      "_io_BufferedReader___init___impl", "_buffered_init", "_buffered_raw_tell", "_io__Buffered_read_impl",
      "_bufferedreader_read_fast", "_bufferedreader_read_generic", "_bufferedreader_raw_read",
      "_bufferedreader_fill_buffer", "_buffered_readinto_generic", "_io__Buffered_readinto_impl"]
    statement := "For all contents and every positive buffer size, after read(k) on a new BufferedReader, io and _pyio agree on whether readinto of an n-byte buffer succeeds."
    source := "invariant: C accelerator vs pure-Python twin"
    status := .refuted, prop := ``BufferedReaderReadintoTwins, thm := some ``bufferedReaderReadintoTwins_refuted
    bug := some "pyio-bufferedreader-readinto-valueerror"
    notes := "BufferedReader(BytesIO(b'abcdefghij'), 3): read(1), readinto(bytearray(3)): C returns 3, _pyio raises ValueError because avail is bounded by len(buf) and not by the space left (_pyio.py:1194)." },
  { id := "pyio-bufferedreader-readline-bound", pyFile := "Lib/_pyio.py"
    pyFns := ["IOBase.readline"]
    statement := "readline(size) with size >= 0 on a _pyio.BufferedReader, BufferedWriter or BufferedRandom never returns more than size bytes, for every raw stream (scripted, lying, re-entrant), every re-entry handler and every buffer state."
    source := "Lib/_pyio.py:516 (IOBase.readline: 'at most size bytes will be read'); Doc/library/io.rst (IOBase.readline)"
    status := .proven, prop := ``PyBufferedReadlineBound, thm := some ``pyBufferedReadlineBound_proven
    notes := "Goes through the peek branch of nreadahead, which 3.15 bounded by size - len(res); with the 3.14.7 bound, size, it overshoots when a line is built over several peeks." },
  { id := "pyio-buffered-c-no-crash", pyFile := "Modules/_io/bufferedio.c"
    pyFns := ["_io_BufferedReader___init___impl", "_buffered_init", "_buffered_raw_tell",
      "_bufferedreader_reset_buf", "_io__Buffered_read_impl", "buffered_closed", "_io__Buffered_detach_impl",
      "_io__Buffered_simple_flush_impl", "_bufferedreader_read_fast", "_bufferedreader_read_generic",
      "_bufferedreader_fill_buffer", "_bufferedreader_raw_read"]
    statement := "No sequence of operations on io.BufferedReader, BufferedWriter or BufferedRandom over a raw stream written in Python kills the interpreter, whatever the raw answers and whatever it calls back into."
    source := "invariant: no crash from pure Python code"
    status := .refuted, prop := ``BufferedCNoCrash, thm := some ``bufferedCNoCrash_refuted
    bug := some "pyio-buffered-reentrant-detach-crash"
    notes := "raw.closed, read by CHECK_CLOSED in read(1) before the lock, calls detach(): self->raw is NULL when _bufferedreader_raw_read calls readinto (SIGSEGV). Duplicate of gh-154997 (open)." },
  { id := "pyio-bufferedreader-no-uninit", pyFile := "Modules/_io/bufferedio.c"
    pyFns := ["_io_BufferedReader___init___impl", "_buffered_init", "_buffered_raw_tell",
      "_bufferedreader_reset_buf", "_io__Buffered_read1_impl", "buffered_closed", "_bufferedreader_raw_read"]
    statement := "Every byte io.BufferedReader returns was stored by somebody: for every raw stream, buffer size and operation sequence, no result contains memory nobody wrote."
    source := "invariant: no uninitialized memory reaches Python objects; twin: _pyio returns zero bytes"
    status := .refuted, prop := ``BufferedReaderNoUninit, thm := some ``bufferedReaderNoUninit_refuted
    bug := some "pyio-bufferedreader-uninitialized-read"
    notes := "readinto answers 1 without storing anything; read1(1) returns the uninitialized byte of a fresh PyBytesWriter (bufferedio.c:1074-1091). lyingRaw_read shows the same through read(1) and the PyMem_Malloc buffer." },
  { id := "pyio-buffered-pyio-no-hang", pyFile := "Lib/_pyio.py"
    pyFns := ["BufferedReader.__init__", "BufferedReader.read", "BufferedReader._read_unlocked", "RawIOBase.read"]
    statement := "No sequence of operations on _pyio.BufferedReader, BufferedWriter or BufferedRandom blocks the thread forever, for every raw stream, including one that calls back into the object."
    source := "invariant: no hang; twin: io raises RuntimeError('reentrant call inside ...'), bufferedio.c:299-303"
    status := .refuted, prop := ``PyBufferedNoHang, thm := some ``pyBufferedNoHang_refuted
    bug := some "pyio-buffered-pyio-reentrant-deadlock"
    notes := "raw.readinto calls read(1) on the reader that is reading: _read_lock (_thread.allocate_lock, not re-entrant) is taken twice. reenteringRaw_c proves the C twin raises RuntimeError and completes the outer read." },
  { id := "pyio-bufferedrandom-failed-seek-twins", pyFile := "Lib/_pyio.py"
    pyFns := ["BufferedRandom.__init__", "BufferedRandom.read", "BufferedRandom.seek", "BufferedRandom.tell",
      "BufferedReader.tell", "_BufferedIOMixin.tell", "BufferedWriter.flush", "BufferedWriter._flush_unlocked",
      "_BufferedIOMixin.closed", "BufferedReader.read", "BufferedReader._read_unlocked",
      "BufferedReader._reset_read_buf", "BufferedReader.__init__", "BufferedWriter.__init__", "RawIOBase.read",
      "_io_BufferedRandom___init___impl", "_io__Buffered_seek_impl", "_buffered_raw_seek",
      "_bufferedwriter_flush_unlocked", "_bufferedwriter_reset_buf", "_io__Buffered_tell_impl"]
    statement := "For every contents, buffer size, read length and target, io.BufferedRandom and _pyio.BufferedRandom report the same tell() after read(k) and a seek(p) that the raw stream refuses."
    source := "invariant: C accelerator vs pure-Python twin; an operation that raises leaves the position where it was"
    status := .refuted, prop := ``RandomFailedSeekTwins, thm := some ``randomFailedSeekTwins_refuted
    bug := some "pyio-bufferedrandom-failed-seek-duplicates"
    notes := "d = b'0123456789', size 8, read(2), seek(-1) raises: C tell() is 2, _pyio 0. _pyio.py:1434-1437 rewinds the raw over the read-ahead, then :1440 raises before :1441-1442 empty the read buffer, which is kept: later reads return its bytes twice." },
  { id := "pyio-buffered-raw-read-checks", pyFile := "Modules/_io/bufferedio.c"
    pyFns := ["_bufferedreader_raw_read", "_PyIO_trap_eintr"]
    statement := "_bufferedreader_raw_read never reports a count outside [0, len] except -2 for None and stores no more than it reports, for every raw answer, state and re-entry handler; an int answer v is the count when 0 <= v <= len and is refused with OSError 'raw readinto() returned invalid length' otherwise; an InterruptedError is retried with the same arguments."
    source := "invariant: what is copied out of the buffer was counted as read (bufferedio.c:1661-1666, :1639-1641)"
    status := .proven, prop := ``RawReadChecks, thm := some ``rawReadChecks_proven },
  { id := "pyio-buffered-raw-write-checks", pyFile := "Modules/_io/bufferedio.c"
    pyFns := ["_bufferedwriter_raw_write"]
    statement := "_bufferedwriter_raw_write never reports a count outside [0, len(b)] except -2 for None, for every raw answer, state and re-entry handler; an int answer is the count when in range and is refused with OSError 'raw write() returned invalid length' otherwise, with -1 for an int too large for Py_ssize_t."
    source := "invariant: write_pos only advances over bytes the raw stream accepted (bufferedio.c:2010-2017)"
    status := .proven, prop := ``RawWriteChecks, thm := some ``rawWriteChecks_proven },
  { id := "pyio-buffered-lock-discipline", pyFile := "Modules/_io/bufferedio.c"
    pyFns := ["_enter_buffered_busy"]
    statement := "A locked section entered while this thread holds the lock does not run, leaves the object untouched and raises RuntimeError('reentrant call inside <_io.Buffered...>'); entered with the lock free it runs once with the lock held, and the lock is free afterwards on every path."
    source := "invariant: the lock serializes and a failure never leaves it held (bufferedio.c:294-338)"
    status := .proven, prop := ``LockDiscipline, thm := some ``lockDiscipline_proven
    notes := "Scope: the interpreter is not finalizing, so the timed acquire and fatal error of :305-325 are not modelled; single-threaded, so a held lock is held by this thread." }
]

end PyLean.PyIO
