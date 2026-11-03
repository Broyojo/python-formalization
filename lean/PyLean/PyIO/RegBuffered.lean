import PyLean.Registry
import PyLean.PyIO.BufInit

/-! Registry entries for BufferedReader/Writer/Random/RWPair, BufferedIOBase. -/

namespace PyLean.PyIO

open PyLean.Registry

def bufferedEntries : List Entry := [
  { id := "pyio-bufferedreader-readinto-twins", pyFile := "Lib/_pyio.py"
    pyFns := ["BufferedReader._readinto", "BufferedIOBase.readinto"]
    statement := "For all contents and every positive buffer size, after read(k) on a new BufferedReader, io and _pyio agree on whether readinto of an n-byte buffer succeeds."
    source := "invariant: C accelerator vs pure-Python twin"
    status := .refuted, prop := ``BufferedReaderReadintoTwins, thm := some ``bufferedReaderReadintoTwins_refuted
    bug := some "pyio-bufferedreader-readinto-valueerror"
    notes := "BufferedReader(BytesIO(b'abcdefghij'), 3): read(1), readinto(bytearray(3)): C returns 3, _pyio raises ValueError because avail is bounded by len(buf) and not by the space left (_pyio.py:1194). The comparison is of success only, so it credits the _pyio functions whose failure it shows, not the C ones. Duplicate of gh-155074." },
  { id := "pyio-bufferedreader-readline-bound", pyFile := "Lib/_pyio.py"
    pyFns := ["IOBase.readline"]
    statement := "readline(size) with size >= 0 on a _pyio.BufferedReader, BufferedWriter or BufferedRandom never returns more than size bytes, for every raw stream (scripted, lying, re-entrant), every re-entry handler and every buffer state."
    source := "Lib/_pyio.py:516 (IOBase.readline: 'at most size bytes will be read'); Doc/library/io.rst (IOBase.readline)"
    status := .proven, prop := ``PyBufferedReadlineBound, thm := some ``pyBufferedReadlineBound_proven
    notes := "Goes through the peek branch of nreadahead, which 3.15 bounded by size - len(res); with the 3.14.7 bound, size, it overshoots when a line is built over several peeks." },
  { id := "pyio-buffered-c-no-crash", pyFile := "Modules/_io/bufferedio.c"
    pyFns := ["_io__Buffered_read_impl", "_io__Buffered_detach_impl", "_bufferedreader_raw_read"]
    statement := "No sequence of operations on io.BufferedReader, BufferedWriter or BufferedRandom over a raw stream written in Python kills the interpreter, whatever the raw answers and whatever it calls back into."
    source := "invariant: no crash from pure Python code"
    status := .refuted, prop := ``BufferedCNoCrash, thm := some ``bufferedCNoCrash_refuted
    bug := some "pyio-buffered-reentrant-detach-crash"
    notes := "raw.closed, read by CHECK_CLOSED in read(1) before the lock, calls detach(): self->raw is NULL when _bufferedreader_raw_read calls readinto (SIGSEGV). Duplicate of gh-154997 (open)." },
  { id := "pyio-buffered-c-no-crash-reinit", pyFile := "Modules/_io/bufferedio.c"
    pyFns := ["_buffered_init", "_io_BufferedReader___init___impl", "_io__Buffered_read_impl",
      "_bufferedreader_read_generic", "_bufferedreader_fill_buffer"]
    statement := "No sequence of operations on io.BufferedReader, BufferedWriter or BufferedRandom over a raw stream written in Python kills the interpreter, whatever the raw answers and whatever it calls back into (here: __init__)."
    source := "invariant: no crash from pure Python code"
    status := .refuted, prop := ``BufferedCNoCrash, thm := some ``bufferedCNoCrash_refuted_reinit
    bug := some "pyio-buffered-reentrant-init-free"
    notes := "raw.readinto, called by read(1) under the lock, calls buf.__init__(raw, 8): _buffered_init (:846-860) frees the buffer and lock the read holds and makes a free new lock; the read's LEAVE_BUFFERED unlocks it and PyMutex_Unlock aborts. reinit_unlocked_ok: the same __init__ from CHECK_CLOSED, before the lock, is harmless (both measured on 3.15.2)." },
  { id := "pyio-buffered-c-no-crash-init-size0", pyFile := "Modules/_io/bufferedio.c"
    pyFns := ["_bufferedreader_read_generic", "_io_BufferedReader___init___impl", "_buffered_init"]
    statement := "No sequence of operations on io.BufferedReader, BufferedWriter or BufferedRandom over a raw stream written in Python kills the interpreter (here: a re-entered __init__ with buffer_size 0)."
    source := "invariant: no crash from pure Python code"
    status := .refuted, prop := ``BufferedCNoCrash, thm := some ``bufferedCNoCrash_refuted_size0
    bug := some "pyio-buffered-reentrant-init-size0"
    notes := "raw.readinto, called by read(10) on a reader of size 3, calls buf.__init__(raw, 0): :1605 stores buffer_size 0 before :841 refuses it, and MINUS_LAST_BLOCK (:408-411, buffer_mask 0) divides by it: SIGFPE (measured on 3.15.2 and main)." },
  { id := "pyio-buffered-c-no-hang", pyFile := "Modules/_io/bufferedio.c"
    pyFns := ["_io_BufferedWriter_write_impl", "_io_BufferedWriter___init___impl", "_buffered_init"]
    statement := "No sequence of operations on io.BufferedReader, BufferedWriter or BufferedRandom blocks the thread forever, whatever the raw stream answers and calls back into."
    source := "invariant: no hang"
    status := .refuted, prop := ``BufferedCNoHang, thm := some ``bufferedCNoHang_refuted
    bug := some "pyio-buffered-reentrant-init-size0"
    notes := "raw.write, called by write(10 bytes) on a writer of size 5, calls buf.__init__(raw, 0): buffer_size becomes 0 and `while (remaining >= self->buffer_size)` (:2186) calls raw.write(b'') forever (measured on 3.15.2 and main)." },
  { id := "pyio-bufferedreader-no-uninit", pyFile := "Modules/_io/bufferedio.c"
    pyFns := ["_buffered_init", "_io__Buffered_peek_impl", "_bufferedreader_peek_unlocked",
      "_bufferedreader_fill_buffer", "_bufferedreader_raw_read"]
    statement := "Every byte io.BufferedReader returns was stored by somebody: for every raw stream, buffer size and operation sequence, no result contains memory nobody wrote."
    source := "invariant: no uninitialized memory reaches Python objects; twin: _pyio returns zero bytes"
    status := .refuted, prop := ``BufferedReaderNoUninit, thm := some ``bufferedReaderNoUninit_refuted
    bug := some "pyio-bufferedreader-uninitialized-read"
    notes := "The reproducer's path: readinto answers len(b) and stores nothing; peek() on a fresh 16-byte reader returns the 16 bytes of the PyMem_Malloc buffer (bufferedio.c:848) that _bufferedreader_fill_buffer counted as read. lyingRaw_stale proves the deterministic stale-byte half of the reproducer for both twins." },
  { id := "pyio-bufferedreader-read1-no-uninit", pyFile := "Modules/_io/bufferedio.c"
    pyFns := ["_io__Buffered_read1_impl", "_bufferedreader_raw_read"]
    statement := "read1(n) on io.BufferedReader never returns memory nobody wrote, for every raw stream, buffer size and n."
    source := "invariant: no uninitialized memory reaches Python objects"
    status := .refuted, prop := ``BufferedRead1NoUninit, thm := some ``bufferedRead1NoUninit_refuted
    bug := some "pyio-bufferedreader-uninitialized-read"
    notes := "readinto answers 1 and stores nothing; read1(1) on a fresh reader keeps one byte of a PyBytesWriter nobody filled (bufferedio.c:1074-1091). On a given run the byte may happen to be 0." },
  { id := "pyio-buffered-pyio-no-hang", pyFile := "Lib/_pyio.py"
    pyFns := ["BufferedReader.read"]
    statement := "No sequence of operations on _pyio.BufferedReader, BufferedWriter or BufferedRandom blocks the thread forever, for every raw stream, including one that calls back into the object."
    source := "invariant: no hang; twin: io raises RuntimeError('reentrant call inside ...'), bufferedio.c:299-303"
    status := .refuted, prop := ``PyBufferedNoHang, thm := some ``pyBufferedNoHang_refuted
    bug := some "pyio-buffered-pyio-reentrant-deadlock"
    notes := "raw.readinto calls read(1) on the reader that is reading: _read_lock (_thread.allocate_lock, not re-entrant) is taken twice. reenteringRaw_c proves the C twin raises RuntimeError and completes the outer read." },
  { id := "pyio-bufferedrandom-failed-seek-twins", pyFile := "Lib/_pyio.py"
    pyFns := ["BufferedRandom.seek"]
    statement := "For every contents, buffer size, read length and target, io.BufferedRandom and _pyio.BufferedRandom report the same tell() after read(k) and a seek(p) that the raw stream refuses."
    source := "invariant: C accelerator vs pure-Python twin; an operation that raises leaves the position where it was"
    status := .refuted, prop := ``RandomFailedSeekTwins, thm := some ``randomFailedSeekTwins_refuted
    bug := some "pyio-bufferedrandom-failed-seek-duplicates"
    notes := "d = b'0123456789', size 8, read(2), seek(-1) raises: C tell() is 2, _pyio 0. _pyio.py:1434-1437 rewinds the raw over the read-ahead, then :1440 raises before :1441-1442 empty the read buffer, which is kept: later reads return its bytes twice." },
  { id := "pyio-bufferedreader-init-inquiry-twins", pyFile := "Modules/_io/bufferedio.c"
    pyFns := ["_io_BufferedReader___init___impl", "BufferedReader.__init__"]
    statement := "io.BufferedReader and _pyio.BufferedReader accept the same raw streams, for every raw stream (whatever readable() answers, raises or calls) and buffer size."
    source := "invariant: C accelerator vs pure-Python twin"
    status := .refuted, prop := ``ReaderInitTwins, thm := some ``readerInitTwins_refuted
    bug := some "pyio-buffered-init-inquiry-truthy"
    notes := "readable() returning 1: _PyIOBase_check_readable (iobase.c:446-461) refuses anything but True, _pyio.py:1052 accepts any truthy value." },
  { id := "pyio-bufferedwriter-init-inquiry-twins", pyFile := "Modules/_io/bufferedio.c"
    pyFns := ["_io_BufferedWriter___init___impl", "BufferedWriter.__init__"]
    statement := "io.BufferedWriter and _pyio.BufferedWriter accept the same raw streams, for every raw stream and buffer size."
    source := "invariant: C accelerator vs pure-Python twin"
    status := .refuted, prop := ``WriterInitTwins, thm := some ``writerInitTwins_refuted
    bug := some "pyio-buffered-init-inquiry-truthy"
    notes := "writable() returning 1: iobase.c:479-494 refuses it, _pyio.py:1248 accepts it." },
  { id := "pyio-bufferedrandom-init-inquiry-twins", pyFile := "Modules/_io/bufferedio.c"
    pyFns := ["_io_BufferedRandom___init___impl", "BufferedRandom.__init__"]
    statement := "io.BufferedRandom and _pyio.BufferedRandom accept the same raw streams, for every raw stream and buffer size."
    source := "invariant: C accelerator vs pure-Python twin"
    status := .refuted, prop := ``RandomInitTwins, thm := some ``randomInitTwins_refuted
    bug := some "pyio-buffered-init-inquiry-truthy"
    notes := "seekable() returning 1, asked first by both: iobase.c:413-428 refuses it, _pyio.py:1426 (raw._checkSeekable, :430-435) accepts it." },
  { id := "pyio-buffered-c-init-success", pyFile := "Modules/_io/bufferedio.c"
    pyFns := ["_io_BufferedReader___init___impl", "_io_BufferedWriter___init___impl",
              "_io_BufferedRandom___init___impl", "_buffered_init"]
    statement := "For io.BufferedReader, BufferedWriter and BufferedRandom over a raw stream whose seekable(), readable() and writable() answer True, whose tell() answers its position and that calls nothing back, for every buffer size: size <= 0 is refused with ValueError('buffer size must be strictly positive') after the inquiries; a size the allocator refuses raises MemoryError; otherwise construction succeeds with ok set, the raw attached, buffer_size = size, a buffer of size bytes, a free lock, buffer_mask = size - 1 exactly for a power of two, abs_pos = the raw's tell() when it fits Py_off_t (else 0, the failure cleared), an empty read buffer for a reader and an empty write buffer at 0 for a writer, and the raw has seen exactly the type's inquiries and one tell(), with no read, write or seek."
    source := "doc: the constructors' documented arguments (raw, buffer_size); the bodies bufferedio.c:1592-1620, :1944-1974, :2485-2520 and _buffered_init :838-872"
    status := .proven, prop := ``CInitSucceeds, thm := some ``cInitSucceeds_proven
    notes := "Smoke-tested on 3.15.2: difftest cases with no operations (sizes 1, 3, 8, 8192, 0, -1, -5, 2**48, 2**48+1, logs as stated), a raw at position 5 whose tell() the object then reports, and a raw whose tell() answers 2**63, which constructs. The allocator's refusal is the module's allocation assumption (memLimit = 2**48, PyIO/Basic.lean), about the machine; lock allocation (:855-858) is assumed to succeed." },
  { id := "pyio-buffered-py-init-success", pyFile := "Lib/_pyio.py"
    pyFns := ["BufferedReader.__init__", "BufferedWriter.__init__", "BufferedRandom.__init__"]
    statement := "For _pyio.BufferedReader, BufferedWriter and BufferedRandom over the same raw streams, for every buffer size: size <= 0 is refused with ValueError('invalid buffer size') after the inquiry; every positive size is accepted (nothing is allocated), the object attached, buffer_size = size, a reader's read buffer empty at 0 with a free _read_lock, a writer's write buffer empty with a free _write_lock, and the raw has seen exactly the type's inquiries (seekable() first for BufferedRandom) and nothing else."
    source := "doc: the constructors' documented arguments; the bodies _pyio.py:1049-1060, :1247-1256, :1425-1428"
    status := .proven, prop := ``PyInitSucceeds, thm := some ``pyInitSucceeds_proven
    notes := "Smoke-tested on 3.15.2 with the C cases above: _pyio accepts 2**48 and 2**48+1 where C raises MemoryError, and asks no tell()." },
  { id := "pyio-buffered-raw-read-checks", pyFile := "Modules/_io/bufferedio.c"
    pyFns := ["_bufferedreader_raw_read", "_PyIO_trap_eintr"]
    statement := "_bufferedreader_raw_read never reports a count outside [0, len] except -2 for None and stores no more than it reports, for every raw answer, state and re-entry handler; an int answer v is the count when 0 <= v <= len and is refused with OSError 'raw readinto() returned invalid length' otherwise; an exception that is an instance of OSError (by its class's MRO, so for every class hierarchy) with errno EINTR is retried with the same arguments and every other exception (InterruptedError('x') without errno included) propagates unchanged."
    source := "invariant: what is copied out of the buffer was counted as read (bufferedio.c:1661-1666, :1639-1641, :878-901)"
    status := .proven, prop := ``RawReadChecks, thm := some ``rawReadChecks_proven
    notes := "Measured on 3.15.2: InterruptedError('x') and MyOSError('x') propagate; PermissionError, InterruptedError, FileExistsError, ConnectionResetError, io.UnsupportedOperation and a user OSError subclass with errno EINTR are retried. The exception's class is given by its MRO (RStep.raise), so the statement quantifies over every hierarchy." },
  { id := "pyio-buffered-raw-write-checks", pyFile := "Modules/_io/bufferedio.c"
    pyFns := ["_bufferedwriter_raw_write"]
    statement := "_bufferedwriter_raw_write never reports a count outside [0, len(b)] except -2 for None, for every raw answer, state and re-entry handler; an int answer is the count when in range and is refused with OSError 'raw write() returned invalid length' otherwise, with -1 for an int too large for Py_ssize_t."
    source := "invariant: write_pos only advances over bytes the raw stream accepted (bufferedio.c:2010-2017)"
    status := .proven, prop := ``RawWriteChecks, thm := some ``rawWriteChecks_proven },
  { id := "pyio-buffered-lock-discipline", pyFile := "Modules/_io/bufferedio.c"
    pyFns := ["_enter_buffered_busy"]
    statement := "Over the bodies of every method of BufferedReader, BufferedWriter and BufferedRandom, __init__ included, for every state, raw stream and re-entered call: a call ends with the same lock, held or not as it found it, unless the process died or __init__ replaced it by a new free lock; a call made with the lock free leaves it free unless the process died; and close(), or write() on a writer, made while this thread holds the lock is refused with RuntimeError('reentrant call inside <_io.Buffered...>') and changes nothing."
    source := "invariant: the lock serializes and a failure never leaves it held (bufferedio.c:294-338)"
    status := .proven, prop := ``LockDiscipline, thm := some ``lockDiscipline_proven
    notes := "Proved compositionally over every method body (BufLock.lean, Keeps), with re-entered calls run by stepC. Scope: one thread and no interpreter finalization, so the timed acquire and fatal error of :305-325 are not modelled." }
]

end PyLean.PyIO
