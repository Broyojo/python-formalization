import PyLean.Registry
import PyLean.PyIO.BufProps

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
    statement := "readline(size) with size >= 0 on a _pyio.BufferedReader or BufferedRandom never returns more than size bytes, for every raw stream and every buffer state."
    source := "Lib/_pyio.py:516 (IOBase.readline: 'at most size bytes will be read'); Doc/library/io.rst (IOBase.readline)"
    status := .proven, prop := ``PyBufferedReadlineBound, thm := some ``pyBufferedReadlineBound_proven
    notes := "Goes through the peek branch of nreadahead, which 3.15 bounded by size - len(res); with the 3.14.7 bound, size, it overshoots when a line is built over several peeks." }
]

end PyLean.PyIO
