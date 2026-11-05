import PyLean.Registry
import PyLean.Pickle.Diff
import PyLean.Pickle.SaveLongProps
import PyLean.Pickle.LongLineProps
import PyLean.Pickle.IntNarrow
import PyLean.Pickle.LongShortest
import PyLean.Pickle.TextRoundtrip
import PyLean.Pickle.OpenProps
import PyLean.Pickle.EncProps
import PyLean.Pickle.EncFrame
import PyLean.Pickle.EncRecProps
import PyLean.Pickle.CountedLong
import PyLean.Pickle.EncPins
import PyLean.Pickle.DecProps
import PyLean.Pickle.ToolsGen
import PyLean.Pickle.ToolsExact
import PyLean.Pickle.ToolsSteps
import PyLean.Pickle.ToolsDis
import PyLean.Pickle.DecChunk

/-!
`Lib/pickle.py` vs `Modules/_pickle.c`, CPython 3.15.2, on plain data: None,
bool, int, str, bytes, bytearray, tuple, list, dict, set and frozenset, under
protocols 0-5. Floats, custom classes, reduce and anything that runs code are
out of scope. The encoder mirrors (`EncRec.lean`) carry both recursion limits (C stack room,
Python frames) and the `protocol` and `buffer_callback` arguments; `fix_imports=False`, file
output, `fast` mode, `persistent_id`, `reducer_override` and subclasses are out of scope. The memo is modelled with object identity; cyclic objects are
difftested on the decoding side only.
-/

namespace PyLean.Pickle

open PyLean.Registry

def entries : List Entry := [
  { id := "pickle-decode-encode-long", pyFile := "Lib/pickle.py"
    pyFns := ["encode_long", "decode_long"]
    statement := "decode_long(encode_long(x)) == x for every int x, through the trimmed two's-complement encoding at every byte boundary."
    source := "docstrings of encode_long and decode_long, Lib/pickle.py:372-420", status := .proven
    prop := ``DecodeEncodeLong, thm := some ``decodeEncodeLong_proven },
  { id := "pickle-encode-long-shortest", pyFile := "Lib/pickle.py"
    pyFns := ["encode_long", "decode_long"]
    statement := "encode_long(x) is the unique shortest byte string that decode_long maps to x, so encode_long is a bijection from ints onto the shortest encodings, including the sign-trimmed -(2**(8*j - 1))."
    source := "docstrings of encode_long and decode_long, Lib/pickle.py:372-420; LONG1/LONG4 in Lib/pickletools.py", status := .proven
    prop := ``EncodeLongShortest, thm := some ``encodeLongShortest_proven },
  { id := "pickle-load-counted-long", pyFile := "Modules/_pickle.c"
    pyFns := ["load_counted_long"]
    statement := "At any position of an unframed stream, LONG1 and LONG4 in the C unpickler: too few bytes for the count raise; a negative count raises UnpicklingError 'LONG pickle has negative byte count'; a zero count pushes 0 right after the count; too few bytes for the payload raise; otherwise the payload, read as a signed little-endian int, is pushed and the reader stands right after it."
    source := "LONG1/LONG4 format, Lib/pickletools.py:875-928; Modules/_pickle.c:5703-5734", status := .proven
    prop := ``CountedLongRead, thm := some ``countedLongRead_proven
    notes := "Frames are outside (frame_end is -1). The payload save_long writes is encode_long(x), which decode_long maps back to x (pickle-decode-encode-long)." },
  { id := "pickle-text-int-roundtrip", pyFile := "Lib/pickle.py"
    pyFns := ["_Unpickler.load_int", "_Unpickler.load_long", "load_int", "load_long"]
    statement := "For every int with at most 4300 decimal digits, the text lines I<x> and L<x>L (as protocol 0 writes them, and L<x>L at protocol 1 outside the 4-byte range) read back as the int x in both unpicklers, never as a bool."
    source := "pickle round trip, Doc/library/pickle.rst", status := .proven
    prop := ``TextIntRoundtrip, thm := some ``textIntRoundtrip_proven
    notes := "About the readers only; save_long is pinned by pickle-save-long-twins-sized. Past 4300 digits repr raises ValueError at dump time, in both twins." },
  { id := "pickle-save-long-twins", pyFile := "Modules/_pickle.c"
    pyFns := ["save_long"]
    statement := "For every int and protocol 0-5, the C and Python save_long produce the same bytes or the same exception."
    source := "invariant: C accelerator vs pure-Python twin", status := .refuted
    prop := ``SaveLongTwinsAgree, thm := some ``saveLongTwinsAgree_refuted
    bug := some "pickle-c-long4-untrimmed-size"
    notes := "C checks the untrimmed byte count, so it refuses -(2**(8*(2**31-1)-1)), which Python encodes in LONG4." },
  { id := "pickle-save-long-same-outcome", pyFile := "Modules/_pickle.c"
    pyFns := ["save_long", "_Pickler.save_long", "encode_long"]
    statement := "For every int except -(2**(8*(2**31-1)-1)) and every protocol 0-5, the C and Python save_long both raise or return the same bytes."
    source := "invariant: C accelerator vs pure-Python twin", status := .proven
    prop := ``SaveLongSameOutcome, thm := some ``saveLongSameOutcome_proven
    notes := "The exclusion is the single counterexample of pickle-save-long-twins. Past the LONG4 limit both raise, with different classes." },
  { id := "pickle-save-long-twins-sized", pyFile := "Modules/_pickle.c"
    pyFns := ["save_long", "_Pickler.save_long", "encode_long"]
    statement := "For every int with bit_length/8 + 1 <= 0x7fffffff and every protocol 0-5, the C and Python save_long produce the same bytes, so they choose among BININT1, BININT2, BININT, LONG1, LONG4, INT and LONG identically at every boundary."
    source := "invariant: C accelerator vs pure-Python twin", status := .proven
    prop := ``SaveLongTwinsAgreeSized, thm := some ``saveLongTwinsAgreeSized_proven
    notes := "The hypothesis is exactly the C size check that the refuted property trips." },
  { id := "pickle-int-line-twins", pyFile := "Modules/_pickle.c"
    pyFns := ["load_int"]
    statement := "For every complete INT line, the C and Python unpicklers accept the same lines and return the same value, including int vs bool."
    source := "invariant: C accelerator vs pure-Python twin", status := .refuted
    prop := ``IntLineTwins, thm := some ``intLineTwins_refuted
    bug := some "pickle-c-nul-in-text-args"
    notes := "I12\\0 is 12 in C and ValueError in Python. python/cpython#126996, open. The bool spellings of 3.14 are gone: load_int now tests for 00 and 01 as Python does." },
  { id := "pickle-int-line-twins-no-nul", pyFile := "Modules/_pickle.c"
    pyFns := ["load_int"]
    statement := "The same, for lines without NUL bytes."
    source := "invariant: C accelerator vs pure-Python twin", status := .refuted
    prop := ``IntLineTwinsNoNul, thm := some ``intLineTwinsNoNul_refuted
    bug := some "pickle-c-int-digit-limit"
    notes := "5000 zeros and a 1 are 1 through strtol in C and over the digit limit in Python." },
  { id := "pickle-int-line-twins-narrow", pyFile := "Modules/_pickle.c"
    pyFns := ["load_int", "_Unpickler.load_int"]
    statement := "For every complete INT line that is not a line with NUL that C accepts, and not a line past the digit limit that C's strtol path accepts, the C strtol fast path, its PyLong_FromString fallback and Python's int() accept the same lines and return the same value, including the bools I00 and I01."
    source := "invariant: C accelerator vs pure-Python twin", status := .proven
    prop := ``IntLineTwinsPrecise, thm := some ``intLineTwinsPrecise_proven
    notes := "The hypotheses are exactly the two refutations above; lines both twins reject stay in the statement. Exception classes can differ (an empty line is UnpicklingError in C, ValueError in Python)." },
  { id := "pickle-long-line-twins", pyFile := "Modules/_pickle.c"
    pyFns := ["load_long"]
    statement := "For every complete LONG line, the C and Python unpicklers accept the same lines and return the same value."
    source := "invariant: C accelerator vs pure-Python twin", status := .refuted
    prop := ``LongLineTwins, thm := some ``longLineTwins_refuted
    bug := some "pickle-c-nul-in-text-args"
    notes := "L5\\0 is 5 in C and ValueError in Python." },
  { id := "pickle-long-line-twins-no-nul", pyFile := "Modules/_pickle.c"
    pyFns := ["load_long", "_Unpickler.load_long"]
    statement := "For every complete LONG line, with or without the L suffix, except lines with NUL that C accepts, the C and Python unpicklers accept the same lines and return the same value."
    source := "invariant: C accelerator vs pure-Python twin", status := .proven
    prop := ``LongLineTwinsPrecise, thm := some ``longLineTwinsPrecise_proven
    notes := "The hypothesis is exactly the refuted case. Includes the 4300-digit limit, whitespace and underscores." },
  { id := "pickle-dumps-twins", pyFile := "Modules/_pickle.c"
    pyFns := ["_pickle_dumps_impl", "_dumps"]
    statement := "For every plain value, int protocol argument, C stack room and Python frame budget, pickle.dumps and pickle._dumps produce the same bytes or the same exception."
    source := "invariant: C accelerator vs pure-Python twin", status := .refuted
    prop := ``DumpsTwinsAgreeR, thm := some ``dumpsTwinsAgreeR_refuted
    bug := some "pickle-protocol-long-overflow"
    notes := "protocol=-2**63-1 is OverflowError in C and the highest protocol in Python." },
  { id := "pickle-dumps-twins-long", pyFile := "Modules/_pickle.c"
    pyFns := ["_pickle_dumps_impl", "_dumps"]
    statement := "The same, for protocol arguments within C long."
    source := "invariant: C accelerator vs pure-Python twin", status := .refuted
    prop := ``DumpsTwinsAgreeLongR, thm := some ``dumpsTwinsAgreeLongR_refuted
    bug := some "pickle-py-oversize-struct-error"
    notes := "bytes(2**32) at protocol 3: OverflowError in C, struct.error in Python." },
  { id := "pickle-dumps-twins-rec", pyFile := "Modules/_pickle.c"
    pyFns := ["save", "save_list", "_Pickler.save", "_Pickler.save_list", "_Pickler._batch_appends"]
    statement := "For every C stack room and Python frame budget, on the values and protocols of pickle-dumps-twins-narrow, pickle.dumps and pickle._dumps both raise or return the same bytes."
    source := "invariant: C accelerator vs pure-Python twin", status := .refuted
    prop := ``DumpsTwinsRec, thm := some ``dumpsTwinsRec_refuted
    bug := some "pickle-twins-recursion-limit"
    notes := "Witness [[]] with 100 levels of room and 5 frames. At the default limit, lists 331 deep fail in pickle._dumps and pickle in C (probe); python/cpython#47369." },
  { id := "pickle-dumps-twins-narrow", pyFile := "Modules/_pickle.c"
    pyFns := ["save_none", "save_bool", "save_long", "_save_bytes_data", "_save_bytearray_data", "save_unicode", "write_unicode_binary", "memo_get", "_Pickler_Write", "_Pickler_CommitFrame", "_write_size64", "_Pickler_SetBufferCallback", "_Framer.__init__", "_Framer.start_framing", "_Framer.end_framing", "_Pickler.put", "_Pickler.get", "_Pickler.save_none", "_Pickler.save_bool", "_Pickler.save_long", "_Pickler._save_bytes_no_memo", "_Pickler._save_bytearray_no_memo", "encode_long"]
    statement := "With 4 * depth + 4 levels of C stack room and 10 * depth + 18 Python frames left where pickle._dumps is called (depth: the container nesting), for every plain value whose ints pass C's LONG4 size check, protocol None or an int within C long, and buffer_callback None or not, pickle.dumps and pickle._dumps both raise, or both return the same bytes: memoization, framing at protocol 4+, opcode choice, every batch size of list, dict and set, and the reduce paths for bytes, bytearray, set and frozenset included."
    source := "invariant: C accelerator vs pure-Python twin", status := .open
    prop := ``DumpsTwinsNarrow
    notes := "Open: false on a fresh interpreter, the default state, which persists after import pickle and other encodes. There the first protocol 0 str looks up the raw-unicode-escape codec in Python frames (encodings.search_function, importlib), so 'a' needs 15 frames, b'xy' 20 and bytearray(b'z') 25 against the bound of 18 (probe). Needs a codec-cache model in the Python mirror. The Lean theorem dumpsTwinsNarrow_proven holds of the model, which has no codec registry." },
  { id := "pickle-dumps-twins-norec", pyFile := "Modules/_pickle.c"
    pyFns := ["save_none", "save_bool", "save_long", "_save_bytes_data", "_save_bytearray_data", "save_unicode", "write_unicode_binary", "memo_get", "_Pickler_Write", "_Pickler_CommitFrame", "_write_size64", "_Pickler_SetBufferCallback", "_Framer.__init__", "_Framer.start_framing", "_Framer.end_framing", "_Pickler.put", "_Pickler.get", "_Pickler.save_none", "_Pickler.save_bool", "_Pickler.save_long", "_Pickler._save_bytes_no_memo", "_Pickler._save_bytearray_no_memo", "encode_long"]
    statement := "For every C stack room and Python frame budget under which neither twin raises its RecursionError, on the values and protocols of pickle-dumps-twins-narrow, pickle.dumps and pickle._dumps both raise, or both return the same bytes."
    source := "invariant: C accelerator vs pure-Python twin", status := .proven
    prop := ``DumpsTwinsNoRec, thm := some ``dumpsTwinsNoRec_proven
    notes := "EncRecApprox.lean: every bounded encoder computes what its frames-free twin computes or raises its RecursionError. No frame bound: on a fresh interpreter the Python twin's extra codec-lookup frames can only add RecursionErrors, which the hypothesis excludes." },
  { id := "pickle-dumps-protocol-float", pyFile := "Modules/_pickle.c"
    pyFns := ["_Pickler_SetProtocol", "_Pickler.__init__"]
    statement := "With the room and frames of pickle-dumps-twins-narrow, for every protocol object (None, int, float, or another type), pickle.dumps and pickle._dumps both raise or return the same bytes."
    source := "invariant: C accelerator vs pure-Python twin", status := .refuted
    prop := ``DumpsTwinsProtocol, thm := some ``dumpsTwinsProtocol_refuted
    bug := some "pickle-protocol-float"
    notes := "pickle.dumps(None, 2.5) is TypeError (PyLong_AsLong); pickle._dumps(None, 2.5) is b'\\x80\\x02N.' (int(2.5))." },
  { id := "pickle-atoms-exact", pyFile := "Modules/_pickle.c"
    pyFns := ["save_none", "save_bool", "_Pickler_SetBufferCallback", "_Pickler.save_none", "_Pickler.save_bool",
      "_Framer.__init__", "_Framer.start_framing", "_Framer.end_framing"]
    statement := "For protocols 0-5, buffer_callback None or not, every C stack room of 4 levels and up and every budget of 18 frames and up: pickle.dumps and pickle._dumps of None, True and False raise ValueError 'buffer_callback needs protocol >= 5' with a callback below protocol 5, and otherwise return PROTO p from protocol 2, then N, NEWTRUE/NEWFALSE from protocol 2 or I01/I00 lines below, then STOP, with no FRAME (the frame holds under 4 bytes)."
    source := "pickle stream format, Lib/pickletools.py (NONE, NEWTRUE, NEWFALSE, INT, PROTO, FRAME); Doc/library/pickle.rst (buffer_callback)", status := .proven
    prop := ``AtomsExact, thm := some ``atomsExact_proven },
  { id := "pickle-memo-ops-exact", pyFile := "Modules/_pickle.c"
    pyFns := ["memo_get", "_Pickler.put", "_Pickler.get"]
    statement := "For every protocol and memo index, both picklers' PUT and GET opcodes: MEMOIZE from protocol 4 (PUT); text PUT/GET with the decimal index at protocol 0; BINPUT/BINGET with the index byte below 256; LONG_BINPUT/LONG_BINGET with a 4-byte field that reads back as the index below 2**32; an error from 2**32."
    source := "pickle stream format, Lib/pickletools.py (PUT, BINPUT, LONG_BINPUT, GET, BINGET, LONG_BINGET, MEMOIZE)", status := .proven
    prop := ``MemoOpsExact, thm := some ``memoOpsExact_proven
    notes := "memo_put is not claimed (its fast-mode return is not modelled)." },
  { id := "pickle-bytes-classes", pyFile := "Modules/_pickle.c"
    pyFns := ["_save_bytes_data", "_Pickler._save_bytes_no_memo", "_write_size64"]
    statement := "For every bytes payload and protocol 3 and up, both picklers write SHORT_BINBYTES with a 1-byte length to 255 bytes, BINBYTES with a 4-byte length below 2**32, BINBYTES8 with an 8-byte length from protocol 4 (each length field reads back as the size), and raise at protocol 3 from 2**32; payloads of 64 KiB and up bypass the frame."
    source := "pickle stream format, Lib/pickletools.py (SHORT_BINBYTES, BINBYTES, BINBYTES8); PEP 3154", status := .proven
    prop := ``BytesClassesBoth, thm := some ``bytesClassesBoth_proven },
  { id := "pickle-str-classes", pyFile := "Modules/_pickle.c"
    pyFns := ["write_unicode_binary", "save_unicode", "_write_size64"]
    statement := "For every UTF-8 payload and protocol 1 and up, both picklers write SHORT_BINUNICODE with a 1-byte length to 255 bytes from protocol 4, BINUNICODE with a 4-byte length below 2**32, BINUNICODE8 with an 8-byte length from protocol 4 (each reads back as the size), and raise below protocol 4 from 2**32; at protocol 0 C writes UNICODE, the raw-unicode-escape text and a newline."
    source := "pickle stream format, Lib/pickletools.py (SHORT_BINUNICODE, BINUNICODE, BINUNICODE8, UNICODE)", status := .proven
    prop := ``StrClassesBoth, thm := some ``strClassesBoth_proven
    notes := "The escape text itself is the shared cRawUnicodeEscape (raw_unicode_escape is not claimed). Python's protocol 0 line is not claimed: its raw-unicode-escape codec lookup runs Python frames until cached, which the model does not have." },
  { id := "pickle-bytearray-exact", pyFile := "Modules/_pickle.c"
    pyFns := ["_save_bytearray_data", "_Pickler._save_bytearray_no_memo", "_write_size64"]
    statement := "For every bytearray payload at protocol 5, both picklers write BYTEARRAY8 with an 8-byte length that reads back as the size, outside the frame from 64 KiB."
    source := "pickle stream format, Lib/pickletools.py (BYTEARRAY8); PEP 574", status := .proven
    prop := ``BytearrayExact, thm := some ``bytearrayExact_proven },
  { id := "pickle-bytearray-obj-exact", pyFile := "Modules/_pickle.c"
    pyFns := ["_save_bytearray_data", "_write_size64"]
    statement := "C save() on a bytearray not yet in the memo, protocol 5, any payload and stack room of a level or more: the opcode boundary, BYTEARRAY8 with an 8-byte length that reads back as the size and the payload (outside the frame from 64 KiB), MEMOIZE, and the bytearray memoized under the next index."
    source := "pickle stream format, Lib/pickletools.py (BYTEARRAY8, MEMOIZE); PEP 574", status := .proven
    prop := ``BytearrayObjExact, thm := some ``bytearrayObjExact_proven },
  { id := "pickle-frames-exact", pyFile := "Modules/_pickle.c"
    pyFns := ["_Pickler_CommitFrame", "_Pickler_Write", "_write_size64", "_Framer.__init__",
      "_Framer.start_framing", "_Framer.end_framing"]
    statement := "Both framers between start and finish: a frame of at least 4 bytes is written as FRAME with an 8-byte length that reads back as its size, a shorter one bare; at an opcode boundary a frame of 64 KiB or more is committed and a new one opened, a smaller one is continued."
    source := "PEP 3154 (FRAME); Lib/pickletools.py", status := .proven
    prop := ``FramesExact, thm := some ``framesExact_proven
    notes := "The C clauses follow from the FR invariant of EncFrame.lean (cFrame_py)." },
  { id := "pickle-dumps-twins-exact-sized", pyFile := "Modules/_pickle.c"
    pyFns := ["_pickle_dumps_impl", "_dumps"]
    statement := "With no str or bytes payload over 4 GiB below protocol 4, and fewer than 2**32 memoized objects, pickle.dumps and pickle._dumps produce the same bytes or the same exception, class and message."
    source := "invariant: C accelerator vs pure-Python twin", status := .open
    prop := ``DumpsTwinsExactSized
    notes := "Open: EncSim's Out relation forgets the exception. Needs the simulation redone with equal exceptions and SizeOk threaded through every lemma. The only exceptions left are the repr digit limit, which is equal in both twins." },
  { id := "pickle-roundtrip", pyFile := "Lib/pickle.py"
    pyFns := ["_dumps", "_loads", "_pickle_dumps_impl", "_pickle_loads_impl"]
    statement := "For every well-formed plain value (hashable distinct keys and set elements, consistent ids, valid code points), every protocol 0-5 and every pairing of the two picklers and two unpicklers, loads(dumps(x, p)) is x with structure and type preserved, whenever dumps returns."
    source := "Doc/library/pickle.rst; invariant", status := .open
    prop := ``RoundTrip
    notes := "Open: needs a compiler-correctness proof over the memo, the heap (lists are memoized before their items are appended) and frames. Difftest evidence only; the integer and text-line cases are proven separately." },
  { id := "pickle-loads-twins-exact", pyFile := "Modules/_pickle.c"
    pyFns := ["_pickle_loads_impl", "_loads"]
    statement := "On every data-only stream, pickle.loads and pickle._loads raise the same exception class."
    source := "invariant: C accelerator vs pure-Python twin", status := .refuted
    prop := ``LoadsTwinsExact, thm := some ``loadsTwinsExact_refuted
    bug := some "pickle-py-unpickler-raw-exceptions"
    notes := "POP on an empty stack: UnpicklingError in C, IndexError in Python. Allowed by the docs." },
  { id := "pickle-loads-twins-accept", pyFile := "Modules/_pickle.c"
    pyFns := ["_pickle_loads_impl", "_loads"]
    statement := "pickle.loads and pickle._loads accept the same data-only streams and return equal objects."
    source := "invariant: C accelerator vs pure-Python twin", status := .refuted
    prop := ``LoadsTwinsAccept, thm := some ``loadsTwinsAccept_refuted
    bug := some "pickle-c-nul-in-text-args"
    notes := "I12\\0 as a whole stream. An empty APPENDS or ADDITEMS on the wrong target no longer differs: do_append and load_additems look the method up as Python does. The other text-opcode and memo divergences have their own entries." },
  { id := "pickle-memoize-twins", pyFile := "Modules/_pickle.c"
    pyFns := []
    statement := "After any BINPUT, MEMOIZE stores under the number of elements in the memo in both unpicklers, so a following BINGET finds the same object or fails in both."
    source := "Lib/pickletools.py:1874-1875 (MEMOIZE); invariant: C accelerator vs pure-Python twin", status := .refuted
    prop := ``MemoizeTwins, thm := some ``memoizeTwins_refuted
    bug := some "pickle-c-memo-dict-unsynced"
    notes := "BINPUT 200 sends the key to memo_dict without counting it, so MEMOIZE writes index 0 in C and index 1 in Python: new in 3.15." },
  { id := "pickle-loads-twins-narrow", pyFile := "Modules/_pickle.c"
    pyFns := ["_pickle_loads_impl", "_loads"]
    statement := "On every data-only stream whose run meets none of the divergences on record (the INT digit limit, NUL in text arguments, PUT index above sys.maxsize, a PUT index that C may keep in memo_dict, a payload of at least 1 MiB that overruns its frame), pickle.loads and pickle._loads both raise or return equal objects."
    source := "invariant: C accelerator vs pure-Python twin", status := .open
    prop := ``LoadsTwinsNarrow
    notes := "Open: DecSim.lean has the state relation, the sequencing rule with Python's doomed runs, and how each reader computes. Still missing: the read, readline and readinto simulations, one lemma per handler over the tables, and the loop. This would settle most load_* rows." },
  { id := "pickle-frame-twins", pyFile := "Lib/pickle.py"
    pyFns := ["_Unframer.load_frame", "load_frame"]
    statement := "For a stream starting with a FRAME of any length, the two unpicklers accept the same streams and return equal objects."
    source := "PEP 3154; invariant: C accelerator vs pure-Python twin", status := .refuted
    prop := ``FrameTwins, thm := some ``frameTwins_refuted
    bug := some "pickle-c-nul-in-text-args"
    notes := "A frame around I12\\0: the body is unconstrained, so a divergence outside a frame is one inside it. A frame longer than the data no longer differs: pickle-frame-read." },
  { id := "pickle-frame-read", pyFile := "Lib/pickle.py"
    pyFns := ["_Unframer.load_frame", "_Unframer._chunked_file_read", "_Unpickler.load_frame", "load_frame"]
    statement := "FRAME n at the start of a stream, for every n up to sys.maxsize: with fewer than n bytes left both unpicklers raise, EOFError in Python; otherwise both hold exactly the next n bytes as the frame and continue at its first byte."
    source := "PEP 3154: a frame of the stated length; python/cpython#128853", status := .proven
    prop := ``FrameRead, thm := some ``frameRead_proven
    notes := "chunkedFileRead_run shows the chunk loop reads what one file_read would, on a BytesIO." },
  { id := "pickle-frame-chunk-twins", pyFile := "Modules/_pickle.c"
    pyFns := []
    statement := "A BINBYTES payload that runs past the end of its frame is rejected by both unpicklers, wherever the frame ends."
    source := "invariant: C accelerator vs pure-Python twin; the check in _Unpickler_ReadInto, Modules/_pickle.c:1514-1562; Lib/pickle.py:284-295", status := .refuted
    prop := ``FrameChunkTwins, thm := some ``frameChunkTwins_refuted
    bug := some "pickle-c-frame-chunk-straddle"
    notes := "A frame ending 1 MiB into a 2 MiB payload: the chunked read of 3.15 leaves the frame without an error; Python raises. C rejects every other frame end. BYTEARRAY8 is accepted by both twins at such a frame end, so it is not a twin difference." },
  { id := "pickle-put-twins", pyFile := "Modules/_pickle.c"
    pyFns := ["load_put"]
    statement := "For every decimal PUT index, the two unpicklers accept the same stream and return equal objects."
    source := "invariant: C accelerator vs pure-Python twin", status := .refuted
    prop := ``PutTwins, thm := some ``putTwins_refuted
    bug := some "pickle-c-put-index-ssize"
    notes := "Index 2**63: OverflowError in C. Maintainers: not a bug (python/cpython#144410)." },
  { id := "pickletools-read-uint-exact", pyFile := "Lib/pickletools.py"
    pyFns := ["read_uint1", "read_uint2", "read_uint4", "read_uint8"]
    statement := "At any position of any stream, read_uint1, 2, 4 and 8 return the integer struct.pack wrote and advance by its size, and raise ValueError on fewer bytes."
    source := "docstrings of the readers, Lib/pickletools.py:214-308", status := .proven
    prop := ``ReadUintExact, thm := some ``readUintExact_proven },
  { id := "pickletools-read-int4-roundtrip", pyFile := "Lib/pickletools.py"
    pyFns := ["read_int4"]
    statement := "read_int4 returns every int the pickler's struct.pack('<i') wrote, at any position of any stream."
    source := "docstring of read_int4, Lib/pickletools.py:254-266", status := .proven
    prop := ``ReadInt4Roundtrip, thm := some ``readInt4Roundtrip_proven },
  { id := "pickletools-read-counted-roundtrip", pyFile := "Lib/pickletools.py"
    pyFns := ["read_bytes1", "read_string1", "read_bytes4", "read_bytes8", "read_bytearray8"]
    statement := "read_bytes1, read_string1, read_bytes4, read_bytes8 and read_bytearray8 return the payload after its count and stop right after it, for every payload the count field can hold, at any position of any stream."
    source := "pickle stream format, Lib/pickletools.py:411-593", status := .proven
    prop := ``ReadCountedRoundtrip, thm := some ``readCountedRoundtrip_proven },
  { id := "pickletools-read-string4-roundtrip", pyFile := "Lib/pickletools.py"
    pyFns := ["read_string4"]
    statement := "read_string4 returns the latin-1 text of every payload under 2**31 bytes, the range of its signed count."
    source := "pickle stream format, Lib/pickletools.py:440-460", status := .proven
    prop := ``ReadString4Roundtrip, thm := some ``readString4Roundtrip_proven },
  { id := "pickletools-read-long-roundtrip", pyFile := "Lib/pickletools.py"
    pyFns := ["read_long1", "read_long4"]
    statement := "read_long1 and read_long4 read back encode_long(x) for every int x whose encoding fits their count field."
    source := "LONG1 and LONG4 format, Lib/pickletools.py:875-928", status := .proven
    prop := ``ReadLongRoundtrip, thm := some ``readLongRoundtrip_proven },
  { id := "pickletools-read-unicode-roundtrip", pyFile := "Lib/pickletools.py"
    pyFns := ["read_unicodestring1", "read_unicodestring4", "read_unicodestring8"]
    statement := "read_unicodestring1, 4 and 8 return the utf-8/surrogatepass decoding of the payload, for every decodable payload their count can hold, at any position of any stream."
    source := "pickle stream format, Lib/pickletools.py:631-737", status := .proven
    prop := ``ReadUnicodeRoundtrip, thm := some ``readUnicodeRoundtrip_proven },
  { id := "pickletools-read-float8-exact", pyFile := "Lib/pickletools.py"
    pyFns := ["read_float8"]
    statement := "read_float8 consumes exactly the eight bytes of a BINFLOAT, and raises ValueError on fewer."
    source := "docstring of read_float8, Lib/pickletools.py:837-850", status := .proven
    prop := ``ReadFloat8Exact, thm := some ``readFloat8Exact_proven
    notes := "The value of the bytes as a float is struct.unpack's: compared bit for bit by the difftest." },
  { id := "pickletools-read-unicodenl", pyFile := "Lib/pickletools.py"
    pyFns := ["read_unicodestringnl"]
    statement := "read_unicodestringnl is raw-unicode-escape on the line, as in load_unicode, and raises ValueError when the newline is missing."
    source := "twin: pickletools vs pickle", status := .proven
    prop := ``ReadUnicodeNl, thm := some ``readUnicodeNl_proven },
  { id := "pickletools-decimal-short-twin", pyFile := "Lib/pickletools.py"
    pyFns := ["read_decimalnl_short"]
    statement := "On every complete line, read_decimalnl_short and the unpickler's load_int accept the same lines and return the same int or bool, although only one of them keeps the newline for int()."
    source := "twin: pickletools vs pickle", status := .proven
    prop := ``DecimalShortTwin, thm := some ``decimalShortTwin_proven },
  { id := "pickletools-decimal-long-twin", pyFile := "Lib/pickletools.py"
    pyFns := ["read_decimalnl_long"]
    statement := "On every complete line, read_decimalnl_long and the unpickler's load_long return the same int or raise the same exception, message included."
    source := "twin: pickletools vs pickle", status := .proven
    prop := ``DecimalLongTwin, thm := some ``decimalLongTwin_proven },
  { id := "pickletools-read-stringnl-plain", pyFile := "Lib/pickletools.py"
    pyFns := ["read_stringnl"]
    statement := "read_stringnl on a line quoted with either quote and without backslashes returns the text between the quotes, at any position of any stream."
    source := "docstring of read_stringnl, Lib/pickletools.py:317-342", status := .proven
    prop := ``ReadStringnlPlain, thm := some ``readStringnlPlain_proven
    notes := "Lines with escapes go through the same escape decoder as load_string and are difftested. A lone quote is accepted here and rejected by load_string; maintainers hold pickletools may be more lenient (python/cpython#127045)." },
  { id := "pickletools-noescape-verbatim", pyFile := "Lib/pickletools.py"
    pyFns := ["read_stringnl_noescape"]
    statement := "read_stringnl_noescape returns every decodable line as load_global and load_persid read it, untouched."
    source := "stringnl_noescape descriptor, Lib/pickletools.py:377-386; twin", status := .refuted
    prop := ``NoescapeVerbatim, thm := some ``noescapeVerbatim_refuted
    bug := some "pickle-tools-noescape-decodes-escapes"
    notes := "A line ending in a backslash raises ValueError, and valid protocol 0 persistent ids reach it." },
  { id := "pickletools-noescape-no-backslash", pyFile := "Lib/pickletools.py"
    pyFns := ["read_stringnl_noescape", "read_stringnl_noescape_pair", "read_stringnl"]
    statement := "On every line without a backslash, read_stringnl_noescape returns the UTF-8 decoding of the line or raises UnicodeDecodeError, and read_stringnl_noescape_pair joins two such lines with a space."
    source := "stringnl_noescape descriptor; twin", status := .proven
    prop := ``NoescapeNoBackslash, thm := some ``noescapeNoBackslash_proven
    notes := "The hypothesis is exactly the refuted case." },
  { id := "pickletools-genops-fuel", pyFile := "Lib/pickletools.py"
    pyFns := ["_genops", "genops"]
    statement := "_genops ends on every byte string, with or without tell: len(data) + 1 rounds suffice and more change nothing. A FLOAT opcode ends the model's run with its Excluded marker."
    source := "invariant: no hang", status := .proven
    prop := ``GenopsFuelEnough, thm := some ``genopsFuelEnough_proven
    notes := "Rests on every reader moving forward and staying inside the data. read_floatnl needs float() of text, so the model stops there where CPython continues: nothing is claimed past a FLOAT opcode until the binary64 model lands." },
  { id := "pickletools-genops-wellformed", pyFile := "Lib/pickletools.py"
    pyFns := ["_genops", "genops"]
    statement := "On every byte string the model of genops accepts, the opcodes start at 0, are contiguous, move forward, stay inside the data, and STOP is the last and only STOP."
    source := "invariant; docstring of genops, Lib/pickletools.py:2328-2351", status := .proven
    prop := ``GenopsWellFormed, thm := some ``genopsWellFormed_proven
    notes := "Streams with a FLOAT opcode are outside: the model stops there with Excluded, see pickletools-genops-fuel." },
  { id := "pickletools-dis-no-indexerror", pyFile := "Lib/pickletools.py"
    pyFns := ["dis"]
    statement := "dis reports bad streams with ValueError: it never raises IndexError."
    source := "docstring of dis, Lib/pickletools.py:2448-2459", status := .refuted
    prop := ``DisNoIndexError, thm := some ``disNoIndexError_refuted
    bug := some "pickle-tools-dis-mark-indexerror"
    notes := "b'(\\x85t.': TUPLE1 consumes the mark, then TUPLE walks off the emulated stack. Only malformed streams, which both unpicklers reject. Separately, repr(arg) stops dis on ints past the 4300-digit limit, on valid pickles: a deliberate limit, not recorded as a bug." },
  { id := "pickletools-dis-follows-genops", pyFile := "Lib/pickletools.py"
    pyFns := ["dis", "_genops", "genops"]
    statement := "When dis raises nothing, genops accepts the stream and the last line printed is the maximum protocol over its opcodes."
    source := "docstring of dis, Lib/pickletools.py:2424-2460", status := .proven
    prop := ``DisFollowsGenops, thm := some ``disFollowsGenops_proven
    notes := "The text of each line, the indentation and the annotations are difftested exactly." },
  { id := "pickletools-dis-stack-repr", pyFile := "Lib/pickletools.py"
    pyFns := ["StackObject.__repr__"]
    statement := "The 'stack not empty after STOP' error names what is left, bottom first, in list repr with each StackObject shown by name."
    source := "Lib/pickletools.py:976-977, :2591-2592", status := .proven
    prop := ``DisStackRepr, thm := some ``disStackRepr_proven },
  { id := "pickletools-optimize-raw-copy", pyFile := "Lib/pickletools.py"
    pyFns := ["optimize", "_genops"]
    statement := "optimize returns a stream without memo or frame opcodes, of protocol below 4, unchanged up to its STOP, at any opcode size."
    source := "docstring of optimize, Lib/pickletools.py:2356-2357", status := .proven
    prop := ``OptimizeRawCopy, thm := some ``optimizeRawCopy_proven
    notes := "Covers only the copying path, by hypothesis. Removing PUTs, renumbering and reframing are difftested exactly and stated in the open pickle-optimize-sound." },
  { id := "pickle-optimize-sound", pyFile := "Lib/pickletools.py"
    pyFns := ["optimize"]
    statement := "On a stream an unpickler accepts, that unpickler returns an equal object from optimize(stream)."
    source := "docstring of optimize; invariant", status := .open
    prop := ``OptimizeSound
    notes := "Open: needs a simulation between the decoder on the input and on the output, relating memo indices through newids. Fuzz evidence: 29941 real pickles, recursive ones included, no difference in either unpickler; idempotent; never grew." }
]

end PyLean.Pickle
