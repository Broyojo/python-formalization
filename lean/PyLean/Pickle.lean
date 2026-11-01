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
import PyLean.Pickle.DecProps
import PyLean.Pickle.ToolsGen
import PyLean.Pickle.DecSim

/-!
`Lib/pickle.py` vs `Modules/_pickle.c`, CPython 3.14.7, on plain data: None,
bool, int, str, bytes, bytearray, tuple, list, dict, set and frozenset, under
protocols 0-5. Floats, custom classes, reduce and anything that runs code are
out of scope. The memo is modelled with object identity; cyclic objects are
difftested on the decoding side only.
-/

namespace PyLean.Pickle

open PyLean.Registry

def entries : List Entry := [
  { id := "pickle-decode-encode-long", pyFile := "Lib/pickle.py"
    pyFns := ["encode_long", "decode_long", "load_counted_long"]
    statement := "decode_long(encode_long(x)) == x for every int x, through the trimmed two's-complement encoding at every byte boundary."
    source := "docstrings of encode_long and decode_long, Lib/pickle.py:356-404", status := .proven
    prop := ``DecodeEncodeLong, thm := some ``decodeEncodeLong_proven },
  { id := "pickle-encode-long-shortest", pyFile := "Lib/pickle.py"
    pyFns := ["encode_long", "decode_long"]
    statement := "encode_long(x) is the unique shortest byte string that decode_long maps to x, so encode_long is a bijection from ints onto the shortest encodings, including the sign-trimmed -(2**(8*j - 1))."
    source := "docstrings of encode_long and decode_long, Lib/pickle.py:356-404; LONG1/LONG4 in Lib/pickletools.py", status := .proven
    prop := ``EncodeLongShortest, thm := some ``encodeLongShortest_proven },
  { id := "pickle-text-int-roundtrip", pyFile := "Lib/pickle.py"
    pyFns := ["_Pickler.save_long", "_Unpickler.load_int", "_Unpickler.load_long", "load_int", "load_long"]
    statement := "For every int with at most 4300 decimal digits, the protocol 0/1 lines I<x> and L<x>L read back as the int x in both unpicklers, never as a bool."
    source := "pickle round trip, Doc/library/pickle.rst", status := .proven
    prop := ``TextIntRoundtrip, thm := some ``textIntRoundtrip_proven
    notes := "Past 4300 digits repr raises ValueError at dump time, in both twins." },
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
    bug := some "pickle-c-int-bool-spelling"
    notes := "I 1 is True in C and 1 in Python. python/cpython#135241, fixed on main." },
  { id := "pickle-int-line-twins-no-bool-spelling", pyFile := "Modules/_pickle.c"
    pyFns := ["load_int"]
    statement := "The same, for lines other than an optional space or sign before 0 or 1."
    source := "invariant: C accelerator vs pure-Python twin", status := .refuted
    prop := ``IntLineTwinsNoBoolSpelling, thm := some ``intLineTwinsNoBoolSpelling_refuted
    bug := some "pickle-c-nul-in-text-args"
    notes := "I12\\0 is 12 in C and ValueError in Python. python/cpython#126996, open." },
  { id := "pickle-int-line-twins-no-nul", pyFile := "Modules/_pickle.c"
    pyFns := ["load_int"]
    statement := "The same, also for lines without NUL bytes."
    source := "invariant: C accelerator vs pure-Python twin", status := .refuted
    prop := ``IntLineTwinsNoNul, thm := some ``intLineTwinsNoNul_refuted
    bug := some "pickle-c-int-digit-limit"
    notes := "5000 zeros and a 1 are 1 through strtol in C and over the digit limit in Python." },
  { id := "pickle-int-line-twins-narrow", pyFile := "Modules/_pickle.c"
    pyFns := ["load_int", "_Unpickler.load_int"]
    statement := "For every complete INT line that is not a bool spelling, not a line with NUL that C accepts, and not a line past the digit limit that C's strtol path accepts, the C strtol fast path, its PyLong_FromString fallback and Python's int() accept the same lines and return the same value, including the bools I00 and I01."
    source := "invariant: C accelerator vs pure-Python twin", status := .proven
    prop := ``IntLineTwinsPrecise, thm := some ``intLineTwinsPrecise_proven
    notes := "The hypotheses are exactly the three refutations above; lines both twins reject stay in the statement. Exception classes can differ (an empty line is UnpicklingError in C, ValueError in Python)." },
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
    statement := "For every plain value and protocol argument, pickle.dumps and pickle._dumps produce the same bytes or the same exception."
    source := "invariant: C accelerator vs pure-Python twin", status := .refuted
    prop := ``DumpsTwinsAgree, thm := some ``dumpsTwinsAgree_refuted
    bug := some "pickle-c-batch-encoding"
    notes := "A list of 1001 items ends MARK item APPENDS in C and item APPEND in Python. Fixed on main." },
  { id := "pickle-dumps-twins-batch-ok", pyFile := "Modules/_pickle.c"
    pyFns := ["_pickle_dumps_impl", "_dumps"]
    statement := "The same, for values without the batch shapes where the twins differ."
    source := "invariant: C accelerator vs pure-Python twin", status := .refuted
    prop := ``DumpsTwinsAgreeBatchOk, thm := some ``dumpsTwinsAgreeBatchOk_refuted
    bug := some "pickle-protocol-long-overflow"
    notes := "protocol=-2**63-1 is OverflowError in C and the highest protocol in Python." },
  { id := "pickle-dumps-twins-batch-ok-long", pyFile := "Modules/_pickle.c"
    pyFns := ["_pickle_dumps_impl", "_dumps"]
    statement := "The same, also for protocol arguments within C long."
    source := "invariant: C accelerator vs pure-Python twin", status := .refuted
    prop := ``DumpsTwinsAgreeBatchOkLong, thm := some ``dumpsTwinsAgreeBatchOkLong_refuted
    bug := some "pickle-py-oversize-struct-error"
    notes := "bytes(2**32) at protocol 3: OverflowError in C, struct.error in Python." },
  { id := "pickle-dumps-twins-narrow", pyFile := "Modules/_pickle.c"
    pyFns := ["dump", "_pickle_dumps_impl", "save", "save_none", "save_bool", "save_long", "save_bytes",
      "_save_bytes_data", "save_bytearray", "_save_bytearray_data", "_Pickler_write_bytes", "save_unicode",
      "write_unicode_binary", "raw_unicode_escape", "store_tuple_elements", "save_tuple", "save_list",
      "batch_list", "batch_list_exact", "save_dict", "batch_dict", "batch_dict_exact_impl", "batch_dict_exact",
      "save_set", "save_frozenset_impl", "save_frozenset", "memo_get", "memo_put", "_Pickler_Write",
      "_Pickler_OpcodeBoundary", "_Pickler_CommitFrame", "_Pickler_SetProtocol", "_write_size64",
      "_Pickler.dump", "_dumps", "_Pickler.__init__", "_Pickler.memoize", "_Pickler.put", "_Pickler.get",
      "_Pickler.save", "_Pickler.save_none", "_Pickler.save_bool", "_Pickler.save_long",
      "_Pickler._save_bytes_no_memo", "_Pickler.save_bytes", "_Pickler._save_bytearray_no_memo",
      "_Pickler.save_bytearray", "_Pickler.save_str", "_Pickler.save_tuple", "_Pickler.save_list",
      "_Pickler._batch_appends", "_Pickler.save_dict", "_Pickler._batch_setitems", "_Pickler.save_set",
      "_Pickler.save_frozenset", "_Framer.__init__", "_Framer.start_framing", "_Framer.end_framing",
      "_Framer.commit_frame", "_Framer.write", "_Framer.write_large_bytes", "encode_long"]
    statement := "For every plain value without the batch shapes, whose ints pass C's LONG4 size check, and every protocol within C long, pickle.dumps and pickle._dumps both raise, or both return the same bytes: memoization, framing at protocol 4+, opcode choice and the reduce paths for bytes, bytearray, set and frozenset included."
    source := "invariant: C accelerator vs pure-Python twin", status := .proven
    prop := ``DumpsTwinsNarrow, thm := some ``dumpsTwinsNarrow_proven
    notes := "Each hypothesis is one refutation above. Exception classes may differ when both raise: on record in pickle-dumps-twins-batch-ok-long, exact equality is the open pickle-dumps-twins-exact-sized. Values are acyclic by construction; object identity is arbitrary, so sharing is covered. save_reduce and save_global are mirrored for the five globals only, so they are not claimed here." },
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
    bug := some "pickle-c-empty-batch-no-type-check"
    notes := "APPENDS with no items on None. The text-opcode and frame divergences have their own entries." },
  { id := "pickle-loads-twins-narrow", pyFile := "Modules/_pickle.c"
    pyFns := ["_pickle_loads_impl", "_loads"]
    statement := "On every data-only stream whose run meets none of the divergences on record (INT spellings and digit limit, NUL in text arguments, PUT index above sys.maxsize, an empty APPENDS or ADDITEMS batch on the wrong target, a FRAME longer than the data), pickle.loads and pickle._loads both raise or return equal objects."
    source := "invariant: C accelerator vs pure-Python twin", status := .open
    prop := ``LoadsTwinsNarrow
    notes := "Open: DecSim.lean has the state relation, the sequencing rule with Python's doomed runs, and how each reader computes. Still missing: the read, readline and readinto simulations, one lemma per handler over the tables, and the loop. This would settle most load_* rows." },
  { id := "pickle-frame-twins", pyFile := "Lib/pickle.py"
    pyFns := ["_Unframer.load_frame", "load_frame"]
    statement := "For a stream starting with a FRAME of any length, the two unpicklers accept the same streams and return equal objects."
    source := "PEP 3154; invariant: C accelerator vs pure-Python twin", status := .refuted
    prop := ``FrameTwins, thm := some ``frameTwins_refuted
    bug := some "pickle-py-truncated-frame"
    notes := "A frame longer than the data: C reports truncation, Python returns the object. python/cpython#128853; main rejects." },
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
    source := "docstrings of the readers, Lib/pickletools.py:212-306", status := .proven
    prop := ``ReadUintExact, thm := some ``readUintExact_proven },
  { id := "pickletools-read-int4-roundtrip", pyFile := "Lib/pickletools.py"
    pyFns := ["read_int4"]
    statement := "read_int4 returns every int the pickler's struct.pack('<i') wrote, at any position of any stream."
    source := "docstring of read_int4, Lib/pickletools.py:252-264", status := .proven
    prop := ``ReadInt4Roundtrip, thm := some ``readInt4Roundtrip_proven },
  { id := "pickletools-read-counted-roundtrip", pyFile := "Lib/pickletools.py"
    pyFns := ["read_bytes1", "read_string1", "read_bytes4", "read_bytes8", "read_bytearray8"]
    statement := "read_bytes1, read_string1, read_bytes4, read_bytes8 and read_bytearray8 return the payload after its count and stop right after it, for every payload the count field can hold, at any position of any stream."
    source := "pickle stream format, Lib/pickletools.py:409-591", status := .proven
    prop := ``ReadCountedRoundtrip, thm := some ``readCountedRoundtrip_proven },
  { id := "pickletools-read-string4-roundtrip", pyFile := "Lib/pickletools.py"
    pyFns := ["read_string4"]
    statement := "read_string4 returns the latin-1 text of every payload under 2**31 bytes, the range of its signed count."
    source := "pickle stream format, Lib/pickletools.py:438-458", status := .proven
    prop := ``ReadString4Roundtrip, thm := some ``readString4Roundtrip_proven },
  { id := "pickletools-read-long-roundtrip", pyFile := "Lib/pickletools.py"
    pyFns := ["read_long1", "read_long4"]
    statement := "read_long1 and read_long4 read back encode_long(x) for every int x whose encoding fits their count field."
    source := "LONG1 and LONG4 format, Lib/pickletools.py:873-926", status := .proven
    prop := ``ReadLongRoundtrip, thm := some ``readLongRoundtrip_proven },
  { id := "pickletools-read-unicode-roundtrip", pyFile := "Lib/pickletools.py"
    pyFns := ["read_unicodestring1", "read_unicodestring4", "read_unicodestring8"]
    statement := "read_unicodestring1, 4 and 8 return the utf-8/surrogatepass decoding of the payload, for every decodable payload their count can hold, at any position of any stream."
    source := "pickle stream format, Lib/pickletools.py:629-735", status := .proven
    prop := ``ReadUnicodeRoundtrip, thm := some ``readUnicodeRoundtrip_proven },
  { id := "pickletools-read-float8-exact", pyFile := "Lib/pickletools.py"
    pyFns := ["read_float8"]
    statement := "read_float8 consumes exactly the eight bytes of a BINFLOAT, and raises ValueError on fewer."
    source := "docstring of read_float8, Lib/pickletools.py:835-848", status := .proven
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
    source := "docstring of read_stringnl, Lib/pickletools.py:315-340", status := .proven
    prop := ``ReadStringnlPlain, thm := some ``readStringnlPlain_proven
    notes := "Lines with escapes go through the same escape decoder as load_string and are difftested. A lone quote is accepted here and rejected by load_string; maintainers hold pickletools may be more lenient (python/cpython#127045)." },
  { id := "pickletools-noescape-verbatim", pyFile := "Lib/pickletools.py"
    pyFns := ["read_stringnl_noescape"]
    statement := "read_stringnl_noescape returns every decodable line as load_global and load_persid read it, untouched."
    source := "stringnl_noescape descriptor, Lib/pickletools.py:375-384; twin", status := .refuted
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
    source := "invariant; docstring of genops, Lib/pickletools.py:2300-2323", status := .proven
    prop := ``GenopsWellFormed, thm := some ``genopsWellFormed_proven
    notes := "Streams with a FLOAT opcode are outside: the model stops there with Excluded, see pickletools-genops-fuel." },
  { id := "pickletools-dis-no-indexerror", pyFile := "Lib/pickletools.py"
    pyFns := ["dis"]
    statement := "dis reports bad streams with ValueError: it never raises IndexError."
    source := "docstring of dis, Lib/pickletools.py:2420-2431", status := .refuted
    prop := ``DisNoIndexError, thm := some ``disNoIndexError_refuted
    bug := some "pickle-tools-dis-mark-indexerror"
    notes := "b'(\\x85t.': TUPLE1 consumes the mark, then TUPLE walks off the emulated stack. Only malformed streams, which both unpicklers reject. Separately, repr(arg) stops dis on ints past the 4300-digit limit, on valid pickles: a deliberate limit, not recorded as a bug." },
  { id := "pickletools-dis-follows-genops", pyFile := "Lib/pickletools.py"
    pyFns := ["dis", "_genops", "genops"]
    statement := "When dis raises nothing, genops accepts the stream and the last line printed is the maximum protocol over its opcodes."
    source := "docstring of dis, Lib/pickletools.py:2396-2432", status := .proven
    prop := ``DisFollowsGenops, thm := some ``disFollowsGenops_proven
    notes := "The text of each line, the indentation and the annotations are difftested exactly." },
  { id := "pickletools-dis-stack-repr", pyFile := "Lib/pickletools.py"
    pyFns := ["StackObject.__repr__"]
    statement := "The 'stack not empty after STOP' error names what is left, bottom first, in list repr with each StackObject shown by name."
    source := "Lib/pickletools.py:974-975, :2545-2546", status := .proven
    prop := ``DisStackRepr, thm := some ``disStackRepr_proven },
  { id := "pickletools-optimize-raw-copy", pyFile := "Lib/pickletools.py"
    pyFns := ["optimize", "_genops"]
    statement := "optimize returns a stream without memo or frame opcodes, of protocol below 4, unchanged up to its STOP, at any opcode size."
    source := "docstring of optimize, Lib/pickletools.py:2328-2329", status := .proven
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
