import PyLean.Registry
import PyLean.Pickle.Diff
import PyLean.Pickle.SaveLongProps
import PyLean.Pickle.LongLineProps
import PyLean.Pickle.IntNarrow
import PyLean.Pickle.LongShortest
import PyLean.Pickle.TextRoundtrip
import PyLean.Pickle.EncProps
import PyLean.Pickle.EncFrame
import PyLean.Pickle.DecProps

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
    pyFns := ["encode_long", "decode_long"]
    statement := "decode_long(encode_long(x)) == x for every int x, through the trimmed two's-complement encoding at every byte boundary."
    source := "docstrings of encode_long and decode_long, Lib/pickle.py:356-404", status := .proven
    prop := ``DecodeEncodeLong, thm := some ``decodeEncodeLong_proven },
  { id := "pickle-encode-long-shortest", pyFile := "Lib/pickle.py"
    pyFns := ["encode_long", "decode_long"]
    statement := "encode_long(x) is the unique shortest byte string that decode_long maps to x, so encode_long is a bijection from ints onto the shortest encodings, including the sign-trimmed -(2**(8*j - 1))."
    source := "docstrings of encode_long and decode_long, Lib/pickle.py:356-404; LONG1/LONG4 in Lib/pickletools.py", status := .proven
    prop := ``EncodeLongShortest, thm := some ``encodeLongShortest_proven },
  { id := "pickle-text-int-roundtrip", pyFile := "Lib/pickle.py"
    pyFns := ["save_long", "load_int", "load_long"]
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
  { id := "pickle-save-long-twins-sized", pyFile := "Modules/_pickle.c"
    pyFns := ["save_long"]
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
    pyFns := ["load_int"]
    statement := "For every complete INT line with no NUL byte, not a bool spelling and with at most 4300 digit bytes, the C strtol fast path, its PyLong_FromString fallback and Python's int() accept the same lines and return the same value, including the bools I00 and I01."
    source := "invariant: C accelerator vs pure-Python twin", status := .proven
    prop := ``IntLineTwinsNarrow, thm := some ``intLineTwinsNarrow_proven
    notes := "The three hypotheses are the three refutations above. The digit bound is the documented sys.get_int_max_str_digits limit; it excludes some lines both twins reject. Exception classes can differ (an empty line is UnpicklingError in C, ValueError in Python)." },
  { id := "pickle-long-line-twins", pyFile := "Modules/_pickle.c"
    pyFns := ["load_long"]
    statement := "For every complete LONG line, the C and Python unpicklers accept the same lines and return the same value."
    source := "invariant: C accelerator vs pure-Python twin", status := .refuted
    prop := ``LongLineTwins, thm := some ``longLineTwins_refuted
    bug := some "pickle-c-nul-in-text-args"
    notes := "L5\\0 is 5 in C and ValueError in Python." },
  { id := "pickle-long-line-twins-no-nul", pyFile := "Modules/_pickle.c"
    pyFns := ["load_long"]
    statement := "For every complete LONG line without NUL bytes, with or without the L suffix, the C and Python unpicklers accept the same lines and return the same value."
    source := "invariant: C accelerator vs pure-Python twin", status := .proven
    prop := ``LongLineTwinsNoNul, thm := some ``longLineTwinsNoNul_proven
    notes := "The hypothesis is exactly the refuted case. Includes the 4300-digit limit, whitespace and underscores." },
  { id := "pickle-dumps-twins", pyFile := "Modules/_pickle.c"
    pyFns := ["dumps", "_dumps"]
    statement := "For every plain value and protocol argument, pickle.dumps and pickle._dumps produce the same bytes or the same exception."
    source := "invariant: C accelerator vs pure-Python twin", status := .refuted
    prop := ``DumpsTwinsAgree, thm := some ``dumpsTwinsAgree_refuted
    bug := some "pickle-c-batch-encoding"
    notes := "A list of 1001 items ends MARK item APPENDS in C and item APPEND in Python. Fixed on main." },
  { id := "pickle-dumps-twins-batch-ok", pyFile := "Modules/_pickle.c"
    pyFns := ["dumps", "_dumps"]
    statement := "The same, for values without the batch shapes where the twins differ."
    source := "invariant: C accelerator vs pure-Python twin", status := .refuted
    prop := ``DumpsTwinsAgreeBatchOk, thm := some ``dumpsTwinsAgreeBatchOk_refuted
    bug := some "pickle-protocol-long-overflow"
    notes := "protocol=-2**63-1 is OverflowError in C and the highest protocol in Python." },
  { id := "pickle-dumps-twins-batch-ok-long", pyFile := "Modules/_pickle.c"
    pyFns := ["dumps", "_dumps"]
    statement := "The same, also for protocol arguments within C long."
    source := "invariant: C accelerator vs pure-Python twin", status := .refuted
    prop := ``DumpsTwinsAgreeBatchOkLong, thm := some ``dumpsTwinsAgreeBatchOkLong_refuted
    bug := some "pickle-py-oversize-struct-error"
    notes := "bytes(2**32) at protocol 3: OverflowError in C, struct.error in Python." },
  { id := "pickle-dumps-twins-narrow", pyFile := "Modules/_pickle.c"
    pyFns := ["dumps", "_dumps"]
    statement := "For every plain value without the batch shapes, whose ints pass C's LONG4 size check, and every protocol within C long, pickle.dumps and pickle._dumps both raise, or both return the same bytes: memoization, framing at protocol 4+, opcode choice and the reduce paths for bytes, bytearray, set and frozenset included."
    source := "invariant: C accelerator vs pure-Python twin", status := .proven
    prop := ``DumpsTwinsNarrow, thm := some ``dumpsTwinsNarrow_proven
    notes := "Each hypothesis is one refutation above. Exception classes may differ when both raise (pickle-py-oversize-struct-error). Values are acyclic by construction; object identity is arbitrary, so sharing is covered." },
  { id := "pickle-loads-twins-exact", pyFile := "Modules/_pickle.c"
    pyFns := ["loads", "_loads"]
    statement := "On every data-only stream, pickle.loads and pickle._loads raise the same exception class."
    source := "invariant: C accelerator vs pure-Python twin", status := .refuted
    prop := ``LoadsTwinsExact, thm := some ``loadsTwinsExact_refuted
    bug := some "pickle-py-unpickler-raw-exceptions"
    notes := "POP on an empty stack: UnpicklingError in C, IndexError in Python. Allowed by the docs." },
  { id := "pickle-loads-twins-accept", pyFile := "Modules/_pickle.c"
    pyFns := ["loads", "_loads"]
    statement := "pickle.loads and pickle._loads accept the same data-only streams and return equal objects."
    source := "invariant: C accelerator vs pure-Python twin", status := .refuted
    prop := ``LoadsTwinsAccept, thm := some ``loadsTwinsAccept_refuted
    bug := some "pickle-c-empty-batch-no-type-check"
    notes := "APPENDS with no items on None. The text-opcode and frame divergences have their own entries." },
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
    notes := "Index 2**63: OverflowError in C. Maintainers: not a bug (python/cpython#144410)." }
]

end PyLean.Pickle
