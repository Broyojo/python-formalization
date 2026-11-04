import PyLean.BytesObj.Bytes.Slots
import PyLean.BytesObj.Bytes.Specs3
import PyLean.BytesObj.Bytes.FromFormatProps

/-!
Properties of the escape decoder, of `bytes`' slots, and of three C-API helpers.
-/

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

set_option linter.unusedSimpArgs false

/-! ## `_PyBytes_DecodeEscape2` -/

/-- A run with no backslash is copied (bytesobject.c:1187-1190). -/
theorem decodeLoop_lit (errors : Option String) (q : Seq) (h : 92 ∉ q) :
    ∀ (fuel pos : Nat) (out : Seq) (fb : FirstBad), q.length < fuel →
      decodeLoop errors fuel pos q out fb = .ok (out ++ q, fb) := by
  induction q with
  | nil =>
    intro fuel pos out fb hf
    cases fuel with
    | zero => omega
    | succ f => simp [decodeLoop]
  | cons c cs ih =>
    intro fuel pos out fb hf
    have hc : c ≠ 92 := fun e => h (by simp [e])
    have hcs : 92 ∉ cs := fun e => h (by simp [e])
    cases fuel with
    | zero => omega
    | succ f =>
      simp only [List.length_cons] at hf
      simp only [decodeLoop, if_pos hc]
      rw [ih hcs f (pos + 1) (out ++ [c]) fb (by omega)]
      simp

/-- The one-character escapes, `(escape byte, value)`, bytesobject.c:1200-1211. -/
def escPairs : List (Nat × Nat) :=
  [(92, 92), (39, 39), (34, 34), (98, 8), (102, 12), (116, 9), (110, 10), (114, 13), (118, 11), (97, 7)]

/-- The escapes of `_PyBytes_DecodeEscape2` (bytesobject.c:1186-1275), each followed by any run without
a backslash: the one-character escapes `\\ \' \" \b \f \t \n \r \v \a`; a backslash-newline, which
writes nothing; three octal digits, kept modulo 256, with a value above `0o377` reported at the
first digit (`s - 3`, :1225-1229); one octal digit before a non-octal byte; two hex digits after `\x`; and an unknown escape,
which keeps the backslash and is reported at its byte. A trailing backslash is the `ValueError`. An
invalid `\x` is the `ValueError` with the backslash's position under `strict` (or no handler), `?`
under `replace`, nothing under `ignore`, which then skip one more hex digit, and the `unknown error
handling code` ValueError under any other name. -/
def EscapeSpec : Prop :=
  (∀ (e v : Nat) (q : Seq) (err : Option String), (e, v) ∈ escPairs → 92 ∉ q →
    decodeEscape2 (92 :: e :: q) err = .ok (v :: q, none)) ∧
  (∀ (q : Seq) (err : Option String), 92 ∉ q → decodeEscape2 (92 :: 10 :: q) err = .ok (q, none)) ∧
  (∀ (a b c : Nat) (q : Seq) (err : Option String), isOct a → isOct b → isOct c → 92 ∉ q →
    let v := ((a - 48) * 8 + (b - 48)) * 8 + (c - 48)
    decodeEscape2 (92 :: a :: b :: c :: q) err = .ok (v % 256 :: q, if v > 255 then some (v, 1) else none)) ∧
  (∀ (a d : Nat) (q : Seq) (err : Option String), isOct a → isOct d = false → d ≠ 92 → 92 ∉ q →
    decodeEscape2 (92 :: a :: d :: q) err = .ok ((a - 48) :: d :: q, none)) ∧
  (∀ (d1 d2 : Nat) (q : Seq) (err : Option String), digitValue d1 < 16 → digitValue d2 < 16 → 92 ∉ q →
    decodeEscape2 (92 :: 120 :: d1 :: d2 :: q) err = .ok ((digitValue d1 * 16 + digitValue d2) :: q, none)) ∧
  (∀ (e : Nat) (q : Seq) (err : Option String), simpleEscape e = none → e ≠ 10 → isOct e = false →
    e ≠ 120 → 92 ∉ q → decodeEscape2 (92 :: e :: q) err = .ok (92 :: e :: q, some (e, 1))) ∧
  (∀ (p : Seq) (err : Option String), 92 ∉ p →
    decodeEscape2 (p ++ [92]) err = .error (.valueError "Trailing \\ in string")) ∧
  (∀ (g : Nat) (q : Seq), digitValue g ≥ 16 →
    decodeEscape2 (92 :: 120 :: g :: q) none = .error (.valueError "invalid \\x escape at position 0") ∧
    decodeEscape2 (92 :: 120 :: g :: q) (some "strict") =
      .error (.valueError "invalid \\x escape at position 0")) ∧
  (∀ (g : Nat) (q : Seq), digitValue g ≥ 16 → isXDigitC g = false → g ≠ 92 → 92 ∉ q →
    decodeEscape2 (92 :: 120 :: g :: q) (some "replace") = .ok (63 :: g :: q, none) ∧
    decodeEscape2 (92 :: 120 :: g :: q) (some "ignore") = .ok (g :: q, none)) ∧
  (∀ (h g : Nat) (q : Seq), digitValue h < 16 → isXDigitC h = true → digitValue g ≥ 16 → g ≠ 92 →
    92 ∉ q → decodeEscape2 (92 :: 120 :: h :: g :: q) (some "replace") = .ok (63 :: g :: q, none)) ∧
  (∀ (g : Nat) (q : Seq) (e : String), digitValue g ≥ 16 → e ≠ "strict" → e ≠ "replace" →
    e ≠ "ignore" → decodeEscape2 (92 :: 120 :: g :: q) (some e) =
      .error (.valueError s!"decoding error; unknown error handling code: {e}"))

/-- A run with no backslash in front of the rest. -/
theorem decodeLoop_app (errors : Option String) (p : Seq) (h : 92 ∉ p) :
    ∀ (r : Seq) (fuel pos : Nat) (out : Seq) (fb : FirstBad), p.length < fuel →
      decodeLoop errors fuel pos (p ++ r) out fb =
        decodeLoop errors (fuel - p.length) (pos + p.length) r (out ++ p) fb := by
  induction p with
  | nil => intro r fuel pos out fb _; simp
  | cons c cs ih =>
    intro r fuel pos out fb hf
    have hc : c ≠ 92 := fun e => h (by simp [e])
    have hcs : 92 ∉ cs := fun e => h (by simp [e])
    cases fuel with
    | zero => omega
    | succ f =>
      simp only [List.length_cons] at hf
      simp only [List.cons_append, decodeLoop, if_pos hc]
      rw [ih hcs r f (pos + 1) (out ++ [c]) fb (by omega)]
      simp only [List.length_cons, List.append_assoc, List.singleton_append]
      congr 1 <;> omega

theorem oct_facts (a : Nat) (h : isOct a = true) :
    simpleEscape a = none ∧ a ≠ 10 ∧ a ≠ 120 ∧ a ≠ 92 ∧ 48 ≤ a ∧ a ≤ 55 := by
  simp only [isOct, decide_eq_true_eq] at h
  refine ⟨?_, by omega, by omega, by omega, h.1, h.2⟩
  unfold simpleEscape
  repeat (rw [if_neg (by omega)])

theorem simple_ne92 (e : Nat) (h : simpleEscape e = none) : e ≠ 92 := by
  intro he; subst he; simp [simpleEscape] at h

/-! One iteration of the loop for each escape, at any fuel. -/

theorem step_simple (err : Option String) (f pos : Nat) (e v : Nat) (q out : Seq) (fb : FirstBad)
    (he : (e, v) ∈ escPairs) :
    decodeLoop err (f + 1) pos (92 :: e :: q) out fb = decodeLoop err f (pos + 2) q (out ++ [v]) fb := by
  simp only [escPairs, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at he
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [decodeLoop, simpleEscape]

theorem step_nl (err : Option String) (f pos : Nat) (q out : Seq) (fb : FirstBad) :
    decodeLoop err (f + 1) pos (92 :: 10 :: q) out fb = decodeLoop err f (pos + 2) q out fb := by
  simp [decodeLoop]

theorem step_oct3 (err : Option String) (f pos : Nat) (a b c : Nat) (q out : Seq) (fb : FirstBad)
    (ha : isOct a = true) (hb : isOct b = true) (hc : isOct c = true) :
    decodeLoop err (f + 1) pos (92 :: a :: b :: c :: q) out fb =
      let v := ((a - 48) * 8 + (b - 48)) * 8 + (c - 48)
      decodeLoop err f (pos + 4) q (out ++ [v % 256])
        (if v > 255 ∧ fb.isNone then some (v, pos + 1) else fb) := by
  obtain ⟨sa, a10, a120, a92, a1, a2⟩ := oct_facts a ha
  simp only [decodeLoop, a92, a10, sa, ha, hb, hc, ite_true, ite_false, ne_eq, not_false_eq_true]
  have e1 : 2 + 1 + 1 = 4 := rfl
  have e2 : pos + 4 - 3 = pos + 1 := by omega
  simp [e2]

theorem step_oct1 (err : Option String) (f pos : Nat) (a d : Nat) (q out : Seq) (fb : FirstBad)
    (ha : isOct a = true) (hd : isOct d = false) :
    decodeLoop err (f + 1) pos (92 :: a :: d :: q) out fb =
      decodeLoop err f (pos + 2) (d :: q) (out ++ [(a - 48) % 256])
        (if a - 48 > 255 ∧ fb.isNone then some (a - 48, pos - 1) else fb) := by
  obtain ⟨sa, a10, a120, a92, a1, a2⟩ := oct_facts a ha
  simp only [decodeLoop, a92, a10, sa, ha, hd, if_true, if_false, ne_eq, not_false_eq_true,
    Bool.false_eq_true]
  congr 2 <;> omega

theorem step_x (err : Option String) (f pos : Nat) (d1 d2 : Nat) (q out : Seq) (fb : FirstBad)
    (h1 : digitValue d1 < 16) (h2 : digitValue d2 < 16) :
    decodeLoop err (f + 1) pos (92 :: 120 :: d1 :: d2 :: q) out fb =
      decodeLoop err f (pos + 4) q (out ++ [digitValue d1 * 16 + digitValue d2]) fb := by
  simp [decodeLoop, simpleEscape, isOct, h1, h2]

theorem step_unknown (err : Option String) (f pos : Nat) (e : Nat) (q out : Seq) (fb : FirstBad)
    (he : simpleEscape e = none) (e10 : e ≠ 10) (eo : isOct e = false) (e120 : e ≠ 120) :
    decodeLoop err (f + 1) pos (92 :: e :: q) out fb =
      decodeLoop err f (pos + 1) (e :: q) (out ++ [92]) (if fb.isNone then some (e, pos + 1) else fb) := by
  simp [decodeLoop, he, e10, eo, e120]

theorem step_xbad (err : Option String) (f pos : Nat) (g : Nat) (q out : Seq) (fb : FirstBad)
    (hg : digitValue g ≥ 16) :
    decodeLoop err (f + 1) pos (92 :: 120 :: g :: q) out fb =
      match badHex err pos (g :: q) out with
      | .ok (o, r, n) => decodeLoop err f (pos + 2 + n) r o fb
      | .error x => .error x := by
  have hg' : ¬ digitValue g < 16 := by omega
  cases q <;> simp [decodeLoop, simpleEscape, isOct, hg'] <;> rfl

theorem step_xbad2 (err : Option String) (f pos : Nat) (h g : Nat) (q out : Seq) (fb : FirstBad)
    (hng : ¬ (digitValue h < 16 ∧ digitValue g < 16)) :
    decodeLoop err (f + 1) pos (92 :: 120 :: h :: g :: q) out fb =
      match badHex err pos (h :: g :: q) out with
      | .ok (o, r, n) => decodeLoop err f (pos + 2 + n) r o fb
      | .error x => .error x := by
  simp only [decodeLoop, simpleEscape, isOct, hng, ite_false, ite_true]
  simp <;> rfl

theorem decodeEscape2_eq (s : Seq) (err : Option String) :
    decodeEscape2 s err = decodeLoop err ((2 * s.length + 1) + 1) 0 s [] none := rfl

theorem escapeSpec_proven : EscapeSpec := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e v q err he hq
    rw [decodeEscape2_eq, step_simple _ _ _ _ _ _ _ _ he, decodeLoop_lit _ q hq _ _ _ _ (by simp; omega)]
    simp
  · intro q err hq
    rw [decodeEscape2_eq, step_nl, decodeLoop_lit _ q hq _ _ _ _ (by simp; omega)]
    simp
  · intro a b c q err ha hb hc hq
    rw [decodeEscape2_eq, step_oct3 _ _ _ _ _ _ _ _ _ ha hb hc]
    simp only []
    rw [decodeLoop_lit _ q hq _ _ _ _ (by simp; omega)]
    simp
  · intro a d q err ha hd d92 hq
    obtain ⟨sa, a10, a120, a92, a1, a2⟩ := oct_facts a ha
    have hq' : 92 ∉ d :: q := by simp [Ne.symm d92, hq]
    rw [decodeEscape2_eq, step_oct1 _ _ _ _ _ _ _ _ ha hd,
      decodeLoop_lit _ (d :: q) hq' _ _ _ _ (by simp; omega)]
    have h1 : ¬ (a - 48 > 255) := by omega
    have h2 : (a - 48) % 256 = a - 48 := Nat.mod_eq_of_lt (by omega)
    simp [h1, h2]
  · intro d1 d2 q err h1 h2 hq
    rw [decodeEscape2_eq, step_x _ _ _ _ _ _ _ _ h1 h2, decodeLoop_lit _ q hq _ _ _ _ (by simp; omega)]
    simp
  · intro e q err he e10 eo e120 hq
    have e92 := simple_ne92 e he
    have hq' : 92 ∉ e :: q := by simp [Ne.symm e92, hq]
    rw [decodeEscape2_eq, step_unknown _ _ _ _ _ _ _ he e10 eo e120,
      decodeLoop_lit _ (e :: q) hq' _ _ _ _ (by simp; omega)]
    simp
  · intro p err hp
    rw [decodeEscape2_eq, decodeLoop_app _ p hp [92] _ _ _ _ (by simp; omega)]
    have : 2 * (p ++ [92]).length + 1 + 1 - p.length = (p.length + 3) + 1 := by simp; omega
    rw [this]
    simp [decodeLoop]
  · intro g q hg
    constructor
    all_goals
      rw [decodeEscape2_eq, step_xbad _ _ _ _ _ _ _ hg]
      simp [badHex]
      rfl
  · intro g q hg hx g92 hq
    have hq' : 92 ∉ g :: q := by simp [Ne.symm g92, hq]
    constructor
    all_goals
      rw [decodeEscape2_eq, step_xbad _ _ _ _ _ _ _ hg]
      simp only [badHex, hx]
      simp only [Option.getD_some, beq_iff_eq]
      simp
      rw [decodeLoop_lit _ (g :: q) hq' _ _ _ _ (by simp; omega)]
      simp
  · intro h g q hh hx hg g92 hq
    have hq' : 92 ∉ g :: q := by simp [Ne.symm g92, hq]
    have hng : ¬ (digitValue h < 16 ∧ digitValue g < 16) := by omega
    rw [decodeEscape2_eq, step_xbad2 _ _ _ _ _ _ _ _ hng]
    simp only [badHex, hx]
    simp
    rw [decodeLoop_lit _ (g :: q) hq' _ _ _ _ (by simp; omega)]
    simp
  · intro g q e hg h1 h2 h3
    rw [decodeEscape2_eq, step_xbad _ _ _ _ _ _ _ hg]
    simp [badHex, h1, h2, h3]

/-! ## `PyBytes_DecodeEscape` under `-W error` -/

/-- `PyBytes_DecodeEscape` (bytesobject.c:1284-1320): a decode with no invalid escape is the result
under any warnings filter; with one, the warning is issued (the text names an octal value above `0o377`
in octal, and any other escape by its byte), and under an `error` filter the call fails with the
`DeprecationWarning` itself (:1299-1316). End to end for `\777` and for an unknown escape. -/
def DecodeEscapeWarn : Prop :=
  (∀ (s : Seq) (err : Option String) (r : Seq), decodeEscape2 s err = .ok (r, none) →
    bytesDecodeEscapeW s err true = .ok (r, none) ∧ bytesDecodeEscapeW s err false = .ok (r, none)) ∧
  (∀ (s : Seq) (err : Option String) (r : Seq) (fb : Nat × Nat) (m : String),
    decodeEscape2 s err = .ok (r, some fb) → escapeWarning (some fb) = some m →
    bytesDecodeEscapeW s err true = .error (.named "DeprecationWarning" m) ∧
    bytesDecodeEscapeW s err false = .ok (r, some m)) ∧
  (∀ err : Option String, bytesDecodeEscapeW [92, 55, 55, 55] err true = .error (.named "DeprecationWarning"
    "b\"\\777\" is an invalid octal escape sequence. Such sequences will not work in the future. ")) ∧
  (∀ (e : Nat) (err : Option String), simpleEscape e = none → e ≠ 10 → isOct e = false → e ≠ 120 →
    e < 256 → bytesDecodeEscapeW [92, e] err true = .error (.named "DeprecationWarning"
      ("b\"\\" ++ String.ofList [Char.ofNat e] ++
        "\" is an invalid escape sequence. Such sequences will not work in the future. ")))

theorem decodeEscapeWarn_proven : DecodeEscapeWarn := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s err r h
    simp [bytesDecodeEscapeW, h, escapeWarning, bind, Except.bind, pure, Except.pure]
  · intro s err r fb m h hm
    simp [bytesDecodeEscapeW, h, hm, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExcept.throw]
    rfl
  · intro err
    have := (escapeSpec_proven).2.2.1 55 55 55 [] err rfl rfl rfl (by simp)
    simp only [] at this
    simp [bytesDecodeEscapeW, this, escapeWarning, bind, Except.bind, pure, Except.pure, throw,
      throwThe, MonadExcept.throw]
    decide
  · intro e err he e10 eo e120 h256
    have := (escapeSpec_proven).2.2.2.2.2.1 e [] err he e10 eo e120 (by simp)
    have h1 : ¬ (e > 255) := by omega
    simp [bytesDecodeEscapeW, this, escapeWarning, h1, bind, Except.bind, pure, Except.pure, throw,
      throwThe, MonadExcept.throw]
    rfl

/-! ## The cached hash, `PyBytes_AsStringAndSize`, `PyBytes_Join` -/

/-- `set_ob_shash` (bytesobject.c:53-64) stores the hash `bytes_hash` computed, and nothing else
changes; a filled cache is returned as it is. -/
def SetObShash : Prop :=
  (∀ (hb : Seq → Int) (o : BytesSt), o.shash = -1 →
    bytesHash hb o = (hb o.data, { o with shash := hb o.data })) ∧
  (∀ (hb : Seq → Int) (o : BytesSt), o.shash ≠ -1 → bytesHash hb o = (o.shash, o))

theorem setObShash_proven : SetObShash := by
  refine ⟨?_, ?_⟩
  · intro hb o h; simp [bytesHash, h]
  · intro hb o h; simp [bytesHash, h]

/-- `PyBytes_AsStringAndSize(obj, &s, len)` (bytesobject.c:1346-1371): a non-bytes is the
`expected bytes, X found` TypeError with or without a length pointer; with `len == NULL` a string
without NUL is accepted and one with a NUL refused (:1363-1368). -/
def AsStringAndSizeSpec : Prop :=
  (∀ (o : Obj) (wantLen : Bool), (∀ s, o ≠ .bytes s) →
    pyBytesAsStringAndSize o wantLen = .error (expectedBytes o)) ∧
  (∀ s : Seq, 0 ∉ s → pyBytesAsStringAndSize (.bytes s) false = .ok s) ∧
  (∀ (a b : Seq), 0 ∉ a → pyBytesAsStringAndSize (.bytes (a ++ 0 :: b)) false =
    .error (.valueError "embedded null byte"))

theorem asStringAndSizeSpec_proven : AsStringAndSizeSpec := by
  refine ⟨?_, ?_, ?_⟩
  · intro o w h
    cases o <;> first | exact absurd rfl (h _) | simp [pyBytesAsStringAndSize]
  · intro s h
    simp [pyBytesAsStringAndSize, takeWhile_nz' s h]
  · exact cApiSpec_proven.2.2.2.1

/-- `PyBytes_Join(sep, iterable)` (bytesobject.c:1994-2008) refuses a `sep` that is not bytes with
`sep: expected bytes, got T`, whatever the iterable; with a bytes `sep` it is `bytes.join`. -/
def PyBytesJoinSep : Prop :=
  (∀ (sep it : Obj), (∀ s, sep ≠ .bytes s) →
    pyBytesJoin sep it = .error (.typeError s!"sep: expected bytes, got {sep.typeName}")) ∧
  (∀ (s : Seq) (it : Obj), pyBytesJoin (.bytes s) it = stringlibJoin s it)

theorem pyBytesJoinSep_proven : PyBytesJoinSep := by
  refine ⟨?_, ?_⟩
  · intro sep it h
    cases sep <;> first | exact absurd rfl (h _) | rfl
  · intro s it; rfl

/-! ## `bytes_repr`, `bytes_str`, `bytes_richcompare` -/

/-- `repr(b)` (`bytes_repr`, bytesobject.c:1509-1513) uses smart quotes: `"` exactly when the bytes have
a `'` and no `"`, else `'`, with the body of the literal. -/
def BytesReprSmart : Prop :=
  ∀ s : Seq, (∀ c ∈ s, c < 256) → (s.length : Int) * 5 + 3 ≤ ssizeMax →
    bytesReprSlot s = .ok (if 39 ∈ s ∧ 34 ∉ s then [98, 34] ++ reprBody 34 s ++ [34]
      else [98, 39] ++ reprBody 39 s ++ [39])

theorem bytesReprSmart_proven : BytesReprSmart := by
  intro s hs hl
  have h := (reprSpec_proven "bytes" s true hs hl).1
  simp only [bytesReprSlot, bytesRepr]
  rw [h]
  by_cases hq : 39 ∈ s ∧ 34 ∉ s <;> simp [hq]

/-- Under `-b` (`bw = 1`) `str(b)` warns `str() on a bytes instance` and gives `repr(b)`; under `-bb`
it raises that `BytesWarning` (bytesobject.c:1515-1525). `b == x` and `b != x` with a str or an int `x`
warn `Comparison between bytes and string` / `... and int` and give `NotImplemented`, or raise under
`-bb`; the order comparisons never warn; without `-b` nothing is issued (:1655-1667). -/
def BytesWarnings : Prop :=
  (∀ s : Seq, bytesStrW 0 s = (bytesReprSlot s).map (fun r => (r, []))) ∧
  (∀ s : Seq, bytesStrW 1 s = (bytesReprSlot s).map (fun r => (r, ["str() on a bytes instance"]))) ∧
  (∀ (s : Seq) (bw : Nat), 2 ≤ bw → bytesStrW bw s = .error (.named "BytesWarning" "str() on a bytes instance")) ∧
  (∀ (s cs : Seq) (op : CmpOp), (op = .eq ∨ op = .ne) →
    bytesRichcompareW 1 (.bytes s) (.str cs) op = .ok (none, ["Comparison between bytes and string"]) ∧
    bytesRichcompareW 2 (.bytes s) (.str cs) op =
      .error (.named "BytesWarning" "Comparison between bytes and string")) ∧
  (∀ (s : Seq) (v : Int) (op : CmpOp), (op = .eq ∨ op = .ne) →
    bytesRichcompareW 1 (.bytes s) (.int v) op = .ok (none, ["Comparison between bytes and int"]) ∧
    bytesRichcompareW 2 (.int v) (.bytes s) op =
      .error (.named "BytesWarning" "Comparison between bytes and int")) ∧
  (∀ (bw : Nat) (a b : Obj) (op : CmpOp), (op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge) →
    bytesRichcompareW bw a b op = .ok (bytesRichcompareObj a b op, [])) ∧
  (∀ (a b : Obj) (op : CmpOp), bytesRichcompareW 0 a b op = .ok (bytesRichcompareObj a b op, []))

theorem bytesWarnings_proven : BytesWarnings := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s
    simp only [bytesStrW, ne_eq, not_true_eq_false, ite_false]
    cases bytesReprSlot s <;> rfl
  · intro s
    simp only [bytesStrW, bytesWarn]
    cases bytesReprSlot s <;> rfl
  · intro s bw h
    have h0 : bw ≠ 0 := by omega
    simp [bytesStrW, bytesWarn, h0, h, bind, Except.bind]
  · intro s cs op hop
    rcases hop with rfl | rfl <;> exact ⟨by simp [bytesRichcompareW, bytesWarn, bind, Except.bind,
      pure, Except.pure], by simp [bytesRichcompareW, bytesWarn, bind, Except.bind, pure, Except.pure]⟩
  · intro s v op hop
    rcases hop with rfl | rfl <;> exact ⟨by simp [bytesRichcompareW, bytesWarn, bind, Except.bind,
      pure, Except.pure], by simp [bytesRichcompareW, bytesWarn, bind, Except.bind, pure, Except.pure]⟩
  · intro bw a b op hop
    have hne : ¬ (op = .eq ∨ op = .ne) := by rcases hop with rfl | rfl | rfl | rfl <;> simp
    cases a <;> cases b <;> simp [bytesRichcompareW, bytesRichcompareObj, hne]
  · intro a b op
    cases a <;> cases b <;> simp [bytesRichcompareW, bytesRichcompareObj]

/-! ## `bytes_item`, `PySequence_GetItem`, `bytes_subscript` -/

/-- `sq_item` (`bytes_item`, bytesobject.c:1622-1631) does not wrap a negative index; through
`PySequence_GetItem`, which adds the length first (Objects/abstract.c:1849-1857), it agrees with
`b[i]` for every index in `Py_ssize_t`. `bytes_subscript` dispatches on the item (:1730-1789): an int,
a bool or an object with `__index__` is that index, with the overflow message naming the item's
type; an `__index__` that raises passes its exception on; anything else that is not a slice is the
`byte indices must be integers or slices` TypeError. -/
def SubscriptDispatch : Prop :=
  (∀ (s : Seq) (i : Int), i < 0 → bytesItem s i = .error (.indexError "index out of range")) ∧
  (∀ (s : Seq) (i : Int), ssizeMin ≤ i → i ≤ ssizeMax → pySequenceGetItem s i = bytesGetItem s i) ∧
  (∀ (s : Seq) (v : Int), bytesSubscriptObj s (.int v) = bytesGetItem s v) ∧
  (∀ (s : Seq) (v : Int), ssizeMin ≤ v → v ≤ ssizeMax → bytesSubscriptObj s (.index v) = bytesGetItem s v) ∧
  (∀ (s : Seq) (v : Int), (v < ssizeMin ∨ v > ssizeMax) → bytesSubscriptObj s (.index v) =
    .error (.indexError "cannot fit 'BIdx' into an index-sized integer")) ∧
  (∀ (s : Seq) (b : Bool), bytesSubscriptObj s (.bool b) = bytesGetItem s (if b then 1 else 0)) ∧
  (∀ (s : Seq) (e : PyExc), bytesSubscriptObj s (.indexRaises e) = .error e) ∧
  (∀ (s : Seq) (o : Obj), o.index? = none → bytesSubscriptObj s o =
    .error (.typeError s!"byte indices must be integers or slices, not {o.typeName}"))

theorem subscriptDispatch_proven : SubscriptDispatch := by
  have hmax := ssizeMax_val
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s i h; simp [bytesItem, h]
  · intro s i h1 h2
    have hr : ssizeMin ≤ i ∧ i ≤ ssizeMax := ⟨h1, h2⟩
    simp [pySequenceGetItem, bytesItem, bytesGetItem, Sequences.subIndex, Sequences.asSsizeExc, hr,
      bind, Except.bind, pure, Except.pure]
    split <;> rfl
  · intro s v
    by_cases hr : ssizeMin ≤ v ∧ v ≤ ssizeMax
    · have hr' : ¬ (v < ssizeMin ∨ v > ssizeMax) := by omega
      simp [bytesSubscriptObj, Obj.index?, bytesGetItem, Sequences.subIndex, Sequences.asSsizeExc, hr, hr',
        bind, Except.bind, pure, Except.pure]
      split <;> rfl
    · have hr' : v < ssizeMin ∨ v > ssizeMax := by omega
      simp [bytesSubscriptObj, Obj.index?, bytesGetItem, Sequences.subIndex, Sequences.asSsizeExc, hr, hr',
        Obj.typeName, bind, Except.bind]
      rfl
  · intro s v h1 h2
    have hr : ssizeMin ≤ v ∧ v ≤ ssizeMax := ⟨h1, h2⟩
    have hr' : ¬ (v < ssizeMin ∨ v > ssizeMax) := by omega
    simp [bytesSubscriptObj, Obj.index?, bytesGetItem, Sequences.subIndex, Sequences.asSsizeExc, hr, hr',
      bind, Except.bind, pure, Except.pure]
    split <;> rfl
  · intro s v h
    simp [bytesSubscriptObj, Obj.index?, h, Obj.typeName]
    rfl
  · intro s b
    have hr : ¬ ((if b then (1 : Int) else 0) < ssizeMin ∨ (if b then (1 : Int) else 0) > ssizeMax) := by
      simp only [ssizeMin, hmax]; split <;> omega
    have hr2 : ssizeMin ≤ (if b then (1 : Int) else 0) ∧ (if b then (1 : Int) else 0) ≤ ssizeMax := by
      simp only [ssizeMin, hmax]; split <;> omega
    simp only [bytesSubscriptObj, Obj.index?, hr, ite_false, bytesGetItem, Sequences.subIndex,
      Sequences.asSsizeExc, hr2, ite_true, bind, Except.bind, pure, Except.pure]
    rfl
  · intro s e; rfl
  · intro s o h
    simp [bytesSubscriptObj, h]

/-! ## `bytes_buffer_getbuffer` -/

/-- A bytes exports its contents read-only (bytesobject.c:1792-1798): `PyBUF_SIMPLE` and every request
without `PyBUF_WRITABLE` succeed with `readonly = 1`, and a `PyBUF_WRITABLE` request is refused with
`BufferError('Object is not writable.')` (Objects/abstract.c:788-793); `PyBUF_READ` and `PyBUF_WRITE`
are the `SystemError` of `PyErr_BadInternalCall` (:784-787, recorded as
bytesobj-bytearray-buffer-flags-systemerror). -/
def BytesBufferSpec : Prop :=
  (∀ (s : Seq) (flags : Int), flags % 2 = 1 → bytesGetBuffer s flags =
    .error (bufferError "Object is not writable.")) ∧
  (∀ (s : Seq) (flags : Int), flags % 2 = 0 → flags ≠ 0x100 → flags ≠ 0x200 →
    bytesGetBuffer s flags = .ok (s, true)) ∧
  (∀ s : Seq, bytesGetBuffer s 0x100 =
    .error (systemError "Objects/abstract.c:785: bad argument to internal function"))

theorem bytesBufferSpec_proven : BytesBufferSpec := by
  refine ⟨?_, ?_, ?_⟩
  · intro s flags h
    have h0 : flags ≠ 0 := by intro e; subst e; simp at h
    have h1 : ¬ (flags = 0x100 ∨ flags = 0x200) := by omega
    simp [bytesGetBuffer, h0, h1, h]
  · intro s flags h h1 h2
    by_cases h0 : flags = 0
    · simp [bytesGetBuffer, h0]
    · have h3 : ¬ (flags = 0x100 ∨ flags = 0x200) := by omega
      simp [bytesGetBuffer, h0, h3, h]
  · intro s; rfl

/-! ## `partition` and `rpartition` return the separator object -/

/-- The contents of a result item. -/
def objContents (o : Obj) : Seq := (o.buffer?).getD []

/-- `b.partition(sep)` and `b.rpartition(sep)` (bytesobject.c:1899-1936): the contents are those of
`stringlib_partition` on the buffers, and the middle item is the separator object itself when it is
found (the docstring's "the separator itself": a bytearray or memoryview separator comes back as it
is), the empty bytes when it is not. -/
def PartitionObj : Prop :=
  (∀ (s : Seq) (sep : Obj) (b : Seq), getBuffer sep = .ok b →
    (bytesPartitionObj s sep).map (fun t => (objContents t.1, objContents t.2.1, objContents t.2.2)) =
      bytesPartition s b ∧
    (bytesRPartitionObj s sep).map (fun t => (objContents t.1, objContents t.2.1, objContents t.2.2)) =
      bytesRPartition s b) ∧
  (∀ (s : Seq) (sep : Obj) (b : Seq), getBuffer sep = .ok b → b ≠ [] →
    (bytesPartitionObj s sep).map (fun t => t.2.1) =
      .ok (if fastsearch s b (-1) .search < 0 then .bytes [] else sep) ∧
    (bytesRPartitionObj s sep).map (fun t => t.2.1) =
      .ok (if fastsearch s b (-1) .rsearch < 0 then .bytes [] else sep))

@[simp] theorem objContents_bytes (x : Seq) : objContents (.bytes x) = x := rfl

theorem getBuffer_contents (sep : Obj) (b : Seq) (h : getBuffer sep = .ok b) : objContents sep = b := by
  unfold getBuffer at h
  unfold objContents
  cases hb : sep.buffer? with
  | none => simp [hb] at h
  | some x => simp [hb] at h; simp [h]

theorem partitionObj_proven : PartitionObj := by
  refine ⟨?_, ?_⟩
  · intro s sep b hb
    have hc := getBuffer_contents sep b hb
    constructor
    · simp only [bytesPartitionObj, hb, bytesPartition, stringlibPartition]
      by_cases h0 : b.length = 0
      · simp [h0, Except.map]
      · simp only [h0, ite_false]
        by_cases hp : fastsearch s b (-1) .search < 0
        · simp [hp, Except.map, objContents, Obj.buffer?]
        · simp [hp, Except.map, hc]
    · simp only [bytesRPartitionObj, hb, bytesRPartition, stringlibRPartition]
      by_cases h0 : b.length = 0
      · simp [h0, Except.map]
      · simp only [h0, ite_false]
        by_cases hp : fastsearch s b (-1) .rsearch < 0
        · simp [hp, Except.map, objContents, Obj.buffer?]
        · simp [hp, Except.map, hc]
  · intro s sep b hb hne
    have h0 : ¬ b.length = 0 := by intro h; exact hne (List.eq_nil_of_length_eq_zero h)
    constructor
    · simp only [bytesPartitionObj, hb, h0, ite_false]
      by_cases hp : fastsearch s b (-1) .search < 0 <;> simp [hp, Except.map]
    · simp only [bytesRPartitionObj, hb, h0, ite_false]
      by_cases hp : fastsearch s b (-1) .rsearch < 0 <;> simp [hp, Except.map]

end PyLean.BytesObj.Bytes
