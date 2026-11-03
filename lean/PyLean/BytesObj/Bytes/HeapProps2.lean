import PyLean.BytesObj.Bytes.Heap2
import PyLean.BytesObj.Bytes.HeapProps
import PyLean.StrSearch.Strip
import PyLean.BytesObj.Bytes.ByteArrayProps4

/-!
Properties of the delegating methods, `center`/`ljust`/`rjust` with `fillchar`, `replace` with
`count` and `splitlines` with `keepends` (Objects/bytearrayobject.c, CPython 3.15.2).
-/

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

/-! ## The delegating methods -/

theorem baPredE_app (p : Seq → Bool) (h : H) : baPredE p h = (.ok (p h.ba.seq), h) := rfl

theorem baMapE_small (f : Seq → Seq) (h : H) (hs : h.ba.data.length < 2 ^ 46) :
    baMapE f h = (.ok (f h.ba.seq), h) := by
  obtain ⟨r, hr⟩ := fromSize_small h.ba hs
  simp [baMapE, E.bind_app, curSeq, hr]

theorem baMapE_huge (f : Seq → Seq) (h : H) (h1 : (h.ba.data.length : Int) ≤ baSizeMax)
    (h2 : (h.ba.data.length : Int) + 33 ≥ 2 ^ 47) :
    baMapE f h = (.error memoryError, h) := by
  have hl : h.ba.seq.length = h.ba.data.length := by simp [BA.seq]
  have hm := allocFailureSilent_proven.2.2.1 none h.ba.seq.length (by rw [hl]; exact h1) (by rw [hl]; exact h2)
  simp [baMapE, E.bind_app, curSeq, hm]

/-- `Py_ISALNUM` etc. as byte ranges, Python/pyctype.c. -/
theorem alnum_ranges (c : Nat) : isAlnumC c = decide ((48 ≤ c ∧ c ≤ 57) ∨ (65 ≤ c ∧ c ≤ 90) ∨ (97 ≤ c ∧ c ≤ 122)) := by
  simp only [isAlnumC, isAlphaC, isUpperC, isLowerC, isDigitC]
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  constructor <;> intro hc <;> omega

theorem alpha_ranges (c : Nat) : isAlphaC c = decide ((65 ≤ c ∧ c ≤ 90) ∨ (97 ≤ c ∧ c ≤ 122)) := by
  simp only [isAlphaC, isUpperC, isLowerC]
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, decide_eq_true_eq]

theorem space_ranges (c : Nat) : isSpaceC c = decide (c = 9 ∨ c = 10 ∨ c = 11 ∨ c = 12 ∨ c = 13 ∨ c = 32) := by
  simp only [isSpaceC, byteSpace]
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq]
  constructor <;> intro hc <;> omega

/-- `bytearray.isalnum()`, :2098-2106: true exactly for a non-empty object of ASCII letters and
digits (`[0-9A-Za-z]`), and the object is not changed. For every heap. -/
def BaIsalnumSpec : Prop :=
  ∀ h : H, baIsalnumE h =
    (.ok (decide (h.ba.seq ≠ []) &&
      h.ba.seq.all (fun c => decide ((48 ≤ c ∧ c ≤ 57) ∨ (65 ≤ c ∧ c ≤ 90) ∨ (97 ≤ c ∧ c ≤ 122)))), h)

theorem baIsalnumSpec_proven : BaIsalnumSpec := by
  intro h
  simp only [baIsalnumE, baPredE_app, bytesIsAlnum, classShortcut_proven isAlnumC h.ba.seq, ← alnum_ranges]

/-- `bytearray.isalpha()`, :2108-2116: true exactly for a non-empty object of ASCII letters. -/
def BaIsalphaSpec : Prop :=
  ∀ h : H, baIsalphaE h =
    (.ok (decide (h.ba.seq ≠ []) && h.ba.seq.all (fun c => decide ((65 ≤ c ∧ c ≤ 90) ∨ (97 ≤ c ∧ c ≤ 122)))), h)

theorem baIsalphaSpec_proven : BaIsalphaSpec := by
  intro h
  simp only [baIsalphaE, baPredE_app, bytesIsAlpha, classShortcut_proven isAlphaC h.ba.seq, ← alpha_ranges]

/-- `bytearray.isdigit()`, :2128-2136: true exactly for a non-empty object of ASCII digits. -/
def BaIsdigitSpec : Prop :=
  ∀ h : H, baIsdigitE h =
    (.ok (decide (h.ba.seq ≠ []) && h.ba.seq.all (fun c => decide (48 ≤ c ∧ c ≤ 57))), h)

theorem baIsdigitSpec_proven : BaIsdigitSpec := by
  intro h
  simp only [baIsdigitE, baPredE_app, bytesIsDigit, classShortcut_proven isDigitC h.ba.seq]
  rfl

/-- `bytearray.isspace()`, :2148-2156: true exactly for a non-empty object of the six ASCII
whitespace bytes `\t\n\v\f\r` and space. -/
def BaIsspaceSpec : Prop :=
  ∀ h : H, baIsspaceE h =
    (.ok (decide (h.ba.seq ≠ []) &&
      h.ba.seq.all (fun c => decide (c = 9 ∨ c = 10 ∨ c = 11 ∨ c = 12 ∨ c = 13 ∨ c = 32))), h)

theorem baIsspaceSpec_proven : BaIsspaceSpec := by
  intro h
  simp only [baIsspaceE, baPredE_app, bytesIsSpace, classShortcut_proven isSpaceC h.ba.seq, ← space_ranges]

/-- `bytearray.isascii()`, :2118-2126: true exactly when every byte is below 128, the empty object
included. Hypothesis: the type invariant that every byte is below 256. -/
def BaIsasciiSpec : Prop :=
  ∀ h : H, (∀ c ∈ h.ba.seq, c < 256) → baIsasciiE h = (.ok (h.ba.seq.all (· < 128)), h)

theorem baIsasciiSpec_proven : BaIsasciiSpec := by
  intro h hs
  simp only [baIsasciiE, baPredE_app, isAsciiSpec_proven _ hs]

/-- `bytearray.islower()`, :2138-2146: no ASCII capital and at least one ASCII small letter. -/
def BaIslowerSpec : Prop :=
  ∀ h : H, baIslowerE h =
    (.ok (h.ba.seq.all (fun c => !decide (65 ≤ c ∧ c ≤ 90)) && h.ba.seq.any (fun c => decide (97 ≤ c ∧ c ≤ 122))), h)

theorem baIslowerSpec_proven : BaIslowerSpec := by
  intro h
  simp only [baIslowerE, baPredE_app, (casedSpec_proven _).1, isUpperC]
  rfl

/-- `bytearray.isupper()`, :2168-2176: no ASCII small letter and at least one ASCII capital. -/
def BaIsupperSpec : Prop :=
  ∀ h : H, baIsupperE h =
    (.ok (h.ba.seq.all (fun c => !decide (97 ≤ c ∧ c ≤ 122)) && h.ba.seq.any (fun c => decide (65 ≤ c ∧ c ≤ 90))), h)

theorem baIsupperSpec_proven : BaIsupperSpec := by
  intro h
  simp only [baIsupperE, baPredE_app, (casedSpec_proven _).2, isLowerC]
  rfl

/-- A cased byte: an ASCII letter. -/
def casedB (c : Nat) : Bool := isUpperC c || isLowerC c

/-- Each byte with whether the byte before it is cased (`false` for the first). -/
def withPrev (prev : Bool) (s : Seq) : List (Nat × Bool) := s.zip (prev :: s.map casedB)

/-- The titlecase condition at one position: a capital follows no cased byte, a small letter follows
a cased byte. -/
def titleOk (x : Nat × Bool) : Bool := (!isUpperC x.1 || !x.2) && (!isLowerC x.1 || x.2)

theorem titleLoop_closed (cased prev : Bool) (s : Seq) :
    titleLoop cased prev s = ((cased || s.any casedB) && (withPrev prev s).all titleOk) := by
  induction s generalizing cased prev with
  | nil => simp [titleLoop, withPrev]
  | cons c rest ih =>
    simp only [titleLoop, withPrev, List.map_cons, List.zip_cons_cons, List.all_cons, List.any_cons]
    have hw : ∀ p, (rest.zip (p :: rest.map casedB)) = withPrev p rest := fun _ => rfl
    cases hu : isUpperC c
    · cases hl : isLowerC c
      · have hc : casedB c = false := by simp [casedB, hu, hl]
        simp only [Bool.false_eq_true, ↓reduceIte, ih, hc, hw, titleOk, hu, hl]
        cases cased <;> cases prev <;> simp
      · have hc : casedB c = true := by simp [casedB, hl]
        simp only [Bool.false_eq_true, ↓reduceIte, hl, hc, hw, titleOk, hu]
        cases prev <;> simp [ih]
    · have hl : isLowerC c = false := up_low_disjoint c hu
      have hc : casedB c = true := by simp [casedB, hu]
      simp only [↓reduceIte, hc, hw, titleOk, hu, hl]
      cases prev <;> simp [ih]

/-- `bytearray.istitle()`, :2158-2166: at least one ASCII letter, every capital follows a byte that
is not a letter and every small letter follows a letter; the one-byte shortcut of
`_Py_bytes_istitle` agrees. For every heap. -/
def BaIstitleSpec : Prop :=
  ∀ h : H, baIstitleE h = (.ok (h.ba.seq.any casedB && (withPrev false h.ba.seq).all titleOk), h)

theorem baIstitleSpec_proven : BaIstitleSpec := by
  intro h
  simp only [baIstitleE, baPredE_app]
  congr 2
  unfold bytesIsTitle
  generalize h.ba.seq = s
  cases s with
  | nil => simp [withPrev]
  | cons c rest =>
    cases rest with
    | nil =>
      simp only [List.length_cons, List.length_nil, ↓reduceIte, List.headD_cons, List.any_cons, List.any_nil,
        Bool.or_false, withPrev, List.map_cons, List.map_nil, List.zip_cons_cons, List.zip_nil_right, List.all_cons,
        List.all_nil, Bool.and_true, titleOk, casedB, Bool.not_false, Bool.or_true, Bool.true_and]
      cases hu : isUpperC c
      · cases hl : isLowerC c <;> simp
      · simp [up_low_disjoint c hu]
    | cons d more =>
      have h1 : ¬ ((c :: d :: more).length = 1) := by simp
      have h2 : ¬ ((c :: d :: more).length = 0) := by simp
      simp only [h1, h2, ↓reduceIte, titleLoop_closed, Bool.false_or]

/-- What `_Py_bytes_title` writes at one position: a small letter after a non-letter becomes a
capital, a capital after a letter becomes small, every other byte stays. -/
def titleAt (x : Nat × Bool) : Nat :=
  if isLowerC x.1 && !x.2 then toUpperC x.1 else if isUpperC x.1 && x.2 then toLowerC x.1 else x.1

theorem titleMap_closed (prev : Bool) (s : Seq) : titleMap prev s = (withPrev prev s).map titleAt := by
  induction s generalizing prev with
  | nil => simp [titleMap, withPrev]
  | cons c rest ih =>
    simp only [titleMap, withPrev, List.map_cons, List.zip_cons_cons]
    have hw : ∀ p, (rest.zip (p :: rest.map casedB)) = withPrev p rest := fun _ => rfl
    cases hl : isLowerC c
    · cases hu : isUpperC c
      · have hc : casedB c = false := by simp [casedB, hu, hl]
        simp [titleAt, hl, hu, hc, hw, ih]
      · have hc : casedB c = true := by simp [casedB, hu]
        cases prev <;> simp [titleAt, hl, hu, hc, hw, ih]
    · have hu : isUpperC c = false := low_up_disjoint c hl
      have hc : casedB c = true := by simp [casedB, hl]
      cases prev <;> simp [titleAt, hl, hu, hc, hw, ih]

/-- `bytearray.lower()`, :2515-2523: a new bytearray in which each ASCII capital (65-90) is the small
letter 32 above it and every other byte is unchanged; the object is not changed. Below 2^46 bytes;
from `PyByteArray_SIZE_MAX` down to 2^47 - 33 bytes the allocation raises `MemoryError`. -/
def BaLowerSpec : Prop :=
  ∀ h : H,
    (h.ba.data.length < 2 ^ 46 →
      baLowerE h = (.ok (h.ba.seq.map (fun c => if 65 ≤ c ∧ c ≤ 90 then c + 32 else c)), h)) ∧
    ((h.ba.data.length : Int) ≤ baSizeMax → (h.ba.data.length : Int) + 33 ≥ 2 ^ 47 →
      baLowerE h = (.error memoryError, h))

theorem baLowerSpec_proven : BaLowerSpec := fun h =>
  ⟨fun hs => by rw [baLowerE, baMapE_small _ h hs]; rfl, fun h1 h2 => baMapE_huge _ h h1 h2⟩

/-- `bytearray.upper()`, :2505-2513: each ASCII small letter (97-122) becomes the capital 32 below
it. The same size conditions. -/
def BaUpperSpec : Prop :=
  ∀ h : H,
    (h.ba.data.length < 2 ^ 46 →
      baUpperE h = (.ok (h.ba.seq.map (fun c => if 97 ≤ c ∧ c ≤ 122 then c - 32 else c)), h)) ∧
    ((h.ba.data.length : Int) ≤ baSizeMax → (h.ba.data.length : Int) + 33 ≥ 2 ^ 47 →
      baUpperE h = (.error memoryError, h))

theorem baUpperSpec_proven : BaUpperSpec := fun h =>
  ⟨fun hs => by rw [baUpperE, baMapE_small _ h hs]; rfl, fun h1 h2 => baMapE_huge _ h h1 h2⟩

/-- `bytearray.swapcase()`, :2485-2493: small letters become capitals and capitals small letters. -/
def BaSwapcaseSpec : Prop :=
  ∀ h : H,
    (h.ba.data.length < 2 ^ 46 →
      baSwapcaseE h = (.ok (h.ba.seq.map (fun c =>
        if 97 ≤ c ∧ c ≤ 122 then c - 32 else if 65 ≤ c ∧ c ≤ 90 then c + 32 else c)), h)) ∧
    ((h.ba.data.length : Int) ≤ baSizeMax → (h.ba.data.length : Int) + 33 ≥ 2 ^ 47 →
      baSwapcaseE h = (.error memoryError, h))

theorem baSwapcaseSpec_proven : BaSwapcaseSpec := fun h =>
  ⟨fun hs => by
    rw [baSwapcaseE, baMapE_small _ h hs]
    simp only [bytesSwapcase]
    congr 3
    funext c
    simp only [swapC, isLowerC, isUpperC, toUpperC, toLowerC]
    by_cases h1 : 97 ≤ c ∧ c ≤ 122 <;> by_cases h2 : 65 ≤ c ∧ c ≤ 90 <;> simp [h1, h2],
   fun h1 h2 => baMapE_huge _ h h1 h2⟩

/-- `bytearray.capitalize()`, :2203-2211: the first byte as `upper()` gives it, the rest as
`lower()` gives them. -/
def BaCapitalizeSpec : Prop :=
  ∀ h : H,
    (h.ba.data.length < 2 ^ 46 →
      baCapitalizeE h = (.ok (match h.ba.seq with
        | [] => []
        | c :: rest => (if 97 ≤ c ∧ c ≤ 122 then c - 32 else c) ::
            rest.map (fun c => if 65 ≤ c ∧ c ≤ 90 then c + 32 else c)), h)) ∧
    ((h.ba.data.length : Int) ≤ baSizeMax → (h.ba.data.length : Int) + 33 ≥ 2 ^ 47 →
      baCapitalizeE h = (.error memoryError, h))

theorem baCapitalizeSpec_proven : BaCapitalizeSpec := fun h =>
  ⟨fun hs => by
    rw [baCapitalizeE, baMapE_small _ h hs]
    cases h.ba.seq <;> rfl,
   fun h1 h2 => baMapE_huge _ h h1 h2⟩

/-- `bytearray.title()`, :2495-2503: a small letter after a non-letter becomes a capital and a
capital after a letter becomes small; every other byte stays (`titleAt`). -/
def BaTitleSpec : Prop :=
  ∀ h : H,
    (h.ba.data.length < 2 ^ 46 → baTitleE h = (.ok ((withPrev false h.ba.seq).map titleAt), h)) ∧
    ((h.ba.data.length : Int) ≤ baSizeMax → (h.ba.data.length : Int) + 33 ≥ 2 ^ 47 →
      baTitleE h = (.error memoryError, h))

theorem baTitleSpec_proven : BaTitleSpec := fun h =>
  ⟨fun hs => by rw [baTitleE, baMapE_small _ h hs, bytesTitle, titleMap_closed], fun h1 h2 => baMapE_huge _ h h1 h2⟩


/-! ## `center`, `ljust`, `rjust` with `fillchar` -/

def fillMsg (k : PadKind) (kind : String) (n : Nat) : PyExc :=
  .typeError s!"{k.fname}(): argument 2 must be a byte string of length 1, not a {kind} object of length {n}"

/-- `center`, `ljust` and `rjust` of `bytearray`: `width` is converted first and its `__index__` may
change the object; then `fillchar` must be a `bytes` (a subclass too, by its stored size, which does
not call its `__len__`) or a `bytearray` of length 1, else `TypeError` with the message of the
clinic: a byte string of another length names its type and length, `self` is measured after
`width`'s `__index__`, and any other object (a `memoryview` and `None` included) names its type.
Then the result is the `bytes` method (`bytesCenter`, `bytesLjust`, `bytesRjust`) on the contents
as `width`'s `__index__` left them, with a space for no `fillchar`. An exception of `width` comes
before any check of `fillchar`. For every heap and every callback, with a width in `Py_ssize_t`. -/
def BaJustSpec : Prop :=
  ∀ (h : H) (k : PadKind) (acts : List Act), k ≠ .zfill →
    let h' := runActs h acts
    (∀ (e : PyExc) (fill : Option Arg), baJustE k (.idx acts (.error e)) fill h = (.error e, h')) ∧
    ∀ w : Int, ssizeMin ≤ w → w ≤ ssizeMax →
      baJustE k (.idx acts (.ok w)) none h = (padOp k h'.ba.seq w 32, h') ∧
      (∀ c : Nat, baJustE k (.idx acts (.ok w)) (some (.obj (.bytes [c]))) h = (padOp k h'.ba.seq w c, h')) ∧
      (∀ c : Nat, baJustE k (.idx acts (.ok w)) (some (.obj (.bytearray [c]))) h = (padOp k h'.ba.seq w c, h')) ∧
      (∀ s : Seq, s.length ≠ 1 →
        baJustE k (.idx acts (.ok w)) (some (.obj (.bytes s))) h = (.error (fillMsg k "bytes" s.length), h')) ∧
      (∀ s : Seq, s.length ≠ 1 →
        baJustE k (.idx acts (.ok w)) (some (.obj (.bytearray s))) h = (.error (fillMsg k "bytearray" s.length), h')) ∧
      (∀ (la : List Act) (lr : Py Int) (s : Seq),
        baJustE k (.idx acts (.ok w)) (some (.slen la lr s)) h = baJustE k (.idx acts (.ok w)) (some (.obj (.bytes s))) h) ∧
      baJustE k (.idx acts (.ok w)) (some .me) h =
        (if h'.ba.seq.length = 1 then padOp k h'.ba.seq w (h'.ba.seq.headD 0)
         else .error (fillMsg k "bytearray" h'.ba.seq.length), h') ∧
      baJustE k (.idx acts (.ok w)) (some (.obj .none)) h =
        (.error (.typeError s!"{k.fname}() argument 2 must be a byte string of length 1, not None"), h') ∧
      (∀ o : Obj, (∀ s, o ≠ .bytes s) → (∀ s, o ≠ .bytearray s) → o ≠ .none →
        baJustE k (.idx acts (.ok w)) (some (.obj o)) h =
          (.error (.typeError s!"{k.fname}() argument 2 must be a byte string of length 1, not {o.typeName}"), h'))

theorem baJustSpec_proven : BaJustSpec := by
  intro h k acts _
  dsimp only
  refine ⟨?_, ?_⟩
  · intro e fill
    simp [baJustE, E.bind_app, clinicSsizeE, indexE, runCb_app]
  intro w h1 h2
  have hc := clinic_idx acts w ⟨h1, h2⟩ h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [baJustE, E.bind_app, hc, fillCharE, curSeq]
  · intro c; simp [baJustE, E.bind_app, hc, fillCharE, curSeq]
  · intro c; simp [baJustE, E.bind_app, hc, fillCharE, curSeq]
  · intro s hs; simp [baJustE, E.bind_app, hc, fillCharE, hs, fillMsg]
  · intro s hs; simp [baJustE, E.bind_app, hc, fillCharE, hs, fillMsg]
  · intro la lr s; simp [baJustE, E.bind_app, hc, fillCharE]
  · by_cases hs : (runActs h acts).ba.seq.length = 1
    · simp [baJustE, E.bind_app, hc, fillCharE, curSeq, hs]
    · simp [baJustE, E.bind_app, hc, fillCharE, curSeq, hs, fillMsg]
  · simp [baJustE, E.bind_app, hc, fillCharE]
  · intro o hb hba hn
    cases o <;> simp_all [baJustE, E.bind_app, hc, fillCharE, Arg.typeName]

/-! ## `replace` with `count` -/

/-- `bytearray.replace(old, new, count)`: the clinic takes the buffer of `old`, then of `new`, then
converts `count` (its `__index__` runs, and may change the object, after both `__buffer__`s), and
only then `bytearray_replace_impl`, :1842-1850, reads the object; both `__release_buffer__`s run
after the result is made, and also when `count` raises. For every heap and every callback, with a
count in `Py_ssize_t`; the result is `bytes.replace` of the contents as the three callbacks left
them. Scope: a Python `__buffer__` returns `memoryview(bytes(...))`. -/
def BaReplaceSpec : Prop :=
  ∀ (h : H) (a1 r1 a2 r2 a3 : List Act) (o n : Seq),
    let h3 := runActs (runActs (runActs h a1) a2) a3
    (∀ c : Int, ssizeMin ≤ c → c ≤ ssizeMax →
      baReplaceE (.buf a1 (.ok o) r1) (.buf a2 (.ok n) r2) (some (.idx a3 (.ok c))) h =
        (bytesReplace h3.ba.seq o n c, runActs (runActs h3 r1) r2)) ∧
    (∀ e : PyExc,
      baReplaceE (.buf a1 (.ok o) r1) (.buf a2 (.ok n) r2) (some (.idx a3 (.error e))) h =
        (.error e, runActs (runActs h3 r1) r2)) ∧
    (∀ c : Int, ssizeMin ≤ c → c ≤ ssizeMax →
      baReplaceE (.obj (.bytes o)) (.obj (.bytes n)) (some (.obj (.int c))) h = (bytesReplace h.ba.seq o n c, h))

theorem baReplaceSpec_proven : BaReplaceSpec := by
  intro h a1 r1 a2 r2 a3 o n
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro c h1 h2
    simp [baReplaceE, E.bind_app, E.attempt_app, getBuf_buf, clinic_idx a3 c ⟨h1, h2⟩, curSeq, Buf.read,
      runCb_app]
  · intro e
    simp [baReplaceE, E.bind_app, E.attempt_app, getBuf_buf, clinicSsizeE, indexE, runCb_app]
  · intro c h1 h2
    simp [baReplaceE, E.bind_app, E.attempt_app, getBuf_obj (.bytes o) o rfl, getBuf_obj (.bytes n) n rfl,
      clinic_int c ⟨h1, h2⟩, curSeq, Buf.read, noRel]

/-! ## `splitlines` with `keepends` -/

/-- `bytearray.splitlines(keepends)`: `keepends` goes through `PyObject_IsTrue` before the body reads
the object, so a `__bool__` that changes the object is seen, and one that raises is the result;
`self` as `keepends` is true when it is not empty. The result is `bytes.splitlines` of the contents
then, and with `keepends` true the lines join back to the contents. For every heap and callback. -/
def BaSplitlinesSpec : Prop :=
  ∀ h : H,
    baSplitlinesTE none h = (.ok (bytesSplitlines h.ba.seq false), h) ∧
    (∀ b : Bool, baSplitlinesTE (some (.obj b)) h = (.ok (bytesSplitlines h.ba.seq b), h)) ∧
    (∀ (acts : List Act) (b : Bool),
      baSplitlinesTE (some (.cls acts (.ok b))) h = (.ok (bytesSplitlines (runActs h acts).ba.seq b), runActs h acts)) ∧
    (∀ (acts : List Act) (e : PyExc), baSplitlinesTE (some (.cls acts (.error e))) h = (.error e, runActs h acts)) ∧
    baSplitlinesTE (some .me) h = (.ok (bytesSplitlines h.ba.seq (decide (h.ba.seq ≠ []))), h) ∧
    (∀ acts : List Act, ∃ ls, baSplitlinesTE (some (.cls acts (.ok true))) h = (.ok ls, runActs h acts) ∧
      ls.flatten = (runActs h acts).ba.seq)

theorem baSplitlinesSpec_proven : BaSplitlinesSpec := by
  intro h
  refine ⟨rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl, ?_, ?_⟩
  · have : (h.ba.size = 0) ↔ (h.ba.seq = []) := by
      simp [BA.size, BA.seq]
    simp [baSplitlinesTE, isTrueE, E.bind_app, curSize, curSeq, this]
  · intro acts
    exact ⟨_, rfl, splitlines_flatten _ _⟩


/-! ## `startswith`/`endswith`: the tuple form and a non-buffer argument -/

theorem tailLoop_objs (h1 : H) (st en : Int) (fwd : Bool) (os : List Obj) :
    tailLoopE cRead h1.ptr h1.ba.size st en fwd (os.map Arg.obj) h1 =
      (bytesTailmatchObj.loop h1.ba.seq st en fwd os, h1) := by
  induction os with
  | nil => rfl
  | cons o rest ih =>
    simp only [List.map_cons, tailLoopE, bytesTailmatchObj.loop, tailItem, getBuffer, E.bind_app, tailmatchE]
    cases hb : o.buffer? with
    | none => simp only [getBuf_obj_none o hb]
    | some t =>
      simp only [getBuf_obj o t hb, cRead, readE_app, read_self, Buf.read, E.pure_app, noRel]
      split
      · rfl
      · exact ih

theorem loop_bytes (s : Seq) (st en : Int) (fwd : Bool) (ts : List Seq) :
    bytesTailmatchObj.loop s st en fwd (ts.map Obj.bytes) = .ok (ts.any fun t => bytesTailmatch s t st en fwd) := by
  induction ts with
  | nil => rfl
  | cons t rest ih =>
    simp only [List.map_cons, bytesTailmatchObj.loop, tailItem, getBuffer, Obj.buffer?, List.any_cons]
    split
    · rename_i hm; simp [hm]
    · rename_i hm; simp [hm, ih]

theorem loop_nobuf (s : Seq) (st en : Int) (fwd : Bool) (ts : List Seq) (o : Obj) (rest : List Obj)
    (hb : o.buffer? = none) (hn : (ts.any fun t => bytesTailmatch s t st en fwd) = false) :
    bytesTailmatchObj.loop s st en fwd (ts.map Obj.bytes ++ o :: rest) = .error (notBytesLike o) := by
  induction ts with
  | nil => simp [bytesTailmatchObj.loop, tailItem, getBuffer, hb]
  | cons t more ih =>
    simp only [List.any_cons, Bool.or_eq_false_iff] at hn
    simp only [List.map_cons, List.cons_append, bytesTailmatchObj.loop, tailItem, getBuffer, Obj.buffer?, hn.1,
      Bool.false_eq_true, ↓reduceIte]
    exact ih hn.2

/-- `bytearray.startswith` and `endswith` (:1478-1509, `_Py_bytes_tailmatch`, bytes_methods.c:675-706)
with arguments that run no Python code. A tuple tries its items in order and is `bytes`'s tuple
loop on the contents: true at the first item that matches, false when none does, and the
`TypeError` of the first item that is not bytes-like, unreplaced, when no earlier item matched (items
after a match are not looked at). One object that is not bytes-like gets the method's own message.
For every heap whose views are exports and all bounds. -/
def BaTailmatchSpec : Prop :=
  ∀ (h : H), Inv h → ∀ (fname : String) (st en : Option Int) (fwd : Bool),
    (∀ os : List Obj, baTailmatchE cRead fname (.tuple (os.map .obj)) (bnd st) (bnd en) fwd h =
      (bytesTailmatchObj h.ba.seq fname (.tuple os) (argStart st) (argEnd en) fwd, h)) ∧
    (∀ ts : List Seq,
      baTailmatchE cRead fname (.tuple (ts.map (fun t => .obj (.bytes t)))) (bnd st) (bnd en) fwd h =
        (.ok (ts.any fun t => bytesTailmatch h.ba.seq t (argStart st) (argEnd en) fwd), h)) ∧
    (∀ (ts : List Seq) (o : Obj) (rest : List Obj), o.buffer? = none →
      (ts.any fun t => bytesTailmatch h.ba.seq t (argStart st) (argEnd en) fwd) = false →
      baTailmatchE cRead fname (.tuple ((ts.map (fun t => .obj (.bytes t))) ++ .obj o :: rest.map .obj))
        (bnd st) (bnd en) fwd h = (.error (notBytesLike o), h)) ∧
    (∀ o : Obj, o.buffer? = none →
      baTailmatchE cRead fname (.one (.obj o)) (bnd st) (bnd en) fwd h =
        (.error (.typeError s!"{fname} first arg must be bytes or a tuple of bytes, not {o.typeName}"), h))

theorem tail_tuple (h : H) (hi : Inv h) (fname : String) (st en : Option Int) (fwd : Bool) (os : List Obj) :
    baTailmatchE cRead fname (.tuple (os.map .obj)) (bnd st) (bnd en) fwd h =
      (bytesTailmatchObj h.ba.seq fname (.tuple os) (argStart st) (argEnd en) fwd, h) := by
  unfold baTailmatchE
  simp only [E.bind_app, sliceIndex_bnd]
  apply withBuffer_seq h hi
  intro h1 e1
  subst e1
  simp only [argStart_map, argEnd_map]
  rw [tailLoop_objs]
  simp [bytesTailmatchObj, seq_getBuffer]

theorem baTailmatchSpec_proven : BaTailmatchSpec := by
  intro h hi fname st en fwd
  refine ⟨tail_tuple h hi fname st en fwd, ?_, ?_, ?_⟩
  · intro ts
    have e : ts.map (fun t => Arg.obj (.bytes t)) = (ts.map Obj.bytes).map Arg.obj := by simp
    rw [e, tail_tuple h hi]
    simp only [bytesTailmatchObj, loop_bytes]
  · intro ts o rest hb hn
    have e : ts.map (fun t => Arg.obj (.bytes t)) ++ Arg.obj o :: rest.map Arg.obj =
        (ts.map Obj.bytes ++ o :: rest).map Arg.obj := by simp
    rw [e, tail_tuple h hi]
    simp only [bytesTailmatchObj, loop_nobuf _ _ _ _ ts o rest hb hn]
  · intro o hb
    unfold baTailmatchE
    simp only [E.bind_app, sliceIndex_bnd]
    apply withBuffer_seq h hi
    intro h1 e1
    subst e1
    simp only [E.bind_app, E.attempt_app, tailmatchE, getBuf_obj_none o hb]
    rfl

/-! ## `hex` with a separator -/

/-! ## Comparison -/

/-- `bytearray_richcompare`, :1222-1275, against an object that runs no Python code is the
comparison of `bytes` on the two byte strings (`==` is equality of the contents), and
`NotImplemented` for an object without the buffer protocol; the object is left as it was. For
every heap and operator. -/
def BaRichSpec : Prop :=
  ∀ (h : H) (op : CmpOp),
    (∀ (o : Obj) (t : Seq), o.buffer? = some t →
      baRichE cRead (.obj o) op h = (.ok (some (bytesRichcompare h.ba.seq t op)), h)) ∧
    (∀ (o : Obj) (t : Seq), o.buffer? = some t →
      baRichE cRead (.obj o) .eq h = (.ok (some (decide (h.ba.seq = t))), h)) ∧
    (∀ o : Obj, o.buffer? = none → baRichE cRead (.obj o) op h = (.ok none, h))

theorem baRichSpec_proven : BaRichSpec := by
  intro h op
  have tw : ∀ (o : Obj) (t : Seq) (op : CmpOp), o.buffer? = some t →
      baRichE cRead (.obj o) op h = (.ok (some (bytesRichcompare h.ba.seq t op)), h) := by
    intro o t op hb
    rw [rich_twin]
    have e : baRichcompare (.bytearray h.ba.seq) o op = baRichcompare (.bytes h.ba.seq) (.bytes t) op := by
      unfold baRichcompare; rw [hb]; rfl
    rw [e, (richcompareTwins_proven h.ba.seq t op).1]
  refine ⟨fun o t hb => tw o t op hb, ?_, ?_⟩
  · intro o t hb
    rw [tw o t .eq hb, (richcompareTwins_proven h.ba.seq t .eq).2.1]
  · intro o hb
    rw [rich_twin]
    unfold baRichcompare; rw [hb]; rfl


/-! ## Success conditions: `PyByteArray_FromStringAndSize`, `copy`, `clear` -/

theorem seq_seqData (s : Seq) : (seqData s).map Int.toNat = s := by
  simp [seqData, List.map_map, Function.comp_def]

/-- `PyByteArray_FromStringAndSize(bytes, size)`, :168-206, with `bytearray_reinit_from_bytes`,
:55-67: a negative size is the `SystemError`; any size below 2^46 succeeds with a new object without
exports, `ob_start == ob_bytes`, `ob_alloc` the size of the new `bytes` object (the empty bytes for
0), and the `size` bytes copied from `bytes` (precondition: `bytes` points at `size` bytes), or
`size` bytes nobody wrote for `NULL`. The overflow and memory failures above are those of
`AllocFailureSilent`. -/
def BaFromStringAndSizeSpec : Prop :=
  (∀ (bytes : Option Seq) (size : Int), size < 0 →
    baFromStringAndSize bytes size = .error (systemError "Negative size passed to PyByteArray_FromStringAndSize")) ∧
  (∀ (bytes : Option Seq) (size : Int), 0 ≤ size → size < 2 ^ 46 → (∀ s, bytes = some s → s.length = size.toNat) →
    ∃ r, baFromStringAndSize bytes size = .ok r ∧ r.exports = 0 ∧ r.offset = 0 ∧ r.alloc = size ∧
      r.data = (match bytes with
        | some s => seqData s
        | none => List.replicate size.toNat uninit))

theorem baFromStringAndSizeSpec_proven : BaFromStringAndSizeSpec := by
  refine ⟨?_, ?_⟩
  · intro bytes size h
    simp [baFromStringAndSize, h]
  · intro bytes size h0 h1 hb
    have hn : ¬ size < 0 := by omega
    have hc := bytesSizeCheck_ok size h0 (by omega)
    by_cases hz : size = 0
    · subst hz
      refine ⟨{}, by simp [baFromStringAndSize, hc], rfl, rfl, rfl, ?_⟩
      cases bytes with
      | none => rfl
      | some s =>
        have := hb s rfl
        simp at this
        simp [this, seqData]
    · cases bytes with
      | none =>
        exact ⟨{ data := List.replicate size.toNat uninit, alloc := size },
          by simp only [baFromStringAndSize, hn, ↓reduceIte, hc, hz], rfl, rfl, rfl, rfl⟩
      | some s =>
        have := hb s rfl
        refine ⟨{ data := seqData (s.take size.toNat), alloc := size },
          by simp only [baFromStringAndSize, hn, ↓reduceIte, hc, hz], rfl, rfl, rfl, ?_⟩
        simp only
        rw [← this, List.take_length]

/-- `bytearray.copy()`, :1382-1388: for every object below 2^46 bytes, a new bytearray without
exports holding the contents, the empty object included. -/
def BaCopySpec : Prop :=
  ∀ b : BA, b.data.length < 2 ^ 46 →
    ∃ r, baCopy b = .ok r ∧ r.seq = b.seq ∧ r.exports = 0 ∧ r.offset = 0 ∧ r.alloc = b.size

theorem baCopySpec_proven : BaCopySpec := by
  intro b hs
  have hl : b.seq.length = b.size.toNat := by simp [BA.seq, BA.size]
  obtain ⟨r, hr, h1, h2, h3, h4⟩ := baFromStringAndSizeSpec_proven.2 (some b.seq) b.size (by simp [BA.size])
    (by simp only [BA.size]; exact_mod_cast hs) (fun s e => by cases e; exact hl)
  refine ⟨r, hr, ?_, h1, h2, h3⟩
  simp only at h4
  simp [BA.seq, h4, seq_seqData]

/-- `bytearray.clear()`, :1366-1373 (`PyByteArray_Resize(self, 0)`): an empty object is left alone,
exports or not; a non-empty one with exports raises `BufferError` and is unchanged; otherwise it
becomes the empty object on the empty `bytes` (issue #153419), at offset 0. For every object. -/
def BaClearSpec : Prop :=
  ∀ b : BA,
    (b.size = 0 → baClear b = .ok b) ∧
    (b.size ≠ 0 → 0 < b.exports → baClear b = .error (bufferError "Existing exports of data: object cannot be re-sized")) ∧
    (b.size ≠ 0 → b.exports = 0 → baClear b = .ok { b with data := [], alloc := 0, offset := 0 })

theorem baClearSpec_proven : BaClearSpec := by
  intro b
  refine ⟨?_, ?_, ?_⟩
  · intro hz
    unfold baClear
    have := exportRule_proven.1 b
    rw [hz] at this
    exact this
  · intro hz hx
    exact exportRule_proven.2.1 b 0 (Int.le_refl 0) (Ne.symm hz) hx
  · intro hz hx
    have hd : b.data ≠ [] := by intro e; apply hz; simp [BA.size, e]
    simp [baClear, baResize, Ne.symm hz, canResize, hx, baResizeAlloc, bind, Except.bind, pure, Except.pure,
      resizedData]

/-! ## In-place repeat -/

/-- `bytearray_irepeat_lock_held` (`b *= n`), :471-506: `n = 1` returns the object untouched (also
with exports); a count `≤ 0` is 0 and empties the object, `MemoryError` exactly when
`len(b) > PyByteArray_SIZE_MAX // n`, `BufferError` with exports whenever the size changes, and
otherwise the object holds `n` copies of its old contents. For every object, with the result below
2^46 bytes. -/
def BaIRepeatSpec : Prop :=
  ∀ (b : BA) (n : Int),
    (n = 1 → baIRepeat b n = .ok b) ∧
    (n ≤ 0 → b.size = 0 → baIRepeat b n = .ok b) ∧
    (n ≤ 0 → b.size ≠ 0 → 0 < b.exports →
      baIRepeat b n = .error (bufferError "Existing exports of data: object cannot be re-sized")) ∧
    (n ≤ 0 → b.exports = 0 → ∃ r, baIRepeat b n = .ok r ∧ r.data = []) ∧
    (1 < n → b.size > Int.tdiv baSizeMax n → baIRepeat b n = .error memoryError) ∧
    (1 < n → b.size ≠ 0 → b.size ≤ Int.tdiv baSizeMax n → 0 < b.exports →
      baIRepeat b n = .error (bufferError "Existing exports of data: object cannot be re-sized")) ∧
    (1 < n → b.exports = 0 → b.size * n < 2 ^ 46 →
      ∃ r, baIRepeat b n = .ok r ∧ r.data = seqData (List.replicate n.toNat b.seq).flatten)

theorem tdiv_ok (s n : Int) (hn : 0 < n) (hs0 : 0 ≤ s) (hsz : s * n < 2 ^ 46) : ¬ s > Int.tdiv baSizeMax n := by
  have hmax : baSizeMax = 2 ^ 63 - 1 - 33 := rfl
  rw [Int.tdiv_eq_ediv_of_nonneg (by rw [hmax]; omega)]
  intro hgt
  have h1 : (baSizeMax / n + 1) * n ≤ s * n := Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
  have h2 : baSizeMax < (baSizeMax / n + 1) * n := Int.lt_ediv_add_one_mul_self _ hn
  rw [hmax] at h2 h1; omega

theorem baIRepeatSpec_proven : BaIRepeatSpec := by
  intro b n
  have hs0 : 0 ≤ b.size := by simp [BA.size]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h1; subst h1; exact concatSpec2_proven.2.2.2.1 b
  · intro hn hz
    have hd : b.data = [] := by simpa [BA.size] using hz
    have hc : (if n < 0 then 0 else n) = 0 := by split <;> omega
    unfold baIRepeat
    simp only [hc, bind, Except.bind, pure, Except.pure]
    simp [Int.mul_zero, hz, baResize, bytesRepeatFill, seqData, pure, Except.pure]
    cases b; simp_all
  · intro hn hz hx
    have hc : (if n < 0 then 0 else n) = 0 := by split <;> omega
    unfold baIRepeat
    simp only [hc, bind, Except.bind, pure, Except.pure]
    rw [show b.size * 0 = 0 by simp, exportRule_proven.2.1 b 0 (Int.le_refl 0) (Ne.symm hz) hx]
    simp
  · intro hn hx
    have hc : (if n < 0 then 0 else n) = 0 := by split <;> omega
    obtain ⟨r, hr, _⟩ := exportRule_proven.2.2.2 b 0 (Int.le_refl 0) hx (by decide)
    refine ⟨{ r with data := seqData (bytesRepeatFill 0 b.seq) }, ?_, by simp [bytesRepeatFill, seqData]⟩
    unfold baIRepeat
    simp only [hc, bind, Except.bind, pure, Except.pure]
    simp [hr]
  · intro hn hb
    have hc : (if n < 0 then 0 else n) = n := by split <;> omega
    have h1 : n ≠ 1 := by omega
    unfold baIRepeat
    simp [hc, h1, hb, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, show 0 < n by omega]
  · intro hn hz hb hx
    exact concatSpec2_proven.2.2.2.2.1 b n hn hz hb hx
  · intro hn hx hsz
    have hc : (if n < 0 then 0 else n) = n := by split <;> omega
    have h1 : n ≠ 1 := by omega
    have hd := tdiv_ok b.size n (by omega) hs0 hsz
    have hpos : 0 ≤ b.size * n := Int.mul_nonneg hs0 (by omega)
    obtain ⟨r, hr, _⟩ := exportRule_proven.2.2.2 b (b.size * n) hpos hx hsz
    refine ⟨{ r with data := seqData (bytesRepeatFill (b.size * n).toNat b.seq) }, ?_, ?_⟩
    · unfold baIRepeat
      simp only [hc, h1, ↓reduceIte, bind, Except.bind, pure, Except.pure]
      simp [hd, hr]
    · show seqData _ = seqData _
      by_cases hz : b.seq = []
      · have : b.data = [] := by simpa [BA.seq] using hz
        have hsz0 : b.size = 0 := by simp [BA.size, this]
        simp [hz, hsz0, bytesRepeatFill]
      · have hl : (b.size * n).toNat = n.toNat * b.seq.length := by
          have : b.seq.length = b.data.length := by simp [BA.seq]
          rw [this]; simp only [BA.size]
          rw [Int.toNat_mul (by omega) (by omega)]
          simp [Nat.mul_comm]
        rw [hl, repeatFill_proven b.seq n.toNat hz (by omega)]

/-! ## append, insert, pop: the conversions, then the body, which refuses with exports -/

def exportsMsg : PyExc := bufferError "Existing exports of data: object cannot be re-sized"

theorem getByteValueE_range (a : Arg) (h h' : H) (c : Nat) (hg : getByteValueE a h = (.ok c, h')) : c < 256 := by
  unfold getByteValueE at hg
  simp only [E.bind_app] at hg
  rcases hx : indexE a h with ⟨r, h1⟩
  rw [hx] at hg
  cases r with
  | error e => simp at hg
  | ok v =>
    simp only at hg
    by_cases hv : v < 0 ∨ v ≥ 256
    · simp [hv, E.throw_app] at hg
    · simp only [hv, ↓reduceIte, E.pure_app, Prod.mk.injEq, Except.ok.injEq] at hg
      omega

theorem clinicSsizeE_range (a : Arg) (h h' : H) (i : Int) (hg : clinicSsizeE a h = (.ok i, h')) :
    ssizeMin ≤ i ∧ i ≤ ssizeMax := by
  unfold clinicSsizeE at hg
  simp only [E.bind_app] at hg
  rcases hx : indexE a h with ⟨r, h1⟩
  rw [hx] at hg
  cases r with
  | error e => simp at hg
  | ok v =>
    simp only [E.lift_app, Sequences.asSsize] at hg
    split at hg
    · simp only [Prod.mk.injEq, Except.ok.injEq] at hg
      omega
    · simp at hg

theorem append_exports (b : BA) (c : Nat) (hc : c < 256) (hx : 0 < b.exports) :
    baAppend b (.int c) = .error exportsMsg := by
  have hr := exportRule_proven.2.1 b (b.size + 1) (by simp [BA.size]; omega) (by omega) hx
  simp [baAppend, getByte_ok c hc, bind, Except.bind, hr, exportsMsg]

theorem insert_exports (b : BA) (i : Int) (c : Nat) (hc : c < 256) (hi : ssizeMin ≤ i ∧ i ≤ ssizeMax)
    (hx : 0 < b.exports) : baInsert b i (.int c) = .error exportsMsg := by
  have hr := exportRule_proven.2.1 b (b.size + 1) (by simp [BA.size]; omega) (by omega) hx
  have ha : Sequences.asSsize i = .ok i := by simp [Sequences.asSsize, hi]
  simp [baInsert, ha, getByte_ok c hc, bind, Except.bind, hr, exportsMsg]

/-- `bytearray.append(item)`, :2189-2201: the clinic's `_getbytevalue` of `item` runs first (its
exception is the result, with what its `__index__` did kept); then the body resizes to `n + 1`,
which with exports (a view the callback took, say) raises `BufferError`; otherwise the byte is
appended, as `list.append` does. For every heap, every item, and objects below 2^45 bytes. -/
def BaAppendSpec : Prop :=
  ∀ (h : H) (item : Arg),
    (∀ (e : PyExc) (h' : H), getByteValueE item h = (.error e, h') → baAppendE item h = (.error e, h')) ∧
    (∀ (c : Nat) (h' : H), getByteValueE item h = (.ok c, h') →
      (0 < h'.ba.exports → baAppendE item h = (.error exportsMsg, h')) ∧
      (h'.ba.exports = 0 → h'.ba.size < 2 ^ 45 →
        ∃ r, baAppendE item h = (.ok (), h'.put r) ∧ r.data = Sequences.listAppend h'.ba.data (c : Int)))

theorem baAppendSpec_proven : BaAppendSpec := by
  intro h item
  refine ⟨?_, ?_⟩
  · intro e h' hg
    simp [baAppendE, E.bind_app, hg]
  · intro c h' hg
    have hc := getByteValueE_range item h h' c hg
    refine ⟨?_, ?_⟩
    · intro hx
      simp [baAppendE, E.bind_app, hg, put_ok, append_exports _ c hc hx]
    · intro hx hs
      obtain ⟨r, hr, hd⟩ := mutatorsSpec_proven.1 h'.ba c hc hx hs
      exact ⟨r, by simp [baAppendE, E.bind_app, hg, put_ok, hr], hd⟩

/-- `bytearray.insert(index, item)`, :2074-2096: the clinic converts `index` (`_PyNumber_Index`,
`PyLong_AsSsize_t`) and then `item` (`_getbytevalue`), each exception passing out with the changes
of the callbacks before it; the body then resizes, which with exports raises `BufferError`, and
otherwise inserts as `list.insert` does at the clamped index. For every heap and every pair of
arguments, and objects below 2^45 bytes. -/
def BaInsertSpec : Prop :=
  ∀ (h : H) (index item : Arg),
    (∀ (e : PyExc) (h1 : H), clinicSsizeE index h = (.error e, h1) → baInsertE index item h = (.error e, h1)) ∧
    ∀ (i : Int) (h1 : H), clinicSsizeE index h = (.ok i, h1) →
      (∀ (e : PyExc) (h2 : H), getByteValueE item h1 = (.error e, h2) → baInsertE index item h = (.error e, h2)) ∧
      (∀ (c : Nat) (h2 : H), getByteValueE item h1 = (.ok c, h2) →
        (0 < h2.ba.exports → baInsertE index item h = (.error exportsMsg, h2)) ∧
        (h2.ba.exports = 0 → h2.ba.size < 2 ^ 45 →
          ∃ r, baInsertE index item h = (.ok (), h2.put r) ∧
            Sequences.listInsert h2.ba.data i (c : Int) = .ok r.data))

theorem baInsertSpec_proven : BaInsertSpec := by
  intro h index item
  refine ⟨?_, ?_⟩
  · intro e h1 hi
    simp [baInsertE, E.bind_app, hi]
  · intro i h1 hi
    have hr := clinicSsizeE_range index h h1 i hi
    refine ⟨?_, ?_⟩
    · intro e h2 hg
      simp [baInsertE, E.bind_app, hi, hg]
    · intro c h2 hg
      have hc := getByteValueE_range item h1 h2 c hg
      refine ⟨?_, ?_⟩
      · intro hx
        simp [baInsertE, E.bind_app, hi, hg, put_ok, insert_exports _ i c hc hr hx]
      · intro hx hs
        obtain ⟨r, hr', hd⟩ := mutatorsSpec_proven.2.1 h2.ba i c hc hx hs hr.1 hr.2
        exact ⟨r, by simp [baInsertE, E.bind_app, hi, hg, put_ok, hr'], hd⟩

/-- `bytearray.pop(index)`, :2359-2388. The body: `IndexError('pop from empty bytearray')` on an empty
object, the index counted from the end when negative, `IndexError('pop index out of range')` outside,
then `_canresize`'s `BufferError` with exports, and otherwise the byte at the index, removed. The
clinic converts `index` first (`-1` when absent), and its exception passes out. For every object
and index in `Py_ssize_t`, objects below 2^45 bytes for the success. -/
def BaPopSpec : Prop :=
  (∀ (b : BA) (i : Int), ssizeMin ≤ i → i ≤ ssizeMax →
    let n := b.size
    let j := if i < 0 then i + n else i
    (n = 0 → baPop b (some i) = .error (.indexError "pop from empty bytearray")) ∧
    (n ≠ 0 → (j < 0 ∨ j ≥ n) → baPop b (some i) = .error (.indexError "pop index out of range")) ∧
    (0 ≤ j → j < n → 0 < b.exports → baPop b (some i) = .error exportsMsg) ∧
    (0 ≤ j → j < n → b.exports = 0 → n < 2 ^ 45 →
      ∃ r, baPop b (some i) = .ok (b.data.getD j.toNat 0, r) ∧ r.data = b.data.eraseIdx j.toNat)) ∧
  (∀ (h : H) (a : Arg) (i : Int) (h1 : H), clinicSsizeE a h = (.ok i, h1) →
    baPopE (some a) h = liftBAR (fun b => baPop b (some i)) h1) ∧
  (∀ (h : H) (a : Arg) (e : PyExc) (h1 : H), clinicSsizeE a h = (.error e, h1) →
    baPopE (some a) h = (.error e, h1)) ∧
  (∀ h : H, baPopE none h = liftBAR (fun b => baPop b (some (-1))) h)

theorem baPopSpec_proven : BaPopSpec := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro b i h1 h2
    dsimp only
    have ha : Sequences.popArg (some i) = .ok i := by simp [Sequences.popArg, Sequences.asSsize, h1, h2]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hn
      simp [baPop, ha, hn, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
    · intro hn hj
      simp [baPop, ha, hn, hj, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
    · intro hj1 hj2 hx
      have hn : b.size ≠ 0 := by split at hj1 <;> omega
      have hj : ¬ ((if i < 0 then i + b.size else i) < 0 ∨ (if i < 0 then i + b.size else i) ≥ b.size) := by omega
      simp [baPop, ha, hn, hj, bind, Except.bind, canResize, hx, exportsMsg]
    · intro hj1 hj2 hx hs
      have hn : b.size ≠ 0 := by split at hj1 <;> omega
      have hj : ¬ ((if i < 0 then i + b.size else i) < 0 ∨ (if i < 0 then i + b.size else i) ≥ b.size) := by omega
      obtain ⟨r, hr⟩ := resize_small b (b.size - 1) (by omega) hx (by omega)
      refine ⟨{ r with data := b.data.eraseIdx (if i < 0 then i + b.size else i).toNat }, ?_, rfl⟩
      simp [baPop, ha, hn, hj, bind, Except.bind, canResize, hx, hr, pure, Except.pure]
  · intro h a i h1 hi
    simp [baPopE, E.bind_app, hi]
  · intro h a e h1 hi
    simp [baPopE, E.bind_app, hi]
  · intro h
    rfl

/-! ## The growth strategy of `bytearray_resize_lock_held` -/

theorem storage_small (old new : Int) (h0 : 0 ≤ new) (h1 : new + 33 < 2 ^ 47) : baStorageCheck old new = .ok () := by
  unfold baStorageCheck
  have h2 : ¬ (new > baSizeMax) := by unfold baSizeMax; rw [ssizeMax_val, objsize_val]; omega
  rw [if_neg h2]
  exact bytesResizeCheck_small _ _ h0 h1

/-- `bytearray_resize_lock_held`, :263-343, with `bytearray_reinit_from_bytes`, :55-67, and
`bytearray_resize_storage`, :227-260, on success: a resize to 0 of an object without exports installs
the empty `bytes` (alloc 0, offset 0). Any other new size `n` keeps the first bytes, and the new
`ob_alloc` follows the strategy exactly: inside the buffer and not below half of it, the quick exit
keeps `ob_alloc` and `ob_start`; below half (major downsize) it is `n`; growing to at most 1.125 times
`ob_alloc` (moderate upsize) it is `n + n // 8 + (3 if n < 9 else 6)`; beyond that (major upsize) it is
`n`; and after a reallocation `ob_start == ob_bytes`. An overallocation above `PyByteArray_SIZE_MAX`
is `MemoryError`. On 3.15.2, `bytearray(10).append(1)` leaves `__alloc__()` at 51. For every object
without exports and every size below 2^46. -/
def BaResizeStrategy : Prop :=
  (∀ b : BA, b.size ≠ 0 → b.exports = 0 → baResize b 0 = .ok { b with data := [], alloc := 0, offset := 0 }) ∧
  (∀ (b : BA) (n : Int), 0 < n → n ≠ b.size → b.exports = 0 → n < 2 ^ 46 →
    ∃ r, baResize b n = .ok r ∧ r.data = resizedData b.data n ∧ r.exports = 0 ∧
      (if n + b.offset ≤ b.alloc ∧ ¬ n < b.alloc / 2 then r.alloc = b.alloc ∧ r.offset = b.offset
       else r.offset = 0 ∧ r.alloc = (if n + b.offset ≤ b.alloc then n
          else if 8 * n ≤ 9 * b.alloc then n + n / 8 + (if n < 9 then 3 else 6) else n))) ∧
  (∀ (b : BA) (n : Int), 0 < n → n ≠ b.size → b.exports = 0 → ¬ (n + b.offset ≤ b.alloc) →
    8 * n ≤ 9 * b.alloc → n + n / 8 + (if n < 9 then 3 else 6) > baSizeMax → baResize b n = .error memoryError) ∧
  ((do let b ← baNew (some (.int 10)) none none; let r ← baAppend b (.int 1); pure (baAllocMethod r) : Py Int) = .ok 51)

theorem baResizeStrategy_proven : BaResizeStrategy := by
  refine ⟨?_, ?_, ?_, rfl⟩
  · intro b hz hx
    simp [baResize, Ne.symm hz, canResize, hx, baResizeAlloc, bind, Except.bind, pure, Except.pure, resizedData]
  · intro b n hn hne hx hs
    have h0 : ¬ n < 0 := by omega
    have hz : n ≠ 0 := by omega
    have h8 : 0 ≤ n / 8 := Int.ediv_nonneg (by omega) (by decide)
    have h8' : n / 8 ≤ n := Int.ediv_le_self _ (by omega)
    unfold baResize
    simp only [bind, Except.bind, pure, Except.pure, h0, ↓reduceIte, hne, canResize, hx, Nat.lt_irrefl,
      gt_iff_lt]
    unfold baResizeAlloc baNewAlloc
    simp only [hz, ↓reduceIte]
    by_cases c1 : n + b.offset ≤ b.alloc
    · by_cases c2 : n < b.alloc / 2
      · simp only [c1, c2, ↓reduceIte, storage_small b.alloc n (by omega) (by omega), and_false]
        exact ⟨_, rfl, rfl, by simp [hx], rfl, rfl⟩
      · simp only [c1, c2, ↓reduceIte, not_false_eq_true, and_self]
        exact ⟨_, rfl, rfl, by simp [hx], rfl, rfl⟩
    · by_cases c3 : 8 * n ≤ 9 * b.alloc
      · have hst := storage_small b.alloc (n + n / 8 + if n < 9 then 3 else 6) (by split <;> omega)
          (by split <;> omega)
        simp only [c1, c3, ↓reduceIte, hst, false_and]
        exact ⟨_, rfl, rfl, by simp [hx], rfl, rfl⟩
      · simp only [c1, c3, ↓reduceIte, storage_small b.alloc n (by omega) (by omega), false_and]
        exact ⟨_, rfl, rfl, by simp [hx], rfl, rfl⟩
  · intro b n hn hne hx c1 c3 hbig
    have h0 : ¬ n < 0 := by omega
    have hz : n ≠ 0 := by omega
    simp [baResize, h0, hne, canResize, hx, baResizeAlloc, baNewAlloc, hz, c1, c3, baStorageCheck, hbig,
      bind, Except.bind]

/-! ## `bytearray_setslice_linear` succeeds -/

/-- `bytearray_setslice_linear`, :601-684, for `0 ≤ lo ≤ hi ≤ len`: a splice that keeps the size
writes in place and succeeds even with exports; one that changes the size raises `BufferError` with
exports (`_canresize` for a shrink, the resize for a growth); and without exports every splice below
2^45 bytes succeeds, through each of its three branches, leaving `data[:lo] + bytes + data[hi:]`
and no exports. -/
def BaSetsliceLinearOk : Prop :=
  ∀ (self : BA) (lo hi : Nat) (bytes : List Int), lo ≤ hi → hi ≤ self.data.length →
    (self.data.length : Int) + bytes.length < 2 ^ 45 →
    ((bytes.length : Int) = (hi : Int) - lo → baSetsliceLinear self lo hi bytes = .ok (baCopyIn self lo bytes)) ∧
    ((bytes.length : Int) ≠ (hi : Int) - lo → 0 < self.exports →
      baSetsliceLinear self lo hi bytes = .error exportsMsg) ∧
    (self.exports = 0 → ∃ r, baSetsliceLinear self lo hi bytes = .ok r ∧
      r.data = self.data.take lo ++ bytes ++ self.data.drop hi ∧ r.exports = 0)

theorem resizeNoSize_ne (s : BA) (hx : s.exports = 0) (hs : s.size < 2 ^ 46) (e : PyExc) :
    baResizeNoSize s s.size ≠ .error e := by
  obtain ⟨p, hp⟩ := baResizeAlloc_ok s s.size (by simp [BA.size]) hs
  simp [baResizeNoSize, canResize, hx, hp, bind, Except.bind, pure, Except.pure]

theorem setsliceLinear_ok (self : BA) (lo hi : Nat) (bytes : List Int) (hl : lo ≤ hi) (hh : hi ≤ self.data.length)
    (hs : (self.data.length : Int) + bytes.length < 2 ^ 45) (hx : self.exports = 0) :
    ∃ r, baSetsliceLinear self lo hi bytes = .ok r := by
  have hsize : self.size = (self.data.length : Int) := rfl
  unfold baSetsliceLinear
  simp only
  by_cases hneg : (bytes.length : Int) - ((hi : Int) - lo) < 0
  · rw [if_pos hneg]
    have hc : canResize self = .ok () := by simp [canResize, hx]
    rw [hc]
    simp only
    by_cases h0 : (lo : Int) = 0
    · rw [if_pos h0]
      unfold baShrinkStart
      simp only [bind, Except.bind, pure, Except.pure]
      split
      · rename_i e he
        exact absurd he (resizeNoSize_ne _ (by simpa using hx) (by simp only [BA.size, List.length_drop]; omega) e)
      · exact ⟨_, rfl⟩
    · rw [if_neg h0]
      unfold baShrinkMove setsliceShrinkMove baMove
      have hM : Sequences.memmove self.data ((lo : Int) + bytes.length) hi (self.size - hi) =
          .ok (self.data.take (lo + bytes.length) ++ (self.data.drop hi).take (self.data.length - hi) ++
            self.data.drop (lo + bytes.length + (self.data.length - hi))) := by
        have e1 : (lo : Int) + bytes.length = ((lo + bytes.length : Nat) : Int) := by omega
        have e2 : self.size - hi = ((self.data.length - hi : Nat) : Int) := by rw [hsize]; omega
        rw [e1, e2]
        exact memmove_ok _ _ _ _ (by omega) (by omega)
      simp only [bind, Except.bind, pure, Except.pure, hM]
      obtain ⟨r, hr⟩ := resize_small
        { self with data := self.data.take (lo + bytes.length) ++ (self.data.drop hi).take (self.data.length - hi) ++
            self.data.drop (lo + bytes.length + (self.data.length - hi)) }
        (self.size + ((bytes.length : Int) - ((hi : Int) - lo))) (by rw [hsize]; omega) hx (by rw [hsize]; omega)
      simp only [hr]
      exact ⟨_, rfl⟩
  · rw [if_neg hneg]
    by_cases hpos : (bytes.length : Int) - ((hi : Int) - lo) > 0
    · rw [if_pos hpos]
      unfold baGrow baMove
      have hm : ¬ (self.size > baSizeMax - ((bytes.length : Int) - ((hi : Int) - lo))) := by
        unfold baSizeMax; rw [ssizeMax_val, objsize_val, hsize]; omega
      simp only [bind, Except.bind, pure, Except.pure, hm, ↓reduceIte]
      obtain ⟨r, hr⟩ := resize_small self (self.size + ((bytes.length : Int) - ((hi : Int) - lo)))
        (by rw [hsize]; omega) hx (by rw [hsize]; omega)
      simp only [hr]
      have hlen := resize_len _ _ _ hr
      have hSz : r.size = ((lo + bytes.length + (self.data.length - hi) : Nat) : Int) := by
        simp only [BA.size, hlen, hsize]; omega
      have hM : Sequences.memmove r.data ((lo : Int) + bytes.length) hi (r.size - lo - bytes.length) =
          .ok (r.data.take (lo + bytes.length) ++ (r.data.drop hi).take (self.data.length - hi) ++
            r.data.drop (lo + bytes.length + (self.data.length - hi))) := by
        have e1 : (lo : Int) + bytes.length = ((lo + bytes.length : Nat) : Int) := by omega
        have e2 : r.size - lo - bytes.length = ((self.data.length - hi : Nat) : Int) := by rw [hSz]; omega
        rw [e1, e2]
        have hl2 : r.data.length = lo + bytes.length + (self.data.length - hi) := by
          have : (r.data.length : Int) = lo + bytes.length + (self.data.length - hi) := by rw [hlen, hsize]; omega
          omega
        exact memmove_ok _ _ _ _ (by omega) (by omega)
      simp only [hM]
      exact ⟨_, rfl⟩
    · rw [if_neg hpos]
      exact ⟨_, rfl⟩

theorem baSetsliceLinearOk_proven : BaSetsliceLinearOk := by
  intro self lo hi bytes hl hh hs
  have hsize : self.size = (self.data.length : Int) := rfl
  refine ⟨?_, ?_, ?_⟩
  · intro he
    unfold baSetsliceLinear
    have h1 : ¬ ((bytes.length : Int) - ((hi : Int) - lo) < 0) := by omega
    have h2 : ¬ ((bytes.length : Int) - ((hi : Int) - lo) > 0) := by omega
    simp only [h1, h2, ↓reduceIte]
  · intro he hx
    unfold baSetsliceLinear
    by_cases hneg : (bytes.length : Int) - ((hi : Int) - lo) < 0
    · simp [hneg, canResize, hx, exportsMsg]
    · have hpos : (bytes.length : Int) - ((hi : Int) - lo) > 0 := by omega
      have hm : ¬ (self.size > baSizeMax - ((bytes.length : Int) - ((hi : Int) - lo))) := by
        unfold baSizeMax; rw [ssizeMax_val, objsize_val, hsize]; omega
      have hr := exportRule_proven.2.1 self (self.size + ((bytes.length : Int) - ((hi : Int) - lo)))
        (by rw [hsize]; omega) (by omega) hx
      simp only [hneg, hpos, ↓reduceIte, baGrow, bind, Except.bind, hm, hr, exportsMsg]
  · intro hx
    obtain ⟨r, hr⟩ := setsliceLinear_ok self lo hi bytes hl hh hs hx
    exact ⟨r, hr, setsliceSpec_proven self r lo hi bytes hl hh hr, (setsliceLinear_exports self r lo hi bytes hr).trans hx⟩

/-! ## The slice branches of subscript and assignment -/

/-- A slice part: absent, or an `RIdx` whose `__index__` runs `acts` and returns `v`. -/
def ipArg : Option (List Act × Int) → Option Arg
  | none => none
  | some (a, v) => some (.idx a (.ok v))

def ipVal (p : Option (List Act × Int)) : Option Int := p.map Prod.snd

def ipActs : Option (List Act × Int) → List Act
  | none => []
  | some (a, _) => a

theorem clamp_same (x : Int) : StrSearch.clampSsize x = RangeSlice.clampSsize x := by
  have : ssizeMin ≤ ssizeMax := by decide
  unfold StrSearch.clampSsize RangeSlice.clampSsize
  simp only [Int.max_def, Int.min_def]
  repeat' split
  all_goals omega

theorem slicePart_ip (p : Option (List Act × Int)) (h : H) :
    slicePartE (ipArg p) h = (.ok ((ipVal p).map RangeSlice.clampSsize), runActs h (ipActs p)) := by
  cases p with
  | none => rfl
  | some x =>
    obtain ⟨a, v⟩ := x
    simp [ipArg, ipVal, ipActs, slicePartE, Arg.isNone, Arg.indexCheck, asSsizeE, indexE, runCb_app, E.bind_app,
      Functor.map, E.bind_def, E.pure, clamp_same]

theorem baGetSlice_seq (b : BA) (sl : RangeSlice.Slice) : baGetSlice b sl = baGetSlice (baOf b.seq) sl := by
  have h1 : (baOf b.seq).size = b.size := by rw [baOf_size]; simp [BA.size, BA.seq]
  simp only [baGetSlice, h1, baOf_seq]

/-- The step of a slice part is not zero once clamped. -/
def stepOk (se : Option (List Act × Int)) : Prop := ∀ a v, se = some (a, v) → RangeSlice.clampSsize v ≠ 0

/-- `bytearray_subscript_lock_held` (:530-588) for a slice of `__index__` parts: `PySlice_Unpack` runs
the `__index__` of the step, then of the start, then of the stop (Objects/sliceobject.c:219-262), a
zero step raising `ValueError` before the others run; `PySlice_AdjustIndices` then uses the size as
the callbacks left it, and the result is a new bytearray holding `bytes`'s slice of the contents then
(`bytes_subscript`, which `SubscriptSpec` pins to `range(*s.indices(len))`). For every heap, every
callback and every value. -/
def BaSubscriptSlice : Prop :=
  ∀ (h : H) (st sp se : Option (List Act × Int)),
    (∀ (a : List Act) (v : Int), se = some (a, v) → RangeSlice.clampSsize v = 0 →
      baSubscriptE (.slice (ipArg st) (ipArg sp) (ipArg se)) h =
        (.error (.valueError "slice step cannot be zero"), runActs h a)) ∧
    (stepOk se →
      let h' := runActs (runActs (runActs h (ipActs se)) (ipActs st)) (ipActs sp)
      baSubscriptE (.slice (ipArg st) (ipArg sp) (ipArg se)) h =
        (SubRes.slice <$> bytesGetSlice h'.ba.seq ⟨ipVal st, ipVal sp, ipVal se⟩, h'))

theorem sliceUnpack_ip (st sp se : Option (List Act × Int)) (h : H) (hok : stepOk se) :
    sliceUnpackE (ipArg st) (ipArg sp) (ipArg se) h =
      (RangeSlice.sliceUnpack ⟨ipVal st, ipVal sp, ipVal se⟩,
        runActs (runActs (runActs h (ipActs se)) (ipActs st)) (ipActs sp)) := by
  unfold sliceUnpackE RangeSlice.sliceUnpack
  have hst : ∀ (q : Option (List Act × Int)) (h1 : H), slicePartE (ipArg q) h1 = (.ok ((ipVal q).map RangeSlice.clampSsize), runActs h1 (ipActs q)) :=
    slicePart_ip
  rcases st with _ | ⟨a1, v1⟩ <;> rcases sp with _ | ⟨a2, v2⟩ <;> rcases se with _ | ⟨a3, v3⟩
  all_goals first
    | (have hz := hok _ _ rfl
       simp [E.bind_app, hst, ipVal, ipActs, hz, E.pure_app]; rfl)
    | (simp [E.bind_app, hst, ipVal, ipActs, E.pure_app]; rfl)

theorem baSubscriptSlice_proven : BaSubscriptSlice := by
  intro h st sp se
  refine ⟨?_, ?_⟩
  · intro a v hse hz
    subst hse
    simp [baSubscriptE, sliceUnpackE, E.bind_app, slicePart_ip, ipVal, ipActs, hz, E.throw_app]
  · intro hok
    dsimp only
    rw [(subscriptTwins_proven).1, ← baGetSlice_seq]
    simp only [baSubscriptE, E.bind_app, sliceUnpack_ip _ _ _ h hok]
    unfold baGetSlice
    cases hu : RangeSlice.sliceUnpack ⟨ipVal st, ipVal sp, ipVal se⟩ with
    | error e => rfl
    | ok t =>
      obtain ⟨a, b, c⟩ := t
      simp only [curSize, curSeq, Except.bind, bind, pure, Except.pure]
      split <;> (try split) <;> simp_all [Functor.map, Except.map, E.pure_app, E.pure]

/-- `bytearray_ass_subscript_lock_held` (:781-940) for one key: the key's own `__index__` runs first
(`PyNumber_AsSsize_t` with `IndexError`), then the value's (`_getbytevalue`), and the position is
checked against the size both left; `del b[i]` is the deletion of one byte at the position after the
key's callback; a key that is neither an index nor a slice is the `TypeError`. For every heap, every
callback and every position in `Py_ssize_t`. -/
def BaAssSubIndex : Prop :=
  ∀ (h : H) (ka : List Act) (i : Int), ssizeMin ≤ i → i ≤ ssizeMax →
    (∀ (va : List Act) (v : Int),
      baAssSubE (.one (.idx ka (.ok i))) (some (.idx va (.ok v))) h =
        liftBA (fun b => baAssIndex b i (some (.int v))) (runActs (runActs h ka) va)) ∧
    baAssSubE (.one (.idx ka (.ok i))) none h = liftBA (fun b => baAssIndex b i none) (runActs h ka) ∧
    (∀ (e : PyExc) (value : Option Arg),
      baAssSubE (.one (.idx ka (.error e))) value h = (.error e, runActs h ka)) ∧
    (∀ (o : Obj) (value : Option Arg), o.index? = none →
      baAssSubE (.one (.obj o)) value h =
        (.error (.typeError s!"bytearray indices must be integers or slices, not {o.typeName}"), h))

theorem baAssSubIndex_proven : BaAssSubIndex := by
  intro h ka i h1 h2
  have hs : Sequences.subIndex i = .ok i := by
    simp only [Sequences.subIndex, Sequences.asSsizeExc, h1, h2, and_self, ↓reduceIte]
  have hr : ssizeMin ≤ i ∧ i ≤ ssizeMax := ⟨h1, h2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro va v
    unfold baAssIndex
    by_cases hv : v < 0 ∨ v ≥ 256
    · simp [baAssSubE, Arg.indexCheck, asSsizeE, indexE, runCb_app, hr, Functor.map, E.bind_def,
        getByte_idx, hv, put_ok, hs, getByteValue_int, bind, Except.bind, Except.map]
    · have hm := max_byte v hv
      simp [baAssSubE, Arg.indexCheck, asSsizeE, indexE, runCb_app, hr, Functor.map, E.bind_def,
        getByte_idx, hv, put_ok, hs, getByteValue_int, bind, Except.bind, Except.map, E.pure, curSize, hm,
        Function.comp]
      repeat' split
      all_goals simp_all [E.throw_bind, throw, throwThe, MonadExceptOf.throw, pure, Except.pure, put_ok, E.bind_err]
  · unfold baAssIndex
    simp [baAssSubE, Arg.indexCheck, asSsizeE, indexE, runCb_app, hr, Functor.map, E.bind_def, put_ok, hs, bind,
      Except.bind, Except.map, E.pure, curSize]
    repeat' split
    all_goals simp_all [E.throw_bind, throw, throwThe, MonadExceptOf.throw, pure, Except.pure, put_ok, E.bind_err]
  · intro e value
    simp [baAssSubE, Arg.indexCheck, asSsizeE, indexE, runCb_app, E.bind_app]
  · intro o value hx
    simp [baAssSubE, Arg.indexCheck, hx, E.bind_app, Arg.typeName]

/-! ## Buffer export and release -/

/-- `bytearray_getbuffer_lock_held`/`bytearray_getbuffer` (:69-96) and `bytearray_releasebuffer`
(:98-106): a `NULL` view is the `BufferError` of :74-78; the flags `PyBUF_READ` and `PyBUF_WRITE` are
refused by `PyBuffer_FillInfo` with `SystemError`; any other request exports the contents, writable,
and raises `ob_exports` by one. While the export is held every resize to another size is refused;
releasing it lowers `ob_exports` again, after which every resize does what it did before the export;
and taking and releasing a `memoryview` in Python leaves the heap as it was. For every object. -/
def BaBufferExport : Prop :=
  ∀ (b : BA) (flags : Int),
    baGetBufferC b true flags = .error (bufferError "bytearray_getbuffer: view==NULL argument is obsolete") ∧
    ((flags = 0x100 ∨ flags = 0x200) →
      baGetBufferC b false flags = .error (systemError "Objects/abstract.c:785: bad argument to internal function")) ∧
    (flags ≠ 0x100 → flags ≠ 0x200 →
      baGetBufferC b false flags = .ok ((b.seq, false), { b with exports := b.exports + 1 })) ∧
    baReleaseBuffer (baGetBuffer b) = b ∧
    (∀ n : Int, 0 ≤ n → n ≠ b.size → baResize (baGetBuffer b) n = .error exportsMsg) ∧
    (∀ n : Int, baResize (baReleaseBuffer (baGetBuffer b)) n = baResize b n) ∧
    (∀ h : H, runActs h [.grab, .drop] = h)

theorem baBufferExport_proven : BaBufferExport := by
  intro b flags
  refine ⟨rfl, ?_, ?_, release_get b, ?_, ?_, ?_⟩
  · intro hf
    have : flags ≠ 0 := by omega
    simp [baGetBufferC, this, hf]
  · intro h1 h2
    have : ¬ (flags ≠ 0 ∧ (flags = 0x100 ∨ flags = 0x200)) := by omega
    simp only [baGetBufferC, Bool.false_eq_true, ↓reduceIte, this]
    rfl
  · intro n h0 hn
    exact exportRule_proven.2.1 _ n h0 hn (by simp [baGetBuffer])
  · intro n
    rw [release_get]
  · intro h
    simp [runActs, Act.run, release_get]

/-! ## `__alloc__` and `__sizeof__` -/

/-- `bytearray.__alloc__()` (:2605-2613) reports the size of the `bytes` object, `ob_alloc + 33`, when
there is storage and 0 otherwise; `__sizeof__` (:2813-2823) is the type's basic size plus that, 64 for
`bytearray`. Through the growth strategy: `bytearray()` reports 0, `bytearray(n)` for `n > 0` reports
`n + 33` (an exact allocation from empty storage), and `bytearray(10).append(1)` reports 51. -/
def BaAllocReport : Prop :=
  (∀ b : BA, baAllocMethod b = if b.alloc > 0 then b.alloc + 33 else 0) ∧
  (∀ (basic : Int) (b : BA), baSizeofT basic b = basic + baAllocMethod b) ∧
  (∀ b : BA, baSizeof b = baSizeofT 64 b) ∧
  (baAllocMethod <$> baNew none none none = .ok 0) ∧
  (∀ n : Nat, 0 < n → (n : Int) + 1 < 2 ^ 46 → baAllocMethod <$> baNew (some (.int n)) none none = .ok (n + 33)) ∧
  ((do let b ← baNew (some (.int 10)) none none; let r ← baAppend b (.int 1); pure (baAllocMethod r) : Py Int) = .ok 51)

theorem baAllocReport_proven : BaAllocReport := by
  refine ⟨fun b => rfl, ?_, ?_, rfl, ?_, baResizeStrategy_proven.2.2.2⟩
  · intro basic b
    simp only [baSizeofT, baAllocMethod, objsize_val]
    split <;> omega
  · intro b
    rfl
  · intro n h0 hs
    obtain ⟨r, hr, _, _, hc⟩ := baResizeStrategy_proven.2.1 {} n (by omega) (by simp [BA.size]; omega) rfl (by omega)
    have hz : ¬ ((n : Int) + 0 ≤ 0 ∧ ¬ (n : Int) < 0 / 2) := by omega
    have h1 : ¬ ((n : Int) + 0 ≤ 0) := by omega
    have h2 : ¬ (8 * (n : Int) ≤ 9 * 0) := by omega
    simp only [show ({} : BA).offset = 0 from rfl, show ({} : BA).alloc = 0 from rfl, hz, ↓reduceIte, h1, h2] at hc
    have hr1 : ssizeMin ≤ (n : Int) ∧ (n : Int) ≤ ssizeMax := by
      rw [ssizeMax_val, show ssizeMin = -9223372036854775808 by decide]; omega
    have hn : ¬ ((n : Int) < 0) := by omega
    have hza : ({} : BA).size = 0 := rfl
    have hp' : 0 < n := h0
    have hnew : baNew (some (.int n)) none none = .ok { r with data := List.replicate n 0 } := by
      simp [baNew, baNewObject_eq, baInit, init_fresh, hza, Obj.index?, countOf, hr1, hn, hp', hr]
    rw [hnew]
    simp [Functor.map, Except.map, baAllocMethod, hc.2, objsize_val]
    omega

/-! ## `resize(size)` -/

theorem resizedData_take (d : List Int) (n : Int) (h : (d.length : Int) ≤ n) :
    (resizedData d n).take d.length = d := by
  simp only [resizedData]
  rw [List.take_of_length_le (l := d) (by omega)]
  simp

/-- `bytearray.resize(size)` (:1588-1602, with `bytearray_resize_lock_held`): a negative size is the
`ValueError`; the same size changes nothing (also with exports); another size raises `BufferError`
with exports; otherwise the first bytes are kept and new bytes are zero (the `memset` of :1597-1600,
so nothing unwritten shows). The clinic's conversion runs first and its exception passes out. For
every object and size in `Py_ssize_t`, below 2^46 for the success. -/
def BaResizeMethodSpec : Prop :=
  (∀ (b : BA) (n : Int), ssizeMin ≤ n → n ≤ ssizeMax →
    (n < 0 → baResizeMethod b n = .error (.valueError s!"Can only resize to positive sizes, got {n}")) ∧
    (n = b.size → baResizeMethod b n = .ok b) ∧
    (0 ≤ n → n ≠ b.size → 0 < b.exports → baResizeMethod b n = .error exportsMsg) ∧
    (0 ≤ n → b.exports = 0 → n < 2 ^ 46 → ∃ r, baResizeMethod b n = .ok r ∧
      r.data = b.data.take n.toNat ++ List.replicate (n.toNat - b.data.length) 0)) ∧
  (∀ (h : H) (a : Arg) (n : Int) (h1 : H), clinicSsizeE a h = (.ok n, h1) →
    baResizeMethodE a h = liftBA (fun b => baResizeMethod b n) h1) ∧
  (∀ (h : H) (a : Arg) (e : PyExc) (h1 : H), clinicSsizeE a h = (.error e, h1) →
    baResizeMethodE a h = (.error e, h1))

theorem baResizeMethodSpec_proven : BaResizeMethodSpec := by
  refine ⟨?_, ?_, ?_⟩
  · intro b n h1 h2
    have ha : Sequences.asSsize n = .ok n := by simp [Sequences.asSsize, h1, h2]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hn
      simp [baResizeMethod, ha, baResize, hn, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
    · intro hn
      subst hn
      simp [baResizeMethod, ha, exportRule_proven.1 b, bind, Except.bind, pure, Except.pure]
    · intro h0 hn hx
      simp [baResizeMethod, ha, exportRule_proven.2.1 b n h0 hn hx, bind, Except.bind, exportsMsg]
    · intro h0 hx hs
      by_cases hn : n = b.size
      · subst hn
        refine ⟨b, by simp [baResizeMethod, ha, exportRule_proven.1 b, bind, Except.bind, pure, Except.pure], ?_⟩
        have : b.size.toNat = b.data.length := by simp [BA.size]
        simp [this]
      · obtain ⟨r, hr, hd, _⟩ := exportRule_proven.2.2.2 b n h0 hx hs
        simp only [hn, ↓reduceIte] at hd
        by_cases hg : n > b.size
        · refine ⟨{ r with data := r.data.take b.size.toNat ++ List.replicate (n - b.size).toNat 0 }, ?_, ?_⟩
          · simp [baResizeMethod, ha, hr, bind, Except.bind, pure, Except.pure, hg]
          · have e1 : b.size.toNat = b.data.length := by simp [BA.size]
            have e2 : (n - b.size).toNat = n.toNat - b.data.length := by simp only [BA.size]; omega
            simp only [e1, e2, hd]
            rw [resizedData_take _ _ (by simp [BA.size] at hg; omega)]
            rw [List.take_of_length_le (l := b.data) (by simp [BA.size] at hg; omega)]
        · refine ⟨r, by simp [baResizeMethod, ha, hr, bind, Except.bind, pure, Except.pure, hg], ?_⟩
          rw [hd]
          simp only [resizedData]
          have : n.toNat - b.data.length = 0 := by simp [BA.size] at hg; omega
          simp [this]
  · intro h a n h1 hi
    simp [baResizeMethodE, E.bind_app, hi]
  · intro h a e h1 hi
    simp [baResizeMethodE, E.bind_app, hi]

/-! ## `reverse()` -/

theorem getD_of_lt (l : List Int) (p : Nat) (h : p < l.length) : l.getD p 0 = l[p] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem getD_set (l : List Int) (i j : Nat) (a : Int) (hi : i < l.length) :
    (l.set i a).getD j 0 = if i = j then a else l.getD j 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  split
  · simp [hi]
  · rfl

theorem reverseLoop_length (n : Nat) (d : List Int) (k : Nat) : (reverseLoop n d k).length = d.length := by
  induction k with
  | zero => rfl
  | succ k ih => simp [reverseLoop, swapAt, ih]

theorem reverseLoop_getD (d : List Int) (k : Nat) (hk : k ≤ d.length / 2) (p : Nat) (hp : p < d.length) :
    (reverseLoop d.length d k).getD p 0 =
      if p < k ∨ d.length - 1 - p < k then d.getD (d.length - 1 - p) 0 else d.getD p 0 := by
  induction k generalizing p with
  | zero => simp [reverseLoop]
  | succ k ih =>
    have hl := reverseLoop_length d.length d k
    simp only [reverseLoop, swapAt]
    have hk1 : k < d.length := by omega
    have hk2 : d.length - 1 - k < d.length := by omega
    rw [getD_set _ _ _ _ (by simp [hl]; omega), getD_set _ _ _ _ (by rw [hl]; omega)]
    have ea := ih (by omega) k hk1
    have eb := ih (by omega) (d.length - 1 - k) hk2
    simp only [show ¬ (k < k ∨ d.length - 1 - k < k) by omega, ↓reduceIte] at ea
    simp only [show ¬ (d.length - 1 - k < k ∨ d.length - 1 - (d.length - 1 - k) < k) by omega, ↓reduceIte] at eb
    have em : d.length - 1 - (d.length - 1 - k) = k := by omega
    by_cases h1 : d.length - 1 - k = p
    · subst h1
      simp only [↓reduceIte, ea, em]
      simp [show d.length - 1 - k < k + 1 ∨ k < k + 1 by omega]
    · simp only [h1, ↓reduceIte]
      by_cases h2 : k = p
      · subst h2
        simp only [↓reduceIte, eb]
        simp [show k < k + 1 by omega]
      · simp only [h2, ↓reduceIte]
        rw [ih (by omega) p hp]
        have c : (p < k ∨ d.length - 1 - p < k) ↔ (p < k + 1 ∨ d.length - 1 - p < k + 1) := by omega
        by_cases hc : p < k ∨ d.length - 1 - p < k
        · simp [hc, c.mp hc]
        · have hc' : ¬ (p < k + 1 ∨ d.length - 1 - p < k + 1) := fun x => hc (c.mpr x)
          simp only [hc, hc', ↓reduceIte]

/-- `bytearray.reverse()`, :2033-2050: the swap loop over `head` and `tail` leaves the contents
reversed, for every object, the odd middle byte staying in place; nothing else changes. -/
def BaReverseSpec : Prop :=
  ∀ b : BA, baReverseLoop b = { b with data := b.data.reverse } ∧ baReverseLoop b = baReverse b

theorem baReverseSpec_proven : BaReverseSpec := by
  intro b
  have e : reverseLoop b.data.length b.data (b.data.length / 2) = b.data.reverse := by
    apply List.ext_getElem (by simp [reverseLoop_length])
    intro p h1 h2
    have hp : p < b.data.length := by simpa [reverseLoop_length] using h1
    have := reverseLoop_getD b.data (b.data.length / 2) (Nat.le_refl _) p hp
    rw [getD_of_lt _ _ h1] at this
    rw [this, List.getElem_reverse]
    split
    · rw [getD_of_lt _ _ (by omega)]
    · have : p = b.data.length - 1 - p := by omega
      rw [getD_of_lt _ _ hp]
      congr 1
  exact ⟨by simp [baReverseLoop, e], by simp [baReverseLoop, baReverse, e]⟩

/-! ## The iterator -/

theorem baDrain_from (seq : BA) : ∀ (fuel i : Nat), seq.data.length - i < fuel →
    baDrain seq fuel { index := i } = seq.data.drop i := by
  intro fuel
  induction fuel with
  | zero => intro i h; omega
  | succ k ih =>
    intro i h
    by_cases hi : i < seq.data.length
    · have hn : baIterNext seq { index := i } = (some (seq.data.getD i 0), { index := (i : Int) + 1 }) :=
        baIterSpec_proven.1 seq i hi
      simp only [baDrain, hn]
      have e : ({ index := (i : Int) + 1 } : BAIter) = { index := ((i + 1 : Nat) : Int) } := by simp
      rw [e, ih (i + 1) (by omega)]
      rw [getD_of_lt _ _ hi]
      exact (List.drop_eq_getElem_cons hi).symm
    · have hn := baIterSpec_proven.2.1 seq i (by omega)
      simp only [baDrain, hn]
      rw [List.drop_of_length_le (by omega)]

/-- The iterator of `bytearray` (`bytearray_iter`, :3179-3195, `bytearrayiter_next`, :3042-3074,
`bytearrayiter_length_hint`, :3076-3089, `bytearrayiter_setstate`, :3110-3132): `iter` refuses
anything but a bytearray and starts at 0, so `list(iter(b))` is `list(b)`; on an object that does not
change, the length hint is exactly the number of items still to come, 0 once exhausted;
`__setstate__` takes an `int` only (`TypeError` otherwise, `OverflowError` outside `Py_ssize_t`, no
`__index__`), does nothing to an exhausted iterator, and otherwise sets the index clamped to
`[-1, len]`, so that the iterator then yields `b[k:]`. For every object and state. -/
def BaIterFull : Prop :=
  baIterOf false = .error (systemError "Objects/bytearrayobject.c:3184: bad argument to internal function") ∧
  baIterOf true = .ok { index := 0 } ∧
  (∀ seq : BA, baDrain seq (seq.data.length + 1) { index := 0 } = seq.data) ∧
  (∀ (seq : BA) (i : Nat), baIterLen seq { index := i } = (baDrain seq (seq.data.length + 1) { index := i }).length) ∧
  (∀ (seq : BA) (it : BAIter) (fuel : Nat), it.index < 0 → baIterLen seq it = 0 ∧ baDrain seq fuel it = []) ∧
  (∀ (seq : BA) (it : BAIter) (o : Obj), o.longValue? = none →
    baIterSetstateObj seq it o = .error (.typeError "an integer is required")) ∧
  (∀ (seq : BA) (it : BAIter) (v : Int), (v < ssizeMin ∨ v > ssizeMax) →
    baIterSetstateObj seq it (.int v) = .error (.overflowError "Python int too large to convert to C ssize_t")) ∧
  (∀ (seq : BA) (it : BAIter) (v : Int), ssizeMin ≤ v → v ≤ ssizeMax → it.index < 0 →
    baIterSetstateObj seq it (.int v) = .ok it) ∧
  (∀ (seq : BA) (it : BAIter) (v : Int), ssizeMin ≤ v → v ≤ ssizeMax → 0 ≤ it.index →
    baIterSetstateObj seq it (.int v) = .ok { index := if v < -1 then -1 else if v > seq.size then seq.size else v }) ∧
  (∀ (seq : BA) (k : Nat), k ≤ seq.data.length → (k : Int) ≤ ssizeMax →
    ∃ it, baIterSetstateObj seq {} (.int k) = .ok it ∧ baDrain seq (seq.data.length + 1) it = seq.data.drop k)

theorem baIterFull_proven : BaIterFull := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro seq
    have := baDrain_from seq (seq.data.length + 1) 0 (by omega)
    simpa using this
  · intro seq i
    rw [baDrain_from seq _ i (by omega)]
    simp [baIterLen, BA.size]
    omega
  · intro seq it fuel hi
    refine ⟨by simp [baIterLen, show ¬ (0 ≤ it.index) by omega], ?_⟩
    cases fuel with
    | zero => rfl
    | succ k => simp [baDrain, baIterNext, hi]
  · intro seq it o hl
    simp [baIterSetstateObj, hl]
  · intro seq it v hv
    have : ¬ (ssizeMin ≤ v ∧ v ≤ ssizeMax) := by omega
    simp [baIterSetstateObj, Obj.longValue?, baIterSetstate, Sequences.asSsize, this, bind, Except.bind]
  · intro seq it v h1 h2 hi
    simp [baIterSetstateObj, Obj.longValue?, baIterSetstate, Sequences.asSsize, h1, h2, bind, Except.bind,
      show ¬ (0 ≤ it.index) by omega, pure, Except.pure]
  · intro seq it v h1 h2 hi
    simp [baIterSetstateObj, Obj.longValue?, baIterSetstate, Sequences.asSsize, h1, h2, bind, Except.bind, hi,
      pure, Except.pure]
  · intro seq k hk hm
    have h1 : ssizeMin ≤ (k : Int) := by rw [show ssizeMin = -9223372036854775808 by decide]; omega
    have hs : ¬ ((k : Int) > seq.size) := by simp [BA.size]; omega
    have hn : ¬ ((k : Int) < -1) := by omega
    refine ⟨{ index := k }, ?_, baDrain_from seq _ k (by omega)⟩
    simp [baIterSetstateObj, Obj.longValue?, baIterSetstate, Sequences.asSsize, h1, hm, bind, Except.bind, hs, hn,
      pure, Except.pure]

/-! ## The slice branch of assignment -/

/-- A converted right-hand side as the pure model takes it: `NULL`, or a `bytearray`. -/
def valObj : Option Seq → Option Obj
  | none => none
  | some s => some (.bytearray s)

theorem assSliceCore_ip (st sp se : Option (List Act × Int)) (bytes : Option Seq) (h : H) (hok : stepOk se) :
    assSliceCore (ipArg st) (ipArg sp) (ipArg se) bytes h =
      liftBA (fun b => baAssSlice b ⟨ipVal st, ipVal sp, ipVal se⟩ (valObj bytes))
        (runActs (runActs (runActs h (ipActs se)) (ipActs st)) (ipActs sp)) := by
  unfold assSliceCore
  simp only [E.bind_app, sliceUnpack_ip _ _ _ h hok]
  unfold baAssSlice
  cases hu : RangeSlice.sliceUnpack ⟨ipVal st, ipVal sp, ipVal se⟩ with
  | error e => simp [put_ok, Except.bind, bind]
  | ok t =>
    obtain ⟨a, b, c⟩ := t
    have hv : ∀ x : BA, assValue x (valObj bytes) = .ok bytes := by
      intro x; cases bytes <;> rfl
    simp only [curSize, E.pure_app, Except.bind, bind, hv]
    split <;> rfl

/-- `bytearray_ass_subscript_lock_held` (:828-940) for a slice of `__index__` parts: `del b[s]` and
`b[s] = bytearray(...)` unpack the slice once (step, start, stop) and then splice the contents as the
callbacks left them, as the pure model of the assignment does (whose contents
`SliceAssignAgreesNonempty` and `SliceDeleteAgrees` pin to `list`); any other right-hand side is
looked at after one unpacking: a number or a `str` is the `TypeError`, and a `bytes` is copied with
`PyByteArray_FromObject` and the function called again (:856-862), so every part's `__index__` runs
twice. For every heap, every callback and value, with a non-zero step and a value below 2^46 bytes. -/
def BaAssSubSlice : Prop :=
  ∀ (h : H) (st sp se : Option (List Act × Int)), stepOk se →
    let sl : RangeSlice.Slice := ⟨ipVal st, ipVal sp, ipVal se⟩
    let once := fun (h0 : H) => runActs (runActs (runActs h0 (ipActs se)) (ipActs st)) (ipActs sp)
    baAssSubE (.slice (ipArg st) (ipArg sp) (ipArg se)) none h =
      liftBA (fun b => baAssSlice b sl none) (once h) ∧
    (∀ v : Seq, baAssSubE (.slice (ipArg st) (ipArg sp) (ipArg se)) (some (.obj (.bytearray v))) h =
      liftBA (fun b => baAssSlice b sl (some (.bytearray v))) (once h)) ∧
    (∀ v : Seq, (v.length : Int) + 1 < 2 ^ 46 →
      baAssSubE (.slice (ipArg st) (ipArg sp) (ipArg se)) (some (.obj (.bytes v))) h =
        liftBA (fun b => baAssSlice b sl (some (.bytes v))) (once (once h))) ∧
    (∀ n : Int, baAssSubE (.slice (ipArg st) (ipArg sp) (ipArg se)) (some (.obj (.int n))) h =
      (.error (.typeError "can assign only bytes, buffers, or iterables of ints in range(0, 256)"), once h)) ∧
    (∀ cs : Seq, baAssSubE (.slice (ipArg st) (ipArg sp) (ipArg se)) (some (.obj (.str cs))) h =
      (.error (.typeError "can assign only bytes, buffers, or iterables of ints in range(0, 256)"), once h))

theorem sliceUnpack_ne (st sp se : Option (List Act × Int)) (hok : stepOk se) (e : PyExc) :
    RangeSlice.sliceUnpack ⟨ipVal st, ipVal sp, ipVal se⟩ ≠ .error e := by
  unfold RangeSlice.sliceUnpack
  rcases se with _ | ⟨a, v⟩
  · simp [ipVal, bind, Except.bind, pure, Except.pure]
  · have hz := hok a v rfl
    simp [ipVal, hz, bind, Except.bind, pure, Except.pure]

theorem baAssSubSlice_proven : BaAssSubSlice := by
  intro h st sp se hok
  dsimp only
  have hu := sliceUnpack_ip st sp se
  obtain ⟨t, ht⟩ : ∃ t, RangeSlice.sliceUnpack ⟨ipVal st, ipVal sp, ipVal se⟩ = .ok t := by
    cases hsu : RangeSlice.sliceUnpack ⟨ipVal st, ipVal sp, ipVal se⟩ with
    | error e => exact absurd hsu (sliceUnpack_ne st sp se hok e)
    | ok t => exact ⟨t, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [baAssSubE]
    exact assSliceCore_ip st sp se none h hok
  · intro v
    simp only [baAssSubE]
    exact assSliceCore_ip st sp se (some v) h hok
  · intro v hv
    obtain ⟨r, hr, hd⟩ := initSpec_proven.1 v hv
    have hseq : r.seq = v := by rw [BA.seq, hd]; exact seqData_seq v
    have hsl : ∀ x : BA, baAssSlice x ⟨ipVal st, ipVal sp, ipVal se⟩ (some (.bytes v)) =
        baAssSlice x ⟨ipVal st, ipVal sp, ipVal se⟩ (valObj (some v)) := by
      intro x
      simp only [baAssSlice, valObj, assValue_bytes]
      rfl
    simp only [baAssSubE, E.bind_app, hu _ hok, ht, Arg.numberCheck, Obj.isNumber, Bool.false_or, Bool.false_eq_true,
      ↓reduceIte, fromObjectE, E.lift_app, hr, Functor.map, Except.map, hseq]
    rw [assSliceCore_ip st sp se (some v) _ hok]
    simp only [hsl]
  · intro n
    simp [baAssSubE, E.bind_app, hu _ hok, ht, Arg.numberCheck, Obj.isNumber]
  · intro cs
    simp [baAssSubE, E.bind_app, hu _ hok, ht, Arg.numberCheck, Obj.isNumber]

/-! ## `bytearray_setslice` -/

def clampLo (lo n : Int) : Int := if lo < 0 then 0 else if lo > n then n else lo

def clampHi (lo hi n : Int) : Int :=
  let l := clampLo lo n
  let x := if hi < l then l else hi
  if x > n then n else x

/-- `bytearray_setslice(self, lo, hi, values)`, :686-738, as `extend` and the C API reach it: `NULL`
deletes; `self` is copied first; a value without the buffer protocol is
`TypeError("can't set bytearray slice from <type>")`; a buffer's `__buffer__` runs first and both
bounds are clamped to the size it left (gh-153578), the splice is `bytearray_setslice_linear` on
those bounds, and `__release_buffer__` runs after the splice, whatever it returned. For every heap,
bounds and value. Scope: a Python `__buffer__` returns `memoryview(bytes(...))`. -/
def BaSetsliceSpec : Prop :=
  ∀ (h : H) (lo hi : Int),
    baSetsliceE lo hi none h =
      liftBA (fun b => baSetsliceLinear b (clampLo lo h.ba.size) (clampHi lo hi h.ba.size) []) h ∧
    baSetsliceE lo hi (some .me) h =
      liftBA (fun b => baSetsliceLinear b (clampLo lo h.ba.size) (clampHi lo hi h.ba.size) (seqData h.ba.seq)) h ∧
    (∀ (o : Obj) (t : Seq), o.buffer? = some t → baSetsliceE lo hi (some (.obj o)) h =
      liftBA (fun b => baSetsliceLinear b (clampLo lo h.ba.size) (clampHi lo hi h.ba.size) (seqData t)) h) ∧
    (∀ o : Obj, o.buffer? = none → baSetsliceE lo hi (some (.obj o)) h =
      (.error (.typeError s!"can't set bytearray slice from {o.typeName}"), h)) ∧
    (∀ (acts rel : List Act) (t : Seq),
      let h1 := runActs h acts
      let r := liftBA (fun b => baSetsliceLinear b (clampLo lo h1.ba.size) (clampHi lo hi h1.ba.size) (seqData t)) h1
      baSetsliceE lo hi (some (.buf acts (.ok t) rel)) h = (r.1, runActs r.2 rel)) ∧
    (∀ (acts rel : List Act) (e : PyExc), baSetsliceE lo hi (some (.buf acts (.error e) rel)) h =
      (.error (.typeError "can't set bytearray slice from RBuf"), runActs h acts))

theorem liftBA_split (f : BA → Py BA) (h : H) :
    liftBA f h = ((liftBA f h).1, (liftBA f h).2) := rfl

theorem baSetsliceSpec_proven : BaSetsliceSpec := by
  intro h lo hi
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [baSetsliceE, E.bind_app, E.pure_app, curSize, E.attempt_app, noRel, E.lift_app, clampLo, clampHi]
    rfl
  · simp only [baSetsliceE, E.bind_app, E.pure_app, curSize, curSeq, E.attempt_app, noRel, E.lift_app, clampLo,
      clampHi]
    rfl
  · intro o t hb
    simp only [baSetsliceE, E.bind_app, E.attempt_app, getBuf_obj o t hb, Buf.read, E.pure_app, curSize, noRel,
      E.lift_app, clampLo, clampHi]
    rfl
  · intro o hb
    simp only [baSetsliceE, E.bind_app, E.attempt_app, getBuf_obj_none o hb]
    rfl
  · intro acts rel t
    simp only [baSetsliceE, E.bind_app, E.attempt_app, getBuf_buf, Buf.read, E.pure_app, curSize, E.lift_app,
      runCb_app, clampLo, clampHi]
    rfl
  · intro acts rel e
    have hg : getBufE (.buf acts (.error e) rel) h = (.error e, runActs h acts) := by
      unfold getBufE; rfl
    simp only [baSetsliceE, E.bind_app, E.attempt_app, hg]
    rfl

/-! ## `__init__` -/

theorem put_ba (h : H) (b : BA) : (h.put b).ba = b := rfl

theorem init_reset (h : H) (hx : h.ba.exports = 0) :
    ∃ h0 : H, (∀ k : E Unit, (do canResizeE; resizeE 0; k : E Unit) h = k h0) ∧ h0.ba.data = [] ∧
      h0.ba.exports = 0 := by
  have hc : canResize h.ba = .ok () := by simp [canResize, hx]
  by_cases hz : h.ba.size = 0
  · refine ⟨h, ?_, by simpa [BA.size] using hz, hx⟩
    have hr : baResize h.ba 0 = .ok h.ba := by
      have := exportRule_proven.1 h.ba; rw [hz] at this; exact this
    intro k
    simp [E.bind_app, canResizeE, hc, resizeE, hr, put_self]
  · have hr := baResizeStrategy_proven.1 h.ba hz hx
    refine ⟨h.put { h.ba with data := [], alloc := 0, offset := 0 }, fun k => ?_, rfl, by simp [H.put, hx]⟩
    simp [E.bind_app, canResizeE, hc, resizeE, hr]

theorem initFast_ok : ∀ (vs : List Nat) (i : Nat) (cur : BA) (pre : List Int), (∀ c ∈ vs, c < 256) →
    cur.data = pre ++ List.replicate vs.length uninit → pre.length = i →
    baInitFast.go i cur (vs.map (fun c : Nat => Obj.int (c : Int))) = .inl ({ cur with data := pre ++ seqData vs }, none) := by
  intro vs
  induction vs with
  | nil =>
    intro i cur pre _ hd _
    simp [baInitFast.go, seqData]
    cases cur; simp_all
  | cons c cs ih =>
    intro i cur pre hc hd hi
    have h1 : c < 256 := hc c (by simp)
    have hb : getByteValue (.int c) = .ok c := by
      have h : ¬ ((c : Int) < 0 ∨ (c : Int) ≥ 256) := by omega
      simp [getByteValue, Obj.index?, h]
    simp only [List.map_cons, baInitFast.go, hb]
    have hset : (cur.data.set i (c : Int)) = (pre ++ [(c : Int)]) ++ List.replicate cs.length uninit := by
      rw [hd, ← hi]
      simp [List.replicate_succ, List.set_append_right]
    rw [ih (i + 1) { cur with data := cur.data.set i (c : Int) } (pre ++ [(c : Int)])
      (fun x hx => hc x (by simp [hx])) hset (by simp [hi])]
    simp [seqData]

/-- `bytearray___init___impl`, :982-1182: with exports `__init__` raises `BufferError` and changes
nothing, whatever the argument (`_canresize` comes first); otherwise the object is emptied first and
then: no argument leaves it empty; an `int` `n > 0` gives `n` zero bytes, a negative one
`ValueError('negative count')` (the object stays empty), one outside `Py_ssize_t` the `OverflowError`
of `PyNumber_AsSsize_t`; a buffer gives its bytes; a list of `int`s goes through the fast path, which
gives the values when all are in `range(256)` and otherwise empties the object again and raises the
`ValueError` of the first bad one (so no unwritten byte is left, `InitInitialised`). For every heap
and argument below 2^46 bytes. -/
def BaInitESpec : Prop :=
  ∀ h : H,
    (0 < h.ba.exports → ∀ (arg : Option Arg) (enc : Option (String × Codec)) (err : Option String),
      baInitE arg enc err h = (.error exportsMsg, h)) ∧
    (h.ba.exports = 0 →
      (∃ h', baInitE none none none h = (.ok (), h') ∧ h'.ba.data = []) ∧
      (∀ n : Nat, 0 < n → (n : Int) < 2 ^ 46 →
        ∃ h', baInitE (some (.obj (.int n))) none none h = (.ok (), h') ∧ h'.ba.data = List.replicate n 0) ∧
      (∀ v : Int, v < 0 → ssizeMin ≤ v →
        ∃ h', baInitE (some (.obj (.int v))) none none h = (.error (.valueError "negative count"), h') ∧ h'.ba.data = []) ∧
      (∀ v : Int, v > ssizeMax →
        ∃ h', baInitE (some (.obj (.int v))) none none h =
          (.error (.overflowError "cannot fit 'int' into an index-sized integer"), h') ∧ h'.ba.data = []) ∧
      (∀ s : Seq, (s.length : Int) < 2 ^ 46 →
        ∃ h', baInitE (some (.obj (.bytes s))) none none h = (.ok (), h') ∧ h'.ba.data = seqData s) ∧
      (∀ vs : List Nat, (∀ c ∈ vs, c < 256) → 0 < vs.length → (vs.length : Int) < 2 ^ 46 →
        ∃ h', baInitE (some (.obj (.list (vs.map (fun c : Nat => Obj.int (c : Int)))))) none none h = (.ok (), h') ∧
          h'.ba.data = seqData vs))

theorem baInitESpec_proven : BaInitESpec := by
  intro h
  refine ⟨?_, ?_⟩
  · intro hx arg enc err
    have hc : canResize h.ba = .error exportsMsg := by simp [canResize, hx, exportsMsg]
    simp [baInitE, E.bind_app, canResizeE, hc]
  · intro hx
    obtain ⟨h0, hbase, hd0, hx0⟩ := init_reset h hx
    have hs0 : h0.ba.size = 0 := by simp [BA.size, hd0]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact ⟨h0, by unfold baInitE; rw [hbase]; rfl, hd0⟩
    · intro n hn hs
      obtain ⟨r, hr, hd, hxr⟩ := exportRule_proven.2.2.2 h0.ba n (by omega) hx0 hs
      have hne : ¬ ((n : Int) = h0.ba.size) := by omega
      simp only [hne, ↓reduceIte] at hd
      have hr1 : ssizeMin ≤ (n : Int) ∧ (n : Int) ≤ ssizeMax := by
        rw [ssizeMax_val, show ssizeMin = -9223372036854775808 by decide]; omega
      refine ⟨{ h0.put r with ba := { r with data := List.replicate n 0 } }, ?_, rfl⟩
      unfold baInitE
      rw [hbase]
      simp [E.bind_app, encNoArg, Arg.indexCheck, Obj.index?, E.attempt_app, asSsizeE, indexE, E.lift_app, hr1,
        show ¬ ((n : Int) < 0) by omega, resizeE, hr, Arg.typeName, Obj.typeName, hn, put_ba]
    · intro v hv h1
      have hr1 : ssizeMin ≤ v ∧ v ≤ ssizeMax := ⟨h1, by rw [ssizeMax_val]; omega⟩
      refine ⟨h0, ?_, hd0⟩
      unfold baInitE
      rw [hbase]
      simp [E.bind_app, encNoArg, Arg.indexCheck, Obj.index?, E.attempt_app, asSsizeE, indexE, E.lift_app, hr1, hv,
        E.throw_app]
    · intro v hv
      have hr1 : ¬ (ssizeMin ≤ v ∧ v ≤ ssizeMax) := by omega
      refine ⟨h0, ?_, hd0⟩
      unfold baInitE
      rw [hbase]
      have hte : ∀ m, isTypeError (.overflowError m) = false := fun _ => rfl
      simp [E.bind_app, encNoArg, Arg.indexCheck, Obj.index?, E.attempt_app, asSsizeE, indexE, E.lift_app, hr1,
        E.throw_app, hte, Arg.typeName, Obj.typeName]
      rfl
    · intro s hs
      by_cases hz : s.length = 0
      · have he : s = [] := List.eq_nil_of_length_eq_zero hz
        subst he
        have hr : baResize h0.ba 0 = .ok h0.ba := by
          have := exportRule_proven.1 h0.ba; rw [hs0] at this; exact this
        refine ⟨{ h0 with ba := { h0.ba with data := seqData [] } }, ?_, by simp [seqData]⟩
        unfold baInitE
        rw [hbase]
        simp only [E.bind_app, encNoArg, Arg.indexCheck, Obj.index?, Arg.bufferCheck, Obj.buffer?,
          getBuf_obj (.bytes []) [] rfl, E.attempt_app, resizeE, Buf.len, List.length_nil,
          show ((0 : Nat) : Int) = 0 from rfl, hr, put_self,
          Buf.read, noRel, E.pure_app, E.modify_app, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, E.throw_app,
          Bool.not_false, Option.isSome_some]
      · obtain ⟨r, hr, _, _⟩ := exportRule_proven.2.2.2 h0.ba s.length (by omega) hx0 hs
        refine ⟨{ h0.put r with ba := { r with data := seqData s } }, ?_, rfl⟩
        unfold baInitE
        rw [hbase]
        simp only [E.bind_app, encNoArg, Arg.indexCheck, Obj.index?, Arg.bufferCheck, Obj.buffer?,
          getBuf_obj (.bytes s) s rfl, E.attempt_app, resizeE, Buf.len, hr, Buf.read, noRel, put_ba, E.pure_app,
          E.modify_app, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, E.throw_app, Bool.not_false,
          Option.isSome_some]
    · intro vs hc hpos hs
      obtain ⟨r, hr, hd, _⟩ := exportRule_proven.2.2.2 h0.ba vs.length (by omega) hx0 (by simpa using hs)
      have hne : ¬ ((vs.length : Int) = h0.ba.size) := by omega
      simp only [hne, ↓reduceIte, resizedData, hd0, List.take_nil, List.nil_append, List.length_nil,
        Nat.sub_zero] at hd
      have hl : (vs.length : Int).toNat = vs.length := by simp
      rw [hl] at hd
      have hf := initFast_ok vs 0 r [] hc (by simpa [List.length_map] using hd) rfl
      refine ⟨(h0.put r).put { r with data := [] ++ seqData vs }, ?_, rfl⟩
      unfold baInitE
      rw [hbase]
      simp [E.bind_app, encNoArg, Arg.indexCheck, Obj.index?, Arg.bufferCheck, Obj.buffer?, resizeE, hr, baInitFast,
        List.length_map, hf, put_ba]

/-! ## The documented buffer flags -/

/-- `inspect.BufferFlags.READ` and `inspect.BufferFlags.WRITE` (Lib/inspect.py:3366-3367), which
Doc/library/inspect.rst:1877-1901 lists among "the flags that can be passed to the `__buffer__`
method". -/
def inspectReadWrite : List Int := [0x100, 0x200]

/-- A buffer request on a bytearray with a flag the documentation offers for `__buffer__` does not fail
with `SystemError`, the exception of an internal error. Refuted: `PyBuffer_FillInfo`, which
`bytearray_getbuffer_lock_held` calls (:81), answers `PyBUF_READ` and `PyBUF_WRITE` with
`PyErr_BadInternalCall` (Objects/abstract.c:784-786), so `bytearray().__buffer__(inspect.BufferFlags.READ)`
raises `SystemError: Objects/abstract.c:785: bad argument to internal function`, where
`memoryview(b'').__buffer__` of the same flag succeeds. -/
def BufferFlagsNoSystemError : Prop :=
  ∀ (b : BA) (flags : Int) (e : PyExc), flags ∈ inspectReadWrite →
    baGetBufferC b false flags = .error e → e.className ≠ "SystemError"

theorem bufferFlagsNoSystemError_refuted : ¬ BufferFlagsNoSystemError := by
  intro hp
  exact hp {} 0x100 _ (by simp [inspectReadWrite]) ((baBufferExport_proven {} 0x100).2.1 (Or.inl rfl)) rfl

/-! ## `hex` with a separator -/

theorem strhex_bytes1 (s : Seq) (c : Nat) (hc : c ≤ 127) (bps : Int) :
    strhexImpl s (some (.bytes [c])) bps false = strhexBody s (some c) bps := by
  have h1 : ¬ (c > 127 ∧ (!false) = true) := by omega
  simp only [strhexImpl, objLength, List.length_cons, List.length_nil, bind, Except.bind, ne_eq,
    not_true_eq_false, ↓reduceIte, pure, Except.pure, List.headD_cons, h1]
  rfl

theorem strhex_str1 (s : Seq) (c : Nat) (hc : c ≤ 127) (bps : Int) :
    strhexImpl s (some (.str [c])) bps false = strhexBody s (some c) bps := by
  have h1 : ¬ (c > 127 ∧ (!false) = true) := by omega
  have h2 : ¬ (c ≥ 256) := by omega
  simp only [strhexImpl, objLength, List.length_cons, List.length_nil, bind, Except.bind, ne_eq,
    not_true_eq_false, ↓reduceIte, pure, Except.pure, List.headD_cons, h1, h2]
  rfl

/-- `baHexE` once the separator's check has given `r`: `ob_exports` is raised around the check and
lowered after, and a separator that runs no Python code leaves the object as it was. -/
theorem hex_after_sep (h : H) (bps : Int) (h1 : ssizeMin ≤ bps) (h2 : bps ≤ ssizeMax) (o : Obj)
    (r : Py (Option Nat)) (hr0 : ∀ hb : H, (lengthE (.obj o) >>= fun n => E.lift (hexSepCheck (.obj o) n)) hb = (r, hb)) :
    baHexE cRead (some (.obj o)) (some (.obj (.int bps))) h =
      ((r >>= fun parsed => strhexBody h.ba.seq parsed bps), h) := by
  have rs := read_same h { h with ba := baGetBuffer h.ba } ⟨rfl, rfl, rfl, rfl⟩
  have e3 : ({ ba := baReleaseBuffer (baGetBuffer h.ba), gen := h.gen, kept := h.kept } : H) = h := by
    rw [release_get]
  have hr := hr0 { h with ba := baGetBuffer h.ba }
  simp only [E.bind_app] at hr
  simp only [baHexE, E.bind_app, clinic_int bps ⟨h1, h2⟩, E.get_app, exportsUp, E.modify_app, E.attempt_app,
    hexSepE]
  rw [hr]
  cases r with
  | error e => simp [exportsDown, E.modify_app, e3, E.lift_app, bind, Except.bind]
  | ok p => simp [cRead, readE_app, rs, exportsDown, E.modify_app, e3, seq_getBuffer, E.lift_app, bind, Except.bind]

/-- `bytearray.hex(sep, bytes_per_sep)` (:2733-2747) with a separator that runs no Python code: a
one-byte `bytes` or one-character `str` below 128 gives `bytes.hex` of the contents with that
separator (whose grouping by `bytes_per_sep` is `HexGroups`); a `bytes` of another length is
`ValueError('sep must be length 1.')`, a non-ASCII one `ValueError('sep must be ASCII.')`, and an
object without a length the `TypeError` of `PyObject_Length`. The object is left as it was in every
case (`ob_exports` is lowered again). For every heap and every `bytes_per_sep` in `Py_ssize_t`. -/
def BaHexSepSpec : Prop :=
  ∀ (h : H) (bps : Int), ssizeMin ≤ bps → bps ≤ ssizeMax →
    (∀ c : Nat, c ≤ 127 → baHexE cRead (some (.obj (.bytes [c]))) (some (.obj (.int bps))) h =
      (bytesHex h.ba.seq (some (.bytes [c])) bps, h)) ∧
    (∀ c : Nat, c ≤ 127 → baHexE cRead (some (.obj (.str [c]))) (some (.obj (.int bps))) h =
      (bytesHex h.ba.seq (some (.str [c])) bps, h)) ∧
    (∀ s : Seq, s.length ≠ 1 → baHexE cRead (some (.obj (.bytes s))) (some (.obj (.int bps))) h =
      (.error (.valueError "sep must be length 1."), h)) ∧
    (∀ c : Nat, 128 ≤ c → baHexE cRead (some (.obj (.bytes [c]))) (some (.obj (.int bps))) h =
      (.error (.valueError "sep must be ASCII."), h)) ∧
    (∀ c : Nat, 128 ≤ c → baHexE cRead (some (.obj (.str [c]))) (some (.obj (.int bps))) h =
      (.error (.valueError "sep must be ASCII."), h)) ∧
    (∀ v : Int, baHexE cRead (some (.obj (.int v))) (some (.obj (.int bps))) h =
      (.error (.typeError "object of type 'int' has no len()"), h))

theorem baHexSepSpec_proven : BaHexSepSpec := by
  intro h bps h1 h2
  have hr : ¬ (bps < ssizeMin ∨ bps > ssizeMax) := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc
    have hc' : ¬ (c > 127) := by omega
    rw [hex_after_sep h bps h1 h2 (.bytes [c]) (.ok (some c)) (fun hb => by
      simp only [E.bind_app, lengthE, objLength, E.lift_app, Functor.map, Except.map]
      simp [ objLength, E.lift_app, hexSepCheck, hc', Functor.map, Except.map, E.bind_app, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw, bind, Except.bind])]
    simp [bytesHex, hr, strhex_bytes1 _ c hc, bind, Except.bind]
  · intro c hc
    have hc' : ¬ (c > 127) := by omega
    have hc2 : ¬ (c ≥ 256) := by omega
    rw [hex_after_sep h bps h1 h2 (.str [c]) (.ok (some c)) (fun hb => by
      simp only [E.bind_app, lengthE, objLength, E.lift_app, Functor.map, Except.map]
      simp [ objLength, E.lift_app, hexSepCheck, hc', hc2, Functor.map, Except.map, E.bind_app, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw, bind, Except.bind])]
    simp [bytesHex, hr, strhex_str1 _ c hc, bind, Except.bind]
  · intro s hs
    have hs' : ((s.length : Nat) : Int) ≠ 1 := by omega
    rw [hex_after_sep h bps h1 h2 (.bytes s) (.error (.valueError "sep must be length 1.")) (fun hb => by
      simp only [E.bind_app, lengthE, objLength, E.lift_app, Functor.map, Except.map]
      simp [ objLength, E.lift_app, hexSepCheck, hs', Functor.map, Except.map, E.bind_app, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw, bind, Except.bind])]
    rfl
  · intro c hc
    have hc' : c > 127 := by omega
    rw [hex_after_sep h bps h1 h2 (.bytes [c]) (.error (.valueError "sep must be ASCII.")) (fun hb => by
      simp only [E.bind_app, lengthE, objLength, E.lift_app, Functor.map, Except.map]
      simp [ objLength, E.lift_app, hexSepCheck, hc', Functor.map, Except.map, E.bind_app, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw, bind, Except.bind])]
    rfl
  · intro c hc
    rw [hex_after_sep h bps h1 h2 (.str [c]) (.error (.valueError "sep must be ASCII.")) (fun hb => by
      simp only [E.bind_app, lengthE, objLength, E.lift_app, Functor.map, Except.map]
      by_cases hc2 : c ≥ 256
      · simp [hexSepCheck, hc2, pure, Except.pure, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
      · have hc' : c > 127 := by omega
        simp [lengthE, objLength, E.lift_app, hexSepCheck, hc2, hc', Functor.map, Except.map, E.bind_app, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw, bind, Except.bind])]
    rfl
  · intro v
    rw [hex_after_sep h bps h1 h2 (.int v) (.error (.typeError "object of type 'int' has no len()")) (fun hb => by
      simp only [E.bind_app, lengthE, objLength, E.lift_app, Functor.map, Except.map]
      simp [ objLength, E.lift_app, Functor.map, Except.map, E.bind_app, Obj.typeName, bind, Except.bind]
      rfl)]
    rfl

end PyLean.BytesObj.Bytes
