import PyLean.BytesObj.Bytes.FormatProps

/-!
More properties of `_PyBytes_FormatEx`: literal text, argument accounting, the
conversion helpers, and the three places where it misreports an error.
-/

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

/-! ## Literal text and argument accounting -/

/-- The result of a `%` with a format holding no `%`, for each kind of right operand. -/
def literalOutcome (args : Obj) (fmt : Seq) : Py Seq :=
  match args with
  | .tuple [] => .ok fmt
  | .tuple _ => .error (.typeError "not all arguments converted during bytes formatting")
  | .dict _ | .list _ | .memview _ _ => .ok fmt
  | _ => .error (.typeError "not all arguments converted during bytes formatting")

/-- For every format without `%` whose size an object can have (`len + 33 < 2^47`,
so the writer's allocation succeeds): the bytes are copied, an empty tuple or a mapping
is accepted, and any other right operand is reported as unconverted. This pins the
literal-run branch and the final `argidx < arglen && !dict` check. -/
def FormatLiteral : Prop :=
  ∀ (fmt : Seq) (args : Obj), 37 ∉ fmt → (fmt.length : Int) + 33 < 2 ^ 47 →
    bytesFormatEx fmt args false = literalOutcome args fmt

theorem ssizeMax_val : ssizeMax = 9223372036854775807 := by decide
theorem small_val : smallBufferSize = 512 := rfl
theorem objsize_val : bytesObjectSize = 33 := rfl

theorem bytesFromSize_ok (n : Nat) (h0 : (n : Int) ≠ 0) (hs : (n : Int) + 33 < 2 ^ 47) :
    bytesFromSize n = .ok (List.replicate n 0) := by
  unfold bytesFromSize
  have h4 : ¬ ((n : Int) > ssizeMax - bytesObjectSize) := by rw [ssizeMax_val, objsize_val]; omega
  have h5 : mallocFails (bytesObjectSize + (n : Int)) = false := by
    have : ¬ ((bytesObjectSize + (n : Int)) ≥ 2 ^ 47) := by rw [objsize_val]; omega
    simpa [mallocFails] using this
  rw [if_neg h0, if_neg h4]
  simp [h5]

theorem writerAlloc_ok (size : Nat) (hs : (size : Int) + 33 < 2 ^ 47) :
    ∃ w, writerAlloc (writerInit false) size = .ok w := by
  unfold writerAlloc writerInit writerPrepare
  simp only [bind, Except.bind, pure, Except.pure, Int.zero_add]
  by_cases h0 : (size : Int) = 0
  · simp [h0]
  · have h1 : ¬ ((0 : Int) > ssizeMax - size) := by rw [ssizeMax_val]; omega
    simp only [h0, if_false, h1]
    by_cases h2 : (size : Int) > smallBufferSize
    · have hr : writerResize { allocated := smallBufferSize, useSmall := true } (size : Int) =
          .ok { allocated := (size : Int), useSmall := false } := by
        unfold writerResize writerResizeCheck
        simp [bytesFromSize_ok size h0 hs, bind, Except.bind, pure, Except.pure, Except.map]
      simp only [h2, if_true, hr]
      exact ⟨_, rfl⟩
    · simp only [h2, if_false]
      exact ⟨_, rfl⟩

theorem findIdx_none_of_not_mem (l : Seq) (h : 37 ∉ l) : l.findIdx? (· == 37) = none := by
  rw [List.findIdx?_eq_none_iff]
  intro x hx
  have : x ≠ 37 := fun e => h (e ▸ hx)
  simpa using this

theorem not_mem_getD (l : Seq) (i : Nat) (h : 37 ∉ l) (hi : i < l.length) : l.getD i 0 ≠ 37 := by
  intro e
  apply h
  have : l[i] = 37 := by simpa [List.getD, hi] using e
  exact this ▸ List.getElem_mem hi

theorem not_mem_drop (l : Seq) (k : Nat) (h : 37 ∉ l) : 37 ∉ l.drop k :=
  fun m => h (List.mem_of_mem_drop m)

theorem not_mem_take (l : Seq) (k : Nat) (h : 37 ∉ l) : 37 ∉ l.take k :=
  fun m => h (List.mem_of_mem_take m)

/-- The whole literal goes in one iteration of the main loop. -/
theorem formatLoop_literal (fmt : Seq) (dict : Option Obj) (ba : Bool) (fuel : Nat) (st : FS)
    (h : 37 ∉ fmt) (h1 : st.pos = 0) (h2 : st.cnt = fmt.length) (h3 : st.out = [])
    (hf : fmt.length + 1 ≤ fuel) :
    ∃ st', formatLoop fmt dict ba fuel st = .ok st' ∧ st'.out = fmt ∧ st'.argidx = st.argidx ∧
      st'.arglen = st.arglen := by
  cases hfmt : fmt with
  | nil =>
    subst hfmt
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    have h0 : st.cnt = 0 := by simpa using h2
    refine ⟨{ st with cnt := st.cnt - 1 }, ?_, by simpa using h3, rfl, rfl⟩
    rw [formatLoop]
    have : ¬ (st.cnt - 1 ≥ 0) := by omega
    simp only [if_neg this]
  | cons c cs =>
    subst hfmt
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 + 1 := ⟨fuel - 2, by simp at hf; omega⟩
    have hc : c ≠ 37 := fun e => h (by simp [e])
    have hcs : 37 ∉ cs := fun e => h (by simp [e])
    have hcnt : st.cnt - 1 = cs.length := by simp at h2; omega
    have hnn : st.cnt - 1 ≥ 0 := by omega
    have hg : (c :: cs).getD st.pos 0 ≠ 37 := by rw [h1]; simpa using hc
    have hrest : ((c :: cs).drop (st.pos + 1)).take (st.cnt - 1).toNat = cs := by
      rw [hcnt, h1]; simp
    have hfi : (((c :: cs).drop (st.pos + 1)).take (st.cnt - 1).toNat).findIdx? (· == 37) = none := by
      rw [hrest]; exact findIdx_none_of_not_mem _ hcs
    have hcopy : ((c :: cs).drop st.pos).take (st.cnt - 1 + 1).toNat = c :: cs := by
      have e : (st.cnt - 1 + 1).toNat = cs.length + 1 := by omega
      rw [e, h1]; simp
    let S : FS := { st with cnt := (st.cnt - 1) - ((st.cnt - 1 + 1) - 1), out := st.out ++ (c :: cs),
                            pos := st.pos + (st.cnt - 1 + 1).toNat }
    have hS : ¬ (S.cnt - 1 ≥ 0) := by
      show ¬ ((st.cnt - 1) - ((st.cnt - 1 + 1) - 1) - 1 ≥ 0)
      omega
    refine ⟨{ S with cnt := S.cnt - 1 }, ?_, ?_, rfl, rfl⟩
    · rw [formatLoop]
      simp only [if_pos hnn]
      simp only [ne_eq]
      rw [if_pos hg]
      simp only [hfi, hcopy]
      show formatLoop (c :: cs) dict ba (f + 1) S = _
      rw [formatLoop]
      simp only [if_neg hS]
    · show st.out ++ (c :: cs) = c :: cs
      rw [h3]; rfl

theorem formatLoop_literal' (fmt : Seq) (dict : Option Obj) (ba : Bool) (fuel : Nat) (st : FS)
    (r : Py FS) (hr : formatLoop fmt dict ba fuel st = r)
    (h : 37 ∉ fmt) (h1 : st.pos = 0) (h2 : st.cnt = fmt.length) (h3 : st.out = [])
    (hf : fmt.length + 1 ≤ fuel) :
    ∃ st', r = .ok st' ∧ st'.out = fmt ∧ st'.argidx = st.argidx ∧ st'.arglen = st.arglen := by
  subst hr
  exact formatLoop_literal fmt dict ba fuel st h h1 h2 h3 hf

/-- `bytesFormatEx` on a format without `%`. -/
theorem formatLiteral_proven : FormatLiteral := by
  intro fmt args h hsize
  obtain ⟨w, hw⟩ := writerAlloc_ok fmt.length hsize
  unfold bytesFormatEx
  simp only [bind, Except.bind, hw, pure, Except.pure]
  cases args
  case tuple xs =>
    cases xs
    all_goals
      simp only
      split
      · rename_i e heq
        obtain ⟨_, h1, _⟩ := formatLoop_literal' _ _ _ _ _ _ heq h rfl rfl rfl (Nat.le_refl _)
        simp at h1
      · rename_i st' heq
        obtain ⟨s2, h1, h2, h3, h4⟩ := formatLoop_literal' _ _ _ _ _ _ heq h rfl rfl rfl (Nat.le_refl _)
        simp only [Except.ok.injEq] at h1
        subst h1
        simp [h2, h3, h4, asMapping, literalOutcome, writerFinish]
        try rfl
  all_goals
    simp only
    split
    · rename_i e heq
      obtain ⟨_, h1, _⟩ := formatLoop_literal' _ _ _ _ _ _ heq h rfl rfl rfl (Nat.le_refl _)
      simp at h1
    · rename_i st' heq
      obtain ⟨s2, h1, h2, h3, h4⟩ := formatLoop_literal' _ _ _ _ _ _ heq h rfl rfl rfl (Nat.le_refl _)
      simp only [Except.ok.injEq] at h1
      subst h1
      simp [h2, h3, h4, asMapping, literalOutcome, writerFinish]
      try rfl

/-! ## `byte_converter` and `format_obj` -/

/-- `%c`: an int (or index) is accepted exactly in `range(256)`, a bytes or bytearray
exactly with length 1; `%b`: bytes, bytearray, `__bytes__` and buffers give their
contents, in that order of preference. -/
def ConvertersSpec : Prop :=
  (∀ v : Int, byteConverter (.int v) =
    if 0 ≤ v ∧ v ≤ 255 then .ok v.toNat else .error (.overflowError "%c arg not in range(256)")) ∧
  (∀ s : Seq, s.length = 1 → byteConverter (.bytes s) = .ok (s.headD 0) ∧
    byteConverter (.bytearray s) = .ok (s.headD 0)) ∧
  (∀ s : Seq, formatObj (.bytes s) = .ok s ∧ formatObj (.bytearray s) = .ok s ∧
    formatObj (.dunder (.bytes s)) = .ok s ∧ ∀ a, formatObj (.memview s a) = .ok s)

theorem convertersSpec_proven : ConvertersSpec := by
  refine ⟨?_, ?_, ?_⟩
  · intro v
    by_cases h : 0 ≤ v ∧ v ≤ 255 <;> simp [byteConverter, Obj.index?, h]
  · intro s h
    simp [byteConverter, h]
  · intro s
    simp [formatObj, Obj.buffer?]

/-- `formatlong` and `getnextarg`: an int subclass or number goes through its integer
value; `o`, `x`, `X` refuse a float and everything else; `d` refuses a non-number; the
argument cursor stops at the end of the tuple. -/
def FormatLongTypes : Prop :=
  (∀ (b : Bool) (fl : Fl) (prec : Int) (t : Nat),
    formatLong (.bool b) fl prec t = unicodeFormatLong (if b then 1 else 0) fl.alt prec t) ∧
  (∀ (v : Int) (fl : Fl) (prec : Int) (t : Nat),
    formatLong (.index v) fl prec t = unicodeFormatLong v fl.alt prec t) ∧
  (∀ (f : Flt) (fl : Fl) (prec : Int) (t : Nat), (t = 111 ∨ t = 120 ∨ t = 88) →
    ∃ m, formatLong (.float f) fl prec t = .error (.typeError m)) ∧
  (∀ (s : Seq) (fl : Fl) (prec : Int) (t : Nat),
    ∃ m, formatLong (.bytes s) fl prec t = .error (.typeError m)) ∧
  (∀ st : FS, st.arglen ≥ 0 → st.argidx ≥ st.arglen →
    getNextArg st = .error (.typeError "not enough arguments for format string"))

theorem formatLongTypes_proven : FormatLongTypes := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro b fl prec t
    simp [formatLong, Obj.longValue?]
  · intro v fl prec t
    by_cases h : t = 111 ∨ t = 120 ∨ t = 88 <;>
      simp [formatLong, Obj.longValue?, Obj.isNumber, Obj.index?, h, numberLong]
  · intro f fl prec t h
    simp [formatLong, Obj.longValue?, Obj.isNumber, Obj.index?, h, notInteger, PyExc.className]
  · intro s fl prec t
    simp [formatLong, Obj.longValue?, Obj.isNumber]
  · intro st h1 h2
    have : ¬ (st.argidx < st.arglen) := by omega
    simp [getNextArg, this]

/-! ## Wrong exceptions -/

/-- `%` followed by a byte that is no conversion: is this the documented `ValueError`? -/
def isValueErr (r : Py Seq) : Bool :=
  match r with
  | .error (.valueError _) => true
  | _ => false

/-- Bytes that end a conversion specifier with an error: no flag, digit, `.`, `*`,
length modifier, `(`, or conversion character. -/
def badConv (b : Nat) : Bool :=
  !(asc "-+ #0123456789.*hlL(%diouxXeEfFgGcsbar").contains b

/-- "An unknown conversion raises `ValueError`": `b'%\xff' % (1,)` should report an
unsupported format character, as it does for every ASCII byte and as `str % args`
does. -/
def BadConvIsValueError : Prop :=
  ∀ b, b < 256 → badConv b = true → isValueErr (bytesMod [37, b] (.tuple [.int 1])) = true

theorem badConvIsValueError_refuted : ¬ BadConvIsValueError := by
  intro h
  have := h 255 (by decide) (by decide)
  revert this
  decide

/-- The narrowed statement: for an ASCII byte the `default:` case gives the
`ValueError`. Above 127 `c` is a negative `int` and `PyErr_Format("%c")` fails first. -/
def BadConvAsciiIsValueError : Prop :=
  ∀ b, b < 128 → badConv b = true → isValueErr (bytesMod [37, b] (.tuple [.int 1])) = true

set_option maxRecDepth 100000 in
theorem badConvAsciiIsValueError_proven : BadConvAsciiIsValueError := by
  unfold BadConvAsciiIsValueError
  decide

/-- "`%f` reports the conversion failure": the exception of `PyFloat_AsDouble` reaches
the caller, as in `str % args` (`formatfloat` in Objects/unicodeobject.c returns -1). -/
def FloatErrorPreserved : Prop :=
  ∀ (v : Obj) (fl : Fl) (prec : Int) (e : PyExc), asDouble v = .error e →
    formatFloatText v fl prec 102 = .error e

set_option exponentiation.threshold 3000 in
set_option maxRecDepth 100000 in
theorem asDouble_huge : asDouble (.int (2 ^ 1024)) =
    .error (.overflowError "int too large to convert to float") := by
  decide

set_option exponentiation.threshold 3000 in
theorem floatErrorPreserved_refuted : ¬ FloatErrorPreserved := by
  intro h
  have hd := asDouble_huge
  have := h (.int (2 ^ 1024)) {} (-1) _ hd
  unfold formatFloatText at this
  rw [hd] at this
  exact absurd this (by intro e; cases e)

/-- The narrowed statement: a non-number gets `TypeError`, for both types. -/
def FloatArgType : Prop :=
  ∀ (s : Seq) (fl : Fl) (prec : Int) (t : Nat),
    formatFloatText (.bytes s) fl prec t = .error (.typeError "float argument required, not bytes")

theorem floatArgType_proven : FloatArgType := by
  intro s fl prec t
  simp [formatFloatText, asDouble, Obj.typeName]
  decide

/-- "A negative `*` width is a left-justified field of that absolute width": if
`b'%*d' % (w, 1)` succeeds for `w < 0`, the result has at least `-w` bytes. -/
def NegStarWidth : Prop :=
  ∀ (w : Int) (out : Seq), ssizeMin ≤ w → w < 0 →
    bytesMod (asc "%*d") (.tuple [.int w, .int 1]) = .ok out → (out.length : Int) ≥ -w

theorem negStarWidth_refuted : ¬ NegStarWidth := by
  intro h
  have := h ssizeMin [49] (by decide) (by decide) (by decide)
  revert this
  decide

/-- The narrowed statement: for every other negative width the negation is exact. -/
def NegWrapExact : Prop := ∀ w : Int, ssizeMin < w → w < 0 → negWrap w = -w ∧ 0 < negWrap w

theorem negWrapExact_proven : NegWrapExact := by
  intro w h1 h2
  have : w ≠ ssizeMin := by omega
  simp [negWrap, this]
  omega

end PyLean.BytesObj.Bytes
