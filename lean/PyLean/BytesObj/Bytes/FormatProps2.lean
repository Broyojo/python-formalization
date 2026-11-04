import PyLean.BytesObj.Bytes.FormatProps

/-!
More properties of `_PyBytes_FormatEx`: literal text, argument accounting, the
conversion helpers, and what it reports for a bad conversion, a failed `%f` and a `*`.
-/

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

/-! ## Literal text and argument accounting -/

/-- The result of a `%` with a format holding no `%`, for each kind of right operand. -/
def literalOutcome (args : Obj) (fmt : Seq) : Py Seq :=
  match args with
  | .tuple [] => .ok fmt
  | .tuple xs =>
    .error (.typeError s!"not all arguments converted during bytes formatting (required 0, got {(xs.length : Int)})")
  | .dict _ | .list _ | .memview _ _ => .ok fmt
  | _ => .error (.typeError "not all arguments converted during bytes formatting (required 0, got 1)")

/-- For every format without `%` whose size an object can have (`len + 33 < 2^47`,
so the writer's allocation succeeds): the bytes are copied, an empty tuple or a mapping
is accepted, and any other right operand is reported as unconverted. This pins the
literal-run branch and the final `argidx < arglen && !dict` check. -/
def FormatLiteral : Prop :=
  ∀ (fmt : Seq) (args : Obj), 37 ∉ fmt → (fmt.length : Int) + 33 < 2 ^ 47 →
    bytesFormatEx fmt args false = literalOutcome args fmt

theorem ssizeMax_val : ssizeMax = 9223372036854775807 := by decide
theorem small_val : smallBufferSize = 256 := rfl
theorem objsize_val : bytesObjectSize = 33 := rfl

theorem bytesSizeCheck_ok (n : Int) (h0 : 0 ≤ n) (hs : n + 33 < 2 ^ 47) :
    bytesSizeCheck n = .ok () := by
  unfold bytesSizeCheck
  have h4 : ¬ (n > ssizeMax - bytesObjectSize) := by rw [ssizeMax_val, objsize_val]; omega
  have h5 : mallocFails (bytesObjectSize + n) = false := by
    have : ¬ ((bytesObjectSize + n) ≥ 2 ^ 47) := by rw [objsize_val]; omega
    simpa [mallocFails] using this
  by_cases h : n = 0
  · simp [h]
  · rw [if_neg h, if_neg h4]
    simp [h5]

theorem bytesFromSize_ok (n : Nat) (hs : (n : Int) + 33 < 2 ^ 47) :
    bytesFromSize n = .ok (List.replicate n 0) := by
  unfold bytesFromSize
  rw [bytesSizeCheck_ok _ (by omega) hs]
  simp

/-- A writer for a format of a size an object can have: its size is that size, and it can be
finished at that size. -/
theorem writerCreate_ok (size : Nat) (hs : (size : Int) + 33 < 2 ^ 47) :
    ∃ w, writerCreate size false = .ok w ∧ writerFinishSize w size = .ok () := by
  unfold writerCreate
  have h0 : ¬ ((size : Int) < 0) := by omega
  simp only [if_neg h0]
  by_cases h1 : (size : Int) ≥ 1
  · simp only [if_pos h1]
    by_cases h2 : (size : Int) ≤ smallBufferSize
    · have hr : writerResizeRaw { useBytearray := false, overallocate := !false } (size : Int) false =
          .ok { useBytearray := false, overallocate := !false } := by
        simp only [writerResizeRaw, writerAllocated, h2, if_true]
      rw [hr]
      refine ⟨_, rfl, ?_⟩
      have h3 : ¬ ((size : Int) = 0) := by omega
      simp [writerFinishSize, bytesSizeCheck_ok _ (by omega) hs, h3]
    · have hc := bytesSizeCheck_ok (size : Int) (by omega) hs
      have hr : writerResizeRaw { useBytearray := false, overallocate := !false } (size : Int) false =
          .ok { useBytearray := false, overallocate := !false, obj := some (size, size) } := by
        simp [writerResizeRaw, writerAllocated, h2, writerObjResize, hc]
      rw [hr]
      refine ⟨_, rfl, ?_⟩
      simp [writerFinishSize]
  · have h3 : (size : Int) = 0 := by omega
    simp only [if_neg h1]
    refine ⟨_, rfl, ?_⟩
    simp [writerFinishSize, h3]

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
      st'.arglen = st.arglen ∧ st'.w = st.w := by
  cases hfmt : fmt with
  | nil =>
    subst hfmt
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    have h0 : st.cnt = 0 := by simpa using h2
    refine ⟨{ st with cnt := st.cnt - 1 }, ?_, by simpa using h3, rfl, rfl, rfl⟩
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
    refine ⟨{ S with cnt := S.cnt - 1 }, ?_, ?_, rfl, rfl, rfl⟩
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
    ∃ st', r = .ok st' ∧ st'.out = fmt ∧ st'.argidx = st.argidx ∧ st'.arglen = st.arglen ∧
      st'.w = st.w := by
  subst hr
  exact formatLoop_literal fmt dict ba fuel st h h1 h2 h3 hf

/-- `bytesFormatEx` on a format without `%`. -/
theorem formatLiteral_proven : FormatLiteral := by
  intro fmt args h hsize
  obtain ⟨w, hw, hfin⟩ := writerCreate_ok fmt.length hsize
  unfold bytesFormatEx
  simp only [bind, Except.bind, hw]
  generalize hr : formatLoop fmt (asMapping args) false (fmt.length + 1) _ = r
  obtain ⟨s2, rfl, h2, h3, h4, h5⟩ := formatLoop_literal' _ _ _ _ _ _ hr h rfl rfl rfl (Nat.le_refl _)
  simp only [h2, h3, h4, h5, writerFinish, hfin]
  cases args
  case tuple xs =>
    cases xs with
    | nil => simp [literalOutcome, asMapping, throw, throwThe, MonadExcept.throw, pure, Except.pure]
    | cons x xs =>
      have hlt : (0 : Int) < ((x :: xs).length : Int) := by simp only [List.length_cons]; omega
      have hn : ¬ ((xs.length : Int) + 1 < 0) := by omega
      simp [literalOutcome, asMapping, hlt, hn, throw, throwThe, MonadExcept.throw]
      rfl
  all_goals simp [literalOutcome, asMapping, throw, throwThe, MonadExcept.throw, pure, Except.pure]
  all_goals rfl

/-! ## `byte_converter` and `format_obj` -/

/-- `%c`: an int (or index) is accepted exactly in `range(256)`, a bytes or bytearray
exactly with length 1, each refusal naming the argument through `FORMAT_ERROR`; `%b`: bytes,
bytearray, `__bytes__` and buffers give their contents, in that order of preference. -/
def ConvertersSpec : Prop :=
  (∀ (st : FS) (v : Int), byteConverter st (.int v) =
    if 0 ≤ v ∧ v ≤ 255 then .ok v.toNat
    else .error (formatError .overflowError st "%c argument not in range(256)")) ∧
  (∀ (st : FS) (s : Seq), s.length = 1 → byteConverter st (.bytes s) = .ok (s.headD 0) ∧
    byteConverter st (.bytearray s) = .ok (s.headD 0)) ∧
  (∀ (st : FS) (s : Seq), s.length ≠ 1 →
    (byteConverter st (.bytes s) = .error (formatError .typeError st
      s!"%c requires an integer in range(256) or a single byte, not a bytes object of length {s.length}")) ∧
    (byteConverter st (.bytearray s) = .error (formatError .typeError st
      s!"%c requires an integer in range(256) or a single byte, not a bytearray object of length {s.length}"))) ∧
  (∀ (st : FS) (s : Seq), formatObj st (.bytes s) = .ok s ∧ formatObj st (.bytearray s) = .ok s ∧
    formatObj st (.dunder (.bytes s)) = .ok s ∧ ∀ a, formatObj st (.memview s a) = .ok s)

theorem convertersSpec_proven : ConvertersSpec := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro st v
    by_cases h : 0 ≤ v ∧ v ≤ 255 <;> simp [byteConverter, Obj.index?, h]
  · intro st s h
    simp [byteConverter, h]
  · intro st s h
    simp [byteConverter, h]
  · intro st s
    simp [formatObj, Obj.buffer?]

/-- `formatlong` and `getnextarg`: an int subclass or number goes through its integer
value; `o`, `x`, `X` refuse a float and everything else; `d` refuses a non-number; the
argument cursor stops at the end of the tuple, a single argument serves one conversion, and a `*`
cannot take a single argument. -/
def FormatLongTypes : Prop :=
  (∀ (st : FS) (b : Bool) (fl : Fl) (prec : Int) (t : Nat),
    formatLong st (.bool b) fl prec t = unicodeFormatLong (if b then 1 else 0) fl.alt prec t) ∧
  (∀ (st : FS) (v : Int) (fl : Fl) (prec : Int) (t : Nat),
    formatLong st (.index v) fl prec t = unicodeFormatLong v fl.alt prec t) ∧
  (∀ (st : FS) (f : Binary64.F64) (fl : Fl) (prec : Int) (t : Nat), (t = 111 ∨ t = 120 ∨ t = 88) →
    formatLong st (.float f) fl prec t = .error
      (formatError .typeError st (requiresMsg t "an integer" "float"))) ∧
  (∀ (st : FS) (s : Seq) (fl : Fl) (prec : Int) (t : Nat), (t ≠ 111 ∧ t ≠ 120 ∧ t ≠ 88) →
    formatLong st (.bytes s) fl prec t = .error
      (formatError .typeError st (requiresMsg t "a real number" "bytes"))) ∧
  (∀ (st : FS) (b : Bool), st.arglen ≥ 0 → st.argidx ≥ st.arglen →
    getNextArg st b = .error (.typeError s!"not enough arguments for format string (got {st.arglen})")) ∧
  (∀ (st : FS), st.arglen = -1 → st.argidx = -2 →
    getNextArg st true = .ok (st.args, { st with argidx := -1 }) ∧
    getNextArg st false = .error (.typeError "not enough arguments for format string (got 1)"))

theorem formatLongTypes_proven : FormatLongTypes := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro st b fl prec t
    simp [formatLong, Obj.longValue?]
  · intro st v fl prec t
    by_cases h : t = 111 ∨ t = 120 ∨ t = 88 <;>
      simp [formatLong, Obj.longValue?, Obj.isNumber, Obj.index?, h, numberLong]
  · intro st f fl prec t h
    simp [formatLong, Obj.longValue?, Obj.isNumber, Obj.index?, h, notInteger, PyExc.className,
      isTypeError, excMatches, Obj.typeName]
  · intro st s fl prec t h
    have h2 : ¬ (t = 111 ∨ t = 120 ∨ t = 88) := by omega
    simp [formatLong, Obj.longValue?, Obj.isNumber, h2, Obj.typeName]
  · intro st b h1 h2
    have h3 : ¬ (st.argidx < st.arglen) := by omega
    have h4 : ¬ (st.arglen < 0) := by omega
    simp [getNextArg, h3, h4]
  · intro st h1 h2
    have h3 : st.argidx < st.arglen := by omega
    have h4 : ¬ (st.arglen ≥ 0) := by omega
    have h5 : st.arglen < 0 := by omega
    constructor
    · simp [getNextArg, h3, h4, h2]
      omega
    · simp only [getNextArg, h3, h4, h5, if_true, if_false, Bool.false_eq_true]
      rfl

/-! ## Refusals -/

/-- Bytes that end a conversion specifier with an error: no flag, digit, `.`, `*`,
length modifier, `(`, or conversion character. -/
def badConv (b : Nat) : Bool :=
  !(asc "-+ #0123456789.*hlL(%diouxXeEfFgGcsbar").contains b

/-- The `default:` case for every byte of a two-byte format: `b'%\xff' % (1,)` is a `ValueError` that
names the byte and both positions, for a byte above 127 too, where `c` is negative. -/
def BadConvIsValueError : Prop :=
  ∀ b, b < 256 → badConv b = true →
    bytesMod [37, b] (.tuple [.int 1]) = .error (unsupportedChar (sgnChar b) 0 1)

set_option maxRecDepth 100000 in
theorem badConvIsValueError_proven : BadConvIsValueError := by
  unfold BadConvIsValueError
  decide

/-- `%f` keeps the exception of `PyFloat_AsDouble`, as `str % args` does, and replaces only a
`TypeError`, which is the message for a non-number. -/
def FloatErrorPreserved : Prop :=
  ∀ (st : FS) (v : Obj) (fl : Fl) (prec : Int) (t : Nat) (e : PyExc), asDouble v = .error e →
    formatFloatText st v fl prec t = .error
      (if isTypeError e then
        formatError .typeError st (requiresMsg t "a real number" v.typeName)
       else e)

theorem floatErrorPreserved_proven : FloatErrorPreserved := by
  intro st v fl prec t e h
  unfold formatFloatText
  rw [h]
  simp only
  split <;> rfl

set_option exponentiation.threshold 3000 in
set_option maxRecDepth 100000 in
theorem asDouble_huge : asDouble (.int (2 ^ 1024)) =
    .error (.overflowError "int too large to convert to float") := by
  decide

/-- The two arms reached: a non-number is the `TypeError` of the conversion, and an int past the
range of a double keeps the `OverflowError`. -/
def FloatArgType : Prop :=
  (∀ (st : FS) (s : Seq) (fl : Fl) (prec : Int) (t : Nat),
    formatFloatText st (.bytes s) fl prec t =
      .error (formatError .typeError st (requiresMsg t "a real number" "bytes"))) ∧
  (∀ (st : FS) (fl : Fl) (prec : Int) (t : Nat),
    formatFloatText st (.int (2 ^ 1024)) fl prec t =
      .error (.overflowError "int too large to convert to float"))

set_option exponentiation.threshold 3000 in
theorem floatArgType_proven : FloatArgType := by
  refine ⟨?_, ?_⟩
  · intro st s fl prec t
    simp [formatFloatText, asDouble, Obj.typeName, isTypeError, excMatches, PyExc.className]
  · intro st fl prec t
    have h : isTypeError (.overflowError "int too large to convert to float") = false := by decide
    unfold formatFloatText
    rw [asDouble_huge]
    simp [h]

/-- A `*` width (bytesobject.c:771-804). A negative width is a left-justified field of the absolute
width, for all but `PY_SSIZE_T_MIN`, which has no negation and is refused, as a width outside
`Py_ssize_t` is. `v` is the argument `getnextarg` gave. Hypothesis: no mapping key in force, the only
case that gets to the argument. -/
def NegStarWidth : Prop :=
  ∀ (format : Seq) (at' : Int) (st st' : FS) (fl : Fl) (w : Int),
    st.arglen ≥ -1 → getNextArg st false = .ok (.int w, st') →
    (ssizeMin < w → w < 0 → ∃ st2 c, parseWidth format at' st fl 42 =
      .ok (st2, { fl with ljust := true }, -w, c)) ∧
    (0 ≤ w → w ≤ ssizeMax → ∃ st2 c, parseWidth format at' st fl 42 = .ok (st2, fl, w, c)) ∧
    ((w ≤ ssizeMin ∨ w > ssizeMax) → parseWidth format at' st fl 42 =
      .error (formatError .overflowError st' "too big for width"))

theorem negStarWidth_proven : NegStarWidth := by
  intro format at' st st' fl w h1 h2
  have hk : ¬ (st.arglen < -1) := by omega
  have hc : (42 : Int) = 42 := rfl
  unfold parseWidth
  simp only [bind, Except.bind, pure, Except.pure, hk, if_false, if_true, h2]
  refine ⟨?_, ?_, ?_⟩
  · intro h3 h4
    have hs : w ≤ ssizeMax := by unfold ssizeMax; omega
    have h5 : ¬ (w ≤ ssizeMin ∨ w > ssizeMax) := by omega
    simp [starWidth, Obj.longValue?, h5, h4]
  · intro h3 h4
    have h5 : ¬ (w ≤ ssizeMin ∨ w > ssizeMax) := by
      have : ssizeMin < 0 := by decide
      omega
    have h6 : ¬ w < 0 := by omega
    simp [starWidth, Obj.longValue?, h5, h6]
  · intro h3
    simp [starWidth, Obj.longValue?, h3]

end PyLean.BytesObj.Bytes
