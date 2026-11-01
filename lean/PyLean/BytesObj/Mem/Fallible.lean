import PyLean.BytesObj.Mem.Evil

/-!
The failure paths of the Python callbacks a memoryview operation runs: `__index__`,
`__float__`, `__bool__` and `__buffer__` may raise, or return an object of the wrong
type, after having released views. Each statement unfolds the function it names and
pins what that function does with the failure; none holds for an arbitrary function.
-/

namespace PyLean.BytesObj.Mem

open PyLean

/-- `fire` never fails: `BufferError` from `m.release()` is swallowed by the callback. -/
theorem fire_ok (r : Option Nat) (st : St) : ∃ s, fire r st = (.ok (), s) := by
  have hrel : ∀ (i : Nat) (s : St), (memoryRelease i s).1 = .ok () := by
    intro i s
    unfold memoryRelease
    simp only
    split
    · rfl
    · split
      · unfold mbufRelease
        simp only
        split
        · rfl
        · exact pyBufferRelease_ok _ _
      · rfl
  cases r with
  | none => exact ⟨st, rfl⟩
  | some i =>
    unfold fire
    simp only
    split
    · have := hrel i st
      rcases hx : memoryRelease i st with ⟨res, s⟩
      rw [hx] at this
      simp only at this
      subst this
      exact ⟨s, rfl⟩
    · exact ⟨st, rfl⟩

/-- `fire` does not touch the byte store: releasing a view frees no bytes in this model. -/
theorem fire_mem (r : Option Nat) (st st' : St) (h : fire r st = (.ok (), st')) : st'.mem = st.mem := by
  have hm := fire_mono r st
  rw [h] at hm
  exact hm.mem

/-- What a `pylong_as_*` does: `c` is the C conversion after `_PyNumber_Index`.
A raising `__index__` passes its exception up, a non-int result is the `TypeError` of
`_PyNumber_Index`, both after the callback ran; and a value goes through `c`. An object
with no `__index__` raises `TypeError` with no callback. -/
def ConvRule (f : Obj → M Int) (c : Int → Py Int) : Prop :=
  ∀ (r : Option Nat) (e : PyExc) (t : String) (n : Int) (s : List Char) (st st' : St),
    fire r st = (.ok (), st') →
      f (.index (.raises e) r) st = (.error e, st') ∧
      f (.index (.wrong t) r) st = (.error (indexWrong t), st') ∧
      f (.index (.val n) r) st = (c n, st') ∧
      f (.int n) st = (c n, st) ∧
      f (.str s) st = (.error (.typeError "'str' object cannot be interpreted as an integer"), st)

/-- The six `pylong_as_*` with the conversion each one uses, on every failure of `__index__`:
`PyLong_AsLong`, `PyLong_AsUnsignedLong` and so on. -/
def PylongFailures : Prop :=
  ConvRule pylongAsLd asLong ∧ ConvRule pylongAsLu asUnsignedLong ∧
  ConvRule pylongAsLld asLong ∧ ConvRule pylongAsLlu asUnsignedLong ∧
  ConvRule pylongAsZd longAsSsize ∧ ConvRule pylongAsZu asUnsignedLong

theorem lift_apply {α : Type} (x : Py α) (st : St) : M.lift x st = (x, st) := rfl

theorem numberIndex_raises (e : PyExc) (r : Option Nat) (st st' : St) (h : fire r st = (.ok (), st')) :
    numberIndex (.index (.raises e) r) st = (.error e, st') := by
  simp only [numberIndex, M.bind_app, h]
  rfl

theorem numberIndex_wrong (t : String) (r : Option Nat) (st st' : St) (h : fire r st = (.ok (), st')) :
    numberIndex (.index (.wrong t) r) st = (.error (indexWrong t), st') := by
  simp only [numberIndex, M.bind_app, h]
  rfl

theorem numberIndex_val (n : Int) (r : Option Nat) (st st' : St) (h : fire r st = (.ok (), st')) :
    numberIndex (.index (.val n) r) st = (.ok n, st') := by
  simp only [numberIndex, M.bind_app, h]
  rfl

theorem pylongFailures_proven : PylongFailures := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (intro r e t n s st st' h
     refine ⟨?_, ?_, ?_, ?_, ?_⟩
     · simp only [pylongAsLd, pylongAsLu, pylongAsLld, pylongAsLlu, pylongAsZd, pylongAsZu, M.bind_app,
         numberIndex_raises e r st st' h]
     · simp only [pylongAsLd, pylongAsLu, pylongAsLld, pylongAsLlu, pylongAsZd, pylongAsZu, M.bind_app,
         numberIndex_wrong t r st st' h]
     · simp only [pylongAsLd, pylongAsLu, pylongAsLld, pylongAsLlu, pylongAsZd, pylongAsZu, M.bind_app,
         numberIndex_val n r st st' h, lift_apply]
     · rfl
     · rfl)

/-- `fix_error_int`, on each class of exception a raising `__index__` can now deliver:
`TypeError` and the `ValueError` and `OverflowError` pair are replaced by the
`memoryview:` messages naming the format, and anything else passes through unchanged
(:1658-1664). -/
def FixErrorInt : Prop :=
  ∀ (fmt : List Char) (m cls : String),
    fixErrorInt fmt (.typeError m) = typeErrorInt fmt ∧
    fixErrorInt fmt (.valueError m) = valueErrorInt fmt ∧
    fixErrorInt fmt (.overflowError m) = valueErrorInt fmt ∧
    fixErrorInt fmt (.named cls m) = .named cls m ∧
    fixErrorInt fmt (.indexError m) = .indexError m

theorem fixErrorInt_proven : FixErrorInt := by
  intro fmt m cls
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem mapErr_err {α : Type} (f : PyExc → PyExc) (x : M α) (st st' : St) (e : PyExc)
    (h : x st = (.error e, st')) : M.mapErr f x st = (.error (f e), st') := by
  simp only [M.mapErr, h]

/-- `m[i] = item` for every integer format, when `__index__` of the item fails: nothing is
written, the callback's effects stay, and the error is the one `fix_error_int` makes of
it, so a `Boom` keeps its class while a `ValueError` becomes `memoryview: invalid value
for format`. The `?` arm is different on purpose: `PyObject_IsTrue` failing returns at
once, with the comment `preserve original error` (:1988-1989), so a raising `__bool__`
keeps even a `ValueError`. The float arms rewrite like the integer ones. -/
def PackFailures : Prop :=
  ∀ (self : Nat) (ptr : Int) (r : Option Nat) (e : PyExc) (t : String) (st st' : St),
    fire r st = (.ok (), st') →
      (∀ c ∈ ['b', 'h', 'i', 'l', 'B', 'H', 'I', 'L', 'q', 'Q', 'n', 'N'],
        packSingle self ptr (.index (.raises e) r) [c] st = (.error (fixErrorInt [c] e), st') ∧
        packSingle self ptr (.index (.wrong t) r) [c] st = (.error (typeErrorInt [c]), st')) ∧
      (∀ c ∈ ['f', 'd', 'e'],
        packSingle self ptr (.floatLike (.raises e) r) [c] st = (.error (fixErrorInt [c] e), st') ∧
        packSingle self ptr (.floatLike (.wrong t) r) [c] st = (.error (typeErrorInt [c]), st')) ∧
      packSingle self ptr (.boolLike (.raises e) r) ['?'] st = (.error e, st') ∧
      packSingle self ptr (.boolLike (.wrong t) r) ['?'] st = (.error (boolWrong t), st') ∧
      st'.mem = st.mem

theorem floatAsDouble_raises (e : PyExc) (r : Option Nat) (st st' : St) (h : fire r st = (.ok (), st')) :
    floatAsDouble (.floatLike (.raises e) r) st = (.error e, st') := by
  simp only [floatAsDouble, M.bind_app, h]
  rfl

theorem floatAsDouble_wrong (t : String) (r : Option Nat) (st st' : St) (h : fire r st = (.ok (), st')) :
    floatAsDouble (.floatLike (.wrong t) r) st = (.error (floatWrong t), st') := by
  simp only [floatAsDouble, M.bind_app, h]
  rfl

theorem isTrue_raises (e : PyExc) (r : Option Nat) (st st' : St) (h : fire r st = (.ok (), st')) :
    isTrue (.boolLike (.raises e) r) st = (.error e, st') := by
  simp only [isTrue, M.bind_app, h]
  rfl

theorem isTrue_wrong (t : String) (r : Option Nat) (st st' : St) (h : fire r st = (.ok (), st')) :
    isTrue (.boolLike (.wrong t) r) st = (.error (boolWrong t), st') := by
  simp only [isTrue, M.bind_app, h]
  rfl

theorem packFailures_proven : PackFailures := by
  intro self ptr r e t st st' h
  refine ⟨?_, ?_, ?_, ?_, fire_mem r st st' h⟩
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (constructor <;>
        simp only [packSingle, cc, List.getD_cons_zero, M.bind_app, M.mapErr, pylongAsLd, pylongAsLu,
          pylongAsLld, pylongAsLlu, pylongAsZd, pylongAsZu, numberIndex_raises e r st st' h,
          numberIndex_wrong t r st st' h, indexWrong, fixErrorInt])
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;>
      (constructor <;>
        simp only [packSingle, cc, List.getD_cons_zero, M.bind_app, M.mapErr,
          floatAsDouble_raises e r st st' h, floatAsDouble_wrong t r st st' h, floatWrong, fixErrorInt])
  · simp only [packSingle, cc, List.getD_cons_zero, M.bind_app, isTrue_raises e r st st' h]
  · simp only [packSingle, cc, List.getD_cons_zero, M.bind_app, isTrue_wrong t r st st' h]

/-- A failing `__index__` in a subscript, for a live view that is not 0-dimensional:
`m[k]` and `m[k] = v` raise what `__index__` raised, or the `TypeError` for a non-int,
and `m[k] = v` writes nothing. The key is converted before the item is looked up, so
this is the failure at :2608-2609 and :2686-2687. -/
def KeyFailures : Prop :=
  ∀ (self : Nat) (r : Option Nat) (e : PyExc) (t : String) (v : Obj) (st st' : St),
    baseInaccessible st self = false → (st.mv self).view.ndim ≠ 0 →
    fire r st = (.ok (), st') →
      memorySubscript self (.one (.obj (.index (.raises e) r))) st = (.error e, st') ∧
      memorySubscript self (.one (.obj (.index (.wrong t) r))) st = (.error (indexWrong t), st') ∧
      ((st.mv self).view.readonly = false → (st.mv self).view.ndim = 1 →
        (∃ f, adjustFmt (st.mv self).view = .ok f) →
        memoryAssSub self (.one (.obj (.index (.raises e) r))) (some v) st = (.error e, st') ∧
        (memoryAssSub self (.one (.obj (.index (.raises e) r))) (some v) st).2.mem = st.mem)

theorem keyFailures_proven : KeyFailures := by
  intro self r e t v st st' h0 hn hf
  refine ⟨?_, ?_, ?_⟩
  · simp only [memorySubscript, M.bind_app, checkReleased_ok _ _ h0, M.get, hn, ↓reduceIte, Obj.isIndex,
      numberIndex_raises e r st st' hf]
  · simp only [memorySubscript, M.bind_app, checkReleased_ok _ _ h0, M.get, hn, ↓reduceIte, Obj.isIndex,
      numberIndex_wrong t r st st' hf]
  · intro hro h1 ⟨f, hfmt⟩
    have key : memoryAssSub self (.one (.obj (.index (.raises e) r))) (some v) st = (.error e, st') := by
      simp only [memoryAssSub, M.bind_app, checkReleased_ok _ _ h0, M.get, M.lift, hfmt, hro,
        Bool.false_eq_true, ↓reduceIte, Obj.isIndex, h1, Nat.lt_irrefl, Nat.one_ne_zero,
        numberIndex_raises e r st st' hf]
    refine ⟨key, ?_⟩
    rw [key]
    exact fire_mem r st st' hf

/-- `ptr_from_tuple`, and `memory_item_multi` through it: a tuple longer than `ndim` is the
`TypeError` of :2430-2435 before any `__index__` runs, and a raising `__index__` in the
first position is the failure at :2441-2442. -/
def TupleFailures : Prop :=
  ∀ (v : Buf) (tup : List KeyElem) (r : Option Nat) (e : PyExc) (rest : List KeyElem) (st st' : St),
    (tup.length > v.ndim →
      ptrFromTuple v tup st =
        (.error (.typeError s!"cannot index {v.ndim}-dimension view with {tup.length}-element tuple"), st)) ∧
    (fire r st = (.ok (), st') → (rest.length + 1) ≤ v.ndim →
      ptrFromTuple v (.obj (.index (.raises e) r) :: rest) st = (.error e, st'))

theorem tupleFailures_proven : TupleFailures := by
  intro v tup r e rest st st'
  constructor
  · intro h
    simp only [ptrFromTuple, h, ↓reduceIte, M.bind_app, M.throw_app]
  · intro hf hle
    have hn : ¬ ((.obj (.index (.raises e) r) :: rest : List KeyElem).length > v.ndim) := by
      simp only [List.length_cons]
      omega
    simp only [ptrFromTuple, tupleLoop, elemIndex, M.bind_app, numberIndex_raises e r st st' hf,
      if_neg hn]

/-- A failing `__buffer__`: `memoryview(x)`, `memoryview._from_flags(x, flags)` and the
`PyObject_GetBuffer` of a slice assignment all raise what it raised, or the `TypeError`
of typeobject.c:10718-10719 for a non-memoryview result, after its callback ran, and
no view or managed buffer is left behind. -/
def BufferFailures : Prop :=
  ∀ (r : Option Nat) (e : PyExc) (t : String) (flags : Nat) (st st' : St), fire r st = (.ok (), st') →
    memoryviewNew (.exporter (.raises e) r) st = (.error e, st') ∧
    memoryviewNew (.exporter (.wrong t) r) st = (.error (bufferWrong t), st') ∧
    memoryViewFromObjectAndFlags (.exporter (.raises e) r) flags st = (.error e, st') ∧
    memoryViewFromObjectAndFlags (.exporter (.wrong t) r) flags st = (.error (bufferWrong t), st') ∧
    getBufferFull (.exporter (.raises e) r) st = (.error e, st') ∧
    getBufferFull (.exporter (.wrong t) r) st = (.error (bufferWrong t), st') ∧
    st'.mem = st.mem

theorem bufferFailures_proven : BufferFailures := by
  intro r e t flags st st' h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fire_mem r st st' h⟩ <;>
    (simp only [memoryviewNew, memoryViewFromObject, memoryViewFromObjectAndFlags, getBufferFull,
       M.bind_app, h]
     try rfl)

end PyLean.BytesObj.Mem
