import PyLean.MathInt.FltOpen
import PyLean.MathInt.FltNext
import PyLean.MathInt.FltLogProps

/-!
# Properties: the failure and special-value paths of `math.fsum`

`math_fsum` (Modules/mathmodule.c:1280-1396) converts each item as it is reached
(`ASSIGN_DOUBLE`), so an item that fails to convert, or the iterator's own exception, is raised
only if processing the items before it did not raise first (`OverflowError("intermediate
overflow in fsum")`, or `MemoryError` from `_fsum_realloc`). Non-finite items are summed apart
(`special_sum`, `inf_sum`, :1323-1335) and decide the result: `ValueError("-inf + inf in fsum")`
when both infinities occur (:1347-1350), else a NaN when a NaN occurs, else the infinity.
-/

namespace PyLean.MathInt

open PyLean PyLean.Binary64 PyLean.Binary64.F64

/-- The step `math_fsum` folds over the items. -/
abbrev fsumF (st : FsumSt) (item : Arg) : Py FsumSt := do fsumStep st (← assignDouble item)

/-- The exceptions processing an item can raise. -/
def isStepErr (e : PyExc) : Bool :=
  e == .overflowError "intermediate overflow in fsum" || e == .named "MemoryError" "math.fsum partials"

/-- `math.fsum`'s failure and special-value paths.

* the iterator's exception is raised after the items, unless processing them raised first;
* an item whose conversion raises is raised likewise, after the items before it;
* for floats with a non-finite item, unless a partial sum of the finite items overflows (or the
  partials cannot grow): `ValueError('-inf + inf in fsum')` when both infinities occur, else a
  NaN when a NaN occurs, else the infinity that occurs. -/
def FsumPaths : Prop :=
  (∀ (xs : List F64) (e : PyExc), math_fsum ⟨xs.map .float, some e⟩ =
    match math_fsum ⟨xs.map .float, none⟩ with
    | .error e' => if isStepErr e' then .error e' else .error e
    | .ok _ => .error e) ∧
  (∀ (xs : List F64) (o : Arg) (rest : List Arg) (err : Option PyExc) (ex : PyExc),
    asDouble o = .error ex →
    math_fsum ⟨xs.map .float ++ o :: rest, err⟩ =
      match math_fsum ⟨xs.map .float, none⟩ with
      | .error e' => if isStepErr e' then .error e' else .error ex
      | .ok _ => .error ex) ∧
  (∀ xs : List F64, xs.any (fun x => !x.isFinite) = true →
    (∃ e, math_fsum ⟨xs.map .float, none⟩ = .error e ∧ isStepErr e = true) ∨
    math_fsum ⟨xs.map .float, none⟩ =
      (if F64.inf false ∈ xs ∧ F64.inf true ∈ xs then .error (.valueError "-inf + inf in fsum")
       else if xs.any (·.isNaN) then .ok F64.qnan
       else if F64.inf false ∈ xs then .ok (F64.inf false) else .ok (F64.inf true)))

/-! ## Errors -/

theorem assignDouble_eq' (o : Arg) : assignDouble o = asDouble o := by cases o <;> rfl

theorem fsumStep_err {st : FsumSt} {x : F64} {e : PyExc} (h : fsumStep st x = .error e) :
    isStepErr e = true := by
  unfold fsumStep at h
  generalize fsumInner x st.p [] = r at h
  obtain ⟨x', ps⟩ := r
  simp only at h
  split at h
  · split at h
    · split at h
      · cases h; decide
      · cases h
    · split at h
      · split at h
        · cases h
        · cases h; decide
      · cases h
  · cases h

theorem fold_err : ∀ (xs : List F64) (st : FsumSt) (e : PyExc),
    (xs.map Arg.float).foldlM fsumF st = .error e → isStepErr e = true := by
  intro xs
  induction xs with
  | nil => intro st e h; cases h
  | cons x xs ih =>
    intro st e h
    simp only [List.map_cons, List.foldlM_cons, fsumF, assignDouble, bind, Except.bind] at h
    cases hs : fsumStep st x with
    | error e' => rw [hs] at h; cases h; exact fsumStep_err hs
    | ok st' => rw [hs] at h; exact ih st' e h

theorem fsumEnd_err {st : FsumSt} {e : PyExc} (h : fsumEnd st = .error e) :
    isStepErr e = false := by
  unfold fsumEnd at h
  by_cases h1 : isZeroC st.special_sum = true
  · simp only [h1, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    rcases hr : st.p.reverse with _ | ⟨top, rest⟩
    · rw [hr] at h; cases h
    · rw [hr] at h
      simp only at h
      generalize fsumTop rest top c0 = t at h
      obtain ⟨hi, lo, below⟩ := t
      simp only at h
      rcases below with _ | ⟨pn1, tl⟩
      · cases h
      · simp only at h
        split at h
        · split at h <;> cases h
        · cases h
  · simp only [Bool.not_eq_true] at h1
    simp only [h1, Bool.not_false, ↓reduceIte] at h
    split at h
    · cases h; decide
    · cases h

theorem math_fsum_eq (items : List Arg) (err : Option PyExc) :
    math_fsum ⟨items, err⟩ = (do
      let st ← items.foldlM fsumF {}
      let st ← (It.finish ⟨items, err⟩ st : Py FsumSt)
      fsumEnd st) := rfl

theorem fsum_tail (xs : List F64) (err : Option PyExc) (e : PyExc)
    (htail : ∀ st, (do let st ← (It.finish ⟨xs.map .float, err⟩ st : Py FsumSt); fsumEnd st) =
      .error e) :
    math_fsum ⟨xs.map .float, err⟩ =
      match math_fsum ⟨xs.map .float, none⟩ with
      | .error e' => if isStepErr e' then .error e' else .error e
      | .ok _ => .error e := by
  rw [math_fsum_eq, math_fsum_eq]
  cases hf : (xs.map Arg.float).foldlM fsumF {} with
  | error e' =>
    simp only [bind, Except.bind]
    simp only [fold_err xs {} e' hf, ↓reduceIte]
  | ok st =>
    have h1 := htail st
    simp only [bind, Except.bind] at h1 ⊢
    rw [h1]
    simp only [It.finish]
    cases hend : fsumEnd st with
    | ok v => rfl
    | error e' => simp only [fsumEnd_err hend, Bool.false_eq_true, ↓reduceIte]

/-! ## Non-finite items -/

/-- `special_sum` after the non-finite items seen so far, by which kinds occurred. -/
def specOf (p n nan : Bool) : F64 :=
  if nan || (p && n) then F64.qnan else if p then F64.inf false else if n then F64.inf true else c0

/-- `inf_sum` after the infinities seen so far. -/
def infOf (p n : Bool) : F64 :=
  if p && n then F64.qnan else if p then F64.inf false else if n then F64.inf true else c0

theorem lt_abs_nonfinite {x : F64} (hx : x.isFinite = false) (y : F64) :
    F64.lt (F64.abs x) (F64.abs y) = false := by
  rcases classify x with h | h | h
  · rw [hx] at h; cases h
  · have hai : (F64.abs x).isInf = true := by
      unfold isInf; rw [(abs_fields x).2.1, (abs_fields x).2.2]; exact h
    rw [eq_inf_of_isInf hai, (abs_fields x).1]
    unfold F64.lt
    have : (F64.inf false).isNaN = false ∧ (F64.inf false).isInf = true ∧
      (F64.inf false).sign = false := by decide +kernel
    simp [this]
  · have : (F64.abs x).isNaN = true := by rw [abs_isNaN]; exact h
    unfold F64.lt; simp [this]

theorem add_nonfinite {x : F64} (hx : x.isFinite = false) (y : F64) :
    (F64.add x y).isFinite = false := by
  unfold F64.add
  rcases classify x with h | h | h
  · rw [hx] at h; cases h
  · simp only [not_nan_of_inf h, h, Bool.false_or, ↓reduceIte]
    split
    · exact (by decide +kernel : F64.qnan.isFinite = false)
    · split
      · exact (by decide +kernel : F64.qnan.isFinite = false)
      · exact hx
  · simp only [h, Bool.true_or, ↓reduceIte]; decide +kernel

theorem fsumInner_nonfinite : ∀ (ps acc : List F64) (x : F64), x.isFinite = false →
    (fsumInner x ps acc).1.isFinite = false := by
  intro ps
  induction ps with
  | nil => intro acc x hx; exact hx
  | cons y ys ih =>
    intro acc x hx
    simp only [fsumInner, lt_abs_nonfinite hx, Bool.false_eq_true, ↓reduceIte]
    exact ih _ _ (add_nonfinite hx y)

theorem fsumStep_nonfinite (st : FsumSt) {x : F64} (hx : x.isFinite = false) :
    fsumStep st x =
      .ok { st with p := [], special_sum := F64.add st.special_sum x, inf_sum := (if x.isInf then F64.add st.inf_sum x else st.inf_sum) } := by
  have h1 := fsumInner_nonfinite st.p [] x hx
  unfold fsumStep
  generalize fsumInner x st.p [] = r at h1
  obtain ⟨x', ps⟩ := r
  simp only at h1
  have hz : isZeroC x' = false := by
    rw [isZeroC_eq]; cases h : x'.isZero
    · rfl
    · rw [isFinite_of_isZero h] at h1; cases h1
  simp [hz, h1, hx]

theorem fsumStep_finite {st st' : FsumSt} {x : F64} (hx : x.isFinite = true)
    (h : fsumStep st x = .ok st') :
    st'.special_sum = st.special_sum ∧ st'.inf_sum = st.inf_sum := by
  unfold fsumStep at h
  generalize fsumInner x st.p [] = r at h
  obtain ⟨x', ps⟩ := r
  simp only at h
  by_cases hz : isZeroC x' = true
  · simp only [hz, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h; cases h; exact ⟨rfl, rfl⟩
  · simp only [Bool.not_eq_true] at hz
    simp only [hz, Bool.not_false, ↓reduceIte] at h
    by_cases hf : x'.isFinite = true
    · simp only [hf, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      split at h
      · split at h
        · cases h; exact ⟨rfl, rfl⟩
        · cases h
      · cases h; exact ⟨rfl, rfl⟩
    · simp only [Bool.not_eq_true] at hf
      simp [hf, hx] at h

theorem spec_step (p n nan : Bool) {x : F64} (hx : x.isFinite = false) :
    F64.add (specOf p n nan) x =
      specOf (p || F64.inf false == x) (n || F64.inf true == x) (nan || x.isNaN) ∧
    (if x.isInf then F64.add (infOf p n) x else infOf p n) =
      infOf (p || F64.inf false == x) (n || F64.inf true == x) := by
  rcases classify x with h | h | h
  · rw [hx] at h; cases h
  · have hn := not_nan_of_inf h
    rw [eq_inf_of_isInf h]
    cases x.sign <;> cases p <;> cases n <;> cases nan <;> decide +kernel
  · have hi := not_inf_of_nan h
    have hne1 : (F64.inf false == x) = false := by
      cases hh : (F64.inf false == x)
      · rfl
      · have := beq_iff_eq.1 hh; subst this; exact absurd h (by decide +kernel)
    have hne2 : (F64.inf true == x) = false := by
      cases hh : (F64.inf true == x)
      · rfl
      · have := beq_iff_eq.1 hh; subst this; exact absurd h (by decide +kernel)
    simp only [hne1, hne2, h, hi, Bool.or_false, Bool.or_true, Bool.false_eq_true, ↓reduceIte,
      and_self]
    unfold F64.add specOf
    simp [h]

theorem fold_special : ∀ (xs : List F64) (st st' : FsumSt) (p n nan : Bool),
    st.special_sum = specOf p n nan → st.inf_sum = infOf p n →
    (xs.map Arg.float).foldlM fsumF st = .ok st' →
    st'.special_sum = specOf (p || xs.contains (F64.inf false)) (n || xs.contains (F64.inf true))
      (nan || xs.any (·.isNaN)) ∧
    st'.inf_sum = infOf (p || xs.contains (F64.inf false)) (n || xs.contains (F64.inf true)) := by
  intro xs
  induction xs with
  | nil => intro st st' p n nan h1 h2 h; cases h; simp [h1, h2]
  | cons x xs ih =>
    intro st st' p n nan h1 h2 h
    simp only [List.map_cons, List.foldlM_cons, fsumF, assignDouble, bind, Except.bind] at h
    cases hs : fsumStep st x with
    | error e => rw [hs] at h; cases h
    | ok st1 =>
      rw [hs] at h
      by_cases hx : x.isFinite = true
      · obtain ⟨e1, e2⟩ := fsumStep_finite hx hs
        have := ih st1 st' p n nan (by rw [e1, h1]) (by rw [e2, h2]) h
        have hne1 : (F64.inf false == x) = false := by
          cases hh : (F64.inf false == x)
          · rfl
          · have := beq_iff_eq.1 hh; subst this; exact absurd hx (by decide +kernel)
        have hne2 : (F64.inf true == x) = false := by
          cases hh : (F64.inf true == x)
          · rfl
          · have := beq_iff_eq.1 hh; subst this; exact absurd hx (by decide +kernel)
        simp only [List.contains_cons, List.any_cons, hne1, hne2, isNaN_false_of_finite hx,
          Bool.false_or]
        exact this
      · have hx' : x.isFinite = false := by simpa using hx
        rw [fsumStep_nonfinite st hx'] at hs
        cases hs
        obtain ⟨s1, s2⟩ := spec_step p n nan hx'
        have := ih _ st' (p || F64.inf false == x) (n || F64.inf true == x) (nan || x.isNaN)
          (by simp only [h1]; exact s1) (by simp only [h2]; exact s2) h
        simp only [List.contains_cons, List.any_cons, Bool.or_assoc] at this ⊢
        exact this

theorem specOf_nz (a b c : Bool) (h : (a || b || c) = true) : isZeroC (specOf a b c) = false := by
  cases a <;> cases b <;> cases c <;> first | decide +kernel | simp at h

theorem infOf_nan (a b : Bool) : (infOf a b).isNaN = (a && b) := by
  cases a <;> cases b <;> decide +kernel

theorem fsumPaths_proven : FsumPaths := by
  refine ⟨fun xs e => ?_, fun xs o rest err ex ho => ?_, fun xs hnf => ?_⟩
  · apply fsum_tail
    intro st; rfl
  · rw [math_fsum_eq, math_fsum_eq, List.foldlM_append]
    cases hf : (xs.map Arg.float).foldlM fsumF {} with
    | error e' =>
      simp only [bind, Except.bind]
      simp only [fold_err xs {} e' hf, ↓reduceIte]
    | ok st =>
      simp only [bind, Except.bind, List.foldlM_cons, fsumF, assignDouble_eq', ho]
      simp only [It.finish]
      cases hend : fsumEnd st with
      | ok v => rfl
      | error e' => simp only [fsumEnd_err hend, Bool.false_eq_true, ↓reduceIte]
  · rw [math_fsum_eq]
    cases hf : (xs.map Arg.float).foldlM fsumF {} with
    | error e' => left; exact ⟨e', by simp [bind, Except.bind, hf], fold_err xs {} e' hf⟩
    | ok st =>
      right
      obtain ⟨s1, s2⟩ := fold_special xs {} st false false false rfl rfl hf
      simp only [Bool.false_or] at s1 s2
      simp only [bind, Except.bind, It.finish]
      have hany : xs.contains (F64.inf false) = true ∨ xs.contains (F64.inf true) = true ∨
          xs.any (·.isNaN) = true := by
        obtain ⟨x, hxm, hxf⟩ := List.any_eq_true.1 hnf
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at hxf
        rcases classify x with h | h | h
        · rw [hxf] at h; cases h
        · rw [eq_inf_of_isInf h] at hxm
          cases hs : x.sign
          · left; rw [hs] at hxm; exact List.contains_iff_mem.2 hxm
          · right; left; rw [hs] at hxm; exact List.contains_iff_mem.2 hxm
        · right; right; exact List.any_eq_true.2 ⟨x, hxm, h⟩
      have c1 : (F64.inf false ∈ xs) = (xs.contains (F64.inf false) = true) := by
        rw [List.contains_iff_mem]
      have c2 : (F64.inf true ∈ xs) = (xs.contains (F64.inf true) = true) := by
        rw [List.contains_iff_mem]
      have hz := specOf_nz (xs.contains (F64.inf false)) (xs.contains (F64.inf true))
        (xs.any (·.isNaN)) (by rcases hany with h | h | h <;> simp only [h, Bool.true_or, Bool.or_true])
      unfold fsumEnd
      rw [s1, s2, hz, infOf_nan]; simp only [c1, c2]
      simp only [Bool.not_false, ↓reduceIte]
      revert hany
      cases xs.contains (F64.inf false) <;> cases xs.contains (F64.inf true) <;>
        cases xs.any (·.isNaN) <;> intro hany <;> simp [specOf] at hany ⊢

end PyLean.MathInt
