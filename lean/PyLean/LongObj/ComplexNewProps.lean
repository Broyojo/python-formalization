import PyLean.LongObj.ComplexObjProps

/-!
Properties of the constructor paths: `try_complex_special_method`,
`actual_complex_new`, `complex_new_impl`, `complex_from_number_impl`.

These are about the order in which a user's methods run and which error wins, so
they hold over every `CDouble` instance. The state `s` is the log of earlier
events; a statement that the result carries `s` unchanged says no Python code ran
and nothing was warned about.
-/

namespace PyLean.LongObj.Cplx

open CDouble

section

variable {R : Type} [CDouble R]

theorem bind_pure_none {α : Type} (f : Option (Cx R) → M α) (s : List Ev) :
    (bind (pure none) f : M α) s = f none s := rfl

end

/-! ## `try_complex_special_method` -/

/-- The outcomes of `__complex__`, complexobject.c:505-535: absent, and nothing runs;
returning an exact complex, and its value is the result; returning a subclass instance,
which warns, and when the warning filter makes `DeprecationWarning` an error, that error is
the result (:524-531); returning anything else, which is the `TypeError` of :517-521, with
the call on the log. An exception from the method propagates. The inherited
`complex.__complex__` of a complex (or subclass) instance gives its value, with no Python
code run. -/
def TrySpecialOutcomes : Prop :=
  ∀ (R : Type) [CDouble R] (E : Env R) (op : Obj R) (s : List Ev),
    (op.dcomplex = .absent → try_complex_special_method E op s = .ok none s) ∧
    (∀ e, op.dcomplex = .raises e →
      try_complex_special_method E op s = .error e (Ev.call "__complex__" :: s)) ∧
    (∀ res c, op.dcomplex = .returns res → res.val = .cplx c → res.exact = true →
      try_complex_special_method E op s = .ok (some c) (Ev.call "__complex__" :: s)) ∧
    (∀ res c, op.dcomplex = .returns res → res.val = .cplx c → res.exact = false →
      E.warnErr = false →
      try_complex_special_method E op s =
        .ok (some c) (Ev.warn (s!"{op.ti.fqName}.__complex__() must return a complex, not {res.ti.fqName}.  " ++
          "The ability to return an instance of a strict subclass of complex " ++
          "is deprecated, and may be removed in a future version of Python.") ::
          Ev.call "__complex__" :: s)) ∧
    (∀ res c, op.dcomplex = .returns res → res.val = .cplx c → res.exact = false →
      E.warnErr = true →
      try_complex_special_method E op s =
        .error (.named "DeprecationWarning" (s!"{op.ti.fqName}.__complex__() must return a complex, not {res.ti.fqName}.  " ++
          "The ability to return an instance of a strict subclass of complex " ++
          "is deprecated, and may be removed in a future version of Python."))
          (Ev.call "__complex__" :: s)) ∧
    (∀ c, op.dcomplex = .builtin → op.val = .cplx c →
      try_complex_special_method E op s = .ok (some c) s) ∧
    (∀ res, op.dcomplex = .returns res → (∀ c, res.val ≠ .cplx c) →
      try_complex_special_method E op s =
        .error (.typeError s!"{op.ti.fqName}.__complex__() must return a complex, not {res.ti.fqName}")
          (Ev.call "__complex__" :: s))

theorem try_special_returns {R : Type} [CDouble R] (E : Env R) (op res : Obj R) (s : List Ev)
    (h : op.dcomplex = .returns res) :
    try_complex_special_method E op s = complexResult E op res (Ev.call "__complex__" :: s) := by
  simp only [try_complex_special_method, h]
  rfl

theorem trySpecialOutcomes_proven : TrySpecialOutcomes := by
  intro R _ E op s
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    rw [try_special_absent E op h]
    rfl
  · intro e h
    simp only [try_complex_special_method, h]
    rfl
  · intro res c h1 h2 h3
    rw [try_special_returns E op res s h1]
    simp only [complexResult, h2, h3, ite_true]
    rfl
  · intro res c h1 h2 h3 hw
    rw [try_special_returns E op res s h1]
    simp only [complexResult, h2, h3, Bool.false_eq_true, ite_false, warnDep, hw]
    rfl
  · intro res c h1 h2 h3 hw
    rw [try_special_returns E op res s h1]
    simp only [complexResult, h2, h3, Bool.false_eq_true, ite_false, warnDep, hw, ite_true]
    rfl
  · intro c h1 h2
    cases op with
    | mk ti ex val dc nf ni =>
      simp only [Obj.dcomplex, Obj.val] at h1 h2
      subst h1 h2
      cases ex <;> rfl
  · intro res h1 h2
    rw [try_special_returns E op res s h1]
    unfold complexResult
    cases hv : res.val with
    | cplx c => exact absurd hv (h2 c)
    | flt _ => rfl
    | long _ => rfl
    | str _ _ => rfl
    | none => rfl
    | other => rfl

theorem complexResult_not_none {R : Type} [CDouble R] (E : Env R) (op res : Obj R) (s s' : List Ev) :
    complexResult E op res s ≠ .ok none s' := by
  unfold complexResult
  cases hv : res.val
  case cplx c =>
    cases he : res.exact
    · simp only [Bool.false_eq_true, ite_false, warnDep]
      cases hw : E.warnErr
      · simp only [Bool.false_eq_true, ite_false]
        intro h
        cases h
      · simp only [ite_true]
        intro h
        cases h
    · simp only [ite_true]
      intro h
      cases h
  all_goals (intro h; cases h)

theorem try_special_not_none {R : Type} [CDouble R] (E : Env R) (op : Obj R) (s s' : List Ev)
    (h : op.dcomplex ≠ .absent) :
    try_complex_special_method E op s ≠ .ok none s' := by
  unfold try_complex_special_method
  cases hd : op.dcomplex with
  | absent => exact absurd hd h
  | builtin =>
    simp only [bind, EStateM.bind]
    cases hc : callSlot "__complex__" Slot.builtin op s with
    | error e s₂ => intro h'; cases h'
    | ok o s₂ => exact complexResult_not_none E op o s₂ s'
  | raises e => intro h'; cases h'
  | returns o => exact complexResult_not_none E op o _ s'

/-! ## `complex_new_impl` check order -/

/-- `realNumberLike`, unfolded: the test of lines 1216-1217 and 1229-1230. -/
theorem realNumberLike_false_iff {R : Type} [CDouble R] (o : Obj R) :
    realNumberLike o = false ↔
      (o.ti.hasNumber = false ∨
        (o.nbFloat.isAbsent = true ∧ o.nbIndex.isAbsent = true ∧ o.isComplex = false)) := by
  simp only [realNumberLike]
  cases h1 : o.ti.hasNumber <;> cases h2 : o.nbFloat.isAbsent <;>
    cases h3 : o.nbIndex.isAbsent <;> cases h4 : o.isComplex <;> simp

/-- The `real` argument is checked first. With no `__complex__` on it, a `real`
that is not a number raises its `TypeError` whatever `imag` is, before either
argument is converted, with no Python code having run. -/
def NewChecksRealFirst : Prop :=
  ∀ (R : Type) [CDouble R] (E : Env R) (t : TyArg) (r : Obj R) (i? : Option (Obj R))
    (s : List Ev),
    r.dcomplex = .absent → realNumberLike r = false →
      complex_new_impl E t (some r) i? s =
        .error (.typeError
          s!"complex() argument 'real' must be a real number, not {r.ti.fqName}") s

theorem newChecksRealFirst_proven : NewChecksRealFirst := by
  intro R _ E t r i? s h1 h2
  have htry := try_special_absent E r h1
  simp only [complex_new_impl, Option.getD, bind, EStateM.bind]
  rw [htry]
  simp only [pure, EStateM.pure, h2, Bool.not_false, ite_true]
  rfl

/-- Then `imag` is checked, still before anything converts: a `real` that passes
and an `imag` that does not raises the `imag` `TypeError`, and no `__float__` or
`__index__` of either argument has run. -/
def NewChecksImagBeforeConverting : Prop :=
  ∀ (R : Type) [CDouble R] (E : Env R) (t : TyArg) (r i : Obj R) (s : List Ev),
    r.dcomplex = .absent → realNumberLike r = true → realNumberLike i = false →
      complex_new_impl E t (some r) (some i) s =
        .error (.typeError
          s!"complex() argument 'imag' must be a real number, not {i.ti.fqName}") s

theorem newChecksImagBeforeConverting_proven : NewChecksImagBeforeConverting := by
  intro R _ E t r i s h1 h2 h3
  have htry := try_special_absent E r h1
  simp only [complex_new_impl, Option.getD, bind, EStateM.bind]
  rw [htry]
  simp only [pure, EStateM.pure, h2, h3, Bool.not_true, Bool.not_false, Bool.false_eq_true,
    ite_false, ite_true]
  rfl

/-- `PyNumber_Float` and `PyFloat_AsDouble` are the same computation, except on a
`float` subclass whose `nb_float` is not the inherited one. -/
theorem numberFloat_eq_asDouble {R : Type} [CDouble R] (E : Env R) (o : Obj R)
    (hn : realNumberLike o = true) (hc : o.isComplex = false)
    (hf : ∀ x, o.val = .flt x → o.exact = false → o.nbFloat = .builtin) :
    PyNumber_Float E o = PyFloat_AsDouble E o := by
  have hs : o.ti.hasNumber = true ∧ (o.nbFloat.isAbsent = false ∨ o.nbIndex.isAbsent = false) := by
    simp only [realNumberLike, hc, Bool.or_false, Bool.and_eq_true, Bool.or_eq_true,
      Bool.not_eq_true'] at hn
    exact hn
  obtain ⟨h1, h2⟩ := hs
  have key : ∀ (hv : ∀ x, o.val ≠ .flt x), PyNumber_Float E o = PyFloat_AsDouble E o := by
    intro hv
    have e1 : PyNumber_Float E o =
        (if o.ti.hasNumber && !o.nbFloat.isAbsent then
          (do
            let res ← callSlot "__float__" o.nbFloat o
            match res.val with
            | .flt x =>
              if res.exact then pure x
              else do
                warnDep E (nonFloatDep o res)
                pure x
            | _ => throw (.typeError (nonFloatMsg o res)))
        else if o.ti.hasNumber && !o.nbIndex.isAbsent then
          (do
            let res ← _PyNumber_Index E o
            liftPy (longAsDouble res))
        else throw (.typeError
          s!"float() argument must be a string or a real number, not '{pct 200 o.ti.tpName}'")) := by
      unfold PyNumber_Float
      cases hval : o.val with
      | flt x => exact absurd hval (hv x)
      | _ => rfl
    have e2 : PyFloat_AsDouble E o =
        (if !o.ti.hasNumber || o.nbFloat.isAbsent then
          (if o.ti.hasNumber && !o.nbIndex.isAbsent then
            (do
              let res ← _PyNumber_Index E o
              liftPy (longAsDouble res))
          else throw (.typeError s!"must be real number, not {pct 50 o.ti.tpName}"))
        else
          (do
            let res ← callSlot "__float__" o.nbFloat o
            match res.val with
            | .flt x =>
              if res.exact then pure x
              else do
                warnDep E (nonFloatDep o res)
                pure x
            | _ => throw (.typeError (nonFloatMsg o res)))) := by
      unfold PyFloat_AsDouble
      cases hval : o.val with
      | flt x => exact absurd hval (hv x)
      | _ => rfl
    rw [e1, e2, h1]
    cases hfa : o.nbFloat.isAbsent with
    | false => rfl
    | true =>
      have h3 : o.nbIndex.isAbsent = false := by
        rcases h2 with h | h
        · rw [hfa] at h; exact Bool.noConfusion h
        · exact h
      simp [h3]
  cases hv : o.val with
  | flt x =>
    cases he : o.exact with
    | true =>
      unfold PyNumber_Float PyFloat_AsDouble
      rw [hv, he]
    | false =>
      have hb := hf x hv he
      have hcall : callSlot "__float__" Slot.builtin o = pure (mkFloat x) := by
        simp only [callSlot, hv, he, Bool.false_eq_true, ite_false]
      unfold PyNumber_Float PyFloat_AsDouble
      rw [hv, he, hb, h1]
      simp only [Slot.isAbsent, Bool.not_false, Bool.and_self, ite_true]
      rw [hcall]
      rfl
  | cplx c => simp [Obj.isComplex, hv] at hc
  | long n => exact key (by simp [hv])
  | str t r => exact key (by simp [hv])
  | none => exact key (by simp [hv])
  | other => exact key (by simp [hv])

/-- The narrowing of `OneArgMatchesTwoArgOnFloats`: on any real-number object, not
a complex or a string, without `__complex__`, and not a `float` subclass that
overrides `__float__`, `complex(x)` and `complex(x, 0.0)` are the same
computation, including errors and the log. The excluded cases are on record: the
subclass in the refutation, and a complex or string, which the two forms treat
differently on purpose (deprecation, parsing). -/
def OneArgMatchesTwoArgNarrow : Prop :=
  ∀ (R : Type) [CDouble R] (E : Env R) (t : TyArg) (x : Obj R),
    x.dcomplex = .absent → realNumberLike x = true → x.isComplex = false →
    (∀ a b, x.val ≠ .str a b) → (∀ v, x.val = .flt v → x.exact = false → x.nbFloat = .builtin) →
    actual_complex_new E t [x] [] = actual_complex_new E t [x, mkFloat CDouble.zero] []

/-- `actual_complex_new` on one argument that is neither a string nor a complex
instance. -/
theorem actual_one_arg_body {R : Type} [CDouble R] (E : Env R) (t : TyArg) (x : Obj R)
    (h3 : x.isComplex = false) (h4 : ∀ a b, x.val ≠ .str a b) :
    actual_complex_new E t [x] [] = (do
      match ← try_complex_special_method E x with
      | some c => pure (complex_subtype_from_doubles t c.real c.imag)
      | none =>
        if x.isComplex then
          let c := cvalOf x
          pure (complex_subtype_from_doubles t c.real c.imag)
        else if x.ti.hasNumber && (!x.nbFloat.isAbsent || !x.nbIndex.isAbsent) then do
          let r ← PyFloat_AsDouble E x
          pure (complex_subtype_from_doubles t r CDouble.zero)
        else
          throw (.typeError
            s!"complex() argument must be a string or a number, not {x.ti.fqName}")) := by
  have hexact : x.isComplexExact = false := by simp [Obj.isComplexExact, h3]
  unfold actual_complex_new
  simp only [List.length_cons, List.length_nil, List.isEmpty_nil]
  have hg : (decide (0 + 1 > 1) || !true) = false := by decide
  simp only [hg, Bool.false_eq_true, ite_false, hexact, Bool.false_and]
  cases hv : x.val with
  | str a b => exact absurd hv (h4 a b)
  | _ => rfl

/-- `actual_complex_new` on one argument that is neither a string nor a complex and
has no `__complex__`. -/
theorem actual_one_arg {R : Type} [CDouble R] (E : Env R) (t : TyArg) (x : Obj R)
    (h1 : x.dcomplex = .absent) (h3 : x.isComplex = false) (h4 : ∀ a b, x.val ≠ .str a b)
    (hslots : (x.ti.hasNumber && (!x.nbFloat.isAbsent || !x.nbIndex.isAbsent)) = true) :
    actual_complex_new E t [x] [] =
      (do let r ← PyFloat_AsDouble E x; pure (complex_subtype_from_doubles t r CDouble.zero)) := by
  have htry := try_special_absent E x h1
  rw [actual_one_arg_body E t x h3 h4]
  funext s
  simp only [htry, bind, EStateM.bind, pure, EStateM.pure, h3, hslots, Bool.false_eq_true,
    ite_false, ite_true]

theorem asCComplex_body {R : Type} [CDouble R] (E : Env R) (x : Obj R)
    (h3 : x.isComplex = false) :
    PyComplex_AsCComplex E x = (do
      match ← try_complex_special_method E x with
      | some c => pure c
      | none =>
        let v ← PyFloat_AsDouble E x
        pure ⟨v, CDouble.zero⟩) := by
  unfold PyComplex_AsCComplex
  cases hv : x.val with
  | cplx c => simp [Obj.isComplex, hv] at h3
  | _ => rfl

theorem oneArgMatchesTwoArgNarrow_proven : OneArgMatchesTwoArgNarrow := by
  intro R _ E t x h1 h2 h3 h4 h5
  have hrun := numberFloat_eq_asDouble E x h2 h3 h5
  have hslots : (x.ti.hasNumber && (!x.nbFloat.isAbsent || !x.nbIndex.isAbsent)) = true := by
    simpa [realNumberLike, h3] using h2
  rw [actual_one_arg E t x h1 h3 h4 hslots]
  funext s
  have htry : try_complex_special_method E x s = .ok none s := by
    rw [try_special_absent E x h1]; rfl
  have hnl : realNumberLike (mkFloat (CDouble.zero : R)) = true := rfl
  have hto : actual_complex_new E t [x, mkFloat CDouble.zero] [] s =
      complex_new_impl E t (some x) (some (mkFloat CDouble.zero)) s := rfl
  rw [hto, ← hrun]
  simp only [complex_new_impl, Option.getD, bind, EStateM.bind, htry, pure, EStateM.pure, h2, hnl,
    Bool.not_true, Bool.false_eq_true, ite_false, h3]
  cases hf : PyNumber_Float E x s with
  | error e s₂ => simp [hf]
  | ok v s₂ =>
    simp only [hf]
    rfl

/-! ## `actual_complex_new` dispatch -/

/-- `complex()` is `0j`; `complex(z)` on an exact complex is `z` itself; a string
goes to the parser, before `__complex__` is looked at. -/
def NewDispatch : Prop :=
  ∀ (R : Type) [CDouble R] (E : Env R) (t : TyArg) (o : Obj R) (s : List Ev),
    actual_complex_new E t [] [] s = .ok ⟨t, ⟨CDouble.zero, CDouble.zero⟩, false⟩ s ∧
    (o.isComplexExact = true →
      actual_complex_new E .complex [o] [] s = .ok ⟨.complex, cvalOf o, true⟩ s) ∧
    (∀ a b, o.val = .str a b → o.isComplexExact = false →
      actual_complex_new E t [o] [] s = complex_subtype_from_string E t o s)

theorem newDispatch_proven : NewDispatch := by
  intro R _ E t o s
  refine ⟨rfl, ?_, ?_⟩
  · intro h
    simp only [actual_complex_new, List.length_cons, List.length_nil, List.isEmpty_nil]
    simp [h, pure, EStateM.pure]
  · intro a b h1 h2
    simp only [actual_complex_new, List.length_cons, List.length_nil, List.isEmpty_nil]
    simp [h1, h2]

/-- `complex_subtype_from_string` on a `str` is the parser's outcome, and its
`TypeError` branch fires on everything else. -/
def SubtypeFromString : Prop :=
  ∀ (R : Type) [CDouble R] (E : Env R) (t : TyArg) (v : Obj R) (s : List Ev),
    (∀ a b c, v.val = .str a b → complex_from_str E.db E.sd a b = .ok c →
      complex_subtype_from_string E t v s = .ok ⟨t, c, false⟩ s) ∧
    (∀ a b e, v.val = .str a b → complex_from_str E.db E.sd a b = .error e →
      complex_subtype_from_string E t v s = .error e s) ∧
    ((∀ a b, v.val ≠ .str a b) →
      complex_subtype_from_string E t v s =
        .error (.typeError
          s!"complex() argument must be a string or a number, not {v.ti.fqName}") s)

theorem subtypeFromString_proven : SubtypeFromString := by
  intro R _ E t v s
  refine ⟨?_, ?_, ?_⟩
  · intro a b c h1 h2
    simp only [complex_subtype_from_string, h1, h2]
    rfl
  · intro a b e h1 h2
    simp only [complex_subtype_from_string, h1, h2]
    rfl
  · intro h
    unfold complex_subtype_from_string
    cases hv : v.val with
    | str a b => exact absurd hv (h a b)
    | _ => rfl

/-! ## `complex.from_number` -/

/-- `complex.from_number(x)` is `complex(x)` on every number that is not a complex
or string instance: the exact complex, and any object with `__complex__`,
`__float__` or `__index__`. On an exact complex it returns `x` itself. A complex
subclass is left out, since `PyComplex_AsCComplex` reads its value directly while
`complex(x)` calls an overriding `__complex__`. -/
def FromNumberMatchesConstructor : Prop :=
  ∀ (R : Type) [CDouble R] (E : Env R) (x : Obj R),
    (x.isComplexExact = true →
      complex_from_number_impl E .complex x = actual_complex_new E .complex [x] []) ∧
    (x.isComplex = false → (∀ a b, x.val ≠ .str a b) →
      (x.dcomplex ≠ .absent ∨
        (x.ti.hasNumber = true ∧ (x.nbFloat.isAbsent = false ∨ x.nbIndex.isAbsent = false))) →
      ∀ s, mapRes Made.cval (complex_from_number_impl E .complex x s) =
        mapRes Made.cval (actual_complex_new E .complex [x] [] s))

theorem fromNumberMatchesConstructor_proven : FromNumberMatchesConstructor := by
  intro R _ E x
  constructor
  · intro h
    funext s
    simp only [complex_from_number_impl, actual_complex_new, List.length_cons, List.length_nil,
      List.isEmpty_nil]
    simp [h, pure, EStateM.pure]
  · intro h1 h2 h3 s
    have hexact : x.isComplexExact = false := by simp [Obj.isComplexExact, h1]
    have hne : (TyArg.complex != TyArg.complex) = false := by decide
    have hl : complex_from_number_impl E .complex x s =
        (do
          let cv ← PyComplex_AsCComplex E x
          pure (PyComplex_FromCComplex cv) : M (Made R)) s := by
      simp only [complex_from_number_impl, hexact, Bool.false_and, Bool.false_eq_true, ite_false,
        hne]
    rw [hl, actual_one_arg_body E .complex x h1 h2, asCComplex_body E x h1]
    simp only [bind, EStateM.bind, pure, EStateM.pure]
    cases ht : try_complex_special_method E x s with
    | error e s' => simp [mapRes]
    | ok a s' =>
      cases a with
      | some c =>
        simp [mapRes, EStateM.pure, PyComplex_FromCComplex, complex_subtype_from_doubles,
          complex_subtype_from_c_complex]
      | none =>
        have hslots : (x.ti.hasNumber && (!x.nbFloat.isAbsent || !x.nbIndex.isAbsent)) = true := by
          rcases h3 with h3 | ⟨h4, h5⟩
          · exact absurd ht (try_special_not_none E x s s' h3)
          · rcases h5 with h5 | h5 <;> simp [h4, h5]
        simp only [h1, hslots, Bool.false_eq_true, ite_false, ite_true]
        cases hf : PyFloat_AsDouble E x s' with
        | error e s₂ => simp [mapRes, EStateM.bind, EStateM.pure, hf]
        | ok v s₂ =>
          simp [mapRes, EStateM.bind, EStateM.pure, hf, PyComplex_FromCComplex,
            complex_subtype_from_doubles, complex_subtype_from_c_complex]

end PyLean.LongObj.Cplx
