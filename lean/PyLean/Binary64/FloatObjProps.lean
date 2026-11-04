import PyLean.Binary64.FloatObj

/-!
Properties of the object-level float paths in `FloatObj.lean`. Each is stated for every
object, every slot result (exceptions included) and both settings of the warnings filter.
-/

namespace PyLean.Binary64

open PyLean F64

/-- The object is not a float of any value (`!PyFloat_Check`). -/
def NotFloat (o : FObj) : Prop := ∀ x, o.kind ≠ .float x

/-- The object is not an int of any value (`!PyLong_Check`). -/
def NotInt (o : FObj) : Prop := ∀ n, o.kind ≠ .int n

/-! ## `_PyNumber_Index` and `PyFloat_AsDouble` -/

/-- `_PyNumber_Index` (abstract.c:1410-1453) for every object and slot result: an int gives
its value; otherwise a NULL `nb_index` is `TypeError`, an exception from `__index__`
propagates, an exact int result is taken, a strict int subclass result raises the
`DeprecationWarning` when the filter makes it an error and is taken otherwise, and any
other result is `TypeError`. -/
def NumberIndexSpec : Prop :=
  ∀ (warnErr : Bool) (o : FObj),
    (∀ n, o.kind = .int n → numberIndex warnErr o = .ok n) ∧
    (NotInt o → o.nbIndex = none →
      numberIndex warnErr o = .error (.typeError s!"'{o.tp.take 200}' object cannot be interpreted as an integer")) ∧
    (∀ e, NotInt o → o.nbIndex = some (.error e) → numberIndex warnErr o = .error e) ∧
    (∀ res n, NotInt o → o.nbIndex = some (.ok res) → res.kind = .int n →
      numberIndex warnErr o =
        if res.exact then .ok n
        else if warnErr then .error (.named "DeprecationWarning" (deprecationMsgIndex o res)) else .ok n) ∧
    (∀ res, NotInt o → o.nbIndex = some (.ok res) → NotInt res →
      numberIndex warnErr o = .error (.typeError s!"{o.fq}.__index__() must return an int, not {res.fq}"))

/-- `_PyNumber_Index` past its `PyLong_Check`. -/
theorem numberIndex_notInt {w : Bool} {o : FObj} (hn : NotInt o) :
    numberIndex w o =
      match o.nbIndex with
      | none => .error (.typeError s!"'{o.tp.take 200}' object cannot be interpreted as an integer")
      | some (.error e) => .error e
      | some (.ok res) =>
        match res.kind with
        | .int n =>
          if res.exact then .ok n
          else if w then .error (.named "DeprecationWarning" (deprecationMsgIndex o res))
          else .ok n
        | _ => .error (.typeError s!"{o.fq}.__index__() must return an int, not {res.fq}") := by
  obtain ⟨id, k, ex, tp, fq, f, i⟩ := o
  cases k with
  | int m => exact absurd rfl (hn m)
  | _ => rfl

theorem numberIndexSpec_proven : NumberIndexSpec := by
  intro w o
  refine ⟨fun n h => ?_, fun hn h => ?_, fun e hn h => ?_, fun res n hn h hr => ?_, fun res hn h hr => ?_⟩
  · obtain ⟨id, k, ex, tp, fq, f, i⟩ := o
    simp only [FObj.kind] at h; subst h; rfl
  · rw [numberIndex_notInt hn, h]
  · rw [numberIndex_notInt hn, h]
  · rw [numberIndex_notInt hn, h]; simp only []; rw [hr]
  · rw [numberIndex_notInt hn, h]; simp only []
    generalize hk : res.kind = k at hr
    cases k with
    | int m => exact absurd hk (hr m)
    | _ => rfl

/-- `PyFloat_AsDouble` (floatobject.c:247-303) for every object and slot result. A float
(a subclass too, whatever its `__float__`) gives its value (:259-261). Otherwise: with a
NULL `nb_float`, an `nb_index` goes through `_PyNumber_Index` and `PyLong_AsDouble`
(:263-272), and with neither it is `TypeError` (:273-275); an exception from `__float__`
propagates (:278-281); an exact float result is taken, a strict float subclass result
raises the `DeprecationWarning` when the filter makes it an error (:290-297) and is taken
otherwise, and any other result is `TypeError` (:283-288). -/
def AsDoubleSpec : Prop :=
  ∀ (warnErr : Bool) (o : FObj),
    (∀ x, o.kind = .float x → asDoubleO warnErr o = .ok x) ∧
    (NotFloat o → o.nbFloat = none → o.nbIndex ≠ none →
      asDoubleO warnErr o = (numberIndex warnErr o).bind PyLong_AsDouble) ∧
    (NotFloat o → o.nbFloat = none → o.nbIndex = none →
      asDoubleO warnErr o = .error (.typeError s!"must be real number, not {o.tp.take 50}")) ∧
    (∀ e, NotFloat o → o.nbFloat = some (.error e) → asDoubleO warnErr o = .error e) ∧
    (∀ res x, NotFloat o → o.nbFloat = some (.ok res) → res.kind = .float x →
      asDoubleO warnErr o =
        if res.exact then .ok x
        else if warnErr then .error (.named "DeprecationWarning" (deprecationMsgFloat o res)) else .ok x) ∧
    (∀ res, NotFloat o → o.nbFloat = some (.ok res) → NotFloat res →
      asDoubleO warnErr o = .error (.typeError s!"{o.fq}.__float__() must return a float, not {res.fq}"))

/-- `PyFloat_AsDouble` past its `PyFloat_Check`. -/
theorem asDouble_notFloat {w : Bool} {o : FObj} (hn : NotFloat o) :
    asDoubleO w o =
      match o.nbFloat with
      | none =>
        match o.nbIndex with
        | some _ => (numberIndex w o).bind PyLong_AsDouble
        | none => .error (.typeError s!"must be real number, not {o.tp.take 50}")
      | some (.error e) => .error e
      | some (.ok res) =>
        match res.kind with
        | .float x =>
          if res.exact then .ok x
          else if w then .error (.named "DeprecationWarning" (deprecationMsgFloat o res))
          else .ok x
        | _ => .error (.typeError s!"{o.fq}.__float__() must return a float, not {res.fq}") := by
  obtain ⟨id, k, ex, tp, fq, f, i⟩ := o
  cases k with
  | float y => exact absurd rfl (hn y)
  | _ => rfl

theorem asDoubleSpec_proven : AsDoubleSpec := by
  intro w o
  refine ⟨fun x h => ?_, fun hn h hi => ?_, fun hn h hi => ?_, fun e hn h => ?_,
    fun res x hn h hr => ?_, fun res hn h hr => ?_⟩
  · obtain ⟨id, k, ex, tp, fq, f, i⟩ := o
    simp only [FObj.kind] at h; subst h; rfl
  · rw [asDouble_notFloat hn, h]
    simp only []
    cases hc : o.nbIndex with
    | none => exact absurd hc hi
    | some r => rfl
  · rw [asDouble_notFloat hn, h]; simp only []; rw [hi]
  · rw [asDouble_notFloat hn, h]
  · rw [asDouble_notFloat hn, h]; simp only []; rw [hr]
  · rw [asDouble_notFloat hn, h]; simp only []
    generalize hk : res.kind = k at hr
    cases k with
    | float y => exact absurd hk (hr y)
    | _ => rfl

/-- An object whose `__index__` returns `10**400` and that has no `__float__` makes
`PyFloat_AsDouble` raise `OverflowError`, from `PyLong_AsDouble`. -/
theorem asDouble_index_overflow (w : Bool) :
    asDoubleO w (.mk 5 .plain true "C" "m.C" none (some (.ok (.mk 6 (.int (10 ^ 400)) true "int" "int" none none)))) =
      .error (.overflowError "int too large to convert to float") := by
  cases w <;> decide +kernel

/-! ## `PyFloat_FromString` and `PyNumber_Float` -/

/-- `PyFloat_FromString`'s dispatch (floatobject.c:189-221): a str through the decimal and
space transform, bytes, bytearray and buffers as bytes, and `TypeError` for anything
else, which `float([])` reaches. -/
def FromStringDispatch : Prop :=
  ∀ o : FObj,
    (∀ cps, o.kind = .str cps → fromStringO o = PyFloat_FromString (.str cps)) ∧
    (∀ b, (o.kind = .bytes b ∨ o.kind = .bytearray b ∨ o.kind = .buffer b) →
      fromStringO o = PyFloat_FromString (.bytes b)) ∧
    ((o.kind = .plain ∨ (∃ x, o.kind = .float x) ∨ (∃ n, o.kind = .int n)) →
      fromStringO o = .error (.typeError
        s!"float() argument must be a string or a real number, not '{o.tp.take 200}'"))

theorem fromStringDispatch_proven : FromStringDispatch := by
  intro o
  obtain ⟨id, k, ex, tp, fq, f, i⟩ := o
  refine ⟨fun c h => ?_, fun b h => ?_, fun h => ?_⟩
  · simp only [FObj.kind] at h; subst h; rfl
  · simp only [FObj.kind] at h; rcases h with h | h | h <;> subst h <;> rfl
  · simp only [FObj.kind] at h
    rcases h with h | ⟨x, h⟩ | ⟨n, h⟩ <;> subst h <;> rfl

/-- `PyNumber_Float` (abstract.c:1602-1657) and `float_new_impl` (floatobject.c:1567-1585)
for `type == float`, every object and slot result. `float()` is a new `0.0`; an exact str
goes straight to `PyFloat_FromString`; an exact float is returned itself. Anything else
asks its `nb_float` first, so a float or str subclass overriding `__float__` gets its
override: an exception propagates, an exact float result is returned as that object, a
strict float subclass result raises the `DeprecationWarning` under an error filter and is
copied into a new float otherwise, and any other result is `TypeError`. With a NULL
`nb_float`, `nb_index` is used through `PyLong_AsDouble`; with neither, a float subclass
gives a new float of its value and anything else goes to `PyFloat_FromString`. -/
def FloatNewSpec : Prop :=
  ∀ (warnErr : Bool) (o : FObj),
    floatNew warnErr none none = .ok (.fresh d0) ∧
    (∀ cps, o.kind = .str cps → o.exact = true →
      floatNew warnErr none (some o) = (PyFloat_FromString (.str cps)).map .fresh) ∧
    (∀ x, o.kind = .float x → o.exact = true → floatNew warnErr none (some o) = .ok (.same x)) ∧
    (∀ e, o.isExactFloat = false → (∀ cps, o.kind = .str cps → o.exact = false) →
      o.nbFloat = some (.error e) → floatNew warnErr none (some o) = .error e) ∧
    (∀ res x, o.isExactFloat = false → (∀ cps, o.kind = .str cps → o.exact = false) →
      o.nbFloat = some (.ok res) → res.kind = .float x →
      floatNew warnErr none (some o) =
        if res.exact then .ok (.obj res x)
        else if warnErr then .error (.named "DeprecationWarning" (deprecationMsgFloat o res))
        else .ok (.fresh x)) ∧
    (∀ res, o.isExactFloat = false → (∀ cps, o.kind = .str cps → o.exact = false) →
      o.nbFloat = some (.ok res) → NotFloat res →
      floatNew warnErr none (some o) =
        .error (.typeError s!"{o.fq}.__float__() must return a float, not {res.fq}")) ∧
    (o.isExactFloat = false → (∀ cps, o.kind = .str cps → o.exact = false) →
      o.nbFloat = none → o.nbIndex ≠ none →
      floatNew warnErr none (some o) =
        ((numberIndex warnErr o).bind PyLong_AsDouble).map .fresh) ∧
    (∀ x, o.kind = .float x → o.exact = false → o.nbFloat = none → o.nbIndex = none →
      floatNew warnErr none (some o) = .ok (.fresh x)) ∧
    (NotFloat o → (∀ cps, o.kind = .str cps → o.exact = false) →
      o.nbFloat = none → o.nbIndex = none →
      floatNew warnErr none (some o) = (fromStringO o).map .fresh)

/-- `PyNumber_Float` past its `PyFloat_CheckExact`. -/
theorem numberFloat_notExact {w : Bool} {o : FObj} (hx : o.isExactFloat = false) :
    numberFloat w o =
      match o.nbFloat with
      | some (.error e) => .error e
      | some (.ok res) =>
        match res.kind with
        | .float x =>
          if res.exact then .ok (.obj res x)
          else if w then .error (.named "DeprecationWarning" (deprecationMsgFloat o res))
          else .ok (.fresh x)
        | _ => .error (.typeError s!"{o.fq}.__float__() must return a float, not {res.fq}")
      | none =>
        match o.nbIndex with
        | some _ => ((numberIndex w o).bind PyLong_AsDouble).map .fresh
        | none =>
          match o.kind with
          | .float x => .ok (.fresh x)
          | _ => (fromStringO o).map .fresh := by
  obtain ⟨id, k, ex, tp, fq, f, i⟩ := o
  cases k with
  | float y =>
    cases ex with
    | true => simp [FObj.isExactFloat, FObj.kind, FObj.exact] at hx
    | false =>
      simp only [numberFloat, FObj.kind, FObj.exact, FObj.nbFloat, FObj.nbIndex]
      rcases f with _ | (_ | _) <;> rcases i with _ | (_ | _) <;> try rfl
      all_goals simp [bind, Except.bind, Except.map, pure, Except.pure]
      all_goals (split <;> rfl)
  | _ =>
    simp only [numberFloat, FObj.kind, FObj.exact, FObj.nbFloat, FObj.nbIndex]
    rcases f with _ | (_ | _) <;> rcases i with _ | (_ | _) <;> try rfl
    all_goals simp [bind, Except.bind, Except.map, pure, Except.pure]
    all_goals (split <;> rfl)

/-- `float_new_impl` for `float` itself, past its `PyUnicode_CheckExact`. -/
theorem floatNew_notStr {w : Bool} {o : FObj} (hs : ∀ cps, o.kind = .str cps → o.exact = false) :
    floatNew w none (some o) = numberFloat w o := by
  obtain ⟨id, k, ex, tp, fq, f, i⟩ := o
  cases k with
  | str c =>
    have := hs c rfl
    simp only [FObj.exact] at this
    subst this; rfl
  | _ => rfl

theorem floatNewSpec_proven : FloatNewSpec := by
  intro w o
  refine ⟨rfl, fun c hk he => ?_, fun x hk he => ?_, fun e hx hs h => ?_, fun res x hx hs h hr => ?_,
    fun res hx hs h hr => ?_, fun hx hs h hi => ?_, fun x hk he h hi => ?_, fun hx hs h hi => ?_⟩
  · obtain ⟨id, k, ex, tp, fq, f, i⟩ := o
    simp only [FObj.kind, FObj.exact] at hk he; subst hk; subst he; rfl
  · obtain ⟨id, k, ex, tp, fq, f, i⟩ := o
    simp only [FObj.kind, FObj.exact] at hk he; subst hk; subst he; rfl
  · rw [floatNew_notStr hs, numberFloat_notExact hx, h]
  · rw [floatNew_notStr hs, numberFloat_notExact hx, h]; simp only []; rw [hr]
  · rw [floatNew_notStr hs, numberFloat_notExact hx, h]; simp only []
    generalize hk : res.kind = k at hr
    cases k with
    | float y => exact absurd hk (hr y)
    | _ => rfl
  · rw [floatNew_notStr hs, numberFloat_notExact hx, h]; simp only []
    cases hc : o.nbIndex with
    | none => exact absurd hc hi
    | some r => rfl
  · have hx : o.isExactFloat = false := by simp [FObj.isExactFloat, hk, he]
    have hs : ∀ cps, o.kind = .str cps → o.exact = false := by intro c hc; rw [hk] at hc; cases hc
    rw [floatNew_notStr hs, numberFloat_notExact hx, h]; simp only []; rw [hi]; simp only []; rw [hk]
  · have hx' : o.isExactFloat = false := by
      unfold FObj.isExactFloat
      generalize hk : o.kind = k
      cases k with
      | float y => exact absurd hk (hx y)
      | _ => rfl
    rw [floatNew_notStr hs, numberFloat_notExact hx', h]; simp only []; rw [hi]; simp only []
    generalize hk : o.kind = k
    cases k with
    | float y => exact absurd hk (hx y)
    | _ => rfl

/-! ## Subclasses, `vectorcall`, `from_number` -/

/-- `float_subtype_new` (floatobject.c:1593-1610) and the subclass branch of `float_new_impl`
(:1573-1578): `F(x)` first makes `float(x)` exactly as `float` would, so its exceptions
propagate unchanged, and then returns a new `F` instance holding that value; `F()` holds
`float(0)`, which is `0.0`. -/
def FloatSubtypeNewSpec : Prop :=
  ∀ (warnErr : Bool) (c : FCls) (x : FObj),
    floatNew warnErr (some c) (some x) =
      (floatNew warnErr none (some x)).map (fun r => .freshSub c.name r.floatVal) ∧
    (∀ e, floatNew warnErr none (some x) = .error e → floatNew warnErr (some c) (some x) = .error e) ∧
    (∀ r, floatNew warnErr none (some x) = .ok r →
      floatNew warnErr (some c) (some x) = .ok (.freshSub c.name r.floatVal)) ∧
    floatNew warnErr (some c) none = .ok (.freshSub c.name d0)

theorem floatSubtypeNewSpec_proven : FloatSubtypeNewSpec := by
  intro w c x
  have e : floatNew w (some c) (some x) =
      (floatNew w none (some x)).map (fun r => .freshSub c.name r.floatVal) := by
    show floatSubtypeNew w c x = _
    unfold floatSubtypeNew
    simp only [floatNew]
    cases floatNewExact w (some x) <;> rfl
  refine ⟨e, fun err h => by rw [e, h]; rfl, fun r h => by rw [e, h]; rfl, ?_⟩
  cases w <;> rfl

/-- `float_vectorcall` (floatobject.c:1613-1627): any keyword argument is `TypeError` before
the arguments are looked at (`_PyArg_NoKwnames`), more than one positional argument is
`TypeError`, and otherwise it is `float_new_impl` with the one argument or none. -/
def FloatVectorcallSpec : Prop :=
  ∀ (warnErr : Bool) (cls : Option FCls) (args : List FObj) (kwnames : List String),
    (kwnames ≠ [] → floatVectorcall warnErr cls args kwnames =
      .error (.typeError "float() takes no keyword arguments")) ∧
    (kwnames = [] → 1 < args.length → floatVectorcall warnErr cls args kwnames =
      .error (.typeError s!"float expected at most 1 argument, got {args.length}")) ∧
    floatVectorcall warnErr cls [] [] = floatNew warnErr cls none ∧
    (∀ x, floatVectorcall warnErr cls [x] [] = floatNew warnErr cls (some x))

theorem floatVectorcallSpec_proven : FloatVectorcallSpec := by
  intro w cls args kw
  refine ⟨fun h => by simp [floatVectorcall, h], fun h hl => ?_, rfl, fun _ => rfl⟩
  subst h
  match args, hl with
  | _ :: _ :: _, _ => simp [floatVectorcall]

/-- `float_from_number_impl` (floatobject.c:1641-1657): an exact float with `cls = float` is
returned itself (:1644-1647); a float subclass instance gives a new float of its value,
without its `__float__`; anything else goes through `PyFloat_AsDouble`, whose exceptions
propagate, so a str is `TypeError`; and a subclass `cls` gets `cls(result)` called, whose
result is returned as it is, `__new__` overrides included (:1653-1655). -/
def FloatFromNumberSpec : Prop :=
  ∀ (warnErr : Bool) (cls : Option FCls) (o : FObj),
    (∀ x, o.kind = .float x → o.exact = true → floatFromNumber warnErr none o = .ok (.same x)) ∧
    (∀ x, o.kind = .float x → o.exact = false → floatFromNumber warnErr none o = .ok (.fresh x)) ∧
    (NotFloat o → floatFromNumber warnErr none o = (asDoubleO warnErr o).map .fresh) ∧
    (∀ c : FCls, floatFromNumber warnErr (some c) o =
      (asDoubleO warnErr o).bind fun x => (c.call x).map .called) ∧
    (∀ cps, o.kind = .str cps → floatFromNumber warnErr cls o =
      .error (.typeError s!"must be real number, not {o.tp.take 50}") ∨ o.nbFloat ≠ none ∨ o.nbIndex ≠ none)

theorem floatFromNumberSpec_proven : FloatFromNumberSpec := by
  intro w cls o
  obtain ⟨id, k, ex, tp, fq, f, i⟩ := o
  refine ⟨fun x hk he => ?_, fun x hk he => ?_, fun hn => ?_, fun c => ?_, fun cps hk => ?_⟩
  · simp only [FObj.kind, FObj.exact] at hk he; subst hk; subst he; rfl
  · simp only [FObj.kind, FObj.exact] at hk he; subst hk; subst he; rfl
  · cases k with
    | float y => exact absurd rfl (hn y)
    | _ =>
      simp only [floatFromNumber, FObj.kind]
      cases asDoubleO w _ <;> rfl
  · have h1 : floatFromNumber w (some c) (.mk id k ex tp fq f i) =
        (asDoubleO w (.mk id k ex tp fq f i)) >>= fun x => (c.call x) >>= fun r => pure (.called r) := by
      cases k <;> rfl
    rw [h1]
    generalize asDoubleO w (FObj.mk id k ex tp fq f i) = r
    cases r with
    | error e => rfl
    | ok x =>
      show (c.call x >>= fun r => pure (FRes.called r)) = (c.call x).map FRes.called
      cases c.call x <;> rfl
  · simp only [FObj.kind] at hk; subst hk
    by_cases hf : f = none
    · by_cases hi : i = none
      · subst hf; subst hi; left
        cases cls <;> rfl
      · right; right; exact hi
    · right; left; exact hf

/-! ## `float_float`, `conjugate`, `real`, `__getnewargs__` -/

/-- Whether a result is the argument object itself. -/
def FRes.isSame : FRes → Bool
  | .same _ => true
  | _ => false

/-- `float_float` (floatobject.c:1069-1077), behind `__float__`, and `conjugate` and `real`,
which call it: the result is always an exact float with all 64 bits of `self` (a NaN keeps
its payload), and it is `self` itself exactly when `self` is an exact float; a subclass
instance gets a new exact float. -/
def FloatFloatSpec : Prop :=
  ∀ (x : F64) (exact : Bool),
    (∀ r ∈ [floatFloatO x exact, floatConjugateO x exact, floatGetrealO x exact],
      r.val = some x ∧ (r.isSame = true ↔ exact = true) ∧
      (exact = false → r = .fresh x))

theorem floatFloatSpec_proven : FloatFloatSpec := by
  intro x e r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> cases e <;> simp [floatFloatO, floatConjugateO, floatGetrealO,
    FRes.val, FRes.isSame]

/-- An exact float object of value `x`, with the slots `float` has. -/
def exactFloatObj (id : Nat) (x : F64) : FObj :=
  .mk id (.float x) true "float" "float" (some (.ok (.mk id (.float x) true "float" "float" none none))) none

/-- `float.__getnewargs__` (floatobject.c:1665-1669) is the 1-tuple `(x,)`, and pickling's
reconstruction `float(*x.__getnewargs__())` gives back all 64 bits of `x`, NaN payload
included, for every float and every identity the new float in the tuple gets. -/
def GetnewargsSpec : Prop :=
  ∀ (x : F64) (warnErr : Bool) (id : Nat),
    (floatGetnewargsO x).length = 1 ∧
    (floatGetnewargsO x).map (fun y => (floatNew warnErr none (some (exactFloatObj id y))).map FRes.floatVal) =
      [.ok x]

theorem getnewargsSpec_proven : GetnewargsSpec := fun _ _ _ => ⟨rfl, rfl⟩

/-! ## `float.fromhex` at the object level -/

theorem utf8Encode_ascii : ∀ (i : Nat) (cps : List Nat), (∀ c ∈ cps, c < 0x80) → utf8Encode i cps = .ok cps
  | _, [], _ => rfl
  | i, c :: cs, h => by
    have hc : c < 0x80 := h c (List.mem_cons_self ..)
    have ih := utf8Encode_ascii (i + 1) cs (fun d hd => h d (List.mem_cons_of_mem _ hd))
    simp [utf8Encode, utf8Cp, hc, ih]

/-- `float.fromhex` on any argument and class (floatobject.c:1225-1463): a non-str is
`TypeError` from `PyUnicode_AsUTF8AndSize` (:1280-1282), a str holding a surrogate is
`UnicodeEncodeError`, and otherwise its UTF-8 is parsed, parse and overflow errors
propagating before any class is called; `float.fromhex` gives a new float, and a subclass
`cls` gets `cls(x)` called, its result or exception returned as it is (:1444-1446). -/
def FloatFromhexObjSpec : Prop :=
  ∀ (cls : Option FCls) (o : FObj),
    ((∀ cps, o.kind ≠ .str cps) →
      floatFromhexO cls o = .error (.typeError "bad argument type for built-in operation")) ∧
    (∀ cps i, o.kind = .str cps → utf8Encode 0 cps = .error i →
      ∃ msg, floatFromhexO cls o = .error (.named "UnicodeEncodeError" msg)) ∧
    (∀ cps, o.kind = .str cps → (∀ c ∈ cps, c < 0x80) →
      floatFromhexO none o = (float_fromhex cps).map .fresh ∧
      ∀ c : FCls, floatFromhexO (some c) o = (float_fromhex cps).bind fun x => (c.call x).map .called)

theorem floatFromhexObjSpec_proven : FloatFromhexObjSpec := by
  intro cls o
  obtain ⟨id, k, ex, tp, fq, f, i⟩ := o
  refine ⟨fun h => ?_, fun cps j hk he => ?_, fun cps hk ha => ?_⟩
  · cases k with
    | str c => exact absurd rfl (h c)
    | _ => rfl
  · simp only [FObj.kind] at hk; subst hk
    exact ⟨_, by simp only [floatFromhexO, FObj.kind, he]; rfl⟩
  · simp only [FObj.kind] at hk; subst hk
    refine ⟨?_, fun c => ?_⟩
    · simp only [floatFromhexO, FObj.kind, utf8Encode_ascii 0 cps ha]
      cases float_fromhex cps <;> rfl
    · simp only [floatFromhexO, FObj.kind, utf8Encode_ascii 0 cps ha]
      cases float_fromhex cps <;> try rfl
      all_goals (simp [bind, Except.bind, Except.map, pure, Except.pure]; try (cases c.call _ <;> rfl))

/-! ## `round` -/

/-- `float.__round__` (floatobject.c:1024-1066) on every `ndigits` object: `None` rounds to
an int; otherwise `PyNumber_AsSsize_t` runs first, so a non-integer (`round(1.5, 'a')`), an
`__index__` that raises, returns a non-int, or returns an int subclass under an error
filter, raises before `x` is looked at; an int too large for `Py_ssize_t` is clipped, so a
huge positive `ndigits` returns `x` and a huge negative one a zero with the sign of `x`. -/
def FloatRoundObjSpec : Prop :=
  ∀ (warnErr : Bool) (x : F64) (o : FObj),
    floatRoundO warnErr x none = (float_round_int x).map .int ∧
    (∀ e, numberIndex warnErr o = .error e → floatRoundO warnErr x (some o) = .error e) ∧
    (∀ n, numberIndex warnErr o = .ok n →
      floatRoundO warnErr x (some o) = (float_round_ndigits x (clipSsize n)).map .float) ∧
    (∀ n, numberIndex warnErr o = .ok n → ssizeMax < n →
      floatRoundO warnErr x (some o) = .ok (.float x)) ∧
    (∀ n, numberIndex warnErr o = .ok n → n < ssizeMin → x.isFinite = true →
      floatRoundO warnErr x (some o) = .ok (.float (F64.mul d0 x)))

theorem clip_big {n : Int} (h : ssizeMax < n) : clipSsize n = ssizeMax := by
  unfold clipSsize ssizeMax ssizeMin at *; omega

theorem clip_small {n : Int} (h : n < ssizeMin) : clipSsize n = ssizeMin := by
  unfold clipSsize ssizeMax ssizeMin at *; omega

theorem floatRoundObjSpec_proven : FloatRoundObjSpec := by
  intro w x o
  have base : ∀ n, numberIndex w o = .ok n →
      floatRoundO w x (some o) = (float_round_ndigits x (clipSsize n)).map .float := by
    intro n h
    simp only [floatRoundO, numberAsSsize, h, bind, Except.bind, pure, Except.pure]
    cases float_round_ndigits x (clipSsize n) <;> rfl
  refine ⟨rfl, fun e h => ?_, base, fun n h hb => ?_, fun n h hs hf => ?_⟩
  · simp [floatRoundO, numberAsSsize, h, bind, Except.bind]
  · rw [base n h, clip_big hb]
    have hc : clipSsize ssizeMax = ssizeMax := by decide
    unfold float_round_ndigits
    rw [hc]
    by_cases hf : x.isFinite = true
    · simp [hf, ssizeMax]; rfl
    · simp [hf]; rfl
  · rw [base n h, clip_small hs]
    have hc : clipSsize ssizeMin = ssizeMin := by decide
    unfold float_round_ndigits
    rw [hc]
    simp [hf, ssizeMin]; rfl

/-- `round(1.5, 'a')`: `'str' object cannot be interpreted as an integer`. -/
theorem round_str_ndigits (w : Bool) (x : F64) :
    floatRoundO w x (some (.mk 7 (.str [97]) true "str" "str" none none)) =
      .error (.typeError "'str' object cannot be interpreted as an integer") := by
  cases w <;> rfl

end PyLean.Binary64
