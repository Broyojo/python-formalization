import PyLean.TypeObj.ExcPropsBase

/-!
Bound methods, builtin methods and method-wrappers as values: what binding produces, when two of
them are equal, that equal ones hash equal, and what `__reduce__` rebuilds.

The statements relate functions to each other (binding to comparison, comparison to hashing,
`__reduce__` to `getattr`, `types.MethodType` to `function.__get__`) instead of describing one
body. A hypothesis is one of: the case being described (`o` is not `None`), or the purity of a
callee's hash, which is what the data-model rule "equal objects hash equal" has to assume of the
function a method wraps.
-/

namespace PyLean.TypeObj

theorem genericHash_is {a b : Val} (h : a.is b = true) : genericHash a = genericHash b := by
  cases a <;> cases b <;>
    first
    | rfl
    | (simp [Val.is] at h; done)
    | (simp [Val.is] at h; subst h; rfl)

theorem payload_push_self (w : World) (o : Obj) :
    payloadOf { w with heap := w.heap.push (.val o) } (.obj w.heap.size) = some o.body := by
  simp [payloadOf, get_push_size]

theorem payload_push_old (w : World) (o : Obj) {a : Addr} (h : a < w.heap.size) :
    payloadOf { w with heap := w.heap.push (.val o) } (.obj a) = payloadOf w (.obj a) := by
  simp [payloadOf, get_push_lt w _ h]

/-- The objects of two successive allocations, in the second world. -/
theorem two_allocs (w : World) (o1 o2 : Obj) :
    let w1 : World := { w with heap := w.heap.push (.val o1) }
    let w2 : World := { w1 with heap := w1.heap.push (.val o2) }
    payloadOf w2 (.obj w.heap.size) = some o1.body ∧
      payloadOf w2 (.obj (w.heap.size + 1)) = some o2.body := by
  intro w1 w2
  constructor
  · have hlt : w.heap.size < w1.heap.size := by simp [w1]
    show payloadOf { w1 with heap := w1.heap.push (.val o2) } (.obj w.heap.size) = _
    rw [payload_push_old w1 o2 hlt]
    exact payload_push_self w o1
  · have h := payload_push_self w1 o2
    simpa only [w1, Array.size_push] using h

theorem funcDescrGet_bound (f o : Val) (w : World) (ho : o ≠ .none) :
    funcDescrGet f (some o) w = .ok (.obj w.heap.size)
      { w with heap := w.heap.push (.val { cls := B.method, body := .bound f o }) } := by
  cases o with
  | none => exact absurd rfl ho
  | _ => simp [funcDescrGet, pyMethodNew, alloc_app]

theorem payload_push_mono (w : World) (o : Obj) {v : Val} {p : Payload}
    (h : payloadOf w v = some p) (hp : p ≠ .plain) :
    payloadOf { w with heap := w.heap.push (.val o) } v = some p := by
  cases v with
  | obj a =>
    by_cases ha : a < w.heap.size
    · rw [payload_push_old w o ha]; exact h
    · have hd : w.get a = default := by
        simp only [World.get]
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (Nat.le_of_not_lt ha)]
        rfl
      have hq : payloadOf w (.obj a) = some .plain := by
        simp only [payloadOf, hd]
        rfl
      rw [hq] at h
      cases h
      exact absurd rfl hp
  | _ => simp [payloadOf] at h

/-! ## Bound methods -/

/-- **Binding one function twice gives equal methods with equal hashes.** `a.f == a.f` although
each access makes a new object, `a.f != b.f` when `a is not b`, and the first holds of the hash
too. The function's hash is assumed pure, the second case is the same function bound to a
different object. -/
def BoundMethodEqualityByBinding : Prop :=
  ∀ (rt : Rt) (f o1 o2 m1 m2 : Val) (h : Int) (w w1 w2 : World), o1 ≠ .none → o2 ≠ .none →
    funcDescrGet f (some o1) w = .ok m1 w1 → funcDescrGet f (some o2) w1 = .ok m2 w2 →
    (∀ u, rt.hash f u = .ok h u) →
    methodRichcompare rt m1 m2 .eq w2 = .ok (.bool (o1.is o2)) w2 ∧
    methodRichcompare rt m1 m2 .ne w2 = .ok (.bool (!o1.is o2)) w2 ∧
    (o1.is o2 = true →
      ∃ r, callHash rt (.c .method) m1 w2 = .ok r w2 ∧ callHash rt (.c .method) m2 w2 = .ok r w2)

theorem boundMethodEqualityByBinding_proven : BoundMethodEqualityByBinding := by
  intro rt f o1 o2 m1 m2 h w w1 w2 h1 h2 hb1 hb2 hh
  rw [funcDescrGet_bound f o1 w h1] at hb1
  simp only [R.ok.injEq] at hb1
  obtain ⟨rfl, rfl⟩ := hb1
  rw [funcDescrGet_bound f o2 _ h2] at hb2
  simp only [R.ok.injEq] at hb2
  obtain ⟨rfl, rfl⟩ := hb2
  obtain ⟨p1, p2⟩ := two_allocs w { cls := B.method, body := .bound f o1 }
    { cls := B.method, body := .bound f o2 }
  simp only at p1 p2
  refine ⟨?_, ?_, ?_⟩
  · simp [methodRichcompare, p1, p2, richCompareBool, Val.is_refl]
  · simp [methodRichcompare, p1, p2, richCompareBool, Val.is_refl]
  · intro hi
    refine ⟨hashMix (genericHash o1) h, ?_, ?_⟩
    · simp [callHash, p1, hh]
    · simp [callHash, p2, hh, genericHash_is hi]

/-- **Equal methods hash equal, for any two functions that compare and hash equal.** The
data-model rule, for `method_richcompare` and `method_hash`. The comparison may run user code; the
payload of a method cannot change. -/
def BoundMethodEqualHashEqual : Prop :=
  ∀ (rt : Rt) (a b f1 f2 s1 s2 : Val) (h : Int) (w w1 : World),
    payloadOf w a = some (.bound f1 s1) → payloadOf w b = some (.bound f2 s2) →
    payloadOf w1 a = some (.bound f1 s1) → payloadOf w1 b = some (.bound f2 s2) →
    methodRichcompare rt a b .eq w = .ok (.bool true) w1 →
    (∀ u, rt.hash f1 u = .ok h u) → (∀ u, rt.hash f2 u = .ok h u) →
    ∃ r, callHash rt (.c .method) a w1 = .ok r w1 ∧ callHash rt (.c .method) b w1 = .ok r w1

theorem boundMethodEqualHashEqual_proven : BoundMethodEqualHashEqual := by
  intro rt a b f1 f2 s1 s2 h w w1 pa pb pa1 pb1 hc hf1 hf2
  simp only [methodRichcompare, M.bind_app, getW_app, pa, pb] at hc
  cases hb : richCompareBool rt f1 f2 .eq w with
  | err e w' => simp [hb] at hc
  | ok v w' =>
    simp [hb] at hc
    obtain ⟨⟨_, hi⟩, rfl⟩ := hc
    refine ⟨hashMix (genericHash s1) h, ?_, ?_⟩
    · simp [callHash, pa1, hf1]
    · simp [callHash, pb1, hf2, genericHash_is hi]

/-- **The comparison of methods.** A raising `__eq__` of `__func__` raises out of `==` and `!=`
even when the selves differ, because `__func__` is compared first; `!=` is the negation of `==`
with the same effects; and the orderings, or another operand of a different type, are
`NotImplemented`, with no user code run. -/
def MethodCompareProtocol : Prop :=
  ∀ (rt : Rt) (a b f1 f2 s1 s2 : Val) (w : World),
    payloadOf w a = some (.bound f1 s1) →
    ((∀ op, op ≠ CmpOp.eq → op ≠ CmpOp.ne → methodRichcompare rt a b op w = .ok .notImpl w) ∧
     (∀ op, (∀ f s, payloadOf w b ≠ some (.bound f s)) →
        methodRichcompare rt a b op w = .ok .notImpl w)) ∧
    (payloadOf w b = some (.bound f2 s2) →
      (∀ e w1, richCompareBool rt f1 f2 .eq w = .err e w1 →
        methodRichcompare rt a b .eq w = .err e w1 ∧ methodRichcompare rt a b .ne w = .err e w1) ∧
      (∀ x w1, methodRichcompare rt a b .eq w = .ok (.bool x) w1 →
        methodRichcompare rt a b .ne w = .ok (.bool (!x)) w1))

theorem methodCompareProtocol_proven : MethodCompareProtocol := by
  intro rt a b f1 f2 s1 s2 w pa
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro op h1 h2
    cases op <;> first | exact absurd rfl h1 | exact absurd rfl h2 | simp [methodRichcompare]
  · intro op hb
    cases hp : payloadOf w b with
    | none => cases op <;> simp [methodRichcompare, pa, hp]
    | some x =>
      cases x with
      | bound f s => exact absurd hp (hb f s)
      | _ => cases op <;> simp [methodRichcompare, pa, hp]
  · intro pb
    constructor
    · intro e w1 hr
      simp [methodRichcompare, pa, pb, hr]
    · intro x w1 hc
      simp only [methodRichcompare, M.bind_app, getW_app, pa, pb] at hc ⊢
      cases hb : richCompareBool rt f1 f2 .eq w with
      | err e w' => simp [hb] at hc
      | ok v w' =>
        simp [hb] at hc ⊢
        obtain ⟨hx, rfl⟩ := hc
        simp [← hx]

/-- **An unhashable `__func__` makes the method unhashable**, with the same exception and no
result. -/
def MethodHashPropagates : Prop :=
  ∀ (rt : Rt) (m f s : Val) (e : PyErr) (w w1 : World),
    payloadOf w m = some (.bound f s) → rt.hash f w = .err e w1 →
    callHash rt (.c .method) m w = .err e w1

theorem methodHashPropagates_proven : MethodHashPropagates := by
  intro rt m f s e w w1 p hh
  simp [callHash, p, hh]

/-- **`types.MethodType(f, x)` is `f.__get__(x)`**: the constructor and the descriptor build the
same object, when the constructor accepts. It refuses a non-callable, then `None`, where
`__get__` returns the function, as it does with no instance. -/
def MethodNewAgreesWithBinding : Prop :=
  ∀ (rt : Rt) (f x : Val) (w : World),
    (funcDescrGet f (some .none) w = .ok f w ∧ funcDescrGet f none w = .ok f w) ∧
    (excCallableCheck w f = true → x ≠ .none →
      callTpNew rt (.c .method) B.method [f, x] [] w = funcDescrGet f (some x) w) ∧
    (excCallableCheck w f = false →
      callTpNew rt (.c .method) B.method [f, x] [] w =
        (typeErr "first argument must be callable" : M Val) w) ∧
    (excCallableCheck w f = true →
      callTpNew rt (.c .method) B.method [f, .none] [] w =
        (typeErr "instance must not be None" : M Val) w)

theorem methodNewAgreesWithBinding_proven : MethodNewAgreesWithBinding := by
  intro rt f x w
  refine ⟨⟨rfl, rfl⟩, ?_, ?_, ?_⟩
  · intro hc hx
    rw [funcDescrGet_bound f x w hx]
    cases x with
    | none => exact absurd rfl hx
    | _ => simp [callTpNew, noKeywords, unpackTuple, hc, Val.is, alloc_app]
  · intro hc
    simp [callTpNew, noKeywords, unpackTuple, hc, typeErr, raiseC]
  · intro hc
    simp [callTpNew, noKeywords, unpackTuple, hc, Val.is, typeErr, raiseC]

/-! ## Builtin methods and method-wrappers -/

theorem descrCheck_ok {owner : Addr} {name : Name} {o : Val} {w w' : World} {u : Unit}
    (h : descrCheck owner name o w = .ok u w') :
    isSubtype w (typeOf w o) owner = true ∧ w' = w := by
  by_cases hs : isSubtype w (typeOf w o) owner = true
  · simp [descrCheck, hs] at h
    exact ⟨hs, h.symm⟩
  · have hs' : isSubtype w (typeOf w o) owner = false := by simpa using hs
    simp [descrCheck, hs', typeErr, raiseC] at h

theorem methodGet_ok {d : Val} {owner : Addr} {name : Name} {b : Builtin} {o m : Val}
    {w w' : World} (h : methodGet d owner name b (some o) w = .ok m w') :
    m = .obj w.heap.size ∧
      w' = { w with heap := w.heap.push (.val { cls := B.builtinFn, body := .builtin b (some o) }) } := by
  simp only [methodGet, M.bind_app] at h
  cases hc : descrCheck owner name o w with
  | err e w1 => simp [hc] at h
  | ok u w1 =>
    obtain ⟨_, rfl⟩ := descrCheck_ok hc
    simp only [hc, alloc_app] at h
    simp at h
    exact ⟨h.1.symm, h.2.symm⟩

theorem wrapperdescrGet_ok {d : Val} {owner : Addr} {name : Name} {o m : Val} {w w' : World}
    (h : wrapperdescrGet d owner name (some o) w = .ok m w') :
    m = .obj w.heap.size ∧
      w' = { w with heap := w.heap.push (.val { cls := B.methodWrapper, body := .methodWrapper d o }) } := by
  simp only [wrapperdescrGet, M.bind_app] at h
  cases hc : descrCheck owner name o w with
  | err e w1 => simp [hc] at h
  | ok u w1 =>
    obtain ⟨_, rfl⟩ := descrCheck_ok hc
    simp only [hc, alloc_app] at h
    simp at h
    exact ⟨h.1.symm, h.2.symm⟩

theorem optIs_some (a b : Val) :
    (match (some a : Option Val), (some b : Option Val) with
      | some x, some y => x.is y
      | none, none => true
      | _, _ => false) = a.is b := rfl

/-- **Two builtin methods are equal when they are the same C function on the same object**, and
then their hashes agree. `[].append == [].append` is false for two lists, true for one. -/
def CFunctionEqualityByBinding : Prop :=
  ∀ (rt : Rt) (d1 d2 o1 o2 m1 m2 : Val) (t1 t2 : Addr) (n1 n2 : Name) (b1 b2 : Builtin)
    (w w1 w2 : World),
    methodGet d1 t1 n1 b1 (some o1) w = .ok m1 w1 → methodGet d2 t2 n2 b2 (some o2) w1 = .ok m2 w2 →
    let eq := o1.is o2 && b1 == b2
    callRichcompareEq rt (.c .builtinFn) m1 m2 .eq w2 = .ok (.bool eq) w2 ∧
    callRichcompareEq rt (.c .builtinFn) m1 m2 .ne w2 = .ok (.bool (!eq)) w2 ∧
    (eq = true → ∃ r, callHash rt (.c .builtinFn) m1 w2 = .ok r w2 ∧
      callHash rt (.c .builtinFn) m2 w2 = .ok r w2)

theorem cFunctionEqualityByBinding_proven : CFunctionEqualityByBinding := by
  intro rt d1 d2 o1 o2 m1 m2 t1 t2 n1 n2 b1 b2 w w1 w2 h1 h2
  obtain ⟨rfl, rfl⟩ := methodGet_ok h1
  obtain ⟨rfl, rfl⟩ := methodGet_ok h2
  obtain ⟨p1, p2⟩ := two_allocs w { cls := B.builtinFn, body := .builtin b1 (some o1) }
    { cls := B.builtinFn, body := .builtin b2 (some o2) }
  simp only at p1 p2
  refine ⟨?_, ?_, ?_⟩
  · simp [callRichcompareEq, p1, p2]
  · simp [callRichcompareEq, p1, p2]
  · intro he
    simp only [Bool.and_eq_true, beq_iff_eq] at he
    obtain ⟨hi, rfl⟩ := he
    refine ⟨hashMix (genericHash o1) (strHash (toString (repr b1))), ?_, ?_⟩
    · simp [callHash, p1]
    · simp [callHash, p2, genericHash_is hi]

/-- **Two method-wrappers are equal when they wrap one descriptor on one object**, and then their
hashes agree. -/
def WrapperEqualityByBinding : Prop :=
  ∀ (rt : Rt) (d1 d2 o1 o2 m1 m2 : Val) (t1 t2 : Addr) (n1 n2 : Name) (w w1 w2 : World),
    wrapperdescrGet d1 t1 n1 (some o1) w = .ok m1 w1 →
    wrapperdescrGet d2 t2 n2 (some o2) w1 = .ok m2 w2 →
    let eq := d1.is d2 && o1.is o2
    callRichcompareEq rt (.c .methodWrapper) m1 m2 .eq w2 = .ok (.bool eq) w2 ∧
    callRichcompareEq rt (.c .methodWrapper) m1 m2 .ne w2 = .ok (.bool (!eq)) w2 ∧
    (eq = true → ∃ r, callHash rt (.c .methodWrapper) m1 w2 = .ok r w2 ∧
      callHash rt (.c .methodWrapper) m2 w2 = .ok r w2)

theorem wrapperEqualityByBinding_proven : WrapperEqualityByBinding := by
  intro rt d1 d2 o1 o2 m1 m2 t1 t2 n1 n2 w w1 w2 h1 h2
  obtain ⟨rfl, rfl⟩ := wrapperdescrGet_ok h1
  obtain ⟨rfl, rfl⟩ := wrapperdescrGet_ok h2
  obtain ⟨p1, p2⟩ := two_allocs w { cls := B.methodWrapper, body := .methodWrapper d1 o1 }
    { cls := B.methodWrapper, body := .methodWrapper d2 o2 }
  simp only at p1 p2
  refine ⟨?_, ?_, ?_⟩
  · simp [callRichcompareEq, p1, p2]
  · simp [callRichcompareEq, p1, p2]
  · intro he
    simp only [Bool.and_eq_true] at he
    refine ⟨hashMix (genericHash o1) (genericHash d1), ?_, ?_⟩
    · simp [callHash, p1]
    · simp [callHash, p2, genericHash_is he.1, genericHash_is he.2]

/-- **The four descriptors that bind agree on the guard**: with no instance each returns itself and
does nothing; given an instance of the wrong type, each raises the same `TypeError`, naming the
descriptor, its class and the instance's type. -/
def DescrGetsShareGuard : Prop :=
  ∀ (rt : Rt) (d : Val) (t : Addr) (n : Name) (b : Builtin) (o : Val) (w : World),
    (methodGet d t n b none w = .ok d w ∧ wrapperdescrGet d t n none w = .ok d w ∧
      memberGet rt d t n none w = .ok d w ∧ getsetDescrGet rt d t n none w = .ok d w) ∧
    (isSubtype w (typeOf w o) t = false →
      let e : M Val := typeErr s!"descriptor '{n}' for '{trunc 100 (tpName w t)}' objects doesn't apply to a '{trunc 100 (typeName w o)}' object"
      methodGet d t n b (some o) w = e w ∧ wrapperdescrGet d t n (some o) w = e w ∧
      memberGet rt d t n (some o) w = e w ∧ getsetDescrGet rt d t n (some o) w = e w)

theorem descrGetsShareGuard_proven : DescrGetsShareGuard := by
  intro rt d t n b o w
  refine ⟨⟨rfl, rfl, rfl, rfl⟩, ?_⟩
  intro hs
  have hc : descrCheck t n o w =
      (typeErr s!"descriptor '{n}' for '{trunc 100 (tpName w t)}' objects doesn't apply to a '{trunc 100 (typeName w o)}' object" : M Unit) w := by
    simp [descrCheck, hs]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [methodGet, wrapperdescrGet, memberGet, getsetDescrGet, hc, typeErr, raiseC]

/-! ## `__reduce__` -/

/-- `t` is `(getattr, (o, n))`: applying its first item to its second is `getattr(o, n)`. -/
def IsGetattrCall (rt : Rt) (w : World) (t o : Val) (n : Name) : Prop :=
  ∃ g b args, t = .tuple [g, .tuple args] ∧ payloadOf w g = some (.builtin b none) ∧
    callBuiltin rt b none args [] none w = rt.getAttr o n w

theorem reduceToGetattr_call (rt : Rt) (o : Val) (n : Name) (w : World) :
    ∃ t w', reduceToGetattr o (.str n) w = .ok t w' ∧ IsGetattrCall rt w' t o n := by
  refine ⟨.tuple [.obj w.heap.size, .tuple [o, .str n]],
    { w with heap := w.heap.push (.val { cls := B.builtinFn, body := .builtin .getattr none }) },
    by simp [reduceToGetattr, alloc_app], ?_⟩
  refine ⟨_, .getattr, [o, .str n], rfl, payload_push_self _ _, ?_⟩
  simp [callBuiltin, checkBuiltinArgs, builtinConv, attrName, strOf]

/-- **`__reduce__` of methods and descriptors rebuilds by `getattr`.** For a bound method, a builtin
method with a `__self__`, a method-wrapper and a descriptor, the result applied to itself is
`getattr` of the right object and name, so unpickling looks the callable up again. A builtin
with no `__self__` reduces to its bare name, and a `__func__` whose `__name__` raises makes
`__reduce__` raise. -/
def ReduceIsGetattr : Prop :=
  ∀ (rt : Rt) (w : World),
    (∀ m f s nm, payloadOf w m = some (.bound f s) →
      (∀ u, rt.getAttr f "__name__" u = .ok (.str nm) u) →
      ∃ t w', methodReduce rt m w = .ok t w' ∧ IsGetattrCall rt w' t s nm) ∧
    (∀ m f s e w1, payloadOf w m = some (.bound f s) → rt.getAttr f "__name__" w = .err e w1 →
      methodReduce rt m w = .err e w1) ∧
    (∀ m b x nm, payloadOf w m = some (.builtin b (some x)) → builtinName b = some nm →
      ∃ t w', methReduce m w = .ok t w' ∧ IsGetattrCall rt w' t x nm) ∧
    (∀ m b nm, payloadOf w m = some (.builtin b none) → builtinName b = some nm →
      methReduce m w = .ok (.str nm) w) ∧
    (∀ m d s o p g, payloadOf w m = some (.methodWrapper d s) →
      payloadOf w d = some (.wrapperDescr o p g) →
      ∃ t w', wrapperReduce m w = .ok t w' ∧ IsGetattrCall rt w' t s p.name) ∧
    (∀ d o nm, descrInfo w d = some (o, nm) →
      ∃ t w', descrReduce d w = .ok t w' ∧ IsGetattrCall rt w' t (.obj o) nm)

theorem reduceIsGetattr_proven : ReduceIsGetattr := by
  intro rt w
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m f s nm p hn
    obtain ⟨t, w', h, hc⟩ := reduceToGetattr_call rt s nm w
    exact ⟨t, w', by simp [methodReduce, p, hn, h], hc⟩
  · intro m f s e w1 p hn
    simp [methodReduce, p, hn]
  · intro m b x nm p hn
    obtain ⟨t, w', h, hc⟩ := reduceToGetattr_call rt x nm w
    exact ⟨t, w', by simp [methReduce, p, hn, h], hc⟩
  · intro m b nm p hn
    simp [methReduce, p, hn]
  · intro m d s o p g pm pd
    obtain ⟨t, w', h, hc⟩ := reduceToGetattr_call rt s p.name w
    exact ⟨t, w', by simp [wrapperReduce, pm, pd, h], hc⟩
  · intro d o nm hd
    obtain ⟨t, w', h, hc⟩ := reduceToGetattr_call rt (.obj o) nm w
    exact ⟨t, w', by simp [descrReduce, hd, h], hc⟩

/-! ## `classmethod` -/

/-- **The three ways to reach a classmethod bind the same thing.** `cm.__get__(o)`,
`cm.__get__(o, type(o))` and `cm.__get__(None, type(o))` build methods of one function on one
class, which compare equal. -/
def ClassmethodBindingsAgree : Prop :=
  ∀ (rt : Rt) (cm f o m1 m2 m3 : Val) (w w1 w2 w3 : World),
    payloadOf w cm = some (.classmethod f) →
    cmDescrGet cm (some o) none w = .ok m1 w1 →
    cmDescrGet cm (some o) (some (.obj (typeOf w o))) w1 = .ok m2 w2 →
    cmDescrGet cm none (some (.obj (typeOf w o))) w2 = .ok m3 w3 →
    methodRichcompare rt m1 m2 .eq w3 = .ok (.bool true) w3 ∧
    methodRichcompare rt m1 m3 .eq w3 = .ok (.bool true) w3 ∧
    methodRichcompare rt m2 m3 .eq w3 = .ok (.bool true) w3

theorem classmethodBindingsAgree_proven : ClassmethodBindingsAgree := by
  intro rt cm f o m1 m2 m3 w w1 w2 w3 pc h1 h2 h3
  have nb : ∀ a b : Val, Payload.bound a b ≠ .plain := by intro a b h; cases h
  simp only [cmDescrGet, M.bind_app, getW_app, pc, pyMethodNew, alloc_app] at h1
  simp only [R.ok.injEq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  have pc1 := payload_push_mono w { cls := B.method, body := .bound f (.obj (typeOf w o)) } pc
    (by intro h; cases h)
  simp only [cmDescrGet, M.bind_app, getW_app, pc1, pyMethodNew, alloc_app] at h2
  simp only [R.ok.injEq] at h2
  obtain ⟨rfl, rfl⟩ := h2
  have pc2 := payload_push_mono _ { cls := B.method, body := .bound f (.obj (typeOf w o)) } pc1
    (by intro h; cases h)
  simp only [cmDescrGet, M.bind_app, getW_app, pc2, pyMethodNew, alloc_app] at h3
  simp only [R.ok.injEq] at h3
  obtain ⟨rfl, rfl⟩ := h3
  have q0 := payload_push_self w { cls := B.method, body := .bound f (.obj (typeOf w o)) }
  have q1 := payload_push_self { w with heap := w.heap.push (.val { cls := B.method, body := .bound f (.obj (typeOf w o)) }) }
    { cls := B.method, body := .bound f (.obj (typeOf w o)) }
  have q2 := payload_push_self { w with heap := (w.heap.push (.val { cls := B.method, body := .bound f (.obj (typeOf w o)) })).push (.val { cls := B.method, body := .bound f (.obj (typeOf w o)) }) }
    { cls := B.method, body := .bound f (.obj (typeOf w o)) }
  have r0 := payload_push_mono _ { cls := B.method, body := .bound f (.obj (typeOf w o)) } q0 (nb _ _)
  have r0' := payload_push_mono _ { cls := B.method, body := .bound f (.obj (typeOf w o)) } r0 (nb _ _)
  have r1 := payload_push_mono _ { cls := B.method, body := .bound f (.obj (typeOf w o)) } q1 (nb _ _)
  simp only [Array.size_push] at r0' r1 q2
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [methodRichcompare, r0', r1, q2, richCompareBool, Val.is_refl]

end PyLean.TypeObj
