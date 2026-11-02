import PyLean.TypeObj.PropsMisc

/-!
More properties of `Objects/typeobject.c`: wrapper arity tables, `type_new` argument
handling, and joint inheritance of the comparison slots.
-/

namespace PyLean.TypeObj

/-- **Arity of the zero-argument wrappers.** `__len__`, `__bool__`, `__hash__`, `__next__`
called with arguments raise the exact `TypeError`. -/
def WrapperArity0 : Prop :=
  ∀ (rt : Rt) (p : SlotDef) (f : SlotFn) (self : Val) (args : List Val) (wr : WrapKind) (w : World),
    p.wrapper = some wr → wr ∈ [.len, .inquiry, .hash, .next] → args ≠ [] →
    wrapperApply rt p f self args [] w = (typeErr (argCountMsg 0 args.length) : M Val) w

theorem wrapperArity0_proven : WrapperArity0 := by
  intro rt p f self args wr w h1 h2 h3
  have hl : args.length ≠ 0 := by simpa using h3
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
  rcases h2 with rfl | rfl | rfl | rfl <;>
    simp [wrapperApply, h1, checkNumArgs, hl, typeErr, raiseC]

/-- **Arity of the one-argument wrappers.** Comparison methods, `__contains__`, `__delete__`,
`__delitem__`, `__delattr__`, called with another count raise the exact `TypeError`. -/
def WrapperArity1 : Prop :=
  ∀ (rt : Rt) (p : SlotDef) (f : SlotFn) (self : Val) (args : List Val) (op : CmpOp)
    (wr : WrapKind) (w : World),
    p.wrapper = some wr →
    wr ∈ [.richcmp op, .descrDelete, .sqDelitem, .objobj, .delitem, .binaryR, .indexArg, .sqItem] →
    args.length ≠ 1 →
    wrapperApply rt p f self args [] w = (typeErr (argCountMsg 1 args.length) : M Val) w

theorem wrapperArity1_proven : WrapperArity1 := by
  intro rt p f self args op wr w h1 h2 h3
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
  rcases h2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [wrapperApply, h1, checkNumArgs, h3, typeErr, raiseC]

/-- `wrap_ternaryfunc` and `wrap_ternaryfunc_r` accept one or two arguments,
`Objects/typeobject.c:9928`. -/
def WrapperArityPow : Prop :=
  ∀ (rt : Rt) (p : SlotDef) (f : SlotFn) (self : Val) (args : List Val) (wr : WrapKind) (w : World),
    p.wrapper = some wr → wr ∈ [.ternary, .ternaryR] → args.length ≠ 1 → args.length ≠ 2 →
    wrapperApply rt p f self args [] w =
      (typeErr s!"expected 1 or 2 arguments, got {args.length}" : M Val) w

theorem wrapperArityPow_proven : WrapperArityPow := by
  intro rt p f self args wr w h1 h2 h3 h4
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
  rcases h2 with rfl | rfl <;> simp [wrapperApply, h1, checkPowArgs, h3, h4, typeErr, raiseC]

/-- `wrap_init` returns `None` on success, `Objects/typeobject.c:10503`. -/
def WrapInitReturnsNone : Prop :=
  ∀ (rt : Rt) (p : SlotDef) (f : SlotFn) (self : Val) (args : List Val) (kw : Kw) (w w1 : World),
    p.wrapper = some .init → callTpInit rt f self args kw w = .ok () w1 →
    wrapperApply rt p f self args kw w = .ok .none w1

theorem wrapInitReturnsNone_proven : WrapInitReturnsNone := by
  intro rt p f self args kw w w1 h1 h2
  simp [wrapperApply, h1, h2]

/-- `wrap_lenfunc` returns the length as an int; `wrap_hashfunc` the hash. -/
def WrapLenHash : Prop :=
  ∀ (rt : Rt) (p : SlotDef) (f : SlotFn) (self : Val) (n : Int) (w w1 : World),
    (p.wrapper = some .len → callLen rt f self w = .ok n w1 →
      wrapperApply rt p f self [] [] w = .ok (.int n) w1) ∧
    (p.wrapper = some .hash → callHash rt f self w = .ok n w1 →
      wrapperApply rt p f self [] [] w = .ok (.int n) w1)

theorem wrapLenHash_proven : WrapLenHash := by
  intro rt p f self n w w1
  constructor
  · intro h1 h2; simp [wrapperApply, h1, checkNumArgs, h2]
  · intro h1 h2; simp [wrapperApply, h1, checkNumArgs, h2]

/-- `object.__eq__(a, b)` and friends apply the comparison slot with the wrapper's `op`:
`wrap_richcmpfunc`, `Objects/typeobject.c:10353`. -/
def WrapRichcmp : Prop :=
  ∀ (rt : Rt) (p : SlotDef) (f : SlotFn) (self other : Val) (op : CmpOp) (w : World),
    p.wrapper = some (.richcmp op) →
    wrapperApply rt p f self [other] [] w = callRichcompare rt f self other op w

theorem wrapRichcmp_proven : WrapRichcmp := by
  intro rt p f self other op w h
  simp [wrapperApply, h, checkNumArgs]

/-- `wrapperdescr_call`: the first argument must be an instance of the wrapper's class,
`Objects/descrobject.c:554`. -/
def WrapperDescrSelfChecked : Prop :=
  ∀ (rt : Rt) (o : Addr) (p : SlotDef) (f : SlotFn) (self : Val) (rest : List Val) (kw : Kw)
    (w : World),
    isSubtype w (typeOf w self) o = false →
    wrapperdescrCall rt o p f (self :: rest) kw w =
      (typeErr s!"descriptor '{p.name}' requires a '{trunc 100 (tpName w o)}' object but received a '{trunc 100 (typeName w self)}'" : M Val) w

theorem wrapperDescrSelfChecked_proven : WrapperDescrSelfChecked := by
  intro rt o p f self rest kw w h
  simp [wrapperdescrCall, h, typeErr, raiseC]

/-- **`type.__new__` argument parsing**: the messages of `PyArg_ParseTuple(args, "UO!O")`
and the check of the namespace, `Objects/typeobject.c:5125-5137`. -/
def TypeNewArgs : Prop :=
  ∀ (rt : Rt) (m : Addr) (a b c : Val) (args : List Val) (kw : Kw) (w : World),
    (args.length ≠ 3 → typeNew rt m args kw w =
      (typeErr s!"type.__new__() takes exactly 3 arguments ({args.length} given)" : M Val) w) ∧
    (strOf w a = none → typeNew rt m [a, b, c] kw w =
      (typeErr s!"type.__new__() argument 1 must be str, not {typeName w a}" : M Val) w)

theorem typeNewArgs_proven : TypeNewArgs := by
  intro rt m a b c args kw w
  constructor
  · intro h
    match args, h with
    | [], _ => simp [typeNew]
    | [_], _ => simp [typeNew]
    | [_, _], _ => simp [typeNew]
    | [_, _, _], h => simp at h
    | _ :: _ :: _ :: _ :: _, _ => simp [typeNew]
  · intro h
    simp [typeNew, h]

/-- **Empty bases mean `object`**: `Objects/typeobject.c:5050-5058`. -/
def TypeNewEmptyBases : Prop :=
  ∀ (rt : Rt) (ctx : TypeNewCtx) (w : World),
    ctx.bases = [] →
    typeNewGetBases rt ctx w = .ok (.inr { ctx with base := B.object, bases := [.obj B.object] }) w

theorem typeNewEmptyBases_proven : TypeNewEmptyBases := by
  intro rt ctx w h
  simp [typeNewGetBases, h]

/-- A non-class base with `__mro_entries__` is refused by `type()`, which unlike the
`class` statement does not resolve it, `Objects/typeobject.c:5066-5075`. -/
def TypeNewMroEntries : Prop :=
  ∀ (rt : Rt) (ctx : TypeNewCtx) (b m : Val) (rest : List Val) (w w1 : World),
    ctx.bases = b :: rest → typeCheck w b = false →
    rt.getOptionalAttr b "__mro_entries__" w = .ok (some m) w1 →
    typeNewGetBases rt ctx w =
      (typeErr "type() doesn't support MRO entry resolution; use types.new_class()" : M _) w1

theorem typeNewMroEntries_proven : TypeNewMroEntries := by
  intro rt ctx b m rest w w1 h1 h2 h3
  simp [typeNewGetBases, h1, checkMroEntries, h2, h3, typeErr, raiseC]

/-- `__classcell__` must be a cell: `Objects/typeobject.c:4821`. -/
def ClassCellChecked : Prop :=
  ∀ (key : Name) (value cell : Val) (dict : NameDict) (w : World),
    NameDict.get? dict key = some cell → (∀ c, payloadOf w cell ≠ some (.cell c)) →
    typeNewSetCell key value dict w =
      (typeErr s!"{key} must be a nonlocal cell, not {trunc 200 (typeRepr w (typeOf w cell))}" : M NameDict) w

theorem classCellChecked_proven : ClassCellChecked := by
  intro key value cell dict w h1 h2
  simp only [typeNewSetCell, M.bind_app, getW_app, h1]
  cases cell with
  | obj a =>
    cases hp : payloadOf w (.obj a) with
    | none => rfl
    | some p =>
      cases p with
      | cell c => exact (h2 c hp).elim
      | _ => rfl
  | _ => rfl

/-- `tp_mro` lookups for `__mro__`, `__bases__`, `__base__` read the type's fields. -/
def TypeGetters : Prop :=
  ∀ (rt : Rt) (t : Addr) (w : World),
    (tdata w B.type).heap = false →
    getsetGetImpl rt B.type "__bases__" (.obj t) w = .ok (.tuple ((tdata w t).bases.map Val.obj)) w ∧
    getsetGetImpl rt B.type "__mro__" (.obj t) w =
      .ok (match (tdata w t).mro with
           | some m => .tuple (m.map Val.obj)
           | none => .none) w

theorem typeGetters_proven : TypeGetters := by
  intro rt t w h
  have h0 : B.type ≠ B.object := by decide
  constructor <;> simp [getsetGetImpl, h, h0] <;> rfl

/-- `type_name`, `type_qualname` for a heap type are `ht_name`, `ht_qualname`. -/
def TypeNameGetters : Prop :=
  ∀ (rt : Rt) (t : Addr) (w : World),
    (tdata w B.type).heap = false → (tdata w t).heap = true →
    getsetGetImpl rt B.type "__name__" (.obj t) w = .ok (.str (tdata w t).name) w ∧
    getsetGetImpl rt B.type "__qualname__" (.obj t) w = .ok (.str (tdata w t).qualname) w

theorem typeNameGetters_proven : TypeNameGetters := by
  intro rt t w h1 h2
  have h0 : B.type ≠ B.object := by decide
  constructor <;> simp [getsetGetImpl, h1, h2, h0, typeQualname]

/-- `object.__class__` is `type(obj)` for every object: `object_get_class`,
`Objects/typeobject.c:7627`. -/
def ObjectGetClass : Prop :=
  ∀ (rt : Rt) (obj : Val) (w : World),
    getsetGetImpl rt B.object "__class__" obj w = .ok (.obj (typeOf w obj)) w

theorem objectGetClass_proven : ObjectGetClass := by
  intro rt obj w
  simp [getsetGetImpl]

/-- `type_repr` of a heap class in a module, `Objects/typeobject.c:2458`. -/
def TypeReprHeap : Prop :=
  ∀ (w : World) (t : Addr) (m : String),
    (tdata w t).heap = true → NameDict.get? (tdata w t).dict "__module__" = some (.str m) →
    m ≠ "builtins" → typeRepr w t = s!"<class '{m}.{(tdata w t).qualname}'>"

theorem typeReprHeap_proven : TypeReprHeap := by
  intro w t m h1 h2 h3
  simp [typeRepr, h1, h2, h3, typeQualname]

/-- `object_repr` and `object_str`: `str()` of an object with the default `__str__` is its
`tp_repr`, `Objects/typeobject.c:7566`. -/
def ObjectStrUsesRepr : Prop :=
  ∀ (rt : Rt) (v : Val) (r : SlotFn) (w : World),
    slotOf w (typeOf w v) .tp_repr = some r →
    callStr rt (.c .object) v w = callRepr rt r v w

/-- **Binding `super` never checks against a NULL type.** For the object `super.__new__(super)`
allocates, and every `obj`, `super_descr_get` does not reach `supercheck` with a NULL type.
No hypothesis: `obj = None` is one of the cases covered, and returns `self` at
`Objects/typeobject.c:12891`. FALSE: `__init__` is what sets `su->type`, and `__new__` can be
called alone, so `super.__new__(super).__get__(1)` is a NULL dereference. -/
def SuperBindHasType : Prop :=
  ∀ (w w' : World) (v o : Val),
    alloc B.super (freshBody w B.super) w = .ok v w' →
    superBindsNullType w' v o = false

/-- **`superBindsNullType` is the branch of `super_descr_get` that crashes.** For every `Rt`, an
object for which the predicate holds runs `superDescrGet` into its `none` branch, the point where
C calls `supercheck` with a NULL type. So the refutation below is about `super_descr_get` itself
and not only about the predicate. -/
def SuperBindNullIsTheBranch : Prop :=
  ∀ (rt : Rt) (self o : Val) (w : World), superBindsNullType w self o = true →
    ∃ site, superDescrGet rt self (some o) w = .err (.gap site) w

theorem superBindNullIsTheBranch_proven : SuperBindNullIsTheBranch := by
  intro rt self o w h
  cases hp : payloadOf w self with
  | none => cases o <;> simp [superBindsNullType, hp] at h
  | some b =>
    cases b
    case super ty so ot =>
      cases ty <;> cases so <;> cases o <;> simp [superBindsNullType, hp] at h
      all_goals simp [superDescrGet, hp, h, gapAt]
    all_goals cases o <;> simp [superBindsNullType, hp] at h

/-- A heap in which address 24 is `super`, with the MRO it has in CPython. -/
def superNullW : World :=
  { heap := (Array.replicate 24 (.val {} : Cell)).push
      (.ty 1 { name := "super", mro := some [B.super, B.object] }) }

/-- `superNullW` after `super.__new__(super)`. -/
def superNullW' : World :=
  { superNullW with
    heap := superNullW.heap.push (.val { cls := B.super, body := .super none none none }) }

theorem superBindHasType_refuted : ¬SuperBindHasType := by
  intro h
  have hb := h superNullW superNullW' (.obj 25) (.int 1) rfl
  exact absurd hb (by decide)

theorem objectStrUsesRepr_proven : ObjectStrUsesRepr := by
  intro rt v r w h
  simp [callStr, isExcFamily, h]

end PyLean.TypeObj
