import PyLean.Bytecode.Uops1

/-!
Step rules of `Python/bytecodes.c`, part 2: lines 1848-3120 (cells, builders,
`super`, attributes, comparison, imports, jumps, pattern matching). Conventions
as in `Uops1.lean`.
-/

namespace PyLean.Bytecode.Uop

open PyLean.Bytecode

/-! ### Lines 1848-1937: cells -/

/-- `:2354`. -/
def DELETE_FAST (e : Env) : M Unit := stk 0 0 fun _ => do
  let v ← getLocal e.oparg
  if v == .null then
    let co ← getCode e.P
    (formatExcCheckArg "UnboundLocalError" (unboundLocalMsg (co.localsplusnames.getD e.oparg "")) : RM _)
  setLocal e.oparg .null
  pure []

/-- `PyCell_New`. -/
def cellNew (v : Val) : RM Val := alloc (.cell v)

/-- The contents of the cell in a local. -/
def cellGet : Val → RM Val
  | .ref a => do
    match ← getObj a with
    | .cell v => pure v
    | _ => fault "not a cell"
  | _ => fault "not a cell"

def cellSet (c v : Val) : RM Unit :=
  match c with
  | .ref a => setObj a (.cell v)
  | _ => fault "not a cell"

/-- `:2368`. -/
def MAKE_CELL (e : Env) : M Unit := stk 0 0 fun _ => do
  let initial ← getLocal e.oparg
  let c ← (cellNew initial : RM Val)
  setLocal e.oparg c
  pure []

/-- `:2381`. -/
def DELETE_DEREF (e : Env) : M Unit := stk 0 0 fun _ => do
  let c ← getLocal e.oparg
  let old ← (cellGet c : RM Val)
  if old == .null then
    let co ← getCode e.P
    (formatExcUnbound co e.oparg : RM _)
  (cellSet c .null : RM Unit)
  pure []

/-- `:2393`. -/
def LOAD_FROM_DICT_OR_DEREF (e : Env) : M Unit := stkK 1 1 fun
  | [cd] => do
    let co ← getCode e.P
    let name := co.localsplusnames.getD e.oparg ""
    match ← (optItem e cd name : RM _) with
    | some v => pure [v]
    | none =>
      let c ← getLocal e.oparg
      let v ← (cellGet c : RM Val)
      if v == .null then (formatExcUnbound co e.oparg : RM _)
      pure [v]
  | _ => fault "arity"

/-- `:2424`. -/
def LOAD_DEREF (e : Env) : M Unit := stk 0 1 fun _ => do
  let c ← getLocal e.oparg
  let v ← (cellGet c : RM Val)
  if v == .null then
    let co ← getCode e.P
    (formatExcUnbound co e.oparg : RM _)
  pure [v]

/-- `:2433`. -/
def STORE_DEREF (e : Env) : M Unit := stk 1 0 fun
  | [v] => do
    let c ← getLocal e.oparg
    (cellSet c v : RM Unit)
    pure []
  | _ => fault "arity"

/-- `:2438`. -/
def COPY_FREE_VARS (e : Env) : M Unit := stk 0 0 fun _ => do
  let f ← getFrame
  let co ← getCode e.P
  let func ← (getFunc f.funcobj : RM _)
  let closure ← (tupleItems func.closure : RM _)
  let offset := co.nlocalsplus - e.oparg
  for i in List.range e.oparg do
    setLocal (offset + i) (closure.getD i .null)
  pure []

/-! ### Lines 1939-2147: builders -/

/-- `:2452`. -/
def BUILD_STRING (e : Env) : M Unit := stk e.oparg 1 fun pieces => do
  let strs := pieces.map fun
    | .str s => s
    | _ => ""
  pure [.str (String.join strs)]
/-- `:2459`. -/
def BUILD_INTERPOLATION (e : Env) : M Unit := stk (2 + (e.oparg &&& 1)) 1 fun
  | v :: s :: rest => do
    let fmt := if e.oparg &&& 1 != 0 then rest.headD .null else .str ""
    pure [← e.om.buildInterpolation e.ctx v s (e.oparg >>> 2) fmt]
  | _ => fault "arity"
/-- `:2483`. -/
def BUILD_TEMPLATE (e : Env) : M Unit := stk 2 1 fun
  | [a, b] => do pure [← e.om.buildTemplate e.ctx a b]
  | _ => fault "arity"
/-- `:2493`. -/
def BUILD_TUPLE (e : Env) : M Unit := stk e.oparg 1 fun vs => do pure [← (mkTuple vs : RM Val)]
/-- `:2502`. -/
def BUILD_LIST (e : Env) : M Unit := stk e.oparg 1 fun vs => do pure [← (mkList vs : RM Val)]
/-- `:2533`. -/
def LIST_EXTEND (e : Env) : M Unit := stk (e.oparg + 1) e.oparg fun ins => do
  let it := ins.getLastD .null
  let rest := ins.dropLast
  let ext : RM Unit := tryExc (e.om.listExtend e.ctx (rest.headD .null) it) fun exc => do
    if (← givenMatches exc 8 (.cls "TypeError")) && !(← e.om.isIterable it) then
      typeError s!"Value after * must be an iterable, not {trunc200 (← tpName it)}"
    else throw (.exc exc)
  ext
  pure rest
/-- `:2545`. -/
def SET_UPDATE (e : Env) : M Unit := stk (e.oparg + 1) e.oparg fun ins => do
  let it := ins.getLastD .null
  let rest := ins.dropLast
  e.om.setUpdate e.ctx (rest.headD .null) it
  pure rest
/-- `:2547`. -/
def BUILD_SET (e : Env) : M Unit := stk e.oparg 1 fun vs => do
  let s ← (alloc (.set false #[]) : RM Val)
  for v in vs do
    (setAdd e.om e.ctx s v : RM Unit)
  pure [s]
/-- `_PyDict_FromItems`. -/
def dictFromItems (e : Env) : List Val → Val → RM Unit
  | k :: v :: rest, d => do dictSet e.om e.ctx d k v; dictFromItems e rest d
  | _, _ => pure ()
/-- `:2575`. -/
def BUILD_MAP (e : Env) : M Unit := stk (e.oparg * 2) 1 fun vs => do
  let d ← (mkDict : RM Val)
  (dictFromItems e vs d : RM Unit)
  pure [d]
/-- `:2583`. -/
def SETUP_ANNOTATIONS (e : Env) : M Unit := stk 0 0 fun _ => do
  let l := (← getFrame).locals
  if l == .null then (raiseS "SystemError" "no locals found when setting up annotations" : RM _)
  let r ← (optItem e l "__annotations__" : RM _)
  if r.isNone then
    let d ← (mkDict : RM Val)
    e.om.setItem e.ctx l (.str "__annotations__") d
  pure []
/-- `:2636`. -/
def DICT_UPDATE (e : Env) : M Unit := stk (e.oparg + 1) e.oparg fun ins => do
  let upd := ins.getLastD .null
  let rest := ins.dropLast
  let u : RM Unit := tryExc (e.om.dictUpdate e.ctx (rest.headD .null) upd) fun exc => do
    if ← givenMatches exc 8 (.cls "AttributeError") then
      typeError s!"'{trunc200 (← tpName upd)}' object is not a mapping"
    else throw (.exc exc)
  u
  pure rest

/-- `_PyObject_FunctionStr`: `qualname()`, with the module for non-builtins. -/
def functionStr (e : Env) (f : Val) : RM String := do
  let q ← tryExc (e.om.getAttr e.ctx f "__qualname__") fun _ => pure .null
  match q with
  | .str qn =>
    let m ← tryExc (e.om.getAttr e.ctx f "__module__") fun _ => pure .null
    match m with
    | .str "builtins" => pure s!"{qn}()"
    | .str mn => pure s!"{mn}.{qn}()"
    | _ => pure s!"{qn}()"
  | _ =>
    match ← e.om.str e.ctx f with
    | .str s => pure s
    | _ => pure ""

/-- `_PyEval_FormatKwargsError`, `Python/ceval.c:3414-3446`: since 3.15 an `AttributeError`
is rewritten only when `kwargs` really has no `keys` attribute. The model's `dictMerge`
reports a duplicate key as a `KeyError`, which is `dupkey != NULL` here. -/
def formatKwargsError {α : Type} (e : Env) (kwargs exc : Val) (func : Val) : RM α := do
  if ← givenMatches exc 8 (.cls "AttributeError") then
    let hasKeys ← tryExc (do let _ ← e.om.getAttr e.ctx kwargs "keys"; pure true) fun x => do
      if ← givenMatches x 8 (.cls "AttributeError") then pure false else throw (.exc x)
    if hasKeys then throw (.exc exc)
    typeError s!"Value after ** must be a mapping, not {← tpName kwargs}"
  else if ← givenMatches exc 8 (.cls "KeyError") then
    let d ← excData exc
    let args ← tupleItems d.args
    if args.size == 1 then
      let fs ← functionStr e func
      match ← e.om.str e.ctx (args.getD 0 .null) with
      | .str k => typeError s!"{fs} got multiple values for keyword argument '{k}'"
      | _ => throw (.exc exc)
    else throw (.exc exc)
  else throw (.exc exc)

/-- `:2654`. -/
def DICT_MERGE (e : Env) : M Unit := stk (e.oparg + 4) (e.oparg + 3) fun ins => do
  let upd := ins.getLastD .null
  let rest := ins.dropLast
  let callable := rest.headD .null
  let d := rest.getD 3 .null
  let u : RM Unit := tryExc (e.om.dictMerge e.ctx d upd) fun exc =>
    formatKwargsError e upd exc callable
  u
  pure rest
/-- `:2656`. -/
def MAP_ADD (e : Env) : M Unit := stk (e.oparg + 2) e.oparg fun ins => do
  let rest := ins.dropLast.dropLast
  let key := ins.getD e.oparg .null
  let v := ins.getD (e.oparg + 1) .null
  (dictSet e.om e.ctx (rest.headD .null) key v : RM Unit)
  pure rest

/-! ### Lines 2149-2264: `super` -/

/-- `:2679`. -/
def _SPECIALIZE_LOAD_SUPER_ATTR : M Unit := pure ()
/-- `:2692`. -/
def _LOAD_SUPER_ATTR (e : Env) : M Unit := stk 3 1 fun
  | [gs, c, slf] => do
    -- With `oparg & 2 == 0` C calls `super()` with no arguments, and
    -- `super_init_without_args` reads `__class__` and the first local from the
    -- frame: the same two values the compiler has put on the stack.
    let args := if e.oparg &&& 2 != 0 || gs == .cls "super" then [c, slf] else []
    let sup ← e.om.call e.ctx gs args []
    let name ← getName e (e.oparg >>> 2)
    pure [← e.om.getAttr e.ctx sup name]
  | _ => fault "arity"
/-- `:2740`. -/
def LOAD_SUPER_ATTR (e : Env) : M Unit := do
  _SPECIALIZE_LOAD_SUPER_ATTR; _LOAD_SUPER_ATTR e; _PUSH_NULL_CONDITIONAL e
/-- `:2669`. -/
def INSTRUMENTED_LOAD_SUPER_ATTR (e : Env) : M Unit := do _LOAD_SUPER_ATTR e; _PUSH_NULL_CONDITIONAL e
/-- `:2745`. -/
def LOAD_SUPER_ATTR_ATTR (e : Env) : M Unit := do
  guardTop 3 fun
    | [gs, c, _] => do
      if gs != .cls "super" then pure true else pure !(← (isType c : RM Bool))
    | _ => fault "arity"
  stk 3 1 fun
    | [_, c, slf] => do
      let name ← getName e (e.oparg >>> 2)
      let (a, _) ← e.om.superLookup e.ctx c slf name false
      pure [a]
    | _ => fault "arity"
/-- `:2761`. -/
def LOAD_SUPER_ATTR_METHOD (e : Env) : M Unit := do
  guardTop 3 fun
    | [gs, c, _] => do
      if gs != .cls "super" then pure true else pure !(← (isType c : RM Bool))
    | _ => fault "arity"
  stkK 3 2 fun
    | [_, c, slf] => do
      let name ← getName e (e.oparg >>> 2)
      let wantMethod ← e.om.genericGetattr slf
      let (a, found) ← e.om.superLookup e.ctx c slf name wantMethod
      pure [a, if found then slf else .null]
    | _ => fault "arity"

/-! ### Lines 2266-2644: attributes -/

/-- `:2828`. -/
def _SPECIALIZE_LOAD_ATTR : M Unit := pure ()
/-- `:2841`. -/
def _LOAD_ATTR (e : Env) : M Unit :=
  stk 1 (1 + (e.oparg &&& 1)) fun
    | [owner] => do
      let name ← getName e (e.oparg >>> 1)
      if e.oparg &&& 1 != 0 then
        let (a, s) ← e.om.getMethod e.ctx owner name
        pure [a, s]
      else
        pure [← e.om.getAttr e.ctx owner name]
    | _ => fault "arity"
/-- `:2857`. -/
def LOAD_ATTR (e : Env) : M Unit := do _SPECIALIZE_LOAD_ATTR; _LOAD_ATTR e
/-- `:2868`, after `_LOCK_OBJECT`, which does nothing on the GIL build. -/
def _GUARD_TYPE_VERSION_LOCKED (e : Env) : M Unit := _GUARD_TYPE_VERSION e

/-- The instance record behind a value. -/
def instOf : Val → RM (Option (Addr × InstObj))
  | .ref a => do
    match ← getObj a with
    | .inst i => pure (some (a, i))
    | _ => pure none
  | _ => pure none

/-- `_CHECK_MANAGED_OBJECT_HAS_VALUES`, `:2301`. The model stores every instance
attribute in a dict; "inline values valid" is "the dict has been materialized". -/
def _CHECK_MANAGED_OBJECT_HAS_VALUES : M Unit := guardTop 1 fun
  | [o] => do
    match ← (instOf o : RM _) with
    | some (_, i) => pure (i.dict == .null)
    | none => pure true
  | _ => fault "arity"

/-- `values[index]`, deopting when the slot does not hold `name`: the model's
reading of `attr_o == NULL`, since it has no shared-keys table. -/
def instanceSlot (o : Val) (index : Nat) (name : String) : BM Val := do
  match ← (instOf o : RM _) with
  | some (_, i) =>
    let d ← (getDict i.dict : RM _)
    match d.entries[index]? with
    | some en => if en.key == .str name then pure en.value else throw .deopt
    | none => throw .deopt
  | none => throw .deopt

/-- `:2890`. -/
def _LOAD_ATTR_INSTANCE_VALUE (e : Env) : M Unit := stk 1 1 fun
  | [o] => do
    let name ← getName e (e.oparg >>> 1)
    pure [← instanceSlot o (cacheNat e 1) name]
  | _ => fault "arity"
/-- `:2908`. -/
def LOAD_ATTR_INSTANCE_VALUE (e : Env) : M Unit := do
  _GUARD_TYPE_VERSION e; _CHECK_MANAGED_OBJECT_HAS_VALUES; _LOAD_ATTR_INSTANCE_VALUE e
  _PUSH_NULL_CONDITIONAL e
/-- `:2918`. -/
def _LOAD_ATTR_MODULE (e : Env) : M Unit := stk 1 1 fun
  | [.ref a] => do
    match ← (getObj a : RM Obj) with
    | .module _ d => pure [← dictSlot (.ref d) (cacheNat e 0) (cacheNat e 1)]
    | _ => throw .deopt
  | _ => throw .deopt
/-- `:2943`. -/
def LOAD_ATTR_MODULE (e : Env) : M Unit := do _LOAD_ATTR_MODULE e; _PUSH_NULL_CONDITIONAL e
/-- `:2950`. -/
def _LOAD_ATTR_WITH_HINT (e : Env) : M Unit := stk 1 1 fun
  | [o] => do
    let name ← getName e (e.oparg >>> 1)
    pure [← instanceSlot o (cacheNat e 1) name]
  | _ => fault "arity"
/-- `:2990`. -/
def LOAD_ATTR_WITH_HINT (e : Env) : M Unit := do
  _GUARD_TYPE_VERSION e; _LOAD_ATTR_WITH_HINT e; _PUSH_NULL_CONDITIONAL e
/-- `:2999`. -/
def _LOAD_ATTR_SLOT (e : Env) : M Unit := stk 1 1 fun
  | [o] => do
    match ← (instOf o : RM _) with
    | some (_, i) =>
      match i.slots[cacheNat e 1]? with
      | some v => if v == .null then throw .deopt else pure [v]
      | none => throw .deopt
    | none => throw .deopt
  | _ => fault "arity"
/-- `:3016`. -/
def LOAD_ATTR_SLOT (e : Env) : M Unit := do
  _GUARD_TYPE_VERSION e; _LOAD_ATTR_SLOT e; _PUSH_NULL_CONDITIONAL e

/-- `tp_version_tag` of a type object. -/
def classVersion : Val → RM (Option Nat)
  | .ref a => do
    match ← getObj a with
    | .cls c => pure (some c.version)
    | _ => pure none
  | _ => pure none

/-- `:3025`. -/
def _CHECK_ATTR_CLASS (e : Env) : M Unit := guardTop 1 fun
  | [o] => do
    match ← (classVersion o : RM _) with
    | some v => pure (v != cacheNat e 0)
    | none => pure true
  | _ => fault "arity"
/-- `:3033`. -/
def _LOAD_ATTR_CLASS (e : Env) : M Unit := stk 1 1 fun _ => pure [(e.cache[1]?).getD .null]
/-- `:3040`. -/
def LOAD_ATTR_CLASS (e : Env) : M Unit := do
  _CHECK_ATTR_CLASS e; _LOAD_ATTR_CLASS e; _PUSH_NULL_CONDITIONAL e
/-- `:3048`. -/
def LOAD_ATTR_CLASS_WITH_METACLASS_CHECK (e : Env) : M Unit := do
  _CHECK_ATTR_CLASS e; _LOAD_ATTR_CLASS e; _PUSH_NULL_CONDITIONAL e

/-- The function in a `descr/4` cache entry, under its version guard. In C the entry cannot
dangle while the type version holds. The model's `quick` difftest rewrites a program from an
earlier run, and the two runs allocate differently once they diverge, so the entry can
name another object there: that reads as a failed version guard, not a model fault. -/
def cachedFunc (f : Val) (version : Nat) : BM FuncObj := do
  deoptIf !(← (isFunction f : RM Bool))
  let func ← (getFunc f : RM _)
  deoptIf (func.version != version)
  pure func

/-- `:3056`. On 3.15 the shape of the code object is the specializer's business, and at run
time only the function's version is guarded. The cache holds `[type version, fget, func
version]`. -/
def _LOAD_ATTR_PROPERTY_FRAME (e : Env) : M Frame := do
  let fget := (e.cache[1]?).getD .null
  let (func, co) ← BM.lift do
    let func ← cachedFunc fget (cacheNat e 2)
    let co ← (getCodeR e.P func.code : RM _)
    deoptIf !(← hasStackSpace)
    pure (func, co)
  let ins ← popN 1
  let nf := frameInitialize co func.code func fget .null
  pure { nf with fast := nf.fast.setIfInBounds 0 (ins.headD .null) }

/-- `:3070`. -/
def LOAD_ATTR_PROPERTY (e : Env) : M Unit := do
  _GUARD_TYPE_VERSION e
  _CHECK_PEP_523
  let nf ← _LOAD_ATTR_PROPERTY_FRAME e
  BM.lift (_SAVE_RETURN_OFFSET e)
  _PUSH_FRAME nf

/-- `:3098`. On 3.15 this ends in `_SAVE_RETURN_OFFSET + _PUSH_FRAME`, where 3.14 went through
`DISPATCH_INLINED` and its `start_frame` recursion check. -/
def LOAD_ATTR_GETATTRIBUTE_OVERRIDDEN (e : Env) : M Unit := do
  _GUARD_TYPE_VERSION e
  _CHECK_PEP_523
  let f := (e.cache[2]?).getD .null
  let (func, co) ← BM.lift do
    let func ← cachedFunc f (cacheNat e 1)
    let co ← (getCodeR e.P func.code : RM _)
    deoptIf !(← hasStackSpace)
    pure (func, co)
  let name ← BM.lift (getName e (e.oparg >>> 1))
  let ins ← popN 1
  let nf := frameInitialize co func.code func f .null
  let nf := { nf with fast := (nf.fast.setIfInBounds 0 (ins.headD .null)).setIfInBounds 1 (.str name) }
  BM.lift (_SAVE_RETURN_OFFSET e)
  _PUSH_FRAME nf

/-- `:3107`. -/
def _GUARD_DORV_NO_DICT : M Unit := pure ()

/-- Replace the `index` slot of an instance's dict under the key `name`. -/
def instanceStore (o : Val) (index : Nat) (name : String) (v : Val) : BM Unit := do
  match ← (instOf o : RM _) with
  | some (_, i) =>
    let d ← (getDict i.dict : RM _)
    match d.entries[index]? with
    | some en =>
      if en.key == .str name then
        (putDict i.dict { d with entries := d.entries.setIfInBounds index { en with value := v } } : RM Unit)
      else throw .deopt
    | none => throw .deopt
  | none => throw .deopt

/-- `:3119`. -/
def _STORE_ATTR_INSTANCE_VALUE (e : Env) : M Unit := stk 2 0 fun
  | [v, o] => do
    instanceStore o (cacheNat e 1) (← getName e e.oparg) v
    pure []
  | _ => fault "arity"
/-- `:3142`. -/
def STORE_ATTR_INSTANCE_VALUE (e : Env) : M Unit := do
  _GUARD_TYPE_VERSION_LOCKED e; _GUARD_DORV_NO_DICT; _STORE_ATTR_INSTANCE_VALUE e
/-- `:3151`. -/
def _STORE_ATTR_WITH_HINT (e : Env) : M Unit := stk 2 0 fun
  | [v, o] => do
    instanceStore o (cacheNat e 1) (← getName e e.oparg) v
    pure []
  | _ => fault "arity"
/-- `:3186`. -/
def STORE_ATTR_WITH_HINT (e : Env) : M Unit := do _GUARD_TYPE_VERSION e; _STORE_ATTR_WITH_HINT e
/-- `:3193`. -/
def _STORE_ATTR_SLOT (e : Env) : M Unit := stk 2 0 fun
  | [v, .ref a] => do
    match ← (getObj a : RM Obj) with
    | .inst i =>
      (setObj a (.inst { i with slots := i.slots.setIfInBounds (cacheNat e 1) v }) : RM Unit)
      pure []
    | _ => throw .deopt
  | _ => throw .deopt
/-- `:3207`. -/
def STORE_ATTR_SLOT (e : Env) : M Unit := do _GUARD_TYPE_VERSION e; _STORE_ATTR_SLOT e

/-! ### Lines 2646-2860: comparison -/

/-- `:3220`. -/
def _SPECIALIZE_COMPARE_OP : M Unit := pure ()
/-- `:3232`. -/
def _COMPARE_OP (e : Env) : M Unit := stk 2 1 fun
  | [l, r] => do
    let res ← e.om.richCompare e.ctx l r (e.oparg >>> 5)
    if e.oparg &&& 16 != 0 then pure [.bool (← e.om.isTrue e.ctx res)]
    else pure [res]
  | _ => fault "arity"
/-- `:3251`. -/
def COMPARE_OP (e : Env) : M Unit := do _SPECIALIZE_COMPARE_OP; _COMPARE_OP e

/-- `dleft`/`dright` as C doubles. -/
def flt (a : UInt64) : Float := Float.ofBits a

/-- `:3262`. -/
def _COMPARE_OP_FLOAT (e : Env) : M Unit := stk 2 1 fun
  | [.float l, .float r] =>
    let signIsh := comparisonBit (flt l >= flt r) (flt l <= flt r)
    pure [.bool (signIsh &&& e.oparg != 0)]
  | _ => fault "not floats"
/-- `:3280`. -/
def _COMPARE_OP_INT (e : Env) : M Unit := stk 2 1 fun
  | [.int l, .int r] => do
    if !isCompact l then throw .deopt
    if !isCompact r then throw .deopt
    let signIsh := comparisonBit (decide (l ≥ r)) (decide (l ≤ r))
    pure [.bool (signIsh &&& e.oparg != 0)]
  | _ => fault "not ints"
/-- `:3302`. `COMPARISON_NOT_EQUALS` is 7 (`Include/internal/pycore_code.h:538`). -/
def _COMPARE_OP_STR (e : Env) : M Unit := stk 2 1 fun
  | [.str l, .str r] =>
    let eq : Nat := if l == r then 1 else 0
    pure [.bool ((7 + eq) &&& e.oparg != 0)]
  | _ => fault "not strs"
/-- `:3253`. -/
def COMPARE_OP_FLOAT (e : Env) : M Unit := do _GUARD_TOS_FLOAT; _GUARD_NOS_FLOAT; _COMPARE_OP_FLOAT e
/-- `:3256`. -/
def COMPARE_OP_INT (e : Env) : M Unit := do _GUARD_TOS_INT; _GUARD_NOS_INT; _COMPARE_OP_INT e
/-- `:3259`. -/
def COMPARE_OP_STR (e : Env) : M Unit := do _GUARD_TOS_UNICODE; _GUARD_NOS_UNICODE; _COMPARE_OP_STR e

/-- `:3320`. -/
def IS_OP (e : Env) : M Unit := stk 2 1 fun
  | [l, r] => pure [.bool (((if l == r then 1 else 0) ^^^ e.oparg) != 0)]
  | _ => fault "arity"
/-- `:3335`. -/
def _CONTAINS_OP (e : Env) : M Unit := stk 2 1 fun
  | [l, r] => do
    let res ← e.om.contains e.ctx r l
    pure [.bool (((if res then 1 else 0) ^^^ e.oparg) != 0)]
  | _ => fault "arity"
/-- `:3349`. -/
def _SPECIALIZE_CONTAINS_OP : M Unit := pure ()
/-- `:3361`. -/
def CONTAINS_OP (e : Env) : M Unit := do _SPECIALIZE_CONTAINS_OP; _CONTAINS_OP e

/-- `PyAnySet_CheckExact`. -/
def notAnySet (v : Val) : BM Bool := do
  match v with
  | .ref a =>
    match ← (getObj a : RM Obj) with
    | .set .. => pure false
    | _ => pure true
  | _ => pure true
/-- `:3363`. -/
def _GUARD_TOS_ANY_SET : M Unit := guardTop 1 fun
  | [o] => notAnySet o
  | _ => fault "arity"
/-- `:3380`. -/
def _CONTAINS_OP_SET (e : Env) : M Unit := stk 2 1 fun
  | [l, r] => do
    let res ← (setContains e.om e.ctx r l : RM Bool)
    pure [.bool (((if res then 1 else 0) ^^^ e.oparg) != 0)]
  | _ => fault "arity"
/-- `:3378`. -/
def CONTAINS_OP_SET (e : Env) : M Unit := do _GUARD_TOS_ANY_SET; _CONTAINS_OP_SET e
/-- `:3399`. -/
def _CONTAINS_OP_DICT (e : Env) : M Unit := stk 2 1 fun
  | [l, r] => do
    let res ← (dictContains e.om e.ctx r l : RM Bool)
    pure [.bool (((if res then 1 else 0) ^^^ e.oparg) != 0)]
  | _ => fault "arity"
/-- `:3397`. -/
def CONTAINS_OP_DICT (e : Env) : M Unit := do _GUARD_TOS_ANY_DICT; _CONTAINS_OP_DICT e

/-- `:3415`. -/
def CHECK_EG_MATCH (e : Env) : M Unit := stk 2 2 fun
  | [ev, mt] => do
    (checkExceptStarTypeValid mt : RM Unit)
    let (m, rest) ← (exceptionGroupMatch e.om e.ctx ev mt : RM _)
    if m != .none then (setExcInfoTop m : RM Unit)
    pure [rest, m]
  | _ => fault "arity"
/-- `:3441`. -/
def CHECK_EXC_MATCH : M Unit := stkK 2 2 fun
  | [l, r] => do
    (checkExceptTypeValid r : RM Unit)
    let res ← (givenMatches l 8 r : RM Bool)
    pure [l, .bool res]
  | _ => fault "arity"
/-- `:3456`. -/
def IMPORT_NAME (e : Env) : M Unit := stk 2 1 fun
  | [level, fromlist] => do
    let name ← getName e e.oparg
    let f ← getFrame
    pure [← e.om.importName e.ctx f name fromlist level]
  | _ => fault "arity"
/-- `:3478`. -/
def IMPORT_FROM (e : Env) : M Unit := stkK 1 2 fun
  | [from_] => do
    let name ← getName e e.oparg
    pure [from_, ← e.om.importFrom e.ctx from_ name]
  | _ => fault "arity"

/-! ### Lines 2879-3031: jumps -/

/-- `:3494`. -/
def JUMP_FORWARD (e : Env) : M Unit := BM.lift (jumpBy e.oparg)
/-- `:3656`. -/
def JUMP_BACKWARD_NO_INTERRUPT (e : Env) : M Unit := BM.lift (jumpBy (-(e.oparg : Int)))
/-- `:3503`. -/
def _SPECIALIZE_JUMP_BACKWARD : M Unit := pure ()
/-- `:3515`: tier 2 is not built. -/
def _JIT : M Unit := pure ()
/-- `:6604`: only reached while tracing for the JIT, which is not built. -/
def TRACE_RECORD : M Unit := fault "TRACE_RECORD without a JIT tracer"
/-- `:3544`. -/
def JUMP_BACKWARD (e : Env) : M Unit := do
  _SPECIALIZE_JUMP_BACKWARD; _CHECK_PERIODIC; JUMP_BACKWARD_NO_INTERRUPT e
/-- `:3550`. -/
def JUMP_BACKWARD_NO_JIT (e : Env) : M Unit := do _CHECK_PERIODIC; JUMP_BACKWARD_NO_INTERRUPT e
/-- `:3555`. -/
def JUMP_BACKWARD_JIT (e : Env) : M Unit := do _CHECK_PERIODIC; JUMP_BACKWARD_NO_INTERRUPT e; _JIT
/-- `:3579`: unreachable on a build without tier 2. -/
def ENTER_EXECUTOR : M Unit := fault "ENTER_EXECUTOR is not supported in this build"

/-- `next_instr->op.code == NOT_TAKEN`. -/
def nextIsNotTaken (e : Env) : BM Bool := do
  let co ← getCode e.P
  let n ← getNext
  pure ((co.instrs[n]?.map (·.op)) == some .NOT_TAKEN)

/-- Shared by `_POP_JUMP_IF_FALSE` and `_POP_JUMP_IF_TRUE`:
`JUMPBY(flag ? oparg : next_instr->op.code == NOT_TAKEN)`. -/
def jumpIf (e : Env) (flag : Bool) : BM Unit := do
  if flag then jumpBy e.oparg
  else if ← nextIsNotTaken e then jumpBy 1

/-- `:3621`. -/
def _POP_JUMP_IF_FALSE (e : Env) : M Unit := stk 1 0 fun
  | [.bool b] => do jumpIf e !b; pure []
  | _ => fault "POP_JUMP_IF_FALSE on a non-bool"
/-- `:3629`. -/
def _POP_JUMP_IF_TRUE (e : Env) : M Unit := stk 1 0 fun
  | [.bool b] => do jumpIf e b; pure []
  | _ => fault "POP_JUMP_IF_TRUE on a non-bool"
/-- `:3637`. -/
def _IS_NONE : M Unit := stk 1 1 fun
  | [v] => pure [.bool (v == .none)]
  | _ => fault "arity"
/-- `:3648`. -/
def POP_JUMP_IF_TRUE (e : Env) : M Unit := _POP_JUMP_IF_TRUE e
/-- `:3650`. -/
def POP_JUMP_IF_FALSE (e : Env) : M Unit := _POP_JUMP_IF_FALSE e
/-- `:3652`. -/
def POP_JUMP_IF_NONE (e : Env) : M Unit := do _IS_NONE; _POP_JUMP_IF_TRUE e
/-- `:3654`. -/
def POP_JUMP_IF_NOT_NONE (e : Env) : M Unit := do _IS_NONE; _POP_JUMP_IF_FALSE e

/-! ### Lines 3033-3119: `len`, pattern matching, iterators -/

/-- `:3666`. -/
def GET_LEN (e : Env) : M Unit := stkK 1 2 fun
  | [o] => do pure [o, .int (← e.om.length e.ctx o)]
  | _ => fault "arity"
/-- `:3699`. -/
def MATCH_CLASS (e : Env) : M Unit := stk 3 1 fun
  | [s, t, names] => do
    match ← e.om.matchClass e.ctx s t e.oparg names with
    | some a => pure [a]
    | none => pure [.none]
  | _ => fault "arity"
/-- `:3701`. -/
def MATCH_MAPPING (e : Env) : M Unit := stk 1 2 fun
  | [s] => do pure [s, .bool (← e.om.isMapping s)]
  | _ => fault "arity"
/-- `:3706`. -/
def MATCH_SEQUENCE (e : Env) : M Unit := stk 1 2 fun
  | [s] => do pure [s, .bool (← e.om.isSequence s)]
  | _ => fault "arity"
/-- `:3711`. -/
def MATCH_KEYS (e : Env) : M Unit := stkK 2 3 fun
  | [s, k] => do pure [s, k, ← e.om.matchKeys e.ctx s k]
  | _ => fault "arity"

/-- `PyCoro_CheckExact`/`PyGen_CheckExact` of a value. -/
def genKindOf : Val → RM (Option GenKind)
  | .ref a => do
    match ← getObj a with
    | .gen g => pure (some g.kind)
    | _ => pure none
  | _ => pure none

/-- `GET_ITER_YIELD_FROM_NO_CHECK`, `Include/internal/pycore_opcode_utils.h:96`. -/
def getIterYieldFromNoCheck : Nat := 2
/-- `GET_ITER_YIELD_FROM_CORO_CHECK`, `Include/internal/pycore_opcode_utils.h:97`. -/
def getIterYieldFromCoroCheck : Nat := 3

/-- `fixup_getiter`, `Python/specialize.c:46-59`, which `_PyCode_Quicken` runs on every
`GET_ITER`: a nonzero oparg becomes one of the two checked forms by the code's flags, so
`types.coroutine` is seen after compilation. Idempotent. -/
def fixupGetIter (oparg flags : Nat) : Nat :=
  if oparg == 0 then 0
  else if flagSet flags (coCoroutine ||| coIterableCoroutine) then getIterYieldFromNoCheck
  else getIterYieldFromCoroCheck

/-- `tp->tp_iter == PyObject_SelfIter`: the iterator types of the model and generators.
An instance of a Python class has `slot_tp_iter` there, whatever its `__iter__` does. -/
def isSelfIter : Val → RM Bool
  | .ref a => do
    match ← getObj a with
    | .listIter .. | .tupleIter .. | .rangeIter .. | .strIter .. | .seqIter .. | .callIter ..
    | .dictIter .. | .setIter .. | .enumerate .. | .zip .. | .map .. | .filter .. | .reversed .. =>
      pure true
    | .gen g => pure (g.kind == .gen)
    | _ => pure false
  | _ => pure false

/-- `_PyEval_GetIter`, `Python/ceval.c:1131-1163`, without the failure of `PyStackRef_CLOSE`,
which has none: `(iter, index_or_null)`. -/
def getIterStack (e : Env) (co : Code) (iterable : Val) : RM (List Val) := do
  if ← hasIterItem iterable then return [iterable, .tagged 0]
  if ← isSelfIter iterable then return [iterable, .null]
  let yieldFrom := fixupGetIter e.oparg co.flags
  if yieldFrom != 0 && (← genKindOf iterable) == some .coro then
    if yieldFrom == getIterYieldFromCoroCheck then
      typeError "cannot 'yield from' a coroutine object in a non-coroutine generator"
    return [iterable, .null]
  return [← e.om.getIter e.ctx iterable, .null]

/-- `:3736`: `(iterable -- iter, index_or_null)`. -/
def _GET_ITER (e : Env) : M Unit := stk 1 2 fun
  | [o] => do
    let co ← getCode e.P
    (getIterStack e co o : RM _)
  | _ => fault "arity"
/-- `:3724`. -/
def _SPECIALIZE_GET_ITER : M Unit := pure ()
/-- `:3743`. -/
def GET_ITER (e : Env) : M Unit := do _SPECIALIZE_GET_ITER; _GET_ITER e
/-- `:3748`. -/
def _GUARD_ITERATOR : M Unit := guardTop 1 fun
  | [o] => do return !(← (isSelfIter o : RM Bool))
  | _ => fault "arity"
/-- `:3754`. -/
def GET_ITER_SELF : M Unit := do _GUARD_ITERATOR; PUSH_NULL
/-- `:3760`. -/
def _GUARD_ITER_VIRTUAL : M Unit := guardTop 1 fun
  | [o] => do return !(← (hasIterItem o : RM Bool))
  | _ => fault "arity"
/-- `:3766`. -/
def _PUSH_TAGGED_ZERO : M Unit := stk 0 1 fun _ => pure [.tagged 0]
/-- `:3770`. -/
def GET_ITER_VIRTUAL : M Unit := do _GUARD_ITER_VIRTUAL; _PUSH_TAGGED_ZERO

end PyLean.Bytecode.Uop
