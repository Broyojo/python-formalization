import PyLean.Bytecode.Builtins

/-!
The choice of `Python/specialize.c`, as a pure function of the operands an
instruction just saw: `suggest` returns the specialized form and its inline cache.

The adaptive interpreter rewrites code in place. The model keeps `Program`
immutable and instead rewrites it between two runs: a first run records what
`suggest` says at each instruction (`runProfiled`), and `applyProfile` builds the
rewritten program. The caches hold what the C specializer stores: versions as
`.tagged`, cached objects as themselves.
-/

namespace PyLean.Bytecode.Proto

open PyLean.Bytecode Uop

/-- Operands, top of stack first. -/
abbrev Tops := List Val

def isList (v : Val) : RM Bool := isExactList v
def isTuple (v : Val) : RM Bool := isExactTuple v
def isDict (v : Val) : RM Bool := isExactDict v

def isAnySet : Val → RM Bool
  | .ref a => do
    match ← getObj a with
    | .set .. => pure true
    | _ => pure false
  | _ => pure false

def isSlice : Val → RM Bool
  | .ref a => do
    match ← getObj a with
    | .slice .. => pure true
    | _ => pure false
  | _ => pure false

def specInstr (i : Instr) (o : Op) (c : List Val := []) : Option Instr :=
  some { i with op := o, cache := c }

/-- The index of a str key among the entries of a dict. -/
def dictIndex (dv : Val) (name : String) : RM (Option Nat) := do
  let d ← getDict dv
  dictFind (strKeyEq name) d (hashStr name)

/-- `function_kind(code) == SIMPLE_FUNCTION`, `Python/specialize.c`. -/
def simpleFunction (c : Code) : Bool :=
  c.flags &&& (coVarkeywords ||| coVarargs) == 0 && c.kwonlyargcount == 0 &&
    c.flags &&& coOptimized != 0

/-- The class record of an instance, if the type is a Python class. -/
def heapClass (v : Val) : RM (Option ClassObj) := do
  match ← typeOf v with
  | .ref a =>
    match ← getObj a with
    | .cls c => pure (some c)
    | _ => pure none
  | _ => pure none

/-- `_Py_Specialize_BinaryOp`. -/
def suggestBinaryOp (P : Program) (i : Instr) (next? : Option Instr) (f : Frame) :
    Tops → RM (Option Instr)
  | r :: l :: _ => do
    match i.arg with
    | 0 | 13 =>
      match l, r with
      | .int a, .int b =>
        pure (if isCompact a && isCompact b then specInstr i .BINARY_OP_ADD_INT else none)
      | .float _, .float _ => pure (specInstr i .BINARY_OP_ADD_FLOAT)
      | .str _, .str _ =>
        match next? with
        | some n =>
          if n.op == .STORE_FAST && f.fast.getD n.arg .null == l then
            pure (specInstr i .BINARY_OP_INPLACE_ADD_UNICODE)
          else pure (specInstr i .BINARY_OP_ADD_UNICODE)
        | none => pure (specInstr i .BINARY_OP_ADD_UNICODE)
      | _, _ => pure none
    | 10 | 23 =>
      match l, r with
      | .int a, .int b =>
        pure (if isCompact a && isCompact b then specInstr i .BINARY_OP_SUBTRACT_INT else none)
      | .float _, .float _ => pure (specInstr i .BINARY_OP_SUBTRACT_FLOAT)
      | _, _ => pure none
    | 5 | 18 =>
      match l, r with
      | .int a, .int b =>
        pure (if isCompact a && isCompact b then specInstr i .BINARY_OP_MULTIPLY_INT else none)
      | .float _, .float _ => pure (specInstr i .BINARY_OP_MULTIPLY_FLOAT)
      | _, _ => pure none
    | 7 | 20 => pure (specInstr i .BINARY_OP_EXTEND [.tagged 0])
    | 1 | 14 => pure (specInstr i .BINARY_OP_EXTEND [.tagged 1])
    | 12 | 25 => pure (specInstr i .BINARY_OP_EXTEND [.tagged 2])
    | 26 =>
      match l, r with
      | .str s, .int k =>
        if isNonNegCompact k then
          if s.toList.any (fun c => asciiLimit ≤ c.toNat) then
            pure (specInstr i .BINARY_OP_SUBSCR_USTR_INT)
          else pure (specInstr i .BINARY_OP_SUBSCR_STR_INT)
        else pure none
      | _, _ =>
        if ← isDict l then pure (specInstr i .BINARY_OP_SUBSCR_DICT)
        else if ← isList l then
          match r with
          | .int k =>
            pure (if isNonNegCompact k then specInstr i .BINARY_OP_SUBSCR_LIST_INT else none)
          | _ =>
            if ← isSlice r then pure (specInstr i .BINARY_OP_SUBSCR_LIST_SLICE) else pure none
        else if ← isTuple l then
          match r with
          | .int k =>
            pure (if isNonNegCompact k then specInstr i .BINARY_OP_SUBSCR_TUPLE_INT else none)
          | _ => pure none
        else
          match l with
          | .ref a =>
            match ← getObj a with
            | .inst ins =>
              match ← userLookup ins.cls "__getitem__" with
              | some g =>
                if ← isFunction g then
                  let fo ← getFunc g
                  let co ← getCodeR P fo.code
                  if simpleFunction co && co.argcount == 2 then
                    let tv := ((← heapClass l).map (·.version)).getD 0
                    pure (specInstr i .BINARY_OP_SUBSCR_GETITEM [.tagged fo.version, g, .tagged tv])
                  else pure none
                else pure none
              | none => pure none
            | _ => pure none
          | _ => pure none
    | _ => pure none
  | _ => pure none

/-- `_Py_Specialize_ToBool`. -/
def suggestToBool (i : Instr) : Tops → RM (Option Instr)
  | v :: _ => do
    match v with
    | .bool _ => pure (specInstr i .TO_BOOL_BOOL)
    | .int _ => pure (specInstr i .TO_BOOL_INT)
    | .none => pure (specInstr i .TO_BOOL_NONE)
    | .str _ => pure (specInstr i .TO_BOOL_STR)
    | _ =>
      if ← isList v then pure (specInstr i .TO_BOOL_LIST)
      else
        match ← typeOf v with
        | t@(.ref a) =>
          if (← userLookup t "__bool__").isNone && (← userLookup t "__len__").isNone then
            match ← getObj a with
            | .cls c =>
              if c.mro.length == 2 then
                pure (specInstr i .TO_BOOL_ALWAYS_TRUE [.tagged c.version])
              else pure none
            | _ => pure none
          else pure none
        | _ => pure none
  | _ => pure none

/-- `_Py_Specialize_CompareOp`. -/
def suggestCompare (i : Instr) : Tops → RM (Option Instr)
  | r :: l :: _ =>
    match l, r with
    | .int _, .int _ => pure (specInstr i .COMPARE_OP_INT)
    | .float _, .float _ => pure (specInstr i .COMPARE_OP_FLOAT)
    | .str _, .str _ =>
      if i.arg >>> 5 == 2 || i.arg >>> 5 == 3 then pure (specInstr i .COMPARE_OP_STR)
      else pure none
    | _, _ => pure none
  | _ => pure none

/-- `_Py_Specialize_ContainsOp`. -/
def suggestContains (i : Instr) : Tops → RM (Option Instr)
  | r :: _ => do
    if ← isDict r then pure (specInstr i .CONTAINS_OP_DICT)
    else if ← isAnySet r then pure (specInstr i .CONTAINS_OP_SET)
    else pure none
  | _ => pure none

/-- `_Py_Specialize_ForIter`, `Python/specialize.c:2710-2769`. -/
def suggestForIter (i : Instr) : Tops → RM (Option Instr)
  | .null :: .ref a :: _ => do
    match ← getObj a with
    | .rangeIter .. => pure (specInstr i .FOR_ITER_RANGE)
    | .gen g => pure (if g.kind == .gen then specInstr i .FOR_ITER_GEN else none)
    | _ => pure none
  | .null :: _ => pure none
  | _ :: it :: _ => do
    if ← isList it then pure (specInstr i .FOR_ITER_LIST)
    else if ← isTuple it then pure (specInstr i .FOR_ITER_TUPLE)
    else pure (specInstr i .FOR_ITER_VIRTUAL)
  | _ => pure none

/-- `_Py_Specialize_Send`, `Python/specialize.c:2771-2800`. The third operand from the top is
the receiver. -/
def suggestSend (i : Instr) : Tops → RM (Option Instr)
  | _ :: _ :: r :: _ => do
    if ← hasIterItem r then return specInstr i .SEND_VIRTUAL
    match r with
    | .ref a =>
      match ← getObj a with
      | .gen g => pure (if g.kind != .asyncGen then specInstr i .SEND_GEN else none)
      | _ => pure none
    | _ => pure none
  | _ => pure none

/-- `_Py_Specialize_GetIter`, `Python/specialize.c:2966-2982`. -/
def suggestGetIter (i : Instr) : Tops → RM (Option Instr)
  | v :: _ => do
    if ← hasIterItem v then pure (specInstr i .GET_ITER_VIRTUAL)
    else if ← isSelfIter v then pure (specInstr i .GET_ITER_SELF)
    else pure none
  | _ => pure none

/-- `_Py_Specialize_CallFunctionEx`, `Python/specialize.c:2802-2822`. -/
def suggestCallEx (i : Instr) : Tops → RM (Option Instr)
  | _ :: _ :: _ :: f :: _ => do
    if ← isFunction f then pure (specInstr i .CALL_EX_PY)
    else pure (specInstr i .CALL_EX_NON_PY_GENERAL)
  | _ => pure none

/-- `_Py_Specialize_UnpackSequence`. -/
def suggestUnpack (i : Instr) : Tops → RM (Option Instr)
  | .ref a :: _ => do
    match ← getObj a with
    | .tuple t =>
      if t.size != i.arg then pure none
      else if i.arg == 2 then pure (specInstr i .UNPACK_SEQUENCE_TWO_TUPLE)
      else pure (specInstr i .UNPACK_SEQUENCE_TUPLE)
    | .list _ => pure (specInstr i .UNPACK_SEQUENCE_LIST)
    | _ => pure none
  | _ => pure none

/-- `_Py_Specialize_StoreSubscr`. -/
def suggestStoreSubscr (i : Instr) : Tops → RM (Option Instr)
  | k :: c :: _ => do
    if ← isDict c then pure (specInstr i .STORE_SUBSCR_DICT)
    else if ← isList c then
      match k with
      | .int _ => pure (specInstr i .STORE_SUBSCR_LIST_INT)
      | _ => pure none
    else pure none
  | _ => pure none

/-- `_Py_Specialize_LoadGlobal`. -/
def suggestLoadGlobal (i : Instr) (co : Code) (f : Frame) : RM (Option Instr) := do
  let name := co.names.getD (i.arg >>> 1) ""
  if !(← isExactDict f.globals) || !(← isExactDict f.builtins) then return none
  let gd ← getDict f.globals
  match ← dictIndex f.globals name with
  | some ix => pure (specInstr i .LOAD_GLOBAL_MODULE [.tagged gd.version, .tagged ix])
  | none =>
    let bd ← getDict f.builtins
    match ← dictIndex f.builtins name with
    | some ix =>
      pure (specInstr i .LOAD_GLOBAL_BUILTIN [.tagged gd.version, .tagged bd.version, .tagged ix])
    | none => pure none

/-- A plain Python class of instances, with no attribute hooks. -/
def plainAttr (t : Val) : RM Bool := do
  return (← userLookup t "__getattr__").isNone && (← userLookup t "__getattribute__").isNone

/-- `_Py_Specialize_LoadAttr`. -/
def suggestLoadAttr (P : Program) (i : Instr) (co : Code) : Tops → RM (Option Instr)
  | owner :: _ => do
    let name := co.names.getD (i.arg >>> 1) ""
    let wantMethod := i.arg &&& 1 != 0
    match owner with
    | .ref a =>
      match ← getObj a with
      | .module _ d =>
        if wantMethod then return none
        match ← dictIndex (.ref d) name with
        | some ix =>
          let dd ← getDict (.ref d)
          pure (specInstr i .LOAD_ATTR_MODULE [.tagged dd.version, .tagged ix])
        | none => pure none
      | .inst ins =>
        let some c ← heapClass owner | return none
        let t := ins.cls
        if !(← plainAttr t) then
          match ← userLookup t "__getattribute__" with
          | some g =>
            if (← userLookup t "__getattr__").isNone && (← isFunction g) && !wantMethod then
              let fo ← getFunc g
              let cg ← getCodeR P fo.code
              if cg.argcount == 2 then
                return specInstr i .LOAD_ATTR_GETATTRIBUTE_OVERRIDDEN
                  [.tagged c.version, .tagged fo.version, g]
            return none
          | none => return none
        let d? ← typeLookup t name
        let dataDescr ← match d? with
          | some d => isDataDescr d
          | none => pure false
        if let some d := d? then
          if let .ref da := d then
            if let .property fget .. ← getObj da then
              if wantMethod || fget == .null then return none
              if ← isFunction fget then
                let fo ← getFunc fget
                let cg ← getCodeR P fo.code
                if simpleFunction cg && cg.argcount == 1 then
                  return specInstr i .LOAD_ATTR_PROPERTY [.tagged c.version, fget, .tagged fo.version]
              return none
        if dataDescr then return none
        if c.slots.contains name then return none
        if ins.dict != .null then
          if let some ix ← dictIndex ins.dict name then
            if d?.isNone || !wantMethod then
              return specInstr i .LOAD_ATTR_INSTANCE_VALUE [.tagged c.version, .tagged ix]
            return none
        match d? with
        | some d =>
          let isFn ← isFunction d
          if wantMethod && isFn then
            if ins.dict != .null then
              return specInstr i .LOAD_ATTR_METHOD_WITH_VALUES [.tagged c.version, d]
            return specInstr i .LOAD_ATTR_METHOD_LAZY_DICT [.tagged c.version, d]
          pure none
        | none => pure none
      | .cls c =>
        if c.metaclass != .cls "type" then return none
        match ← typeLookup owner name with
        | some d =>
          let plain ← match d with
            | .ref da =>
              match ← getObj da with
              | .func _ | .cls _ | .tuple _ | .list _ | .dict _ => pure true
              | _ => pure false
            | .methDescr .. => pure false
            | _ => pure true
          if plain && !wantMethod then
            pure (specInstr i .LOAD_ATTR_CLASS [.tagged c.version, d])
          else pure none
        | none => pure none
      | _ => pure none
    | _ => pure none
  | _ => pure none

/-- `_Py_Specialize_StoreAttr`. -/
def suggestStoreAttr (i : Instr) (co : Code) : Tops → RM (Option Instr)
  | owner :: _ => do
    let name := co.names.getD i.arg ""
    match owner with
    | .ref a =>
      match ← getObj a with
      | .inst ins =>
        let some c ← heapClass owner | return none
        if (← userLookup ins.cls "__setattr__").isSome then return none
        if let some d ← typeLookup ins.cls name then
          if ← isDataDescr d then return none
        if let some ix := c.slots.findIdx? (· == name) then
          return specInstr i .STORE_ATTR_SLOT [.tagged c.version, .tagged ix]
        if ins.dict != .null then
          if let some ix ← dictIndex ins.dict name then
            return specInstr i .STORE_ATTR_INSTANCE_VALUE [.tagged c.version, .tagged ix]
        pure none
      | _ => pure none
    | _ => pure none
  | _ => pure none

/-- `_Py_Specialize_Call`. -/
def suggestCall (P : Program) (i : Instr) : Tops → RM (Option Instr)
  | tops => do
    let a := i.arg
    let args := tops.take a
    let selfOrNull := tops.getD a .null
    let callable := tops.getD (a + 1) .null
    let total := a + (if selfOrNull != .null then 1 else 0)
    let pyFunc (f : Val) (n : Nat) (exact general : Op) : RM (Option Instr) := do
      let fo ← getFunc f
      let co ← getCodeR P fo.code
      if simpleFunction co && co.argcount == n then
        pure (specInstr i exact [.tagged fo.version])
      else pure (specInstr i general [.tagged fo.version])
    let _ := args
    match callable with
    | .cls "type" =>
      if a == 1 && selfOrNull == .null then pure (specInstr i .CALL_TYPE_1) else pure none
    | .cls "str" =>
      if a == 1 && selfOrNull == .null then pure (specInstr i .CALL_STR_1) else pure none
    | .cls "tuple" =>
      if a == 1 && selfOrNull == .null then pure (specInstr i .CALL_TUPLE_1) else pure none
    | .cls _ => pure (specInstr i .CALL_BUILTIN_CLASS)
    | .builtin "len" =>
      if a == 1 && selfOrNull == .null then pure (specInstr i .CALL_LEN)
      else pure (specInstr i .CALL_BUILTIN_O)
    | .builtin "isinstance" =>
      if total == 2 && a == 2 then pure (specInstr i .CALL_ISINSTANCE)
      else pure (specInstr i .CALL_BUILTIN_FAST_WITH_KEYWORDS)
    | .builtin _ => pure (specInstr i .CALL_BUILTIN_FAST_WITH_KEYWORDS)
    | .methDescr "list" "append" =>
      if a == 1 && (← isList selfOrNull) then pure (specInstr i .CALL_LIST_APPEND)
      else pure (specInstr i .CALL_METHOD_DESCRIPTOR_O)
    | .methDescr .. => pure (specInstr i .CALL_METHOD_DESCRIPTOR_FAST)
    | .ref c =>
      match ← getObj c with
      | .func _ => pyFunc callable total .CALL_PY_EXACT_ARGS .CALL_PY_GENERAL
      | .method f _ =>
        if selfOrNull != .null then return none
        if ← isFunction f then
          pyFunc f (a + 1) .CALL_BOUND_METHOD_EXACT_ARGS .CALL_BOUND_METHOD_GENERAL
        else pure none
      | .cls k =>
        if selfOrNull != .null then return none
        if k.metaclass != .cls "type" then return none
        if (← userLookup callable "__new__").isSome then return none
        if k.mro.length != 2 then return none
        match ← userLookup callable "__init__" with
        | some ini =>
          if ← isFunction ini then
            let fo ← getFunc ini
            let co ← getCodeR P fo.code
            if simpleFunction co && co.argcount == a + 1 then
              return specInstr i .CALL_ALLOC_AND_ENTER_INIT [.tagged k.version, ini]
          pure none
        | none => pure none
      | _ => pure (specInstr i .CALL_NON_PY_GENERAL)
    | _ => pure (specInstr i .CALL_NON_PY_GENERAL)

/-- `_Py_Specialize_CallKw`. -/
def suggestCallKw (i : Instr) : Tops → RM (Option Instr)
  | tops => do
    let a := i.arg
    let selfOrNull := tops.getD (a + 1) .null
    let callable := tops.getD (a + 2) .null
    match callable with
    | .ref c =>
      match ← getObj c with
      | .func fo => pure (specInstr i .CALL_KW_PY [.tagged fo.version])
      | .method f _ =>
        if selfOrNull != .null then return none
        if ← isFunction f then
          let fo ← getFunc f
          pure (specInstr i .CALL_KW_BOUND_METHOD [.tagged fo.version])
        else pure none
      | _ => pure (specInstr i .CALL_KW_NON_PY)
    | _ => pure (specInstr i .CALL_KW_NON_PY)

/-- What the specializer would do at this instruction, given the state. -/
def suggest (P : Program) (co : Code) (i : Instr) (next? : Option Instr) (f : Frame)
    (tops : Tops) : RM (Option Instr) :=
  match i.op with
  | .BINARY_OP => suggestBinaryOp P i next? f tops
  | .TO_BOOL => suggestToBool i tops
  | .COMPARE_OP => suggestCompare i tops
  | .CONTAINS_OP => suggestContains i tops
  | .GET_ITER => suggestGetIter i tops
  | .FOR_ITER => suggestForIter i tops
  | .SEND => suggestSend i tops
  | .UNPACK_SEQUENCE => suggestUnpack i tops
  | .STORE_SUBSCR => suggestStoreSubscr i tops
  | .LOAD_GLOBAL => suggestLoadGlobal i co f
  | .LOAD_ATTR => suggestLoadAttr P i co tops
  | .STORE_ATTR => suggestStoreAttr i co tops
  | .CALL => suggestCall P i tops
  | .CALL_KW => suggestCallKw i tops
  | .CALL_FUNCTION_EX => suggestCallEx i tops
  | .LOAD_SUPER_ATTR =>
    pure (specInstr i (if i.arg &&& 1 != 0 then .LOAD_SUPER_ATTR_METHOD else .LOAD_SUPER_ATTR_ATTR))
  | .RESUME => pure (specInstr i .RESUME_CHECK)
  | .JUMP_BACKWARD => pure (specInstr i .JUMP_BACKWARD_NO_JIT)
  | _ => pure none

end PyLean.Bytecode.Proto
