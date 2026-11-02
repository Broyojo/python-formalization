import PyLean.Bytecode.Protocol

/-!
The rest of the concrete `ObjModel`: `PyNumber_*`, `str`/`repr`, iteration, calls,
class creation, builtin functions and methods, and the record itself.
-/

namespace PyLean.Bytecode.Proto

open PyLean.Bytecode Uop

section
variable (P : Program) (om : ObjModel) (ctx : Ctx)

/-- Builtin non-numeric operators: sequence concatenation and repetition, set and
dict operators. `none` is `NotImplemented`. -/
def seqBinary (nb : Nat) (l r : Val) : RM (Option Val) := do
  /- `PyMapping_Check`, abstract.c: the type has `mp_subscript`. -/
  let hasSubscript (v : Val) : RM Bool := do
    match v with
    | .str _ | .bytes _ => pure true
    | .ref b =>
      match ← getObj b with
      | .dict _ | .list _ | .tuple _ | .range .. => pure true
      | .inst i => pure (← userLookup i.cls "__getitem__").isSome
      | _ => pure false
    | _ => pure false
  match nb, l, r with
  | 0, .str a, .str b => pure (some (.str (a ++ b)))
  | 0, .bytes a, .bytes b => pure (some (.bytes (a ++ b)))
  | 6, .str a, _ =>
    -- `PyUnicode_Format`, unicode_format.c:1031-1101, for a template with no conversion in it,
    -- so `argidx` never moves; a template with one is the named exclusion
    -- `str-percent-conversion`.
    if a.contains '%' then fault "str % with conversions is not modelled"
    else
      let isTuple ← match r with
        | .ref b => match ← getObj b with
          | .tuple x => pure (some x.size)
          | _ => pure none
        | _ => pure none
      let isStr := match r with | .str _ => true | _ => false
      let dict := (← hasSubscript r) && isTuple.isNone && !isStr
      if dict || isTuple == some 0 then pure (some (.str a))
      else typeError s!"not all arguments converted during string formatting (required 0, got {isTuple.getD 1})"
  | 6, .bytes a, _ =>
    -- `_PyBytes_FormatEx`, bytesobject.c:618-1158, with the same named exclusion.
    if a.contains 37 then fault "bytes % with conversions is not modelled"
    else
      let isTuple ← match r with
        | .ref b => match ← getObj b with
          | .tuple x => pure (some x.size)
          | _ => pure none
        | _ => pure none
      let isBytesOrStr := match r with | .bytes _ | .str _ => true | _ => false
      let dict := (← hasSubscript r) && isTuple.isNone && !isBytesOrStr
      if dict || isTuple == some 0 then pure (some (.bytes a))
      else typeError s!"not all arguments converted during bytes formatting (required 0, got {isTuple.getD 1})"
  | 5, .bytes a, _ =>
    match intOf r with
    | some n => pure (some (.bytes (List.flatten (List.replicate n.toNat a))))
    | none => pure none
  | 5, _, .bytes b =>
    match intOf l with
    | some n => pure (some (.bytes (List.flatten (List.replicate n.toNat b))))
    | none => pure none
  | 5, .str a, _ =>
    match intOf r with
    | some n => pure (some (.str (pyStrRepeat a n)))
    | none => pure none
  | 5, _, .str b =>
    match intOf l with
    | some n => pure (some (.str (pyStrRepeat b n)))
    | none => pure none
  | _, .ref a, .ref b =>
    match nb, ← getObj a, ← getObj b with
    | 0, .list x, .list y => pure (some (← mkList (x.toList ++ y.toList)))
    | 0, .tuple x, .tuple y => pure (some (← mkTuple (x.toList ++ y.toList)))
    | 7, .dict _, .dict _ =>
      let d ← mkDict
      om.dictUpdate ctx d l
      om.dictUpdate ctx d r
      pure (some d)
    | _, .set f x, .set _ y =>
      let keep (p : (Int × Val) → RM Bool) (src : Array (Int × Val)) : RM (List (Int × Val)) :=
        src.toList.filterM p
      let contains (v : Val) (kv : Int × Val) : RM Bool := setContains om ctx v kv.2
      match nb with
      | 7 =>
        let ry ← keep (fun kv => do return !(← contains l kv)) y
        pure (some (← alloc (.set f (x ++ ry.toArray))))
      | 1 => pure (some (← alloc (.set f (← keep (contains r) x).toArray)))
      | 10 => pure (some (← alloc (.set f (← keep (fun kv => do return !(← contains r kv)) x).toArray)))
      | 12 =>
        let a1 ← keep (fun kv => do return !(← contains r kv)) x
        let a2 ← keep (fun kv => do return !(← contains l kv)) y
        pure (some (← alloc (.set f (a1 ++ a2).toArray)))
      | _ => pure none
    | _, _, _ => pure none
  | 5, .ref a, _ =>
    match ← getObj a, intOf r with
    | .list x, some n =>
      pure (some (← mkList (List.flatten (List.replicate n.toNat x.toList))))
    | .tuple x, some n =>
      pure (some (← mkTuple (List.flatten (List.replicate n.toNat x.toList))))
    | _, _ => pure none
  | 5, _, .ref b =>
    match intOf l, ← getObj b with
    | some n, .list x =>
      pure (some (← mkList (List.flatten (List.replicate n.toNat x.toList))))
    | some n, .tuple x =>
      pure (some (← mkTuple (List.flatten (List.replicate n.toNat x.toList))))
    | _, _ => pure none
  | _, _, _ => pure none

/-- `binary_op1` over builtin payloads: numbers first, then sequences. -/
def builtinBinary (nb : Nat) (l r : Val) : RM (Option Val) := do
  match nb, l, r with
  -- `bool_and`, `bool_or`, `bool_xor`, boolobject.c: two bools give a bool
  | 1, .bool a, .bool b => return some (.bool (a && b))
  | 7, .bool a, .bool b => return some (.bool (a || b))
  | 12, .bool a, .bool b => return some (.bool (a != b))
  | _, _, _ => pure ()
  match intOf l, intOf r with
  | some a, some b => intBinary nb a b
  | _, _ =>
    match l, r with
    | .float a, .float b => floatBinary nb a b
    | .float a, _ =>
      if (intOf r).isSome then
        match ← toFloatBits r with
        | some b => floatBinary nb a b
        | none => pure none
      else seqBinary om ctx nb l r
    | _, .float b =>
      if (intOf l).isSome then
        match ← toFloatBits l with
        | some a => floatBinary nb a b
        | none => pure none
      else seqBinary om ctx nb l r
    | _, _ => seqBinary om ctx nb l r

/-- `list(iterable)`/`PySequence_List`. -/
def seqToList (v : Val) : RM (List Val) := do
  drain om ctx (← om.getIter ctx v) 1000000 []

/-- `PySequence_Fast`, `Objects/abstract.c`: an exact list or tuple as it is, otherwise
`list(iter(v))`, with a `TypeError` from `iter` replaced by `msg`. -/
def seqFast (v : Val) (msg : String) : RM (List Val) := do
  if let .ref a := v then
    match ← getObj a with
    | .list x | .tuple x => return x.toList
    | _ => pure ()
  let it ← tryExc (om.getIter ctx v) fun e => do
    if ← givenMatches e 8 (.cls "TypeError") then typeError msg else throw (.exc e)
  drain om ctx it 1000000 []

/-- The loop of `merge_from_seq2_lock_held`, `Objects/dictobject.c:4068-4126`. Elements
are taken one at a time, so pairs before a failing element stay in the dict. The
`_PyErr_FormatNote` of line 3826 adds a note, which the model does not record. -/
def mergeFromSeq2Loop (d it : Val) : Nat → Nat → RM Unit
  | 0, _ => throw .fuel
  | n + 1, i => do
    match ← iterNextOpt om ctx it with
    | none => pure ()
    | some item =>
      let kv ← seqFast om ctx item "object is not iterable"
      match kv with
      | [k, v] =>
        dictSet om ctx d k v
        mergeFromSeq2Loop d it n (i + 1)
      | _ => valueError s!"dictionary update sequence element #{i} has length {kv.length}; 2 is required"

/-- `dict_update_arg`, `Objects/dictobject.c:3992`: a mapping, or a sequence of pairs. -/
def dictUpdateArgFwd (d o : Val) : RM Unit := do
  if (← isExactDict o) || (← optAttr om ctx o "keys").isSome then
    return ← om.dictUpdate ctx d o
  mergeFromSeq2Loop om ctx d (← om.getIter ctx o) 1000000 0

/-- The concatenation errors of `PyNumber_Add`/`Multiply` when the left operand
is a sequence, `Objects/abstract.c`. -/
def seqError (nb : Nat) (l r : Val) : RM (Option String) := do
  let name ← tpName l
  let rn ← tpName r
  match nb, l with
  | 0, .str _ => pure (some s!"can only concatenate str (not \"{rn}\") to str")
  | 0, .bytes _ => pure (some s!"can't concat {rn} to bytes")
  | 0, .ref a =>
    match ← getObj a with
    | .list _ | .tuple _ => pure (some s!"can only concatenate {name} (not \"{rn}\") to {name}")
    | _ => pure none
  | _, _ => pure none

/-- `(tp_as_sequence != NULL, sq_repeat != NULL)` of the type of `v`. Every heap type
has a `tp_as_sequence`; it has `sq_repeat` only by inheriting one. -/
def seqSlots (v : Val) : RM (Bool × Bool) := do
  let builtinRepeat (x : Val) : RM Bool := do
    match x with
    | .str _ | .bytes _ => pure true
    | .ref a =>
      match ← getObj a with
      | .list _ | .tuple _ => pure true
      | _ => pure false
    | _ => pure false
  match v with
  | .str _ | .bytes _ => pure (true, true)
  | .ref a =>
    match ← getObj a with
    | .list _ | .tuple _ => pure (true, true)
    | .dict _ | .set .. | .range .. | .dictView .. => pure (true, false)
    | .inst i => pure (true, ← builtinRepeat i.base)
    | _ => pure (false, false)
  | _ => pure (false, false)

/-- `sequence_repeat`, `Objects/abstract.c:1157-1173`. The `OverflowError` of
`PyNumber_AsSsize_t` is the named exclusion `huge-seq-repeat`. -/
def sequenceRepeat (seq n : Val) : RM Val := do
  match ← asIndex om ctx n with
  | some c =>
    match ← seqBinary om ctx 5 (← payload seq) (.int c) with
    | some v => pure v
    | none => fault "sq_repeat on a type that has none"
  | none => typeError s!"can't multiply sequence by non-int of type '{← tpName n}'"

/-- The `sq_repeat` fallback of `PyNumber_Multiply`, abstract.c:1169-1179, and of
`PyNumber_InPlaceMultiply`, abstract.c:1323-1341. They differ: in place, a left operand
with a `tp_as_sequence` and no repeat (a `dict`, a `set`, a `range`) rules out the right
operand. `none` is `binop_type_error`. -/
def mulSeqFallback (inplace : Bool) (l r : Val) : RM (Option Val) := do
  let (mv, rv) ← seqSlots l
  let (mw, rw) ← seqSlots r
  if inplace then
    if mv then
      if rv then return some (← sequenceRepeat om ctx l r)
    else if mw then
      if rw then return some (← sequenceRepeat om ctx r l)
    pure none
  else
    if rv then return some (← sequenceRepeat om ctx l r)
    if rw then return some (← sequenceRepeat om ctx r l)
    pure none

/-- `_PyEval_BinaryOps[nb]`: `binary_op1` with the reflected protocol, the
in-place slot first for `NB_INPLACE_*`, and `PyObject_GetItem` for `NB_SUBSCR`. -/
def binaryOpImpl (nb : Nat) (l r : Val) : RM Val := do
  if nb == 26 then return ← om.getItem ctx l r
  let inplace := nb ≥ 13
  let base := if inplace then nb - 13 else nb
  let name := opDunder base
  let lt ← typeOf l
  let rt_ ← typeOf r
  if inplace then
    if (← userLookup lt s!"__i{name}__").isSome then
      if let some v ← callDunder om ctx l s!"__i{name}__" [r] then
        if v != .notImpl then return v
    -- list `+=` and friends mutate in place
    if let .ref a := l then
      match ← getObj a, base with
      | .list x, 0 =>
        let vals ← drain om ctx (← om.getIter ctx r) 1000000 []
        setObj a (.list (x ++ vals.toArray))
        return l
      | .list x, 5 =>
        -- `list_inplace_repeat` through `sequence_repeat`
        if let some n ← asIndex om ctx r then
          setObj a (.list (List.flatten (List.replicate n.toNat x.toList)).toArray)
          return l
      | .dict _, 7 =>
        dictUpdateArgFwd om ctx l r
        return l
      | .set _ _, _ =>
        if let some v ← seqBinary om ctx base l r then
          if let .ref b := v then
            setObj a (← getObj b)
            return l
      | _, _ => pure ()
  let lU := (← userLookup lt s!"__{name}__")
  let rU := (← userLookup rt_ s!"__r{name}__")
  let attempt (v o : Val) (n : String) : RM (Option Val) := do
    match ← callDunder om ctx v n [o] with
    | some x => pure (if x == .notImpl then none else some x)
    | none => pure none
  let rFirst := lt != rt_ && (← isSubtype rt_ lt) && rU.isSome
  if rFirst then
    if let some x ← attempt r l s!"__r{name}__" then return x
  if lU.isSome then
    if let some x ← attempt l r s!"__{name}__" then return x
  if lU.isNone && rU.isNone || true then
    if let some x ← builtinBinary om ctx base (← payload l) (← payload r) then return x
  if !rFirst && lt != rt_ && rU.isSome then
    if let some x ← attempt r l s!"__r{name}__" then return x
  if base == 5 then
    if let some v ← mulSeqFallback om ctx inplace l r then return v
  else if let some m ← seqError base l r then typeError m
  typeError s!"unsupported operand type(s) for {opSymbol nb}: '{← tpName l}' and '{← tpName r}'"

/-- `PyNumber_Negative`. -/
def negativeImpl (v : Val) : RM Val := do
  match v with
  | .int i => pure (.int (-i))
  | .bool b => pure (.int (if b then -1 else 0))
  | .float b => pure (.float (b ^^^ 0x8000000000000000))
  | _ =>
    match ← callDunder om ctx v "__neg__" [] with
    | some r => pure r
    | none => typeError s!"bad operand type for unary -: '{← tpName v}'"

/-- `PyNumber_Invert`. -/
def invertImpl (v : Val) : RM Val := do
  match v with
  | .int i => pure (.int (-i - 1))
  | .bool b => pure (.int (if b then -2 else -1))
  | _ =>
    match ← callDunder om ctx v "__invert__" [] with
    | some r => pure r
    | none => typeError s!"bad operand type for unary ~: '{← tpName v}'"

/-- `PyNumber_Positive`. -/
def positiveImpl (v : Val) : RM Val := do
  match v with
  | .int _ | .float _ => pure v
  | .bool b => pure (.int (if b then 1 else 0))
  | _ =>
    match ← callDunder om ctx v "__pos__" [] with
    | some r => pure r
    | none => typeError s!"bad operand type for unary +: '{← tpName v}'"

/-- `PySequence_Contains`. -/
def containsImpl (c item : Val) : RM Bool := do
  match c with
  | .str s =>
    match item with
    | .str t => pure ((s.splitOn t).length > 1 || t == "")
    | _ => typeError s!"'in <string>' requires string as left operand, not {← tpName item}"
  | .bytes b =>
    match item with
    | .int i =>
      if i < 0 || i > 255 then valueError "byte must be in range(0, 256)"
      pure (b.contains (UInt8.ofNat i.toNat))
    | .bool x => pure (b.contains (if x then 1 else 0))
    | .bytes t =>
      let n := t.length
      pure ((List.range (b.length + 1)).any fun i => (b.drop i).take n == t)
    | _ => typeError s!"a bytes-like object is required, not '{← tpName item}'"
  | .ref a =>
    match ← getObj a with
    | .dict _ => do
      dictContains om ctx c item
    | .set .. => do
      setContains om ctx c item
    | .range start stop step len =>
      match intOf item with
      | some i =>
        if len == 0 then pure false
        else if step > 0 then pure (start ≤ i && i < stop && (i - start) % step == 0)
        else pure (stop < i && i ≤ start && (start - i) % (-step) == 0)
      -- `range_contains`, rangeobject.c:504: anything but an exact int or bool goes to
      -- `_PySequence_IterSearch`, abstract.c:2166, which compares `item == obj`.
      | none =>
        (List.range len.toNat).anyM fun (k : Nat) => eqBool om ctx (.int (start + (k : Int) * step)) item
    | .list items | .tuple items =>
      items.toList.anyM fun x => eqBool om ctx item x
    | _ =>
      match ← callDunder om ctx c "__contains__" [item] with
      | some r => om.isTrue ctx r
      | none =>
        let it ← tryExc (om.getIter ctx c) fun e => do
          if ← givenMatches e 8 (.cls "TypeError") then
            typeError s!"argument of type '{← tpName c}' is not a container or iterable"
          else throw (.exc e)
        let vals ← drain om ctx it 1000000 []
        vals.anyM fun x => eqBool om ctx item x
  | _ => typeError s!"argument of type '{← tpName c}' is not a container or iterable"

/-- `PyObject_Length`. -/
def lengthImpl (v : Val) : RM Int := do
  match v with
  | .str s => pure s.length
  | .bytes b => pure b.length
  | .ref a =>
    match ← getObj a with
    | .list i | .tuple i => pure i.size
    | .dict d => pure d.entries.size
    | .dictView d _ =>
      match ← getObj d with
      | .dict dd => pure dd.entries.size
      | _ => fault "dict view"
    | .set _ i => pure i.size
    | .range _ _ _ n => pure n
    | _ =>
      match ← callDunder om ctx v "__len__" [] with
      | some (.int n) =>
        if n < 0 then valueError "__len__() should return >= 0"
        pure n
      | some (.bool b) => pure (if b then 1 else 0)
      | some x => typeError s!"'{← tpName x}' object cannot be interpreted as an integer"
      | none =>
        let p ← payload v
        if p != v then om.length ctx p
        else typeError s!"object of type '{← tpName v}' has no len()"
  | _ => typeError s!"object of type '{← tpName v}' has no len()"

/-- Join with `, `, as `list_repr` does. -/
def commaJoin (xs : List String) : String := joinStrs ", " xs

def strOf : Val → String
  | .str s => s
  | _ => ""

/-- `<class 'x'>` text. -/
def classRepr (c : Val) : RM String := do
  match c with
  | .cls n => pure s!"<class '{n}'>"
  | _ => pure s!"<class '__main__.{(← (match c with
      | .ref a => do
        match ← getObj a with
        | .cls k => pure k.qualname
        | _ => pure ""
      | _ => pure ""))}'>"

/-- `PyObject_Repr`. -/
def reprImpl (v : Val) : RM Val := do
  let list (xs : List Val) : RM (List String) := xs.mapM fun x => do
    return strOf (← om.repr ctx x)
  match v with
  | .none => pure (.str "None")
  | .notImpl => pure (.str "NotImplemented")
  | .ellipsis => pure (.str "Ellipsis")
  | .bool b => pure (.str (if b then "True" else "False"))
  | .int i =>
    -- `long_to_decimal_string_internal`, longobject.c: `sys.int_info.default_max_str_digits`
    let t := toString i.natAbs
    if t.length > 4300 then
      valueError "Exceeds the limit (4300 digits) for integer string conversion; use sys.set_int_max_str_digits() to increase the limit"
    pure (.str (toString i))
  | .float b => pure (.str (Num.repr b))
  | .str s => pure (.str (strRepr s))
  | .bytes b => pure (.str (bytesRepr b))
  | .cls _ => pure (.str (← classRepr v))
  | .builtin n => pure (.str s!"<built-in function {n}>")
  | .ref a =>
    match ← getObj a with
    | .list items => pure (.str ("[" ++ commaJoin (← list items.toList) ++ "]"))
    | .tuple items =>
      if items.size == 1 then pure (.str ("(" ++ (← list items.toList).headD "" ++ ",)"))
      else pure (.str ("(" ++ commaJoin (← list items.toList) ++ ")"))
    | .dict d =>
      let parts ← d.entries.toList.mapM fun en => do
        return strOf (← om.repr ctx en.key) ++ ": " ++ strOf (← om.repr ctx en.value)
      pure (.str ("{" ++ commaJoin parts ++ "}"))
    | .set frozen items =>
      let inner := commaJoin (← list (items.toList.map (·.2)))
      if frozen then
        pure (.str (if items.size == 0 then "frozenset()" else "frozenset({" ++ inner ++ "})"))
      else pure (.str (if items.size == 0 then "set()" else "{" ++ inner ++ "}"))
    | .range start stop step _ =>
      if step == 1 then pure (.str s!"range({start}, {stop})")
      else pure (.str s!"range({start}, {stop}, {step})")
    | .slice s t st =>
      let f (x : Val) : RM String := do return strOf (← om.repr ctx x)
      pure (.str s!"slice({← f s}, {← f t}, {← f st})")
    | .cls _ => pure (.str (← classRepr v))
    | .inst i =>
      match ← callDunder om ctx v "__repr__" [] with
      | some r =>
        match r with
        | .str _ => pure r
        -- `PyObject_Repr`, `Objects/object.c:793`
        | _ => typeError s!"{← tpName v}.__repr__() must return a str, not {← tpName r}"
      | none =>
        match i.exc with
        | some d =>
          let n ← tpName v
          let args ← tupleItems d.args
          if args.size == 1 then
            pure (.str s!"{n}({strOf (← om.repr ctx (args.getD 0 .null))})")
          else pure (.str s!"{n}({commaJoin (← list args.toList)})")
        | none =>
          if i.base != .null then om.repr ctx i.base
          else pure (.str s!"<{← tpName v} object>")
    | _ => pure (.str s!"<{← tpName v} object>")
  | _ => pure (.str s!"<{← tpName v} object>")

/-- `PyObject_Str`. -/
def strImpl (v : Val) : RM Val := do
  match v with
  | .str _ => pure v
  | .ref a =>
    match ← getObj a with
    | .inst i =>
      match ← userLookup i.cls "__str__" with
      | some _ =>
        match ← callDunder om ctx v "__str__" [] with
        | some r =>
          match r with
          | .str _ => pure r
          -- `PyObject_Str`, `Objects/object.c:835`
          | _ => typeError s!"{← tpName v}.__str__() must return a str, not {← tpName r}"
        | none => om.repr ctx v
      | none =>
        match i.exc with
        | some d =>
          let args ← tupleItems d.args
          if (← isSubtype i.cls (.cls "KeyError")) && args.size == 1 then
            om.repr ctx (args.getD 0 .null)
          else if args.size == 0 then pure (.str "")
          else if args.size == 1 then om.str ctx (args.getD 0 .null)
          else om.repr ctx d.args
        | none =>
          if i.base != .null && (← userLookup i.cls "__repr__").isNone then om.str ctx i.base
          else
            -- `object_str` calls `tp_repr` itself, not `PyObject_Repr`, so a result that is
            -- not a str fails the check of `PyObject_Str`
            match ← callDunder om ctx v "__repr__" [] with
            | some (.str s) => pure (.str s)
            | some r => typeError s!"{← tpName v}.__str__() must return a str, not {← tpName r}"
            | none => om.repr ctx v
    | _ => om.repr ctx v
  | _ => om.repr ctx v

/-- `format(value, spec)` for `[[fill]align][0][width]` on str and int, the part of
the mini-language the difftest emits. -/
def formatImpl (v spec : Val) : RM Val := do
  let s := match spec with
    | .str s => s
    | _ => ""
  -- the check on the result, `PyObject_Format`, `Objects/abstract.c:900`
  let checked (r : Val) : RM Val := do
    match r with
    | .str _ => pure r
    | _ => typeError s!"{← tpName v}.__format__() must return a str, not {← tpName r}"
  if s == "" then
    if let some r ← callDunder om ctx v "__format__" [.str ""] then return ← checked r
    return ← om.str ctx v
  if let some r ← callDunder om ctx v "__format__" [spec] then return ← checked r
  let isNum := (match v with | .int _ | .float _ => true | _ => false)
  let body := strOf (← om.str ctx v)
  let cs := s.toList
  let isAlign (c : Char) := c == '<' || c == '>' || c == '^'
  let (fill, align, rest) : Char × Char × List Char :=
    match cs with
    | c :: a :: r => if isAlign a then (c, a, r)
      else if isAlign c then (' ', c, a :: r)
      else (' ', (if isNum then '>' else '<'), cs)
    | [c] => if isAlign c then (' ', c, []) else (' ', (if isNum then '>' else '<'), cs)
    | [] => (' ', '<', [])
  let (fill, rest) := match rest with
    | '0' :: r => (if fill == ' ' then '0' else fill, r)
    | r => (fill, r)
  let w := rest.foldl (fun n c => if c.isDigit then n * 10 + (c.toNat - 48) else n) 0
  let pad := w - body.length
  let rep (n : Nat) := String.ofList (List.replicate n fill)
  match align with
  | '<' => pure (.str (body ++ rep pad))
  | '^' => pure (.str (rep (pad / 2) ++ body ++ rep (pad - pad / 2)))
  | _ => pure (.str (rep pad ++ body))

/-- One item from each iterator, for `zip` and `map`. -/
def nextAll : List Val → List Val → RM (Option (List Val))
  | [], acc => pure (some acc.reverse)
  | x :: xs, acc => do
    match ← iterNextOpt om ctx x with
    | some v => nextAll xs (v :: acc)
    | none => pure none

/-- `filter_next`. -/
def filterNext (f i : Val) : Nat → RM (Option Val)
  | 0 => throw .fuel
  | n + 1 => do
    match ← iterNextOpt om ctx i with
    | none => pure none
    | some v =>
      let t ← if f == .none then om.isTrue ctx v
        else om.isTrue ctx (← call1 om ctx f [v])
      if t then pure (some v) else filterNext f i n

/-- `tp_iternext`. -/
def iterNextImpl (it : Val) : RM (Option Val) := do
  match it with
  | .ref a =>
    match ← getObj a with
    | .listIter seq index =>
      -- `listiter_next`, `Objects/listobject.c`
      if index < 0 then return none
      match seq with
      | none => return none
      | some sq =>
        match ← getObj sq with
        | .list items =>
          match items[index.toNat]? with
          | some v =>
            setObj a (.listIter seq (index + 1))
            pure (some v)
          | none =>
            setObj a (.listIter none (-1))
            pure none
        | _ => fault "list iterator over a non-list"
    | .tupleIter seq index =>
      match seq with
      | none => return none
      | some sq =>
        match ← getObj sq with
        | .tuple items =>
          match items[index.toNat]? with
          | some v =>
            setObj a (.tupleIter seq (index + 1))
            pure (some v)
          | none =>
            setObj a (.tupleIter none index)
            pure none
        | _ => fault "tuple iterator over a non-tuple"
    | .rangeIter start step len =>
      if len > 0 then
        setObj a (.rangeIter (start + step) step (len - 1))
        pure (some (.int start))
      else pure none
    | .strIter rest =>
      match rest with
      | c :: r =>
        setObj a (.strIter r)
        pure (some (.str c.toString))
      | [] => pure none
    | .seqIter seq index =>
      -- `iter_iternext`, `Objects/iterobject.c`
      if seq == .null then return none
      tryExc
        (do
          let v ← om.getItem ctx seq (.int index)
          setObj a (.seqIter seq (index + 1))
          pure (some v))
        fun e => do
          if (← givenMatches e 8 (.cls "IndexError")) || (← givenMatches e 8 (.cls "StopIteration")) then
            setObj a (.seqIter .null index)
            pure none
          else throw (.exc e)
    | .callIter c s =>
      -- `calliter_iternext`, `Objects/iterobject.c`
      if c == .null then return none
      tryExc
        (do
          let r ← call1 om ctx c []
          if ← eqBool om ctx r s then
            setObj a (.callIter .null .null)
            pure none
          else pure (some r))
        fun e => do
          if ← givenMatches e 8 (.cls "StopIteration") then
            setObj a (.callIter .null .null)
            pure none
          else throw (.exc e)
    | .dictIter d kind index used =>
      match ← getObj d with
      | .dict dd =>
        if dd.entries.size != used then
          runtimeError "dictionary changed size during iteration"
        match dd.entries[index]? with
        | some en =>
          setObj a (.dictIter d kind (index + 1) used)
          match kind with
          | 0 => pure (some en.key)
          | 1 => pure (some en.value)
          | _ => pure (some (← mkTuple [en.key, en.value]))
        | none => pure none
      | _ => fault "dict iterator over a non-dict"
    | .setIter items index =>
      match items[index]? with
      | some kv =>
        setObj a (.setIter items (index + 1))
        pure (some kv.2)
      | none => pure none
    | .enumerate i index =>
      match ← iterNextOpt om ctx i with
      | some v =>
        setObj a (.enumerate i (index + 1))
        pure (some (← mkTuple [.int index, v]))
      | none => pure none
    | .zip its _ =>
      match ← nextAll om ctx its [] with
      | some vs => pure (some (← mkTuple vs))
      | none => pure none
    | .map f its =>
      match ← nextAll om ctx its [] with
      | some vs => pure (some (← call1 om ctx f vs))
      | none => pure none
    | .filter f i => filterNext om ctx f i 1000000
    | .reversed seq index =>
      if index < 0 then return none
      setObj a (.reversed seq (index - 1))
      pure (some (← om.getItem ctx seq (.int index)))
    | .gen g =>
      if g.kind == .gen then genIterNext ctx a
      else typeError s!"'{← tpName it}' object is not an iterator"
    | .inst i =>
      match ← userLookup i.cls "__next__" with
      | some _ =>
        match ← callDunder om ctx it "__next__" [] with
        | some v => pure (some v)
        | none => pure none
      -- `_PyObject_NextNotImplemented`, `Objects/object.c`: `__next__` went away after the
      -- iterator was made, and the slot it left behind says this
      | none => typeError s!"'{← tpName it}' object is not iterable"
    | _ => typeError s!"'{← tpName it}' object is not an iterator"
  | _ => typeError s!"'{← tpName it}' object is not an iterator"

/-- `tp_iternext != NULL`. -/
def isIteratorImpl (v : Val) : RM Bool := do
  match v with
  | .ref a =>
    match ← getObj a with
    | .listIter .. | .tupleIter .. | .rangeIter .. | .strIter .. | .seqIter .. | .callIter ..
    | .dictIter .. | .setIter .. | .enumerate .. | .zip .. | .map .. | .filter .. | .reversed .. =>
      pure true
    | .gen g => pure (g.kind == .gen)
    | .inst i => return (← userLookup i.cls "__next__").isSome
    | _ => pure false
  | _ => pure false

/-- `tp_iter != NULL || PySequence_Check`. -/
def isIterableImpl (v : Val) : RM Bool := do
  match v with
  | .str _ | .bytes _ => pure true
  | .ref a =>
    match ← getObj a with
    | .list _ | .tuple _ | .dict _ | .set .. | .range .. | .dictView .. | .gen _ => pure true
    | .inst i =>
      if (← userLookup i.cls "__iter__").isSome then pure true
      else return (← userLookup i.cls "__getitem__").isSome
    | _ => isIteratorImpl v
  | _ => pure false

/-- `int(x)` for the forms the difftest uses. -/
def intFromStr (s : String) : Option Int :=
  let t := s.trimAscii.toString
  t.toInt?

/-- Instantiate an exception class: `BaseException_new`. -/
def excNew (cls : Val) (args : List Val) : RM Val := newExc cls args

/-- `PyObject_IsSubclass`/`IsInstance` with a tuple of classes. -/
def isSubclassImpl (c : Val) : Nat → Val → RM Bool
  | 0, _ => pure false
  | n + 1, t => do
    match t with
    | .ref a =>
      match ← getObj a with
      | .tuple items => items.toList.anyM (isSubclassImpl c n)
      | _ => isSubtype c t
    | _ =>
      if t == .builtin "type" then pure false
      else isSubtype c t

def isInstanceImpl (i t : Val) : RM Bool := do
  if !(← isTupleOrType t) then
    typeError "isinstance() arg 2 must be a type, a tuple of types, or a union"
  isSubclassImpl (← typeOf i) 8 t
where
  isTupleOrType (t : Val) : RM Bool := do
    if ← isType t then pure true else isExactTuple t

/-- `Objects/typeobject.c:type_new` for the class statement. -/
def buildClass (name : String) (bases : List Val) (ns : Val) : RM Val := do
  let bases' := if bases.isEmpty then [Val.cls "object"] else bases
  for b in bases' do
    if !(← isType b) then typeError "bases must be types"
  let mros ← bases'.mapM mroOf
  let selfDict := ns
  let dictAddr ← match selfDict with
    | .ref d => pure d
    | _ => fault "class namespace"
  let qual ← dictGetStr ns "__qualname__"
  let slots ← dictGetStr ns "__slots__"
  let slotNames ← match slots with
    | some (.ref a) =>
      match ← getObj a with
      | .tuple items | .list items => pure (items.toList.map strOf)
      | _ => pure []
    | some (.str s) => pure [s]
    | _ => pure []
  let inherited : List String ← (do
    let mut acc : List String := []
    for b in bases' do
      if let .ref a := b then
        if let .cls k ← getObj a then
          acc := acc ++ k.slots
    pure acc)
  let ver ← freshVersion
  let cv ← alloc (.cls { name := name, qualname := (match qual with | some (.str q) => q | _ => name),
                         bases := bases', mro := [], dict := dictAddr, version := ver,
                         slots := inherited ++ slotNames,
                         hasDict := slots.isNone })
  match c3Merge 32 (mros ++ [bases']) [] with
  | none => typeError "Cannot create a consistent method resolution order (MRO) for bases"
  | some merged =>
    match cv with
    | .ref a =>
      match ← getObj a with
      | .cls c =>
        setObj a (.cls { c with mro := cv :: merged })
        -- `__classcell__`
        if let some cell ← dictGetStr ns "__classcell__" then
          cellSet cell cv
          let _ ← dictPopStr ns "__classcell__"
        pure cv
      | _ => fault "class"
    | _ => fault "class"

/-- `type_call` for classes defined in Python. -/
def instantiate (c : Val) (args : List Val) (kw : List String) : RM Val := do
  -- `__new__`
  let isExc ← isSubtype c (.cls "BaseException")
  let npos := args.length - kw.length
  let newF ← userLookup c "__new__"
  let baseCls : Option String := (← mroOf c).findSome? fun
    | .cls n => if n == "object" then none else some n
    | _ => none
  let self ← match newF with
    | some f =>
      let fv ← match f with
        | .ref a =>
          match ← getObj a with
          | .staticMethod g => pure g
          | _ => pure f
        | _ => pure f
      om.call ctx fv (c :: args) kw
    | none =>
      let slotCount := (← (match c with
        | .ref a => do
          match ← getObj a with
          | .cls k => pure k.slots.length
          | _ => pure 0
        | _ => pure 0))
      -- `object_new`, `Objects/typeobject.c:7477`
      if let .ref ca := c then
        if let .cls k ← getObj ca then
          if !k.abstractMethods.isEmpty then
            let names := joinStrs "', '" k.abstractMethods
            typeError s!"Can't instantiate abstract class {k.name} without an implementation for abstract method{if k.abstractMethods.length == 1 then "" else "s"} '{names}'"
      if isExc then
        let t ← mkTuple (args.take npos)
        let isStop ← isSubtype c (.cls "StopIteration")
        let value := if isStop then args.head?.getD .none else .none
        alloc (.inst { cls := c, exc := some { args := t, value := value } })
      else
        let baseV ← match baseCls with
          | some n =>
            if n == "int" || n == "str" || n == "float" || n == "tuple" || n == "list"
               || n == "dict" || n == "set" then
              om.call ctx (.cls n) args kw
            else pure .null
          | none => pure .null
        let needsNoArgs := baseV == .null && (← userLookup c "__init__").isNone &&
          (!args.isEmpty)
        if needsNoArgs then typeError s!"{← typeNameOf c}() takes no arguments"
        alloc (.inst { cls := c, base := baseV, slots := Array.replicate slotCount .null })
  -- `__init__`, only for instances of `c`
  if !(← isSubtype (← typeOf self) c) then return self
  match ← userLookup (← typeOf self) "__init__" with
  | some f =>
    let b ← descrBind om ctx f self (← typeOf self)
    let r ← om.call ctx b args kw
    if r != .none then typeError s!"__init__() should return None, not '{← tpName r}'"
    pure self
  | none => pure self

/-- `__build_class__`, `Python/bltinmodule.c`. -/
def buildClassBuiltin (args : List Val) : RM Val := do
  match args with
  | func :: .str name :: bases =>
    let ns ← mkDict
    let cell ← evalVector P ctx func ns [] []
    let _ := cell
    buildClass name bases ns
  | _ => typeError "__build_class__: not enough arguments"

def sortInsert (cmpLt : Val × Val → Val × Val → RM Bool) (x : Val × Val) :
    List (Val × Val) → RM (List (Val × Val))
  | [] => pure [x]
  | y :: ys => do
    if ← cmpLt x y then pure (x :: y :: ys)
    else return y :: (← sortInsert cmpLt x ys)

/-- `list.sort`: stable; keys computed first. -/
def sortVals (items : List Val) (key : Val) (reverse : Bool) : RM (List Val) := do
  let keyed ← items.mapM fun v => do
    if key == .none then pure (v, v) else pure (← call1 om ctx key [v], v)
  let lt (a b : Val × Val) : RM Bool := cmpBool om ctx a.1 b.1 0
  let keyed := if reverse then keyed.reverse else keyed
  let mut acc : List (Val × Val) := []
  for x in keyed.reverse do
    acc ← sortInsert lt x acc
  let out := acc.map (·.2)
  pure (if reverse then out.reverse else out)

/-- Keyword arguments by name. -/
def kwGet (args : List Val) (kw : List String) (n : String) : Option Val :=
  let npos := args.length - kw.length
  (kw.zip (args.drop npos)).lookup n

/-- `str.split(sep)`, whitespace form. -/
def splitWs (s : String) : List String :=
  (s.split Char.isWhitespace).toList.map (fun x => x.toString) |>.filter (· != "")

/-- First position of an element equal to `x`. -/
def indexOfEq (x : Val) : Nat → List Val → RM (Option Nat)
  | _, [] => pure none
  | i, v :: r => do if ← eqBool om ctx v x then pure (some i) else indexOfEq x (i + 1) r

/-- Builtin methods. `self` is the receiver. -/
def callMethod (tp name : String) (self0 : Val) (args : List Val) (kw : List String) : RM Val := do
  -- the C methods read the base struct of a subclass instance, which here is its `base`
  let self ← if ["list", "dict", "str", "tuple", "set", "frozenset"].contains tp
    then payload self0 else pure self0
  match tp, name with
  | "list", "append" =>
    match args with
    | [v] => listAppend self v; pure .none
    | _ => typeError s!"list.append() takes exactly one argument ({args.length} given)"
  | "list", "extend" =>
    match args with
    | [v] => om.listExtend ctx self v; pure .none
    | _ => typeError s!"list.extend() takes exactly one argument ({args.length} given)"
  | "list", "pop" =>
    match self with
    | .ref a =>
      match ← getObj a with
      | .list items =>
        if items.size == 0 then raiseS "IndexError" "pop from empty list"
        let i : Int := match args with
          | [.int n] => if n < 0 then n + items.size else n
          | _ => items.size - 1
        if i < 0 || i ≥ items.size then raiseS "IndexError" "pop index out of range"
        setObj a (.list (items.eraseIdxIfInBounds i.toNat))
        pure (items.getD i.toNat .null)
      | _ => fault "self"
    | _ => fault "self"
  | "list", "insert" =>
    match self, args with
    | .ref a, [.int n, v] =>
      match ← getObj a with
      | .list items =>
        let l := items.toList
        let i := if n < 0 then max 0 (n + items.size) else min n items.size
        setObj a (.list (l.take i.toNat ++ [v] ++ l.drop i.toNat).toArray)
        pure .none
      | _ => fault "self"
    | _, _ => typeError "insert expected 2 arguments"
  | "list", "reverse" =>
    match self with
    | .ref a =>
      match ← getObj a with
      | .list items => setObj a (.list items.reverse); pure .none
      | _ => fault "self"
    | _ => fault "self"
  | "list", "clear" =>
    match self with
    | .ref a => setObj a (.list #[]); pure .none
    | _ => fault "self"
  | "list", "copy" =>
    match self with
    | .ref a =>
      match ← getObj a with
      | .list items => mkList items.toList
      | _ => fault "self"
    | _ => fault "self"
  | "list", "sort" =>
    match self with
    | .ref a =>
      match ← getObj a with
      | .list items =>
        let s ← sortVals om ctx items.toList ((kwGet args kw "key").getD .none)
          (match kwGet args kw "reverse" with | some (.bool b) => b | _ => false)
        setObj a (.list s.toArray)
        pure .none
      | _ => fault "self"
    | _ => fault "self"
  | "list", "index" | "tuple", "index" =>
    match self, args with
    | .ref a, x :: _ =>
      match ← getObj a with
      | .list items | .tuple items =>
        match ← indexOfEq om ctx x 0 items.toList with
        | some i => pure (.int i)
        | none => valueError (if tp == "list" then s!"list.index(x): x not in list" else "tuple.index(x): x not in tuple")
      | _ => fault "self"
    | _, _ => typeError "index expected at least 1 argument, got 0"
  | "list", "count" | "tuple", "count" =>
    match self, args with
    | .ref a, [x] =>
      match ← getObj a with
      | .list items | .tuple items =>
        let n ← items.toList.foldlM (fun c v => do
          if ← eqBool om ctx v x then pure (c + 1) else pure c) 0
        pure (.int n)
      | _ => fault "self"
    | _, _ => typeError "count() takes exactly one argument"
  | "list", "remove" =>
    match self, args with
    | .ref a, [x] =>
      match ← getObj a with
      | .list items =>
        match ← indexOfEq om ctx x 0 items.toList with
        | some i => setObj a (.list (items.eraseIdxIfInBounds i)); pure .none
        | none => valueError "list.remove(x): x not in list"
      | _ => fault "self"
    | _, _ => typeError "remove() takes exactly one argument"
  | "dict", "get" =>
    match args with
    | k :: rest =>
      match ← dictGet om ctx self k with
      | some v => pure v
      | none => pure (rest.headD .none)
    | [] => typeError "get expected at least 1 argument, got 0"
  | "dict", "keys" | "dict", "values" | "dict", "items" =>
    match self with
    | .ref a => alloc (.dictView a (match name with | "keys" => 0 | "values" => 1 | _ => 2))
    | _ => fault "self"
  | "dict", "pop" =>
    match self, args with
    | .ref a, k :: rest =>
      match ← getObj a with
      | .dict d =>
        let h ← hashFor om ctx "dict key" k
        match ← dictFind (eqBool om ctx k) d h with
        | some i =>
          let v := d.entries[i]?.map (·.value)
          dictRemoveAt self d i
          pure (v.getD .null)
        | none =>
          match rest with
          | r :: _ => pure r
          | [] => raiseVal (← newExc (.cls "KeyError") [k])
      | _ => fault "self"
    | _, _ => typeError "pop expected at least 1 argument, got 0"
  | "dict", "setdefault" =>
    match args with
    | k :: rest =>
      match ← dictGet om ctx self k with
      | some v => pure v
      | none =>
        let v := rest.headD .none
        dictSet om ctx self k v
        pure v
    | [] => typeError "setdefault expected at least 1 argument, got 0"
  | "dict", "update" =>
    match args with
    | [o] => dictUpdateArgFwd om ctx self o; pure .none
    | _ => pure .none
  | "dict", "clear" =>
    match self with
    | .ref a =>
      let ver ← freshVersion
      setObj a (.dict { version := ver }); pure .none
    | _ => fault "self"
  | "dict", "copy" =>
    let d ← mkDict
    om.dictUpdate ctx d self
    pure d
  | "str", _ =>
    let s := match self with
      | .str x => x
      | _ => ""
    match name, args with
    | "join", [it] =>
      let parts ← seqToList om ctx it
      let strs ← parts.zipIdx.mapM fun (p, i) =>
        match p with
        | .str x => pure x
        | _ => do typeError s!"sequence item {i}: expected str instance, {← tpName p} found"
      pure (.str (joinStrs s strs))
    | "upper", [] => pure (.str s.toUpper)
    | "lower", [] => pure (.str s.toLower)
    | "strip", [] => pure (.str s.trimAscii.toString)
    | "split", [] =>
      mkList ((splitWs s).map .str)
    | "split", [.str sep] =>
      mkList ((s.splitOn sep).map .str)
    | "replace", [.str a, .str b] =>
      pure (.str (joinStrs b (s.splitOn a)))
    | "startswith", [.str p] => pure (.bool (s.startsWith p))
    | "endswith", [.str p] => pure (.bool (s.endsWith p))
    | "find", [.str p] =>
      let parts := s.splitOn p
      if parts.length > 1 then pure (.int (parts.headD "").length) else pure (.int (-1))
    | "isdigit", [] => pure (.bool (s != "" && s.toList.all Char.isDigit))
    | _, _ => typeError s!"str.{name}: unsupported arguments"
  | "set", "add" =>
    match args with
    | [v] =>
      setAdd om ctx self v
      pure .none
    | _ => typeError s!"set.add() takes exactly one argument ({args.length} given)"
  | "set", "discard" | "set", "remove" =>
    match self, args with
    | .ref a, [k] =>
      match ← getObj a with
      | .set f items =>
        let h ← hashFor om ctx "set element" k
        let rest ← items.toList.filterM fun kv => do
          if kv.1 == h then return !(← eqBool om ctx k kv.2) else pure true
        if rest.length == items.size && name == "remove" then
          raiseVal (← newExc (.cls "KeyError") [k])
        setObj a (.set f rest.toArray)
        pure .none
      | _ => fault "self"
    | _, _ => typeError "set.remove() takes exactly one argument"
  | "set", "pop" =>
    match self with
    | .ref a =>
      match ← getObj a with
      | .set f items =>
        match items.toList with
        | kv :: rest => setObj a (.set f rest.toArray); pure kv.2
        | [] => raiseS "KeyError" "pop from an empty set"
      | _ => fault "self"
    | _ => fault "self"
  | "set", "clear" =>
    match self with
    | .ref a => setObj a (.set false #[]); pure .none
    | _ => fault "self"
  | "set", "copy" | "frozenset", "copy" =>
    match self with
    | .ref a =>
      match ← getObj a with
      | .set f items => alloc (.set f items)
      | _ => fault "self"
    | _ => fault "self"
  | "set", "union" | "frozenset", "union" =>
    match args with
    | [o] => do
      let s ← om.call ctx (.cls tp) [self] []
      om.setUpdate ctx s o
      pure s
    | _ => pure self
  | "set", "intersection" | "frozenset", "intersection" =>
    match args with
    | [o] => do
      let s ← alloc (.set (tp == "frozenset") #[])
      for v in ← seqToList om ctx self do
        if ← om.contains ctx o v then setAdd om ctx s v
      pure s
    | _ => pure self
  | "generator", "send" | "coroutine", "send" =>
    match self, args with
    | .ref a, [v] => genSend ctx a (some v)
    | _, _ => typeError s!"generator.send() takes exactly one argument ({args.length} given)"
  | "generator", "close" | "coroutine", "close" =>
    match self with
    | .ref a => genCloseV P om ctx a
    | _ => fault "self"
  | "generator", "throw" | "coroutine", "throw" =>
    match self, args with
    | .ref a, typ :: _ => genThrow 32 a typ
    | _, _ => typeError "throw expected at least 1 argument, got 0"
  | "BaseException", "with_traceback" => pure self
  | "object", "__init__" => pure .none
  | "object", "__repr__" => pure (.str s!"<{← tpName self} object>")
  | "object", "__str__" => om.str ctx self
  | "object", "__eq__" =>
    match args with
    | [o] => pure (if self == o then .bool true else .notImpl)
    | _ => typeError "__eq__ expected 1 argument"
  | "object", "__ne__" =>
    match args with
    | [o] => pure (.bool (self != o))
    | _ => typeError "__ne__ expected 1 argument"
  | "object", "__hash__" => pure (.int (← om.hash ctx self))
  | "object", "__setattr__" =>
    match args with
    | [.str n, v] =>
      match self with
      | .ref a =>
        match ← getObj a with
        | .inst i =>
          let d ← instDict a i
          dictSetStr d n v
          pure .none
        | _ => noAttr self n
      | _ => noAttr self n
    | _ => typeError "__setattr__ expected 2 arguments"
  | "object", "__getattribute__" =>
    match args with
    | [.str n] => genericGetAttr om ctx self n
    | _ => typeError "__getattribute__ expected 1 argument"
  | "object", "__delattr__" => pure .none
  | "object", "__init_subclass__" => pure .none
  | "property", _ =>
    match self, args with
    | .ref a, [f] =>
      match ← getObj a with
      | .property g s d =>
        match name with
        | "setter" => alloc (.property g f d)
        | "getter" => alloc (.property f s d)
        | _ => alloc (.property g s f)
      | _ => fault "self"
    | _, _ => typeError "property method takes one argument"
  | _, _ => typeError s!"{tp}.{name}: not modelled"
where
  /-- `_gen_throw` with `tb = NULL` and the one-argument `throw`,
  `Objects/genobject.c:624-726`. The generator is `FRAME_EXECUTING` from :649 on, through
  every look at the sub-iterator. Only a successful call into it, the failed lookup of its
  `throw` and a failed `gen_set_exception` write the old state back. -/
  genThrow : Nat → Addr → Val → RM Val
    | 0, _, _ => throw .fuel
    | fuel + 1, a, typ => do
      let g ← getGen a
      let state := g.frameState
      -- `gen_set_exception`, :546-601, with `val` and `tb` absent
      let setException : RM Val := do
        if ← isExcClass typ then om.call ctx typ [] []
        else if ← isExcInstance typ then pure typ
        else typeError s!"exceptions must be classes or instances deriving from BaseException, not {← tpName typ}"
      if state == 4 then alreadyExecuting g.kind
      if state == 5 then
        if g.kind == .coro then runtimeError "cannot reuse already awaited coroutine"
        throw (.exc (← tryExc setException fun e => pure e))
      let restore : RM Unit := do
        let g2 ← getGen a
        setObj a (.gen { g2 with frameState := state })
      let throwHere : RM Val := do
        let exc ← tryExc setException fun e => do restore; throw (.exc e)
        genThrowCurrent ctx a exc
      setObj a (.gen { g with frameState := 4 })
      match genYf g with
      | none => throwHere
      | some yf =>
        if ← givenMatches typ 8 (.cls "GeneratorExit") then
          let err ← tryExc (do genCloseIter P om ctx 32 yf; pure (Option.none)) fun e => pure (some e)
          match err with
          | some e => return ← genThrowCurrent ctx a e
          | none => return ← throwHere
        let after (r : Except Val Val) : RM Val :=
          match r with
          | .ok v => do restore; pure v
          | .error e => genThrowCurrent ctx a e
        match ← genKindOf yf with
        | some .gen | some .coro =>
          match yf with
          | .ref y => after (← tryExc (Except.ok <$> genThrow fuel y typ) fun e => pure (Except.error e))
          | _ => throwHere
        | _ =>
          match ← tryExc (optAttr om ctx yf "throw") fun e => do restore; throw (.exc e) with
          | none => throwHere
          | some m => after (← tryExc (Except.ok <$> call1 om ctx m [typ]) fun e => pure (Except.error e))

/-- `min`/`max`. -/
def minMax (name : String) (op : Nat) (args : List Val) (kw : List String) : RM Val := do
  let npos := args.length - kw.length
  let pos := args.take npos
  let key := (kwGet args kw "key").getD .none
  let items ← match pos with
    | [it] => seqToList om ctx it
    | _ => pure pos
  match items with
  | [] =>
    match kwGet args kw "default" with
    | some d => pure d
    | none => valueError s!"{name}() iterable argument is empty"
  | x :: rest =>
    let kf (v : Val) : RM Val := if key == .none then pure v else call1 om ctx key [v]
    let mut best := x
    let mut bk ← kf x
    for v in rest do
      let k ← kf v
      if ← cmpBool om ctx k bk op then
        best := v
        bk := k
    pure best

/-- `range(...)`, `Objects/rangeobject.c`. -/
def rangeNew (args : List Val) : RM Val := do
  let need (v : Val) : RM Int := do
    match ← asIndex om ctx v with
    | some n => pure n
    | none => typeError s!"'{← tpName v}' object cannot be interpreted as an integer"
  let (start, stop, step) ← match args with
    | [a] => pure ((0 : Int), ← need a, (1 : Int))
    | [a, b] => pure (← need a, ← need b, 1)
    | [a, b, c] => pure (← need a, ← need b, ← need c)
    | [] => typeError "range expected at least 1 argument, got 0"
    | _ => typeError s!"range expected at most 3 arguments, got {args.length}"
  if step == 0 then valueError "range() arg 3 must not be zero"
  let len :=
    if step > 0 then (if start < stop then (stop - start - 1) / step + 1 else 0)
    else (if start > stop then (start - stop - 1) / (-step) + 1 else 0)
  alloc (.range start stop step len)

/-- Calling a builtin type. -/
def callType (n : String) (args : List Val) (kw : List String) : RM Val := do
  match n with
  | "int" =>
    match args with
    | [] => pure (.int 0)
    | [v] =>
      match ← payload v with
      | .int i => pure (.int i)
      | .bool b => pure (.int (if b then 1 else 0))
      | .float b =>
        if Num.isNan b then valueError "cannot convert float NaN to integer"
        if Num.isInf b then raiseS "OverflowError" "cannot convert float infinity to integer"
        let (x, d) := Num.toRat b
        pure (.int (Int.tdiv x ((2 : Int) ^ d)))
      | .str s =>
        match intFromStr s with
        | some i => pure (.int i)
        | none => valueError s!"invalid literal for int() with base 10: {strRepr s}"
      -- `PyNumber_Long` -> `_PyLong_FromBytes`, longobject.c:3166
      | .bytes b =>
        match intFromStr (String.ofList (b.map fun x => Char.ofNat x.toNat)) with
        | some i => pure (.int i)
        | none => valueError s!"invalid literal for int() with base 10: {bytesRepr (b.take 200)}"
      | x =>
        match ← callDunder om ctx x "__int__" [] with
        | some r => pure r
        | none => typeError s!"int() argument must be a string, a bytes-like object or a real number, not '{← tpName x}'"
    | _ => typeError "int() takes at most 1 argument in this model"
  | "float" =>
    match args with
    | [] => pure (.float 0)
    | [v] =>
      match ← toFloatBits (← payload v) with
      | some b => pure (.float b)
      | none => typeError s!"float() argument must be a string or a real number, not '{← tpName v}'"
    | _ => typeError "float expected at most 1 argument"
  | "str" =>
    match args with
    | [] => pure (.str "")
    | [v] => om.str ctx v
    | _ => typeError "str() takes at most 1 argument in this model"
  | "bool" =>
    match args with
    | [] => pure (.bool false)
    | [v] => pure (.bool (← om.isTrue ctx v))
    | _ => typeError s!"bool expected at most 1 argument, got {args.length}"
  | "list" =>
    match args with
    | [] => mkList []
    | [v] => mkList (← seqToList om ctx v)
    | _ => typeError s!"list expected at most 1 argument, got {args.length}"
  | "tuple" =>
    match args with
    | [] => mkTuple []
    | [v] =>
      if ← isExactTuple v then pure v else mkTuple (← seqToList om ctx v)
    | _ => typeError s!"tuple expected at most 1 argument, got {args.length}"
  | "set" | "frozenset" =>
    let s ← alloc (.set (n == "frozenset") #[])
    match args with
    | [] => pure s
    | [v] =>
      for x in ← seqToList om ctx v do
        setAdd om ctx s x
      pure s
    | _ => typeError s!"{n} expected at most 1 argument, got {args.length}"
  | "dict" =>
    let d ← mkDict
    let npos := args.length - kw.length
    if let [m] := args.take npos then dictUpdateArgFwd om ctx d m
    for (k, v) in kw.zip (args.drop npos) do dictSetStr d k v
    pure d
  | "range" => rangeNew om ctx args
  | "slice" =>
    match args with
    | [a] => alloc (.slice .none a .none)
    | [a, b] => alloc (.slice a b .none)
    | [a, b, c] => alloc (.slice a b c)
    | _ => typeError "slice expected at least 1 argument"
  | "object" =>
    if !args.isEmpty then typeError "object() takes no arguments"
    alloc (.inst { cls := .cls "object" })
  | "type" =>
    match args with
    | [v] => typeOf v
    | _ => typeError "type() takes 1 or 3 arguments"
  | "super" =>
    match args with
    | [c, o] =>
      let ot ← if ← isType o then
          (if ← isSubtype o c then pure o else typeOf o)
        else typeOf o
      if !(← isSubtype ot c) then
        typeError "super(type, obj): obj must be an instance or subtype of type"
      alloc (.super c o ot)
    | _ => typeError "super() without arguments is not modelled here"
  | "property" =>
    let g := (args.getD 0 .none)
    alloc (.property (if g == .none then .null else g) .null .null)
  | "staticmethod" => alloc (.staticMethod (args.headD .null))
  | "classmethod" => alloc (.classMethod (args.headD .null))
  | "enumerate" =>
    match args with
    | it :: rest =>
      let start := match rest with
        | [.int s] => s
        | _ => match kwGet args kw "start" with
          | some (.int s) => s
          | _ => 0
      alloc (.enumerate (← om.getIter ctx it) start)
    | [] => typeError "enumerate() missing required argument 'iterable'"
  | "zip" =>
    let its ← args.mapM (om.getIter ctx)
    alloc (.zip its false)
  | "map" =>
    match args with
    | f :: its =>
      let its ← its.mapM (om.getIter ctx)
      alloc (.map f its)
    | [] => typeError "map() must have at least two arguments."
  | "filter" =>
    match args with
    | [f, it] => alloc (.filter f (← om.getIter ctx it))
    | _ => typeError s!"filter expected 2 arguments, got {args.length}"
  | "reversed" =>
    match args with
    | [v] =>
      if let .ref a := v then
        match ← getObj a with
        | .list items | .tuple items => return ← alloc (.reversed v ((items.size : Int) - 1))
        | .range .. | .inst _ =>
          return ← alloc (.reversed v ((← om.length ctx v) - 1))
        | _ => pure ()
      if let .str s := v then return ← alloc (.reversed v ((s.length : Int) - 1))
      typeError s!"'{← tpName v}' object is not reversible"
    | _ => typeError s!"reversed expected 1 argument, got {args.length}"
  | _ =>
    if isBuiltinExcName n then excNew (.cls n) (args.take (args.length - kw.length))
    else typeError s!"cannot create '{n}' instances"

/-- Builtin functions, `Python/bltinmodule.c`. -/
def callBuiltin (n : String) (args : List Val) (kw : List String) : RM Val := do
  let npos := args.length - kw.length
  let pos := args.take npos
  match n, pos with
  | "print", _ =>
    let parts ← pos.mapM fun v => do return strOf (← om.str ctx v)
    let sep := match kwGet args kw "sep" with
      | some (.str s) => s
      | _ => " "
    let en := match kwGet args kw "end" with
      | some (.str s) => s
      | _ => "\n"
    write (joinStrs sep parts ++ en)
    pure .none
  | "len", [v] => pure (.int (← om.length ctx v))
  | "len", _ => typeError s!"len() takes exactly one argument ({args.length} given)"
  | "repr", [v] => om.repr ctx v
  | "iter", [v] => om.getIter ctx v
  | "iter", [c, s] =>
    alloc (.callIter c s)
  | "next", v :: rest =>
    if !(← om.isIterator v) then typeError s!"'{← tpName v}' object is not an iterator"
    let r ← tryExc (om.iterNext ctx v) fun e => do
      if !rest.isEmpty && (← givenMatches e 8 (.cls "StopIteration")) then pure none
      else throw (.exc e)
    match r, rest with
    | some x, _ => pure x
    | none, d :: _ => pure d
    | none, [] => stopIter .none
  | "abs", [v] =>
    match v with
    | .int i => pure (.int i.natAbs)
    | .bool b => pure (.int (if b then 1 else 0))
    | .float b => pure (.float (b &&& 0x7FFFFFFFFFFFFFFF))
    | _ =>
      match ← callDunder om ctx v "__abs__" [] with
      | some r => pure r
      | none => typeError s!"bad operand type for abs(): '{← tpName v}'"
  | "min", _ => minMax om ctx "min" 0 args kw
  | "max", _ => minMax om ctx "max" 4 args kw
  | "sum", it :: rest =>
    let mut acc := rest.headD (.int 0)
    for v in ← seqToList om ctx it do
      acc ← om.binaryOp ctx 0 acc v
    pure acc
  | "sorted", [it] =>
    let xs ← seqToList om ctx it
    let s ← sortVals om ctx xs ((kwGet args kw "key").getD .none)
      (match kwGet args kw "reverse" with | some (.bool b) => b | _ => false)
    mkList s
  | "any", [it] =>
    let xs ← seqToList om ctx it
    pure (.bool (← xs.anyM (om.isTrue ctx)))
  | "all", [it] =>
    let xs ← seqToList om ctx it
    pure (.bool (← xs.allM (om.isTrue ctx)))
  | "isinstance", [a, b] => pure (.bool (← om.isInstance ctx a b))
  | "issubclass", [a, b] => pure (.bool (← isSubclassImpl a 8 b))
  | "getattr", [o, .str name] => om.getAttr ctx o name
  | "getattr", [o, .str name, d] =>
    match ← optAttr om ctx o name with
    | some v => pure v
    | none => pure d
  | "setattr", [o, .str name, v] => om.setAttr ctx o name v; pure .none
  | "delattr", [o, .str name] => om.delAttr ctx o name; pure .none
  | "hasattr", [o, .str name] => pure (.bool (← optAttr om ctx o name).isSome)
  | "callable", [v] =>
    match v with
    | .builtin _ | .cls _ | .methDescr .. => pure (.bool true)
    | .ref a =>
      match ← getObj a with
      | .func _ | .method .. | .cls _ | .boundBuiltin .. => pure (.bool true)
      | .inst i => pure (.bool (← userLookup i.cls "__call__").isSome)
      | _ => pure (.bool false)
    | _ => pure (.bool false)
  | "hash", [v] => pure (.int (← om.hash ctx v))
  | "ord", [.str s] =>
    match s.toList with
    | [c] => pure (.int c.toNat)
    | _ => typeError s!"ord() expected a character, but string of length {s.length} found"
  | "chr", [.int i] => pure (.str (Char.ofNat i.toNat).toString)
  | "divmod", [a, b] =>
    let q ← om.binaryOp ctx 2 a b
    let r ← om.binaryOp ctx 6 a b
    mkTuple [q, r]
  | "pow", [a, b] => om.binaryOp ctx 8 a b
  | "__build_class__", _ => buildClassBuiltin P ctx args
  | "format", [v] => om.format ctx v .null
  | "format", [v, s] => om.format ctx v s
  | "id", [v] =>
    match v with
    | .ref a => pure (.int a)
    | _ => pure (.int 0)
  | _, _ => typeError s!"{n}: not modelled"

/-- `PyObject_Vectorcall`. -/
def callImpl (f : Val) (args : List Val) (kw : List String) : RM Val := do
  match f with
  | .builtin n => callBuiltin P om ctx n args kw
  | .cls n =>
    callType om ctx n args kw
  | .methDescr tp n =>
    match args with
    | self :: rest =>
      if !(← isSubtype (← typeOf self) (.cls tp)) then
        typeError s!"descriptor '{n}' for '{tp}' objects doesn't apply to a '{← tpName self}' object"
      callMethod P om ctx tp n self rest kw
    | [] => typeError s!"unbound method {tp}.{n}() needs an argument"
  | .ref a =>
    match ← getObj a with
    | .func _ =>
      let fo ← getFunc f
      let co ← getCodeR P fo.code
      evalVector P ctx f (localsFor co fo) args kw
    | .method fn s => om.call ctx fn (s :: args) kw
    | .boundBuiltin tp n s => callMethod P om ctx tp n s args kw
    | .cls _ => instantiate om ctx f args kw
    | .inst i =>
      match ← userLookup i.cls "__call__" with
      | some c =>
        let b ← descrBind om ctx c f i.cls
        om.call ctx b args kw
      | none => typeError s!"'{← tpName f}' object is not callable"
    | _ => typeError s!"'{← tpName f}' object is not callable"
  | _ => typeError s!"'{← tpName f}' object is not callable"

/-- `_PyObject_LookupSpecialMethod`, `Objects/typeobject.c`. -/
def lookupSpecialImpl (o : Val) (name : String) : RM (Option (Val × Val)) := do
  let tp ← typeOf o
  match ← typeLookup tp name with
  | none => pure none
  | some d =>
    let methLike ← match d with
      | .methDescr .. => pure true
      | .ref a =>
        match ← getObj a with
        | .func _ => pure true
        | _ => pure false
      | _ => pure false
    if methLike then pure (some (d, o))
    else pure (some (← descrBind om ctx d o tp, .null))

/-- `_PySuper_Lookup`, `Objects/typeobject.c`: walk the MRO of `type(obj)` after
`su_type`. -/
def superLookupImpl (suType suObj : Val) (name : String) (wantMethod : Bool) : RM (Val × Bool) := do
  let objType ← if ← isType suObj then
      (if ← isSubtype suObj suType then pure suObj else typeOf suObj)
    else typeOf suObj
  if !(← isSubtype objType suType) then
    typeError "super(type, obj): obj must be an instance or subtype of type"
  let mro ← mroOf objType
  let rest := (mro.dropWhile (· != suType)).drop 1
  let rec go : List Val → RM (Option Val)
    | [] => pure none
    | .cls n :: r =>
      match builtinOwnAttr n name with
      | some v => pure (some v)
      | none => go r
    | .ref a :: r => do
      match ← getObj a with
      | .cls c =>
        match ← dictGetStr (.ref c.dict) name with
        | some v => pure (some v)
        | none => go r
      | _ => go r
    | _ :: r => go r
  match ← go rest with
  | some d =>
    let isFn ← match d with
      | .methDescr .. => pure true
      | .ref a =>
        match ← getObj a with
        | .func _ => pure true
        | _ => pure false
      | _ => pure false
    if wantMethod && isFn then pure (d, true)
    else
      let obj := if suObj == objType then Val.null else suObj
      pure (← descrBind om ctx d obj objType, false)
  | none =>
    raiseS "AttributeError" s!"'super' object has no attribute '{name}'"

/-- `PyDict_Update`/`_PyDict_MergeEx`: `override = 2` raises `KeyError` on a
duplicate key. -/
def dictMergeImpl (override : Nat) (d o : Val) : RM Unit := do
  if ← isExactDict o then
    let src ← getDict o
    for en in src.entries.toList do
      if override == 2 then
        if (← dictGet om ctx d en.key).isSome then
          raiseVal (← newExc (.cls "KeyError") [en.key])
      dictSet om ctx d en.key en.value
    return ()
  match ← optAttr om ctx o "keys" with
  | some kf =>
    let keys ← seqToList om ctx (← call1 om ctx kf [])
    for k in keys do
      if override == 2 then
        if (← dictGet om ctx d k).isSome then
          raiseVal (← newExc (.cls "KeyError") [k])
      dictSet om ctx d k (← om.getItem ctx o k)
  | none =>
    raiseVal (← newExc (.cls "AttributeError") [.str s!"'{← tpName o}' object has no attribute 'keys'"])

/-- `stopiteration_error`, `Python/intrinsics.c:140-182`. -/
def stopIterationError (f : Frame) (exc : Val) : RM Val := do
  let co ← getCodeR P f.code
  let msg? ← if ← givenMatches exc 8 (.cls "StopIteration") then
      pure (some (if flagSet co.flags coAsyncGenerator then "async generator raised StopIteration"
        else if flagSet co.flags coCoroutine then "coroutine raised StopIteration"
        else "generator raised StopIteration"))
    else if flagSet co.flags coAsyncGenerator && (← givenMatches exc 8 (.cls "StopAsyncIteration")) then
      pure (some "async generator raised StopAsyncIteration")
    else pure none
  match msg? with
  | some m =>
    let err ← newExc (.cls "RuntimeError") [.str m]
    setCause err exc
    setContext err exc
    pure err
  | none => pure exc

/-- `_PyIntrinsics_UnaryFunctions`, `Python/intrinsics.c:208-222`. -/
def intrinsic1Impl (f : Frame) (n : Nat) (v : Val) : RM Val := do
  match n with
  | 0 => raiseS "SystemError" "invalid intrinsic function"
  | 1 =>
    if v != .none then write (strOf (← om.repr ctx v) ++ "\n")
    pure .none
  | 3 => stopIterationError P f v
  | 5 => positiveImpl om ctx v
  | 6 =>
    match v with
    | .ref a =>
      match ← getObj a with
      | .list items => mkTuple items.toList
      | _ => fault "list_to_tuple on a non-list"
    | _ => fault "list_to_tuple on a non-list"
  | _ => fault "intrinsic not modelled"

/-- `_PyIntrinsics_BinaryFunctions`, `Python/intrinsics.c:257-265`. -/
def intrinsic2Impl (_ : Frame) (n : Nat) (_ _ : Val) : RM Val := do
  match n with
  | 0 => raiseS "SystemError" "invalid intrinsic function"
  | _ => fault "intrinsic not modelled"

/-- `_PyCoro_GetAwaitableIter`, `Objects/genobject.c:1246-1287`. The coroutine test comes
first. `%T` omits the module for `__main__` and `builtins`, the only modules here. -/
def awaitableIter (o : Val) : RM Val := do
  match ← genKindOf o with
  | some .coro => pure o
  | _ =>
    match ← callDunder om ctx o "__await__" [] with
    | some r =>
      if (← genKindOf r) == some .coro then
        typeError s!"{← tpName o}.__await__() must return an iterator, not coroutine"
      if !(← om.isIterator r) then
        typeError s!"{← tpName o}.__await__() must return an iterator, not {← tpName r}"
      pure r
    | none => typeError s!"'{← tpName o}' object can't be awaited"

/-- `_PyEval_GetAwaitable`, `Python/ceval.c:3645-3667`. -/
def getAwaitableImpl (o : Val) (oparg : Nat) : RM Val := do
  let r ← tryExc (awaitableIter om ctx o) fun e => do
    if (← userLookup (← typeOf o) "__await__").isNone && (← genKindOf o) != some .coro then
      let t ← tpName o
      if oparg == 1 then
        typeError s!"'async with' received an object from __aenter__ that does not implement __await__: {t}"
      if oparg == 2 then
        typeError s!"'async with' received an object from __aexit__ that does not implement __await__: {t}"
    throw (.exc e)
  if (← genKindOf r) == some .coro then
    if let .ref a := r then
      if (genYf (← getGen a)).isSome then
        runtimeError "coroutine is being awaited already"
  pure r

/-- `GET_AITER`, `Python/bytecodes.c:1607-1641`. -/
def getAIterImpl (o : Val) : RM Val := do
  match ← callDunder om ctx o "__aiter__" [] with
  | none =>
    typeError s!"'async for' requires an object with __aiter__ method, got {← tpName o}"
  | some it =>
    if (← userLookup (← typeOf it) "__anext__").isNone then
      typeError s!"'async for' received an object from __aiter__ that does not implement __anext__: {← tpName it}"
    pure it

/-- `_PyEval_GetANext`, `Python/ceval.c:3557-3594`. -/
def getANextImpl (o : Val) : RM Val := do
  match ← callDunder om ctx o "__anext__" [] with
  | none =>
    typeError s!"'async for' requires an iterator with __anext__ method, got {← tpName o}"
  | some n =>
    tryExc (awaitableIter om ctx n) fun e => do
      if ← givenMatches e 8 (.cls "TypeError") then
        let err ← newExc (.cls "TypeError")
          [.str s!"'async for' received an invalid object from __anext__: {← tpName n}"]
        setCause err e
        setContext err e
        raiseVal err
      else throw (.exc e)

/-- `_PyEval_MatchKeys`, `Python/ceval.c:437-523`. -/
def matchKeysImpl (m keys : Val) : RM Val := do
  let ks ← tupleItems keys
  if ks.size == 0 then return ← mkTuple []
  let (getm, slf) ← om.getMethod ctx m "get"
  let dummy ← alloc (.inst { cls := .cls "object" })
  let mut seen : List Val := []
  let mut vals : List Val := []
  for k in ks.toList do
    if ← seen.anyM (eqBool om ctx k) then
      valueError s!"mapping pattern checks duplicate key ({strOf (← om.repr ctx k)})"
    seen := k :: seen
    let args := if slf != .null then [slf, k, dummy] else [k, dummy]
    let v ← om.call ctx getm args []
    if v == dummy then return .none
    vals := v :: vals
  mkTuple vals.reverse

/-- `match_class_attr`, `Python/ceval.c:528-549`. -/
def matchClassAttr (subject typ : Val) (name : String) (seen : List String) :
    RM (Option Val × List String) := do
  if seen.contains name then
    typeError s!"{← typeNameOf typ}() got multiple sub-patterns for attribute {strRepr name}"
  pure (← optAttr om ctx subject name, name :: seen)

/-- Types that match themselves positionally, `_Py_TPFLAGS_MATCH_SELF`. -/
def matchSelf (t : Val) : Bool :=
  match t with
  | .cls n =>
    ["bool", "bytearray", "bytes", "dict", "float", "frozenset", "int", "list", "set", "str",
     "tuple"].contains n
  | _ => false

/-- `_PyEval_MatchClass`, `Python/ceval.c:553-669`. -/
def matchClassImpl (subject typ : Val) (nargs : Nat) (kwargs : Val) : RM (Option Val) := do
  if !(← isType typ) then typeError "called match pattern must be a class"
  if !(← om.isInstance ctx subject typ) then return none
  let mut seen : List String := []
  let mut attrs : List Val := []
  if nargs != 0 then
    let ma ← optAttr om ctx typ "__match_args__"
    let tn ← typeNameOf typ
    let (names, selfMatch) ← match ma with
      | some v =>
        if !(← isExactTuple v) then
          typeError s!"{tn}.__match_args__ must be a tuple (got {← tpName v})"
        pure ((← tupleItems v).toList, false)
      | none => pure ([], matchSelf typ)
    let allowed := if selfMatch then 1 else names.length
    if allowed < nargs then
      typeError s!"{tn}() accepts {allowed} positional sub-pattern{if allowed == 1 then "" else "s"} ({nargs} given)"
    if selfMatch then attrs := [subject]
    else
      for nm in names.take nargs do
        match nm with
        | .str n =>
          let (a, s) ← matchClassAttr om ctx subject typ n seen
          seen := s
          match a with
          | some x => attrs := x :: attrs
          | none => return none
        | _ => typeError s!"__match_args__ elements must be strings (got {← tpName nm})"
  for nm in (← tupleItems kwargs).toList do
    let (a, s) ← matchClassAttr om ctx subject typ (strOf nm) seen
    seen := s
    match a with
    | some x => attrs := x :: attrs
    | none => return none
  pure (some (← mkTuple attrs.reverse))

/-- `tp_flags & Py_TPFLAGS_MAPPING`/`SEQUENCE`. -/
def isMappingImpl (v : Val) : RM Bool := do
  match v with
  | .ref a =>
    match ← getObj a with
    | .dict _ => pure true
    | .inst i => pure (i.base != .null && (← om_isDict i.base))
    | _ => pure false
  | _ => pure false
where om_isDict (b : Val) : RM Bool := isExactDict b

def isSequenceImpl (v : Val) : RM Bool := do
  match v with
  | .ref a =>
    match ← getObj a with
    | .list _ | .tuple _ | .range .. => pure true
    | .inst i =>
      match i.base with
      | .ref _ => do return (← isExactList i.base) || (← isExactTuple i.base)
      | _ => pure false
    | _ => pure false
  | _ => pure false

/-- `except*`: `exc.split(match_type)`. -/
def egSplitImpl (_ _ : Val) : RM (Val × Val) := fault "exception group split not modelled"

end

/-- The record. `n` bounds the depth of purely C-level protocol nesting; Python
code re-enters through `Ctx.evalFrame`, which uses the outermost record. -/
def mkOM (P : Program) : Nat → ObjModel
  | 0 =>
    let bad {α : Type} : RM α := throw .fuel
    { isTrue := fun _ _ => bad, negative := fun _ _ => bad, invert := fun _ _ => bad
      binaryOp := fun _ _ _ _ => bad, richCompare := fun _ _ _ _ => bad, contains := fun _ _ _ => bad
      getItem := fun _ _ _ => bad, setItem := fun _ _ _ _ => bad, delItem := fun _ _ _ => bad
      getAttr := fun _ _ _ => bad, getMethod := fun _ _ _ => bad, setAttr := fun _ _ _ _ => bad
      delAttr := fun _ _ _ => bad, getIter := fun _ _ => bad, iterNext := fun _ _ => bad
      isIterator := fun _ => bad, isIterable := fun _ => bad, call := fun _ _ _ _ => bad
      str := fun _ _ => bad, repr := fun _ _ => bad, ascii := fun _ _ => bad
      format := fun _ _ _ => bad, length := fun _ _ => bad, hash := fun _ _ => bad
      lookupSpecial := fun _ _ _ => bad, superLookup := fun _ _ _ _ _ => bad
      genericGetattr := fun _ => bad, typeLookup := fun _ _ => bad, isInstance := fun _ _ _ => bad
      importName := fun _ _ _ _ _ => bad, importFrom := fun _ _ _ => bad, egSplit := fun _ _ _ => bad
      egWrap := fun _ _ => bad, matchClass := fun _ _ _ _ _ => bad, matchKeys := fun _ _ _ => bad
      isMapping := fun _ => bad, isSequence := fun _ => bad, getAIter := fun _ _ => bad
      getANext := fun _ _ => bad, getAwaitable := fun _ _ _ => bad, dictUpdate := fun _ _ _ => bad
      dictMerge := fun _ _ _ => bad, listExtend := fun _ _ _ => bad, setUpdate := fun _ _ _ => bad
      intrinsic1 := fun _ _ _ _ => bad, intrinsic2 := fun _ _ _ _ _ => bad
      buildInterpolation := fun _ _ _ _ _ => bad, buildTemplate := fun _ _ _ => bad }
  | n + 1 =>
    let om := mkOM P n
    { isTrue := fun ctx v => isTrueImpl om ctx v
      negative := fun ctx v => negativeImpl om ctx v
      invert := fun ctx v => invertImpl om ctx v
      binaryOp := fun ctx nb l r => binaryOpImpl om ctx nb l r
      richCompare := fun ctx l r op => richCompareImpl om ctx l r op
      contains := fun ctx c i => containsImpl om ctx c i
      getItem := fun ctx c k => getItemImpl om ctx c k
      setItem := fun ctx c k v => setItemImpl om ctx c k v
      delItem := fun ctx c k => delItemImpl om ctx c k
      getAttr := fun ctx o n => getAttrImpl om ctx o n
      getMethod := fun ctx o n => getMethodImpl om ctx o n
      setAttr := fun ctx o n v => setAttrImpl om ctx o n v
      delAttr := fun ctx o n => setAttrImpl om ctx o n .null
      getIter := fun ctx v => getIterImpl om ctx v
      iterNext := fun ctx v => iterNextImpl om ctx v
      isIterator := fun v => isIteratorImpl v
      isIterable := fun v => isIterableImpl v
      call := fun ctx f a k => callImpl P om ctx f a k
      str := fun ctx v => strImpl om ctx v
      repr := fun ctx v => reprImpl om ctx v
      ascii := fun ctx v => reprImpl om ctx v
      format := fun ctx v s => formatImpl om ctx v s
      length := fun ctx v => lengthImpl om ctx v
      hash := fun ctx v => hashImpl om ctx v
      lookupSpecial := fun ctx o n => lookupSpecialImpl om ctx o n
      superLookup := fun ctx c s n m => superLookupImpl om ctx c s n m
      genericGetattr := fun v => do
        return (← userLookup (← typeOf v) "__getattribute__").isNone
      typeLookup := typeLookup
      isInstance := fun ctx i t => isInstanceImpl i t
      importName := fun _ _ n _ _ => raiseS "ModuleNotFoundError" s!"No module named '{n}'"
      importFrom := fun ctx v n => om.getAttr ctx v n
      egSplit := fun ctx a b => egSplitImpl a b
      egWrap := fun _ _ => fault "exception groups not modelled"
      matchClass := fun ctx s t n k => matchClassImpl om ctx s t n k
      matchKeys := fun ctx m k => matchKeysImpl om ctx m k
      isMapping := fun v => isMappingImpl v
      isSequence := fun v => isSequenceImpl v
      getAIter := fun ctx o => getAIterImpl om ctx o
      getANext := fun ctx o => getANextImpl om ctx o
      getAwaitable := fun ctx o n => getAwaitableImpl om ctx o n
      dictUpdate := fun ctx d o => dictMergeImpl om ctx 1 d o
      dictMerge := fun ctx d o => dictMergeImpl om ctx 2 d o
      listExtend := fun ctx l o => do
        let vals ← seqToList om ctx o
        for v in vals do listAppend l v
      setUpdate := fun ctx s o => do
        for v in ← seqToList om ctx o do
          setAdd om ctx s v
      intrinsic1 := fun ctx f n v => intrinsic1Impl P om ctx f n v
      intrinsic2 := fun _ f n a b => intrinsic2Impl f n a b
      buildInterpolation := fun _ _ _ _ _ => fault "template strings not modelled"
      buildTemplate := fun _ _ _ => fault "template strings not modelled" }

/-- The model used by the difftest. -/
def builtinOM (P : Program) : ObjModel := mkOM P 24

end PyLean.Bytecode.Proto
