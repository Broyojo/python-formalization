import PyLean.Bytecode.Exec
import PyLean.Bytecode.Num

/-!
A concrete `ObjModel`, enough to run real compiled programs through the machine
in the difftest: `int`, `bool`, `float`, `str`, `bytes`, `list`, `tuple`, `dict`,
`set`, `range`, `slice`, exceptions, functions, generators, classes with single
or multiple inheritance, descriptors and the dunder protocols.

The interpreter proper does not depend on this file: it is written against the
`ObjModel` structure, and `TypeObj` can replace this instance. Each function takes
the model itself as `om`, so nested protocol calls go back through the record.
-/

namespace PyLean.Bytecode.Proto

open PyLean.Bytecode Uop

/-- Method names of builtin types that the model implements. -/
def methodNames : String → List String
  | "list" => ["append", "extend", "pop", "insert", "remove", "reverse", "sort", "index", "count",
               "clear", "copy"]
  | "dict" => ["get", "keys", "values", "items", "pop", "setdefault", "update", "clear", "copy"]
  | "str" => ["join", "upper", "lower", "strip", "split", "replace", "startswith", "endswith",
              "find", "isdigit"]
  | "tuple" => ["index", "count"]
  | "set" => ["add", "remove", "discard", "pop", "union", "intersection", "clear", "copy"]
  | "frozenset" => ["union", "intersection", "copy"]
  | "generator" | "coroutine" => ["send", "throw", "close"]
  | "BaseException" => ["with_traceback", "add_note"]
  | "object" => ["__init__", "__repr__", "__str__", "__eq__", "__ne__", "__hash__",
                 "__setattr__", "__getattribute__", "__delattr__", "__init_subclass__"]
  | _ => []

/-- `_PyType_Lookup` in a builtin type's own `tp_dict`. -/
def builtinOwnAttr (tp name : String) : Option Val :=
  if (methodNames tp).contains name then some (.methDescr tp name) else none

/-- `_PyType_Lookup`. -/
def typeLookup (tp : Val) (name : String) : RM (Option Val) := do
  let rec go : List Val → RM (Option Val)
    | [] => pure none
    | .cls n :: rest =>
      match builtinOwnAttr n name with
      | some v => pure (some v)
      | none => go rest
    | .ref a :: rest => do
      match ← getObj a with
      | .cls c =>
        match ← dictGetStr (.ref c.dict) name with
        | some v => pure (some v)
        | none => go rest
      | _ => go rest
    | _ :: rest => go rest
  go (← mroOf tp)

/-- `_PyType_Lookup` restricted to classes defined in Python: the slot of a dunder
is only "overridden" when some heap type in the MRO defines it. -/
def userLookup (tp : Val) (name : String) : RM (Option Val) := do
  let rec go : List Val → RM (Option Val)
    | [] => pure none
    | .ref a :: rest => do
      match ← getObj a with
      | .cls c =>
        match ← dictGetStr (.ref c.dict) name with
        | some v => pure (some v)
        | none => go rest
      | _ => go rest
    | _ :: rest => go rest
  go (← mroOf tp)

/-- Unwrap the payload of an instance of a subclass of a builtin value type. -/
def payload : Val → RM Val
  | .ref a => do
    match ← getObj a with
    | .inst i => pure (if i.base != .null then i.base else .ref a)
    | _ => pure (.ref a)
  | v => pure v

def intOf : Val → Option Int
  | .int i => some i
  | .bool b => some (if b then 1 else 0)
  | _ => none

/-- `float()` of an int operand of a mixed operation. -/
def toFloatBits : Val → RM (Option UInt64)
  | .float b => pure (some b)
  | .int i =>
    let b := Num.ofInt i
    if Num.tooLarge b then raiseS "OverflowError" "int too large to convert to float" else pure (some b)
  | .bool b => pure (some (Num.ofInt (if b then 1 else 0)))
  | _ => pure none

/-- Symbols for the `unsupported operand` message, `binop_type_error`. -/
def opSymbol : Nat → String
  | 0 => "+" | 1 => "&" | 2 => "//" | 3 => "<<" | 4 => "@" | 5 => "*" | 6 => "%"
  | 7 => "|" | 8 => "** or pow()" | 9 => ">>" | 10 => "-" | 11 => "/" | 12 => "^"
  | 13 => "+=" | 14 => "&=" | 15 => "//=" | 16 => "<<=" | 17 => "@=" | 18 => "*=" | 19 => "%="
  | 20 => "|=" | 21 => "**=" | 22 => ">>=" | 23 => "-=" | 24 => "/=" | _ => "^="

/-- Dunder names. -/
def opDunder : Nat → String
  | 0 => "add" | 1 => "and" | 2 => "floordiv" | 3 => "lshift" | 4 => "matmul" | 5 => "mul"
  | 6 => "mod" | 7 => "or" | 8 => "pow" | 9 => "rshift" | 10 => "sub" | 11 => "truediv"
  | _ => "xor"

/-- The C library `pow` that `float_pow` calls. It is an oracle for the difftest
(`Binary64.floatPowCore` takes any `pow`); no proof depends on it. -/
def cpow (a b : Binary64.F64) : Binary64.F64 :=
  Binary64.F64.ofBits (Float.pow (Float.ofBits (ofF a)) (Float.ofBits (ofF b))).toBits.toNat

/-- `float` arithmetic, `Objects/floatobject.c:541-803`, through the exact mirrors in
`Binary64/Float.lean`. `(-2.5) ** 0.5` hands off to `complex_pow`, and the model has no
`complex` value: `bytecode_diff.py` excludes that case by name (`float-pow-complex`). -/
def floatBinary (nb : Nat) (a b : UInt64) : RM (Option Val) :=
  let (x, y) := (toF a, toF b)
  let fin (r : Binary64.F64) : RM (Option Val) := pure (some (.float (ofF r)))
  let raised {α} (e : PyExc) : RM α :=
    match e with
    | .zeroDivisionError m => raiseS "ZeroDivisionError" m
    -- `_Py_ADJUST_ERANGE1` then `PyErr_SetFromErrno`: `str(e)` shows the args tuple.
    | .overflowError _ => raiseS "OverflowError" "(34, 'Numerical result out of range')"
    | _ => fault "float arithmetic raised an unexpected exception"
  let lift (r : Py Binary64.F64) : RM (Option Val) :=
    match r with
    | .ok v => fin v
    | .error e => raised e
  match nb with
  | 0 => fin (Binary64.F64.add x y)
  | 5 => fin (Binary64.F64.mul x y)
  | 10 => fin (Binary64.F64.sub x y)
  | 11 => lift (if Binary64.F64.eq y Binary64.d0 then Binary64.zeroDiv else .ok (Binary64.F64.div x y))
  | 2 => lift (if Binary64.F64.eq y Binary64.d0 then Binary64.zeroDiv else .ok (Binary64.float_div_mod x y).1)
  | 6 => lift (Binary64.floatRemCore x y)
  | 8 =>
    match Binary64.floatPowCore cpow x y with
    | .ok (.float r) => fin r
    | .ok (.complexPow ..) => fault "float ** gives a complex result, which is not modelled"
    | .error e => raised e
  | _ => pure none

/-- `int` arithmetic, `Objects/longobject.c`. `none` is `NotImplemented`. -/
def intBinary (nb : Nat) (a b : Int) : RM (Option Val) :=
  match nb with
  | 0 => pure (some (.int (a + b)))
  | 1 => pure (some (.int (intAnd a b)))
  | 2 => if b == 0 then raiseS "ZeroDivisionError" "division by zero"
         else pure (some (.int (Int.fdiv a b)))
  | 3 => if b < 0 then valueError "negative shift count"
         else if a == 0 then pure (some (.int 0))
         else if b ≥ 1 <<< 24 then fault "left shift too large for the model"
         else pure (some (.int (a * (2 : Int) ^ b.toNat)))
  | 5 => pure (some (.int (a * b)))
  | 6 => if b == 0 then raiseS "ZeroDivisionError" "division by zero"
         else pure (some (.int (Int.fmod a b)))
  | 7 => pure (some (.int (intOr a b)))
  | 8 =>
    -- `long_pow`: a negative exponent goes to `float_pow`, longobject.c. The bases
    -- 0, 1, -1 are decided here so that a huge exponent costs nothing, as it does in
    -- the binary-exponentiation loop of `long_pow`.
    if b ≥ 0 then
      if a == 0 then pure (some (.int (if b == 0 then 1 else 0)))
      else if a == 1 then pure (some (.int 1))
      else if a == -1 then pure (some (.int (if b % 2 == 0 then 1 else -1)))
      else pure (some (.int (a ^ b.toNat)))
    else floatBinary 8 (Num.ofInt a) (Num.ofInt b)
  | 9 => if b < 0 then valueError "negative shift count"
         -- `long_rshift1`: a shift past every digit leaves the sign
         else if b ≥ 1 <<< 24 then pure (some (.int (if a < 0 then -1 else 0)))
         else pure (some (.int (Int.fdiv a ((2 : Int) ^ b.toNat))))
  | 10 => pure (some (.int (a - b)))
  | 11 =>
    if b == 0 then raiseS "ZeroDivisionError" "division by zero"
    -- `long_true_divide`, longobject.c:4853-4854: `negate ? -0.0 : 0.0`
    else if a == 0 then pure (some (.float (if b < 0 then 0x8000000000000000 else 0)))
    else
      let n := if b < 0 then -a else a
      let r := Num.ofRat n b.natAbs
      if Num.tooLarge r then raiseS "OverflowError" "integer division result too large for a float"
      else pure (some (.float r))
  | 12 => pure (some (.int (intXor a b)))
  | _ => pure none

def pyStrRepeat (s : String) (n : Int) : String :=
  String.join (List.replicate n.toNat s)

/-- `PySlice_AdjustIndices`, `Objects/sliceobject.c`: `(start, stop, slicelength)`. -/
def adjustIndices (length start stop step : Int) : Int × Int × Int :=
  let start :=
    if start < 0 then (let s := start + length; if s < 0 then (if step < 0 then -1 else 0) else s)
    else if start ≥ length then (if step < 0 then length - 1 else length) else start
  let stop :=
    if stop < 0 then (let s := stop + length; if s < 0 then (if step < 0 then -1 else 0) else s)
    else if stop ≥ length then (if step < 0 then length - 1 else length) else stop
  let n :=
    if step < 0 then (if stop < start then (start - stop - 1) / (-step) + 1 else 0)
    else (if start < stop then (stop - start - 1) / step + 1 else 0)
  (start, stop, n)

/-- `_PyEval_SliceIndex`, `Python/ceval.c:2948-2955`, for ints; `dflt` when `None`.
Out-of-range values saturate to `Py_ssize_t`. -/
def sliceIndex (v : Val) (dflt : Int) : RM Int :=
  let clamp (i : Int) : Int := max PyLean.ssizeMin (min PyLean.ssizeMax i)
  match v with
  | .none => pure dflt
  | .int i => pure (clamp i)
  | .bool b => pure (if b then 1 else 0)
  | _ => typeError "slice indices must be integers or None or have an __index__ method"

/-- `PySlice_Unpack` + `PySlice_AdjustIndices`: the picked positions. -/
def sliceRange (len : Int) (s t st : Val) : RM (List Nat) := do
  let step ← sliceIndex st 1
  if step == 0 then valueError "slice step cannot be zero"
  let step := max (-PyLean.ssizeMax) step
  let start ← sliceIndex s (if step < 0 then PyLean.ssizeMax else 0)
  let stop ← sliceIndex t (if step < 0 then PyLean.ssizeMin else PyLean.ssizeMax)
  let (b, _, n) := adjustIndices len start stop step
  pure ((List.range n.toNat).map fun (i : Nat) => (b + (i : Int) * step).toNat)

def strSlice (s : String) (idx : List Nat) : String :=
  let cs := s.toList
  String.ofList (idx.filterMap fun i => cs[i]?)

/-- `repr(str)`, `unicode_repr` for printable text. -/
def strRepr (s : String) : String :=
  let q := if s.contains '\'' && !s.contains '"' then '"' else '\''
  let esc (c : Char) : String :=
    if c == q then "\\" ++ c.toString
    else if c == '\\' then "\\\\"
    else if c == '\n' then "\\n"
    else if c == '\r' then "\\r"
    else if c == '\t' then "\\t"
    else if c.toNat < 32 || c.toNat == 127 then
      let h := Nat.toDigits 16 c.toNat
      "\\x" ++ String.ofList (List.replicate (2 - h.length) '0' ++ h)
    else c.toString
  q.toString ++ String.join (s.toList.map esc) ++ q.toString

def bytesRepr (b : List UInt8) : String :=
  let q := if b.contains 39 && !b.contains 34 then '"' else '\''
  let esc (x : UInt8) : String :=
    let n := x.toNat
    if n == q.toNat then "\\" ++ q.toString
    else if n == 92 then "\\\\"
    else if n == 10 then "\\n"
    else if n == 13 then "\\r"
    else if n == 9 then "\\t"
    else if n < 32 || n ≥ 127 then
      let h := Nat.toDigits 16 n
      "\\x" ++ String.ofList (List.replicate (2 - h.length) '0' ++ h)
    else (Char.ofNat n).toString
  "b" ++ q.toString ++ String.join (b.map esc) ++ q.toString

/-- `long_hash`: reduction modulo `2^61 - 1`, with `-1` replaced by `-2`. -/
def hashInt (i : Int) : Int :=
  let p : Int := 2305843009213693951
  let m := (i.natAbs : Int) % p
  let r := if i < 0 then -m else m
  if r == -1 then -2 else r

def isSubclassOf (a b : Val) : RM Bool := isSubtype a b

/-- C3 merge, `pmerge` in `Objects/typeobject.c`. -/
def c3Merge : Nat → List (List Val) → List Val → Option (List Val)
  | 0, _, _ => none
  | n + 1, seqs, acc =>
    let seqs := seqs.filter (!·.isEmpty)
    if seqs.isEmpty then some acc.reverse
    else
      let good (c : Val) : Bool := seqs.all fun s => !(s.drop 1).contains c
      match (seqs.filterMap (·.head?)).find? good with
      | none => none
      | some c =>
        c3Merge n (seqs.map fun s => if s.head? == some c then s.drop 1 else s) (c :: acc)

/-- Lexicographic order on byte strings. -/
def cmpNats : List Nat → List Nat → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | x :: xs, y :: ys => if x < y then .lt else if y < x then .gt else cmpNats xs ys

section
variable (P : Program) (om : ObjModel) (ctx : Ctx)

/-- `_PyEval_Vector`, `Python/ceval.c:2139-2183`. -/
def evalVector (f : Val) (locals : Val) (args : List Val) (kw : List String) : RM Val := do
  let nf ← framePushAndInit P f locals args kw
  ctx.evalFrame nf none

/-- Call a function (or anything) with positional args. -/
def call1 (f : Val) (args : List Val) : RM Val := om.call ctx f args []

/-- `tp_descr_get` on `attr` found on a type, for `obj` (`.null` for class access). -/
def descrBind (attr obj tp : Val) : RM Val := do
  match attr with
  | .ref a =>
    match ← getObj a with
    | .func _ => if obj == .null then pure attr else alloc (.method attr obj)
    | .staticMethod f => pure f
    | .classMethod f => alloc (.method f tp)
    | .property fget _ _ =>
      if obj == .null then pure attr
      else if fget == .null then raiseS "AttributeError" "property has no getter"
      else call1 om ctx fget [obj]
    | .inst _ =>
      match ← userLookup (← typeOf attr) "__get__" with
      | some g => call1 om ctx g [attr, (if obj == .null then .none else obj), tp]
      | none => pure attr
    | _ => pure attr
  | .methDescr t n =>
    if obj == .null then pure attr else alloc (.boundBuiltin t n obj)
  | _ => pure attr

/-- Is `attr` a data descriptor (`tp_descr_set != NULL`)? -/
def isDataDescr (attr : Val) : RM Bool := do
  match attr with
  | .ref a =>
    match ← getObj a with
    | .property .. => pure true
    | .inst _ =>
      let t ← typeOf attr
      if (← userLookup t "__set__").isSome then pure true
      else return (← userLookup t "__delete__").isSome
    | _ => pure false
  | _ => pure false

/-- Call `type(v).name(v, *args)` when a Python class defines it. -/
def callDunder (v : Val) (name : String) (args : List Val) : RM (Option Val) := do
  match ← userLookup (← typeOf v) name with
  | some f =>
    let b ← descrBind om ctx f v (← typeOf v)
    pure (some (← call1 om ctx b args))
  | none => pure none

/-- `_PyObject_LookupAttr` flavoured `getattr`: `AttributeError` means absent. -/
def optAttr (o : Val) (n : String) : RM (Option Val) :=
  tryExc (some <$> om.getAttr ctx o n) fun e => do
    if ← givenMatches e 8 (.cls "AttributeError") then pure none else throw (.exc e)

/-- `attribute_error`-style message. -/
def noAttr {α : Type} (o : Val) (n : String) : RM α := do
  raiseS "AttributeError" s!"'{← tpName o}' object has no attribute '{n}'"

/-- `PyObject_GenericGetAttr`. -/
def genericGetAttr (o : Val) (name : String) : RM Val := do
  let tp ← typeOf o
  let descr ← typeLookup tp name
  if let some d := descr then
    if ← isDataDescr d then return ← descrBind om ctx d o tp
  match o with
  | .ref a =>
    if let .inst i ← getObj a then
      -- `member_get` for a `__slots__` name
      if let .ref ca := i.cls then
        if let .cls c ← getObj ca then
          if let some idx := c.slots.findIdx? (· == name) then
            let v := i.slots.getD idx .null
            if v == .null then noAttr o name
            return v
      if i.dict != .null then
        if let some v ← dictGetStr i.dict name then return v
  | _ => pure ()
  match descr with
  | some d => descrBind om ctx d o tp
  | none => noAttr o name

/-- `type_getattro`. -/
def typeGetAttr (o : Val) (name : String) : RM Val := do
  match ← typeLookup o name with
  | some d => descrBind om ctx d .null o
  | none =>
    raiseS "AttributeError" s!"type object '{← typeNameOf o}' has no attribute '{name}'"

/-- Exception fields exposed as attributes. -/
def excAttr (o : Val) (name : String) : RM (Option Val) := do
  if !(← isExcInstance o) then return none
  let d ← excData o
  match name with
  | "args" => pure (some d.args)
  | "__cause__" => pure (some (if d.cause == .null then .none else d.cause))
  | "__context__" => pure (some (if d.context == .null then .none else d.context))
  | "__suppress_context__" => pure (some (.bool d.suppressContext))
  | "__traceback__" => pure (some .none)
  | "value" => if ← isSubtype (← typeOf o) (.cls "StopIteration") then pure (some d.value) else pure none
  | _ => pure none

/-- `gen_getyieldfrom`, `Objects/genobject.c:890-914`. -/
def genYfGet (g : GenObj) : Val :=
  if g.frameState == 2 then g.frame.stack.getD 1 .none else .none

/-- `slot_tp_getattr_hook` and the special members of builtin objects. -/
def getAttrImpl (o : Val) (name : String) : RM Val := do
  if name == "__class__" then return ← typeOf o
  if let .ref a := o then
    match ← getObj a with
    | .func f =>
      match name with
      | "__name__" => return .str f.name
      | "__qualname__" => return .str f.qualname
      | "__module__" => return .str "__main__"
      | "__defaults__" => return (if f.defaults == .null then .none else f.defaults)
      | _ => pure ()
    | .cls c =>
      match name with
      | "__name__" => return .str c.name
      | "__qualname__" => return .str c.qualname
      | "__mro__" => return ← mkTuple c.mro
      | "__bases__" => return ← mkTuple c.bases
      | "__dict__" => return .ref c.dict
      | _ => pure ()
    | .module _ d =>
      match ← dictGetStr (.ref d) name with
      | some v => return v
      | none => raiseS "AttributeError" s!"module has no attribute '{name}'"
    | .inst i =>
      if name == "__dict__" && i.dict != .null then return i.dict
      if let some v ← excAttr o name then return v
    | .gen g =>
      let pre := match g.kind with | .coro => "cr_" | _ => "gi_"
      if name == "__name__" then return .str g.name
      if name == "__qualname__" then return .str g.qualname
      if name == pre ++ "running" then return .bool (g.frameState == 4)
      if name == pre ++ "suspended" then return .bool (g.frameState == 1 || g.frameState == 2)
      if name == (match g.kind with | .coro => "cr_await" | _ => "gi_yieldfrom") then
        return (genYfGet g)
    | .method f s =>
      match name with
      | "__self__" => return s
      | "__func__" => return f
      | _ => return ← om.getAttr ctx f name
    | .property fget fset fdel =>
      match name with
      | "fget" => return (if fget == .null then .none else fget)
      | "fset" => return (if fset == .null then .none else fset)
      | "fdel" => return (if fdel == .null then .none else fdel)
      | "setter" => return ← alloc (.boundBuiltin "property" "setter" o)
      | "getter" => return ← alloc (.boundBuiltin "property" "getter" o)
      | "deleter" => return ← alloc (.boundBuiltin "property" "deleter" o)
      | _ => pure ()
    | .slice s t st =>
      match name with
      | "start" => return s
      | "stop" => return t
      | "step" => return st
      | _ => pure ()
    | .super tp obj objType =>
      if name != "__class__" then
        let (v, _) ← om.superLookup ctx tp obj name false
        return v
      let _ := objType
    | .range start stop step _ =>
      match name with
      | "start" => return .int start
      | "stop" => return .int stop
      | "step" => return .int step
      | _ => pure ()
    | _ => pure ()
  if let .cls n := o then
    match name with
    | "__name__" | "__qualname__" => return .str n
    | "__module__" => return .str "builtins"
    | "__mro__" => return ← mkTuple (← mroOf o)
    | _ => pure ()
  if ← isType o then
    return ← typeGetAttr om ctx o name
  match o with
  | .int i =>
    match name with
    | "real" | "numerator" => return .int i
    | "imag" => return .int 0
    | "denominator" => return .int 1
    | _ => pure ()
  | .bool b =>
    match name with
    | "real" | "numerator" => return .int (if b then 1 else 0)
    | "imag" => return .int 0
    | "denominator" => return .int 1
    | _ => pure ()
  | .float _ =>
    match name with
    | "real" => return o
    | _ => pure ()
  | .builtin n =>
    match name with
    | "__name__" | "__qualname__" => return .str n
    | "__module__" => return .str "builtins"
    | _ => pure ()
  | .methDescr _ n =>
    match name with
    | "__name__" => return .str n
    | _ => pure ()
  | _ => pure ()
  let tp ← typeOf o
  match ← userLookup tp "__getattribute__" with
  | some f =>
    let b ← descrBind om ctx f o tp
    tryExc (call1 om ctx b [.str name]) fun e => do
      if ← givenMatches e 8 (.cls "AttributeError") then
        match ← userLookup tp "__getattr__" with
        | some h =>
          let hb ← descrBind om ctx h o tp
          call1 om ctx hb [.str name]
        | none => throw (.exc e)
      else throw (.exc e)
  | none =>
    match ← userLookup tp "__getattr__" with
    | some h =>
      tryExc (genericGetAttr om ctx o name) fun e => do
        if ← givenMatches e 8 (.cls "AttributeError") then
          let hb ← descrBind om ctx h o tp
          call1 om ctx hb [.str name]
        else throw (.exc e)
    | none => genericGetAttr om ctx o name

/-- `_PyObject_GetMethodStackRef`, `Objects/object.c`. -/
def getMethodImpl (o : Val) (name : String) : RM (Val × Val) := do
  let tp ← typeOf o
  let isCls ← isType o
  let hookless := (← userLookup tp "__getattribute__").isNone
  if isCls || !hookless then
    return (← om.getAttr ctx o name, .null)
  match ← typeLookup tp name with
  | some d =>
    let methLike ← match d with
      | .methDescr .. => pure true
      | .ref a =>
        match ← getObj a with
        | .func _ => pure true
        | _ => pure false
      | _ => pure false
    if methLike then
      if let .ref a := o then
        if let .inst i ← getObj a then
          if i.dict != .null then
            if let some v ← dictGetStr i.dict name then return (v, .null)
      return (d, o)
    else return (← om.getAttr ctx o name, .null)
  | none => return (← om.getAttr ctx o name, .null)

/-- The instance dict, materialized on demand. -/
def instDict (a : Addr) (i : InstObj) : RM Val := do
  if i.dict != .null then pure i.dict
  else
    let d ← mkDict
    setObj a (.inst { i with dict := d })
    pure d

/-- `tp_setattro`, `v = .null` for deletion. -/
def setAttrImpl (o : Val) (name : String) (v : Val) : RM Unit := do
  let tp ← typeOf o
  let isDel := v == .null
  let hook := if isDel then "__delattr__" else "__setattr__"
  if let some f ← userLookup tp hook then
    let b ← descrBind om ctx f o tp
    let _ ← call1 om ctx b (if isDel then [.str name] else [.str name, v])
    return ()
  if let .ref a := o then
    if let .cls c ← getObj a then
      if isDel then
        if !(← dictPopStr (.ref c.dict) name) then
          raiseS "AttributeError" s!"type object '{c.name}' has no attribute '{name}'"
      else dictSetStr (.ref c.dict) name v
      let ver ← freshVersion
      setObj a (.cls { c with version := ver })
      return ()
  if let some d ← typeLookup tp name then
    if let .ref a := d then
      if let .property _ fset fdel ← getObj a then
        let f := if isDel then fdel else fset
        if f == .null then
          raiseS "AttributeError"
            s!"property '{name}' of '{← tpName o}' object has no {if isDel then "deleter" else "setter"}"
        let _ ← call1 om ctx f (if isDel then [o] else [o, v])
        return ()
      if ← isDataDescr d then
        let m := if isDel then "__delete__" else "__set__"
        let _ ← callDunder om ctx d m (if isDel then [o] else [o, v])
        return ()
  match o with
  | .ref a =>
    match ← getObj a with
    | .inst i =>
      -- `__slots__`
      let cls ← getObj (match i.cls with | .ref c => c | _ => 0)
      if let .cls c := cls then
        if let some idx := c.slots.findIdx? (· == name) then
          if isDel && i.slots.getD idx .null == .null then
            raiseVal (← newExc (.cls "AttributeError") [.str name])
          setObj a (.inst { i with slots := i.slots.setIfInBounds idx v })
          return ()
        if !c.hasDict then
          if isDel then noAttr o name
          raiseS "AttributeError"
            s!"'{c.name}' object has no attribute '{name}' and no __dict__ for setting new attributes"
      let d ← instDict a i
      if isDel then
        if !(← dictPopStr d name) then noAttr o name
      else dictSetStr d name v
      return ()
    | .func _ => return ()
    | _ => pure ()
  | _ => pure ()
  raiseS "AttributeError"
    s!"'{← tpName o}' object has no attribute '{name}' and no __dict__ for setting new attributes"

/-- `PyObject_RichCompare` result as a `bool`-testing helper. -/
def cmpBool (l r : Val) (op : Nat) : RM Bool := do
  om.isTrue ctx (← om.richCompare ctx l r op)

/-- Result of comparison from a three-way `Ordering`. -/
def ordResult (o : Ordering) (op : Nat) : Bool :=
  match op with
  | 0 => o == .lt
  | 1 => o != .gt
  | 2 => o == .eq
  | 3 => o != .eq
  | 4 => o == .gt
  | _ => o != .lt

/-- Lexicographic comparison, `list_richcompare` and `tuplerichcompare`. -/
def seqCompare (a b : List Val) (op : Nat) : RM Bool := do
  let rec go : List Val → List Val → RM (Option (Val × Val))
    | x :: xs, y :: ys => do
      if ← eqBool om ctx x y then go xs ys else pure (some (x, y))
    | _, _ => pure none
  if op == 2 && a.length != b.length then return false
  if op == 3 && a.length != b.length then return true
  match ← go a b with
  | some (x, y) =>
    if op == 2 then return false
    if op == 3 then return true
    cmpBool om ctx x y op
  | none => pure (ordResult (compare a.length b.length) op)

def opName : Nat → String
  | 0 => "<" | 1 => "<=" | 2 => "==" | 3 => "!=" | 4 => ">" | _ => ">="
def opSwap : Nat → Nat
  | 0 => 4 | 1 => 5 | 2 => 2 | 3 => 3 | 4 => 0 | _ => 1
def cmpDunder : Nat → String
  | 0 => "__lt__" | 1 => "__le__" | 2 => "__eq__" | 3 => "__ne__" | 4 => "__gt__" | _ => "__ge__"

/-- `tp_richcompare` of the builtin types. `none` is `NotImplemented`. -/
def builtinCompare (l r : Val) (op : Nat) : RM (Option Val) := do
  let some' (b : Bool) : RM (Option Val) := pure (some (.bool b))
  match l, r with
  | .str a, .str b => some' (ordResult (compare a b) op)
  | .bytes a, .bytes b =>
    some' (ordResult (cmpNats (a.map (·.toNat)) (b.map (·.toNat))) op)
  | .none, .none => if op == 2 then some' true else if op == 3 then some' false else pure none
  | .ref a, .ref b =>
    match ← getObj a, ← getObj b with
    | .list x, .list y | .tuple x, .tuple y =>
      some' (← seqCompare om ctx x.toList y.toList op)
    | .dict x, .dict y =>
      if op != 2 && op != 3 then return none
      let same ← if x.entries.size != y.entries.size then pure false else
        x.entries.toList.allM fun en => do
          match ← dictGet om ctx r en.key with
          | some v => eqBool om ctx en.value v
          | none => pure false
      some' (if op == 2 then same else !same)
    | .set _ x, .set _ y =>
      let sub (p q : Array (Int × Val)) (qv : Val) : RM Bool :=
        p.toList.allM fun kv => setContains om ctx qv kv.2
      match op with
      | 2 => some' (x.size == y.size && (← sub x y r))
      | 3 => some' !(x.size == y.size && (← sub x y r))
      | 1 => some' (x.size ≤ y.size && (← sub x y r))
      | 0 => some' (x.size < y.size && (← sub x y r))
      | 5 => some' (y.size ≤ x.size && (← sub y x l))
      | _ => some' (y.size < x.size && (← sub y x l))
    | .range a1 _ s1 n1, .range a2 _ s2 n2 =>
      if op != 2 && op != 3 then return none
      let same := n1 == n2 && (n1 == 0 || (a1 == a2 && (n1 == 1 || s1 == s2)))
      some' (if op == 2 then same else !same)
    | _, _ => pure none
  | _, _ =>
    match (intOf l), (intOf r) with
    | some a, some b => some' (ordResult (compare a b) op)
    | _, _ =>
      match l, r with
      | .float a, .float b =>
        let (x, y) := (toF a, toF b)
        some' (match op with
          | 0 => Binary64.F64.lt x y | 1 => Binary64.F64.le x y | 2 => Binary64.F64.eq x y
          | 3 => Binary64.F64.ne x y | 4 => Binary64.F64.gt x y | _ => Binary64.F64.ge x y)
      | .float a, _ =>
        match intOf r with
        | some i =>
          if Num.isNan a then some' (op == 3)
          else if Num.isInf a then
            some' (ordResult (if (Num.fields a).1 then .lt else .gt) op)
          else some' (ordResult (Num.cmpFloatInt a i) op)
        | none => pure none
      | _, .float b =>
        match intOf l with
        | some i =>
          if Num.isNan b then some' (op == 3)
          else if Num.isInf b then
            some' (ordResult (if (Num.fields b).1 then .gt else .lt) op)
          else some' (ordResult (Num.cmpFloatInt b i).swap op)
        | none => pure none
      | _, _ => pure none

/-- `do_richcompare`, `Objects/object.c`. -/
def richCompareImpl (l r : Val) (op : Nat) : RM Val := do
  let lt ← typeOf l
  let rt_ ← typeOf r
  let ltU ← userLookup lt (cmpDunder op)
  let rtU ← userLookup rt_ (cmpDunder (opSwap op))
  let attempt (v o : Val) (name : String) : RM (Option Val) := do
    match ← callDunder om ctx v name [o] with
    | some x => pure (if x == .notImpl then none else some x)
    | none => pure none
  let builtin : RM (Option Val) := do
    let (pl, pr) := (← payload l, ← payload r)
    if pl == l && pr == r then builtinCompare om ctx l r op
    else builtinCompare om ctx pl pr op
  -- reversed operand goes first when the right type is a proper subclass
  let checkedReverse := lt != rt_ && (← isSubtype rt_ lt) && rtU.isSome
  if checkedReverse then
    if let some x ← attempt r l (cmpDunder (opSwap op)) then return x
  if ltU.isSome then
    if let some x ← attempt l r (cmpDunder op) then return x
  else if let some x ← builtin then return x
  if !checkedReverse && rtU.isSome then
    if let some x ← attempt r l (cmpDunder (opSwap op)) then return x
  -- default `object.__ne__` inverts `__eq__`
  if op == 3 then
    if (← userLookup lt "__eq__").isSome then
      if let some x ← attempt l r "__eq__" then
        return .bool !(← om.isTrue ctx x)
    if (← userLookup rt_ "__eq__").isSome then
      if let some x ← attempt r l "__eq__" then
        return .bool !(← om.isTrue ctx x)
  match op with
  | 2 => return .bool (l == r)
  | 3 => return .bool (l != r)
  | _ =>
    typeError s!"'{opName op}' not supported between instances of '{← tpName l}' and '{← tpName r}'"

/-- `PyObject_IsTrue`. -/
def isTrueImpl (v : Val) : RM Bool := do
  match v with
  | .bool b => pure b
  | .none => pure false
  | .notImpl => typeError "NotImplemented should not be used in a boolean context"
  | .int i => pure (i != 0)
  | .float b => pure !((Num.toRat b).1 == 0 && Num.isFinite b)
  | .str s => pure (s != "")
  | .bytes b => pure !b.isEmpty
  | .ref a =>
    match ← getObj a with
    | .list i | .tuple i => pure (i.size != 0)
    | .dict d => pure (d.entries.size != 0)
    | .set _ i => pure (i.size != 0)
    | .range _ _ _ n => pure (n != 0)
    | .inst i =>
      match ← userLookup i.cls "__bool__" with
      | some _ =>
        match ← callDunder om ctx v "__bool__" [] with
        | some (.bool b) => pure b
        -- `slot_nb_bool`, `Objects/typeobject.c:10938`
        | some x => typeError s!"{← tpName v}.__bool__() must return a bool, not {← tpName x}"
        | none => pure true
      | none =>
        if (← userLookup i.cls "__len__").isSome then return (← om.length ctx v) != 0
        if i.base != .null then om.isTrue ctx i.base else pure true
    | _ => pure true
  | _ => pure true

/-- `_Py_HashDouble` semantics for what the model can distinguish. -/
def hashFloat (b : UInt64) : Int :=
  match Num.toIntExact? b with
  | some i => hashInt i
  | none => hashInt (Int.ofNat b.toNat)

/-- `PyObject_Hash`. -/
def hashImpl (v : Val) : RM Int := do
  let unhashable {α} : RM α := do typeError s!"unhashable type: '{← tpName v}'"
  match v with
  | .int i => pure (hashInt i)
  | .bool b => pure (if b then 1 else 0)
  | .float b => pure (hashFloat b)
  | .str s => pure (hashStr s)
  | .bytes b => pure (hashInt (b.foldl (fun h x => h * 31 + (x.toNat : Int)) 5))
  | .none => pure 0x123456
  | .ref a =>
    match ← getObj a with
    | .list _ | .dict _ => unhashable
    | .set false _ => unhashable
    | .slice .. => pure (a : Int)
    | .tuple items =>
      let hs ← items.toList.mapM (om.hash ctx)
      pure (hs.foldl (fun h x => (h * 1000003 + x) % 2305843009213693951) 0x345678)
    | .set true items =>
      pure (frozensetHash items)
    | .range start _ step len =>
      -- `range_hash`, rangeobject.c:594: `hash((len(r), None, None))` when empty,
      -- `hash((len(r), r.start, None))` for one element, else `(len, start, step)`.
      let hs := [hashInt len,
        if len == 0 then 0x123456 else hashInt start,
        if len ≤ 1 then 0x123456 else hashInt step]
      pure (hs.foldl (fun h x => (h * 1000003 + x) % 2305843009213693951) 0x345678)
    | .inst i =>
      match ← userLookup i.cls "__hash__" with
      | some .none => unhashable
      | some _ =>
        match ← callDunder om ctx v "__hash__" [] with
        | some (.int h) => pure (hashInt h)
        | some (.bool b) => pure (if b then 1 else 0)
        | _ => typeError "__hash__ method should return an integer"
      | none =>
        if (← userLookup i.cls "__eq__").isSome then unhashable
        else if i.base != .null then om.hash ctx i.base
        else pure (a : Int)
    | _ => pure (a : Int)
  | .cls n => pure (hashStr n)
  | .builtin n => pure (hashStr n)
  | _ => pure 1

/-- The `__index__` protocol for subscripts. -/
def asIndex (i : Val) : RM (Option Int) := do
  match i with
  | .int n => pure (some n)
  | .bool b => pure (some (if b then 1 else 0))
  | _ =>
    match ← userLookup (← typeOf i) "__index__" with
    | some _ =>
      match ← callDunder om ctx i "__index__" [] with
      | some (.int n) => pure (some n)
      | some (.bool b) => pure (some (if b then 1 else 0))
      -- `_PyNumber_Index`, `Objects/abstract.c:1434`
      | some x => typeError s!"{← tpName i}.__index__() must return an int, not {← tpName x}"
      | none => pure none
    | none =>
      match ← payload i with
      | .int n => pure (some n)
      | _ => pure none

/-- A subscript that must fit `Py_ssize_t`. -/
def indexSsize (n : Int) : RM Int :=
  if n > PyLean.ssizeMax || n < PyLean.ssizeMin then
    raiseS "IndexError" "cannot fit 'int' into an index-sized integer"
  else pure n

/-- `PyObject_GetItem`. -/
def getItemImpl (c k : Val) : RM Val := do
  let c ← if (← userLookup (← typeOf c) "__getitem__").isSome then pure c else payload c
  let badIdx (tp : String) : RM Val := do
    typeError s!"{tp} indices must be integers or slices, not {← tpName k}"
  match c with
  | .str s =>
    let cs := s.toList
    if let .ref a := k then
      if let .slice x y z ← getObj a then
        return .str (strSlice s (← sliceRange cs.length x y z))
    match ← asIndex om ctx k with
    | some n =>
      let n ← indexSsize n
      let i := if n < 0 then n + cs.length else n
      if i < 0 || i ≥ cs.length then raiseS "IndexError" "string index out of range"
      pure (.str (cs.getD i.toNat ' ').toString)
    | none => typeError s!"string indices must be integers, not '{← tpName k}'"
  | .bytes b =>
    if let .ref a := k then
      if let .slice x y z ← getObj a then
        let idx ← sliceRange b.length x y z
        return .bytes (idx.filterMap fun i => b[i]?)
    match ← asIndex om ctx k with
    | some n =>
      let n ← indexSsize n
      let i := if n < 0 then n + b.length else n
      if i < 0 || i ≥ b.length then raiseS "IndexError" "index out of range"
      pure (.int (b.getD i.toNat 0).toNat)
    | none => typeError s!"byte indices must be integers or slices, not {← tpName k}"
  | .ref a =>
    match ← getObj a with
    | .list items | .tuple items =>
      let isList := match ← getObj a with | .list _ => true | _ => false
      let name := if isList then "list" else "tuple"
      if let .ref b := k then
        if let .slice x y z ← getObj b then
          let idx ← sliceRange items.size x y z
          let vals := idx.map fun i => items.getD i .null
          return ← if isList then mkList vals else mkTuple vals
      match ← asIndex om ctx k with
      | some n =>
        let n ← indexSsize n
        let i := if n < 0 then n + items.size else n
        if i < 0 || i ≥ items.size then
          raiseS "IndexError" s!"{name} index out of range"
        pure (items.getD i.toNat .null)
      | none => badIdx name
    | .dict _ =>
      match ← dictGet om ctx c k with
      | some v => pure v
      | none => raiseVal (← newExc (.cls "KeyError") [k])
    | .range start _ step len =>
      if let .ref b := k then
        if let .slice x y z ← getObj b then
          let st ← sliceIndex z 1
          if st == 0 then valueError "slice step cannot be zero"
          let lo ← sliceIndex x (if st < 0 then PyLean.ssizeMax else 0)
          let hi ← sliceIndex y (if st < 0 then PyLean.ssizeMin else PyLean.ssizeMax)
          let (b0, b1, n) := adjustIndices len lo hi st
          return ← alloc (.range (start + b0 * step) (start + b1 * step) (step * st) n)
      match ← asIndex om ctx k with
      | some n =>
        let i := if n < 0 then n + len else n
        if i < 0 || i ≥ len then raiseS "IndexError" "range object index out of range"
        pure (.int (start + i * step))
      | none => typeError s!"range indices must be integers or slices, not {← tpName k}"
    | _ =>
      match ← callDunder om ctx c "__getitem__" [k] with
      | some v => pure v
      | none =>
        if ← isType c then
          typeError s!"type '{← typeNameOf c}' is not subscriptable"
        typeError s!"'{← tpName c}' object is not subscriptable"
  | _ =>
    if ← isType c then
      typeError s!"type '{← typeNameOf c}' is not subscriptable"
    typeError s!"'{← tpName c}' object is not subscriptable"

/-- `PyObject_SetItem`. -/
def setItemImpl (c k v : Val) : RM Unit := do
  match c with
  | .ref a =>
    match ← getObj a with
    | .list items =>
      if let .ref b := k then
        if let .slice x y z ← getObj b then
          let vals ← drain om ctx (← om.getIter ctx v) 1000000 []
          let idx ← sliceRange items.size x y z
          let step ← sliceIndex z 1
          if step == 1 then
            let lo := (← sliceRange items.size x y .none).head?.getD
              (let (s, _, _) := adjustIndices items.size (← sliceIndex x 0) (← sliceIndex y PyLean.ssizeMax) 1; s.toNat)
            let l := items.toList
            setObj a (.list (l.take lo ++ vals ++ l.drop (lo + idx.length)).toArray)
          else
            if vals.length != idx.length then
              valueError s!"attempt to assign sequence of size {vals.length} to extended slice of size {idx.length}"
            let new := (idx.zip vals).foldl (fun acc p => acc.setIfInBounds p.1 p.2) items
            setObj a (.list new)
          return ()
      match ← asIndex om ctx k with
      | some n =>
        let n ← indexSsize n
        let i := if n < 0 then n + items.size else n
        if i < 0 || i ≥ items.size then
          raiseS "IndexError" "list assignment index out of range"
        setObj a (.list (items.setIfInBounds i.toNat v))
      | none => typeError s!"list indices must be integers or slices, not {← tpName k}"
    | .dict _ =>
      dictSet om ctx c k v
    | _ =>
      match ← callDunder om ctx c "__setitem__" [k, v] with
      | some _ => pure ()
      | none => typeError s!"'{← tpName c}' object does not support item assignment"
  | _ => typeError s!"'{← tpName c}' object does not support item assignment"

/-- `PyObject_DelItem`. -/
def delItemImpl (c k : Val) : RM Unit := do
  match c with
  | .ref a =>
    match ← getObj a with
    | .list items =>
      if let .ref b := k then
        if let .slice x y z ← getObj b then
          let idx ← sliceRange items.size x y z
          let l := (items.toList.zipIdx.filter fun p => !idx.contains p.2).map (·.1)
          setObj a (.list l.toArray)
          return ()
      match ← asIndex om ctx k with
      | some n =>
        let n ← indexSsize n
        let i := if n < 0 then n + items.size else n
        if i < 0 || i ≥ items.size then
          raiseS "IndexError" "list assignment index out of range"
        setObj a (.list (items.eraseIdxIfInBounds i.toNat))
      | none => typeError s!"list indices must be integers or slices, not {← tpName k}"
    | .dict d =>
      let h ← hashFor om ctx "dict key" k
      match ← dictFind (eqBool om ctx k) d h with
      | some i => dictRemoveAt c d i
      | none => raiseVal (← newExc (.cls "KeyError") [k])
    | _ =>
      match ← callDunder om ctx c "__delitem__" [k] with
      | some _ => pure ()
      | none => typeError s!"'{← tpName c}' object doesn't support item deletion"
  | _ => typeError s!"'{← tpName c}' object doesn't support item deletion"

/-- `PyObject_GetIter`. -/
def getIterImpl (v : Val) : RM Val := do
  let notIter : RM Val := do typeError s!"'{← tpName v}' object is not iterable"
  match v with
  | .str s => alloc (.strIter s.toList)
  | .bytes b => do
    let t ← mkTuple (b.map fun x => .int x.toNat)
    match t with
    | .ref a => alloc (.tupleIter (some a) 0)
    | _ => fault "alloc"
  | .ref a =>
    match ← getObj a with
    | .list _ => alloc (.listIter (some a) 0)
    | .tuple _ => alloc (.tupleIter (some a) 0)
    | .dict d => alloc (.dictIter a 0 0 d.entries.size)
    | .dictView d k =>
      match ← getObj d with
      | .dict dd => alloc (.dictIter d k 0 dd.entries.size)
      | _ => fault "dict view"
    | .set _ items => alloc (.setIter items 0)
    | .range start _ step len => alloc (.rangeIter start step len)
    | .gen g =>
      if g.kind == .coro then notIter else pure v
    | .listIter .. | .tupleIter .. | .rangeIter .. | .strIter .. | .seqIter .. | .callIter ..
    | .dictIter .. | .setIter .. | .enumerate .. | .zip .. | .map .. | .filter .. | .reversed .. =>
      pure v
    | .inst i =>
      match ← userLookup i.cls "__iter__" with
      | some f =>
        if f == .none then notIter else
        let b ← descrBind om ctx f v i.cls
        let r ← call1 om ctx b []
        if !(← om.isIterator r) then
          -- `PyObject_GetIter`, `Objects/abstract.c:2828`
          typeError s!"{← tpName v}.__iter__() must return an iterator, not {← tpName r}"
        pure r
      | none =>
        if (← userLookup i.cls "__getitem__").isSome then alloc (.seqIter v 0)
        else if i.base != .null then om.getIter ctx i.base
        else notIter
    | _ => notIter
  | _ => notIter

/-- The object a generator is suspended on: `_PyFrame_StackPeek(frame, 2)` under
`frame_state == FRAME_SUSPENDED_YIELD_FROM`, `Objects/genobject.c:493-494`, :651-653 and
:779-781. `_PyGen_yf` is gone in 3.15. The top of a suspended `yield from` is
`index_or_null`, and the receiver is under it. -/
def genYf (g : GenObj) : Option Val :=
  if g.frameState == 2 then g.frame.stack[1]? else none

/-- What `gen_send_ex2` hands back. -/
inductive Send where
  | next (v : Val)
  | ret (v : Val)
  /-- `PYGEN_ERROR` with no exception set: an exhausted `next()`. -/
  | none

/-- `gen_raise_already_executing_error`, `Objects/genobject.c:241-252`. -/
def alreadyExecuting {α : Type} (k : GenKind) : RM α :=
  valueError (match k with
    | .coro => "coroutine already executing"
    | .asyncGen => "async generator already executing"
    | .gen => "generator already executing")

/-- `gen_send_ex2`, `Objects/genobject.c:254-325`: the generator is already marked
`FRAME_EXECUTING`. `exc` is the exception being thrown in, if any. `generator_return_kind`
(:289-302) reads the same as "the frame state is suspended" on one thread, which is what the
3.14 code tested and what the model tests. -/
def genSendEx2 (a : Addr) (arg : Option Val) (exc : Option Val) : RM Send := do
  let g ← getGen a
  let gf := { g.frame with stack := arg.getD .none :: g.frame.stack }
  pushExcState g
  if let some e := exc then
    -- `_PyErr_ChainStackItem`, `Python/errors.c`
    if g.excValue != .null && g.excValue != .none && g.excValue != e then
      setContext e g.excValue
  setObj a (.gen { g with frame := gf })
  let result ← ctx.evalFrame gf exc
  let g' ← getGen a
  if g'.frameState == 1 || g'.frameState == 2 then return .next result
  if result == .none && g'.kind != .asyncGen && arg.isNone then return .none
  return .ret result

/-- `gen_send_ex`, `Objects/genobject.c:329-370`: the state checks, then `gen_send_ex2`. -/
def genSendExChecked (a : Addr) (arg : Option Val) : RM Send := do
  let g ← getGen a
  if g.frameState == 0 && (arg.isSome && arg != some .none) then
    typeError (match g.kind with
      | .coro => "can't send non-None value to a just-started coroutine"
      | .asyncGen => "can't send non-None value to a just-started async generator"
      | .gen => "can't send non-None value to a just-started generator")
  if g.frameState == 4 then alreadyExecuting g.kind
  if g.frameState == 5 then
    if g.kind == .coro then
      runtimeError "cannot reuse already awaited coroutine"
    else if arg.isSome then return .ret .none
    return .none
  setObj a (.gen { g with frameState := 4 })
  genSendEx2 ctx a arg none

/-- `_PyGen_SetStopIterationValue`, `Objects/genobject.c:782-799`. -/
def stopIter {α : Type} (v : Val) : RM α := do
  throw (.exc (← newExc (.cls "StopIteration") (if v == .none then [] else [v])))

/-- `gen_set_stop_iteration`, `Objects/genobject.c:384-399`, on what came back. -/
def sendToVal (a : Addr) : Send → RM Val
  | .next v => pure v
  | .ret v => do
    let g ← getGen a
    if g.kind == .asyncGen then throw (.exc (← newExc (.cls "StopAsyncIteration") []))
    else stopIter v
  | .none =>
    -- NULL with no exception: only `gen_iternext` reaches this
    stopIter .none

/-- `gen_send`, `Objects/genobject.c:405-414`. -/
def genSend (a : Addr) (arg : Option Val) : RM Val := do
  sendToVal a (← genSendExChecked ctx a arg)

/-- `gen_throw_current_exception`, `Objects/genobject.c:603-612`. -/
def genThrowCurrent (a : Addr) (exc : Val) : RM Val := do
  sendToVal a (← genSendEx2 ctx a (some .none) (some exc))

/-- `gen_clear_frame`, `Objects/genobject.c:166-174`. -/
def genClearFrame (a : Addr) : RM Unit := do
  let g ← getGen a
  setObj a (.gen { g with excValue := .null, frame := { g.frame with fast := #[], stack := [] } })

/-- `gen_iternext`, `Objects/genobject.c:760-774`. -/
def genIterNext (a : Addr) : RM (Option Val) := do
  match ← genSendExChecked ctx a none with
  | .next v => pure (some v)
  | .ret v => if v != .none then stopIter v else pure none
  | .none => pure none

mutual

/-- `gen_close_iter`, `Objects/genobject.c:424-449`. -/
def genCloseIter (n : Nat) (yf : Val) : RM Unit := do
  match n with
  | 0 => throw .fuel
  | n + 1 =>
    match ← genKindOf yf with
    | some .gen | some .coro =>
      match yf with
      | .ref y => let _ ← genClose n y; pure ()
      | _ => pure ()
    | _ =>
      match ← optAttr om ctx yf "close" with
      | some m => let _ ← call1 om ctx m []; pure ()
      | none => pure ()

/-- `gen_close`, `Objects/genobject.c:463-541`. The state check comes first, the generator
stays `FRAME_EXECUTING` from there on, and a running frame is refused. -/
def genClose (n : Nat) (a : Addr) : RM Val := do
  match n with
  | 0 => throw .fuel
  | n + 1 =>
    let g ← getGen a
    if g.frameState == 0 then
      setObj a (.gen { g with frameState := 5 })
      genClearFrame a
      return .none
    if g.frameState == 5 then return .none
    if g.frameState == 4 then alreadyExecuting g.kind
    setObj a (.gen { g with frameState := 4 })
    -- an error of closing `yf` replaces the `GeneratorExit` below
    let err ← match genYf g with
      | some yf => tryExc (do genCloseIter n yf; pure (Option.none)) fun e => pure (some e)
      | none => pure none
    let g ← getGen a
    let code ← getCodeR P g.frame.code
    let ins := code.instrs[g.frame.instrPtr]?
    if let some i := ins then
      -- `is_resume`, :451-461, and `RESUME_OPARG_DEPTH1_MASK`, 8 on 3.15
      if i.op == .RESUME || i.op == .RESUME_CHECK || i.op == .RESUME_CHECK_JIT ||
          i.op == .INSTRUMENTED_RESUME then
        if i.arg &&& 8 != 0 then
          setObj a (.gen { g with frameState := 5 })
          genClearFrame a
          return .none
    let e ← match err with
      | some e => pure e
      | none => newExc (.cls "GeneratorExit") []
    -- lines 517-540: a return value is the result, a yield is an error, and of the
    -- exceptions only `GeneratorExit` is swallowed
    let r : RM (Except Val Send) := tryExc (Except.ok <$> genSendEx2 ctx a (some .none) (some e))
      fun x => do
        if ← givenMatches x 8 (.cls "GeneratorExit") then pure (.error .none)
        else throw (.exc x)
    match ← r with
    | .error v => return v
    | .ok (.ret v) => return v
    | .ok _ =>
      runtimeError (match g.kind with
        | .coro => "coroutine ignored GeneratorExit"
        | .asyncGen => "async generator ignored GeneratorExit"
        | .gen => "generator ignored GeneratorExit")

end

/-- `generator.close()`. -/
def genCloseV (a : Addr) : RM Val := genClose P om ctx 64 a

end

end PyLean.Bytecode.Proto
