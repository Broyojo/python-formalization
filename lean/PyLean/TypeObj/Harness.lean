import PyLean.TypeObj.Builtins

/-!
A small statement language for difftest scenarios: class statements, `def`s with log and
return bodies, and probes. It is not a model of the compiler or the eval loop (that is
`Bytecode`). It exists to drive the object model the way a Python program does:
`execClass` mirrors `builtin___build_class__` (`Python/bltinmodule.c:102`). The generator
in `difftest/typeobj_diff.py` renders the same trees as Python source.
-/

namespace PyLean.TypeObj

inductive BinOpE where
  | add | sub | mul | matmul | mod | floordiv | truediv | lshift | rshift | band | bor | bxor | pow
  deriving Repr, Inhabited, DecidableEq

inductive UnOpE where
  | neg | pos | invert | not
  deriving Repr, Inhabited, DecidableEq

inductive Expr where
  | lit (v : Val)
  | name (n : Name)
  | attr (e : Expr) (n : Name)
  | call (f : Expr) (args : List Expr) (kw : List (Name × Expr))
  | bin (op : BinOpE) (a b : Expr)
  | un (op : UnOpE) (a : Expr)
  | cmp (op : CmpOp) (a b : Expr)
  | isE (a b : Expr)
  | inE (a b : Expr)
  | notInE (a b : Expr)
  | tupleE (es : List Expr)
  | listE (es : List Expr)
  | dictE (es : List (Expr × Expr))
  | sub (a k : Expr)
  | super0
  deriving Repr, Inhabited

structure ParamSpec where
  pos : List Name := []
  posonly : Nat := 0
  kwonly : List Name := []
  varargs : Option Name := none
  varkw : Option Name := none
  defaults : List Expr := []
  kwdefaults : List (Name × Expr) := []
  deriving Repr, Inhabited

inductive Stmt where
  | expr (e : Expr)
  | assign (n : Name) (e : Expr)
  | setattr (o : Expr) (n : Name) (e : Expr)
  | delattr (o : Expr) (n : Name)
  | setitem (o k e : Expr)
  | delitem (o k : Expr)
  | aug (n : Name) (op : BinOpE) (e : Expr)
  | ret (e : Expr)
  | raiseS (e : Expr)
  | raiseFrom (e c : Expr)
  | log (s : String)
  | defS (n qual : Name) (p : ParamSpec) (code : Nat)
  | classS (n : Name) (bases : List Expr) (kw : List (Name × Expr)) (cell : Bool) (code : Nat)
  | tryS (body : List Stmt) (exc : Expr) (var : Name) (handler : List Stmt)
  | ifS (c : Expr) (t e : List Stmt)
  | probe (tag : String) (e : Expr)
  | probeS (tag : String) (body : List Stmt)
  deriving Repr, Inhabited

/-- What the scenario shares. -/
structure Env where
  codes : Array (List Stmt)
  builtins : NameDict
  globals : Addr

/-- An execution frame. -/
structure Frame where
  locals : NameDict := []
  /-- Class body namespace. -/
  ns : Option Val := none
  func : Option Val := none
  /-- The `__class__` cell of an enclosing class statement. -/
  cell : Option Val := none
  /-- The exception being handled, for `__context__`. -/
  handling : Option Val := none
  deriving Inhabited

/-- `repr`-independent canonical text for a value; the difftest compares these. -/
def canon (w : World) : Nat → Val → String
  | 0, _ => "<deep>"
  | fuel + 1, v =>
    match v with
    | .none => "None"
    | .notImpl => "NotImplemented"
    | .ellipsis => "Ellipsis"
    | .bool b => if b then "True" else "False"
    | .int i => toString i
    | .float _ => "<float>"
    | .str s => reprStr s
    | .tuple xs => "(" ++ ", ".intercalate (xs.map (canon w fuel)) ++ ")"
    | .obj a =>
      match asType w v with
      | some t => s!"<class {tpName w t}>"
      | none =>
        let tn := typeName w v
        match payloadOf w v with
        | some (.list xs) =>
          if typeOf w v == B.list then "[" ++ ", ".intercalate (xs.map (canon w fuel)) ++ "]"
          else s!"<{tn} [" ++ ", ".intercalate (xs.map (canon w fuel)) ++ "]>"
        | some (.dict es) =>
          let items := es.map fun (k, x) => canon w fuel k ++ ": " ++ canon w fuel x
          if typeOf w v == B.dict then "{" ++ ", ".intercalate items ++ "}"
          else s!"<{tn} " ++ "{" ++ ", ".intercalate items ++ "}>"
        | some (.boxed x) => s!"<{tn} {canon w fuel x}>"
        | some (.func f) => s!"<function {f.qualname}>"
        | some (.bound f s) => s!"<method {canon w fuel f} of {canon w fuel s}>"
        | some (.builtin _ _) => "<builtin>"
        | some (.exc e) =>
          s!"<{tn} " ++ "(" ++ ", ".intercalate (e.args.map (canon w fuel)) ++ ")>"
        | _ => let _ := a; s!"<{tn}>"

def binopE (rt : Rt) (op : BinOpE) (a b : Val) : M Val :=
  match op with
  | .add => pyNumberAdd rt a b
  | .sub => binaryOp rt a b .nb_subtract "-"
  | .mul => pyNumberMultiply rt a b
  | .matmul => binaryOp rt a b .nb_matrix_multiply "@"
  | .mod => binaryOp rt a b .nb_remainder "%"
  | .floordiv => binaryOp rt a b .nb_floor_divide "//"
  | .truediv => binaryOp rt a b .nb_true_divide "/"
  | .lshift => binaryOp rt a b .nb_lshift "<<"
  | .rshift => binaryOp rt a b .nb_rshift ">>"
  | .band => binaryOp rt a b .nb_and "&"
  | .bor => binaryOp rt a b .nb_or "|"
  | .bxor => binaryOp rt a b .nb_xor "^"
  | .pow => pyNumberPower rt a b .none

def ibinopE (rt : Rt) (op : BinOpE) (a b : Val) : M Val :=
  match op with
  | .add => pyNumberInPlaceAdd rt a b
  | .sub => binaryIop rt a b .nb_inplace_subtract .nb_subtract "-="
  | .mul => pyNumberInPlaceMultiply rt a b
  | .matmul => binaryIop rt a b .nb_inplace_matrix_multiply .nb_matrix_multiply "@="
  | .mod => binaryIop rt a b .nb_inplace_remainder .nb_remainder "%="
  | .floordiv => binaryIop rt a b .nb_inplace_floor_divide .nb_floor_divide "//="
  | .truediv => binaryIop rt a b .nb_inplace_true_divide .nb_true_divide "/="
  | .lshift => binaryIop rt a b .nb_inplace_lshift .nb_lshift "<<="
  | .rshift => binaryIop rt a b .nb_inplace_rshift .nb_rshift ">>="
  | .band => binaryIop rt a b .nb_inplace_and .nb_and "&="
  | .bor => binaryIop rt a b .nb_inplace_or .nb_or "|="
  | .bxor => binaryIop rt a b .nb_inplace_xor .nb_xor "^="
  | .pow => ternaryIop rt a b .none

/-- Globals dict store. -/
def storeGlobal (env : Env) (n : Name) (v : Val) : M Unit :=
  modObj env.globals fun o =>
    match o.body with
    | .dict es => { o with body := .dict (dictSetEntry es (.str n) v) }
    | _ => o

/-- `LOAD_NAME`/`LOAD_GLOBAL`. -/
def loadName (env : Env) (rt : Rt) (fr : Frame) (n : Name) : M Val := do
  match NameDict.get? fr.locals n with
  | some v => pure v
  | none =>
    let viaNs : Option (M (Option Val)) := fr.ns.map fun ns => do
      catchMatch B.KeyError (some <$> pyGetItem rt ns (.str n)) (pure none)
    let inNs ← match viaNs with
      | some act => act
      | none => pure none
    match inNs with
    | some v => pure v
    | none =>
      let w ← getW
      match dictLookup ((dictOf w (.obj env.globals)).getD []) (.str n) with
      | some v => pure v
      | none =>
        match NameDict.get? env.builtins n with
        | some v => pure v
        | none => raiseC B.NameError s!"name '{n}' is not defined"

/-- Store a name in the current scope. -/
def storeName (env : Env) (rt : Rt) (fr : Frame) (inFunc : Bool) (n : Name) (v : Val) : M Frame := do
  match fr.ns with
  | some ns =>
    pySetItem rt ns (.str n) (some v)
    pure fr
  | none =>
    if inFunc then pure { fr with locals := NameDict.set fr.locals n v }
    else
      storeGlobal env n v
      pure fr

/-- `super()` with no arguments: `super_init_without_args`,
`Objects/typeobject.c:12066`. The first local is the first parameter. -/
def superZero (rt : Rt) (fr : Frame) : M Val := do
  let w ← getW
  let some f := fr.func
    | runtimeErr "super(): no current frame"
  let fd := match payloadOf w f with
    | some (.func d) => d
    | _ => default
  if fd.argcount == 0 then runtimeErr "super(): no arguments"
  let first := NameDict.get? fr.locals (fd.varnames.getD 0 "")
  let some obj := first
    | runtimeErr "super(): arg[0] deleted"
  match fd.classCell with
  | none => runtimeErr "super(): __class__ cell not found"
  | some c =>
    match payloadOf w (.obj c) with
    | some (.cell (some ty)) =>
      match asType w ty with
      | some t =>
        let o := if obj.is .none then none else some obj
        let ot ← match o with
          | some x => some <$> supercheck rt t x
          | none => pure none
        alloc B.super (.super (some t) o ot)
      | none => runtimeErr s!"super(): __class__ is not a type ({typeName w ty})"
    | _ => runtimeErr "super(): empty __class__ cell"

/-- `Frame` results of a block: the frame, and a return value if `return` ran. -/
abbrev Flow := Frame × Option Val

/-- Text of an exception for probes: `type(e).__name__` and `str(e)`. -/
def errText (rt : Rt) (e : PyErr) : M String := do
  match e with
  | .fuel => pure "!MODEL-FUEL"
  | .gap site => pure s!"!MODEL-GAP@{site}"
  | .exc cls msg val =>
    let w ← getW
    match val with
    | some v =>
      let s ← tryM (rt.str v) (fun _ => pure "<str failed>")
      pure s!"!{tpName w (typeOf w v)}: {s}"
    | none => pure s!"!{tpName w cls}: {msg}"

mutual
  def evalExpr (env : Env) (rt : Rt) (fr : Frame) : Nat → Expr → M Val
    | 0, _ => raise .fuel
    | fuel + 1, e =>
      match e with
      | .lit v => pure v
      | .name n => loadName env rt fr n
      | .attr o n => do
        let v ← evalExpr env rt fr fuel o
        rt.getAttr v n
      | .call (.attr o n) args kw => do
        let v ← evalExpr env rt fr fuel o
        let (m, unbound) ← pyGetMethod rt v n
        let a ← evalList env rt fr fuel args
        let k ← evalKw env rt fr fuel kw
        if unbound then rt.call m (v :: a) k else rt.call m a k
      | .call f args kw => do
        let fv ← evalExpr env rt fr fuel f
        let a ← evalList env rt fr fuel args
        let k ← evalKw env rt fr fuel kw
        rt.call fv a k
      | .bin op a b => do
        let x ← evalExpr env rt fr fuel a
        let y ← evalExpr env rt fr fuel b
        binopE rt op x y
      | .un op a => do
        let x ← evalExpr env rt fr fuel a
        match op with
        | .neg => pyNumberNegative rt x
        | .pos => pyNumberPositive rt x
        | .invert => pyNumberInvert rt x
        | .not => .bool <$> (not <$> rt.isTrue x)
      | .cmp op a b => do
        let x ← evalExpr env rt fr fuel a
        let y ← evalExpr env rt fr fuel b
        rt.richCompare x y op
      | .isE a b => do
        let x ← evalExpr env rt fr fuel a
        let y ← evalExpr env rt fr fuel b
        pure (.bool (x.is y))
      | .inE a b => do
        let x ← evalExpr env rt fr fuel a
        let y ← evalExpr env rt fr fuel b
        .bool <$> pySequenceContains rt y x
      | .notInE a b => do
        let x ← evalExpr env rt fr fuel a
        let y ← evalExpr env rt fr fuel b
        .bool <$> (not <$> pySequenceContains rt y x)
      | .tupleE es => .tuple <$> evalList env rt fr fuel es
      | .listE es => do
        let xs ← evalList env rt fr fuel es
        alloc B.list (.list xs)
      | .dictE es => do
        let ks ← evalList env rt fr fuel (es.map (·.1))
        let vs ← evalList env rt fr fuel (es.map (·.2))
        alloc B.dict (.dict ((ks.zip vs).foldl (fun d (k, v) => dictSetEntry d k v) []))
      | .sub a k => do
        let x ← evalExpr env rt fr fuel a
        let y ← evalExpr env rt fr fuel k
        pyGetItem rt x y
      | .super0 => superZero rt fr

  def evalList (env : Env) (rt : Rt) (fr : Frame) : Nat → List Expr → M (List Val)
    | 0, _ => raise .fuel
    | _, [] => pure []
    | fuel + 1, e :: es => do
      let v ← evalExpr env rt fr fuel e
      let vs ← evalList env rt fr fuel es
      pure (v :: vs)

  def evalKw (env : Env) (rt : Rt) (fr : Frame) : Nat → List (Name × Expr) → M Kw
    | 0, _ => raise .fuel
    | _, [] => pure []
    | fuel + 1, (k, e) :: es => do
      let v ← evalExpr env rt fr fuel e
      let vs ← evalKw env rt fr fuel es
      pure ((k, v) :: vs)
end

/-- Build a function object. -/
def makeFunction (env : Env) (rt : Rt) (fr : Frame) (fuel : Nat) (n qual : Name) (p : ParamSpec)
    (code : Nat) : M Val := do
  let defaults ← evalList env rt fr fuel p.defaults
  let kwdefaults ← evalKw env rt fr fuel p.kwdefaults
  let w ← getW
  let cellAddr : Option Addr := match fr.cell with
    | some (.obj c) => some c
    | _ => none
  alloc B.function (.func {
    name := n, qualname := qual, module := (w.curModule).getD .none
    argcount := p.pos.length, posonly := p.posonly, kwonly := p.kwonly.length
    varnames := p.pos ++ p.kwonly ++ p.varargs.toList ++ p.varkw.toList
    hasVarargs := p.varargs.isSome, hasVarkw := p.varkw.isSome
    defaults := defaults, kwdefaults := kwdefaults, code := code, classCell := cellAddr
    defaultsSet := !defaults.isEmpty, kwdefaultsSet := !kwdefaults.isEmpty })

/-- Instantiate what `raise X` names: `_PyErr_SetObject` with a class calls it. -/
def raiseValue (rt : Rt) (v : Val) : M Val := do
  let w ← getW
  match asType w v with
  | some t =>
    if isSubtype w t B.BaseException then rt.call v [] []
    else typeErr "exceptions must derive from BaseException"
  | none =>
    if isSubtype w (typeOf w v) B.BaseException then pure v
    else typeErr "exceptions must derive from BaseException"

/-- Set an exception field. -/
def modExc (v : Val) (f : ExcData → ExcData) : M Unit :=
  match v with
  | .obj a => modObj a fun o =>
    match o.body with
    | .exc d => { o with body := .exc (f d) }
    | _ => o
  | _ => pure ()

/-- `PyTraceBack_Here` as far as a scenario can see: an exception caught in a frame has a
traceback object. -/
def attachTraceback (x : Val) : M Unit := do
  let w ← getW
  match (excDataOf w x).traceback with
  | .none =>
    let tb ← alloc B.traceback .plain
    modExc x fun d => { d with traceback := tb }
  | _ => pure ()

mutual
  def execStmt (env : Env) (rt : Rt) (inFunc : Bool) : Nat → Frame → Stmt → M Flow
    | 0, _, _ => raise .fuel
    | fuel + 1, fr, s => do
    match s with
    | .expr e =>
      let _ ← evalExpr env rt fr fuel e
      pure (fr, none)
    | .assign n e =>
      let v ← evalExpr env rt fr fuel e
      let fr ← storeName env rt fr inFunc n v
      pure (fr, none)
    | .setattr o n e =>
      let v ← evalExpr env rt fr fuel e
      let ov ← evalExpr env rt fr fuel o
      rt.setAttr ov n (some v)
      pure (fr, none)
    | .delattr o n =>
      let ov ← evalExpr env rt fr fuel o
      rt.setAttr ov n none
      pure (fr, none)
    | .setitem o k e =>
      let v ← evalExpr env rt fr fuel e
      let ov ← evalExpr env rt fr fuel o
      let kv ← evalExpr env rt fr fuel k
      pySetItem rt ov kv (some v)
      pure (fr, none)
    | .delitem o k =>
      let ov ← evalExpr env rt fr fuel o
      let kv ← evalExpr env rt fr fuel k
      pySetItem rt ov kv none
      pure (fr, none)
    | .aug n op e =>
      let a ← loadName env rt fr n
      let b ← evalExpr env rt fr fuel e
      let r ← ibinopE rt op a b
      let fr ← storeName env rt fr inFunc n r
      pure (fr, none)
    | .ret e =>
      let v ← evalExpr env rt fr fuel e
      pure (fr, some v)
    | .raiseS e =>
      let v ← evalExpr env rt fr fuel e
      let x ← raiseValue rt v
      if let some h := fr.handling then
        unless h.is x do modExc x fun d => { d with context := some h }
      raise (.exc (typeOf (← getW) x) "" (some x))
    | .raiseFrom e c =>
      let v ← evalExpr env rt fr fuel e
      let x ← raiseValue rt v
      let cv ← evalExpr env rt fr fuel c
      match cv with
      | .none => modExc x fun d => { d with cause := none, suppressContext := true }
      | _ =>
        let cx ← raiseValue rt cv
        modExc x fun d => { d with cause := some cx, suppressContext := true }
      if let some h := fr.handling then
        unless h.is x do modExc x fun d => { d with context := some h }
      raise (.exc (typeOf (← getW) x) "" (some x))
    | .log t =>
      logEvent t
      pure (fr, none)
    | .defS n qual p code =>
      let f ← makeFunction env rt fr fuel n qual p code
      let fr ← storeName env rt fr inFunc n f
      pure (fr, none)
    | .classS n bases kw cell code =>
      let cv ← execClass env rt fr fuel n bases kw cell code
      let fr ← storeName env rt fr inFunc n cv
      pure (fr, none)
    | .tryS body exc var handler =>
      let saved := fr
      tryM (execBlock env rt inFunc fuel fr body) fun e => do
        match e with
        | .fuel => raise .fuel
        | _ =>
          let cls ← evalExpr env rt saved fuel exc
          let w ← getW
          match asType w cls with
          | some c =>
            if excMatches w e c then
              let x ← excObject e
              attachTraceback x
              let fr' := { saved with locals := NameDict.set saved.locals var x, handling := some x }
              let (fr2, r) ← execBlock env rt inFunc fuel fr' handler
              pure ({ fr2 with handling := saved.handling }, r)
            else raise e
          | none => typeErr "catching classes that do not inherit from BaseException is not allowed"
    | .ifS c t e =>
      let v ← evalExpr env rt fr fuel c
      if ← rt.isTrue v then execBlock env rt inFunc fuel fr t
      else execBlock env rt inFunc fuel fr e
    | .probe tag e =>
      let out ← tryM (do
          let v ← evalExpr env rt fr fuel e
          let w ← getW
          pure (canon w 12 v))
        (errText rt)
      logEvent s!"{tag}={out}"
      pure (fr, none)
    | .probeS tag body =>
      let (fr', out) ← tryM (do
          let (f, _) ← execBlock env rt inFunc fuel fr body
          pure (f, "ok"))
        (fun e => do
          let t ← errText rt e
          pure (fr, t))
      logEvent s!"{tag}={out}"
      pure (fr', none)

  def execBlock (env : Env) (rt : Rt) (inFunc : Bool) : Nat → Frame → List Stmt → M Flow
    | 0, _, _ => raise .fuel
    | _, fr, [] => pure (fr, none)
    | fuel + 1, fr, s :: rest => do
      let (fr', r) ← execStmt env rt inFunc fuel fr s
      match r with
      | some _ => pure (fr', r)
      | none => execBlock env rt inFunc fuel fr' rest

  /-- `builtin___build_class__`, `Python/bltinmodule.c:102`; `update_bases` at `:30`. -/
  def execClass (env : Env) (rt : Rt) (fr : Frame) : Nat → Name → List Expr →
      List (Name × Expr) → Bool → Nat → M Val
    | 0, _, _, _, _, _ => raise .fuel
    | fuel + 1, n, bases, kw, cell, code => do
    let orig ← evalList env rt fr fuel bases
    let kwv ← evalKw env rt fr fuel kw
    -- update_bases
    let mut newBases : List Val := []
    let mut changed := false
    for b in orig do
      let w ← getW
      if typeCheck w b then
        newBases := newBases ++ [b]
      else
        match ← rt.getOptionalAttr b "__mro_entries__" with
        | none => newBases := newBases ++ [b]
        | some meth =>
          let nb ← rt.call meth [.tuple orig] []
          let w ← getW
          match tupleOf w nb with
          | some xs =>
            changed := true
            newBases := newBases ++ xs
          | none => typeErr "__mro_entries__ must return a tuple"
    let basesV := newBases
    let w ← getW
    let metaKw := NameDict.get? kwv "metaclass"
    let mkw := NameDict.erase kwv "metaclass"
    let meta0 : Val := match metaKw with
      | some m => m
      | none =>
        match basesV with
        | [] => .obj B.type
        | b :: _ => .obj (typeOf w b)
    let isclass := match metaKw with
      | some m => typeCheck w m
      | none => true
    let metaV ←
      if isclass then
        match meta0 with
        | .obj m => .obj <$> calculateMetaclass m basesV
        | _ => gap%
      else pure meta0
    let prep ← rt.getOptionalAttr metaV "__prepare__"
    let ns ← match prep with
      | none => alloc B.dict (.dict [])
      | some p => rt.call p [.str n, .tuple basesV] mkw
    let w ← getW
    unless pyMappingCheck w ns do
      let mn := if isclass then trunc 200 (match metaV with
        | .obj m => tpName w m
        | _ => "") else "<metaclass>"
      typeErr s!"{mn}.__prepare__() must return a mapping, not {trunc 200 (typeName w ns)}"
    let cellV ← if cell then alloc B.cell (.cell none) else pure Val.none
    let frameC : Frame := { ns := some ns, cell := if cell then some cellV else none }
    pySetItem rt ns (.str "__module__") (some (w.curModule.getD .none))
    pySetItem rt ns (.str "__qualname__") (some (.str n))
    pySetItem rt ns (.str "__firstlineno__") (some (.int 1))
    let body := env.codes.getD code []
    let (fr2, _) ← execBlock env rt false fuel frameC body
    let _ := fr2
    pySetItem rt ns (.str "__static_attributes__") (some (.tuple []))
    if cell then pySetItem rt ns (.str "__classcell__") (some cellV)
    if changed then pySetItem rt ns (.str "__orig_bases__") (some (.tuple orig))
    let cls ← rt.call metaV [.str n, .tuple basesV, ns] mkw
    let w ← getW
    if cell && typeCheck w cls then
      match payloadOf w cellV with
      | some (.cell (some cc)) =>
        unless cc.is cls do
          let a ← rt.repr cc
          let c ← rt.repr cls
          typeErr s!"__class__ set to {a} defining {reprStr n} as {c}"
      | _ =>
        let c ← rt.repr cls
        runtimeErr s!"__class__ not set defining {reprStr n} as {c}. Was __classcell__ propagated to type.__new__?"
    pure cls
end

/-- `Rt.exec` for scenario functions. -/
def harnessExec (env : Env) (rt : Rt) (code : Nat) (func : Val) (locals : NameDict) : M Val := do
  let body := env.codes.getD code []
  let fr : Frame := { locals := locals, func := some func }
  let (_, r) ← execBlock env rt true 100000 fr body
  pure (r.getD .none)

/-- Re-entrancy bound of the scenario interpreter. -/
def harnessFuel : Nat := 6000

/-- The scenario helpers of `difftest/typeobj_exc_diff.py`: `bytes` constructors and the
`_testcapi` entry points into `Objects/exceptions.c`. Each is an `excMethod` by name. -/
def harnessExcFunctions : List (Name × String) :=
  [("_bytes", "harness.bytes"), ("_bytearray", "harness.bytearray"),
   ("_prep_reraise_star", "capi.prep_reraise_star")] ++
  (["encode", "decode", "translate"].flatMap fun k =>
    ["get_start", "set_start", "get_end", "set_end"].map fun op =>
      (s!"_unicode_{k}_{op}", s!"capi.unicode_{k}_{op}"))

/-- Bind `harnessExcFunctions` in the globals. -/
def installExcFunctions (env : Env) : List (Name × String) → M Unit
  | [] => pure ()
  | (n, m) :: rest => do
    let f ← alloc B.builtinFn (.builtin (.excMethod m) none)
    storeGlobal env n f
    installExcFunctions env rest

/-- Run a scenario: the observable trace in order. -/
def runScenario (codes : Array (List Stmt)) (main : List Stmt) : List String :=
  let (w0, bi) := initialState
  let setup : M Unit := do
    let g ← alloc B.dict (.dict [])
    match g with
    | .obj ga =>
      let env : Env := { codes := codes, builtins := bi, globals := ga }
      let rt := rtOf (harnessExec env) harnessFuel
      modW fun w => { w with curModule := some (.str "__main__") }
      installExcFunctions env harnessExcFunctions
      let _ ← execBlock env rt false 100000 {} main
    | _ => pure ()
  match setup w0 with
  | .ok _ w => w.trace.reverse
  | .err e w =>
    let tail := match e with
      | .fuel => "MODEL-FUEL"
      | .gap site => s!"MODEL-GAP@{site}"
      | .exc c m _ => s!"UNCAUGHT {tpName w c}: {m}"
    (tail :: w.trace).reverse

end PyLean.TypeObj
