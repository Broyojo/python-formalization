import PyLean.Decimal.Division
import PyLean.Decimal.Parse

/-!
`_pydecimal`'s `Context` class and the module-level context functions.

`Ctx` (`Arith.lean`) is what an operation reads; `PyContext` here is the object
itself, with `flags` and `traps` as the dicts they are (`SigDict`, insertion order
kept, because `__repr__` and `__reduce__` read them in that order).

`Arg` is an operand as Python sees it: a Decimal, an int, or anything else.
Identity is not modelled: `_shallow_copy` shares its dicts with the original where
`copy` does not, which a value model cannot tell apart.
-/

namespace PyLean.Decimal

open PyLean

/-! ## Operands -/

/-- An operand of a `Context` method or a binary operator. -/
inductive Arg where
  | dec (d : Dec)
  | int (n : Int)
  | other
  deriving Repr, Inhabited

/-- `"Unable to convert %s to Decimal" % other`, formatted text the model does not render. -/
def unableMsg : String := "~Unable to convert to Decimal"

/-- `_convert_other(other, raiseit)`, _pydecimal.py:6096-6113, without `allow_float`,
which nothing in the module passes. `none` is `NotImplemented`. -/
def convertOther (raiseit : Bool) : Arg → Py (Option Dec)
  | .dec d => .ok (some d)
  | .int n => do return some (← pyFromInt n)
  | .other => if raiseit then .error (.typeError unableMsg) else .ok none

/-- `_convert_other(other, raiseit=True)`, which never returns `NotImplemented`. -/
def convertRaise (x : Arg) : Py Dec := do
  match ← convertOther true x with
  | some d => return d
  | none => throw (.typeError unableMsg)

/-- The operator prologue `other = _convert_other(other); if other is NotImplemented:
return other`. -/
def opArg {α : Type} (f : Ctx → Dec → Dec → DM α) (c : Ctx) (a : Dec) (b : Arg) : DM (Option α) := do
  match ← liftPy (convertOther false b) with
  | some o => return some (← f c a o)
  | none => return none

/-- A reflected operator: `__rsub__`, `__rtruediv__`, `__rdivmod__`, `__rmod__`,
`__rfloordiv__`, _pydecimal.py:1304-1310, :1466-1471, :1509-1514, :1543-1548,
:1655-1660: `other.__op__(self, context=context)` after the same prologue. -/
def ropArg {α : Type} (f : Ctx → Dec → Dec → DM α) (c : Ctx) (a : Dec) (b : Arg) : DM (Option α) := do
  match ← liftPy (convertOther false b) with
  | some o => return some (← f c o a)
  | none => return none

def rsub := ropArg sub
def rtruediv := ropArg truediv
def rdivmod := ropArg divmodD
def rmod := ropArg modD
def rfloordiv := ropArg floordivD

/-! ## `Context` methods: three shapes -/

/-- `a = _convert_other(a, raiseit=True); r = a.__op__(b, context=self); if r is
NotImplemented: raise TypeError(...); else: return r`: `Context.add`, `subtract`,
`multiply`, `divide`, `divide_int`, `divmod`, `remainder`. -/
def ctxOp {α : Type} (f : Ctx → Dec → Dec → DM α) (c : Ctx) (a b : Arg) : DM α := do
  let x ← liftPy (convertRaise a)
  match ← opArg f c x b with
  | some r => return r
  | none => throw (.typeError unableMsg)

/-- `a = _convert_other(a, raiseit=True); return a.m(b, context=self)`, where
`a.m` starts with `other = _convert_other(other, raiseit=True)`. -/
def ctxBin {α : Type} (f : Ctx → Dec → Dec → DM α) (c : Ctx) (a b : Arg) : DM α := do
  let x ← liftPy (convertRaise a)
  let y ← liftPy (convertRaise b)
  f c x y

/-- `a = _convert_other(a, raiseit=True); return a.m(context=self)`. -/
def ctxUn {α : Type} (f : Ctx → Dec → DM α) (c : Ctx) (a : Arg) : DM α := do
  let x ← liftPy (convertRaise a)
  f c x

/-- `Context.fma`, _pydecimal.py:4546-4567; `Decimal.fma` converts `other` and
`third` first, :1975-1996. -/
def contextFma (c : Ctx) (a b t : Arg) : DM Dec := do
  let x ← liftPy (convertRaise a)
  let y ← liftPy (convertRaise b)
  let z ← liftPy (convertRaise t)
  fma c x y z

def contextAdd := ctxOp add
def contextSubtract := ctxOp sub
def contextMultiply := ctxOp mul
def contextDivide := ctxOp truediv
def contextDivideInt := ctxOp floordivD
def contextDivmod := ctxOp divmodD
def contextRemainder := ctxOp modD

def contextCompare := ctxBin compareD
def contextCompareSignal := ctxBin compareSignal
def contextMax := ctxBin maxD
def contextMaxMag := ctxBin maxMag
def contextMin := ctxBin minD
def contextMinMag := ctxBin minMag
def contextLogicalAnd := ctxBin logicalAnd
def contextLogicalOr := ctxBin logicalOr
def contextLogicalXor := ctxBin logicalXor
def contextNextToward := ctxBin nextToward
def contextQuantize := ctxBin (fun c a b => quantize c a b)
def contextRemainderNear := ctxBin remainderNear
def contextRotate := ctxBin rotate
def contextScaleb := ctxBin scaleb
def contextShift := ctxBin shift
def contextCompareTotal := ctxBin (fun _ a b => (pure (decOfInt (compareTotal a b)) : DM Dec))
def contextCompareTotalMag := ctxBin (fun _ a b => (pure (decOfInt (compareTotalMag a b)) : DM Dec))
def contextCopySign := ctxBin (fun _ a b => (pure (copySign a b) : DM Dec))
def contextSameQuantum := ctxBin (fun _ a b => (pure (sameQuantum a b) : DM Bool))

def contextAbs := ctxUn (fun c a => dunderAbs c a)
def contextLogb := ctxUn logb
def contextLogicalInvert := ctxUn logicalInvert
def contextMinus := ctxUn dunderNeg
def contextPlus := ctxUn dunderPos
def contextNextMinus := ctxUn nextMinus
def contextNextPlus := ctxUn nextPlus
def contextNormalize := ctxUn normalize
def contextToIntegralExact := ctxUn (fun c a => toIntegralExact c a)
def contextToIntegralValue := ctxUn (fun c a => toIntegralValue c a)
def contextNumberClass := ctxUn (fun c a => (pure (numberClass c a) : DM String))
def contextIsNormal := ctxUn (fun c a => (pure (isNormal c a) : DM Bool))
def contextIsSubnormal := ctxUn (fun c a => (pure (isSubnormal c a) : DM Bool))
def contextToEngString := ctxUn (fun c a => (pure (toEng a c.capitals) : DM (List Char)))
def contextToSciString := ctxUn (fun c a => liftPy (pyStr a c.capitals))
def contextCopyAbs := ctxUn (fun _ a => (pure (copyAbs a) : DM Dec))
def contextCopyNegate := ctxUn (fun _ a => (pure (copyNegate a) : DM Dec))
def contextCopyDecimal := ctxUn (fun _ a => (pure a : DM Dec))
def contextIsFinite := ctxUn (fun _ a => (pure (isFinite a) : DM Bool))
def contextIsInfinite := ctxUn (fun _ a => (pure (isInfinite a) : DM Bool))
def contextIsNan := ctxUn (fun _ a => (pure (isNanP a) : DM Bool))
def contextIsQnan := ctxUn (fun _ a => (pure (isQnan a) : DM Bool))
def contextIsSigned := ctxUn (fun _ a => (pure (isSigned a) : DM Bool))
def contextIsSnan := ctxUn (fun _ a => (pure (isSnan a) : DM Bool))
def contextIsZero := ctxUn (fun _ a => (pure (isZero a) : DM Bool))

/-- `Context.radix`, _pydecimal.py:5362-5368. -/
def contextRadix : Dec := radixD

/-- `Context.canonical`, _pydecimal.py:4255-4266: unlike the other methods this one
takes only a Decimal. -/
def contextCanonical : Arg → Py Dec
  | .dec d => .ok (canonicalD d)
  | _ => .error (.typeError "canonical requires a Decimal as an argument.")

/-- `Context.is_canonical`, _pydecimal.py:4569-4580. -/
def contextIsCanonical : Arg → Py Bool
  | .dec d => .ok (isCanonical d)
  | _ => .error (.typeError "is_canonical requires a Decimal as an argument.")

/-- `Context._apply`, _pydecimal.py:4252-4253. -/
def contextApply (c : Ctx) (a : Dec) : DM (List Char) := do
  let r ← fix c a
  liftPy (pyStr r c.capitals)

/-! ## The `Context` object -/

/-- `_signals`, _pydecimal.py:332-333. -/
def pySignals : List Signal :=
  [.clamped, .divisionByZero, .inexact, .overflow, .rounded,
   .underflow, .invalidOperation, .subnormal, .floatOperation]

/-- A key of a dict passed as `flags` or `traps`. -/
inductive SigKey where
  | sig (s : Signal)
  | other
  deriving Repr, DecidableEq, Inhabited

/-- A valid signal dict, in insertion order. -/
abbrev SigDict := List (Signal × Bool)

/-- A value assigned to a context attribute or passed to `Context()`. -/
inductive CtxArg where
  | none
  | int (n : Int)
  | str (s : String)
  | list (l : List SigKey)
  | dict (d : List (SigKey × Bool))
  /-- A tuple of `n` elements, which `"%s ..." % d` treats as the format arguments. -/
  | tuple (n : Nat)
  | obj
  deriving Repr, Inhabited

structure PyContext where
  prec : Int
  rounding : Rounding
  emin : Int
  emax : Int
  capitals : Int
  clamp : Int
  flags : SigDict
  traps : SigDict
  ignored : List Signal
  deriving Repr, DecidableEq, Inhabited

def Rounding.name : Rounding → String
  | .up => "ROUND_UP" | .down => "ROUND_DOWN" | .ceiling => "ROUND_CEILING"
  | .floor => "ROUND_FLOOR" | .halfUp => "ROUND_HALF_UP" | .halfDown => "ROUND_HALF_DOWN"
  | .halfEven => "ROUND_HALF_EVEN" | .r05up => "ROUND_05UP"

/-- `_rounding_modes`, _pydecimal.py:342-343. -/
def roundingModes : List Rounding :=
  [.down, .halfUp, .halfEven, .ceiling, .floor, .up, .halfDown, .r05up]

def roundingOfName (s : String) : Option Rounding := roundingModes.find? (fun r => r.name == s)

/-- `Context._set_integer_check`, _pydecimal.py:4005-4017: `none` is `'-inf'` / `'inf'`. -/
def setIntegerCheck (name : String) (v : CtxArg) (vmin vmax : Option Int) : Py Int :=
  match v with
  | .int value =>
    match vmin, vmax with
    | none, some hi =>
      if value > hi then .error (.valueError s!"{name} must be in [-inf, {hi}]. got: {value}")
      else .ok value
    | some lo, none =>
      if value < lo then .error (.valueError s!"{name} must be in [{lo}, inf]. got: {value}")
      else .ok value
    | some lo, some hi =>
      if value < lo ∨ value > hi then .error (.valueError s!"{name} must be in [{lo}, {hi}]. got {value}")
      else .ok value
    | none, none => .ok value
  | _ => .error (.typeError s!"{name} must be an integer")

def hasKey (d : List (SigKey × Bool)) (k : SigKey) : Bool := d.any (fun p => p.1 == k)

/-- Drop the key wrapper from a dict all of whose keys are signals. -/
def sigEntries (d : List (SigKey × Bool)) : SigDict :=
  d.filterMap (fun p => match p.1 with
    | .sig s => some (s, p.2)
    | .other => none)

/-- `"%s must be a signal dict" % d` for a non-dict `d`, _pydecimal.py:4021: a tuple is
taken as the argument tuple of `%`, so an empty one and one of two or more elements fail in
the formatting itself (Objects/unicodeobject.c, `PyUnicode_Format`). -/
def notSignalDictMsg : CtxArg → String
  | .tuple 0 => "not enough arguments for format string (got 0)"
  | .tuple (n + 2) => s!"not all arguments converted during string formatting (required 1, got {n + 2})"
  | _ => "~must be a signal dict"

/-- `Context._set_signal_dict`, _pydecimal.py:4019-4028. -/
def setSignalDict (v : CtxArg) : Py SigDict :=
  match v with
  | .dict d =>
    if hasKey d .other then .error (.keyError "~is not a valid signal dict")
    else if !pySignals.all (fun s => hasKey d (.sig s)) then .error (.keyError "~is not a valid signal dict")
    else .ok (sigEntries d)
  | v => .error (.typeError (notSignalDictMsg v))

/-- The signals of a list assigned to `_ignored_flags`. `_raise_error` and `_regard_flags`
only test signals for membership and remove them (_pydecimal.py:4113, :4141), so other
elements change nothing they do. Any other object is stored as is in Python and is out of
scope here: `_ignored_flags` is private, and the module only ever assigns a list. -/
def ignoredOf : CtxArg → List Signal
  | .list l => l.filterMap (fun k => match k with
    | .sig s => some s
    | .other => none)
  | _ => []

/-- `Context.__setattr__`, _pydecimal.py:4030-4053. -/
def pySetattr (c : PyContext) (name : String) (v : CtxArg) : Py PyContext := do
  if name == "prec" then return { c with prec := ← setIntegerCheck name v (some 1) none }
  else if name == "Emin" then return { c with emin := ← setIntegerCheck name v none (some 0) }
  else if name == "Emax" then return { c with emax := ← setIntegerCheck name v (some 0) none }
  else if name == "capitals" then return { c with capitals := ← setIntegerCheck name v (some 0) (some 1) }
  else if name == "clamp" then return { c with clamp := ← setIntegerCheck name v (some 0) (some 1) }
  else if name == "rounding" then
    match v with
    | .str s =>
      match roundingOfName s with
      | some r => return { c with rounding := r }
      | none => throw (.typeError s!"{s}: invalid rounding mode")
    | _ => throw (.typeError "~: invalid rounding mode")
  else if name == "flags" then return { c with flags := ← setSignalDict v }
  else if name == "traps" then return { c with traps := ← setSignalDict v }
  else if name == "_ignored_flags" then return { c with ignored := ignoredOf v }
  else throw (.named "AttributeError" s!"'decimal.Context' object has no attribute '{name}'")

/-- `Context.__delattr__`, _pydecimal.py:4055-4056. -/
def pyDelattr (name : String) : Py Unit :=
  .error (.named "AttributeError" s!"{name} cannot be deleted")

/-- The arguments of `Context(...)`. -/
structure CtxInit where
  prec : CtxArg := .none
  rounding : CtxArg := .none
  emin : CtxArg := .none
  emax : CtxArg := .none
  capitals : CtxArg := .none
  clamp : CtxArg := .none
  flags : CtxArg := .none
  traps : CtxArg := .none
  ignored : Option (List Signal) := none
  deriving Repr, Inhabited

/-- `dict((s, int(s in l)) for s in _signals + l)`, _pydecimal.py:3994: a key
outside `_signals` stays in the dict for `_set_signal_dict` to refuse. -/
def signalDictOf (l : List SigKey) : List (SigKey × Bool) :=
  pySignals.map (fun s => (SigKey.sig s, l.contains (.sig s))) ++
    (if l.contains .other then [(.other, true)] else [])

/-- The value `Context()` assigns to `traps` or `flags`, _pydecimal.py:3991-4003. A
value that is neither a dict nor a list fails at `_signals + value`. -/
def signalArg (dflt : List (SigKey × Bool)) : CtxArg → Py CtxArg
  | .none => .ok (.dict dflt)
  | .dict d => .ok (.dict d)
  | .list l => .ok (.dict (signalDictOf l))
  | _ => .error (.typeError "~can only concatenate list to list")

def orElseArg (a dflt : CtxArg) : CtxArg :=
  match a with
  | .none => dflt
  | v => v

def keyed (d : SigDict) : List (SigKey × Bool) := d.map (fun p => (.sig p.1, p.2))

/-- `Context.__init__(...)`, _pydecimal.py:3969-4003; `dc` is `DefaultContext`. -/
def pyContextNew (dc : PyContext) (a : CtxInit) : Py PyContext := do
  let c := dc
  let c ← pySetattr c "prec" (orElseArg a.prec (.int dc.prec))
  let c ← pySetattr c "rounding" (orElseArg a.rounding (.str dc.rounding.name))
  let c ← pySetattr c "Emin" (orElseArg a.emin (.int dc.emin))
  let c ← pySetattr c "Emax" (orElseArg a.emax (.int dc.emax))
  let c ← pySetattr c "capitals" (orElseArg a.capitals (.int dc.capitals))
  let c ← pySetattr c "clamp" (orElseArg a.clamp (.int dc.clamp))
  let c ← pySetattr c "_ignored_flags" (.list ((a.ignored.getD []).map .sig))
  let c ← pySetattr c "traps" (← signalArg (keyed dc.traps) a.traps)
  pySetattr c "flags" (← signalArg (keyed (pySignals.map (fun s => (s, false)))) a.flags)

/-- `Context.__repr__`, _pydecimal.py:4066-4077: the names in dict order. -/
def setNames (d : SigDict) : List String := (d.filter (·.2)).map (fun p => p.1.name)

def pyContextRepr (c : PyContext) : String :=
  s!"Context(prec={c.prec}, rounding={c.rounding.name}, Emin={c.emin}, Emax={c.emax}, " ++
    s!"capitals={c.capitals}, clamp={c.clamp}, flags=[{", ".intercalate (setNames c.flags)}], " ++
    s!"traps=[{", ".intercalate (setNames c.traps)}])"

/-- `Context.clear_flags`, `clear_traps`, _pydecimal.py:4079-4087. -/
def clearDict (d : SigDict) : SigDict := d.map (fun p => (p.1, false))
def clearFlags (c : PyContext) : PyContext := { c with flags := clearDict c.flags }
def clearTraps (c : PyContext) : PyContext := { c with traps := clearDict c.traps }

/-- `Context.copy`, _pydecimal.py:4096-4102, and `Context._shallow_copy`, :4089-4094. -/
def contextCopy (dc c : PyContext) : Py PyContext :=
  pyContextNew dc
    { prec := .int c.prec, rounding := .str c.rounding.name, emin := .int c.emin, emax := .int c.emax
      capitals := .int c.capitals, clamp := .int c.clamp, flags := .dict (keyed c.flags)
      traps := .dict (keyed c.traps), ignored := some c.ignored }

/-- `Context.__reduce__`, _pydecimal.py:4059-4064: the arguments to rebuild the context. -/
def contextReduce (c : PyContext) : CtxInit :=
  { prec := .int c.prec, rounding := .str c.rounding.name, emin := .int c.emin, emax := .int c.emax
    capitals := .int c.capitals, clamp := .int c.clamp
    flags := .list ((c.flags.filter (·.2)).map (fun p => .sig p.1))
    traps := .list ((c.traps.filter (·.2)).map (fun p => .sig p.1)) }

/-- `Context._set_rounding`, _pydecimal.py:4156-4173. -/
def setRounding (c : PyContext) (type : CtxArg) : Py (PyContext × Rounding) := do
  let c' ← pySetattr c "rounding" type
  return (c', c.rounding)

/-- `Context._ignore_flags`, _pydecimal.py:4131-4136. -/
def ignoreFlags (c : PyContext) (fl : List Signal) : PyContext × List Signal :=
  ({ c with ignored := c.ignored ++ fl }, fl)

/-- `Context._ignore_all_flags`, _pydecimal.py:4127-4129. -/
def ignoreAllFlags (c : PyContext) : PyContext × List Signal := ignoreFlags c pySignals

/-- `Context._regard_flags`, _pydecimal.py:4138-4143: `self._ignored_flags.remove(flag)`
for each flag, which raises when one is missing. -/
def regardFlags (c : PyContext) : List Signal → Py PyContext
  | [] => .ok c
  | f :: fs =>
    if f ∈ c.ignored then regardFlags { c with ignored := c.ignored.erase f } fs
    else .error (.valueError "list.remove(x): x not in list")

/-- The fields of `Ctx` a `PyContext` holds; flags live in the `DM` state. -/
def PyContext.toCtx (c : PyContext) : Ctx :=
  { prec := c.prec.toNat, rounding := c.rounding, emin := c.emin, emax := c.emax
    capitals := c.capitals != 0, clamp := c.clamp != 0
    traps := (c.traps.filter (·.2)).map (·.1) }

/-! ## `create_decimal` -/

/-- `num != num.strip() or '_' in num`, _pydecimal.py:4181. -/
def needsStrip (s : List Char) : Bool := strip s != s || s.contains '_'

/-- `Context.create_decimal(num)` for a str, _pydecimal.py:4175-4190. -/
def createDecimalStr (c : Ctx) (s : List Char) : DM Dec := do
  if needsStrip s then return ← invalid c
  match pyParse s with
  | .error e => if e == invalidOp then return ← invalid c else throw e
  | .ok d =>
    if isnan d ≠ 0 ∧ (if payloadOf d = 0 then (0 : Int) else numDigits (payloadOf d)) >
        (c.prec : Int) - (if c.clamp then 1 else 0) then
      return ← invalid c
    fix c d

/-- `Context.create_decimal(num)` for a Decimal or an int: `Decimal(num, context=self)` is exact. -/
def createDecimalArg (c : Ctx) (a : Arg) : DM Dec := do
  let d ← liftPy (convertRaise a)
  if isnan d ≠ 0 ∧ (if payloadOf d = 0 then (0 : Int) else numDigits (payloadOf d)) >
      (c.prec : Int) - (if c.clamp then 1 else 0) then
    return ← invalid c
  fix c d

/-! ## The current context -/

/-- The thread's `_current_context_var`. -/
structure ThreadCtx where
  current : Option PyContext
  deriving Repr, DecidableEq, Inhabited

/-- `getcontext`, _pydecimal.py:358-370: a thread with no context gets `Context()`. -/
def getContext (dc : PyContext) (t : ThreadCtx) : Py (PyContext × ThreadCtx) :=
  match t.current with
  | some c => .ok (c, t)
  | none => do
    let c ← pyContextNew dc {}
    return (c, { current := some c })

/-- `setcontext`, _pydecimal.py:372-377. `template` says that the object is
`DefaultContext`, `BasicContext` or `ExtendedContext`. -/
def setContext (dc : PyContext) (ctx : PyContext) (template : Bool) : Py ThreadCtx := do
  if template then
    let c ← contextCopy dc ctx
    return { current := some (clearFlags c) }
  return { current := some ctx }

/-- `_ContextManager`, _pydecimal.py:3935-3948. -/
structure CtxManager where
  newContext : PyContext
  saved : Option PyContext := none
  deriving Repr, Inhabited

/-- `_ContextManager.__init__`, _pydecimal.py:3941-3942. -/
def managerInit (dc ctx : PyContext) : Py CtxManager := do
  return { newContext := ← contextCopy dc ctx }

/-- `_ContextManager.__enter__`, _pydecimal.py:3943-3946. -/
def managerEnter (dc : PyContext) (m : CtxManager) (t : ThreadCtx) :
    Py (CtxManager × ThreadCtx × PyContext) := do
  let (saved, t1) ← getContext dc t
  let m' := { m with saved := some saved }
  let t2 ← setContext dc m.newContext false
  let _ := t1
  return (m', t2, m.newContext)

/-- `_ContextManager.__exit__`, _pydecimal.py:3947-3948. -/
def managerExit (dc : PyContext) (m : CtxManager) : Py ThreadCtx :=
  match m.saved with
  | some s => setContext dc s false
  | none => .error (.named "AttributeError" "~saved_context")

/-- `_context_attributes`, _pydecimal.py:354-356. -/
def contextAttributes : List String :=
  ["prec", "Emin", "Emax", "capitals", "clamp", "rounding", "flags", "traps"]

/-- `setattr(ctx_manager.new_context, key, value)` for each keyword, in order. -/
def applyKwargs (m : CtxManager) : List (String × CtxArg) → Py CtxManager
  | [] => .ok m
  | (key, value) :: rest =>
    if key ∈ contextAttributes then do
      let nc ← pySetattr m.newContext key value
      applyKwargs { m with newContext := nc } rest
    else .error (.typeError s!"'{key}' is an invalid keyword argument for this function")

/-- `localcontext`, _pydecimal.py:381-424. -/
def localContext (dc : PyContext) (t : ThreadCtx) (ctx : Option PyContext)
    (kwargs : List (String × CtxArg)) : Py (CtxManager × ThreadCtx) := do
  let (base, t1) ← match ctx with
    | some c => pure (c, t)
    | none => getContext dc t
  let m ← managerInit dc base
  let m ← applyKwargs m kwargs
  return (m, t1)

/-- `IEEE_CONTEXT_MAX_BITS`, _pydecimal.py:89, for a 64-bit `sys.maxsize`. -/
def ieeeMaxBits : Int := 512

/-- `IEEEContext`, _pydecimal.py:427-445. -/
def ieeeContext (dc : PyContext) (bits : Int) : Py PyContext := do
  if bits ≤ 0 ∨ bits > ieeeMaxBits ∨ bits % 32 ≠ 0 then
    throw (.valueError s!"argument must be a multiple of 32, with a maximum of {ieeeMaxBits}")
  let ctx ← pyContextNew dc {}
  let ctx ← pySetattr ctx "prec" (.int (9 * (bits / 32) - 2))
  let emax : Int := 3 * (2 ^ (bits / 16 + 3).toNat)
  let ctx ← pySetattr ctx "Emax" (.int emax)
  let ctx ← pySetattr ctx "Emin" (.int (1 - emax))
  let ctx ← pySetattr ctx "rounding" (.str "ROUND_HALF_EVEN")
  let ctx ← pySetattr ctx "clamp" (.int 1)
  pySetattr ctx "traps" (.dict (keyed (pySignals.map (fun s => (s, false)))))

/-! ## Numbers the module exports -/

/-- `DefaultContext`, _pydecimal.py:6157-6165. -/
def defaultContext : PyContext :=
  { prec := 28, rounding := .halfEven, emin := -999999, emax := 999999, capitals := 1, clamp := 0
    flags := pySignals.map (fun s => (s, false))
    traps := pySignals.map (fun s => (s, s == .divisionByZero || s == .overflow || s == .invalidOperation))
    ignored := [] }

end PyLean.Decimal
