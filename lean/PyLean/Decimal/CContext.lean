import PyLean.Decimal.Context

/-!
`_decimal`'s context: status bits, `SignalDict`, the `Context` type, the current
context and the context manager (Modules/_decimal/_decimal.c).

Status words keep libmpdec's condition bits (`Bit`), because they are visible: a
signal covers a set of bits (`MPD_IEEE_Invalid_operation` covers seven), exception
args list conditions rather than signals, and `repr(context)` places
InvalidOperation by the first bit set. A word is a list of bits with set semantics.
`DEC_ERRORS` return values are modelled as `Py` errors.

Identity is not modelled, so `template` arguments say whether an object is one of
the three templates, and `SigObj` is `none` for a `SignalDict` with a NULL
`flags` pointer.
-/

namespace PyLean.Decimal

open PyLean

/-- Status bits in bit order, libmpdec/mpdecimal.h:256-270. `notImplemented` is
`MPD_Float_operation`, _decimal.c:196. -/
inductive Bit where
  | clamped | conversionSyntax | divisionByZero | divisionImpossible | divisionUndefined
  | fpuError | inexact | invalidContext | invalidOperation | mallocError | notImplemented
  | overflow | rounded | subnormal | underflow
  deriving Repr, DecidableEq, Inhabited

def allBits : List Bit :=
  [.clamped, .conversionSyntax, .divisionByZero, .divisionImpossible, .divisionUndefined,
   .fpuError, .inexact, .invalidContext, .invalidOperation, .mallocError, .notImplemented,
   .overflow, .rounded, .subnormal, .underflow]

/-- `MPD_IEEE_Invalid_operation`, libmpdec/mpdecimal.h:274-280. -/
def ieeeInvalid : List Bit :=
  [.conversionSyntax, .divisionImpossible, .divisionUndefined, .fpuError, .invalidContext,
   .invalidOperation, .mallocError]

abbrev Status := List Bit

/-- `a | b`, in bit order. -/
def orBits (a b : Status) : Status := allBits.filter (fun x => a.contains x || b.contains x)

/-- `a & b`, in bit order. -/
def andBits (a b : Status) : Status := allBits.filter (fun x => a.contains x && b.contains x)

/-- `a & ~b`, in bit order. -/
def clearBits (a b : Status) : Status := allBits.filter (fun x => a.contains x && !b.contains x)

/-- The `flag` of a `signal_map` row, _decimal.c:291-299. -/
def Signal.flagBits : Signal → Status
  | .invalidOperation => ieeeInvalid
  | .floatOperation => [.notImplemented]
  | .divisionByZero => [.divisionByZero]
  | .overflow => [.overflow]
  | .underflow => [.underflow]
  | .subnormal => [.subnormal]
  | .inexact => [.inexact]
  | .rounded => [.rounded]
  | .clamped => [.clamped]

/-- `signal_map`, _decimal.c:291-299. -/
def signalMap : List Signal :=
  [.invalidOperation, .floatOperation, .divisionByZero, .overflow, .underflow,
   .subnormal, .inexact, .rounded, .clamped]

/-- `flags & cm->flag`. -/
def hasSignal (st : Status) (s : Signal) : Bool := s.flagBits.any st.contains

/-- `cond_map`, _decimal.c:305-309, without the `EXTRA_FUNCTIONALITY` row for MallocError
(:310-312), which CPython builds leave out. -/
def condMap : List (Bit × String) :=
  [(.invalidOperation, "InvalidOperation"), (.conversionSyntax, "ConversionSyntax"),
   (.divisionImpossible, "DivisionImpossible"), (.divisionUndefined, "DivisionUndefined"),
   (.invalidContext, "InvalidContext")]

/-- `flags_as_exception`, _decimal.c:419-430. -/
def flagsAsException (st : Status) : Option Signal := signalMap.find? (hasSignal st)

/-- `exception_as_flag`, _decimal.c:432-446 (inventory: `Py_LOCAL_INLINE`). -/
def exceptionAsFlag : SigKey → Py Status
  | .sig s => .ok s.flagBits
  | .other .. => .error (.keyError "~valid values for signals are")

/-- `flags_as_list`, _decimal.c:448-478: conditions first, then `signal_map+1`. -/
def flagsAsList (st : Status) : List String :=
  (condMap.filter (fun p => st.contains p.1)).map (·.2) ++
    ((signalMap.drop 1).filter (hasSignal st)).map Signal.name

/-- `signals_as_list`, _decimal.c:481-501. -/
def signalsAsList (st : Status) : List Signal := signalMap.filter (hasSignal st)

/-- `list_as_flags`, _decimal.c:504-524. -/
def listAsFlags : List SigKey → Py Status
  | [] => .ok []
  | k :: rest => do
    let x ← exceptionAsFlag k
    let r ← listAsFlags rest
    return orBits x r

/-- `flags_as_dict`, _decimal.c:527-546. -/
def flagsAsDict (st : Status) : SigDict := signalMap.map (fun s => (s, hasSignal st s))

/-- `PyDict_GetItemWithError(val, signal)` then `PyObject_IsTrue` of the value (_decimal.c:571-583). -/
def lookupKey (d : List (SigKey × SigVal)) (k : SigKey) : Option Bool :=
  (d.find? (fun p => p.1 == k)).map (·.2.truth)

/-- `dict_as_flags`, _decimal.c:549-589. Since 3.15 it takes `PyAnyDict_Check`, so a
`frozendict` is `CtxArg.dict` here; `_pydecimal` still wants a `dict`. -/
def dictAsFlags : CtxArg → Py Status
  | .dict d =>
    if d.length ≠ 9 then .error (.keyError "'invalid signal dict'")
    else
      signalMap.foldlM (fun (flags : Status) cm =>
        match lookupKey d (.sig cm) with
        | none => .error (.keyError "'invalid signal dict'")
        | some true => .ok (orBits flags cm.flagBits)
        | some false => .ok flags) []
  | _ => .error (.typeError "argument must be a signal dict")

/-! ## The context -/

/-- A `_decimal.Context`: `mpd_context_t` and `capitals`. -/
structure CContext where
  prec : Int
  emax : Int
  emin : Int
  traps : Status
  status : Status
  round : Rounding
  clamp : Int
  capitals : Int
  deriving Repr, DecidableEq, Inhabited

/-- `dflt_ctx`, _decimal.c:1428-1432. -/
def dfltCtx : CContext :=
  { prec := 28, emax := 999999, emin := -999999
    traps := orBits ieeeInvalid [.divisionByZero, .overflow], status := []
    round := .halfEven, clamp := 0, capitals := 1 }

/-- `dec_addstatus`, _decimal.c:611-639: the status is merged first, then the first
trapped signal in `signal_map` order raises. -/
def decAddStatus (c : CContext) (status : Status) : CContext × Option PyExc :=
  let c' := { c with status := orBits c.status status }
  if (andBits status (orBits c.traps [.mallocError])).isEmpty then (c', none)
  else if status.contains .mallocError then (c', some (.named "MemoryError" ""))
  else
    match flagsAsException (andBits c.traps status) with
    | some s => (c', some (.named s.name "~"))
    | none => (c', some (.named "RuntimeError" "internal error in flags_as_exception"))

/-- `getround`, _decimal.c:642-659. -/
def getRound : CtxArg → Py Rounding
  | .str s =>
    match roundingOfName s with
    | some r => .ok r
    | none => .error (.typeError "~valid values for rounding are")
  | _ => .error (.typeError "~valid values for rounding are")

/-- `PyLong_AsSsize_t`. -/
def longAsSsize : CtxArg → Py Int
  | .int n =>
    if n < mpdSsizeMin ∨ n > mpdSsizeMax then .error (.overflowError "~Python int too large to convert to C ssize_t")
    else .ok n
  | .bool b => .ok (if b then 1 else 0)
  | _ => .error (.typeError "~object cannot be interpreted as an integer")

/-- `context_setprec`, _decimal.c:954-971, and `mpd_qsetprec`, libmpdec/context.c:198-205. -/
def contextSetprec (c : CContext) (v : CtxArg) : Py CContext := do
  let x ← longAsSsize v
  if x ≤ 0 ∨ x > mpdMaxPrec then throw (.valueError "valid range for prec is [1, MAX_PREC]")
  return { c with prec := x }

/-- `context_setemin`, _decimal.c:974-991, and `mpd_qsetemin`, libmpdec/context.c:218-225. -/
def contextSetemin (c : CContext) (v : CtxArg) : Py CContext := do
  let x ← longAsSsize v
  if x > 0 ∨ x < mpdMinEmin then throw (.valueError "valid range for Emin is [MIN_EMIN, 0]")
  return { c with emin := x }

/-- `context_setemax`, _decimal.c:994-1011, and `mpd_qsetemax`, libmpdec/context.c:208-215. -/
def contextSetemax (c : CContext) (v : CtxArg) : Py CContext := do
  let x ← longAsSsize v
  if x < 0 ∨ x > mpdMaxEmax then throw (.valueError "valid range for Emax is [0, MAX_EMAX]")
  return { c with emax := x }

/-- `context_setround`, _decimal.c:1085-1102. -/
def contextSetround (c : CContext) (v : CtxArg) : Py CContext := do
  return { c with round := ← getRound v }

/-- `context_setcapitals`, _decimal.c:1105-1121. -/
def contextSetcapitals (c : CContext) (v : CtxArg) : Py CContext := do
  let x ← longAsSsize v
  if x ≠ 0 ∧ x ≠ 1 then throw (.valueError "valid values for capitals are 0 or 1")
  return { c with capitals := x }

/-- `context_setclamp`, _decimal.c:1255-1272: `BOUNDS_CHECK` turns a value outside
`int` into `INT_MAX`, which `mpd_qsetclamp` then refuses. -/
def contextSetclamp (c : CContext) (v : CtxArg) : Py CContext := do
  let x ← longAsSsize v
  let x : Int := if x < -(2 ^ 31) ∨ 2 ^ 31 - 1 < x then 2 ^ 31 - 1 else x
  if x ≠ 0 ∧ x ≠ 1 then throw (.valueError "valid values for clamp are 0 or 1")
  return { c with clamp := x }

/-- `context_settraps_list`, _decimal.c:1145-1161. -/
def contextSettrapsList (c : CContext) (l : List SigKey) : Py CContext := do
  return { c with traps := ← listAsFlags l }

/-- `context_settraps_dict`, _decimal.c:1164-1186. -/
def contextSettrapsDict (c : CContext) (v : CtxArg) : Py CContext := do
  return { c with traps := ← dictAsFlags v }

/-- `context_setstatus_list`, _decimal.c:1210-1227. -/
def contextSetstatusList (c : CContext) (l : List SigKey) : Py CContext := do
  return { c with status := ← listAsFlags l }

/-- `context_setstatus_dict`, _decimal.c:1230-1252. -/
def contextSetstatusDict (c : CContext) (v : CtxArg) : Py CContext := do
  return { c with status := ← dictAsFlags v }

/-- `context_setattr`, _decimal.c:1316-1334, after which `PyObject_GenericSetAttr`
reaches the getset table. -/
def cSetattr (c : CContext) (name : String) (v : CtxArg) : Py CContext :=
  if name == "traps" then contextSettrapsDict c v
  else if name == "flags" then contextSetstatusDict c v
  else if name == "prec" then contextSetprec c v
  else if name == "Emin" then contextSetemin c v
  else if name == "Emax" then contextSetemax c v
  else if name == "rounding" then contextSetround c v
  else if name == "capitals" then contextSetcapitals c v
  else if name == "clamp" then contextSetclamp c v
  else .error (.named "AttributeError" s!"'decimal.Context' object has no attribute '{name}'")

/-- `context_setattrs`, _decimal.c:1337-1396. `None` skips a field. -/
def contextSetattrs (c : CContext) (a : CtxInit) : Py CContext := do
  let step (f : CContext → CtxArg → Py CContext) (c : CContext) (v : CtxArg) : Py CContext :=
    match v with
    | .none => .ok c
    | v => f c v
  let c ← step contextSetprec c a.prec
  let c ← step contextSetround c a.rounding
  let c ← step contextSetemin c a.emin
  let c ← step contextSetemax c a.emax
  let c ← step contextSetcapitals c a.capitals
  let c ← step contextSetclamp c a.clamp
  let c ← match a.traps with
    | .none => pure c
    | .list l => contextSettrapsList c l
    | v => contextSettrapsDict c v
  match a.flags with
  | .none => pure c
  | .list l => contextSetstatusList c l
  | v => contextSetstatusDict c v

/-- `context_new`, _decimal.c:1435-1486: `*ctx = *CTX(state->default_context_template)`
(:1468, every field, `status` included), then `CtxCaps(self) = 1` (:1477), whatever the
template's `capitals`. -/
def contextNew (template : CContext) : CContext := { template with capitals := 1 }

/-- `Context(...)`: `context_new` then `context_init_impl`, _decimal.c:1556-1567. -/
def cContextCall (template : CContext) (a : CtxInit) : Py CContext :=
  contextSetattrs (contextNew template) a

/-- `_decimal_Context_clear_traps_impl`, `_decimal_Context_clear_flags_impl`, _decimal.c:1403-1423. -/
def cClearTraps (c : CContext) : CContext := { c with traps := [] }
def cClearFlags (c : CContext) : CContext := { c with status := [] }

/-- `context_copy`, _decimal.c:1671-1686: every field, `capitals` included. -/
def contextCopyC (c : CContext) : CContext := c

/-- `_decimal_Context___reduce___impl`, _decimal.c:1724-1756: the constructor arguments. -/
def contextReduceC (c : CContext) : CtxInit :=
  { prec := .int c.prec, rounding := .str c.round.name, emin := .int c.emin, emax := .int c.emax
    capitals := .int c.capitals, clamp := .int c.clamp
    flags := .list ((signalsAsList c.status).map .sig)
    traps := .list ((signalsAsList c.traps).map .sig) }

/-- `dec_signal_string`, _decimal.c:331-347. -/
def Bit.sigString : Bit → String
  | .clamped => "Clamped"
  | .divisionByZero => "DivisionByZero"
  | .inexact => "Inexact"
  | .notImplemented => "FloatOperation"
  | .overflow => "Overflow"
  | .rounded => "Rounded"
  | .subnormal => "Subnormal"
  | .underflow => "Underflow"
  | _ => "InvalidOperation"

/-- `mpd_lsnprint_signals`, libmpdec/io.c:1535-1575: in bit order, and
InvalidOperation once, at the first of its bits that is set. -/
def lsnprintSignals (st : Status) : String :=
  let names := (allBits.filter st.contains).foldl
    (fun (acc : List String × Bool) b =>
      if ieeeInvalid.contains b then
        if acc.2 then acc else (acc.1 ++ [b.sigString], true)
      else (acc.1 ++ [b.sigString], acc.2)) ([], false)
  "[" ++ ", ".intercalate names.1 ++ "]"

/-- `context_repr`, _decimal.c:1570-1599. -/
def contextReprC (c : CContext) : String :=
  s!"Context(prec={c.prec}, rounding={c.round.name}, Emin={c.emin}, Emax={c.emax}, " ++
    s!"capitals={c.capitals}, clamp={c.clamp}, flags={lsnprintSignals c.status}, " ++
    s!"traps={lsnprintSignals c.traps})"

/-- `init_basic_context`, _decimal.c:1602-1612. -/
def basicContextC : CContext :=
  { dfltCtx with prec := 9, traps := orBits dfltCtx.traps [.underflow, .clamped], round := .halfUp, capitals := 1 }

/-- `init_extended_context`, _decimal.c:1615-1624. -/
def extendedContextC : CContext :=
  { dfltCtx with prec := 9, traps := [], capitals := 1 }

/-- `MPD_IEEE_CONTEXT_MAX_BITS` on a 64-bit build. -/
def mpdIeeeMaxBits : Int := 512

/-- `_decimal_IEEEContext`, whose clinic `Py_ssize_t` converter takes `__index__`, and
`_decimal_IEEEContext_impl`, _decimal.c:1640-1669, with `mpd_ieee_context`,
libmpdec/context.c:129-146. -/
def ieeeContextC (template : CContext) (v : CtxArg) : Py CContext := do
  let bits ← longAsSsize v
  let err : PyExc := .valueError s!"argument must be a multiple of 32, with a maximum of {mpdIeeeMaxBits}"
  if bits ≤ 0 ∨ bits > 2 ^ 31 - 1 then throw err
  if bits ≤ 0 ∨ bits > mpdIeeeMaxBits ∨ bits % 32 ≠ 0 then throw err
  let context := contextNew template
  let emax : Int := 3 * 2 ^ (bits / 16 + 3).toNat
  return { context with
    prec := 9 * (bits / 32) - 2, emax := emax, emin := 1 - emax, round := .halfEven
    traps := [], status := [], clamp := 1 }

/-! ## `SignalDict` -/

/-- A `SignalDict`: the word it points at, or `none` for a NULL pointer
(`signaldict_init`, _decimal.c:675-680). -/
abbrev SigObj := Option Status

def invalidSd : PyExc := .valueError "invalid signal dict"

/-- `signaldict_len`, _decimal.c:683-689. -/
def signaldictLen : SigObj → Py Nat
  | none => .error invalidSd
  | some _ => .ok 9

/-- `signaldict_iter`, _decimal.c:692-699: the signals in `signal_map` order. -/
def signaldictIter : SigObj → Py (List Signal)
  | none => .error invalidSd
  | some _ => .ok signalMap

/-- `signaldict_getitem`, _decimal.c:702-716. -/
def signaldictGetitem (sd : SigObj) (key : SigKey) : Py Bool :=
  match sd with
  | none => .error invalidSd
  | some st => do
    let flag ← exceptionAsFlag key
    return flag.any st.contains

/-- `signaldict_setitem`, _decimal.c:719-751: `value = none` is `del`. -/
def signaldictSetitem (sd : SigObj) (key : SigKey) (value : Option Bool) : Py Status :=
  match sd with
  | none => .error invalidSd
  | some st =>
    match value with
    | none => .error (.valueError "signal keys cannot be deleted")
    | some x => do
      let flag ← exceptionAsFlag key
      return if x then orBits st flag else clearBits st flag

/-- `cm->fqname`, _decimal.c:291-299. -/
def Signal.fqname (s : Signal) : String := "decimal." ++ s.name

/-- `signaldict_repr`, _decimal.c:763-788. -/
def signaldictRepr : SigObj → Py String
  | none => .error invalidSd
  | some st =>
    .ok ("{" ++ ", ".intercalate (signalMap.map (fun s =>
      s!"<class '{s.fqname}'>:" ++ (if hasSignal st s then "True" else "False"))) ++ "}")

/-- The right operand of a `SignalDict` comparison. -/
inductive SdOperand where
  | sd (w : SigObj)
  | dict (d : List (SigKey × SigVal))
  | other

/-- `signaldict_richcompare`, _decimal.c:791-824, for `==` (`ne = false`) and `!=`.
`none` is `NotImplemented`. A dict with invalid signals compares as `NotImplemented`. -/
def signaldictRichcompare (v : SigObj) (w : SdOperand) (ne : Bool) : Py (Option Bool) :=
  match v, w with
  | none, .sd _ | none, .dict _ | none, .other => .error invalidSd
  | some _, .sd none => .error invalidSd
  | some a, .sd (some b) => .ok (some (((andBits a allBits) == (andBits b allBits)) != ne))
  | some a, .dict d =>
    match dictAsFlags (.dict d) with
    | .ok flags => .ok (some (((andBits a allBits) == (andBits flags allBits)) != ne))
    | .error _ => .ok none
  | some _, .other => .ok none

/-- `signaldict_copy`, _decimal.c:827-834: a plain dict. -/
def signaldictCopy : SigObj → Py SigDict
  | none => .error invalidSd
  | some st => .ok (flagsAsDict st)

/-! ## The current context and the context manager -/

/-- The thread's `current_context_var`. -/
structure CThread where
  current : Option CContext
  deriving Repr, DecidableEq, Inhabited

/-- `init_current_context`, _decimal.c:1932-1948: a copy of the template with
`status` cleared, unlike `context_new`. -/
def initCurrentContext (template : CContext) : CContext :=
  { contextCopyC template with status := [] }

/-- `current_context`, _decimal.c:1951-1967; `PyDec_GetCurrentContext`, :1976-1981. -/
def currentContextC (template : CContext) (t : CThread) : CContext × CThread :=
  match t.current with
  | some c => (c, t)
  | none =>
    let c := initCurrentContext template
    (c, { current := some c })

/-- `PyDec_SetCurrentContext`, _decimal.c:1985-2013. -/
def setCurrentContextC (v : CContext) (template : Bool) : CThread :=
  if template then { current := some { contextCopyC v with status := [] } }
  else { current := some v }

/-- The `ctx` argument of `localcontext`. -/
inductive LocalArg where
  | none
  | ctx (c : CContext)
  | other

/-- `_decimal_localcontext_impl`, _decimal.c:2072-2120: the local context, and the global one to restore. -/
def ctxmanagerNew (template : CContext) (t : CThread) (local_ : LocalArg) (a : CtxInit) :
    Py (CContext × CContext × CThread) := do
  let (global, t1) := currentContextC template t
  let base ← match local_ with
    | .none => pure global
    | .ctx c => pure c
    | .other => throw (.typeError "optional argument must be a context")
  let localCopy ← contextSetattrs (contextCopyC base) a
  return (localCopy, global, t1)

/-- `ctxmanager_set_local`, _decimal.c:2152-2163. -/
def ctxmanagerSetLocal (localCopy : CContext) : CThread × CContext :=
  (setCurrentContextC localCopy false, localCopy)

/-- `ctxmanager_restore_global`, _decimal.c:2166-2177. -/
def ctxmanagerRestoreGlobal (global : CContext) : CThread := setCurrentContextC global false

/-! ## `Context.canonical` -/

/-- `_decimal_Context_canonical_impl`, _decimal.c:7020-7033: `Decimal` only, like `_pydecimal`, with
another message. -/
def ctxCanonicalC : Arg → Py Dec
  | .dec d => .ok (canonicalD d)
  | _ => .error (.typeError "argument must be a Decimal")

/-- `_decimal_Context_is_canonical_impl`, _decimal.c:6962-6975. -/
def ctxIsCanonicalC : Arg → Py Bool
  | .dec d => .ok (isCanonical d)
  | _ => .error (.typeError "argument must be a Decimal")

/-! ## libmpdec's integer division

`_pydecimal` returns the quotient of `_divide` as it is; libmpdec finalizes it. -/

/-- A context whose signals do not raise: libmpdec records status and
`dec_addstatus` decides afterwards. -/
def noTraps (c : Ctx) : Ctx := { c with traps := [] }

/-- An operation as `_decimal` runs it: all of its status is collected, merged into the
context's flags, and then the first trapped signal in `signal_map` order raises
(`dec_addstatus`, _decimal.c:611-639). -/
def cOp {α : Type} (c : Ctx) (body : DM α) : DM α := fun fl => do
  let (r, st) ← body.run []
  let fl' := st.foldl (fun acc s => if s ∈ acc then acc else acc ++ [s]) fl
  match signalMap.find? (fun s => st.contains s && c.traps.contains s) with
  | some s => .error (.named s.name "~")
  | none => .ok (r, fl')

/-- `_mpd_qdivmod`, libmpdec/mpdecimal.c:3955-4094, for finite operands and `b ≠ 0`.
`none` is `MPD_Division_impossible`. -/
def mpdDivmodFin (c : Ctx) (sa : Bool) (ca : Nat) (ea : Int) (sb : Bool) (cb : Nat) (eb : Int) :
    Option (Dec × Dec) :=
  let idealExp := min ea eb
  let sab := sa != sb
  if ca = 0 then some (.fin sab 0 0, .fin sa 0 idealExp)
  else
    let expdiff := adjustedD ca ea - adjustedD cb eb
    if expdiff < 0 then
      some (.fin sab 0 0, if ea > eb then .fin sa (ca * 10 ^ (ea - eb).toNat) idealExp else .fin sa ca ea)
    else if expdiff > c.prec then none
    else
      let p := scaled ca ea cb eb
      let q := p.1 / p.2
      if numDigits q > c.prec then none
      else some (.fin sab q 0, .fin sa (p.1 % p.2) idealExp)

/-- `mpd_qdivint`, libmpdec/mpdecimal.c:4151-4191: the quotient goes through
`mpd_qfinalize` (:4190), which is `_fix`. -/
def mpdDivint (c : Ctx) (a b : Dec) : DM Dec := do
  let sign := a.neg != b.neg
  if isSpecial a || isSpecial b then
    if let some ans ← checkNans c a (some b) then return ans
    if isinfinity a ≠ 0 ∧ isinfinity b ≠ 0 then return ← invalid c
    if isinfinity a ≠ 0 then return .inf sign
    if isinfinity b ≠ 0 then return .fin sign 0 0
  if isZero b then
    if isZero a then return ← invalid c
    return ← divByZero c sign
  match a, b with
  | .fin sa ca ea, .fin sb cb eb =>
    match mpdDivmodFin c sa ca ea sb cb eb with
    | some p => fix c p.1
    | none => invalid c
  | _, _ => return a

/-- `mpd_qdivmod`, libmpdec/mpdecimal.c:4098-4148: both results go through `mpd_qfinalize`
(:4146-4147). -/
def mpdDivmod (c : Ctx) (a b : Dec) : DM (Dec × Dec) := do
  let sign := a.neg != b.neg
  if isSpecial a || isSpecial b then
    if let some ans ← checkNans c a (some b) then return (ans, ans)
    if isinfinity a ≠ 0 then
      let q : Dec := if isinfinity b ≠ 0 then nanD else .inf sign
      raiseSig c .invalidOperation
      return (q, nanD)
    if isinfinity b ≠ 0 then
      let r ← fix c a
      return (.fin sign 0 0, r)
  if isZero b then
    if isZero a then
      raiseSig c .invalidOperation
      return (nanD, nanD)
    raiseSig c .divisionByZero
    raiseSig c .invalidOperation
    return (.inf sign, nanD)
  match a, b with
  | .fin sa ca ea, .fin sb cb eb =>
    match mpdDivmodFin c sa ca ea sb cb eb with
    | some p =>
      let q ← fix c p.1
      let r ← fix c p.2
      return (q, r)
    | none =>
      raiseSig c .invalidOperation
      return (nanD, nanD)
  | _, _ => return (a, a)

/-- `a // b` and `divmod(a, b)` in `_decimal`. -/
def floordivC (c : Ctx) (a b : Dec) : DM Dec := cOp c (mpdDivint (noTraps c) a b)
def divmodC (c : Ctx) (a b : Dec) : DM (Dec × Dec) := cOp c (mpdDivmod (noTraps c) a b)

end PyLean.Decimal
