import PyLean.Bytecode.ObjModel

/-!
Helpers of `Python/ceval.c` that the instruction bodies call, CPython 3.15.2:
the exception table (`get_exception_handler`), argument binding
(`initialize_locals`), frame creation, `do_raise`, unpacking, name lookup and the
error formatters. Line numbers refer to `Python/ceval.c` unless stated otherwise; on 3.15
the exception table search and `do_raise` live in `Python/ceval.h`.
-/

namespace PyLean.Bytecode

/-! ## The dict primitives that argument binding and namespaces need -/

/-- `_Py_HashSecret`-free stand-in for `unicode_hash`: only equality of hashes of
equal strings is observable from the interpreter (the difftest never prints a
str hash, which is randomized in CPython anyway). -/
def hashStr (s : String) : Int :=
  Int.ofNat (s.foldl (fun h c => (h * 1000003 + c.toNat) % 2305843009213693951) 7)

/-- `lookdict`: first entry with an equal stored hash for which `eq` holds. -/
def dictFind (eq : Val → RM Bool) (d : DictObj) (h : Int) : RM (Option Nat) :=
  let rec go : Nat → Nat → RM (Option Nat)
    | 0, _ => pure none
    | n + 1, i => do
      match d.entries[i]? with
      | none => pure none
      | some e =>
        if e.hash == h then
          if ← eq e.key then pure (some i) else go n (i + 1)
        else go n (i + 1)
  go d.entries.size 0

def getDict : Val → RM DictObj
  | .ref a => do
    match ← getObj a with
    | .dict d => pure d
    | _ => fault "expected a dict"
  | _ => fault "expected a dict"

def putDict (v : Val) (d : DictObj) : RM Unit :=
  match v with
  | .ref a => setObj a (.dict d)
  | _ => fault "expected a dict"

def strKeyEq (name : String) (k : Val) : RM Bool := pure (k == .str name)

/-- `PyDict_GetItemRef` for a str key, on an exact dict. -/
def dictGetStr (dv : Val) (name : String) : RM (Option Val) := do
  let d ← getDict dv
  match ← dictFind (strKeyEq name) d (hashStr name) with
  | some i => pure (d.entries[i]?.map (·.value))
  | none => pure none

/-- `insertdict`: replace the value of `idx`, or append and change `dk_version`. -/
def dictInsertAt (dv : Val) (d : DictObj) (idx : Option Nat) (h : Int) (k v : Val) : RM Unit := do
  match idx with
  | some i =>
    putDict dv { d with entries := d.entries.modify i fun e => { e with value := v } }
  | none =>
    let ver ← freshVersion
    putDict dv { entries := d.entries.push { hash := h, key := k, value := v }, version := ver }

/-- `delitem_common`. -/
def dictRemoveAt (dv : Val) (d : DictObj) (i : Nat) : RM Unit := do
  let ver ← freshVersion
  putDict dv { entries := d.entries.eraseIdxIfInBounds i, version := ver }

/-- `PyDict_SetItem` for a str key. -/
def dictSetStr (dv : Val) (name : String) (v : Val) : RM Unit := do
  let d ← getDict dv
  let h := hashStr name
  let idx ← dictFind (strKeyEq name) d h
  dictInsertAt dv d idx h (.str name) v

/-- `PyDict_Pop(d, name, NULL)`: `false` when the key is absent. -/
def dictPopStr (dv : Val) (name : String) : RM Bool := do
  let d ← getDict dv
  match ← dictFind (strKeyEq name) d (hashStr name) with
  | some i => dictRemoveAt dv d i; pure true
  | none => pure false

def mkDict : RM Val := do
  let ver ← freshVersion
  alloc (.dict { version := ver })

/-- `PyDict_CheckExact`. -/
def isExactDict : Val → RM Bool
  | .ref a => do
    match ← getObj a with
    | .dict _ => pure true
    | _ => pure false
  | _ => pure false

/-- `PyList_CheckExact`. -/
def isExactList : Val → RM Bool
  | .ref a => do
    match ← getObj a with
    | .list _ => pure true
    | _ => pure false
  | _ => pure false

/-- `PyTuple_CheckExact`. -/
def isExactTuple : Val → RM Bool
  | .ref a => do
    match ← getObj a with
    | .tuple _ => pure true
    | _ => pure false
  | _ => pure false

/-! ## Exception table -/

/-- `parse_varint` (`Include/internal/pycore_code.h`): the value and the next
position. The 6-bit groups are big-endian, bit 6 means "more". -/
def parseVarint (t : Array Nat) (p : Nat) : Nat × Nat :=
  let rec go : Nat → Nat → Nat → Nat × Nat
    | 0, q, val => (val, q + 1)
    | n + 1, q, val =>
      if (t.getD q 0) &&& 64 != 0 then
        go n (q + 1) ((val <<< 6) ||| (t.getD (q + 1) 0 &&& 63))
      else (val, q + 1)
  go t.size p (t.getD p 0 &&& 63)

/-- `scan_back_to_entry_start`, `Python/ceval.h:440-444`. -/
def scanBack (t : Array Nat) : Nat → Nat → Nat
  | 0, p => p
  | n + 1, p => if (t.getD p 128) &&& 128 == 0 then scanBack t n (p - 1) else p

/-- `skip_to_next_entry`, `Python/ceval.h:446-452`. -/
def skipToNext (t : Array Nat) (e : Nat) : Nat → Nat → Nat
  | 0, p => p
  | n + 1, p => if p < e && (t.getD p 128) &&& 128 == 0 then skipToNext t e n (p + 1) else p

/-- `#define MAX_LINEAR_SEARCH 40`, `Python/ceval.h:455`. -/
def maxLinearSearch : Nat := 40

/-- The linear scan of `get_exception_handler`, `Python/ceval.h:457-505`:
`some (handler, level, lasti)`. -/
def scanTable (t : Array Nat) (e index : Nat) : Nat → Nat → Option (Nat × Nat × Bool)
  | 0, _ => none
  | n + 1, scan =>
    if scan < e then
      let (startOffset, scan) := parseVarint t scan
      if startOffset > index then none
      else
        let (size, scan) := parseVarint t scan
        if startOffset + size > index then
          let (handler, scan) := parseVarint t scan
          let (depthAndLasti, _) := parseVarint t scan
          some (handler, depthAndLasti >>> 1, depthAndLasti &&& 1 != 0)
        else scanTable t e index n (skipToNext t e t.size scan)
    else none

/-- The binary search of `get_exception_handler`, `Python/ceval.h:457-505`. -/
def bisectTable (t : Array Nat) (index : Nat) : Nat → Nat → Nat → Nat × Nat
  | 0, s, e => (s, e)
  | n + 1, s, e =>
    let mid := scanBack t t.size (s + (e - s) / 2)
    let (offset, _) := parseVarint t mid
    let (s, e) := if offset > index then (s, mid) else (mid, e)
    if e - s > maxLinearSearch then bisectTable t index n s e else (s, e)

/-- `get_exception_handler`, `Python/ceval.h:457-505`. -/
def getExceptionHandler (t : Array Nat) (index : Nat) : Option (Nat × Nat × Bool) :=
  let s := 0
  let e := t.size
  if e - s > maxLinearSearch then
    let (offset, _) := parseVarint t s
    if offset > index then none
    else
      let (s, e) := bisectTable t index t.size s e
      scanTable t e index t.size s
  else scanTable t e index t.size s

/-! ## Function objects -/

def getFunc : Val → RM FuncObj
  | .ref a => do
    match ← getObj a with
    | .func f => pure f
    | _ => fault "expected a function"
  | _ => fault "expected a function"

def isFunction : Val → RM Bool
  | .ref a => do
    match ← getObj a with
    | .func _ => pure true
    | _ => pure false
  | _ => pure false

def getCodeR (P : Program) (i : Nat) : RM Code := fun rt =>
  match P[i]? with
  | some c => .ok c rt
  | none => .error (.fault "no code object") rt

def coOptimized : Nat := 0x1
def coVarargs : Nat := 0x4
def coVarkeywords : Nat := 0x8
def coGenerator : Nat := 0x20
def coCoroutine : Nat := 0x80
def coIterableCoroutine : Nat := 0x100
def coAsyncGenerator : Nat := 0x200

def flagSet (flags bit : Nat) : Bool := flags &&& bit != 0

/-- `_PyFrame_Initialize` (`Include/internal/pycore_frame.h`). -/
def frameInitialize (c : Code) (codeIdx : Nat) (func : FuncObj) (funcv locals : Val) : Frame :=
  { code := codeIdx, funcobj := funcv, globals := func.globals, builtins := func.builtins,
    locals := locals, instrPtr := 0, returnOffset := 0,
    fast := Array.replicate c.nlocalsplus .null, stack := [], owner := .thread }

/-- `repr(s)` for a keyword name in `format_missing`. -/
def reprName (s : String) : String := "'" ++ s ++ "'"

def joinStrs (sep : String) : List String → String
  | [] => ""
  | [a] => a
  | a :: r => a ++ sep ++ joinStrs sep r

/-- `format_missing`, lines 1513-1574. -/
def formatMissing {α : Type} (kind : String) (names : List String) (qualname : String) : RM α :=
  let len := names.length
  let nameStr :=
    match len with
    | 1 => names.getD 0 ""
    | 2 => s!"{names.getD 0 ""} and {names.getD 1 ""}"
    | _ =>
      let tail := s!", {names.getD (len - 2) ""}, and {names.getD (len - 1) ""}"
      joinStrs ", " (names.take (len - 2)) ++ tail
  typeError s!"{qualname}() missing {len} required {kind} argument{if len == 1 then "" else "s"}: {nameStr}"

/-- `missing_arguments`, lines 1576-1613. `defcount = none` is C's `-1`. -/
def missingArguments {α : Type} (co : Code) (defcount : Option Nat) (fast : Array Val)
    (qualname : String) : RM α :=
  let (kind, start, stop) :=
    match defcount with
    | some d => ("positional", 0, co.argcount - d)
    | none => ("keyword-only", co.argcount, co.argcount + co.kwonlyargcount)
  let names := ((List.range' start (stop - start)).filter fun i => fast.getD i .null == .null).map
    fun i => reprName (co.localsplusnames.getD i "")
  formatMissing kind names qualname

/-- `too_many_positional`, lines 1615-1671. -/
def tooManyPositional {α : Type} (co : Code) (gvn : Nat) (defaults : Val) (fast : Array Val)
    (qualname : String) : RM α := do
  let kwonlyGiven := ((List.range' co.argcount co.kwonlyargcount).filter
    fun i => fast.getD i .null != .null).length
  let defcount := (← tupleItems defaults).size
  let (plural, sig) :=
    if defcount != 0 then (true, s!"from {co.argcount - defcount} to {co.argcount}")
    else (co.argcount != 1, s!"{co.argcount}")
  let kwonlySig :=
    if kwonlyGiven != 0 then
      s!" positional argument{if gvn != 1 then "s" else ""} (and {kwonlyGiven} keyword-only argument{if kwonlyGiven != 1 then "s" else ""})"
    else ""
  typeError s!"{qualname}() takes {sig} positional argument{if plural then "s" else ""} but {gvn}{kwonlySig} {if gvn == 1 && kwonlyGiven == 0 then "was" else "were"} given"

/-- `positional_only_passed_as_keyword`, lines 1673-1735: raises when any
positional-only name appears among the keywords. -/
def posonlyPassedAsKeyword (co : Code) (kwnames : List String) (qualname : String) : RM Unit := do
  let conflicts := (List.range co.posonlyargcount).flatMap fun k =>
    let n := co.localsplusnames.getD k ""
    kwnames.filter (· == n)
  if !conflicts.isEmpty then
    typeError s!"{qualname}() got some positional-only arguments passed as keyword arguments: '{joinStrs ", " conflicts}'"

/-- Index of `name` among the parameters that may be passed by keyword,
lines 1762-1782. -/
def kwSlot (co : Code) (name : String) : Option Nat :=
  let total := co.argcount + co.kwonlyargcount
  (List.range' co.posonlyargcount (total - co.posonlyargcount)).find?
    fun j => co.localsplusnames.getD j "" == name

/-- The keyword loop of `initialize_locals`, lines 1804-1903. -/
def bindKeywords (co : Code) (func : FuncObj) (kwdict : Val) :
    List (String × Val) → Array Val → RM (Array Val)
  | [], fast => pure fast
  | (keyword, value) :: rest, fast => do
    match kwSlot co keyword with
    | some j =>
      if fast.getD j .null != .null then
        typeError s!"{func.qualname}() got multiple values for argument '{keyword}'"
      bindKeywords co func kwdict rest (fast.setIfInBounds j value)
    | none =>
      if kwdict == .null then
        -- `positional_only_passed_as_keyword` needs all the names; the caller checks first.
        typeError s!"{func.qualname}() got an unexpected keyword argument '{keyword}'"
      dictSetStr kwdict keyword value
      bindKeywords co func kwdict rest fast

/-- `initialize_locals`, lines 1737-1984. `args` are the positional arguments,
`kwargs` the keyword arguments in `kwnames` order. -/
def initializeLocals (co : Code) (func : FuncObj) (fast0 : Array Val)
    (args : List Val) (kwargs : List (String × Val)) : RM (Array Val) := do
  let totalArgs := co.argcount + co.kwonlyargcount
  let argcount := args.length
  let hasVarargs := flagSet co.flags coVarargs
  let hasVarkw := flagSet co.flags coVarkeywords
  -- lines 1747-1758
  let (kwdict, fast) ← if hasVarkw then do
      let kd ← mkDict
      let i := if hasVarargs then totalArgs + 1 else totalArgs
      pure (kd, fast0.setIfInBounds i kd)
    else pure (Val.null, fast0)
  -- lines 1764-1774
  let n := if argcount > co.argcount then co.argcount else argcount
  let fast := (List.range n).foldl (fun f j => f.setIfInBounds j (args.getD j .null)) fast
  -- lines 1777-1795
  let fast ← if hasVarargs then do
      let u ← mkTuple (args.drop n)
      pure (fast.setIfInBounds totalArgs u)
    else pure fast
  -- lines 1804-1903, with the posonly check of 1844-1850 done when the first
  -- unknown keyword is met
  let needsPosonly := kwdict == .null && co.posonlyargcount != 0 &&
    kwargs.any fun kv => (kwSlot co kv.1).isNone
  let fast ← if needsPosonly then do
      let upto := kwargs.takeWhile fun kv => (kwSlot co kv.1).isSome
      let fast ← bindKeywords co func kwdict upto fast
      posonlyPassedAsKeyword co (kwargs.map (·.1)) func.qualname
      bindKeywords co func kwdict (kwargs.drop upto.length) fast
    else bindKeywords co func kwdict kwargs fast
  -- lines 1906-1910
  if argcount > co.argcount && !hasVarargs then
    tooManyPositional co argcount func.defaults fast func.qualname
  -- lines 1913-1940
  let fast ← if argcount < co.argcount then do
      let defs ← tupleItems func.defaults
      let defcount := defs.size
      let m := co.argcount - defcount
      let missing := ((List.range' argcount (m - argcount)).filter
        fun i => fast.getD i .null == .null).length
      if missing != 0 then
        missingArguments co (some defcount) fast func.qualname
      let i0 := if n > m then n - m else 0
      pure <| (List.range' i0 (defcount - i0)).foldl
        (fun f i => if f.getD (m + i) .null == .null
          then f.setIfInBounds (m + i) (defs.getD i .null) else f) fast
    else pure fast
  -- lines 1943-1966
  if co.kwonlyargcount > 0 then
    let mut fast := fast
    let mut missing := 0
    for i in List.range' co.argcount (totalArgs - co.argcount) do
      if fast.getD i .null != .null then continue
      let varname := co.localsplusnames.getD i ""
      if func.kwdefaults != .null then
        match ← dictGetStr func.kwdefaults varname with
        | some def_ =>
          fast := fast.setIfInBounds i def_
          continue
        | none => pure ()
      missing := missing + 1
    if missing != 0 then
      missingArguments co none fast func.qualname
    pure fast
  else pure fast

/-- `_PyEvalFramePushAndInit`, lines 2033-2068. `args` holds the positional
arguments followed by the values of `kwnames`. -/
def framePushAndInit (P : Program) (funcv locals : Val) (args : List Val)
    (kwnames : List String) : RM Frame := do
  let func ← getFunc funcv
  let co ← getCodeR P func.code
  let f := frameInitialize co func.code func funcv locals
  let npos := args.length - kwnames.length
  let fast ← initializeLocals co func f.fast (args.take npos) (kwnames.zip (args.drop npos))
  pure { f with fast := fast }

/-- `PyFunction_New`-time `locals`: `code_flags & CO_OPTIMIZED ? NULL : globals`
(`Python/bytecodes.c:4402`). -/
def localsFor (co : Code) (func : FuncObj) : Val :=
  if flagSet co.flags coOptimized then .null else func.globals

/-! ## Name errors -/

/-- `%.Ns` of `PyUnicode_FromFormat`, `unicode_fromformat_write_utf8`,
`Objects/unicodeobject.c:2623-2661`: it reads at most `n` bytes, stopping early at a NUL
(`:2634-2636`), and when it stops at the limit an incomplete UTF-8 sequence at the cut is dropped
(`pconsumed`, `:2637-2644`). On valid UTF-8 the result is the longest prefix of whole characters
before the first NUL whose encoding fits in `n` bytes. The same cut as `TypeObj.truncUtf8`. -/
def truncUtf8 : Nat → List Char → List Char
  | _, [] => []
  | n, c :: cs =>
    if c = '\x00' then [] else if c.utf8Size ≤ n then c :: truncUtf8 (n - c.utf8Size) cs else []

/-- `%.200s` of a C string: the UTF-8 of a `str` (`PyUnicode_AsUTF8`, for a name) or a type's
`tp_name`. A `String` holds no surrogate, so the UTF-8 is valid and nothing is replaced. -/
def trunc200 (s : String) : String := String.ofList (truncUtf8 200 s.toList)

/-- `_PyEval_FormatExcCheckArg`, `Python/ceval.c:3449-3475`: raise `cls` with the formatted
message, and when `cls` is `NameError` itself (`exc == PyExc_NameError`, so not its subclass
`UnboundLocalError`) set the new exception's `name` to `obj`, to offer suggestions later. The
`PyUnicode_AsUTF8` failure cannot happen to a `String`. -/
def formatExcCheckArg {α : Type} (cls msg obj : String) : RM α := do
  let v ← newExc (.cls cls) [.str msg]
  if cls == "NameError" then setExcData v { ← excData v with name := .str obj }
  raiseVal v

def nameErrorMsg (n : String) : String := s!"name '{trunc200 n}' is not defined"
def unboundLocalMsg (n : String) : String :=
  s!"cannot access local variable '{n}' where it is not associated with a value"
def unboundFreeMsg (n : String) : String :=
  s!"cannot access free variable '{n}' where it is not associated with a value in enclosing scope"

/-- `PyUnstable_Code_GetFirstFree`. -/
def firstFree (c : Code) : Nat := c.nlocalsplus - c.nfreevars

/-- `_PyEval_FormatExcUnbound`, lines 3477-3492. -/
def formatExcUnbound {α : Type} (co : Code) (oparg : Nat) : RM α :=
  let name := co.localsplusnames.getD oparg ""
  if oparg < firstFree co then formatExcCheckArg "UnboundLocalError" (unboundLocalMsg name) name
  else formatExcCheckArg "NameError" (unboundFreeMsg name) name

/-! ## `except` type checks -/

def catchMsg : String :=
  "catching classes that do not inherit from BaseException is not allowed"

/-- `_PyEval_CheckExceptTypeValid`, lines 3340-3363. -/
def checkExceptTypeValid (right : Val) : RM Unit := do
  let items? ← match right with
    | .ref a =>
      match ← getObj a with
      | .tuple items => pure (some items)
      | _ => pure none
    | _ => pure none
  match items? with
  | some items =>
    for e in items.toList do
      if !(← isExcClass e) then typeError catchMsg
  | none =>
    if !(← isExcClass right) then typeError catchMsg

/-- `_PyEval_CheckExceptStarTypeValid`, lines 3365-3400. -/
def checkExceptStarTypeValid (right : Val) : RM Unit := do
  checkExceptTypeValid right
  let items? ← match right with
    | .ref a =>
      match ← getObj a with
      | .tuple items => pure (some items)
      | _ => pure none
    | _ => pure none
  let isSub ← match items? with
    | some items => items.toList.anyM fun e => isSubtype e (.cls "BaseExceptionGroup")
    | none => isSubtype right (.cls "BaseExceptionGroup")
  if isSub then
    typeError "catching ExceptionGroup with except* is not allowed. Use except instead."

/-! ## `raise` -/

section
variable (om : ObjModel) (ctx : Ctx)

/-- `_PyObject_CallNoArgs` on an exception class, with the checks of `do_raise`. -/
def callExcClass (e : Val) : RM Val := do
  let value ← om.call ctx e [] []
  if !(← isExcInstance value) then
    let tn ← typeOf value
    let r1 ← om.repr ctx e
    let r2 ← om.repr ctx tn
    match r1, r2 with
    | .str a, .str b =>
      typeError s!"calling {a} should have returned an instance of BaseException, not {b}"
    | _, _ => fault "repr returned non-str"
  pure value

/-- `do_raise`, `Python/ceval.h:516-614`. `true` is "re-raise": the C function returns 1
and the caller goes to `exception_unwind` directly. The exception is carried by
the thrown `Err`. -/
def doRaise (exc cause : Val) : RM Unit := do
  if exc == .null then
    let ev ← topmostExc
    if ev == .none || ev == .null then
      runtimeError "No active exception to reraise"
    throw (.unwind ev)
  let value ← if ← isExcClass exc then callExcClass om ctx exc
    else if ← isExcInstance exc then pure exc
    else typeError "exceptions must derive from BaseException"
  if cause != .null then
    let fixed ← if ← isExcClass cause then callExcClass om ctx cause
      else if ← isExcInstance cause then pure cause
      else if cause == .none then pure .null
      else typeError "exception causes must derive from BaseException"
    setCause value fixed
  raiseVal value

/-- `PyIter_Next`: `StopIteration` is swallowed. -/
def iterNextOpt (it : Val) : RM (Option Val) :=
  tryExc (om.iterNext ctx it) fun e => do
    if ← givenMatches e 8 (.cls "StopIteration") then pure none else throw (.exc e)

/-- `PySequence_List(it)`, draining. `fuel` is the iteration bound. -/
def drain (it : Val) : Nat → List Val → RM (List Val)
  | 0, _ => throw .fuel
  | n + 1, acc => do
    match ← iterNextOpt om ctx it with
    | some v => drain it n (v :: acc)
    | none => pure acc.reverse

/-- `_PyEval_UnpackIterableStackRef`, lines 2357-2459. The result is in the order
of `*--sp`: first the value that ends up deepest. `argcntafter = none` is `-1`. -/
def unpackIterable (v : Val) (argcnt : Nat) (argcntafter : Option Nat) : RM (List Val) := do
  let it ← tryExc (om.getIter ctx v) fun e => do
    if (← givenMatches e 8 (.cls "TypeError")) && !(← om.isIterable v) then
      typeError s!"cannot unpack non-iterable {trunc200 (← tpName v)} object"
    else throw (.exc e)
  let rec first : Nat → Nat → List Val → RM (List Val)
    | 0, _, acc => pure acc.reverse
    | n + 1, i, acc => do
      match ← iterNextOpt om ctx it with
      | some w => first n (i + 1) (w :: acc)
      | none =>
        match argcntafter with
        | none => valueError s!"not enough values to unpack (expected {argcnt}, got {i})"
        | some after =>
          valueError s!"not enough values to unpack (expected at least {argcnt + after}, got {i})"
  let head ← first argcnt 0 []
  match argcntafter with
  | none =>
    match ← iterNextOpt om ctx it with
    | none => pure head
    | some _ =>
      let ll? ← match v with
        | .ref a =>
          match ← getObj a with
          | .list items | .tuple items => pure (some items.size)
          | .dict d => pure (some d.entries.size)
          | _ => pure none
        | _ => pure none
      match ll? with
      | some ll =>
        if ll > argcnt then
          valueError s!"too many values to unpack (expected {argcnt}, got {ll})"
        else valueError s!"too many values to unpack (expected {argcnt})"
      | none => valueError s!"too many values to unpack (expected {argcnt})"
  | some after =>
    let l ← drain om ctx it 1000000 []
    let ll := l.length
    if ll < after then
      valueError s!"not enough values to unpack (expected at least {argcnt + after}, got {argcnt + ll})"
    let lv ← mkList (l.take (ll - after))
    pure (head ++ [lv] ++ l.drop (ll - after))

/-- `PyObject_RichCompareBool(a, b, Py_EQ)`: identity implies equality. -/
def eqBool (a b : Val) : RM Bool := do
  if a == b then pure true
  else om.isTrue ctx (← om.richCompare ctx a b 2)

/-- `dict_unhashable_type`, `Objects/dictobject.c:2441`, and its twin
`set_unhashable_type`, `Objects/setobject.c:346`: an exact `TypeError` from
`hash()` is re-raised with the container in the message. -/
def hashFor (what : String) (key : Val) : RM Int :=
  tryExc (om.hash ctx key) fun e => do
    if (← typeOf e) == .cls "TypeError" then
      match ← om.str ctx e with
      | .str m => typeError s!"cannot use '{← tpName key}' as a {what} ({m})"
      | _ => throw (.exc e)
    else throw (.exc e)

/-- `PyDict_GetItemRef`: `none` is "absent". -/
def dictGet (dv key : Val) : RM (Option Val) := do
  let h ← hashFor om ctx "dict key" key
  let d ← getDict dv
  match ← dictFind (eqBool om ctx key) d h with
  | some i => pure (d.entries[i]?.map (·.value))
  | none => pure none

/-- `PyDict_SetItem`. -/
def dictSet (dv key v : Val) : RM Unit := do
  let h ← hashFor om ctx "dict key" key
  let d ← getDict dv
  let idx ← dictFind (eqBool om ctx key) d h
  dictInsertAt dv d idx h key v

/-- `PyDict_Contains`. -/
def dictContains (dv key : Val) : RM Bool := do
  return (← dictGet om ctx dv key).isSome

/-- `_PySet_AddTakeRef` on a set address. -/
def setAdd (sv key : Val) : RM Unit := do
  let h ← hashFor om ctx "set element" key
  match sv with
  | .ref a =>
    match ← getObj a with
    | .set fr items =>
      let found ← items.toList.anyM fun kv =>
        if kv.1 == h then eqBool om ctx key kv.2 else pure false
      if !found then
        match ← getObj a with
        | .set fr' items' => setObj a (.set fr' (items'.push (h, key)))
        | _ => setObj a (.set fr items)
    | _ => fault "expected a set"
  | _ => fault "expected a set"

/-- `frozenset_hash_impl` over the stored hashes. -/
def frozensetHash (items : Array (Int × Val)) : Int :=
  items.toList.foldl (fun h kv => (h + kv.1) % 2305843009213693951) 7

/-- `_PySet_Contains`, `Objects/setobject.c:2544-2564`: an unhashable `set` key is looked up
as if it were a `frozenset`. -/
def setContains (sv key : Val) : RM Bool := do
  let h ← tryExc (hashFor om ctx "set element" key) fun e => do
    match key with
    | .ref a =>
      match ← getObj a with
      | .set _ items =>
        if ← givenMatches e 8 (.cls "TypeError") then pure (frozensetHash items)
        else throw (.exc e)
      | _ => throw (.exc e)
    | _ => throw (.exc e)
  match sv with
  | .ref a =>
    match ← getObj a with
    | .set _ items =>
      items.toList.anyM fun kv => if kv.1 == h then eqBool om ctx key kv.2 else pure false
    | _ => fault "expected a set"
  | _ => fault "expected a set"

/-- `PyMapping_GetOptionalItem(o, key)`: `KeyError` means absent. -/
def getOptionalItem (o k : Val) : RM (Option Val) :=
  tryExc (some <$> om.getItem ctx o k) fun e => do
    if ← givenMatches e 8 (.cls "KeyError") then pure none else throw (.exc e)

/-- `_PyEval_ExceptionGroupMatch`, lines 2263-2348: `(match, rest)`. -/
def exceptionGroupMatch (excValue matchType : Val) : RM (Val × Val) := do
  if excValue == .none then return (.none, .none)
  if ← givenMatches excValue 8 matchType then
    let isEg ← isSubtype (← typeOf excValue) (.cls "BaseExceptionGroup")
    if isEg then return (excValue, .none)
    let wrapped ← om.egWrap ctx excValue
    return (wrapped, .none)
  if ← isSubtype (← typeOf excValue) (.cls "BaseExceptionGroup") then
    om.egSplit ctx excValue matchType
  else return (.none, excValue)

end

end PyLean.Bytecode
