import PyLean.Bytecode.ObjModel
import PyLean.TypeObj.ExcCore

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

/-- `format_missing`, lines 1514-1574. -/
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

/-- `missing_arguments`, lines 1577-1613. `defcount = none` is C's `-1`. `end = co_argcount -
defcount` cannot be negative here: the caller has a missing name below it. -/
def missingArguments {α : Type} (co : Code) (defcount : Option Nat) (fast : Array Val)
    (qualname : String) : RM α :=
  let (kind, start, stop) :=
    match defcount with
    | some d => ("positional", 0, co.argcount - d)
    | none => ("keyword-only", co.argcount, co.argcount + co.kwonlyargcount)
  let names := ((List.range' start (stop - start)).filter fun i => fast.getD i .null == .null).map
    fun i => reprName (co.localsplusnames.getD i "")
  formatMissing kind names qualname

/-- `too_many_positional`, lines 1616-1671. -/
def tooManyPositional {α : Type} (co : Code) (gvn : Nat) (defaults : Val) (fast : Array Val)
    (qualname : String) : RM α := do
  let kwonlyGiven := ((List.range' co.argcount co.kwonlyargcount).filter
    fun i => fast.getD i .null != .null).length
  let defcount := (← tupleItems defaults).size
  -- `atleast = co_argcount - defcount` is a `Py_ssize_t`: negative when `__defaults__` was replaced
  -- by a longer tuple
  let (plural, sig) :=
    if defcount != 0 then (true, s!"from {(co.argcount : Int) - defcount} to {co.argcount}")
    else (co.argcount != 1, s!"{co.argcount}")
  let kwonlySig :=
    if kwonlyGiven != 0 then
      s!" positional argument{if gvn != 1 then "s" else ""} (and {kwonlyGiven} keyword-only argument{if kwonlyGiven != 1 then "s" else ""})"
    else ""
  typeError s!"{qualname}() takes {sig} positional argument{if plural then "s" else ""} but {gvn}{kwonlySig} {if gvn == 1 && kwonlyGiven == 0 then "was" else "were"} given"

/-- What the keyword binding of `initialize_locals` asks of the object model when a keyword is
not an exact `str`, which only a `**` mapping can pass (`_PyStack_UnpackDict` keeps every key
whose type has `Py_TPFLAGS_UNICODE_SUBCLASS`): Python code may run in each. -/
structure KwHooks where
  /-- `PyObject_RichCompareBool(a, b, Py_EQ)` (`Objects/object.c`). -/
  eq : Val → Val → RM Bool
  /-- The text of `PyObject_Str(o)`, for `'%S'`. -/
  str : Val → RM String
  /-- `PyDict_SetItem(d, k, v)` on the fresh `**kwargs` dict. -/
  setItem : Val → Val → Val → RM Unit

/-- `PyUnicode_Check(keyword)` and its `str` data: an exact `str`, or an instance of a `str`
subclass, whose `str` payload is `base`. The same test as `kwKeyName` in `Uops3.lean`. -/
def kwText (rt : Rt) : Val → Option String
  | .str s => some s
  | .ref a =>
    match rt.heap[a]? with
    | some (.inst i) =>
      match i.base with
      | .str s => some s
      | _ => none
    | _ => none
  | _ => none

/-- The hooks of the machine's object model: `PyObject_RichCompareBool` is identity, else
`PyObject_RichCompare` then `PyObject_IsTrue` (a `bool` result read as it is). -/
def kwHooksOf (om : ObjModel) (ctx : Ctx) : KwHooks where
  eq a b := do
    if a == b then pure true else om.isTrue ctx (← om.richCompare ctx a b 2)
  str o := do
    let v ← om.str ctx o
    match kwText (← get) v with
    | some t => pure t
    | none => fault "str() did not return a str"
  setItem d k v := om.setItem ctx d k v

/-- Hooks for a `kwnames` of exact `str` only, which never call them (`findKwSlot`, `fmtKw`,
`posonlyHits` and the `**kwargs` store test for an exact `str` first). -/
def strKwHooks : KwHooks where
  eq _ _ := fault "keyword comparison on an exact str"
  str _ := fault "keyword str() on an exact str"
  setItem _ _ _ := fault "keyword store on an exact str"

/-- `positional_only_passed_as_keyword`, lines 1674-1735, for one positional-only name `n`: every
keyword equal to it, in keyword order. An exact `str` keyword is compared by text (the pointer
test of line 1688 for an interned name, else `PyObject_RichCompareBool` of two exact `str`); any
other keyword object goes through `PyObject_RichCompareBool(posonly_name, kwname, Py_EQ)`
(line 1697), which for a `str` subclass overriding `__eq__` runs its reflected `__eq__` first, and
whose error (`cmp < 0`, `goto fail`, lines 1704-1706) is the result. -/
def posonlyHits (hk : KwHooks) (n : String) : List Val → RM (List Val)
  | [] => pure []
  | kw :: rest => do
    let hit ← match kw with
      | .str s => pure (s == n)
      | _ => hk.eq (.str n) kw
    let tl ← posonlyHits hk n rest
    pure (if hit then kw :: tl else tl)

/-- The outer loop of `positional_only_passed_as_keyword` (line 1684), positional-only name by
name. -/
def posonlyConflicts (hk : KwHooks) (kwnames : List Val) : List String → RM (List Val)
  | [] => pure []
  | n :: ns => do
    let a ← posonlyHits hk n kwnames
    let b ← posonlyConflicts hk kwnames ns
    pure (a ++ b)

/-- `positional_only_passed_as_keyword`, lines 1674-1735: the conflicting keyword objects joined
with `", "` (`PyUnicode_Join`, which reads each one's `str` data) into the `TypeError`. -/
def posonlyPassedAsKeyword (hk : KwHooks) (co : Code) (kwnames : List Val) (qualname : String) :
    RM Unit := do
  let conflicts ← posonlyConflicts hk kwnames
    ((List.range co.posonlyargcount).map fun k => co.localsplusnames.getD k "")
  if !conflicts.isEmpty then
    let rt ← get
    typeError s!"{qualname}() got some positional-only arguments passed as keyword arguments: '{joinStrs ", " (conflicts.map fun c => (kwText rt c).getD "")}'"

/-- Index of `name` among the parameters that may be passed by keyword, the first of
`co_varnames[co_posonlyargcount:total_args]` with that text: for an exact `str` keyword the pointer
loop (lines 1815-1822) and the `PyObject_RichCompareBool` loop (lines 1825-1835) find the same
one, the names being interned. -/
def kwSlot (co : Code) (name : String) : Option Nat :=
  let total := co.argcount + co.kwonlyargcount
  (List.range' co.posonlyargcount (total - co.posonlyargcount)).find?
    fun j => co.localsplusnames.getD j "" == name

/-- The slow loop, lines 1825-1835, for a keyword object that is not an exact `str` (so no
pointer in the first loop is it): `PyObject_RichCompareBool(keyword, varname, Py_EQ)` in order
(line 1832), the first true one is the slot (`kw_found`), and an error is `kw_fail`
(lines 1836-1838). -/
def kwSlotSlow (hk : KwHooks) (co : Code) (keyword : Val) : List Nat → RM (Option Nat)
  | [] => pure none
  | j :: js => do
    if ← hk.eq keyword (.str (co.localsplusnames.getD j "")) then pure (some j)
    else kwSlotSlow hk co keyword js

/-- Lines 1815-1835: the slot a keyword names, if any. -/
def findKwSlot (hk : KwHooks) (co : Code) (keyword : Val) : RM (Option Nat) :=
  match keyword with
  | .str s => pure (kwSlot co s)
  | _ => kwSlotSlow hk co keyword
      (List.range' co.posonlyargcount (co.argcount + co.kwonlyargcount - co.posonlyargcount))

/-- `'%S'` of a keyword (`PyObject_Str`): the text of an exact `str`, else the hook. -/
def fmtKw (hk : KwHooks) : Val → RM String
  | .str s => pure s
  | k => hk.str k

/-- `possible_keywords` (lines 1853-1861): the names that may be passed by keyword. -/
def possibleKeywords (co : Code) : List String :=
  let total := co.argcount + co.kwonlyargcount
  (List.range' co.posonlyargcount (total - co.posonlyargcount)).map fun j => co.localsplusnames.getD j ""

/-- The unexpected keyword `TypeError` of lines 1851-1876: `_Py_CalculateSuggestions` over
`possible_keywords` when `total_args > co_posonlyargcount` (the same `Python/suggestions.c`
model as `TypeObj.calcSuggestion`), on the keyword's `str` data, then
`"%U() got an unexpected keyword argument '%S'"` with `". Did you mean '%S'?"` when it found one.
`PyUnicode_AsUTF8AndSize` cannot fail on a `String` (no surrogates), and the `PyList_New` failure
is not modelled. -/
def kwSuggestion (co : Code) (keyword : String) : Option String :=
  if co.argcount + co.kwonlyargcount > co.posonlyargcount then
    PyLean.TypeObj.calcSuggestion (possibleKeywords co) keyword
  else none

def unexpectedKeyword {α : Type} (hk : KwHooks) (co : Code) (qualname : String) (keyword : Val) :
    RM α := do
  let txt := (kwText (← get) keyword).getD ""
  let shown ← fmtKw hk keyword
  match kwSuggestion co txt with
  | some sug => typeError s!"{qualname}() got an unexpected keyword argument '{shown}'. Did you mean '{sug}'?"
  | none => typeError s!"{qualname}() got an unexpected keyword argument '{shown}'"

/-- The keyword loop of `initialize_locals`, lines 1803-1903, over the keywords in `kwnames`
order; `kwnames` is all of them, for `positional_only_passed_as_keyword`. A keyword that is not a
`str` is the "keywords must be strings" `TypeError` (lines 1810-1815). One that names a parameter
fills its local, or raises "got multiple values" if it is set (`kw_found`, lines 1894-1901); one
that names none goes into `**kwargs` (`PyDict_SetItem` with the keyword object, line 1882), or,
with no `**kwargs`, raises the positional-only error when there are positional-only parameters
and a keyword names one, else the unexpected keyword error. An error in a comparison is the
result (`kw_fail`). -/
def bindKeywords (hk : KwHooks) (co : Code) (func : FuncObj) (kwdict : Val) (kwnames : List Val) :
    List (Val × Val) → Array Val → RM (Array Val)
  | [], fast => pure fast
  | (keyword, value) :: rest, fast => do
    if (kwText (← get) keyword).isNone then
      typeError s!"{func.qualname}() keywords must be strings"
    match ← findKwSlot hk co keyword with
    | some j =>
      if fast.getD j .null != .null then
        typeError s!"{func.qualname}() got multiple values for argument '{← fmtKw hk keyword}'"
      bindKeywords hk co func kwdict kwnames rest (fast.setIfInBounds j value)
    | none =>
      if kwdict == .null then
        if co.posonlyargcount != 0 then
          posonlyPassedAsKeyword hk co kwnames func.qualname
        unexpectedKeyword hk co func.qualname keyword
      match keyword with
      | .str s => dictSetStr kwdict s value
      | k => hk.setItem kwdict k value
      bindKeywords hk co func kwdict kwnames rest fast

/-- `initialize_locals`, lines 1738-1984. `args` are the positional arguments,
`kwargs` the keyword objects and values in `kwnames` order. -/
def initializeLocals (hk : KwHooks) (co : Code) (func : FuncObj) (fast0 : Array Val)
    (args : List Val) (kwargs : List (Val × Val)) : RM (Array Val) := do
  let totalArgs := co.argcount + co.kwonlyargcount
  let argcount := args.length
  let hasVarargs := flagSet co.flags coVarargs
  let hasVarkw := flagSet co.flags coVarkeywords
  -- lines 1747-1760
  let (kwdict, fast) ← if hasVarkw then do
      let kd ← mkDict
      let i := if hasVarargs then totalArgs + 1 else totalArgs
      pure (kd, fast0.setIfInBounds i kd)
    else pure (Val.null, fast0)
  -- lines 1763-1773
  let n := if argcount > co.argcount then co.argcount else argcount
  let fast := (List.range n).foldl (fun f j => f.setIfInBounds j (args.getD j .null)) fast
  -- lines 1775-1800
  let fast ← if hasVarargs then do
      let u ← mkTuple (args.drop n)
      pure (fast.setIfInBounds totalArgs u)
    else pure fast
  -- lines 1802-1903
  let fast ← bindKeywords hk co func kwdict (kwargs.map (·.1)) kwargs fast
  -- lines 1905-1910
  if argcount > co.argcount && !hasVarargs then
    tooManyPositional co argcount func.defaults fast func.qualname
  -- lines 1912-1940. `m = co_argcount - defcount` is a `Py_ssize_t`, negative when
  -- `__defaults__` was replaced by a tuple longer than the parameters; then no positional
  -- is missing, `i = n - m` skips the first defaults, and the last `co_argcount - n` fill the
  -- unfilled slots from `n` on.
  let fast ← if argcount < co.argcount then do
      let defs ← tupleItems func.defaults
      let defcount := defs.size
      let m : Int := (co.argcount : Int) - defcount
      let missing := ((List.range' argcount (m.toNat - argcount)).filter
        fun i => fast.getD i .null == .null).length
      if missing != 0 then
        missingArguments co (some defcount) fast func.qualname
      let i0 : Nat := if (n : Int) > m then ((n : Int) - m).toNat else 0
      pure <| (List.range' i0 (defcount - i0)).foldl
        (fun f i => if f.getD (m + i).toNat .null == .null
          then f.setIfInBounds (m + i).toNat (defs.getD i .null) else f) fast
    else pure fast
  -- lines 1942-1966
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
def framePushAndInit (P : Program) (hk : KwHooks) (funcv locals : Val) (args : List Val)
    (kwnames : List Val) : RM Frame := do
  let func ← getFunc funcv
  let co ← getCodeR P func.code
  let f := frameInitialize co func.code func funcv locals
  let npos := args.length - kwnames.length
  let fast ← initializeLocals hk co func f.fast (args.take npos) (kwnames.zip (args.drop npos))
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

/-- `%.100s`, as `trunc200`. -/
def trunc100 (s : String) : String := String.ofList (truncUtf8 100 s.toList)

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

/-- `_PyEval_CheckExceptTypeValid`, `Python/ceval.c:3340-3363`: `PyTuple_Check`, so a `tuple` subclass
instance is checked item by item. -/
def checkExceptTypeValid (right : Val) : RM Unit := do
  match ← tupleCheckItems? right with
  | some items =>
    for e in items.toList do
      if !(← isExcClass e) then typeError catchMsg
  | none =>
    if !(← isExcClass right) then typeError catchMsg

/-- `_PyEval_CheckExceptStarTypeValid`, lines 3365-3400. -/
def checkExceptStarTypeValid (right : Val) : RM Unit := do
  checkExceptTypeValid right
  let isSub ← match ← tupleCheckItems? right with
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
    -- `&&` short-circuits in C: the slots are read only after a `TypeError`
    if ← givenMatches e 8 (.cls "TypeError") then
      if !(← om.isIterable v) then
        typeError s!"cannot unpack non-iterable {trunc200 (← tpName v)} object"
      else throw (.exc e)
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
    -- `PySequence_List(it)`, `Objects/abstract.c:2081-2101`: `PyList_New(0)` then
    -- `_PyList_Extend(result, it)`, which is the object model's `listExtend`
    let lv ← mkList []
    om.listExtend ctx lv it
    let l ← match lv with
      | .ref a => do
        match ← getObj a with
        | .list items => pure items.toList
        | _ => fault "PySequence_List: not a list"
      | _ => fault "PySequence_List: not a list"
    let ll := l.length
    if ll < after then
      valueError s!"not enough values to unpack (expected at least {argcnt + after}, got {argcnt + ll})"
    -- `Py_SET_SIZE(l, ll - argcntafter)` (`:2449`): the same list, cut
    match lv with
    | .ref a => setObj a (.list (l.take (ll - after)).toArray)
    | _ => pure ()
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

/-- The items of an exact tuple (`PyTuple_CheckExact`): a tuple subclass instance is not one. -/
def exactTupleItems? : Val → RM (Option (Array Val))
  | .ref a => do
    match ← getObj a with
    | .tuple items => pure (some items)
    | _ => pure none
  | _ => pure none

/-- `_PyEval_ExceptionGroupMatch`, `Python/ceval.c:2263-2348`: `(match, rest)`. `None` gives
`(None, None)` (`:2266-2270`); a full match by `PyErr_GivenExceptionMatches` gives the group
itself, or a naked exception wrapped by `_PyExc_CreateExceptionGroup` (`:2273-2305`, the wrapping
and traceback are the `egWrap` oracle); a group that does not match is split by calling its
`split` attribute with the match type (`PyObject_CallMethod`, `:2313-2317`, which can run any
Python code a subclass defines), whose result must be an exact tuple (`:2321-2327`) of at least two
items (`:2330-2337`), the first two of which are taken as they are (`:2339-2340`); anything else
gives `(None, exc_value)` (`:2344-2346`). -/
def exceptionGroupMatch (excValue matchType : Val) : RM (Val × Val) := do
  if excValue == .none then return (.none, .none)
  if ← givenMatches excValue 8 matchType then
    let isEg ← isSubtype (← typeOf excValue) (.cls "BaseExceptionGroup")
    if isEg then return (excValue, .none)
    let wrapped ← om.egWrap ctx excValue
    return (wrapped, .none)
  if ← isSubtype (← typeOf excValue) (.cls "BaseExceptionGroup") then
    let split ← om.getAttr ctx excValue "split"
    let pair ← om.call ctx split [matchType] []
    match ← exactTupleItems? pair with
    | none =>
      typeError s!"{trunc200 (← tpName excValue)}.split must return a tuple, not {trunc200 (← tpName pair)}"
    | some items =>
      match items.toList with
      | m :: r :: _ => return (m, r)
      | _ =>
        typeError s!"{trunc200 (← tpName excValue)}.split must return a 2-tuple, got tuple of size {items.size}"
  else return (.none, excValue)

end

end PyLean.Bytecode
