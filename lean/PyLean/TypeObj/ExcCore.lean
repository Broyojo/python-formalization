import PyLean.TypeObj.Attr

/-!
`BaseException` and what every other exception class in `Objects/exceptions.c` builds on.

This file comes before `Protocol`, so the abstract-object helpers the exception code calls
(`PySequence_Tuple`, `PyNumber_AsSsize_t`, ...) are stated here over `Rt`, with the same
branches as their twins in `Protocol.lean`.

## Representation

* `ExcData.members` holds the `PyObject *` members of the subclasses by Python attribute
  name. An absent name is a NULL field, which reads as `None` (`_Py_T_OBJECT`,
  `Python/structmember.c:99`).
* `start` and `end` of the Unicode errors are `Py_ssize_t` members, stored as `.int` under
  the same names; absent means the zero of `tp_alloc`.
* `ExcData.traceback` uses `Val.none` for the NULL field. A traceback object is a heap
  object of class `B.traceback`.
* `ExcData.notes` is the C field `PyBaseExceptionObject.notes`. `add_note` does not touch
  it: `__notes__` is an ordinary instance attribute.
-/

namespace PyLean.TypeObj

namespace B
def OSError : Addr := 57
def BlockingIOError : Addr := 58
def ChildProcessError : Addr := 59
def BrokenPipeError : Addr := 61
def ConnectionAbortedError : Addr := 62
def ConnectionRefusedError : Addr := 63
def ConnectionResetError : Addr := 64
def FileExistsError : Addr := 65
def FileNotFoundError : Addr := 66
def ImportError : Addr := 69
def InterruptedError : Addr := 70
def IsADirectoryError : Addr := 71
def NotADirectoryError : Addr := 74
def PermissionError : Addr := 75
def ProcessLookupError : Addr := 76
def SyntaxError : Addr := 80
def SystemExit : Addr := 82
def TimeoutError : Addr := 84
def UnicodeError : Addr := 85
def UnicodeDecodeError : Addr := 86
def UnicodeEncodeError : Addr := 87
def UnicodeTranslateError : Addr := 88
end B

/-! ## Reading an exception object -/

/-- The fields of an exception object; the empty fields for anything else. -/
def excDataOf (w : World) (v : Val) : ExcData :=
  match payloadOf w v with
  | some (.exc e) => e
  | _ => {}

/-- `self->args`. -/
def excArgs (w : World) (v : Val) : List Val := (excDataOf w v).args

/-- Update the fields of an exception object. -/
def excUpdate (v : Val) (f : ExcData → ExcData) : M Unit :=
  match v with
  | .obj a => modObj a fun o =>
    match o.body with
    | .exc d => { o with body := .exc (f d) }
    | _ => o
  | _ => pure ()

/-- A `PyObject *` member. -/
def memGet (d : ExcData) (n : Name) : Option Val := NameDict.get? d.members n

/-- `Py_XSETREF(self->n, v)`. -/
def memSet (n : Name) (v : Option Val) (d : ExcData) : ExcData :=
  { d with members :=
      match v with
      | some x => NameDict.set d.members n x
      | none => NameDict.erase d.members n }

/-- `PyExceptionInstance_Check`. -/
def excInstanceCheck (w : World) (v : Val) : Bool := isSubtype w (typeOf w v) B.BaseException

/-- `PyExceptionClass_Check`. -/
def excClassCheck (w : World) (v : Val) : Bool :=
  match asType w v with
  | some t => isSubtype w t B.BaseException
  | none => false

/-- `_PyBaseExceptionGroup_Check`. -/
def egCheck (w : World) (v : Val) : Bool := isSubtype w (typeOf w v) B.BaseExceptionGroup

/-- `PyTraceBack_Check`. -/
def tracebackCheck (w : World) (v : Val) : Bool := typeOf w v == B.traceback

/-- `_PyType_Name`, `Objects/typeobject.c:1543`: `tp_name` after the last dot. -/
def pyTypeName (w : World) (t : Addr) : String :=
  let n := tpName w t
  ((n.splitOn ".").getLast?).getD n

/-- `PyObject_Str`, which renders a NULL pointer as `<NULL>`, `Objects/object.c:801`. -/
def strOrNull (rt : Rt) : Option Val → M String
  | some v => rt.str v
  | none => pure "<NULL>"

/-! ## Abstract-object helpers over `Rt` -/

/-- The filled slot `s` of the type of `v`, honouring NULL `tp_as_*` structs. -/
def excSlotIn (w : World) (v : Val) (s : Slot) : Option SlotFn :=
  if hasGroup w (typeOf w v) s.group then slotOf w (typeOf w v) s else none

/-- `PySequence_Check`, `Objects/abstract.c:1681`. -/
def excSeqCheck (w : World) (s : Val) : Bool :=
  (dictOf w s).isNone && (excSlotIn w s .sq_item).isSome

/-- `PyCallable_Check`, `Objects/object.c:2179`. -/
def excCallableCheck (w : World) (v : Val) : Bool := (slotOf w (typeOf w v) .tp_call).isSome

/-- `PyNumber_Check`, `Objects/abstract.c:913`. -/
def excNumberCheck (w : World) (o : Val) : Bool :=
  (excSlotIn w o .nb_index).isSome || (excSlotIn w o .nb_int).isSome ||
    (excSlotIn w o .nb_float).isSome

/-- The iteration loop of `PySequence_Tuple` and `PySequence_List`. `fuel` is a model bound. -/
def excCollect (rt : Rt) (it : Val) : Nat → M (List Val)
  | 0 => raise .fuel
  | fuel + 1 => do
    match ← rt.iterNext it with
    | none => pure []
    | some x =>
      let rest ← excCollect rt it fuel
      pure (x :: rest)

/-- Loop bound for iteration. A model limit, not a Python one. -/
def excIterFuel : Nat := 100000

/-- `PySequence_Tuple`, `Objects/abstract.c:2005`, items only. -/
def excSeqTuple (rt : Rt) (v : Val) : M (List Val) := do
  match v with
  | .tuple xs => pure xs
  | _ =>
    let w ← getW
    match listOf w v, typeOf w v == B.list with
    | some xs, true => pure xs
    | _, _ =>
      let it ← rt.getIter v
      excCollect rt it excIterFuel

/-- `PyObject_Size` by way of the `len` builtin. -/
def excLen (rt : Rt) (o : Val) : M Int := do
  let f ← alloc B.builtinFn (.builtin .len none)
  let r ← rt.call f [o] []
  let w ← getW
  pure ((intOf w r).getD 0)

/-- `PyObject_LengthHint`, `Objects/abstract.c:95`. -/
def excLengthHint (rt : Rt) (o : Val) (dflt : Int) : M Int := do
  let w ← getW
  let hasLen := (excSlotIn w o .sq_length).isSome || (excSlotIn w o .mp_length).isSome
  let first : M (Option Int) :=
    if hasLen then catchMatch B.TypeError (some <$> excLen rt o) (pure none)
    else pure none
  match ← first with
  | some r => pure r
  | none =>
    match ← lookupSpecial rt o "__length_hint__" with
    | none => pure dflt
    | some hint =>
      let r? ← catchMatch B.TypeError (some <$> rt.call hint [] []) (pure none)
      match r? with
      | none => pure dflt
      | some .notImpl => pure dflt
      | some result =>
        let w ← getW
        match intOf w result with
        | none =>
          typeErr s!"{objFQN w o}.__length_hint__() must return an int, not {objFQN w result}"
        | some i =>
          if !inSsize i then overflowErr "Python int too large to convert to C ssize_t"
          else if i < 0 then valueErr s!"{objFQN w o}.__length_hint__() must return a non-negative int"
          else pure i

/-- `PySequence_List`, `Objects/abstract.c:2081`, items only. -/
def excSeqList (rt : Rt) (v : Val) : M (List Val) := do
  let w ← getW
  match v with
  | .tuple xs => pure xs
  | _ =>
    match listOf w v, typeOf w v == B.list with
    | some xs, true => pure xs
    | _, _ =>
      let it ← rt.getIter v
      let n ← excLengthHint rt v 8
      if n ≥ 2 ^ 48 then raiseC B.MemoryError ""
      excCollect rt it excIterFuel

/-- `_PyNumber_Index`, `Objects/abstract.c:1410`, as the value of the resulting `int`. -/
def excNumberIndex (rt : Rt) (item : Val) : M Int := do
  let w ← getW
  match intOf w item with
  | some i => pure i
  | none =>
    let bad := s!"'{trunc 200 (typeName w item)}' object cannot be interpreted as an integer"
    if !hasGroup w (typeOf w item) .number then typeErr bad
    match slotOf w (typeOf w item) .nb_index with
    | none => typeErr bad
    | some .generic =>
      let r ← vectorcallMethod rt "__index__" [item]
      let w ← getW
      match intOf w r with
      | some i => pure i
      | none => typeErr s!"{objFQN w item}.__index__() must return an int, not {objFQN w r}"
    | some _ => gap%

/-- `PyNumber_AsSsize_t(item, PyExc_ValueError)`, `Objects/abstract.c:1468`. -/
def excAsSsizeValueError (rt : Rt) (item : Val) : M Int := do
  let i ← excNumberIndex rt item
  if inSsize i then pure i
  else
    let w ← getW
    valueErr s!"cannot fit '{trunc 200 (typeName w item)}' into an index-sized integer"

/-- `PyLong_AsSsize_t` overflow, `Objects/longobject.c:708`. -/
def excAsSsizeLong (i : Int) : M Int :=
  if inSsize i then pure i
  else overflowErr "Python int too large to convert to C ssize_t"

/-- `PyObject_IsInstance(inst, PyExc_Exception)`. `PyExc_Exception` is an exact `type`, so
this is `object_isinstance`, `Objects/abstract.c:2603`, with a concrete class. -/
def excIsInstanceOf (rt : Rt) (inst : Val) (ca : Addr) : M Bool := do
  let w ← getW
  if isSubtype w (typeOf w inst) ca then pure true
  else
    match ← rt.getOptionalAttr inst "__class__" with
    | none => pure false
    | some icls =>
      let w ← getW
      match asType w icls with
      | some ia => if ia != typeOf w inst then pure (isSubtype w ia ca) else pure false
      | none => pure false

/-! ## Argument parsing: the cases of `Python/getargs.c` these constructors use -/

/-- `Py_TYPE(arg)->tp_name` in `converterr`, `Python/getargs.c:673`. -/
def excArgName (w : World) (v : Val) : String :=
  if v.is .none then "None" else trunc 50 (typeName w v)

/-- `%.Ns` of `PyUnicode_FromFormat`, `unicode_fromformat_write_utf8`,
`Objects/unicodeobject.c:2623-2660`: at most `n` bytes of the UTF-8 string, and an incomplete
sequence at the cut is dropped (`pconsumed`), so the result is the longest prefix of whole
characters whose encoding fits in `n` bytes. -/
def truncUtf8 : Nat → List Char → List Char
  | _, [] => []
  | n, c :: cs => if c.utf8Size ≤ n then c :: truncUtf8 (n - c.utf8Size) cs else []

/-- The message of `_PyArg_NoKeywords`, `Python/getargs.c:2956`. -/
def noKwMsg (name : String) : String :=
  s!"{String.ofList (truncUtf8 200 name.toList)}() takes no keyword arguments"

/-- `_PyArg_NoKeywords(name, kw)`, `Python/getargs.c:2942-2959`: `"%.200s() takes no keyword
arguments"`. -/
def argNoKeywords (name : String) (kw : Kw) : M Unit :=
  unless kw.isEmpty do typeErr (noKwMsg name)

/-- `_PyArg_NoKwnames(name, kwnames)`, `Python/getargs.c:2978-2993`: the same refusal, with `%s`,
so the name is not cut. -/
def argNoKwnames (name : String) (kw : Kw) : M Unit :=
  unless kw.isEmpty do typeErr s!"{name}() takes no keyword arguments"

/-- The arity error of `vgetargs1_impl`, `Python/getargs.c:256`. -/
def argCount (fname : Option String) (min max n : Nat) : M Unit := do
  if n < min || max < n then
    let f := match fname with
      | some s => s ++ "()"
      | none => "function"
    let how := if min == max then "exactly" else if n < min then "at least" else "at most"
    let m := if n < min then min else max
    typeErr s!"{f} takes {how} {m} argument{if m == 1 then "" else "s"} ({n} given)"

/-- `seterror` around a `must be X, not Y` conversion failure, `Python/getargs.c:440`. -/
def argPrefix (fname : Option String) (i : Nat) : String :=
  let p := match fname with
    | some s => s ++ "() "
    | none => ""
  s!"{p}argument {i}"

/-- Format `U`: `PyUnicode_Check`. -/
def argU (fname : Option String) (i : Nat) (v : Val) : M Unit := do
  let w ← getW
  if (strOf w v).isNone then
    typeErr s!"{argPrefix fname i} must be str, not {excArgName w v}"

/-- Format `n`: `_PyNumber_Index`, then `PyLong_AsSsize_t`, in `convertsimple`, `Python/getargs.c`. -/
def argN (rt : Rt) (v : Val) : M Int := do
  let i ← excNumberIndex rt v
  excAsSsizeLong i

/-! ### `_Py_CalculateSuggestions`, `Python/suggestions.c:8-180` -/

/-- The UTF-8 bytes of a character (`PyUnicode_AsUTF8AndSize`). A Lean `Char` is never a
surrogate, so the encoding cannot fail. -/
def utf8OfChar (c : Char) : List Nat :=
  let n := c.toNat
  if n < 0x80 then [n]
  else if n < 0x800 then [0xC0 + n / 64, 0x80 + n % 64]
  else if n < 0x10000 then [0xE0 + n / 4096, 0x80 + n / 64 % 64, 0x80 + n % 64]
  else [0xF0 + n / 262144, 0x80 + n / 4096 % 64, 0x80 + n / 64 % 64, 0x80 + n % 64]

def utf8Of (s : String) : List Nat := s.toList.flatMap utf8OfChar

/-- `MOVE_COST`, `Python/suggestions.c:11`. -/
def moveCost : Nat := 2

/-- `substitution_cost`, `Python/suggestions.c:16-35`, on bytes. `LEAST_FIVE_BITS` of a signed
`char` keeps the low five bits, as `% 32` does on the unsigned byte, and a byte above 127 is never
in `'A'..'Z'`. -/
def subCost (a b : Nat) : Nat :=
  if a % 32 != b % 32 then moveCost
  else if a == b then 0
  else
    let lo := fun x => if 65 ≤ x ∧ x ≤ 90 then x + 32 else x
    if lo a == lo b then 1 else moveCost

/-- `while (a_size && b_size && a[0] == b[0])`, `Python/suggestions.c:49-52`. -/
def trimCommon : List Nat → List Nat → List Nat × List Nat
  | x :: xs, y :: ys => if x == y then trimCommon xs ys else (x :: xs, y :: ys)
  | a, b => (a, b)

/-- One row of `levenshtein_distance`'s inner loop, `Python/suggestions.c:84-111`: the new
buffer, the last `result` and the row's `minimum`. -/
def levRow (code : Nat) : List Nat → List Nat → Nat → Nat → Nat → List Nat × Nat × Nat
  | x :: xs, d :: ds, distance, result, minimum =>
    let substitute := distance + subCost code x
    let insertDelete := min result d + moveCost
    let result := min insertDelete substitute
    let (buf, r, m) := levRow code xs ds d result (min minimum result)
    (result :: buf, r, m)
  | _, _, _, result, minimum => ([], result, minimum)

/-- The outer loop, `Python/suggestions.c:82-118`, with its early bail (`:112-115`). -/
def levRows (a : List Nat) (maxCost : Nat) : List Nat → Nat → List Nat → Nat → Nat
  | [], _, _, result => result
  | code :: bs, bIndex, buf, _ =>
    let (buf', r, m) := levRow code a buf (bIndex * moveCost) (bIndex * moveCost) (2 ^ 64)
    if m > maxCost then maxCost + 1 else levRows a maxCost bs (bIndex + 1) buf' r

/-- `levenshtein_distance`, `Python/suggestions.c:38-120`. The pointer-identity test (`:44`)
never fires here: equal names are skipped by the caller first. -/
def levDist (a b : List Nat) (maxCost : Nat) : Nat :=
  let (a, b) := trimCommon a b
  let (ra, rb) := trimCommon a.reverse b.reverse
  let (a, b) := (ra.reverse, rb.reverse)
  if a.isEmpty || b.isEmpty then (a.length + b.length) * moveCost
  else if a.length > 40 || b.length > 40 then maxCost + 1
  else
    let (a, b) := if b.length < a.length then (b, a) else (a, b)
    if (b.length - a.length) * moveCost > maxCost then maxCost + 1
    else levRows a maxCost b 0 ((List.range a.length).map fun i => (i + 1) * moveCost) 0

/-- The candidate loop of `_Py_CalculateSuggestions`, `Python/suggestions.c:150-172`, with the
best suggestion so far and its distance. A negative `max_distance` becomes a huge `size_t` in the
call, so the distance is computed in full and the candidate is skipped by `:165`. -/
def suggestLoop (name : String) : List String → Option String → Nat → Option String
  | [], sug, _ => sug
  | item :: rest, sug, sd =>
    if item == name then suggestLoop name rest sug sd
    else
      let nb := utf8Of name
      let ib := utf8Of item
      let base : Int := ((nb.length + ib.length + 3) * moveCost / 6 : Nat)
      let maxD : Int := match sug with
        | none => base
        | some _ => min base ((sd : Int) - 1)
      if maxD < 0 then suggestLoop name rest sug sd
      else
        let cur := levDist nb ib maxD.toNat
        if (cur : Int) > maxD then suggestLoop name rest sug sd
        else
          match sug with
          | none => suggestLoop name rest (some item) cur
          | some _ =>
            if cur < sd then suggestLoop name rest (some item) cur else suggestLoop name rest sug sd

/-- `_Py_CalculateSuggestions(dir, name)`, `Python/suggestions.c:122-180`. -/
def calcSuggestion (dir : List String) (name : String) : Option String :=
  if dir.length ≥ 750 then none else suggestLoop name dir none 0

/-- The message of an unexpected keyword, `Python/getargs.c:1979-1995` (and `:1605-1625`):
`"%.200s() got an unexpected keyword argument '%S'"`, followed by `". Did you mean '%S'?"` when
`_Py_CalculateSuggestions` finds a parameter name close to it. -/
def unexpectedKwMsg (fname : String) (names : List Name) (k : Name) : String :=
  let head := s!"{String.ofList (truncUtf8 200 fname.toList)}() got an unexpected keyword argument '{k}'"
  match calcSuggestion names k with
  | some s => head ++ s!". Did you mean '{s}'?"
  | none => head

/-- The "make sure there are no extraneous keyword arguments" loop of `vgetargskeywords_impl`,
`Python/getargs.c:1939-1999`: the first keyword, in dict order, that names no parameter. -/
def argUnexpectedKeyword (fname : String) (names : List Name) (kw : Kw) : M Unit :=
  match kw.find? (fun p => !names.contains p.1) with
  | some (k, _) => typeErr (unexpectedKwMsg fname names k)
  | none => typeErr s!"invalid keyword argument for {fname}()"

/-- `PyArg_ParseTupleAndKeywords(empty_tuple, kwds, "|$OO...:fname", names, ...)`:
`vgetargskeywords`, `Python/getargs.c:2015`, for keyword-only objects. -/
def argKeywordOnly (fname : String) (names : List Name) (kw : Kw) : M (Name → Option Val) := do
  if kw.length > names.length then
    let l := names.length
    typeErr s!"{fname}() takes at most {l} keyword argument{if l == 1 then "" else "s"} ({kw.length} given)"
  if kw.any (fun p => !names.contains p.1) then
    argUnexpectedKeyword fname names kw
  pure fun n => NameDict.get? kw n

/-! ## `BaseException` -/

/-- `BaseException_new`, `Objects/exceptions.c:52-77`: `tp_alloc`, every field NULL or 0, and
`args` stored (`:65-68`); `kwds` is ignored. `args` is never NULL here: `type_call` always passes
a tuple. -/
def baseExceptionNew (t : Addr) (args : List Val) : M Val :=
  alloc t (.exc { args := args })

/-- `BaseException_init`, `Objects/exceptions.c:80-88`: the keyword refusal (`:83-84`), then
`args` replaced (`:86`). -/
def baseExceptionInit (self : Val) (args : List Val) (kw : Kw) : M Unit := do
  let w ← getW
  argNoKeywords (typeName w self) kw
  excUpdate self fun d => { d with args := args }

/-- `BaseException_vectorcall`, `Objects/exceptions.c:92`: `tp_vectorcall` of the exact
classes that use `BaseException_new` and `BaseException_init` (`_PyExc_InitTypes`, `:4502`),
which is `type_call` with the two steps merged. -/
def baseExceptionVectorcall (t : Addr) (args : List Val) (kw : Kw) : M Val := do
  let w ← getW
  argNoKwnames (tpName w t) kw
  alloc t (.exc { args := args })

/-- `BaseException_str`, `Objects/exceptions.c:163`. -/
def baseExceptionStr (rt : Rt) (v : Val) : M Val := do
  let w ← getW
  match excArgs w v with
  | [] => pure (.str "")
  | [x] => .str <$> rt.str x
  | xs => .str <$> rt.str (.tuple xs)

/-- `BaseException_repr`, `Objects/exceptions.c:185`. -/
def baseExceptionRepr (rt : Rt) (v : Val) : M Val := do
  let w ← getW
  let name := pyTypeName w (typeOf w v)
  match excArgs w v with
  | [x] =>
    let r ← rt.repr x
    pure (.str s!"{name}({r})")
  | xs =>
    let r ← rt.repr (.tuple xs)
    pure (.str (name ++ r))

/-- `ImportError_repr`, `Objects/exceptions.c:1928`: the repr of the args, with its `)` dropped,
then `name=` and `path=`. -/
def importErrorRepr (rt : Rt) (v : Val) : M Val := do
  let w ← getW
  let d := excDataOf w v
  let hasargs := !(excArgs w v).isEmpty
  match memGet d "name", memGet d "path" with
  | none, none => baseExceptionRepr rt v
  | name, path =>
    let r ← baseExceptionRepr rt v
    let head := match r with
      | .str s => String.ofList (s.toList.dropLast)
      | _ => ""
    let (s1, hasargs) ← match name with
      | some n =>
        let nr ← rt.repr n
        pure (head ++ (if hasargs then ", " else "") ++ s!"name={nr}", true)
      | none => pure (head, hasargs)
    let s2 ← match path with
      | some p =>
        let pr ← rt.repr p
        pure (s1 ++ (if hasargs then ", " else "") ++ s!"path={pr}")
      | none => pure s1
    pure (.str (s2 ++ ")"))

/-- `BaseException___reduce___impl`, `Objects/exceptions.c:212`. -/
def baseExceptionReduce (v : Val) : M Val := do
  let w ← getW
  let tv : Val := .obj (typeOf w v)
  match instDictAddr w v with
  | some d => pure (.tuple [tv, .tuple (excArgs w v), .obj d])
  | none => pure (.tuple [tv, .tuple (excArgs w v)])

/-- The `PyDict_Next` loop of `BaseException___setstate___impl`, `Objects/exceptions.c:246-255`:
position `i` of the dict as it is now, so a `__setattr__` that adds to `state` is seen by the
later turns. Each pair goes to `PyObject_SetAttr`, whose `PyUnicode_Check` on the name
(`Objects/object.c`) is the `TypeError`; a failed set ends the loop (`:252-254`). Deleting an
entry during the loop is not exact: `PyDict_Next` walks a table with dummy entries, and the
model has a list (as `dictReprLoop` in `Protocol.lean`). `fuel` is a model bound. -/
def setstateLoop (rt : Rt) (self state : Val) : Nat → Nat → M Unit
  | 0, _ => raise .fuel
  | fuel + 1, i => do
    let w ← getW
    match ((dictOf w state).getD [])[i]? with
    | none => pure ()
    | some (k, v) =>
      match strOf w k with
      | none =>
        typeErr s!"attribute name must be string, not '{trunc 200 (typeName w k)}'"
      | some n =>
        rt.setAttr self n (some v)
        setstateLoop rt self state fuel (i + 1)

/-- `BaseException___setstate___impl`, `Objects/exceptions.c:235-258`. -/
def baseExceptionSetstate (rt : Rt) (self state : Val) : M Val := do
  if state.is .none then pure .none
  else
    let w ← getW
    match dictOf w state with
    | none => typeErr "state is not a dictionary"
    | some _ =>
      setstateLoop rt self state excIterFuel 0
      pure .none

/-- `BaseException___traceback___set_impl`, `Objects/exceptions.c:392`, and
`PyException_SetTraceback`, `:526`. -/
def baseExceptionTracebackSet (self : Val) (value : Option Val) : M Unit := do
  let w ← getW
  match value with
  | none => typeErr "__traceback__ may not be deleted"
  | some v =>
    if tracebackCheck w v then excUpdate self fun d => { d with traceback := v }
    else if v.is .none then excUpdate self fun d => { d with traceback := .none }
    else typeErr "__traceback__ must be a traceback or None"

/-- `BaseException_with_traceback_impl`, `Objects/exceptions.c:271`. -/
def baseExceptionWithTraceback (self tb : Val) : M Val := do
  baseExceptionTracebackSet self (some tb)
  pure self

/-- `BaseException_add_note_impl`, `Objects/exceptions.c:290`; the argument check is
the clinic wrapper, `Objects/clinic/exceptions.c.h`. -/
def baseExceptionAddNote (rt : Rt) (self note : Val) : M Val := do
  let w ← getW
  if (strOf w note).isNone then
    typeErr s!"add_note() argument must be str, not {excArgName w note}"
  let notes ← rt.getOptionalAttr self "__notes__"
  let l ← match notes with
    | none =>
      let l ← alloc B.list (.list [])
      rt.setAttr self "__notes__" (some l)
      pure l
    | some n =>
      let w ← getW
      if (listOf w n).isNone then typeErr "Cannot add note: __notes__ is not a list"
      pure n
  let w ← getW
  match l with
  | .obj a =>
    modObj a fun o => { o with body := .list (((listOf w l).getD []) ++ [note]) }
    pure .none
  | _ => gap%

/-- `_PyException_AddNote`, `Objects/exceptions.c:4646`. -/
def pyExceptionAddNote (rt : Rt) (exc note : Val) : M Unit := do
  let w ← getW
  unless excInstanceCheck w exc do
    typeErr s!"exc must be an exception, not '{typeName w exc}'"
  let _ ← baseExceptionAddNote rt exc note

/-- `BaseException_args_get_impl`, `Objects/exceptions.c:335-342`. The `self->args == NULL`
branch (`:338-340`) is unreachable in the model: `args` is a list, and only `tp_clear` sets the
field to NULL. -/
def baseExceptionArgsGet (e : ExcData) : Val := .tuple e.args

/-- `BaseException___traceback___get_impl`, `Objects/exceptions.c:374-381`: NULL reads as
`None`, which is how the model stores NULL. -/
def baseExceptionTracebackGet (e : ExcData) : Val := e.traceback

/-- `BaseException_args_set_impl`, `Objects/exceptions.c:352-365`. -/
def baseExceptionArgsSet (rt : Rt) (self : Val) (value : Option Val) : M Unit := do
  match value with
  | none => typeErr "args may not be deleted"
  | some v =>
    let seq ← excSeqTuple rt v
    excUpdate self fun d => { d with args := seq }

/-- `PyException_SetContext`, `Objects/exceptions.c:568`. -/
def pyExceptionSetContext (self : Val) (context : Option Val) : M Unit :=
  excUpdate self fun d => { d with context := context }

/-- `PyException_SetCause`, `Objects/exceptions.c:547`: it always sets `suppress_context`. -/
def pyExceptionSetCause (self : Val) (cause : Option Val) : M Unit :=
  excUpdate self fun d => { d with suppressContext := true, cause := cause }

/-- `BaseException___context___set_impl`, `Objects/exceptions.c:438`. -/
def baseExceptionContextSet (self : Val) (value : Option Val) : M Unit := do
  let w ← getW
  match value with
  | none => typeErr "__context__ may not be deleted"
  | some v =>
    if v.is .none then pyExceptionSetContext self none
    else if !excInstanceCheck w v then
      typeErr "exception context must be None or derive from BaseException"
    else pyExceptionSetContext self (some v)

/-- `BaseException___cause___set_impl`, `Objects/exceptions.c:482`. -/
def baseExceptionCauseSet (self : Val) (value : Option Val) : M Unit := do
  let w ← getW
  match value with
  | none => typeErr "__cause__ may not be deleted"
  | some v =>
    if v.is .none then pyExceptionSetCause self none
    else if !excInstanceCheck w v then
      typeErr "exception cause must be None or derive from BaseException"
    else pyExceptionSetCause self (some v)

/-- `Py_T_BOOL`, `Python/structmember.c:180`: the `__suppress_context__` member. -/
def suppressContextSet (self : Val) (value : Option Val) : M Unit := do
  match value with
  | none => typeErr "can't delete numeric/char attribute"
  | some (.bool b) => excUpdate self fun d => { d with suppressContext := b }
  | some _ => typeErr "attribute value type must be bool"

/-- `PyObject_GenericSetDict`, `Objects/object.c:2125`. -/
def excDictSet (obj : Val) (value : Option Val) : M Unit := do
  let w ← getW
  match value, obj with
  | none, _ => typeErr "cannot delete __dict__"
  | some v, .obj a =>
    match dictOf w v, v with
    | some _, .obj d => modObj a fun o => { o with dict := some d }
    | _, _ =>
      typeErr s!"__dict__ must be set to a dictionary, not a '{trunc 200 (typeName w v)}'"
  | _, _ => gap%

/-! ### The thin C API of `BaseException`, `Objects/exceptions.c:514-599` -/

/-- `PyException_GetTraceback`, `Objects/exceptions.c:515`. -/
def pyExceptionGetTraceback (w : World) (self : Val) : Option Val :=
  match (excDataOf w self).traceback with
  | .none => none
  | t => some t

/-- `PyException_GetCause`, `Objects/exceptions.c:536`. -/
def pyExceptionGetCause (w : World) (self : Val) : Option Val := (excDataOf w self).cause

/-- `PyException_GetContext`, `Objects/exceptions.c:557`. -/
def pyExceptionGetContext (w : World) (self : Val) : Option Val := (excDataOf w self).context

/-- `PyException_GetArgs`, `Objects/exceptions.c:576`. -/
def pyExceptionGetArgs (w : World) (self : Val) : Val := .tuple (excArgs w self)

/-- `PyException_SetArgs`, `Objects/exceptions.c:586`. -/
def pyExceptionSetArgs (self : Val) (args : List Val) : M Unit :=
  excUpdate self fun d => { d with args := args }

/-- `PyExceptionClass_Name`, `Objects/exceptions.c:595`. -/
def pyExceptionClassName (w : World) (t : Addr) : String := tpName w t

/-! ## `StopIteration`, `SystemExit`, `KeyError` -/

/-- `StopIteration_init`, `Objects/exceptions.c:750`. -/
def stopIterationInit (self : Val) (args : List Val) (kw : Kw) : M Unit := do
  baseExceptionInit self args kw
  excUpdate self (memSet "value" (some (args.headD .none)))

/-- `SystemExit_init`, `Objects/exceptions.c:815`. -/
def systemExitInit (self : Val) (args : List Val) (kw : Kw) : M Unit := do
  baseExceptionInit self args kw
  match args with
  | [] => pure ()
  | [x] => excUpdate self (memSet "code" (some x))
  | xs => excUpdate self (memSet "code" (some (.tuple xs)))

/-- `KeyError_str`, `Objects/exceptions.c:3019`. -/
def keyErrorStr (rt : Rt) (v : Val) : M Val := do
  let w ← getW
  match excArgs w v with
  | [x] => .str <$> rt.repr x
  | _ => baseExceptionStr rt v

/-! ## `ImportError`, `NameError`, `AttributeError` -/

/-- `msg` of `ImportError_init`, `Objects/exceptions.c:1831-1834`: the argument when there is
exactly one, NULL otherwise. -/
def importMsg (args : List Val) : Option Val :=
  match args with
  | [m] => some m
  | _ => none

/-- `ImportError_init`, `Objects/exceptions.c:1803-1837`: `BaseException_init` with no keywords
first (`:1813`), then the keyword-only parse (`:1820`), then the three members and `msg`. -/
def importErrorInit (self : Val) (args : List Val) (kw : Kw) : M Unit := do
  baseExceptionInit self args []
  let get ← argKeywordOnly "ImportError" ["name", "path", "name_from"] kw
  excUpdate self (memSet "name" (get "name"))
  excUpdate self (memSet "path" (get "path"))
  excUpdate self (memSet "name_from" (get "name_from"))
  excUpdate self (memSet "msg" (importMsg args))

/-- `ImportError_str`, `Objects/exceptions.c:1870`. -/
def importErrorStr (rt : Rt) (v : Val) : M Val := do
  let w ← getW
  match memGet (excDataOf w v) "msg" with
  | some (.str s) => pure (.str s)
  | _ => baseExceptionStr rt v

/-- A fresh copy of the entries of the instance dict, `dict ? PyDict_Copy(dict) : PyDict_New()`. -/
def instDictEntries (w : World) (v : Val) : List (Val × Val) :=
  match instDictAddr w v with
  | some d => (dictOf w (.obj d)).getD []
  | none => []

/-- `if (x && PyDict_SetItem(dict, k, x) < 0)`: set `k` when the member is not NULL. The keys
are interned exact strs, so `PyDict_SetItem` cannot fail or run code. -/
def optSetEntry (es : List (Val × Val)) (k : Name) (x : Option Val) : List (Val × Val) :=
  match x with
  | some y => dictSetEntry es (.str k) y
  | none => es

/-- `ImportError_getstate`, `Objects/exceptions.c:1879-1908`. -/
def importErrorGetstate (v : Val) : M Val := do
  let w ← getW
  let d := excDataOf w v
  let (name, path, nameFrom) := (memGet d "name", memGet d "path", memGet d "name_from")
  if name.isSome || path.isSome || nameFrom.isSome then
    let es := optSetEntry (optSetEntry (optSetEntry (instDictEntries w v) "name" name) "path" path)
      "name_from" nameFrom
    alloc B.dict (.dict es)
  else
    match instDictAddr w v with
    | some a => pure (.obj a)
    | none => pure .none

/-- `ImportError_reduce`, `Objects/exceptions.c:1911-1925`. -/
def importErrorReduce (v : Val) : M Val := do
  let state ← importErrorGetstate v
  let w ← getW
  let tv : Val := .obj (typeOf w v)
  if state.is .none then pure (.tuple [tv, .tuple (excArgs w v)])
  else pure (.tuple [tv, .tuple (excArgs w v), state])

/-- `NameError_init`, `Objects/exceptions.c:2581`. -/
def nameErrorInit (self : Val) (args : List Val) (kw : Kw) : M Unit := do
  baseExceptionInit self args []
  let get ← argKeywordOnly "NameError" ["name"] kw
  excUpdate self (memSet "name" (get "name"))

/-- `AttributeError_init`, `Objects/exceptions.c:2664`. -/
def attributeErrorInit (self : Val) (args : List Val) (kw : Kw) : M Unit := do
  baseExceptionInit self args []
  let get ← argKeywordOnly "AttributeError" ["name", "obj"] kw
  excUpdate self (memSet "name" (get "name"))
  excUpdate self (memSet "obj" (get "obj"))

/-- `AttributeError_getstate`, `Objects/exceptions.c:2720`: `self->args` is never NULL on
an initialised object, so the dictionary branch always runs. -/
def attributeErrorGetstate (v : Val) : M Val := do
  let w ← getW
  let d := excDataOf w v
  let es := instDictEntries w v
  let es := match memGet d "name" with
    | some n => dictSetEntry es (.str "name") n
    | none => es
  alloc B.dict (.dict (dictSetEntry es (.str "args") (.tuple d.args)))

/-- `AttributeError_reduce`, `Objects/exceptions.c:2749`. -/
def attributeErrorReduce (v : Val) : M Val := do
  let state ← attributeErrorGetstate v
  let w ← getW
  pure (.tuple [.obj (typeOf w v), .tuple (excArgs w v), state])

/-! ## `MemoryError` -/

/-- `MemoryError_new`, `Objects/exceptions.c:4143`, on the path every program with fewer
than 16 live `MemoryError`s takes: `get_memory_error` hands out a freelist entry, whose
`args` is the empty tuple whatever was passed. `ExcFreelist.lean` models the list itself. -/
def memoryErrorNew (t : Addr) (args : List Val) : M Val :=
  if t != B.MemoryError then baseExceptionNew t args
  else baseExceptionNew t []

end PyLean.TypeObj
