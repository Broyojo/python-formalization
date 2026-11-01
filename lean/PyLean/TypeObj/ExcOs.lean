import PyLean.TypeObj.ExcCore

/-!
`OSError` and `SyntaxError`: `Objects/exceptions.c:2066-2462`, `:2791-2951`.

The errno map is the Linux table: `_PyExc_InitState` is built from the platform's `<errno.h>`
macros, and the difftest runs on Linux x86-64.
-/

namespace PyLean.TypeObj

/-- The output parameters of `oserror_parse_args`. -/
structure OsParsed where
  myerrno : Option Val := none
  strerror : Option Val := none
  filename : Option Val := none
  filename2 : Option Val := none

/-- `oserror_parse_args`, `Objects/exceptions.c:2067`: positions 0, 1, 2 and 4; position 3 is
`winerror`, which is parsed and dropped outside Windows. -/
def oserrorParseArgs (args : List Val) : OsParsed :=
  if 2 ≤ args.length ∧ args.length ≤ 5 then
    { myerrno := args[0]?, strerror := args[1]?, filename := args[2]?, filename2 := args[4]? }
  else {}

/-- Does this optional object hold something other than NULL or `None`? -/
def nonNone (v : Option Val) : Bool :=
  match v with
  | some .none | none => false
  | some _ => true

/-- `oserror_init`, `Objects/exceptions.c:2124`. -/
def oserrorInit (rt : Rt) (self : Val) (args : List Val) (p : OsParsed) : M Unit := do
  let w ← getW
  let nargs := args.length
  let mut newArgs := args
  match p.filename with
  | some fn =>
    if !fn.is .none then
      if typeOf w self == B.BlockingIOError && excNumberCheck w fn then
        let n ← excAsSsizeValueError rt fn
        excUpdate self fun d => { d with written := n }
      else
        excUpdate self (memSet "filename" (some fn))
        if nonNone p.filename2 then
          excUpdate self (memSet "filename2" p.filename2)
        if 2 ≤ nargs ∧ nargs ≤ 5 then
          newArgs := args.take 2
  | none => pure ()
  excUpdate self (memSet "errno" p.myerrno)
  excUpdate self (memSet "strerror" p.strerror)
  excUpdate self fun d => { d with args := newArgs }

/-- `oserror_use_init`, `Objects/exceptions.c:2184`. -/
def oserrorUseInit (w : World) (t : Addr) : Bool :=
  slotOf w t .tp_init != some (.c .osError) && slotOf w t .tp_new == some (.c .osError)

/-- `errnomap` on Linux x86-64, `Objects/exceptions.c:4554-4581`. -/
def errnoMap : List (Int × Addr) :=
  [(11, B.BlockingIOError), (114, B.BlockingIOError), (115, B.BlockingIOError),
   (32, B.BrokenPipeError), (108, B.BrokenPipeError), (10, B.ChildProcessError),
   (103, B.ConnectionAbortedError), (111, B.ConnectionRefusedError),
   (104, B.ConnectionResetError), (17, B.FileExistsError), (2, B.FileNotFoundError),
   (21, B.IsADirectoryError), (20, B.NotADirectoryError), (4, B.InterruptedError),
   (13, B.PermissionError), (1, B.PermissionError), (3, B.ProcessLookupError),
   (110, B.TimeoutError)]

/-- `PyDict_GetItemWithError(errnomap, key)`: the keys are exact small ints, so the hash finds
the only candidate and `==` confirms it. -/
def errnoLookup (rt : Rt) (key : Val) : M (Option Addr) := do
  let h ← rt.hash key
  match errnoMap.find? (fun p => p.1 == h) with
  | none => pure none
  | some (k, t) =>
    match key with
    | .int i => pure (if i == k then some t else none)
    | .bool b => pure (if (if b then (1 : Int) else 0) == k then some t else none)
    | _ =>
      let r ← rt.richCompare (.int k) key .eq
      if ← rt.isTrue r then pure (some t) else pure none

/-- `OSError_new`, `Objects/exceptions.c:2215-2238`: argument parsing and the choice of
class. Parsing is deferred to `__init__` when `oserror_use_init`, which is why extra
arguments and keywords are ignored there. -/
def osErrorNewClass (rt : Rt) (t : Addr) (args : List Val) (kw : Kw) : M (Addr × OsParsed) := do
  let w ← getW
  if oserrorUseInit w t then return (t, {})
  argNoKeywords (tpName w t) kw
  let p := oserrorParseArgs args
  match p.myerrno with
  | some e =>
    if (intOf w e).isSome && t == B.OSError then
      match ← errnoLookup rt e with
      | some nt => pure (nt, p)
      | none => pure (t, p)
    else pure (t, p)
  | none => pure (t, p)

/-- `OSError_new`, `Objects/exceptions.c:2204`. -/
def osErrorNew (rt : Rt) (t : Addr) (args : List Val) (kw : Kw) : M Val := do
  let (cls, p) ← osErrorNewClass rt t args kw
  let self ← alloc cls (.exc {})
  let w ← getW
  if !oserrorUseInit w cls then
    oserrorInit rt self args p
  pure self

/-- `OSError_init`, `Objects/exceptions.c:2272`. -/
def osErrorInit (rt : Rt) (self : Val) (args : List Val) (kw : Kw) : M Unit := do
  let w ← getW
  if !oserrorUseInit w (typeOf w self) then return ()
  argNoKeywords (typeName w self) kw
  oserrorInit rt self args (oserrorParseArgs args)

/-- `OR_NONE`, `Objects/exceptions.c:2350`. -/
def orNone (v : Option Val) : Val := v.getD .none

/-- `OSError_str`, `Objects/exceptions.c:2347`. -/
def osErrorStr (rt : Rt) (self : Val) : M Val := do
  let w ← getW
  let d := excDataOf w self
  let (eno, serr) := (memGet d "errno", memGet d "strerror")
  match memGet d "filename" with
  | some fn =>
    let a ← rt.str (orNone eno)
    let b ← rt.str (orNone serr)
    let c ← rt.repr fn
    match memGet d "filename2" with
    | some f2 =>
      let e ← rt.repr f2
      pure (.str s!"[Errno {a}] {b}: {c} -> {e}")
    | none => pure (.str s!"[Errno {a}] {b}: {c}")
  | none =>
    match eno, serr with
    | some x, some y =>
      let a ← rt.str x
      let b ← rt.str y
      pure (.str s!"[Errno {a}] {b}")
    | _, _ => baseExceptionStr rt self

/-- The `args` of `OSError_reduce`, `Objects/exceptions.c:2401-2423`: with a filename and two
arguments, the filenames go back in their positions, `winerror` as `None`. -/
def osReduceArgs (d : ExcData) : List Val :=
  match d.args, memGet d "filename" with
  | [a, b], some fn =>
    match memGet d "filename2" with
    | some f2 => [a, b, fn, .none, f2]
    | none => [a, b, fn]
  | xs, _ => xs

/-- `OSError_reduce`, `Objects/exceptions.c:2393`. -/
def osErrorReduce (self : Val) : M Val := do
  let w ← getW
  let d := excDataOf w self
  let tv : Val := .obj (typeOf w self)
  match instDictAddr w self with
  | some da => pure (.tuple [tv, .tuple (osReduceArgs d), .obj da])
  | none => pure (.tuple [tv, .tuple (osReduceArgs d)])

/-- `OSError_written_get`, `Objects/exceptions.c:2434`. -/
def osErrorWrittenGet (self : Val) : M Val := do
  let w ← getW
  let n := (excDataOf w self).written
  if n == -1 then attrErr "characters_written" else pure (.int n)

/-- `OSError_written_set`, `Objects/exceptions.c:2445`. -/
def osErrorWrittenSet (rt : Rt) (self : Val) (value : Option Val) : M Unit := do
  let w ← getW
  match value with
  | none =>
    if (excDataOf w self).written == -1 then attrErr "characters_written"
    excUpdate self fun d => { d with written := -1 }
  | some v =>
    let n ← excAsSsizeValueError rt v
    excUpdate self fun d => { d with written := n }

/-! ## `SyntaxError` -/

/-- The member assignments of `SyntaxError_init`, `Objects/exceptions.c:2822-2828`. -/
def syntaxErrorStoreInfo (self : Val) (info : List Val) : M Unit := do
  excUpdate self (memSet "filename" info[0]?)
  excUpdate self (memSet "lineno" info[1]?)
  excUpdate self (memSet "offset" info[2]?)
  excUpdate self (memSet "text" info[3]?)
  excUpdate self (memSet "end_lineno" info[4]?)
  excUpdate self (memSet "end_offset" info[5]?)
  excUpdate self (memSet "_metadata" info[6]?)

/-- The two-argument case of `SyntaxError_init`, `Objects/exceptions.c:2804-2834`. -/
def syntaxErrorParseInfo (rt : Rt) (self info0 : Val) : M Unit := do
  let info ← excSeqTuple rt info0
  argCount none 4 7 info.length
  syntaxErrorStoreInfo self info
  if info[4]?.isSome && info[5]?.isNone then
    typeErr "end_offset must be provided when end_lineno is provided"

/-- `SyntaxError_init`, `Objects/exceptions.c:2791`. -/
def syntaxErrorInit (rt : Rt) (self : Val) (args : List Val) (kw : Kw) : M Unit := do
  baseExceptionInit self args kw
  match args with
  | [] => pure ()
  | a0 :: _ =>
    excUpdate self (memSet "msg" (some a0))
    match args with
    | [_, info0] => syntaxErrorParseInfo rt self info0
    | _ => pure ()

/-- `SEP`, `Include/osdefs.h`, on POSIX. -/
def sepChar : Char := '/'

/-- The offset loop of `my_basename`, `Objects/exceptions.c:2893-2897`: one past the last `SEP`. -/
def basenameOffset : Nat → Nat → List Char → Nat
  | _, off, [] => off
  | i, off, c :: cs => basenameOffset (i + 1) (if c == sepChar then i + 1 else off) cs

/-- `my_basename`, `Objects/exceptions.c:2883`. -/
def myBasename (name : String) : String :=
  let off := basenameOffset 0 0 name.toList
  if off != 0 then String.ofList (name.toList.drop off) else name

/-- `PyLong_AsLongAndOverflow` as `%ld` prints it: overflow gives `-1`. -/
def longOrMinusOne (i : Int) : Int := if inSsize i then i else -1

/-- `SyntaxError_str`, `Objects/exceptions.c:2908`. `%S` on the message runs first. -/
def syntaxErrorStr (rt : Rt) (self : Val) : M Val := do
  let w ← getW
  let d := excDataOf w self
  let filename : Option String :=
    match memGet d "filename" with
    | some f => (strOf w f).map myBasename
    | none => none
  let lineno : Option Int :=
    match memGet d "lineno" with
    | some (.int i) => some i
    | _ => none
  let msg := orNone (memGet d "msg")
  match filename, lineno with
  | none, none => .str <$> rt.str msg
  | some f, some l =>
    let m ← rt.str msg
    pure (.str s!"{m} ({f}, line {longOrMinusOne l})")
  | some f, none =>
    let m ← rt.str msg
    pure (.str s!"{m} ({f})")
  | none, some l =>
    let m ← rt.str msg
    pure (.str s!"{m} (line {longOrMinusOne l})")

end PyLean.TypeObj
