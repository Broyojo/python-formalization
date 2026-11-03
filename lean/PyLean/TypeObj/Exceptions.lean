import PyLean.TypeObj.ExcCore
import PyLean.TypeObj.ExcGroup
import PyLean.TypeObj.ExcOs
import PyLean.TypeObj.ExcUnicode

/-!
The exception hierarchy: `Objects/exceptions.c`.

Each exception class belongs to a `CFn` family naming the C functions it installs (see
`familyOf` in `Builtins.lean`). The bodies live in `ExcCore`, `ExcGroup`, `ExcOs` and
`ExcUnicode`. This file provides the entry points the slot dispatchers call:

* `excCallStr`, `excCallRepr`: `tp_str`, `tp_repr`;
* `excTpNew`, `excTpInit`: `tp_new`, `tp_init`;
* `excGetsetGet`, `excGetsetSet`: `PyGetSetDef`s and `PyMemberDef`s;
* `excMethod`: `PyMethodDef`s, by name.
-/

namespace PyLean.TypeObj

/-- `tp_str` of the exception families. -/
def excCallStr (rt : Rt) (f : CFn) (v : Val) : M Val :=
  match f with
  | .keyError => keyErrorStr rt v
  | .exceptionGroup => baseExceptionGroupStr rt v
  | .importError => importErrorStr rt v
  | .osError => osErrorStr rt v
  | .syntaxError => syntaxErrorStr rt v
  | .unicodeEncodeError => unicodeEncodeErrorStr rt v
  | .unicodeDecodeError => unicodeDecodeErrorStr rt v
  | .unicodeTranslateError => unicodeTranslateErrorStr rt v
  | _ => baseExceptionStr rt v

/-- `tp_repr` of the exception families. -/
def excCallRepr (rt : Rt) (f : CFn) (v : Val) : M Val :=
  match f with
  | .exceptionGroup => baseExceptionGroupRepr rt v
  | .importError => importErrorRepr rt v
  | _ => baseExceptionRepr rt v

/-- `tp_new` of the exception families. `kwds` matters only to `OSError_new`. -/
def excTpNew (rt : Rt) (f : CFn) (t : Addr) (args : List Val) (kw : Kw) : M Val :=
  match f with
  | .exceptionGroup => baseExceptionGroupNew rt t args
  | .osError => osErrorNew rt t args kw
  | .memoryError => memoryErrorNew t args
  | _ => baseExceptionNew t args

/-- `tp_init` of the exception families. -/
def excTpInit (rt : Rt) (f : CFn) (self : Val) (args : List Val) (kw : Kw) : M Unit :=
  match f with
  | .stopIteration => stopIterationInit self args kw
  | .systemExit => systemExitInit self args kw
  | .exceptionGroup => baseExceptionGroupInit self args kw
  | .importError => importErrorInit self args kw
  | .osError => osErrorInit rt self args kw
  | .nameError => nameErrorInit self args kw
  | .attributeError => attributeErrorInit self args kw
  | .syntaxError => syntaxErrorInit rt self args kw
  | .unicodeEncodeError => unicodeEncodeErrorInit rt self args kw
  | .unicodeDecodeError => unicodeDecodeErrorInit rt self args kw
  | .unicodeTranslateError => unicodeTranslateErrorInit rt self args kw
  | _ => baseExceptionInit self args kw

/-- Getter for a `PyGetSetDef` or `PyMemberDef` of an exception class. -/
def excGetsetGet (_rt : Rt) (_owner : Addr) (n : Name) (obj : Val) : M Val := do
  let w ← getW
  match payloadOf w obj with
  | some (.exc e) =>
    if n == "args" then return baseExceptionArgsGet e
    if n == "__traceback__" then return baseExceptionTracebackGet e
    if n == "__context__" then return e.context.getD .none
    if n == "__cause__" then return e.cause.getD .none
    if n == "__suppress_context__" then return .bool e.suppressContext
    if n == "__dict__" then
      let d ← ensureDict obj
      return .obj d
    if n == "message" then return e.egMessage.getD .none
    if n == "exceptions" then return .tuple e.egExceptions
    if n == "characters_written" then return ← osErrorWrittenGet obj
    if n == "start" || n == "end" then return .int (ssizeMember e n)
    return (memGet e n).getD .none
  | _ => gap%

/-- Setter for a `PyGetSetDef` or `PyMemberDef` of an exception class. -/
def excGetsetSet (rt : Rt) (_owner : Addr) (n : Name) (obj : Val) (value : Option Val) :
    M Unit := do
  let w ← getW
  match payloadOf w obj with
  | some (.exc _) =>
    if n == "__cause__" then return ← baseExceptionCauseSet obj value
    if n == "__context__" then return ← baseExceptionContextSet obj value
    if n == "__traceback__" then return ← baseExceptionTracebackSet obj value
    if n == "__suppress_context__" then return ← suppressContextSet obj value
    if n == "args" then return ← baseExceptionArgsSet rt obj value
    if n == "__dict__" then return ← excDictSet obj value
    if n == "characters_written" then return ← osErrorWrittenSet rt obj value
    if n == "start" || n == "end" then
      match value with
      | none => return ← typeErr "can't delete numeric/char attribute"
      | some v =>
        match intOf w v with
        | none => return ← typeErr "an integer is required"
        | some i =>
          let i ← excAsSsizeLong i
          return ← excUpdate obj (memSet n (some (.int i)))
    excUpdate obj (memSet n value)
  | _ => gap%

/-- The arity check of a `METH_O` method descriptor, `method_vectorcall_O`, `Objects/descrobject.c:454`. -/
def methO (name : String) (args : List Val) : M Val :=
  match args with
  | [a] => pure a
  | _ => typeErr s!"{name}() takes exactly one argument ({args.length} given)"

/-- The arity check of a `METH_NOARGS` method descriptor, `method_vectorcall_NOARGS`, `Objects/descrobject.c:427`. -/
def methNoArgs (name : String) (args : List Val) : M Unit :=
  match args with
  | [] => pure ()
  | _ => typeErr s!"{name}() takes no arguments ({args.length} given)"

/-- `_testcapi` wrappers of the Unicode error getters and setters,
`Modules/_testcapi/exceptions.c:384-541`: `name` is `unicode_<kind>_<get|set>_<start|end>`. -/
def excTestcapiUnicode (rt : Rt) (name : Name) (args : List Val) : M Val := do
  let (k, rest) : UKind × String :=
    if name.startsWith "unicode_encode_" then (.encode, name.drop 15 |>.toString)
    else if name.startsWith "unicode_decode_" then (.decode, name.drop 15 |>.toString)
    else (.translate, name.drop 18 |>.toString)
  match rest, args with
  | "get_start", [self] => .int <$> pyUnicodeErrorGetStart k self
  | "get_end", [self] => .int <$> pyUnicodeErrorGetEnd k self
  | "set_start", [self, v] =>
    let n ← argN rt v
    pyUnicodeErrorSetStart k self n
    pure .none
  | "set_end", [self, v] =>
    let n ← argN rt v
    pyUnicodeErrorSetEnd k self n
    pure .none
  | _, _ => gap%

/-- `PyMethodDef`s of exception classes, by `Builtin.excMethod` name; `harness.` and `capi.`
names are the functions a difftest scenario reaches through `_testcapi`. -/
def excMethod (rt : Rt) (name : Name) (self : Val) (args : List Val) (_kw : Kw) : M Val := do
  match name with
  | "BaseException.__reduce__" =>
    methNoArgs name args
    baseExceptionReduce self
  | "BaseException.__setstate__" =>
    baseExceptionSetstate rt self (← methO name args)
  | "BaseException.with_traceback" =>
    baseExceptionWithTraceback self (← methO name args)
  | "BaseException.add_note" =>
    baseExceptionAddNote rt self (← methO name args)
  | "BaseExceptionGroup.derive" =>
    baseExceptionGroupDerive rt self (← methO name args)
  | "BaseExceptionGroup.split" =>
    baseExceptionGroupSplit rt self (← methO name args)
  | "BaseExceptionGroup.subgroup" =>
    baseExceptionGroupSubgroup rt self (← methO name args)
  | "ImportError.__reduce__" =>
    methNoArgs name args
    importErrorReduce self
  | "OSError.__reduce__" =>
    methNoArgs name args
    osErrorReduce self
  | "AttributeError.__getstate__" =>
    methNoArgs name args
    attributeErrorGetstate self
  | "AttributeError.__reduce__" =>
    methNoArgs name args
    attributeErrorReduce self
  | "capi.prep_reraise_star" =>
    match args with
    | [orig, excs] => pyUnstableExcPrepReraiseStar rt orig excs
    | _ => gap%
  | "harness.bytes" | "harness.bytearray" =>
    let w ← getW
    let bs := args.map fun a => ((intOf w a).getD 0).toNat
    alloc (if name == "harness.bytes" then B.bytes else B.bytearray) (.bytes bs)
  | _ =>
    if name.startsWith "capi.unicode_" then excTestcapiUnicode rt (name.drop 5 |>.toString) args
    else gap%

end PyLean.TypeObj
