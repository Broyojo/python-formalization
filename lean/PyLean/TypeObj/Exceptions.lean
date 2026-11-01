import PyLean.TypeObj.Attr

/-!
The exception hierarchy: `Objects/exceptions.c`.

Each exception class belongs to a `CFn` family naming the C functions it installs. This
file provides the entry points the slot dispatchers call:

* `excCallStr`, `excCallRepr`: `tp_str`, `tp_repr`;
* `excTpNew`, `excTpInit`: `tp_new`, `tp_init`;
* `excGetsetGet`, `excGetsetSet`: `PyGetSetDef`s and `PyMemberDef`s;
* `excMethod`: `PyMethodDef`s, by name.
-/

namespace PyLean.TypeObj

/-- The `args` of an exception object. -/
def excArgs (w : World) (v : Val) : List Val :=
  match payloadOf w v with
  | some (.exc e) => e.args
  | _ => []

/-- `BaseException_str`, `Objects/exceptions.c:171`. -/
def baseExceptionStr (rt : Rt) (v : Val) : M Val := do
  let w ← getW
  match excArgs w v with
  | [] => pure (.str "")
  | [x] => .str <$> rt.str x
  | xs => .str <$> rt.str (.tuple xs)

/-- `KeyError_str`, `Objects/exceptions.c:2942`. -/
def keyErrorStr (rt : Rt) (v : Val) : M Val := do
  let w ← getW
  match excArgs w v with
  | [x] => .str <$> rt.repr x
  | _ => baseExceptionStr rt v

/-- `BaseException_repr`, `Objects/exceptions.c:193`. -/
def baseExceptionRepr (rt : Rt) (v : Val) : M Val := do
  let w ← getW
  let args := excArgs w v
  let tn := typeQualname w (typeOf w v)
  let mut rs : List String := []
  for a in args do
    rs := rs ++ [← rt.repr a]
  match rs with
  | [r] => pure (.str s!"{tn}({r})")
  | _ => pure (.str (tn ++ "(" ++ ", ".intercalate rs ++ ")"))

/-- `tp_str` of the exception families. -/
def excCallStr (rt : Rt) (f : CFn) (v : Val) : M Val :=
  match f with
  | .keyError => keyErrorStr rt v
  | _ => baseExceptionStr rt v

/-- `tp_repr` of the exception families. -/
def excCallRepr (rt : Rt) (_f : CFn) (v : Val) : M Val := baseExceptionRepr rt v

/-- `BaseException_new`, `Objects/exceptions.c:60`. -/
def excTpNew (_rt : Rt) (_f : CFn) (t : Addr) (args : List Val) (_kw : Kw) : M Val :=
  alloc t (.exc { args := args })

/-- `BaseException_init`, `Objects/exceptions.c:88`. -/
def excTpInit (_rt : Rt) (_f : CFn) (self : Val) (args : List Val) (kw : Kw) : M Unit := do
  let w ← getW
  unless kw.isEmpty do typeErr s!"{typeName w self}() takes no keyword arguments"
  match self with
  | .obj a =>
    modObj a fun o =>
      match o.body with
      | .exc d => { o with body := .exc { d with args := args } }
      | _ => o
  | _ => unmodelled

/-- Getter for a `PyGetSetDef` or `PyMemberDef` of an exception class. -/
def excGetsetGet (_rt : Rt) (_owner : Addr) (n : Name) (obj : Val) : M Val := do
  let w ← getW
  match payloadOf w obj with
  | some (.exc e) =>
    if n == "args" then return .tuple e.args
    if n == "__traceback__" then return e.traceback
    if n == "__context__" then return e.context.getD .none
    if n == "__cause__" then return e.cause.getD .none
    if n == "__suppress_context__" then return .bool e.suppressContext
    if n == "__dict__" then
      let d ← ensureDict obj
      return .obj d
    unmodelled
  | _ => unmodelled

/-- Setter for a `PyGetSetDef` or `PyMemberDef` of an exception class. -/
def excGetsetSet (rt : Rt) (_owner : Addr) (n : Name) (obj : Val) (value : Option Val) :
    M Unit := do
  let w ← getW
  match payloadOf w obj, obj with
  | some (.exc e), .obj a =>
    let setE (g : ExcData) : M Unit := modObj a fun o => { o with body := .exc g }
    if n == "__cause__" then
      match value with
      | none => typeErr "__cause__ may not be deleted"
      | some .none => return ← setE { e with cause := none, suppressContext := true }
      | some v =>
        if isSubtype w (typeOf w v) B.BaseException then
          return ← setE { e with cause := some v, suppressContext := true }
        typeErr "exception cause must be None or derive from BaseException"
    if n == "__context__" then
      match value with
      | none => typeErr "__context__ may not be deleted"
      | some .none => return ← setE { e with context := none }
      | some v =>
        if isSubtype w (typeOf w v) B.BaseException then
          return ← setE { e with context := some v }
        typeErr "exception context must be None or derive from BaseException"
    if n == "__suppress_context__" then
      match value with
      | some v => return ← setE { e with suppressContext := ← rt.isTrue v }
      | none => typeErr "can't delete numeric/char attribute"
    if n == "args" then
      match value with
      | none => typeErr "args may not be deleted"
      | some v =>
        -- `PySequence_Tuple` needs `Protocol`; exact tuples and lists cover the setter.
        match tupleOf w v, listOf w v with
        | some xs, _ | _, some xs => return ← setE { e with args := xs }
        | _, _ => unmodelled
    unmodelled
  | _, _ => unmodelled

/-- `PyMethodDef`s of exception classes, by `Builtin.excMethod` name. -/
def excMethod (_rt : Rt) (_name : Name) (_self : Val) (_args : List Val) (_kw : Kw) : M Val :=
  unmodelled

end PyLean.TypeObj
