import PyLean.UnicodeObj.CodecProps

/-!
Interning: Objects/unicodeobject.c:14290-14510, for the default build. The paths under
`Py_GIL_DISABLED` are a platform branch.

Interning is about which object you get, so objects have ids and the state is a heap. Equal text
never stands for the same object here: the theorems compare ids. `PyDict_SetDefaultRef` can fail only
by running out of memory, since the keys are exact `str`, and that path is not modelled.

A mortal interned string leaves the dict when it is deallocated. There are no refcounts here, so
every object lives forever; `unicode_dealloc` is out of scope.
-/

namespace PyLean.UnicodeObj

open PyLean

abbrev ObjId := Nat

/-- `PyUnicode_CHECK_INTERNED`. -/
inductive InternState where
  | none | mortal | immortal | static
  deriving Repr, DecidableEq

/-- What matters of an object here. -/
structure UObj where
  text : Str := []
  /-- `PyUnicode_Check`. -/
  isStr : Bool := true
  /-- `PyUnicode_CheckExact`. -/
  exact : Bool := true
  state : InternState := .none
  /-- `_Py_IsImmortal`. -/
  immortal : Bool := false
  deriving Repr, DecidableEq

/-- The heap and the tables. -/
structure IWorld where
  objs : ObjId → UObj
  /-- The per-interpreter `interned_strings` dict. -/
  dict : Str → Option ObjId
  /-- `INTERNED_STRINGS`, the statically allocated strings. -/
  cache : Str → Option ObjId
  /-- `LATIN1(ch)`. -/
  latin1 : Nat → ObjId
  /-- The empty string. -/
  empty : ObjId
  /-- The next free id. -/
  next : ObjId

def IWorld.setObj (W : IWorld) (i : ObjId) (o : UObj) : IWorld :=
  { W with objs := fun j => if j = i then o else W.objs j }

/-- `immortalize_interned`, unicodeobject.c:14259-14276. -/
def immortalizeInterned (W : IWorld) (s : ObjId) : IWorld :=
  W.setObj s { W.objs s with immortal := true, state := .immortal }

/-- The test at unicodeobject.c:14347: one character, of the one-byte kind. -/
def latin1Of : Str → Option Nat
  | [c] => if c < 256 then some c else none
  | _ => none

/-- `intern_common`, unicodeobject.c:14291-14460, without the free-threaded paths. -/
def internCommon (W : IWorld) (s : ObjId) (immortalize : Bool) : IWorld × ObjId :=
  let o := W.objs s
  if !o.isStr then (W, s)
  else if !o.exact then (W, s)
  else
    match o.state with
    | .mortal => (if immortalize then immortalizeInterned W s else W, s)
    | .immortal | .static => (W, s)
    | .none =>
      let imm := immortalize || o.immortal
      match latin1Of o.text with
      | some c => (W, W.latin1 c)
      | none =>
        match W.cache o.text with
        | some r => (W, r)
        | none =>
          match W.dict o.text with
          | some t =>
            (if imm && ((W.objs t).state == .mortal) then immortalizeInterned W t else W, t)
          | none =>
            let W1 : IWorld :=
              { W with dict := fun k => if k = o.text then some s else W.dict k }
            let W2 := W1.setObj s { o with state := .mortal }
            (if imm then immortalizeInterned W2 s else W2, s)

/-- `_PyUnicode_InternMortal`, which is `sys.intern` and `PyUnicode_InternInPlace`. -/
def internMortal (W : IWorld) (s : ObjId) : IWorld × ObjId := internCommon W s false

/-- `_PyUnicode_InternImmortal`, which is `PyUnicode_InternImmortal`. -/
def internImmortal (W : IWorld) (s : ObjId) : IWorld × ObjId := internCommon W s true

/-- A new `str` with this text, as `unicode_result` leaves it: the singletons for the empty string
and for one character of the one-byte kind. -/
def newStr (W : IWorld) (text : Str) : IWorld × ObjId :=
  match latin1Of text with
  | some c => (W, W.latin1 c)
  | none =>
    if text.isEmpty then (W, W.empty)
    else
      let i := W.next
      ({ W.setObj i { text } with next := i + 1 }, i)

/-- A new instance of a subclass of `str`, or of something else. -/
def newObj (W : IWorld) (o : UObj) : IWorld × ObjId :=
  let i := W.next
  ({ W.setObj i o with next := i + 1 }, i)

/-- `PyUnicode_InternFromString`, unicodeobject.c:14501-14510: a strict decode that can fail. -/
def internFromString (W : IWorld) (b : Bytes) : Py (IWorld × ObjId) :=
  match utf8Decode b .strict with
  | .error e => .error e
  | .ok text =>
    let (W1, s) := newStr W text
    .ok (internMortal W1 s)

/-- An operation of the difftest. Each one that succeeds adds a handle. -/
inductive KOp where
  | newStr (text : Str)
  | newSub (text : Str)
  | newOther
  | mortal (h : Nat)
  | immortal (h : Nat)
  | fromString (b : Bytes)

/-- One operation on a list of handles, in the order they were made. -/
def applyKOp (W : IWorld) (hs : List ObjId) : KOp → IWorld × List ObjId × Py Unit
  | .newStr t => let (W1, i) := newStr W t; (W1, hs ++ [i], .ok ())
  | .newSub t => let (W1, i) := newObj W { text := t, exact := false }; (W1, hs ++ [i], .ok ())
  | .newOther => let (W1, i) := newObj W { isStr := false, exact := false }; (W1, hs ++ [i], .ok ())
  | .mortal h => let (W1, i) := internMortal W (hs.getD h 0); (W1, hs ++ [i], .ok ())
  | .immortal h => let (W1, i) := internImmortal W (hs.getD h 0); (W1, hs ++ [i], .ok ())
  | .fromString b =>
    match internFromString W b with
    | .ok (W1, i) => (W1, hs ++ [i], .ok ())
    | .error e => (W, hs, .error e)

def runKOps : IWorld → List ObjId → List KOp → IWorld × List ObjId × List (Py Unit)
  | W, hs, [] => (W, hs, [])
  | W, hs, op :: t =>
    let (W1, hs1, r) := applyKOp W hs op
    let (W2, hs2, rs) := runKOps W1 hs1 t
    (W2, hs2, r :: rs)

/-- Where a string is in the list of statically allocated strings. -/
def staticIndex (t : Str) : List Str → Option Nat
  | [] => none
  | x :: r => if x = t then some 0 else (staticIndex t r).map (· + 1)

/-- A statically allocated string. -/
def staticObj (t : Str) : UObj := { text := t, state := .static, immortal := true }

/-- The heap of `startWorld`: the ids below 256 are `LATIN1`, 256 is the empty string, the
statically allocated strings follow, and every id after them is unused. -/
def startObj (statics : List Str) (i : ObjId) : UObj :=
  if i < 256 then staticObj [i]
  else if i = 256 then staticObj []
  else if i - 257 < statics.length then staticObj (statics.getD (i - 257) [])
  else {}

/-- The runtime when a program starts, for a list of statically allocated strings. -/
def startWorld (statics : List Str) : IWorld :=
  { objs := startObj statics
    dict := fun _ => none
    cache := fun t => if t.isEmpty then some 256 else (staticIndex t statics).map (· + 257)
    latin1 := fun c => c
    empty := 256
    next := 257 + statics.length }

end PyLean.UnicodeObj
