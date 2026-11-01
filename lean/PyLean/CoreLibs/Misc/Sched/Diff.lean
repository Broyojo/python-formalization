import PyLean.CoreLibs.Misc.Common
import PyLean.CoreLibs.Misc.Sched.Model

/-! `misc.sched` cases. Times and priorities are ints or strs, so comparisons can raise. The world
is a fake clock: `timefunc` returns the clock and adds `tick`, `delayfunc` adds its argument and
logs it. Actions are data, interpreted by `callA` and by the Python side the same way. -/

namespace PyLean.CoreLibs.Misc.Sched

open Lean PyLean PyLean.Diff PyLean.CoreLibs.Misc

/-- An int or a str: what the difftest stores as a time or priority. -/
inductive TV where
  | i (n : Int)
  | s (t : String)
  deriving Repr, DecidableEq, Inhabited

def TV.cls : TV → String
  | .i _ => "int"
  | .s _ => "str"

def tvEq : TV → TV → Bool
  | .i a, .i b => a == b
  | .s a, .s b => a == b
  | _, _ => false

def strLt (a b : String) : Bool := decide (a < b)

def tvOrd (op : String) (ii : Int → Int → Bool) (ss : String → String → Bool) (a b : TV) : Py Bool :=
  match a, b with
  | .i x, .i y => .ok (ii x y)
  | .s x, .s y => .ok (ss x y)
  | _, _ => .error (.typeError
      s!"'{op}' not supported between instances of '{a.cls}' and '{b.cls}'")

def tvLt : TV → TV → Py Bool := tvOrd "<" (fun a b => decide (a < b)) strLt
def tvGt : TV → TV → Py Bool := tvOrd ">" (fun a b => decide (b < a)) (fun a b => strLt b a)

def tvCmp : Cmp TV := { eq := fun a b => .ok (tvEq a b), lt := tvLt }

/-- An action, as data. -/
inductive Act where
  | log (tag : Int)
  | boom
  | enterabs (t : TV) (p : TV) (a : Act)
  | cancel (handle : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- The clock, what was logged, `delay` failures still to come, and the handles returned so far. -/
structure Wd where
  clock : Int
  tick : Int
  log : List Json
  raiseDelay : Option Int
  handles : List (Event TV TV Act Int)

instance : Repr Wd := ⟨fun w _ => repr w.clock⟩

abbrev S := Sched TV TV Act Int Wd

def tvJson : TV → Json
  | .i n => jInt n
  | .s t => jStr t

def addLog (s : S) (j : Json) : S :=
  { s with world := { s.world with log := s.world.log ++ [j] } }

def wAddHandle (s : S) (ev : Event TV TV Act Int) : S :=
  { s with world := { s.world with handles := s.world.handles ++ [ev] } }

def envBase (call : Act → List Int → List (String × Int) → S → S × Py Unit) :
    Env TV TV Act Int Wd where
  ct := tvCmp
  cp := tvCmp
  gt := tvGt
  sub := fun a b => match a, b with
    | .i x, .i y => .ok (.i (x - y))
    | _, _ => .error (.typeError "~sub")
  add := fun a b => match a, b with
    | .i x, .i y => .ok (.i (x + y))
    | _, _ => .error (.typeError
        s!"unsupported operand type(s) for +: '{a.cls}' and '{b.cls}'")
  zero := .i 0
  timefunc := fun w => ({ w with clock := w.clock + w.tick }, .ok (.i w.clock))
  delayfunc := fun w d =>
    let w := { w with log := w.log ++ [Json.arr #["delay", tvJson d]] }
    match w.raiseDelay with
    | some n =>
      if n = 0 then ({ w with raiseDelay := none }, .error (.named "RuntimeError" "delay failed"))
      else ({ w with raiseDelay := some (n - 1) }, .ok ())
    | none =>
      match d with
      | .i x => ({ w with clock := w.clock + x }, .ok ())
      | _ => (w, .ok ())
  call := call
  eqRest := fun a b => decide (a.action = b.action) && a.argument == b.argument && a.kwargs == b.kwargs

/-- `eventLt` only reads the comparisons, so actions can schedule through this environment. -/
def env0 : Env TV TV Act Int Wd := envBase (fun _ _ _ s => (s, .ok ()))

def jPairs (kw : List (String × Int)) : Json :=
  jList (fun kv => Json.arr #[jStr kv.1, jInt kv.2]) kw

def callA (a : Act) (args : List Int) (kw : List (String × Int)) (s : S) : S × Py Unit :=
  let tag : Json := match a with
    | .log t => jInt t
    | .boom => jStr "boom"
    | .enterabs _ _ _ => jStr "enterabs"
    | .cancel _ => jStr "cancel"
  let s := addLog s (Json.arr #["call", tag, jList jInt args, jPairs kw])
  match a with
  | .log _ => (s, .ok ())
  | .boom => (s, .error (.named "RuntimeError" "action failed"))
  | .enterabs t p a' =>
    match enterabs env0 s t p a' [] none with
    | (s, .ok ev) => (wAddHandle s ev, .ok ())
    | (s, .error x) => (s, .error x)
  | .cancel i =>
    match s.world.handles[i]? with
    | some ev => cancel env0 s ev
    | none => (s, .ok ())

def env : Env TV TV Act Int Wd := envBase callA

def parseTV (j : Json) : Except String TV :=
  match j with
  | .str t => .ok (.s t)
  | v => do return .i (← v.getInt?)

partial def parseAct (j : Json) : Except String Act := do
  match ← jStrAt j 0 with
  | "log" => return .log (← jIntAt j 1)
  | "boom" => return .boom
  | "enterabs" =>
    let t ← parseTV (← jGetI j 1)
    let p ← parseTV (← jGetI j 2)
    let a ← parseAct (← jGetI j 3)
    return .enterabs t p a
  | "cancel" => return .cancel (← jNatAt j 1)
  | o => throw s!"bad act {o}"

def parseKw (j : Json) : Except String (Option (List (String × Int))) :=
  match j with
  | .null => .ok none
  | v => do
    let items ← jArr v
    return some (← items.mapM (fun kv => do return ((← jStrAt kv 0), (← jIntAt kv 1))))

def jEvent (ev : Event TV TV Act Int) : Json :=
  Json.arr #[tvJson ev.time, tvJson ev.priority, toJson ev.sequence, jList jInt ev.argument,
    jPairs ev.kwargs]

def jEv3 (ev : Event TV TV Act Int) : Json :=
  Json.arr #[tvJson ev.time, tvJson ev.priority, toJson ev.sequence]

def step (s : S) (op : Json) : Except String (S × Json) := do
  match ← jStrAt op 0 with
  | "enterabs" | "enter" =>
    let t ← parseTV (← jGetI op 1)
    let p ← parseTV (← jGetI op 2)
    let a ← parseAct (← jGetI op 3)
    let args ← jIntListAt op 4
    let kw ← parseKw (← jGetI op 5)
    let (s, r) := if (← jStrAt op 0) == "enter" then enter env s t p a args kw
      else enterabs env s t p a args kw
    match r with
    | .ok ev => return (wAddHandle s ev, encR jEvent r)
    | .error _ => return (s, encR jEvent r)
  | "cancel" =>
    let i ← jNatAt op 1
    match s.world.handles[i]? with
    | some ev =>
      let (s, r) := cancel env s ev
      return (s, encR jUnit r)
    | none => return (s, encR jUnit (.ok ()))
  | "empty" => return (s, encR jBool (.ok (empty s)))
  | "queue" => return (s, encR (jList jEv3) (queue env s))
  | "run" =>
    let b ← jBoolAt op 1
    let rd ← jOptIntAt op 2
    let s := { s with world := { s.world with raiseDelay := rd } }
    let (s, r) := run env 2000 s b
    let s := { s with world := { s.world with raiseDelay := none } }
    return (s, encR (jOpt tvJson) r)
  | o => throw s!"unknown op {o}"

def runCase (j : Json) : Except String Json := do
  let tick ← getInt j "tick"
  let w : Wd := { clock := 0, tick, log := [], raiseDelay := none, handles := [] }
  let mut s : S := init w
  let mut out : Array Json := #[]
  for op in (← jArr (← field j "ops")) do
    let (s', r) ← step s op
    s := s'
    out := out.push r
  let d := Json.arr #[jList jEv3 s.queue, toJson s.seq, jInt s.world.clock, Json.arr s.world.log.toArray]
  return Json.mkObj [("ok", Json.arr (out.push d))]

end PyLean.CoreLibs.Misc.Sched
