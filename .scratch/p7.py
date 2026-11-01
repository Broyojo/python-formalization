p='lean/PyLean/Bytecode/Diff.lean'
s=open(p).read()
s=s.replace('''import PyLean.Bytecode.Specialize
''','''import PyLean.Bytecode.Specialize
import PyLean.Bytecode.FrameObj
import PyLean.Bytecode.IterObj
''')
s=s.replace('''def run (fn : String) (j : Json) : Except String Json :=
  match fn with
''','''/-- `fn = "frame_jump"`: `frame_lineno_set_impl` on a dumped function. -/
def runFrameJump (j : Json) : Except String Json := do
  let code ← (← field j "code").getArr?
  let units ← code.mapM fun u => do
    let op ← (u.getArrVal? 0 >>= (·.getNat?))
    let arg ← (u.getArrVal? 1 >>= (·.getNat?))
    match Op.ofNat? op with
    | some o => pure ({ op := o, arg := arg } : FrameObj.Unit')
    | none => throw s!"unknown opcode {op}"
  let table ← natArr j "table"
  let lines ← (← field j "lines").getArr?
  let lines ← lines.mapM (·.getInt?)
  let first ← getInt j "first"
  let value ← getInt j "value"
  let lasti ← getNat j "lasti"
  match FrameObj.linenoDecide units table lines first value lasti with
  | .error m => pure (Json.mkObj [("ok", Json.arr #[toJson "err", toJson m])])
  | .ok addr _ => pure (Json.mkObj [("ok", Json.arr #[toJson "ok", toJson addr])])

/-- `fn = "iter_seq"`: a script of `next`/`__length_hint__`/`__setstate__`/`__reduce__`
on `iter(seq)` or `reversed(seq)`. -/
def runIterSeq (j : Json) : Except String Json := do
  let script ← (← field j "script").getArr?
  let script ← script.mapM (·.getInt?)
  let ops ← (← field j "ops").getArr?
  let rev ← getBool j "rev"
  let getitem (i : Int) : Py Int :=
    if i < 0 then .error (.indexError "out") else
    match (script[i.toNat]?).getD (-1) with
    | -1 => .error (.indexError "out")
    | -2 => .error .stopIteration
    | -3 => .error (.valueError "v")
    | a => .ok a
  let enc : Py (Option Int) → Json
    | .ok (some v) => toJson v
    | .ok none => toJson "stop"
    | .error e => toJson e.className
  let size : Py Int := .ok script.size
  let mut it : IterObj.SeqIter := IterObj.seqIterNew
  let mut ro : IterObj.Rev := IterObj.revNew script.size
  let mut out : Array Json := #[]
  for o in ops do
    let op ← (o.getArrVal? 0 >>= (·.getStr?))
    let arg ← (o.getArrVal? 1 >>= (·.getInt?))
    match op, rev with
    | "next", false =>
      let (it', r) := IterObj.iterIternext getitem it
      it := it'
      out := out.push (enc r)
    | "next", true =>
      let (ro', r) := IterObj.revNext getitem ro
      ro := ro'
      out := out.push (enc r)
    | "hint", false =>
      out := out.push (match IterObj.iterLen (some size) it with
        | .ok (some v) => toJson v
        | _ => Json.null)
    | "hint", true =>
      out := out.push (match IterObj.revLen size ro with
        | .ok v => toJson v
        | .error e => toJson e.className)
    | "set", false =>
      it := IterObj.iterSetstate it arg
      out := out.push (toJson "set")
    | "set", true =>
      match IterObj.revSetstate size ro arg with
      | .ok r => ro := r
      | .error _ => pure ()
      out := out.push (toJson "set")
    | _, false =>
      out := out.push (match IterObj.iterReduce it with
        | some v => toJson v
        | none => Json.null)
    | _, true =>
      out := out.push (match IterObj.revReduce ro with
        | some v => toJson v
        | none => Json.null)
  pure (Json.mkObj [("ok", Json.arr out)])

/-- `fn = "enum_counts"`: indices of `enumerate(start)` and the pickled count. -/
def runEnum (j : Json) : Except String Json := do
  let start ← match (← getStr j "start").toInt? with
    | some i => pure i
    | none => throw "start"
  let n ← getNat j "n"
  let e0 := IterObj.enumNew start
  let idx := IterObj.enumIndices n e0
  let en := (List.range n).foldl (fun e _ => (IterObj.enumNext e).1) e0
  pure (Json.mkObj [("ok", Json.arr #[Json.arr (idx.map (fun i => toJson (toString i))).toArray,
    toJson (toString (IterObj.enumReduce en))])])

/-- `fn = "cell_cmp"`: the six comparisons of two cells of ints. -/
def runCell (j : Json) : Except String Json := do
  let get (k : String) : Except String (Option Int) := getOptInt j k
  let a ← get "a"
  let b ← get "b"
  let cmp (x y : Int) (op : Nat) : Py Bool := .ok (match op with
    | 0 => decide (x < y) | 1 => decide (x ≤ y) | 2 => decide (x = y)
    | 3 => decide (x ≠ y) | 4 => decide (x > y) | _ => decide (x ≥ y))
  let rs := (List.range 6).map fun op =>
    match IterObj.cellCompare cmp id a b op with
    | .ok r => toJson r
    | .error _ => Json.null
  pure (Json.mkObj [("ok", Json.arr rs.toArray)])

def run (fn : String) (j : Json) : Except String Json :=
  match fn with
  | "frame_jump" => runFrameJump j
  | "iter_seq" => runIterSeq j
  | "enum_counts" => runEnum j
  | "cell_cmp" => runCell j
''')
open(p,'w').write(s)
