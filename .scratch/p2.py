p='lean/PyLean/Bytecode/State.lean'
s=open(p).read()
s=s.replace('''  /-- `_PyThreadState_HasStackSpace`: whether the current data-stack chunk has
  room. It depends on the allocator's chunk boundaries, so it is an oracle. -/
  stackSpace : Bool := true
  deriving Inhabited''','''  /-- `_PyThreadState_HasStackSpace`: whether the current data-stack chunk has
  room. It depends on the allocator's chunk boundaries, so it is an oracle. -/
  stackSpace : Bool := true
  /-- Written only by the profiling loop of the difftest: per code object and
  instruction, the specialized form seen first. -/
  profile : Array (Array (Option Instr)) := #[]
  deriving Inhabited''')
open(p,'w').write(s)

p='lean/PyLean/Bytecode/Diff.lean'
s=open(p).read()
s=s.replace('import PyLean.Bytecode.Builtins\n','import PyLean.Bytecode.Specialize\n')
s=s.replace('''/-- `PyEval_EvalCode`, `Python/ceval.c:957-987`, on a fresh interpreter. -/
def runMain (fuel : Nat) (P : Program) (main : Nat) : RM Val := do
  let builtins ← initBuiltins
  let globals ← mkDict
  dictSetStr globals "__name__" (.str "__main__")
  dictSetStr globals "__builtins__" builtins
  let co ← getCodeR P main
  let f ← alloc (.func { code := main, globals := globals, builtins := builtins,
                         name := co.name, qualname := co.name })
  let om := builtinOM P
  let ctx : Ctx := { evalFrame := evalFrame P om fuel }
  evalVector P ctx f globals [] []
''','''/-- `PyEval_EvalCode`, `Python/ceval.c:957-987`, on a fresh interpreter. -/
def runMainWith (ev : Frame → Option Val → RM Val) (P : Program) (main : Nat) : RM Val := do
  let builtins ← initBuiltins
  let globals ← mkDict
  dictSetStr globals "__name__" (.str "__main__")
  dictSetStr globals "__builtins__" builtins
  let co ← getCodeR P main
  let f ← alloc (.func { code := main, globals := globals, builtins := builtins,
                         name := co.name, qualname := co.name })
  evalVector P { evalFrame := ev } f globals [] []

def runMain (fuel : Nat) (P : Program) (main : Nat) : RM Val :=
  runMainWith (evalFrame P (builtinOM P) fuel) P main

/-- Note what the specializer would do at the instruction about to execute. -/
def recordProfile (P : Program) (s : St) : St :=
  let c := s.regs.frame.code
  let ip := s.regs.next
  match P[c]? with
  | none => s
  | some co =>
    let filled := match s.regs.rt.profile[c]? with
      | some row => (row[ip]?.join).isSome
      | none => true
    let afterExtended := ip != 0 && (co.instrs[ip - 1]?.map (·.op)) == some .EXTENDED_ARG
    if filled || afterExtended then s
    else
      match co.instrs[ip]? with
      | none => s
      | some i =>
        match suggest P co i (co.instrs[ip + instrSize i.op]?) s.regs.frame s.stack s.regs.rt with
        | .ok (some i') _ =>
          let rt := s.regs.rt
          let row := (rt.profile.getD c #[]).setIfInBounds ip (some i')
          { s with regs := { s.regs with rt := { rt with profile := rt.profile.setIfInBounds c row } } }
        | _ => s

/-- `runLoop` with `recordProfile` before each instruction. -/
def runLoopP (P : Program) (om : ObjModel) : Nat → St → EStateM.Result Err Rt Val
  | 0, s => .error .fuel s.regs.rt
  | n + 1, s =>
    let s := recordProfile P s
    let ctx : Ctx := { evalFrame := evalWith P (runLoopP P om n) }
    match afterInstr P (stepInstr P om ctx s 6 0) with
    | .cont s' => runLoopP P om n s'
    | .ret v rt => .ok v rt
    | .raised v rt => .error (.exc v) rt
    | .stop e rt => .error e rt

/-- Rewrite each instruction the profile has an answer for. -/
def applyProfile (P : Program) (prof : Array (Array (Option Instr))) : Program :=
  (P.zipIdx).map fun (co, c) =>
    match prof[c]? with
    | none => co
    | some row =>
      { co with instrs := (co.instrs.zipIdx).map fun (i, ip) =>
          match row[ip]? with
          | some (some i') => i'
          | _ => i }
''')
s=s.replace('''/-- Run a dumped module. -/
def runProgram (j : Json) (transform : Program → Program) : Except String Json := do''','''/-- Run a dumped module; with `quick`, profile a first run and report the run of
the specialized program. -/
def runProgram (j : Json) (quick : Bool) : Except String Json := do''')
s=s.replace('''    let P : Program := transform (#[trampolineCode, initCleanupCode] ++ cs)
    let rt := match (getNat j "reclimit" |>.toOption) with
      | some n => { rt with pyRecursionRemaining := n, recursionLimit := n }
      | none => rt
''','''    let P : Program := #[trampolineCode, initCleanupCode] ++ cs
    let rt := match (getNat j "reclimit" |>.toOption) with
      | some n => { rt with pyRecursionRemaining := n, recursionLimit := n }
      | none => rt
    let P ← if quick then do
        let rt1 := { rt with profile := P.map fun c => Array.replicate c.instrs.size none }
        match runMainWith (evalWith P (runLoopP P (builtinOM P) fuel)) P (main + 2) rt1 with
        | .ok _ r | .error (.exc _) r => pure (applyProfile P r.profile)
        | .error _ _ => pure P
      else pure P
''')
s=s.replace('''  | "run" => runProgram j id
''','''  | "run" => runProgram j false
  | "quick" => runProgram j true
''')
open(p,'w').write(s)

p='difftest/bytecode_diff.py'
s=open(p).read()
s=s.replace('''    return dict(mod="bytecode", fn="run", codes=table, main=main_idx, src=src, family=fam.__name__)
''','''    fn = "quick" if rng.random() < 0.5 else "run"
    return dict(mod="bytecode", fn=fn, codes=table, main=main_idx, src=src, family=fam.__name__)
''')
s=s.replace('''        gc.collect()
    return {"ok": {"out"''','''        gc.collect(1)
    return {"ok": {"out"''')
open(p,'w').write(s)

p='.scratch/dbg.py'
s=open(p).read()
s=s.replace("if c is None or c['fn'] != 'run':","if c is None or c['fn'] == 'effect':")
s=s.replace("    fam = c['family']\n","    fam = c['family'] + ('+q' if c['fn'] == 'quick' else '')\n")
s=s.replace('''print({k: f"{ok[k]}/{tot[k]}" for k in tot})''','''print({k: f"{ok[k]}/{tot[k]}" for k in sorted(tot) if ok[k] != tot[k]})''')
open(p,'w').write(s)
