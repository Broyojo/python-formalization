import PyLean.Bytecode.SpecLocals
import PyLean.Bytecode.LawfulBuiltin

/-!
Closure cells and the tuple and list builders, `Python/bytecodes.c`: `MAKE_CELL`, `DELETE_DEREF`,
`LOAD_DEREF`, `STORE_DEREF`, `BUILD_TUPLE`, `BUILD_LIST`.

A cell is a heap object holding one value or NULL. What `STORE_DEREF` writes, `LOAD_DEREF`
reads back; `DELETE_DEREF` empties the cell, after which reading or deleting it again raises
the error `_PyEval_FormatExcUnbound` builds (a `NameError` for a free variable, an
`UnboundLocalError` for a cell variable). `MAKE_CELL` wraps the local's current value, which is
an argument's value when the function's own parameter is captured.

A builder pops its `oparg` operands and pushes one new object holding them in the order they
were pushed, leaving everything below untouched.
-/

namespace PyLean.Bytecode

open Uop

/-- The state after writing object `o` at address `c`. -/
abbrev withObj (s : St) (c : Addr) (o : Obj) : St :=
  { s with regs := { s.regs with rt := { s.regs.rt with heap := s.regs.rt.heap.setIfInBounds c o } } }

theorem cellGet_ok {rt : Rt} {c : Addr} {v : Val} (h : rt.heap[c]? = some (.cell v)) :
    cellGet (.ref c) rt = .ok v rt := by
  simp [cellGet, getObj, h, bind, EStateM.bind, pure, EStateM.pure]

/-- `STORE_DEREF` puts the value in the cell; `LOAD_DEREF` pushes what a bound cell holds, and
after a store it pushes what was stored; `DELETE_DEREF` empties a bound cell. On an empty cell
`LOAD_DEREF` and `DELETE_DEREF` raise the same exception and leave the stack and the cell alone.
The hypothesis is that local `oparg` holds a cell, which the compiler guarantees for these
opcodes after `MAKE_CELL` or `COPY_FREE_VARS`. -/
def CellRules : Prop := ∀ (e : Env) (s : St) (c : Addr) (old : Val),
  s.regs.frame.fast[e.oparg]? = some (.ref c) → s.regs.rt.heap[c]? = some (.cell old) →
    (∀ v rest, s.stack = v :: rest →
      execOp e .STORE_DEREF s = .ok () { withObj s c (.cell v) with stack := rest } ∧
      (v ≠ .null → (execOp e .STORE_DEREF *> execOp e .LOAD_DEREF) s =
        .ok () (withObj s c (.cell v)))) ∧
    (old ≠ .null →
      execOp e .LOAD_DEREF s = .ok () { s with stack := old :: s.stack } ∧
      execOp e .DELETE_DEREF s = .ok () (withObj s c (.cell .null))) ∧
    (old = .null → ∀ (co : Code) x rt, e.P[s.regs.frame.code]? = some co →
      (formatExcUnbound co e.oparg : RM Unit) s.regs.rt = .error x rt →
      execOp e .LOAD_DEREF s = .error x { s with regs := { s.regs with rt := rt } } ∧
      execOp e .DELETE_DEREF s = .error x { s with regs := { s.regs with rt := rt } })

theorem storeDeref_ok (e : Env) (s : St) (c : Addr) (v : Val) (rest : List Val)
    (hf : s.regs.frame.fast[e.oparg]? = some (.ref c)) (hs : s.stack = v :: rest) :
    execOp e .STORE_DEREF s = .ok () { withObj s c (.cell v) with stack := rest } := by
  show stk 1 0 _ s = _
  obtain ⟨regs, stack⟩ := s
  simp only at hs hf
  subst hs
  exact stk_ok (outs := []) (r := _) (by simp)
    (by simp [bind, EStateM.bind, getLocal_ok hf, cellSet, setObj, RM.lift, liftM, monadLift,
      MonadLift.monadLift, pure, EStateM.pure]) rfl

theorem loadDeref_ok (e : Env) (s : St) (c : Addr) (v : Val)
    (hf : s.regs.frame.fast[e.oparg]? = some (.ref c)) (hc : s.regs.rt.heap[c]? = some (.cell v))
    (hn : v ≠ .null) :
    execOp e .LOAD_DEREF s = .ok () { s with stack := v :: s.stack } := by
  have hb : (v == Val.null) = false := by simpa using hn
  show stk 0 1 _ s = _
  exact stk_ok (outs := [v]) (r := s.regs) (by simp)
    (by simp [bind, EStateM.bind, getLocal_ok hf, cellGet_ok hc, hb, RM.lift, liftM, monadLift,
      MonadLift.monadLift, pure, EStateM.pure]) rfl

theorem cellRules_proven : CellRules := by
  intro e s c old hf hc
  refine ⟨fun v rest hs => ⟨storeDeref_ok e s c v rest hf hs, fun hn => ?_⟩, fun hn => ⟨?_, ?_⟩,
    fun hn co x rt hco hx => ⟨?_, ?_⟩⟩
  · simp only [SeqRight.seqRight, EStateM.seqRight, storeDeref_ok e s c v rest hf hs]
    have hf' : ({ withObj s c (.cell v) with stack := rest } : St).regs.frame.fast[e.oparg]? =
        some (.ref c) := hf
    have hc' : ({ withObj s c (.cell v) with stack := rest } : St).regs.rt.heap[c]? = some (.cell v) := by
      simp [withObj, Array.getElem?_setIfInBounds, (Array.getElem?_eq_some_iff.1 hc).1]
    rw [loadDeref_ok e _ c v hf' hc' hn]
    obtain ⟨regs, stack⟩ := s
    simp only at hs
    subst hs
    rfl
  · exact loadDeref_ok e s c old hf hc hn
  · have hb : (old == Val.null) = false := by simpa using hn
    show stk 0 0 _ s = _
    exact stk_ok (outs := []) (r := _) (by simp)
      (by simp [bind, EStateM.bind, getLocal_ok hf, cellGet_ok hc, hb, cellSet, setObj, RM.lift, liftM,
        monadLift, MonadLift.monadLift, pure, EStateM.pure]) rfl
  · subst hn
    show stk 0 1 _ s = _
    exact stk_err (by simp) (by
      simp [bind, EStateM.bind, getLocal_ok hf, cellGet_ok hc, getCode_ok hco, RM.lift, liftM, monadLift,
        MonadLift.monadLift, hx])
  · subst hn
    show stk 0 0 _ s = _
    exact stk_err (by simp) (by
      simp [bind, EStateM.bind, getLocal_ok hf, cellGet_ok hc, getCode_ok hco, RM.lift, liftM, monadLift,
        MonadLift.monadLift, hx])

/-- `MAKE_CELL` replaces local `oparg` with a new cell holding the local's value, so a following
`LOAD_DEREF` reads that value back. -/
def MakeCellRules : Prop := ∀ (e : Env) (s : St) (old : Val),
  s.regs.frame.fast[e.oparg]? = some old →
    execOp e .MAKE_CELL s = .ok ()
      { s with regs := { s.regs with
          rt := { s.regs.rt with heap := s.regs.rt.heap.push (.cell old) },
          frame := { s.regs.frame with
            fast := s.regs.frame.fast.setIfInBounds e.oparg (.ref s.regs.rt.heap.size) } } } ∧
    (old ≠ .null → (execOp e .MAKE_CELL *> execOp e .LOAD_DEREF) s = .ok ()
      { s with
        regs := { s.regs with
          rt := { s.regs.rt with heap := s.regs.rt.heap.push (.cell old) },
          frame := { s.regs.frame with
            fast := s.regs.frame.fast.setIfInBounds e.oparg (.ref s.regs.rt.heap.size) } },
        stack := old :: s.stack })

theorem makeCellRules_proven : MakeCellRules := by
  intro e s old hf
  have h1 : execOp e .MAKE_CELL s = .ok ()
      { s with regs := { s.regs with
          rt := { s.regs.rt with heap := s.regs.rt.heap.push (.cell old) },
          frame := { s.regs.frame with
            fast := s.regs.frame.fast.setIfInBounds e.oparg (.ref s.regs.rt.heap.size) } } } := by
    show stk 0 0 _ s = _
    exact stk_ok (outs := []) (r := _) (by simp)
      (by simp [bind, EStateM.bind, getLocal_ok hf, cellNew, alloc, setLocal, RM.lift, liftM, monadLift,
        MonadLift.monadLift, pure, EStateM.pure]) rfl
  refine ⟨h1, fun hn => ?_⟩
  simp only [SeqRight.seqRight, EStateM.seqRight, h1]
  apply loadDeref_ok e _ s.regs.rt.heap.size old _ _ hn
  · have hlt : e.oparg < s.regs.frame.fast.size := (Array.getElem?_eq_some_iff.1 hf).1
    simp [Array.getElem?_setIfInBounds, hlt]
  · simp

/-- `BUILD_TUPLE n` and `BUILD_LIST n` pop their `n` operands and push a new object holding them
in the order they were pushed, leaving the rest of the stack alone. -/
def BuildRules : Prop := ∀ (e : Env) (regs : Regs) (top rest : List Val), top.length = e.oparg →
    execOp e .BUILD_TUPLE ⟨regs, top ++ rest⟩ = .ok ()
      ⟨{ regs with rt := { regs.rt with heap := regs.rt.heap.push (.tuple top.reverse.toArray) } },
        .ref regs.rt.heap.size :: rest⟩ ∧
    execOp e .BUILD_LIST ⟨regs, top ++ rest⟩ = .ok ()
      ⟨{ regs with rt := { regs.rt with heap := regs.rt.heap.push (.list top.reverse.toArray) } },
        .ref regs.rt.heap.size :: rest⟩

theorem buildRules_proven : BuildRules := by
  intro e regs top rest hn
  have ht : ((top ++ rest).take e.oparg).reverse = top.reverse := by rw [← hn]; simp
  have hd : (top ++ rest).drop e.oparg = rest := by rw [← hn]; simp
  constructor
  · show stk _ 1 _ _ = _
    refine (stk_ok (outs := [.ref regs.rt.heap.size])
      (r := { regs with rt := { regs.rt with heap := regs.rt.heap.push (.tuple top.reverse.toArray) } })
      (by simp; omega) ?_ rfl).trans ?_
    · simp only [ht]
      simp [bind, EStateM.bind, mkTuple, alloc, RM.lift, liftM, monadLift, MonadLift.monadLift, pure,
        EStateM.pure]
    · simp [hd]
  · show stk _ 1 _ _ = _
    refine (stk_ok (outs := [.ref regs.rt.heap.size])
      (r := { regs with rt := { regs.rt with heap := regs.rt.heap.push (.list top.reverse.toArray) } })
      (by simp; omega) ?_ rfl).trans ?_
    · simp only [ht]
      simp [bind, EStateM.bind, mkList, alloc, RM.lift, liftM, monadLift, MonadLift.monadLift, pure,
        EStateM.pure]
    · simp [hd]

end PyLean.Bytecode
