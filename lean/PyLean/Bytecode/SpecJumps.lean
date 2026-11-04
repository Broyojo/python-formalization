import PyLean.Bytecode.SpecLocals

/-!
The unconditional relative jumps at the level of the dispatch loop: where the instruction after
`JUMP_FORWARD` and `JUMP_BACKWARD_NO_INTERRUPT` is fetched from, for every oparg, with or without
`EXTENDED_ARG` prefixes, checked against the jump target `Lib/dis.py` reports.

`dis` computes the target of a relative jump in `_get_jump_target` (`Lib/dis.py`): `offset + 2 +
arg*2 + 2*caches`, with `arg` negated for a backward jump, where `offset` is the jump's own offset
and `arg` is accumulated over the `EXTENDED_ARG` prefixes as `code[i+1] | extended_arg` with
`extended_arg = arg << 8` (`_unpack_opargs`). In code units that is `p + 1 + caches ± arg`. The
interpreter gets there differently: `TARGET` advances `next_instr` past the instruction and its
inline caches before the body runs (`frame->instr_ptr = next_instr; next_instr += 1 +
INLINE_CACHE_ENTRIES`), `EXTENDED_ARG` shifts the oparg into the next fetch
(`EXTENDED_ARG`, `Python/bytecodes.c:6054-6060`), and then the body does `JUMPBY(oparg)` (`:3494-3496`) or
`JUMPBY(-oparg)` (`:3656-3664`). These statements say the two agree, and that nothing else moves:
the stack, the heap, and a pending eval-breaker event, which `JUMP_BACKWARD_NO_INTERRUPT` leaves
for the innermost generator (bpo-30039), are exactly as they were, and `frame->instr_ptr` records
the jump. A body that jumped from its own address instead of the next one, by `oparg + 1`, by a
cache-adjusted amount, in the wrong direction, or that ran the periodic check, fails one of them.
-/

namespace PyLean.Bytecode

open Uop

/-- The state after a relative jump at `p` with full oparg `arg`, `dir` being `1` or `-1`. -/
abbrev jumpedFrom (s : St) (p : Nat) (target : Nat) : St :=
  { s with regs := { s.regs with frame := { s.regs.frame with instrPtr := p }, next := target } }

/-- `_get_jump_target`, `Lib/dis.py`, in code units: the jump at `p` with `caches` inline cache
entries and oparg `arg`. -/
def disJumpTarget (backward : Bool) (p caches arg : Nat) : Int :=
  (p : Int) + 1 + caches + (if backward then -(arg : Int) else arg)

/-- For every program, state, `EXTENDED_ARG` carry `carry` (dis's `extended_arg`) and oparg byte
`lo`: fetching `JUMP_FORWARD lo` at `p` continues at dis's target for the full oparg
`(carry <<< 8) ||| lo`, with only `instr_ptr` and `next_instr` changed; fetching
`JUMP_BACKWARD_NO_INTERRUPT lo` does the same backwards, whenever the target is inside the code
(the `assert(oparg <= INSTR_OFFSET())` of `:3662`, a compiler invariant). An `EXTENDED_ARG hi` at
`p` fetches the instruction at `p + 1` with the carry `(carry <<< 8) ||| hi`, so a chain of
prefixes builds dis's oparg. -/
def JumpDispatch : Prop :=
  ∀ (P : Program) (om : ObjModel) (ctx : Ctx) (s : St) (c : Code) (n carry : Nat) (ins : Instr),
    P[s.regs.frame.code]? = some c → c.instrs[s.regs.next]? = some ins →
    (ins.op = .JUMP_FORWARD →
      stepInstr P om ctx s (n + 1) carry =
        .ok () (jumpedFrom s s.regs.next
          (disJumpTarget false s.regs.next 0 ((carry <<< 8) ||| ins.arg)).toNat)) ∧
    (ins.op = .JUMP_BACKWARD_NO_INTERRUPT → (carry <<< 8) ||| ins.arg ≤ s.regs.next + 1 →
      stepInstr P om ctx s (n + 1) carry =
        .ok () (jumpedFrom s s.regs.next
          (disJumpTarget true s.regs.next 0 ((carry <<< 8) ||| ins.arg)).toNat)) ∧
    (ins.op = .EXTENDED_ARG →
      stepInstr P om ctx s (n + 1) carry =
        stepInstr P om ctx { s with regs := { s.regs with next := s.regs.next + 1 } } n
          ((carry <<< 8) ||| ins.arg))

theorem jumpDispatch_proven : JumpDispatch := by
  intro P om ctx s c n carry ins hc hi
  obtain ⟨op, arg, cache⟩ := ins
  refine ⟨fun hop => ?_, fun hop hle => ?_, fun hop => ?_⟩
  · simp only at hop
    subst hop
    simp only [stepInstr, hc, hi, Option.bind_some]
    simp [execOp, JUMP_FORWARD, beginInstr, instrSize, uninstr, BM.lift, jumpBy, disJumpTarget,
      jumpedFrom, Op.deopt, Op.caches]
  · simp only at hop hle
    subst hop
    simp only [stepInstr, hc, hi, Option.bind_some]
    simp [execOp, JUMP_BACKWARD_NO_INTERRUPT, beginInstr, instrSize, uninstr, BM.lift, jumpBy,
      disJumpTarget, jumpedFrom, Op.deopt, Op.caches]
  · simp only at hop
    subst hop
    simp only [stepInstr, hc, hi, Option.bind_some]
    simp

def JumpFull : Prop := JumpRules ∧ JumpDispatch
theorem jumpFull_proven : JumpFull := ⟨jumpRules_proven, jumpDispatch_proven⟩

end PyLean.Bytecode
