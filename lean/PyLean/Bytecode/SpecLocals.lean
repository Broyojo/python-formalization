import PyLean.Bytecode.Exec

/-!
What the stack, local-variable, constant and jump opcodes do, for every state.

These are the contracts the compiler relies on, stated apart from the step rules:
a superinstruction is the two instructions it replaces, `LOAD_FAST_AND_CLEAR` and
`STORE_FAST` save and restore a local around an inlined comprehension, `SWAP`
undoes itself, a conditional jump goes where its condition says. Each statement
fixes the whole result state, so an opcode that touched anything else would fail.

The one hypothesis on these is that an index the compiler emits is in range
(`fast[i]? = some v`, `i < consts.size`, `n ≤ stack.length`), a type invariant of
compiled code: `co_nlocalsplus` sizes the locals and `co_stacksize` the stack.
-/

namespace PyLean.Bytecode

open Uop

/-! ### Running a step rule -/

theorem stk_ok {p q : Nat} {f : List Val → BM (List Val)} {s : St} {outs : List Val} {r : Regs}
    (hp : p ≤ s.stack.length) (hf : f (s.stack.take p).reverse s.regs = .ok outs r)
    (hq : outs.length = q) :
    stk p q f s = .ok () { regs := r, stack := outs.reverse ++ s.stack.drop p } := by
  subst hq
  simp [stk, popN, hp, bind, EStateM.bind, BM.lift, hf, pushAll, pure, EStateM.pure]

theorem stk_err {p q : Nat} {f : List Val → BM (List Val)} {s : St} {e : Err} {r : Regs}
    (hp : p ≤ s.stack.length) (hf : f (s.stack.take p).reverse s.regs = .error e r) :
    stk p q f s = .error e { regs := r, stack := s.stack.drop p } := by
  simp [stk, popN, hp, bind, EStateM.bind, BM.lift, hf]

theorem getLocal_ok {r : Regs} {i : Nat} {v : Val} (h : r.frame.fast[i]? = some v) :
    getLocal i r = .ok v r := by
  simp [getLocal, h]

/-- The state after `GETLOCAL(i) = v`. -/
def withLocal (s : St) (i : Nat) (v : Val) : St :=
  { s with regs := { s.regs with frame := { s.regs.frame with
      fast := s.regs.frame.fast.setIfInBounds i v } } }

/-! ### Locals -/

/-- `LOAD_FAST` and `LOAD_FAST_BORROW` push the local and change nothing else:
`Python/bytecodes.c:283-291`. A borrowed reference is not a different value. -/
def LoadFastPushes : Prop := ∀ (e : Env) (s : St) (v : Val),
  s.regs.frame.fast[e.oparg]? = some v →
    execOp e .LOAD_FAST s = .ok () { s with stack := v :: s.stack } ∧
    execOp e .LOAD_FAST_BORROW s = .ok () { s with stack := v :: s.stack }

theorem loadFastPushes_proven : LoadFastPushes := by
  intro e s v h
  constructor <;>
  · show stk 0 1 _ s = _
    exact stk_ok (outs := [v]) (r := s.regs) (by simp)
      (by simp [bind, EStateM.bind, getLocal_ok h, pure, EStateM.pure]) rfl

/-- `LOAD_FAST_CHECK` on a bound local is `LOAD_FAST`. On an unbound one it raises
`UnboundLocalError` with the message of `Python/ceval_macros.h:399`, naming the variable,
and the stack and locals do not change: `:271-281`. -/
def LoadFastCheckRules : Prop := ∀ (e : Env) (s : St) (v : Val) (c : Code),
  s.regs.frame.fast[e.oparg]? = some v → e.P[s.regs.frame.code]? = some c →
    (v ≠ .null → execOp e .LOAD_FAST_CHECK s = execOp e .LOAD_FAST s) ∧
    (v = .null → ∀ x rt,
      (raiseS "UnboundLocalError" (unboundLocalMsg (c.localsplusnames.getD e.oparg "")) : RM Unit)
        s.regs.rt = .error x rt →
      execOp e .LOAD_FAST_CHECK s = .error x { s with regs := { s.regs with rt := rt } })

theorem getCode_ok {P : Program} {r : Regs} {c : Code} (h : P[r.frame.code]? = some c) :
    getCode P r = .ok c r := by
  simp [getCode, h]

theorem loadFastCheckRules_proven : LoadFastCheckRules := by
  intro e s v c hv hc
  constructor
  · intro hne
    have hb : (v == Val.null) = false := by simpa using hne
    have h1 : execOp e .LOAD_FAST_CHECK s = .ok () { s with stack := v :: s.stack } := by
      show stk 0 1 _ s = _
      exact stk_ok (outs := [v]) (r := s.regs) (by simp)
        (by simp [bind, EStateM.bind, getLocal_ok hv, hb, pure, EStateM.pure]) rfl
    rw [h1, (loadFastPushes_proven e s v hv).1]
  · intro hn x rt hr
    subst hn
    simp only [Array.getD_eq_getD_getElem?] at hr
    show stk 0 1 _ s = _
    exact stk_err (by simp) (by
      simp [bind, EStateM.bind, getLocal_ok hv, getCode_ok hc, liftM, monadLift, MonadLift.monadLift,
        RM.lift, formatExcCheckArg, hr])

theorem setIfInBounds_restore {α : Type} {a : Array α} {i : Nat} {v x : α} (h : a[i]? = some v) :
    (a.setIfInBounds i x).setIfInBounds i v = a := by
  obtain ⟨hlt, rfl⟩ := Array.getElem?_eq_some_iff.1 h
  apply Array.ext_getElem?
  intro j
  by_cases hj : i = j
  · subst hj
    simp [Array.getElem?_setIfInBounds, hlt]
  · simp [Array.getElem?_setIfInBounds, hj]

/-- `LOAD_FAST_AND_CLEAR` pushes the local and leaves it unbound, and `STORE_FAST` then puts it
back. This is how the compiler saves a name around an inlined comprehension (PEP 709): the
pair must restore the state exactly, including a local that was unbound. `:293-296`, `:323`. -/
def LoadClearStoreRestores : Prop := ∀ (e : Env) (s : St) (v : Val),
  s.regs.frame.fast[e.oparg]? = some v →
    execOp e .LOAD_FAST_AND_CLEAR s = .ok () { withLocal s e.oparg .null with stack := v :: s.stack } ∧
    (execOp e .LOAD_FAST_AND_CLEAR *> execOp e .STORE_FAST) s = .ok () s

theorem storeFast_ok (e : Env) (regs : Regs) (v : Val) (rest : List Val) :
    execOp e .STORE_FAST { regs := regs, stack := v :: rest } =
      .ok () (withLocal { regs := regs, stack := rest } e.oparg v) := by
  show stk 1 0 _ _ = _
  exact stk_ok (outs := []) (r := _) (by simp)
    (by simp [setLocal, bind, EStateM.bind, pure, EStateM.pure]) rfl

theorem loadClearStoreRestores_proven : LoadClearStoreRestores := by
  intro e s v h
  have h1 : execOp e .LOAD_FAST_AND_CLEAR s =
      .ok () { withLocal s e.oparg .null with stack := v :: s.stack } := by
    show stk 0 1 _ s = _
    exact stk_ok (outs := [v]) (r := _) (by simp)
      (by simp [bind, EStateM.bind, getLocal_ok h, setLocal, withLocal, pure, EStateM.pure]) rfl
  refine ⟨h1, ?_⟩
  simp only [SeqRight.seqRight, EStateM.seqRight, h1]
  show execOp e .STORE_FAST { regs := _, stack := v :: s.stack } = _
  rw [storeFast_ok]
  cases s with
  | mk regs stack =>
    cases regs with
    | mk rt frame prev next =>
      cases frame
      simp only [withLocal] at h ⊢
      simp only [setIfInBounds_restore h]

/-- `STORE_FAST` moves the top of the stack into the local, and a following `LOAD_FAST`
reads back what was stored. `:323-330`. -/
def StoreFastRules : Prop := ∀ (e : Env) (regs : Regs) (v : Val) (rest : List Val),
  e.oparg < regs.frame.fast.size →
    execOp e .STORE_FAST { regs := regs, stack := v :: rest } =
      .ok () (withLocal { regs := regs, stack := rest } e.oparg v) ∧
    (execOp e .STORE_FAST *> execOp e .LOAD_FAST) { regs := regs, stack := v :: rest } =
      .ok () (withLocal { regs := regs, stack := v :: rest } e.oparg v)

theorem storeFastRules_proven : StoreFastRules := by
  intro e regs v rest hi
  refine ⟨storeFast_ok e regs v rest, ?_⟩
  simp only [SeqRight.seqRight, EStateM.seqRight, storeFast_ok]
  have h : (withLocal { regs := regs, stack := rest } e.oparg v).regs.frame.fast[e.oparg]? = some v := by
    simp [withLocal, Array.getElem?_setIfInBounds, hi]
  rw [(loadFastPushes_proven e _ v h).1]
  rfl

/-! ### Superinstructions -/

/-- `oparg >> 4` and `oparg & 15`, the two operands of a superinstruction. -/
abbrev hi (e : Env) : Env := { e with oparg := e.oparg >>> 4 }
abbrev lo (e : Env) : Env := { e with oparg := e.oparg &&& 15 }

/-- The superinstructions are the pair the compiler combined (`Python/flowgraph.c`,
`insert_superinstructions`): `:298-310`, `:336-357`. -/
def SuperinstructionsExpand : Prop := ∀ (e : Env) (s : St) (a b : Val),
  s.regs.frame.fast[e.oparg >>> 4]? = some a → s.regs.frame.fast[e.oparg &&& 15]? = some b →
    execOp e .LOAD_FAST_LOAD_FAST s = (execOp (hi e) .LOAD_FAST *> execOp (lo e) .LOAD_FAST) s ∧
    execOp e .LOAD_FAST_BORROW_LOAD_FAST_BORROW s =
      (execOp (hi e) .LOAD_FAST_BORROW *> execOp (lo e) .LOAD_FAST_BORROW) s

theorem superinstructionsExpand_proven : SuperinstructionsExpand := by
  intro e s a b ha hb
  have h1 := loadFastPushes_proven (hi e) s a ha
  have h2 := loadFastPushes_proven (lo e) { s with stack := a :: s.stack } b hb
  constructor
  · simp only [SeqRight.seqRight, EStateM.seqRight, h1.1, h2.1]
    show stk 0 2 _ s = _
    exact stk_ok (outs := [a, b]) (r := s.regs) (by simp)
      (by simp [bind, EStateM.bind, getLocal_ok ha, getLocal_ok hb, pure, EStateM.pure]) rfl
  · simp only [SeqRight.seqRight, EStateM.seqRight, h1.2, h2.2]
    show stk 0 2 _ s = _
    exact stk_ok (outs := [a, b]) (r := s.regs) (by simp)
      (by simp [bind, EStateM.bind, getLocal_ok ha, getLocal_ok hb, pure, EStateM.pure]) rfl

/-- `STORE_FAST_LOAD_FAST` and `STORE_FAST_STORE_FAST` expand the same way, in the order that
matters when both operands name the same local: the store comes first, and `oparg1` is written
before `oparg2`. -/
def StoreSuperExpand : Prop := ∀ (e : Env) (regs : Regs) (x y : Val) (rest : List Val) (b : Val),
    execOp e .STORE_FAST_STORE_FAST { regs := regs, stack := x :: y :: rest } =
      (execOp (hi e) .STORE_FAST *> execOp (lo e) .STORE_FAST)
        { regs := regs, stack := x :: y :: rest } ∧
    ((withLocal { regs := regs, stack := rest } (e.oparg >>> 4) x).regs.frame.fast[e.oparg &&& 15]?
        = some b →
      execOp e .STORE_FAST_LOAD_FAST { regs := regs, stack := x :: rest } =
        (execOp (hi e) .STORE_FAST *> execOp (lo e) .LOAD_FAST)
          { regs := regs, stack := x :: rest })

theorem storeSuperExpand_proven : StoreSuperExpand := by
  intro e regs x y rest b
  constructor
  · simp only [SeqRight.seqRight, EStateM.seqRight, storeFast_ok]
    show stk 2 0 _ _ = _
    rw [show execOp (lo e) .STORE_FAST
        (withLocal { regs := regs, stack := y :: rest } (hi e).oparg x)
        = execOp (lo e) .STORE_FAST
          { regs := (withLocal { regs := regs, stack := y :: rest } (hi e).oparg x).regs,
            stack := y :: rest } from rfl, storeFast_ok]
    exact stk_ok (outs := []) (r := _) (by simp)
      (by simp [setLocal, withLocal, bind, EStateM.bind, pure, EStateM.pure]) rfl
  · intro hb
    simp only [SeqRight.seqRight, EStateM.seqRight, storeFast_ok]
    rw [(loadFastPushes_proven (lo e) _ b hb).1]
    show stk 1 1 _ _ = _
    refine stk_ok (outs := [b]) (r := (withLocal { regs := regs, stack := rest } (e.oparg >>> 4) x).regs)
      (by simp) ?_ rfl
    have : getLocal (e.oparg &&& 15) (withLocal { regs := regs, stack := rest } (e.oparg >>> 4) x).regs
        = .ok b (withLocal { regs := regs, stack := rest } (e.oparg >>> 4) x).regs := getLocal_ok hb
    have hs : setLocal (e.oparg >>> 4) x regs =
        .ok () (withLocal { regs := regs, stack := rest } (e.oparg >>> 4) x).regs := rfl
    show (do setLocal (e.oparg >>> 4) x; pure [← getLocal (e.oparg &&& 15)]) regs = _
    simp only [bind, EStateM.bind, hs, this, pure, EStateM.pure]

/-! ### Deleting a local -/

/-- `DELETE_FAST` unbinds a bound local, leaving the stack alone. On a local that is already
unbound it raises the same `UnboundLocalError` as `LOAD_FAST_CHECK`, with the stack unchanged:
the two share the check at `:2354-2362` and `:271-279`. -/
def DeleteFastRules : Prop := ∀ (e : Env) (s : St) (v : Val) (c : Code),
  s.regs.frame.fast[e.oparg]? = some v → e.P[s.regs.frame.code]? = some c →
    (v ≠ .null → execOp e .DELETE_FAST s = .ok () (withLocal s e.oparg .null)) ∧
    (v = .null → ∀ x rt,
      (raiseS "UnboundLocalError" (unboundLocalMsg (c.localsplusnames.getD e.oparg "")) : RM Unit)
        s.regs.rt = .error x rt →
      execOp e .DELETE_FAST s = .error x { s with regs := { s.regs with rt := rt } })

theorem deleteFastRules_proven : DeleteFastRules := by
  intro e s v c h hc
  constructor
  · intro hne
    have hb : (v == Val.null) = false := by simpa using hne
    show stk 0 0 _ s = _
    exact stk_ok (outs := []) (r := _) (by simp)
      (by simp [bind, EStateM.bind, getLocal_ok h, hb, setLocal, withLocal, pure, EStateM.pure]) rfl
  · intro hn x rt hr
    subst hn
    simp only [Array.getD_eq_getD_getElem?] at hr
    show stk 0 0 _ s = _
    exact stk_err (by simp) (by
      simp [bind, EStateM.bind, getLocal_ok h, getCode_ok hc, liftM, monadLift, MonadLift.monadLift,
        RM.lift, formatExcCheckArg, hr])

/-! ### Constants -/

/-- `LOAD_CONST` pushes `co_consts[oparg]` and `LOAD_SMALL_INT` pushes the int `oparg` itself:
`:312-321`. -/
def LoadConstRules : Prop := ∀ (e : Env) (s : St) (c : Code) (k : Val),
  e.P[s.regs.frame.code]? = some c → c.consts[e.oparg]? = some k →
    execOp e .LOAD_CONST s = .ok () { s with stack := k :: s.stack } ∧
    execOp e .LOAD_SMALL_INT s = .ok () { s with stack := .int e.oparg :: s.stack }

theorem loadConstRules_proven : LoadConstRules := by
  intro e s c k hc hk
  constructor
  · show stk 0 1 _ s = _
    exact stk_ok (outs := [k]) (r := s.regs) (by simp)
      (by simp [bind, EStateM.bind, getConst, getCode_ok hc, hk, pure, EStateM.pure]) rfl
  · show stk 0 1 _ s = _
    exact stk_ok (outs := [.int e.oparg]) (r := s.regs) (by simp) rfl rfl

/-! ### The stack -/

/-- `POP_TOP`, `END_FOR` and `POP_ITER` drop what they name and `PUSH_NULL` pushes NULL, and
pushing then popping changes nothing. `END_SEND` keeps the value and drops what was below it:
`:359-361`, `:389-407`, `:428-434`. -/
def StackDrops : Prop := ∀ (e : Env) (regs : Regs) (a b c : Val) (rest : List Val),
    execOp e .POP_TOP { regs := regs, stack := a :: rest } = .ok () { regs := regs, stack := rest } ∧
    execOp e .END_FOR { regs := regs, stack := a :: rest } = .ok () { regs := regs, stack := rest } ∧
    execOp e .POP_ITER { regs := regs, stack := a :: b :: rest } =
      .ok () { regs := regs, stack := rest } ∧
    execOp e .END_SEND { regs := regs, stack := a :: b :: c :: rest } =
      .ok () { regs := regs, stack := a :: rest } ∧
    (execOp e .PUSH_NULL *> execOp e .POP_TOP) { regs := regs, stack := rest } =
      .ok () { regs := regs, stack := rest }

theorem stackDrops_proven : StackDrops := by
  intro e regs a b c rest
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show stk 1 0 _ _ = _
    exact stk_ok (outs := []) (r := regs) (by simp) rfl rfl
  · show stk 1 0 _ _ = _
    exact stk_ok (outs := []) (r := regs) (by simp) rfl rfl
  · show stk 2 0 _ _ = _
    exact stk_ok (outs := []) (r := regs) (by simp) rfl rfl
  · show stk 3 1 _ _ = _
    exact stk_ok (outs := [a]) (r := regs) (by simp) rfl rfl
  · have h : execOp e .PUSH_NULL { regs := regs, stack := rest } =
        .ok () { regs := regs, stack := .null :: rest } := by
      show stk 0 1 _ _ = _
      exact stk_ok (outs := [.null]) (r := regs) (by simp) rfl rfl
    simp only [SeqRight.seqRight, EStateM.seqRight, h]
    show stk 1 0 _ _ = _
    exact stk_ok (outs := []) (r := regs) (by simp) rfl rfl

/-- `COPY n` pushes a duplicate of the `n`th item from the top, leaving the rest in place:
`:5906-5908`. -/
def CopyRules : Prop := ∀ (e : Env) (regs : Regs) (top : List Val) (b : Val) (rest : List Val),
  top.length + 1 = e.oparg →
    execOp e .COPY { regs := regs, stack := top ++ b :: rest } =
      .ok () { regs := regs, stack := b :: top ++ b :: rest }

theorem take_app {α : Type} (top : List α) (b : α) (rest : List α) :
    (top ++ b :: rest).take (top.length + 1) = top ++ [b] := by
  induction top with
  | nil => simp
  | cons x xs ih => simpa using ih

theorem drop_app {α : Type} (top : List α) (b : α) (rest : List α) :
    (top ++ b :: rest).drop (top.length + 1) = rest := by
  induction top with
  | nil => simp
  | cons x xs ih => simpa using ih

theorem copyRules_proven : CopyRules := by
  intro e regs top b rest h
  show stk _ _ _ _ = _
  have ht : ((top ++ b :: rest).take e.oparg).reverse = b :: top.reverse := by
    rw [← h, take_app]; simp
  have hd : (top ++ b :: rest).drop e.oparg = rest := by rw [← h, drop_app]
  refine (stk_ok (outs := b :: top.reverse ++ [b]) (r := regs) (by simp; omega) ?_
    (by simp; omega)).trans ?_
  · simp only [ht]
    rfl
  · simp only [hd]
    simp

/-- `SWAP n` exchanges the top with the `n`th item and touches nothing else, so doing it twice
changes nothing: `:5942-5947`. -/
def SwapRules : Prop := ∀ (e : Env) (regs : Regs) (t b : Val) (mid rest : List Val),
  mid.length + 2 = e.oparg →
    execOp e .SWAP { regs := regs, stack := t :: mid ++ b :: rest } =
      .ok () { regs := regs, stack := b :: mid ++ t :: rest } ∧
    (execOp e .SWAP *> execOp e .SWAP) { regs := regs, stack := t :: mid ++ b :: rest } =
      .ok () { regs := regs, stack := t :: mid ++ b :: rest }

theorem swap_step (e : Env) (regs : Regs) (t b : Val) (mid rest : List Val)
    (h : mid.length + 2 = e.oparg) :
    execOp e .SWAP { regs := regs, stack := t :: mid ++ b :: rest } =
      .ok () { regs := regs, stack := b :: mid ++ t :: rest } := by
  show stk _ _ _ _ = _
  have ht : ((t :: mid ++ b :: rest).take e.oparg).reverse = b :: mid.reverse ++ [t] := by
    rw [← h]
    have := take_app (t :: mid) b rest
    simp only [List.cons_append, List.length_cons] at this ⊢
    simp [this]
  have hd : (t :: mid ++ b :: rest).drop e.oparg = rest := by
    rw [← h]
    have := drop_app (t :: mid) b rest
    simpa using this
  refine (stk_ok (outs := t :: mid.reverse ++ [b]) (r := regs) (by simp; omega) ?_
    (by simp; omega)).trans ?_
  · have hl : (mid.reverse ++ [t]).getLastD b = t := by simp [List.getLastD_eq_getLast?]
    simp only [ht]
    simp [hl, pure, EStateM.pure]
  · simp only [hd]
    simp

theorem swapRules_proven : SwapRules := by
  intro e regs t b mid rest h
  refine ⟨swap_step e regs t b mid rest h, ?_⟩
  simp only [SeqRight.seqRight, EStateM.seqRight, swap_step e regs t b mid rest h]
  exact swap_step e regs b t mid rest h

/-! ### Jumps -/

/-- `next_instr` after `JUMPBY(oparg)`. -/
abbrev jumped (s : St) (d : Int) : St :=
  { s with regs := { s.regs with next := ((s.regs.next : Int) + d).toNat } }

/-- The eval breaker with its pending event consumed. -/
abbrev consumed (regs : Regs) (rt : Rt) : Regs := { regs with rt := rt }

/-- `JUMP_FORWARD` adds `oparg` to `next_instr` and `JUMP_BACKWARD_NO_INTERRUPT` subtracts it,
neither touches the stack, and neither handles a pending event, whatever is pending: the
`yield from` loop deliberately leaves it for the innermost generator (`:3657-3661`, bpo-30039).
`JUMP_BACKWARD` is `_CHECK_PERIODIC + JUMP_BACKWARD_NO_INTERRUPT` (`:3544-3548`): with nothing
pending it jumps back, and when `_Py_HandlePending` fails it leaves through `ERROR_IF` (`:157-160`)
with the stack as it was and without jumping, raising what the handler raised (after the
implicit chaining of `_PyErr_SetObject`). A jump forward and back returns to the start.
`:3494-3496`. A compiled backward jump never leaves the code, the `assert(oparg <=
INSTR_OFFSET())` of `:3662`, which is the hypothesis `oparg ≤ next`. -/
def JumpRules : Prop := ∀ (e : Env) (s : St),
    execOp e .JUMP_FORWARD s = .ok () (jumped s e.oparg) ∧
    (e.oparg ≤ s.regs.next →
      execOp e .JUMP_BACKWARD_NO_INTERRUPT s = .ok () (jumped s (-(e.oparg : Int))) ∧
      (s.regs.rt.pendingExc = .null →
        execOp e .JUMP_BACKWARD s = .ok () (jumped s (-(e.oparg : Int)))) ∧
      (∀ x rt, s.regs.rt.pendingExc ≠ .null →
        setObject s.regs.rt.pendingExc { s.regs.rt with pendingExc := .null } = .ok x rt →
        execOp e .JUMP_BACKWARD s = .error (.exc x) ⟨consumed s.regs rt, s.stack⟩)) ∧
    (execOp e .JUMP_FORWARD *> execOp e .JUMP_BACKWARD_NO_INTERRUPT) s = .ok () s

theorem jumpRules_proven : JumpRules := by
  intro e s
  refine ⟨rfl, fun _ => ⟨rfl, fun hp => ?_, fun x rt hp hx => ?_⟩, ?_⟩
  · simp [execOp, JUMP_BACKWARD, _SPECIALIZE_JUMP_BACKWARD, _CHECK_PERIODIC, checkPeriodics, hp,
      JUMP_BACKWARD_NO_INTERRUPT, bind, EStateM.bind, BM.lift, RM.lift, liftM, monadLift,
      MonadLift.monadLift, pure, EStateM.pure, jumpBy]
  · have hb : (s.regs.rt.pendingExc == .null) = false := by simpa using hp
    simp [execOp, JUMP_BACKWARD, _SPECIALIZE_JUMP_BACKWARD, _CHECK_PERIODIC, checkPeriodics, hb,
      raiseVal, hx, bind, EStateM.bind, BM.lift, RM.lift, liftM, monadLift, MonadLift.monadLift, pure,
      EStateM.pure, throw, throwThe, MonadExcept.throw, EStateM.throw, MonadExceptOf.throw]
  · cases s with
    | mk regs stack =>
      cases regs with
      | mk rt frame prev next =>
        show EStateM.Result.ok () _ = _
        congr 2
        simp only [Regs.mk.injEq, and_self, and_true, true_and]
        omega

/-- Where a conditional branch leaves `next_instr`: `oparg` further on if taken, otherwise one
further if the next instruction is the `NOT_TAKEN` that marks the fall-through,
`JUMPBY(flag ? oparg : next_instr->op.code == NOT_TAKEN)`, `:3626` and `:3634`. -/
def branched (s : St) (c : Code) (oparg : Nat) (taken : Bool) : Nat :=
  if taken then s.regs.next + oparg
  else if (c.instrs[s.regs.next]?.map (·.op)) == some .NOT_TAKEN then s.regs.next + 1
  else s.regs.next

/-- The state after a conditional branch that popped the condition. -/
abbrev afterBranch (regs : Regs) (rest : List Val) (c : Code) (oparg : Nat) (taken : Bool) : St :=
  { regs := { regs with next := branched { regs := regs, stack := rest } c oparg taken },
    stack := rest }

theorem jumpIf_ok (e : Env) (regs : Regs) (rest : List Val) (c : Code) (flag : Bool)
    (hc : e.P[regs.frame.code]? = some c) :
    jumpIf e flag regs =
      .ok () { regs with next := branched { regs := regs, stack := rest } c e.oparg flag } := by
  have hn : nextIsNotTaken e regs =
      .ok ((c.instrs[regs.next]?.map (·.op)) == some Op.NOT_TAKEN) regs := by
    simp [nextIsNotTaken, bind, EStateM.bind, getCode_ok hc, getNext, pure, EStateM.pure]
  cases flag with
  | true =>
    show jumpBy e.oparg regs = _
    simp only [jumpBy, branched, ite_true]
    simp only [EStateM.Result.ok.injEq, true_and, Regs.mk.injEq, and_true]
    omega
  | false =>
    show EStateM.bind (nextIsNotTaken e)
      (fun x => if x = true then jumpBy 1 else pure ()) regs = _
    simp only [EStateM.bind, hn]
    by_cases h : (c.instrs[regs.next]?.map (·.op)) == some Op.NOT_TAKEN
    · simp only [h, ite_true, branched, Bool.false_eq_true, ite_false, jumpBy]
      simp
    · simp only [h, Bool.false_eq_true, ite_false, branched, pure, EStateM.pure]

/-- `POP_JUMP_IF_TRUE` jumps on `True`, `POP_JUMP_IF_FALSE` on `False`, `POP_JUMP_IF_NONE` when
the value is `None` and `POP_JUMP_IF_NOT_NONE` when it is not. Each pops what it tests and
touches nothing else: `:3621-3654`. -/
def BranchRules : Prop := ∀ (e : Env) (regs : Regs) (rest : List Val) (c : Code) (b : Bool) (v : Val),
  e.P[regs.frame.code]? = some c →
    execOp e .POP_JUMP_IF_TRUE { regs := regs, stack := .bool b :: rest } =
      .ok () (afterBranch regs rest c e.oparg b) ∧
    execOp e .POP_JUMP_IF_FALSE { regs := regs, stack := .bool b :: rest } =
      .ok () (afterBranch regs rest c e.oparg !b) ∧
    execOp e .POP_JUMP_IF_NONE { regs := regs, stack := v :: rest } =
      .ok () (afterBranch regs rest c e.oparg (v == .none)) ∧
    execOp e .POP_JUMP_IF_NOT_NONE { regs := regs, stack := v :: rest } =
      .ok () (afterBranch regs rest c e.oparg !(v == .none))

theorem popJumpTrue_ok (e : Env) (regs : Regs) (rest : List Val) (c : Code) (b : Bool)
    (hc : e.P[regs.frame.code]? = some c) :
    _POP_JUMP_IF_TRUE e { regs := regs, stack := .bool b :: rest } =
      .ok () (afterBranch regs rest c e.oparg b) := by
  refine stk_ok (outs := [])
    (r := { regs with next := branched { regs := regs, stack := rest } c e.oparg b }) (by simp) ?_ rfl
  show (do jumpIf e b; pure []) regs = _
  simp only [bind, EStateM.bind, jumpIf_ok e regs rest c b hc, pure, EStateM.pure]

theorem popJumpFalse_ok (e : Env) (regs : Regs) (rest : List Val) (c : Code) (b : Bool)
    (hc : e.P[regs.frame.code]? = some c) :
    _POP_JUMP_IF_FALSE e { regs := regs, stack := .bool b :: rest } =
      .ok () (afterBranch regs rest c e.oparg !b) := by
  refine stk_ok (outs := [])
    (r := { regs with next := branched { regs := regs, stack := rest } c e.oparg !b }) (by simp) ?_ rfl
  show (do jumpIf e !b; pure []) regs = _
  simp only [bind, EStateM.bind, jumpIf_ok e regs rest c (!b) hc, pure, EStateM.pure]

theorem branchRules_proven : BranchRules := by
  intro e regs rest c b v hc
  have hnone : _IS_NONE { regs := regs, stack := v :: rest } =
      .ok () { regs := regs, stack := .bool (v == .none) :: rest } :=
    stk_ok (outs := [.bool (v == .none)]) (r := regs) (by simp) rfl rfl
  refine ⟨popJumpTrue_ok e regs rest c b hc, popJumpFalse_ok e regs rest c b hc, ?_, ?_⟩
  · show (do _IS_NONE; _POP_JUMP_IF_TRUE e) _ = _
    simp only [bind, EStateM.bind, hnone]
    exact popJumpTrue_ok e regs rest c _ hc
  · show (do _IS_NONE; _POP_JUMP_IF_FALSE e) _ = _
    simp only [bind, EStateM.bind, hnone]
    exact popJumpFalse_ok e regs rest c _ hc

/-- `UNARY_NOT` on a bool flips it, so doing it twice changes nothing: `:477`. The compiler
guarantees the operand is a bool, because `TO_BOOL` precedes it. -/
def UnaryNotRules : Prop := ∀ (e : Env) (regs : Regs) (b : Bool) (rest : List Val),
    execOp e .UNARY_NOT { regs := regs, stack := .bool b :: rest } =
      .ok () { regs := regs, stack := .bool (!b) :: rest } ∧
    (execOp e .UNARY_NOT *> execOp e .UNARY_NOT) { regs := regs, stack := .bool b :: rest } =
      .ok () { regs := regs, stack := .bool b :: rest }

theorem unaryNot_ok (e : Env) (regs : Regs) (b : Bool) (rest : List Val) :
    execOp e .UNARY_NOT { regs := regs, stack := .bool b :: rest } =
      .ok () { regs := regs, stack := .bool (!b) :: rest } :=
  stk_ok (outs := [.bool !b]) (r := regs) (by simp) rfl rfl

theorem unaryNotRules_proven : UnaryNotRules := by
  intro e regs b rest
  refine ⟨unaryNot_ok e regs b rest, ?_⟩
  simp only [SeqRight.seqRight, EStateM.seqRight, unaryNot_ok, Bool.not_not]

end PyLean.Bytecode
