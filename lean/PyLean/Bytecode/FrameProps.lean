import PyLean.Bytecode.FrameObj

/-!
Properties of the stack-kind analysis behind `frame.f_lineno = n`.
-/

namespace PyLean.Bytecode.FrameObj

/-- `compatible_kind`: nothing goes to kind 0, `NULL` never goes to `Object`, anything
goes to `Null`, and otherwise the kinds must be equal. -/
def CompatibleKind : Prop :=
  (∀ k, compatibleKind k 0 = false) ∧ compatibleKind Null Object = false ∧
  (∀ k, compatibleKind k Null = true) ∧
  (∀ k, k ≠ Null → compatibleKind k Object = true) ∧
  compatibleKind Iterator Except = false ∧ compatibleKind Lasti Except = false

theorem compatibleKind_proven : CompatibleKind := by
  refine ⟨?_, by decide, ?_, ?_, by decide, by decide⟩
  · intro k; simp [compatibleKind]
  · intro k; simp [compatibleKind, Null, Object]
  · intro k hk; simp [compatibleKind, Object, Null] at hk ⊢; omega

/-- `pop_value` undoes `push_value` below the overflow threshold, and `top_of_stack`
reads the kind that was pushed. -/
def PushPop : Prop :=
  ∀ (s : Int) (k : Nat), 0 ≤ s → s < 2 ^ 60 → k < 8 →
    popValue (pushValue s k) = s ∧ topOfStack (pushValue s k) = k

/-- A stack that went to `OVERFLOWED` stays there. -/
def Overflowed : Prop :=
  (∀ k, pushValue OVERFLOWED k = OVERFLOWED) ∧ popValue OVERFLOWED = OVERFLOWED

theorem overflowed_proven : Overflowed := by
  constructor
  · intro k; simp [pushValue, OVERFLOWED, asU64, WILL_OVERFLOW]
  · decide

/-- `stack_swap` computes a 64-bit stack, as `mark_stacks` needs. False: the C
function's return type is `Kind`, and any stack of more than ten entries loses its
bottom. -/
def StackSwapKeepsStack : Prop :=
  ∀ (s : Int) (n : Nat), 0 ≤ s → 1 ≤ n → stackSwap s n = stackSwap64 s n

/-- Twelve `Iterator` entries. -/
def deepIters : Int := (List.range 12).foldl (fun s _ => pushValue s Iterator) 0

theorem stackSwapKeepsStack_refuted : ¬StackSwapKeepsStack := by
  intro h
  have := h deepIters 2 (by decide) (by decide)
  exact absurd this (by decide)

/-- What remains true: `stack_swap` is right while the result fits 32 bits, that is
for at most ten entries. -/
def StackSwapShallow : Prop :=
  ∀ (s : Int) (n : Nat), 0 ≤ stackSwap64 s n → stackSwap64 s n < 2 ^ 32 →
    stackSwap s n = stackSwap64 s n

theorem stackSwapShallow_proven : StackSwapShallow := by
  intro s n h0 h1
  have key : stackSwap s n = Int.fmod (stackSwap64 s n) ((2 : Int) ^ 32) := rfl
  rw [key, Int.fmod_eq_emod_of_nonneg _ (by decide)]
  exact Int.emod_eq_of_lt h0 h1

/-- `OVERFLOWED` survives a `SWAP`. False: the narrowing turns `-1` into a positive
stack of invalid kinds, and "stack is too deep to analyze" is lost. -/
def SwapKeepsOverflowed : Prop := ∀ n, 1 ≤ n → stackSwap OVERFLOWED n = OVERFLOWED

theorem swapKeepsOverflowed_refuted : ¬SwapKeepsOverflowed := by
  intro h
  exact absurd (h 2 (by decide)) (by decide)

/-- The stack of a `with` body as `mark_stacks` sees it: the context manager's
`__exit__` and its `self`, which `LOAD_SPECIAL` pushes through the `default:` case. -/
def withBodyStack : Int :=
  applyDelta (pushValue EMPTY_STACK Object) (stackEffect .LOAD_SPECIAL 1)

/-- Two ordinary values on the stack, as in the middle of `(a, b,\n c)`. -/
def exprStack : Int := pushValue (pushValue EMPTY_STACK Object) Object

/-- `self_or_null` of `LOAD_SPECIAL` can be `NULL` (`Python/bytecodes.c:4131`), so a jump
from a `with` body must not land where an object is required. False: the analysis
gives the slot kind `Object` and accepts the jump. -/
def JumpKeepsObjects : Prop :=
  peek withBodyStack 1 = Null ∨ compatibleStack withBodyStack exprStack = false

theorem jumpKeepsObjects_refuted : ¬JumpKeepsObjects := by
  intro h
  rcases h with h | h
  · exact absurd h (by decide)
  · exact absurd h (by decide)

/-- The body of `def victim(p=1, q=2):\n    x = [p,\n         q]\n    for i in x:\n
y = i\n    return 1`, as compiled by 3.15.2: one unit for each code unit of `co_code`, so the
inline caches are here as `CACHE`. -/
def loopCode : Array Unit' := #[
  ⟨.RESUME, 0⟩, ⟨.CACHE, 0⟩,
  ⟨.LOAD_FAST_BORROW, 0⟩, ⟨.LOAD_FAST_BORROW, 1⟩, ⟨.BUILD_LIST, 2⟩, ⟨.STORE_FAST, 2⟩,
  ⟨.LOAD_FAST, 2⟩, ⟨.GET_ITER, 0⟩, ⟨.CACHE, 0⟩,
  ⟨.FOR_ITER, 5⟩, ⟨.CACHE, 0⟩, ⟨.STORE_FAST, 3⟩,
  ⟨.LOAD_FAST, 3⟩, ⟨.STORE_FAST, 4⟩, ⟨.JUMP_BACKWARD, 7⟩, ⟨.CACHE, 0⟩,
  ⟨.END_FOR, 0⟩, ⟨.POP_ITER, 0⟩, ⟨.LOAD_SMALL_INT, 1⟩, ⟨.RETURN_VALUE, 0⟩]

/-- `marklines` on it, with the function on line 2. Line 3 starts twice: at `LOAD_FAST_BORROW p`
with an empty stack, and at `BUILD_LIST`, where it resumes after the continuation line. -/
def loopLines : Array Int := #[2, -1, 3, 4, 3, -1, 5, -1, -1, -1, -1, -1, 6, -1, -1, -1, 5, -1, 7, -1]

/-- The second output of `GET_ITER` is not an object: `_PyEval_GetIter` stores a tagged int
or `NULL` there (`Python/ceval.c:1136`, `:1139`). So no approved jump may keep that slot
where the target needs an object. When `start ≤ best` the loop at `Objects/frameobject.c:1825`
pops nothing, so the slots stay, and two `Iterator` entries on top are what `GET_ITER` leaves
(`:1396-1400`), which no other opcode pushes. Hypotheses: none on the code; the statement is
over every function, and `linenoDecide` is the decision `frame_lineno_set_impl` makes.
False since 3.15: `mark_stacks` calls the slot `Iterator`, and `compatible_kind` lets `Iterator`
flow into `Object`, so the jump below lands on `BUILD_LIST 2` with the iterable and the
index as operands, and CPython segfaults in `_PyList_FromStackRefStealOnSuccess`. -/
def JumpKeepsIterIndex : Prop :=
  ∀ (code : Array Unit') (table : Array Nat) (lines : Array Int) (first value : Int)
    (lasti addr : Nat) (best : Int),
    linenoDecide code table lines first value lasti = .ok addr best →
    let start := (markStacks code table).getD lasti UNINITIALIZED
    start ≤ best → peek start 1 = Iterator → peek start 2 = Iterator → peek best 1 ≠ Object

set_option maxRecDepth 100000 in
/-- From `y = i`, unit 12, to line 3. CPython reports `f_lasti` 8 after this jump, unit 4. -/
theorem loopJump : linenoDecide loopCode #[] loopLines 2 3 12 = .ok 4 27 := by decide

set_option maxRecDepth 100000 in
theorem loopStart : (markStacks loopCode #[]).getD 12 UNINITIALIZED = 9 := by decide

theorem jumpKeepsIterIndex_refuted : ¬JumpKeepsIterIndex := by
  intro h
  have := h loopCode #[] loopLines 2 3 12 4 27 loopJump
  simp only [loopStart] at this
  exact absurd rfl (this (by decide) (by decide) (by decide))

/-- `first_line_not_before` returns a line that is really in the table and not before
the request, or `-1` when no such line exists. -/
def FirstLine : Prop :=
  ∀ (lines : Array Int) (line : Int), 0 ≤ line →
    let r := firstLineNotBefore lines line
    r = -1 ∨ (r ∈ lines.toList ∧ line ≤ r)

theorem firstLine_proven : FirstLine := by
  intro lines line _
  simp only [firstLineNotBefore]
  rw [← Array.foldl_toList]
  -- the accumulator is always `none` or an in-range line not before `line`
  have inv : ∀ (l : List Int) (acc : Option Int),
      (∀ x, acc = some x → x ∈ lines.toList ∧ line ≤ x) →
      (∀ x ∈ l, x ∈ lines.toList) →
      ∀ x, l.foldl (fun acc v =>
        if v ≥ line then (match acc with | none => some v | some a => if v < a then some v else some a)
        else acc) acc = some x → x ∈ lines.toList ∧ line ≤ x := by
    intro l
    induction l with
    | nil => intro acc h _ x hx; exact h x hx
    | cons v t ih =>
      intro acc h1 h2 x hx
      simp only [List.foldl_cons] at hx
      refine ih _ ?_ (fun y hy => h2 y (by simp [hy])) x hx
      intro y hy
      by_cases hv : v ≥ line
      · simp only [hv, ↓reduceIte] at hy
        cases acc with
        | none => simp only [Option.some.injEq] at hy; subst hy; exact ⟨h2 v (by simp), hv⟩
        | some a =>
          by_cases hlt : v < a
          · simp only [hlt, ↓reduceIte, Option.some.injEq] at hy; subst hy; exact ⟨h2 v (by simp), hv⟩
          · simp only [hlt, ↓reduceIte] at hy; exact h1 y hy
      · simp only [hv, ↓reduceIte] at hy; exact h1 y hy
  cases hr : lines.toList.foldl (fun acc v =>
      if v ≥ line then (match acc with | none => some v | some a => if v < a then some v else some a)
      else acc) (none : Option Int) with
  | none => left; simp
  | some x => right; exact inv lines.toList none (by simp) (fun _ h => h) x hr

end PyLean.Bytecode.FrameObj
