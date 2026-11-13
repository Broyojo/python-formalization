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

/-- What remains true: on a stack of at most ten entries `stack_swap` is a swap. `peek`
reads the entries in push order: nothing on the empty stack, the kind just pushed at depth 1
and every earlier entry one deeper. Read back through it, `stack_swap s n` has the old
entry `n` on top, the old top at depth `n`, and every other depth as it was, so the
narrowing of the return value loses nothing here.

Hypotheses. `1 ≤ n` is the assert at line 1242; `s < 2 ^ 30` and `n ≤ 10` say the stack and
the depth stay within ten entries, and `StackSwapKeepsStack` above is the record of what
happens beyond that. `1 ≤ m` is the assert of `peek`, line 1235, and `m ≤ 21` is
`MAX_STACK_ENTRIES`, line 1202, the deepest entry a stack can hold. `0 ≤ s`, `s < 2 ^ 60`
and `k < 8` select the branch of `push_value` that pushes, with a three-bit kind; its
result is a non-negative `int64_t`, so the 21 entries read back determine it. The branch
that returns `OVERFLOWED` is not part of this statement. `top_of_stack` is `peek` at depth
1 on every stack, which is how `stack_swap` reads the old top.

The last conjunct is the earlier form of this entry, kept so that nothing it said is
dropped. It compares the model with its own 64-bit helper and pins no behaviour by itself. -/
def StackSwapShallow : Prop :=
  (∀ m, 1 ≤ m → m ≤ 21 → peek EMPTY_STACK m = 0) ∧
  (∀ (s : Int) (k m : Nat), 0 ≤ s → s < 2 ^ 60 → k < 8 → 1 ≤ m → m + 1 ≤ 21 →
    (0 ≤ pushValue s k ∧ pushValue s k < 2 ^ 63) ∧
      peek (pushValue s k) 1 = k ∧ peek (pushValue s k) (m + 1) = peek s m) ∧
  (∀ s : Int, topOfStack s = peek s 1) ∧
  (∀ (s : Int) (n m : Nat), 0 ≤ s → s < 2 ^ 30 → 1 ≤ n → n ≤ 10 → 1 ≤ m → m ≤ 21 →
    peek (stackSwap s n) m =
      if m = 1 then peek s n else if m = n then peek s 1 else peek s m) ∧
  ∀ (s : Int) (n : Nat), 0 ≤ stackSwap64 s n → stackSwap64 s n < 2 ^ 32 →
    stackSwap s n = stackSwap64 s n

/-- `peek` with the shift and the mask as a division and a remainder. -/
theorem peek_eq (s : Int) (m : Nat) :
    peek s m = ((s / (2 : Int) ^ (3 * (m - 1))) % 8).toNat := by
  unfold peek
  rw [Int.fdiv_eq_ediv_of_nonneg _ (Int.pow_nonneg (by decide)),
    Int.fmod_eq_emod_of_nonneg _ (by decide)]

/-- Below the bottom of a stack of at most ten entries `peek` reads kind 0. -/
theorem peek_deep (x : Int) (m : Nat) (h0 : 0 ≤ x) (h1 : x < 2 ^ 30) (hm : 11 ≤ m) :
    peek x m = 0 := by
  rw [peek_eq]
  obtain ⟨j, hj⟩ : ∃ j, 3 * (m - 1) = 30 + j := ⟨3 * (m - 1) - 30, by omega⟩
  have hp : (0 : Int) < (2 : Int) ^ j := Int.pow_pos (by decide)
  have hlt : x < (2 : Int) ^ (3 * (m - 1)) := by
    rw [hj, Int.pow_add]
    simp only [Int.reducePow] at h1 ⊢
    omega
  rw [Int.ediv_eq_zero_of_lt h0 hlt]
  rfl

/-- The model's 64-bit helper `stackSwap64` in closed form: with `d` the entry at depth `n`
and `t` the top, the entry at depth `n` gains `t - d` and the top loses it. This is
arithmetic on the helper, for every `Int` and depth; it says nothing about C where C's
`int` shifts overflow (`n > 10`). -/
theorem stackSwap64_eq (s : Int) (n : Nat) :
    stackSwap64 s n =
      s + (s % 8 - s / (2 : Int) ^ (3 * (n - 1)) % 8) * ((2 : Int) ^ (3 * (n - 1)) - 1) := by
  unfold stackSwap64 topOfStack
  simp only [peek_eq]
  rw [Int.fmod_eq_emod_of_nonneg _ (by decide), Int.fmod_eq_emod_of_nonneg _ (by decide),
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide)),
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))]
  generalize hd : s / (2 : Int) ^ (3 * (n - 1)) % 8 = d
  generalize ht : s % 8 = t
  -- the low three bits of `replaced_low` are still the top
  have hx : (s - d * (2 : Int) ^ (3 * (n - 1)) + t * (2 : Int) ^ (3 * (n - 1))) % 8 = t := by
    by_cases h1 : 3 * (n - 1) = 0
    · rw [h1] at hd ⊢
      simp only [Int.pow_zero, Int.mul_one, Int.ediv_one] at hd ⊢
      omega
    · obtain ⟨j, hj⟩ : ∃ j, 3 * (n - 1) = 3 + j := ⟨3 * (n - 1) - 3, by omega⟩
      rw [hj, Int.pow_add]
      generalize (2 : Int) ^ j = p
      have e : s - d * ((2 : Int) ^ 3 * p) + t * ((2 : Int) ^ 3 * p) = s + 8 * ((t - d) * p) := by
        rw [Int.sub_mul, Int.mul_sub]
        simp only [Int.reducePow]
        rw [Int.mul_left_comm 8, Int.mul_left_comm 8, Int.mul_left_comm d 8,
          Int.mul_left_comm t 8]
        omega
      rw [e, Int.add_mul_emod_self_left]
      exact ht
  rw [hx, Int.sub_mul, Int.mul_sub, Int.mul_sub]
  omega

/-- The ten entries of a shallow stack, `d0` on top. -/
theorem digits10 (s : Int) (h0 : 0 ≤ s) (h1 : s < 2 ^ 30) :
    ∃ d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 : Int,
      (0 ≤ d0 ∧ d0 < 8) ∧ (0 ≤ d1 ∧ d1 < 8) ∧ (0 ≤ d2 ∧ d2 < 8) ∧ (0 ≤ d3 ∧ d3 < 8) ∧
      (0 ≤ d4 ∧ d4 < 8) ∧ (0 ≤ d5 ∧ d5 < 8) ∧ (0 ≤ d6 ∧ d6 < 8) ∧ (0 ≤ d7 ∧ d7 < 8) ∧
      (0 ≤ d8 ∧ d8 < 8) ∧ (0 ≤ d9 ∧ d9 < 8) ∧
      s = d0 + 8 * d1 + 64 * d2 + 512 * d3 + 4096 * d4 + 32768 * d5 + 262144 * d6 +
        2097152 * d7 + 16777216 * d8 + 134217728 * d9 := by
  refine ⟨s % 8, s / 8 % 8, s / 64 % 8, s / 512 % 8, s / 4096 % 8, s / 32768 % 8,
    s / 262144 % 8, s / 2097152 % 8, s / 16777216 % 8, s / 134217728 % 8, ?_⟩
  simp only [Int.reducePow] at h1
  omega

set_option maxHeartbeats 4000000 in
theorem stackSwapShallow_proven : StackSwapShallow := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro m _ _
    rw [peek_eq]; simp [EMPTY_STACK]
  · intro s k m h0 h1 hk hm _
    have hpush : pushValue s k = s * 8 + k := by
      unfold pushValue asU64 WILL_OVERFLOW
      rw [ite_eq_right (by omega)]
    rw [hpush, peek_eq, peek_eq, peek_eq]
    refine ⟨by omega, ?_, ?_⟩
    · simp only [Nat.sub_self, Nat.mul_zero, Int.pow_zero, Int.ediv_one]; omega
    · have e : 3 * (m + 1 - 1) = 3 + 3 * (m - 1) := by omega
      rw [e, Int.pow_add, ← Int.ediv_ediv_of_nonneg (by decide)]
      have : (s * 8 + (k : Int)) / (2 : Int) ^ 3 = s := by omega
      rw [this]
  · intro s
    rw [peek_eq]
    simp only [topOfStack, Int.fmod_eq_emod_of_nonneg _ (show (0 : Int) ≤ 8 by decide),
      Nat.sub_self, Nat.mul_zero, Int.pow_zero, Int.ediv_one]
  · intro s n m h0 h1 hn hn' hm _
    have hN : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 := by
      omega
    obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, hs⟩ :=
      digits10 s h0 h1
    -- entry `i + 1` of `s`, counted from the top, is `d i`
    have q0 : s % 8 = d0 := by subst hs; omega
    have q1 : s / 8 % 8 = d1 := by subst hs; omega
    have q2 : s / 64 % 8 = d2 := by subst hs; omega
    have q3 : s / 512 % 8 = d3 := by subst hs; omega
    have q4 : s / 4096 % 8 = d4 := by subst hs; omega
    have q5 : s / 32768 % 8 = d5 := by subst hs; omega
    have q6 : s / 262144 % 8 = d6 := by subst hs; omega
    have q7 : s / 2097152 % 8 = d7 := by subst hs; omega
    have q8 : s / 16777216 % 8 = d8 := by subst hs; omega
    have q9 : s / 134217728 % 8 = d9 := by subst hs; omega
    -- the swapped stack still has at most ten entries, so the narrowing on return keeps it
    have hfit : 0 ≤ stackSwap64 s n ∧ stackSwap64 s n < 2 ^ 30 := by
      rw [stackSwap64_eq s n]
      rcases hN with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [Nat.reduceSub, Nat.reduceMul, Int.reducePow, Int.pow_zero, Int.ediv_one,
          Int.reduceSub, q0, q1, q2, q3, q4, q5, q6, q7, q8, q9] <;> omega
    have hnarrow : stackSwap s n = stackSwap64 s n := by
      have key : stackSwap s n = Int.fmod (stackSwap64 s n) ((2 : Int) ^ 32) := rfl
      rw [key, Int.fmod_eq_emod_of_nonneg _ (by decide)]
      exact Int.emod_eq_of_lt hfit.1 (Int.lt_trans hfit.2 (by decide))
    rw [hnarrow]
    by_cases hm' : 11 ≤ m
    · rw [peek_deep _ m hfit.1 hfit.2 hm', ite_eq_right (by omega), ite_eq_right (by omega),
        peek_deep _ m h0 h1 hm']
    · have hM : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 ∨ m = 10 := by
        omega
      clear hfit hnarrow h0 h1
      rw [stackSwap64_eq s n]
      simp only [peek_eq]
      rcases hN with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        rcases hM with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [Nat.reduceSub, Nat.reduceMul, Int.reducePow, Int.pow_zero, Int.ediv_one,
          Int.reduceSub, Nat.reduceEqDiff, reduceIte, q0, q1, q2, q3, q4, q5, q6, q7, q8, q9] <;>
        clear q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 <;> subst hs <;> refine congrArg Int.toNat ?_ <;> omega
  · intro s n h0 h1
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
