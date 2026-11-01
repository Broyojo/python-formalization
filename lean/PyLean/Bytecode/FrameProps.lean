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

theorem pushPop_proven : PushPop := by
  intro s k h0 h1 hk
  have hu : asU64 s = s.toNat := by
    unfold asU64
    rw [Int.emod_eq_of_lt h0 (by omega)]
  have hn : ¬ WILL_OVERFLOW ≤ asU64 s := by
    rw [hu]; unfold WILL_OVERFLOW; omega
  simp only [pushValue, hn, ↓reduceIte, popValue, topOfStack]
  constructor
  · rw [Int.fdiv_eq_ediv_of_dvd_or_pos]
    all_goals omega
  · rw [Int.fmod_eq_emod_of_nonneg _ (by decide)]
    omega

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

/-- `self_or_null` of `LOAD_SPECIAL` can be `NULL` (`Python/bytecodes.c:3502`), so a jump
from a `with` body must not land where an object is required. False: the analysis
gives the slot kind `Object` and accepts the jump. -/
def JumpKeepsObjects : Prop :=
  peek withBodyStack 1 = Null ∨ compatibleStack withBodyStack exprStack = false

theorem jumpKeepsObjects_refuted : ¬JumpKeepsObjects := by
  intro h
  rcases h with h | h
  · exact absurd h (by decide)
  · exact absurd h (by decide)

/-- `first_line_not_before` returns a line that is really in the table and not before
the request, or `-1` when no such line exists. -/
def FirstLine : Prop :=
  ∀ (lines : Array Int) (line : Int), 0 ≤ line →
    let r := firstLineNotBefore lines line
    r = -1 ∨ (r ∈ lines.toList ∧ line ≤ r)

theorem firstLine_proven : FirstLine := by
  intro lines line h
  simp only [firstLineNotBefore]
  rw [← Array.foldl_toList]
  have key : ∀ (l : List Int) (acc : Option Int),
      (∀ x, acc = some x → x ∈ lines.toList ∧ line ≤ x) →
      (∀ x ∈ l, x ∈ lines.toList) →
      ∀ x, l.foldl (fun acc l => if l ≥ line && (acc == none || some l < acc) then some l else acc) acc = some x →
        x ∈ lines.toList ∧ line ≤ x := by
    intro l
    induction l with
    | nil => intro acc h1 _ x hx; exact h1 x hx
    | cons a t ih =>
      intro acc h1 h2 x hx
      simp only [List.foldl_cons] at hx
      refine ih _ ?_ (fun y hy => h2 y (by simp [hy])) x hx
      intro y hy
      split at hy
      · rename_i hc
        simp only [Option.some.injEq] at hy
        subst hy
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        exact ⟨h2 _ (by simp), hc.1⟩
      · exact h1 y hy
  cases hr : lines.toList.foldl (fun acc l => if l ≥ line && (acc == none || some l < acc) then some l else acc) (none : Option Int) with
  | none => left; simp
  | some x =>
    right
    have := key lines.toList none (by simp) (fun _ h => h) x hr
    simpa using this

end PyLean.Bytecode.FrameObj
