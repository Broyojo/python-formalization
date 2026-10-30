import PyLean.Sequences.DequeOps

/-!
Deque properties: maxlen eviction, the documented rotation loop, copies and
concatenation.
-/

namespace PyLean.Sequences

open PyLean

/-- The deque end operations are the documented list operations, with
"items discarded from the opposite end" once a bounded deque is full
(Doc/library/collections.rst:475-481): for every deque satisfying the layout
invariant (type invariant `Deque.WF`, preserved by every operation), every
`x` and every iterable `xs` (other than the deque itself, which is
`extendSelf`):
`append`/`extend`/`d += xs`/`extend(d)` keep the last `maxlen` items of
`items + xs`, `appendleft`/`extendleft` keep the first `maxlen` of
`reversed(xs) + items`, `pop`/`popleft` remove the last/first item (or raise
`IndexError` on an empty deque), and `deque(xs, maxlen)` holds the last
`maxlen` items of `xs`. All results satisfy the invariant and keep `maxlen`. -/
def DequeEndsEvict : Prop :=
  ∀ (d : Deque), d.WF → ∀ (x : Int) (xs : List Int),
    ((d.append x).WF ∧ (d.append x).items = keepLast d.maxlen (d.items ++ [x]) ∧
      (d.append x).maxlen = d.maxlen) ∧
    ((d.appendleft x).WF ∧ (d.appendleft x).items = keepFirst d.maxlen (x :: d.items) ∧
      (d.appendleft x).maxlen = d.maxlen) ∧
    ((d.extend xs).WF ∧ (d.extend xs).items = keepLast d.maxlen (d.items ++ xs) ∧
      (d.extend xs).maxlen = d.maxlen) ∧
    ((d.extendleft xs).WF ∧ (d.extendleft xs).items = keepFirst d.maxlen (xs.reverse ++ d.items) ∧
      (d.extendleft xs).maxlen = d.maxlen) ∧
    (d.extendSelf.WF ∧ d.extendSelf.items = keepLast d.maxlen (d.items ++ d.items)) ∧
    (d.extendleftSelf.WF ∧ d.extendleftSelf.items = keepFirst d.maxlen (d.items.reverse ++ d.items)) ∧
    (d.items = [] → d.pop = .error (.indexError "pop from an empty deque") ∧
      d.popleft = .error (.indexError "pop from an empty deque")) ∧
    (d.items ≠ [] →
      (∃ d', d.pop = .ok (ix d.items (d.items.length - 1), d') ∧ d'.WF ∧ d'.items = d.items.dropLast ∧
        d'.maxlen = d.maxlen) ∧
      (∃ d', d.popleft = .ok (ix d.items 0, d') ∧ d'.WF ∧ d'.items = d.items.drop 1 ∧
        d'.maxlen = d.maxlen))

theorem dequeEndsEvict_proven : DequeEndsEvict := by
  intro d h x xs
  refine ⟨Deque.append_spec d x h, Deque.appendleft_spec d x h, Deque.extend_spec d xs h,
    Deque.extendleft_spec d xs h, ?_, ?_, ?_, ?_⟩
  · obtain ⟨a, b, _⟩ := Deque.extend_spec d d.items h; exact ⟨a, b⟩
  · obtain ⟨a, b, _⟩ := Deque.extendleft_spec d d.items h; exact ⟨a, b⟩
  · intro he
    have hs : d.size = 0 := by rw [Deque.size_eq, he]; rfl
    exact ⟨by unfold Deque.pop; rw [iteT hs], by unfold Deque.popleft; rw [iteT hs]⟩
  · intro hne
    exact ⟨Deque.pop_wf d h hne, Deque.popleft_wf d h hne⟩

/-- `deque(xs, maxlen)`: `maxlen=None` keeps all items; an int `0 <= maxlen
<= sys.maxsize` keeps the last `maxlen` items; a negative `maxlen` raises
`ValueError` and one beyond `Py_ssize_t` raises `OverflowError`. -/
def DequeConstruct : Prop :=
  ∀ (xs : List Int) (m : Option Int),
    match m with
    | none => ∃ d, Deque.make xs none = .ok d ∧ d.WF ∧ d.items = xs ∧ d.maxlen = -1
    | some m =>
      (0 ≤ m → m ≤ ssizeMax → ∃ d, Deque.make xs (some m) = .ok d ∧ d.WF ∧ d.items = keepLast m xs ∧
        d.maxlen = m) ∧
      (m < 0 → ssizeMin ≤ m → Deque.make xs (some m) = .error (.valueError "maxlen must be non-negative")) ∧
      ((m < ssizeMin ∨ ssizeMax < m) →
        Deque.make xs (some m) = .error (.overflowError "Python int too large to convert to C ssize_t"))

theorem new_wf (m : Int) (hm : m = -1 ∨ 0 ≤ m) : ({ Deque.new with maxlen := m } : Deque).WF := by
  refine ⟨?_, ?_⟩
  · rw [Deque.layout_iff]; simp [Deque.new, CENTER]
  · rw [Deque.maxOk_iff]; simp only [Deque.new, List.length_nil, Int.natCast_zero]; omega

theorem make_none (xs : List Int) :
    Deque.make xs none = .ok (({ Deque.new with maxlen := -1 } : Deque).extend xs) := rfl

theorem make_some (xs : List Int) (m : Int) (h0 : 0 ≤ m) (h1 : m ≤ ssizeMax) :
    Deque.make xs (some m) = .ok (({ Deque.new with maxlen := m } : Deque).extend xs) := by
  simp only [Deque.make, Deque.init, asSsize, bind, Except.bind, pure, Except.pure]
  rw [iteT ⟨by unfold ssizeMin; unfold ssizeMax at h1; omega, h1⟩]
  simp only [iteF (show ¬ m < 0 by omega)]
  rfl

theorem dequeConstruct_proven : DequeConstruct := by
  intro xs m
  cases m with
  | none =>
    obtain ⟨a, b, c⟩ := Deque.extend_spec { Deque.new with maxlen := -1 } xs (new_wf (-1) (Or.inl rfl))
    refine ⟨_, make_none xs, a, ?_, c⟩
    rw [b]; simp [Deque.new, keepLast]
  | some m =>
    refine ⟨fun h0 h1 => ?_, fun h0 h1 => ?_, fun h => ?_⟩
    · obtain ⟨a, b, c⟩ := Deque.extend_spec { Deque.new with maxlen := m } xs (new_wf m (Or.inr h0))
      exact ⟨_, make_some xs m h0 h1, a, b, c⟩
    · simp only [Deque.make, Deque.init, asSsize, bind, Except.bind, pure, Except.pure]
      rw [iteT ⟨h1, by unfold ssizeMax; omega⟩]
      simp only [iteT h0]; rfl
    · simp only [Deque.make, Deque.init, asSsize, bind, Except.bind, pure, Except.pure]
      rw [iteF (by omega)]

/-! ### Rotation -/

/-- One documented right step, `d.appendleft(d.pop())`, and one left step,
`d.append(d.popleft())`. -/
def rotStepR (d : Deque) : Py Deque := do
  let (x, d) ← d.pop
  return d.appendleft x
def rotStepL (d : Deque) : Py Deque := do
  let (x, d) ← d.popleft
  return d.append x

def iterPy (f : Deque → Py Deque) : Nat → Deque → Py Deque
  | 0, d => .ok d
  | k + 1, d => do iterPy f k (← f d)

/-- `d.rotate(n)` is the documented loop (Doc/library/collections.rst:574-581):
for every non-empty deque (`WF`) and every int `n`, `rotate(n)` raises
`OverflowError` exactly when `n` is outside `Py_ssize_t`, and otherwise
leaves the same items (and `maxlen`) as `n` repetitions of
`d.appendleft(d.pop())` (for `n >= 0`) or `-n` repetitions of
`d.append(d.popleft())` (for `n < 0`), keeping the layout invariant —
including for `n` far larger than `len(d)` and for `n = -2**63`. -/
def RotateLoop : Prop :=
  ∀ (d : Deque), d.WF → d.items ≠ [] → ∀ (n : Int),
    ((n < ssizeMin ∨ ssizeMax < n) →
      d.rotate n = .error (.overflowError "Python int too large to convert to C ssize_t")) ∧
    (ssizeMin ≤ n → n ≤ ssizeMax →
      ∃ d' d'', d.rotate n = .ok d' ∧ d'.WF ∧ d'.maxlen = d.maxlen ∧
        (if 0 ≤ n then iterPy rotStepR n.toNat d else iterPy rotStepL (-n).toNat d) = .ok d'' ∧
        d'.items = d''.items)

theorem rotStepR_spec (d : Deque) (h : d.WF) (hne : d.items ≠ []) :
    ∃ d', rotStepR d = .ok d' ∧ d'.WF ∧ d'.items = rotLi (-1) d.items ∧ d'.maxlen = d.maxlen ∧
      d'.items ≠ [] := by
  obtain ⟨d1, hp, w1, i1, m1⟩ := Deque.pop_wf d h hne
  obtain ⟨a, b, c⟩ := Deque.appendleft_spec d1 (ix d.items (d.items.length - 1)) w1
  have hlen : 0 < d.items.length := List.length_pos_iff.mpr hne
  have hitems : (d1.appendleft (ix d.items (d.items.length - 1))).items = rotLi (-1) d.items := by
    rw [b, i1, m1, keepFirst_of_le]
    · unfold rotLi
      rw [emod_char (-1) ((d.items.length : Int) - 1) _ (-1) (by omega) (by omega) (by omega)]
      unfold rotL
      rw [show ((d.items.length : Int) - 1).toNat = d.items.length - 1 by omega, List.dropLast_eq_take]
      rw [List.drop_eq_getElem_cons (by omega), List.drop_of_length_le (by omega)]
      simp only [List.cons_append, List.nil_append, ix, List.getD_eq_getElem?_getD]
      congr 1
      rw [List.getElem?_eq_getElem (by omega)]
      simp only [Option.getD_some]
      congr; omega
    · rcases h.2 with h2 | h2
      · left; omega
      · right; simp only [List.length_cons, List.length_dropLast]; rw [Deque.size_eq] at h2; omega
  refine ⟨_, ?_, a, hitems, by rw [c, m1], ?_⟩
  · simp only [rotStepR, hp, bind, Except.bind, pure, Except.pure]
  · rw [hitems]; intro he; have := congrArg List.length he; rw [length_rotLi, List.length_nil] at this; omega

theorem rotStepL_spec (d : Deque) (h : d.WF) (hne : d.items ≠ []) :
    ∃ d', rotStepL d = .ok d' ∧ d'.WF ∧ d'.items = rotLi 1 d.items ∧ d'.maxlen = d.maxlen ∧
      d'.items ≠ [] := by
  obtain ⟨d1, hp, w1, i1, m1⟩ := Deque.popleft_wf d h hne
  obtain ⟨a, b, c⟩ := Deque.append_spec d1 (ix d.items 0) w1
  have hlen : 0 < d.items.length := List.length_pos_iff.mpr hne
  have hitems : (d1.append (ix d.items 0)).items = rotLi 1 d.items := by
    rw [b, i1, m1, keepLast_of_le]
    · unfold rotLi
      by_cases h1 : d.items.length = 1
      · rw [h1, show ((1 : Nat) : Int) = 1 by rfl, Int.emod_self]
        match hd : d.items, h1 with
        | [y], _ => simp [rotL, ix]
      rw [Int.emod_eq_of_lt (by omega) (by omega)]
      unfold rotL
      match hd : d.items, hne with
      | y :: ys, _ => simp [ix]
    · rcases h.2 with h2 | h2
      · left; omega
      · right; simp only [List.length_append, List.length_drop, List.length_singleton]
        rw [Deque.size_eq] at h2; omega
  refine ⟨_, ?_, a, hitems, by rw [c, m1], ?_⟩
  · simp only [rotStepL, hp, bind, Except.bind, pure, Except.pure]
  · rw [hitems]; intro he; have := congrArg List.length he; rw [length_rotLi, List.length_nil] at this; omega

theorem iterPy_R (k : Nat) : ∀ (d : Deque), d.WF → d.items ≠ [] →
    ∃ d', iterPy rotStepR k d = .ok d' ∧ d'.items = rotLi (-(k : Int)) d.items := by
  induction k with
  | zero => intro d _ _; exact ⟨d, rfl, by simp [rotLi_zero]⟩
  | succ k ih =>
    intro d h hne
    obtain ⟨d1, h1, w1, i1, _, ne1⟩ := rotStepR_spec d h hne
    obtain ⟨d2, h2, i2⟩ := ih d1 w1 ne1
    refine ⟨d2, ?_, ?_⟩
    · simp only [iterPy, h1, bind, Except.bind, h2]
    · rw [i2, i1, rotLi_rotLi]; congr 1; (try omega)

theorem iterPy_L (k : Nat) : ∀ (d : Deque), d.WF → d.items ≠ [] →
    ∃ d', iterPy rotStepL k d = .ok d' ∧ d'.items = rotLi (k : Int) d.items := by
  induction k with
  | zero => intro d _ _; exact ⟨d, rfl, by simp [rotLi_zero]⟩
  | succ k ih =>
    intro d h hne
    obtain ⟨d1, h1, w1, i1, _, ne1⟩ := rotStepL_spec d h hne
    obtain ⟨d2, h2, i2⟩ := ih d1 w1 ne1
    refine ⟨d2, ?_, ?_⟩
    · simp only [iterPy, h1, bind, Except.bind, h2]
    · rw [i2, i1, rotLi_rotLi]; congr 1; (try omega)

theorem rotateLoop_proven : RotateLoop := by
  intro d h hne n
  refine ⟨fun hn => ?_, fun h0 h1 => ?_⟩
  · simp only [Deque.rotate, asSsize, bind, Except.bind]
    rw [iteF (by omega)]
  · obtain ⟨d', hr, w', i', m'⟩ := Deque.rotateC_wf d n h
    have hrot : d.rotate n = .ok d' := by
      simp only [Deque.rotate, asSsize, bind, Except.bind]
      rw [iteT ⟨h0, h1⟩]; exact hr
    by_cases hn : 0 ≤ n
    · obtain ⟨d'', h2, i2⟩ := iterPy_R n.toNat d h hne
      refine ⟨d', d'', hrot, w', m', by rw [iteT hn]; exact h2, ?_⟩
      rw [i', i2, show ((n.toNat : Nat) : Int) = n by omega]
    · obtain ⟨d'', h2, i2⟩ := iterPy_L (-n).toNat d h hne
      refine ⟨d', d'', hrot, w', m', by rw [iteF hn]; exact h2, ?_⟩
      rw [i', i2, show (((-n).toNat : Nat) : Int) = -n by omega]

end PyLean.Sequences
