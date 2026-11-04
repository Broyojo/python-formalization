import PyLean.Sequences.DequeReentrant

/-!
Deque iteration (`deque_iter`, `dequeiter_next`, `deque_reviter`, `dequereviter_next`,
`__reversed__`), the iterator types' `__new__`, `__length_hint__` and `__reduce__`, and the
deque methods built on iteration: `__reduce__`, `repr`, `__sizeof__` and rich comparison
with element comparisons that raise or change either deque.

The iterators keep a block cursor numbered from the deque's `leftblock` (`Deque.Iter`).
`FwdAt d it p` / `RevAt d it p` say that `it` stands after `p` calls on the unchanged
deque `d`: its state matches, `p` items are consumed, and the cursor addresses item `p`
(forward) or item `len - 1 - p` (reverse) whenever one is left.
-/

namespace PyLean.Sequences

open PyLean

set_option linter.unusedSectionVars false

variable {α : Type} [Inhabited α]

theorem ix_drop (l : List α) (p : Nat) (hp : p < l.length) : ix l p :: l.drop (p + 1) = l.drop p := by
  unfold ix
  rw [Int.toNat_natCast, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp, Option.getD_some]
  exact (List.drop_eq_getElem_cons hp).symm

theorem ix_rev_drop (l : List α) (p : Nat) (hp : p < l.length) :
    ix l ((l.length : Int) - 1 - p) :: l.reverse.drop (p + 1) = l.reverse.drop p := by
  have hp' : p < l.reverse.length := by simpa using hp
  rw [List.drop_eq_getElem_cons hp' (l := l.reverse), List.getElem_reverse]
  unfold ix
  rw [show ((l.length : Int) - 1 - p).toNat = l.length - 1 - p by omega, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by omega), Option.getD_some]

namespace Deque

/-- `it` is `iter(d)` after `p` calls of `__next__` on the unchanged deque `d`. -/
def FwdAt (d : Deque α) (it : Iter) (p : Nat) : Prop :=
  it.state = d.state ∧ it.counter = (d.items.length : Int) - p ∧ p ≤ d.items.length ∧
    (p < d.items.length → it.b * 64 + it.index - d.left = p ∧ 0 ≤ it.index ∧ it.index < 64)

/-- `it` is `reversed(d)` after `p` calls of `__next__` on the unchanged deque `d`. -/
def RevAt (d : Deque α) (it : Iter) (p : Nat) : Prop :=
  it.state = d.state ∧ it.counter = (d.items.length : Int) - p ∧ p ≤ d.items.length ∧
    (p < d.items.length → it.b * 64 + it.index - d.left = (d.items.length : Int) - 1 - p ∧
      0 ≤ it.index ∧ it.index < 64)

theorem fwd_init (d : Deque α) (h : d.Layout) : FwdAt d d.iter 0 := by
  have h' := h
  rw [layout_iff] at h'
  refine ⟨rfl, ?_, Nat.zero_le _, fun _ => ⟨?_, h'.1, h'.2.1⟩⟩
  · simp only [iter, size_eq]; omega
  · simp only [iter]; omega

theorem rev_init (d : Deque α) (h : d.Layout) : RevAt d d.reviter 0 := by
  have h' := h
  rw [layout_iff] at h'
  refine ⟨rfl, ?_, Nat.zero_le _, fun hp => ⟨?_, h'.2.2.1, h'.2.2.2.1⟩⟩
  · simp only [reviter, size_eq]; omega
  · simp only [reviter, rbNum, size_eq]; omega

theorem fwd_step (d : Deque α) (h : d.Layout) (it : Iter) (p : Nat) (hf : FwdAt d it p)
    (hp : p < d.items.length) :
    ∃ it', iterNext d it = (.ok (some (ix d.items p)), it') ∧ FwdAt d it' (p + 1) := by
  obtain ⟨hs, hc, _, hpos⟩ := hf
  obtain ⟨e1, e2, e3⟩ := hpos hp
  have h' := h
  rw [layout_iff] at h'
  have hst : ¬ d.state ≠ it.state := by rw [hs]; simp
  have hc0 : ¬ it.counter = 0 := by omega
  have hr := read_ok d h it.b it.index (by dq_omega) (by dq_omega) e2 e3 (by omega) (by dq_omega)
  rw [e1] at hr
  unfold iterNext
  rw [iteF hst, iteF hc0, hr]
  refine ⟨_, rfl, ?_⟩
  by_cases hh : it.index + 1 = 64 ∧ it.counter - 1 > 0
  · rw [iteT hh]
    exact ⟨hs, by simp only; omega, by omega, fun _ => ⟨by simp only; omega, by simp only; omega,
      by simp only; omega⟩⟩
  · rw [iteF hh]
    exact ⟨hs, by simp only; omega, by omega, fun _ => ⟨by simp only; omega, by simp only; omega,
      by simp only; omega⟩⟩

theorem rev_step (d : Deque α) (h : d.Layout) (it : Iter) (p : Nat) (hf : RevAt d it p)
    (hp : p < d.items.length) :
    ∃ it', reviterNext d it = (.ok (some (ix d.items ((d.items.length : Int) - 1 - p))), it') ∧
      RevAt d it' (p + 1) := by
  obtain ⟨hs, hc, _, hpos⟩ := hf
  obtain ⟨e1, e2, e3⟩ := hpos hp
  have h' := h
  rw [layout_iff] at h'
  have hst : ¬ d.state ≠ it.state := by rw [hs]; simp
  have hc0 : ¬ it.counter = 0 := by omega
  have hr := read_ok d h it.b it.index (by dq_omega) (by dq_omega) e2 e3 (by omega) (by dq_omega)
  rw [e1] at hr
  unfold reviterNext
  rw [iteF hc0, iteF hst, hr]
  refine ⟨_, rfl, ?_⟩
  by_cases hh : it.index - 1 < 0 ∧ it.counter - 1 > 0
  · rw [iteT hh]
    exact ⟨hs, by simp only; omega, by omega, fun _ => ⟨by simp only; omega, by simp only; omega,
      by simp only; omega⟩⟩
  · rw [iteF hh]
    exact ⟨hs, by simp only; omega, by omega, fun _ => ⟨by simp only; omega, by simp only; omega,
      by simp only; omega⟩⟩

theorem fwd_end (d : Deque α) (it : Iter) (hf : FwdAt d it d.items.length) :
    iterNext d it = (.ok none, it) := by
  obtain ⟨hs, hc, _, _⟩ := hf
  have hst : ¬ d.state ≠ it.state := by rw [hs]; simp
  have hc0 : it.counter = 0 := by omega
  unfold iterNext
  rw [iteF hst, iteT hc0]

theorem rev_end (d : Deque α) (it : Iter) (hf : RevAt d it d.items.length) :
    reviterNext d it = (.ok none, it) := by
  obtain ⟨_, hc, _, _⟩ := hf
  have hc0 : it.counter = 0 := by omega
  unfold reviterNext
  rw [iteT hc0]

theorem fwd_drain (d : Deque α) (h : d.Layout) : ∀ (k : Nat) (it : Iter) (p n : Nat), FwdAt d it p →
    p + k = d.items.length → drain iterNext d (n + k + 1) it = .ok (d.items.drop p)
  | 0, it, p, n, hf, hk => by
    have hf' : FwdAt d it d.items.length := by rw [← hk]; exact hf
    simp only [drain, fwd_end d it hf']
    rw [List.drop_eq_nil_of_le (by omega)]
  | k + 1, it, p, n, hf, hk => by
    obtain ⟨it', h1, h2⟩ := fwd_step d h it p hf (by omega)
    rw [show n + (k + 1) + 1 = (n + k + 1) + 1 by omega, drain.eq_2]
    simp only [h1]
    rw [fwd_drain d h k it' (p + 1) n h2 (by omega)]
    exact congrArg Except.ok (ix_drop _ _ (by omega))

theorem rev_drain (d : Deque α) (h : d.Layout) : ∀ (k : Nat) (it : Iter) (p n : Nat), RevAt d it p →
    p + k = d.items.length → drain reviterNext d (n + k + 1) it = .ok (d.items.reverse.drop p)
  | 0, it, p, n, hf, hk => by
    have hf' : RevAt d it d.items.length := by rw [← hk]; exact hf
    simp only [drain, rev_end d it hf']
    rw [List.drop_eq_nil_of_le (by simp; omega)]
  | k + 1, it, p, n, hf, hk => by
    obtain ⟨it', h1, h2⟩ := rev_step d h it p hf (by omega)
    rw [show n + (k + 1) + 1 = (n + k + 1) + 1 by omega, drain.eq_2]
    simp only [h1]
    rw [rev_drain d h k it' (p + 1) n h2 (by omega)]
    exact congrArg Except.ok (ix_rev_drop _ _ (by omega))

/-- The consuming loop of `dequeiter_new`, from an iterator at `p`. -/
theorem fwd_advance (d : Deque α) (h : d.Layout) : ∀ (k : Nat) (it : Iter) (p : Nat), FwdAt d it p →
    ∃ it', iterAdvance iterNext d k it = .ok it' ∧ FwdAt d it' (min (p + k) d.items.length)
  | 0, it, p, hf => ⟨it, rfl, by rw [Nat.add_zero, Nat.min_eq_left hf.2.2.1]; exact hf⟩
  | k + 1, it, p, hf => by
    by_cases hp : p < d.items.length
    · obtain ⟨it', h1, h2⟩ := fwd_step d h it p hf hp
      obtain ⟨it'', h3, h4⟩ := fwd_advance d h k it' (p + 1) h2
      refine ⟨it'', ?_, by rw [show p + (k + 1) = p + 1 + k by omega]; exact h4⟩
      simp only [iterAdvance, h1]; exact h3
    · have hpl : p = d.items.length := by have := hf.2.2.1; omega
      have hf' : FwdAt d it d.items.length := by rw [← hpl]; exact hf
      have he := fwd_end d it hf'
      have hc0 : it.counter = 0 := by have := hf.2.1; omega
      refine ⟨it, ?_, by rw [Nat.min_eq_right (by omega)]; exact hf'⟩
      simp only [iterAdvance, he, hc0, ne_eq, not_true_eq_false, ite_false]

theorem rev_advance (d : Deque α) (h : d.Layout) : ∀ (k : Nat) (it : Iter) (p : Nat), RevAt d it p →
    ∃ it', iterAdvance reviterNext d k it = .ok it' ∧ RevAt d it' (min (p + k) d.items.length)
  | 0, it, p, hf => ⟨it, rfl, by rw [Nat.add_zero, Nat.min_eq_left hf.2.2.1]; exact hf⟩
  | k + 1, it, p, hf => by
    by_cases hp : p < d.items.length
    · obtain ⟨it', h1, h2⟩ := rev_step d h it p hf hp
      obtain ⟨it'', h3, h4⟩ := rev_advance d h k it' (p + 1) h2
      refine ⟨it'', ?_, by rw [show p + (k + 1) = p + 1 + k by omega]; exact h4⟩
      simp only [iterAdvance, h1]; exact h3
    · have hpl : p = d.items.length := by have := hf.2.2.1; omega
      have hf' : RevAt d it d.items.length := by rw [← hpl]; exact hf
      have he := rev_end d it hf'
      have hc0 : it.counter = 0 := by have := hf.2.1; omega
      refine ⟨it, ?_, by rw [Nat.min_eq_right (by omega)]; exact hf'⟩
      simp only [iterAdvance, he, hc0, ne_eq, not_true_eq_false, ite_false]

end Deque

/-! ### Iteration -/

/-- `iter(d)` and `reversed(d)` (`deque_iter`, `dequeiter_next_lock_held`, `dequeiter_next`,
`deque___reversed___impl`, `deque_reviter`, `dequereviter_next_lock_held`,
`dequereviter_next`), for every element type and every deque (type invariant `WF`): walking
the block cursor yields every item in order (reversed for `reversed(d)`), then
`StopIteration`; after `p <= len(d)` calls `__length_hint__()` (`dequeiter_len`) is
`len(d) - p` and the remaining calls yield `d[p:]` (forward) or `reversed(d)[p:]`; an
exhausted iterator keeps returning `StopIteration` while the deque is unchanged. Once the
deque's mutation counter has moved (any method that moves items, from any code): the
forward iterator raises `RuntimeError('deque mutated during iteration')` and keeps raising
it on every later call, also when it was exhausted before the change, while the reverse
iterator, which tests exhaustion first (:2124 before :2127), raises it once and then
reports `StopIteration`, and an exhausted reverse iterator just reports `StopIteration`.
Both set `__length_hint__()` to 0. -/
def DequeIterWalk : Prop :=
  ∀ (α : Type) [Inhabited α] (d : Deque α), d.WF →
    d.drain Deque.iterNext (d.items.length + 1) d.iter = .ok d.items ∧
    d.drain Deque.reviterNext (d.items.length + 1) d.reviter = .ok d.items.reverse ∧
    (∀ p : Nat, p ≤ d.items.length →
      (∃ it, Deque.iterAdvance Deque.iterNext d p d.iter = .ok it ∧ Deque.FwdAt d it p ∧
        Deque.iterLen it = d.items.length - p ∧
        d.drain Deque.iterNext (d.items.length + 1) it = .ok (d.items.drop p) ∧
        (p = d.items.length → Deque.iterNext d it = (.ok none, it))) ∧
      (∃ it, Deque.iterAdvance Deque.reviterNext d p d.reviter = .ok it ∧ Deque.RevAt d it p ∧
        Deque.iterLen it = d.items.length - p ∧
        d.drain Deque.reviterNext (d.items.length + 1) it = .ok (d.items.reverse.drop p) ∧
        (p = d.items.length → Deque.reviterNext d it = (.ok none, it)))) ∧
    (∀ (p : Nat) (it : Deque.Iter) (d' d'' : Deque α), d'.state ≠ d.state →
      (Deque.FwdAt d it p →
        ∃ it', Deque.iterNext d' it = (.error Deque.mutatedErr, it') ∧ Deque.iterLen it' = 0 ∧
          Deque.iterNext d' it' = (.error Deque.mutatedErr, it')) ∧
      (Deque.RevAt d it p → p < d.items.length →
        ∃ it', Deque.reviterNext d' it = (.error Deque.mutatedErr, it') ∧ Deque.iterLen it' = 0 ∧
          Deque.reviterNext d'' it' = (.ok none, it')) ∧
      (Deque.RevAt d it d.items.length → Deque.reviterNext d' it = (.ok none, it)))

theorem dequeIterWalk_proven : DequeIterWalk := by
  intro α _ d h
  have hL := h.1
  refine ⟨?_, ?_, fun p hp => ⟨?_, ?_⟩, fun p it d' d'' hst => ⟨fun hf => ?_, fun hf hp => ?_, fun hf => ?_⟩⟩
  · have := Deque.fwd_drain d hL d.items.length d.iter 0 0 (Deque.fwd_init d hL) (by omega)
    rw [Nat.zero_add] at this; exact this
  · have := Deque.rev_drain d hL d.items.length d.reviter 0 0 (Deque.rev_init d hL) (by omega)
    rw [Nat.zero_add] at this; exact this
  · obtain ⟨it, h1, h2⟩ := Deque.fwd_advance d hL p d.iter 0 (Deque.fwd_init d hL)
    rw [Nat.zero_add, Nat.min_eq_left hp] at h2
    refine ⟨it, h1, h2, ?_, ?_, fun he => Deque.fwd_end d it (by rw [← he]; exact h2)⟩
    · unfold Deque.iterLen; exact h2.2.1
    · have := Deque.fwd_drain d hL (d.items.length - p) it p p h2 (by omega)
      rw [show p + (d.items.length - p) + 1 = d.items.length + 1 by omega] at this; exact this
  · obtain ⟨it, h1, h2⟩ := Deque.rev_advance d hL p d.reviter 0 (Deque.rev_init d hL)
    rw [Nat.zero_add, Nat.min_eq_left hp] at h2
    refine ⟨it, h1, h2, ?_, ?_, fun he => Deque.rev_end d it (by rw [← he]; exact h2)⟩
    · unfold Deque.iterLen; exact h2.2.1
    · have := Deque.rev_drain d hL (d.items.length - p) it p p h2 (by omega)
      rw [show p + (d.items.length - p) + 1 = d.items.length + 1 by omega] at this; exact this
  · have hs : d'.state ≠ it.state := by rw [hf.1]; exact hst
    refine ⟨{ it with counter := 0 }, ?_, rfl, ?_⟩
    · unfold Deque.iterNext; rw [iteT hs]
    · unfold Deque.iterNext; rw [iteT hs]
  · have hs : d'.state ≠ it.state := by rw [hf.1]; exact hst
    have hc : ¬ it.counter = 0 := by have := hf.2.1; omega
    refine ⟨{ it with counter := 0 }, ?_, rfl, ?_⟩
    · unfold Deque.reviterNext; rw [iteF hc, iteT hs]
    · unfold Deque.reviterNext; rw [iteT rfl]
  · have hc : it.counter = 0 := by have := hf.2.1; omega
    unfold Deque.reviterNext; rw [iteT hc]

/-! ### The iterator types: `__new__`, `__reduce__` -/

/-- `type(iter(d))(d, index)` and `type(reversed(d))(d, index)` (`dequeiter_new`,
`dequereviter_new`), `it.__length_hint__()` (`dequeiter_len`) and `it.__reduce__()`
(`dequeiter_reduce`, shared by both types), for every deque (type invariants `WF` and
`len(d) <= sys.maxsize`) and every int `index`: inside `Py_ssize_t`, the new iterator has
consumed `c = min(max(index, 0), len(d))` items (a negative index consumes none, one past
the end stops at exhaustion), so its length hint is `len(d) - c` and it yields `d[c:]`
(`reversed(d)[c:]`); outside it raises `OverflowError`. `__reduce__` gives
`(type(it), (d, len(d) - it.__length_hint__()))`, and rebuilding from it gives an iterator
that yields exactly what is left of the original, for every iterator reached by `__next__`
calls on the unchanged deque (pickle round trip). -/
def DequeIterNew : Prop :=
  ∀ (α : Type) [Inhabited α] (d : Deque α), d.WF → (d.items.length : Int) ≤ ssizeMax →
    (∀ index : Int, ssizeMin ≤ index → index ≤ ssizeMax →
      (∃ it, d.iterNew index = .ok it ∧
        Deque.iterLen it = d.items.length - min index.toNat d.items.length ∧
        d.drain Deque.iterNext (d.items.length + 1) it = .ok (d.items.drop (min index.toNat d.items.length))) ∧
      (∃ it, d.reviterNew index = .ok it ∧
        Deque.iterLen it = d.items.length - min index.toNat d.items.length ∧
        d.drain Deque.reviterNext (d.items.length + 1) it =
          .ok (d.items.reverse.drop (min index.toNat d.items.length)))) ∧
    (∀ index : Int, (index < ssizeMin ∨ ssizeMax < index) →
      d.iterNew index = .error (.overflowError "Python int too large to convert to C ssize_t") ∧
      d.reviterNew index = .error (.overflowError "Python int too large to convert to C ssize_t")) ∧
    (∀ (p : Nat) (it : Deque.Iter), p ≤ d.items.length →
      (Deque.FwdAt d it p → d.iterReduce it = p ∧
        ∃ it', d.iterNew (d.iterReduce it) = .ok it' ∧
          d.drain Deque.iterNext (d.items.length + 1) it' = d.drain Deque.iterNext (d.items.length + 1) it) ∧
      (Deque.RevAt d it p → d.iterReduce it = p ∧
        ∃ it', d.reviterNew (d.iterReduce it) = .ok it' ∧
          d.drain Deque.reviterNext (d.items.length + 1) it' = d.drain Deque.reviterNext (d.items.length + 1) it))

theorem iterNew_spec (d : Deque α) (h : d.Layout) (index : Int) (h0 : ssizeMin ≤ index) (h1 : index ≤ ssizeMax) :
    (∃ it, d.iterNew index = .ok it ∧ Deque.FwdAt d it (min index.toNat d.items.length)) ∧
    (∃ it, d.reviterNew index = .ok it ∧ Deque.RevAt d it (min index.toNat d.items.length)) := by
  have ha : asSsize index = .ok index := by unfold asSsize; rw [iteT ⟨h0, h1⟩]
  obtain ⟨it, e1, e2⟩ := Deque.fwd_advance d h (min index.toNat (d.items.length + 1)) d.iter 0 (Deque.fwd_init d h)
  obtain ⟨jt, f1, f2⟩ := Deque.rev_advance d h (min index.toNat (d.items.length + 1)) d.reviter 0 (Deque.rev_init d h)
  have hm : min (0 + min index.toNat (d.items.length + 1)) d.items.length = min index.toNat d.items.length := by
    generalize index.toNat = t
    omega
  rw [hm] at e2 f2
  refine ⟨⟨it, ?_, e2⟩, ⟨jt, ?_, f2⟩⟩
  · unfold Deque.iterNew; rw [ha]; exact e1
  · unfold Deque.reviterNew; rw [ha]; exact f1

theorem dequeIterNew_proven : DequeIterNew := by
  intro α _ d h hlen
  have hL := h.1
  refine ⟨fun index h0 h1 => ?_, fun index hi => ?_, fun p it hp => ⟨fun hf => ?_, fun hf => ?_⟩⟩
  · obtain ⟨⟨it, e1, e2⟩, ⟨jt, f1, f2⟩⟩ := iterNew_spec d hL index h0 h1
    refine ⟨⟨it, e1, by unfold Deque.iterLen; exact e2.2.1, ?_⟩, ⟨jt, f1, by unfold Deque.iterLen; exact f2.2.1, ?_⟩⟩
    · generalize hc : min index.toNat d.items.length = c at e2 ⊢
      have hcl : c ≤ d.items.length := by rw [← hc]; exact Nat.min_le_right _ _
      have := Deque.fwd_drain d hL (d.items.length - c) it c c e2 (by omega)
      rw [show c + (d.items.length - c) + 1 = d.items.length + 1 by omega] at this
      exact this
    · generalize hc : min index.toNat d.items.length = c at f2 ⊢
      have hcl : c ≤ d.items.length := by rw [← hc]; exact Nat.min_le_right _ _
      have := Deque.rev_drain d hL (d.items.length - c) jt c c f2 (by omega)
      rw [show c + (d.items.length - c) + 1 = d.items.length + 1 by omega] at this
      exact this
  · have ha : asSsize index = .error (.overflowError "Python int too large to convert to C ssize_t") := by
      unfold asSsize; rw [iteF (by omega)]
    refine ⟨?_, ?_⟩
    · unfold Deque.iterNew; rw [ha]; rfl
    · unfold Deque.reviterNew; rw [ha]; rfl
  · have hr : d.iterReduce it = p := by unfold Deque.iterReduce; rw [Deque.size_eq, hf.2.1]; omega
    refine ⟨hr, ?_⟩
    obtain ⟨⟨it', e1, e2⟩, _⟩ := iterNew_spec d hL p (by unfold ssizeMin; unfold ssizeMax at hlen; omega)
      (by omega)
    rw [show min (p : Int).toNat d.items.length = p by omega] at e2
    refine ⟨it', by rw [hr]; exact e1, ?_⟩
    have a1 := Deque.fwd_drain d hL (d.items.length - p) it' p p e2 (by omega)
    have a2 := Deque.fwd_drain d hL (d.items.length - p) it p p hf (by omega)
    rw [show p + (d.items.length - p) + 1 = d.items.length + 1 by omega] at a1 a2
    rw [a1, a2]
  · have hr : d.iterReduce it = p := by unfold Deque.iterReduce; rw [Deque.size_eq, hf.2.1]; omega
    refine ⟨hr, ?_⟩
    obtain ⟨_, ⟨it', e1, e2⟩⟩ := iterNew_spec d hL p (by unfold ssizeMin; unfold ssizeMax at hlen; omega)
      (by omega)
    rw [show min (p : Int).toNat d.items.length = p by omega] at e2
    refine ⟨it', by rw [hr]; exact e1, ?_⟩
    have a1 := Deque.rev_drain d hL (d.items.length - p) it' p p e2 (by omega)
    have a2 := Deque.rev_drain d hL (d.items.length - p) it p p hf (by omega)
    rw [show p + (d.items.length - p) + 1 = d.items.length + 1 by omega] at a1 a2
    rw [a1, a2]

/-- The property refuted: `type(iter(d))(...)` and `type(reversed(d))(...)` reject keyword
arguments with `TypeError`, as a call that does not accept them must. `dequeiter_new` and
`dequereviter_new` parse only `args` (:2017, :2167) and never look at `kwds`, so
`type(iter(d))(d, index=3)` silently returns a fresh iterator over all of `d`. -/
def DequeIterNewKw : Prop :=
  ∀ (α : Type) [Inhabited α] (d : Deque α) (index : Option Int) (kw : List String), kw ≠ [] →
    (∃ msg, d.iterNewArgs index kw = .error (.typeError msg)) ∧
    (∃ msg, d.reviterNewArgs index kw = .error (.typeError msg))

/-- Both constructors accept `index=3` and return a fresh iterator. -/
theorem dequeIterNewKw_neither :
    ¬ (∀ (d : Deque Int) (index : Option Int) (kw : List String), kw ≠ [] →
        ∃ msg, d.iterNewArgs index kw = .error (.typeError msg)) ∧
    ¬ (∀ (d : Deque Int) (index : Option Int) (kw : List String), kw ≠ [] →
        ∃ msg, d.reviterNewArgs index kw = .error (.typeError msg)) := by
  have e1 : (Deque.new "deque" : Deque Int).iterNewArgs none ["index"] =
      .ok (Deque.new "deque" : Deque Int).iter := by decide
  have e2 : (Deque.new "deque" : Deque Int).reviterNewArgs none ["index"] =
      .ok (Deque.new "deque" : Deque Int).reviter := by decide
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨msg, hm⟩ := h (Deque.new "deque") none ["index"] (by simp)
    rw [e1] at hm; exact nomatch hm
  · obtain ⟨msg, hm⟩ := h (Deque.new "deque") none ["index"] (by simp)
    rw [e2] at hm; exact nomatch hm

theorem dequeIterNewKw_refuted : ¬ DequeIterNewKw :=
  fun h => dequeIterNewKw_neither.2 (fun d index kw hk => (h Int d index kw hk).2)

end PyLean.Sequences
