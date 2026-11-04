import PyLean.Sequences.DequeRepeat
import PyLean.Sequences.PopRemove

/-!
Deque methods that run Python code on the deque they are working on: `extend`,
`extendleft` and `+=` over an iterator that changes (or re-initialises) the deque,
`__init__` itself, and the searches `count`, `in`, `index`, `remove` with an `__eq__` that
raises or mutates the deque. Also `d + other` for every kind of operand and `d * n`.
-/

namespace PyLean.Sequences

open PyLean

set_option linter.unusedSectionVars false

variable {α : Type} [Inhabited α]

namespace Deque

/-- A callback keeps the type invariant `WF` and the bound: Python code that acts on the
deque through its methods other than `__init__`. -/
def KeepsWF (f : Deque α → Deque α) : Prop := ∀ d : Deque α, d.WF → (f d).WF ∧ (f d).maxlen = d.maxlen

/-- A `__next__` call that never raises, whatever it does to the deque. -/
def Yields (nx : NextFn α) : Prop := ∀ d, ∃ x, (nx d).1 = .ok x

/-- A `__next__` call that always raises `e`, whatever it does to the deque first. -/
def RaisesAlways (nx : NextFn α) (e : PyExc) : Prop := ∀ d, (nx d).1 = .error e

theorem pushLoop_wf (push : Deque α → α → Int → Deque α) (m : Int)
    (hpush : ∀ (d : Deque α) (x : α), d.WF → d.maxlen = m → (push d x m).WF ∧ (push d x m).maxlen = m) :
    ∀ (nexts : List (NextFn α)) (d : Deque α),
    (∀ nx ∈ nexts, KeepsWF (fun d => (nx d).2)) → d.WF → d.maxlen = m →
    (pushLoop push m nexts d).2.WF ∧ (pushLoop push m nexts d).2.maxlen = m
  | [], d, _, h, hm => ⟨h, hm⟩
  | nx :: rest, d, hk, h, hm => by
    have w1 : (nx d).2.WF := (hk nx (List.mem_cons_self ..) d h).1
    have m1 : (nx d).2.maxlen = d.maxlen := (hk nx (List.mem_cons_self ..) d h).2
    rcases hc : nx d with ⟨r, d1⟩
    rw [hc] at w1 m1
    simp only at w1 m1
    cases r with
    | error e => simp only [pushLoop, hc]; exact ⟨w1, by rw [m1, hm]⟩
    | ok x =>
      simp only [pushLoop, hc]
      obtain ⟨w2, m2⟩ := hpush d1 x w1 (by rw [m1, hm])
      exact pushLoop_wf push m hpush rest _ (fun nx' h' => hk nx' (List.mem_cons_of_mem _ h')) w2 m2

theorem consumeLoop_wf : ∀ (nexts : List (NextFn α)) (d : Deque α),
    (∀ nx ∈ nexts, KeepsWF (fun d => (nx d).2)) → d.WF →
    (consumeLoop nexts d).2.WF ∧ (consumeLoop nexts d).2.maxlen = d.maxlen
  | [], d, _, h => ⟨h, rfl⟩
  | nx :: rest, d, hk, h => by
    have w1 : (nx d).2.WF := (hk nx (List.mem_cons_self ..) d h).1
    have m1 : (nx d).2.maxlen = d.maxlen := (hk nx (List.mem_cons_self ..) d h).2
    rcases hc : nx d with ⟨r, d1⟩
    rw [hc] at w1 m1
    simp only at w1 m1
    cases r with
    | error e => simp only [consumeLoop, hc]; exact ⟨w1, m1⟩
    | ok x =>
      simp only [consumeLoop, hc]
      obtain ⟨a, b⟩ := consumeLoop_wf rest d1 (fun nx' h' => hk nx' (List.mem_cons_of_mem _ h')) w1
      exact ⟨a, by rw [b, m1]⟩

theorem push_right_ok (m : Int) (d : Deque α) (x : α) (h : d.WF) (hm : d.maxlen = m) :
    (d.appendM x m).WF ∧ (d.appendM x m).maxlen = m := by
  have := append_spec d x h
  unfold append at this
  rw [hm] at this
  exact ⟨this.1, this.2.2⟩

theorem push_left_ok (m : Int) (d : Deque α) (x : α) (h : d.WF) (hm : d.maxlen = m) :
    (d.appendleftM x m).WF ∧ (d.appendleftM x m).maxlen = m := by
  have := appendleft_spec d x h
  unfold appendleft at this
  rw [hm] at this
  exact ⟨this.1, this.2.2⟩

theorem heurR_wf (d : Deque α) (h : d.WF) :
    (if d.size = 0 then { d with left := 1, right := 0 } else d).WF ∧
      (if d.size = 0 then { d with left := 1, right := 0 } else d).maxlen = d.maxlen := by
  split
  · rename_i hs
    refine ⟨⟨?_, ?_⟩, rfl⟩
    · rw [layout_iff]; rw [size_eq] at hs; simp only; omega
    · exact h.2
  · exact ⟨h, rfl⟩

theorem heurL_wf (d : Deque α) (h : d.WF) :
    (if d.size = 0 then { d with left := 64 - 1, right := 64 - 2 } else d).WF ∧
      (if d.size = 0 then { d with left := 64 - 1, right := 64 - 2 } else d).maxlen = d.maxlen := by
  split
  · rename_i hs
    refine ⟨⟨?_, ?_⟩, rfl⟩
    · rw [layout_iff]; rw [size_eq] at hs; simp only; omega
    · exact h.2
  · exact ⟨h, rfl⟩

theorem extendRe_wf (d : Deque α) (h : d.WF) (it : ReIter α) (hg : KeepsWF (fun d => (it.getIter d).2))
    (hn : ∀ nx ∈ it.nexts, KeepsWF (fun d => (nx d).2)) :
    (d.extendRe it).2.WF ∧ (d.extendRe it).2.maxlen = d.maxlen := by
  have w1 : (it.getIter d).2.WF := (hg d h).1
  have m1 : (it.getIter d).2.maxlen = d.maxlen := (hg d h).2
  unfold extendRe
  rcases hc : it.getIter d with ⟨r, d1⟩
  rw [hc] at w1 m1
  simp only at w1 m1
  cases r with
  | error e => exact ⟨w1, m1⟩
  | ok u =>
    cases u
    simp only
    split
    · obtain ⟨a, b⟩ := consumeLoop_wf it.nexts d1 hn w1
      exact ⟨a, by rw [b, m1]⟩
    · obtain ⟨w2, m2⟩ := heurR_wf d1 w1
      exact pushLoop_wf appendM d.maxlen (push_right_ok d.maxlen) it.nexts _ hn w2 (by rw [m2, m1])

theorem extendleftRe_wf (d : Deque α) (h : d.WF) (it : ReIter α) (hg : KeepsWF (fun d => (it.getIter d).2))
    (hn : ∀ nx ∈ it.nexts, KeepsWF (fun d => (nx d).2)) :
    (d.extendleftRe it).2.WF ∧ (d.extendleftRe it).2.maxlen = d.maxlen := by
  have w1 : (it.getIter d).2.WF := (hg d h).1
  have m1 : (it.getIter d).2.maxlen = d.maxlen := (hg d h).2
  unfold extendleftRe
  rcases hc : it.getIter d with ⟨r, d1⟩
  rw [hc] at w1 m1
  simp only at w1 m1
  cases r with
  | error e => exact ⟨w1, m1⟩
  | ok u =>
    cases u
    simp only
    split
    · obtain ⟨a, b⟩ := consumeLoop_wf it.nexts d1 hn w1
      exact ⟨a, by rw [b, m1]⟩
    · obtain ⟨w2, m2⟩ := heurL_wf d1 w1
      exact pushLoop_wf appendleftM d.maxlen (push_left_ok d.maxlen) it.nexts _ hn w2 (by rw [m2, m1])

/-- The outcome of the loops for calls that yield, then a fixed ending. -/
theorem pushLoop_outcome (push : Deque α → α → Int → Deque α) (m : Int) (fin : List (NextFn α))
    (r : Py Unit) (hfin : ∀ d, (pushLoop push m fin d).1 = r) :
    ∀ (ys : List (NextFn α)), (∀ y ∈ ys, Yields y) → ∀ d, (pushLoop push m (ys ++ fin) d).1 = r
  | [], _, d => hfin d
  | y :: ys, hy, d => by
    obtain ⟨x, hx⟩ := hy y (List.mem_cons_self ..) d
    rcases hc : y d with ⟨r', d'⟩
    rw [hc] at hx
    simp only at hx
    subst hx
    simp only [List.cons_append, pushLoop, hc]
    exact pushLoop_outcome push m fin r hfin ys (fun y' h' => hy y' (List.mem_cons_of_mem _ h')) _

theorem consumeLoop_outcome (fin : List (NextFn α)) (r : Py Unit) (hfin : ∀ d, (consumeLoop fin d).1 = r) :
    ∀ (ys : List (NextFn α)), (∀ y ∈ ys, Yields y) → ∀ d, (consumeLoop (ys ++ fin) d).1 = r
  | [], _, d => hfin d
  | y :: ys, hy, d => by
    obtain ⟨x, hx⟩ := hy y (List.mem_cons_self ..) d
    rcases hc : y d with ⟨r', d'⟩
    rw [hc] at hx
    simp only at hx
    subst hx
    simp only [List.cons_append, consumeLoop, hc]
    exact consumeLoop_outcome fin r hfin ys (fun y' h' => hy y' (List.mem_cons_of_mem _ h')) _

theorem fin_push (push : Deque α → α → Int → Deque α) (m : Int) (f : NextFn α) (e : PyExc)
    (hf : RaisesAlways f e) (d : Deque α) : (pushLoop push m [f] d).1 = finalizeIterator (some e) := by
  have := hf d
  rcases hc : f d with ⟨r, d'⟩
  rw [hc] at this
  simp only at this
  subst this
  simp only [pushLoop, hc]

theorem fin_consume (f : NextFn α) (e : PyExc) (hf : RaisesAlways f e) (d : Deque α) :
    (consumeLoop [f] d).1 = finalizeIterator (some e) := by
  have := hf d
  rcases hc : f d with ⟨r, d'⟩
  rw [hc] at this
  simp only at this
  subst this
  simp only [consumeLoop, hc]

/-- Both loops of `extendRe` reach the same outcome `r`. -/
theorem extendRe_outcome (d : Deque α) (g : Deque α → Deque α) (ys fin : List (NextFn α)) (r : Py Unit)
    (hy : ∀ y ∈ ys, Yields y) (hp : ∀ m d, (pushLoop appendM m fin d).1 = r)
    (hc : ∀ d, (consumeLoop fin d).1 = r) :
    (d.extendRe ⟨fun d => (.ok (), g d), ys ++ fin⟩).1 = r := by
  unfold extendRe
  simp only
  split
  · exact consumeLoop_outcome fin r hc ys hy _
  · exact pushLoop_outcome appendM _ fin r (hp _) ys hy _

theorem extendleftRe_outcome (d : Deque α) (g : Deque α → Deque α) (ys fin : List (NextFn α)) (r : Py Unit)
    (hy : ∀ y ∈ ys, Yields y) (hp : ∀ m d, (pushLoop appendleftM m fin d).1 = r)
    (hc : ∀ d, (consumeLoop fin d).1 = r) :
    (d.extendleftRe ⟨fun d => (.ok (), g d), ys ++ fin⟩).1 = r := by
  unfold extendleftRe
  simp only
  split
  · exact consumeLoop_outcome fin r hc ys hy _
  · exact pushLoop_outcome appendleftM _ fin r (hp _) ys hy _

end Deque

/-- `d.extend(it)` and `d.extendleft(it)` over an iterator that runs code on
the deque (Python-level `__iter__`/`__next__`, re-entrant; type invariant `WF` of the
deque). For every element type, every deque `d` and every iterator whose `__iter__` and
`__next__` calls each keep the invariant and `maxlen` (any code acting on `d` through its
methods other than `__init__`), the deque the method leaves satisfies the invariant and
keeps `maxlen`, including bounded deques with `maxlen == 0` (the `consume_iterator` path).
The outcome, for every `d` and every iterator whose `__iter__` does anything to `d` and
returns, and whose calls yield (doing anything to `d`) and then optionally end with a call
that raises `e`: `None` when the calls just run out or `e` is `StopIteration`, `e` itself
otherwise; the same with `maxlen == 0`, where the items are dropped. An `__iter__` that
raises `e` makes the method raise `e`, with no `__next__` call. -/
def DequeExtendRe : Prop :=
  ∀ (α : Type) [Inhabited α] (d : Deque α),
    (d.WF → ∀ (it : ReIter α), Deque.KeepsWF (fun d => (it.getIter d).2) →
      (∀ nx ∈ it.nexts, Deque.KeepsWF (fun d => (nx d).2)) →
      ((d.extendRe it).2.WF ∧ (d.extendRe it).2.maxlen = d.maxlen) ∧
      ((d.extendleftRe it).2.WF ∧ (d.extendleftRe it).2.maxlen = d.maxlen)) ∧
    (∀ (g : Deque α → Deque α) (ys : List (NextFn α)), (∀ y ∈ ys, Deque.Yields y) →
      (d.extendRe ⟨fun d => (.ok (), g d), ys⟩).1 = .ok () ∧
      (d.extendleftRe ⟨fun d => (.ok (), g d), ys⟩).1 = .ok () ∧
      ∀ (f : NextFn α) (e : PyExc), Deque.RaisesAlways f e →
        (e = .stopIteration →
          (d.extendRe ⟨fun d => (.ok (), g d), ys ++ [f]⟩).1 = .ok () ∧
          (d.extendleftRe ⟨fun d => (.ok (), g d), ys ++ [f]⟩).1 = .ok ()) ∧
        (e ≠ .stopIteration →
          (d.extendRe ⟨fun d => (.ok (), g d), ys ++ [f]⟩).1 = .error e ∧
          (d.extendleftRe ⟨fun d => (.ok (), g d), ys ++ [f]⟩).1 = .error e)) ∧
    (∀ (e : PyExc) (g : Deque α → Deque α) (nexts : List (NextFn α)),
      d.extendRe ⟨fun d => (.error e, g d), nexts⟩ = (.error e, g d) ∧
      d.extendleftRe ⟨fun d => (.error e, g d), nexts⟩ = (.error e, g d))

theorem dequeExtendRe_proven : DequeExtendRe := by
  intro α _ d
  refine ⟨fun h it hg hn => ⟨Deque.extendRe_wf d h it hg hn, Deque.extendleftRe_wf d h it hg hn⟩,
    fun g ys hy => ?_, fun e g nexts => ⟨rfl, rfl⟩⟩
  have e0 : ∀ m (d : Deque α), (Deque.pushLoop Deque.appendM m [] d).1 = .ok () := fun _ _ => rfl
  have e1 : ∀ m (d : Deque α), (Deque.pushLoop Deque.appendleftM m [] d).1 = .ok () := fun _ _ => rfl
  have e2 : ∀ (d : Deque α), (Deque.consumeLoop [] d).1 = .ok () := fun _ => rfl
  have r0 := Deque.extendRe_outcome d g ys [] _ hy e0 e2
  have l0 := Deque.extendleftRe_outcome d g ys [] _ hy e1 e2
  rw [List.append_nil] at r0 l0
  refine ⟨r0, l0, fun f e hf => ?_⟩
  have r1 := Deque.extendRe_outcome d g ys [f] _ hy (fun m d => Deque.fin_push _ m f e hf d)
    (Deque.fin_consume f e hf)
  have l1 := Deque.extendleftRe_outcome d g ys [f] _ hy (fun m d => Deque.fin_push _ m f e hf d)
    (Deque.fin_consume f e hf)
  refine ⟨fun he => ?_, fun he => ?_⟩
  · subst he
    exact ⟨r1, l1⟩
  · rw [Deque.finalize_some e he] at r1 l1
    exact ⟨r1, l1⟩

/-- `d.__init__(maxlen=m)` with no iterable, as Python code inside an iterator would call
it: keeps the invariant for every deque, with the new bound. -/
theorem reinit_wf (d : Deque α) (h : d.WF) (m : Int) (h0 : 0 ≤ m) (h1 : m ≤ ssizeMax) :
    (d.initRe none (.int m)).2.WF ∧ (d.initRe none (.int m)).2.maxlen = m ∧
      (d.initRe none (.int m)).1 = .ok () ∧ (d.initRe none (.int m)).2.items = [] ∧
      (d.initRe none (.int m)).2.left = (if d.items = [] then d.left else CENTER + 1) := by
  have h' := h.1
  rw [Deque.layout_iff] at h'
  unfold Deque.initRe
  simp only [asSsize]
  rw [iteT ⟨by unfold ssizeMin; unfold ssizeMax at h1; omega, h1⟩]
  simp only [iteF (show ¬ m < 0 by omega)]
  by_cases hs : ({ d with maxlen := m } : Deque α).size > 0
  · rw [iteT hs]
    have hne : d.items ≠ [] := by
      intro he; rw [Deque.size_eq] at hs; simp only [he] at hs; simp at hs
    have hs' : ¬ ({ d with maxlen := m } : Deque α).size = 0 := by omega
    unfold Deque.clear
    rw [iteF hs']
    refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · rw [Deque.layout_iff]; simp [CENTER]
    · rw [Deque.maxOk_iff]; simp only [List.length_nil, Int.natCast_zero]; right; omega
    all_goals (try simp only [iteF hne]) <;> first | rfl | trivial
  · rw [iteF hs]
    have he : d.items = [] := by
      rw [Deque.size_eq] at hs; simp only at hs
      exact List.eq_nil_of_length_eq_zero (by omega)
    refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · rw [Deque.layout_iff]; simp only; exact h'
    · rw [Deque.maxOk_iff]; simp only [he, List.length_nil, Int.natCast_zero]; right; omega
    all_goals (try simp only [iteT he]) <;> first | rfl | trivial | exact he

/-- The bound read once (_collectionsmodule.c:484, :539) is not the deque's bound any more
once an iterator re-initialises the deque with `d.__init__(maxlen=1)`, and the loop goes
on appending under the old one. The property refuted: for every deque and every iterator
whose `__iter__` and `__next__` calls each keep the deque's invariant (`len(d) <= maxlen`
for a bounded deque) — `__init__` included — `extend` and `extendleft` leave a deque that
satisfies it. Neither does: `dequeExtendKeepsBound_neither` breaks each with the same
iterator, and the refutation goes through `extendleft`. -/
def DequeExtendKeepsBound : Prop :=
  ∀ (α : Type) [Inhabited α] (d : Deque α), d.WF → ∀ (it : ReIter α),
    (∀ d : Deque α, d.WF → (it.getIter d).2.WF) → (∀ nx ∈ it.nexts, ∀ d : Deque α, d.WF → (nx d).2.WF) →
    (d.extendRe it).2.WF ∧ (d.extendleftRe it).2.WF

/-- `__iter__` runs `d.__init__(maxlen=1)` and returns `iter([1, 2, 3])`. -/
def reinitIter : ReIter Int :=
  ⟨fun d => (.ok (), (d.initRe none (.int 1)).2), [fun d => (.ok 1, d), fun d => (.ok 2, d), fun d => (.ok 3, d)]⟩

theorem new_deque_wf : (Deque.new "deque" : Deque Int).WF := by
  refine ⟨?_, ?_⟩
  · rw [Deque.layout_iff]; decide
  · rw [Deque.maxOk_iff]; decide

/-- `deque().extend(X())` and `deque().extendleft(X())`, `X.__iter__` running
`d.__init__(maxlen=1)` and returning `iter([1, 2, 3])`, both leave three items under
`maxlen == 1`: `deque([1, 2, 3], maxlen=1)` and `deque([3, 2, 1], maxlen=1)`. -/
theorem reinitIter_outcome :
    ((Deque.new "deque" : Deque Int).extendRe reinitIter).2.items = [1, 2, 3] ∧
    ((Deque.new "deque" : Deque Int).extendRe reinitIter).2.maxlen = 1 ∧
    ((Deque.new "deque" : Deque Int).extendleftRe reinitIter).2.items = [3, 2, 1] ∧
    ((Deque.new "deque" : Deque Int).extendleftRe reinitIter).2.maxlen = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem reinitIter_keeps :
    (∀ d : Deque Int, d.WF → (reinitIter.getIter d).2.WF) ∧
    (∀ nx ∈ reinitIter.nexts, ∀ d : Deque Int, d.WF → (nx d).2.WF) :=
  ⟨fun d hd => (reinit_wf d hd 1 (by decide) (by decide)).1,
   fun nx hm d hd => by
    simp only [reinitIter, List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> exact hd⟩

/-- Both halves fail on the same iterator: `extend` (`deque_extend_impl`) and `extendleft`
(`deque_extendleft_impl`) each leave `len(d) == 3 > maxlen == 1`. -/
theorem dequeExtendKeepsBound_neither :
    ¬ (∀ (d : Deque Int), d.WF → ∀ (it : ReIter Int),
        (∀ d : Deque Int, d.WF → (it.getIter d).2.WF) → (∀ nx ∈ it.nexts, ∀ d : Deque Int, d.WF → (nx d).2.WF) →
        (d.extendRe it).2.WF) ∧
    ¬ (∀ (d : Deque Int), d.WF → ∀ (it : ReIter Int),
        (∀ d : Deque Int, d.WF → (it.getIter d).2.WF) → (∀ nx ∈ it.nexts, ∀ d : Deque Int, d.WF → (nx d).2.WF) →
        (d.extendleftRe it).2.WF) := by
  obtain ⟨i1, m1, i2, m2⟩ := reinitIter_outcome
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := (h _ new_deque_wf reinitIter reinitIter_keeps.1 reinitIter_keeps.2).2
    rw [Deque.maxOk_iff, i1, m1] at this
    simp at this
  · have := (h _ new_deque_wf reinitIter reinitIter_keeps.1 reinitIter_keeps.2).2
    rw [Deque.maxOk_iff, i2, m2] at this
    simp at this

theorem dequeExtendKeepsBound_refuted : ¬ DequeExtendKeepsBound :=
  fun h => dequeExtendKeepsBound_neither.2 (fun d hd it hg hn => (h Int d hd it hg hn).2)

/-! ### The bound applied after a re-initialisation, and the layout -/

namespace Deque

theorem appendM_layout (d : Deque α) (x : α) (m : Int) (h : d.Layout) : (d.appendM x m).Layout := by
  have h' := h
  rw [layout_iff] at h'
  unfold appendM
  simp only
  generalize hd1 : ({ d with items := d.items ++ [x], right := (if d.right = 64 - 1 then -1 else d.right) + 1 } : Deque α) = d1
  have hl1 : d1.Layout := by
    rw [← hd1, layout_iff]; simp only [List.length_append, List.length_singleton]
    split <;> omega
  by_cases ht : d1.needsTrim m = true
  · rw [iteT ht]
    have hne : d1.items ≠ [] := by rw [← hd1]; simp
    obtain ⟨d', hp, hl, _, _⟩ := popleft_spec d1 hl1 hne
    rw [hp]; exact hl
  · rw [iteF ht]
    subst hd1
    rw [layout_iff] at hl1 ⊢
    exact hl1

theorem appendleftM_layout (d : Deque α) (x : α) (m : Int) (h : d.Layout) : (d.appendleftM x m).Layout := by
  have h' := h
  rw [layout_iff] at h'
  unfold appendleftM
  simp only
  generalize hd1 : ({ d with items := x :: d.items, left := (if d.left = 0 then 64 else d.left) - 1 } : Deque α) = d1
  have hl1 : d1.Layout := by
    rw [← hd1, layout_iff]; simp only [List.length_cons]
    split <;> omega
  by_cases ht : d1.needsTrim m = true
  · rw [iteT ht]
    have hne : d1.items ≠ [] := by rw [← hd1]; simp
    obtain ⟨d', hp, hl, _, _⟩ := pop_spec d1 hl1 hne
    rw [hp]; exact hl
  · rw [iteF ht]
    subst hd1
    rw [layout_iff] at hl1 ⊢
    exact hl1

/-- A callback keeps the block layout (whatever it does to `maxlen`): Python code acting on
the deque through any of its methods, `__init__` included. -/
def KeepsLayout (f : Deque α → Deque α) : Prop := ∀ d : Deque α, d.Layout → (f d).Layout

theorem pushLoop_layout (push : Deque α → α → Int → Deque α) (m : Int)
    (hpush : ∀ (d : Deque α) (x : α), d.Layout → (push d x m).Layout) :
    ∀ (nexts : List (NextFn α)) (d : Deque α),
    (∀ nx ∈ nexts, KeepsLayout (fun d => (nx d).2)) → d.Layout → (pushLoop push m nexts d).2.Layout
  | [], d, _, h => h
  | nx :: rest, d, hk, h => by
    have w1 : (nx d).2.Layout := hk nx (List.mem_cons_self ..) d h
    rcases hc : nx d with ⟨r, d1⟩
    rw [hc] at w1
    cases r with
    | error e => simp only [pushLoop, hc]; exact w1
    | ok x =>
      simp only [pushLoop, hc]
      exact pushLoop_layout push m hpush rest _ (fun nx' h' => hk nx' (List.mem_cons_of_mem _ h')) (hpush d1 x w1)

theorem consumeLoop_layout : ∀ (nexts : List (NextFn α)) (d : Deque α),
    (∀ nx ∈ nexts, KeepsLayout (fun d => (nx d).2)) → d.Layout → (consumeLoop nexts d).2.Layout
  | [], d, _, h => h
  | nx :: rest, d, hk, h => by
    have w1 : (nx d).2.Layout := hk nx (List.mem_cons_self ..) d h
    rcases hc : nx d with ⟨r, d1⟩
    rw [hc] at w1
    cases r with
    | error e => simp only [consumeLoop, hc]; exact w1
    | ok x =>
      simp only [consumeLoop, hc]
      exact consumeLoop_layout rest d1 (fun nx' h' => hk nx' (List.mem_cons_of_mem _ h')) w1

theorem heurR_layout (d : Deque α) (h : d.Layout) :
    (if d.size = 0 then { d with left := 1, right := 0 } else d).Layout := by
  split
  · rename_i hs; rw [layout_iff]; rw [size_eq] at hs; simp only; omega
  · exact h

theorem heurL_layout (d : Deque α) (h : d.Layout) :
    (if d.size = 0 then { d with left := 64 - 1, right := 64 - 2 } else d).Layout := by
  split
  · rename_i hs; rw [layout_iff]; rw [size_eq] at hs; simp only; omega
  · exact h

theorem extendRe_layout (d : Deque α) (h : d.Layout) (it : ReIter α) (hg : KeepsLayout (fun d => (it.getIter d).2))
    (hn : ∀ nx ∈ it.nexts, KeepsLayout (fun d => (nx d).2)) : (d.extendRe it).2.Layout := by
  have w1 : (it.getIter d).2.Layout := hg d h
  unfold extendRe
  rcases hc : it.getIter d with ⟨r, d1⟩
  rw [hc] at w1
  cases r with
  | error e => exact w1
  | ok u =>
    simp only
    split
    · exact consumeLoop_layout it.nexts d1 hn w1
    · exact pushLoop_layout appendM d.maxlen (fun d x h => appendM_layout d x _ h) it.nexts _ hn (heurR_layout d1 w1)

theorem extendleftRe_layout (d : Deque α) (h : d.Layout) (it : ReIter α) (hg : KeepsLayout (fun d => (it.getIter d).2))
    (hn : ∀ nx ∈ it.nexts, KeepsLayout (fun d => (nx d).2)) : (d.extendleftRe it).2.Layout := by
  have w1 : (it.getIter d).2.Layout := hg d h
  unfold extendleftRe
  rcases hc : it.getIter d with ⟨r, d1⟩
  rw [hc] at w1
  cases r with
  | error e => exact w1
  | ok u =>
    simp only
    split
    · exact consumeLoop_layout it.nexts d1 hn w1
    · exact pushLoop_layout appendleftM d.maxlen (fun d x h => appendleftM_layout d x _ h) it.nexts _ hn (heurL_layout d1 w1)

/-- The loops over an iterator that does not touch the deque, with the bound `m` fixed. -/
theorem pushLoop_pure_fixed (push : Deque α → α → Int → Deque α) (m : Int) (e : Option PyExc) (xs : List α) :
    ∀ d : Deque α, pushLoop push m (ReIter.ofList xs e).nexts d =
      (finalizeIterator e, xs.foldl (fun d x => push d x m) d) := by
  rw [ofList_nexts]
  induction xs with
  | nil => intro d; exact pushLoop_end _ _ _ _
  | cons x xs ih =>
    intro d
    simp only [List.map_cons, List.cons_append, pushLoop, List.foldl_cons]
    exact ih _

theorem foldl_appendM_fixed (m : Int) (hm0 : m = -1 ∨ 0 < m) (xs : List α) : ∀ (d : Deque α), d.Layout →
    (m < 0 ∨ (d.items.length : Int) ≤ m) →
    (xs.foldl (fun d x => d.appendM x m) d).items = keepLast m (d.items ++ xs) ∧
    (xs.foldl (fun d x => d.appendM x m) d).maxlen = d.maxlen := by
  induction xs with
  | nil => intro d _ hm; exact ⟨by rw [List.append_nil, keepLast_of_le _ _ hm]; rfl, rfl⟩
  | cons x xs ih =>
    intro d h hm
    simp only [List.foldl_cons]
    obtain ⟨hl, hi, hmx⟩ := appendM_spec d x m h hm
    have hm' : m < 0 ∨ ((d.appendM x m).items.length : Int) ≤ m := by
      rw [hi]
      rcases hm0 with hp | hp
      · left; omega
      · right; exact length_keepLast_le _ _ (by omega)
    obtain ⟨h2, h3⟩ := ih _ hl hm'
    refine ⟨?_, by rw [h3, hmx]⟩
    rw [h2, hi]
    unfold keepLast
    split
    · simp
    · rw [keepLast_keepLast]; simp

theorem foldl_appendleftM_fixed (m : Int) (hm0 : m = -1 ∨ 0 < m) (xs : List α) : ∀ (d : Deque α), d.Layout →
    (m < 0 ∨ (d.items.length : Int) ≤ m) →
    (xs.foldl (fun d x => d.appendleftM x m) d).items = keepFirst m (xs.reverse ++ d.items) ∧
    (xs.foldl (fun d x => d.appendleftM x m) d).maxlen = d.maxlen := by
  induction xs with
  | nil => intro d _ hm; exact ⟨by rw [List.reverse_nil, List.nil_append, keepFirst_of_le _ _ hm]; rfl, rfl⟩
  | cons x xs ih =>
    intro d h hm
    simp only [List.foldl_cons]
    obtain ⟨hl, hi, hmx⟩ := appendleftM_spec d x m h hm
    have hm' : m < 0 ∨ ((d.appendleftM x m).items.length : Int) ≤ m := by
      rw [hi]
      rcases hm0 with hp | hp
      · left; omega
      · right; exact length_keepFirst_le _ _ (by omega)
    obtain ⟨h2, h3⟩ := ih _ hl hm'
    refine ⟨?_, by rw [h3, hmx]⟩
    rw [h2, hi]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
    unfold keepFirst
    split
    · rfl
    · exact take_append_take _ _ _

end Deque

/-- An iterator whose `__iter__` runs `d.__init__(maxlen=m')` and returns an iterator over
`xs` that ends with `e` (`none`: exhaustion) and does not touch the deque. -/
def reinitWith (m' : Int) (xs : List α) (e : Option PyExc) : ReIter α :=
  ⟨fun d => (.ok (), (d.initRe none (.int m')).2), (ReIter.ofList xs e).nexts⟩

/-- What `extend` and `extendleft` do when the iterable re-initialises the deque
(`deque_extend_impl`, `deque_extendleft_impl`; type invariant `WF`, no hypothesis on the
iterator beyond keeping the block layout). For every deque, every iterator whose `__iter__`
and `__next__` calls keep the block layout — any change of `maxlen` included, so
`d.__init__(maxlen=...)` is allowed — both leave a valid block layout (the length bound is
what can break, `DequeExtendKeepsBound`). And for every `0 <= m' <= sys.maxsize`, every `xs`
and every ending `e`, an `__iter__` that runs `d.__init__(maxlen=m')` and then yields `xs`
makes them return `None` or raise `e` as usual, and leaves the deque with bound `m'` but
holding the last (`extend`) or first (`extendleft`, reversed) `d.maxlen` items of `xs`, under
the bound `d` had on entry (:484, :539), nothing at all if that bound was 0
(`consume_iterator`); an unbounded entry keeps every item. -/
def DequeExtendStaleBound : Prop :=
  ∀ (α : Type) [Inhabited α] (d : Deque α), d.WF →
    (∀ (it : ReIter α), Deque.KeepsLayout (fun d => (it.getIter d).2) →
      (∀ nx ∈ it.nexts, Deque.KeepsLayout (fun d => (nx d).2)) →
      (d.extendRe it).2.Layout ∧ (d.extendleftRe it).2.Layout) ∧
    ∀ (m' : Int), 0 ≤ m' → m' ≤ ssizeMax → ∀ (xs : List α) (e : Option PyExc),
      (d.extendRe (reinitWith m' xs e)).1 = finalizeIterator e ∧
      (d.extendRe (reinitWith m' xs e)).2.items = (if d.maxlen = 0 then [] else keepLast d.maxlen xs) ∧
      (d.extendRe (reinitWith m' xs e)).2.maxlen = m' ∧
      (d.extendleftRe (reinitWith m' xs e)).1 = finalizeIterator e ∧
      (d.extendleftRe (reinitWith m' xs e)).2.items =
        (if d.maxlen = 0 then [] else keepFirst d.maxlen xs.reverse) ∧
      (d.extendleftRe (reinitWith m' xs e)).2.maxlen = m'

theorem dequeExtendStaleBound_proven : DequeExtendStaleBound := by
  intro α _ d h
  refine ⟨fun it hg hn => ⟨Deque.extendRe_layout d h.1 it hg hn, Deque.extendleftRe_layout d h.1 it hg hn⟩,
    fun m' h0 h1 xs e => ?_⟩
  obtain ⟨w1, mx1, _, it1, _⟩ := reinit_wf d h m' h0 h1
  generalize hd1 : (d.initRe none (.int m')).2 = d1 at w1 mx1 it1
  have er : d.extendRe (reinitWith m' xs e) =
      if d.maxlen = 0 then Deque.consumeLoop (ReIter.ofList xs e).nexts d1
      else Deque.pushLoop Deque.appendM d.maxlen (ReIter.ofList xs e).nexts
        (if d1.size = 0 then { d1 with left := 1, right := 0 } else d1) := by
    unfold Deque.extendRe reinitWith; simp only [hd1]
  have el : d.extendleftRe (reinitWith m' xs e) =
      if d.maxlen = 0 then Deque.consumeLoop (ReIter.ofList xs e).nexts d1
      else Deque.pushLoop Deque.appendleftM d.maxlen (ReIter.ofList xs e).nexts
        (if d1.size = 0 then { d1 with left := 64 - 1, right := 64 - 2 } else d1) := by
    unfold Deque.extendleftRe reinitWith; simp only [hd1]
  rw [er, el]
  by_cases hz : d.maxlen = 0
  · rw [iteT hz, iteT hz, iteT hz, iteT hz, Deque.ofList_nexts, Deque.consumeLoop_pure]
    exact ⟨rfl, it1, mx1, rfl, it1, mx1⟩
  · rw [iteF hz, iteF hz, iteF hz, iteF hz, Deque.pushLoop_pure_fixed, Deque.pushLoop_pure_fixed]
    have hm0 : d.maxlen = -1 ∨ 0 < d.maxlen := by
      rcases Deque.maxlen_cases d h with a | a | a
      · exact Or.inl a
      · exact absurd a hz
      · exact Or.inr a
    have lr := Deque.heurR_layout d1 w1.1
    have ll := Deque.heurL_layout d1 w1.1
    have ir : (if d1.size = 0 then { d1 with left := 1, right := 0 } else d1).items = [] := by
      split <;> exact it1
    have il : (if d1.size = 0 then { d1 with left := 64 - 1, right := 64 - 2 } else d1).items = [] := by
      split <;> exact it1
    have mr : (if d1.size = 0 then { d1 with left := 1, right := 0 } else d1).maxlen = m' := by
      split <;> exact mx1
    have ml : (if d1.size = 0 then { d1 with left := 64 - 1, right := 64 - 2 } else d1).maxlen = m' := by
      split <;> exact mx1
    obtain ⟨a1, a2⟩ := Deque.foldl_appendM_fixed d.maxlen hm0 xs _ lr (by rw [ir]; simp; omega)
    obtain ⟨b1, b2⟩ := Deque.foldl_appendleftM_fixed d.maxlen hm0 xs _ ll (by rw [il]; simp; omega)
    rw [ir, List.nil_append] at a1
    rw [il, List.append_nil] at b1
    exact ⟨rfl, a1, by rw [a2, mr], rfl, b1, by rw [b2, ml]⟩

/-! ### `d += it` -/

/-- `d += it` (`deque_inplace_concat`, _collectionsmodule.c:578-590), for every deque and
every iterator, re-entrant ones included (no hypothesis): the deque is left exactly as
`d.extend(it)` leaves it; when `extend` returns `None`, `+=` returns the deque itself (`d`,
not `None`), and when it raises `e`, `+=` raises `e`. In particular, for every `WF` deque
and an iterator over `xs` that does not touch it, `d += xs` returns `d` holding the last
`maxlen` items of `list(d) + xs` (also when it ends with `StopIteration`), an iterator
raising `e` after `xs` raises `e` with those items kept, and a non-iterable raises
`TypeError` with the deque unchanged. -/
def DequeIAdd : Prop :=
  ∀ (α : Type) [Inhabited α] (d : Deque α),
    (∀ (it : ReIter α),
      (d.iaddRe it).2 = (d.extendRe it).2 ∧
      ((d.extendRe it).1 = .ok () → (d.iaddRe it).1 = .ok .self) ∧
      (∀ e, (d.extendRe it).1 = .error e → (d.iaddRe it).1 = .error e)) ∧
    (d.WF → ∀ (xs : List α),
      (∀ e : Option PyExc, (e = none ∨ e = some .stopIteration) →
        (d.iadd (.iter xs e)).1 = .ok .self ∧ (d.iadd (.iter xs e)).2.items = keepLast d.maxlen (d.items ++ xs)) ∧
      (∀ e : PyExc, e ≠ .stopIteration →
        (d.iadd (.iter xs (some e))).1 = .error e ∧
        (d.iadd (.iter xs (some e))).2.items = keepLast d.maxlen (d.items ++ xs)) ∧
      (∀ t, d.iadd (.notIterable t) = (.error (notIterableErr t), d)))

theorem iaddRe_gen (d : Deque α) (it : ReIter α) :
    (d.iaddRe it).2 = (d.extendRe it).2 ∧
    ((d.extendRe it).1 = .ok () → (d.iaddRe it).1 = .ok .self) ∧
    (∀ e, (d.extendRe it).1 = .error e → (d.iaddRe it).1 = .error e) := by
  unfold Deque.iaddRe
  rcases d.extendRe it with ⟨r, d'⟩
  cases r with
  | ok u =>
    refine ⟨rfl, fun _ => rfl, fun e h => ?_⟩
    cases h
  | error e' =>
    refine ⟨rfl, fun h => ?_, fun e h => ?_⟩
    · cases h
    · cases h; rfl

theorem dequeIAdd_proven : DequeIAdd := by
  intro α _ d
  refine ⟨iaddRe_gen d, fun h xs => ⟨fun e he => ?_, fun e he => ?_, fun t => rfl⟩⟩
  · have hx := Deque.extendRe_ofList d xs e
    have hf : finalizeIterator e = .ok () := by rcases he with he | he <;> subst he <;> rfl
    obtain ⟨g1, g2, _⟩ := iaddRe_gen d (.ofList xs e)
    rw [hx, hf] at g2
    refine ⟨g2 rfl, ?_⟩
    show (d.iaddRe (.ofList xs e)).2.items = _
    rw [g1, hx]
    exact (Deque.extend_spec d xs h).2.1
  · have hx := Deque.extendRe_ofList d xs (some e)
    obtain ⟨g1, _, g3⟩ := iaddRe_gen d (.ofList xs (some e))
    rw [hx, Deque.finalize_some e he] at g3
    refine ⟨g3 e rfl, ?_⟩
    show (d.iaddRe (.ofList xs (some e))).2.items = _
    rw [g1, hx]
    exact (Deque.extend_spec d xs h).2.1

/-! ### `__init__` and `__new__` -/

/-- `deque.__new__` and `deque.__init__` (`deque_new`, `deque_init_impl`), for every element
type and type name: a new deque is empty, unbounded (`maxlen` is `None` before any
`__init__`), centred in its one block, and satisfies the invariant. For every deque `d`
(type invariant `WF`), not only a fresh one: `d.__init__(xs, maxlen)` with
`0 <= maxlen <= sys.maxsize` or no `maxlen` first empties `d`, then holds the last `maxlen`
items of `xs`; an iterator that raises `e` (not `StopIteration`) after yielding `xs` makes
`__init__` raise `e` with those items in `d`; an invalid `maxlen` raises before anything
is cleared, so `d` is unchanged. `d.__init__()` without an iterable empties `d` without
moving an empty deque's block indices, unlike `d.__init__([])`, which starts filling from
the left edge of the block (`deque()` and `deque([])` lay their items out differently, as
`__sizeof__` shows once they grow). -/
def DequeInit : Prop :=
  ∀ (α : Type) [Inhabited α] (t : String),
    (Deque.new t : Deque α).WF ∧ (Deque.new t : Deque α).getMaxlen = none ∧
      (Deque.new t : Deque α).items = [] ∧ (Deque.new t : Deque α).left = CENTER + 1 ∧
    ∀ (d : Deque α), d.WF →
      (∀ (xs : List α) (m : Int), 0 ≤ m → m ≤ ssizeMax →
        (d.init (.iter xs none) (.int m)).1 = .ok () ∧
        (d.init (.iter xs none) (.int m)).2.items = keepLast m xs ∧
        (d.init (.iter xs none) (.int m)).2.maxlen = m ∧
        (∀ e, e ≠ .stopIteration → (d.init (.iter xs (some e)) (.int m)).1 = .error e ∧
          (d.init (.iter xs (some e)) (.int m)).2.items = keepLast m xs) ∧
        (d.initRe none (.int m)).1 = .ok () ∧ (d.initRe none (.int m)).2.items = [] ∧
        (d.initRe none (.int m)).2.left = (if d.items = [] then d.left else CENTER + 1) ∧
        (m ≠ 0 → (d.init (.iter [] none) (.int m)).2.left = 1)) ∧
      (∀ xs : List α, (d.init (.iter xs none) .absent).1 = .ok () ∧
        (d.init (.iter xs none) .absent).2.items = xs ∧ (d.init (.iter xs none) .absent).2.maxlen = -1) ∧
      (∀ src : PyIterable α, d.init src .other = (.error (.typeError "an integer is required"), d)) ∧
      (∀ (src : PyIterable α) (m : Int), m < 0 → ssizeMin ≤ m →
        d.init src (.int m) = (.error (.valueError "maxlen must be non-negative"), d))

/-- `d.__init__(iterable, m)` for `0 <= m <= sys.maxsize`: the cleared deque with bound `m`,
then `extendRe`. -/
theorem init_int (d : Deque α) (src : PyIterable α) (m : Int) (h0 : 0 ≤ m) (h1 : m ≤ ssizeMax) :
    d.init src (.int m) =
      (let d1 : Deque α := { d with maxlen := m }
       (if d1.size > (0 : Int) then d1.clear else d1).extendRe (.ofIterable src)) := by
  unfold Deque.init Deque.initRe
  simp only [asSsize]
  rw [iteT ⟨by unfold ssizeMin; unfold ssizeMax at h1; omega, h1⟩]
  simp only [iteF (show ¬ m < 0 by omega)]

/-- The cleared deque with bound `m`, any `m` that is `-1` or non-negative. -/
theorem cleared_wf (d : Deque α) (h : d.WF) (m : Int) (hm : m = -1 ∨ 0 ≤ m) :
    let d1 : Deque α := { d with maxlen := m }
    (if d1.size > (0 : Int) then d1.clear else d1).WF ∧
      (if d1.size > (0 : Int) then d1.clear else d1).items = [] ∧
      (if d1.size > (0 : Int) then d1.clear else d1).maxlen = m := by
  intro d1
  have h' := h.1
  rw [Deque.layout_iff] at h'
  by_cases hs : d1.size > 0
  · rw [iteT hs]
    have hs' : ¬ d1.size = 0 := by omega
    unfold Deque.clear
    rw [iteF hs']
    refine ⟨⟨?_, ?_⟩, rfl, rfl⟩
    · rw [Deque.layout_iff]; simp [CENTER]
    · rw [Deque.maxOk_iff]; simp only [List.length_nil, Int.natCast_zero, d1]; omega
  · rw [iteF hs]
    have he : d.items = [] := by
      simp only [d1, Deque.size_eq] at hs
      exact List.eq_nil_of_length_eq_zero (by omega)
    refine ⟨⟨?_, ?_⟩, he, rfl⟩
    · rw [Deque.layout_iff]; exact h'
    · rw [Deque.maxOk_iff]; simp only [d1, he, List.length_nil, Int.natCast_zero]; omega

theorem dequeInit_proven : DequeInit := by
  intro α _ t
  refine ⟨new_wf t (-1) (Or.inl rfl), rfl, rfl, rfl, fun d h => ⟨fun xs m h0 h1 => ?_, fun xs => ?_,
    fun src => rfl, fun src m hm hm' => ?_⟩⟩
  · obtain ⟨w, i, mx⟩ := cleared_wf d h m (Or.inr h0)
    obtain ⟨_, _, r3, r4, r5⟩ := reinit_wf d h m h0 h1
    try simp only at w i mx
    have hx := Deque.extend_spec _ xs w
    have key : ∀ (ys : List α) (e : Option PyExc), d.init (.iter ys e) (.int m) =
        (finalizeIterator e, (if ({ d with maxlen := m } : Deque α).size > (0 : Int) then
          ({ d with maxlen := m } : Deque α).clear else { d with maxlen := m }).extend ys) := by
      intro ys e
      rw [init_int d _ m h0 h1]
      exact Deque.extendRe_ofList _ ys e
    refine ⟨by rw [key]; rfl, by rw [key, hx.2.1, i, mx]; rfl, by rw [key, hx.2.2, mx],
      fun e he => ⟨by rw [key]; exact Deque.finalize_some e he, by rw [key, hx.2.1, i, mx]; rfl⟩,
      r3, r4, r5, fun hm0 => ?_⟩
    rw [key]
    have hs : (if ({ d with maxlen := m } : Deque α).size > (0 : Int) then
        ({ d with maxlen := m } : Deque α).clear else { d with maxlen := m }).size = 0 := by
      rw [Deque.size_eq, i]; rfl
    show (Deque.extend _ []).left = 1
    unfold Deque.extend
    rw [mx, iteF hm0]
    simp only [List.foldl_nil]
    rw [iteT hs]
  · obtain ⟨w, i, mx⟩ := cleared_wf d h (-1) (Or.inl rfl)
    try simp only at w i mx
    have hx := Deque.extend_spec _ xs w
    unfold Deque.init Deque.initRe
    simp only [ReIter.ofIterable]
    rw [Deque.extendRe_ofList]
    refine ⟨rfl, by rw [hx.2.1, i, mx]; rfl, by rw [hx.2.2, mx]⟩
  · unfold Deque.init Deque.initRe
    simp only [asSsize]
    rw [iteT ⟨hm', by unfold ssizeMax; omega⟩]
    simp only [iteT hm]

/-! ### `count`, `in`, `index`, `remove` with a re-entrant `__eq__` -/

namespace Deque

theorem scanLoop_skip (d : Deque α) (hL : d.Layout) (cmp : Cmp α) (v : α) (cf : Bool) (me : PyExc) :
    ∀ (k n : Nat) (p b j : Int), b * 64 + j - d.left = p → 0 ≤ j → j < 64 → 0 ≤ p → p + k ≤ d.size →
    (∀ q : Nat, q < k → cmp d (ix d.items (p + q)) v = (.ok false, d)) →
    ∃ b' j', b' * 64 + j' - d.left = p + k ∧ 0 ≤ j' ∧ j' < 64 ∧
      scanLoop cmp v d.state cf me (k + n) p b j d = scanLoop cmp v d.state cf me n (p + k) b' j' d := by
  have h' := hL
  rw [layout_iff] at h'
  intro k
  induction k with
  | zero => intro n p b j hp h0 h1 _ _ _; exact ⟨b, j, by omega, h0, h1, by simp⟩
  | succ k ih =>
    intro n p b j hp h0 h1 hp0 hk hq
    rw [show k + 1 + n = (k + n) + 1 by omega]
    simp only [scanLoop]
    rw [read_ok d hL b j (by dq_omega) (by dq_omega) h0 h1 (by omega) (by dq_omega)]
    simp only [hp]
    have h0q := hq 0 (by omega)
    rw [show p + ((0 : Nat) : Int) = p by omega] at h0q
    rw [h0q]
    simp only [Bool.and_false, Bool.false_eq_true, ite_false, ne_eq, not_true_eq_false]
    obtain ⟨c1, c2, c3⟩ := step1_pos d b j p hp h0 h1
    obtain ⟨b', j', e1, e2, e3, e4⟩ := ih n (p + 1) _ _ c1 c2 c3 (by omega) (by omega)
      (fun q hq' => by
        have := hq (q + 1) (by omega)
        rw [show p + ((q + 1 : Nat) : Int) = p + 1 + q by omega] at this
        exact this)
    refine ⟨b', j', by rw [e1]; omega, e2, e3, ?_⟩
    rw [e4, show p + 1 + (k : Int) = p + ((k + 1 : Nat) : Int) by omega]

theorem countLoop_skip (d : Deque α) (hL : d.Layout) (cmp : Cmp α) (v : α) :
    ∀ (k n : Nat) (p b j c : Int), b * 64 + j - d.left = p → 0 ≤ j → j < 64 → 0 ≤ p → p + k ≤ d.size →
    (∀ q : Nat, q < k → cmp d (ix d.items (p + q)) v = (.ok false, d)) →
    ∃ b' j', b' * 64 + j' - d.left = p + k ∧ 0 ≤ j' ∧ j' < 64 ∧
      countLoop cmp v d.state (k + n) b j c d = countLoop cmp v d.state n b' j' c d := by
  have h' := hL
  rw [layout_iff] at h'
  intro k
  induction k with
  | zero => intro n p b j c hp h0 h1 _ _ _; exact ⟨b, j, by omega, h0, h1, by simp⟩
  | succ k ih =>
    intro n p b j c hp h0 h1 hp0 hk hq
    rw [show k + 1 + n = (k + n) + 1 by omega]
    simp only [countLoop]
    rw [read_ok d hL b j (by dq_omega) (by dq_omega) h0 h1 (by omega) (by dq_omega)]
    simp only [hp]
    have h0q := hq 0 (by omega)
    rw [show p + ((0 : Nat) : Int) = p by omega] at h0q
    rw [h0q]
    simp only [Bool.false_eq_true, ite_false, Int.add_zero, ne_eq, not_true_eq_false]
    obtain ⟨c1, c2, c3⟩ := step1_pos d b j p hp h0 h1
    obtain ⟨b', j', e1, e2, e3, e4⟩ := ih n (p + 1) _ _ c c1 c2 c3 (by omega) (by omega)
      (fun q hq' => by
        have := hq (q + 1) (by omega)
        rw [show p + ((q + 1 : Nat) : Int) = p + 1 + q by omega] at this
        exact this)
    exact ⟨b', j', by rw [e1]; omega, e2, e3, e4⟩

/-- One step of `scanLoop` at a valid cursor. -/
theorem scanLoop_at (d : Deque α) (hL : d.Layout) (cmp : Cmp α) (v : α) (st : Nat) (cf : Bool) (me : PyExc)
    (n : Nat) (p b j : Int) (hp : b * 64 + j - d.left = p) (h0 : 0 ≤ j) (h1 : j < 64) (hp0 : 0 ≤ p)
    (hk : p < d.size) :
    scanLoop cmp v st cf me (n + 1) p b j d =
      match cmp d (ix d.items p) v with
      | (.error e, d) => (.error e, d)
      | (.ok c, d) =>
        if !cf && c then (.ok (some p), d)
        else if st ≠ d.state then (.error me, d)
        else if c then (.ok (some p), d)
        else scanLoop cmp v st cf me n (p + 1) (step1 b j).1 (step1 b j).2 d := by
  have h' := hL
  rw [layout_iff] at h'
  simp only [scanLoop]
  rw [read_ok d hL b j (by dq_omega) (by dq_omega) h0 h1 (by omega) (by dq_omega)]
  simp only [hp]
  rfl

theorem countLoop_at (d : Deque α) (hL : d.Layout) (cmp : Cmp α) (v : α) (st : Nat)
    (n : Nat) (p b j c : Int) (hp : b * 64 + j - d.left = p) (h0 : 0 ≤ j) (h1 : j < 64) (hp0 : 0 ≤ p)
    (hk : p < d.size) :
    countLoop cmp v st (n + 1) b j c d =
      match cmp d (ix d.items p) v with
      | (.error e, d) => (.error e, d)
      | (.ok r, d) =>
        if st ≠ d.state then (.error (.named "RuntimeError" "deque mutated during iteration"), d)
        else countLoop cmp v st n (step1 b j).1 (step1 b j).2 (c + if r then 1 else 0) d := by
  have h' := hL
  rw [layout_iff] at h'
  simp only [countLoop]
  rw [read_ok d hL b j (by dq_omega) (by dq_omega) h0 h1 (by omega) (by dq_omega)]
  simp only [hp]
  rfl

end Deque

/-- The searches with an `__eq__` that raises or mutates the deque
(`deque_count_impl`, `deque_contains_lock_held`, `deque_index_impl`, `deque_remove_impl`).
For every element type, every deque `d` (type invariant `WF`), every value `v`, every
comparison `cmp` (`PyObject_RichCompareBool(item, v, Py_EQ)`, which may run any code on
`d` and raise), and every position `k < len(d)` such that the comparisons with the items
before `k` are false and leave `d` alone: if the comparison with item `k` raises `e`,
all four methods raise `e`, leaving the deque as the comparison did; if it returns `c`
after changing the deque's mutation counter (any method that moves items), `count`
raises `RuntimeError('deque mutated during iteration')`, `x in d` and
`d.index(x, 0, len(d))` (`deque_index_impl` after its argument conversion) return the
match (`True`, `k`) when `c` is true and raise the same `RuntimeError` otherwise, and
`d.remove(x)` raises `IndexError('deque mutated during iteration')` whatever `c` is (it
checks the counter before the match). -/
def DequeSearchRe : Prop :=
  ∀ (α : Type) [Inhabited α] (d : Deque α), d.WF →
    ∀ (cmp : Cmp α) (v : α) (k : Nat),
    k < d.items.length → (∀ q : Nat, q < k → cmp d (ix d.items q) v = (.ok false, d)) →
    (∀ (e : PyExc) (d' : Deque α), cmp d (ix d.items k) v = (.error e, d') →
      d.count cmp v = (.error e, d') ∧ d.contains cmp v = (.error e, d') ∧
      d.indexC cmp v 0 d.size = (.error e, d') ∧ d.remove cmp v = (.error e, d')) ∧
    (∀ (c : Bool) (d' : Deque α), cmp d (ix d.items k) v = (.ok c, d') → d'.state ≠ d.state →
      d.count cmp v = (.error Deque.mutatedErr, d') ∧
      d.contains cmp v = (if c then .ok true else .error Deque.mutatedErr, d') ∧
      d.indexC cmp v 0 d.size = (if c then .ok (k : Int) else .error Deque.mutatedErr, d') ∧
      d.remove cmp v = (.error (.indexError "deque mutated during iteration"), d'))

/-- `deque_index_impl(d, v, 0, len(d))` scans the whole deque from the left. -/
theorem indexC_full (d : Deque α) (h : d.WF) (cmp : Cmp α) (v : α) :
    d.indexC cmp v 0 d.size =
      match Deque.scanLoop cmp v d.state false Deque.mutatedErr d.items.length 0 0 d.left d with
      | (.ok (some k), d) => (.ok k, d)
      | (.ok none, d) => (.error (.valueError "deque.index(x): x not in deque"), d)
      | (.error e, d) => (.error e, d) := by
  have h' := h.1
  rw [Deque.layout_iff] at h'
  have a1 : ¬ ((0 : Int) < 0) := by decide
  have a2 : ¬ (d.size < 0) := by rw [Deque.size_eq]; omega
  have a3 : ¬ (d.size > d.size) := by omega
  have a4 : ¬ ((0 : Int) > d.size) := by rw [Deque.size_eq]; omega
  have a5 : ¬ ((0 : Int) - 64 > 0) := by decide
  have hrb : ¬ ((0 : Int) > d.rbNum + 1 ∨ (0 : Int) - 1 > d.rbNum) := by
    unfold Deque.rbNum; rw [Deque.size_eq]
    have : 0 ≤ (d.left + (d.items.length : Int) - 1) / 64 := by
      apply Int.ediv_nonneg _ (by decide)
      rcases Nat.eq_zero_or_pos d.items.length with h0 | h0
      · have := h'.2.2.2.2.2 (by omega); omega
      · omega
    omega
  unfold Deque.indexC
  simp only [a1, a2, a3, a4, a5, ite_false, Int.zero_mul, Int.sub_self, Int.toNat_zero, List.range_zero,
    List.foldl_nil]
  rw [iteF hrb, Deque.size_eq, show ((d.items.length : Int) - 0).toNat = d.items.length by omega]
  rfl

theorem dequeSearchRe_proven : DequeSearchRe := by
  intro α _ d h cmp v k hk hpre
  have hL := h.1
  have h' := h.1
  rw [Deque.layout_iff] at h'
  obtain ⟨N, hN⟩ : ∃ N, d.items.length = k + (N + 1) := ⟨d.items.length - k - 1, by omega⟩
  have hpre' : ∀ q : Nat, q < k → cmp d (ix d.items ((0 : Int) + q)) v = (.ok false, d) := by
    intro q hq; rw [Int.zero_add]; exact hpre q hq
  have hsz : (0 : Int) + k ≤ d.size := by rw [Deque.size_eq]; omega
  have hsz' : (0 : Int) + k < d.size := by rw [Deque.size_eq]; omega
  -- the scans of `in`/`index` (match first) and of `remove` (state first)
  obtain ⟨b1, j1, p1, q1, r1, s1⟩ := Deque.scanLoop_skip d hL cmp v false Deque.mutatedErr k (N + 1)
    0 0 d.left (by omega) h'.1 h'.2.1 (by omega) hsz hpre'
  obtain ⟨b2, j2, p2, q2, r2, s2⟩ := Deque.scanLoop_skip d hL cmp v true
    (.indexError "deque mutated during iteration") k (N + 1) 0 0 d.left (by omega) h'.1 h'.2.1 (by omega)
    hsz hpre'
  obtain ⟨b3, j3, p3, q3, r3, s3⟩ := Deque.countLoop_skip d hL cmp v k (N + 1) 0 0 d.left 0 (by omega)
    h'.1 h'.2.1 (by omega) hsz hpre'
  rw [Deque.scanLoop_at d hL _ _ _ _ _ N _ _ _ p1 q1 r1 (by omega) hsz'] at s1
  rw [Deque.scanLoop_at d hL _ _ _ _ _ N _ _ _ p2 q2 r2 (by omega) hsz'] at s2
  rw [Deque.countLoop_at d hL _ _ _ N _ _ _ _ p3 q3 r3 (by omega) hsz'] at s3
  simp only [Int.zero_add] at s1 s2 s3
  have ec : d.count cmp v = Deque.countLoop cmp v d.state (k + (N + 1)) 0 d.left 0 d := by
    unfold Deque.count; rw [← hN]
  have ei : d.contains cmp v = match Deque.scanLoop cmp v d.state false Deque.mutatedErr (k + (N + 1)) 0 0
      d.left d with
      | (.ok r, d) => (.ok r.isSome, d)
      | (.error e, d) => (.error e, d) := by
    unfold Deque.contains; rw [← hN]; rfl
  have ex := indexC_full d h cmp v
  rw [hN] at ex
  have er : d.remove cmp v = match Deque.scanLoop cmp v d.state true
      (.indexError "deque mutated during iteration") (k + (N + 1)) 0 0 d.left d with
      | (.error e, d) => (.error e, d)
      | (.ok none, d) => (.error (.valueError "deque.remove(x): x not in deque"), d)
      | (.ok (some i), d) =>
        match d.delItem i with
        | .ok d => (.ok (), d)
        | .error e => (.error e, d) := by
    unfold Deque.remove; rw [← hN]; rfl
  refine ⟨fun e d' hc => ?_, fun c d' hc hst => ?_⟩
  · rw [hc] at s1 s2 s3
    rw [ec, ei, ex, er, s1, s2, s3]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl
  · rw [hc] at s1 s2 s3
    have hst' : d.state ≠ d'.state := fun x => hst x.symm
    rw [ec, ei, ex, er, s1, s2, s3]
    cases c <;> simp [hst'] <;> rfl

/-! ### `d + other` and `d * n` -/

/-- `d + other` for every kind of right operand (`deque_concat_lock_held`, `deque_concat`),
for every deque `d` (type invariants: `WF`, `maxlen` a `Py_ssize_t`): an operand that is
not a deque instance raises `TypeError("can only concatenate deque (not \"T\") to deque")`
with its type's name; an instance check that raises (a `__class__` property raising
something other than `AttributeError`) raises that; an instance (a deque, or an object
whose `__class__` claims to be one) is iterated into a copy of `d`: an iteration yielding
`xs` gives the last `d.maxlen` items of `list(d) + xs`, with `d`'s bound and type and the
invariant (the same when it ends with `StopIteration`), an iteration that raises `e`
after `xs` raises `e`, and a non-iterable instance raises `TypeError` from `iter()`. -/
def DequeConcatArgs : Prop :=
  ∀ (α : Type) [Inhabited α] (d : Deque α), d.WF → d.maxlen ≤ ssizeMax →
    (∀ t, d.concat (.notInst t) =
      .error (.typeError s!"can only concatenate deque (not \"{t}\") to deque")) ∧
    (∀ e, d.concat (.raises e) = .error e) ∧
    (∀ xs, ∃ n, d.concat (.inst (.iter xs none)) = .ok n ∧ n.WF ∧
      n.items = keepLast d.maxlen (d.items ++ xs) ∧ n.maxlen = d.maxlen ∧ n.tname = d.tname) ∧
    (∀ xs, d.concat (.inst (.iter xs (some .stopIteration))) = d.concat (.inst (.iter xs none))) ∧
    (∀ xs e, e ≠ .stopIteration → d.concat (.inst (.iter xs (some e))) = .error e) ∧
    (∀ t, d.concat (.inst (.notIterable t)) = .error (notIterableErr t))

theorem dequeConcatArgs_proven : DequeConcatArgs := by
  intro α _ d h hm
  obtain ⟨c, h1, w, i, m, t⟩ := copy_spec d h (Or.inr hm)
  have hx := Deque.extend_spec c
  refine ⟨fun t => rfl, fun e => rfl, fun xs => ?_, fun xs => ?_, fun xs e he => ?_, fun t => ?_⟩
  · obtain ⟨w2, i2, m2⟩ := hx xs w
    refine ⟨c.extend xs, ?_, w2, by rw [i2, m, i], by rw [m2, m], by rw [extend_tname, t]⟩
    unfold Deque.concat; rw [h1]; simp only; rw [Deque.extendIter_iter]; rfl
  · unfold Deque.concat; rw [h1]; simp only; rw [Deque.extendIter_iter, Deque.extendIter_iter]; rfl
  · unfold Deque.concat; rw [h1]; simp only; rw [Deque.extendIter_iter, Deque.finalize_some e he]
  · unfold Deque.concat; rw [h1]; rfl

/-- `d * n` (`deque_repeat`: copy, then repeat the copy in place) holds the last `maxlen`
items of `list(d) * n`, for every deque (type invariants: `WF`, `maxlen` a `Py_ssize_t`)
and every `n` in `Py_ssize_t`, when `d` has at most one item or `len(d) * n <= sys.maxsize`;
the result keeps the invariant and `d`'s bound. An `n` outside `Py_ssize_t` raises
`OverflowError` (`sequence_repeat`). -/
def DequeMulChecked : Prop :=
  ∀ (α : Type) [Inhabited α] (d : Deque α), d.WF → d.maxlen ≤ ssizeMax → ∀ (n : Int),
    ((ssizeMin ≤ n → n ≤ ssizeMax → (d.items.length ≤ 1 ∨ (d.items.length : Int) * n ≤ ssizeMax) →
      ∃ d', d.mul n = .ok d' ∧ d'.items = keepLast d.maxlen (rep n.toNat d.items) ∧ d'.WF ∧
        d'.maxlen = d.maxlen) ∧
    ((n < ssizeMin ∨ ssizeMax < n) →
      d.mul n = .error (.overflowError "cannot fit 'int' into an index-sized integer")))

theorem dequeMulChecked_proven : DequeMulChecked := by
  intro α _ d h hm n
  refine ⟨fun hn0 hn1 hsmall => ?_, fun hn => ?_⟩
  · obtain ⟨c, h1, w, i, m, _⟩ := copy_spec d h (Or.inr hm)
    obtain ⟨d', e1, e2, e3, e4⟩ := dequeIRepeatChecked_proven α c w n hn0 hn1 (by rw [i]; exact hsmall)
    have hrc : repeatCount n = .ok n := by unfold repeatCount asSsizeExc; rw [iteT ⟨hn0, hn1⟩]
    have e : d.mul n = c.irepeat n := by
      unfold Deque.mul Deque.irepeat
      rw [hrc]
      simp only [bind, Except.bind]
      rw [h1]
    exact ⟨d', by rw [e, e1], by rw [e2, i, m], e3, by rw [e4, m]⟩
  · have hrc : repeatCount n = .error (.overflowError "cannot fit 'int' into an index-sized integer") := by
      unfold repeatCount asSsizeExc; rw [iteF (by omega)]
    unfold Deque.mul
    rw [hrc]
    rfl

/-- `d * n` keeps the last `maxlen` items of `list(d) * n` whenever that result has at most
`sys.maxsize` items (always for a bounded deque), the analogue of `DequeIRepeat` for `*`. -/
def DequeMul : Prop :=
  ∀ (α : Type) [Inhabited α] (d : Deque α), d.WF → ∀ (n : Int), ssizeMin ≤ n → n ≤ ssizeMax →
    (0 ≤ d.maxlen ∨ (d.items.length : Int) * n ≤ ssizeMax) →
    ∃ d', d.mul n = .ok d' ∧ d'.items = keepLast d.maxlen (rep n.toNat d.items)

theorem dequeMul_refuted : ¬ DequeMul := by
  intro h
  obtain ⟨d', h1, _⟩ := h Int d12 d12_wf (2 ^ 62) (by decide) (by decide) (Or.inl (by decide))
  have : d12.mul (2 ^ 62) = .error memoryError := by decide
  rw [this] at h1
  exact nomatch h1

end PyLean.Sequences
