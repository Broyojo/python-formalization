import PyLean.CoreLibs.Misc.Queue.Model

/-! Properties of `Lib/queue.py`, single-threaded. Statements are about the mirrored methods; the
queue orders are stated over any item type. -/

namespace PyLean.CoreLibs.Misc.Queue

open PyLean PyLean.Accel PyLean.CoreLibs.Misc

variable {α ρ : Type}

/-- `put_nowait` each item in turn; `none` if one fails. -/
def putsOk (I : Impl α ρ) : Q ρ → List α → Option (Q ρ)
  | q, [] => some q
  | q, x :: rest =>
    match putNowait I q x with
    | (q, .ok ()) => putsOk I q rest
    | (_, .error _) => none

/-- `get_nowait` `n` times; `none` if one fails. -/
def getsOk (I : Impl α ρ) : Nat → Q ρ → Option (List α)
  | 0, _ => some []
  | n + 1, q =>
    match getNowait I q with
    | (q, .ok v) => (getsOk I n q).map (v :: ·)
    | (_, .error _) => none

theorem putNowait_room (I : Impl α ρ) (q : Q ρ) (x : α) (hs : q.isShutdown = false)
    (hr : q.maxsize ≤ 0 ∨ (I.qsize q.queue : Int) < q.maxsize) :
    putNowait I q x = putTail I q x := by
  simp only [putNowait, put, hs, Bool.false_eq_true, if_false]
  rcases hr with h | h
  · rw [if_neg (by omega)]
  · by_cases hm : q.maxsize > 0
    · rw [if_pos hm]
      simp only [Bool.not_false, if_true]
      rw [if_neg (by omega)]
    · rw [if_neg hm]

theorem getNowait_some (I : Impl α ρ) (q : Q ρ) (h : I.qsize q.queue ≠ 0) :
    getNowait I q = getTail I q := by
  simp [getNowait, get, h]

theorem fifo_puts (xs : List α) : ∀ q : Q (List α), q.isShutdown = false →
    (q.maxsize ≤ 0 ∨ (q.queue.length : Int) + xs.length ≤ q.maxsize) →
    putsOk fifo q xs =
      some { q with queue := q.queue ++ xs, unfinished := q.unfinished + xs.length } := by
  induction xs with
  | nil => intro q _ _; simp [putsOk]
  | cons x rest ih =>
    intro q hs hr
    simp only [List.length_cons] at hr
    have h1 : putNowait fifo q x =
        ({ q with queue := q.queue ++ [x], unfinished := q.unfinished + 1 }, .ok ()) := by
      rw [putNowait_room _ _ _ hs (by simp only [fifo]; omega)]
      rfl
    simp only [putsOk, h1]
    rw [ih { q with queue := q.queue ++ [x], unfinished := q.unfinished + 1 } hs
      (by simp only [List.length_append, List.length_singleton]; push_cast; omega)]
    simp only [List.append_assoc, List.singleton_append, Option.some.injEq, List.length_cons]
    congr 1
    push_cast
    omega

theorem fifo_gets (xs : List α) : ∀ q : Q (List α), q.queue = xs →
    getsOk fifo xs.length q = some xs := by
  induction xs with
  | nil => intro q _; rfl
  | cons x rest ih =>
    intro q hq
    have hne : fifo.qsize q.queue ≠ 0 := by simp [fifo, hq]
    have h1 : getNowait fifo q = ({ q with queue := rest }, .ok x) := by
      rw [getNowait_some _ _ hne]
      simp [getTail, fifo, hq]
    simp only [List.length_cons, getsOk, h1]
    rw [ih _ rfl]
    rfl

/-- `Queue` is first in, first out: from a new queue, `put_nowait` of any items that fit (or into an
unbounded queue, `maxsize <= 0`) succeeds, `unfinished_tasks` counts them, and `get_nowait` returns
them in the same order. -/
def QueueFifoOrder : Prop :=
  ∀ (α : Type) (maxsize : Int) (xs : List α), (maxsize ≤ 0 ∨ (xs.length : Int) ≤ maxsize) →
    ∃ q, putsOk fifo (init fifo maxsize) xs = some q ∧ q.unfinished = xs.length ∧
      getsOk fifo xs.length q = some xs

theorem queueFifoOrder_proven : QueueFifoOrder := by
  intro α m xs h
  have := fifo_puts xs (init fifo m) rfl (by simpa [init, fifo] using h)
  refine ⟨_, this, by simp [init], fifo_gets _ _ (by simp [init, fifo])⟩

theorem lifo_puts (xs : List α) : ∀ q : Q (List α), q.isShutdown = false →
    (q.maxsize ≤ 0 ∨ (q.queue.length : Int) + xs.length ≤ q.maxsize) →
    putsOk lifo q xs =
      some { q with queue := q.queue ++ xs, unfinished := q.unfinished + xs.length } := by
  induction xs with
  | nil => intro q _ _; simp [putsOk]
  | cons x rest ih =>
    intro q hs hr
    simp only [List.length_cons] at hr
    have h1 : putNowait lifo q x =
        ({ q with queue := q.queue ++ [x], unfinished := q.unfinished + 1 }, .ok ()) := by
      rw [putNowait_room _ _ _ hs (by simp only [lifo]; omega)]
      rfl
    simp only [putsOk, h1]
    rw [ih { q with queue := q.queue ++ [x], unfinished := q.unfinished + 1 } hs
      (by simp only [List.length_append, List.length_singleton]; push_cast; omega)]
    simp only [List.append_assoc, List.singleton_append, Option.some.injEq, List.length_cons]
    congr 1
    push_cast
    omega

theorem lifo_gets (n : Nat) : ∀ (xs : List α) (q : Q (List α)), q.queue = xs → xs.length = n →
    getsOk lifo n q = some xs.reverse := by
  induction n with
  | zero =>
    intro xs q _ hl
    have : xs = [] := List.length_eq_zero_iff.1 hl
    subst this
    rfl
  | succ n ih =>
    intro xs q hq hl
    have hne : xs ≠ [] := by
      intro e
      subst e
      simp at hl
    obtain ⟨d, last, hd⟩ : ∃ d last, xs = d ++ [last] :=
      ⟨xs.dropLast, xs.getLast hne, (List.dropLast_concat_getLast hne).symm⟩
    subst hd
    have hqs : lifo.qsize q.queue ≠ 0 := by simp [lifo, hq]
    have hgl : (d ++ [last]).getLast? = some last := by simp
    have hdl : (d ++ [last]).dropLast = d := by simp
    have h1 : getNowait lifo q = ({ q with queue := d }, .ok last) := by
      rw [getNowait_some _ _ hqs]
      simp [getTail, lifo, hq]
    simp only [getsOk, h1]
    rw [ih d _ rfl (by simpa using hl)]
    simp

/-- `LifoQueue` is last in, first out: the same scenario returns the items reversed. -/
def LifoQueueOrder : Prop :=
  ∀ (α : Type) (maxsize : Int) (xs : List α), (maxsize ≤ 0 ∨ (xs.length : Int) ≤ maxsize) →
    ∃ q, putsOk lifo (init lifo maxsize) xs = some q ∧ q.unfinished = xs.length ∧
      getsOk lifo xs.length q = some xs.reverse

theorem lifoQueueOrder_proven : LifoQueueOrder := by
  intro α m xs h
  have := lifo_puts xs (init lifo m) rfl (by simpa [init, lifo] using h)
  refine ⟨_, this, by simp [init], lifo_gets _ xs _ (by simp [init, lifo]) rfl⟩

variable [Inhabited α]

theorem prio_puts {lt : α → α → Bool} (hlt : StrictWeak lt) (xs : List α) :
    ∀ q : Q (List α), q.isShutdown = false → IsHeap lt q.queue →
    (q.maxsize ≤ 0 ∨ (q.queue.length : Int) + xs.length ≤ q.maxsize) →
    ∃ q', putsOk (prio (fun a b => .ok (lt a b))) q xs = some q' ∧ IsHeap lt q'.queue ∧
      q'.queue.Perm (q.queue ++ xs) ∧ q'.unfinished = q.unfinished + xs.length ∧
      q'.isShutdown = false := by
  induction xs with
  | nil => intro q hs hh _; exact ⟨q, rfl, hh, by simp, by simp, hs⟩
  | cons x rest ih =>
    intro q hs hh hr
    simp only [List.length_cons] at hr
    have h1 : putNowait (prio (fun a b => .ok (lt a b))) q x =
        putTail (prio (fun a b => .ok (lt a b))) q x :=
      putNowait_room _ _ _ hs (by simp only [prio]; omega)
    obtain ⟨c1, c2⟩ := pyHeappush_correct hlt q.queue x hh
    have hp := heappushP_pure lt q.queue x
    let q1 : Q (List α) :=
      { q with queue := pyHeappush lt q.queue x, unfinished := q.unfinished + 1 }
    have h2 : putTail (prio (fun a b => .ok (lt a b))) q x = (q1, .ok ()) := by
      simp [putTail, prio, hp, q1]
    have hl1 : q1.queue.length = q.queue.length + 1 := by
      have := c2.length_eq
      simpa [q1] using this
    obtain ⟨q', e1, e2, e3, e4, e5⟩ := ih q1 hs c1 (by rw [hl1]; push_cast; simp only [q1]; omega)
    refine ⟨q', ?_, e2, ?_, ?_, e5⟩
    · simp only [putsOk, h1, h2]
      exact e1
    · refine e3.trans ?_
      have : (q1.queue ++ rest).Perm ((x :: q.queue) ++ rest) := c2.append_right rest
      refine this.trans ?_
      simp only [List.cons_append]
      exact (List.perm_middle).symm
    · rw [e4]
      simp only [q1, List.length_cons]
      push_cast
      omega

theorem prio_gets {lt : α → α → Bool} (hlt : StrictWeak lt) (n : Nat) :
    ∀ q : Q (List α), q.queue.length = n → IsHeap lt q.queue →
    q.isShutdown = false →
    ∃ l, getsOk (prio (fun a b => .ok (lt a b))) n q = some l ∧ l.Perm q.queue ∧
      l.Pairwise (fun a b => lt b a = false) := by
  induction n with
  | zero =>
    intro q hl _ _
    have : q.queue = [] := List.length_eq_zero_iff.1 hl
    exact ⟨[], rfl, by rw [this], List.Pairwise.nil⟩
  | succ n ih =>
    intro q hl hh hs
    have hne : q.queue ≠ [] := by
      intro e
      simp [e] at hl
    have hqs : (prio (fun a b => .ok (lt a b))).qsize q.queue ≠ 0 := by simp [prio, hl]
    obtain ⟨v, h', hp, hq⟩ := heappopP_pure lt q.queue hne
    obtain ⟨v2, h2, hq2, hh2, hperm, hmin⟩ := pyHeappop_correct hlt q.queue hh hne
    rw [hq] at hq2
    cases hq2
    have hlen : h'.length = n := by
      have := hperm.length_eq
      simp at this
      omega
    obtain ⟨l, e1, e2, e3⟩ := ih { q with queue := h' } hlen hh2 hs
    refine ⟨v :: l, ?_, ?_, ?_⟩
    · have h1 : getNowait (prio (fun a b => .ok (lt a b))) q = ({ q with queue := h' }, .ok v) := by
        rw [getNowait_some _ _ hqs]
        simp [getTail, prio, hp]
      simp only [getsOk, h1]
      rw [e1]
      rfl
    · exact (e2.cons v).trans hperm
    · refine List.Pairwise.cons ?_ e3
      intro b hb
      exact hmin b (hperm.subset (List.mem_cons_of_mem _ (e2.subset hb)))

/-- `PriorityQueue` "retrieves open entries in priority order (lowest first)": when `<` on the
items is a strict weak order and raises nothing (the condition of `heapq`), `get_nowait` returns a
permutation of the items put, each one not less than the one before it. -/
def PriorityQueueOrder : Prop :=
  ∀ (α : Type) [Inhabited α] (lt : α → α → Bool), StrictWeak lt →
    ∀ (maxsize : Int) (xs : List α), (maxsize ≤ 0 ∨ (xs.length : Int) ≤ maxsize) →
    ∃ q l, putsOk (prio (fun a b => .ok (lt a b))) (init (prio fun a b => .ok (lt a b)) maxsize) xs
        = some q ∧
      q.unfinished = xs.length ∧
      getsOk (prio (fun a b => .ok (lt a b))) xs.length q = some l ∧ l.Perm xs ∧
      l.Pairwise (fun a b => lt b a = false)

theorem priorityQueueOrder_proven : PriorityQueueOrder := by
  intro α _ lt hlt m xs h
  obtain ⟨q, e1, e2, e3, e4, hs⟩ := prio_puts hlt xs (init (prio fun a b => .ok (lt a b)) m) rfl
    (isHeap_nil lt) (by simpa [init, prio] using h)
  have hlen : q.queue.length = xs.length := by
    have := e3.length_eq
    simpa [init, prio] using this
  obtain ⟨l, g1, g2, g3⟩ := prio_gets hlt xs.length q hlen e2 hs
  refine ⟨q, l, e1, ?_, g1, ?_, g3⟩
  · simp [e4, init]
  · refine g2.trans ?_
    simpa [init, prio] using e3

/-- `put_nowait` and `get_nowait` on the boundary, for every queue organization: `Full` exactly when
`0 < maxsize <= qsize()`, `Empty` exactly when `qsize() == 0`, each leaving the queue unchanged, and
`ShutDown` before either test. -/
def NowaitBoundary : Prop :=
  ∀ (α ρ : Type) (I : Impl α ρ) (q : Q ρ) (x : α),
    (q.isShutdown = true → putNowait I q x = (q, .error shutDown)) ∧
    (q.isShutdown = false → 0 < q.maxsize → q.maxsize ≤ (I.qsize q.queue : Int) →
      putNowait I q x = (q, .error full)) ∧
    (q.isShutdown = false → (q.maxsize ≤ 0 ∨ (I.qsize q.queue : Int) < q.maxsize) →
      putNowait I q x = putTail I q x) ∧
    (I.qsize q.queue = 0 → q.isShutdown = false → getNowait I q = (q, .error empty)) ∧
    (I.qsize q.queue = 0 → q.isShutdown = true → getNowait I q = (q, .error shutDown)) ∧
    (I.qsize q.queue ≠ 0 → getNowait I q = getTail I q)

theorem nowaitBoundary_proven : NowaitBoundary := by
  intro α ρ I q x
  refine ⟨?_, ?_, putNowait_room I q x, ?_, ?_, getNowait_some I q⟩
  · intro h; simp [putNowait, put, h]
  · intro h1 h2 h3
    have : (I.qsize q.queue : Int) ≥ q.maxsize := h3
    simp [putNowait, put, h1, h2, this]
  · intro h1 h2; simp [getNowait, get, h1, h2]
  · intro h1 h2; simp [getNowait, get, h1, h2]

/-- `qsize`, `empty` and `full` read the same state: `empty()` is `qsize() == 0` and `full()` is
`0 < maxsize <= qsize()`, as the docstrings of Lib/queue.py:115 and :129 say. `_qsize` is the length
of the representation for the three queue classes. -/
def SizePredicates : Prop :=
  ∀ (α ρ : Type) (I : Impl α ρ) (q : Q ρ),
    (isEmpty I q = true ↔ qsize I q = 0) ∧
    (isFull I q = true ↔ (0 < q.maxsize ∧ q.maxsize ≤ (qsize I q : Int)))

theorem sizePredicates_proven : SizePredicates := by
  intro α ρ I q
  simp [isEmpty, isFull, qsize]

/-- `task_done` and `join`: "Raises a ValueError if called more times than there were items placed
in the queue". With `unfinished_tasks > 0` it decrements, and at 0 it raises and changes nothing.
`join` returns at once exactly when the count is 0; otherwise it can only wait for another thread. A
successful `put` is what raises the count; `get` leaves it. -/
def TaskAccounting : Prop :=
  ∀ (α ρ : Type) (I : Impl α ρ) (q : Q ρ) (x : α),
    (q.unfinished ≥ 1 → taskDone q = ({ q with unfinished := q.unfinished - 1 }, .ok ())) ∧
    (q.unfinished = 0 →
      taskDone q = (q, .error (.valueError "task_done() called too many times"))) ∧
    (q.unfinished = 0 → join q = .ok ()) ∧
    (q.unfinished ≠ 0 → join q = .error blocksForever) ∧
    (∀ r, I.put q.queue x = (r, .ok ()) → (putTail I q x).1.unfinished = q.unfinished + 1) ∧
    (getTail I q).1.unfinished = q.unfinished

theorem taskAccounting_proven : TaskAccounting := by
  intro α ρ I q x
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have h' : ¬(q.unfinished - 1 ≤ 0 ∧ q.unfinished - 1 < 0) := by omega
    simp only [taskDone, if_neg h']
  · intro h
    have h' : q.unfinished - 1 ≤ 0 ∧ q.unfinished - 1 < 0 := by omega
    simp only [taskDone, if_pos h']
  · intro h; simp [join, h]
  · intro h; simp [join, h]
  · intro r h; simp [putTail, h]
  · rfl

/-- `timeout` validation. With `block` and a bounded queue, a negative `timeout` is the `ValueError`,
even when there is room. On an unbounded queue, `put` ignores `timeout`, because the bounded branch
is where it is read. `get` validates it whether or not an item is there, unless the queue is shut
down and empty. With `block=False`, it is ignored by both. -/
def TimeoutValidation : Prop :=
  ∀ (α ρ : Type) (I : Impl α ρ) (q : Q ρ) (x : α) (t : Int),
    (t < 0 → q.isShutdown = false → q.maxsize > 0 → put I q x true (some t) = (q, .error negTimeout)) ∧
    (q.isShutdown = false → q.maxsize ≤ 0 → put I q x true (some t) = putTail I q x) ∧
    (q.isShutdown = false → put I q x false (some t) = putNowait I q x) ∧
    (t < 0 → q.isShutdown = false → get I q true (some t) = (q, .error negTimeout)) ∧
    (get I q false (some t) = getNowait I q)

theorem timeoutValidation_proven : TimeoutValidation := by
  intro α ρ I q x t
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h1 h2 h3; simp [put, h1, h2, h3]
  · intro h1 h2
    have : ¬ q.maxsize > 0 := by omega
    simp [put, h1, this]
  · intro _; rfl
  · intro h1 h2; simp [get, h1, h2]
  · rfl

/-- A timed `put` or `get` that cannot proceed raises `Full` or `Empty`, and only the clock moves:
the waits have no other effect in a single thread. A timeout of `0` is the same as `block=False`. -/
def TimedOutcome : Prop :=
  ∀ (α ρ : Type) (I : Impl α ρ) (q : Q ρ) (x : α) (t : Int), t ≥ 0 →
    (q.isShutdown = false → 0 < q.maxsize → q.maxsize ≤ (I.qsize q.queue : Int) →
      (put I q x true (some t)).2 = .error full ∧
      (put I q x true (some t)).1.queue = q.queue ∧
      (put I q x true (some t)).1.now = q.now + t) ∧
    (q.isShutdown = false → I.qsize q.queue = 0 →
      (get I q true (some t)).2 = .error empty ∧
      (get I q true (some t)).1.queue = q.queue ∧
      (get I q true (some t)).1.now = q.now + t)

theorem timedOutcome_proven : TimedOutcome := by
  intro α ρ I q x t ht
  constructor
  · intro h1 h2 h3
    have ht' : ¬ t < 0 := by omega
    have h4 : (I.qsize q.queue : Int) ≥ q.maxsize := h3
    by_cases h0 : t = 0
    · subst h0
      simp [put, h1, h2, h4, timedOut]
    · have : ¬ (q.now + t - q.now ≤ 0) := by omega
      simp [put, h1, h2, h4, timedOut, ht', this]
      omega
  · intro h1 h2
    have ht' : ¬ t < 0 := by omega
    by_cases h0 : t = 0
    · subst h0
      simp [get, h1, h2, timedOut, timedOut']
    · have : ¬ (q.now + t - q.now ≤ 0) := by omega
      simp [get, h1, h2, timedOut, timedOut', ht', this]
      omega

/-- `unfinished_tasks` after `shutdown(immediate=True)` removed `n` items. -/
def drained (u : Int) (n : Nat) : Int := if u > 0 then max (u - n) 0 else u

omit [Inhabited α] in
/-- `drain` on a FIFO deque: the queue empties and `unfinished_tasks` drops by one per item, not
below 0. -/
theorem drain_fifo (xs : List α) : ∀ q : Q (List α), q.queue = xs →
    (drain fifo (xs.length + 1) q).2 = .ok () ∧ (drain fifo (xs.length + 1) q).1.queue = [] ∧
    (drain fifo (xs.length + 1) q).1.unfinished = drained q.unfinished xs.length ∧
    (drain fifo (xs.length + 1) q).1.isShutdown = q.isShutdown := by
  induction xs with
  | nil =>
    intro q hq
    have h : drain fifo 1 q = (q, .ok ()) := by simp [drain, fifo, hq]
    have hd : drained q.unfinished 0 = q.unfinished := by
      unfold drained
      split <;> simp <;> omega
    simp only [List.length_nil, Nat.zero_add, h, hq, hd, true_and]
  | cons x rest ih =>
    intro q hq
    have hq' : fifo.get q.queue = (rest, .ok x) := by simp [fifo, hq]
    have hsz : fifo.qsize q.queue ≠ 0 := by simp [fifo, hq]
    by_cases hu : q.unfinished > 0
    · have hs : drain fifo (rest.length + 1 + 1) q =
          drain fifo (rest.length + 1) { q with queue := rest, unfinished := q.unfinished - 1 } := by
        rw [drain]
        simp only [if_pos hsz, hq', hu, if_true]
      obtain ⟨a, b, c, d⟩ := ih { q with queue := rest, unfinished := q.unfinished - 1 } rfl
      simp only [List.length_cons]
      rw [hs]
      refine ⟨a, b, ?_, d⟩
      rw [c]
      simp only [drained, if_pos hu]
      split <;> omega
    · have hs : drain fifo (rest.length + 1 + 1) q =
          drain fifo (rest.length + 1) { q with queue := rest } := by
        rw [drain]
        simp only [if_pos hsz, hq', hu, if_false]
      obtain ⟨a, b, c, d⟩ := ih { q with queue := rest } rfl
      simp only [List.length_cons]
      rw [hs]
      refine ⟨a, b, ?_, d⟩
      rw [c]
      simp only [drained, if_neg hu]

/-- `shutdown`: afterwards `put` raises `ShutDown` whatever its arguments, and `get` still returns
what is queued and raises `ShutDown` once the queue is empty. `shutdown(immediate=True)` on a `Queue`
removes every item and lowers `unfinished_tasks` by that number, not below 0, so that `get` raises at
once. -/
def ShutdownSemantics : Prop :=
  ∀ (α : Type) (q : Q (List α)) (x : α) (b : Bool) (t : Option Int) (y : α) (ys : List α),
    (put fifo (shutdown fifo q false).1 x b t).2 = .error shutDown ∧
    (shutdown fifo q false).2 = .ok () ∧
    (shutdown fifo q false).1.queue = q.queue ∧
    (q.queue = [] → (get fifo (shutdown fifo q false).1 b t).2 = .error shutDown) ∧
    (q.queue = y :: ys → (getNowait fifo (shutdown fifo q false).1).2 = .ok y) ∧
    (shutdown fifo q true).2 = .ok () ∧
    (shutdown fifo q true).1.queue = [] ∧
    (shutdown fifo q true).1.unfinished = drained q.unfinished q.queue.length ∧
    (get fifo (shutdown fifo q true).1 b t).2 = .error shutDown

theorem shutdownSemantics_proven : ShutdownSemantics := by
  intro α q x b t y ys
  obtain ⟨d1, d2, d3, d4⟩ := drain_fifo q.queue { q with isShutdown := true } rfl
  have hs : shutdown fifo q true = drain fifo (q.queue.length + 1) { q with isShutdown := true } := by
    simp [shutdown, fifo]
  rw [← hs] at d1 d2 d3 d4
  refine ⟨by simp [put, shutdown], by simp [shutdown], by simp [shutdown], ?_, ?_, d1, d2, d3, ?_⟩
  · intro h; simp [get, shutdown, fifo, h]
  · intro h; simp [getNowait, get, shutdown, fifo, h, getTail]
  · have hg : ∀ q' : Q (List α), q'.isShutdown = true → q'.queue = [] →
        (get fifo q' b t).2 = .error shutDown := by
      intro q' h1 h2
      simp [get, fifo, h1, h2]
    exact hg _ d4 d2

/-- A `put` that raises in `_put` does not count: `PriorityQueue.put` of an item that cannot be
compared raises from `heappush`, `unfinished_tasks` stays, and the item stays in `queue` at the end,
because `heappush` appends first. The maintainers declined rollback in `heapq`
(python/cpython#100968), so this states the behaviour. -/
def FailedPutKeepsItem : Prop :=
  ∀ (α : Type) [Inhabited α] (e : PyExc) (q : Q (List α)) (x : α) (y : α),
    q.isShutdown = false → q.maxsize ≤ 0 → q.queue = [y] →
    let bad : LtP α := fun _ _ => .error e
    (put (prio bad) q x).2 = .error e ∧
    (put (prio bad) q x).1.queue = [y, x] ∧
    (put (prio bad) q x).1.unfinished = q.unfinished

theorem failedPutKeepsItem_proven : FailedPutKeepsItem := by
  intro α _ e q x y h1 h2 h3
  have h4 : ¬ q.maxsize > 0 := by omega
  simp [put, h1, h4, putTail, prio, heappushP, siftdownP, siftdownLoopP, h3, at!]

/-! ### `_PySimpleQueue` and `_queue.SimpleQueue` -/

/-- A `_PySimpleQueue` holding `c`: the semaphore count equals the length, its invariant. -/
def pysq (c : List α) : PySQ α := { queue := c, count := c.length, now := 0 }

/-- The two `SimpleQueue`s agree when no timeout is combined with `block=False`: `put`, `get`,
`put_nowait`, `get_nowait`, `empty` and `qsize` give the same results and keep the same contents,
for a queue whose semaphore count equals its length, which every operation preserves. -/
def SimpleQueueTwinsBlocking : Prop :=
  ∀ (α : Type) (c : List α) (x : α) (block : Bool) (timeout : Option Int) (q : PySQ α),
    q.queue = c → q.count = c.length →
    (block = true ∨ timeout = none) →
    (q.get block timeout).2 = (cGet c block timeout).2 ∧
    (q.get block timeout).1.queue = (cGet c block timeout).1 ∧
    (q.get block timeout).1.count = (cGet c block timeout).1.length ∧
    (q.getNowait).2 = (cGet c false none).2 ∧
    (q.put x block timeout).queue = cPut c x ∧
    (q.put x block timeout).count = (cPut c x).length ∧
    (q.putNowait x).queue = cPut c x ∧
    q.isEmpty = c.isEmpty ∧
    q.qsize = c.length

omit [Inhabited α] in
theorem pysq_get_blocking (c : List α) (block : Bool) (timeout : Option Int) (q : PySQ α)
    (h1 : q.queue = c) (h2 : q.count = c.length) (hb : block = true ∨ timeout = none) :
    (q.get block timeout).2 = (cGet c block timeout).2 ∧
    (q.get block timeout).1.queue = (cGet c block timeout).1 ∧
    (q.get block timeout).1.count = (cGet c block timeout).1.length := by
  cases c with
  | nil =>
    have hc : q.count = 0 := by simpa using h2
    cases timeout with
    | none =>
      cases block <;> simp [PySQ.get, semAcquire, cGet, hc, h1]
    | some t =>
      have hbt : block = true := by simpa using hb
      subst hbt
      by_cases ht : t < 0
      · simp [PySQ.get, cGet, ht, h1, hc]
      · simp [PySQ.get, semAcquire, cGet, ht, hc, h1]
  | cons a rest =>
    have hc : q.count ≠ 0 := by simp [h2]; omega
    have hc' : q.count - 1 = rest.length := by simp [h2]
    cases timeout with
    | none =>
      cases block <;> simp [PySQ.get, semAcquire, cGet, hc, hc', h1]
    | some t =>
      have hbt : block = true := by simpa using hb
      subst hbt
      by_cases ht : t < 0
      · simp [PySQ.get, cGet, ht, h1, h2]
      · simp [PySQ.get, semAcquire, cGet, ht, hc, hc', h1]

/-- `_PySimpleQueue.get` and `_queue.SimpleQueue.get` give the same outcome for all arguments, for a queue whose
semaphore count is its length. With `block=False` both ignore `timeout`, as the shared docstring says: the Python twin
drops it at Lib/queue.py:349-350, which is the fix of python/cpython#156476. -/
def SimpleQueueGetTwins : Prop :=
  ∀ (α : Type) (c : List α) (block : Bool) (timeout : Option Int),
    (PySQ.get (pysq c) block timeout).2 = (cGet c block timeout).2

theorem simpleQueueGetTwins_proven : SimpleQueueGetTwins := by
  intro α c block timeout
  cases block with
  | true => exact (pysq_get_blocking c true timeout (pysq c) rfl rfl (.inl rfl)).1
  | false =>
    have h := (pysq_get_blocking c false none (pysq c) rfl rfl (.inr rfl)).1
    have a : PySQ.get (pysq c) false timeout = PySQ.get (pysq c) false none := by simp [PySQ.get]
    have b : cGet c false timeout = cGet c false none := by simp [cGet]
    rw [a, b]
    exact h

theorem simpleQueueTwinsBlocking_proven : SimpleQueueTwinsBlocking := by
  intro α c x block timeout q h1 h2 hb
  obtain ⟨g1, g2, g3⟩ := pysq_get_blocking c block timeout q h1 h2 hb
  obtain ⟨n1, _, _⟩ := pysq_get_blocking c false none q h1 h2 (.inr rfl)
  refine ⟨g1, g2, g3, n1, ?_, ?_, ?_, ?_, ?_⟩
  · simp [PySQ.put, cPut, h1]
  · simp [PySQ.put, cPut, h2]
  · simp [PySQ.putNowait, PySQ.put, cPut, h1]
  · simp only [PySQ.isEmpty, h1]
    cases c <;> simp
  · simp [PySQ.qsize, h1]

end PyLean.CoreLibs.Misc.Queue
