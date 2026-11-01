import PyLean.CoreLibs.Misc.Sched.Model

/-!
Properties of `sched.scheduler`, over any time and priority types. The documented precondition is
`TotalEnv`: times and priorities are totally ordered by `==` and `<` and those do not raise
("Numeric type compatible with the return value of the timefunc function", Lib/sched.py:36). Events
are then ordered by `(time, priority, sequence)`, which `evLt` states. States are those reached from
`__init__` through `enterabs`, `enter` and `cancel`.
-/

namespace PyLean.CoreLibs.Misc.Sched

open PyLean PyLean.Accel PyLean.CoreLibs.Misc

/-- A strict total order. -/
structure StrictTotal {A : Type} [DecidableEq A] (lt : A → A → Bool) : Prop where
  irrefl : ∀ a, lt a a = false
  trans : ∀ a b c, lt a b = true → lt b c = true → lt a c = true
  total : ∀ a b, a ≠ b → lt a b = true ∨ lt b a = true

/-- Lexicographic order on pairs. -/
def lex {A B : Type} [DecidableEq A] (l1 : A → A → Bool) (l2 : B → B → Bool) (x y : A × B) : Bool :=
  if x.1 = y.1 then l2 x.2 y.2 else l1 x.1 y.1

theorem StrictTotal.lex {A B : Type} [DecidableEq A] [DecidableEq B] {l1 : A → A → Bool}
    {l2 : B → B → Bool} (h1 : StrictTotal l1) (h2 : StrictTotal l2) : StrictTotal (lex l1 l2) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a; simp [Sched.lex, h2.irrefl]
  · intro a b c hab hbc
    simp only [Sched.lex] at *
    by_cases e1 : a.1 = b.1
    · rw [if_pos e1] at hab
      by_cases e2 : b.1 = c.1
      · rw [if_pos e2] at hbc
        rw [if_pos (e1.trans e2)]
        exact h2.trans _ _ _ hab hbc
      · rw [if_neg e2] at hbc
        rw [if_neg (by rw [e1]; exact e2), e1]
        exact hbc
    · rw [if_neg e1] at hab
      by_cases e2 : b.1 = c.1
      · rw [if_pos e2] at hbc
        rw [if_neg (by rw [← e2]; exact e1), ← e2]
        exact hab
      · rw [if_neg e2] at hbc
        by_cases e3 : a.1 = c.1
        · subst_vars
          rw [e3] at hab
          have := h1.trans _ _ _ hab hbc
          rw [h1.irrefl] at this
          cases this
        · rw [if_neg e3]
          exact h1.trans _ _ _ hab hbc
  · intro a b hne
    simp only [Sched.lex]
    by_cases e1 : a.1 = b.1
    · simp only [if_pos e1, if_pos e1.symm]
      have : a.2 ≠ b.2 := fun e => hne (Prod.ext e1 e)
      exact h2.total _ _ this
    · simp only [if_neg e1, if_neg (Ne.symm e1)]
      exact h1.total _ _ e1

theorem StrictTotal.strictWeak {A : Type} [DecidableEq A] {lt : A → A → Bool} (h : StrictTotal lt) :
    StrictWeak lt := by
  refine ⟨h.irrefl, h.trans, ?_⟩
  intro a b c hac
  by_cases e : a = b
  · subst e; exact .inr hac
  · rcases h.total a b e with h1 | h1
    · exact .inl h1
    · exact .inr (h.trans _ _ _ h1 hac)

def natLt (a b : Nat) : Bool := decide (a < b)

theorem strictTotal_nat : StrictTotal natLt := by
  refine ⟨?_, ?_, ?_⟩
  · intro a; simp [natLt]
  · intro a b c; simp only [natLt, decide_eq_true_eq]; omega
  · intro a b h; simp only [natLt, decide_eq_true_eq]; omega

variable {T P A V W : Type} [DecidableEq T] [DecidableEq P]

/-- The fields events are ordered by. -/
def key (a : Event T P A V) : T × P × Nat := (a.time, a.priority, a.sequence)

/-- `(time, priority, sequence)` order, from the orders of the field types. -/
def evLt (ltT : T → T → Bool) (ltP : P → P → Bool) (a b : Event T P A V) : Bool :=
  lex ltT (lex ltP natLt) (key a) (key b)

/-- The documented precondition: `==` and `<` on times and priorities are a total order and raise
nothing. -/
structure TotalEnv (e : Env T P A V W) (ltT : T → T → Bool) (ltP : P → P → Bool) : Prop where
  teq : ∀ a b, e.ct.eq a b = .ok (decide (a = b))
  tlt : ∀ a b, e.ct.lt a b = .ok (ltT a b)
  peq : ∀ a b, e.cp.eq a b = .ok (decide (a = b))
  plt : ∀ a b, e.cp.lt a b = .ok (ltP a b)
  tord : StrictTotal ltT
  pord : StrictTotal ltP

theorem TotalEnv.strictWeak {e : Env T P A V W} {ltT : T → T → Bool} {ltP : P → P → Bool}
    (h : TotalEnv e ltT ltP) : StrictWeak (evLt (A := A) (V := V) ltT ltP) := by
  have ht := (h.tord.lex (h.pord.lex strictTotal_nat)).strictWeak
  exact ⟨fun a => ht.irrefl _, fun a b c => ht.trans _ _ _, fun a b c => ht.negTrans _ _ _⟩

theorem TotalEnv.eventLt_eq {e : Env T P A V W} {ltT : T → T → Bool} {ltP : P → P → Bool}
    (h : TotalEnv e ltT ltP) : eventLt e = fun a b => .ok (evLt ltT ltP a b) := by
  funext a b
  simp only [eventLt, evLt, lex, key, h.teq, h.peq, h.tlt, h.plt, bind, Except.bind, pure, Except.pure]
  by_cases e1 : a.time = b.time
  · by_cases e2 : a.priority = b.priority
    · simp [e1, e2, natLt]
    · simp [e1, e2]
  · simp [e1]

section Heapify

variable {α : Type} [Inhabited α]

theorem heapifyLoopP_pure (lt : α → α → Bool) :
    ∀ (is : List Nat) (h : List α), (∀ i ∈ is, i < h.length) →
      heapifyLoopP (fun a b => .ok (lt a b)) is h =
        (is.foldl (fun h i => pySiftup lt h i) h, none) := by
  intro is
  induction is with
  | nil => intro h _; rfl
  | cons i rest ih =>
    intro h hb
    have hi := hb i (by simp)
    simp only [heapifyLoopP, siftupP_pure lt h i hi, List.foldl_cons]
    apply ih
    intro k hk
    rw [pySiftup_length]
    exact hb k (by simp [hk])

theorem heapifyP_pure (lt : α → α → Bool) (x : List α) :
    heapifyP (fun a b => .ok (lt a b)) x = (pyHeapify lt x, none) := by
  unfold heapifyP pyHeapify
  apply heapifyLoopP_pure
  intro i hi
  have := List.mem_range.1 (List.mem_reverse.1 hi)
  omega

end Heapify

variable [Inhabited T] [Inhabited P] [Inhabited A]

/-- The states a program can reach through `__init__`, `enterabs`, `enter` and `cancel`. -/
inductive Reach (e : Env T P A V W) : Sched T P A V W → Prop where
  | init (w : W) : Reach e (init w)
  | enterabs (s : Sched T P A V W) (t : T) (p : P) (a : A) (args : List V)
      (kw : Option (List (String × V))) : Reach e s → Reach e (enterabs e s t p a args kw).1
  | enter (s : Sched T P A V W) (d : T) (p : P) (a : A) (args : List V)
      (kw : Option (List (String × V))) : Reach e s → Reach e (enter e s d p a args kw).1
  | cancel (s : Sched T P A V W) (ev : Event T P A V) : Reach e s → Reach e (cancel e s ev).1

/-- What `heappush` does to `_queue` under a total order. -/
theorem enterabs_queue {e : Env T P A V W} {ltT : T → T → Bool} {ltP : P → P → Bool}
    (h : TotalEnv e ltT ltP) (s : Sched T P A V W) (t : T) (p : P) (a : A) (args : List V)
    (kw : Option (List (String × V))) :
    let ev : Event T P A V :=
      { time := t, priority := p, sequence := s.seq, action := a, argument := args,
        kwargs := kw.getD [] }
    enterabs e s t p a args kw =
      ({ s with queue := pyHeappush (evLt ltT ltP) s.queue ev, seq := s.seq + 1 }, .ok ev) := by
  simp only [enterabs, h.eventLt_eq, heappushP_pure]

theorem reach_heap {e : Env T P A V W} {ltT : T → T → Bool} {ltP : P → P → Bool}
    (h : TotalEnv e ltT ltP) {s : Sched T P A V W} (r : Reach e s) :
    IsHeap (evLt ltT ltP) s.queue := by
  have hw := h.strictWeak (A := A) (V := V)
  induction r with
  | init w => exact isHeap_nil _
  | enterabs s t p a args kw _ ih =>
    simp only [enterabs_queue h]
    exact (pyHeappush_correct hw _ _ ih).1
  | enter s d p a args kw _ ih =>
    simp only [Sched.enter]
    cases hn : (e.timefunc s.world).2 with
    | error x => simpa [hn] using ih
    | ok now =>
      cases ha : e.add now d with
      | error x => simpa [hn, ha] using ih
      | ok time =>
        simp only [hn, ha]
        rw [enterabs_queue h]
        exact (pyHeappush_correct hw _ _ ih).1
  | cancel s ev _ ih =>
    simp only [Sched.cancel]
    cases hr : listRemove e ev s.queue with
    | error x => simpa using ih
    | ok q =>
      simp only [h.eventLt_eq, heapifyP_pure]
      exact (pyHeapify_correct hw q).1

/-- `scheduler.queue` is "An ordered list of upcoming events": for every state reached through
`enterabs`, `enter` and `cancel` with totally ordered times and priorities, the property returns the
queued events, each exactly once, in `(time, priority, sequence)` order. "Events scheduled for the
same time will be executed in the order of their priority", and in scheduling order after that. -/
def QueueOrdered : Prop :=
  ∀ (T P A V W : Type) [DecidableEq T] [DecidableEq P] [Inhabited T] [Inhabited P] [Inhabited A]
    (e : Env T P A V W) (ltT : T → T → Bool) (ltP : P → P → Bool), TotalEnv e ltT ltP →
    ∀ s, Reach e s →
      ∃ l, queue e s = .ok l ∧ l.Perm s.queue ∧
        l.Pairwise (fun a b => evLt ltT ltP b a = false)

theorem queueOrdered_proven : QueueOrdered := by
  intro T P A V W _ _ _ _ _ e ltT ltP h s r
  have hw := h.strictWeak (A := A) (V := V)
  simp only [queue, h.eventLt_eq]
  exact popsP_sorted hw _ _ rfl (reach_heap h r)

/-- `enter` is "A variant that specifies the time as a relative time": it reads the clock once and
is `enterabs` at `timefunc() + delay`. A clock or `+` that raises leaves the queue alone. -/
def EnterRelative : Prop :=
  ∀ (T P A V W : Type) [Inhabited T] [Inhabited P] [Inhabited A] (e : Env T P A V W)
    (s : Sched T P A V W) (d : T) (p : P) (a : A) (args : List V) (kw : Option (List (String × V)))
    (w : W) (now t : T),
    (e.timefunc s.world = (w, .ok now) → e.add now d = .ok t →
      enter e s d p a args kw = enterabs e { s with world := w } t p a args kw) ∧
    (∀ x, e.timefunc s.world = (w, .ok now) → e.add now d = .error x →
      (enter e s d p a args kw).2 = .error x ∧ (enter e s d p a args kw).1.queue = s.queue) ∧
    (∀ x, e.timefunc s.world = (w, .error x) →
      (enter e s d p a args kw).2 = .error x ∧ (enter e s d p a args kw).1.queue = s.queue)

theorem enterRelative_proven : EnterRelative := by
  intro T P A V W _ _ _ e s d p a args kw w now t
  refine ⟨?_, ?_, ?_⟩
  · intro h1 h2; simp [enter, h1, h2]
  · intro x h1 h2; simp [enter, h1, h2]
  · intro x h1; simp [enter, h1]

/-- `enterabs` returns the event as an ID: its fields are the arguments, `kwargs` defaults to `{}`,
its `sequence` is the old counter, and the counter moves on, also when `heappush` raises. A
comparison that raises leaves the event at the end of the list, as with `PriorityQueue`. -/
def EnterabsId : Prop :=
  ∀ (T P A V W : Type) [DecidableEq T] [DecidableEq P] [Inhabited T] [Inhabited P] [Inhabited A]
    (e : Env T P A V W) (ltT : T → T → Bool) (ltP : P → P → Bool), TotalEnv e ltT ltP →
    ∀ (s : Sched T P A V W) (t : T) (p : P) (a : A) (args : List V)
      (kw : Option (List (String × V))),
    let ev : Event T P A V :=
      { time := t, priority := p, sequence := s.seq, action := a, argument := args,
        kwargs := kw.getD [] }
    (enterabs e s t p a args kw).2 = .ok ev ∧
    (enterabs e s t p a args kw).1.seq = s.seq + 1 ∧
    (IsHeap (evLt ltT ltP) s.queue → (enterabs e s t p a args kw).1.queue.Perm (ev :: s.queue))

theorem enterabsId_proven : EnterabsId := by
  intro T P A V W _ _ _ _ _ e ltT ltP h s t p a args kw
  have hw := h.strictWeak (A := A) (V := V)
  simp only [enterabs_queue h]
  exact ⟨trivial, trivial, fun hh => (pyHeappush_correct hw _ _ hh).2⟩

/-- `empty()` is `True` exactly when `_queue` is empty, which is exactly when `queue` is `[]`. -/
def EmptyQueue : Prop :=
  ∀ (T P A V W : Type) [DecidableEq T] [DecidableEq P] [Inhabited T] [Inhabited P] [Inhabited A]
    (e : Env T P A V W) (ltT : T → T → Bool) (ltP : P → P → Bool), TotalEnv e ltT ltP →
    ∀ s, Reach e s → (empty s = true ↔ queue e s = .ok [])

theorem emptyQueue_proven : EmptyQueue := by
  intro T P A V W _ _ _ _ _ e ltT ltP h s r
  obtain ⟨l, h1, h2, -⟩ := queueOrdered_proven T P A V W e ltT ltP h s r
  rw [h1]
  constructor
  · intro h3
    have : s.queue = [] := by simpa [empty] using h3
    rw [this] at h2
    rw [h2.eq_nil]
  · intro h3
    have : l = [] := by simpa using h3
    rw [this] at h2
    have := h2.symm.eq_nil
    simp [empty, this]

omit [DecidableEq T] [DecidableEq P] [Inhabited T] [Inhabited P] [Inhabited A] in
/-- Elements a `listRemove` cannot match are skipped. -/
theorem listRemove_absent (e : Env T P A V W) (x : Event T P A V) :
    ∀ q : List (Event T P A V), (∀ a ∈ q, eventEq e a x = .ok false) →
      listRemove e x q = .error (.valueError "list.remove(x): x not in list") := by
  intro q
  induction q with
  | nil => intro _; rfl
  | cons a rest ih =>
    intro h
    simp [listRemove, h a (by simp), ih (fun b hb => h b (by simp [hb])), bind, Except.bind]

/-- `cancel` of an event that is not in the queue: "this raises ValueError", and the queue stays. -/
def CancelAbsent : Prop :=
  ∀ (T P A V W : Type) [Inhabited T] [Inhabited P] [Inhabited A] (e : Env T P A V W)
    (s : Sched T P A V W) (ev : Event T P A V),
    (∀ a ∈ s.queue, eventEq e a ev = .ok false) →
    cancel e s ev = (s, .error (.valueError "list.remove(x): x not in list"))

theorem cancelAbsent_proven : CancelAbsent := by
  intro T P A V W _ _ _ e s ev h
  simp [cancel, listRemove_absent e ev _ h]

/-- Removing the only matching element leaves the rest. -/
theorem listRemove_unique (e : Env T P A V W) (x : Event T P A V) :
    ∀ q : List (Event T P A V), x ∈ q → eventEq e x x = .ok true →
      (∀ a ∈ q, a ≠ x → eventEq e a x = .ok false) →
      ∃ r, listRemove e x q = .ok r ∧ q.Perm (x :: r) := by
  intro q
  induction q with
  | nil => intro h; simp at h
  | cons a rest ih =>
    intro hm hx hu
    by_cases hax : a = x
    · subst hax
      exact ⟨rest, by simp [listRemove, hx, bind, Except.bind, pure, Except.pure], List.Perm.refl _⟩
    · have hm' : x ∈ rest := by
        rcases List.mem_cons.1 hm with h | h
        · exact absurd h.symm hax
        · exact h
      obtain ⟨r, h1, h2⟩ := ih hm' hx (fun b hb hne => hu b (by simp [hb]) hne)
      refine ⟨a :: r, ?_, ?_⟩
      · simp [listRemove, hu a (by simp) hax, h1, bind, Except.bind, pure, Except.pure]
      · exact (h2.cons a).trans (List.Perm.swap _ _ _)

/-- `cancel` with the ID an event got: for a queue whose events have distinct sequence numbers
(which `enterabs` guarantees), the event goes and every other event stays, in heap order. -/
def CancelPresent : Prop :=
  ∀ (T P A V W : Type) [DecidableEq T] [DecidableEq P] [Inhabited T] [Inhabited P] [Inhabited A]
    (e : Env T P A V W) (ltT : T → T → Bool) (ltP : P → P → Bool), TotalEnv e ltT ltP →
    (∀ a, e.eqRest a a = true) →
    ∀ (s : Sched T P A V W) (ev : Event T P A V), ev ∈ s.queue →
      (∀ a ∈ s.queue, a ≠ ev → a.sequence ≠ ev.sequence) →
      (cancel e s ev).2 = .ok () ∧ s.queue.Perm (ev :: (cancel e s ev).1.queue) ∧
        IsHeap (evLt ltT ltP) (cancel e s ev).1.queue

theorem cancelPresent_proven : CancelPresent := by
  intro T P A V W _ _ _ _ _ e ltT ltP h hrefl s ev hm hu
  have hw := h.strictWeak (A := A) (V := V)
  have hself : eventEq e ev ev = .ok true := by
    simp [eventEq, h.teq, h.peq, hrefl, bind, Except.bind, pure, Except.pure]
  have hother : ∀ a ∈ s.queue, a ≠ ev → eventEq e a ev = .ok false := by
    intro a ha hne
    have hs := hu a ha hne
    simp only [eventEq, h.teq, h.peq, bind, Except.bind, pure, Except.pure]
    by_cases e1 : a.time = ev.time
    · by_cases e2 : a.priority = ev.priority
      · simp [e1, e2, hs]
      · simp [e1, e2]
    · simp [e1]
  obtain ⟨r, h1, h2⟩ := listRemove_unique e ev s.queue hm hself hother
  obtain ⟨c1, c2⟩ := pyHeapify_correct hw r
  have hc : cancel e s ev = ({ s with queue := pyHeapify (evLt ltT ltP) r }, .ok ()) := by
    simp only [cancel, h1, h.eventLt_eq, heapifyP_pure]
  rw [hc]
  exact ⟨rfl, h2.trans (c2.symm.cons ev), c1⟩

/-! ### `run` -/

/-- `run` on an empty queue returns `None` without asking the clock. When the first event lies in
the future and `blocking` is false, `run` returns the delay until it, as the docstring says, and
leaves the queue. An action that raises propagates, and its event is gone and the others stay:
"exceptions are not caught but the scheduler's state remains well-defined so run() may be called
again". -/
def RunBasics : Prop :=
  ∀ (T P A V W : Type) [Inhabited T] [Inhabited P] [Inhabited A] (e : Env T P A V W)
    (s : Sched T P A V W) (fuel : Nat) (b : Bool),
    (s.queue = [] → run e (fuel + 1) s b = (s, .ok none)) ∧
    (∀ ev rest w now d, s.queue = ev :: rest → e.timefunc s.world = (w, .ok now) →
      e.gt ev.time now = .ok true → e.sub ev.time now = .ok d →
      run e (fuel + 1) s false = ({ s with world := w }, .ok (some d)))

theorem runBasics_proven : RunBasics := by
  intro T P A V W _ _ _ e s fuel b
  refine ⟨?_, ?_⟩
  · intro h
    simp [run, runLoop, h]
  · intro ev rest w now d h1 h2 h3 h4
    simp [run, runLoop, h1, h2, h3, h4]

theorem at0_pop {ltT : T → T → Bool} {ltP : P → P → Bool} (ev : Event T P A V)
    (rest h' : List (Event T P A V)) (v : Event T P A V)
    (hroot : heappopP (fun a b => .ok (evLt ltT ltP a b)) (ev :: rest) = (h', .ok v)) : v = ev := by
  cases rest with
  | nil => simpa [heappopP, at!] using (congrArg Prod.snd hroot).symm
  | cons r1 r2 =>
    have hl : ¬ ((ev :: r1 :: r2).length = 0) := by simp
    simp only [heappopP] at hroot
    rw [if_neg hl] at hroot
    have hl2 : ¬ ((ev :: r1 :: r2).length - 1 = 0) := by simp
    rw [if_neg hl2] at hroot
    have hat0 : at! ((ev :: r1 :: r2).take ((ev :: r1 :: r2).length - 1)) 0 = ev := by
      simp [at!]
    rw [hat0] at hroot
    revert hroot
    generalize siftupP (α := Event T P A V) _ _ 0 = sr
    obtain ⟨a, b⟩ := sr
    cases b with
    | some x => simp
    | none =>
      simp only [Prod.mk.injEq, Except.ok.injEq]
      intro hh'
      exact hh'.2.symm

/-- An action failing: the event has left the heap before the call. -/
def RunActionRaises : Prop :=
  ∀ (T P A V W : Type) [DecidableEq T] [DecidableEq P] [Inhabited T] [Inhabited P] [Inhabited A]
    (e : Env T P A V W) (ltT : T → T → Bool) (ltP : P → P → Bool), TotalEnv e ltT ltP →
    ∀ (s : Sched T P A V W) (fuel : Nat) (b : Bool) (ev : Event T P A V) (rest : List (Event T P A V))
      (w : W) (now : T) (x : PyExc),
      IsHeap (evLt ltT ltP) s.queue → s.queue = ev :: rest →
      e.timefunc s.world = (w, .ok now) → e.gt ev.time now = .ok false →
      (∀ s', e.call ev.action ev.argument ev.kwargs s' = (s', .error x)) →
      (run e (fuel + 1) s b).2 = .error x ∧
      s.queue.Perm (ev :: (run e (fuel + 1) s b).1.queue)

theorem runActionRaises_proven : RunActionRaises := by
  intro T P A V W _ _ _ _ _ e ltT ltP h s fuel b ev rest w now x hh hq h1 h2 h3
  have hw := h.strictWeak (A := A) (V := V)
  have hne : s.queue ≠ [] := by simp [hq]
  obtain ⟨v, h', hp, hpy⟩ := heappopP_pure (evLt ltT ltP) s.queue hne
  obtain ⟨v2, h2', hq2, _, hperm, _⟩ := pyHeappop_correct hw s.queue hh hne
  rw [hpy] at hq2
  cases hq2
  have hel : (run e (fuel + 1) s b) = ({ s with world := w, queue := h' }, .error x) := by
    simp only [run, runLoop, hq, h1, h2]
    rw [← hq, h.eventLt_eq, hp]
    simp only [h3]
  rw [hel]
  refine ⟨rfl, ?_⟩
  have hv : v = ev := by
    exact at0_pop ev rest h' v (by rw [← hq]; exact hp)
  rw [hv] at hperm
  exact hperm.symm

/-- A log of action calls in the world. -/
structure LogEnv (e : Env T P A V W) (ltT : T → T → Bool) (ltP : P → P → Bool) (now : T)
    (log : W → List A) : Prop where
  total : TotalEnv e ltT ltP
  /-- The clock is past every event and nothing else happens to the queue: an action only records
  itself. -/
  time : ∀ w, e.timefunc w = (w, .ok now)
  due : ∀ t, e.gt t now = .ok false
  delay : ∀ w d, e.delayfunc w d = (w, .ok ())
  call : ∀ a args kw s, ∃ w', e.call a args kw s = ({ s with world := w' }, .ok ()) ∧
    log w' = log s.world ++ [a]

/-- `run` executes events in order: with every event due and actions that only record themselves,
`run()` empties the queue and calls the actions in the order `queue` lists them, then returns
`None`. -/
def RunOrder : Prop :=
  ∀ (T P A V W : Type) [DecidableEq T] [DecidableEq P] [Inhabited T] [Inhabited P] [Inhabited A]
    (e : Env T P A V W) (ltT : T → T → Bool) (ltP : P → P → Bool) (now : T) (log : W → List A),
    LogEnv e ltT ltP now log →
    ∀ s b, IsHeap (evLt ltT ltP) s.queue →
    ∃ l, queue e s = .ok l ∧
      (run e (s.queue.length + 1) s b).2 = .ok none ∧
      (run e (s.queue.length + 1) s b).1.queue = [] ∧
      log (run e (s.queue.length + 1) s b).1.world = log s.world ++ l.map (·.action)

theorem run_loop_log {e : Env T P A V W} {ltT : T → T → Bool} {ltP : P → P → Bool} {now : T}
    {log : W → List A} (hl : LogEnv e ltT ltP now log) (b : Bool) :
    ∀ (n : Nat) (s : Sched T P A V W), s.queue.length = n → IsHeap (evLt ltT ltP) s.queue →
      ∃ l, popsP (fun a b => .ok (evLt ltT ltP a b)) n s.queue = .ok l ∧
        (runLoop e b (n + 1) s).2 = .ok none ∧ (runLoop e b (n + 1) s).1.queue = [] ∧
        log (runLoop e b (n + 1) s).1.world = log s.world ++ l.map (·.action) := by
  have hw := hl.total.strictWeak (A := A) (V := V)
  intro n
  induction n with
  | zero =>
    intro s hn _
    have hq : s.queue = [] := List.length_eq_zero_iff.1 hn
    refine ⟨[], by simp [hq, popsP], ?_⟩
    simp [runLoop, hq]
  | succ n ih =>
    intro s hn hh
    have hne : s.queue ≠ [] := by
      intro e0
      simp [e0] at hn
    obtain ⟨ev, rest, hq⟩ := List.exists_cons_of_ne_nil hne
    obtain ⟨v, h', hp, hpy⟩ := heappopP_pure (evLt ltT ltP) s.queue hne
    obtain ⟨v2, h2', hq2, hh2, hperm, _⟩ := pyHeappop_correct hw s.queue hh hne
    rw [hpy] at hq2
    cases hq2
    have hv : v = ev := at0_pop ev rest h' v (by rw [← hq]; exact hp)
    subst hv
    have hlen : h'.length = n := by
      have := hperm.length_eq
      simp at this
      omega
    obtain ⟨w', hc, hlog⟩ := hl.call v.action v.argument v.kwargs { s with queue := h' }
    let s' : Sched T P A V W := { s with queue := h', world := w' }
    obtain ⟨l, e1, e2, e3, e4⟩ := ih s' hlen hh2
    have hstep : runLoop e b (n + 1 + 1) s = runLoop e b (n + 1) s' := by
      rw [runLoop]
      simp only [hq, hl.time, hl.due]
      rw [← hq, hl.total.eventLt_eq, hp]
      simp only [hc, hl.delay]
      rfl
    refine ⟨v :: l, ?_, ?_, ?_, ?_⟩
    · simp only [popsP, hp]
      rw [show popsP (fun a b => .ok (evLt ltT ltP a b)) n h' =
        popsP (fun a b => .ok (evLt ltT ltP a b)) n s'.queue from rfl, e1]
    · rw [hstep]; exact e2
    · rw [hstep]; exact e3
    · rw [hstep, e4]
      simp only [s', hlog, List.map_cons, List.append_assoc, List.singleton_append]

theorem runOrder_proven : RunOrder := by
  intro T P A V W _ _ _ _ _ e ltT ltP now log hl s b hh
  obtain ⟨l, e1, e2, e3, e4⟩ := run_loop_log hl b s.queue.length s rfl hh
  refine ⟨l, ?_, e2, e3, e4⟩
  simp only [queue, hl.total.eventLt_eq]
  exact e1

end PyLean.CoreLibs.Misc.Sched
