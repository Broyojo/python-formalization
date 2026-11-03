import PyLean.PyIO.BufReentry

/-!
What `Modules/_io/bufferedio.c` checks in the answers of a raw stream that is a
Python object: the counts of `readinto` and `write` (`_bufferedreader_raw_read`,
`_bufferedwriter_raw_write`), the retry on `EINTR` (`_PyIO_trap_eintr`), and the
lock that refuses a re-entrant call (`_enter_buffered_busy`).
-/

namespace PyLean.PyIO

open PyLean

namespace BC2

theorem bind_def {α β : Type} (m : BM α) (f : α → BM β) (R : CH) (s : BufS) :
    (m >>= f) R s = match m R s with
      | (s', .ok a) => f a R s'
      | (s', .error e) => (s', .error e) := rfl

theorem bind_ok {α β : Type} {m : BM α} {f : α → BM β} {R : CH} {s s' : BufS} {b : β}
    (h : (m >>= f) R s = (s', .ok b)) : ∃ s1 a, m R s = (s1, .ok a) ∧ f a R s1 = (s', .ok b) := by
  rw [bind_def] at h
  split at h
  · next s1 a hm => exact ⟨s1, a, hm, h⟩
  · simp at h

theorem bind_of_ok {α β : Type} {m : BM α} {f : α → BM β} {R : CH} {s s1 : BufS} {a : α}
    (h : m R s = (s1, .ok a)) : (m >>= f) R s = f a R s1 := by
  show (match m R s with | (s', .ok a) => f a R s' | (s', .error e) => (s', .error e)) = _
  rw [h]

theorem get_apply (R : CH) (s : BufS) : (get : BM BufS) R s = (s, .ok s) := rfl
theorem pure_apply {α : Type} (a : α) (R : CH) (s : BufS) : (pure a : BM α) R s = (s, .ok a) := rfl
theorem put_apply (t : BufS) (R : CH) (s : BufS) : (put t : BM Unit) R s = (t, .ok ()) := rfl

theorem crash_not_ok {α : Type} (R : CH) (s s' : BufS) (a : α) : (crash : BM α) R s ≠ (s', .ok a) := by
  simp [crash, bind_def, mod, thr]

theorem thr_not_ok {α : Type} (e : PyExc) (R : CH) (s s' : BufS) (a : α) :
    (thr e : BM α) R s ≠ (s', .ok a) := by
  simp [thr]

theorem pure_ok {α : Type} {a b : α} {R : CH} {s s' : BufS} (h : (pure a : BM α) R s = (s', .ok b)) :
    a = b := by
  simp only [pure_apply, Prod.mk.injEq, Except.ok.injEq] at h
  exact h.2

/-- With no hooks, a callback only logs and counts the call. -/
theorem callback_nohook (c : RCall) (R : CH) (s : BufS) (hh : s.raw.hooks = []) :
    callback c R s = ({ s with raw := (s.raw.enter c).1 }, .ok ()) := by
  unfold callback Raw.enter
  simp [hh]

/-- What a raw callback hands back is the raw method's answer on some raw. -/
theorem onRaw_ok {α : Type} (c : RCall) (f : Raw → Raw × α) (R : CH) (s s' : BufS) (a : α)
    (h : onRaw c f R s = (s', .ok a)) : ∃ r, (f r).2 = a := by
  unfold onRaw at h
  obtain ⟨s0, x, -, h⟩ := bind_ok h
  try dsimp only at h
  split at h
  · obtain ⟨s1, y, h1, -⟩ := bind_ok h
    exact absurd h1 (crash_not_ok _ _ _ _)
  · obtain ⟨s1, y, -, h⟩ := bind_ok h
    obtain ⟨s3, z, h3, h⟩ := bind_ok h
    simp only [get_apply, Prod.mk.injEq] at h3
    obtain ⟨rfl, h3⟩ := h3
    cases h3
    try dsimp only at h
    obtain ⟨s4, w, -, h⟩ := bind_ok h
    exact ⟨_, pure_ok h⟩

/-- On an attached raw with no hooks, a callback answers what the raw method answers. -/
theorem onRaw_nohook {α : Type} (c : RCall) (f : Raw → Raw × α) (R : CH) (s : BufS)
    (hd : s.detached = false) (hh : s.raw.hooks = []) :
    onRaw c f R s = ({ s with raw := (f (s.raw.enter c).1).1 }, .ok (f (s.raw.enter c).1).2) := by
  unfold onRaw
  rw [bind_of_ok (get_apply R s)]
  dsimp only
  simp only [hd, Bool.false_eq_true, ite_false]
  rw [bind_of_ok (callback_nohook _ R s hh)]
  rw [bind_of_ok (get_apply R _)]
  dsimp only
  rw [bind_of_ok (put_apply _ R _)]
  simp [pure_apply, hd]

end BC2

/-- `readinto` of the scripted raw stores at most `len` bytes and never answers
with a bare count. -/
theorem Raw.readinto_data (r : Raw) (len : Nat) (d : List Nat) (h : (r.readinto len).2 = .data d) :
    d.length ≤ len := by
  unfold Raw.readinto at h
  split at h
  · simp at h
  · split at h <;> simp at h
    all_goals (subst h; simp only [List.length_take]; omega)

theorem Raw.readinto_not_count (r : Raw) (len n : Nat) : (r.readinto len).2 ≠ .count n := by
  unfold Raw.readinto
  split
  · simp
  · split <;> simp

theorem Raw.write_count (r : Raw) (b : List Nat) (n : Nat) (h : (r.write b).2 = .count n) :
    n ≤ b.length := by
  unfold Raw.write at h
  split at h
  · simp at h
  · split at h <;> simp at h
    all_goals (subst h; first | omega | (simp only [List.length_take]; omega))

theorem Raw.write_not_data (r : Raw) (b d : List Nat) : (r.write b).2 ≠ .data d := by
  unfold Raw.write
  split
  · simp
  · split <;> simp

/-! ## `_bufferedreader_raw_read` and `_PyIO_trap_eintr` -/

/-- The raw state after a callback that consumed one `readinto` script step. -/
def afterReadinto (s : BufS) (len : Int) (t : List RStep) : BufS :=
  { s with raw := { (s.raw.enter (.readinto len)).1 with rs := t } }

/-- `_bufferedreader_raw_read` (bufferedio.c:1622-1670), for every answer of the
raw stream's `readinto`:

1. it never reports a count outside `[0, len]` other than the `-2` of `None`, and
   it stores no more bytes than it reports (whatever the answer: an exception,
   `None`, a `str`, any int, or bytes), for every state, hook and handler;
2. an int answer `v` that fits `Py_ssize_t` is the count when `0 <= v <= len` and
   is refused with `OSError("raw readinto() returned invalid length ...")`
   otherwise (:1661-1666);
3. an exception that is an `OSError` (any subclass) with `errno == EINTR` is
   swallowed and the call is made again with the same arguments, and every other
   exception propagates unchanged: the class name plays no part, so
   `InterruptedError('x')` (no `errno`) propagates and `PermissionError(EINTR, 'x')`
   is retried (:1639-1641 and `_PyIO_trap_eintr`, :878-901).

Invariant: what is copied out of the buffer was counted as read. The hypothesis
`0 <= len` holds at every caller (`buffer_size - start`, `remaining`, `n > 0`); in
2 and 3 the raw is attached, open and has no hooks, which is what makes its answer
the one the script names. -/
def RawReadChecks : Prop :=
  (∀ (ptr : Option Bool) (len : Int) (fuel : Nat) (R : CH) (s s' : BufS) (n : Int) (d : List Nat),
    0 ≤ len → BC2.rawRead ptr len fuel R s = (s', .ok (n, d)) →
    n = -2 ∨ (0 ≤ n ∧ n ≤ len ∧ (d.length : Int) ≤ n)) ∧
  (∀ (len : Int) (fuel : Nat) (R : CH) (s : BufS) (v : Int) (t : List RStep),
    s.detached = false → s.raw.closed = false → s.raw.hooks = [] → s.raw.rs = .bad v :: t → InSsize v →
    (BC2.rawRead none len (fuel + 1) R s).2 =
      if v < 0 ∨ v > len then
        .error (osError s!"raw readinto() returned invalid length {v} (should have been between 0 and {len})")
      else .ok (v, [])) ∧
  (∀ (len : Int) (fuel : Nat) (R : CH) (s : BufS) (c m : String) (eno : Option Nat) (t : List RStep),
    s.detached = false → s.raw.closed = false → s.raw.hooks = [] →
    s.raw.rs = .raise c m eno :: t →
    (BC2.isOSErrorCls c = true ∧ eno = some 4 →
      BC2.rawRead none len (fuel + 2) R s = BC2.rawRead none len (fuel + 1) R (afterReadinto s len t)) ∧
    (¬(BC2.isOSErrorCls c = true ∧ eno = some 4) →
      (BC2.rawRead none len (fuel + 1) R s).2 = .error (.named c (errMsg m eno))))

theorem rawRead_count (ptr : Option Bool) (len : Int) (hl : 0 ≤ len) : ∀ (fuel : Nat) (R : CH)
    (s s' : BufS) (n : Int) (d : List Nat), BC2.rawRead ptr len fuel R s = (s', .ok (n, d)) →
    n = -2 ∨ (0 ≤ n ∧ n ≤ len ∧ (d.length : Int) ≤ n) := by
  intro fuel
  induction fuel with
  | zero => intro R s s' n d h; simp [BC2.rawRead, BC2.thr] at h
  | succ f ih =>
    intro R s s' n d h
    unfold BC2.rawRead at h
    try dsimp only at h
    split at h
    · obtain ⟨s1, a, h1, -⟩ := BC2.bind_ok h
      exact absurd h1 (BC2.thr_not_ok _ _ _ _ _)
    · obtain ⟨s1, res, ho, h⟩ := BC2.bind_ok h
      obtain ⟨r, hr⟩ := BC2.onRaw_ok _ _ _ _ _ _ ho
      have hlt := Int.toNat_of_nonneg hl
      cases res with
      | exc e =>
        try dsimp only at h
        split at h
        · exact ih _ _ _ _ _ h
        · exact absurd h (BC2.thr_not_ok _ _ _ _ _)
      | none =>
        have := BC2.pure_ok h
        simp only [Prod.mk.injEq] at this
        left; exact this.1.symm
      | data dd =>
        have hlen := Raw.readinto_data r len.toNat dd hr
        try dsimp only at h
        split at h
        · obtain ⟨s2, a, h1, -⟩ := BC2.bind_ok h
          exact absurd h1 (BC2.crash_not_ok _ _ _ _)
        · split at h
          · obtain ⟨s2, a, -, h⟩ := BC2.bind_ok h
            have := BC2.pure_ok h
            simp only [Prod.mk.injEq] at this
            obtain ⟨rfl, rfl⟩ := this
            right; omega
          · have := BC2.pure_ok h
            simp only [Prod.mk.injEq] at this
            obtain ⟨rfl, rfl⟩ := this
            right; omega
      | count k => exact absurd hr (Raw.readinto_not_count r len.toNat k)
      | wrong => exact absurd h (BC2.thr_not_ok _ _ _ _ _)
      | bad v =>
        try dsimp only at h
        split at h
        · exact absurd h (BC2.thr_not_ok _ _ _ _ _)
        · split at h
          · exact absurd h (BC2.thr_not_ok _ _ _ _ _)
          · next hv =>
            split at h
            · obtain ⟨s2, a, -, h⟩ := BC2.bind_ok h
              have := BC2.pure_ok h
              simp only [Prod.mk.injEq] at this
              obtain ⟨rfl, rfl⟩ := this
              right; simp; omega
            · have := BC2.pure_ok h
              simp only [Prod.mk.injEq] at this
              obtain ⟨rfl, rfl⟩ := this
              right; simp; omega

theorem rawReadChecks_proven : RawReadChecks := by
  refine ⟨fun ptr len fuel R s s' n d hl h => rawRead_count ptr len hl fuel R s s' n d h, ?_, ?_⟩
  · intro len fuel R s v t hd hc hh hr hv
    unfold BC2.rawRead
    dsimp only
    simp only [reduceCtorEq, ite_false]
    rw [BC2.bind_of_ok (BC2.onRaw_nohook _ _ R s hd hh)]
    have hres : ((s.raw.enter (.readinto len)).1.readinto len.toNat).2 = .bad v := by
      simp [Raw.readinto, Raw.enter, hc, hr]
    rw [hres]
    dsimp only
    simp only [hv, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    by_cases hb : v < 0 ∨ v > len
    · simp [hb, BC2.thr]
    · simp only [hb, ite_false]
      split
      · rfl
      · rfl
  · intro len fuel R s c m eno t hd hc hh hr
    have hres : ((s.raw.enter (.readinto len)).1.readinto len.toNat).2 =
        .exc (.named c (errMsg m eno)) eno := by
      simp [Raw.readinto, Raw.enter, hc, hr]
    constructor
    · intro ⟨h1, h2⟩
      conv => lhs; unfold BC2.rawRead
      dsimp only
      simp only [reduceCtorEq, ite_false]
      rw [BC2.bind_of_ok (BC2.onRaw_nohook _ _ R s hd hh)]
      rw [hres]
      dsimp only
      simp only [BC2.trapEintr, PyExc.className, h1, h2, beq_self_eq_true, Bool.and_self, ite_true]
      congr 1
      simp [afterReadinto, Raw.readinto, Raw.enter, hc, hr]
    · intro hn
      unfold BC2.rawRead
      dsimp only
      simp only [reduceCtorEq, ite_false]
      rw [BC2.bind_of_ok (BC2.onRaw_nohook _ _ R s hd hh)]
      rw [hres]
      dsimp only
      have ht : BC2.trapEintr (.named c (errMsg m eno)) eno = false := by
        simp only [BC2.trapEintr, PyExc.className, Bool.and_eq_false_iff]
        by_cases h1 : BC2.isOSErrorCls c = true
        · right; cases eno with
          | none => rfl
          | some n =>
            have h4 : n ≠ 4 := fun h4 => hn ⟨h1, by rw [h4]⟩
            simp [h4]
        · left; simpa using h1
      simp only [ht, Bool.false_eq_true, ite_false, BC2.thr]

/-! ## `_bufferedwriter_raw_write` -/

/-- `_bufferedwriter_raw_write` (bufferedio.c:1976-2021), for every answer of the raw
stream's `write`:

1. it never reports a count outside `[0, len(b)]` other than the `-2` of `None`,
   for every state, hook and handler;
2. an int answer `v` is the count when `0 <= v <= len(b)`; otherwise, and for an
   int too large for `Py_ssize_t` (whose failed conversion leaves `n == -1`,
   :2010-2017), it is refused with `OSError("raw write() returned invalid
   length ...")`.

Invariant: `write_pos` only advances over bytes the raw stream accepted. In 2 the
raw is attached, open and has no hooks. -/
def RawWriteChecks : Prop :=
  (∀ (ptr : Option Bool) (b : List Nat) (fuel : Nat) (R : CH) (s s' : BufS) (n : Int),
    BC2.rawWrite ptr b fuel R s = (s', .ok n) → n = -2 ∨ (0 ≤ n ∧ n ≤ b.length)) ∧
  (∀ (b : List Nat) (fuel : Nat) (R : CH) (s : BufS) (v : Int) (t : List RStep),
    s.detached = false → s.raw.closed = false → s.raw.hooks = [] → s.raw.ws = .bad v :: t →
    let n : Int := if InSsize v then v else -1
    (BC2.rawWrite none b (fuel + 1) R s).2 =
      if n < 0 ∨ n > b.length then
        .error (osError s!"raw write() returned invalid length {n} (should have been between 0 and {b.length})")
      else .ok n)

theorem rawWrite_count (ptr : Option Bool) (b : List Nat) : ∀ (fuel : Nat) (R : CH) (s s' : BufS) (n : Int),
    BC2.rawWrite ptr b fuel R s = (s', .ok n) → n = -2 ∨ (0 ≤ n ∧ n ≤ b.length) := by
  intro fuel
  induction fuel with
  | zero => intro R s s' n h; simp [BC2.rawWrite, BC2.thr] at h
  | succ f ih =>
    intro R s s' n h
    unfold BC2.rawWrite at h
    try dsimp only at h
    split at h
    · obtain ⟨s1, a, h1, -⟩ := BC2.bind_ok h
      exact absurd h1 (BC2.thr_not_ok _ _ _ _ _)
    · obtain ⟨s1, res, ho, h⟩ := BC2.bind_ok h
      obtain ⟨r, hr⟩ := BC2.onRaw_ok _ _ _ _ _ _ ho
      try dsimp only at h
      split at h
      · obtain ⟨s2, a, h1, -⟩ := BC2.bind_ok h
        exact absurd h1 (BC2.crash_not_ok _ _ _ _)
      · cases res with
        | exc e =>
          try dsimp only at h
          split at h
          · exact ih _ _ _ _ h
          · exact absurd h (BC2.thr_not_ok _ _ _ _ _)
        | none =>
          left; exact (BC2.pure_ok h).symm
        | count k =>
          have hk := Raw.write_count r b k hr
          try dsimp only at h
          split at h
          · obtain ⟨s2, a, -, h⟩ := BC2.bind_ok h
            have := BC2.pure_ok h
            subst this; right; omega
          · have := BC2.pure_ok h
            subst this; right; omega
        | data dd => exact absurd hr (Raw.write_not_data r b dd)
        | wrong => exact absurd h (BC2.thr_not_ok _ _ _ _ _)
        | bad v =>
          try dsimp only at h
          repeat' (split at h)
          all_goals first
            | exact absurd h (BC2.thr_not_ok _ _ _ _ _)
            | (obtain ⟨s2, a, -, h⟩ := BC2.bind_ok h
               have := BC2.pure_ok h
               subst this; right; omega)
            | (have := BC2.pure_ok h
               subst this; right; omega)

theorem rawWriteChecks_proven : RawWriteChecks := by
  refine ⟨fun ptr b fuel R s s' n h => rawWrite_count ptr b fuel R s s' n h, ?_⟩
  intro b fuel R s v t hd hc hh hw
  unfold BC2.rawWrite
  dsimp only
  simp only [reduceCtorEq, ite_false]
  rw [BC2.bind_of_ok (BC2.onRaw_nohook _ _ R s hd hh)]
  have hres : ((s.raw.enter (.write b)).1.write b).2 = .bad v := by
    simp [Raw.write, Raw.enter, hc, hw]
  rw [hres]
  dsimp only
  generalize hn : (if InSsize v then v else -1) = n
  by_cases hb : n < 0 ∨ n > b.length
  · simp [hb, BC2.thr]
  · simp only [hb, ite_false]
    by_cases hp : n > 0
    · rw [if_pos hp]; rfl
    · rw [if_neg hp]; rfl

end PyLean.PyIO
