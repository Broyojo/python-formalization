import PyLean.Accel.HeapqCRobust

/-!
C and Python agree for every comparison that neither reads nor writes the heap list (`ofSt f`:
it may raise, keep state of its own, and its answer may depend on that state). The C sift
loops swap where the Python ones move items into a hole and write `newitem` at the end; the
simulation invariant is that the C list is the Python list with the hole filled by `newitem`,
and both make the same comparisons, in the same order, on the same operands, with the same
callback state.
-/

namespace PyLean.Accel.Heapq

open PyLean

theorem Eff.bind_assoc {W ε β γ δ : Type} (x : Eff W ε β) (f : β → Eff W ε γ) (g : γ → Eff W ε δ) :
    (x >>= f) >>= g = x >>= fun a => f a >>= g := by
  show Eff.bind' (Eff.bind' x f) g = Eff.bind' x (fun a => Eff.bind' (f a) g)
  unfold Eff.bind'
  congr 1
  funext w
  dsimp only
  rcases x.run w with ⟨r, w'⟩
  cases r <;> rfl

theorem Eff.pure_bind {W ε β γ : Type} (b : β) (f : β → Eff W ε γ) : (pure b >>= f) = f b := rfl

theorem Eff.ite_bind {W ε β γ : Type} (c : Prop) [Decidable c] (x y : Eff W ε β) (g : β → Eff W ε γ) :
    ((if c then x else y) >>= g) = if c then x >>= g else y >>= g := by
  split <;> rfl

variable {σ α : Type} [Inhabited α]

/-! ### Python list primitives -/

theorem listIndex_nat (n len : Nat) (h : n < len) : listIndex (n : Int) len = some n := by
  simp only [listIndex]
  rw [if_neg (show ¬ ((n : Int) < 0) by omega),
    if_pos (show (0 : Int) ≤ (n : Int) ∧ (n : Int) < (len : Int) by omega)]
  simp

theorem listGet_run (i : Int) (n : Nat) (hi : i = n) {w : HW σ α} (h : n < w.heap.length) :
    ((listSeq : Seq (HW σ α) α).get i).run w = (.ok (at! w.heap n), w) := by
  subst hi
  show (match listIndex (n : Int) w.heap.length with
    | some j => (Except.ok (at! w.heap j), w)
    | none => (Except.error (PyExc.indexError "list index out of range"), w)) = _
  rw [listIndex_nat n _ h]

theorem listSet_run (i : Int) (n : Nat) (hi : i = n) (v : α) {w : HW σ α} (h : n < w.heap.length) :
    ((listSeq : Seq (HW σ α) α).set i v).run w = (.ok (), { w with heap := w.heap.set n v }) := by
  subst hi
  show (match listIndex (n : Int) w.heap.length with
    | some j => (Except.ok (), { w with heap := w.heap.set j v })
    | none => (Except.error (PyExc.indexError "list assignment index out of range"), w)) = _
  rw [listIndex_nat n _ h]

@[simp] theorem listLen_run (w : HW σ α) :
    ((listSeq : Seq (HW σ α) α).len).run w = (.ok w.heap.length, w) := rfl

@[simp] theorem listAppend_run (v : α) (w : HW σ α) :
    ((listSeq : Seq (HW σ α) α).append v).run w = (.ok (), { w with heap := w.heap ++ [v] }) := rfl

@[simp] theorem listTruth_run (w : HW σ α) :
    ((listSeq : Seq (HW σ α) α).truth).run w = (.ok (!w.heap.isEmpty), w) := rfl

theorem ofSt_run (f : α → α → σ → Except PyExc Bool × σ) (a b : α) (w : HW σ α) :
    (ofSt f a b).run w = ((f a b w.st).1, { w with st := (f a b w.st).2 }) := rfl

theorem cLtOrd_ofSt (mx : Bool) (f : α → α → σ → Except PyExc Bool × σ) (x y : α) :
    cLtOrd mx (ofSt f) x y = cLt (ofSt f) (if mx then y else x) (if mx then x else y) := by
  cases mx <;> rfl

theorem pyLtOrd_ofSt (mx : Bool) (f : α → α → σ → Except PyExc Bool × σ) (x y : α) :
    pyLtOrd (ofSt f) mx x y = ofSt f (if mx then y else x) (if mx then x else y) := by
  cases mx <;> rfl

/-- One comparison through `ofSt f`, in C and in Python, on worlds with the same state. -/
theorem cmp_ofSt (f : α → α → σ → Except PyExc Bool × σ) (a b : α) (st : σ) (hC hP : List α) :
    (∃ c s', f a b st = (.ok c, s') ∧
      (cLt (ofSt f) a b).run ⟨st, hC⟩ = (.ok c, ⟨s', hC⟩) ∧
      (ofSt f a b).run ⟨st, hP⟩ = (.ok c, ⟨s', hP⟩)) ∨
    (∃ e s', (cLt (ofSt f) a b).run ⟨st, hC⟩ = (.error (.py e), ⟨s', hC⟩) ∧
      (ofSt f a b).run ⟨st, hP⟩ = (.error e, ⟨s', hP⟩)) := by
  rcases h : f a b st with ⟨r, s'⟩
  cases r with
  | ok c => exact Or.inl ⟨c, s', rfl, by simp [cLt_run, ofSt_run, h], by simp [ofSt_run, h]⟩
  | error e => exact Or.inr ⟨e, s', by simp [cLt_run, ofSt_run, h], by simp [ofSt_run, h]⟩

/-! ### Outcome relations -/

/-- Same outcome: the same value and the same world, or the same exception with the same
callback state (the lists may differ: see `HeapTwinsAgreeOnRaise`). -/
def Rel {β : Type} : Except CErr β × HW σ α → Except PyExc β × HW σ α → Prop
  | (.ok a, w1), (.ok b, w2) => a = b ∧ w1 = w2
  | (.error (.py e1), w1), (.error e2, w2) => e1 = e2 ∧ w1.st = w2.st
  | _, _ => False

theorem Rel.bind {β γ : Type} {x : CM σ α β} {y : Eff (HW σ α) PyExc β} {f : β → CM σ α γ}
    {g : β → Eff (HW σ α) PyExc γ} {w1 w2 : HW σ α} (h : Rel (x.run w1) (y.run w2))
    (hk : ∀ b w, Rel ((f b).run w) ((g b).run w)) : Rel ((x >>= f).run w1) ((y >>= g).run w2) := by
  rcases hx : x.run w1 with ⟨r1, v1⟩
  rcases hy : y.run w2 with ⟨r2, v2⟩
  rw [hx, hy] at h
  cases r1 with
  | ok a =>
    cases r2 with
    | ok b =>
      obtain ⟨rfl, rfl⟩ := h
      rw [Eff.run_bind_ok hx, Eff.run_bind_ok hy]; exact hk a v1
    | error _ => exact h.elim
  | error e1 =>
    cases e1 with
    | crash _ => cases r2 <;> exact h.elim
    | py e1 =>
      cases r2 with
      | ok _ => exact h.elim
      | error e2 => rw [Eff.run_bind_err hx, Eff.run_bind_err hy]; exact h

theorem Rel.pure {β : Type} (b : β) (w : HW σ α) :
    Rel ((Pure.pure b : CM σ α β).run w) ((Pure.pure b : Eff (HW σ α) PyExc β).run w) :=
  ⟨rfl, rfl⟩

/-! ### siftdown -/

theorem set_swap (h : List α) (pos pp : Nat) (n v : α) (hne : pos ≠ pp) :
    ((h.set pos n).set pp n).set pos v = (h.set pos v).set pp n := by
  rw [List.set_comm _ _ hne, List.set_set, List.set_comm _ _ (Ne.symm hne)]

theorem pp_int (pos : Nat) (h : 1 ≤ pos) :
    ((pos : Int) - (1 : Int)) / (2 : Int) = (((pos - 1) >>> 1 : Nat) : Int) := by
  rw [shr1']; omega

theorem sdLoop_sim (mx : Bool) (f : α → α → σ → Except PyExc Bool × σ) (s0 : Nat) (newitem : α) :
    ∀ (fuel pos : Nat) (hP : List α) (st : σ), pos < hP.length → pos < fuel →
      Rel ((cSiftdownLoop mx (ofSt f) s0 hP.length fuel newitem pos).run ⟨st, hP.set pos newitem⟩)
        ((pySiftdownLoop listSeq (ofSt f) mx (s0 : Int) newitem fuel (pos : Int) >>= fun p =>
          listSeq.set p newitem).run ⟨st, hP⟩) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ h; omega
  | succ fuel ih =>
    intro pos hP st hpos hf
    simp only [cSiftdownLoop, pySiftdownLoop]
    by_cases hgt : pos > s0
    · have hgt' : (pos : Int) > (s0 : Int) := by omega
      rw [if_pos hgt, if_pos hgt', pp_int pos (by omega)]
      have hpp : (pos - 1) >>> 1 < pos := by rw [shr1']; omega
      have hne : pos ≠ (pos - 1) >>> 1 := by omega
      simp only [Eff.bind_assoc]
      rw [Eff.run_bind_ok (cItem_run (show (pos - 1) >>> 1 < (hP.set pos newitem).length by
          simp; omega)),
        Eff.run_bind_ok (listGet_run _ _ rfl (show (pos - 1) >>> 1 < hP.length by omega)),
        at!_set_ne _ _ _ _ hne, cLtOrd_ofSt, pyLtOrd_ofSt]
      rcases cmp_ofSt f (if mx then at! hP ((pos - 1) >>> 1) else newitem)
          (if mx then newitem else at! hP ((pos - 1) >>> 1)) st (hP.set pos newitem) hP with
        ⟨c, s', -, h1, h2⟩ | ⟨e, s', h1, h2⟩
      · rw [Eff.run_bind_ok h1, Eff.run_bind_ok h2, Eff.run_bind_ok (cSize_run _)]
        simp only [List.length_set, ne_eq, not_true_eq_false, if_false]
        cases c
        · simp only [Bool.not_false, if_true, Bool.false_eq_true, if_false, Eff.run_pure]
          rw [Eff.pure_bind, listSet_run _ pos rfl _ hpos]
          exact ⟨rfl, rfl⟩
        · simp only [Bool.not_true, Bool.false_eq_true, if_false, if_true, Eff.bind_assoc]
          rw [Eff.run_bind_ok (cItem_run (show (pos - 1) >>> 1 < (hP.set pos newitem).length by
              simp; omega)),
            Eff.run_bind_ok (cItem_run (show pos < (hP.set pos newitem).length by simp; omega)),
            at!_set_ne _ _ _ _ hne, at!_set_self _ _ _ hpos,
            Eff.run_bind_ok (cStore_run (show (pos - 1) >>> 1 < (hP.set pos newitem).length by
              simp; omega)),
            Eff.run_bind_ok (cStore_run (show pos < ((hP.set pos newitem).set ((pos - 1) >>> 1)
              newitem).length by simp; omega)),
            Eff.run_bind_ok (listSet_run _ pos rfl _ hpos)]
          simp only
          rw [set_swap _ _ _ _ _ hne]
          have := ih ((pos - 1) >>> 1) (hP.set pos (at! hP ((pos - 1) >>> 1))) s'
            (by simp; omega) (by omega)
          simpa only [List.length_set] using this
      · rw [Eff.run_bind_err h1, Eff.run_bind_err h2]
        exact ⟨rfl, rfl⟩
    · have hgt' : ¬ (pos : Int) > (s0 : Int) := by omega
      rw [if_neg hgt, if_neg hgt', Eff.run_pure, Eff.pure_bind, listSet_run _ pos rfl _ hpos]
      exact ⟨rfl, rfl⟩

theorem siftdown_sim (mx : Bool) (f : α → α → σ → Except PyExc Bool × σ) (s0 pos : Nat)
    (w : HW σ α) (h : pos < w.heap.length) :
    Rel ((cSiftdown mx (ofSt f) s0 pos).run w)
      ((pySiftdown listSeq (ofSt f) mx (s0 : Int) (pos : Int)).run w) := by
  simp only [cSiftdown, pySiftdown]
  rw [Eff.run_bind_ok (cSize_run w), if_neg (Nat.not_le.2 h), Eff.run_bind_ok (cItem_run h),
    Eff.run_bind_ok (listGet_run _ pos rfl h), Int.toNat_natCast]
  have := sdLoop_sim mx f s0 (at! w.heap pos) (pos + 1) pos w.heap w.st h (by omega)
  rw [set_at!_self] at this
  exact this

/-! ### siftup -/

/-- The Python loop result relates to the C one: the same final `pos`, and the C list is the
Python list with the hole at `pos` filled by `newitem`. -/
def HoleRel (newitem : α) (len : Nat) :
    Except CErr Nat × HW σ α → Except PyExc Int × HW σ α → Prop
  | (.ok p, wC), (.ok q, wP) =>
    q = p ∧ p < len ∧ wP.heap.length = len ∧ wC = { wP with heap := wP.heap.set p newitem }
  | (.error (.py e1), wC), (.error e2, wP) => e1 = e2 ∧ wC.st = wP.st
  | _, _ => False

theorem child_sim (mx : Bool) (f : α → α → σ → Except PyExc Bool × σ) (endpos cp pos : Nat)
    (newitem : α) (hP : List α) (st : σ) (hlen : hP.length = endpos) (hpos : pos < cp)
    (hcp : cp < endpos) :
    (∃ b s', (cChild mx (ofSt f) endpos cp).run ⟨st, hP.set pos newitem⟩ =
        (.ok (if b then cp + 1 else cp), ⟨s', hP.set pos newitem⟩) ∧
      (pyTakeRight listSeq (ofSt f) mx endpos (cp : Int) ((cp : Int) + 1)).run ⟨st, hP⟩ =
        (.ok b, ⟨s', hP⟩) ∧ (b = true → cp + 1 < endpos)) ∨
    (∃ e s', (cChild mx (ofSt f) endpos cp).run ⟨st, hP.set pos newitem⟩ =
        (.error (.py e), ⟨s', hP.set pos newitem⟩) ∧
      (pyTakeRight listSeq (ofSt f) mx endpos (cp : Int) ((cp : Int) + 1)).run ⟨st, hP⟩ =
        (.error e, ⟨s', hP⟩)) := by
  unfold cChild pyTakeRight
  by_cases hr : cp + 1 < endpos
  · have hr' : (cp : Int) + 1 < (endpos : Int) := by omega
    rw [if_pos hr, if_pos hr']
    have hcpne : pos ≠ cp := by omega
    have hcp1ne : pos ≠ cp + 1 := by omega
    have hpy1 : ((cp : Int) + 1) = ((cp + 1 : Nat) : Int) := by omega
    rw [hpy1]
    cases mx
    · -- `siftup`: a = arr[childpos], b = arr[childpos + 1]; Python reads heap[childpos] first
      simp only [pyChildLt, Bool.false_eq_true, ↓reduceIte, Eff.bind_assoc]
      rw [Eff.run_bind_ok (cItem_run (show cp < (hP.set pos newitem).length by simp; omega)),
        Eff.run_bind_ok (cItem_run (show cp + 1 < (hP.set pos newitem).length by simp; omega)),
        at!_set_ne _ _ _ _ hcpne, at!_set_ne _ _ _ _ hcp1ne,
        Eff.run_bind_ok (listGet_run _ cp rfl (show cp < hP.length by omega)),
        Eff.run_bind_ok (listGet_run _ (cp + 1) rfl (show cp + 1 < hP.length by omega))]
      rcases cmp_ofSt f (at! hP cp) (at! hP (cp + 1)) st (hP.set pos newitem) hP with
        ⟨c, s', -, h1, h2⟩ | ⟨e, s', h1, h2⟩
      · rw [Eff.run_bind_ok h1, Eff.run_bind_ok h2, Eff.run_bind_ok (cSize_run _)]
        simp only [List.length_set, hlen, ne_eq, not_true_eq_false, ↓reduceIte, Eff.run_pure]
        refine Or.inl ⟨!c, s', ?_, by rfl, fun _ => hr⟩
        cases c <;> simp
      · rw [Eff.run_bind_err h1, Eff.run_bind_err h2]
        exact Or.inr ⟨e, s', rfl, rfl⟩
    · -- `siftup_max`: a = arr[childpos + 1], b = arr[childpos]; Python reads heap[rightpos] first
      simp only [pyChildLt, ↓reduceIte, Eff.bind_assoc]
      rw [Eff.run_bind_ok (cItem_run (show cp + 1 < (hP.set pos newitem).length by simp; omega)),
        Eff.run_bind_ok (cItem_run (show cp < (hP.set pos newitem).length by simp; omega)),
        at!_set_ne _ _ _ _ hcpne, at!_set_ne _ _ _ _ hcp1ne,
        Eff.run_bind_ok (listGet_run _ (cp + 1) rfl (show cp + 1 < hP.length by omega)),
        Eff.run_bind_ok (listGet_run _ cp rfl (show cp < hP.length by omega))]
      rcases cmp_ofSt f (at! hP (cp + 1)) (at! hP cp) st (hP.set pos newitem) hP with
        ⟨c, s', -, h1, h2⟩ | ⟨e, s', h1, h2⟩
      · rw [Eff.run_bind_ok h1, Eff.run_bind_ok h2, Eff.run_bind_ok (cSize_run _)]
        simp only [List.length_set, hlen, ne_eq, not_true_eq_false, ↓reduceIte, Eff.run_pure]
        refine Or.inl ⟨!c, s', ?_, by rfl, fun _ => hr⟩
        cases c <;> simp
      · rw [Eff.run_bind_err h1, Eff.run_bind_err h2]
        exact Or.inr ⟨e, s', rfl, rfl⟩
  · have hr' : ¬ (cp : Int) + 1 < (endpos : Int) := by omega
    rw [if_neg hr, if_neg hr']
    exact Or.inl ⟨false, st, rfl, rfl, by simp⟩

theorem suLoop_sim (mx : Bool) (f : α → α → σ → Except PyExc Bool × σ) (endpos : Nat) (newitem : α) :
    ∀ (fuel pos : Nat) (hP : List α) (st : σ), hP.length = endpos → pos < endpos →
      endpos - pos < fuel →
      HoleRel newitem endpos
        ((cSiftupLoop mx (ofSt f) endpos (endpos >>> 1) fuel pos).run ⟨st, hP.set pos newitem⟩)
        ((pySiftupLoop listSeq (ofSt f) mx endpos fuel (pos : Int)).run ⟨st, hP⟩) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ h; omega
  | succ fuel ih =>
    intro pos hP st hlen hpos hf
    simp only [cSiftupLoop, pySiftupLoop]
    by_cases hlim : pos < endpos >>> 1
    · have hc : 2 * pos + 1 < endpos := by rw [shr1'] at hlim; omega
      have hc' : 2 * (pos : Int) + 1 < (endpos : Int) := by omega
      have e : 2 * (pos : Int) + 1 = ((2 * pos + 1 : Nat) : Int) := by omega
      rw [if_pos hlim, if_pos hc', e]
      rcases child_sim mx f endpos (2 * pos + 1) pos newitem hP st hlen (by omega) hc with
        ⟨b, s', h1, h2, hb⟩ | ⟨e, s', h1, h2⟩
      · rw [Eff.run_bind_ok h1, Eff.run_bind_ok h2]
        cases b
        · try simp only [Bool.false_eq_true, ↓reduceIte]
          have hne : pos ≠ 2 * pos + 1 := by omega
          rw [Eff.run_bind_ok (cItem_run (show 2 * pos + 1 < (hP.set pos newitem).length by
              simp; omega)),
            Eff.run_bind_ok (cItem_run (show pos < (hP.set pos newitem).length by simp; omega)),
            at!_set_ne _ _ _ _ hne, at!_set_self _ _ _ (by omega),
            Eff.run_bind_ok (cStore_run (show 2 * pos + 1 < (hP.set pos newitem).length by
              simp; omega)),
            Eff.run_bind_ok (cStore_run (show pos < ((hP.set pos newitem).set (2 * pos + 1)
              newitem).length by simp; omega)),
            Eff.run_bind_ok (listGet_run _ (2 * pos + 1) rfl (show 2 * pos + 1 < hP.length by omega)),
            Eff.run_bind_ok (listSet_run _ pos rfl _ (show pos < hP.length by omega))]
          simp only
          rw [set_swap _ _ _ _ _ hne]
          exact ih (2 * pos + 1) (hP.set pos (at! hP (2 * pos + 1))) s' (by simp; omega) hc
            (by omega)
        · try simp only [↓reduceIte]
          have hb' := hb rfl
          have hne : pos ≠ 2 * pos + 1 + 1 := by omega
          have e2 : ((2 * pos + 1 : Nat) : Int) + 1 = ((2 * pos + 1 + 1 : Nat) : Int) := by omega
          rw [e2]
          rw [Eff.run_bind_ok (cItem_run (show 2 * pos + 1 + 1 < (hP.set pos newitem).length by
              simp; omega)),
            Eff.run_bind_ok (cItem_run (show pos < (hP.set pos newitem).length by simp; omega)),
            at!_set_ne _ _ _ _ hne, at!_set_self _ _ _ (by omega),
            Eff.run_bind_ok (cStore_run (show 2 * pos + 1 + 1 < (hP.set pos newitem).length by
              simp; omega)),
            Eff.run_bind_ok (cStore_run (show pos < ((hP.set pos newitem).set (2 * pos + 1 + 1)
              newitem).length by simp; omega)),
            Eff.run_bind_ok (listGet_run _ (2 * pos + 1 + 1) rfl
              (show 2 * pos + 1 + 1 < hP.length by omega)),
            Eff.run_bind_ok (listSet_run _ pos rfl _ (show pos < hP.length by omega))]
          simp only
          rw [set_swap _ _ _ _ _ hne]
          exact ih (2 * pos + 1 + 1) (hP.set pos (at! hP (2 * pos + 1 + 1))) s' (by simp; omega)
            hb' (by omega)
      · rw [Eff.run_bind_err h1, Eff.run_bind_err h2]
        exact ⟨rfl, rfl⟩
    · have hc' : ¬ 2 * (pos : Int) + 1 < (endpos : Int) := by rw [shr1'] at hlim; omega
      rw [if_neg hlim, if_neg hc']
      exact ⟨rfl, hpos, hlen, rfl⟩

theorem siftup_sim (mx : Bool) (f : α → α → σ → Except PyExc Bool × σ) (pos : Nat) (w : HW σ α)
    (h : pos < w.heap.length) :
    Rel ((cSiftup mx (ofSt f) pos).run w) ((pySiftup listSeq (ofSt f) mx (pos : Int)).run w) := by
  simp only [cSiftup, pySiftup]
  rw [Eff.run_bind_ok (cSize_run w), if_neg (Nat.not_le.2 h), Eff.run_bind_ok (listLen_run w),
    Eff.run_bind_ok (listGet_run _ pos rfl h)]
  have hl := suLoop_sim mx f w.heap.length (at! w.heap pos) (w.heap.length + 1) pos w.heap w.st rfl h
    (by omega)
  rw [set_at!_self] at hl
  rcases hc : (cSiftupLoop mx (ofSt f) w.heap.length (w.heap.length >>> 1) (w.heap.length + 1) pos).run w
    with ⟨rc, wc⟩
  rcases hp : (pySiftupLoop listSeq (ofSt f) mx w.heap.length (w.heap.length + 1) (pos : Int)).run w
    with ⟨rp, wp⟩
  have hl' : HoleRel (at! w.heap pos) w.heap.length (rc, wc) (rp, wp) := by
    rw [← hc, ← hp]; exact hl
  cases rc with
  | ok p =>
    cases rp with
    | ok q =>
      obtain ⟨rfl, hp1, hp2, rfl⟩ := hl'
      rw [Eff.run_bind_ok hc, Eff.run_bind_ok hp,
        Eff.run_bind_ok (listSet_run _ p rfl _ (show p < wp.heap.length by omega))]
      exact siftdown_sim mx f pos p _ (by simp; omega)
    | error _ => exact hl'.elim
  | error e1 =>
    cases e1 with
    | crash _ => cases rp <;> exact hl'.elim
    | py e1 =>
      cases rp with
      | ok _ => exact hl'.elim
      | error e2 => rw [Eff.run_bind_err hc, Eff.run_bind_err hp]; exact hl'

end PyLean.Accel.Heapq
