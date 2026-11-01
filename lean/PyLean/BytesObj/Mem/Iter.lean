import PyLean.BytesObj.Mem.Misc

/-!
Iteration, `count` and `index` on 1-D views, against the items `tolist` gives.
-/

namespace PyLean.BytesObj.Mem

open PyLean

/-- Calling `next` up to `k` times, collecting the items until it stops. -/
def drain (it : Nat) : Nat → M (List Item)
  | 0 => pure []
  | k + 1 => do
    match ← memoryiterNext it with
    | none => pure []
    | some x => return x :: (← drain it k)

/-- The iterator `it` is at `index`, over the 1-D view `v`, with format `fmt`. -/
structure IterAt (st : St) (it v : Nat) (index n : Int) (fmt : List Char) : Prop where
  valid : it < st.iters.length
  state : st.iters.getD it default = { index := index, seq := some v, length := n, fmt := fmt }

/-- `st` after one item of iterator `it`. -/
def stepIter (st : St) (it v : Nat) (index n : Int) (fmt : List Char) : St :=
  { st with iters := st.iters.set it { index := index + 1, seq := some v, length := n, fmt := fmt } }

/-- `st` after iterator `it` stopped. -/
def stopIter (st : St) (it : Nat) (index n : Int) (fmt : List Char) : St :=
  { st with iters := st.iters.set it { index := index, seq := none, length := n, fmt := fmt } }

/-- `st` with a new iterator. -/
def newIter (st : St) (v : Nat) (n : Int) (fmt : List Char) : St :=
  { st with iters := st.iters ++ [{ fmt := fmt, length := n, index := 0, seq := some v }] }

theorem live_iters (st : St) (self : Nat) (n d : Int) (f : List Char) (l : List MIter)
    (h : Live1D st self n d f) : Live1D { st with iters := l } self n d f :=
  { valid := h.valid, mbuf := h.mbuf, live := h.live, unres := h.unres, ndim := h.ndim,
    shape := h.shape, strides := h.strides, subs := h.subs, format := h.format,
    nonneg := h.nonneg, bound := h.bound, span := h.span }

theorem iter_step (st : St) (it self : Nat) (index n d : Int) (f fmt : List Char)
    (hL : Live1D st self n d f) (hI : IterAt st it self index n fmt) (h : index < n)
    (g : Int → Item) (hg : ∀ p, unpackRaw st.mem p fmt = .ok (g p)) :
    memoryiterNext it st =
      (.ok (some (g ((st.mv self).view.buf + d * index))),
       stepIter st it self index n fmt) := by
  have hl' : baseInaccessible (stepIter st it self index n fmt) self = false := hL.live
  simp only [memoryiterNext, M.bind_app, M.get, hI.state, h, ↓reduceIte, checkReleased_ok _ _ hL.live,
    hL.strides, hL.subs, Option.getD_some, List.getD_cons_zero, adjustPtr_none, M.modify,
    M.pure_app]
  have hu : unpackSingle self ((st.mv self).view.buf + d * index) fmt (stepIter st it self index n fmt) =
      (.ok (g ((st.mv self).view.buf + d * index)), stepIter st it self index n fmt) := by
    rw [unpackSingle_live _ _ _ _ hl', show (stepIter st it self index n fmt).mem = st.mem from rfl, hg]
  simp only [stepIter] at hu ⊢
  rw [hu]

theorem iter_stop (st : St) (it self : Nat) (index n : Int) (fmt : List Char)
    (hI : IterAt st it self index n fmt) (h : ¬ index < n) :
    memoryiterNext it st =
      (.ok none, stopIter st it index n fmt) := by
  simp only [memoryiterNext, M.bind_app, M.get, hI.state, h, ↓reduceIte, M.modify, M.pure_app]
  rfl

theorem iterAt_step (st : St) (it self : Nat) (index n : Int) (fmt : List Char)
    (hI : IterAt st it self index n fmt) :
    IterAt (stepIter st it self index n fmt) it self (index + 1) n fmt := by
  have hv := hI.valid
  exact ⟨by simpa [stepIter] using hv, by
    simp [stepIter, List.getD_eq_getElem?_getD, hv]⟩

/-- `next` walks the items from `index` to the end, then stops. -/
theorem drain_spec (it self : Nat) (n d : Int) (f fmt : List Char) (g : Int → Item) (k : Nat)
    (st : St) (index : Int) (hL : Live1D st self n d f) (hI : IterAt st it self index n fmt)
    (hk : (n - index).toNat = k) (hi : index ≤ n)
    (hg : ∀ p, unpackRaw st.mem p fmt = .ok (g p)) :
    ∃ s, drain it (k + 1) st = (.ok ((walk d k ((st.mv self).view.buf + d * index)).map g), s) ∧
      s.mem = st.mem ∧ s.mvs = st.mvs ∧ s.mbufs = st.mbufs := by
  induction k generalizing st index with
  | zero =>
    have h : ¬ index < n := by omega
    simp only [drain, M.bind_app, iter_stop st it self index n fmt hI h, M.pure_app, walk, List.map_nil]
    exact ⟨_, rfl, rfl, rfl, rfl⟩
  | succ k ih =>
    have h : index < n := by omega
    have e := iter_step st it self index n d f fmt hL hI h g hg
    have hL' : Live1D (stepIter st it self index n fmt) self n d f := live_iters st self n d f _ hL
    obtain ⟨s, h1, h2, h3, h4⟩ := ih _ (index + 1) hL' (iterAt_step st it self index n fmt hI) (by omega)
      (by omega) hg
    refine ⟨s, ?_, h2, h3, h4⟩
    have hbuf : (St.mv (stepIter st it self index n fmt) self).view.buf = (st.mv self).view.buf := rfl
    rw [drain]
    simp only [M.bind_app, e, h1, M.pure_app]
    simp only [walk, List.map_cons, hbuf]
    rw [show (st.mv self).view.buf + d * index + d = (st.mv self).view.buf + d * (index + 1) by
      rw [Int.mul_add, Int.mul_one, Int.add_assoc]]

theorem memoryIter_spec (st : St) (self : Nat) (n d : Int) (f fmt : List Char)
    (hL : Live1D st self n d f) (hf : adjustFmt (st.mv self).view = .ok fmt) :
    memoryIter self st = (.ok st.iters.length, newIter st self n fmt) := by
  have hl : memoryLength self st = (.ok n, st) := by
    simp only [memoryLength, M.bind_app, checkReleased_ok _ _ hL.live, M.get, hL.ndim, Nat.one_ne_zero,
      ↓reduceIte, M.pure_app, hL.shape, Option.getD_some, List.getD_cons_zero]
  simp only [memoryIter, M.bind_app, checkReleased_ok _ _ hL.live, M.get, hL.ndim, Nat.one_ne_zero,
    ↓reduceIte, ne_eq, not_true_eq_false, M.lift, hf]
  rw [hl]
  rfl

/-- `list(m)` is `m.tolist()` for every 1-D view of a native format, for every stride
(`memory_iter`, `memoryiter_next`, `memory_length`, :3491-3555): each item in order, then
`StopIteration`. Hypotheses: a live view. -/
def IterYields : Prop :=
  ∀ (st : St) (self : Nat) (n d : Int) (f : List Char) (c : Char),
    Live1D st self n d f → adjustFmt (st.mv self).view = .ok [c] → nativeChar c = true →
    ∃ g : Int → Item, (∀ p, unpackRaw st.mem p [c] = .ok (g p)) ∧
      ∃ s, (do let it ← memoryIter self; drain it (n.toNat + 1) : M (List Item)) st =
        (.ok ((walk d n.toNat (st.mv self).view.buf).map g), s)

theorem iterAt_new (st : St) (self : Nat) (n : Int) (fmt : List Char) :
    IterAt (newIter st self n fmt) st.iters.length self 0 n fmt :=
  ⟨by simp [newIter], by simp [newIter, List.getD_eq_getElem?_getD]⟩

theorem iterYields_proven : IterYields := by
  intro st self n d f c hL hf hc
  obtain ⟨g, hg⟩ := native_total st.mem c hc
  refine ⟨g, hg, ?_⟩
  have hL' : Live1D (newIter st self n [c]) self n d f := live_iters st self n d f _ hL
  obtain ⟨s, h1, -, -, -⟩ := drain_spec st.iters.length self n d f [c] g n.toNat _ 0 hL'
    (iterAt_new st self n [c]) (by simp) hL.nonneg hg
  refine ⟨s, ?_⟩
  simp only [M.bind_app, memoryIter_spec st self n d f [c] hL hf, h1]
  simp [show St.mv (newIter st self n [c]) self = st.mv self from rfl]

/-- The count `countLoop` reaches. -/
def countItems (x : Obj) (l : List Item) : Int := (l.filter fun i => itemEqObj i x).length

theorem countLoop_spec (it self : Nat) (n d : Int) (f fmt : List Char) (g : Int → Item) (value : Obj)
    (k : Nat) (st : St) (index count : Int) (fuel : Nat) (hL : Live1D st self n d f)
    (hI : IterAt st it self index n fmt) (hk : (n - index).toNat = k) (hi : index ≤ n)
    (hg : ∀ p, unpackRaw st.mem p fmt = .ok (g p)) (hf : k + 1 ≤ fuel) :
    (countLoop it value fuel count st).1 =
      .ok (count + countItems value ((walk d k ((st.mv self).view.buf + d * index)).map g)) := by
  induction k generalizing st index count fuel with
  | zero =>
    match fuel, hf with
    | fuel + 1, _ =>
      have h : ¬ index < n := by omega
      simp [countLoop, M.bind_app, iter_stop st it self index n fmt hI h, M.pure_app, walk, countItems]
  | succ k ih =>
    match fuel, hf with
    | fuel + 1, hf =>
      have h : index < n := by omega
      have e := iter_step st it self index n d f fmt hL hI h g hg
      have hL' : Live1D (stepIter st it self index n fmt) self n d f := live_iters st self n d f _ hL
      have ih' := ih _ (index + 1) (if itemEqObj (g ((st.mv self).view.buf + d * index)) value = true
        then count + 1 else count) fuel hL' (iterAt_step st it self index n fmt hI) (by omega) (by omega)
        hg (by omega)
      simp only [countLoop, M.bind_app, e]
      rw [ih']
      have hbuf : (St.mv (stepIter st it self index n fmt) self).view.buf = (st.mv self).view.buf := rfl
      rw [hbuf, show (st.mv self).view.buf + d * (index + 1) = (st.mv self).view.buf + d * index + d by
        rw [Int.mul_add, Int.mul_one, Int.add_assoc]]
      simp only [walk, List.map_cons, countItems, List.filter_cons]
      split <;> simp <;> omega

/-- `m.count(x)` is `m.tolist().count(x)` for every 1-D view of a native format and every
built-in `x`, for every stride. Hypotheses: a live view. -/
def CountIsList : Prop :=
  ∀ (st : St) (self : Nat) (n d : Int) (f : List Char) (c : Char) (x : Obj),
    Live1D st self n d f → adjustFmt (st.mv self).view = .ok [c] → nativeChar c = true →
    ∃ g : Int → Item, (∀ p, unpackRaw st.mem p [c] = .ok (g p)) ∧
      (memoryviewCount self x st).1 =
        .ok (countItems x ((walk d n.toNat (st.mv self).view.buf).map g))

theorem countIsList_proven : CountIsList := by
  intro st self n d f c x hL hf hc
  obtain ⟨g, hg⟩ := native_total st.mem c hc
  refine ⟨g, hg, ?_⟩
  have hL' : Live1D (newIter st self n [c]) self n d f := live_iters st self n d f _ hL
  have hs := countLoop_spec st.iters.length self n d f [c] g x n.toNat _ 0 0 (n.toNat + 2) hL'
    (iterAt_new st self n [c]) (by simp) hL.nonneg hg (by omega)
  have hlen : ((newIter st self n [c]).iters.getD st.iters.length default).length = n := by
    simp [newIter, List.getD_eq_getElem?_getD]
  simp only [memoryviewCount, M.bind_app, memoryIter_spec st self n d f [c] hL hf, M.get, hlen]
  rw [hs]
  simp [show St.mv (newIter st self n [c]) self = st.mv self from rfl]

/-- First position `>= start` and `< stop` of `x`, on the item at each address. -/
def firstFrom (g : Int → Item) (buf d : Int) (x : Obj) : Nat → Int → Option Int
  | 0, _ => none
  | k + 1, i => if itemEqObj (g (buf + d * i)) x then some i else firstFrom g buf d x k (i + 1)

theorem indexLoop_spec (self : Nat) (n d : Int) (f fmt : List Char) (g : Int → Item) (value : Obj)
    (st : St) (hL : Live1D st self n d f) (hf : adjustFmt (st.mv self).view = .ok fmt)
    (hg : ∀ p, unpackRaw st.mem p fmt = .ok (g p)) (fuel : Nat) (i stop : Int)
    (h0 : 0 ≤ i) (hs : stop ≤ n) (hk : (stop - i).toNat = fuel) :
    indexLoop self value (fuel + 1) i stop st =
      (match firstFrom g (st.mv self).view.buf d value fuel i with
       | some j => .ok j
       | none => .error (.valueError "memoryview.index(x): x not found"), st) := by
  induction fuel generalizing i with
  | zero =>
    have : ¬ i < stop := by omega
    simp [indexLoop, this, firstFrom, M.throw_app]
  | succ k ih =>
    have hlt : i < stop := by omega
    have hin : -n ≤ i ∧ i < n := by omega
    have hpos : pos i n = i := by simp [pos, show ¬ i < 0 by omega]
    have hm := memoryItem_eq st self i n d f fmt hL hf
    rw [lookup_in _ _ _ i n d hL.shape hL.strides hL.subs hin, hpos] at hm
    simp only [hg] at hm
    rw [indexLoop]
    simp only [hlt, ↓reduceIte, M.bind_app, hm, firstFrom]
    split
    · simp [M.pure_app]
    · exact ih (i + 1) (by omega) (by omega)

/-- `m.index(x, start, stop)` on a 1-D view of a native format searches exactly
`range(start', stop')`, where a negative bound counts from the end and both are clipped to
`[0, n]`: the first position whose item equals `x`, or `ValueError`, like `list.index` on
`tolist()` (:2852-2898). Hypotheses: a live view; `start` and `stop` are `Py_ssize_t`, as
`slice_index` leaves them. -/
def IndexIsSearch : Prop :=
  ∀ (st : St) (self : Nat) (n d : Int) (f : List Char) (c : Char) (x : Obj) (start stop : Int),
    Live1D st self n d f → adjustFmt (st.mv self).view = .ok [c] → nativeChar c = true →
    ∃ g : Int → Item, (∀ p, unpackRaw st.mem p [c] = .ok (g p)) ∧
      let stop' := min (if stop < 0 then max (stop + n) 0 else stop) n
      let start' := min (if start < 0 then max (start + n) 0 else start) stop'
      memoryviewIndex self x start stop st =
        (match firstFrom g (st.mv self).view.buf d x (stop' - start').toNat start' with
         | some j => .ok j
         | none => .error (.valueError "memoryview.index(x): x not found"), st)

theorem indexIsSearch_proven : IndexIsSearch := by
  intro st self n d f c x start stop hL hf hc
  obtain ⟨g, hg⟩ := native_total st.mem c hc
  refine ⟨g, hg, ?_⟩
  have hnn := hL.nonneg
  intro stop' start'
  have hst : 0 ≤ stop' ∧ stop' ≤ n := by
    simp only [stop']
    split <;> omega
  have hsa : 0 ≤ start' ∧ start' ≤ stop' := by
    simp only [start']
    split <;> omega
  have e : (stop' - start' + 1).toNat = (stop' - start').toNat + 1 := by omega
  simp only [memoryviewIndex, M.bind_app, checkReleased_ok _ _ hL.live, M.get, hL.ndim, Nat.one_ne_zero,
    ↓reduceIte, hL.shape, Option.getD_some, List.getD_cons_zero]
  show indexLoop self x (stop' - start' + 1).toNat start' stop' st = _
  rw [e]
  exact indexLoop_spec self n d f [c] g x st hL hf hg _ _ _ hsa.1 hst.2 rfl

end PyLean.BytesObj.Mem
