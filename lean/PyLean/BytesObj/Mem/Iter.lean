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

theorem memoryviewTolist_eq (st : St) (self : Nat) (c : Char) (sh strs : List Int) (g : Int → Item)
    (hl : baseInaccessible st self = false) (hf : adjustFmt (st.mv self).view = .ok [c])
    (hg : ∀ p, unpackRaw st.mem p [c] = .ok (g p)) (hsh : (st.mv self).view.shape = some sh)
    (hst : (st.mv self).view.strides = some strs) (hne : sh ≠ []) (hn : sh.length = (st.mv self).view.ndim) :
    memoryviewTolist self st =
      (.ok (treeOf st.mem g sh strs (st.mv self).view.suboffsets (st.mv self).view.buf), st) := by
  have hfn : (fun p => (unpackSingle self p [c] st).1) = fun p => Except.ok (g p) := by
    funext p
    rw [unpackSingle_live _ _ _ _ hl, hg]
  have hnd : ¬ (st.mv self).view.ndim = 0 := by
    rw [← hn]
    intro h
    exact hne (List.length_eq_zero_iff.1 h)
  by_cases h1 : (st.mv self).view.ndim = 1
  · have hn' := hn
    rw [h1] at hn'
    obtain ⟨n, rfl⟩ := List.length_eq_one_iff.1 hn'
    simp only [memoryviewTolist, M.bind_app, checkReleased_ok _ _ hl, M.get, M.lift, hf, hnd, ↓reduceIte,
      h1, hsh, hst, Option.getD_some, List.getD_cons_zero]
    simp only [hfn, tolistBase_ok, treeOf, Nat.one_ne_zero, ↓reduceIte, M.bind_app, M.lift, M.pure_app,
      List.map_map]
    rfl
  · simp only [memoryviewTolist, M.bind_app, checkReleased_ok _ _ hl, M.get, M.lift, hf, hnd, ↓reduceIte,
      h1, hsh, hst, Option.getD_some]
    simp only [hfn, tolistRec_ok, M.pure_app]

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

/-- No item of the view is at `NULL`, the exit `IterNull` is about. It holds of every exporter
with memory behind it, so it is a type invariant of the views these theorems are about. -/
def NoNull (st : St) (self : Nat) (d n : Int) : Prop :=
  ∀ j : Int, 0 ≤ j → j < n →
    adjustPtr st.mem ((st.mv self).view.buf + d * j) (st.mv self).view.suboffsets 0 ≠ nullPtr

/-- The item at an address before `ADJUST_PTR`. -/
def ItemAt (st : St) (self : Nat) (fmt : List Char) (g : Int → Item) : Prop :=
  ∀ p, unpackRaw st.mem (adjustPtr st.mem p (st.mv self).view.suboffsets 0) fmt = .ok (g p)

theorem iter_step (st : St) (it self : Nat) (index n d : Int) (f fmt : List Char)
    (hL : Live1D st self n d f) (hI : IterAt st it self index n fmt) (h : index < n)
    (h0 : 0 ≤ index) (hn : NoNull st self d n) (g : Int → Item) (hg : ItemAt st self fmt g) :
    memoryiterNext it st =
      (.ok (some (g ((st.mv self).view.buf + d * index))),
       stepIter st it self index n fmt) := by
  have hl' : baseInaccessible (stepIter st it self index n fmt) self = false := hL.live
  simp only [memoryiterNext, M.bind_app, M.get, hI.state, h, ↓reduceIte, checkReleased_ok _ _ hL.live,
    hL.strides, Option.getD_some, List.getD_cons_zero, M.modify, M.pure_app, hn index h0 h]
  have hu : unpackSingle self
        (adjustPtr st.mem ((st.mv self).view.buf + d * index) (st.mv self).view.suboffsets 0) fmt
        (stepIter st it self index n fmt) =
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
    (hk : (n - index).toNat = k) (hi : index ≤ n) (h0 : 0 ≤ index)
    (hn : NoNull st self d n) (hg : ItemAt st self fmt g) :
    ∃ s, drain it (k + 1) st = (.ok ((walk d k ((st.mv self).view.buf + d * index)).map g), s) ∧
      s.mem = st.mem ∧ s.mvs = st.mvs ∧ s.mbufs = st.mbufs := by
  induction k generalizing st index with
  | zero =>
    have h : ¬ index < n := by omega
    simp only [drain, M.bind_app, iter_stop st it self index n fmt hI h, M.pure_app, walk, List.map_nil]
    exact ⟨_, rfl, rfl, rfl, rfl⟩
  | succ k ih =>
    have h : index < n := by omega
    have e := iter_step st it self index n d f fmt hL hI h h0 hn g hg
    have hL' : Live1D (stepIter st it self index n fmt) self n d f := live_iters st self n d f _ hL
    obtain ⟨s, h1, h2, h3, h4⟩ := ih _ (index + 1) hL' (iterAt_step st it self index n fmt hI) (by omega)
      (by omega) (by omega) hn hg
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

/-- `list(m)` is `m.tolist()` for every 1-D view of a native format, for every stride, with or
without a suboffset (`memory_iter`, `memoryiter_next`, `memory_length`, :3491-3555): each item in
order, then `StopIteration`. Hypotheses: a live view; `NoNull`, a type invariant. -/
def IterYields : Prop :=
  ∀ (st : St) (self : Nat) (n d : Int) (f : List Char) (c : Char),
    Live1D st self n d f → adjustFmt (st.mv self).view = .ok [c] → nativeChar c = true →
    NoNull st self d n →
    ∃ (l : List Item) (s : St), (do let it ← memoryIter self; drain it (n.toNat + 1) : M (List Item)) st =
        (.ok l, s) ∧ memoryviewTolist self st = (.ok (.node (l.map .leaf)), st)

theorem iterAt_new (st : St) (self : Nat) (n : Int) (fmt : List Char) :
    IterAt (newIter st self n fmt) st.iters.length self 0 n fmt :=
  ⟨by simp [newIter], by simp [newIter, List.getD_eq_getElem?_getD]⟩

theorem iterYields_proven : IterYields := by
  intro st self n d f c hL hf hc hn
  obtain ⟨g0, hg0⟩ := native_total st.mem c hc
  have hL' : Live1D (newIter st self n [c]) self n d f := live_iters st self n d f _ hL
  have hg : ItemAt (newIter st self n [c]) self [c] (fun p => g0 (adjustPtr st.mem p (st.mv self).view.suboffsets 0)) :=
    fun p => hg0 _
  obtain ⟨s, h1, -, -, -⟩ := drain_spec st.iters.length self n d f [c] _ n.toNat _ 0 hL'
    (iterAt_new st self n [c]) (by simp) hL.nonneg (Int.le_refl 0) hn hg
  refine ⟨(walk d n.toNat (st.mv self).view.buf).map fun p =>
    g0 (adjustPtr st.mem p (st.mv self).view.suboffsets 0), s, ?_, ?_⟩
  · simp only [M.bind_app, memoryIter_spec st self n d f [c] hL hf, h1]
    simp [show St.mv (newIter st self n [c]) self = st.mv self from rfl]
  · rw [memoryviewTolist_eq st self c [n] [d] g0 hL.live hf hg0 hL.shape hL.strides (by simp) (by rw [hL.ndim]; rfl)]
    simp [treeOf, Function.comp_def]

/-- A value with no Python `__eq__` compares by value, with no effect, except a memoryview
against a `bytes` item, which is `memory_richcompare`. -/
theorem itemEqM_plain (i : Item) (x : Obj) (hx : ∀ r rel, x ≠ .eqLike r rel)
    (hv : ∀ j, x = .view j → ∀ b, i ≠ .bytes b) :
    itemEqM i x = pure (itemEqObj i x) := by
  cases x with
  | eqLike r rel => exact absurd rfl (hx r rel)
  | view j =>
    cases i with
    | bytes b => exact absurd rfl (hv j rfl b)
    | _ => rfl
  | _ => rfl

/-- Only format `c` unpacks to `bytes`. -/
theorem unpackRaw_bytes (m : Mem) (p : Int) (c : Char) (b : List Nat)
    (h : unpackRaw m p [c] = .ok (.bytes b)) : c = 'c' := by
  unfold unpackRaw at h
  simp only [cc, List.getD_cons_zero] at h
  split at h <;> first | rfl | (simp at h; done) | skip

/-- The count `countLoop` reaches. -/
def countItems (x : Obj) (l : List Item) : Int := (l.filter fun i => itemEqObj i x).length

theorem countLoop_spec (it self : Nat) (n d : Int) (f fmt : List Char) (g : Int → Item) (value : Obj)
    (k : Nat) (st : St) (index count : Int) (fuel : Nat) (hL : Live1D st self n d f)
    (hI : IterAt st it self index n fmt) (hk : (n - index).toNat = k) (hi : index ≤ n)
    (h0 : 0 ≤ index) (hn : NoNull st self d n) (hx : ∀ r rel, value ≠ .eqLike r rel)
    (hv : ∀ j, value = .view j → ∀ p b, g p ≠ .bytes b)
    (hg : ItemAt st self fmt g) (hf : k + 1 ≤ fuel) :
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
      have e := iter_step st it self index n d f fmt hL hI h h0 hn g hg
      have hL' : Live1D (stepIter st it self index n fmt) self n d f := live_iters st self n d f _ hL
      have ih' := ih _ (index + 1) (if itemEqObj (g ((st.mv self).view.buf + d * index)) value = true
        then count + 1 else count) fuel hL' (iterAt_step st it self index n fmt hI) (by omega) (by omega)
        (by omega) hn hg (by omega)
      simp only [countLoop, M.bind_app, e, itemEqM_plain _ _ hx (fun j e b => hv j e _ b), M.pure_app]
      rw [ih']
      have hbuf : (St.mv (stepIter st it self index n fmt) self).view.buf = (st.mv self).view.buf := rfl
      rw [hbuf, show (st.mv self).view.buf + d * (index + 1) = (st.mv self).view.buf + d * index + d by
        rw [Int.mul_add, Int.mul_one, Int.add_assoc]]
      simp only [walk, List.map_cons, countItems, List.filter_cons]
      split <;> simp <;> omega

/-- `m.count(x)` is `m.tolist().count(x)` for every 1-D view of a native format and every
`x` with no Python `__eq__`, for every stride, with or without a suboffset. Hypotheses: a live
view; `NoNull`, a type invariant; `x` has no Python `__eq__`, the case `EqFailures` is about; `x`
is not a memoryview compared with the `bytes` items of format `c`, which `ItemEqView` is about. -/
def CountIsList : Prop :=
  ∀ (st : St) (self : Nat) (n d : Int) (f : List Char) (c : Char) (x : Obj),
    Live1D st self n d f → adjustFmt (st.mv self).view = .ok [c] → nativeChar c = true →
    NoNull st self d n → (∀ r rel, x ≠ .eqLike r rel) → (∀ j, x = .view j → c ≠ 'c') →
    ∃ l : List Item, memoryviewTolist self st = (.ok (.node (l.map .leaf)), st) ∧
      (memoryviewCount self x st).1 = .ok (countItems x l)

theorem countIsList_proven : CountIsList := by
  intro st self n d f c x hL hf hc hn hx hview
  obtain ⟨g0, hg0⟩ := native_total st.mem c hc
  have hL' : Live1D (newIter st self n [c]) self n d f := live_iters st self n d f _ hL
  have hg : ItemAt (newIter st self n [c]) self [c] (fun p => g0 (adjustPtr st.mem p (st.mv self).view.suboffsets 0)) :=
    fun p => hg0 _
  have hs := countLoop_spec st.iters.length self n d f [c] _ x n.toNat _ 0 0 (n.toNat + 2) hL'
    (iterAt_new st self n [c]) (by simp) hL.nonneg (Int.le_refl 0) hn hx
    (fun j e p b hb => hview j e (unpackRaw_bytes st.mem _ c b (by rw [hg0]; exact congrArg _ hb))) hg (by omega)
  refine ⟨(walk d n.toNat (st.mv self).view.buf).map fun p =>
    g0 (adjustPtr st.mem p (st.mv self).view.suboffsets 0), ?_, ?_⟩
  · rw [memoryviewTolist_eq st self c [n] [d] g0 hL.live hf hg0 hL.shape hL.strides (by simp) (by rw [hL.ndim]; rfl)]
    simp [treeOf, Function.comp_def]
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
    (hg : ItemAt st self fmt g) (hx : ∀ r rel, value ≠ .eqLike r rel)
    (hv : ∀ j, value = .view j → ∀ p b, g p ≠ .bytes b)
    (fuel : Nat) (i stop : Int) (h0 : 0 ≤ i) (hs : stop ≤ n) (hk : (stop - i).toNat = fuel) :
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
    rw [lookup_in _ _ _ i n d hL.shape hL.strides hin, hpos] at hm
    have hg' : ∀ p, unpackRaw st.mem (adjustPtr st.mem p (st.mv self).view.suboffsets 0) fmt = .ok (g p) := hg
    simp only [hg'] at hm
    rw [indexLoop]
    simp only [hlt, ↓reduceIte, M.bind_app, hm, itemEqM_plain _ _ hx (fun j e b => hv j e _ b), M.pure_app,
      firstFrom]
    split
    · simp [M.pure_app]
    · exact ih (i + 1) (by omega) (by omega)

/-- `m.index(x, start, stop)` on a 1-D view of a native format searches exactly
`range(start', stop')`, where a negative bound counts from the end and both are clipped to
`[0, n]`: the first position whose item equals `x`, or `ValueError`, like `list.index` on
`tolist()` (:2852-2898). Hypotheses: a live view; `start` and `stop` are `Py_ssize_t`, as
`slice_index` leaves them; `x` has no Python `__eq__`, the case `EqFailures` is about; `x` is not
a memoryview compared with the `bytes` items of format `c`, which `ItemEqView` is about. -/
def IndexIsSearch : Prop :=
  ∀ (st : St) (self : Nat) (n d : Int) (f : List Char) (c : Char) (x : Obj) (start stop : Int),
    Live1D st self n d f → adjustFmt (st.mv self).view = .ok [c] → nativeChar c = true →
    (∀ r rel, x ≠ .eqLike r rel) → (∀ j, x = .view j → c ≠ 'c') →
    ∃ g : Int → Item, ItemAt st self [c] g ∧
      let stop' := min (if stop < 0 then max (stop + n) 0 else stop) n
      let start' := min (if start < 0 then max (start + n) 0 else start) stop'
      memoryviewIndex self x start stop st =
        (match firstFrom g (st.mv self).view.buf d x (stop' - start').toNat start' with
         | some j => .ok j
         | none => .error (.valueError "memoryview.index(x): x not found"), st)

theorem indexIsSearch_proven : IndexIsSearch := by
  intro st self n d f c x start stop hL hf hc hx hview
  obtain ⟨g0, hg0⟩ := native_total st.mem c hc
  have hg : ItemAt st self [c] (fun p => g0 (adjustPtr st.mem p (st.mv self).view.suboffsets 0)) :=
    fun p => hg0 _
  refine ⟨_, hg, ?_⟩
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
  exact indexLoop_spec self n d f [c] _ x st hL hf hg hx
    (fun j e p b hb => hview j e (unpackRaw_bytes st.mem _ c b (by rw [hg0]; exact congrArg _ hb)))
    _ _ _ hsa.1 hst.2 rfl

end PyLean.BytesObj.Mem
