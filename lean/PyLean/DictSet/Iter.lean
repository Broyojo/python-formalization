import PyLean.DictSet.Props4
import PyLean.DictSet.Split
import PyLean.DictSet.Findings

/-!
The six dict iterators over an unchanged dict, both table forms, in both directions, and what each of
them does when the dict did change.

`ma_used` is not assumed to fit `Py_ssize_t`: the table invariants bound it, because neither table
form can have more than `2**63` slots.
-/

namespace PyLean.DictSet

open PyLean

section
variable {K V : Type}

/-- The backwards scan stops at the last live entry at or below `i`. -/
theorem scanDown_spec (es : List (Option (Ent K V))) :
    ∀ i, (scanDown es i = none ∧ (es.take (i + 1)).filterMap id = []) ∨
      ∃ j e, j ≤ i ∧ scanDown es i = some (j, e) ∧
        (es.take (i + 1)).filterMap id = (es.take j).filterMap id ++ [e] := by
  intro i
  induction i with
  | zero =>
    cases es with
    | nil => left; simp [scanDown]
    | cons a t =>
      cases a with
      | none => left; simp [scanDown]
      | some e => right; exact ⟨0, e, Nat.le_refl _, by simp [scanDown], by simp⟩
  | succ i ih =>
    rw [List.take_succ (i := i + 1)]
    cases h : es[i + 1]? with
    | none =>
      have hs : scanDown es (i + 1) = scanDown es i := by simp [scanDown, h]
      rw [hs]
      rcases ih with ⟨h1, h2⟩ | ⟨j, e, hj, h1, h2⟩
      · left; simp [h1, h2]
      · right; exact ⟨j, e, by omega, h1, by simp [h2]⟩
    | some o =>
      cases o with
      | none =>
        have hs : scanDown es (i + 1) = scanDown es i := by simp [scanDown, h]
        rw [hs]
        rcases ih with ⟨h1, h2⟩ | ⟨j, e, hj, h1, h2⟩
        · left; simp [h1, h2]
        · right; exact ⟨j, e, by omega, h1, by simp [h2]⟩
      | some e =>
        have hs : scanDown es (i + 1) = some (i + 1, e) := by simp [scanDown, h]
        right
        refine ⟨i + 1, e, by omega, hs, ?_⟩
        simp

/-- A reverse iterator over an unchanged combined table walks `dk_entries` back from `pos`, at any
`n - 1`. -/
theorem reverse_drain (d : PyDict K V) (k : Keys K V) (hb : d.body = .combined k) :
    ∀ (fuel n : Nat) (di : DictIter) (acc : List (K × V)),
      di.alive = true → di.rev = true → di.used = d.used → di.pos = (n : Int) - 1 →
      di.len = (((k.entries.take n).filterMap id).length : Int) → n ≤ k.nentries → n < fuel →
      (dictiterDrain d fuel di acc).1 =
        .ok (acc.reverse ++
          (((k.entries.take n).filterMap id).reverse.map fun e => (e.key, e.value))) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _ _ _ _ h; omega
  | succ fuel ih =>
    intro n di acc ha hr hu hp hl hn hf
    cases n with
    | zero =>
      have hx : dictiterNext d di = (.ok none, { di with alive := false }) := by
        simp [dictiterNext, hr, dictiterNextReverse, ha, hu, hp]
      simp [dictiterDrain, hx]
    | succ m =>
      have hpos : di.pos = (m : Int) := by omega
      have hlt : m < k.nentries := by omega
      rcases scanDown_spec k.entries m with ⟨h1, h2⟩ | ⟨j, e, hj, h1, h2⟩
      · have hx : dictiterNext d di = (.ok none, { di with alive := false }) := by
          simp [dictiterNext, hr, dictiterNextReverse, ha, hu, hpos, hb, h1, Nat.not_le.mpr hlt]
        simp [dictiterDrain, hx, h2]
      · have hlen : di.len = (((k.entries.take j).filterMap id).length : Int) + 1 := by
          rw [hl, h2]
          simp
        have hl0 : (di.len == 0) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]
          omega
        have hx : dictiterNext d di = (.ok (some (e.key, e.value)),
            { di with pos := (j : Int) - 1, len := di.len - 1 }) := by
          simp [dictiterNext, hr, dictiterNextReverse, ha, hu, hpos, hb, h1, Nat.not_le.mpr hlt, hl0]
        simp only [dictiterDrain, hx]
        rw [ih j { di with pos := (j : Int) - 1, len := di.len - 1 } ((e.key, e.value) :: acc)
          ha hr hu rfl (by simp only [hlen]; omega) (by omega) (by omega)]
        rw [h2]
        simp

end

section
variable {K V : Type} [DecidableEq K] {hf : K → Int} {eqv : K → K → Bool} {isStr : K → Bool}

omit [DecidableEq K] in
/-- A forward iterator over a split table walks the order array. -/
theorem forward_drain_split (d : PyDict K V) (k : Keys K Unit) (v : Values V)
    (hb : d.body = .split k v) (w : SplitWF hf eqv isStr k v d.used) :
    ∀ (fuel i : Nat) (di : DictIter) (acc : List (K × V)),
      di.alive = true → di.rev = false → di.used = d.used → di.pos = (i : Int) →
      di.len = (d.used : Int) - i → i ≤ d.used → d.used < i + fuel →
      (dictiterDrain d fuel di acc).1 =
        .ok (acc.reverse ++ ((v.order.drop i).filterMap (slot k v)).map fun e => (e.key, e.value)) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _ _ _ _ h; omega
  | succ fuel ih =>
    intro i di acc ha hr hu hp hl hi hf'
    by_cases hc : i < d.used
    · have hlen : i < v.order.length := by rw [← w.used]; exact hc
      have hmem : v.order[i] ∈ v.order := List.getElem_mem hlen
      obtain ⟨e0, x, h1, h2, h3⟩ := slot_of_order w hmem
      have hidx : v.indexFromOrder i = v.order[i] := by
        simp [Values.indexFromOrder, List.getD, hlen]
      have hl0 : (di.len == 0) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        rw [hl]
        omega
      have hx : dictiterNext d di = (.ok (some (e0.key, x)),
          { di with pos := ((i : Nat) : Int) + 1, len := di.len - 1 }) := by
        simp only [dictiterNext, hr, dictiterNextForward]
        simp [ha, hu, hb, hp, hc, Nat.not_le.mpr hc, hidx, h1, h2, hl0]
      have hdrop : v.order.drop i = v.order[i] :: v.order.drop (i + 1) :=
        List.drop_eq_getElem_cons hlen
      simp only [dictiterDrain, hx]
      rw [ih (i + 1) { di with pos := ((i : Nat) : Int) + 1, len := di.len - 1 } ((e0.key, x) :: acc)
        ha hr hu (by simp) (by simp only [hl]; omega) (by omega) (by omega)]
      rw [hdrop]
      simp only [List.filterMap_cons, h3]
      simp
    · have hei : i = d.used := by omega
      have hd : v.order.drop i = [] := List.drop_eq_nil_of_le (by rw [← w.used]; omega)
      have hx : dictiterNext d di = (.ok none, { di with alive := false }) := by
        simp only [dictiterNext, hr, dictiterNextForward]
        simp [ha, hu, hb, hp, hei]
      simp [dictiterDrain, hx, hd]

omit [DecidableEq K] in
/-- A reverse iterator over a split table walks the order array back from `n - 1`. -/
theorem reverse_drain_split (d : PyDict K V) (k : Keys K Unit) (v : Values V)
    (hb : d.body = .split k v) (w : SplitWF hf eqv isStr k v d.used) :
    ∀ (fuel n : Nat) (di : DictIter) (acc : List (K × V)),
      di.alive = true → di.rev = true → di.used = d.used → di.pos = (n : Int) - 1 →
      di.len = (n : Int) → n ≤ d.used → n < fuel →
      (dictiterDrain d fuel di acc).1 =
        .ok (acc.reverse ++
          (((v.order.take n).filterMap (slot k v)).reverse.map fun e => (e.key, e.value))) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _ _ _ _ h; omega
  | succ fuel ih =>
    intro n di acc ha hr hu hp hl hn hf'
    cases n with
    | zero =>
      have hx : dictiterNext d di = (.ok none, { di with alive := false }) := by
        simp [dictiterNext, hr, dictiterNextReverse, ha, hu, hp]
      simp [dictiterDrain, hx]
    | succ m =>
      have hpos : di.pos = (m : Int) := by omega
      have hlen : m < v.order.length := by rw [← w.used]; omega
      have hmem : v.order[m] ∈ v.order := List.getElem_mem hlen
      obtain ⟨e0, x, h1, h2, h3⟩ := slot_of_order w hmem
      have hidx : v.indexFromOrder m = v.order[m] := by
        simp [Values.indexFromOrder, List.getD, hlen]
      have hl0 : (di.len == 0) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        omega
      have hx : dictiterNext d di = (.ok (some (e0.key, x)),
          { di with pos := (m : Int) - 1, len := di.len - 1 }) := by
        simp only [dictiterNext, hr, dictiterNextReverse]
        simp [ha, hu, hb, hpos, hidx, h1, h2, hl0]
      simp only [dictiterDrain, hx]
      rw [ih m { di with pos := (m : Int) - 1, len := di.len - 1 } ((e0.key, x) :: acc)
        ha hr hu rfl (by simp only [hl]; omega) (by omega) (by omega)]
      have ht : (v.order.take (m + 1)).filterMap (slot k v) =
          (v.order.take m).filterMap (slot k v) ++ [⟨e0.key, e0.hash, x⟩] := by
        rw [List.take_succ (i := m), List.getElem?_eq_getElem hlen]
        simp only [Option.toList, List.filterMap_append, List.filterMap_cons, h3,
          List.filterMap_nil]
      rw [ht]
      simp

omit [DecidableEq K] in
theorem used_lt_of_frac {used log2 : Nat} (h : log2 < 64)
    (h1 : used ≤ usableFraction (2 ^ log2)) : used < 2 ^ 63 := by
  have h2 : 2 ^ log2 ≤ 2 ^ 63 := Nat.pow_le_pow_right (by omega) (by omega)
  simp only [usableFraction, Nat.shiftLeft_eq, Nat.pow_one] at h1
  omega

/-- `ma_used` fits `Py_ssize_t`, on a combined table. -/
theorem dictInv_used_lt (d : PyDict K V) (hd : DictInv hf eqv isStr d) : d.used < 2 ^ 63 := by
  obtain ⟨k, _, w, hu⟩ := hd.wf
  have h1 := liveEntries_length_le k
  have h2 := w.nent
  have h3 := w.usableNN
  have : d.used ≤ usableFraction k.size := by omega
  exact used_lt_of_frac w.small this

omit [DecidableEq K] in
/-- `ma_used` fits `Py_ssize_t`, on a split table. -/
theorem split_used_lt (used : Nat) (k : Keys K Unit) (v : Values V)
    (w : SplitWF hf eqv isStr k v used) : used < 2 ^ 63 := by
  have h0 : used ≤ k.nentries := by
    rw [w.used]
    exact nodup_length_le _ _ w.nodup (fun x hx => ((w.order x).mp hx).1)
  have h2 := w.nent
  have h3 := w.core.usableNN
  have : used ≤ usableFraction k.size := by omega
  exact used_lt_of_frac w.small this

omit [DecidableEq K] in
theorem hint_new (d : PyDict K V) (hmax : d.used < 2 ^ 63) (kind : IterKind) (rev : Bool) :
    dictiterLengthHint d (dictiterNew d kind rev) = .ok d.used := by
  have hint : toU64 (d.used : Int) = d.used := by
    simp only [toU64]
    have : (d.used : Int) % (2 ^ 64 : Int) = d.used := Int.emod_eq_of_lt (by omega) (by omega)
    rw [this]
    simp
  simp [dictiterLengthHint, dictiterLen, dictiterNew, hint, Nat.not_le.mpr hmax]

/-- `list(it)` on a new iterator over a dict in either form. -/
theorem iter_toList (d : PyDict K V) (hd : DictInv hf eqv isStr d ∨ SplitInv hf eqv isStr d)
    (kind : IterKind) :
    (dictiterToList d (dictiterNew d kind false)).1 = .ok (dictAssoc d) ∧
    (dictiterToList d (dictiterNew d kind true)).1 = .ok (dictAssoc d).reverse := by
  rcases hd with hd | ⟨k, v, hb, w⟩
  · have hmax := dictInv_used_lt d hd
    obtain ⟨k, hb, _, hu⟩ := hd.wf
    have hdrop : (k.entries.drop 0) = k.entries := rfl
    have hle : (liveEntries k).length ≤ d.body.nentries := by
      have := liveEntries_length_le k
      simpa [Body.nentries, hb] using this
    have hn : d.body.nentries = k.nentries := by simp [Body.nentries, hb]
    constructor
    · simp only [dictiterToList, hint_new d hmax]
      have := forward_drain d k hb (d.body.nentries + d.used + 2) (dictiterNew d kind false) 0 []
        rfl (by simp [dictiterNew]) (by simp [dictiterNew]) (by simp [dictiterNew])
        (by simp [dictiterNew, hu, liveEntries])
        (by
          have h1 : (k.entries.filterMap id).length ≤ d.body.nentries := hle
          simp only [hdrop]
          omega)
      simpa [dictAssoc, hb, Keys.items, liveEntries] using this
    · simp only [dictiterToList, hint_new d hmax]
      have := reverse_drain d k hb (d.body.nentries + d.used + 2) k.nentries
        (dictiterNew d kind true) []
        rfl (by simp [dictiterNew]) (by simp [dictiterNew])
        (by simp [dictiterNew, Body.isSplit, Body.nentries, hb, Keys.nentries])
        (by simp [dictiterNew, hu, liveEntries, Keys.nentries])
        (Nat.le_refl _) (by omega)
      have ht : k.entries.take k.nentries = k.entries := List.take_of_length_le (Nat.le_refl _)
      rw [ht] at this
      simpa [dictAssoc, hb, Keys.items, liveEntries, List.map_reverse] using this
  · have hmax := split_used_lt d.used k v w
    have hn : d.body.nentries = k.nentries := by simp [Body.nentries, hb]
    have ht : v.order.take d.used = v.order := by
      rw [w.used]
      simp
    have hl : splitLive k v d.used = v.order.filterMap (slot k v) := by
      rw [splitLive_eq, ht]
    constructor
    · simp only [dictiterToList, hint_new d hmax]
      have := forward_drain_split d k v hb w (d.body.nentries + d.used + 2) 0
        (dictiterNew d kind false) []
        rfl (by simp [dictiterNew]) (by simp [dictiterNew]) (by simp [dictiterNew])
        (by simp [dictiterNew]) (by omega) (by omega)
      simpa [dictAssoc, hb, hl] using this
    · simp only [dictiterToList, hint_new d hmax]
      have := reverse_drain_split d k v hb w (d.body.nentries + d.used + 2) d.used
        (dictiterNew d kind true) []
        rfl (by simp [dictiterNew]) (by simp [dictiterNew])
        (by simp [dictiterNew, Body.isSplit, hb]) (by simp [dictiterNew]) (Nat.le_refl _) (by omega)
      rw [ht] at this
      simpa [dictAssoc, hb, hl, List.map_reverse] using this

end

/-- `list(it)` for each of the six iterators on a well-formed dict of either form, after
`dictiter_new`: forward, the list in order; backward, the list reversed; and each flavour hands back
what it says. `ma_used` needs no bound here: the table invariants give it. -/
def DictIterOrder : Prop :=
  ∀ (K V : Type) [DecidableEq K] (hf : K → Int) (eqv : K → K → Bool) (isStr : K → Bool)
    (d : PyDict K V), (DictInv hf eqv isStr d ∨ SplitInv hf eqv isStr d) → ∀ kind : IterKind,
    (dictiterToList d (dictiterNew d kind false)).1 = .ok (dictAssoc d) ∧
    (dictiterToList d (dictiterNew d kind true)).1 = .ok (dictAssoc d).reverse ∧
    (dictiterNew d kind false).kind = kind ∧ (dictiterNew d kind true).kind = kind ∧
    (∀ (p : K × V), IterKind.key.result p = .key p.1 ∧ IterKind.value.result p = .value p.2 ∧
      IterKind.item.result p = .item p.1 p.2)
theorem dictIterOrder_proven : DictIterOrder := by
  intro K V _ hf eqv isStr d hd kind
  obtain ⟨h1, h2⟩ := iter_toList d hd kind
  exact ⟨h1, h2, rfl, rfl, fun _ => ⟨rfl, rfl, rfl⟩⟩

/-- The three views give the iterator of their kind, in either direction. -/
def ViewIterOrder : Prop :=
  ∀ (K V : Type) [DecidableEq K] (hf : K → Int) (eqv : K → K → Bool) (isStr : K → Bool)
    (d : PyDict K V), (DictInv hf eqv isStr d ∨ SplitInv hf eqv isStr d) → ∀ (kind : ViewKind),
    (dictiterToList d (dictviewIter (viewNew kind d) false)).1 = .ok (dictAssoc d) ∧
    (dictiterToList d (dictviewIter (viewNew kind d) true)).1 = .ok (dictAssoc d).reverse ∧
    (∀ rev, (dictviewIter (viewNew .keys d) rev).kind = .key) ∧
    (∀ rev, (dictviewIter (viewNew .values d) rev).kind = .value) ∧
    (∀ rev, (dictviewIter (viewNew .items d) rev).kind = .item)
theorem viewIterOrder_proven : ViewIterOrder := by
  intro K V _ hf eqv isStr d hd kind
  have h : ∀ k, (dictiterToList d (dictiterNew d k false)).1 = .ok (dictAssoc d) ∧
      (dictiterToList d (dictiterNew d k true)).1 = .ok (dictAssoc d).reverse :=
    iter_toList d hd
  refine ⟨?_, ?_, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩ <;> cases kind
  · exact (h .key).1
  · exact (h .item).1
  · exact (h .value).1
  · exact (h .key).2
  · exact (h .item).2
  · exact (h .value).2

/-- What an iterator does when it cannot go on, for any iterator and any dict. An exhausted one stays
exhausted; a changed size raises and stays raised, because `di_used` is set to `-1` and `ma_used` is
never that; and both directions raise when they find an entry past the count they started with,
which is how a change that kept the size shows, and hand the entry back otherwise. -/
def DictIterFailure : Prop :=
  ∀ (K V : Type) (d : PyDict K V) (di : DictIter),
    (di.alive = false → dictiterNext d di = (.ok none, di)) ∧
    (di.alive = true → di.used ≠ d.used →
      let e := runtimeError "dictionary changed size during iteration"
      let di' := { di with used := -1 }
      dictiterNext d di = (.error e, di') ∧ dictiterNext d di' = (.error e, di')) ∧
    (di.alive = true → di.used = d.used → di.rev = false → di.len = 0 →
      ∀ (k : Keys K V) (j : Nat) (e : Ent K V), d.body = .combined k →
        scanFrom (k.entries.drop di.pos.toNat) di.pos.toNat = some (j, e) →
        dictiterNext d di =
          (.error (runtimeError "dictionary keys changed during iteration"),
            { di with alive := false })) ∧
    (di.alive = true → di.used = d.used → di.rev = false → di.len = 0 →
      ∀ (k : Keys K Unit) (v : Values V) (e : Ent K Unit) (x : V), d.body = .split k v →
        di.pos < d.used → k.entry (v.indexFromOrder di.pos.toNat) = some e →
        v.get (v.indexFromOrder di.pos.toNat) = some x →
        dictiterNext d di =
          (.error (runtimeError "dictionary keys changed during iteration"),
            { di with alive := false })) ∧
    (di.alive = true → di.used = d.used → di.rev = true →
      ∀ (k : Keys K V) (j : Nat) (e : Ent K V), d.body = .combined k → 0 ≤ di.pos →
        di.pos < k.nentries → scanDown k.entries di.pos.toNat = some (j, e) →
        (di.len = 0 → dictiterNext d di =
          (.error (runtimeError "dictionary keys changed during iteration"),
            { di with alive := false })) ∧
        (di.len ≠ 0 → dictiterNext d di =
          (.ok (some (e.key, e.value)), { di with pos := (j : Int) - 1, len := di.len - 1 })))
theorem dictIterFailure_proven : DictIterFailure := by
  intro K V d di
  refine ⟨fun h => ?_, fun h hn => ?_, fun h hu hr hl k j e hb hs => ?_,
    fun h hu hr hl k v e x hb hlt h1 h2 => ?_, fun h hu hr k j e hb h0 hlt hs => ?_⟩
  · cases hr : di.rev <;> simp [dictiterNext, dictiterNextForward, dictiterNextReverse, h, hr]
  · have h1 : (di.used != (d.used : Int)) = true := by simpa using hn
    have h2 : ((-1 : Int) != (d.used : Int)) = true := by
      simp only [bne_iff_ne, ne_eq]
      omega
    cases hr : di.rev <;>
      simp [dictiterNext, dictiterNextForward, dictiterNextReverse, h, hr, h1, h2] <;> omega
  · simp [dictiterNext, dictiterNextForward, h, hr, hu, hl, hb, hs]
  · have h3 : ¬ di.pos ≥ (d.used : Int) := by omega
    simp [dictiterNext, dictiterNextForward, h, hr, hu, hl, hb, h1, h2, h3]
  · have h1 : ¬ di.pos < 0 := by omega
    have h2 : ¬ di.pos ≥ (k.nentries : Int) := by omega
    constructor
    · intro hl
      simp [dictiterNext, dictiterNextReverse, h, hr, hu, hb, hs, h1, h2, hl]
    · intro hl
      simp [dictiterNext, dictiterNextReverse, h, hr, hu, hb, hs, h1, h2, hl]

section Hint
variable {K V : Type} [DecidableEq K]

/-- What a reverse iterator keeps through any program. -/
def RevOK (di : DictIter) : Prop := di.rev = true ∧ 0 ≤ di.len ∧ di.len < 2 ^ 63

omit [DecidableEq K] in
theorem revOK_next (d : PyDict K V) (di : DictIter) (h : RevOK di) : RevOK (dictiterNext d di).2 := by
  obtain ⟨hr, h0, h1⟩ := h
  simp only [RevOK, dictiterNext, hr, if_true, dictiterNextReverse]
  repeat' split
  all_goals first
    | exact ⟨hr, h0, h1⟩
    | exact ⟨rfl, h0, h1⟩
    | (refine ⟨rfl, ?_, ?_⟩ <;> simp_all <;> omega)

theorem revRun_inv {P : Proto K (PyDict K V)} {hf : K → Int} {eqv : K → K → Bool}
    (H : Honest P hf eqv) : ∀ (steps : List (RevStep K V)) (d : PyDict K V) (di : DictIter),
      DictInv hf eqv P.isStr d → RevOK di → RevOK (revRun P steps d di).2 := by
  intro steps
  induction steps with
  | nil => intro d di _ h; exact h
  | cons s rest ih =>
    intro d di hd h
    cases s with
    | set k v =>
      simp only [revRun]
      rcases setItemRefines_proven K V P hf eqv H d hd k v with ⟨_, h1⟩ | ⟨d', h1, h2, _⟩
      · rw [h1]
        exact ih d di hd h
      · rw [h1]
        exact ih d' di h2 h
    | del k =>
      simp only [revRun]
      rcases dictDelItem_spec H d hd k with ⟨_, h1⟩ | ⟨_, d', h1, h2, _⟩
      · rw [h1]
        exact ih d di hd h
      · rw [h1]
        exact ih d' di h2 h
    | start =>
      simp only [revRun]
      refine ih d _ hd ⟨rfl, ?_, ?_⟩
      · simp [dictiterNew]
      · have := dictInv_used_lt d hd
        simp only [dictiterNew]
        omega
    | next =>
      simp only [revRun]
      exact ih d _ hd (revOK_next d di h)

/-- `__length_hint__` of a reverse dict iterator is a valid `Py_ssize_t`, under any program: since
gh-158254 `len` is decremented only after the test at :6273. -/
theorem revIterLenNonneg_proven : RevIterLenNonneg := by
  intro K V _ P hf eqv H steps r
  have h0 : DictInv hf eqv P.isStr ({ ident := 1 } : PyDict K V) := dictInv_new hf eqv P.isStr 1 1
  have hi : RevOK (dictiterNew ({ ident := 1 } : PyDict K V) .key true) := by
    refine ⟨rfl, ?_, ?_⟩ <;> simp [dictiterNew]
  have hok : RevOK r.2 := revRun_inv H steps _ _ h0 hi
  obtain ⟨_, h1, h2⟩ := hok
  have hint : toU64 r.2.len = r.2.len.toNat := by
    simp only [toU64]
    have : r.2.len % (2 ^ 64 : Int) = r.2.len := Int.emod_eq_of_lt h1 (by omega)
    rw [this]
  simp only [dictiterLen]
  split
  · rw [hint]
    omega
  · simp

end Hint

end PyLean.DictSet
