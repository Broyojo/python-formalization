import PyLean.DictSet.DictOps

/-!
What the table operations leave alone.

The state of `DM` holds the receiver and, during a merge, the source (`PyDict.peer`). `f` below is
any view of that state. The lookup runs `__eq__`, and nothing else in it writes, so if `__eq__`
keeps `f` then so does the lookup, for every answer `__eq__` gives and whether or not it raises.
With `f = id` that is the lying comparison of `Mutation.lean`; with `f = peer` it says the table
operations cannot touch the source, so that a callback is the only way the source can change while
`dict_dict_merge` runs. On a source that stays put, `mergeLive` is then the list of its items.
-/

namespace PyLean.DictSet

open PyLean

variable {K V : Type} [DecidableEq K]

section Probe
variable {σ τ : Type}

/-- The probe loop keeps `f` if `check` does, at any fuel and offset. -/
theorem doLookup_stable (f : σ → τ) (getIx : σ → Nat → Int) (check : Nat → M σ Int)
    (hc : ∀ ix s, f (check ix s).2 = f s) :
    ∀ (fuel mask i perturb : Nat) (s : σ), f (doLookup getIx check fuel mask i perturb s).2 = f s := by
  intro fuel
  induction fuel with
  | zero => intro mask i perturb s; rfl
  | succ fuel ih =>
    intro mask i perturb s
    simp only [doLookup]
    split
    · split
      · rename_i e s' heq
        have := hc (getIx s i).toNat s
        rw [heq] at this
        exact this
      · rename_i cmp s' heq
        have hs : f s' = f s := by
          have := hc (getIx s i).toNat s
          rw [heq] at this
          exact this
        split
        · exact hs
        · split
          · exact hs
          · exact (ih _ _ _ _).trans hs
    · split
      · rfl
      · exact ih _ _ _ _

end Probe

section Lookup
variable {τ : Type} (P : Proto K (PyDict K V)) (f : PyDict K V → τ)

/-- `compare_generic` writes only through `__eq__`. -/
theorem compareGeneric_stable (hp : ∀ a b s, f (P.eq a b s).2 = f s) (ix : Nat) (key : K)
    (hash : Int) (mp : PyDict K V) : f (compareGeneric P ix key hash mp).2 = f mp := by
  simp only [compareGeneric]
  rcases h : mp.body.entryKH ix with _ | ⟨epKey, epHash⟩
  · simp only [h]
  · simp only [h]
    split
    · rfl
    · split
      · split
        · rename_i e mp' heq
          have := hp epKey key mp
          rw [heq] at this
          exact this
        · rename_i b mp' heq
          have hs : f mp' = f mp := by
            have := hp epKey key mp
            rw [heq] at this
            exact this
          split <;> exact hs
      · rfl

/-- `compare_unicode_generic` writes only through `__eq__`. -/
theorem compareUnicodeGeneric_stable (hp : ∀ a b s, f (P.eq a b s).2 = f s) (ix : Nat) (key : K)
    (hash : Int) (mp : PyDict K V) : f (compareUnicodeGeneric P ix key hash mp).2 = f mp := by
  simp only [compareUnicodeGeneric]
  rcases h : mp.body.entryKH ix with _ | ⟨epKey, epHash⟩
  · simp only [h]
  · simp only [h]
    split
    · split
      · rename_i e mp' heq
        have := hp epKey key mp
        rw [heq] at this
        exact this
      · rename_i b mp' heq
        have hs : f mp' = f mp := by
          have := hp epKey key mp
          rw [heq] at this
          exact this
        split <;> exact hs
    · rfl

/-- All three dispatch branches of `_Py_dict_lookup`. -/
theorem scan_stable (hp : ∀ a b s, f (P.eq a b s).2 = f s) (key : K) (hash : Int)
    (mp : PyDict K V) :
    f (if mp.body.kind != .general then
        if P.isStr key then
          doLookup bodyIx (checkUnicode P key hash) (probeFuel mp.body.log2Size) mp.body.mask
            (toU64 hash &&& mp.body.mask) (toU64 hash) mp
        else unicodekeysLookupGeneric P mp.body.mask (probeFuel mp.body.log2Size) key hash mp
      else dictkeysGenericLookup P mp.body.mask (probeFuel mp.body.log2Size) key hash mp).2 = f mp := by
  split
  · split
    · exact doLookup_stable f _ _ (fun ix s => rfl) _ _ _ _ mp
    · simp only [unicodekeysLookupGeneric]
      exact doLookup_stable f _ _ (fun ix s => compareUnicodeGeneric_stable P f hp ix key hash s)
        _ _ _ _ mp
  · simp only [dictkeysGenericLookup]
    exact doLookup_stable f _ _ (fun ix s => compareGeneric_stable P f hp ix key hash s) _ _ _ _ mp

/-- `_Py_dict_lookup`, restarts included, writes only through `__eq__`. -/
theorem dictLookupAux_stable (hp : ∀ a b s, f (P.eq a b s).2 = f s) (key : K) (hash : Int) :
    ∀ (n : Nat) (mp : PyDict K V), f (dictLookupAux P key hash n mp).2 = f mp := by
  intro n
  induction n with
  | zero => intro mp; rfl
  | succ n ih =>
    intro mp
    simp only [dictLookupAux]
    split
    · rename_i e mp' heq
      have := scan_stable P f hp key hash mp
      rw [heq] at this
      exact this
    · rename_i ix mp' heq
      have hs : f mp' = f mp := by
        have := scan_stable P f hp key hash mp
        rw [heq] at this
        exact this
      split
      · exact (ih _).trans hs
      · exact hs

theorem dictLookup_stable (hp : ∀ a b s, f (P.eq a b s).2 = f s) (key : K) (hash : Int)
    (mp : PyDict K V) : f (dictLookup P key hash mp).2 = f mp :=
  dictLookupAux_stable P f hp key hash restartFuel mp

end Lookup

section Peer
variable (P : Proto K (PyDict K V))

omit [DecidableEq K] in
theorem dictResize_peer (l : Nat) (u : Bool) (mp : PyDict K V) :
    (dictResize l u mp).2.peer = mp.peer := by
  simp only [dictResize]
  split
  · rfl
  · split <;> rfl

omit [DecidableEq K] in
theorem insertCombined_peer (KO : KeyOps K) (hash : Int) (key : K) (value : V) (mp : PyDict K V) :
    (insertCombinedDict KO hash key value mp).2.peer = mp.peer := by
  simp only [insertCombinedDict]
  have h1 : (if mp.body.isUnicode && !KO.isStr key then insertionResize false mp
      else (.ok (), mp)).2.peer = mp.peer := by
    split
    · exact dictResize_peer _ _ _
    · rfl
  split
  · rename_i e s heq
    rw [heq] at h1
    exact h1
  · rename_i a mp1 heq
    rw [heq] at h1
    have h2 : (if mp1.body.usable ≤ 0 then insertionResize true mp1
        else (.ok (), mp1)).2.peer = mp1.peer := by
      split
      · exact dictResize_peer _ _ _
      · rfl
    split
    · rename_i e s heq2
      rw [heq2] at h2
      exact h2.trans h1
    · rename_i a2 mp2 heq2
      rw [heq2] at h2
      have h3 := h2.trans h1
      split
      · split
        · exact h3
        · exact h3
      · exact h3

omit [DecidableEq K] in
theorem storeValue_peer (value : V) (ix : Nat) (mp : PyDict K V) :
    (storeValue value ix mp).2.peer = mp.peer := by
  simp only [storeValue]
  split
  · rfl
  · split <;> rfl

theorem insertAfterLookup_peer (key : K) (hash : Int) (value : V) (ix : Int) (old : Option V)
    (mp : PyDict K V) : (insertAfterLookup P key hash value ix old mp).2.peer = mp.peer := by
  simp only [insertAfterLookup]
  split
  · have h := insertCombined_peer P.toKeyOps hash key value mp
    split
    · rename_i a s heq
      rw [heq] at h
      exact h
    · rename_i e s heq
      rw [heq] at h
      exact h
  · exact storeValue_peer _ _ _

omit [DecidableEq K] in
theorem insertSplitValue_peer (value : V) (ix : Nat) (mp : PyDict K V) :
    (insertSplitValue (K := K) value ix mp).2.peer = mp.peer := by
  simp only [insertSplitValue, M.bind_run, M.get_run]
  cases hb : mp.body with
  | combined k => rfl
  | split k v =>
    simp only []
    cases v.get ix <;> rfl

variable {P}

/-- `insertdict` leaves the source alone unless `__eq__` touches it. -/
theorem insertDict_peer (hp : ∀ a b s, (P.eq a b s).2.peer = s.peer) (key : K) (hash : Int)
    (value : V) (mp : PyDict K V) : (insertDict P key hash value mp).2.peer = mp.peer := by
  have via : (match dictLookup P key hash mp with
      | (.ok (ix, old), mp') => insertAfterLookup P key hash value ix old mp'
      | (.error e, mp') => ((.error e, mp') : Py Unit × PyDict K V)).2.peer = mp.peer := by
    have hl := dictLookup_stable P PyDict.peer hp key hash mp
    split
    · rename_i ix old mp' heq
      rw [heq] at hl
      exact (insertAfterLookup_peer P key hash value ix old mp').trans hl
    · rename_i e mp' heq
      rw [heq] at hl
      exact hl
  simp only [insertDict]
  split
  · split
    · split
      · rfl
      · rename_i ix keys' heq
        split
        · exact insertSplitValue_peer _ _ _
        · exact insertAfterLookup_peer P key hash value ix none _
    · exact via
  · exact via

/-- One step of the merge leaves the source alone unless `__eq__` touches it. -/
theorem mergeStep_peer (hp : ∀ a b s, (P.eq a b s).2.peer = s.peer) (ov : Nat) (key : K)
    (hash : Int) (value : V) (mp : PyDict K V) :
    (mergeStep P ov key hash value mp).2.peer = mp.peer := by
  simp only [mergeStep]
  split
  · exact insertDict_peer hp key hash value mp
  · have hl := dictLookup_stable P PyDict.peer hp key hash mp
    simp only [dictContainsKnownHash, M.bind_run]
    rcases hk : dictLookup P key hash mp with ⟨a, s⟩
    rw [hk] at hl
    cases a with
    | error e => exact hl
    | ok r =>
      simp only [M.pure_run]
      split
      · exact (insertDict_peer hp key hash value s).trans hl
      · split
        · exact hl
        · exact hl

end Peer

section Source

omit [DecidableEq K] in
theorem scanFrom_bounds : ∀ (l : List (Option (Ent K V))) (i j : Nat) (e : Ent K V),
    scanFrom l i = some (j, e) → i ≤ j ∧ j < i + l.length := by
  intro l
  induction l with
  | nil => intro i j e h; simp [scanFrom] at h
  | cons x t ih =>
    intro i j e h
    cases x with
    | none =>
      have := ih (i + 1) j e h
      simp only [List.length_cons]
      omega
    | some y =>
      simp only [scanFrom, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      simp only [List.length_cons]
      omega

omit [DecidableEq K] in
/-- `_PyDict_Next` on a combined table moves `pos` forward, and past a slot inside the table. -/
theorem dictNext_step (other : PyDict K V) (ok : Keys K V) (hb : other.body = .combined ok) (i : Nat)
    (pos' : Int) (key : K) (value : V) (hash : Int)
    (h : dictNext other (i : Int) = some (pos', key, value, hash)) :
    ∃ j : Nat, pos' = ((j + 1 : Nat) : Int) ∧ i ≤ j ∧ j < ok.nentries := by
  simp only [dictNext, hb] at h
  split at h
  · simp at h
  · rename_i hi
    have hlt : i < ok.nentries := by omega
    simp only [Int.toNat_natCast] at h
    split at h
    · rename_i j e hs
      have hb := scanFrom_bounds _ _ _ _ hs
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      refine ⟨j, ?_, hb.1, ?_⟩
      · rw [← h.1]; omega
      · have hlen : (ok.entries.drop i).length = ok.nentries - i := by
          simp [Keys.nentries]
        omega
    · simp at h

omit [DecidableEq K] in
theorem dictNext_toPeer (d : PyDict K V) (pos : Int) :
    dictNext d.toPeer.toDict pos = dictNext d pos := rfl

omit [DecidableEq K] in
/-- Enough fuel is enough: the list of a combined table does not depend on how much. -/
theorem dictNextAll_fuel (other : PyDict K V) (ok : Keys K V) (hb : other.body = .combined ok) :
    ∀ (f g i : Nat), i ≤ ok.nentries → ok.nentries < i + f → ok.nentries < i + g →
      dictNextAll other f (i : Int) = dictNextAll other g (i : Int) := by
  intro f
  induction f with
  | zero => intro g i h1 h2; omega
  | succ f ih =>
    intro g i h1 _ h3
    cases g with
    | zero => omega
    | succ g =>
      simp only [dictNextAll]
      cases hn : dictNext other (i : Int) with
      | none => rfl
      | some t =>
        obtain ⟨pos', k, v, h⟩ := t
        obtain ⟨j, rfl, h4, h5⟩ := dictNext_step other ok hb i pos' k v h hn
        simp only [List.cons.injEq, true_and]
        exact ih g (j + 1) (by omega) (by omega) (by omega)

variable {P : Proto K (PyDict K V)}

/-- On a source that no callback touches, `mergeLive` is the list of the source's items, and the
test at @3.14.7:3981 never fires. `__eq__` is otherwise free: it may lie, raise, or change the receiver. -/
theorem mergeLive_quiet (hp : ∀ a b s, (P.eq a b s).2.peer = s.peer) (ov : Nat)
    (other : PyDict K V) (ok : Keys K V) (hb : other.body = .combined ok) :
    ∀ (fuel i : Nat) (d : PyDict K V), d.peer = some other.toPeer → i ≤ ok.nentries →
      ok.nentries < i + fuel →
      mergeLive P ov other.used fuel (i : Int) d =
        mergeLoop P ov (dictNextAll other fuel (i : Int)) d := by
  intro fuel
  induction fuel with
  | zero => intro i d _ h1 h2; omega
  | succ fuel ih =>
    intro i d hd h1 h2
    simp only [mergeLive, hd, dictNext_toPeer, dictNextAll]
    cases hn : dictNext other (i : Int) with
    | none => rfl
    | some t =>
      obtain ⟨pos', k, v, h⟩ := t
      obtain ⟨j, rfl, h4, h5⟩ := dictNext_step other ok hb i pos' k v h hn
      simp only [mergeLoop, M.bind_run]
      have hpeer := mergeStep_peer hp ov k h v d
      rcases hs : mergeStep P ov k h v d with ⟨a, s⟩
      rw [hs] at hpeer
      cases a with
      | error e => rfl
      | ok u =>
        have hsp : s.peer = some other.toPeer := hpeer.trans hd
        simp only [hsp, PyDict.toPeer, bne_self_eq_false, Bool.false_eq_true, if_false]
        exact ih (j + 1) s hsp (by omega) (by omega)

end Source

end PyLean.DictSet
