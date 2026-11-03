import PyLean.TextLibs.PlistReadAll

/-! What `_flatten` builds: every object reachable from the value gets a reference number, the
tables map each object back to it, and the elements of every container written are numbered. -/

namespace PyLean.TextLibs.Plist

open PyLean PyLean.TextLibs

def isScalar (H : WHeap) (c : Nat) : Bool := (scalarType (H.getD c .none)).isSome

/-- `_getrefnum` without the frame: the reference number of an object. -/
def lookupW (H : WHeap) (st : WState) (c : Nat) : Option Nat :=
  if isScalar H c then tableLookup H st c else idLookup H st c

/-- The tables agree with the object list. -/
def WInv (H : WHeap) (st : WState) : Prop :=
  (∀ q ∈ st.objtable, st.objlist[q.2]? = some q.1 ∧ isScalar H q.1 = true) ∧
  (∀ q ∈ st.objidtable, ∃ c, st.objlist[q.2]? = some c ∧ objId H c = q.1 ∧ isScalar H c = false) ∧
  (∀ i c, st.objlist[i]? = some c → lookupW H st c = some i)

def WExt (st st' : WState) : Prop :=
  (∃ l, st'.objlist = st.objlist ++ l) ∧ (∃ l, st'.objtable = st.objtable ++ l) ∧
    (∃ l, st'.objidtable = st.objidtable ++ l)

theorem wext_refl (st : WState) : WExt st st := ⟨⟨[], by simp⟩, ⟨[], by simp⟩, ⟨[], by simp⟩⟩

theorem wext_trans {a b c : WState} (h1 : WExt a b) (h2 : WExt b c) : WExt a c := by
  obtain ⟨⟨l1, e1⟩, ⟨l2, e2⟩, ⟨l3, e3⟩⟩ := h1
  obtain ⟨⟨m1, f1⟩, ⟨m2, f2⟩, ⟨m3, f3⟩⟩ := h2
  exact ⟨⟨l1 ++ m1, by rw [f1, e1, List.append_assoc]⟩, ⟨l2 ++ m2, by rw [f2, e2, List.append_assoc]⟩,
    ⟨l3 ++ m3, by rw [f3, e3, List.append_assoc]⟩⟩

theorem find?_append_some {α : Type} (p : α → Bool) (l m : List α) (a : α) (h : l.find? p = some a) :
    (l ++ m).find? p = some a := by
  rw [List.find?_append, h]; rfl

theorem lookup_ext {H : WHeap} {st st' : WState} (h : WExt st st') (c i : Nat)
    (hl : lookupW H st c = some i) : lookupW H st' c = some i := by
  obtain ⟨_, ⟨l2, e2⟩, ⟨l3, e3⟩⟩ := h
  unfold lookupW tableLookup idLookup at *
  split at hl
  · rw [if_pos (by assumption), e2]
    revert hl
    cases hf : st.objtable.find? (fun x => scalarMatch H x.1 c) with
    | none => simp
    | some q => intro hq; rw [find?_append_some _ _ _ _ hf]; exact hq
  · rw [if_neg (by assumption), e3]
    revert hl
    cases hf : st.objidtable.find? (fun x => x.1 == objId H c) with
    | none => simp
    | some q => intro hq; rw [find?_append_some _ _ _ _ hf]; exact hq

theorem getElem?_append_left' {α : Type} {l : List α} (m : List α) {i : Nat} {a : α}
    (h : l[i]? = some a) : (l ++ m)[i]? = some a := by
  rw [List.getElem?_append_left (lt_of_getElem?_some' h)]; exact h
where
  lt_of_getElem?_some' {l : List α} {i : Nat} {a : α} (h : l[i]? = some a) : i < l.length := by
    rcases Nat.lt_or_ge i l.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none_iff.mpr h'] at h; cases h

/-- The value `lookupW` returns names an object of the list that is the same scalar or the same
object. -/
theorem lookup_sound {H : WHeap} {st : WState} (hI : WInv H st) {c i : Nat}
    (h : lookupW H st c = some i) :
    ∃ c', st.objlist[i]? = some c' ∧
      ((isScalar H c = true ∧ scalarMatch H c' c = true) ∨
        (isScalar H c = false ∧ objId H c' = objId H c ∧ isScalar H c' = false)) := by
  obtain ⟨h1, h2, _⟩ := hI
  unfold lookupW tableLookup idLookup at h
  split at h
  · rename_i hs
    cases hf : st.objtable.find? (fun x => scalarMatch H x.1 c) with
    | none => rw [hf] at h; cases h
    | some q =>
      rw [hf] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      have hm := List.mem_of_find?_eq_some hf
      have hp := List.find?_some hf
      obtain ⟨hq1, _⟩ := h1 q hm
      exact ⟨q.1, hq1, Or.inl ⟨hs, hp⟩⟩
  · rename_i hs
    cases hf : st.objidtable.find? (fun x => x.1 == objId H c) with
    | none => rw [hf] at h; cases h
    | some q =>
      rw [hf] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      have hm := List.mem_of_find?_eq_some hf
      have hp := List.find?_some hf
      obtain ⟨c', hc1, hc2, hc3⟩ := h2 q hm
      simp only [beq_iff_eq] at hp
      exact ⟨c', hc1, Or.inr ⟨by simpa using hs, hc2.trans hp, hc3⟩⟩


/-- The elements of a container written by `_write_object` all have reference numbers. -/
def ChildrenDone (H : WHeap) (cfg : WCfg) (st : WState) (c : Nat) : Prop :=
  match H.getD c .none with
  | .list xs | .tuple xs => ∀ x ∈ xs, (lookupW H st x).isSome
  | .dict items | .fdict items => ∀ kept, writtenItems H cfg items = .ok kept →
      ∀ q ∈ kept, (lookupW H st q.1).isSome ∧ (lookupW H st q.2).isSome
  | _ => True

theorem isSome_ext {H : WHeap} {st st' : WState} (h : WExt st st') (c : Nat)
    (hl : (lookupW H st c).isSome) : (lookupW H st' c).isSome := by
  cases hc : lookupW H st c with
  | none => rw [hc] at hl; cases hl
  | some i => rw [lookup_ext h c i hc]; rfl

theorem childrenDone_ext {H : WHeap} {cfg : WCfg} {st st' : WState} (h : WExt st st') (c : Nat)
    (hd : ChildrenDone H cfg st c) : ChildrenDone H cfg st' c := by
  unfold ChildrenDone at *
  cases hc : H.getD c .none <;> rw [hc] at hd
  all_goals first
    | trivial
    | (intro x hx; exact isSome_ext h x (hd x hx))
    | (intro kept hk q hq; exact ⟨isSome_ext h _ (hd kept hk q hq).1, isSome_ext h _ (hd kept hk q hq).2⟩)

def NewDone (H : WHeap) (cfg : WCfg) (st st' : WState) : Prop :=
  ∀ i c, st.objlist.length ≤ i → st'.objlist[i]? = some c → ChildrenDone H cfg st' c

def FlatOk (H : WHeap) (cfg : WCfg) (f : Nat → WState → Py WState) : Prop :=
  ∀ c st st', WInv H st → f c st = .ok st' →
    WInv H st' ∧ WExt st st' ∧ (lookupW H st' c).isSome ∧ NewDone H cfg st st'

theorem wloop_spec (H : WHeap) (cfg : WCfg) (f : Nat → WState → Py WState) (hf : FlatOk H cfg f) :
    ∀ xs st st', WInv H st → wloop f xs st = .ok st' →
      WInv H st' ∧ WExt st st' ∧ (∀ x ∈ xs, (lookupW H st' x).isSome) ∧ NewDone H cfg st st'
  | [], st, st', hI, h => by
    simp only [wloop] at h; cases h
    exact ⟨hI, wext_refl _, by simp, fun i c hi hc => by
      have := lt_of_getElem?_some hc; omega⟩
  | x :: xs, st, st', hI, h => by
    simp only [wloop, bind, Except.bind] at h
    cases h1 : f x st with
    | error e => rw [h1] at h; cases h
    | ok st1 =>
      rw [h1] at h
      obtain ⟨hI1, he1, hl1, hn1⟩ := hf x st st1 hI h1
      obtain ⟨hI2, he2, hl2, hn2⟩ := wloop_spec H cfg f hf xs st1 st' hI1 h
      refine ⟨hI2, wext_trans he1 he2, ?_, ?_⟩
      · intro y hy
        simp at hy
        rcases hy with rfl | hy
        · exact isSome_ext he2 _ hl1
        · exact hl2 y hy
      · intro i c hi hc
        by_cases hi1 : i < st1.objlist.length
        · have ⟨⟨l, el⟩, _, _⟩ := he2
          have hc1 : st1.objlist[i]? = some c := by
            rw [el, List.getElem?_append_left hi1] at hc; exact hc
          exact childrenDone_ext he2 c (hn1 i c hi hc1)
        · exact hn2 i c (by omega) hc

theorem scalarMatch_self (H : WHeap) (c : Nat) : scalarMatch H c c = true := by
  simp [scalarMatch]

/-- Appending a new object keeps the tables right. -/
theorem winv_append (H : WHeap) (st : WState) (c : Nat) (hI : WInv H st)
    (hns : lookupW H st c = none) :
    let st1 := { st with objlist := st.objlist ++ [c] }
    let st2 := if isScalar H c then { st1 with objtable := st1.objtable ++ [(c, st.objlist.length)] }
      else { st1 with objidtable := st1.objidtable ++ [(objId H c, st.objlist.length)] }
    WInv H st2 ∧ WExt st st2 ∧ lookupW H st2 c = some st.objlist.length := by
  intro st1 st2
  obtain ⟨h1, h2, h3⟩ := hI
  have hlast : (st.objlist ++ [c])[st.objlist.length]? = some c := by simp
  by_cases hs : isScalar H c = true
  · have e2 : st2 = ⟨st.objlist ++ [c], st.objtable ++ [(c, st.objlist.length)], st.objidtable⟩ := by
      simp [st2, st1, hs]
    have hext : WExt st st2 := by
      rw [e2]; exact ⟨⟨[c], rfl⟩, ⟨_, rfl⟩, ⟨[], by simp⟩⟩
    have hnew : lookupW H st2 c = some st.objlist.length := by
      rw [e2]
      unfold lookupW tableLookup at *
      rw [if_pos hs] at hns ⊢
      simp only at hns ⊢
      rw [List.find?_append]
      cases hf : st.objtable.find? (fun x => scalarMatch H x.1 c) with
      | some q => rw [hf] at hns; cases hns
      | none => simp [scalarMatch_self]
    refine ⟨⟨?_, ?_, ?_⟩, hext, hnew⟩
    · rw [e2]; intro q hq
      simp at hq
      rcases hq with hq | rfl
      · exact ⟨getElem?_append_left' _ (h1 q hq).1, (h1 q hq).2⟩
      · exact ⟨hlast, hs⟩
    · rw [e2]; intro q hq
      obtain ⟨c', hc1, hc2, hc3⟩ := h2 q hq
      exact ⟨c', getElem?_append_left' _ hc1, hc2, hc3⟩
    · intro i c' hc'
      by_cases hi : i < st.objlist.length
      · have : st.objlist[i]? = some c' := by
          rw [e2] at hc'; simp only at hc'
          rw [List.getElem?_append_left hi] at hc'; exact hc'
        exact lookup_ext hext c' i (h3 i c' this)
      · have hi' : i = st.objlist.length := by
          have := lt_of_getElem?_some hc'
          rw [e2] at this; simp at this; omega
        subst hi'
        rw [e2] at hc'; simp at hc'; subst hc'
        exact hnew
  · have hs' : isScalar H c = false := by simpa using hs
    have e2 : st2 = ⟨st.objlist ++ [c], st.objtable, st.objidtable ++ [(objId H c, st.objlist.length)]⟩ := by
      simp [st2, st1, hs']
    have hext : WExt st st2 := by
      rw [e2]; exact ⟨⟨[c], rfl⟩, ⟨[], by simp⟩, ⟨_, rfl⟩⟩
    have hnew : lookupW H st2 c = some st.objlist.length := by
      rw [e2]
      unfold lookupW idLookup at *
      rw [if_neg (by simp [hs'])] at hns ⊢
      simp only at hns ⊢
      rw [List.find?_append]
      cases hf : st.objidtable.find? (fun x => x.1 == objId H c) with
      | some q => rw [hf] at hns; cases hns
      | none => simp
    refine ⟨⟨?_, ?_, ?_⟩, hext, hnew⟩
    · rw [e2]; intro q hq
      exact ⟨getElem?_append_left' _ (h1 q hq).1, (h1 q hq).2⟩
    · rw [e2]; intro q hq
      simp at hq
      rcases hq with hq | rfl
      · obtain ⟨c', hc1, hc2, hc3⟩ := h2 q hq
        exact ⟨c', getElem?_append_left' _ hc1, hc2, hc3⟩
      · exact ⟨c, hlast, rfl, hs'⟩
    · intro i c' hc'
      by_cases hi : i < st.objlist.length
      · have : st.objlist[i]? = some c' := by
          rw [e2] at hc'; simp only at hc'
          rw [List.getElem?_append_left hi] at hc'; exact hc'
        exact lookup_ext hext c' i (h3 i c' this)
      · have hi' : i = st.objlist.length := by
          have := lt_of_getElem?_some hc'
          rw [e2] at this; simp at this; omega
        subst hi'
        rw [e2] at hc'; simp at hc'; subst hc'
        exact hnew


theorem seen_eq (H : WHeap) (st : WState) (c : Nat) :
    (if (scalarType (H.getD c .none)).isSome = true then (tableLookup H st c).isSome
      else (idLookup H st c).isSome) = (lookupW H st c).isSome := by
  unfold lookupW isScalar
  split <;> rfl

theorem dictItemsR_ok (r : Nat) (H : WHeap) (cfg : WCfg) (items its : List (Nat × Nat))
    (h : dictItemsR r H cfg items = .ok its) : dictItems H cfg items = .ok its := by
  cases r with
  | zero => simp [dictItemsR, call] at h
  | succ r => simpa [dictItemsR, call] using h

theorem newDone_step (H : WHeap) (cfg : WCfg) (st st2 st' : WState) (c : Nat)
    (he2 : WExt st st2) (hlen2 : st2.objlist.length = st.objlist.length + 1)
    (hc2 : st2.objlist[st.objlist.length]? = some c) (he' : WExt st2 st')
    (hn : NewDone H cfg st2 st') (hcd : ChildrenDone H cfg st' c) : NewDone H cfg st st' := by
  intro i c' hi hc'
  by_cases hi1 : i = st.objlist.length
  · subst hi1
    have ⟨⟨l, el⟩, _, _⟩ := he'
    rw [el, List.getElem?_append_left (by omega), hc2] at hc'
    cases hc'
    exact hcd
  · exact hn i c' (by omega) hc'

theorem flatten_spec (H : WHeap) (cfg : WCfg) : ∀ r, FlatOk H cfg (flattenR H cfg r)
  | 0 => by intro c st st' _ h; simp [flattenR] at h
  | r + 1 => by
    intro c st st' hI h
    have IH := flatten_spec H cfg r
    simp only [flattenR] at h
    rw [seen_eq] at h
    cases hl : lookupW H st c with
    | some i =>
      rw [hl] at h
      simp only [Option.isSome_some, ↓reduceIte, Except.ok.injEq] at h
      subst h
      exact ⟨hI, wext_refl _, by rw [hl]; rfl, fun i c hi hc => by
        have := lt_of_getElem?_some hc; omega⟩
    | none =>
      rw [hl] at h
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨hI2, he2, hl2⟩ := winv_append H st c hI hl
      have hfo : FlatOk H cfg (fun x st => flattenR H cfg r x st) := IH
      generalize hst2 : (if isScalar H c = true then
          (⟨st.objlist ++ [c], st.objtable ++ [(c, st.objlist.length)], st.objidtable⟩ : WState)
        else ⟨st.objlist ++ [c], st.objtable, st.objidtable ++ [(objId H c, st.objlist.length)]⟩) = st2 at hI2 he2 hl2
      have hst2' : st2.objlist = st.objlist ++ [c] := by
        rw [← hst2]; split <;> rfl
      have hlen2 : st2.objlist.length = st.objlist.length + 1 := by rw [hst2']; simp
      have hc2 : st2.objlist[st.objlist.length]? = some c := by rw [hst2']; simp
      have hh : (if (scalarType (H.getD c .none)).isSome = true then
          (⟨st.objlist ++ [c], st.objtable ++ [(c, st.objlist.length)], st.objidtable⟩ : WState)
        else ⟨st.objlist ++ [c], st.objtable, st.objidtable ++ [(objId H c, st.objlist.length)]⟩) = st2 := by
        rw [← hst2]; rfl
      rw [hh] at h
      cases ho : H.getD c .none with
      | dict items | fdict items =>
        rw [ho] at h
        simp only [bind, Except.bind] at h
        cases hdi : dictItemsR r H cfg items with
        | error e => rw [hdi] at h; cases h
        | ok its =>
          rw [hdi] at h
          simp only at h
          cases hk : keptItems H cfg.skipkeys its with
          | error e => rw [hk] at h; cases h
          | ok kept =>
            rw [hk] at h
            simp only at h
            obtain ⟨hI', he', hl', hn'⟩ := wloop_spec H cfg _ hfo _ st2 st' hI2 h
            have hw : writtenItems H cfg items = .ok kept := by
              simp [writtenItems, dictItemsR_ok r H cfg items its hdi, bind, Except.bind, hk]
            refine ⟨hI', wext_trans he2 he', ?_, ?_⟩
            · rw [lookup_ext he' c _ hl2]; rfl
            · apply newDone_step H cfg st st2 st' c he2 hlen2 hc2 he' hn'
              unfold ChildrenDone
              rw [ho]
              intro kept' hk' q hq
              rw [hw] at hk'
              cases hk'
              exact ⟨hl' _ (by simp; exact Or.inl ⟨q.2, hq⟩), hl' _ (by simp; exact Or.inr ⟨q.1, hq⟩)⟩
      | list xs | tuple xs =>
        rw [ho] at h
        simp only at h
        obtain ⟨hI', he', hl', hn'⟩ := wloop_spec H cfg _ hfo xs st2 st' hI2 h
        refine ⟨hI', wext_trans he2 he', ?_, ?_⟩
        · rw [lookup_ext he' c _ hl2]; rfl
        · apply newDone_step H cfg st st2 st' c he2 hlen2 hc2 he' hn'
          unfold ChildrenDone
          rw [ho]
          exact hl'
      | _ =>
        rw [ho] at h
        simp only [Except.ok.injEq] at h
        subst h
        refine ⟨hI2, he2, by rw [hl2]; rfl, ?_⟩
        apply newDone_step H cfg st st2 st2 c he2 hlen2 hc2 (wext_refl _)
          (fun i c hi hc => by have := lt_of_getElem?_some hc; omega)
        unfold ChildrenDone
        rw [ho]
        trivial

end PyLean.TextLibs.Plist
