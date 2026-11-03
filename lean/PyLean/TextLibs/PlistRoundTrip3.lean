import PyLean.TextLibs.PlistRoundTrip2

namespace PyLean.TextLibs.Plist

open PyLean PyLean.TextLibs

theorem lookup_lt {H : WHeap} {st : WState} (hI : WInv H st) {x r : Nat} (h : lookupW H st x = some r) :
    r < st.objlist.length := by
  obtain ⟨c', hc', _⟩ := lookup_sound hI h
  exact lt_of_getElem?_some hc'

theorem winv_init (H : WHeap) : WInv H WState.init :=
  ⟨by simp [WState.init], by simp [WState.init], by simp [WState.init]⟩

/-- The key slot of a written dict item reads back as the key's `str`. -/
theorem key_obj (H : WHeap) (cfg : WCfg) (st : WState) (hI : WInv H st) (os : List Obj)
    (hos : ∀ k, k < st.objlist.length → Rel H cfg st (st.objlist.getD k 0) (os.getD k .none))
    (hlen : os.length = st.objlist.length)
    (q : Nat) (s : List Nat) (hq : keyStr H q = some s) (r : Nat) (hr : lookupW H st q = some r) :
    os[r]? = some (.str s) := by
  have hs : H.getD q .none = .str s := by
    unfold keyStr at hq; split at hq <;> simp_all
  have hsc : isScalar H q = true := by unfold isScalar; rw [hs]; rfl
  obtain ⟨c', hc', hm⟩ := lookup_sound hI hr
  have hrl := lt_of_getElem?_some hc'
  have hrel := hos r hrl
  rw [List.getD_eq_getElem?_getD, hc'] at hrel
  simp only [Option.getD_some] at hrel
  rcases hm with ⟨_, hm⟩ | ⟨h, _⟩
  · have hc's : H.getD c' .none = .str s := by
      unfold scalarMatch at hm
      simp only [hs, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hm
      obtain ⟨ht, hm⟩ := hm
      rcases hm with heq | heq
      · rw [heq, hs]
      · cases hcc : H.getD c' .none <;> rw [hcc] at heq ht <;> simp_all [scalarEq, scalarType]
    unfold Rel at hrel
    rw [hc's] at hrel
    have : os.getD r .none = .str s := by
      cases ho : os.getD r .none <;> rw [ho] at hrel <;> simp_all
    rw [List.getD_eq_getElem?_getD] at this
    cases hh : os[r]? with
    | none => rw [hh] at this; simp at this
    | some o => rw [hh] at this; simp at this; rw [this]
  · rw [hsc] at h; cases h


theorem forall2_mem_and {α β : Type} {P : α → β → Prop} {Q : β → Prop} :
    ∀ {l : List α} {m : List β}, Forall2 P l m → (∀ b ∈ m, Q b) → Forall2 (fun a b => P a b ∧ Q b) l m
  | [], [], .nil, _ => .nil
  | _ :: _, _ :: _, .cons h1 t, hq => .cons ⟨h1, hq _ (by simp)⟩ (forall2_mem_and t (fun b hb => hq b (by simp [hb])))

theorem dict_match (H : WHeap) (cfg : WCfg) (st : WState) (R : Nat → Nat → Prop) (D : Nat → Prop)
    (hRD : ∀ r x, lookupW H st x = some r → D r → R r x) (items ps : List (Nat × Nat))
    (hrel : ∃ kept, writtenItems H cfg items = .ok kept ∧
      Forall2 (fun q p => lookupW H st q.1 = some p.1 ∧ lookupW H st q.2 = some p.2) kept ps)
    (hch : ∀ x ∈ children (.dict ps), D x) :
    ∃ kept, writtenItems H cfg items = .ok kept ∧ Forall2 (fun q p => R p.1 q.1 ∧ R p.2 q.2) kept ps := by
  obtain ⟨kept, hk, hf⟩ := hrel
  refine ⟨kept, hk, forall2_mono (fun q p h => ⟨hRD _ _ h.1.1 h.2.1, hRD _ _ h.1.2 h.2.2⟩)
    (forall2_mem_and (Q := fun p => D p.1 ∧ D p.2) hf (fun p hp => ⟨hch _ ?_, hch _ ?_⟩))⟩
  · exact List.mem_append.mpr (Or.inl (List.mem_map_of_mem hp))
  · exact List.mem_append.mpr (Or.inr (List.mem_map_of_mem hp))

theorem list_match (H : WHeap) (st : WState) (R : Nat → Nat → Prop) (D : Nat → Prop)
    (hRD : ∀ r x, lookupW H st x = some r → D r → R r x) (xs rs : List Nat)
    (hrel : Forall2 (fun x r => lookupW H st x = some r) xs rs) (hch : ∀ x ∈ children (.arr rs), D x) :
    Forall2 (fun x r => R r x) xs rs :=
  forall2_mono (fun x r h => hRD r x h.1 h.2) (forall2_mem_and hrel (fun b hb => hch b hb))

theorem rel_match_same (H : WHeap) (cfg : WCfg) (st : WState) (R : Nat → Nat → Prop) (D : Nat → Prop)
    (hRD : ∀ r x, lookupW H st x = some r → D r → R r x) (c : Nat) (o : Obj)
    (hrel : Rel H cfg st c o) (hch : ∀ x ∈ children o, D x) : Match H cfg R o (H.getD c .none) := by
  unfold Rel at hrel
  unfold Match
  cases hc : H.getD c .none <;> rw [hc] at hrel
  case list xs =>
    cases o with
    | arr rs => exact list_match H st R D hRD xs rs hrel hch
    | _ => exact hrel.elim
  case tuple xs =>
    cases o with
    | arr rs => exact list_match H st R D hRD xs rs hrel hch
    | _ => exact hrel.elim
  case dict items =>
    cases o with
    | dict ps => exact dict_match H cfg st R D hRD items ps hrel hch
    | _ => exact hrel.elim
  case fdict items =>
    cases o with
    | dict ps => exact dict_match H cfg st R D hRD items ps hrel hch
    | _ => exact hrel.elim
  all_goals (cases o <;> simp_all)


theorem scalarEq_cases (a b : WObj) (h : scalarEq a b = true) :
    (∃ x, a = .str x ∧ b = .str x) ∨ (∃ x, a = .int x ∧ b = .int x) ∨ (∃ x, a = .bool x ∧ b = .bool x) ∨
    (∃ x y, a = .float x ∧ b = .float y ∧ Binary64.F64.eq (Binary64.F64.ofBits x) (Binary64.F64.ofBits y) = true) ∨
    (∃ x o, a = .date x o) ∨ (∃ x, a = .bytes x ∧ b = .bytes x) := by
  cases a <;> cases b <;> simp_all [scalarEq]
  all_goals (rename_i o1 _ o2; cases o1 <;> cases o2 <;> simp_all [scalarEq])

theorem match_of_lookup (H : WHeap) (cfg : WCfg) (st : WState) (R : Nat → Nat → Prop) (D : Nat → Prop)
    (hRD : ∀ r x, lookupW H st x = some r → D r → R r x) (hnd : ∀ c us off, H.getD c .none ≠ .date us off)
    (c' c : Nat) (o : Obj) (hrel : Rel H cfg st c' o) (hch : ∀ x ∈ children o, D x)
    (hm : (isScalar H c = true ∧ scalarMatch H c' c = true) ∨
      (isScalar H c = false ∧ objId H c' = objId H c ∧ isScalar H c' = false)) :
    Match H cfg R o (H.getD c .none) := by
  rcases hm with ⟨_, hm⟩ | ⟨_, hid, _⟩
  · unfold scalarMatch at hm
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hm
    obtain ⟨_, hm | hm⟩ := hm
    · subst hm; exact rel_match_same H cfg st R D hRD c' o hrel hch
    · unfold Rel at hrel
      unfold Match
      rcases scalarEq_cases _ _ hm with ⟨x, ha, hb⟩ | ⟨x, ha, hb⟩ | ⟨x, ha, hb⟩ | ⟨x, y, ha, hb, he⟩ |
          ⟨x, o', ha⟩ | ⟨x, ha, hb⟩
      all_goals (try rw [ha] at hrel)
      all_goals (try rw [hb])
      · cases o <;> simp_all
      · cases o <;> simp_all
      · cases o <;> simp_all
      · cases o <;> simp_all
        subst hrel
        exact Or.inr (by
          unfold Binary64.F64.eq at he ⊢
          split at he <;> (try split at he) <;> simp_all <;> (split <;> (try split) <;> simp_all <;> omega))
      · exact absurd ha (hnd c' x o')
      · cases o <;> simp_all
  · cases hc' : objId H c' with
    | cell d =>
      have h1 := objId_cell H c' d hc'
      rw [hc'] at hid
      have h2 := objId_cell H c d hid.symm
      subst h1; subst h2
      exact rel_match_same H cfg st R D hRD _ o hrel hch
    | noneObj =>
      have h1 := objId_none H c' hc'
      rw [hc'] at hid
      have h2 := objId_none H c hid.symm
      unfold Rel at hrel; rw [h1] at hrel
      unfold Match; rw [h2]
      cases o <;> simp_all
    | emptyTuple =>
      have h1 := objId_tuple H c' hc'
      rw [hc'] at hid
      have h2 := objId_tuple H c hid.symm
      unfold Rel at hrel; rw [h1] at hrel
      unfold Match; rw [h2]
      cases o with
      | arr rs => cases hrel; exact .nil
      | _ => exact hrel.elim

end PyLean.TextLibs.Plist
