import PyLean.TextLibs.PlistRoundTrip3

namespace PyLean.TextLibs.Plist

open PyLean PyLean.TextLibs

theorem getD_lt {α : Type} (l : List α) (d : α) {k : Nat} (hk : k < l.length) : l.getD k d = l[k] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; rfl

theorem flatten_drop (encs : List (List Nat)) (j : Nat) (hj : j < encs.length) :
    (encs.drop j).flatten = encs.getD j [] ++ (encs.drop (j + 1)).flatten := by
  have := List.drop_eq_getElem_cons hj
  rw [this, List.flatten_cons, getD_lt _ _ hj]

theorem take_drop_flatten (encs : List (List Nat)) (j : Nat) :
    encs.flatten = (encs.take j).flatten ++ (encs.drop j).flatten := by
  rw [← List.flatten_append, List.take_append_drop]

theorem forall2_left {α β : Type} {P : α → β → Prop} {Q : α → Prop} :
    ∀ {l : List α} {m : List β}, Forall2 P l m → (∀ a ∈ l, Q a) → Forall2 (fun a b => P a b ∧ Q a) l m
  | [], [], .nil, _ => .nil
  | _ :: _, _ :: _, .cons h1 t, hq => .cons ⟨h1, hq _ (by simp)⟩ (forall2_left t (fun a ha => hq a (by simp [ha])))

theorem map_str_ne (a b : Option (List Nat)) (h : a ≠ b) : a.map Obj.str ≠ b.map Obj.str := by
  cases a <;> cases b <;> simp_all

theorem length_le_flatten (encs : List (List Nat)) (h : ∀ e ∈ encs, e ≠ []) :
    encs.length ≤ encs.flatten.length := by
  induction encs with
  | nil => simp
  | cons e es ih =>
    simp only [List.length_cons, List.flatten_cons, List.length_append]
    have he := h e (by simp)
    have : 1 ≤ e.length := by cases e with | nil => exact absurd rfl he | cons _ _ => simp
    have := ih (fun x hx => h x (by simp [hx]))
    omega

/-- The written table satisfies what the reader needs. -/
theorem written_tab (H : WHeap) (cfg : WCfg) (b : List Nat) (hwf : HeapWf H)
    (st : WState) (offsets body : List Nat) (top : Nat)
    (hb : b = bplistHeader ++ body ++ packRefs (countToSize (8 + body.length)) offsets ++
      ([0, 0, 0, 0, 0, 0, countToSize (8 + body.length), countToSize st.objlist.length] ++
        beBytes st.objlist.length 8 ++ beBytes top 8 ++ beBytes (8 + body.length) 8))
    (hbl : b.length < 2 ^ 63)
    (encs : List (List Nat)) (os : List Obj) (hI : WInv H st)
    (h1 : encs.length = st.objlist.length) (h2 : os.length = st.objlist.length)
    (h3 : body = encs.flatten)
    (h6 : ∀ k, k < st.objlist.length → offsets[k]? = some (8 + (encs.take k).flatten.length))
    (h7 : ∀ k, k < st.objlist.length → canon (countToSize st.objlist.length) (os.getD k .none) =
      some (encs.getD k []) ∧ Rel H cfg st (st.objlist.getD k 0) (os.getD k .none))
    (hol : offsets.length = st.objlist.length) :
    TabWf ⟨os, b, offsets, countToSize st.objlist.length⟩ := by
  have hne : ∀ e ∈ encs, e ≠ [] := by
    intro e he
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem he
    have := (h7 k (by omega)).1
    rw [getD_lt _ _ hk] at this
    obtain ⟨tok, tail, ht⟩ := canon_cons _ _ _ this
    rw [ht]; simp
  have hbody : body.length < 2 ^ 63 := by
    have := congrArg List.length hb; simp at this; omega
  have hn : st.objlist.length < 2 ^ 63 := by
    have := length_le_flatten encs hne; rw [h3] at hbody; omega
  have hrs := countToSize_lt st.objlist.length (by omega)
  refine ⟨by simp [hol, h2], countToSize_bin _, ?_⟩
  intro j hj
  simp only at hj ⊢
  have hjn : j < st.objlist.length := by omega
  obtain ⟨hcanon, hrel⟩ := h7 j hjn
  rw [getD_lt _ _ hj] at hcanon hrel
  have hlook : ∀ x r, lookupW H st x = some r → r < 256 ^ countToSize st.objlist.length ∧
      r < os.length := fun x r h => by have := lookup_lt hI h; omega
  -- the bytes of object j
  have hoff : offsets.getD j 0 = 8 + (encs.take j).flatten.length := by
    rw [List.getD_eq_getElem?_getD, h6 j hjn]; rfl
  have hdrop : b.drop (offsets.getD j 0) = encs.getD j [] ++ ((encs.drop (j + 1)).flatten ++
      (packRefs (countToSize (8 + body.length)) offsets ++
      ([0, 0, 0, 0, 0, 0, countToSize (8 + body.length), countToSize st.objlist.length] ++
        beBytes st.objlist.length 8 ++ beBytes top 8 ++ beBytes (8 + body.length) 8))) := by
    rw [hoff, hb, h3, take_drop_flatten encs j, flatten_drop encs j (by omega)]
    simp only [bplistHeader, asciiBytes, List.append_assoc]
    rw [← List.drop_drop]
    simp
  have helen : (encs.getD j []).length + 8 + (encs.take j).flatten.length ≤ b.length := by
    rw [hb, h3, take_drop_flatten encs j, flatten_drop encs j (by omega)]
    simp [bplistHeader, asciiBytes]; omega
  have hejne : encs.getD j [] ≠ [] := hne _ (by rw [getD_lt _ _ (by omega)]; simp)
  have hel1 : 1 ≤ (encs.getD j []).length := by
    cases hh : encs.getD j [] with
    | nil => exact absurd hh hejne
    | cons _ _ => simp
  refine ⟨?_, ?_, ?_, encs.getD j [], _, hcanon, hdrop, by rw [hoff]; omega, by omega⟩
  · -- ObjWf
    unfold Rel at hrel
    cases hc : H.getD (st.objlist.getD j 0) .none <;> rw [hc] at hrel <;> cases ho : os[j] <;>
      rw [ho] at hrel <;> simp only [ObjWf] <;> (try trivial) <;> (try exact hrel.elim)
    · subst hrel; exact hwf.2.1 _ _ hc
    · subst hrel; exact hwf.2.2.1 _ _ hc
    · intro x hx; obtain ⟨y, _, hy⟩ := forall2_mem hrel x hx; exact (hlook _ _ hy).1
    · intro x hx; obtain ⟨y, _, hy⟩ := forall2_mem hrel x hx; exact (hlook _ _ hy).1
    · obtain ⟨_, _, hf⟩ := hrel
      intro p hp; obtain ⟨q, _, hq⟩ := forall2_mem hf p hp
      exact ⟨(hlook _ _ hq.1).1, (hlook _ _ hq.2).1⟩
    · obtain ⟨_, _, hf⟩ := hrel
      intro p hp; obtain ⟨q, _, hq⟩ := forall2_mem hf p hp
      exact ⟨(hlook _ _ hq.1).1, (hlook _ _ hq.2).1⟩
  · -- children
    unfold Rel at hrel
    cases hc : H.getD (st.objlist.getD j 0) .none <;> rw [hc] at hrel <;> cases ho : os[j] <;>
      rw [ho] at hrel <;> simp only [children] <;> (try simp) <;> (try exact hrel.elim)
    · intro x hx; obtain ⟨y, _, hy⟩ := forall2_mem hrel x hx; exact (hlook _ _ hy).2
    · intro x hx; obtain ⟨y, _, hy⟩ := forall2_mem hrel x hx; exact (hlook _ _ hy).2
    all_goals (obtain ⟨_, _, hf⟩ := hrel
               intro x hx
               rcases hx with ⟨y, hy⟩ | ⟨y, hy⟩
               · obtain ⟨q, _, hq⟩ := forall2_mem hf _ hy; exact (hlook _ _ hq.1).2
               · obtain ⟨q, _, hq⟩ := forall2_mem hf _ hy; exact (hlook _ _ hq.2).2)
  · -- dict keys
    unfold Rel at hrel
    cases hc : H.getD (st.objlist.getD j 0) .none <;> rw [hc] at hrel <;> cases ho : os[j] <;>
      rw [ho] at hrel <;> simp only [DictKeysWf] <;> (try trivial) <;> (try exact hrel.elim)
    all_goals (
      obtain ⟨kept, hk, hf⟩ := hrel
      obtain ⟨hstr, hpw⟩ := written_keys H cfg _ kept
        (by first | exact hwf.2.2.2.1 _ _ hc | exact hwf.2.2.2.2 _ _ hc) hk
      have hf2 := forall2_left (Q := fun q => (keyStr H q.1).isSome = true) hf hstr
      have hos7 : ∀ k, k < st.objlist.length → Rel H cfg st (st.objlist.getD k 0) (os.getD k .none) :=
        fun k hk => (h7 k hk).2
      have hkey : ∀ (q p : Nat × Nat), (lookupW H st q.1 = some p.1 ∧ lookupW H st q.2 = some p.2) ∧
          (keyStr H q.1).isSome = true → os[p.1]? = (keyStr H q.1).map Obj.str := by
        intro q p ⟨⟨hq1, _⟩, hqs⟩
        cases hks : keyStr H q.1 with
        | none => rw [hks] at hqs; cases hqs
        | some s => rw [key_obj H cfg st hI os hos7 h2 q.1 s hks p.1 hq1]; rfl
      refine ⟨fun p hp => ?_, ?_⟩
      · obtain ⟨q, _, hq⟩ := forall2_mem hf2 p hp
        cases hks : keyStr H q.1 with
        | none => rw [hks] at hq; cases hq.2
        | some s => exact ⟨s, by rw [hkey q p hq, hks]; rfl⟩
      · rw [forall2_map (fun p => os[p.1]?) (fun q => (keyStr H q.1).map Obj.str) hkey hf2]
        rw [List.pairwise_map] at hpw ⊢
        exact hpw.imp (fun h => map_str_ne _ _ h))

end PyLean.TextLibs.Plist
