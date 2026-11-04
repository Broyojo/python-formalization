import PyLean.CoreLibs.Coll.ODictObj

/-!
`OrderedDict.move_to_end` keeps the list invariant, moving one link to the end or the front.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace PyLean.CoreLibs.Coll

open PyLean

variable {κ ν : Type} [DecidableEq κ]

/-- The parts of the invariant that do not look at the links survive any reordering of the list. -/
theorem odInv_perm {o o' : OD κ ν} {L L' : List (Nat × κ)} (I : ODInv o L) (hp : L'.Perm L)
    (hd : o'.d = o.d) (hm : o'.map = o.map) (hn : o'.next = o.next)
    (hfind : ∀ k, (L'.find? (·.2 = k)).map (·.1) = (L.find? (·.2 = k)).map (·.1))
    (hch : Chain o'.heap 0 L' 0) (hroot : o'.heap 0 = ⟨none, some (lastOf 0 L'), some (nxt L' 0)⟩) :
    ODInv o' L' := by
  refine ⟨hch, hroot, (hp.map _).nodup_iff.2 I.ids, (hp.map _).nodup_iff.2 I.keys,
    fun x hx => by rw [hn]; exact I.pos x ((hp.map (·.1)).mem_iff.1 hx), by rw [hn, hp.length_eq]; exact I.len,
    fun k => by rw [hm, I.map k, hfind k], fun k => ?_, by rw [hd]; exact I.wfd, by rw [hm]; exact I.wfm⟩
  rw [hd, I.mem k]
  exact decide_eq_decide.2 (hp.map (·.2)).mem_iff.symm

theorem find_move (A B : List (Nat × κ)) (i : Nat) (key k : κ) (hkA : key ∉ A.map (·.2)) (hkB : key ∉ B.map (·.2)) :
    ((A ++ B ++ [(i, key)]).find? (·.2 = k)).map (·.1) = ((A ++ (i, key) :: B).find? (·.2 = k)).map (·.1) ∧
    (((i, key) :: (A ++ B)).find? (·.2 = k)).map (·.1) = ((A ++ (i, key) :: B).find? (·.2 = k)).map (·.1) := by
  by_cases hk : key = k
  · subst hk; simp [List.find?_append, find?_snd_none hkA, find?_snd_none hkB]
  · simp [List.find?_append, List.find?_cons, hk]

/-- What unlinking `i` (Lib/collections/__init__.py:199-204) leaves: the other links chained as
`A ++ B` from the root, the link `i` itself untouched, and `link_next.prev` (`soft_link`) is `i`. -/
theorem move_unlink (K : KOps κ) (o : OD κ ν) (A B : List (Nat × κ)) (i : Nat) (key : κ)
    (I : ODInv o (A ++ (i, key) :: B)) (lp ln soft : Nat) (o1 : OD κ ν)
    (hlp : lp = ((o.link i).prev).getD 0) (hln : ln = ((o.link i).next).getD 0)
    (hsoft : soft = ((o.link ln).prev).getD 0) (ho1 : o1 = (o.setNext lp ln).setPrev ln lp) :
    Chain o1.heap 0 (A ++ B) 0 ∧ o1.heap 0 = ⟨none, some (lastOf 0 (A ++ B)), some (nxt (A ++ B) 0)⟩ ∧
      (o1.heap i).key = some key ∧ soft = i ∧ i ≠ 0 ∧ i ∉ (A ++ B).map (·.1) ∧
      (∀ x ∈ (A ++ B).map (·.1), x ≠ 0) ∧ ((A ++ B).map (·.1)).Nodup ∧
      o1.d = o.d ∧ o1.map = o.map ∧ o1.next = o.next ∧ key ∉ A.map (·.2) ∧ key ∉ B.map (·.2) := by
  have IDr := del_core K o A B i key I
  have hch := I.chain
  rw [chain_append] at hch
  obtain ⟨hA, hi, hB⟩ := hch
  have hids : (A.map (·.1) ++ i :: B.map (·.1)).Nodup := by simpa using I.ids
  have hkeys : (A.map (·.2) ++ key :: B.map (·.2)).Nodup := by simpa using I.keys
  have hiA : i ∉ A.map (·.1) := fun h => (List.nodup_append.1 hids).2.2 i h i (by simp) rfl
  have hiB : i ∉ B.map (·.1) := (List.nodup_cons.1 (List.nodup_append.1 hids).2.1).1
  have hkA : key ∉ A.map (·.2) := fun h => (List.nodup_append.1 hkeys).2.2 key h key (by simp) rfl
  have hkB : key ∉ B.map (·.2) := (List.nodup_cons.1 (List.nodup_append.1 hkeys).2.1).1
  have hz : ∀ x ∈ (A ++ (i, key) :: B).map (·.1), x ≠ 0 := fun x hx => Nat.pos_iff_ne_zero.1 (I.pos x hx).1
  have hzA : ∀ x ∈ A.map (·.1), x ≠ 0 := fun x hx => hz x (by
    simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons]; exact Or.inl hx)
  have hzB : ∀ x ∈ B.map (·.1), x ≠ 0 := fun x hx => hz x (by
    simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons]; exact Or.inr (Or.inr hx))
  have hi0 : i ≠ 0 := hz i (by simp)
  have hlpdef : lp = lastOf 0 A := by rw [hlp]; show ((o.heap i).prev).getD 0 = _; rw [hi]; rfl
  have hlndef : ln = nxt B 0 := by rw [hln]; show ((o.heap i).next).getD 0 = _; rw [hi]; rfl
  have hlpi : lp ≠ i := by
    by_cases h : A = []
    · rw [hlpdef, h]; exact Ne.symm hi0
    · intro he; exact hiA (he ▸ hlpdef ▸ lastOf_mem h)
  have hlni : ln ≠ i := by
    by_cases h : B = []
    · rw [hlndef, h]; exact Ne.symm hi0
    · intro he; exact hiB (he ▸ hlndef ▸ nxt_mem 0 h)
  have hH1 : ∀ x, x ≠ i → o1.heap x =
      (odDropLink { o with d := D.del o.d key, map := D.del o.map key } i).heap x := by
    intro x hx
    rw [ho1, hlp, hln]
    simp only [odDropLink, OD.link, OD.setPrev, OD.setNext, setLink_heap, hx, if_false]
  refine ⟨chain_frame (A ++ B) 0 0 (fun x hx => hH1 x (fun e => ?_)) IDr.chain, ?_, ?_, ?_, hi0, ?_, ?_,
    IDr.ids, by rw [ho1]; rfl, by rw [ho1]; rfl, by rw [ho1]; rfl, hkA, hkB⟩
  · rw [e] at hx; simp only [List.map_append, List.mem_append] at hx; exact hx.elim hiA hiB
  · rw [hH1 0 (Ne.symm hi0)]; exact IDr.root
  · rw [ho1]; simp only [OD.setPrev, OD.setNext, setLink_heap, Ne.symm hlni, Ne.symm hlpi, if_false, hi]
  · rw [hsoft]
    by_cases hB' : B = []
    · subst hB'
      rw [hlndef]
      show ((o.heap 0).prev).getD 0 = i
      rw [I.root]
      simp [lastOf]
    · obtain ⟨⟨j, kj⟩, B', rfl⟩ : ∃ q B', B = q :: B' := by
        cases B with
        | nil => exact absurd rfl hB'
        | cons q B' => exact ⟨q, B', rfl⟩
      rw [hlndef]
      show ((o.heap j).prev).getD 0 = i
      rw [hB.1]; rfl
  · simp only [List.map_append, List.mem_append, not_or]; exact ⟨hiA, hiB⟩
  · intro x hx
    simp only [List.map_append, List.mem_append] at hx
    exact hx.elim (hzA x) (hzB x)

/-- **`move_to_end` moves one link and keeps the invariant.** For every key type, every instance with
list `A ++ (i, key) :: B` and a hashable `key`: `od.move_to_end(key)` leaves the list
`A ++ B ++ [(i, key)]` and `od.move_to_end(key, last=False)` leaves `(i, key) :: (A ++ B)`, the dict
(and so every value) unchanged; an absent hashable key raises `KeyError(key)`, and an unhashable one the
dict-key `TypeError` of `self.__map[key]`.

Source: docstring, Lib/collections/__init__.py:194-217 ('Move an existing element to the end (or
beginning if last is false). Raise KeyError if the element does not exist.'). -/
def ODMoveInv : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] (K : KOps κ) (rk : κ → String) (o : OD κ ν) (A B L : List (Nat × κ)) (i : Nat)
    (key k : κ) (m : String),
    (ODInv o (A ++ (i, key) :: B) → K.hash key = .ok () →
      (∃ o', odMoveToEnd K rk o key true = .ok o' ∧ ODInv o' (A ++ B ++ [(i, key)]) ∧ o'.d = o.d) ∧
      (∃ o', odMoveToEnd K rk o key false = .ok o' ∧ ODInv o' ((i, key) :: (A ++ B)) ∧ o'.d = o.d)) ∧
    (ODInv o L → k ∉ L.map (·.2) → K.hash k = .ok () → ∀ last, odMoveToEnd K rk o k last = .error (.keyError (rk k))) ∧
    (K.hash k = .error (.typeError m) → ∀ last,
      odMoveToEnd K rk o k last = .error (.typeError s!"~cannot use '{K.tyName k}' as a dict key ({m})"))

theorem odMoveInv_proven : ODMoveInv := by
  intro κ ν _ K rk o A B L i key k m
  refine ⟨fun I hk => ?_, fun I hkL hk last => ?_, fun hk last => ?_⟩
  · have hmap : D.get? o.map key = some i := by
      rw [I.map key, List.find?_append]
      have hkA : key ∉ A.map (·.2) := by
        have hkeys : (A.map (·.2) ++ key :: B.map (·.2)).Nodup := by simpa using I.keys
        exact fun h => (List.nodup_append.1 hkeys).2.2 key h key (by simp) rfl
      simp [find?_snd_none hkA]
    have hdh : dHash K key = .ok () := by simp [dHash, hk]
    obtain ⟨lp, hlp⟩ : ∃ lp, lp = ((o.link i).prev).getD 0 := ⟨_, rfl⟩
    obtain ⟨ln, hln⟩ : ∃ ln, ln = ((o.link i).next).getD 0 := ⟨_, rfl⟩
    obtain ⟨soft, hsoft⟩ : ∃ soft, soft = ((o.link ln).prev).getD 0 := ⟨_, rfl⟩
    obtain ⟨o1, ho1⟩ : ∃ o1, o1 = (o.setNext lp ln).setPrev ln lp := ⟨_, rfl⟩
    obtain ⟨hch1, hroot1, hkey1, hsofti, hi0, hiM, hzM, hidsM, hd1, hm1, hn1, hkA, hkB⟩ :=
      move_unlink K o A B i key I lp ln soft o1 hlp hln hsoft ho1
    have hres : ∀ last, odMoveToEnd K rk o key last =
        if last then
          .ok (((o1.setLink i fun x => { x with prev := some (((o1.link 0).prev).getD 0), next := some 0 }).setPrev 0
            soft).setNext (((o1.link 0).prev).getD 0) i)
        else
          .ok (((o1.setLink i fun x => { x with prev := some 0, next := some (((o1.link 0).next).getD 0) }).setPrev
            (((o1.link 0).next).getD 0) soft).setNext 0 i) := by
      intro last
      rw [ho1, hsoft, hln, hlp]
      cases last <;> simp only [odMoveToEnd, hdh, ok_bind, hmap, pure_py] <;> (try rfl)
    have hl : ((o1.link 0).prev).getD 0 = lastOf 0 (A ++ B) := by simp [OD.link, hroot1]
    have hf : ((o1.link 0).next).getD 0 = nxt (A ++ B) 0 := by simp [OD.link, hroot1]
    rw [hsofti] at hres
    have hmem_l : A ++ B ≠ [] → lastOf 0 (A ++ B) ∈ (A ++ B).map (·.1) := fun h => lastOf_mem h
    have hmem_f : A ++ B ≠ [] → nxt (A ++ B) 0 ∈ (A ++ B).map (·.1) := fun h => nxt_mem 0 h
    have hl0 : A ++ B = [] → lastOf 0 (A ++ B) = 0 := fun h => by rw [h]; rfl
    have hf0 : A ++ B = [] → nxt (A ++ B) 0 = 0 := fun h => by rw [h]; rfl
    have hli : lastOf 0 (A ++ B) ≠ i := by
      by_cases h : A ++ B = []
      · rw [hl0 h]; exact Ne.symm hi0
      · intro he; exact hiM (he ▸ hmem_l h)
    have hfi : nxt (A ++ B) 0 ≠ i := by
      by_cases h : A ++ B = []
      · rw [hf0 h]; exact Ne.symm hi0
      · intro he; exact hiM (he ▸ hmem_f h)
    have hperm1 : (A ++ B ++ [(i, key)]).Perm (A ++ (i, key) :: B) :=
      List.perm_append_comm.trans (List.perm_middle.symm : ((i, key) :: (A ++ B)).Perm (A ++ (i, key) :: B))
    have hperm2 : ((i, key) :: (A ++ B)).Perm (A ++ (i, key) :: B) := List.perm_middle.symm
    refine ⟨⟨_, by rw [hres true]; rfl, ?_, by rw [ho1]; rfl⟩, ⟨_, by rw [hres false]; rfl, ?_, by rw [ho1]; rfl⟩⟩
    · rw [hl]
      refine odInv_perm I hperm1 (by rw [ho1]; rfl) (by rw [ho1]; rfl) (by rw [ho1]; rfl)
        (fun k => (find_move A B i key k hkA hkB).1) ?_ ?_
      · rw [chain_append]
        refine ⟨chain_retarget (A ++ B) 0 0 i hidsM hch1 ?_ ?_, ?_⟩
        · intro x hx hne
          have hx0 := hzM x hx
          have hxi : x ≠ i := fun e => hiM (e ▸ hx)
          simp [OD.setPrev, OD.setNext, setLink_heap, hne, hx0, hxi]
        · intro hM
          have hl0' : lastOf 0 (A ++ B) ≠ 0 := hzM _ (hmem_l hM)
          simp [OD.setPrev, OD.setNext, setLink_heap, hl0', hli]
        · show _ = _ ∧ True
          refine ⟨?_, trivial⟩
          have hil : i ≠ lastOf 0 (A ++ B) := Ne.symm hli
          simp only [OD.setPrev, OD.setNext, setLink_heap, hil, hi0, if_false, if_true]
          cases h1 : o1.heap i
          rw [h1] at hkey1
          simp only at hkey1
          rw [hkey1]
          rfl
      · by_cases hM : A ++ B = []
        · have hA : A = [] := (List.append_eq_nil_iff.1 hM).1
          have hB : B = [] := (List.append_eq_nil_iff.1 hM).2
          subst hA hB
          simp [OD.setPrev, OD.setNext, setLink_heap, Ne.symm hi0, hroot1, lastOf, nxt]
        · have hl0' : (0 : Nat) ≠ lastOf 0 (A ++ B) := Ne.symm (hzM _ (hmem_l hM))
          have e1 : lastOf 0 (A ++ B ++ [(i, key)]) = i := by rw [lastOf_append, if_neg (by simp)]; rfl
          have e2 : nxt (A ++ B ++ [(i, key)]) 0 = nxt (A ++ B) 0 := by rw [nxt_append, if_neg hM]
          rw [e1, e2]
          simp [OD.setPrev, OD.setNext, setLink_heap, Ne.symm hi0, hl0', hroot1]
    · rw [hf]
      refine odInv_perm I hperm2 (by rw [ho1]; rfl) (by rw [ho1]; rfl) (by rw [ho1]; rfl)
        (fun k => (find_move A B i key k hkA hkB).2) ?_ ?_
      · show _ = _ ∧ Chain _ i (A ++ B) 0
        refine ⟨?_, chain_resource (A ++ B) 0 i 0 hidsM hch1 ?_ ?_⟩
        · simp only [OD.setPrev, OD.setNext, setLink_heap, Ne.symm hfi, hi0, if_false, if_true]
          cases h1 : o1.heap i
          rw [h1] at hkey1
          simp only at hkey1
          rw [hkey1]
        · intro x hx hne
          have hx0 := hzM x hx
          have hxi : x ≠ i := fun e => hiM (e ▸ hx)
          simp [OD.setPrev, OD.setNext, setLink_heap, hne, hx0, hxi]
        · intro hM
          have hf0' : nxt (A ++ B) 0 ≠ 0 := hzM _ (hmem_f hM)
          simp [OD.setPrev, OD.setNext, setLink_heap, hf0', hfi]
      · by_cases hM : A ++ B = []
        · have hA : A = [] := (List.append_eq_nil_iff.1 hM).1
          have hB : B = [] := (List.append_eq_nil_iff.1 hM).2
          subst hA hB
          simp [OD.setPrev, OD.setNext, setLink_heap, Ne.symm hi0, hroot1, lastOf, nxt]
        · have hf0' : (0 : Nat) ≠ nxt (A ++ B) 0 := Ne.symm (hzM _ (hmem_f hM))
          have e1 : lastOf 0 ((i, key) :: (A ++ B)) = lastOf 0 (A ++ B) := by
            rw [show (i, key) :: (A ++ B) = [(i, key)] ++ (A ++ B) from rfl, lastOf_append, if_neg hM]
          have e2 : nxt ((i, key) :: (A ++ B)) 0 = i := rfl
          rw [e1, e2]
          simp [OD.setPrev, OD.setNext, setLink_heap, Ne.symm hi0, hf0', hroot1]
  · have hmap : D.get? o.map k = none := by rw [I.map k, find?_snd_none hkL]; rfl
    cases last <;> simp [odMoveToEnd, dHash, hk, hmap]
  · cases last <;> simp [odMoveToEnd, dHash, hk]

end PyLean.CoreLibs.Coll
