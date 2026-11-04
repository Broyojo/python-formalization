import PyLean.CoreLibs.Coll.ODictSet

/-!
`OrderedDict.__delitem__`, `pop` and `clear` keep the list invariant.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace PyLean.CoreLibs.Coll

open PyLean

variable {κ ν : Type} [DecidableEq κ]

/-- Redirect the `prev` of the first link of a chain. -/
theorem chain_resource {h h' : Nat → OLink κ} :
    ∀ (L : List (Nat × κ)) (p q n : Nat), (L.map (·.1)).Nodup → Chain h p L n →
      (∀ x ∈ L.map (·.1), x ≠ nxt L n → h' x = h x) →
      (L ≠ [] → h' (nxt L n) = { h (nxt L n) with prev := some q }) → Chain h' q L n
  | [], _, _, _, _, _, _, _ => trivial
  | (j, k) :: t, p, q, n, hnd, ⟨h1, h2⟩, hf, hl => by
    refine ⟨?_, chain_frame t j n ?_ h2⟩
    · have := hl (by simp)
      simp only [nxt] at this
      rw [this, h1]
    · intro x hx
      have hnd' := List.nodup_cons.1 (show (j :: t.map (·.1)).Nodup by simpa using hnd)
      exact hf x (by simp [hx]) (by
        simp only [nxt]
        intro he; rw [he] at hx; exact hnd'.1 hx)

theorem nxt_ne_zero {L : List (Nat × κ)} (hz : ∀ x ∈ L.map (·.1), x ≠ 0) (hL : L ≠ []) : nxt L 0 ≠ 0 := by
  cases L with
  | nil => exact absurd rfl hL
  | cons a t => exact hz a.1 (by simp)

theorem nxt_mem {L : List (Nat × κ)} (n : Nat) (hL : L ≠ []) : nxt L n ∈ L.map (·.1) := by
  cases L with
  | nil => exact absurd rfl hL
  | cons a t => simp [nxt]

theorem nxt_append (A B : List (Nat × κ)) (n : Nat) : nxt (A ++ B) n = if A = [] then nxt B n else nxt A n := by
  cases A <;> rfl

theorem lastOf_append (A B : List (Nat × κ)) (p : Nat) :
    lastOf p (A ++ B) = if B = [] then lastOf p A else lastOf p B := by
  by_cases hB : B = []
  · subst hB; simp
  · rw [if_neg hB]
    simp only [lastOf, List.getLast?_append]
    have : B.getLast? = some (B.getLast hB) := List.getLast?_eq_getLast _
    simp [this]

/-- The links after unlinking `link` and clearing its pointers. -/
theorem dropLink_heap (o : OD κ ν) (link lp ln : Nat) (hp : (o.heap link).prev = some lp)
    (hn : (o.heap link).next = some ln) (x : Nat) (hxl : x ≠ link) :
    (odDropLink o link).heap x =
      if x = ln then { (if x = lp then { (o.heap x) with next := some ln } else o.heap x) with prev := some lp }
      else if x = lp then { (o.heap x) with next := some ln } else o.heap x := by
  simp only [odDropLink, OD.link, hp, hn, Option.getD_some, OD.setPrev, OD.setNext, setLink_heap, hxl, if_false]

/-- **`del od[key]` and `od.pop(key)` keep the list invariant, dropping exactly that link.** For every
key type with a hashable `key` at a place `A ++ (i, key) :: B` of the list: `del od[key]` leaves the list
`A ++ B` (the others keep their order), and `od.pop(key)` (with or without a default) returns its value
and leaves the same; an absent key is `KeyError(key)` for `del` and for `pop` without a default, and
`pop` with a default returns it with `od` unchanged.

Source: Lib/collections/__init__.py:133-144, :245-265; Doc/library/collections.rst ('the order of the
remaining items'). -/
def ODDelInv : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] (K : KOps κ) (rk : κ → String) (o : OD κ ν) (A B : List (Nat × κ)) (i : Nat)
    (key : κ), ODInv o (A ++ (i, key) :: B) → K.hash key = .ok () →
    (∃ o', odDel K rk o key = .ok o' ∧ ODInv o' (A ++ B)) ∧
    (∀ dflt, ∃ v o', odPop K rk o key dflt = .ok (v, o') ∧ D.get? o.d key = some v ∧ ODInv o' (A ++ B))

theorem del_core (K : KOps κ) (o : OD κ ν) (A B : List (Nat × κ)) (i : Nat) (key : κ)
    (I : ODInv o (A ++ (i, key) :: B)) :
    ODInv (odDropLink { o with d := D.del o.d key, map := D.del o.map key } i) (A ++ B) := by
  have hch := I.chain
  rw [chain_append] at hch
  obtain ⟨hA, hi, hB⟩ := hch
  simp only [nxt] at hA
  have hpos := I.pos
  have hids : (A.map (·.1) ++ i :: B.map (·.1)).Nodup := by simpa using I.ids
  have hkeys : (A.map (·.2) ++ key :: B.map (·.2)).Nodup := by simpa using I.keys
  have hiA : i ∉ A.map (·.1) := fun h => (List.nodup_append.1 hids).2.2 i h i (by simp) rfl
  have hiB : i ∉ B.map (·.1) := (List.nodup_cons.1 (List.nodup_append.1 hids).2.1).1
  have hBnd : (B.map (·.1)).Nodup := (List.nodup_cons.1 (List.nodup_append.1 hids).2.1).2
  have hAB : ∀ a ∈ A.map (·.1), ∀ b ∈ B.map (·.1), a ≠ b := fun a ha b hb =>
    (List.nodup_append.1 hids).2.2 a ha b (by simp [hb])
  have hz : ∀ x ∈ (A ++ (i, key) :: B).map (·.1), x ≠ 0 := fun x hx => Nat.pos_iff_ne_zero.1 (hpos x hx).1
  have hzA : ∀ x ∈ A.map (·.1), x ≠ 0 := fun x hx => hz x (by
    simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons]; exact Or.inl hx)
  have hzB : ∀ x ∈ B.map (·.1), x ≠ 0 := fun x hx => hz x (by
    simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons]; exact Or.inr (Or.inr hx))
  have hi0 : i ≠ 0 := hz i (by simp)
  obtain ⟨lp, hlpdef⟩ : ∃ lp, lp = lastOf 0 A := ⟨_, rfl⟩
  obtain ⟨ln, hlndef⟩ : ∃ ln, ln = nxt B 0 := ⟨_, rfl⟩
  have hlpA : A ≠ [] → lp ∈ A.map (·.1) := fun h => hlpdef ▸ lastOf_mem h
  have hlp0 : A = [] → lp = 0 := by intro h; subst h; exact hlpdef
  have hlnB : B ≠ [] → ln ∈ B.map (·.1) := fun h => hlndef ▸ nxt_mem 0 h
  have hln0 : B = [] → ln = 0 := by intro h; subst h; exact hlndef
  have hlpi : lp ≠ i := by
    by_cases h : A = []
    · rw [hlp0 h]; exact Ne.symm hi0
    · intro he; exact hiA (he ▸ hlpA h)
  have hlni : ln ≠ i := by
    by_cases h : B = []
    · rw [hln0 h]; exact Ne.symm hi0
    · intro he; exact hiB (he ▸ hlnB h)
  have hlpln : A ≠ [] → lp ≠ ln := by
    intro hA' he
    by_cases hB' : B = []
    · exact hzA lp (hlpA hA') (by rw [he, hln0 hB'])
    · exact hAB lp (hlpA hA') ln (hlnB hB') he
  have hp : (({ o with d := D.del o.d key, map := D.del o.map key } : OD κ ν).heap i).prev = some lp := by
    show (o.heap i).prev = _; rw [hi, hlpdef]
  have hn : (({ o with d := D.del o.d key, map := D.del o.map key } : OD κ ν).heap i).next = some ln := by
    show (o.heap i).next = _; rw [hi, hlndef]
  have hh := dropLink_heap ({ o with d := D.del o.d key, map := D.del o.map key } : OD κ ν) i lp ln hp hn
  have hroot : o.heap 0 = ⟨none, some (if B = [] then i else lastOf 0 B), some (if A = [] then i else nxt A 0)⟩ := by
    rw [I.root, lastOf_append, nxt_append]
    have h1 : lastOf 0 ((i, key) :: B) = if B = [] then i else lastOf 0 B := by
      cases B with
      | nil => rfl
      | cons b B' => simp only [List.cons_ne_nil, if_false]; exact lastOf_cons 0 0 _ _ |>.trans (by
          simp [lastOf, List.getLast?_cons_cons])
    rw [h1]
    by_cases hA' : A = [] <;> simp [hA', nxt]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [chain_append]
    refine ⟨?_, ?_⟩
    · rw [← hlndef]
      refine chain_retarget A 0 i ln (List.nodup_append.1 hids).1 hA ?_ ?_
      · intro x hx hne
        have hxi : x ≠ i := fun h => hiA (h ▸ hx)
        have hxln : x ≠ ln := by
          by_cases hB' : B = []
          · rw [hln0 hB']; exact hzA x hx
          · exact hAB x hx ln (hlnB hB')
        have hne' : x ≠ lp := by rw [hlpdef]; exact hne
        rw [hh x hxi]; simp [hxln, hne']
      · intro hA'
        rw [← hlpdef, hh lp hlpi]
        simp [hlpln hA']
    · rw [← hlpdef]
      refine chain_resource B i lp 0 hBnd hB ?_ ?_
      · intro x hx hne
        have hxi : x ≠ i := fun h => hiB (h ▸ hx)
        have hxlp : x ≠ lp := by
          by_cases hA' : A = []
          · rw [hlp0 hA']; exact hzB x hx
          · exact fun h => hAB lp (hlpA hA') x hx h.symm
        have hne' : x ≠ ln := by rw [hlndef]; exact hne
        rw [hh x hxi]; simp [hne', hxlp]
      · intro hB'
        rw [← hlndef, hh ln hlni]
        by_cases hA' : A = []
        · have h0 : ln ≠ 0 := hlndef ▸ nxt_ne_zero hzB hB'
          have : ln ≠ lp := by rw [hlp0 hA']; exact h0
          simp [this]
        · simp [Ne.symm (hlpln hA')]
  · show (odDropLink { o with d := D.del o.d key, map := D.del o.map key } i).heap 0 = _
    rw [hh 0 (Ne.symm hi0), lastOf_append, nxt_append]
    show (if (0 : Nat) = ln then { (if (0 : Nat) = lp then { (o.heap 0) with next := some ln } else o.heap 0) with prev := some lp }
      else if (0 : Nat) = lp then { (o.heap 0) with next := some ln } else o.heap 0) = _
    rw [hroot]
    by_cases hA' : A = [] <;> by_cases hB' : B = []
    · simp [hA', hB', hlp0 hA', hln0 hB', lastOf, nxt]
    · have h0 : (0 : Nat) ≠ ln := fun h => (hlndef ▸ nxt_ne_zero hzB hB') h.symm
      simp [hA', hB', hlp0 hA', h0, ← hlndef]
    · have h0 : (0 : Nat) ≠ lp := fun h => hzA lp (hlpA hA') h.symm
      simp [hA', hB', hln0 hB', h0, ← hlpdef]
    · have h1 : (0 : Nat) ≠ ln := fun h => (hlndef ▸ nxt_ne_zero hzB hB') h.symm
      have h2 : (0 : Nat) ≠ lp := fun h => hzA lp (hlpA hA') h.symm
      simp [hA', hB', h1, h2]
  · simpa using List.nodup_append.2 ⟨(List.nodup_append.1 hids).1, hBnd, fun a ha b hb => hAB a ha b hb⟩
  · have h1 := List.nodup_append.1 hkeys
    simpa using List.nodup_append.2 ⟨h1.1, (List.nodup_cons.1 h1.2.1).2,
      fun a ha b hb => h1.2.2 a ha b (by simp [hb])⟩
  · intro x hx
    apply hpos x
    simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons] at hx ⊢
    rcases hx with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · have := I.len; simp at this ⊢; show A.length + B.length < o.next; omega
  · intro k
    show D.get? (D.del o.map key) k = _
    rw [D.get?_del I.wfm, I.map k, List.find?_append, List.find?_append]
    have hkA : key ∉ A.map (·.2) := fun h => (List.nodup_append.1 hkeys).2.2 key h key (by simp) rfl
    have hkB : key ∉ B.map (·.2) := (List.nodup_cons.1 (List.nodup_append.1 hkeys).2.1).1
    by_cases hk : key = k
    · subst hk
      simp [find?_snd_none hkA, find?_snd_none hkB]
    · simp [hk, List.find?_cons]
  · intro k
    show D.mem (D.del o.d key) k = _
    have hm := I.mem k
    unfold D.mem at hm ⊢
    rw [D.get?_del I.wfd]
    have hkA : key ∉ A.map (·.2) := fun h => (List.nodup_append.1 hkeys).2.2 key h key (by simp) rfl
    have hkB : key ∉ B.map (·.2) := (List.nodup_cons.1 (List.nodup_append.1 hkeys).2.1).1
    by_cases hk : key = k
    · subst hk
      simp [hkA, hkB]
    · simp only [hk, if_false, hm]; simp [Ne.symm hk]
  · exact D.WF_del I.wfd key
  · exact D.WF_del I.wfm key

theorem odDelInv_proven : ODDelInv := by
  intro κ ν _ K rk o A B i key I hk
  have hin : key ∈ (A ++ (i, key) :: B).map (·.2) := by simp
  have hm : D.mem o.d key = true := by rw [I.mem key]; simp
  have hkeys := I.keys
  have hmap : D.get? o.map key = some i := by
    rw [I.map key, List.find?_append]
    have hkA : key ∉ A.map (·.2) := fun h => by
      have := List.nodup_append.1 (by simpa using hkeys)
      exact this.2.2 key h key (by simp) rfl
    simp [find?_snd_none hkA]
  have hcore := del_core K o A B i key I
  refine ⟨⟨_, ?_, hcore⟩, fun dflt => ?_⟩
  · simp only [odDel, dictDelitem, dHash_ok hk, ok_bind, hm, if_true, pure_py, hmap, Option.getD_some]
  · obtain ⟨v, hv⟩ : ∃ v, D.get? o.d key = some v := Option.isSome_iff_exists.1 hm
    refine ⟨v, _, ?_, hv, hcore⟩
    have hne : o.d.isEmpty = false := by
      cases hd : o.d with
      | nil => rw [hd] at hv; simp [D.get?] at hv
      | cons a t => rfl
    simp only [odPop, hne, Bool.not_false, if_true, dHash_ok hk, ok_bind, hv, hmap, Option.getD_some, pure_py]

/-- **`clear()` empties the list.** For every instance satisfying the invariant, `od.clear()` leaves
the root pointing at itself, `__map` and the dict empty: the invariant with the empty list.

Source: Lib/collections/__init__.py:164-169. -/
def ODClearInv : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] (o : OD κ ν) (L : List (Nat × κ)), ODInv o L → ODInv (odClear o) []

theorem odClearInv_proven : ODClearInv := by
  intro κ ν _ o L I
  refine ⟨trivial, ?_, by simp, by simp, by simp, ?_, fun k => rfl, fun k => rfl, D.WF_nil, D.WF_nil⟩
  · show (((o.setPrev 0 0).setNext 0 0).heap 0) = _
    simp only [OD.setNext, OD.setPrev, setLink_heap, if_true]
    rw [I.root]; rfl
  · show 0 < ((o.setPrev 0 0).setNext 0 0).next
    have := I.len; simp [OD.setNext, OD.setPrev]; omega

end PyLean.CoreLibs.Coll
