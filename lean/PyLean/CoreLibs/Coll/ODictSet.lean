import PyLean.CoreLibs.Coll.ODictProps

/-!
`OrderedDict.__setitem__` keeps the list invariant: a new key gets a new link at the end, an
existing key keeps its place.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace PyLean.CoreLibs.Coll

open PyLean

variable {κ ν : Type} [DecidableEq κ]

@[simp] theorem setLink_heap (o : OD κ ν) (i : Nat) (f : OLink κ → OLink κ) (x : Nat) :
    (o.setLink i f).heap x = if x = i then f (o.heap x) else o.heap x := rfl

@[simp] theorem setLink_next (o : OD κ ν) (i : Nat) (f : OLink κ → OLink κ) : (o.setLink i f).next = o.next := rfl
@[simp] theorem setLink_d (o : OD κ ν) (i : Nat) (f : OLink κ → OLink κ) : (o.setLink i f).d = o.d := rfl
@[simp] theorem setLink_map (o : OD κ ν) (i : Nat) (f : OLink κ → OLink κ) : (o.setLink i f).map = o.map := rfl

theorem mem_set_iff (d : D κ ν) (key k : κ) (v : ν) : D.mem (D.set d key v) k = (decide (key = k) || D.mem d k) := by
  unfold D.mem; rw [D.get?_set]; by_cases h : key = k <;> simp [h]

theorem find?_snd_none {L : List (Nat × κ)} {k : κ} (h : k ∉ L.map (·.2)) : L.find? (·.2 = k) = none := by
  rw [List.find?_eq_none]
  intro x hx hxe
  apply h
  simp only [decide_eq_true_eq] at hxe
  rw [← hxe]
  exact List.mem_map_of_mem hx

/-- The links after `__setitem__` adds `key`: the new link `o.next` after `last`. -/
def addLink (o : OD κ ν) (last : Nat) (key : κ) : OD κ ν :=
  ((({ o with map := D.set o.map key o.next, next := o.next + 1 } : OD κ ν).setLink o.next
    fun _ => ⟨some key, some last, some 0⟩).setNext last o.next).setPrev 0 o.next

theorem addLink_heap (o : OD κ ν) (last : Nat) (key : κ) (hid0 : o.next ≠ 0) (hne : last ≠ o.next) (x : Nat) :
    (addLink o last key).heap x =
      if x = 0 then { (if 0 = last then { (o.heap 0) with next := some o.next } else o.heap 0) with prev := some o.next }
      else if x = last then { (o.heap x) with next := some o.next }
      else if x = o.next then ⟨some key, some last, some 0⟩ else o.heap x := by
  simp only [addLink, OD.setPrev, OD.setNext, setLink_heap]
  by_cases hx0 : x = 0
  · subst hx0
    by_cases h0 : (0 : Nat) = last
    · subst h0; simp [Ne.symm hid0]
    · simp [h0, Ne.symm hid0, Ne.symm h0]
  · by_cases hxl : x = last
    · subst hxl; simp [hx0, hne]
    · by_cases hxi : x = o.next
      · subst hxi; simp [hx0, hxl, Ne.symm hxl]
      · simp [hx0, hxl, hxi]

/-- **`od[k] = v` keeps the list invariant.** For every key type with a hashable `key`: a key already
in the dict keeps its link and place (only the value changes); a new key gets the new link `o.next`
at the end of the list, so iteration order is insertion order. -/
def ODSetInv : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] (K : KOps κ) (o : OD κ ν) (L : List (Nat × κ)) (key : κ) (value : ν),
    ODInv o L → K.hash key = .ok () →
    ∃ o', odSet K o key value = .ok o' ∧
      ODInv o' (if key ∈ L.map (·.2) then L else L ++ [(o.next, key)]) ∧ D.get? o'.d key = some value

theorem odSetInv_proven : ODSetInv := by
  intro κ ν _ K o L key value I hk
  have hmem := I.mem key
  by_cases hin : key ∈ L.map (·.2)
  · have hm : D.mem o.d key = true := by rw [hmem]; simp [hin]
    refine ⟨{ o with d := D.set o.d key value }, ?_, ?_, ?_⟩
    · simp [odSet, dMem_ok o.d hk, hm, dSet_ok o.d value hk]
    · rw [if_pos hin]
      refine ⟨I.chain, I.root, I.ids, I.keys, I.pos, I.len, I.map, fun k => ?_, D.WF_set I.wfd _ _, I.wfm⟩
      show D.mem (D.set o.d key value) k = _
      rw [mem_set_iff, I.mem k]
      by_cases h : key = k
      · subst h; simp [hin]
      · simp [h]
    · show D.get? (D.set o.d key value) key = _
      rw [D.get?_set]; simp
  · have hm : D.mem o.d key = false := by rw [hmem]; simp [hin]
    have hid0 : o.next ≠ 0 := by have := I.len; omega
    have hidL : o.next ∉ L.map (·.1) := fun h => by have := (I.pos _ h).2; omega
    have hlast : (o.heap 0).prev.getD 0 = lastOf 0 L := by rw [I.root]; rfl
    have hlastMem : L ≠ [] → lastOf 0 L ∈ L.map (·.1) := fun h => lastOf_mem h
    have hlastNe : lastOf 0 L ≠ o.next := by
      by_cases hL : L = []
      · subst hL; exact Ne.symm hid0
      · intro he; apply hidL; rw [← he]; exact hlastMem hL
    have hh := addLink_heap o (lastOf 0 L) key hid0 hlastNe
    refine ⟨{ addLink o (lastOf 0 L) key with d := D.set o.d key value }, ?_, ?_, ?_⟩
    · simp only [odSet, dMem_ok o.d hk, hm, ok_bind, Bool.not_false, if_true, dSet_ok o.map _ hk, OD.link, hlast,
        pure_py, OD.setPrev, OD.setNext, setLink_d, dSet_ok o.d value hk]
      rfl
    · rw [if_neg hin]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, D.WF_set I.wfm _ _⟩
      · show Chain (addLink o (lastOf 0 L) key).heap 0 (L ++ [(o.next, key)]) 0
        rw [chain_append]
        refine ⟨?_, ?_⟩
        · refine chain_retarget L 0 0 o.next I.ids I.chain ?_ ?_
          · intro x hx hne
            have hx0 : x ≠ 0 := Nat.pos_iff_ne_zero.1 (I.pos x hx).1
            have hxi : x ≠ o.next := fun h => hidL (by rw [← h]; exact hx)
            rw [hh x]; simp [hx0, hne, hxi]
          · intro hL
            have hl0 : lastOf 0 L ≠ 0 := Nat.pos_iff_ne_zero.1 (I.pos _ (hlastMem hL)).1
            rw [hh (lastOf 0 L)]; simp [hl0]
        · show (addLink o (lastOf 0 L) key).heap o.next = _ ∧ True
          refine ⟨?_, trivial⟩
          rw [hh o.next]; simp [hid0, Ne.symm hlastNe]; rfl
      · show (addLink o (lastOf 0 L) key).heap 0 = _
        rw [hh 0]
        simp only [if_true]
        by_cases hL : L = []
        · subst hL
          simp only [show lastOf 0 ([] : List (Nat × κ)) = 0 from rfl, if_true, I.root]
          rfl
        · have hl0 : (0 : Nat) ≠ lastOf 0 L := fun h => by
            have := (I.pos _ (hlastMem hL)).1; omega
          simp only [hl0, if_false, I.root]
          have h1 : lastOf 0 (L ++ [(o.next, key)]) = o.next := by simp [lastOf]
          have h2 : nxt (L ++ [(o.next, key)]) 0 = nxt L 0 := by
            cases L with
            | nil => exact absurd rfl hL
            | cons a t => rfl
          rw [h1, h2]
      · simp only [List.map_append, List.map_cons, List.map_nil]
        refine List.nodup_append.2 ⟨I.ids, (by simp), ?_⟩
        intro a ha b hb he; simp at hb; subst hb; subst he; exact hidL ha
      · simp only [List.map_append, List.map_cons, List.map_nil]
        refine List.nodup_append.2 ⟨I.keys, (by simp), ?_⟩
        intro a ha b hb he; simp at hb; subst hb; subst he; exact hin ha
      · intro x hx
        simp only [List.map_append, List.mem_append, List.map_cons, List.map_nil, List.mem_singleton] at hx
        rcases hx with hx | hx
        · have := I.pos x hx; exact ⟨this.1, by show x < o.next + 1; omega⟩
        · subst hx; exact ⟨Nat.pos_of_ne_zero hid0, by show o.next < o.next + 1; omega⟩
      · show (L ++ [(o.next, key)]).length < o.next + 1
        have := I.len; simp; omega
      · intro k
        show D.get? (D.set o.map key o.next) k = _
        rw [D.get?_set, List.find?_append]
        by_cases h : key = k
        · subst h; simp [find?_snd_none hin]
        · rw [if_neg h, I.map k]
          cases hf : L.find? (·.2 = k) with
          | some x => simp
          | none => simp [h]
      · intro k
        show D.mem (D.set o.d key value) k = _
        rw [mem_set_iff, I.mem k]
        by_cases h : key = k
        · subst h; simp
        · simp [h, Ne.symm h]
      · exact D.WF_set I.wfd _ _
    · show D.get? (D.set o.d key value) key = _
      rw [D.get?_set]; simp

end PyLean.CoreLibs.Coll
