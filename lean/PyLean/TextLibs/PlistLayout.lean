import PyLean.TextLibs.PlistWriteObj

/-! The file `_BinaryPlistWriter.write` produces: the objects one after the other, the offset
table, the trailer. -/

namespace PyLean.TextLibs.Plist

open PyLean PyLean.TextLibs

theorem drop_objlist (l : List Nat) (j c : Nat) (cs : List Nat) (h : c :: cs = l.drop j) :
    l[j]? = some c ∧ cs = l.drop (j + 1) := by
  have h1 : (l.drop j)[0]? = some c := by rw [← h]; rfl
  rw [List.getElem?_drop, Nat.add_zero] at h1
  refine ⟨h1, ?_⟩
  have : (l.drop j).drop 1 = cs := by rw [← h]; rfl
  rw [List.drop_drop] at this
  rw [← this, Nat.add_comm]

theorem writeAll_spec (r : Nat) (H : WHeap) (cfg : WCfg) (refSize : Nat) (st : WState)
    (hI : WInv H st) (hnd : ∀ c us off, H.getD c .none ≠ .date us off) :
    ∀ (cs : List Nat) (j : Nat) (offs out offs' body : List Nat),
      cs = st.objlist.drop j → writeAll r H cfg refSize st cs offs out = .ok (offs', body) →
      ∃ (encs : List (List Nat)) (os : List Obj), encs.length = cs.length ∧ os.length = cs.length ∧
        body = out ++ encs.flatten ∧ offs'.length = offs.length ∧
        (∀ i, i < j → offs'[i]? = offs[i]?) ∧
        (∀ k, k < cs.length → j + k < offs.length →
          offs'[j + k]? = some (8 + out.length + (encs.take k).flatten.length)) ∧
        (∀ k, k < cs.length → canon refSize (os.getD k .none) = some (encs.getD k []) ∧
          Rel H cfg st (cs.getD k 0) (os.getD k .none))
  | [], _, offs, out, offs', body, _, h => by
    simp only [writeAll, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], [], rfl, rfl, by simp, rfl, fun _ _ => rfl, by simp, by simp⟩
  | c :: cs, j, offs, out, offs', body, hcs, h => by
    obtain ⟨hcj, hcs'⟩ := drop_objlist st.objlist j c cs hcs
    simp only [writeAll, bind, Except.bind] at h
    cases hw : writeObjectR r H cfg refSize st c with
    | error e => rw [hw] at h; cases h
    | ok p =>
    rcases p with ⟨ref, e⟩
    rw [hw] at h
    simp only at h
    obtain ⟨hl, o, hco, hro⟩ := writeObject_spec r H cfg refSize st c ref e (hnd c) hw
    have hrefj : ref = j := by
      have := hI.2.2 j c hcj
      rw [hl] at this; cases this; rfl
    subst hrefj
    obtain ⟨encs, os, h1, h2, h3, h4, h5, h6, h7⟩ :=
      writeAll_spec r H cfg refSize st hI hnd cs (ref + 1) _ _ offs' body hcs' h
    refine ⟨e :: encs, o :: os, by simp [h1], by simp [h2], by rw [h3]; simp, by rw [h4]; simp, ?_, ?_, ?_⟩
    · intro i hi
      rw [h5 i (by omega), List.getElem?_set_ne (by omega)]
    · intro k hk hko
      cases k with
      | zero =>
        rw [Nat.add_zero, h5 ref (by omega), List.getElem?_set_self (by simpa using hko)]
        simp
      | succ k =>
        have := h6 k (by simp at hk; omega) (by simp at hko ⊢; omega)
        rw [show ref + (k + 1) = ref + 1 + k by omega, this]
        simp [Nat.add_assoc]
    · intro k hk
      cases k with
      | zero => exact ⟨hco, hro⟩
      | succ k => exact h7 k (by simp at hk; omega)

end PyLean.TextLibs.Plist
