import PyLean.BytesObj.Mem.Compare

/-!
`memoryview.hex`: the hexlify loops of `_Py_strhex_impl`, and the agreement of the two paths
of `memoryview_hex_impl` with `tobytes`.
-/

namespace PyLean.BytesObj.Mem

open PyLean

/-- Not a character `hexDigit` can produce. -/
def notHexChar (c : Char) : Prop :=
  ¬ (48 ≤ c.toNat ∧ c.toNat ≤ 57) ∧ ¬ (97 ≤ c.toNat ∧ c.toNat ≤ 102)

theorem hexDigit_range : ∀ d : Fin 16, (48 ≤ (hexDigit d.val).toNat ∧ (hexDigit d.val).toNat ≤ 57) ∨
    (97 ≤ (hexDigit d.val).toNat ∧ (hexDigit d.val).toNat ≤ 102) := by
  decide

theorem hexDigit_ne (d : Nat) (hd : d < 16) (c : Char) (hc : notHexChar c) : hexDigit d ≠ c := by
  intro e
  have := hexDigit_range ⟨d, hd⟩
  simp only at this
  rw [e] at this
  exact this.elim hc.1 hc.2

theorem filter_hexPair (l : List Nat) (c : Char) (hc : notHexChar c) (hl : ∀ x ∈ l, x < 256) :
    (l.flatMap hexPair).filter (· != c) = l.flatMap hexPair := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hx := hl x (by simp)
    have h1 := hexDigit_ne (x / 16) (by omega) c hc
    have h2 := hexDigit_ne (x % 16) (by omega) c hc
    simp only [List.flatMap_cons, List.filter_append, hexPair, List.append_cancel_left_eq,
      ih fun y hy => hl y (by simp [hy])]
    simp [h1, h2]

theorem filter_hexLeft (c : Char) (hc : notHexChar c) (k chunks : Nat) (l : List Nat)
    (hl : ∀ x ∈ l, x < 256) : (hexLeft c k chunks l).filter (· != c) = l.flatMap hexPair := by
  induction chunks generalizing l with
  | zero => exact filter_hexPair l c hc hl
  | succ n ih =>
    simp only [hexLeft, List.filter_append, List.filter_cons, bne_self_eq_false, Bool.false_eq_true,
      ↓reduceIte]
    rw [filter_hexPair _ c hc fun x hx => hl x (List.mem_of_mem_take hx),
      ih _ fun x hx => hl x (List.mem_of_mem_drop hx), ← List.flatMap_append, List.take_append_drop]

theorem filter_hexRight (c : Char) (hc : notHexChar c) (k chunks : Nat) (rl : List Nat)
    (hl : ∀ x ∈ rl, x < 256) :
    (hexRight c k chunks rl).filter (· != c) = rl.reverse.flatMap hexPair := by
  induction chunks generalizing rl with
  | zero => exact filter_hexPair _ c hc fun x hx => hl x (by simpa using hx)
  | succ n ih =>
    simp only [hexRight, List.filter_append, List.filter_cons, bne_self_eq_false, Bool.false_eq_true,
      ↓reduceIte]
    rw [ih _ fun x hx => hl x (List.mem_of_mem_drop hx),
      filter_hexPair _ c hc fun x hx => hl x (List.mem_of_mem_take (by simpa using hx)),
      ← List.flatMap_append, ← List.reverse_append, List.take_append_drop]

/-- `hex()`: two lower-case digits per byte; with a separator that is not a hex digit, taking
the separators out gives the same text, for either sign of `bytes_per_sep`, and any group
size. Pystrhex.c:80-134. Hypotheses: the argument is bytes, shorter than `sys.maxsize / 2`
(a type invariant of the store). -/
def HexGroups : Prop :=
  ∀ (arg : List Nat) (c : Char) (group : Int) (r : List Char),
    (∀ x ∈ arg, x < 256) → notHexChar c → strhexBody arg c group = .ok r →
    r.filter (· != c) = arg.flatMap hexPair

theorem hexGroups_proven : HexGroups := by
  intro arg c group r hb hc h
  unfold strhexBody at h
  dsimp only at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [Except.ok.injEq] at h
       subst h
       first
         | exact filter_hexPair _ c hc hb
         | exact filter_hexLeft c hc _ _ _ hb
         | (rw [filter_hexRight c hc _ _ _ (by simpa using hb), List.reverse_reverse]))

/-- A view with suboffsets is not C-contiguous by its flags, unless it has no dimensions. -/
theorem isC_no_subs (v : Buf) (h : (initFlags v).isC = true) (h0 : v.ndim ≠ 0) : v.suboffsets = none := by
  cases hsb : v.suboffsets with
  | none => rfl
  | some s =>
    exfalso
    simp only [initFlags, hsb, Option.isSome_some, ↓reduceIte, Flags.isC, Bool.or_false] at h
    split at h
    · rename_i hn
      exact h0 hn
    · split at h <;> simp at h
    · simp at h

/-- A true flag means contiguous: whenever `init_flags` reports C-contiguity, so does
`PyBuffer_IsContiguous`. -/
theorem isC_contig (v : Buf) (h : (initFlags v).isC = true) (hs : v.suboffsets = none) :
    pyBufferIsContiguous v 'C' = true := by
  simp only [initFlags, hs, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Flags.isC] at h
  split at h
  · rename_i hn
    simp only [pyBufferIsContiguous, hs, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    unfold isCContiguous
    split
    · rfl
    · split
      · rfl
      · rw [hn]
        rfl
  · rename_i hn
    simp only [pyBufferIsContiguous, hs, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    unfold isCContiguous
    split
    · rfl
    · split
      · rfl
      · rename_i st hst
        rw [hn]
        by_cases hm : mvContiguousNdim1 v = true
        · simp only [mvContiguousNdim1, hst, Option.getD_some, Bool.or_eq_true, beq_iff_eq] at hm
          have hnot : ¬ ((v.shape.getD []).getD 0 0 > 1 ∧ st.getD 0 0 ≠ v.itemsize) := by
            rcases hm with h | h
            · rw [h]; omega
            · intro ⟨_, h2⟩; exact h2 h
          simp only [cLoop, hnot, ↓reduceIte]
        · simp [hm] at h
  · simpa [pyBufferIsContiguous, hs] using h

/-- `m.hex(sep, n)` is `m.tobytes().hex(sep, n)`, for every view with no suboffsets or with
them, contiguous or not: the two paths of `memoryview_hex_impl` (:2425-2433, :2435-2452) are
one behaviour. Hypotheses: `self` is live, its flags are those `init_flags` computes, and a
0-dim view has no suboffsets (type invariants, restated because the model keeps the fields
apart). -/
def HexIsTobytes : Prop :=
  ∀ (st : St) (self : Nat) (sep : Option Obj) (bps : Int) (b : List Nat),
    (∀ r rel, sep ≠ some (.lenLike r rel)) →
    baseInaccessible st self = false →
    (st.mv self).flags.isC = (initFlags (st.mv self).view).isC →
    ((st.mv self).view.ndim = 0 → (st.mv self).view.suboffsets = none) →
    memoryviewTobytes self none st = (.ok b, st) →
    (memoryviewHex self sep bps st).1 = strhexWithSep b sep bps

theorem strhexWithSepM_plain (arg : M (List Nat)) (sep : Option Obj) (bps : Int) (st : St) (b : List Nat)
    (hsep : ∀ r rel, sep ≠ some (.lenLike r rel)) (ha : (arg st).1 = .ok b) :
    (strhexWithSepM arg sep bps st).1 = strhexWithSep b sep bps := by
  unfold strhexWithSepM strhexWithSep
  split
  · rename_i r rel
    exact absurd rfl (hsep r rel)
  · simp only [M.bind_app, M.lift]
    cases h : strhexSep sep bps with
    | error e => rfl
    | ok p =>
      obtain ⟨c, g⟩ := p
      simp only [bind, Except.bind]
      rcases hx : arg st with ⟨r, s⟩
      rw [hx] at ha
      simp only at ha
      subst ha
      rfl

theorem withExport_fst {α : Type} (i : Nat) (x : M α) (st : St) :
    (withExport i x st).1 =
      (x (st.setMv i { st.mv i with exports := (st.mv i).exports + 1 })).1 := by
  unfold withExport
  simp only

theorem hexIsTobytes_proven : HexIsTobytes := by
  intro st self sep bps b hsep hl hflags h0 ht
  have htb : pyBufferToContiguous st.mem (st.mv self).view (st.mv self).view.len 'C' = .ok b := by
    simp only [memoryviewTobytes, M.bind_app, checkReleased_ok _ _ hl, M.pure_app, M.get, M.lift,
      parseOrder] at ht
    generalize pyBufferToContiguous st.mem (st.mv self).view (st.mv self).view.len 'C' = r at ht
    cases r <;> simp_all
  by_cases hC : (st.mv self).flags.isC = true
  · have hs : (st.mv self).view.suboffsets = none := by
      rw [hflags] at hC
      cases hsb : (st.mv self).view.suboffsets with
      | none => rfl
      | some s =>
        exfalso
        simp only [initFlags, hsb, Option.isSome_some, ↓reduceIte, Flags.isC, Bool.or_false] at hC
        split at hC
        · rename_i hn
          rw [h0 hn] at hsb
          cases hsb
        · split at hC <;> simp at hC
        · simp at hC
    have hc := isC_contig _ (hflags ▸ hC) hs
    simp only [pyBufferToContiguous, hc, ne_eq, not_true_eq_false, ↓reduceIte, Except.ok.injEq] at htb
    rw [← htb]
    simp only [memoryviewHex, M.bind_app, checkReleased_ok _ _ hl, M.get, hC, ↓reduceIte, M.pure_app]
    rw [withExport_fst]
    exact strhexWithSepM_plain _ _ _ _ _ hsep rfl
  · simp only [memoryviewHex, M.bind_app, checkReleased_ok _ _ hl, M.get, hC, Bool.false_eq_true,
      ↓reduceIte, M.lift, htb]
    exact strhexWithSepM_plain _ _ _ _ _ hsep rfl

end PyLean.BytesObj.Mem
