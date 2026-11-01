import PyLean.BytesObj.Mem.Contents

/-!
`memoryview` comparison: `==` against `!=`, the fast native path against the `struct` path,
and reflexivity for every shape.
-/

namespace PyLean.BytesObj.Mem

open PyLean

/-- `==`, `!=` and the orderings are one computation: `!=` is the negation of `==` in every
state, with the same effects, and an ordering is `NotImplemented` with no effect
(memory_richcompare, :3109-3110, :3180-3190). -/
def CmpEqNe : Prop :=
  ∀ (st : St) (v : Nat) (w : Obj),
    (memoryRichcompare v w .ne st).2 = (memoryRichcompare v w .eq st).2 ∧
    (memoryRichcompare v w .ne st).1 = (Option.map (fun b => !b)) <$> (memoryRichcompare v w .eq st).1 ∧
    memoryRichcompare v w .other st = (.ok none, st)

theorem cmpEqNe_proven : CmpEqNe := by
  intro st v w
  have hne : memoryRichcompare v w .ne st =
      (match memoryRichEqual v w st with
       | (.ok e, s) => (.ok (e.map fun b => !b), s)
       | (.error x, s) => (.error x, s)) := by
    simp only [memoryRichcompare, M.bind_app, reduceCtorEq, ↓reduceIte, M.pure_app]
    rcases memoryRichEqual v w st with ⟨r, s⟩
    cases r <;> rfl
  have heq : memoryRichcompare v w .eq st =
      (match memoryRichEqual v w st with
       | (.ok e, s) => (.ok e, s)
       | (.error x, s) => (.error x, s)) := by
    simp only [memoryRichcompare, M.bind_app, reduceCtorEq, ↓reduceIte, M.pure_app]
    rcases memoryRichEqual v w st with ⟨r, s⟩
    cases r with
    | error x => rfl
    | ok e => cases e <;> rfl
  rw [hne, heq]
  refine ⟨?_, ?_, ?_⟩
  · rcases memoryRichEqual v w st with ⟨r, s⟩
    cases r <;> rfl
  · rcases memoryRichEqual v w st with ⟨r, s⟩
    cases r <;> rfl
  · simp only [memoryRichcompare, M.bind_app, ↓reduceIte, M.pure_app]

/-- The comparison with a released view is identity and a non-buffer is `NotImplemented`
(:3113-3116, :3119-3130), for all states. -/
def CmpSpecialCases : Prop :=
  ∀ (st : St) (v i : Nat),
    (baseInaccessible st v = true →
      (memoryRichEqual v (.view v) st).1 = .ok (some true) ∧
      (∀ b r, (memoryRichEqual v (.exporter (.val b) r) st).1 = .ok (some false))) ∧
    (baseInaccessible st v = false → baseInaccessible st i = true →
      (memoryRichEqual v (.view i) st).1 = .ok (some (i == v))) ∧
    (baseInaccessible st v = false → ∀ n,
      (memoryRichEqual v (.int n) st).1 = .ok none ∧ (memoryRichEqual v .none st).1 = .ok none)

theorem cmpSpecialCases_proven : CmpSpecialCases := by
  intro st v i
  refine ⟨fun h => ⟨?_, fun b r => ?_⟩, fun h1 h2 => ?_, fun h n => ⟨?_, ?_⟩⟩
  all_goals simp [memoryRichEqual, M.bind_app, M.get, M.pure_app, *]

theorem unpackCmp_refl (m : Mem) (p : Int) (c : Char) (h : nativeChar c = true)
    (hf : c ≠ 'f' ∧ c ≠ 'd' ∧ c ≠ 'e') : unpackCmpNative m p p c = .ok true := by
  unfold nativeChar at h
  split at h
  all_goals first
    | (simp only [unpackCmpNative, beq_self_eq_true]; done)
    | (exfalso; simp at hf; done)
    | (simp at h; done)

theorem unpackCmp_none (m : Mem) (p q : Int) (c : Char) :
    unpackCmp m p q c none = unpackCmpNative m p q c := by
  unfold unpackCmp
  split <;> simp_all

theorem cmpBase_refl (m : Mem) (c : Char) (d : Int) (subs : Option (List Int))
    (hc : ∀ p, unpackCmpNative m p p c = .ok true) (n : Nat) (p : Int) :
    cmpBase m c none d d subs subs n p p = .ok true := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    simp only [cmpBase, unpackCmp_none, hc, bind, Except.bind, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, ih]

theorem cmpLoop_refl (d : Int) (body : Int → Int → Py Bool) (hb : ∀ p, body p p = .ok true) (n : Nat)
    (p : Int) : cmpLoop d d body n p p = .ok true := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    simp only [cmpLoop, bind, Except.bind, hb, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ih]

theorem cmpRec_refl (m : Mem) (c : Char) (hc : ∀ p, unpackCmpNative m p p c = .ok true)
    (sh st : List Int) (subs : Option (List Int)) (p : Int) :
    cmpRec m c none sh st subs st subs p p = .ok true := by
  induction sh generalizing st subs p with
  | nil => simp only [cmpRec]
  | cons n xs ih =>
    match xs, ih with
    | [], _ => simp only [cmpRec]; exact cmpBase_refl m c _ subs hc _ _
    | x :: xs, ih =>
      simp only [cmpRec]
      exact cmpLoop_refl _ (fun p' q' => cmpRec m c none (x :: xs) (st.drop 1) (subTail subs) (st.drop 1)
        (subTail subs) (adjustPtr m p' subs 0) (adjustPtr m q' subs 0)) (fun q => ih _ _ _) _ _

theorem nativeChar_of_fmtchar (f : List Char) (c : Char) (size : Int)
    (h : getNativeFmtchar f = some (c, size)) : nativeChar c = true := by
  unfold getNativeFmtchar at h
  split at h <;>
    (simp at h; obtain ⟨⟨hp, -⟩, rfl, -⟩ := h; exact (fmtSize_pos_iff _).1 hp)

/-- `m == m` for every view of a native format other than `f`, `d`, `e`, of any shape,
strides and suboffsets: `v == w` is "equal `tolist()`", and the floats are excepted because
of NaN (Doc/library/stdtypes.rst, `memoryview.__eq__`). Hypotheses: a live view whose shape
array has `ndim` entries. -/
def CmpReflexive : Prop :=
  ∀ (st : St) (self : Nat) (c : Char) (size : Int) (sh : List Int),
    baseInaccessible st self = false →
    getNativeFmtchar ((st.mv self).view.format.getD []) = some (c, size) →
    c ≠ 'f' → c ≠ 'd' → c ≠ 'e' →
    (st.mv self).view.shape.getD [] = sh → sh.length = (st.mv self).view.ndim →
    memoryRichcompare self (.view self) .eq st = (.ok (some true), st)

theorem cmpReflexive_proven : CmpReflexive := by
  intro st self c size sh hl hf h1 h2 h3 hsh hn
  have hnat := nativeChar_of_fmtchar _ _ _ hf
  have hc : ∀ p, unpackCmpNative st.mem p p c = .ok true := fun p =>
    unpackCmp_refl st.mem p c hnat ⟨h1, h2, h3⟩
  have hs : equivShape (st.mv self).view (st.mv self).view = true := by
    simp only [equivShape, beq_self_eq_true, Bool.true_and, hsh]
    rw [← hn, List.take_length]
    exact shapeLoop_refl sh
  have hcmp : compareBufs st.mem (st.mv self).view (st.mv self).view = .ok true := by
    have h_ : c ≠ '_' := by
      intro e
      rw [e] at hnat
      exact absurd hnat (by decide)
    simp only [compareBufs, hs, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hf]
    simp only [h_, or_self, ne_eq, not_true_eq_false, ↓reduceIte]
    split
    · simp only [unpackCmp_none, hc]
    · split
      · exact cmpBase_refl _ _ _ _ hc _ _
      · exact cmpRec_refl _ _ hc _ _ _ _
  simp only [memoryRichcompare, memoryRichEqual, M.bind_app, M.get, hl, Bool.false_eq_true, ↓reduceIte,
    reduceCtorEq, M.lift, hcmp, M.pure_app, Option.map_some]

/-- The fast path of `unpack_cmp` gives what the `struct` path gives, for every native
format and all memory: `Struct(c)` compiles, and comparing its unpacked values is the
`switch` of `unpack_cmp` (:2979-3031). The source's only reason for having both is speed
(the comment at :2958-2963). -/
def CmpFastStruct : Prop :=
  ∀ (m : Mem) (p q : Int) (c : Char), nativeChar c = true →
    ∃ u, structGetUnpacker [c] (fmtSize c) = .ok u ∧
      unpackCmpNative m p q c = structUnpackCmp m p q u u

theorem sub_full (bs : List Nat) : sub bs 0 bs.length = bs := by
  simp [sub]

/-- One native code compiled by `Struct`, unpacked. -/
theorem structUnpackSingle_native (m : Mem) (p : Int) (c : Char) (k : Nat) (it : Int) (hk : k = it.toNat)
    (hc : c ≠ 's' ∧ c ≠ 'p') :
    structUnpackSingle m p ⟨⟨false, [(c, 1, k, 0)], k⟩, it⟩ =
      .ok [structItem false c (rdBytes m p k)] := by
  subst hk
  have hlen : (rdBytes m p it.toNat).length = it.toNat := rdBytes_length _ _ _
  have hsub : sub (rdBytes m p it.toNat) 0 it.toNat = rdBytes m p it.toNat := by
    simp only [sub, List.drop_zero]
    exact List.take_of_length_le (by omega)
  have hu : unpackCode false (rdBytes m p it.toNat) (c, 1, it.toNat, 0) =
      [structItem false c (rdBytes m p it.toNat)] := by
    unfold unpackCode
    split
    · rename_i h; simp only [Prod.mk.injEq] at h; exact absurd h.1 hc.1
    · rename_i h; simp only [Prod.mk.injEq] at h; exact absurd h.1 hc.2
    · rename_i heq
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
      simp [List.range_succ, hsub]
  simp only [structUnpackSingle, structUnpackFrom, hlen, Nat.lt_irrefl, ↓reduceIte, List.flatMap_cons,
    hu, List.flatMap_nil, List.append_nil]

theorem natCast_beq (a b : Nat) : (((a : Int) == (b : Int))) = (a == b) := by
  cases h : (a == b) with
  | true =>
    have := beq_iff_eq.1 h
    subst this
    simp
  | false =>
    have hne : a ≠ b := by
      intro e
      simp [e] at h
    have : (a : Int) ≠ b := by omega
    simp [this]

theorem decLE_one (m : Mem) (p : Int) : decLE (rdBytes m p 1) = rdByte m p := by
  simp [rdBytes, decLE]

macro "he_tac" : tactic => `(tactic| first
  | (simp [unpackCmpNative, structResultEq, structItem, itemEq, rdS, rdU, rdBytes_length, unpackToBool,
       natCast_beq, decLE_one];
     done)
  | (simp [unpackCmpNative, structResultEq, structItem, itemEq, rdS, rdU, rdBytes, decLE, unpackToBool];
     done))

theorem cmpFastStruct_proven : CmpFastStruct := by
  intro m p q c h
  have hg : ∀ (k : Nat) (hk : k = (fmtSize c).toNat) (hc : c ≠ 's' ∧ c ≠ 'p')
      (hu : structGetUnpacker [c] (fmtSize c) = .ok ⟨⟨false, [(c, 1, k, 0)], k⟩, fmtSize c⟩)
      (he : unpackCmpNative m p q c =
        .ok (structResultEq [structItem false c (rdBytes m p k)] [structItem false c (rdBytes m q k)])),
      ∃ u, structGetUnpacker [c] (fmtSize c) = .ok u ∧
        unpackCmpNative m p q c = structUnpackCmp m p q u u := by
    intro k hk hc hu he
    refine ⟨_, hu, ?_⟩
    simp only [structUnpackCmp, structUnpackSingle_native m _ c k _ hk hc, bind, Except.bind, pure,
      Except.pure]
    exact he
  unfold nativeChar at h
  split at h
  all_goals first
    | (exact hg 1 rfl (by decide) rfl (by he_tac))
    | (exact hg 2 rfl (by decide) rfl (by he_tac))
    | (exact hg 4 rfl (by decide) rfl (by he_tac))
    | (exact hg 8 rfl (by decide) rfl (by he_tac))
    | (simp at h)

end PyLean.BytesObj.Mem
