import PyLean.TypeObj.StructSeqCProps

/-!
# `__reduce__` and `__replace__` stay in bounds while the size attributes are the type's own

The counterpart of `ReduceInBounds` and `ReplaceInBounds` (refuted): on a type whose three size
attributes still say what `PyStructSequence_NewType` stored (`HonestLayout`, the state
`NewTypeLayout` proves it builds), both functions only touch memory they own, for every object
the constructor leaves (`WellFormed`), every keyword set and every allocator outcome. So the only
way to the undefined behaviour of the refutations is Python code rebinding those attributes.
-/

namespace PyLean.TypeObj.StructSeq

open PyLean PyLean.UnicodeObj

variable {α β γ : Type}

/-- `Honest`, and `tp_members` holds the `n - u` named fields, with the unnamed ones visible. -/
def HonestLayout (t : CType) (v n u : Nat) : Prop :=
  Honest t v n u ∧ t.members.length = n - u ∧ u ≤ v

theorem isUB_bind {x : CRes β} {f : β → CRes γ} (hx : x.isUB = false)
    (hf : ∀ a, x = .ok a → (f a).isUB = false) : (x >>= f).isUB = false := by
  cases x with
  | ok a => exact hf a rfl
  | exc e => rfl
  | nullNoExc => rfl
  | ub w => simp [CRes.isUB] at hx

theorem isUB_ofPy {x : Py β} : (CRes.ofPy x).isUB = false := by
  cases x <;> rfl

theorem realSize_honest {t : CType} {v n u : Nat} (h : Honest t v n u) : realSize t v = n := by
  obtain ⟨_, hb, hv⟩ := h
  simp only [realSize, hb, obItemOff]
  omega

theorem fromArray_ok (slots : List (Slot α)) :
    ∀ k, (∀ i, i < k → ∃ a, slots[i]? = some (.val a)) → (fromArray slots k).isUB = false := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro h
    simp only [fromArray]
    apply isUB_bind (ih (fun i hi => h i (by omega)))
    intro xs _
    obtain ⟨a, ha⟩ := h k (by omega)
    have hk : k < slots.length := by
      rcases List.getElem?_eq_some_iff.mp ha with ⟨hk, _⟩; exact hk
    have hs : slots[k] = .val a := by
      rcases List.getElem?_eq_some_iff.mp ha with ⟨_, h2⟩; exact h2
    simp only [readSlot, dif_pos hk, CRes.bind_ok, hs, deref]
    rfl

theorem reduceLoop_ok (t : CType) (o : CObj α) (u n : Nat) (hm : t.members.length = n - u)
    (hw : ∀ i, i < n → ∃ a, o.slots[i]? = some (.val a)) :
    ∀ fuel i, u ≤ i → i + fuel ≤ n → (reduceLoop t o u fuel i).isUB = false := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _; rfl
  | succ fuel ih =>
    intro i hu hle
    simp only [reduceLoop]
    have hidx : ∃ b, memberName t.members ((i : Int) - u) "structseq_reduce: tp_members out of range" =
        .ok (.name b) := by
      unfold memberName
      rw [if_neg (show ¬ ((i : Int) - u < 0) by omega)]
      rw [dif_pos (show ((i : Int) - u).toNat < t.members.length by omega)]
      exact ⟨_, rfl⟩
    obtain ⟨b, hb⟩ := hidx
    rw [hb]
    simp only [CRes.bind_ok, fromCString]
    apply isUB_bind isUB_ofPy
    intro key _
    obtain ⟨a, ha⟩ := hw i (by omega)
    have hk : i < o.slots.length := by
      rcases List.getElem?_eq_some_iff.mp ha with ⟨hk, _⟩; exact hk
    have hs : o.slots[i] = .val a := by
      rcases List.getElem?_eq_some_iff.mp ha with ⟨_, h2⟩; exact h2
    simp only [readSlot, dif_pos hk, CRes.bind_ok, hs, deref]
    apply isUB_bind (ih (i + 1) (by omega) (by omega))
    intro _ _
    rfl

/-- `s.__reduce__()` never accesses memory out of bounds while the type's size attributes are
its own, for every object the constructor leaves. -/
def ReduceInBoundsHonest : Prop :=
  ∀ (α : Type) (t : CType) (v n u : Nat) (o : CObj α), HonestLayout t v n u → o.size = v →
    WellFormed t o → (reduceC t o).isUB = false

theorem reduceInBoundsHonest_proven : ReduceInBoundsHonest := by
  intro α t v n u o ⟨hH, hm, huv⟩ hsz hw
  have hrs := realSize_honest hH
  have hw' : ∀ i, i < n → ∃ a, o.slots[i]? = some (.val a) := by
    intro i hi; apply hw; rw [hsz, hrs]; exact hi
  obtain ⟨hd, hb, hv⟩ := hH
  unfold reduceC
  by_cases hu63 : u < 2 ^ 63
  case neg =>
    have hbig : sizeOrNull (getTypeAttrAsSize t.nameStr t.dict "n_unnamed_fields") =
        .exc (.overflowError "Python int too large to convert to C ssize_t") := by
      unfold getTypeAttrAsSize asSsize sizeOrNull
      rw [hd, honest_nunnamed]
      simp only
      rw [if_neg (by unfold ssizeMin ssizeMax; omega)]
    rw [hbig]; rfl
  have h3 : sizeOrNull (getTypeAttrAsSize t.nameStr t.dict "n_unnamed_fields") = .ok u :=
    sizeOf_small _ _ _ u (by rw [hd]; exact honest_nunnamed v n u) hu63
  rw [h3]
  simp only [CRes.bind_ok]
  apply isUB_bind (fromArray_ok o.slots o.size (fun i hi => hw' i (by omega)))
  intro tup _
  apply isUB_bind
  · rw [hsz, show realSize t v = n from realSize_honest ⟨hd, hb, hv⟩]
    exact reduceLoop_ok t o u n hm hw' (n - v) v huv (by omega)
  · intro _ _; rfl

theorem replaceCopyLoop_ok (self : CObj α) (n : Nat) (hw : ∀ i, i < n → ∃ a, self.slots[i]? = some (.val a)) :
    ∀ fuel i (res : List (Slot α)), i + fuel ≤ n → n ≤ res.length →
      (replaceCopyLoop self fuel i res).isUB = false := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _; rfl
  | succ fuel ih =>
    intro i res hle hres
    simp only [replaceCopyLoop]
    obtain ⟨a, ha⟩ := hw i (by omega)
    have hk : i < self.slots.length := by
      rcases List.getElem?_eq_some_iff.mp ha with ⟨hk, _⟩; exact hk
    have hs : self.slots[i] = .val a := by
      rcases List.getElem?_eq_some_iff.mp ha with ⟨_, h2⟩; exact h2
    simp only [readSlot, dif_pos hk, CRes.bind_ok, hs, deref, writeSlot, if_pos (show i < res.length by omega)]
    exact ih (i + 1) _ (by omega) (by simp; omega)

theorem replaceKwLoop_ok (t : CType) (self : CObj α) (n : Nat) (hm : t.members.length = n)
    (hw : ∀ i, i < n → ∃ a, self.slots[i]? = some (.val a)) :
    ∀ fuel i (res : List (Slot α)) (kws : List (Str × α)), i + fuel ≤ n → n ≤ res.length →
      (replaceKwLoop t self fuel i res kws).isUB = false := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _; rfl
  | succ fuel ih =>
    intro i res kws hle hres
    simp only [replaceKwLoop]
    have hidx : ∃ b, memberName t.members (i : Int) "structseq_replace: tp_members past the sentinel" =
        .ok (.name b) := by
      unfold memberName
      rw [if_neg (show ¬ ((i : Int) < 0) by omega)]
      rw [dif_pos (show (i : Int).toNat < t.members.length by omega)]
      exact ⟨_, rfl⟩
    obtain ⟨b, hb⟩ := hidx
    rw [hb]
    simp only [CRes.bind_ok, fromCString]
    apply isUB_bind isUB_ofPy
    intro key _
    obtain ⟨a, ha⟩ := hw i (by omega)
    have hk : i < self.slots.length := by
      rcases List.getElem?_eq_some_iff.mp ha with ⟨hk, _⟩; exact hk
    have hs : self.slots[i] = .val a := by
      rcases List.getElem?_eq_some_iff.mp ha with ⟨_, h2⟩; exact h2
    cases hp : popKw kws key with
    | mk got kws' =>
      simp only
      cases got with
      | some x =>
        simp only [CRes.pure_eq, CRes.bind_ok, writeSlot, if_pos (show i < res.length by omega)]
        exact ih (i + 1) _ _ (by omega) (by simp; omega)
      | none =>
        simp only [readSlot, dif_pos hk, CRes.bind_ok, hs, deref, writeSlot,
          if_pos (show i < res.length by omega)]
        exact ih (i + 1) _ _ (by omega) (by simp; omega)

/-- `copy.replace(s, **kws)` never accesses memory out of bounds while the type's size
attributes are its own, for every object the constructor leaves, every keyword set and every
allocator outcome; the type has fewer than `2^57` fields, as in `NewIndexContract`. (A type with
unnamed fields is refused before any access.) -/
def ReplaceInBoundsHonest : Prop :=
  ∀ (α : Type) (t : CType) (v n u : Nat) (o : CObj α) (nargs : Nat) (kws : Option (List (Str × α)))
    (malloc : Nat → Bool), HonestLayout t v n u → n < 2 ^ 57 → o.size = v → WellFormed t o →
    (replaceC t o nargs kws malloc).isUB = false

theorem replaceInBoundsHonest_proven : ReplaceInBoundsHonest := by
  intro α t v n u o nargs kws malloc ⟨hH, hm, huv⟩ hn hsz hw
  have hrs := realSize_honest hH
  have hw' : ∀ i, i < n → ∃ a, o.slots[i]? = some (.val a) := by
    intro i hi; apply hw; rw [hsz, hrs]; exact hi
  have hnew := newIndexContract_proven α t v n u malloc hH hn
  obtain ⟨hd, hb, hv⟩ := hH
  have h3 : sizeOrNull (getTypeAttrAsSize t.nameStr t.dict "n_unnamed_fields") = .ok u :=
    sizeOf_small _ _ _ u (by rw [hd]; exact honest_nunnamed v n u) (by omega)
  unfold replaceC
  by_cases ha : nargs ≠ 0
  · rw [if_pos ha]; rfl
  · rw [if_neg ha]
    rw [h3]
    simp only [CRes.bind_ok]
    by_cases hu : u > 0
    · rw [if_pos hu]; rfl
    · rw [if_neg hu]
      have hu0 : u = 0 := by omega
      subst hu0
      rcases hnew with ⟨_, hme⟩ | ⟨_, res, hres, _, _, hslots, _⟩
      · rw [hme]; rfl
      · rw [hres]
        simp only [CRes.bind_ok]
        have hlen : n ≤ res.slots.length := by rw [hslots]; simp
        rw [hsz, show realSize t v = n from realSize_honest ⟨hd, hb, hv⟩]
        cases kws with
        | some kws =>
          simp only
          apply isUB_bind (replaceKwLoop_ok t o n (by omega) hw' n 0 res.slots kws (by omega) hlen)
          intro _ _
          split <;> rfl
        | none =>
          simp only
          apply isUB_bind (replaceCopyLoop_ok o n hw' n 0 res.slots (by omega) hlen)
          intro _ _
          rfl

/-! ## The size reads, for every state of the dict -/

/-- What one size read gives, for every content of the dict under that key: the lookup's own
exception, `TypeError` naming the key and the type when it is missing, `TypeError` for a
non-int (no `__index__`), `OverflowError` outside `Py_ssize_t`, `NULL` with no exception for a
negative int, and the value otherwise. -/
def SizeReadSpec : Prop :=
  ∀ (tp key : String) (d : TDict),
    (∀ e, d key = .error e → sizeOrNull (getTypeAttrAsSize tp d key) = .exc e) ∧
    (d key = .ok none →
      sizeOrNull (getTypeAttrAsSize tp d key) = .exc (.typeError s!"~Missed attribute '{key}' of type {tp}")) ∧
    (d key = .ok (some .other) →
      sizeOrNull (getTypeAttrAsSize tp d key) = .exc (.typeError "an integer is required")) ∧
    (∀ n, d key = .ok (some (.int n)) →
      (n < ssizeMin ∨ ssizeMax < n →
        sizeOrNull (getTypeAttrAsSize tp d key) = .exc (.overflowError "Python int too large to convert to C ssize_t")) ∧
      (ssizeMin ≤ n → n < 0 → sizeOrNull (getTypeAttrAsSize tp d key) = .nullNoExc) ∧
      (0 ≤ n → n ≤ ssizeMax → sizeOrNull (getTypeAttrAsSize tp d key) = .ok n.toNat))

/-- `PyStructSequence_New` reads `n_fields`, then `n_sequence_fields`, and allocates nothing
until both succeed: for every type and every allocator, a failing read decides the result, the
first one first, as `SizeReadSpec` gives it. -/
def NewReadsFirst : Prop :=
  SizeReadSpec ∧
  ∀ (α : Type) (t : CType) (malloc : Nat → Bool),
    (∀ r : CRes Nat, sizeOrNull (getTypeAttrAsSize t.nameStr t.dict "n_fields") = r →
      (∀ n, r ≠ .ok n) → pssNew (α := α) t malloc = r.bind (fun _ => .nullNoExc)) ∧
    (∀ n (r : CRes Nat), sizeOrNull (getTypeAttrAsSize t.nameStr t.dict "n_fields") = .ok n →
      sizeOrNull (getTypeAttrAsSize t.nameStr t.dict "n_sequence_fields") = r →
      (∀ v, r ≠ .ok v) → pssNew (α := α) t malloc = r.bind (fun _ => .nullNoExc))

theorem newReadsFirst_proven : NewReadsFirst := by
  refine ⟨?_, ?_⟩
  · intro tp key d
    refine ⟨fun e h => by simp [getTypeAttrAsSize, sizeOrNull, h],
      fun h => by simp [getTypeAttrAsSize, sizeOrNull, h],
      fun h => by simp [getTypeAttrAsSize, sizeOrNull, asSsize, h], ?_⟩
    intro n h
    refine ⟨fun hn => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_⟩
    · simp only [getTypeAttrAsSize, h, asSsize]
      rw [if_neg (by omega)]; rfl
    · simp only [getTypeAttrAsSize, h, asSsize]
      rw [if_pos (by unfold ssizeMax at *; unfold ssizeMin at *; omega)]
      simp only [sizeOrNull]
      rw [if_pos h2]
    · simp only [getTypeAttrAsSize, h, asSsize]
      rw [if_pos (by unfold ssizeMin; omega)]
      simp only [sizeOrNull]
      rw [if_neg (by omega)]
  · intro α t malloc
    constructor
    · intro r hr hne
      unfold pssNew
      rw [hr]
      cases r with
      | ok n => exact absurd rfl (hne n)
      | exc e => rfl
      | nullNoExc => rfl
      | ub w => rfl
    · intro n r h1 h2 hne
      unfold pssNew
      rw [h1]
      simp only [CRes.bind_ok]
      rw [h2]
      cases r with
      | ok v => exact absurd rfl (hne v)
      | exc e => rfl
      | nullNoExc => rfl
      | ub w => rfl

end PyLean.TypeObj.StructSeq
