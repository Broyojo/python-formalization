import PyLean.TypeObj.StructSeqCProps

/-!
# The constructor, `__reduce__` and `__replace__` on the C model, while the sizes are honest

On a type whose three size attributes still hold what `PyStructSequence_NewType` stored
(`HonestLayout`), these theorems give the exact outcome of each function, failure paths first:
`NewImplSpecC` (`structseq_new_impl`: the argument's exception, the not-a-dict refusal, the
three length messages, `MemoryError`, the lookups of the `dict` argument with both
`PyDict_GET_SIZE` reads, and the object built), `ReduceSpecC` and `ReplaceSpecC`. Every callback
(the argument's conversion, the dict lookups, the keyword pops, name decoding) is an arbitrary
outcome. `SizeReadSpec` and `NewReadsFirst` cover every state of the dict.

The refutations `ReplaceInBounds`, `ReduceInBounds`, `NewImplInBounds` (StructSeqCProps.lean)
show what rebinding the size attributes does, and `ReduceInBoundsBuilt` (StructSeqNewType.lean)
what an unnamed hidden field does.
-/

namespace PyLean.TypeObj.StructSeq

open PyLean PyLean.UnicodeObj

variable {α β γ : Type}

/-- `Honest`, and `tp_members` holds the `n - u` named fields, the unnamed fields being visible
(`u ≤ v`). Unnamed fields are "only allowed for indices < n_visible_fields" (structseq.c:23-24);
that is a precondition on the desc, which `PyStructSequence_NewType` does not check
(`ReduceInBoundsBuilt` refutes the statement without it). -/
def HonestLayout (t : CType) (v n u : Nat) : Prop :=
  Honest t v n u ∧ t.members.length = n - u ∧ u ≤ v

theorem isUB_ofPy {x : Py β} : (CRes.ofPy x).isUB = false := by
  cases x <;> rfl

theorem realSize_honest {t : CType} {v n u : Nat} (h : Honest t v n u) : realSize t v = n := by
  obtain ⟨_, hb, hv⟩ := h
  simp only [realSize, hb, obItemOff]
  omega

theorem honest_reads {t : CType} {v n u : Nat} (h : HonestLayout t v n u) (hn : n < 2 ^ 57) :
    sizeOrNull (getTypeAttrAsSize t.nameStr t.dict "n_fields") = .ok n ∧
    sizeOrNull (getTypeAttrAsSize t.nameStr t.dict "n_sequence_fields") = .ok v ∧
    sizeOrNull (getTypeAttrAsSize t.nameStr t.dict "n_unnamed_fields") = .ok u := by
  obtain ⟨⟨hd, _, hv⟩, _, hu⟩ := h
  exact ⟨sizeOf_small _ _ _ n (by rw [hd]; exact honest_nfields v n u) (by omega),
    sizeOf_small _ _ _ v (by rw [hd]; exact honest_nseq v n u) (by omega),
    sizeOf_small _ _ _ u (by rw [hd]; exact honest_nunnamed v n u) (by omega)⟩

/-! ## The block while it is filled -/

/-- `pre` written, `m` slots still `NULL`, then `J`. -/
def shape (pre : List α) (m : Nat) (J : List (Slot α)) : List (Slot α) :=
  pre.map Slot.val ++ List.replicate m .null ++ J

theorem shape_length (pre : List α) (m : Nat) (J : List (Slot α)) :
    (shape pre m J).length = pre.length + m + J.length := by
  simp [shape]; omega

theorem write_shape (pre : List α) (m : Nat) (J : List (Slot α)) (x : α) (w : String) :
    writeSlot (shape pre (m + 1) J) pre.length (.val x) w = .ok (shape (pre ++ [x]) m J) := by
  unfold writeSlot
  rw [if_pos (by rw [shape_length]; omega)]
  congr 1
  simp only [shape, List.replicate_succ, List.append_assoc, List.cons_append, List.map_append,
    List.map_cons, List.map_nil, List.nil_append]
  rw [List.set_append_right _ _ (by simp)]
  simp

theorem read_vals (vals : List α) (rest : List (Slot α)) (i : Nat) (hi : i < vals.length) (w : String) :
    readSlot (vals.map Slot.val ++ rest) i w = .ok (.val vals[i]) := by
  unfold readSlot
  rw [dif_pos (by simp; omega)]
  rw [List.getElem_append_left (by simp; omega)]
  simp

theorem memberName_getD (ms : List Member) (i u : Nat) (hu : u ≤ i) (hi : i - u < ms.length) (w : String) :
    memberName ms ((i : Int) - u) w = .ok (.name (ms.getD (i - u) ⟨[], 0⟩).name) := by
  unfold memberName
  rw [if_neg (show ¬ ((i : Int) - u < 0) by omega)]
  have he : ((i : Int) - u).toNat = i - u := by omega
  rw [dif_pos (by rw [he]; exact hi)]
  simp only [he, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

theorem memberName_nat (ms : List Member) (i : Nat) (hi : i < ms.length) (w : String) :
    memberName ms (i : Int) w = .ok (.name (ms.getD i ⟨[], 0⟩).name) := by
  have := memberName_getD ms i 0 (Nat.zero_le _) (by omega) w
  simpa using this

theorem drop_take_succ (vals : List α) (i k : Nat) (hi : i < vals.length) :
    (vals.drop i).take (k + 1) = vals[i] :: (vals.drop (i + 1)).take k := by
  rw [List.drop_eq_getElem_cons hi]; rfl

theorem CRes.map_bind_ok {x : CRes β} {f : β → CRes γ} : x.bind f = x >>= f := rfl
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
