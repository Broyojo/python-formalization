import PyLean.UnicodeObj.MethTailProps

/-!
`str.partition` and `str.rpartition`: `PyUnicode_Partition` (Objects/unicodeobject.c:12916-12964),
`PyUnicode_RPartition` (:12968-13016), the method wrappers (:13035-13039, :13056-13060) and the
stringlib bodies they dispatch to (Objects/stringlib/partition.h:12-67, :69-124). `FASTSEARCH`
is modelled by its result, the first (`StrSearch.findL`) or last (`StrSearch.rfindL`)
occurrence. The `unicode_askind` widening of the separator and the ASCII/UCS1/UCS2/UCS4
instances do not change the characters compared.
-/

namespace PyLean.UnicodeObj

open PyLean

/-- `STRINGLIB(partition)`, Objects/stringlib/partition.h:12-67. -/
def stringlibPartition (s sep : Str) : Py (Str × Str × Str) :=
  if sep.length = 0 then .error (.valueError "empty separator")
  else
    match StrSearch.findL sep s with
    | none => .ok (s, [], [])
    | some pos => .ok (s.take pos, sep, s.drop (pos + sep.length))

/-- `STRINGLIB(rpartition)`, Objects/stringlib/partition.h:69-124. -/
def stringlibRPartition (s sep : Str) : Py (Str × Str × Str) :=
  if sep.length = 0 then .error (.valueError "empty separator")
  else
    match StrSearch.rfindL sep s with
    | none => .ok ([], [], s)
    | some pos => .ok (s.take pos, sep, s.drop (pos + sep.length))

/-- `PyUnicode_Partition`, unicodeobject.c:12916-12964, with the shortcut of :12930-12933
(`kind1 < kind2 || len1 < len2`; the length test is new in 3.15). -/
def pyUnicodePartition (strObj sepObj : Arg) : Py (Str × Str × Str) := do
  let s ← ensureUnicode strObj
  let sep ← ensureUnicode sepObj
  if kindWidth s < kindWidth sep ∨ s.length < sep.length then return (s, [], [])
  stringlibPartition s sep

/-- `PyUnicode_RPartition`, unicodeobject.c:12968-13016, shortcut at :12982-12985. -/
def pyUnicodeRPartition (strObj sepObj : Arg) : Py (Str × Str × Str) := do
  let s ← ensureUnicode strObj
  let sep ← ensureUnicode sepObj
  if kindWidth s < kindWidth sep ∨ s.length < sep.length then return ([], [], s)
  stringlibRPartition s sep

/-- `unicode_partition` (:13035-13039) and `unicode_rpartition` (:13056-13060). -/
def unicodePartition (s : Str) (sep : Arg) : Py (Str × Str × Str) := pyUnicodePartition (.str s) sep
def unicodeRPartition (s : Str) (sep : Arg) : Py (Str × Str × Str) := pyUnicodeRPartition (.str s) sep

/-- The documented result: "Split the string at the first occurrence of sep, and return a
3-tuple containing the part before the separator, the separator itself, and the part after
it. If the separator is not found, return a 3-tuple containing the string itself, followed by
two empty strings." `rpartition`: the last occurrence, and two empty strings followed by the
string. An empty separator raises `ValueError`, a separator that is not a `str` `TypeError`. -/
def partitionDoc (s : Str) (sep : Arg) (last : Bool) : Py (Str × Str × Str) :=
  match sep with
  | .str sep =>
    if sep = [] then .error (.valueError "empty separator")
    else
      match (if last then StrSearch.rfindL sep s else StrSearch.findL sep s) with
      | none => .ok (if last then ([], [], s) else (s, [], []))
      | some i => .ok (s.take i, sep, s.drop (i + sep.length))
  | a => .error (.typeError s!"must be str, not {a.tpName}")

/-- For every string and every separator object, `partition` and `rpartition` give the
documented result, through the shortcut for a separator of a wider kind or a longer length
and through the general path alike. Type invariants: `Str.Valid`. -/
def PartitionDoc : Prop :=
  ∀ (s : Str) (sep : Arg), Str.Valid s → (∀ t, sep = .str t → Str.Valid t) →
    unicodePartition s sep = partitionDoc s sep false ∧
    unicodeRPartition s sep = partitionDoc s sep true

theorem findL_infix {p s : Str} {i : Nat} (h : StrSearch.findL p s = some i) :
    ∀ c ∈ p, c ∈ s := by
  induction s generalizing i with
  | nil =>
    simp only [StrSearch.findL] at h
    split at h
    · next hp =>
      intro c hc
      have := (List.isPrefixOf_iff_prefix.mp hp).subset hc
      exact this
    · cases h
  | cons x xs ih =>
    simp only [StrSearch.findL] at h
    split at h
    · next hp =>
      intro c hc
      exact (List.isPrefixOf_iff_prefix.mp hp).subset hc
    · cases hf : StrSearch.findL p xs with
      | none => simp [hf] at h
      | some j =>
        intro c hc
        exact List.mem_cons_of_mem _ (ih hf c hc)

theorem rfindL_infix {p s : Str} {i : Nat} (h : StrSearch.rfindL p s = some i) :
    ∀ c ∈ p, c ∈ s := by
  induction s generalizing i with
  | nil =>
    simp only [StrSearch.rfindL] at h
    split at h
    · next hp => intro c hc; exact (List.isPrefixOf_iff_prefix.mp hp).subset hc
    · cases h
  | cons x xs ih =>
    simp only [StrSearch.rfindL] at h
    cases hf : StrSearch.rfindL p xs with
    | some j => intro c hc; exact List.mem_cons_of_mem _ (ih hf c hc)
    | none =>
      simp only [hf] at h
      split at h
      · next hp => intro c hc; exact (List.isPrefixOf_iff_prefix.mp hp).subset hc
      · cases h

theorem foldl_max_mem_or (l : List Nat) : ∀ a, l.foldl max a = a ∨ l.foldl max a ∈ l := by
  induction l with
  | nil => intro a; left; rfl
  | cons y ys ih =>
    intro a
    simp only [List.foldl_cons]
    rcases ih (max a y) with h | h
    · rw [h]
      rcases Nat.le_total a y with hl | hl
      · right; rw [Nat.max_eq_right hl]; exact List.mem_cons_self
      · left; exact Nat.max_eq_left hl
    · right; exact List.mem_cons_of_mem _ h

/-- A separator of a wider kind holds a character the string cannot hold. -/
theorem wider_kind_char (s sep : Str) (hs : Str.Valid s) (hk : kindWidth s < kindWidth sep) :
    ∃ c ∈ sep, c ∉ s := by
  have hmem := foldl_max_mem_or sep 0
  have hbig : 2 ^ (8 * kindWidth s) ≤ maxCharOf sep := by
    unfold kindWidth canonicalKind kindOfMax at hk ⊢
    revert hk
    repeat' split
    all_goals simp [Kind.width] at *
    all_goals omega
  rcases hmem with h0 | hin
  · exfalso
    have : maxCharOf sep = 0 := h0
    have := Nat.one_le_two_pow (n := 8 * kindWidth s)
    omega
  · exact ⟨maxCharOf sep, hin, fun hm => by
      have := mem_lt_kindWidth hs hm; omega⟩

theorem partitionDoc_str (s t : Str) (last : Bool) :
    partitionDoc s (.str t) last =
      if t = [] then .error (.valueError "empty separator")
      else
        match (if last then StrSearch.rfindL t s else StrSearch.findL t s) with
        | none => .ok (if last then ([], [], s) else (s, [], []))
        | some i => .ok (s.take i, t, s.drop (i + t.length)) := rfl

theorem partitionDoc_proven : PartitionDoc := by
  intro s sep hs hsep
  cases sep with
  | str t =>
    have ht := hsep t rfl
    have hnone : (kindWidth s < kindWidth t ∨ s.length < t.length) →
        StrSearch.findL t s = none ∧ StrSearch.rfindL t s = none := by
      intro h
      constructor
      · cases hf : StrSearch.findL t s with
        | none => rfl
        | some i =>
          exfalso
          rcases h with hk | hl
          · obtain ⟨c, hc, hcs⟩ := wider_kind_char s t hs hk
            exact hcs (findL_infix hf c hc)
          · have := StrSearch.findL_le hf; omega
      · cases hf : StrSearch.rfindL t s with
        | none => rfl
        | some i =>
          exfalso
          rcases h with hk | hl
          · obtain ⟨c, hc, hcs⟩ := wider_kind_char s t hs hk
            exact hcs (rfindL_infix hf c hc)
          · have := StrSearch.rfindL_le hf; omega
    have hne : (kindWidth s < kindWidth t ∨ s.length < t.length) → t ≠ [] := by
      intro h ht0
      subst ht0
      rcases h with hk | hl
      · have : kindWidth ([] : Str) = 1 := rfl
        have := kindWidth_cases s
        omega
      · simp at hl
    constructor
    · show (if kindWidth s < kindWidth t ∨ s.length < t.length then .ok (s, [], [])
        else stringlibPartition s t) = _
      rw [partitionDoc_str]
      unfold stringlibPartition
      by_cases h : kindWidth s < kindWidth t ∨ s.length < t.length
      · rw [if_pos h, if_neg (hne h)]
        simp only [Bool.false_eq_true, if_false, (hnone h).1]
      · rw [if_neg h]
        by_cases h0 : t = []
        · subst h0; simp
        · rw [if_neg (by simpa using h0), if_neg h0]
          simp only [Bool.false_eq_true, if_false]
    · show (if kindWidth s < kindWidth t ∨ s.length < t.length then .ok ([], [], s)
        else stringlibRPartition s t) = _
      rw [partitionDoc_str]
      unfold stringlibRPartition
      by_cases h : kindWidth s < kindWidth t ∨ s.length < t.length
      · rw [if_pos h, if_neg (hne h)]
        simp only [if_true, (hnone h).2]
      · rw [if_neg h]
        by_cases h0 : t = []
        · subst h0; simp
        · rw [if_neg (by simpa using h0), if_neg h0]
          simp only [if_true]
  | _ => exact ⟨rfl, rfl⟩

end PyLean.UnicodeObj
