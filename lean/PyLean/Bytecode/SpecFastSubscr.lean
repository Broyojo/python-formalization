import PyLean.Bytecode.SpecFast

/-!
The fast paths of the subscript specializations, as in `SpecFast.lean`: the exact operands on
which each macro answers without calling `__getitem__`/`__setitem__`, what it answers, and that
it exits on every other stack.
-/

namespace PyLean.Bytecode

open Uop

/-- `BINARY_OP_SUBSCR_STR_INT` (`Python/bytecodes.c:1185-1205`) answers the one-character str
at a non-negative compact index of an exact ASCII str, and `BINARY_OP_SUBSCR_USTR_INT`
(`:1207-1228`, new in 3.15) the same for any exact str whose character there is ASCII; both exit
on everything else: a negative or non-compact index, one past the end, a non-ASCII string (for
`STR_INT`) or character (for `USTR_INT`), or operands of another type. -/
def SubscrStrFast : Prop := ∀ (regs : Regs) (rest : List Val) (l r : Val),
  (∀ t i c, l = .str t → (∀ ch ∈ t.toList, ch.toNat < 128) → r = .int i → 0 ≤ i → i < 2 ^ 30 →
    t.toList[i.toNat]? = some c →
    BINARY_OP_SUBSCR_STR_INT ⟨regs, r :: l :: rest⟩ = .ok () ⟨regs, .str (String.singleton c) :: rest⟩) ∧
  (¬ (∃ t i c, l = .str t ∧ (∀ ch ∈ t.toList, ch.toNat < 128) ∧ r = .int i ∧ 0 ≤ i ∧ i < 2 ^ 30 ∧
      t.toList[i.toNat]? = some c) → Deopts (BINARY_OP_SUBSCR_STR_INT ⟨regs, r :: l :: rest⟩)) ∧
  (∀ t i c, l = .str t → r = .int i → 0 ≤ i → i < 2 ^ 30 → t.toList[i.toNat]? = some c → c.toNat < 128 →
    BINARY_OP_SUBSCR_USTR_INT ⟨regs, r :: l :: rest⟩ = .ok () ⟨regs, .str (String.singleton c) :: rest⟩) ∧
  (¬ (∃ t i c, l = .str t ∧ r = .int i ∧ 0 ≤ i ∧ i < 2 ^ 30 ∧ t.toList[i.toNat]? = some c ∧
      c.toNat < 128) → Deopts (BINARY_OP_SUBSCR_USTR_INT ⟨regs, r :: l :: rest⟩))

theorem nonNeg_iff (i : Int) : isNonNegCompact i = true ↔ 0 ≤ i ∧ i < 2 ^ 30 := by
  simp [isNonNegCompact]

theorem compact_of_nonneg {i : Int} (h0 : 0 ≤ i) (h1 : i < 2 ^ 30) : Compact i := ⟨by omega, h1⟩

theorem subscrStrFast_proven : SubscrStrFast := by
  intro regs rest l r
  obtain ⟨_, _, _, _, _, gnu, gna, _, _, _, _, _, _⟩ := guardRules_proven
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro t i c rfl ha rfl h0 h1 hc
    have g1 := guard_tos_int_pass (regs := regs) (rest := .str t :: rest) (compact_of_nonneg h0 h1)
    have g2 := (gna regs rest (.str t) (.int i) (live_str _ t)).1 ⟨t, rfl, ha⟩
    have hn : isNonNegCompact i = true := (nonNeg_iff i).2 ⟨h0, h1⟩
    show (do _GUARD_TOS_INT; _GUARD_NOS_COMPACT_ASCII; _BINARY_OP_SUBSCR_STR_INT) _ = _
    simp only [bind, EStateM.bind, g1, g2]
    bc_simp [_BINARY_OP_SUBSCR_STR_INT, hn, hc]
  · intro hne
    by_cases hr : CompactInt r
    · obtain ⟨i, rfl, hci⟩ := hr
      have g1 := guard_tos_int_pass (regs := regs) (rest := l :: rest) hci
      cases l with
      | str t =>
        by_cases ha : ∀ ch ∈ t.toList, ch.toNat < 128
        · have g2 := (gna regs rest (.str t) (.int i) (live_str _ t)).1 ⟨t, rfl, ha⟩
          refine ⟨⟨regs, rest⟩, ?_⟩
          show (do _GUARD_TOS_INT; _GUARD_NOS_COMPACT_ASCII; _BINARY_OP_SUBSCR_STR_INT) _ = _
          simp only [bind, EStateM.bind, g1, g2]
          cases hn : isNonNegCompact i with
          | false => bc_simp [_BINARY_OP_SUBSCR_STR_INT, hn]
          | true =>
            obtain ⟨h0, h1⟩ := (nonNeg_iff i).1 hn
            cases hc : t.toList[i.toNat]? with
            | none => bc_simp [_BINARY_OP_SUBSCR_STR_INT, hn, hc]
            | some c => exact absurd ⟨t, i, c, rfl, ha, rfl, h0, h1, hc⟩ hne
        · have g2 := (gna regs rest (.str t) (.int i) (live_str _ t)).2
            (fun ⟨t', ht, h⟩ => by cases ht; exact ha h)
          exact ⟨_, by simp only [BINARY_OP_SUBSCR_STR_INT, bind, EStateM.bind, g1, g2]; rfl⟩
      | _ => exact ⟨_, by bc_simp [BINARY_OP_SUBSCR_STR_INT, g1, _GUARD_NOS_COMPACT_ASCII] <;> rfl⟩
    · exact ⟨_, by simp only [BINARY_OP_SUBSCR_STR_INT, bind, EStateM.bind, guard_tos_int_fail hr]; rfl⟩
  · rintro t i c rfl rfl h0 h1 hc ha
    have g1 := guard_tos_int_pass (regs := regs) (rest := .str t :: rest) (compact_of_nonneg h0 h1)
    have g2 := (gnu regs rest (.str t) (.int i) (live_str _ t)).1 ⟨t, rfl⟩
    have hn : isNonNegCompact i = true := (nonNeg_iff i).2 ⟨h0, h1⟩
    have ha' : ¬ asciiLimit ≤ c.toNat := by simp only [asciiLimit]; omega
    show (do _GUARD_TOS_INT; _GUARD_NOS_UNICODE; _BINARY_OP_SUBSCR_USTR_INT) _ = _
    simp only [bind, EStateM.bind, g1, g2]
    bc_simp [_BINARY_OP_SUBSCR_USTR_INT, hn, hc, ha']
  · intro hne
    by_cases hr : CompactInt r
    · obtain ⟨i, rfl, hci⟩ := hr
      have g1 := guard_tos_int_pass (regs := regs) (rest := l :: rest) hci
      cases l with
      | str t =>
        have g2 := (gnu regs rest (.str t) (.int i) (live_str _ t)).1 ⟨t, rfl⟩
        refine ⟨⟨regs, rest⟩, ?_⟩
        show (do _GUARD_TOS_INT; _GUARD_NOS_UNICODE; _BINARY_OP_SUBSCR_USTR_INT) _ = _
        simp only [bind, EStateM.bind, g1, g2]
        cases hn : isNonNegCompact i with
        | false => bc_simp [_BINARY_OP_SUBSCR_USTR_INT, hn]
        | true =>
          obtain ⟨h0, h1⟩ := (nonNeg_iff i).1 hn
          cases hc : t.toList[i.toNat]? with
          | none => bc_simp [_BINARY_OP_SUBSCR_USTR_INT, hn, hc]
          | some c =>
            by_cases ha : c.toNat < 128
            · exact absurd ⟨t, i, c, rfl, rfl, h0, h1, hc, ha⟩ hne
            · have ha' : asciiLimit ≤ c.toNat := by simp only [asciiLimit]; omega
              bc_simp [_BINARY_OP_SUBSCR_USTR_INT, hn, hc, ha']
      | _ => exact ⟨_, by bc_simp [BINARY_OP_SUBSCR_USTR_INT, g1, _GUARD_NOS_UNICODE, notStr] <;> rfl⟩
    · exact ⟨_, by simp only [BINARY_OP_SUBSCR_USTR_INT, bind, EStateM.bind, guard_tos_int_fail hr]; rfl⟩

/-- `BINARY_OP_SUBSCR_TUPLE_INT`, `Python/bytecodes.c:1240-1278`: since 3.15 its bounds check is
the guard `_GUARD_BINARY_OP_SUBSCR_TUPLE_INT_BOUNDS` (`:1250-1261`), which passes exactly on a
non-negative compact index below the length, after which `_BINARY_OP_SUBSCR_TUPLE_INT`
(`:1263-1278`) reads the item without a check of its own. The macro answers the item on an exact
tuple and such an index and exits on everything else. -/
def SubscrTupleFast : Prop := ∀ (regs : Regs) (rest : List Val) (l r : Val), Live regs.rt l →
  (∀ a items i, regs.rt.heap[a]? = some (.tuple items) →
    (0 ≤ i → i < 2 ^ 30 → i < items.size → _GUARD_BINARY_OP_SUBSCR_TUPLE_INT_BOUNDS
      ⟨regs, .int i :: .ref a :: rest⟩ = .ok () ⟨regs, .int i :: .ref a :: rest⟩) ∧
    (¬ (0 ≤ i ∧ i < 2 ^ 30 ∧ i < items.size) → _GUARD_BINARY_OP_SUBSCR_TUPLE_INT_BOUNDS
      ⟨regs, .int i :: .ref a :: rest⟩ = .error .deopt ⟨regs, .int i :: .ref a :: rest⟩)) ∧
  (∀ a items i v, l = .ref a → regs.rt.heap[a]? = some (.tuple items) → r = .int i → 0 ≤ i →
    i < 2 ^ 30 → items[i.toNat]? = some v →
    BINARY_OP_SUBSCR_TUPLE_INT ⟨regs, r :: l :: rest⟩ = .ok () ⟨regs, v :: rest⟩) ∧
  (¬ (∃ a items i v, l = .ref a ∧ regs.rt.heap[a]? = some (.tuple items) ∧ r = .int i ∧ 0 ≤ i ∧
      i < 2 ^ 30 ∧ items[i.toNat]? = some v) →
    Deopts (BINARY_OP_SUBSCR_TUPLE_INT ⟨regs, r :: l :: rest⟩))

theorem tupleBounds (regs : Regs) (rest : List Val) (a : Addr) (items : Array Val) (i : Int)
    (ho : regs.rt.heap[a]? = some (.tuple items)) :
    _GUARD_BINARY_OP_SUBSCR_TUPLE_INT_BOUNDS ⟨regs, .int i :: .ref a :: rest⟩ =
      if 0 ≤ i ∧ i < 2 ^ 30 ∧ i < items.size then .ok () ⟨regs, .int i :: .ref a :: rest⟩
      else .error .deopt ⟨regs, .int i :: .ref a :: rest⟩ := by
  cases hn : isNonNegCompact i with
  | false =>
    have h' : ¬ (0 ≤ i ∧ i < 2 ^ 30 ∧ i < items.size) := fun ⟨a, b, _⟩ => by
      rw [(nonNeg_iff i).2 ⟨a, b⟩] at hn; cases hn
    rw [if_neg h']
    bc_simp [_GUARD_BINARY_OP_SUBSCR_TUPLE_INT_BOUNDS, hn]
  | true =>
    obtain ⟨h0, h1⟩ := (nonNeg_iff i).1 hn
    by_cases hlt : i < items.size
    · rw [if_pos ⟨h0, h1, hlt⟩]
      have : ¬ items.size ≤ i.toNat := by omega
      bc_simp [_GUARD_BINARY_OP_SUBSCR_TUPLE_INT_BOUNDS, hn, ho, this]
    · rw [if_neg fun ⟨_, _, h⟩ => hlt h]
      have : items.size ≤ i.toNat := by omega
      bc_simp [_GUARD_BINARY_OP_SUBSCR_TUPLE_INT_BOUNDS, hn, ho, this]

theorem subscrTupleFast_proven : SubscrTupleFast := by
  intro regs rest l r hl
  obtain ⟨_, _, _, _, _, _, _, _, _, gnt, _, _, _⟩ := guardRules_proven
  refine ⟨fun a items i ho => ?_, ?_, ?_⟩
  · rw [tupleBounds regs rest a items i ho]
    exact ⟨fun h0 h1 h2 => if_pos ⟨h0, h1, h2⟩, fun h => if_neg h⟩
  · rintro a items i v rfl ho rfl h0 h1 hv
    have g1 := guard_tos_int_pass (regs := regs) (rest := .ref a :: rest) (compact_of_nonneg h0 h1)
    have g2 := (gnt regs rest (.ref a) (.int i) hl).1 ⟨a, items, rfl, ho⟩
    have hlt : i < items.size := by
      have hlt' : i.toNat < items.size := (Array.getElem?_eq_some_iff.1 hv).1
      omega
    have g3 := tupleBounds regs rest a items i ho
    rw [if_pos ⟨h0, h1, hlt⟩] at g3
    show (do _GUARD_TOS_INT; _GUARD_NOS_TUPLE; _GUARD_BINARY_OP_SUBSCR_TUPLE_INT_BOUNDS; _BINARY_OP_SUBSCR_TUPLE_INT) _ = _
    simp only [bind, EStateM.bind, g1, g2, g3]
    bc_simp [_BINARY_OP_SUBSCR_TUPLE_INT, ho, hv]
  · intro hne
    by_cases hr : CompactInt r
    · obtain ⟨i, rfl, hci⟩ := hr
      have g1 := guard_tos_int_pass (regs := regs) (rest := l :: rest) hci
      by_cases hlt : IsTuple regs.rt l
      · have g2 := (gnt regs rest l (.int i) hl).1 hlt
        obtain ⟨a, items, rfl, ho⟩ := hlt
        have g3 := tupleBounds regs rest a items i ho
        have hb : ¬ (0 ≤ i ∧ i < 2 ^ 30 ∧ i < items.size) := by
          rintro ⟨h0, h1, h2⟩
          have hi : i.toNat < items.size := by omega
          exact hne ⟨a, items, i, items[i.toNat], rfl, ho, rfl, h0, h1, by simp [hi]⟩
        rw [if_neg hb] at g3
        exact ⟨_, by simp only [BINARY_OP_SUBSCR_TUPLE_INT, bind, EStateM.bind, g1, g2, g3]; rfl⟩
      · exact ⟨_, by simp only [BINARY_OP_SUBSCR_TUPLE_INT, bind, EStateM.bind, g1,
          (gnt regs rest l (.int i) hl).2 hlt]; rfl⟩
    · exact ⟨_, by simp only [BINARY_OP_SUBSCR_TUPLE_INT, bind, EStateM.bind, guard_tos_int_fail hr]; rfl⟩

/-- `STORE_SUBSCR_LIST_INT`, `Python/bytecodes.c:1420-1452`: `list[i] = v` on an exact list and a
compact int stores in place, a negative index counting from the end, and pops all three; on any
other operands or an index outside the list after that adjustment it exits. -/
def StoreSubscrListFast : Prop := ∀ (regs : Regs) (rest : List Val) (k c v : Val), Live regs.rt c →
  (∀ a items i, c = .ref a → regs.rt.heap[a]? = some (.list items) → k = .int i → Compact i →
    0 ≤ normIndex i items.size → normIndex i items.size < items.size →
    STORE_SUBSCR_LIST_INT ⟨regs, k :: c :: v :: rest⟩ = .ok ()
      ⟨{ regs with rt := { regs.rt with heap := (regs.rt.heap.setIfInBounds a
          (.list (items.setIfInBounds (normIndex i items.size).toNat v))) } }, rest⟩) ∧
  (¬ (∃ a items i, c = .ref a ∧ regs.rt.heap[a]? = some (.list items) ∧ k = .int i ∧ Compact i ∧
      0 ≤ normIndex i items.size ∧ normIndex i items.size < items.size) →
    Deopts (STORE_SUBSCR_LIST_INT ⟨regs, k :: c :: v :: rest⟩))

theorem storeSubscrListFast_proven : StoreSubscrListFast := by
  intro regs rest k c v hl
  obtain ⟨_, _, _, _, _, _, _, _, gnl, _, _, _, _⟩ := guardRules_proven
  constructor
  · rintro a items i rfl ho rfl hc h0 h1
    have g1 := guard_tos_int_pass (regs := regs) (rest := .ref a :: v :: rest) hc
    have g2 := (gnl regs (v :: rest) (.ref a) (.int i) hl).1 ⟨a, items, rfl, ho⟩
    show (do _GUARD_TOS_INT; _GUARD_NOS_LIST; _STORE_SUBSCR_LIST_INT) _ = _
    simp only [bind, EStateM.bind, g1, g2]
    unfold normIndex at h0 h1 ⊢
    by_cases hneg : i < 0
    · simp only [hneg, ite_true] at h0 h1 ⊢
      have n1 : ¬ i + (items.size : Int) < 0 := by omega
      have n2 : ¬ (items.size : Int) ≤ i + items.size := by omega
      bc_simp [_STORE_SUBSCR_LIST_INT, ho, hneg, n1, n2, setObj]
    · simp only [hneg, ite_false] at h0 h1 ⊢
      have n2 : ¬ (items.size : Int) ≤ i := by omega
      bc_simp [_STORE_SUBSCR_LIST_INT, ho, hneg, n2, setObj]
  · intro hne
    by_cases hr : CompactInt k
    · obtain ⟨i, rfl, hci⟩ := hr
      have g1 := guard_tos_int_pass (regs := regs) (rest := c :: v :: rest) hci
      by_cases hli : IsList regs.rt c
      · have g2 := (gnl regs (v :: rest) c (.int i) hl).1 hli
        obtain ⟨a, items, rfl, ho⟩ := hli
        have hb : ¬ (0 ≤ normIndex i items.size ∧ normIndex i items.size < items.size) :=
          fun ⟨h0, h1⟩ => hne ⟨a, items, i, rfl, ho, rfl, hci, h0, h1⟩
        refine ⟨⟨regs, rest⟩, ?_⟩
        show (do _GUARD_TOS_INT; _GUARD_NOS_LIST; _STORE_SUBSCR_LIST_INT) _ = _
        simp only [bind, EStateM.bind, g1, g2]
        unfold normIndex at hb
        by_cases hneg : i < 0
        · simp only [hneg, ite_true] at hb
          by_cases hz : i + (items.size : Int) < 0
          · bc_simp [_STORE_SUBSCR_LIST_INT, ho, hneg, hz]
          · have hz' : (items.size : Int) ≤ i + items.size := by omega
            bc_simp [_STORE_SUBSCR_LIST_INT, ho, hneg, hz, hz']
        · simp only [hneg, ite_false] at hb
          have hz' : (items.size : Int) ≤ i := by omega
          bc_simp [_STORE_SUBSCR_LIST_INT, ho, hneg, hz']
      · exact ⟨_, by simp only [STORE_SUBSCR_LIST_INT, bind, EStateM.bind, g1,
          (gnl regs (v :: rest) c (.int i) hl).2 hli]; rfl⟩
    · exact ⟨_, by simp only [STORE_SUBSCR_LIST_INT, bind, EStateM.bind, guard_tos_int_fail hr]; rfl⟩

end PyLean.Bytecode
