import PyLean.JsonMod.EncFullTwins

/-!
Properties of the full encoder models (`EncFull.lean`).

* `DumpsTwinsX` (proven): on exact containers with exact-`str` separators and key types whose
  `tp_name` is their `__name__`, when neither twin raises its `RecursionError`, `json.dumps` gives
  the same text or the same exception with corresponding notes; and nested lists `k + 1` deep need
  `k + 1` levels of C stack room and `k + 3` Python frames.
* Each hypothesis is needed: `DumpsTwinsRec` (no recursion hypothesis), `DumpsTwinsNotes` (the
  notes as printed), `DumpsTwinsSep` (separators that are `str` subclasses) and `DumpsTwinsSub`
  (container subclasses) are refuted.
* `EncoderStringX`, `EncoderStringRaw`: `encoder_write_string` with a custom encoder writes
  `str()` of a `str` subclass.
* `EncoderCallX`: `c_make_encoder(...)(o, level)` for every level, through `create_indent_cache`.
-/

namespace PyLean.JsonMod

open PyLean

/-! ### What a note prints -/

/-- `repr` of the key in a note: of a `str` (its text), or of another key. -/
inductive KeyShown where
  | str (s : PStr)
  | int (n : Int)
  | flt (r : PStr)
  | bool (b : Bool)
  | none
  | obj (t : String)
  deriving DecidableEq, Repr

inductive NoteShown where
  | item (tn : String) (i : Nat)
  | key (tn : String) (k : KeyShown)
  | obj (tn : String)
  deriving DecidableEq, Repr

def KeyShown.ofKey : XKey → KeyShown
  | .str s => .str s
  | .int n => .int n
  | .flt _ r => .flt r
  | .bool b => .bool b
  | .none => .none
  | .obj t _ => .obj t.name

def NoteKey.shown : NoteKey → KeyShown
  | .orig k => .ofKey k
  | .conv s => .str s

/-- The note C prints: `%T` and `%R` of the original key. -/
def showC : Note → NoteShown
  | .item t i => .item t.fq i
  | .key t k => .key t.fq k.shown
  | .obj t => .obj t.fq

/-- The note Python prints: `type(o).__name__` and `repr` of the converted key. -/
def showPy : Note → NoteShown
  | .item t i => .item t.name i
  | .key t k => .key t.name k.shown
  | .obj t => .obj t.name

/-- The same text, or the same exception with the same printed notes. -/
def SameShown (rc rp : XR) : Prop :=
  (∃ t, rc = .ok t ∧ rp = .ok t) ∨
  (∃ e nsC nsP cxC cxP, rc = .error (e, nsC, cxC) ∧ rp = .error (e, nsP, cxP) ∧ nsC.map showC = nsP.map showPy)

/-- The same text, or the same exception (class and message), whatever the notes. -/
def SameExc (rc rp : XR) : Prop :=
  (∃ t, rc = .ok t ∧ rp = .ok t) ∨ (∃ e xC xP, rc = .error (e, xC) ∧ rp = .error (e, xP))

/-! ### Nested lists and the recursion limits -/

/-- `[[...[]...]]`, `k + 1` lists deep. -/
def nestL : Nat → XVal
  | 0 => .seq tList []
  | k + 1 => .seq tList [nestL k]

theorem nestL_okx (k : Nat) : (nestL k).okx = true := by
  induction k with
  | zero => rfl
  | succ k ih => simp [nestL, XVal.okx, XVal.okxList, ih]

/-- `k + 2` levels of cost `W` fit in `c` exactly when `k + 1` fit in what one leaves. -/
theorem thr_le {k W c : Nat} (hw : W ≤ c) : (k + 1 + 1) * W ≤ c ↔ (k + 1) * W ≤ c - W := by
  rw [Nat.succ_mul (k + 1)]; omega

theorem thr_lt {k W c : Nat} (hw : W ≤ c) : c < (k + 1 + 1) * W ↔ c - W < (k + 1) * W := by
  rw [Nat.succ_mul (k + 1)]; omega

theorem thr_big {k W c : Nat} (hw : ¬ W ≤ c) : c < (k + 1) * W := by
  rw [Nat.succ_mul]; omega

theorem cEnterX_pos {α : Type} {c w : Nat} {k : (c' : Nat) → c' < c → Except XErr α} (h : w + 1 ≤ c) :
    cEnterX c w k = k (c - (w + 1)) (by omega) := by
  simp [cEnterX, h]

theorem encNestC (cfg : XCfg) : ∀ (k c lvl : Nat) (seen : List Nat) (anc : List XVal),
    ((k + 1) * (cfg.stk .seq + 1) ≤ c → ∃ t, cObjX cfg c lvl seen anc (nestL k) = .ok t) ∧
    (c < (k + 1) * (cfg.stk .seq + 1) → ∃ ns, cObjX cfg c lvl seen anc (nestL k) = .error (recEncC, ns, [])) := by
  intro k
  induction k with
  | zero =>
    intro c lvl seen anc
    rw [Nat.zero_add, Nat.one_mul]
    by_cases hw : cfg.stk .seq + 1 ≤ c
    · refine ⟨fun _ => ⟨cs "[]", ?_⟩, fun h => by omega⟩
      simp [nestL, cObjX, cEnterX_pos hw, cContX, cSeqPart]
    · exact ⟨fun h => by omega, fun _ => ⟨[], by simp [nestL, cObjX, cEnterX, hw, xe]⟩⟩
  | succ k ih =>
    intro c lvl seen anc
    by_cases hw : cfg.stk .seq + 1 ≤ c
    · rw [thr_le hw, thr_lt hw]
      have key : ∀ lvl' anc' sep,
          ((k + 1) * (cfg.stk .seq + 1) ≤ c - (cfg.stk .seq + 1) →
            ∃ t, cSeqItemsX cfg (c - (cfg.stk .seq + 1)) lvl' seen anc' tList sep 0 [nestL k] = .ok t) ∧
          (c - (cfg.stk .seq + 1) < (k + 1) * (cfg.stk .seq + 1) → ∃ ns,
            cSeqItemsX cfg (c - (cfg.stk .seq + 1)) lvl' seen anc' tList sep 0 [nestL k] = .error (recEncC, ns, [])) := by
        intro lvl' anc' sep
        obtain ⟨h1, h2⟩ := ih (c - (cfg.stk .seq + 1)) lvl' seen anc'
        simp only [cSeqItemsX, ne_eq, not_true_eq_false, ↓reduceIte]
        refine ⟨fun h => ?_, fun h => ?_⟩
        · obtain ⟨t, ht⟩ := h1 h
          rw [ht]
          exact ⟨_, rfl⟩
        · obtain ⟨ns, hns⟩ := h2 h
          rw [hns]
          exact ⟨ns ++ [_], rfl⟩
      simp only [nestL, cObjX, cEnterX_pos hw, cContX, cSeqPart, List.length_cons, List.length_nil,
        Nat.zero_add, Nat.one_ne_zero, ↓reduceIte, Bool.false_eq_true, and_false]
      cases hi : cfg.indent with
      | some ind =>
        obtain ⟨k1, k2⟩ := key (lvl + 1) (XVal.seq tList [nestL k] :: anc)
          (.ok (cfg.itemSep.raw ++ cNewlineIndent ind (lvl + 1)))
        refine ⟨fun h => ?_, fun h => ?_⟩
        · obtain ⟨t, ht⟩ := k1 h
          simp only [ht]
          exact ⟨_, rfl⟩
        · obtain ⟨ns, hns⟩ := k2 h
          simp only [hns]
          exact ⟨ns, rfl⟩
      | none =>
        obtain ⟨k1, k2⟩ := key lvl (XVal.seq tList [nestL k] :: anc) (writeStrObj cfg.itemSep)
        refine ⟨fun h => ?_, fun h => ?_⟩
        · obtain ⟨t, ht⟩ := k1 h
          simp only [ht]
          exact ⟨_, rfl⟩
        · obtain ⟨ns, hns⟩ := k2 h
          simp only [hns]
          exact ⟨ns, rfl⟩
    · have hb := thr_big (k := k + 1) hw
      exact ⟨fun h => by omega, fun _ => ⟨[], by simp [nestL, cObjX, cEnterX, hw, xe]⟩⟩

theorem encNestPy (cfg : XCfg) : ∀ (k b lvl : Nat) (seen : List Nat) (anc : List XVal),
    (k + 1 ≤ b → ∃ t, pyIterX cfg b lvl seen anc (nestL k) = .ok t) ∧
    (b < k + 1 → IsRecPyX (pyIterX cfg b lvl seen anc (nestL k))) := by
  intro k
  induction k with
  | zero =>
    intro b lvl seen anc
    cases b with
    | zero => exact ⟨fun h => by omega, fun _ => ⟨([], []), by simp [nestL, pyIterX, pyCallX, xe]⟩⟩
    | succ b =>
      refine ⟨fun _ => ⟨cs "[]", ?_⟩, fun h => by omega⟩
      simp [nestL, pyIterX, pyCallX, pyContX, pyListPart]
  | succ k ih =>
    intro b lvl seen anc
    cases b with
    | zero => exact ⟨fun h => by omega, fun _ => ⟨([], []), by simp [nestL, pyIterX, pyCallX, xe]⟩⟩
    | succ b =>
      have key : ∀ lvl' anc' buf0 sep, (k + 1 ≤ b → ∃ t, pyListItemsX cfg b lvl' seen anc' tList buf0 sep 0 [nestL k] = .ok t) ∧
          (b < k + 1 → IsRecPyX (pyListItemsX cfg b lvl' seen anc' tList buf0 sep 0 [nestL k])) := by
        intro lvl' anc' buf0 sep
        obtain ⟨h1, h2⟩ := ih b lvl' seen anc'
        have hi : pyItemX cfg b lvl' seen anc' (nestL k) = pyIterX cfg b lvl' seen anc' (nestL k) := by
          cases k <;> simp [nestL, pyItemX]
        simp only [pyListItemsX, hi]
        refine ⟨fun h => ?_, fun h => ?_⟩
        · obtain ⟨t, ht⟩ := h1 h
          rw [ht]
          exact ⟨_, rfl⟩
        · obtain ⟨⟨ns, cx⟩, hns⟩ := h2 h
          rw [hns]
          exact ⟨(ns ++ [_], cx), rfl⟩
      simp only [nestL, pyIterX, pyCallX, pyContX, pyListPart, List.isEmpty_cons, Bool.not_false,
        Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.and_false, and_false]
      cases hi : cfg.indent with
      | some ind =>
        obtain ⟨k1, k2⟩ := key (lvl + 1) (XVal.seq tList [nestL k] :: anc) ([91] ++ [10] ++ rep ind (lvl + 1))
          (cfg.itemSep.raw ++ [10] ++ rep ind (lvl + 1))
        refine ⟨fun h => ?_, fun h => ?_⟩
        · obtain ⟨t, ht⟩ := k1 (by omega)
          simp only [ht]
          exact ⟨_, rfl⟩
        · obtain ⟨ns, hns⟩ := k2 (by omega)
          simp only [hns]
          exact ⟨ns, rfl⟩
      | none =>
        obtain ⟨k1, k2⟩ := key lvl (XVal.seq tList [nestL k] :: anc) [91] cfg.itemSep.raw
        refine ⟨fun h => ?_, fun h => ?_⟩
        · obtain ⟨t, ht⟩ := k1 (by omega)
          simp only [ht]
          exact ⟨_, rfl⟩
        · obtain ⟨ns, hns⟩ := k2 (by omega)
          simp only [hns]
          exact ⟨ns, rfl⟩

theorem dumpsCX_nest (cfg : XCfg) (c k : Nat) :
    ((k + 1) * (cfg.stk .seq + 1) ≤ c → ∃ t, dumpsCX cfg c (nestL k) = .ok t) ∧
    (c < (k + 1) * (cfg.stk .seq + 1) → ∃ ns, dumpsCX cfg c (nestL k) = .error (recEncC, ns, [])) := by
  have : dumpsCX cfg c (nestL k) = cObjX cfg c 0 [] [] (nestL k) := by cases k <;> rfl
  rw [this]
  exact encNestC cfg k c 0 [] []

theorem dumpsPyX_nest (cfg : XCfg) (p k : Nat) :
    (k + 3 ≤ p → ∃ t, dumpsPyX cfg p (nestL k) = .ok t) ∧ (p < k + 3 → IsRecPyX (dumpsPyX cfg p (nestL k))) := by
  have : dumpsPyX cfg p (nestL k) = iterJoinPyX cfg p (nestL k) := by cases k <;> rfl
  rw [this]
  unfold iterJoinPyX
  match p with
  | 0 => exact ⟨fun h => by omega, fun _ => ⟨([], []), rfl⟩⟩
  | 1 => exact ⟨fun h => by omega, fun _ => ⟨([], []), rfl⟩⟩
  | p + 2 =>
    simp only [pyCallX]
    obtain ⟨h1, h2⟩ := encNestPy cfg k p 0 [] []
    exact ⟨fun h => h1 (by omega), fun h => h2 (by omega)⟩

/-! ### Nested dicts and `default` chains -/

/-- `{"a": {"a": ... {}}}`, `k + 1` dicts deep. -/
def nestD : Nat → XVal
  | 0 => .map tDict []
  | k + 1 => .map tDict [(.str [97], nestD k)]

theorem nestD_okx (k : Nat) : (nestD k).okx = true := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [nestD, XVal.okx, XVal.okxItems, XKey.okx, ih, Bool.and_true]
    decide

/-- What a dict nesting raises in C once a dict guard fails, seen from room `x`: the guard's
`RecursionError` when the outermost guard failed or the innermost entered dict's `%R` note had its
stack (`R <= x % W`); otherwise the repr's `RecursionError`, whose `__context__` chain is repr errors
without notes ending in the guard's error without notes. Notes were added only where the repr had
its stack. `W` is a dict level's cost, `R` the repr's. -/
def DictFail {α : Type} (cfg : XCfg) (x : Nat) (r : Except XErr α) : Prop :=
  ∃ e ns cx, r = .error (e, ns, cx) ∧ (ns ≠ [] → cfg.stk .repr + 1 + (cfg.stk .map + 1) ≤ x) ∧
    ((e = recEncC ∧ cx = [] ∧ (x < cfg.stk .map + 1 ∨ cfg.stk .repr + 1 ≤ x % (cfg.stk .map + 1))) ∨
     (e = recRepr ∧ cfg.stk .map + 1 ≤ x ∧ x % (cfg.stk .map + 1) < cfg.stk .repr + 1 ∧
       ∃ m, cx = List.replicate m (recRepr, []) ++ [(recEncC, [])]))

theorem dictFail_step {α : Type} {cfg : XCfg} {c' : Nat} {n : Note} {r : Except XErr α}
    (h : DictFail cfg c' r) : DictFail cfg (c' + (cfg.stk .map + 1)) (cFormatNoteR cfg c' n r) := by
  obtain ⟨e, ns, cx, rfl, hinv, hcase⟩ := h
  have hmod : (c' + (cfg.stk .map + 1)) % (cfg.stk .map + 1) = c' % (cfg.stk .map + 1) := Nat.add_mod_right _ _
  have hle : c' % (cfg.stk .map + 1) ≤ c' := Nat.mod_le _ _
  unfold DictFail
  rw [hmod]
  by_cases hR : cfg.stk .repr + 1 ≤ c'
  · simp only [cFormatNoteR, hR, ↓reduceIte]
    refine ⟨e, ns ++ [n], cx, rfl, fun _ => by omega, ?_⟩
    rcases hcase with ⟨rfl, rfl, h1 | h1⟩ | ⟨rfl, h1, h2, h3⟩
    · left
      refine ⟨rfl, rfl, Or.inr ?_⟩
      rw [Nat.mod_eq_of_lt h1]; exact hR
    · exact Or.inl ⟨rfl, rfl, Or.inr h1⟩
    · exact Or.inr ⟨rfl, by omega, h2, h3⟩
  · simp only [cFormatNoteR, hR, ↓reduceIte]
    have hns : ns = [] := by
      cases ns with
      | nil => rfl
      | cons a l => have := hinv (List.cons_ne_nil a l); omega
    subst hns
    refine ⟨recRepr, [], _, rfl, fun h => absurd rfl h, Or.inr ⟨rfl, by omega, by omega, ?_⟩⟩
    rcases hcase with ⟨rfl, rfl, _⟩ | ⟨rfl, _, _, m, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨m + 1, rfl⟩

theorem encNestDC {cfg : XCfg} (hO : cfg.Okx) : ∀ (k c lvl : Nat) (seen : List Nat) (anc : List XVal),
    ((k + 1) * (cfg.stk .map + 1) ≤ c → ∃ t, cObjX cfg c lvl seen anc (nestD k) = .ok t) ∧
    (c < (k + 1) * (cfg.stk .map + 1) → DictFail cfg c (cObjX cfg c lvl seen anc (nestD k))) := by
  intro k
  induction k with
  | zero =>
    intro c lvl seen anc
    rw [Nat.zero_add, Nat.one_mul]
    by_cases hw : cfg.stk .map + 1 ≤ c
    · refine ⟨fun _ => ⟨cs "{}", ?_⟩, fun h => by omega⟩
      simp only [nestD, cObjX, cEnterX_pos hw, cContX]
      unfold cMapPart
      simp
    · refine ⟨fun h => by omega, fun _ => ⟨recEncC, [], [], ?_, fun h => absurd rfl h, Or.inl ⟨rfl, rfl, Or.inl (by omega)⟩⟩⟩
      simp [nestD, cObjX, cEnterX, hw, xe]
  | succ k ih =>
    intro c lvl seen anc
    by_cases hw : cfg.stk .map + 1 ≤ c
    · rw [thr_le hw, thr_lt hw]
      have key : ∀ lvl' anc' sep nl,
          ((k + 1) * (cfg.stk .map + 1) ≤ c - (cfg.stk .map + 1) → ∃ t,
            cMapItemsX cfg (c - (cfg.stk .map + 1)) lvl' seen anc' tDict sep nl true [(.tup, .str [97], nestD k)] = .ok t) ∧
          (c - (cfg.stk .map + 1) < (k + 1) * (cfg.stk .map + 1) → DictFail cfg c
            (cMapItemsX cfg (c - (cfg.stk .map + 1)) lvl' seen anc' tDict sep nl true [(.tup, .str [97], nestD k)])) := by
        intro lvl' anc' sep nl
        obtain ⟨h1, h2⟩ := ih (c - (cfg.stk .map + 1)) lvl' seen anc'
        simp only [cMapItemsX, cKeyX, ↓reduceIte, cWriteStringX_std hO.cst, writeStrObj, hO.ksep]
        refine ⟨fun h => ?_, fun h => ?_⟩
        · obtain ⟨t, ht⟩ := h1 h
          rw [ht]
          exact ⟨_, rfl⟩
        · obtain ⟨e, ns, cx, he, hrest⟩ := h2 h
          have hd := dictFail_step (α := PStr × Bool) (n := .key tDict (cNoteKey (.str [97])))
            (r := .error (e, ns, cx)) ⟨e, ns, cx, rfl, hrest⟩
          rw [show c - (cfg.stk .map + 1) + (cfg.stk .map + 1) = c by omega] at hd
          simp only [he]
          exact hd
      have hI : cExactItems cfg [(.str [97], nestD k)] = .ok [(.tup, .str [97], nestD k)] := by
        cases hs : cfg.sortKeys <;> simp [cExactItems, hs, xSortItems, Except.map]
      simp only [nestD, cObjX, cEnterX_pos hw, cContX]
      unfold cMapPart
      simp only [hI, List.length_cons, List.length_nil,
        Nat.zero_add, Nat.one_ne_zero, decide_false, Bool.false_eq_true, ↓reduceIte, and_false]
      cases hi : cfg.indent with
      | some ind =>
        obtain ⟨k1, k2⟩ := key (lvl + 1) (XVal.map tDict [(.str [97], nestD k)] :: anc)
          (.ok (cfg.itemSep.raw ++ cNewlineIndent ind (lvl + 1))) (cNewlineIndent ind (lvl + 1))
        refine ⟨fun h => ?_, fun h => ?_⟩
        · obtain ⟨⟨t, f⟩, ht⟩ := k1 h
          simp only [ht]
          exact ⟨_, rfl⟩
        · obtain ⟨e, ns, cx, he, hrest⟩ := k2 h
          simp only [he]
          exact ⟨e, ns, cx, rfl, hrest⟩
      | none =>
        obtain ⟨k1, k2⟩ := key lvl (XVal.map tDict [(.str [97], nestD k)] :: anc) (writeStrObj cfg.itemSep) []
        refine ⟨fun h => ?_, fun h => ?_⟩
        · obtain ⟨⟨t, f⟩, ht⟩ := k1 h
          simp only [ht]
          exact ⟨_, rfl⟩
        · obtain ⟨e, ns, cx, he, hrest⟩ := k2 h
          simp only [he]
          exact ⟨e, ns, cx, rfl, hrest⟩
    · have hb := thr_big (k := k + 1) hw
      refine ⟨fun h => by omega, fun _ => ⟨recEncC, [], [], ?_, fun h => absurd rfl h, Or.inl ⟨rfl, rfl, Or.inl (by omega)⟩⟩⟩
      simp [nestD, cObjX, cEnterX, hw, xe]

theorem needsReplace_a (ascii : Bool) : needsReplace ascii [97] = false := by
  cases ascii <;> decide

theorem encNestDPy (cfg : XCfg) : ∀ (k b lvl : Nat) (seen : List Nat) (anc : List XVal),
    (k + 1 ≤ b → ∃ t, pyIterX cfg b lvl seen anc (nestD k) = .ok t) ∧
    (b < k + 1 → IsRecPyX (pyIterX cfg b lvl seen anc (nestD k))) := by
  intro k
  induction k with
  | zero =>
    intro b lvl seen anc
    cases b with
    | zero => exact ⟨fun h => by omega, fun _ => ⟨([], []), by simp [nestD, pyIterX, pyCallX, xe]⟩⟩
    | succ b =>
      refine ⟨fun _ => ⟨cs "{}", ?_⟩, fun h => by omega⟩
      simp only [nestD, pyIterX, pyCallX, pyContX]
      unfold pyDictPart
      simp
  | succ k ih =>
    intro b lvl seen anc
    cases b with
    | zero => exact ⟨fun h => by omega, fun _ => ⟨([], []), by simp [nestD, pyIterX, pyCallX, xe]⟩⟩
    | succ b =>
      have key : ∀ lvl' anc' nl sep,
          (k + 1 ≤ b → ∃ t, pyDictItemsX cfg b lvl' seen anc' tDict nl sep true [(.tup, .str [97], nestD k)] = .ok t) ∧
          (b < k + 1 → IsRecPyX (pyDictItemsX cfg b lvl' seen anc' tDict nl sep true [(.tup, .str [97], nestD k)])) := by
        intro lvl' anc' nl sep
        obtain ⟨h1, h2⟩ := ih b lvl' seen anc'
        have hi : pyItemX cfg b lvl' seen anc' (nestD k) = pyIterX cfg b lvl' seen anc' (nestD k) := by
          cases k <;> simp [nestD, pyItemX]
        cases b with
        | zero =>
          refine ⟨fun h => by omega, fun _ => ⟨([], []), ?_⟩⟩
          simp [pyDictItemsX, pyKeyX, pyEncStrX, pyCallX, xe]
        | succ b =>
          simp only [pyDictItemsX, pyKeyX, pyEncStrX, pyCallX, needsReplace_a, Bool.false_eq_true,
            ↓reduceIte, hi]
          refine ⟨fun h => ?_, fun h => ?_⟩
          · obtain ⟨t, ht⟩ := h1 h
            rw [ht]
            exact ⟨_, rfl⟩
          · obtain ⟨⟨ns, cx⟩, hns⟩ := h2 h
            rw [hns]
            exact ⟨(ns ++ [_], cx), rfl⟩
      have hI : pyExactItems cfg [(.str [97], nestD k)] = .ok [(.tup, .str [97], nestD k)] := by
        cases hs : cfg.sortKeys <;> simp [pyExactItems, cExactItems, hs, xSortItems, Except.map]
      simp only [nestD, pyIterX, pyCallX, pyContX]
      unfold pyDictPart
      simp only [hI, Except.map, List.isEmpty_cons,
        Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte, and_false]
      cases hi : cfg.indent with
      | some ind =>
        obtain ⟨k1, k2⟩ := key (lvl + 1) (XVal.map tDict [(.str [97], nestD k)] :: anc)
          ([10] ++ rep ind (lvl + 1)) (cfg.itemSep.raw ++ [10] ++ rep ind (lvl + 1))
        refine ⟨fun h => ?_, fun h => ?_⟩
        · obtain ⟨⟨t, f⟩, ht⟩ := k1 (by omega)
          simp only [ht]
          exact ⟨_, rfl⟩
        · obtain ⟨ns, hns⟩ := k2 (by omega)
          simp only [hns]
          exact ⟨ns, rfl⟩
      | none =>
        obtain ⟨k1, k2⟩ := key lvl (XVal.map tDict [(.str [97], nestD k)] :: anc) [] cfg.itemSep.raw
        refine ⟨fun h => ?_, fun h => ?_⟩
        · obtain ⟨⟨t, f⟩, ht⟩ := k1 (by omega)
          simp only [ht]
          exact ⟨_, rfl⟩
        · obtain ⟨ns, hns⟩ := k2 (by omega)
          simp only [hns]
          exact ⟨ns, rfl⟩

/-- `default` turns the object `n < k` into the object `n + 1` and the object `k` into `None`. -/
def chainCfg (cfg : XCfg) (k : Nat) : XCfg :=
  { cfg with dflt := fun n t => if n < k then .ok (.other (n + 1) t) else .ok .none }

theorem chainCfg_okx {cfg : XCfg} (hO : cfg.Okx) (k : Nat) : (chainCfg cfg k).Okx :=
  ⟨hO.cst, hO.isep, hO.ksep, fun n t v' h => by
    simp only [chainCfg] at h
    split at h <;> (cases h; rfl)⟩

/-- The room one `default` level needs to go on: the guard after `default` (:1644) and, for a
Python `default`, the check on entering it. -/
def chainNeed (cfg : XCfg) : Nat :=
  if cfg.dfltPy then max (cfg.stk .call + 1) (cfg.stk .dflt + 1) else cfg.stk .dflt + 1

/-- What a `default` chain raises in C when the room runs out: the guard's `RecursionError`, or
the one of entering a Python `default` (always that one when entering costs at least the guard's
level), without `__context__`. -/
def ChainFail {α : Type} (cfg : XCfg) (r : Except XErr α) : Prop :=
  ∃ e ns, r = .error (e, ns, []) ∧ (e = recEncC ∨ e = recCall) ∧ (cfg.dfltPy = false → e = recEncC) ∧
    (cfg.dfltPy = true → cfg.stk .dflt ≤ cfg.stk .call → e = recCall)

theorem chainNeed_ge (cfg : XCfg) : cfg.stk .dflt + 1 ≤ chainNeed cfg ∧
    (cfg.dfltPy = true → cfg.stk .call + 1 ≤ chainNeed cfg) := by
  unfold chainNeed
  cases cfg.dfltPy <;> simp <;> omega

theorem chainNeed_le {cfg : XCfg} {c : Nat} (h1 : cfg.dfltPy = true → cfg.stk .call + 1 ≤ c)
    (h2 : cfg.stk .dflt + 1 ≤ c) : chainNeed cfg ≤ c := by
  unfold chainNeed
  cases hp : cfg.dfltPy
  · simpa using h2
  · have := h1 hp; simp; omega

theorem ChainFail.note {α : Type} {cfg : XCfg} {r : Except XErr α} (n : Note) (h : ChainFail cfg r) :
    ChainFail cfg (addNote n r) := by
  obtain ⟨e, ns, rfl, h1, h2, h3⟩ := h
  exact ⟨e, ns ++ [n], rfl, h1, h2, h3⟩

theorem chainStep {cfg : XCfg} {c : Nat} {v : XVal} {n : Nat} {t : PyType} {lvl : Nat} {seen : List Nat}
    {anc : List XVal} (hns : ¬ (cfg.checkCircular = true ∧ n ∈ seen)) (hd : cfg.dflt n t = .ok v) :
    cObjX cfg c lvl seen anc (.other n t) =
      if cfg.dfltPy = true ∧ c < cfg.stk .call + 1 then .error (xe recCall)
      else if cfg.stk .dflt + 1 ≤ c then
        addNote (.obj t) (cObjX cfg (c - (cfg.stk .dflt + 1)) lvl (n :: seen) anc v)
      else .error (xe recEncC) := by
  rw [cObjX]
  simp only [hns, ↓reduceIte, cCallDflt]
  by_cases hp : cfg.dfltPy = true
  · by_cases hc : cfg.stk .call + 1 ≤ c
    · simp only [hp, hc, ↓reduceIte, hd, show ¬ (c < cfg.stk .call + 1) by omega, and_false]
      by_cases hw : cfg.stk .dflt + 1 ≤ c
      · simp [cEnterX, hw]
      · simp [cEnterX, hw]
    · simp [hp, hc, show c < cfg.stk .call + 1 by omega]
  · simp only [hp, Bool.false_eq_true, ↓reduceIte, hd, false_and]
    by_cases hw : cfg.stk .dflt + 1 ≤ c
    · simp [cEnterX, hw]
    · simp [cEnterX, hw]

theorem encChainC (cfg : XCfg) (k : Nat) (t : PyType) : ∀ (m n c lvl : Nat) (seen : List Nat) (anc : List XVal),
    n + m = k → (∀ x ∈ seen, x < n) →
    (m * (cfg.stk .dflt + 1) + chainNeed cfg ≤ c → ∃ s, cObjX (chainCfg cfg k) c lvl seen anc (.other n t) = .ok s) ∧
    (c < m * (cfg.stk .dflt + 1) + chainNeed cfg → ChainFail cfg (cObjX (chainCfg cfg k) c lvl seen anc (.other n t))) := by
  have hstk : (chainCfg cfg k).stk = cfg.stk := rfl
  have hpy : (chainCfg cfg k).dfltPy = cfg.dfltPy := rfl
  obtain ⟨hg1, hg2⟩ := chainNeed_ge cfg
  intro m
  induction m with
  | zero =>
    intro n c lvl seen anc hn hs
    have hns : ¬ ((chainCfg cfg k).checkCircular = true ∧ n ∈ seen) := fun h => by have := hs n h.2; omega
    have hd : (chainCfg cfg k).dflt n t = .ok .none := by simp [chainCfg]; omega
    rw [chainStep hns hd, hstk, hpy]
    simp only [Nat.zero_mul, Nat.zero_add]
    by_cases h1 : cfg.dfltPy = true ∧ c < cfg.stk .call + 1
    · rw [if_pos h1]
      refine ⟨fun h => by have := hg2 h1.1; omega, fun _ => ⟨recCall, [], rfl, Or.inr rfl,
        fun h => by simp [h1.1] at h, fun _ _ => rfl⟩⟩
    · rw [if_neg h1]
      by_cases h2 : cfg.stk .dflt + 1 ≤ c
      · rw [if_pos h2]
        refine ⟨fun _ => ⟨cs "null", by simp [cObjX, addNote]⟩, fun h => ?_⟩
        have := chainNeed_le (cfg := cfg) (fun hp => Nat.le_of_not_lt (fun hc => h1 ⟨hp, hc⟩)) h2
        omega
      · rw [if_neg h2]
        refine ⟨fun h => by omega, fun _ => ⟨recEncC, [], rfl, Or.inl rfl, fun _ => rfl, fun hp hle => ?_⟩⟩
        exact absurd ⟨hp, by omega⟩ h1
  | succ m ih =>
    intro n c lvl seen anc hn hs
    have hns : ¬ ((chainCfg cfg k).checkCircular = true ∧ n ∈ seen) := fun h => by have := hs n h.2; omega
    have hd : (chainCfg cfg k).dflt n t = .ok (.other (n + 1) t) := by simp [chainCfg]; omega
    have hs' : ∀ x ∈ n :: seen, x < n + 1 := by
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · omega
      · have := hs x hx; omega
    rw [chainStep hns hd, hstk, hpy, Nat.succ_mul]
    generalize hA : m * (cfg.stk .dflt + 1) = A at ih ⊢
    by_cases h1 : cfg.dfltPy = true ∧ c < cfg.stk .call + 1
    · rw [if_pos h1]
      refine ⟨fun h => by have := hg2 h1.1; omega, fun _ => ⟨recCall, [], rfl, Or.inr rfl,
        fun h => by simp [h1.1] at h, fun _ _ => rfl⟩⟩
    · rw [if_neg h1]
      by_cases h2 : cfg.stk .dflt + 1 ≤ c
      · rw [if_pos h2]
        obtain ⟨i1, i2⟩ := ih (n + 1) (c - (cfg.stk .dflt + 1)) lvl (n :: seen) anc (by omega) hs'
        refine ⟨fun h => ?_, fun h => ?_⟩
        · obtain ⟨s, hs2⟩ := i1 (by omega)
          rw [hs2]
          exact ⟨s, rfl⟩
        · exact ChainFail.note _ (i2 (by omega))
      · rw [if_neg h2]
        refine ⟨fun h => by omega, fun _ => ⟨recEncC, [], rfl, Or.inl rfl, fun _ => rfl, fun hp hle => ?_⟩⟩
        exact absurd ⟨hp, by omega⟩ h1

theorem encChainPy (cfg : XCfg) (k : Nat) (t : PyType) : ∀ (m n b lvl : Nat) (seen : List Nat) (anc : List XVal),
    n + m = k → (∀ x ∈ seen, x < n) →
    (m + 1 ≤ b → ∃ s, pyIterX (chainCfg cfg k) b lvl seen anc (.other n t) = .ok s) ∧
    (b < m + 1 → IsRecPyX (pyIterX (chainCfg cfg k) b lvl seen anc (.other n t))) := by
  intro m
  induction m with
  | zero =>
    intro n b lvl seen anc hn hs
    have hns : n ∉ seen := fun h => by have := hs n h; omega
    have hd : (chainCfg cfg k).dflt n t = .ok .none := by simp [chainCfg]; omega
    rw [pyIterX]
    simp only [hns, and_false, ↓reduceIte]
    cases b with
    | zero => exact ⟨fun h => by omega, fun _ => ⟨([], []), rfl⟩⟩
    | succ b =>
      refine ⟨fun _ => ⟨cs "null", ?_⟩, fun h => by omega⟩
      simp [pyCallX, hd, liftE, pyIterX, addNote]
  | succ m ih =>
    intro n b lvl seen anc hn hs
    have hns : n ∉ seen := fun h => by have := hs n h; omega
    have hd : (chainCfg cfg k).dflt n t = .ok (.other (n + 1) t) := by simp [chainCfg]; omega
    rw [pyIterX]
    simp only [hns, and_false, ↓reduceIte]
    cases b with
    | zero => exact ⟨fun h => by omega, fun _ => ⟨([], []), rfl⟩⟩
    | succ b =>
      have hs' : ∀ x ∈ n :: seen, x < n + 1 := by
        intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · omega
        · have := hs x hx; omega
      obtain ⟨h1, h2⟩ := ih (n + 1) b lvl (n :: seen) anc (by omega) hs'
      simp only [pyCallX, hd, liftE]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · obtain ⟨s, hs2⟩ := h1 (by omega)
        rw [hs2]
        exact ⟨s, rfl⟩
      · obtain ⟨⟨ns, cx⟩, hns2⟩ := h2 (by omega)
        rw [hns2]
        exact ⟨(ns ++ [.obj t], cx), rfl⟩

theorem dumpsCX_nestD {cfg : XCfg} (hO : cfg.Okx) (c k : Nat) :
    ((k + 1) * (cfg.stk .map + 1) ≤ c → ∃ t, dumpsCX cfg c (nestD k) = .ok t) ∧
    (c < (k + 1) * (cfg.stk .map + 1) → DictFail cfg c (dumpsCX cfg c (nestD k))) := by
  have : dumpsCX cfg c (nestD k) = cObjX cfg c 0 [] [] (nestD k) := by cases k <;> rfl
  rw [this]
  exact encNestDC hO k c 0 [] []

theorem dumpsPyX_nestD (cfg : XCfg) (p k : Nat) :
    (k + 3 ≤ p → ∃ t, dumpsPyX cfg p (nestD k) = .ok t) ∧ (p < k + 3 → IsRecPyX (dumpsPyX cfg p (nestD k))) := by
  have : dumpsPyX cfg p (nestD k) = iterJoinPyX cfg p (nestD k) := by cases k <;> rfl
  rw [this]
  unfold iterJoinPyX
  match p with
  | 0 => exact ⟨fun h => by omega, fun _ => ⟨([], []), rfl⟩⟩
  | 1 => exact ⟨fun h => by omega, fun _ => ⟨([], []), rfl⟩⟩
  | p + 2 =>
    simp only [pyCallX]
    obtain ⟨h1, h2⟩ := encNestDPy cfg k p 0 [] []
    exact ⟨fun h => h1 (by omega), fun h => h2 (by omega)⟩

theorem dumpsCX_chain (cfg : XCfg) (c k : Nat) (t : PyType) :
    (k * (cfg.stk .dflt + 1) + chainNeed cfg ≤ c → ∃ s, dumpsCX (chainCfg cfg k) c (.other 0 t) = .ok s) ∧
    (c < k * (cfg.stk .dflt + 1) + chainNeed cfg → ChainFail cfg (dumpsCX (chainCfg cfg k) c (.other 0 t))) :=
  encChainC cfg k t k 0 c 0 [] [] (by omega) (by simp)

theorem dumpsPyX_chain (cfg : XCfg) (p k : Nat) (t : PyType) :
    (k + 3 ≤ p → ∃ s, dumpsPyX (chainCfg cfg k) p (.other 0 t) = .ok s) ∧
    (p < k + 3 → IsRecPyX (dumpsPyX (chainCfg cfg k) p (.other 0 t))) := by
  simp only [dumpsPyX, iterJoinPyX]
  match p with
  | 0 => exact ⟨fun h => by omega, fun _ => ⟨([], []), rfl⟩⟩
  | 1 => exact ⟨fun h => by omega, fun _ => ⟨([], []), rfl⟩⟩
  | p + 2 =>
    simp only [pyCallX]
    obtain ⟨h1, h2⟩ := encChainPy cfg k t k 0 p 0 [] [] (by omega) (by simp)
    exact ⟨fun h => h1 (by omega), fun h => h2 (by omega)⟩

/-! ### The narrowed twin theorem -/

/-- `json.dumps` with `c_make_encoder` (stack room `c`) and without `_json` (`p` frames), for
every option, every value with exact containers (`list`, `tuple`, `dict`, `frozendict`), exact-`str`
separators, no custom encoder, `default` returning such values, and key types whose `tp_name`
(cut to 100 bytes) is their `__name__` (type invariants: code points at most 0x10FFFF, ASCII
`float.__repr__`):
1. when neither raises its `RecursionError`, the same text, or the same exception (class and
   message) whose notes correspond one to one: the same kind of note on the same type with the
   same index; a dict item's note names the original key in C and the key's converted text in
   Python;
2. `[[...[]...]]` `k + 1` deep is encoded by C exactly when `k + 1` list levels fit in the room
   (`(k + 1) * cost <= c`, the guard of :1606), and otherwise raises that guard's `RecursionError`
   ('... while encoding a JSON object') without `__context__`; by Python exactly when `k + 3 <= p`
   (two frames for `_iterencode_once` and `_iterencode`), and otherwise `RecursionError`;
3. `{"a": {"a": ... {}}}` `k + 1` deep is encoded by C exactly when `k + 1` dict levels fit (the
   guard of :1613), and otherwise raises `DictFail`: the guard's `RecursionError` only when the
   innermost entered dict's `%R` note (:1732) still has the repr's stack, else the repr's
   `RecursionError` ('... while getting the repr of an object') whose `__context__` chain is repr
   errors ending in the guard's error (`_PyErr_FormatNote`, Python/errors.c:1281-1292); Python as
   in 2;
4. an object that `default` turns into another one `k` times, then into `None`, is encoded by C
   exactly when `k` levels of the guard after `default` (:1644) and the last one's need fit
   (`chainNeed`: the guard's cost and, for a Python `default`, the cost of entering it), and
   otherwise raises `ChainFail`: for a C `default` the guard's `RecursionError`, for a Python one
   whose entering costs at least a guard's level `RecursionError('Stack overflow (used N kB)')` from
   entering `default` (:1638); Python as in 2.
Each check's cost is a parameter (`XCfg.stk`, the C frames between two checks). CPython 3.15.2 on
x86-64 encodes 47456 nested lists, 29001 nested dicts and 47453 Python-`default` results in the main
thread's stack; past the dict limit it raises the repr's `RecursionError` with a chain of three, and
past the `default` limit the bare 'Stack overflow' one (operator.attrgetter as `default`: the
guard's). -/
def DumpsTwinsX : Prop :=
  ∀ (cfg : XCfg) (c p : Nat) (v : XVal), cfg.Okx → v.okx = true →
    (¬ IsRecCX (dumpsCX cfg c v) → ¬ IsRecPyX (dumpsPyX cfg p v) →
      (∃ t, dumpsCX cfg c v = .ok t ∧ dumpsPyX cfg p v = .ok t) ∨
      (∃ e nsC nsP, dumpsCX cfg c v = .error (e, nsC, []) ∧ dumpsPyX cfg p v = .error (e, nsP, []) ∧
        NotesRel cfg nsC nsP)) ∧
    (∀ k, ((k + 1) * (cfg.stk .seq + 1) ≤ c → ∃ t, dumpsCX cfg c (nestL k) = .ok t) ∧
      (c < (k + 1) * (cfg.stk .seq + 1) → ∃ ns, dumpsCX cfg c (nestL k) = .error (recEncC, ns, []))) ∧
    (∀ k, (k + 3 ≤ p → ∃ t, dumpsPyX cfg p (nestL k) = .ok t) ∧ (p < k + 3 → IsRecPyX (dumpsPyX cfg p (nestL k)))) ∧
    (∀ k, ((k + 1) * (cfg.stk .map + 1) ≤ c → ∃ t, dumpsCX cfg c (nestD k) = .ok t) ∧
      (c < (k + 1) * (cfg.stk .map + 1) → DictFail cfg c (dumpsCX cfg c (nestD k)))) ∧
    (∀ k, (k + 3 ≤ p → ∃ t, dumpsPyX cfg p (nestD k) = .ok t) ∧ (p < k + 3 → IsRecPyX (dumpsPyX cfg p (nestD k)))) ∧
    (∀ k t, (k * (cfg.stk .dflt + 1) + chainNeed cfg ≤ c → ∃ s, dumpsCX (chainCfg cfg k) c (.other 0 t) = .ok s) ∧
      (c < k * (cfg.stk .dflt + 1) + chainNeed cfg → ChainFail cfg (dumpsCX (chainCfg cfg k) c (.other 0 t)))) ∧
    (∀ k t, (k + 3 ≤ p → ∃ s, dumpsPyX (chainCfg cfg k) p (.other 0 t) = .ok s) ∧
      (p < k + 3 → IsRecPyX (dumpsPyX (chainCfg cfg k) p (.other 0 t))))

theorem dumpsX_rel {cfg : XCfg} (hO : cfg.Okx) (c p : Nat) (v : XVal) (hv : v.okx = true) :
    XRelW cfg Eq (dumpsCX cfg c v) (dumpsPyX cfg p v) := by
  cases v with
  | str s =>
    simp only [dumpsCX, dumpsPyX]
    have := strLeaf hO p s hv
    rwa [cWriteStringX_std hO.cst] at this
  | _ =>
    simp only [dumpsCX, dumpsPyX, iterJoinPyX]
    match p with
    | 0 => exact XRelW.recPy ⟨([], []), rfl⟩
    | 1 => exact XRelW.recPy ⟨([], []), rfl⟩
    | p + 2 => simp only [pyCallX]; exact simX hO c p 0 [] [] _ (fun _ h => by simp at h) hv

theorem dumpsTwinsX_proven : DumpsTwinsX := by
  intro cfg c p v hO hv
  refine ⟨fun h1 h2 => ?_, fun k => dumpsCX_nest cfg c k, fun k => dumpsPyX_nest cfg p k,
    fun k => dumpsCX_nestD hO c k, fun k => dumpsPyX_nestD cfg p k, fun k t => dumpsCX_chain cfg c k t,
    fun k t => dumpsPyX_chain cfg p k t⟩
  rcases dumpsX_rel hO c p v hv with ⟨a, b, ha, hb, rfl⟩ | h | h | h
  · exact Or.inl ⟨a, ha, hb⟩
  · exact Or.inr h
  · exact absurd h h1
  · exact absurd h h2

/-- `_make_iterencode(...)(o, _current_indent_level)` without `_json`, `p` frames left where it
is driven. -/
def iterencodePyX (cfg : XCfg) (p : Nat) (v : XVal) (lvl : Nat) : XR :=
  pyCallX p fun p' _ => pyCallX p' fun p'' _ => pyIterX cfg p'' lvl [] [] v

/-- `c_make_encoder(...)(o, level)` (`encoder_call`) for every `level`, on the values and options
of `DumpsTwinsX`:
1. `OverflowError` outside `Py_ssize_t`;
   (every statement is for every behaviour `alloc` of `malloc`)
2. with an `indent`, a failure of `create_indent_cache` is the result whatever the value, in
   particular `OverflowError('repeated string is too long')` when `len(indent) > PY_SSIZE_T_MAX /
   level` from level 2 (`IndentCacheSpec` gives every outcome of the cache);
3. below level 0 the cache is `['\n']` and the call gives what level 0 gives;
4. for `level >= 0`, when `malloc` gave the cache (no indent, or `create_indent_cache` returned), when
   neither twin raises its `RecursionError`, the 1-tuple of the text of
   `_make_iterencode(...)(o, level)`, or the same exception with corresponding notes.
Scope: allocation after `create_indent_cache` does not fail (the writer, the cache's other
entries, Python's `_indent * level`), as everywhere in the encoder models; the refuted
`EncoderCallTwins` shows that 4 needs the cache. A negative level indents differently in
`_make_iterencode`, whose model takes a `Nat` level. -/
def EncoderCallX : Prop :=
  ∀ (alloc : Alloc) (cfg : XCfg) (c p : Nat) (v : XVal) (level : Int), cfg.Okx → v.okx = true →
    (outOfSsize level → encoderCallX alloc cfg c v level = .error (xe ssizeErr)) ∧
    (∀ ind e, cfg.indent = some ind → ¬ outOfSsize level → createIndentCache alloc ind level = .error e →
      encoderCallX alloc cfg c v level = .error (xe e)) ∧
    (∀ ind, cfg.indent = some ind → ¬ outOfSsize level → 2 ≤ level → (ind.length : Int) > ssizeMax / level →
      encoderCallX alloc cfg c v level = .error (xe (.overflowError "repeated string is too long"))) ∧
    (level < 0 → ¬ outOfSsize level →
      (∀ ind, cfg.indent = some ind → createIndentCache alloc ind level = .ok [[10]]) ∧
      encoderCallX alloc cfg c v level = encoderCallX alloc cfg c v 0) ∧
    (0 ≤ level → ¬ outOfSsize level →
      (∀ ind, cfg.indent = some ind → ∃ cache, createIndentCache alloc ind level = .ok cache) →
      ¬ IsRecCX (cObjX cfg c level.toNat [] [] v) →
      ¬ IsRecPyX (iterencodePyX cfg p v level.toNat) →
      (∃ t, encoderCallX alloc cfg c v level = .ok [t] ∧ iterencodePyX cfg p v level.toNat = .ok t) ∨
      (∃ e nsC nsP, encoderCallX alloc cfg c v level = .error (e, nsC, []) ∧
        iterencodePyX cfg p v level.toNat = .error (e, nsP, []) ∧ NotesRel cfg nsC nsP))

theorem encoderCallX_cacheErr {alloc : Alloc} {cfg : XCfg} {c : Nat} {v : XVal} {level : Int} {ind : PStr} {e : PyExc}
    (hi : cfg.indent = some ind) (hs : ¬ outOfSsize level) (he : createIndentCache alloc ind level = .error e) :
    encoderCallX alloc cfg c v level = .error (xe e) := by
  unfold encoderCallX
  rw [if_neg (by simpa using hs)]
  simp [hi, he, Except.map]

theorem encoderCallX_ok {alloc : Alloc} {cfg : XCfg} {c : Nat} {v : XVal} {level : Int} (hs : ¬ outOfSsize level)
    (hc : ∀ ind, cfg.indent = some ind → ∃ cache, createIndentCache alloc ind level = .ok cache) :
    encoderCallX alloc cfg c v level = (match cObjX cfg c (cacheCopies level) [] [] v with
      | .ok t => .ok [t]
      | .error e => .error e) := by
  unfold encoderCallX
  rw [if_neg (by simpa using hs)]
  cases hi : cfg.indent with
  | none => rfl
  | some ind =>
    obtain ⟨cache, hca⟩ := hc ind hi
    simp only [hca, Except.map]
    rfl

theorem encoderCallX_proven : EncoderCallX := by
  intro alloc cfg c p v level hO hv
  refine ⟨fun h => by simp [encoderCallX, h], fun ind e hi hs he => encoderCallX_cacheErr hi hs he,
    fun ind hi hs h2 hov => encoderCallX_cacheErr hi hs (createIndentCache_ovf alloc ind h2 hov),
    fun h1 h2 => ?_, fun h0 h1 hca hc hp => ?_⟩
  · have hneg : ∀ ind, cfg.indent = some ind → createIndentCache alloc ind level = .ok [[10]] :=
      fun ind _ => createIndentCache_lt1 alloc ind (by omega)
    refine ⟨hneg, ?_⟩
    have h3 : ¬ outOfSsize 0 := by decide
    rw [encoderCallX_ok h2 (fun ind hi => ⟨_, hneg ind hi⟩),
      encoderCallX_ok h3 (fun ind _ => ⟨_, createIndentCache_lt1 alloc ind (by omega)⟩)]
    rw [show cacheCopies level = cacheCopies 0 by simp [cacheCopies, show level < 1 by omega]]
  · rw [encoderCallX_ok h1 hca, show cacheCopies level = level.toNat by
      unfold cacheCopies; split <;> omega]
    have hr : XRelW cfg Eq (cObjX cfg c level.toNat [] [] v) (iterencodePyX cfg p v level.toNat) := by
      unfold iterencodePyX
      match p with
      | 0 => exact XRelW.recPy ⟨([], []), rfl⟩
      | 1 => exact XRelW.recPy ⟨([], []), rfl⟩
      | p + 2 => simp only [pyCallX]; exact simX hO c p _ [] [] _ (fun _ h => by simp at h) hv
    rcases hr with ⟨a, b, ha, hb, rfl⟩ | ⟨e, nsC, nsP, ha, hb, hn⟩ | h | h
    · rw [ha]; exact Or.inl ⟨a, rfl, hb⟩
    · rw [ha]; exact Or.inr ⟨e, nsC, nsP, rfl, hb, hn⟩
    · exact absurd h hc
    · exact absurd h hp

end PyLean.JsonMod
