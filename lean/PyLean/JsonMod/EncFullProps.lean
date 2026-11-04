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
* `EncoderCallX`: `c_make_encoder(...)(o, level)` for every level.
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
  (∃ e nsC nsP, rc = .error (e, nsC) ∧ rp = .error (e, nsP) ∧ nsC.map showC = nsP.map showPy)

/-- The same text, or the same exception (class and message), whatever the notes. -/
def SameExc (rc rp : XR) : Prop :=
  (∃ t, rc = .ok t ∧ rp = .ok t) ∨ (∃ e nsC nsP, rc = .error (e, nsC) ∧ rp = .error (e, nsP))

/-! ### Nested lists and the recursion limits -/

/-- `[[...[]...]]`, `k + 1` lists deep. -/
def nestL : Nat → XVal
  | 0 => .seq tList []
  | k + 1 => .seq tList [nestL k]

theorem nestL_okx (k : Nat) : (nestL k).okx = true := by
  induction k with
  | zero => rfl
  | succ k ih => simp [nestL, XVal.okx, XVal.okxList, ih]

theorem nestC (cfg : XCfg) : ∀ (k c lvl : Nat) (seen : List Nat) (anc : List XVal),
    (k + 1 ≤ c → ∃ t, cObjX cfg c lvl seen anc (nestL k) = .ok t) ∧
    (c < k + 1 → IsRecCX (cObjX cfg c lvl seen anc (nestL k))) := by
  intro k
  induction k with
  | zero =>
    intro c lvl seen anc
    cases c with
    | zero => exact ⟨fun h => by omega, fun _ => ⟨[], by simp [nestL, cObjX, cEnterX, xe]⟩⟩
    | succ c =>
      refine ⟨fun _ => ⟨cs "[]", ?_⟩, fun h => by omega⟩
      simp [nestL, cObjX, cEnterX, cContX, cSeqPart]
  | succ k ih =>
    intro c lvl seen anc
    cases c with
    | zero => exact ⟨fun h => by omega, fun _ => ⟨[], by simp [nestL, cObjX, cEnterX, xe]⟩⟩
    | succ c =>
      have key : ∀ lvl' anc' sep, (k + 1 ≤ c → ∃ t, cSeqItemsX cfg c lvl' seen anc' tList sep 0 [nestL k] = .ok t) ∧
          (c < k + 1 → IsRecCX (cSeqItemsX cfg c lvl' seen anc' tList sep 0 [nestL k])) := by
        intro lvl' anc' sep
        obtain ⟨h1, h2⟩ := ih c lvl' seen anc'
        simp only [cSeqItemsX, ne_eq, not_true_eq_false, ↓reduceIte]
        refine ⟨fun h => ?_, fun h => ?_⟩
        · obtain ⟨t, ht⟩ := h1 h
          rw [ht]
          exact ⟨_, rfl⟩
        · obtain ⟨ns, hns⟩ := h2 h
          rw [hns]
          exact ⟨ns ++ [_], rfl⟩
      simp only [nestL, cObjX, cEnterX, cContX, cSeqPart, List.length_cons, List.length_nil,
        Nat.zero_add, Nat.one_ne_zero, ↓reduceIte, Bool.false_eq_true, and_false]
      cases hi : cfg.indent with
      | some ind =>
        obtain ⟨k1, k2⟩ := key (lvl + 1) (XVal.seq tList [nestL k] :: anc)
          (.ok (cfg.itemSep.raw ++ cNewlineIndent ind (lvl + 1)))
        refine ⟨fun h => ?_, fun h => ?_⟩
        · obtain ⟨t, ht⟩ := k1 (by omega)
          simp only [ht]
          exact ⟨_, rfl⟩
        · obtain ⟨ns, hns⟩ := k2 (by omega)
          simp only [hns]
          exact ⟨ns, rfl⟩
      | none =>
        obtain ⟨k1, k2⟩ := key lvl (XVal.seq tList [nestL k] :: anc) (writeStrObj cfg.itemSep)
        refine ⟨fun h => ?_, fun h => ?_⟩
        · obtain ⟨t, ht⟩ := k1 (by omega)
          simp only [ht]
          exact ⟨_, rfl⟩
        · obtain ⟨ns, hns⟩ := k2 (by omega)
          simp only [hns]
          exact ⟨ns, rfl⟩

theorem nestPy (cfg : XCfg) : ∀ (k b lvl : Nat) (seen : List Nat) (anc : List XVal),
    (k + 1 ≤ b → ∃ t, pyIterX cfg b lvl seen anc (nestL k) = .ok t) ∧
    (b < k + 1 → IsRecPyX (pyIterX cfg b lvl seen anc (nestL k))) := by
  intro k
  induction k with
  | zero =>
    intro b lvl seen anc
    cases b with
    | zero => exact ⟨fun h => by omega, fun _ => ⟨[], by simp [nestL, pyIterX, pyCallX, xe]⟩⟩
    | succ b =>
      refine ⟨fun _ => ⟨cs "[]", ?_⟩, fun h => by omega⟩
      simp [nestL, pyIterX, pyCallX, pyContX, pyListPart]
  | succ k ih =>
    intro b lvl seen anc
    cases b with
    | zero => exact ⟨fun h => by omega, fun _ => ⟨[], by simp [nestL, pyIterX, pyCallX, xe]⟩⟩
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
        · obtain ⟨ns, hns⟩ := h2 h
          rw [hns]
          exact ⟨ns ++ [_], rfl⟩
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
    (k + 1 ≤ c → ∃ t, dumpsCX cfg c (nestL k) = .ok t) ∧ (c < k + 1 → IsRecCX (dumpsCX cfg c (nestL k))) := by
  have : dumpsCX cfg c (nestL k) = cObjX cfg c 0 [] [] (nestL k) := by cases k <;> rfl
  rw [this]
  exact nestC cfg k c 0 [] []

theorem dumpsPyX_nest (cfg : XCfg) (p k : Nat) :
    (k + 3 ≤ p → ∃ t, dumpsPyX cfg p (nestL k) = .ok t) ∧ (p < k + 3 → IsRecPyX (dumpsPyX cfg p (nestL k))) := by
  have : dumpsPyX cfg p (nestL k) = iterJoinPyX cfg p (nestL k) := by cases k <;> rfl
  rw [this]
  unfold iterJoinPyX
  match p with
  | 0 => exact ⟨fun h => by omega, fun _ => ⟨[], rfl⟩⟩
  | 1 => exact ⟨fun h => by omega, fun _ => ⟨[], rfl⟩⟩
  | p + 2 =>
    simp only [pyCallX]
    obtain ⟨h1, h2⟩ := nestPy cfg k p 0 [] []
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
2. `[[...[]...]]` `k + 1` deep is encoded by C exactly when `k + 1 <= c` and by Python exactly
   when `k + 3 <= p` (two frames for `_iterencode_once` and `_iterencode`), and otherwise raises
   the `RecursionError`. -/
def DumpsTwinsX : Prop :=
  ∀ (cfg : XCfg) (c p : Nat) (v : XVal), cfg.Okx → v.okx = true →
    (¬ IsRecCX (dumpsCX cfg c v) → ¬ IsRecPyX (dumpsPyX cfg p v) →
      (∃ t, dumpsCX cfg c v = .ok t ∧ dumpsPyX cfg p v = .ok t) ∨
      (∃ e nsC nsP, dumpsCX cfg c v = .error (e, nsC) ∧ dumpsPyX cfg p v = .error (e, nsP) ∧
        NotesRel cfg nsC nsP)) ∧
    (∀ k, (k + 1 ≤ c → ∃ t, dumpsCX cfg c (nestL k) = .ok t) ∧ (c < k + 1 → IsRecCX (dumpsCX cfg c (nestL k)))) ∧
    (∀ k, (k + 3 ≤ p → ∃ t, dumpsPyX cfg p (nestL k) = .ok t) ∧ (p < k + 3 → IsRecPyX (dumpsPyX cfg p (nestL k))))

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
    | 0 => exact XRelW.recPy ⟨[], rfl⟩
    | 1 => exact XRelW.recPy ⟨[], rfl⟩
    | p + 2 => simp only [pyCallX]; exact simX hO c p 0 [] [] _ (fun _ h => by simp at h) hv

theorem dumpsTwinsX_proven : DumpsTwinsX := by
  intro cfg c p v hO hv
  refine ⟨fun h1 h2 => ?_, fun k => dumpsCX_nest cfg c k, fun k => dumpsPyX_nest cfg p k⟩
  rcases dumpsX_rel hO c p v hv with ⟨a, b, ha, hb, rfl⟩ | h | h | h
  · exact Or.inl ⟨a, ha, hb⟩
  · exact Or.inr h
  · exact absurd h h1
  · exact absurd h h2

/-- `_make_iterencode(...)(o, _current_indent_level)` without `_json`, `p` frames left where it
is driven. -/
def iterencodePyX (cfg : XCfg) (p : Nat) (v : XVal) (lvl : Nat) : XR :=
  pyCallX p fun p' _ => pyCallX p' fun p'' _ => pyIterX cfg p'' lvl [] [] v

/-- `c_make_encoder(...)(o, level)` (`encoder_call`) for every `level`: `OverflowError` outside
`Py_ssize_t`; a negative level gives what level 0 gives (the cache starts from `'\n'`); and for
`level >= 0`, on the values of `DumpsTwinsX`, when neither twin raises its `RecursionError`, the
1-tuple of the text of `_make_iterencode(...)(o, level)`, or the same exception with
corresponding notes. -/
def EncoderCallX : Prop :=
  ∀ (cfg : XCfg) (c p : Nat) (v : XVal) (level : Int), cfg.Okx → v.okx = true →
    (outOfSsize level → encoderCallX cfg c v level = .error (xe ssizeErr)) ∧
    (level < 0 → ¬ outOfSsize level → encoderCallX cfg c v level = encoderCallX cfg c v 0) ∧
    (0 ≤ level → ¬ outOfSsize level → ¬ IsRecCX (cObjX cfg c level.toNat [] [] v) →
      ¬ IsRecPyX (iterencodePyX cfg p v level.toNat) →
      (∃ t, encoderCallX cfg c v level = .ok [t] ∧ iterencodePyX cfg p v level.toNat = .ok t) ∨
      (∃ e nsC nsP, encoderCallX cfg c v level = .error (e, nsC) ∧
        iterencodePyX cfg p v level.toNat = .error (e, nsP) ∧ NotesRel cfg nsC nsP))

theorem encoderCallX_proven : EncoderCallX := by
  intro cfg c p v level hO hv
  refine ⟨fun h => by simp [encoderCallX, h], fun h1 h2 => ?_, fun h0 h1 hc hp => ?_⟩
  · have h3 : ¬ outOfSsize 0 := by decide
    simp only [encoderCallX, h2, h3, Bool.false_eq_true, ↓reduceIte]
    rw [show level.toNat = (0 : Int).toNat by omega]
  · simp only [encoderCallX, h1, Bool.false_eq_true, ↓reduceIte]
    have hr : XRelW cfg Eq (cObjX cfg c level.toNat [] [] v) (iterencodePyX cfg p v level.toNat) := by
      unfold iterencodePyX
      match p with
      | 0 => exact XRelW.recPy ⟨[], rfl⟩
      | 1 => exact XRelW.recPy ⟨[], rfl⟩
      | p + 2 => simp only [pyCallX]; exact simX hO c p _ [] [] _ (fun _ h => by simp at h) hv
    rcases hr with ⟨a, b, ha, hb, rfl⟩ | ⟨e, nsC, nsP, ha, hb, hn⟩ | h | h
    · rw [ha]; exact Or.inl ⟨a, rfl, hb⟩
    · rw [ha]; exact Or.inr ⟨e, nsC, nsP, rfl, hb, hn⟩
    · exact absurd h hc
    · exact absurd h hp

end PyLean.JsonMod
