import PyLean.JsonMod.DecRec

/-!
The decoder twins with their recursion limits.

* `LoadsTwinsRec`: for every document and every stack room `c` and frame budget `p`, the twins
  agree up to `ScanTwin`. Refuted: nesting that fits in C's stack exhausts Python's frames
  (`json.loads('[' * 1000 + ']' * 1000)` succeeds with `_json` and raises `RecursionError`
  without it, at the default recursion limit), and the reverse with a high recursion limit and a
  document deep enough for the C stack.
* `LoadsTwinsScanRec`: each bounded model is the unbounded one or its own `RecursionError`, and
  the unbounded one when the room covers the fuel; when neither raises `RecursionError`, the
  twins agree up to `ScanTwin`; and on `'[' * k + ']' * k` C needs exactly `k` levels of room and
  Python exactly `2k + 1` frames.
-/

namespace PyLean.JsonMod

open PyLean

/-- `'[' * k + ']' * k`. -/
def nest (k : Nat) : PStr := List.replicate k 91 ++ List.replicate k 93

/-- What `nest k` decodes to without hooks: `[[...[]...]]`, `k` lists deep. -/
def nestVal : Nat → JVal
  | 0 => .arr []
  | 1 => .arr []
  | j + 2 => .arr [nestVal (j + 1)]

theorem nest_len (k : Nat) : (nest k).length = 2 * k := by simp [nest]; omega

theorem nest_get_lt {k i : Nat} (h : i < k) : (nest k)[i]? = some 91 := by
  simp only [nest]
  rw [List.getElem?_append_left (by simpa using h)]
  simp [h]

theorem nest_get_ge {k i : Nat} (h1 : k ≤ i) (h2 : i < 2 * k) : (nest k)[i]? = some 93 := by
  simp only [nest]
  rw [List.getElem?_append_right (by simpa using h1)]
  simp only [List.length_replicate]
  rw [List.getElem?_replicate]
  simp; omega

theorem nest_getD_lt {k i : Nat} (h : i < k) : (nest k).getD i 0 = 91 := getD_of_some (nest_get_lt h)

theorem nest_getD_ge {k i : Nat} (h1 : k ≤ i) (h2 : i < 2 * k) : (nest k).getD i 0 = 93 :=
  getD_of_some (nest_get_ge h1 h2)

theorem nest_ws {k i : Nat} (h : i < 2 * k) : wsEnd (nest k) i = i := by
  by_cases hk : i < k
  · exact wsEnd_of_not_ws (nest_get_lt hk) rfl
  · exact wsEnd_of_not_ws (nest_get_ge (by omega) h) rfl

theorem nest_ws_end (k : Nat) : wsEnd (nest k) (2 * k) = 2 * k := by
  apply wsEnd_of_none
  rw [List.getElem?_eq_none_iff, nest_len]
  exact Nat.le_refl _

theorem nest_arrAfter {k j : Nat} (h1 : k ≤ j) (h2 : j < 2 * k) :
    cArrAfter (nest k) j = .close ((j + 1 : Nat) : Int) := by
  unfold cArrAfter
  simp only [nest_ws h2, nest_len, nest_getD_ge h1 h2]
  simp [h2]

/-- The C scanner on `nest K` at `i = K - (m + 1)`: `m + 1` levels need `m + 1` levels of room. -/
theorem nestC (cfg : DCfg) (hA : cfg.arrayHook = none) (K : Nat) : ∀ (m i b n : Nat),
    i + (m + 1) = K → 2 * (m + 1) ≤ n →
    cScanOnceR cfg (nest K) b n i =
      if m + 1 ≤ b then .ok (nestVal (m + 1), K + (m + 1)) else .error (recC "array") := by
  intro m
  induction m with
  | zero =>
    intro i b n hi hn
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp only [cScanOnceR, nest_len, show ¬ (i ≥ 2 * K) by omega, ↓reduceIte,
      nest_getD_lt (show i < K by omega)]
    simp only [show (91 : Nat) ≠ 34 by decide, show (91 : Nat) ≠ 123 by decide, ↓reduceIte]
    cases b with
    | zero => rfl
    | succ b =>
      simp only [cEnter, nest_ws (show i + 1 < 2 * K by omega), nest_len,
        nest_getD_ge (show K ≤ i + 1 by omega) (show i + 1 < 2 * K by omega)]
      simp [mkArr, hA, nestVal, Except.map, show ¬ (2 * K ≤ i + 1) by omega]
      omega
  | succ m ih =>
    intro i b n hi hn
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp only [cScanOnceR, nest_len, show ¬ (i ≥ 2 * K) by omega, ↓reduceIte,
      nest_getD_lt (show i < K by omega)]
    simp only [show (91 : Nat) ≠ 34 by decide, show (91 : Nat) ≠ 123 by decide, ↓reduceIte]
    cases b with
    | zero => simp [cEnter]
    | succ b =>
      simp only [cEnter, nest_ws (show i + 1 < 2 * K by omega), nest_len,
        nest_getD_lt (show i + 1 < K by omega)]
      simp only [show (91 : Nat) ≠ 93 by decide, ne_eq, not_false_eq_true, or_true, ↓reduceIte]
      try simp only [show ¬ (2 * K ≤ i + 1) by omega, false_or, ↓reduceIte, not_false_eq_true]
      obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      simp only [cArrLoopR]
      rw [ih (i + 1) b n (by omega) (by omega)]
      by_cases hb : m + 1 ≤ b
      · simp only [hb, ↓reduceIte, show m + 1 + 1 ≤ b + 1 by omega]
        rw [nest_arrAfter (by omega) (by omega)]
        simp [mkArr, hA, nestVal, Except.map]
        omega
      · simp only [hb, ↓reduceIte, show ¬ (m + 1 + 1 ≤ b + 1) by omega]

theorem docFuel_nest (k : Nat) : 2 * k ≤ docFuel (nest k) := by
  simp only [docFuel, nest_len]; omega

theorem loadsCR_nest (cfg : DCfg) (hA : cfg.arrayHook = none) (c k : Nat) (hk : 1 ≤ k) :
    loadsCR cfg c (nest k) = if k ≤ c then .ok (nestVal k) else .error (recC "array") := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  unfold loadsCR decodeWith rawDecodeCR
  rw [nest_ws (show 0 < 2 * (m + 1) by omega)]
  have hr : ¬ (((0 : Nat) : Int) < ssizeMin ∨ ((0 : Nat) : Int) > ssizeMax) := by
    simp [ssizeMin, ssizeMax]
  simp only [hr, ↓reduceIte, show ¬ (((0 : Nat) : Int) < 0) by omega, Int.toNat_natCast]
  rw [nestC cfg hA (m + 1) m 0 c _ (by omega) (docFuel_nest (m + 1))]
  by_cases hc : m + 1 ≤ c
  · simp only [hc, ↓reduceIte, stopToJde]
    have : wsEndPy (nest (m + 1)) ((0 + (m + 1 + (m + 1)) : Nat) : Int) = (((2 * (m + 1)) : Nat) : Int) := by
      rw [show 0 + (m + 1 + (m + 1)) = 2 * (m + 1) by omega, wsEndPy_nat (by simp [nest_len]),
        nest_ws_end]
    simp only [show m + 1 + (m + 1) = 2 * (m + 1) by omega, Nat.zero_add] at this ⊢
    rw [this, nest_len]
    simp
  · simp [hc, stopToJde, recC]

/-- The pure-Python scanner on `nest K` at `i = K - (m + 1)`: `m + 1` levels need `2m + 1`
frames after `_scan_once`'s (each level a `JSONArray` and, inside it, a `_scan_once`). -/
theorem nestPy (cfg : DCfg) (hA : cfg.arrayHook = none) (K : Nat) : ∀ (m i b n : Nat),
    i + (m + 1) = K → 2 * (m + 1) ≤ n →
    pyScanOnceR cfg (nest K) b n (i : Int) =
      if 2 * m + 1 ≤ b then .ok (nestVal (m + 1), ((K + (m + 1) : Nat) : Int)) else .error recPy := by
  intro m
  induction m with
  | zero =>
    intro i b n hi hn
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp only [pyScanOnceR, pyIndex_nat, nest_get_lt (show i < K by omega)]
    simp only [show (91 : Nat) ≠ 34 by decide, show (91 : Nat) ≠ 123 by decide, ↓reduceIte]
    cases b with
    | zero => rfl
    | succ b =>
      simp only [pyCall, slice_nat, nest_get_ge (show K ≤ i + 1 by omega) (show i + 1 < 2 * K by omega)]
      rw [show (i : Int) + 1 = ((i + 1 : Nat) : Int) by omega, slice_nat,
        nest_get_ge (show K ≤ i + 1 by omega) (show i + 1 < 2 * K by omega)]
      simp [inWsSlice, isWs, mkArr, hA, nestVal, Except.map]
      omega
  | succ m ih =>
    intro i b n hi hn
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp only [pyScanOnceR, pyIndex_nat, nest_get_lt (show i < K by omega)]
    simp only [show (91 : Nat) ≠ 34 by decide, show (91 : Nat) ≠ 123 by decide, ↓reduceIte]
    cases b with
    | zero => simp [pyCall]
    | succ b =>
      simp only [pyCall]
      rw [show (i : Int) + 1 = ((i + 1 : Nat) : Int) by omega, slice_nat,
        nest_get_lt (show i + 1 < K by omega)]
      simp only [Option.toList_some, inWsSlice, isWs, Nat.reduceBEq, Bool.or_false, Bool.false_eq_true,
        ↓reduceIte, List.cons.injEq, show (91 : Nat) ≠ 93 by decide, false_and]
      obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      simp only [pyArrLoopR]
      cases b with
      | zero => simp [pyCall, recPy, show ¬ (2 * (m + 1) + 1 ≤ 1) by omega]
      | succ b =>
        simp only [pyCall]
        rw [ih (i + 1) b n (by omega) (by omega)]
        by_cases hb : 2 * m + 1 ≤ b
        · simp only [hb, ↓reduceIte, show 2 * (m + 1) + 1 ≤ b + 1 + 1 by omega]
          rw [arrAfter_twin _ _ (by rw [nest_len]; omega), nest_arrAfter (by omega) (by omega)]
          simp [mkArr, hA, nestVal, Except.map]
          omega
        · simp [hb, recPy, show ¬ (2 * (m + 1) + 1 ≤ b + 1 + 1) by omega]

theorem loadsPyR_nest (cfg : DCfg) (hA : cfg.arrayHook = none) (p k : Nat) (hk : 1 ≤ k) :
    loadsPyR cfg p (nest k) = if 2 * k + 1 ≤ p then .ok (nestVal k) else .error recPy := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  unfold loadsPyR decodeWith rawDecodePyR
  rw [nest_ws (show 0 < 2 * (m + 1) by omega)]
  match p with
  | 0 => simp [stopToJde, recPy]
  | 1 => simp [stopToJde, recPy]
  | p + 2 =>
    simp only
    rw [nestPy cfg hA (m + 1) m 0 p _ (by omega) (docFuel_nest (m + 1))]
    by_cases hc : 2 * m + 1 ≤ p
    · simp only [hc, ↓reduceIte, stopToJde, show 2 * (m + 1) + 1 ≤ p + 2 by omega]
      rw [show m + 1 + (m + 1) = 2 * (m + 1) by omega, wsEndPy_nat (by simp [nest_len]),
        nest_ws_end, nest_len]
      simp
    · simp [hc, stopToJde, recPy, show ¬ (2 * (m + 1) + 1 ≤ p + 2) by omega]

/-! ### Raw decode and loads -/

theorem rawC_bridge (cfg : DCfg) (c : Nat) (s : PStr) (idx : Int) :
    RelB IsRecC (docFuel s) c (rawDecodeCR cfg c s idx) (rawDecodeC cfg s idx) := by
  unfold rawDecodeCR rawDecodeC
  split
  · exact RelB.refl _
  · split
    · exact RelB.refl _
    · have h := (bridgeC cfg s (docFuel s)).1 c idx.toNat
      generalize cScanOnceR cfg s c (docFuel s) idx.toNat = x at h ⊢
      generalize cScanOnce cfg s (docFuel s) idx.toNat = y at h ⊢
      rcases h with ⟨h1 | h1, h2⟩
      · subst h1; exact RelB.refl _
      · refine ⟨Or.inr ?_, fun hf => ?_⟩
        · rcases h1 with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr rfl
        · have := h2 hf; subst this; rfl

theorem rawPy_bridge (cfg : DCfg) (p : Nat) (s : PStr) (idx : Int) :
    RelB IsRecPy (docFuel s + 4) p (rawDecodePyR cfg p s idx) (rawDecodePy cfg s idx) := by
  unfold rawDecodePyR rawDecodePy
  match p with
  | 0 => exact ⟨Or.inr rfl, fun h => by omega⟩
  | 1 => exact ⟨Or.inr rfl, fun h => by omega⟩
  | p + 2 =>
    simp only
    have h := (bridgePy cfg s (docFuel s)).1 p idx
    generalize pyScanOnceR cfg s p (docFuel s) idx = x at h ⊢
    generalize pyScanOnce cfg s (docFuel s) idx = y at h ⊢
    rcases h with ⟨h1 | h1, h2⟩
    · subst h1; exact RelB.refl _
    · refine ⟨Or.inr (by rw [h1]; rfl), fun hf => ?_⟩
      have := h2 (by omega); subst this; rfl

theorem decodeWith_bridge {P : DR JVal → Prop} {Q : DR (JVal × Int) → Prop} (f b : Nat)
    (raw1 raw2 : PStr → Int → DR (JVal × Int)) (s : PStr)
    (hQ : ∀ r, Q r → ∃ e, r = .error e ∧ P (.error e))
    (h : RelB Q f b (raw1 s (wsEnd s 0)) (raw2 s (wsEnd s 0))) :
    RelB P f b (decodeWith raw1 s) (decodeWith raw2 s) := by
  unfold decodeWith
  rcases h with ⟨h1 | h1, h2⟩
  · rw [h1]; exact RelB.refl _
  · obtain ⟨e, he, hP⟩ := hQ _ h1
    refine ⟨Or.inr (by rw [he]; exact hP), fun hf => ?_⟩
    rw [h2 hf]

theorem loadsC_bridge (cfg : DCfg) (c : Nat) (s : PStr) :
    RelB IsRecC (docFuel s) c (loadsCR cfg c s) (loadsC cfg s) :=
  decodeWith_bridge _ _ _ _ s (fun r h => by
    rcases h with rfl | rfl
    · exact ⟨_, rfl, Or.inl rfl⟩
    · exact ⟨_, rfl, Or.inr rfl⟩) (rawC_bridge cfg c s _)

theorem loadsPy_bridge (cfg : DCfg) (p : Nat) (s : PStr) :
    RelB IsRecPy (docFuel s + 4) p (loadsPyR cfg p s) (loadsPy cfg s) :=
  decodeWith_bridge _ _ _ _ s (fun r h => ⟨_, h, rfl⟩) (rawPy_bridge cfg p s _)

/-! ### The properties -/

/-- `json.loads(s)` agrees between the twins up to `ScanTwin` for every document, every
decoder setting, every stack room `c` of C and every frame budget `p` of Python. -/
def LoadsTwinsRec : Prop :=
  ∀ (cfg : DCfg) (c p : Nat) (s : PStr), (s.length : Int) ≤ ssizeMax →
    ScanTwin s (loadsPyR cfg p s) (loadsCR cfg c s)

/-- `'[[]]'` with two levels of C stack room and four Python frames: C returns `[[]]`, Python
needs five frames and raises `RecursionError`. At the default recursion limit the same
happens with `'[' * 1000 + ']' * 1000` (bugs/json-twins-recursion-limit.yaml). -/
theorem loadsTwinsRec_refuted : ¬ LoadsTwinsRec := by
  intro h
  have h1 := h {} 2 4 (nest 2) (by simp [nest, ssizeMax])
  rw [loadsCR_nest {} rfl 2 2 (by omega), loadsPyR_nest {} rfl 4 2 (by omega)] at h1
  simp only [show 2 ≤ 2 from Nat.le_refl 2, ↓reduceIte, show ¬ (2 * 2 + 1 ≤ 4) by omega] at h1
  rcases h1 with h1 | ⟨_, _, _, _, _, h1⟩ | ⟨_, _, _, _, _, h1⟩ <;> cases h1

/-- The same for `raw_decode(s, idx)` with `0 <= idx <= sys.maxsize`. -/
def RawDecodeTwinsRec : Prop :=
  ∀ (cfg : DCfg) (c p : Nat) (s : PStr) (idx : Int), 0 ≤ idx → idx ≤ ssizeMax →
    ScanTwin s (rawDecodePyR cfg p s idx) (rawDecodeCR cfg c s idx)

theorem rawDecodeTwinsRec_refuted : ¬ RawDecodeTwinsRec := by
  intro h
  have h1 := h {} 2 4 (nest 2) 0 (by omega) (by simp [ssizeMax])
  have e1 : rawDecodeCR {} 2 (nest 2) 0 = .ok (nestVal 2, 4) := by
    unfold rawDecodeCR
    simp only [show ¬ ((0 : Int) < ssizeMin ∨ (0 : Int) > ssizeMax) by simp [ssizeMin, ssizeMax],
      ↓reduceIte, show ¬ ((0 : Int) < 0) by omega]
    rw [show (0 : Int).toNat = 0 from rfl, nestC {} rfl 2 1 0 2 _ (by omega) (docFuel_nest 2)]
    simp [stopToJde]
  have e2 : rawDecodePyR {} 4 (nest 2) 0 = .error recPy := by
    unfold rawDecodePyR
    simp only
    rw [show (0 : Int) = ((0 : Nat) : Int) from rfl, nestPy {} rfl 2 1 0 2 _ (by omega) (docFuel_nest 2)]
    simp [stopToJde, recPy]
  rw [e1, e2] at h1
  rcases h1 with h1 | ⟨_, _, _, _, h1, _⟩ | ⟨_, _, _, _, h1, _⟩ <;> cases h1

/-- `json.loads(s)` with the recursion limits, for every document (`len(s) <= sys.maxsize`), every
decoder setting, stack room `c` and frame budget `p`:
1. each bounded model gives the unbounded model's result or a `RecursionError` it raised itself
   (the C message names an object or an array), and the unbounded result when the room covers the
   model's fuel (`4 * len(s) + 8`, plus Python's four frames of `scan_once`, `_scan_once` and a
   string scan);
2. when neither twin raises its `RecursionError`, they agree up to `ScanTwin`;
3. for every decoder without `array_hook`, `'[' * k + ']' * k` (`k >= 1`) decodes in C exactly when
   `k <= c` and in Python exactly when `2 * k + 1 <= p`, and raises the `RecursionError` otherwise. -/
def LoadsTwinsScanRec : Prop :=
  ∀ (cfg : DCfg) (c p : Nat) (s : PStr), (s.length : Int) ≤ ssizeMax →
    (loadsCR cfg c s = loadsC cfg s ∨ IsRecC (loadsCR cfg c s)) ∧
    (loadsPyR cfg p s = loadsPy cfg s ∨ IsRecPy (loadsPyR cfg p s)) ∧
    (docFuel s ≤ c → loadsCR cfg c s = loadsC cfg s) ∧
    (docFuel s + 4 ≤ p → loadsPyR cfg p s = loadsPy cfg s) ∧
    (¬ IsRecC (loadsCR cfg c s) → ¬ IsRecPy (loadsPyR cfg p s) →
      ScanTwin s (loadsPyR cfg p s) (loadsCR cfg c s)) ∧
    (cfg.arrayHook = none → ∀ k, 1 ≤ k →
      loadsCR cfg c (nest k) = (if k ≤ c then .ok (nestVal k) else .error (recC "array")) ∧
      loadsPyR cfg p (nest k) = (if 2 * k + 1 ≤ p then .ok (nestVal k) else .error recPy))

theorem loadsTwinsScanRec_proven : LoadsTwinsScanRec := by
  intro cfg c p s hs
  have hC := loadsC_bridge cfg c s
  have hP := loadsPy_bridge cfg p s
  refine ⟨hC.1, hP.1, hC.2, hP.2, fun h1 h2 => ?_, fun hA k hk =>
    ⟨loadsCR_nest cfg hA c k hk, loadsPyR_nest cfg hA p k hk⟩⟩
  have e1 : loadsCR cfg c s = loadsC cfg s := hC.1.resolve_right h1
  have e2 : loadsPyR cfg p s = loadsPy cfg s := hP.1.resolve_right h2
  rw [e1, e2]
  exact loadsTwinsScan_proven cfg s hs

/-- `raw_decode(s, idx)` with the recursion limits, `0 <= idx <= sys.maxsize`: as
`LoadsTwinsScanRec` 1-2. -/
def RawDecodeTwinsInRangeRec : Prop :=
  ∀ (cfg : DCfg) (c p : Nat) (s : PStr) (idx : Int), 0 ≤ idx → idx ≤ ssizeMax →
    (rawDecodeCR cfg c s idx = rawDecodeC cfg s idx ∨ IsRecC (rawDecodeCR cfg c s idx)) ∧
    (rawDecodePyR cfg p s idx = rawDecodePy cfg s idx ∨ IsRecPy (rawDecodePyR cfg p s idx)) ∧
    (docFuel s ≤ c → rawDecodeCR cfg c s idx = rawDecodeC cfg s idx) ∧
    (docFuel s + 4 ≤ p → rawDecodePyR cfg p s idx = rawDecodePy cfg s idx) ∧
    (¬ IsRecC (rawDecodeCR cfg c s idx) → ¬ IsRecPy (rawDecodePyR cfg p s idx) →
      ScanTwin s (rawDecodePyR cfg p s idx) (rawDecodeCR cfg c s idx))

theorem rawDecodeTwinsInRangeRec_proven : RawDecodeTwinsInRangeRec := by
  intro cfg c p s idx h0 h1
  have hC := rawC_bridge cfg c s idx
  have hP := rawPy_bridge cfg p s idx
  refine ⟨hC.1, hP.1, hC.2, hP.2, fun r1 r2 => ?_⟩
  rw [hC.1.resolve_right r1, hP.1.resolve_right r2]
  exact rawDecodeTwinsInRange_proven cfg s idx h0 h1

end PyLean.JsonMod
