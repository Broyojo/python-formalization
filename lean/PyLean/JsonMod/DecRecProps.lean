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

theorem loadsCR_nest (cfg : DCfg) (hA : cfg.arrayHook = none) (c p k : Nat) (hk : 1 ≤ k) :
    loadsCR cfg c p (nest k) = if k ≤ c then .ok (nestVal k) else .error (recC "array") := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  unfold loadsCR decodeWith rawDecodeCR
  rw [nest_ws (show 0 < 2 * (m + 1) by omega)]
  have hr : ¬ (((0 : Nat) : Int) < ssizeMin ∨ ((0 : Nat) : Int) > ssizeMax) := by
    simp [ssizeMin, ssizeMax]
  simp only [hr, ↓reduceIte, show ¬ (((0 : Nat) : Int) < 0) by omega, Int.toNat_natCast]
  rw [nestC cfg hA (m + 1) m 0 c _ (by omega) (docFuel_nest (m + 1))]
  by_cases hc : m + 1 ≤ c
  · simp only [hc, ↓reduceIte, stopToJde, chargeJde_ok]
    have : wsEndPy (nest (m + 1)) ((0 + (m + 1 + (m + 1)) : Nat) : Int) = (((2 * (m + 1)) : Nat) : Int) := by
      rw [show 0 + (m + 1 + (m + 1)) = 2 * (m + 1) by omega, wsEndPy_nat (by simp [nest_len]),
        nest_ws_end]
    simp only [show m + 1 + (m + 1) = 2 * (m + 1) by omega, Nat.zero_add] at this ⊢
    rw [this, nest_len]
    simp
  · simp [hc, stopToJde, recC, chargeJde_exc]

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

/-! ### Nested objects -/

/-- `'{"":' * k`: `k` objects, each with an empty key whose value is the next one, and nothing
after the last colon. -/
def nestO : Nat → PStr
  | 0 => []
  | k + 1 => [123, 34, 34, 58] ++ nestO k

theorem nestO_len (k : Nat) : (nestO k).length = 4 * k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [nestO, ih]; omega

theorem nestO_drop : ∀ (i m : Nat), (nestO (i + m)).drop (4 * i) = nestO m := by
  intro i
  induction i with
  | zero => intro m; simp
  | succ i ih =>
    intro m
    rw [show i + 1 + m = (i + m) + 1 by omega, show 4 * (i + 1) = 4 + 4 * i by omega, nestO,
      ← List.drop_drop]
    simpa using ih m

/-- The four characters at `4 * i` and what follows them. -/
theorem nestO_at {K i : Nat} (h : i < K) :
    (nestO K)[4 * i]? = some 123 ∧ (nestO K)[4 * i + 1]? = some 34 ∧ (nestO K)[4 * i + 2]? = some 34 ∧
    (nestO K)[4 * i + 3]? = some 58 ∧ (nestO K).drop (4 * i + 2) = 34 :: 58 :: nestO (K - i - 1) := by
  have hd := nestO_drop i (K - i)
  rw [show i + (K - i) = K by omega] at hd
  have e : nestO (K - i) = [123, 34, 34, 58] ++ nestO (K - i - 1) := by
    rw [show K - i = (K - i - 1) + 1 by omega, nestO]; simp
  rw [e] at hd
  have g : ∀ j, (nestO K)[4 * i + j]? = ([123, 34, 34, 58] ++ nestO (K - i - 1))[j]? := by
    intro j; rw [← hd, List.getElem?_drop]
  refine ⟨by simpa using g 0, by simpa using g 1, by simpa using g 2, by simpa using g 3, ?_⟩
  rw [← List.drop_drop, hd]
  rfl

/-- After the colon at `4 * i + 3` there is the next object or the end. -/
theorem nestO_next {K i : Nat} (h : i < K) :
    (i + 1 < K ∧ (nestO K)[4 * i + 4]? = some 123) ∨ (i + 1 = K ∧ (nestO K)[4 * i + 4]? = none) := by
  by_cases h1 : i + 1 < K
  · left
    refine ⟨h1, ?_⟩
    have := (nestO_at h1).1
    rwa [show 4 * (i + 1) = 4 * i + 4 by omega] at this
  · right
    refine ⟨by omega, ?_⟩
    rw [List.getElem?_eq_none_iff, nestO_len]; omega

theorem nestO_ws4 {K i : Nat} (h : i < K) : wsEnd (nestO K) (4 * i + 4) = 4 * i + 4 := by
  rcases nestO_next h with ⟨_, h2⟩ | ⟨_, h2⟩
  · exact wsEnd_of_not_ws h2 rfl
  · exact wsEnd_of_none h2

/-- The C scanner on `nestO K` at the object `i = K - (m + 1)`: `m + 1` levels of room, then
`StopIteration` at the end. -/
theorem nestOC (cfg : DCfg) (K : Nat) : ∀ (m i b n : Nat), i + (m + 1) = K → 2 * (m + 1) + 1 ≤ n →
    cScanOnceR cfg (nestO K) b n (4 * i) =
      if m + 1 ≤ b then .error (.stop ((4 * K : Nat) : Int)) else .error (recC "object") := by
  intro m
  induction m with
  | zero =>
    intro i b n hi hn
    obtain ⟨a0, a1, a2, a3, adrop⟩ := nestO_at (show i < K by omega)
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp only [cScanOnceR, nestO_len, show ¬ (4 * i ≥ 4 * K) by omega, ↓reduceIte, getD_of_some a0]
    simp only [show (123 : Nat) ≠ 34 by decide, ↓reduceIte]
    cases b with
    | zero => rfl
    | succ b =>
      simp only [cEnter, wsEnd_of_not_ws a1 rfl, getD_of_some a1, nestO_len]
      simp only [show ¬ (4 * i + 1 ≥ 4 * K) by omega, show (34 : Nat) ≠ 125 by decide, ne_eq,
        not_false_eq_true, or_true, ↓reduceIte, not_true_eq_false, or_false]
      obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      simp only [cObjBodyR, cScanstring, nestO_len, show ¬ (4 * K < 4 * i + 1 + 1) by omega, ↓reduceIte]
      rw [show 4 * i + 1 + 1 = 4 * i + 2 by omega]
      simp only [cScanLoop, adrop, cFind, true_or, ↓reduceIte, getD_of_some a2, List.take_zero]
      simp only [true_and, ↓reduceIte, show 4 * i + 2 + 0 + 1 = 4 * i + 3 by omega,
        wsEnd_of_not_ws a3 rfl, getD_of_some a3, nestO_len]
      simp only [show ¬ (4 * i + 3 ≥ 4 * K) by omega, ne_eq, not_true_eq_false, or_self, ↓reduceIte,
        show 4 * i + 3 + 1 = 4 * i + 4 by omega, nestO_ws4 (show i < K by omega)]
      obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      simp only [cScanOnceR, nestO_len, show 4 * i + 4 = 4 * K by omega]
      simp
  | succ m ih =>
    intro i b n hi hn
    obtain ⟨a0, a1, a2, a3, adrop⟩ := nestO_at (show i < K by omega)
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp only [cScanOnceR, nestO_len, show ¬ (4 * i ≥ 4 * K) by omega, ↓reduceIte, getD_of_some a0]
    simp only [show (123 : Nat) ≠ 34 by decide, ↓reduceIte]
    cases b with
    | zero => rfl
    | succ b =>
      simp only [cEnter, wsEnd_of_not_ws a1 rfl, getD_of_some a1, nestO_len]
      simp only [show ¬ (4 * i + 1 ≥ 4 * K) by omega, show (34 : Nat) ≠ 125 by decide, ne_eq,
        not_false_eq_true, or_true, ↓reduceIte, not_true_eq_false, or_false]
      obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      simp only [cObjBodyR, cScanstring, nestO_len, show ¬ (4 * K < 4 * i + 1 + 1) by omega, ↓reduceIte]
      rw [show 4 * i + 1 + 1 = 4 * i + 2 by omega]
      simp only [cScanLoop, adrop, cFind, true_or, ↓reduceIte, getD_of_some a2, List.take_zero]
      simp only [true_and, ↓reduceIte, show 4 * i + 2 + 0 + 1 = 4 * i + 3 by omega,
        wsEnd_of_not_ws a3 rfl, getD_of_some a3, nestO_len]
      simp only [show ¬ (4 * i + 3 ≥ 4 * K) by omega, ne_eq, not_true_eq_false, or_self, ↓reduceIte,
        show 4 * i + 3 + 1 = 4 * i + 4 by omega, nestO_ws4 (show i < K by omega)]
      rw [show 4 * i + 4 = 4 * (i + 1) by omega, ih (i + 1) b n (by omega) (by omega)]
      by_cases hb : m + 1 ≤ b
      · simp [hb, show m + 1 + 1 ≤ b + 1 by omega]
      · simp [hb, show ¬ (m + 1 + 1 ≤ b + 1) by omega]

theorem keyScanPy {K i : Nat} (h : i < K) (strict : Bool) (b : Nat) :
    pyScanstringR (nestO K) ((4 * i + 2 : Nat) : Int) strict b = .ok ([], ((4 * i + 3 : Nat) : Int)) := by
  obtain ⟨_, _, a2, _, adrop⟩ := nestO_at h
  have hcl : clampPos (nestO K) ((4 * i + 2 : Nat) : Int) = 4 * i + 2 := by
    simp only [clampPos, nestO_len]
    split <;> omega
  unfold pyScanstringR
  rw [hcl]
  have ht : ∀ t, findTerm (34 :: t) = some 0 := fun t => by
    unfold findTerm; rw [if_pos (by decide)]
  simp only [pyScanLoopR, adrop, ht]
  simp only [Nat.add_zero, getD_of_some a2]
  simp
  all_goals omega

theorem colonPy {K i : Nat} (h : i < K) :
    pyObjColon (nestO K) ((4 * i + 3 : Nat) : Int) = .ok ((4 * i + 4 : Nat) : Int) := by
  obtain ⟨_, _, _, a3, _⟩ := nestO_at h
  unfold pyObjColon
  have hs : pySlice (nestO K) ((4 * i + 3 : Nat) : Int) (((4 * i + 3 : Nat) : Int) + 1) = [58] := by
    rw [slice_nat, a3]; rfl
  simp only [hs, ne_eq, not_true_eq_false, ↓reduceIte]
  rw [show ((4 * i + 3 : Nat) : Int) + 1 = ((4 * i + 4 : Nat) : Int) by omega]
  unfold pyTryWs
  rw [pyIndex_nat]
  rcases nestO_next h with ⟨_, h2⟩ | ⟨_, h2⟩ <;> simp [h2, isWs]

theorem nestOPy_low (cfg : DCfg) {K i : Nat} (h : i < K) (n b : Nat) (hb : b < 2) :
    pyScanOnceR cfg (nestO K) b (n + 2) ((4 * i : Nat) : Int) = .error recPy := by
  obtain ⟨a0, a1, _, _, _⟩ := nestO_at h
  simp only [pyScanOnceR, pyIndex_nat, a0]
  simp only [show (123 : Nat) ≠ 34 by decide, ↓reduceIte]
  match b, hb with
  | 0, _ => rfl
  | 1, _ =>
    simp only [pyCall]
    rw [show ((4 * i : Nat) : Int) + 1 = ((4 * i + 1 : Nat) : Int) by omega, slice_nat, a1]
    simp [pyObjLoopR, pyCall, recPy]

theorem nestOPy_step (cfg : DCfg) {K i : Nat} (h : i < K) (b n : Nat) (e : DErr)
    (he : pyScanOnceR cfg (nestO K) b n ((4 * i + 4 : Nat) : Int) = .error e) :
    pyScanOnceR cfg (nestO K) (b + 2) (n + 2) ((4 * i : Nat) : Int) = stopToJde (.error e) := by
  obtain ⟨a0, a1, _, _, _⟩ := nestO_at h
  simp only [pyScanOnceR, pyIndex_nat, a0]
  simp only [show (123 : Nat) ≠ 34 by decide, ↓reduceIte, pyCall, chargeJde_succ]
  rw [show ((4 * i : Nat) : Int) + 1 = ((4 * i + 1 : Nat) : Int) by omega, slice_nat, a1]
  simp only [Option.toList_some, ne_eq, not_true_eq_false, ↓reduceIte]
  rw [show ((4 * i + 1 : Nat) : Int) + 1 = ((4 * i + 2 : Nat) : Int) by omega]
  simp only [pyObjLoopR, pyCall, keyScanPy h, colonPy h, he]
  cases e <;> rfl

theorem nestOPy (cfg : DCfg) (K : Nat) : ∀ (m i b n : Nat), i + (m + 1) = K → 2 * (m + 1) + 1 ≤ n →
    pyScanOnceR cfg (nestO K) b n ((4 * i : Nat) : Int) =
      if 2 * m + 2 ≤ b then .error (.jde "Expecting value" ((4 * K : Nat) : Int)) else .error recPy := by
  intro m
  induction m with
  | zero =>
    intro i b n hi hn
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
    by_cases hb : b < 2
    · rw [nestOPy_low cfg (show i < K by omega) n b hb]
      simp [show ¬ (2 * 0 + 2 ≤ b) by omega]
    · obtain ⟨b, rfl⟩ : ∃ b', b = b' + 2 := ⟨b - 2, by omega⟩
      obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      have he : pyScanOnceR cfg (nestO K) b (n + 1) ((4 * i + 4 : Nat) : Int) = .error (.stop ((4 * K : Nat) : Int)) := by
        have hn : (nestO K)[4 * K]? = none := by
          rw [List.getElem?_eq_none_iff, nestO_len]; exact Nat.le_refl _
        rw [show 4 * i + 4 = 4 * K by omega]
        simp only [pyScanOnceR, pyIndex_nat, hn]
      rw [nestOPy_step cfg (show i < K by omega) b (n + 1) _ he]
      simp [stopToJde, show 2 * 0 + 2 ≤ b + 2 by omega]
  | succ m ih =>
    intro i b n hi hn
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
    by_cases hb : b < 2
    · rw [nestOPy_low cfg (show i < K by omega) n b hb]
      simp [show ¬ (2 * (m + 1) + 2 ≤ b) by omega]
    · obtain ⟨b, rfl⟩ : ∃ b', b = b' + 2 := ⟨b - 2, by omega⟩
      have hih := ih (i + 1) b n (by omega) (by omega)
      rw [show 4 * (i + 1) = 4 * i + 4 by omega] at hih
      by_cases hc : 2 * m + 2 ≤ b
      · rw [if_pos hc] at hih
        rw [nestOPy_step cfg (show i < K by omega) b n _ hih]
        simp [stopToJde, show 2 * (m + 1) + 2 ≤ b + 2 by omega]
      · rw [if_neg hc] at hih
        rw [nestOPy_step cfg (show i < K by omega) b n _ hih]
        simp [stopToJde, recPy, show ¬ (2 * (m + 1) + 2 ≤ b + 2) by omega]

/-! ### Raw decode and loads -/

/-- The `RecursionError`s of C's `raw_decode`: the scanner's, and the one `JSONDecodeError.__init__`
raises when no frame is left. -/
def IsRecCP {α : Type} (r : DR α) : Prop := IsRecC r ∨ IsRecPy r

theorem rawC_bridge (cfg : DCfg) (c p : Nat) (s : PStr) (idx : Int) :
    (rawDecodeCR cfg c p s idx = rawDecodeC cfg s idx ∨ IsRecCP (rawDecodeCR cfg c p s idx)) ∧
    (docFuel s ≤ c → 1 ≤ p → rawDecodeCR cfg c p s idx = rawDecodeC cfg s idx) := by
  unfold rawDecodeCR rawDecodeC
  split
  · exact ⟨Or.inl rfl, fun _ _ => rfl⟩
  · split
    · exact ⟨Or.inl rfl, fun _ _ => rfl⟩
    · have h := (bridgeC cfg s (docFuel s)).1 c idx.toNat
      generalize cScanOnceR cfg s c (docFuel s) idx.toNat = x at h ⊢
      generalize cScanOnce cfg s (docFuel s) idx.toNat = y at h ⊢
      rcases chargeJde_cases p (stopToJde x) with hc | ⟨hp, hc⟩
      · rw [hc]
        rcases h with ⟨h1 | h1, h2⟩
        · subst h1; exact ⟨Or.inl rfl, fun _ _ => rfl⟩
        · refine ⟨Or.inr (Or.inl ?_), fun hf _ => ?_⟩
          · rcases h1 with rfl | rfl
            · exact Or.inl rfl
            · exact Or.inr rfl
          · have := h2 hf; subst this; rfl
      · rw [hc]
        exact ⟨Or.inr (Or.inr rfl), fun _ h => by omega⟩

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

theorem loadsC_bridge (cfg : DCfg) (c p : Nat) (s : PStr) :
    (loadsCR cfg c p s = loadsC cfg s ∨ IsRecCP (loadsCR cfg c p s)) ∧
    (docFuel s ≤ c → 1 ≤ p → loadsCR cfg c p s = loadsC cfg s) := by
  obtain ⟨h1, h2⟩ := rawC_bridge cfg c p s (wsEnd s 0)
  unfold loadsCR loadsC decodeWith
  refine ⟨?_, fun hf hp => by rw [h2 hf hp]⟩
  rcases h1 with h | h
  · rw [h]; exact Or.inl rfl
  · right
    rcases h with (h | h) | h <;> rw [h]
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (Or.inr rfl)
    · exact Or.inr rfl

theorem loadsPy_bridge (cfg : DCfg) (p : Nat) (s : PStr) :
    RelB IsRecPy (docFuel s + 4) p (loadsPyR cfg p s) (loadsPy cfg s) :=
  decodeWith_bridge _ _ _ _ s (fun r h => ⟨_, h, rfl⟩) (rawPy_bridge cfg p s _)

/-! ### The properties -/

/-- `json.loads(s)` agrees between the twins up to `ScanTwin` for every document, every
decoder setting, every stack room `c` of C and every frame budget `p` of Python. -/
def LoadsTwinsRec : Prop :=
  ∀ (cfg : DCfg) (c p : Nat) (s : PStr), (s.length : Int) ≤ ssizeMax →
    ScanTwin s (loadsPyR cfg p s) (loadsCR cfg c p s)

/-- `'[[]]'` with two levels of C stack room and four Python frames: C returns `[[]]`, Python
needs five frames and raises `RecursionError`. At the default recursion limit the same
happens with `'[' * 1000 + ']' * 1000` (bugs/json-twins-recursion-limit.yaml). -/
theorem loadsTwinsRec_refuted : ¬ LoadsTwinsRec := by
  intro h
  have h1 := h {} 2 4 (nest 2) (by simp [nest, ssizeMax])
  rw [loadsCR_nest {} rfl 2 4 2 (by omega), loadsPyR_nest {} rfl 4 2 (by omega)] at h1
  simp only [show 2 ≤ 2 from Nat.le_refl 2, ↓reduceIte, show ¬ (2 * 2 + 1 ≤ 4) by omega] at h1
  rcases h1 with h1 | ⟨_, _, _, _, _, h1⟩ | ⟨_, _, _, _, _, h1⟩ <;> cases h1

/-- The same for `raw_decode(s, idx)` with `0 <= idx <= sys.maxsize`. -/
def RawDecodeTwinsRec : Prop :=
  ∀ (cfg : DCfg) (c p : Nat) (s : PStr) (idx : Int), 0 ≤ idx → idx ≤ ssizeMax →
    ScanTwin s (rawDecodePyR cfg p s idx) (rawDecodeCR cfg c p s idx)

theorem rawDecodeTwinsRec_refuted : ¬ RawDecodeTwinsRec := by
  intro h
  have h1 := h {} 2 4 (nest 2) 0 (by omega) (by simp [ssizeMax])
  have e1 : rawDecodeCR {} 2 4 (nest 2) 0 = .ok (nestVal 2, 4) := by
    unfold rawDecodeCR
    simp only [show ¬ ((0 : Int) < ssizeMin ∨ (0 : Int) > ssizeMax) by simp [ssizeMin, ssizeMax],
      ↓reduceIte, show ¬ ((0 : Int) < 0) by omega]
    rw [show (0 : Int).toNat = 0 from rfl, nestC {} rfl 2 1 0 2 _ (by omega) (docFuel_nest 2)]
    simp [stopToJde, chargeJde_ok]
  have e2 : rawDecodePyR {} 4 (nest 2) 0 = .error recPy := by
    unfold rawDecodePyR
    simp only
    rw [show (0 : Int) = ((0 : Nat) : Int) from rfl, nestPy {} rfl 2 1 0 2 _ (by omega) (docFuel_nest 2)]
    simp [stopToJde, recPy]
  rw [e1, e2] at h1
  rcases h1 with h1 | ⟨_, _, _, _, h1, _⟩ | ⟨_, _, _, _, h1, _⟩ <;> cases h1

theorem docFuel_nestO (k : Nat) : 2 * k + 1 ≤ docFuel (nestO k) := by
  simp only [docFuel, nestO_len]; omega

theorem nestO_ws0 {k : Nat} (hk : 1 ≤ k) : wsEnd (nestO k) 0 = 0 := by
  have := (nestO_at (K := k) (i := 0) (by omega)).1
  exact wsEnd_of_not_ws this rfl

theorem loadsCR_nestO (cfg : DCfg) (c p k : Nat) (hk : 1 ≤ k) :
    loadsCR cfg c p (nestO k) =
      if k ≤ c then (if p = 0 then .error recPy else .error (.jde "Expecting value" ((4 * k : Nat) : Int)))
      else .error (recC "object") := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  unfold loadsCR decodeWith rawDecodeCR
  rw [nestO_ws0 hk]
  have hr : ¬ (((0 : Nat) : Int) < ssizeMin ∨ ((0 : Nat) : Int) > ssizeMax) := by
    simp [ssizeMin, ssizeMax]
  simp only [hr, ↓reduceIte, show ¬ (((0 : Nat) : Int) < 0) by omega, Int.toNat_natCast]
  rw [show (0 : Nat) = 4 * 0 from rfl, nestOC cfg (m + 1) m 0 c _ (by omega) (by have := docFuel_nestO (m + 1); omega)]
  by_cases hc : m + 1 ≤ c
  · cases p with
    | zero => simp [hc, stopToJde]
    | succ p => simp [hc, stopToJde, chargeJde_succ]
  · simp [hc, stopToJde, recC, chargeJde_exc]

theorem loadsPyR_nestO (cfg : DCfg) (p k : Nat) (hk : 1 ≤ k) :
    loadsPyR cfg p (nestO k) =
      if 2 * k + 2 ≤ p then .error (.jde "Expecting value" ((4 * k : Nat) : Int)) else .error recPy := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  unfold loadsPyR decodeWith rawDecodePyR
  rw [nestO_ws0 hk]
  match p with
  | 0 => simp [stopToJde, recPy]
  | 1 => simp [stopToJde, recPy]
  | p + 2 =>
    simp only
    rw [show (((0 : Nat) : Int)) = ((4 * 0 : Nat) : Int) from rfl,
      nestOPy cfg (m + 1) m 0 p _ (by omega) (by have := docFuel_nestO (m + 1); omega)]
    by_cases hc : 2 * m + 2 ≤ p
    · simp [hc, stopToJde, show 2 * (m + 1) + 2 ≤ p + 2 by omega]
    · simp [hc, stopToJde, recPy, show ¬ (2 * (m + 1) + 2 ≤ p + 2) by omega]

/-- `'"'`: C raises its `JSONDecodeError` with one frame left and `RecursionError` with none;
Python needs four (`scan_once`, `_scan_once`, `py_scanstring` and the error's `__init__`). -/
theorem loads_quote (cfg : DCfg) (c p : Nat) :
    loadsCR cfg c 0 [34] = .error recPy ∧
    loadsCR cfg c (p + 1) [34] = .error (.jde "Unterminated string starting at" 0) ∧
    loadsPyR cfg 3 [34] = .error recPy ∧
    loadsPyR cfg 4 [34] = .error (.jde "Unterminated string starting at" 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [loadsCR, loadsPyR, decodeWith, rawDecodeCR, rawDecodePyR, docFuel, cScanOnceR, pyScanOnceR,
      cScanstring, cScanLoop, cFind, pyScanstringR, pyScanLoopR, pyCall, findTerm, clampPos, pyIndex,
      stopToJde, wsEnd, wsLen, ssizeMin, ssizeMax, chargeJde_succ, recPy, isWs]

/-- `'{'`: Python needs four frames (`scan_once`, `_scan_once`, `JSONObject` and the error's
`__init__`). -/
theorem loads_brace (cfg : DCfg) :
    loadsPyR cfg 3 [123] = .error recPy ∧
    loadsPyR cfg 4 [123] = .error (.jde "Expecting property name enclosed in double quotes" 1) := by
  refine ⟨?_, ?_⟩ <;>
    simp [loadsPyR, decodeWith, rawDecodePyR, docFuel, pyScanOnceR, pyCall, pyIndex, pySlice, sliceBound,
      inWsSlice, stopToJde, wsEnd, wsLen, wsEndPy, chargeJde_succ, recPy, isWs, clampPos]

/-- `'"\\uzz"'`: Python needs five frames (`scan_once`, `_scan_once`, `py_scanstring`,
`_decode_uXXXX` and the error's `__init__`). -/
theorem loads_uzz (cfg : DCfg) :
    loadsPyR cfg 4 [34, 92, 117, 122, 122, 34] = .error recPy ∧
    loadsPyR cfg 5 [34, 92, 117, 122, 122, 34] = .error (.jde "Invalid \\uXXXX escape" 2) := by
  refine ⟨?_, ?_⟩ <;>
    simp [loadsPyR, decodeWith, rawDecodePyR, docFuel, pyScanOnceR, pyScanstringR, pyScanLoopR, pyCall,
      findTerm, isTerm, clampPos, pyIndex, decodeUXXXX, hex4, stopToJde, wsEnd, wsLen, chargeJde_succ, recPy,
      isWs]

/-- `json.loads(s)` with the recursion limits, for every document (`len(s) <= sys.maxsize`), every
decoder setting, stack room `c` and number `p` of frames left at the `scan_once` call:
1. each bounded model gives the unbounded model's result or a `RecursionError` it raised itself
   (C: the scanner's, whose message names an object or an array, or the one of
   `JSONDecodeError.__init__` when `p = 0`), and the unbounded result when the room covers the
   model's fuel (`4 * len(s) + 8`; C also needs `p >= 1`, Python four more frames for
   `scan_once`, `_scan_once`, a string scan and an error's `__init__`);
2. when neither twin raises its `RecursionError`, they agree up to `ScanTwin`;
3. for every decoder without `array_hook`, `'[' * k + ']' * k` (`k >= 1`) decodes in C exactly when
   `k <= c` and in Python exactly when `2 * k + 1 <= p`, and raises the `RecursionError` otherwise
   (the guard of :1140);
4. `'{"":' * k` (`k >= 1`) raises C's `RecursionError` exactly when `c < k` (the guard of :1132)
   and otherwise `JSONDecodeError('Expecting value')` at `4 * k`, or `RecursionError` when `p = 0`;
   Python raises that `JSONDecodeError` exactly when `2 * k + 2 <= p`;
5. the error's frame: on `'"'` C raises `RecursionError` at `p = 0` and its `JSONDecodeError` at
   `p >= 1`, Python its `JSONDecodeError` from four frames and `RecursionError` at three; on `'{'`
   the same in Python; on `'"\\uzz"'` Python needs five (`_decode_uXXXX` raises in its frame). -/
def LoadsTwinsScanRec : Prop :=
  ∀ (cfg : DCfg) (c p : Nat) (s : PStr), (s.length : Int) ≤ ssizeMax →
    (loadsCR cfg c p s = loadsC cfg s ∨ IsRecCP (loadsCR cfg c p s)) ∧
    (loadsPyR cfg p s = loadsPy cfg s ∨ IsRecPy (loadsPyR cfg p s)) ∧
    (docFuel s ≤ c → 1 ≤ p → loadsCR cfg c p s = loadsC cfg s) ∧
    (docFuel s + 4 ≤ p → loadsPyR cfg p s = loadsPy cfg s) ∧
    (¬ IsRecCP (loadsCR cfg c p s) → ¬ IsRecPy (loadsPyR cfg p s) →
      ScanTwin s (loadsPyR cfg p s) (loadsCR cfg c p s)) ∧
    (cfg.arrayHook = none → ∀ k, 1 ≤ k →
      loadsCR cfg c p (nest k) = (if k ≤ c then .ok (nestVal k) else .error (recC "array")) ∧
      loadsPyR cfg p (nest k) = (if 2 * k + 1 ≤ p then .ok (nestVal k) else .error recPy)) ∧
    (∀ k, 1 ≤ k →
      loadsCR cfg c p (nestO k) = (if k ≤ c then
          (if p = 0 then .error recPy else .error (.jde "Expecting value" ((4 * k : Nat) : Int)))
        else .error (recC "object")) ∧
      loadsPyR cfg p (nestO k) =
        (if 2 * k + 2 ≤ p then .error (.jde "Expecting value" ((4 * k : Nat) : Int)) else .error recPy)) ∧
    (loadsCR cfg c 0 [34] = .error recPy ∧
      loadsCR cfg c (p + 1) [34] = .error (.jde "Unterminated string starting at" 0) ∧
      loadsPyR cfg 3 [34] = .error recPy ∧
      loadsPyR cfg 4 [34] = .error (.jde "Unterminated string starting at" 0) ∧
      loadsPyR cfg 3 [123] = .error recPy ∧
      loadsPyR cfg 4 [123] = .error (.jde "Expecting property name enclosed in double quotes" 1) ∧
      loadsPyR cfg 4 [34, 92, 117, 122, 122, 34] = .error recPy ∧
      loadsPyR cfg 5 [34, 92, 117, 122, 122, 34] = .error (.jde "Invalid \\uXXXX escape" 2))

theorem loadsTwinsScanRec_proven : LoadsTwinsScanRec := by
  intro cfg c p s hs
  obtain ⟨hC1, hC2⟩ := loadsC_bridge cfg c p s
  have hP := loadsPy_bridge cfg p s
  obtain ⟨q1, q2, q3, q4⟩ := loads_quote cfg c p
  obtain ⟨b1, b2⟩ := loads_brace cfg
  obtain ⟨u1, u2⟩ := loads_uzz cfg
  refine ⟨hC1, hP.1, hC2, hP.2, fun h1 h2 => ?_, fun hA k hk =>
    ⟨loadsCR_nest cfg hA c p k hk, loadsPyR_nest cfg hA p k hk⟩,
    fun k hk => ⟨loadsCR_nestO cfg c p k hk, loadsPyR_nestO cfg p k hk⟩, q1, q2, q3, q4, b1, b2, u1, u2⟩
  have e1 : loadsCR cfg c p s = loadsC cfg s := hC1.resolve_right h1
  have e2 : loadsPyR cfg p s = loadsPy cfg s := hP.1.resolve_right h2
  rw [e1, e2]
  exact loadsTwinsScan_proven cfg s hs

/-- `raw_decode(s, idx)` with the recursion limits, `0 <= idx <= sys.maxsize`: as
`LoadsTwinsScanRec` 1-2. -/
def RawDecodeTwinsInRangeRec : Prop :=
  ∀ (cfg : DCfg) (c p : Nat) (s : PStr) (idx : Int), 0 ≤ idx → idx ≤ ssizeMax →
    (rawDecodeCR cfg c p s idx = rawDecodeC cfg s idx ∨ IsRecCP (rawDecodeCR cfg c p s idx)) ∧
    (rawDecodePyR cfg p s idx = rawDecodePy cfg s idx ∨ IsRecPy (rawDecodePyR cfg p s idx)) ∧
    (docFuel s ≤ c → 1 ≤ p → rawDecodeCR cfg c p s idx = rawDecodeC cfg s idx) ∧
    (docFuel s + 4 ≤ p → rawDecodePyR cfg p s idx = rawDecodePy cfg s idx) ∧
    (¬ IsRecCP (rawDecodeCR cfg c p s idx) → ¬ IsRecPy (rawDecodePyR cfg p s idx) →
      ScanTwin s (rawDecodePyR cfg p s idx) (rawDecodeCR cfg c p s idx))

theorem rawDecodeTwinsInRangeRec_proven : RawDecodeTwinsInRangeRec := by
  intro cfg c p s idx h0 h1
  obtain ⟨hC1, hC2⟩ := rawC_bridge cfg c p s idx
  have hP := rawPy_bridge cfg p s idx
  refine ⟨hC1, hP.1, hC2, hP.2, fun r1 r2 => ?_⟩
  rw [hC1.resolve_right r1, hP.1.resolve_right r2]
  exact rawDecodeTwinsInRange_proven cfg s idx h0 h1

end PyLean.JsonMod
