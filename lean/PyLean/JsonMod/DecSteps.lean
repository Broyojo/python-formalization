import PyLean.JsonMod.DecLemmas

/-!
The delimiter handling of `JSONArray`/`JSONObject` (Python) and
`_parse_array_unicode`/`_parse_object_unicode` (C) agree at non-negative
positions.
-/

namespace PyLean.JsonMod

open PyLean

theorem slice_nat (s : PStr) (a : Nat) : pySlice s (a : Int) ((a : Int) + 1) = (s[a]?).toList := by
  rw [pySlice_nat1, drop_take1]

theorem ws_or_none_of {s : PStr} {i : Nat} (h : inWsSlice (s[i]?).toList = true) :
    s[i]? = none ∨ ∃ c, s[i]? = some c ∧ isWs c = true := by
  cases hc : s[i]? with
  | none => exact Or.inl rfl
  | some c => rw [hc] at h; exact Or.inr ⟨c, rfl, by simpa [inWsSlice] using h⟩

theorem not_ws_of {s : PStr} {i : Nat} (h : ¬ inWsSlice (s[i]?).toList = true) :
    ∃ c, s[i]? = some c ∧ isWs c = false := by
  cases hc : s[i]? with
  | none => rw [hc] at h; simp [inWsSlice] at h
  | some c => rw [hc] at h; exact ⟨c, rfl, by simpa [inWsSlice] using h⟩

/-- `nextchar = s[end:end+1]; if nextchar in _ws: end = _w(s, end + 1).end(); nextchar = ...`. -/
theorem skipSlice (s : PStr) (e : Nat) (he : e ≤ s.length) :
    (if inWsSlice (pySlice s (e : Int) ((e : Int) + 1)) then
        (wsEndPy s ((e : Int) + 1), pySlice s (wsEndPy s ((e : Int) + 1)) (wsEndPy s ((e : Int) + 1) + 1))
      else ((e : Int), pySlice s (e : Int) ((e : Int) + 1))) =
      (((wsEnd s e : Nat) : Int), (s[wsEnd s e]?).toList) := by
  rw [slice_nat]
  split
  · rename_i h
    rw [wsEndPy_succ he (ws_or_none_of h), slice_nat]
  · rename_i h
    obtain ⟨c, hc, hw⟩ := not_ws_of h
    rw [wsEnd_of_not_ws hc hw]

theorem skipSlice' (s : PStr) (e : Nat) (he : e ≤ s.length) :
    (if inWsSlice (s[e]?).toList then
        (wsEndPy s ((e : Int) + 1), pySlice s (wsEndPy s ((e : Int) + 1)) (wsEndPy s ((e : Int) + 1) + 1))
      else ((e : Int), (s[e]?).toList)) =
      (((wsEnd s e : Nat) : Int), (s[wsEnd s e]?).toList) := by
  have := skipSlice s e he
  rwa [slice_nat] at this

/-- The same with `_w(s, end)` (`JSONObject` entry). -/
theorem skipSlice0 (s : PStr) (e : Nat) (he : e ≤ s.length) :
    (if inWsSlice (pySlice s (e : Int) ((e : Int) + 1)) then
        (wsEndPy s (e : Int), pySlice s (wsEndPy s (e : Int)) (wsEndPy s (e : Int) + 1))
      else ((e : Int), pySlice s (e : Int) ((e : Int) + 1))) =
      (((wsEnd s e : Nat) : Int), (s[wsEnd s e]?).toList) := by
  rw [slice_nat]
  split
  · rw [wsEndPy_nat he, slice_nat]
  · rename_i h
    obtain ⟨c, hc, hw⟩ := not_ws_of h
    rw [wsEnd_of_not_ws hc hw]

theorem skipSlice0' (s : PStr) (e : Nat) (he : e ≤ s.length) :
    (if inWsSlice (s[e]?).toList then
        (wsEndPy s (e : Int), pySlice s (wsEndPy s (e : Int)) (wsEndPy s (e : Int) + 1))
      else ((e : Int), (s[e]?).toList)) =
      (((wsEnd s e : Nat) : Int), (s[wsEnd s e]?).toList) := by
  have := skipSlice0 s e he
  rwa [slice_nat] at this

theorem slice_nat_succ (s : PStr) (x : Nat) :
    pySlice s ((x : Int) + 1) ((x : Int) + 1 + 1) = (s[x + 1]?).toList := by
  rw [show (x : Int) + 1 = ((x + 1 : Nat) : Int) by omega, slice_nat]

/-- The `try:` block: the next non-whitespace index, and `nextchar` there
(`nc0` or `''` past the end). -/
theorem pyTryWs_nat (s : PStr) (x : Nat) (nc0 : PStr) :
    (pyTryWs s (x : Int) nc0).1 = ((wsEnd s x : Nat) : Int) ∧
    (∀ c, s[wsEnd s x]? = some c → (pyTryWs s (x : Int) nc0).2 = [c]) ∧
    (s[wsEnd s x]? = none → (pyTryWs s (x : Int) nc0).2 = nc0 ∨ (pyTryWs s (x : Int) nc0).2 = []) := by
  unfold pyTryWs
  rw [pyIndex_nat]
  cases h1 : s[x]? with
  | none => simp [wsEnd_of_none h1, h1]
  | some c =>
    simp only
    cases hw : isWs c with
    | false => simp [wsEnd_of_not_ws h1 hw, slice_nat, h1]
    | true =>
      simp only [↓reduceIte]
      rw [show (x : Int) + 1 = ((x + 1 : Nat) : Int) by omega, pyIndex_nat, wsEnd_of_ws h1 hw]
      cases h2 : s[x + 1]? with
      | none => simp [wsEnd_of_none h2, h2]
      | some c2 =>
        simp only
        cases hw2 : isWs c2 with
        | false =>
          simp only [hw2, Bool.false_eq_true, ↓reduceIte, wsEnd_of_not_ws h2 hw2]
          rw [slice_nat, h2]; simp
        | true =>
          have hlt : x + 1 < s.length := (List.getElem?_eq_some_iff.mp h2).1
          simp only [↓reduceIte]
          rw [show (x : Int) + 2 = ((x + 2 : Nat) : Int) by omega, wsEndPy_nat (by omega),
            slice_nat, wsEnd_of_ws h2 hw2]
          refine ⟨rfl, ?_, ?_⟩
          · intro c h; rw [h]; rfl
          · intro h; rw [h]; simp

theorem arrAfter_twin (s : PStr) (e : Nat) (he : e ≤ s.length) : pyArrAfter s (e : Int) = cArrAfter s e := by
  unfold pyArrAfter
  simp only []
  rw [skipSlice s e he]
  generalize hw : wsEnd s e = w
  have hwl : w ≤ s.length := hw ▸ wsEnd_le he
  simp only [cArrAfter, hw]
  cases hc : s[w]? with
  | none =>
    have : ¬ w < s.length := by have := List.getElem?_eq_none_iff.mp hc; omega
    simp [this]
  | some c =>
    have hlt : w < s.length := (List.getElem?_eq_some_iff.mp hc).1
    have hgd : s.getD w 0 = c := by simp [List.getD_eq_getElem?_getD, hc]
    simp only [Option.toList_some, List.cons.injEq, and_true, hlt, hgd, true_and, Nat.not_lt]
    by_cases h93 : c = 93
    · simp [h93]
    · simp only [h93, ↓reduceIte, ne_eq, not_false_eq_true]
      by_cases h44 : c = 44
      · subst h44
        simp only [not_true_eq_false, ↓reduceIte, Nat.reduceEqDiff, false_or, Nat.not_le, hlt]
        have e1 : (w : Int) + 1 = ((w + 1 : Nat) : Int) := by omega
        obtain ⟨t1, t2, t3⟩ := pyTryWs_nat s (w + 1) [44]
        push_cast at t1 t2 t3
        rw [t1]
        simp only [show (w : Int) + 1 - 1 = (w : Int) by omega]
        cases hn : s[wsEnd s (w + 1)]? with
        | none =>
          have : ¬ wsEnd s (w + 1) < s.length := by have := List.getElem?_eq_none_iff.mp hn; omega
          have h2 : (pyTryWs s ((w : Int) + 1) [44]).2 ≠ [93] := by
            rcases t3 hn with h | h <;> rw [h] <;> simp
          simp [this, h2, hlt]
        | some d =>
          have hlt' : wsEnd s (w + 1) < s.length := (List.getElem?_eq_some_iff.mp hn).1
          have hd : s[wsEnd s (w + 1)] = d := by
            have := (List.getElem?_eq_some_iff.mp hn).2; exact this
          have : ¬ s.length ≤ w := by omega
          simp [hlt', List.getD_eq_getElem?_getD, hn, t2 d hn, hd, this]
      · simp [h44]

theorem getD_of_some {s : PStr} {i c : Nat} (h : s[i]? = some c) : s.getD i 0 = c := by
  simp [List.getD_eq_getElem?_getD, h]

/-- The colon of `JSONObject` against `_parse_object_unicode`, :716-725. -/
theorem objColon_twin (s : PStr) (e : Nat) (he : e ≤ s.length) :
    pyObjColon s (e : Int) =
      (if wsEnd s e ≥ s.length ∨ s.getD (wsEnd s e) 0 ≠ 58 then
        .error (.jde "Expecting ':' delimiter" ((wsEnd s e : Nat) : Int))
       else .ok ((wsEnd s (wsEnd s e + 1) : Nat) : Int)) := by
  have hw : (if pySlice s (e : Int) ((e : Int) + 1) ≠ [58] then wsEndPy s (e : Int) else (e : Int)) =
      ((wsEnd s e : Nat) : Int) := by
    rw [slice_nat]
    cases hc : s[e]? with
    | none => simp [wsEndPy_nat he]
    | some c =>
      by_cases h58 : c = 58
      · subst h58
        simp [wsEnd_of_not_ws hc (by rfl)]
      · simp [h58, wsEndPy_nat he]
  unfold pyObjColon
  simp only []
  rw [hw]
  generalize hw' : wsEnd s e = w
  have hwl : w ≤ s.length := hw' ▸ wsEnd_le he
  rw [slice_nat]
  cases hc : s[w]? with
  | none =>
    have : s.length ≤ w := by have := List.getElem?_eq_none_iff.mp hc; omega
    simp [this]
  | some c =>
    have hlt : w < s.length := (List.getElem?_eq_some_iff.mp hc).1
    have hnl : ¬ w ≥ s.length := by omega
    by_cases h58 : c = 58
    · subst h58
      simp only [Option.toList_some, ne_eq, not_true_eq_false, ↓reduceIte, hnl, getD_of_some hc, or_self]
      rw [show (w : Int) + 1 = ((w + 1 : Nat) : Int) by omega, (pyTryWs_nat s (w + 1) []).1]
    · simp [h58, hnl, hc]

/-- What comes after a value in `JSONObject` against `_parse_object_unicode`
(the next key's quote being checked at the top of the C loop). -/
theorem objAfter_twin (s : PStr) (e : Nat) (he : e ≤ s.length) :
    pyObjAfter s (e : Int) =
      (match cObjAfter s e with
       | .close i => .close i
       | .err x => .err x
       | .next i =>
         if i.toNat ≥ s.length ∨ s.getD i.toNat 0 ≠ 34 then
           .err (.jde "Expecting property name enclosed in double quotes" i)
         else .next (i + 1)) := by
  have hpair : pyNextChar s (e : Int) = (((wsEnd s e : Nat) : Int), s[wsEnd s e]?) := by
    unfold pyNextChar
    rw [pyIndex_nat]
    cases hc : s[e]? with
    | none => simp [wsEnd_of_none hc, hc]
    | some c =>
      cases hwc : isWs c with
      | false => simp [wsEnd_of_not_ws hc hwc, hc, hwc]
      | true =>
        simp only [hwc, ↓reduceIte]
        rw [wsEndPy_succ he (Or.inr ⟨c, hc, hwc⟩), pyIndex_nat, wsEnd_of_ws hc hwc]
  unfold pyObjAfter
  simp only []
  rw [hpair]
  generalize hw : wsEnd s e = w
  have hwl : w ≤ s.length := hw ▸ wsEnd_le he
  simp only [cObjAfter, hw]
  cases hc : s[w]? with
  | none =>
    have : ¬ w < s.length := by have := List.getElem?_eq_none_iff.mp hc; omega
    simp [this]
  | some c =>
    have hlt : w < s.length := (List.getElem?_eq_some_iff.mp hc).1
    simp only [Option.some.injEq, hlt, getD_of_some hc, true_and, Nat.not_le]
    by_cases h125 : c = 125
    · subst h125; simp
    · simp only [h125, ↓reduceIte, ne_eq]
      by_cases h44 : c = 44
      · subst h44
        simp only [not_true_eq_false, ↓reduceIte, Nat.reduceEqDiff, hlt, Nat.not_le]
        rw [show (w : Int) + 1 = ((w + 1 : Nat) : Int) by omega, wsEndPy_nat (by omega), slice_nat]
        simp only [show ((w + 1 : Nat) : Int) - 1 = (w : Int) by omega]
        generalize hx : wsEnd s (w + 1) = x
        have hxl : x ≤ s.length := hx ▸ wsEnd_le (by omega)
        have hnw : ¬ s.length ≤ w := by omega
        cases hn : s[x]? with
        | none =>
          have : ¬ x < s.length := by have := List.getElem?_eq_none_iff.mp hn; omega
          simp [this, hnw]
        | some d =>
          have hlt' : x < s.length := (List.getElem?_eq_some_iff.mp hn).1
          simp only [Option.toList_some, List.cons.injEq, and_true, hlt', getD_of_some hn, true_and,
            Int.toNat_natCast, Nat.not_le]
          by_cases h34 : d = 34
          · subst h34
            have : s[x] = 34 := (List.getElem?_eq_some_iff.mp hn).2
            simp [hnw, hn, hlt', this]
          · by_cases h125' : d = 125
            · subst h125'; simp [hnw]
            · simp [h34, h125', hnw, hn]
      · simp [h44]

end PyLean.JsonMod
