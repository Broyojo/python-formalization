import PyLean.BytesObj.Bytes.BasicProps4

/-!
Properties of `repr`, `hex`, `fromhex` and the C API functions.
-/

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

/-! ## `repr`: the computed size is the written size -/

/-- The bytes `PyBytes_Repr` budgets for a byte before quote escapes. -/
def reprCost (c : Nat) : Int :=
  if c = 39 then 1 else if c = 34 then 1
  else if c = 92 ∨ c = 9 ∨ c = 10 ∨ c = 13 then 2
  else if c < 32 ∨ c ≥ 127 then 4 else 1

def reprBase : Seq → Int
  | [] => 0
  | c :: rest => reprCost c + reprBase rest

def countOfByte (x : Nat) : Seq → Int
  | [] => 0
  | c :: rest => (if c = x then 1 else 0) + countOfByte x rest

theorem reprScan_spec (s : Seq) (n sq dq n' sq' dq' : Int)
    (h : reprScan s n sq dq = .ok (n', sq', dq')) :
    n' = n + reprBase s ∧ sq' = sq + countOfByte 39 s ∧ dq' = dq + countOfByte 34 s := by
  induction s generalizing n sq dq with
  | nil =>
    simp only [reprScan, Except.ok.injEq, Prod.mk.injEq] at h
    simp [reprBase, countOfByte]
    omega
  | cons c rest ih =>
    unfold reprScan at h
    by_cases h39 : c = 39
    · subst h39
      simp only [if_true] at h
      split at h
      · simp at h
      · have := ih _ _ _ h
        simp only [reprBase, countOfByte, reprCost, if_true]
        have h2 : (39 : Nat) ≠ 34 := by decide
        simp only [h2, if_false]
        omega
    · by_cases h34 : c = 34
      · subst h34
        simp only [h39, if_false, if_true] at h
        split at h
        · simp at h
        · have := ih _ _ _ h
          simp only [reprBase, countOfByte, reprCost, h39, if_false, if_true]
          omega
      · simp only [h39, h34, if_false] at h
        by_cases h2 : c = 92 ∨ c = 9 ∨ c = 10 ∨ c = 13
        · simp only [h2, if_true] at h
          split at h
          · simp at h
          · have := ih _ _ _ h
            simp only [reprBase, countOfByte, reprCost, h39, h34, h2, if_false, if_true]
            omega
        · simp only [h2, if_false] at h
          by_cases h3 : c < 32 ∨ c ≥ 127
          · simp only [h3, if_true] at h
            split at h
            · simp at h
            · have := ih _ _ _ h
              simp only [reprBase, countOfByte, reprCost, h39, h34, h2, h3, if_false, if_true]
              omega
          · simp only [h3, if_false] at h
            split at h
            · simp at h
            · have := ih _ _ _ h
              simp only [reprBase, countOfByte, reprCost, h39, h34, h2, h3, if_false]
              omega

theorem reprBody_length (quote : Nat) (hq : quote = 39 ∨ quote = 34) (s : Seq) :
    ((reprBody quote s).length : Int) = reprBase s + countOfByte quote s := by
  induction s with
  | nil => simp [reprBody, reprBase, countOfByte]
  | cons c rest ih =>
    unfold reprBody at ih ⊢
    simp only [List.flatMap_cons, List.length_append, reprBase, countOfByte, Int.natCast_add]
    rw [ih]
    have hc : ((reprByte quote c).length : Int) = reprCost c + (if c = quote then 1 else 0) := by
      unfold reprByte reprCost
      by_cases h1 : c = quote
      · rcases hq with rfl | rfl <;> subst h1 <;> simp
      · simp only [h1, if_false, false_or]
        by_cases h92 : c = 92
        · subst h92
          have : (92 : Nat) ≠ 39 := by decide
          have h2 : (92 : Nat) ≠ 34 := by decide
          simp
        · by_cases h39 : c = 39
          · subst h39
            simp [h1]
          · by_cases h34 : c = 34
            · subst h34
              simp [h1]
            · repeat' split
              all_goals simp_all
              all_goals omega
    omega

/-- The exact-size allocation of `PyBytes_Repr`: the sizing loop and the optional
`squotes` extra give exactly the length the writing loop produces, for every byte string
and both `smartquotes` settings, so the `PyUnicode_New(newsize)` buffer is never overrun
or left with a gap. -/
def ReprSizeExact : Prop :=
  ∀ (s : Seq) (smart : Bool) (n sq dq : Int) (r : Seq),
    reprScan s 3 0 0 = .ok (n, sq, dq) → bytesRepr s smart = .ok r →
    (r.length : Int) = n + (if smart = true ∧ sq ≠ 0 ∧ dq = 0 then 0 else sq)

theorem reprSizeExact_proven : ReprSizeExact := by
  intro s smart n sq dq r hs h
  obtain ⟨hn, hsq, hdq⟩ := reprScan_spec s 3 0 0 n sq dq hs
  simp only [bytesRepr, bind, Except.bind, hs, pure, Except.pure] at h
  have L39 := reprBody_length 39 (Or.inl rfl) s
  have L34 := reprBody_length 34 (Or.inr rfl) s
  by_cases c1 : smart = true ∧ sq ≠ 0 ∧ dq = 0
  · rw [if_pos c1] at h
    have c2 : ¬ (sq ≠ 0 ∧ (34 : Nat) = 39) := by simp
    rw [if_neg c2] at h
    simp only [Except.ok.injEq] at h
    subst h
    rw [if_pos c1]
    have h0 := c1.2.2
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · rw [if_neg c1] at h
    rw [if_neg c1]
    by_cases c0 : sq = 0
    · have c2 : ¬ (sq ≠ 0 ∧ (39 : Nat) = 39) := by simp [c0]
      rw [if_neg c2] at h
      simp only [Except.ok.injEq] at h
      subst h
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    · have c2 : sq ≠ 0 ∧ (39 : Nat) = 39 := ⟨c0, rfl⟩
      rw [if_pos c2] at h
      split at h
      · simp at h
      · simp only [Except.ok.injEq] at h
        subst h
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega

/-! ## `hex` and `fromhex` -/

theorem strhex_plain (s : Seq) (b : Int) (hl : (s.length : Int) < Int.tdiv ssizeMax 2) :
    strhexImpl s none b false = .ok (s.flatMap hexPair) := by
  have h1 : ¬ ((s.length : Int) ≥ Int.tdiv ssizeMax 2 - 0) := by omega
  simp [strhexImpl, bind, Except.bind, pure, Except.pure]
  exact hl

set_option maxRecDepth 100000 in
theorem hexPair_lt (c : Nat) (hc : c < 256) : ∀ x ∈ hexPair c, x < 128 := by
  revert c
  decide

theorem hexflat_lt (s : Seq) (hs : ∀ c ∈ s, c < 256) : ∀ x ∈ s.flatMap hexPair, x < 128 := by
  intro x hx
  simp only [List.mem_flatMap] at hx
  obtain ⟨c, hc, hx⟩ := hx
  exact hexPair_lt c (hs c hc) x hx

theorem hexflat_length (s : Seq) : (s.flatMap hexPair).length = 2 * s.length := by
  induction s with
  | nil => rfl
  | cons c rest ih =>
    simp only [List.flatMap_cons, List.length_append, ih, hexPair, List.length_cons, List.length_nil]
    omega

/-- `fromhex` inverts `hex`: for every byte string, `bytes.fromhex(b.hex()) == b`. A
`len(b)` with `2 * len(b) < sys.maxsize` is a precondition for the text to exist
(`MemoryError` otherwise). -/
def FromHexRoundTrip : Prop :=
  ∀ s : Seq, (∀ c ∈ s, c < 256) → (s.length : Int) < Int.tdiv ssizeMax 2 →
    ∃ text, bytesHex s none 1 = .ok text ∧ bytesFromHex (.str text) = .ok s

theorem fromHexRoundTrip_proven : FromHexRoundTrip := by
  intro s hs hl
  refine ⟨s.flatMap hexPair, ?_, ?_⟩
  · have h1 : ¬ ((1 : Int) < -2147483648 ∨ (1 : Int) > 2147483647) := by decide
    simp only [bytesHex, h1, if_false, strhex_plain s 1 hl]
  · have hf := findIdx_none_lt _ 128 (hexflat_lt s hs)
    have hlen := hexflat_length s
    simp only [bytesFromHex, hf, fromHexRaw]
    have := fromHex_flat s hs ((s.flatMap hexPair) ++ [0]) (s.flatMap hexPair).length 0 []
      ((s.flatMap hexPair).length + 1) (by simp) (by rw [hlen]; omega) (by rw [hlen]; omega)
    simpa using this

theorem flat_filter_id (sep : Nat) (bs : Seq) (hne : ∀ x ∈ bs.flatMap hexPair, x ≠ sep) :
    (bs.flatMap hexPair).filter (· != sep) = bs.flatMap hexPair := by
  rw [List.filter_eq_self]
  intro x hx
  simpa using hne x hx

/-- `hex(sep, k)` for `k ≠ 0`: dropping the separators gives the plain hex digits, whether
the groups count from the left (`k < 0`) or the right (`k > 0`), for every number of chunks;
the separator is not a hex digit of the data. -/
def HexSepFilter : Prop :=
  ∀ (sep abs k : Nat) (bs : Seq), (∀ x ∈ bs.flatMap hexPair, x ≠ sep) →
    (chunkLeft sep abs k bs).filter (· != sep) = bs.flatMap hexPair ∧
    (chunkRight sep abs k bs).filter (· != sep) = bs.flatMap hexPair

theorem hexSepFilter_proven : HexSepFilter := by
  intro sep abs k bs h
  constructor
  · induction k generalizing bs with
    | zero => exact flat_filter_id sep bs h
    | succ k ih =>
      have htake : ∀ x ∈ (bs.take abs).flatMap hexPair, x ≠ sep := by
        intro x hx
        apply h
        simp only [List.mem_flatMap] at hx ⊢
        obtain ⟨c, hc, hx⟩ := hx
        exact ⟨c, List.mem_of_mem_take hc, hx⟩
      have hdrop : ∀ x ∈ (bs.drop abs).flatMap hexPair, x ≠ sep := by
        intro x hx
        apply h
        simp only [List.mem_flatMap] at hx ⊢
        obtain ⟨c, hc, hx⟩ := hx
        exact ⟨c, List.mem_of_mem_drop hc, hx⟩
      simp only [chunkLeft, List.filter_append, flat_filter_id sep _ htake, ih _ hdrop]
      conv => rhs; rw [← List.take_append_drop abs bs, List.flatMap_append]
      simp
  · induction k generalizing bs with
    | zero => exact flat_filter_id sep bs h
    | succ k ih =>
      have htake : ∀ n, ∀ x ∈ (bs.take n).flatMap hexPair, x ≠ sep := by
        intro n x hx
        apply h
        simp only [List.mem_flatMap] at hx ⊢
        obtain ⟨c, hc, hx⟩ := hx
        exact ⟨c, List.mem_of_mem_take hc, hx⟩
      have hdrop : ∀ n, ∀ x ∈ (bs.drop n).flatMap hexPair, x ≠ sep := by
        intro n x hx
        apply h
        simp only [List.mem_flatMap] at hx ⊢
        obtain ⟨c, hc, hx⟩ := hx
        exact ⟨c, List.mem_of_mem_drop hc, hx⟩
      simp only [chunkRight, List.filter_append, flat_filter_id sep _ (hdrop _), ih _ (htake _)]
      conv => rhs; rw [← List.take_append_drop (bs.length - abs) bs, List.flatMap_append]
      simp

/-! ## C API -/

/-- `PyBytes_FromFormat` copies a format with no conversion (up to a NUL) unchanged, and the
accessor functions report a `TypeError` for anything but `bytes`; without a length pointer
`PyBytes_AsStringAndSize` refuses an embedded NUL. -/
def CApiSpec : Prop :=
  (∀ f : Seq, 37 ∉ f → 0 ∉ f → bytesFromFormat f [] = .ok f) ∧
  (∀ (s : Seq), pyBytesSize (.bytes s) = .ok s.length ∧ pyBytesAsString (.bytes s) = .ok s ∧
    pyBytesAsStringAndSize (.bytes s) true = .ok s) ∧
  (∀ o : Obj, (∀ s, o ≠ .bytes s) → pyBytesSize o = .error (expectedBytes o) ∧
    pyBytesAsString o = .error (expectedBytes o)) ∧
  (∀ (a b : Seq), 0 ∉ a → pyBytesAsStringAndSize (.bytes (a ++ 0 :: b)) false =
    .error (.valueError "embedded null byte")) ∧
  (∀ (s : Seq), (s.length : Int) + 33 < 2 ^ 47 → bytesFromStringAndSize (some s) s.length = .ok s) ∧
  (∀ (s : Option Seq) (n : Int), n < 0 → bytesFromStringAndSize s n =
    .error (systemError "Negative size passed to PyBytes_FromStringAndSize")) ∧
  (∀ (a b : Seq), 0 ∉ a → bytesFromCString (a ++ 0 :: b) = a)

theorem fromFormat_literal (f : Seq) (h1 : 37 ∉ f) (h0 : 0 ∉ f) (fuel i : Nat) (out : Seq)
    (hf : f.length - i < fuel) :
    fromFormatLoop f fuel i [] out = .ok (out ++ f.drop i) := by
  induction fuel generalizing i out with
  | zero => omega
  | succ fuel ih =>
    simp only [fromFormatLoop]
    by_cases hi : i < f.length
    · have hm : f[i] ∈ f := List.getElem_mem hi
      have e : cAt f i = f[i] := by simp [cAt, List.getD, hi]
      have ne0 : f[i] ≠ 0 := fun e => h0 (e ▸ hm)
      have ne37 : f[i] ≠ 37 := fun e => h1 (e ▸ hm)
      rw [e, if_neg ne0, if_pos ne37, ih (i + 1) _ (by omega)]
      simp [← List.drop_eq_getElem_cons hi]
    · have e : cAt f i = 0 := by simp [cAt, List.getD, hi]
      rw [e, if_pos rfl]
      simp [List.drop_of_length_le (show f.length ≤ i by omega)]

theorem takeWhile_nz (a b : Seq) (h : 0 ∉ a) : (a ++ 0 :: b).takeWhile (· != 0) = a := by
  induction a with
  | nil => simp
  | cons c cs ih =>
    have hc : c ≠ 0 := fun e => h (by simp [e])
    have hcs : 0 ∉ cs := fun e => h (by simp [e])
    simp [hc, ih hcs]

theorem cApiSpec_proven : CApiSpec := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f h1 h0
    simpa [bytesFromFormat] using fromFormat_literal f h1 h0 (f.length + 1) 0 [] (by omega)
  · intro s
    simp [pyBytesSize, pyBytesAsString, pyBytesAsStringAndSize]
  · intro o h
    cases o <;> first | exact absurd rfl (h _) | simp [pyBytesSize, pyBytesAsString]
  · intro a b h
    have e := takeWhile_nz a b h
    have c : (!false) = true ∧ ((a ++ 0 :: b).takeWhile (· != 0)).length ≠ (a ++ 0 :: b).length :=
      ⟨rfl, by rw [e]; simp⟩
    simp only [pyBytesAsStringAndSize]
    rw [if_pos c]
  · exact from_string_ok
  · intro s n h
    simp [bytesFromStringAndSize, h]
  · exact fun a b h => takeWhile_nz a b h

end PyLean.BytesObj.Bytes
