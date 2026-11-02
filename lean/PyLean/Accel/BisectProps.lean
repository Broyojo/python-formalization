import PyLean.Accel.Bisect

/-!
Properties of `bisect`: C/Python agreement and the documented insertion point.
-/

namespace PyLean.Accel

open PyLean

/-! ### Loop lemmas -/

theorem ite_true' {β : Type} {c : Prop} [Decidable c] {a b : β} (h : c) :
    (if c then a else b) = a := by simp [h]

theorem ite_false' {β : Type} {c : Prop} [Decidable c] {a b : β} (h : ¬c) :
    (if c then a else b) = b := by simp [h]

theorem bisectLoop_congr (p1 p2 : Int → Py Int) (g : Int → Bool) :
    ∀ (fuel : Nat) (lo hi : Int), (∀ m, lo ≤ m → m < hi → p1 m = p2 m) →
      bisectLoop p1 g fuel lo hi = bisectLoop p2 g fuel lo hi := by
  intro fuel
  induction fuel with
  | zero => intro lo hi _; simp [bisectLoop]
  | succ fuel ih =>
    intro lo hi h
    simp only [bisectLoop]
    split
    · rw [h ((lo + hi) / 2) (by omega) (by omega)]
      cases p2 ((lo + hi) / 2) with
      | error e => rfl
      | ok v =>
        simp only [bind, Except.bind]
        split
        · exact ih _ _ (fun m h1 h2 => h m (by omega) h2)
        · exact ih _ _ (fun m h1 h2 => h m h1 (by omega))
    · rfl

/-- A successful loop returns `lo` itself or a value in `[lo, hi]`. -/
theorem bisectLoop_range (p : Int → Py Int) (g : Int → Bool) :
    ∀ (fuel : Nat) (lo hi ip : Int), bisectLoop p g fuel lo hi = .ok ip →
      lo ≤ ip ∧ (ip ≤ hi ∨ ip = lo) := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi ip h
    simp only [bisectLoop] at h
    split at h
    · cases h
    · cases h; omega
  | succ fuel ih =>
    intro lo hi ip h
    simp only [bisectLoop] at h
    split at h
    · cases hp : p ((lo + hi) / 2) with
      | error e => rw [hp] at h; cases h
      | ok v =>
        rw [hp] at h
        simp only [bind, Except.bind] at h
        split at h
        · have := ih _ _ _ h; omega
        · have := ih _ _ _ h; omega
    · cases h; omega

/-- The loop invariant. `f k` is the (keyed) element at `k < n`; `g` is
monotone (antitone in the "go right" sense). If the loop returns `ip`, every
index in `[L, ip)` below `n` goes right and every index in `[ip, H)` below `n`
does not. -/
theorem bisectLoop_partition (n : Int) (f : Int → Int) (p : Int → Py Int) (g : Int → Bool)
    (hp : ∀ m v, p m = .ok v → m < n ∧ v = f m)
    (hmono : ∀ i j, 0 ≤ i → i ≤ j → j < n → g (f j) = true → g (f i) = true)
    (L H : Int) :
    ∀ (fuel : Nat) (lo hi ip : Int), 0 ≤ L → L ≤ lo → (lo < hi → hi ≤ H) →
      (∀ k, L ≤ k → k < lo → k < n → g (f k) = true) →
      (∀ k, hi ≤ k → k < H → k < n → g (f k) = false) →
      bisectLoop p g fuel lo hi = .ok ip →
      (∀ k, L ≤ k → k < ip → k < n → g (f k) = true) ∧
      (∀ k, ip ≤ k → k < H → k < n → g (f k) = false) := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi ip hL hLlo hhi hleft hright h
    simp only [bisectLoop] at h
    split at h
    · cases h
    · cases h
      exact ⟨hleft, fun k h1 h2 h3 => hright k (by omega) h2 h3⟩
  | succ fuel ih =>
    intro lo hi ip hL hLlo hhi hleft hright h
    simp only [bisectLoop] at h
    split at h
    · rename_i hlt
      cases hpm : p ((lo + hi) / 2) with
      | error e => rw [hpm] at h; cases h
      | ok v =>
        rw [hpm] at h
        obtain ⟨hmn, rfl⟩ := hp _ _ hpm
        simp only [bind, Except.bind] at h
        split at h
        · rename_i hg
          refine ih _ _ _ hL (by omega) (fun _ => hhi hlt) ?_ hright h
          intro k h1 h2 h3
          by_cases hk : k < lo
          · exact hleft k h1 hk h3
          · exact hmono k _ (by omega) (by omega) hmn hg
        · rename_i hg
          refine ih _ _ _ hL hLlo (fun _ => by omega) hleft ?_ h
          intro k h1 h2 h3
          by_cases hk : hi ≤ k
          · exact hright k hk h2 h3
          · cases hgk : g (f k) with
            | false => rfl
            | true =>
              have := hmono _ k (by omega) h1 h3 hgk
              simp_all
    · cases h
      exact ⟨hleft, fun k h1 h2 h3 => hright k (by omega) h2 h3⟩

/-- With enough fuel and probes that succeed on `[lo, hi)`, the loop succeeds. -/
theorem bisectLoop_ok (p : Int → Py Int) (g : Int → Bool) :
    ∀ (fuel : Nat) (lo hi : Int), (hi - lo).toNat ≤ fuel →
      (∀ m, lo ≤ m → m < hi → ∃ v, p m = .ok v) →
      ∃ ip, bisectLoop p g fuel lo hi = .ok ip := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi hf _
    simp only [bisectLoop]
    split
    · omega
    · exact ⟨_, rfl⟩
  | succ fuel ih =>
    intro lo hi hf hp
    simp only [bisectLoop]
    split
    · obtain ⟨v, hv⟩ := hp ((lo + hi) / 2) (by omega) (by omega)
      rw [hv]
      simp only [bind, Except.bind]
      split
      · exact ih _ _ (by omega) (fun m h1 h2 => hp m (by omega) h2)
      · exact ih _ _ (by omega) (fun m h1 h2 => hp m h1 (by omega))
    · exact ⟨_, rfl⟩

/-! ### Twin agreement -/

/-- Twin agreement, for all arguments: `bisect_left`, `bisect_right`,
`insort_left` and `insort_right` of `_bisect` and `bisect.py` return the same
value (or raise the same exception, message included) and leave the same list.
Hypothesis: `len(a)` fits a `Py_ssize_t` (type invariant of `list`). -/
def BisectTwinsAgree : Prop :=
  ∀ (a : List Int) (x lo : Int) (hi : Option Int) (key : Option (Int → Int)),
    (a.length : Int) ≤ ssizeMax →
    cBisectLeft a x lo hi key = pyBisectLeft a x lo hi key ∧
    cBisectRight a x lo hi key = pyBisectRight a x lo hi key ∧
    cInsortLeft a x lo hi key = pyInsortLeft a x lo hi key ∧
    cInsortRight a x lo hi key = pyInsortRight a x lo hi key

/-- `bisect_left([1, 2, 3, 4, 5], 3, 0, -1)` is 2 in C (`hi=-1` is the
clinic default meaning `len(a)`) and 0 in Python (empty range). -/
theorem bisectTwinsAgree_refuted : ¬BisectTwinsAgree := by
  intro h
  have := (h [1, 2, 3, 4, 5] 3 0 (some (-1)) none (by decide)).1
  revert this
  decide

/-- Twin agreement when `hi` is not `-1`: the same four functions agree for
every other `lo` and `hi`, including ints outside `Py_ssize_t`. -/
def BisectTwinsAgreeHiNotMinusOne : Prop :=
  ∀ (a : List Int) (x lo : Int) (hi : Option Int) (key : Option (Int → Int)),
    (a.length : Int) ≤ ssizeMax → hi ≠ some (-1) →
    cBisectLeft a x lo hi key = pyBisectLeft a x lo hi key ∧
    cBisectRight a x lo hi key = pyBisectRight a x lo hi key ∧
    cInsortLeft a x lo hi key = pyInsortLeft a x lo hi key ∧
    cInsortRight a x lo hi key = pyInsortRight a x lo hi key

/-- `bisect_left([1, 2, 3, 4, 5], 3, 2**63)` raises `OverflowError` in C and
returns `2**63` in Python. -/
theorem bisectTwinsAgreeHiNotMinusOne_refuted : ¬BisectTwinsAgreeHiNotMinusOne := by
  intro h
  have := (h [1, 2, 3, 4, 5] 3 (2 ^ 63) none none (by decide) (by decide)).1
  revert this
  decide

/-- Twin agreement for `Py_ssize_t` arguments other than `hi = -1`. -/
def BisectTwinsAgreeInRange : Prop :=
  ∀ (a : List Int) (x lo : Int) (hi : Option Int) (key : Option (Int → Int)),
    (a.length : Int) ≤ ssizeMax → hi ≠ some (-1) →
    ssizeMin ≤ lo → lo ≤ ssizeMax → (∀ h, hi = some h → ssizeMin ≤ h ∧ h ≤ ssizeMax) →
    cBisectLeft a x lo hi key = pyBisectLeft a x lo hi key ∧
    cBisectRight a x lo hi key = pyBisectRight a x lo hi key ∧
    cInsortLeft a x lo hi key = pyInsortLeft a x lo hi key ∧
    cInsortRight a x lo hi key = pyInsortRight a x lo hi key

/-- True on 3.14.7, false on 3.15.2: `bisect_left([], 0, -1)` raises
`ValueError('lo cannot be negative')` in C (the `allow_negative=False` converter)
and `ValueError('lo must be non-negative')` in Python. -/
theorem bisectTwinsAgreeInRange_refuted : ¬BisectTwinsAgreeInRange := by
  intro h
  have := (h [] 0 (-1) none none (by decide) (by simp) (by decide) (by decide) (by simp)).1
  revert this
  decide

/-- The same four functions for every non-negative `Py_ssize_t` `lo` and every
`Py_ssize_t` `hi` except `-1`: same value or same exception and message, and the
same final list. The hypotheses beyond `len(a)` are exactly the refuted cases. -/
def BisectTwinsAgreeNonnegLo : Prop :=
  ∀ (a : List Int) (x lo : Int) (hi : Option Int) (key : Option (Int → Int)),
    (a.length : Int) ≤ ssizeMax → hi ≠ some (-1) →
    0 ≤ lo → lo ≤ ssizeMax → (∀ h, hi = some h → ssizeMin ≤ h ∧ h ≤ ssizeMax) →
    cBisectLeft a x lo hi key = pyBisectLeft a x lo hi key ∧
    cBisectRight a x lo hi key = pyBisectRight a x lo hi key ∧
    cInsortLeft a x lo hi key = pyInsortLeft a x lo hi key ∧
    cInsortRight a x lo hi key = pyInsortRight a x lo hi key

/-- A negative `lo` that fits a `Py_ssize_t`, whatever `hi` is, even an `hi` C
cannot convert: both twins raise `ValueError` before reading `a`, each with its
own message. C refuses in the `lo` converter, so before `hi` is converted. -/
def BisectNegativeLoRaises : Prop :=
  ∀ (a : List Int) (x lo : Int) (hi : Option Int) (key : Option (Int → Int)),
    ssizeMin ≤ lo → lo < 0 →
    cBisectLeft a x lo hi key = .error (.valueError "lo cannot be negative") ∧
    cBisectRight a x lo hi key = .error (.valueError "lo cannot be negative") ∧
    cInsortLeft a x lo hi key = .error (.valueError "lo cannot be negative") ∧
    cInsortRight a x lo hi key = .error (.valueError "lo cannot be negative") ∧
    pyBisectLeft a x lo hi key = .error (.valueError "lo must be non-negative") ∧
    pyBisectRight a x lo hi key = .error (.valueError "lo must be non-negative") ∧
    pyInsortLeft a x lo hi key = .error (.valueError "lo must be non-negative") ∧
    pyInsortRight a x lo hi key = .error (.valueError "lo must be non-negative")

theorem bisectNegativeLoRaises_proven : BisectNegativeLoRaises := by
  intro a x lo hi key h1 h2
  have hc : cConvLo lo = .error (.valueError "lo cannot be negative") := by
    simp only [cConvLo]
    rw [ite_false' (by unfold ssizeMax; omega), ite_true' h2]
  have hl : ∀ y, pyBisectLeft a y lo hi key = .error (.valueError "lo must be non-negative") :=
    fun y => by simp only [pyBisectLeft]; rw [ite_true' h2]
  have hr : ∀ y, pyBisectRight a y lo hi key = .error (.valueError "lo must be non-negative") :=
    fun y => by simp only [pyBisectRight]; rw [ite_true' h2]
  simp only [cBisectLeft, cBisectRight, cInsortLeft, cInsortRight, pyInsortLeft, pyInsortRight,
    hc, hl, hr, bind, Except.bind]
  simp

/-- The C and Python `hi` agree once converted. -/
theorem cHi_eq (a : List Int) (hi : Option Int) (h : Int) (hne : hi ≠ some (-1))
    (hc : cConvHi hi = .ok h) :
    (if h = -1 then (a.length : Int) else h) = hi.getD a.length := by
  cases hi with
  | none => simp [cConvHi] at hc; subst hc; simp
  | some h' =>
    simp only [cConvHi] at hc
    split at hc
    · cases hc
    · cases hc
      have : h ≠ -1 := fun e => hne (by rw [e])
      simp [this]

theorem pyIndex_eq_cIndex (a : List Int) (m : Int) (hm : m ≤ ssizeMax) :
    pyIndex a m = cIndex a m := by
  simp only [pyIndex, cIndex]
  rw [ite_false' (by omega)]

theorem cConvHi_some_le (hi : Option Int) (h : Int) (hc : cConvHi hi = .ok h) : h ≤ ssizeMax := by
  cases hi with
  | none => simp [cConvHi] at hc; subst hc; decide
  | some h' =>
    simp only [cConvHi] at hc
    split at hc
    · cases hc
    · cases hc; omega

/-- The internal searches agree on converted arguments (left). -/
theorem internalLeft_eq (a : List Int) (x lo : Int) (hi : Option Int) (h : Int)
    (key : Option (Int → Int)) (hlen : (a.length : Int) ≤ ssizeMax)
    (hne : hi ≠ some (-1)) (hc : cConvHi hi = .ok h) (h0 : 0 ≤ lo) :
    cInternalLeft a x lo h key = pyBisectLeft a x lo hi key := by
  have hh := cHi_eq a hi h hne hc
  have hle := cConvHi_some_le hi h hc
  simp only [cInternalLeft, pyBisectLeft]
  rw [ite_false' (show ¬ lo < 0 by omega), hh]
  apply bisectLoop_congr
  intro m h1 h2
  have : hi.getD a.length ≤ ssizeMax := by
    cases hi with
    | none => simpa using hlen
    | some h' => rw [← hh]; split <;> omega
  rw [pyIndex_eq_cIndex a m (by omega)]

theorem internalRight_eq (a : List Int) (x lo : Int) (hi : Option Int) (h : Int)
    (key : Option (Int → Int)) (hlen : (a.length : Int) ≤ ssizeMax)
    (hne : hi ≠ some (-1)) (hc : cConvHi hi = .ok h) (h0 : 0 ≤ lo) :
    cInternalRight a x lo h key = pyBisectRight a x lo hi key := by
  have hh := cHi_eq a hi h hne hc
  have hle := cConvHi_some_le hi h hc
  simp only [cInternalRight, pyBisectRight]
  rw [ite_false' (show ¬ lo < 0 by omega), hh]
  apply bisectLoop_congr
  intro m h1 h2
  have : hi.getD a.length ≤ ssizeMax := by
    cases hi with
    | none => simpa using hlen
    | some h' => rw [← hh]; split <;> omega
  rw [pyIndex_eq_cIndex a m (by omega)]

/-- A successful Python search returns a value in `[0, PY_SSIZE_T_MAX]`. -/
theorem pyBisectLeft_range (a : List Int) (x lo : Int) (hi : Option Int) (key : Option (Int → Int))
    (hlen : (a.length : Int) ≤ ssizeMax) (hlo : lo ≤ ssizeMax)
    (hhi : ∀ h, hi = some h → h ≤ ssizeMax) (ip : Int)
    (hr : pyBisectLeft a x lo hi key = .ok ip) : 0 ≤ ip ∧ ip ≤ ssizeMax := by
  simp only [pyBisectLeft] at hr
  split at hr
  · cases hr
  · have := bisectLoop_range _ _ _ _ _ _ hr
    have : hi.getD a.length ≤ ssizeMax := by
      cases hi with
      | none => simpa using hlen
      | some h' => simpa using hhi h' rfl
    omega

theorem pyBisectRight_range (a : List Int) (x lo : Int) (hi : Option Int) (key : Option (Int → Int))
    (hlen : (a.length : Int) ≤ ssizeMax) (hlo : lo ≤ ssizeMax)
    (hhi : ∀ h, hi = some h → h ≤ ssizeMax) (ip : Int)
    (hr : pyBisectRight a x lo hi key = .ok ip) : 0 ≤ ip ∧ ip ≤ ssizeMax := by
  simp only [pyBisectRight] at hr
  split at hr
  · cases hr
  · have := bisectLoop_range _ _ _ _ _ _ hr
    have : hi.getD a.length ≤ ssizeMax := by
      cases hi with
      | none => simpa using hlen
      | some h' => simpa using hhi h' rfl
    omega

theorem listInsert_eq (a : List Int) (i x : Int) (h0 : 0 ≤ i) (h1 : i ≤ ssizeMax) :
    listInsert a i x = .ok (cListInsert a i x) := by
  simp only [listInsert, cListInsert]
  rw [ite_false' (by unfold ssizeMin; omega), ite_false' (by omega)]

theorem bisectTwinsAgreeNonnegLo_proven : BisectTwinsAgreeNonnegLo := by
  intro a x lo hi key hlen hne hlo1 hlo2 hhi
  have hcl : cConvLo lo = .ok lo := by
    simp only [cConvLo]
    rw [ite_false' (by unfold ssizeMin; omega), ite_false' (by omega)]
  have hhi' : ∀ h, hi = some h → h ≤ ssizeMax := fun h e => (hhi h e).2
  cases hc : cConvHi hi with
  | error e =>
    exfalso
    cases hi with
    | none => simp [cConvHi] at hc
    | some h' =>
      have := hhi h' rfl
      simp only [cConvHi] at hc
      rw [ite_false' (by omega)] at hc
      cases hc
  | ok h =>
    have eL := internalLeft_eq a x lo hi h key hlen hne hc hlo1
    have eR := internalRight_eq a x lo hi h key hlen hne hc hlo1
    have eL' := internalLeft_eq a (applyKey key x) lo hi h key hlen hne hc hlo1
    have eR' := internalRight_eq a (applyKey key x) lo hi h key hlen hne hc hlo1
    simp only [cBisectLeft, cBisectRight, cInsortLeft, cInsortRight, pyInsortLeft, pyInsortRight,
      hcl, hc, bind, Except.bind, eL, eR, eL', eR']
    refine ⟨trivial, trivial, ?_, ?_⟩
    · cases hr : pyBisectLeft a (applyKey key x) lo hi key with
      | error e => rfl
      | ok ip =>
        have := pyBisectLeft_range a _ lo hi key hlen hlo2 hhi' ip hr
        simp only [pure, Except.pure]
        rw [listInsert_eq a ip x this.1 this.2]
    · cases hr : pyBisectRight a (applyKey key x) lo hi key with
      | error e => rfl
      | ok ip =>
        have := pyBisectRight_range a _ lo hi key hlen hlo2 hhi' ip hr
        simp only [pure, Except.pure]
        rw [listInsert_eq a ip x this.1 this.2]

/-! ### The documented insertion point -/

/-- `a` is sorted by `key` (`key=None`: by value). -/
def SortedBy (key : Option (Int → Int)) (a : List Int) : Prop :=
  a.Pairwise (fun u v => applyKey key u ≤ applyKey key v)

/-- Python's `a[start:stop]` (step 1) for int bounds: a negative bound counts
from the end, then both are clamped to `[0, len(a)]`. -/
def pySlice (a : List Int) (start stop : Int) : List Int :=
  let n : Int := a.length
  let norm (i : Int) : Int := if i < 0 then max (i + n) 0 else min i n
  let s := norm start
  let e := norm stop
  (a.drop s.toNat).take (e - s).toNat

theorem mem_pySlice (a : List Int) (s t : Int) (hs : 0 ≤ s) (ht : 0 ≤ t) (e : Int)
    (he : e ∈ pySlice a s t) :
    ∃ k : Nat, s ≤ k ∧ (k : Int) < t ∧ k < a.length ∧ a.getD k 0 = e := by
  simp only [pySlice, ite_false' (show ¬ s < 0 by omega), ite_false' (show ¬ t < 0 by omega)] at he
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 he
  simp only [List.length_take, List.length_drop] at hi
  refine ⟨(min s a.length).toNat + i, by omega, by omega, by omega, ?_⟩
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show (min s a.length).toNat + i < a.length by omega)]

theorem sortedBy_get (key : Option (Int → Int)) (a : List Int) (hs : SortedBy key a)
    (i j : Nat) (hij : i ≤ j) (hj : j < a.length) :
    applyKey key (a.getD i 0) ≤ applyKey key (a.getD j 0) := by
  rcases Nat.eq_or_lt_of_le hij with rfl | hlt
  · exact Int.le_refl _
  · have := List.pairwise_iff_getElem.1 hs i j (by omega) hj hlt
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < a.length by omega),
      List.getElem?_eq_getElem hj] using this

/-- The keyed element at an int index. -/
def keyAt (key : Option (Int → Int)) (a : List Int) (k : Int) : Int := applyKey key (a.getD k.toNat 0)

theorem pyProbe_spec (key : Option (Int → Int)) (a : List Int) (m v : Int)
    (h : (applyKey key <$> pyIndex a m) = .ok v) : m < a.length ∧ v = keyAt key a m := by
  simp only [pyIndex] at h
  split at h
  · cases h
  · split at h
    · cases h; exact ⟨by omega, rfl⟩
    · cases h

theorem cProbe_spec (key : Option (Int → Int)) (a : List Int) (m v : Int)
    (h : (applyKey key <$> cIndex a m) = .ok v) : m < a.length ∧ v = keyAt key a m := by
  simp only [cIndex] at h
  split at h
  · cases h; exact ⟨by omega, rfl⟩
  · cases h

theorem mono_left (key : Option (Int → Int)) (a : List Int) (x : Int) (hs : SortedBy key a) :
    ∀ i j : Int, 0 ≤ i → i ≤ j → j < a.length →
      decide (keyAt key a j < x) = true → decide (keyAt key a i < x) = true := by
  intro i j h0 hij hj hg
  have := sortedBy_get key a hs i.toNat j.toNat (by omega) (by omega)
  simp only [keyAt] at hg ⊢
  have := of_decide_eq_true hg
  exact decide_eq_true (by omega)

theorem mono_right (key : Option (Int → Int)) (a : List Int) (x : Int) (hs : SortedBy key a) :
    ∀ i j : Int, 0 ≤ i → i ≤ j → j < a.length →
      (!decide (x < keyAt key a j)) = true → (!decide (x < keyAt key a i)) = true := by
  intro i j h0 hij hj hg
  have := sortedBy_get key a hs i.toNat j.toNat (by omega) (by omega)
  simp only [keyAt, Bool.not_eq_true'] at hg ⊢
  have := of_decide_eq_false hg
  exact decide_eq_false (by omega)

/-- `bisect_left` docstring, Lib/bisect.py:77-79 and Doc/library/bisect.rst:48-51,
for in-range bounds `0 <= lo <= hi <= len(a)` (`hi=None` is `len(a)`) and `a`
sorted by key: both twins return the same `ip` in `[lo, hi]` with every keyed
element of `a[lo:ip]` `< x` and every one of `a[ip:hi]` `>= x`. -/
def BisectLeftPartition : Prop :=
  ∀ (a : List Int) (x lo : Int) (hi : Option Int) (key : Option (Int → Int)),
    (a.length : Int) ≤ ssizeMax → SortedBy key a →
    0 ≤ lo → lo ≤ hi.getD a.length → hi.getD a.length ≤ a.length →
    ∃ ip, pyBisectLeft a x lo hi key = .ok ip ∧ cBisectLeft a x lo hi key = .ok ip ∧
      lo ≤ ip ∧ ip ≤ hi.getD a.length ∧
      (∀ k : Nat, lo ≤ k → (k : Int) < ip → applyKey key (a.getD k 0) < x) ∧
      (∀ k : Nat, ip ≤ k → (k : Int) < hi.getD a.length → x ≤ applyKey key (a.getD k 0))

/-- `bisect_right` docstring, Lib/bisect.py:24-26: as above with `<= x` on the
left and `> x` on the right. -/
def BisectRightPartition : Prop :=
  ∀ (a : List Int) (x lo : Int) (hi : Option Int) (key : Option (Int → Int)),
    (a.length : Int) ≤ ssizeMax → SortedBy key a →
    0 ≤ lo → lo ≤ hi.getD a.length → hi.getD a.length ≤ a.length →
    ∃ ip, pyBisectRight a x lo hi key = .ok ip ∧ cBisectRight a x lo hi key = .ok ip ∧
      lo ≤ ip ∧ ip ≤ hi.getD a.length ∧
      (∀ k : Nat, lo ≤ k → (k : Int) < ip → applyKey key (a.getD k 0) ≤ x) ∧
      (∀ k : Nat, ip ≤ k → (k : Int) < hi.getD a.length → x < applyKey key (a.getD k 0))

theorem hi_ne_of_in_range (a : List Int) (lo : Int) (hi : Option Int) (h0 : 0 ≤ lo)
    (h1 : lo ≤ hi.getD a.length) : hi ≠ some (-1) := by
  rintro rfl; simp at h1; omega

theorem twins_of_in_range (a : List Int) (lo : Int) (hi : Option Int)
    (hlen : (a.length : Int) ≤ ssizeMax) (h0 : 0 ≤ lo)
    (h1 : lo ≤ hi.getD a.length) (h2 : hi.getD a.length ≤ a.length) :
    ∀ x key, cBisectLeft a x lo hi key = pyBisectLeft a x lo hi key ∧
      cBisectRight a x lo hi key = pyBisectRight a x lo hi key := by
  intro x key
  have h := bisectTwinsAgreeNonnegLo_proven a x lo hi key hlen (hi_ne_of_in_range a lo hi h0 h1)
    h0 (by omega) (fun h e => by subst e; simp at h1 h2; unfold ssizeMin; omega)
  exact ⟨h.1, h.2.1⟩

theorem bisectLeftPartition_proven : BisectLeftPartition := by
  intro a x lo hi key hlen hs h0 h1 h2
  have ht := twins_of_in_range a lo hi hlen h0 h1 h2 x key
  have hpy : pyBisectLeft a x lo hi key =
      bisectLoop (fun mid => applyKey key <$> pyIndex a mid) (fun v => decide (v < x))
        (hi.getD a.length - lo).toNat lo (hi.getD a.length) := by
    simp only [pyBisectLeft, ite_false' (show ¬ lo < 0 by omega)]
  obtain ⟨ip, hip⟩ := bisectLoop_ok (fun mid => applyKey key <$> pyIndex a mid) (fun v => decide (v < x))
    _ lo (hi.getD a.length) (Nat.le_refl _) (fun m hm1 hm2 => by
      simp only [pyIndex, ite_false' (show ¬ m > ssizeMax by omega),
        ite_true' (show 0 ≤ m ∧ m < a.length by omega)]
      exact ⟨_, rfl⟩)
  refine ⟨ip, hpy ▸ hip, ht.1 ▸ hpy ▸ hip, ?_⟩
  have hr := bisectLoop_range _ _ _ _ _ _ hip
  have hp := bisectLoop_partition a.length (keyAt key a) _ _ (pyProbe_spec key a)
    (mono_left key a x hs) lo (hi.getD a.length) _ lo (hi.getD a.length) ip h0 (Int.le_refl _)
    (fun _ => Int.le_refl _) (fun k h1 h2 _ => by omega) (fun k h1 h2 _ => by omega) hip
  refine ⟨hr.1, by omega, ?_, ?_⟩
  · intro k hk1 hk2
    have := hp.1 k hk1 hk2 (by omega)
    simpa [keyAt] using this
  · intro k hk1 hk2
    have := hp.2 k hk1 hk2 (by omega)
    simp only [keyAt, Int.toNat_natCast] at this
    have := of_decide_eq_false this
    omega

theorem bisectRightPartition_proven : BisectRightPartition := by
  intro a x lo hi key hlen hs h0 h1 h2
  have ht := twins_of_in_range a lo hi hlen h0 h1 h2 x key
  have hpy : pyBisectRight a x lo hi key =
      bisectLoop (fun mid => applyKey key <$> pyIndex a mid) (fun v => !decide (x < v))
        (hi.getD a.length - lo).toNat lo (hi.getD a.length) := by
    simp only [pyBisectRight, ite_false' (show ¬ lo < 0 by omega)]
  obtain ⟨ip, hip⟩ := bisectLoop_ok (fun mid => applyKey key <$> pyIndex a mid) (fun v => !decide (x < v))
    _ lo (hi.getD a.length) (Nat.le_refl _) (fun m hm1 hm2 => by
      simp only [pyIndex, ite_false' (show ¬ m > ssizeMax by omega),
        ite_true' (show 0 ≤ m ∧ m < a.length by omega)]
      exact ⟨_, rfl⟩)
  refine ⟨ip, hpy ▸ hip, ht.2 ▸ hpy ▸ hip, ?_⟩
  have hr := bisectLoop_range _ _ _ _ _ _ hip
  have hp := bisectLoop_partition a.length (keyAt key a) _ _ (pyProbe_spec key a)
    (mono_right key a x hs) lo (hi.getD a.length) _ lo (hi.getD a.length) ip h0 (Int.le_refl _)
    (fun _ => Int.le_refl _) (fun k h1 h2 _ => by omega) (fun k h1 h2 _ => by omega) hip
  refine ⟨hr.1, by omega, ?_, ?_⟩
  · intro k hk1 hk2
    have := hp.1 k hk1 hk2 (by omega)
    simp only [keyAt, Int.toNat_natCast, Bool.not_eq_true'] at this
    have := of_decide_eq_false this
    omega
  · intro k hk1 hk2
    have := hp.2 k hk1 hk2 (by omega)
    simpa [keyAt] using this

/-! ### The docstring's slice form, for any `lo` and `hi` -/

/-- `all(key(e) < x for e in a[lo:ip]) and all(key(e) >= x for e in a[ip:hi])`. -/
def LeftDoc (key : Option (Int → Int)) (a : List Int) (x lo ip hi : Int) : Prop :=
  (∀ e ∈ pySlice a lo ip, applyKey key e < x) ∧ (∀ e ∈ pySlice a ip hi, x ≤ applyKey key e)

/-- `all(key(e) <= x for e in a[lo:ip]) and all(key(e) > x for e in a[ip:hi])`. -/
def RightDoc (key : Option (Int → Int)) (a : List Int) (x lo ip hi : Int) : Prop :=
  (∀ e ∈ pySlice a lo ip, applyKey key e ≤ x) ∧ (∀ e ∈ pySlice a ip hi, x < applyKey key e)

/-- Doc/library/bisect.rst:48-51 and :70-72, read literally for every `lo`
and `hi` the functions accept: whenever a twin returns `ip` for a sorted `a`,
`ip` partitions the slices `a[lo:ip]` and `a[ip:hi]` (`hi=None` is `len(a)`). -/
def BisectDocPartition : Prop :=
  ∀ (a : List Int) (x lo : Int) (hi : Option Int) (key : Option (Int → Int)),
    (a.length : Int) ≤ ssizeMax → SortedBy key a →
    (∀ ip, pyBisectLeft a x lo hi key = .ok ip → LeftDoc key a x lo ip (hi.getD a.length)) ∧
    (∀ ip, cBisectLeft a x lo hi key = .ok ip → LeftDoc key a x lo ip (hi.getD a.length)) ∧
    (∀ ip, pyBisectRight a x lo hi key = .ok ip → RightDoc key a x lo ip (hi.getD a.length)) ∧
    (∀ ip, cBisectRight a x lo hi key = .ok ip → RightDoc key a x lo ip (hi.getD a.length))

/-- Python `bisect_left([1, 2, 3, 4, 5], 3, 0, -1)` returns 0, but
`a[0:-1] = [1, 2, 3, 4]` contains elements `< 3` (python/cpython#125889). -/
theorem bisectDocPartition_refuted : ¬BisectDocPartition := by
  intro h
  have h1 := (h [1, 2, 3, 4, 5] 3 0 (some (-1)) none (by decide)
    (by simp [SortedBy, applyKey])).1 0 (by decide)
  have := h1.2 1 (by decide)
  revert this
  decide

/-- The same for `hi=None` or `hi >= 0` (any `lo`, including `lo > hi` and
`hi > len(a)`): a twin that returns at all returns a correct partition point;
otherwise it raises (`IndexError` when the search probes past the end). -/
def BisectDocPartitionNonnegHi : Prop :=
  ∀ (a : List Int) (x lo : Int) (hi : Option Int) (key : Option (Int → Int)),
    (a.length : Int) ≤ ssizeMax → SortedBy key a → (∀ h, hi = some h → 0 ≤ h) →
    (∀ ip, pyBisectLeft a x lo hi key = .ok ip → LeftDoc key a x lo ip (hi.getD a.length)) ∧
    (∀ ip, cBisectLeft a x lo hi key = .ok ip → LeftDoc key a x lo ip (hi.getD a.length)) ∧
    (∀ ip, pyBisectRight a x lo hi key = .ok ip → RightDoc key a x lo ip (hi.getD a.length)) ∧
    (∀ ip, cBisectRight a x lo hi key = .ok ip → RightDoc key a x lo ip (hi.getD a.length))

theorem doc_of_loop (key : Option (Int → Int)) (a : List Int) (probe : Int → Py Int) (g : Int → Bool)
    (hprobe : ∀ m v, probe m = .ok v → m < a.length ∧ v = keyAt key a m)
    (hmono : ∀ i j : Int, 0 ≤ i → i ≤ j → j < a.length → g (keyAt key a j) = true → g (keyAt key a i) = true)
    (fuel : Nat) (lo H ip : Int) (h0 : 0 ≤ lo) (hH : 0 ≤ H)
    (hloop : bisectLoop probe g fuel lo H = .ok ip) :
    (∀ e ∈ pySlice a lo ip, g (applyKey key e) = true) ∧
    (∀ e ∈ pySlice a ip H, g (applyKey key e) = false) := by
  have hr := bisectLoop_range _ _ _ _ _ _ hloop
  have hp := bisectLoop_partition a.length (keyAt key a) probe g hprobe hmono lo H fuel lo H ip h0
    (Int.le_refl _) (fun _ => Int.le_refl _) (fun k h1 h2 _ => by omega) (fun k h1 h2 _ => by omega) hloop
  constructor
  · intro e he
    obtain ⟨k, hk1, hk2, hk3, rfl⟩ := mem_pySlice a lo ip h0 (by omega) e he
    have := hp.1 k hk1 hk2 (by omega)
    simpa [keyAt] using this
  · intro e he
    obtain ⟨k, hk1, hk2, hk3, rfl⟩ := mem_pySlice a ip H (by omega) hH e he
    have := hp.2 k hk1 hk2 (by omega)
    simpa [keyAt] using this

theorem c_unfold (a : List Int) (lo : Int) (hi : Option Int) (hnn : ∀ h, hi = some h → 0 ≤ h)
    (r : Int → Int → Py Int) (ip : Int)
    (hc : (do let lo ← cConvLo lo; let hi ← cConvHi hi; r lo hi) = .ok ip) :
    0 ≤ lo ∧ ∃ h, (if h = -1 then (a.length : Int) else h) = hi.getD a.length ∧ r lo h = .ok ip := by
  cases hlo : cConvLo lo with
  | error e => rw [hlo] at hc; cases hc
  | ok lo' =>
    have hl : lo' = lo ∧ 0 ≤ lo := by
      simp only [cConvLo] at hlo; split at hlo
      · cases hlo
      · split at hlo
        · cases hlo
        · cases hlo; exact ⟨rfl, by omega⟩
    obtain ⟨this, hl0⟩ := hl
    subst this
    refine ⟨hl0, ?_⟩
    rw [hlo] at hc
    cases hh : cConvHi hi with
    | error e => simp only [bind, Except.bind, hh] at hc; cases hc
    | ok h =>
      simp only [bind, Except.bind, hh] at hc
      refine ⟨h, ?_, hc⟩
      cases hi with
      | none => simp [cConvHi] at hh; subst hh; simp
      | some h' =>
        have := hnn h' rfl
        simp only [cConvHi] at hh; split at hh
        · cases hh
        · cases hh; simp [show h ≠ -1 by omega]

theorem bisectDocPartitionNonnegHi_proven : BisectDocPartitionNonnegHi := by
  intro a x lo hi key hlen hs hnn
  have hH : 0 ≤ hi.getD a.length := by
    cases hi with
    | none => simp
    | some h => simpa using hnn h rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ip hr
    simp only [pyBisectLeft] at hr
    split at hr
    · cases hr
    · have := doc_of_loop key a _ _ (pyProbe_spec key a) (mono_left key a x hs) _ lo _ ip
        (by omega) hH hr
      exact ⟨fun e he => of_decide_eq_true (this.1 e he), fun e he => by
        have := of_decide_eq_false (this.2 e he); omega⟩
  · intro ip hr
    obtain ⟨hl0, h, hh, hr⟩ := c_unfold a lo hi hnn (fun lo hi => cInternalLeft a x lo hi key) ip hr
    simp only [cInternalLeft] at hr
    rw [hh] at hr
    have := doc_of_loop key a _ _ (cProbe_spec key a) (mono_left key a x hs) _ lo _ ip
      hl0 hH hr
    exact ⟨fun e he => of_decide_eq_true (this.1 e he), fun e he => by
      have := of_decide_eq_false (this.2 e he); omega⟩
  · intro ip hr
    simp only [pyBisectRight] at hr
    split at hr
    · cases hr
    · have := doc_of_loop key a _ _ (pyProbe_spec key a) (mono_right key a x hs) _ lo _ ip
        (by omega) hH hr
      refine ⟨fun e he => ?_, fun e he => ?_⟩
      · have h1 := this.1 e he
        simp only [Bool.not_eq_true'] at h1
        have := of_decide_eq_false h1; omega
      · have h1 := this.2 e he
        simp only [Bool.not_eq_false'] at h1
        exact of_decide_eq_true h1
  · intro ip hr
    obtain ⟨hl0, h, hh, hr⟩ := c_unfold a lo hi hnn (fun lo hi => cInternalRight a x lo hi key) ip hr
    simp only [cInternalRight] at hr
    rw [hh] at hr
    have := doc_of_loop key a _ _ (cProbe_spec key a) (mono_right key a x hs) _ lo _ ip
      hl0 hH hr
    refine ⟨fun e he => ?_, fun e he => ?_⟩
    · have h1 := this.1 e he
      simp only [Bool.not_eq_true'] at h1
      have := of_decide_eq_false h1; omega
    · have h1 := this.2 e he
      simp only [Bool.not_eq_false'] at h1
      exact of_decide_eq_true h1

/-! ### insort keeps the list sorted -/

theorem insertIdx_eq_take_drop {α : Type} (x : α) :
    ∀ (l : List α) (i : Nat), i ≤ l.length → l.insertIdx i x = l.take i ++ x :: l.drop i
  | l, 0, _ => by simp
  | [], _ + 1, h => by simp at h
  | y :: l, i + 1, h => by
    simp only [List.insertIdx_succ_cons, List.take_succ_cons, List.drop_succ_cons, List.cons_append]
    rw [insertIdx_eq_take_drop x l i (by simp at h; omega)]

theorem sorted_insertIdx (key : Option (Int → Int)) (a : List Int) (x : Int) (ip : Nat)
    (hs : SortedBy key a) (hip : ip ≤ a.length)
    (hl : ∀ k : Nat, k < ip → applyKey key (a.getD k 0) ≤ applyKey key x)
    (hr : ∀ k : Nat, ip ≤ k → k < a.length → applyKey key x ≤ applyKey key (a.getD k 0)) :
    SortedBy key (a.insertIdx ip x) := by
  rw [insertIdx_eq_take_drop x a ip hip]
  have hs' : SortedBy key (a.take ip ++ a.drop ip) := by rw [List.take_append_drop]; exact hs
  unfold SortedBy at *
  rw [List.pairwise_append] at hs' ⊢
  obtain ⟨h1, h2, h3⟩ := hs'
  have hT : ∀ u ∈ a.take ip, applyKey key u ≤ applyKey key x := by
    intro u hu
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hu
    simp only [List.length_take] at hi
    have := hl i (by omega)
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < a.length by omega)] using this
  have hD : ∀ v ∈ a.drop ip, applyKey key x ≤ applyKey key v := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hv
    simp only [List.length_drop] at hi
    have := hr (ip + i) (by omega) (by omega)
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show ip + i < a.length by omega)] using this
  refine ⟨h1, List.pairwise_cons.2 ⟨hD, h2⟩, ?_⟩
  intro u hu v hv
  rcases List.mem_cons.1 hv with rfl | hv
  · exact hT u hu
  · exact h3 u hu v hv

/-- `insort_left`/`insort_right` docstrings, Lib/bisect.py:4-8 and :57-61: for
`a` sorted by key and the default bounds, both twins leave a list that is a
permutation of `a` plus `x` and is still sorted by key. -/
def InsortKeepsSorted : Prop :=
  ∀ (a : List Int) (x : Int) (key : Option (Int → Int)),
    (a.length : Int) ≤ ssizeMax → SortedBy key a →
    (∃ l, pyInsortLeft a x 0 none key = .ok l ∧ cInsortLeft a x 0 none key = .ok l ∧
      SortedBy key l ∧ l.Perm (x :: a)) ∧
    (∃ l, pyInsortRight a x 0 none key = .ok l ∧ cInsortRight a x 0 none key = .ok l ∧
      SortedBy key l ∧ l.Perm (x :: a))

theorem insortKeepsSorted_proven : InsortKeepsSorted := by
  intro a x key hlen hs
  have ht := bisectTwinsAgreeNonnegLo_proven a x 0 none key hlen (by simp) (by decide) (by decide)
    (by simp)
  obtain ⟨ipL, hpL, -, hL0, hL1, hLl, hLr⟩ :=
    bisectLeftPartition_proven a (applyKey key x) 0 none key hlen hs (Int.le_refl _) (by simp) (by simp)
  obtain ⟨ipR, hpR, -, hR0, hR1, hRl, hRr⟩ :=
    bisectRightPartition_proven a (applyKey key x) 0 none key hlen hs (Int.le_refl _) (by simp) (by simp)
  simp only [Option.getD_none] at hL1 hLl hLr hR1 hRl hRr
  refine ⟨⟨a.insertIdx ipL.toNat x, ?_, ?_, ?_, ?_⟩, ⟨a.insertIdx ipR.toNat x, ?_, ?_, ?_, ?_⟩⟩
  · simp only [pyInsortLeft, hpL, bind, Except.bind]
    rw [listInsert_eq a ipL x hL0 (by omega)]
    simp [cListInsert, show min ipL a.length = ipL by omega]
  · rw [ht.2.2.1]
    simp only [pyInsortLeft, hpL, bind, Except.bind]
    rw [listInsert_eq a ipL x hL0 (by omega)]
    simp [cListInsert, show min ipL a.length = ipL by omega]
  · exact sorted_insertIdx key a x ipL.toNat hs (by omega)
      (fun k hk => Int.le_of_lt (hLl k (by omega) (by omega)))
      (fun k hk1 hk2 => hLr k (by omega) (by omega))
  · exact List.perm_insertIdx x a (by omega)
  · simp only [pyInsortRight, hpR, bind, Except.bind]
    rw [listInsert_eq a ipR x hR0 (by omega)]
    simp [cListInsert, show min ipR a.length = ipR by omega]
  · rw [ht.2.2.2]
    simp only [pyInsortRight, hpR, bind, Except.bind]
    rw [listInsert_eq a ipR x hR0 (by omega)]
    simp [cListInsert, show min ipR a.length = ipR by omega]
  · exact sorted_insertIdx key a x ipR.toNat hs (by omega)
      (fun k hk => hRl k (by omega) (by omega))
      (fun k hk1 hk2 => Int.le_of_lt (hRr k (by omega) (by omega)))
  · exact List.perm_insertIdx x a (by omega)

end PyLean.Accel
