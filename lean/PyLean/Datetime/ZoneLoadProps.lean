import PyLean.Datetime.ZoneLoad
import PyLean.Datetime.ZoneRuleProps

/-!
# Properties of loading a zone (`zoneinfo`, CPython 3.15.2)

The C and Python twins derive the same per-type data from the tuple `_common.load_data`
returns, layered as in `Accel`:
* the DST offsets (`dst()`): refuted for an `isdst` byte other than 0/1 (Python counts DST
  types with `sum(isdsts)`), refuted again with 0/1 flags for offsets far apart (C narrows
  `long` to `int` in `load_timedelta`), proven for 0/1 flags and offsets below `2**30`;
* the local transition times: refuted for a transition near the ends of `int64_t` (C wraps),
  proven when no sum leaves `int64_t`.
-/

namespace PyLean.Datetime.Zone

open PyLean PyLean.Datetime

/-- What `_common.load_data` returns on success: the transition and type lists have matching
lengths, every transition index names a type, and the values fit the `struct` formats they
were read with (`q`/`l`, `l`, `b`). -/
structure TzifShape (d : TzifData) : Prop where
  lenTrans : d.transIdx.length = d.transUtc.length
  lenTypes : d.isdst.length = d.utcoff.length
  lenAbbr : d.abbr.length = d.utcoff.length
  idx : ∀ i ∈ d.transIdx, 0 ≤ i ∧ i < d.utcoff.length
  utc : ∀ t ∈ d.transUtc, -2 ^ 63 ≤ t ∧ t < 2 ^ 63
  off : ∀ u ∈ d.utcoff, -2 ^ 31 ≤ u ∧ u < 2 ^ 31
  flag : ∀ x ∈ d.isdst, -128 ≤ x ∧ x < 128

/-! ### DST offsets -/

/-- The DST offset `dst()` reports for each type: Python's `_utcoff_to_dstoff`, and C's
`utcoff_to_dstoff` passed through `load_timedelta` (`build_ttinfo`, Modules/_zoneinfo.c:1150). -/
def dstOffsPy (d : TzifData) : List Int := utcoffToDstoffPy d.transIdx d.utcoff d.isdst
def dstOffsC (d : TzifData) : List Int :=
  (utcoffToDstoffC d.transIdx d.utcoff (d.isdst.map fun x => decide (x ≠ 0))).map loadTimedeltaC

/-- For every TZif tuple, both twins give every type the same DST offset. -/
def DstoffTwins : Prop := ∀ d : TzifData, TzifShape d → dstOffsC d = dstOffsPy d

/-- Types `+0` STD, `+1h` DST and `+2h` with `isdst` byte `0xff`: `sum(isdsts)` is 0, so the
Python loop stops before its first step and both DST types keep 0; C finds 1h and 2h. -/
theorem dstoffTwins_refuted : ¬ DstoffTwins := by
  intro h
  have := h ⟨[0, 1, 0, 2], [0, 1000, 2000, 3000], [0, 3600, 7200], [0, 1, -1],
    [[65], [66], [67]], none⟩ ⟨rfl, rfl, rfl, by decide, by decide, by decide, by decide⟩
  revert this
  decide

/-- With `isdst` 0 or 1, as RFC 9636 §3.2 requires, the twins still agree. -/
def DstoffTwinsFlags : Prop :=
  ∀ d : TzifData, TzifShape d → (∀ x ∈ d.isdst, x = 0 ∨ x = 1) → dstOffsC d = dstOffsPy d

/-- A DST type `-2**31` after a standard type `2**31 - 1`: the DST offset `-(2**32 - 1)` is a
`long` in C, and `load_timedelta` passes it to the `int` parameter of `Delta_FromDelta`, so C
reports one second where Python reports `-(2**32 - 1)` seconds. -/
theorem dstoffTwinsFlags_refuted : ¬ DstoffTwinsFlags := by
  intro h
  have := h ⟨[0, 1], [0, 1000], [2147483647, -2147483648], [0, 1], [[65], [66]], none⟩
    ⟨rfl, rfl, rfl, by decide, by decide, by decide, by decide⟩ (by decide)
  revert this
  decide

/-! #### The loops agree on truthiness -/

theorem getD_map_ne (D : List Int) (k : Nat) :
    (D.map fun x => decide (x ≠ 0)).getD k false = decide (D.getD k 0 ≠ 0) := by
  induction D generalizing k with
  | nil => simp
  | cons x xs ih =>
    cases k with
    | zero => simp
    | succ k => simpa using ih k

theorem dstStep_eq (P U D : List Int) (i : Nat) (os : List Int) (found : Nat) :
    dstStepPy P U D U.length i os found =
      ((dstStepC P U (D.map fun x => decide (x ≠ 0)) U.length i os found).1,
       ((dstStepC P U (D.map fun x => decide (x ≠ 0)) U.length i os found).2 : Int)) := by
  have hidx : (((P.getD i 0).toNat : Nat) : Int) < (U.length : Int) - 1 ↔
      (P.getD i 0).toNat < U.length - 1 := by omega
  unfold dstStepPy dstStepC
  simp only [hidx, getD_map_ne]
  generalize (P.getD i 0).toNat = idx
  generalize (P.getD (i - 1) 0).toNat = c1
  generalize (P.getD (i + 1) 0).toNat = c2
  by_cases h1 : D.getD idx 0 = 0 <;> by_cases h2 : os.getD idx 0 = 0 <;>
    by_cases h3 : D.getD c1 0 = 0 <;> by_cases h4 : D.getD c2 0 = 0 <;>
    simp only [h1, h2, h3, h4, ne_eq, not_true_eq_false, not_false_eq_true, decide_true,
      decide_false, Bool.not_true, Bool.not_false, Bool.true_or, Bool.false_or, ite_true,
      ite_false, Bool.false_eq_true, Bool.true_eq_false] <;>
    (repeat' split) <;> simp_all

/-- How many types are DST and already assigned. -/
def cnt : List Int → List Int → Nat
  | x :: xs, o :: os => (if x ≠ 0 ∧ o ≠ 0 then 1 else 0) + cnt xs os
  | _, _ => 0

/-- How many types are DST. -/
def nz : List Int → Nat
  | [] => 0
  | x :: xs => (if x ≠ 0 then 1 else 0) + nz xs

theorem cnt_le (D os : List Int) : cnt D os ≤ nz D := by
  induction D generalizing os with
  | nil => simp [cnt, nz]
  | cons x xs ih =>
    cases os with
    | nil => simp [cnt]
    | cons o os =>
      have := ih os
      simp only [cnt, nz]
      by_cases hx : x = 0 <;> by_cases ho : o = 0 <;> simp [hx, ho] <;> omega

theorem nz_le (D : List Int) : nz D ≤ D.length := by
  induction D with
  | nil => simp [nz]
  | cons x xs ih => simp only [nz, List.length_cons]; split <;> omega

theorem cnt_set (D os : List Int) (k : Nat) (v : Int) (hk : k < os.length)
    (hD : D.getD k 0 ≠ 0) (ho : os.getD k 0 = 0) (hv : v ≠ 0) :
    cnt D (os.set k v) = cnt D os + 1 := by
  induction D generalizing os k with
  | nil => simp at hD
  | cons x xs ih =>
    cases os with
    | nil => simp at hk
    | cons o os =>
      cases k with
      | zero =>
        simp at hD ho
        simp [cnt, hD, ho, hv]
        omega
      | succ k =>
        simp only [List.set_cons_succ, cnt]
        simp at hk hD ho
        rw [ih os k hk hD ho]
        omega

/-- Every DST type is assigned. -/
def AllA (D os : List Int) : Prop := ∀ k, D.getD k 0 ≠ 0 → os.getD k 0 ≠ 0

theorem cnt_eq_all (D os : List Int) (hl : os.length = D.length) (h : cnt D os = nz D) : AllA D os := by
  induction D generalizing os with
  | nil => intro k hk; simp at hk
  | cons x xs ih =>
    cases os with
    | nil => simp at hl
    | cons o os =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      have hle := cnt_le xs os
      simp only [cnt, nz] at h
      intro k hk
      cases k with
      | zero =>
        simp at hk ⊢
        by_cases ho : o = 0
        · simp [hk, ho] at h
          omega
        · exact ho
      | succ k =>
        simp at hk ⊢
        have : cnt xs os = nz xs := by
          by_cases hx : x = 0 <;> by_cases ho : o = 0 <;> simp [hx, ho] at h <;> omega
        exact ih os hl this k hk

theorem sum_eq_nz (D : List Int) (h : ∀ x ∈ D, x = 0 ∨ x = 1) : D.sum = nz D := by
  induction D with
  | nil => simp [nz]
  | cons x xs ih =>
    simp only [List.sum_cons, nz]
    rw [ih (fun y hy => h y (by simp [hy]))]
    rcases h x (by simp) with rfl | rfl <;> simp

theorem dstStepC_cases (P U : List Int) (B : List Bool) (n i : Nat) (os : List Int) (found : Nat) :
    dstStepC P U B n i os found = (os, found) ∨
      ∃ k v, B.getD k false = true ∧ os.getD k 0 = 0 ∧ v ≠ 0 ∧
        (∃ a b, v = U.getD a 0 - U.getD b 0) ∧
        dstStepC P U B n i os found = (os.set k v, found + 1) := by
  unfold dstStepC
  simp only
  by_cases hb : B.getD (P.getD i 0).toNat false = true
  · by_cases ho : os.getD (P.getD i 0).toNat 0 = 0
    · simp only [hb, ho, Bool.not_true, Bool.false_or, ne_eq, not_true_eq_false, decide_false,
        Bool.false_eq_true, ite_false]
      (repeat' split) <;>
        first
        | exact .inl rfl
        | exact .inr ⟨_, _, hb, ho, by assumption, ⟨_, _, rfl⟩, rfl⟩
        | (exfalso; simp_all)
    · left
      simp only [hb, ho, Bool.not_true, Bool.false_or, ne_eq, not_false_eq_true, decide_true,
        ite_true]
  · left
    simp only [Bool.not_eq_true] at hb
    simp only [hb, Bool.not_false, Bool.true_or, ite_true]

theorem getD_map_true (D : List Int) (k : Nat)
    (h : (D.map fun x => decide (x ≠ 0)).getD k false = true) : D.getD k 0 ≠ 0 := by
  rw [getD_map_ne] at h
  simpa using h

theorem getD_true_lt (B : List Bool) (k : Nat) (h : B.getD k false = true) : k < B.length := by
  induction B generalizing k with
  | nil => simp at h
  | cons b bs ih =>
    cases k with
    | zero => simp
    | succ k =>
      simp only [List.getD_cons_succ] at h
      simpa using ih k h

theorem dstStepC_noop (P U D : List Int) (n i : Nat) (os : List Int) (found : Nat) (h : AllA D os) :
    dstStepC P U (D.map fun x => decide (x ≠ 0)) n i os found = (os, found) := by
  rcases dstStepC_cases P U _ n i os found with e | ⟨k, v, hk, ho, _, _, _⟩
  · exact e
  · exact absurd ho (h k (getD_map_true D k hk))

theorem dstLoopC_noop (P U D : List Int) (n c : Nat) :
    ∀ fuel i os found, AllA D os →
      dstLoopC P U (D.map fun x => decide (x ≠ 0)) n c fuel i os found = (os, found) := by
  intro fuel
  induction fuel with
  | zero => intro i os found _; rfl
  | succ fuel ih =>
    intro i os found h
    unfold dstLoopC
    split
    · rfl
    · rw [dstStepC_noop P U D n i os found h]
      exact ih (i + 1) os found h

theorem loops_agree (P U D : List Int) (hlen : D.length = U.length)
    (h01 : ∀ x ∈ D, x = 0 ∨ x = 1) :
    ∀ fuel i os found, os.length = U.length → cnt D os = found →
      let rp := dstLoopPy P U D U.length D.sum fuel i os (found : Int)
      let rc := dstLoopC P U (D.map fun x => decide (x ≠ 0)) U.length U.length fuel i os found
      rc.1 = rp.1 ∧ (rp.2 = true → AllA D rp.1) ∧ (rc.2 = U.length → AllA D rc.1) ∧
        rc.2 ≤ U.length ∧ rc.1.length = U.length := by
  have hsum := sum_eq_nz D h01
  have hnz := nz_le D
  intro fuel
  induction fuel with
  | zero =>
    intro i os found hl hc
    have := cnt_le D os
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [dstLoopPy, dstLoopC]
    · simp only [dstLoopPy, Bool.false_eq_true, false_implies]
    · simp only [dstLoopC]
      exact fun hf => cnt_eq_all D os (by omega) (by omega)
    · simp only [dstLoopC]
      omega
    · simp only [dstLoopC]
      exact hl
  | succ fuel ih =>
    intro i os found hl hc
    have hall : D.sum = found → AllA D os := fun he =>
      cnt_eq_all D os (by omega) (by omega)
    simp only [dstLoopPy, dstLoopC]
    by_cases hb : D.sum = (found : Int)
    · have ha := hall hb
      simp only [hb, ite_true]
      have hrc : dstLoopC P U (D.map fun x => decide (x ≠ 0)) U.length U.length (fuel + 1) i os found
          = (os, found) := by
        simp only [dstLoopC]
        split
        · rfl
        · rw [dstStepC_noop P U D _ i os found ha, dstLoopC_noop P U D _ _ fuel (i + 1) os found ha]
      simp only [dstLoopC] at hrc
      rw [hrc]
      have := cnt_le D os
      exact ⟨rfl, fun _ => ha, fun _ => ha, by omega, hl⟩
    · have hne : ¬ (U.length = found) := by
        intro he
        have := cnt_le D os
        omega
      simp only [hb, ite_false, hne]
      rw [dstStep_eq P U D i os found]
      simp only
      rcases dstStepC_cases P U (D.map fun x => decide (x ≠ 0)) U.length i os found with e | ⟨k, v, hk, ho, hv, -, e⟩
      · rw [e]
        exact ih (i + 1) os found hl hc
      · rw [e]
        have hkl : k < os.length := by
          have := getD_true_lt _ k hk
          simp at this
          omega
        have := ih (i + 1) (os.set k v) (found + 1) (by simp [hl])
          (by rw [cnt_set D os k v hkl (getD_map_true D k hk) ho hv]; omega)
        simpa using this

theorem fill_noop (D os : List Int) (hl : os.length = D.length) (h : AllA D os) :
    fill3600 D os = os := by
  unfold fill3600
  induction D generalizing os with
  | nil => cases os <;> simp_all
  | cons x xs ih =>
    cases os with
    | nil => simp
    | cons o os =>
      simp only [List.zip_cons_cons, List.map_cons]
      have h0 := h 0
      simp at h0
      simp at hl
      rw [ih os hl (fun k hk => by simpa using h (k + 1) (by simpa using hk))]
      by_cases hx : x = 0 <;> by_cases ho : o = 0 <;> simp_all

theorem fillC_eq (D os : List Int) :
    (os.zip (D.map fun x => decide (x ≠ 0))).map (fun (o, d) => if d = true ∧ o = 0 then 3600 else o) =
      fill3600 D os := by
  unfold fill3600
  induction os generalizing D with
  | nil => simp
  | cons o os ih =>
    cases D with
    | nil => simp
    | cons x xs =>
      simp only [List.map_cons, List.zip_cons_cons]
      rw [ih xs]
      by_cases hx : x = 0 <;> by_cases ho : o = 0 <;> simp [hx, ho]

theorem utcoffToDstoff_flags (P U D : List Int) (hlen : D.length = U.length)
    (h01 : ∀ x ∈ D, x = 0 ∨ x = 1) :
    utcoffToDstoffC P U (D.map fun x => decide (x ≠ 0)) = utcoffToDstoffPy P U D := by
  have := loops_agree P U D hlen h01 (P.length - 1) 1 (List.replicate U.length 0) 0 (by simp)
    (by
      induction D generalizing U with
      | nil => cases U <;> rfl
      | cons x xs ih =>
        cases U with
        | nil => rfl
        | cons u us =>
          simp only [List.length_cons, List.replicate_succ, cnt]
          simp at hlen
          rw [ih us hlen (fun y hy => h01 y (by simp [hy]))]
          simp)
  simp only at this
  obtain ⟨heq, hbr, hfull, hle, hlc⟩ := this
  unfold utcoffToDstoffC utcoffToDstoffPy
  simp only [hlen]
  generalize hrp : dstLoopPy P U D U.length D.sum (P.length - 1) 1 (List.replicate U.length 0) (0 : Nat) = rp at *
  generalize hrc : dstLoopC P U (D.map fun x => decide (x ≠ 0)) U.length U.length (P.length - 1) 1
    (List.replicate U.length 0) 0 = rc at *
  obtain ⟨osp, br⟩ := rp
  obtain ⟨osc, fc⟩ := rc
  simp only at heq hbr hfull hle hlc ⊢
  subst heq
  rw [fillC_eq]
  by_cases hf : fc < U.length
  · simp only [hf, ite_true]
    cases br
    · rfl
    · simp only [ite_true]
      exact fill_noop D osc (by omega) (hbr rfl)
  · simp only [hf, ite_false]
    have hfa : fc = U.length := by omega
    cases br
    · simp only [Bool.false_eq_true, ite_false]
      exact (fill_noop D osc (by omega) (hfull hfa)).symm
    · rfl

/-! #### Every C offset fits an `int` when the type offsets do -/

theorem getD_prop (U : List Int) (Q : Int → Prop) (h : ∀ u ∈ U, Q u) (h0 : Q 0) (a : Nat) :
    Q (U.getD a 0) := by
  induction U generalizing a with
  | nil => simpa using h0
  | cons u us ih =>
    cases a with
    | zero => simpa using h u (by simp)
    | succ a =>
      simp only [List.getD_cons_succ]
      exact ih (fun x hx => h x (by simp [hx])) a

def Fits (x : Int) : Prop := -2147483648 ≤ x ∧ x < 2147483648

theorem dstLoopC_fits (P U : List Int) (B : List Bool) (n c : Nat)
    (hU : ∀ u ∈ U, -2 ^ 30 ≤ u ∧ u < 2 ^ 30) :
    ∀ fuel i os found, (∀ x ∈ os, Fits x) →
      ∀ x ∈ (dstLoopC P U B n c fuel i os found).1, Fits x := by
  have hg : ∀ a, -2 ^ 30 ≤ U.getD a 0 ∧ U.getD a 0 < 2 ^ 30 :=
    getD_prop U _ hU (by decide)
  intro fuel
  induction fuel with
  | zero => intro i os found h; simpa [dstLoopC] using h
  | succ fuel ih =>
    intro i os found h
    simp only [dstLoopC]
    split
    · exact h
    · rcases dstStepC_cases P U B n i os found with e | ⟨k, v, -, -, -, ⟨a, b, hv⟩, e⟩
      · rw [e]; exact ih (i + 1) os found h
      · rw [e]
        apply ih (i + 1) _ _
        intro x hx
        rcases List.mem_or_eq_of_mem_set hx with hx | hx
        · exact h x hx
        · have := hg a; have := hg b; unfold Fits; omega

theorem utcoffToDstoffC_fits (P U : List Int) (B : List Bool)
    (hU : ∀ u ∈ U, -2 ^ 30 ≤ u ∧ u < 2 ^ 30) : ∀ x ∈ utcoffToDstoffC P U B, Fits x := by
  have hl := dstLoopC_fits P U B U.length U.length hU (P.length - 1) 1 (List.replicate U.length 0) 0
    (fun x hx => by simp [List.mem_replicate] at hx; unfold Fits; omega)
  unfold utcoffToDstoffC
  simp only
  split
  · intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨⟨o, d⟩, hm, rfl⟩ := hx
    have := hl o (List.of_mem_zip hm).1
    split
    · unfold Fits; omega
    · exact this
  · exact hl

/-- With `isdst` 0 or 1 and type offsets below `2**30` (the RFC 9636 §3.2 range is
`-89999..93599`), the twins give every type the same DST offset. -/
def DstoffTwinsNarrow : Prop :=
  ∀ d : TzifData, TzifShape d → (∀ x ∈ d.isdst, x = 0 ∨ x = 1) →
    (∀ u ∈ d.utcoff, -2 ^ 30 ≤ u ∧ u < 2 ^ 30) → dstOffsC d = dstOffsPy d

theorem dstoffTwinsNarrow_proven : DstoffTwinsNarrow := by
  intro d hs h01 hU
  unfold dstOffsC dstOffsPy
  rw [← utcoffToDstoff_flags d.transIdx d.utcoff d.isdst hs.lenTypes h01]
  have hf := utcoffToDstoffC_fits d.transIdx d.utcoff (d.isdst.map fun x => decide (x ≠ 0)) hU
  conv => rhs; rw [← List.map_id (utcoffToDstoffC _ _ _)]
  apply List.map_congr_left
  intro x hx
  have := hf x hx
  unfold Fits at this
  exact wrap32_id x this.1 this.2

/-! ### Local transition times -/

/-- Both twins compute the same wall-clock transition times. -/
def TsToLocalTwins : Prop :=
  ∀ d : TzifData, TzifShape d →
    tsToLocal wrap64 d.transIdx d.transUtc d.utcoff = tsToLocal id d.transIdx d.transUtc d.utcoff

/-- One transition at `2**63 - 1` into a `+1h` type: C's `int64_t` sum wraps to a negative
time, so every later instant reads as after the last transition. -/
theorem tsToLocalTwins_refuted : ¬ TsToLocalTwins := by
  intro h
  have := h ⟨[1], [9223372036854775807], [0, 3600], [0, 0], [[65], [66]], none⟩
    ⟨rfl, rfl, rfl, by decide, by decide, by decide, by decide⟩
  revert this
  decide

theorem getD_or (U : List Int) (a : Nat) : U.getD a 0 ∈ U ∨ U.getD a 0 = 0 := by
  induction U generalizing a with
  | nil => simp
  | cons u us ih =>
    cases a with
    | zero => simp
    | succ a =>
      simp only [List.getD_cons_succ]
      rcases ih a with h | h
      · exact .inl (List.mem_cons_of_mem _ h)
      · exact .inr h

/-- When no transition time plus type offset leaves `int64_t`, they agree. -/
def TsToLocalTwinsNarrow : Prop :=
  ∀ d : TzifData, TzifShape d →
    (∀ t ∈ d.transUtc, ∀ u ∈ d.utcoff, -2 ^ 63 ≤ t + u ∧ t + u < 2 ^ 63) →
    tsToLocal wrap64 d.transIdx d.transUtc d.utcoff = tsToLocal id d.transIdx d.transUtc d.utcoff

theorem tsToLocalTwinsNarrow_proven : TsToLocalTwinsNarrow := by
  intro d hs hsum
  have hfit : ∀ t ∈ d.transUtc, ∀ a : Nat,
      wrap64 (t + d.utcoff.getD a 0) = t + d.utcoff.getD a 0 := by
    intro t ht a
    rcases getD_or d.utcoff a with hm | h0
    · have := hsum t ht _ hm
      exact wrap64_id _ (by omega) (by omega)
    · rw [h0]
      have := hs.utc t ht
      exact wrap64_id _ (by omega) (by omega)
  unfold tsToLocal
  split
  · rfl
  · simp only [id]
    have hp : ∀ p ∈ d.transUtc.zip ((List.range d.transUtc.length).map fun i =>
        if i = 0 then
          (if d.utcoff.length > 1 then
            (if d.utcoff.getD (d.transIdx.getD 0 0).toNat 0 > d.utcoff.getD 0 0 then
              (d.utcoff.getD (d.transIdx.getD 0 0).toNat 0, d.utcoff.getD 0 0)
            else (d.utcoff.getD 0 0, d.utcoff.getD (d.transIdx.getD 0 0).toNat 0))
          else (d.utcoff.getD 0 0, d.utcoff.getD 0 0))
        else
          (if d.utcoff.getD (d.transIdx.getD i 0).toNat 0 > d.utcoff.getD (d.transIdx.getD (i - 1) 0).toNat 0 then
            (d.utcoff.getD (d.transIdx.getD i 0).toNat 0, d.utcoff.getD (d.transIdx.getD (i - 1) 0).toNat 0)
          else (d.utcoff.getD (d.transIdx.getD (i - 1) 0).toNat 0, d.utcoff.getD (d.transIdx.getD i 0).toNat 0))),
        p.1 ∈ d.transUtc ∧ (∃ a, p.2.1 = d.utcoff.getD a 0) ∧ (∃ a, p.2.2 = d.utcoff.getD a 0) := by
      intro p hp
      refine ⟨(List.of_mem_zip hp).1, ?_⟩
      have h2 := (List.of_mem_zip hp).2
      simp only [List.mem_map, List.mem_range] at h2
      obtain ⟨i, -, hi⟩ := h2
      rw [← hi]
      split
      · split
        · split <;> exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
        · exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
      · split <;> exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
    congr 1
    · apply List.map_congr_left
      intro p hm
      obtain ⟨ht, ⟨a, ha⟩, -⟩ := hp p hm
      rw [ha]; exact hfit _ ht a
    · apply List.map_congr_left
      intro p hm
      obtain ⟨ht, -, ⟨a, ha⟩⟩ := hp p hm
      rw [ha]; exact hfit _ ht a

end PyLean.Datetime.Zone
