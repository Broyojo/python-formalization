import PyLean.TextLibs.PlistWriteErr
import PyLean.Binary64.Props2
import PyLean.Datetime.DeltaProps

/-! Which datetimes survive the binary format: every whole-second one, naive or aware. -/

namespace PyLean.TextLibs.Plist

open PyLean PyLean.TextLibs PyLean.Binary64 PyLean.Binary64.F64

theorem mkRat_whole (N : Int) : mkRat (N * 1000000) 1000000 = (N : Rat) := by
  have := Rat.mkRat_mul_right (n := N) (d := 1) (a := 1000000) (by decide)
  simp only [Nat.one_mul, Rat.mkRat_one] at this
  exact this

theorem isInf_of_finite {x : F64} (h : x.isFinite = true) : x.isInf = false := by
  simp only [F64.isInf, F64.isFinite, bne_iff_ne, ne_eq] at h ⊢
  simp [h]

theorem accum_whole (N : Int) (hN : N.natAbs < 2 ^ 53) :
    accumSeconds (F64.ofInt N) = .ok (0 + N * 1000000, F64.zero false) := by
  obtain ⟨hfin, hval⟩ := ofInt_small hN
  have hnan : (F64.ofInt N).isNaN = false := ofRat_isNaN _
  have hinf := isInf_of_finite hfin
  have htrunc : F64.trunc (F64.ofInt N) = F64.ofInt N := by
    unfold F64.trunc
    rw [hnan, hfin]
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_true, Bool.false_or]
    split
    · rfl
    · rename_i hz
      rw [truncInt_of_int hval]
      unfold F64.ofIntS
      rw [if_neg]
      intro h0
      subst h0
      exact hz (by decide +kernel)
  have hsub : F64.eq (F64.sub (F64.ofInt N) (F64.ofInt N)) (F64.zero false) = true := by
    unfold F64.sub F64.add
    have hninf : (F64.ofInt N).neg.isInf = false := isInf_of_finite (by rw [F64.neg_isFinite]; exact hfin)
    rw [F64.neg_isNaN, hnan, hinf, hninf]
    simp only [Bool.or_self, Bool.false_eq_true, ↓reduceIte, toRat_neg, hval]
    rw [if_pos]
    · generalize ((F64.ofInt N).sign && (F64.ofInt N).neg.sign) = s
      cases s <;> decide +kernel
    · exact Rat.add_neg_cancel _
  have hlong : longFromDouble (F64.ofInt N) = .ok N := by
    simp [longFromDouble, hnan, hinf, truncInt_of_int hval]
  unfold accumSeconds modf
  simp only [hnan, hinf, Bool.false_eq_true, ↓reduceIte]
  rw [htrunc, hlong]
  simp only [bind, Except.bind, hsub, ↓reduceIte, pure, Except.pure]

theorem delta_whole (N : Int) (hN : N.natAbs < 2 ^ 53) :
    deltaFromSeconds (F64.ofInt N) = Datetime.usToDeltaC (0 + N * 1000000) := by
  unfold deltaFromSeconds
  rw [accum_whole N hN]
  simp only [bind, Except.bind]
  rw [if_neg (by decide +kernel)]

theorem epoch_whole (x : Int) (h1 : dtMinUs ≤ x) (h2 : x ≤ dtMaxUs) :
    (Datetime.usToDeltaC x >>= epochPlus) = .ok x := by
  rw [Datetime.usToDeltaC_eq]
  simp only [dtMinUs, dtMaxUs] at h1 h2
  rw [if_pos (show Datetime.fitsCInt (x / 86400000000) by simp [Datetime.fitsCInt] <;> omega)]
  unfold Datetime.mkDeltaN
  rw [if_pos (show -Datetime.MAX_DELTA_DAYS ≤ x / 86400000000 ∧ x / 86400000000 ≤ Datetime.MAX_DELTA_DAYS by
    unfold Datetime.MAX_DELTA_DAYS; omega)]
  have e1 : epochOrdinal = 730486 := rfl
  have e2 : maxOrdinal = 3652059 := rfl
  simp only [bind, Except.bind, epochPlus, Datetime.Delta.toUs]
  repeat' split
  all_goals first | (exfalso; omega) | (congr 1; omega)

/-- Every whole-second datetime survives the binary format: the float `_write_object` writes for
it (:808-815), read back by `_read_object` (`timedelta(seconds=f)` added to 2001-01-01, :587-595),
is the same instant: the naive wall time with `aware_datetime=False`, and the UTC time with
`aware_datetime=True` for an aware datetime of a whole-second fixed offset (:809-812). The
microseconds of other datetimes are not kept in general (`BinaryDateRoundTrip` is refuted at
`datetime.max`). -/
def DateWholeSeconds : Prop :=
  ∀ (cfg : WCfg) (N : Int),
    (cfg.awareDatetime = false → dtMinUs ≤ N * 1000000 → N * 1000000 ≤ dtMaxUs →
      ∃ f, dateSeconds cfg (N * 1000000) none = .ok f ∧
        (deltaFromSeconds (F64.ofBits f) >>= epochPlus) = .ok (N * 1000000)) ∧
    (∀ M : Int, cfg.awareDatetime = true → dtMinUs ≤ (N - M) * 1000000 → (N - M) * 1000000 ≤ dtMaxUs →
      ∃ f, dateSeconds cfg (N * 1000000) (some (M * 1000000)) = .ok f ∧
        (deltaFromSeconds (F64.ofBits f) >>= epochPlus) = .ok ((N - M) * 1000000))

theorem dateWholeSeconds_proven : DateWholeSeconds := by
  intro cfg N
  have key : ∀ K : Int, dtMinUs ≤ K * 1000000 → K * 1000000 ≤ dtMaxUs →
      (deltaFromSeconds (F64.ofBits (F64.ofRat (mkRat (K * 1000000) 1000000)).bits) >>= epochPlus) =
        .ok (K * 1000000) := by
    intro K h1 h2
    have hK : K.natAbs < 2 ^ 53 := by simp only [dtMinUs, dtMaxUs] at h1 h2; omega
    rw [mkRat_whole, F64.ofBits_bits]
    show (deltaFromSeconds (F64.ofInt K) >>= epochPlus) = _
    rw [delta_whole K hK, Int.zero_add]
    exact epoch_whole _ h1 h2
  refine ⟨fun ha h1 h2 => ?_, fun M ha h1 h2 => ?_⟩
  · refine ⟨(F64.ofRat (mkRat (N * 1000000) 1000000)).bits, by simp [dateSeconds, ha, pure, Except.pure, bind, Except.bind], key N h1 h2⟩
  · by_cases hM : M * 1000000 = 0
    · have hM0 : M = 0 := by omega
      subst hM0
      refine ⟨(F64.ofRat (mkRat (N * 1000000) 1000000)).bits, by simp [dateSeconds, ha, pure, Except.pure, bind, Except.bind], ?_⟩
      simpa using key N (by simpa using h1) (by simpa using h2)
    · have e : N * 1000000 - M * 1000000 = (N - M) * 1000000 := by rw [Int.sub_mul]
      refine ⟨_, ?_, key (N - M) h1 h2⟩
      simp only [dateSeconds, ha, ↓reduceIte, hM, bind, Except.bind, pure, Except.pure, e]
      rw [if_neg (by omega)]

end PyLean.TextLibs.Plist
