import PyLean.CoreLibs.CalStat.StatBugs

/-!
`quantiles` (Lib/statistics.py:1176-1224) against the definitions it names in its comments
(statistics.py:1149-1170): Hyndman and Fan's sample quantiles 6 (`'exclusive'`, "R6",
`PERCENTILE.EXC`) and 7 (`'inclusive'`, "R7", `PERCENTILE.INC`), written over the rationals with
`Rat.floor`, independently of the integer `divmod` arithmetic the source uses.
-/

namespace PyLean.CoreLibs.CalStat

open PyLean

/-- Hyndman-Fan definition 7: with the order statistics `x[0] <= ... <= x[N-1]`, the position is
`h = (N - 1) * p` and `Q(p) = x[⌊h⌋] + (h - ⌊h⌋) * (x[⌊h⌋ + 1] - x[⌊h⌋])`. -/
def hf7 (x : List Rat) (p : Rat) : Rat :=
  let h := ((x.length : Rat) - 1) * p
  let k := h.floor
  pick x k.toNat + (h - k) * (pick x (k.toNat + 1) - pick x k.toNat)

/-- Hyndman-Fan definition 6: position `h = (N + 1) * p` counted from one, so the bracketing order
statistics are the `⌊h⌋`-th and the next. Below the first and above the last data point the source
keeps the first two, respectively the last two, and extends the line through them ("clamp to
1 .. ld-1", statistics.py:1218): the cut point then lies outside the data, which is the point of the
method ("a positive probability for values beyond the range of the data", :1153-1154). -/
def hf6 (x : List Rat) (p : Rat) : Rat :=
  let N := x.length
  let h := ((N : Rat) + 1) * p
  let k := max 1 (min h.floor ((N : Int) - 1))
  pick x (k.toNat - 1) + (h - k) * (pick x k.toNat - pick x (k.toNat - 1))

theorem floor_div_int (a n : Int) (hn : 0 < n) : ((a : Rat) / (n : Rat)).floor = a / n := by
  have hN : (0 : Rat) < (n : Rat) := Rat.intCast_pos.mpr hn
  apply Int.le_antisymm
  · have h1 : a < (a / n + 1) * n := Int.lt_ediv_add_one_mul_self a hn
    have : ((a : Rat) / (n : Rat)).floor < a / n + 1 := by
      rw [Rat.floor_lt_iff, Rat.div_lt_iff hN]
      have := Rat.intCast_lt_intCast.mpr h1
      simpa [Rat.intCast_mul] using this
    omega
  · rw [Rat.le_floor_iff]
    refine Rat.not_lt.mp ?_
    intro hc
    rw [Rat.div_lt_iff hN] at hc
    have := Rat.intCast_le_intCast.mpr (Int.ediv_mul_le a (by omega : n ≠ 0))
    rw [Rat.intCast_mul] at this
    exact Rat.not_le.mpr hc this

/-- The interpolation of the source equals the Hyndman-Fan form: `j` and `δ` are the quotient and
remainder of `i * m` by `n`, so `h = m * i / n` has integer part `j` and fraction `δ / n`. -/
theorem interp_hf (a b : Rat) (n δ : Int) (hn : 0 < n) :
    (a * ((n - δ : Int) : Rat) + b * (δ : Rat)) / (n : Rat) = a + ((δ : Rat) / (n : Rat)) * (b - a) := by
  have hN : (n : Rat) ≠ 0 := by
    have : (0 : Rat) < (n : Rat) := Rat.intCast_pos.mpr hn
    intro h; rw [h] at this; exact Rat.lt_irrefl this
  rw [Rat.intCast_sub]
  grind

theorem hf7_eq (vs : List Rat) (n i : Int) (h2 : 2 ≤ vs.length) (h1 : 1 ≤ i) (hin : i < n) :
    quantInclusive (vs.map .frac) n ((vs.length : Int) - 1) i =
      .ok (.frac (hf7 vs ((i : Rat) / (n : Rat)))) := by
  have hn : 0 < n := by omega
  obtain ⟨hj0, hidx, -, -, heq⟩ :=
    quantInc_eq vs n i ((vs.length : Int) - 1) ((i * ((vs.length : Int) - 1)) / n)
      ((i * ((vs.length : Int) - 1)) % n) h2 h1 hin rfl rfl rfl
  rw [heq, interp_hf _ _ _ _ hn]
  have hh : ((vs.length : Rat) - 1) * ((i : Rat) / (n : Rat)) =
      ((i * ((vs.length : Int) - 1) : Int) : Rat) / (n : Rat) := by
    rw [Rat.intCast_mul, Rat.intCast_sub]
    simp only [Rat.intCast_natCast, Rat.intCast_one]
    grind
  have hfl := floor_div_int (i * ((vs.length : Int) - 1)) n hn
  have hsplit := Int.emod_add_mul_ediv (i * ((vs.length : Int) - 1)) n
  simp only [hf7]
  rw [hh, hfl]
  congr 2
  have hN : (n : Rat) ≠ 0 := by
    have : (0 : Rat) < (n : Rat) := Rat.intCast_pos.mpr hn
    intro h; rw [h] at this; exact Rat.lt_irrefl this
  have : ((i * ((vs.length : Int) - 1) : Int) : Rat) =
      (((i * ((vs.length : Int) - 1)) % n : Int) : Rat) + (n : Rat) * (((i * ((vs.length : Int) - 1)) / n : Int) : Rat) := by
    rw [← Rat.intCast_mul, ← Rat.intCast_add, hsplit]
  rw [this]
  grind

theorem hf6_eq (vs : List Rat) (n i : Int) (h2 : 2 ≤ vs.length) (hn : 0 < n) :
    quantExclusive (vs.map .frac) n (vs.length : Int) ((vs.length : Int) + 1) i =
      .ok (.frac (hf6 vs ((i : Rat) / (n : Rat)))) := by
  let ld : Int := vs.length
  let j0 := (i * (ld + 1)) / n
  let j : Int := if j0 < 1 then 1 else if j0 > ld - 1 then ld - 1 else j0
  obtain ⟨hj1, hj2, heq⟩ :=
    quantExc_eq vs n i ld (ld + 1) j0 j (i * (ld + 1) - j * n) h2 hn rfl rfl rfl rfl rfl
  rw [heq, interp_hf _ _ _ _ hn]
  have hh : ((vs.length : Rat) + 1) * ((i : Rat) / (n : Rat)) =
      ((i * (ld + 1) : Int) : Rat) / (n : Rat) := by
    simp only [ld, Rat.intCast_mul, Rat.intCast_add, Rat.intCast_natCast, Rat.intCast_one]
    grind
  have hfl := floor_div_int (i * (ld + 1)) n hn
  have hk : max 1 (min (((i * (ld + 1) : Int) : Rat) / (n : Rat)).floor ((vs.length : Int) - 1)) = j := by
    rw [hfl]
    simp only [j, j0, ld]
    split
    · omega
    · split <;> omega
  simp only [hf6]
  rw [hh, hk]
  congr 2
  have hN : (n : Rat) ≠ 0 := by
    have : (0 : Rat) < (n : Rat) := Rat.intCast_pos.mpr hn
    intro h; rw [h] at this; exact Rat.lt_irrefl this
  rw [Rat.intCast_sub, Rat.intCast_mul j n]
  grind

/-- `quantiles` of `Fraction` data, both methods: the `n` check comes before the data is looked at;
then the cut points are exactly Hyndman and Fan's definition 7 (`'inclusive'`) or 6 (`'exclusive'`) of
`sorted(data)` at `p = i/n` for `i = 1, ..., n-1`, computed without rounding. Two or more points are
needed for this; one point is repeated `n - 1` times; an unknown method raises `ValueError`. `sorted`
is the mirror of `list.sort` (ListSort), whose result is a permutation of the data. -/
def QuantilesHF : Prop :=
  ∀ (qs : List Rat) (n : Int) (me : String),
    (n < 1 → quantiles (fracs qs) n me = .error (.named "StatisticsError" "n must be at least 1")) ∧
    (1 ≤ n → 2 ≤ qs.length → ∃ rs : List Rat,
      pySorted (fracs qs) = .ok (fracs rs) ∧ rs.length = qs.length ∧
      (me = "inclusive" → quantiles (fracs qs) n me =
        .ok ((rangeI 1 n).map (fun (i : Int) => (Val.frac (hf7 rs ((i : Rat) / (n : Rat)))).toN))) ∧
      (me = "exclusive" → quantiles (fracs qs) n me =
        .ok ((rangeI 1 n).map (fun (i : Int) => (Val.frac (hf6 rs ((i : Rat) / (n : Rat)))).toN))) ∧
      (me ≠ "inclusive" → me ≠ "exclusive" →
        quantiles (fracs qs) n me = .error (.valueError s!"~Unknown method: '{me}'")))

theorem mapM_ok_map {α β : Type} (f : α → Py β) (g : α → β) (l : List α) (h : ∀ a ∈ l, f a = .ok (g a)) :
    l.mapM f = .ok (l.map g) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.mapM_cons, List.map_cons]
    rw [h a (by simp), ih (fun x hx => h x (by simp [hx]))]
    rfl

theorem quantilesHF_proven : QuantilesHF := by
  intro qs n me
  refine ⟨?_, ?_⟩
  · intro h
    simp [quantiles, h, bind, Except.bind, throw, throwThe, MonadExcept.throw]
    rfl
  · intro h1 h2
    obtain ⟨rs, hr, hlen⟩ := pySorted_fracs qs
    have hl : 2 ≤ rs.length := by omega
    have hvals : (fracs rs).map (·.v) = rs.map .frac := fracs_vals rs
    have hflen : (fracs rs).length = rs.length := by simp [fracs]
    have hn1 : ¬ n < 1 := by omega
    have hlt : ¬ ((rs.length : Int) < 2) := by omega
    refine ⟨rs, hr, hlen, ?_, ?_, ?_⟩
    · rintro rfl
      have hm : (rangeI 1 n).mapM (fun i => Val.toN <$> quantInclusive (rs.map .frac) n ((rs.length : Int) - 1) i) =
          .ok ((rangeI 1 n).map (fun (i : Int) => (Val.frac (hf7 rs ((i : Rat) / (n : Rat)))).toN)) := by
        apply mapM_ok_map
        intro i hi
        obtain ⟨h3, h4⟩ := mem_rangeI hi
        rw [hf7_eq rs n i hl h3 h4]
        rfl
      simp only [quantiles, hn1, ite_false, bind, Except.bind, hr, hvals, hflen, hlt, ite_true, hm,
        pure, Except.pure]
    · rintro rfl
      have hm : (rangeI 1 n).mapM (fun i => Val.toN <$> quantExclusive (rs.map .frac) n (rs.length : Int)
          ((rs.length : Int) + 1) i) =
          .ok ((rangeI 1 n).map (fun (i : Int) => (Val.frac (hf6 rs ((i : Rat) / (n : Rat)))).toN)) := by
        apply mapM_ok_map
        intro i hi
        rw [hf6_eq rs n i hl (by omega)]
        rfl
      have hne : ("exclusive" = "inclusive") = False := by simp
      simp only [quantiles, hn1, ite_false, bind, Except.bind, hr, hvals, hflen, hlt, hne, ite_true, hm,
        pure, Except.pure]
    · intro hi he
      simp only [quantiles, hn1, ite_false, bind, Except.bind, hr, hvals, hflen, hlt, hi, he,
        pure, Except.pure, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw]

end PyLean.CoreLibs.CalStat
