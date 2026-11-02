import PyLean.MathInt.FltNext
import PyLean.MathInt.FltSum

/-!
# Property: `hypot` and `dist`

`math_hypot_impl` and `math_dist_impl` (Modules/mathmodule.c:1965-2105): `dist(p, q)` is
`hypot` of the coordinate differences, as the docs' "roughly equivalent" code says; both
check their inputs in order; and the special values of `vector_norm` (:1904-1912) follow
C99 Annex F: an infinite coordinate gives `inf` even next to a NaN ("hypot(float('nan'),
float('inf'))" is the documentation's example of a NaN argument without a NaN result).
-/

namespace PyLean.MathInt

open PyLean PyLean.Binary64 PyLean.Binary64.F64

/-- The running maximum of `math_hypot_impl` and `math_dist_impl`. -/
def runMax (xs : List F64) : F64 := xs.foldl (fun m x => if F64.lt m x then x else m) c0

theorem hypotStep_float (acc : List F64) (m : F64) (fn : Bool) (x : F64) :
    hypotStep (acc, m, fn) (.float x) =
      .ok (acc ++ [F64.abs x], if F64.lt m (F64.abs x) then F64.abs x else m, fn || (F64.abs x).isNaN) :=
  rfl

theorem hypot_fold (xs : List F64) : ∀ (acc : List F64) (m : F64) (fn : Bool),
    List.foldlM hypotStep (acc, m, fn) (xs.map .float) =
      .ok (acc ++ xs.map F64.abs, (xs.map F64.abs).foldl (fun m x => if F64.lt m x then x else m) m,
        fn || (xs.map F64.abs).any (·.isNaN)) := by
  induction xs with
  | nil => intro acc m fn; simp [pure, Except.pure]
  | cons x xs ih =>
    intro acc m fn
    rw [List.map_cons, List.foldlM_cons, hypotStep_float]
    simp only [bind, Except.bind]
    rw [ih]
    simp [List.foldl_cons, Bool.or_assoc]

/-- `hypot(*xs)` on floats is `vector_norm` of the absolute values. -/
theorem hypot_floats (xs : List F64) :
    math_hypot (xs.map .float) =
      .ok (vector_norm 1 (xs.map F64.abs) (runMax (xs.map F64.abs)) ((xs.map F64.abs).any (·.isNaN))) := by
  unfold math_hypot runMax
  rw [hypot_fold]
  simp [bind, Except.bind, pure, Except.pure]

theorem distStep_float (acc : List F64) (m : F64) (fn : Bool) (p q : F64) :
    distStep (acc, m, fn) (.float p, .float q) =
      .ok (acc ++ [F64.abs (F64.sub p q)],
        if F64.lt m (F64.abs (F64.sub p q)) then F64.abs (F64.sub p q) else m,
        fn || (F64.abs (F64.sub p q)).isNaN) := rfl

theorem dist_fold (ps : List F64) : ∀ (qs acc : List F64) (m : F64) (fn : Bool),
    List.foldlM distStep (acc, m, fn) ((ps.map .float).zip (qs.map .float)) =
      .ok (acc ++ (ps.zip qs).map (fun pq => F64.abs (F64.sub pq.1 pq.2)),
        ((ps.zip qs).map (fun pq => F64.abs (F64.sub pq.1 pq.2))).foldl
          (fun m x => if F64.lt m x then x else m) m,
        fn || ((ps.zip qs).map (fun pq => F64.abs (F64.sub pq.1 pq.2))).any (·.isNaN)) := by
  induction ps with
  | nil => intro qs acc m fn; simp [pure, Except.pure]
  | cons p ps ih =>
    intro qs acc m fn
    cases qs with
    | nil => simp [pure, Except.pure]
    | cons q qs =>
      rw [List.map_cons, List.map_cons, List.zip_cons_cons, List.foldlM_cons, distStep_float]
      simp only [bind, Except.bind]
      rw [ih]
      simp [List.foldl_cons, Bool.or_assoc]

/-- `dist(p, q)` on float tuples of the same length is `vector_norm` of the absolute
differences. -/
theorem dist_floats (ps qs : List F64) (hl : ps.length = qs.length) :
    math_dist ⟨ps.map .float, none⟩ ⟨qs.map .float, none⟩ =
      .ok (let ds := (ps.zip qs).map (fun pq => F64.abs (F64.sub pq.1 pq.2))
           vector_norm 1 ds (runMax ds) (ds.any (·.isNaN))) := by
  unfold math_dist runMax
  simp only [It.finish, bind, Except.bind, List.length_map, hl, bne_self_eq_false,
    Bool.false_eq_true, ↓reduceIte]
  rw [dist_fold]
  simp [pure, Except.pure]

/-- `dist` and `hypot`.

* `dist(p, q)` on two float tuples of the same length is `hypot(*(px - qx for px, qx in
  zip(p, q)))` (Doc/library/math.rst, "dist": "Roughly equivalent to
  `sqrt(sum((px - qx) ** 2.0 for px, qx in zip(p, q, strict=True)))`", and "hypot":
  `sqrt(sum(x**2 for x in coordinates))`), for every `vector_norm`;
* points of different dimensions raise `ValueError("both points must have the same number of
  dimensions")`, after both are made tuples (an iteration error of `p`, then of `q`, first);
* `hypot()` is `0.0`, `hypot(x)` is `abs(x)` (a NaN for a NaN); an infinite coordinate makes `hypot` `inf`,
  whatever the others are, NaNs included; otherwise a NaN coordinate makes it a NaN. -/
def HypotDist : Prop :=
  (∀ ps qs : List F64, ps.length = qs.length →
    math_dist ⟨ps.map .float, none⟩ ⟨qs.map .float, none⟩ =
      math_hypot ((ps.zip qs).map (fun pq => .float (F64.sub pq.1 pq.2)))) ∧
  (∀ p q : It, p.err = none → q.err = none → p.items.length ≠ q.items.length →
    math_dist p q = .error (.valueError "both points must have the same number of dimensions")) ∧
  (∀ p q : It, ∀ e, p.err = some e → math_dist p q = .error e) ∧
  (∀ p q : It, ∀ e, p.err = none → q.err = some e → math_dist p q = .error e) ∧
  math_hypot [] = .ok c0 ∧
  (∀ x : F64, x.isNaN = false → math_hypot [.float x] = .ok (F64.abs x)) ∧
  (∀ xs : List F64, xs.any (·.isInf) = true → math_hypot (xs.map .float) = .ok (F64.inf false)) ∧
  (∀ xs : List F64, xs.any (·.isInf) = false → xs.any (·.isNaN) = true →
    ∃ v, math_hypot (xs.map .float) = .ok v ∧ v.isNaN = true)

theorem runMax_inf (xs : List F64) (h : (xs.map F64.abs).any (·.isInf) = true) :
    runMax (xs.map F64.abs) = F64.inf false := by
  unfold runMax
  suffices ∀ (ys : List F64) (m : F64), (∀ y ∈ ys, y.sign = false) → m.sign = false →
      m.isNaN = false → (ys.any (·.isInf) = true ∨ m = F64.inf false) →
      ys.foldl (fun m x => if F64.lt m x then x else m) m = F64.inf false by
    apply this _ c0
    · intro y hy; simp at hy; obtain ⟨a, _, rfl⟩ := hy; exact (abs_fields a).1
    · decide +kernel
    · decide +kernel
    · left; exact h
  intro ys
  induction ys with
  | nil => intro m _ _ _ h; simp at h; exact h
  | cons y ys ih =>
    intro m hs hms hmn h
    simp only [List.foldl_cons]
    apply ih
    · intro z hz; exact hs z (List.mem_cons_of_mem _ hz)
    · split
      · exact hs y (List.mem_cons_self ..)
      · exact hms
    · split
      · rename_i hlt
        unfold F64.lt at hlt
        cases hyn : y.isNaN
        · rfl
        · simp [hyn] at hlt
      · exact hmn
    · simp only [List.any_cons, Bool.or_eq_true] at h
      rcases h with (hy | hys) | hm
      · right
        have hyi : y = F64.inf false := by rw [eq_inf_of_isInf hy, hs y (List.mem_cons_self ..)]
        subst hyi
        split
        · rfl
        · rename_i hnl
          -- m is not NaN and not below inf: m is inf
          have hmi : m.isInf = true := by
            apply Classical.byContradiction
            intro hmi
            apply hnl
            unfold F64.lt
            have : (F64.inf false).isNaN = false := by decide +kernel
            simp [hmn, this, hmi, inf_facts.2.2.1]
            have : (F64.inf false).sign = false := by decide +kernel
            simp [this]
          rw [eq_inf_of_isInf hmi, hms]
      · left; exact hys
      · right
        subst hm
        split
        · rename_i hlt
          exfalso; revert hlt
          unfold F64.lt
          have : (F64.inf false).isNaN = false := by decide +kernel
          have hsg : (F64.inf false).sign = false := by decide +kernel
          simp [this, inf_facts.2.2.1, hsg]
        · rfl

theorem abs_isInf (x : F64) : (F64.abs x).isInf = x.isInf := by
  unfold isInf; rw [(abs_fields x).2.1, (abs_fields x).2.2]

theorem hypotDist_proven : HypotDist := by
  refine ⟨fun ps qs hl => ?_, fun p q hp hq hl => ?_, fun p q e hp => ?_, fun p q e hp hq => ?_,
    ?_, fun x hxn => ?_, fun xs hi => ?_, fun xs hi hn => ?_⟩
  · rw [dist_floats ps qs hl]
    have : (ps.zip qs).map (fun pq => Arg.float (F64.sub pq.1 pq.2)) =
        ((ps.zip qs).map (fun pq => F64.sub pq.1 pq.2)).map .float := by simp
    rw [this, hypot_floats]
    simp [List.map_map, Function.comp_def]
  · obtain ⟨pi, pe⟩ := p; obtain ⟨qi, qe⟩ := q
    simp only at hp hq hl; subst hp; subst hq
    simp [math_dist, It.finish, bind, Except.bind, hl]
  · obtain ⟨pi, pe⟩ := p
    simp only at hp; subst hp
    simp [math_dist, It.finish, bind, Except.bind]
  · obtain ⟨pi, pe⟩ := p; obtain ⟨qi, qe⟩ := q
    simp only at hp hq; subst hp; subst hq
    simp [math_dist, It.finish, bind, Except.bind]
  · have := hypot_floats []
    simp only [List.map_nil] at this
    rw [this]
    simp [vector_norm, runMax, isZeroC_eq, c0_facts]
  · have := hypot_floats [x]
    simp only [List.map_cons, List.map_nil] at this
    rw [this]
    have han : (F64.abs x).isNaN = false := by rw [abs_isNaN]; exact hxn
    by_cases hz : x.isZero = true
    · have hA : F64.abs x = c0 := by
        rw [eq_zero_of_isZero hz]; cases x.sign <;> decide +kernel
      rw [hA]; decide +kernel
    · have hz' : (F64.abs x).isZero = false := by rw [abs_isZero]; simpa using hz
      have hlt : F64.lt c0 (F64.abs x) = true := by
        rcases classify (F64.abs x) with h | h | h
        · rw [lt_of_finite c0_facts.1 h, c0_facts.2.2.1]
          have hs := (abs_fields x).1
          have hpos : 0 < (F64.abs x).toRat := by
            have hm := mant_pos_of_not_zero hz'
            rw [toRat_of_finite h, hs]
            simp only [Bool.false_eq_true, ↓reduceIte]
            exact Rat.mul_pos (natCast_pos' hm) (pw_pos _)
          simpa using hpos
        · have hs := (abs_fields x).1
          rw [eq_inf_of_isInf h, hs]; decide +kernel
        · rw [han] at h; cases h
      simp only [vector_norm, runMax, List.foldl_cons, List.foldl_nil, List.length_cons,
        List.length_nil, hlt, ↓reduceIte, List.any_cons, List.any_nil, han, Bool.or_false]
      split
      · rfl
      · simp
  · rw [hypot_floats]
    have h1 : (xs.map F64.abs).any (·.isInf) = true := by
      simp only [List.any_map, Function.comp_def, abs_isInf]; exact hi
    rw [runMax_inf xs h1]
    simp [vector_norm, inf_facts.2.2.1]
  · rw [hypot_floats]
    have h1 : (xs.map F64.abs).any (·.isInf) = false := by
      simp only [List.any_map, Function.comp_def, abs_isInf]; exact hi
    have h2 : (xs.map F64.abs).any (·.isNaN) = true := by
      simp only [List.any_map, Function.comp_def, abs_isNaN]; exact hn
    have hmi : (runMax (xs.map F64.abs)).isInf = false := by
      unfold runMax
      suffices ∀ (ys : List F64) (m : F64), ys.any (·.isInf) = false → m.isInf = false →
          (ys.foldl (fun m x => if F64.lt m x then x else m) m).isInf = false from
        this _ c0 h1 c0_facts.2.2.2.2
      intro ys
      induction ys with
      | nil => intro m _ hm; exact hm
      | cons y ys ih =>
        intro m h hm
        simp only [List.any_cons, Bool.or_eq_false_iff] at h
        simp only [List.foldl_cons]
        apply ih _ h.2
        split
        · exact h.1
        · exact hm
    refine ⟨cNaN, ?_, nan_facts.1⟩
    simp [vector_norm, hmi, h2]

end PyLean.MathInt
