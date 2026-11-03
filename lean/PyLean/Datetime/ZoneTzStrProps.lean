import PyLean.Datetime.ZoneRuleProps

/-!
# The two TZ footer parsers agree on NUL-free footers (`zoneinfo`, CPython 3.15.2)

The C parser (`parse_tz_str` and its helpers) walks the bytes; the Python parser
(`_parse_tz_str`) splits the text at commas and slashes and matches regular expressions. The
proof relates them component by component:
* `abbr_eq`, `time_eq`, `delta_eq`: `parse_abbr`, `parse_transition_time` and `parse_tz_delta`
  are the abbreviation and offset patterns, except that C fails inside an offset where Python
  stops before a `:` that then fails Python's next step;
* `datePy_eq`, `rule_eq`: the date part and the whole of a rule, with `/time`;
* `*_tail`: no C component reads past a comma, so C's walk over the whole footer equals its
  walk over each comma-separated part;
* `tz_eq`, `pyTz_props`: the two results correspond, Python's errors are `ValueError`s, and
  a footer Python accepts is ASCII (so `tz_str.decode()` accepted it too).
-/

namespace PyLean.Datetime.Zone

open PyLean PyLean.Datetime

/-! parse_digits -/

theorem digitsGo_eq (min : Nat) : ∀ (k i : Nat) (v : Int) (p : Bytes), min ≤ i + k →
    parseDigitsC.go min k i v p =
      (let ds := (p.takeWhile isDigitB).take k
       if i + ds.length < min then none
       else some (ds.foldl (fun acc c => acc * 10 + ((c.toNat - 48 : Nat) : Int)) v, p.drop ds.length)) := by
  intro k
  induction k with
  | zero => intro i v p h; simp [parseDigitsC.go]; omega
  | succ k ih =>
    intro i v p h
    cases p with
    | nil =>
      simp [parseDigitsC.go, peek, isDigitB, inR]
    | cons c r =>
      simp only [parseDigitsC.go, peek, List.headD_cons, List.tail_cons]
      by_cases hc : isDigitB c = true
      · simp only [hc, ite_true]
        rw [ih (i + 1) _ r (by omega)]
        simp only [List.takeWhile_cons, hc, ite_true, List.take_succ_cons, List.length_cons,
          List.foldl_cons, List.drop_succ_cons]
        rw [show i + 1 + ((List.takeWhile isDigitB r).take k).length =
          i + (((List.takeWhile isDigitB r).take k).length + 1) by omega]
      · simp only [hc, Bool.false_eq_true, ite_false, List.takeWhile_cons, List.take_nil,
          List.length_nil, Nat.add_zero, List.foldl_nil, List.drop_zero]

theorem digitsVal_foldl (ds : Bytes) (v : Int) :
    ds.foldl (fun acc c => acc * 10 + ((c.toNat - 48 : Nat) : Int)) v =
      v * 10 ^ ds.length + digitsVal ds := by
  unfold digitsVal
  induction ds generalizing v with
  | nil => simp
  | cons c r ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, ih (0 * 10 + _), Int.pow_succ]
    simp only [Int.zero_mul, Int.zero_add]
    generalize (10 : Int) ^ r.length = q
    generalize (((c.toNat - 48 : Nat)) : Int) = e
    rw [Int.add_mul, Int.mul_assoc, Int.mul_comm 10 q]
    omega

theorem parseDigitsC_eq (min max : Nat) (hm : min ≤ max) (p : Bytes) :
    parseDigitsC min max p =
      (let ds := (p.takeWhile isDigitB).take max
       if ds.length < min then none else some (digitsVal ds, p.drop ds.length)) := by
  unfold parseDigitsC
  rw [digitsGo_eq min max 0 0 p (by omega)]
  simp only [Nat.zero_add]
  rfl

/-! parse_abbr -/

theorem quotedRunC_eq : ∀ t : Bytes, quotedRunC t =
    if peek (t.drop (t.takeWhile isQuotedB).length) = 62 then
      some (t.takeWhile isQuotedB, t.drop ((t.takeWhile isQuotedB).length + 1))
    else none := by
  intro t
  induction t with
  | nil => simp [quotedRunC, peek]
  | cons c r ih =>
    by_cases h62 : c = 62
    · subst h62
      simp [quotedRunC, isQuotedB, isAlphaB, isDigitB, inR, peek]
    · by_cases hq : isQuotedB c = true
      · simp only [quotedRunC, h62, ite_false, hq, ite_true, List.takeWhile_cons, List.length_cons,
          List.drop_succ_cons, ih]
        split <;> simp
      · have : peek (c :: r) ≠ 62 := by simpa [peek] using h62
        simp [quotedRunC, h62, hq, List.takeWhile_cons, this]

theorem not_angle_of_quoted (c : UInt8) (h : isQuotedB c = true) : ¬ (c = 60 ∨ c = 62) := by
  intro e
  rcases e with rfl | rfl <;> simp [isQuotedB, isAlphaB, isDigitB, inR] at h

theorem dropAngle_self (l : Bytes) (h : ∀ c ∈ l.head?, ¬ (c = 60 ∨ c = 62)) :
    l.dropWhile (fun c => decide (c = 60 ∨ c = 62)) = l := by
  cases l with
  | nil => rfl
  | cons a r =>
    rw [List.dropWhile_cons]
    have := h a (by simp)
    simp only [decide_eq_true_eq, this, ite_false]

theorem strip_self (l : Bytes) (hn : ∀ c ∈ l, ¬ (c = 60 ∨ c = 62)) : stripAngle l = l := by
  unfold stripAngle
  rw [dropAngle_self l (fun c hc => hn c (List.mem_of_mem_head? hc))]
  rw [dropAngle_self l.reverse (fun c hc => hn c (List.mem_reverse.mp (List.mem_of_mem_head? hc)))]
  exact List.reverse_reverse l

theorem strip_wrap (run : Bytes) (hne : run ≠ []) (hn : ∀ c ∈ run, ¬ (c = 60 ∨ c = 62)) :
    stripAngle ([60] ++ run ++ [62]) = run := by
  unfold stripAngle
  have e1 : (([60] ++ run ++ [62]).dropWhile fun c => decide (c = 60 ∨ c = 62)) = run ++ [62] := by
    rw [List.append_assoc, List.singleton_append, List.dropWhile_cons]
    simp only [show decide ((60 : UInt8) = 60 ∨ (60 : UInt8) = 62) = true by decide, ite_true]
    apply dropAngle_self
    intro c hc
    cases run with
    | nil => exact absurd rfl hne
    | cons a r => simp at hc; subst hc; exact hn a (by simp)
  rw [e1, List.reverse_append, List.reverse_singleton, List.singleton_append, List.dropWhile_cons]
  simp only [show decide ((62 : UInt8) = 60 ∨ (62 : UInt8) = 62) = true by decide, ite_true]
  rw [dropAngle_self run.reverse (fun c hc => hn c (List.mem_reverse.mp (List.mem_of_mem_head? hc)))]
  exact List.reverse_reverse run

theorem mem_takeWhile' {p : UInt8 → Bool} : ∀ (l : Bytes) (c : UInt8), c ∈ l.takeWhile p → p c = true := by
  intro l
  induction l with
  | nil => intro c h; simp at h
  | cons a r ih =>
    intro c h
    rw [List.takeWhile_cons] at h
    split at h
    · rename_i ha
      rcases List.mem_cons.mp h with rfl | h
      · exact ha
      · exact ih c h
    · simp at h

theorem quoted_not_angle (c : UInt8) (h : isQuotedB c = true) : ¬ (c = 60 ∨ c = 62) := by
  intro e
  rcases e with rfl | rfl <;> simp [isQuotedB, isAlphaB, isDigitB, inR] at h

theorem alpha_not_angle (c : UInt8) (h : isAlphaB c = true) : ¬ (c = 60 ∨ c = 62) := by
  intro e
  rcases e with rfl | rfl <;> simp [isAlphaB, inR] at h

theorem abbr_eq (p : Bytes) : parseAbbrC p = (reAbbr p).map (fun gr => (stripAngle gr.1, gr.2)) := by
  unfold parseAbbrC reAbbr
  by_cases h60 : peek p = 60
  · rw [if_pos h60, quotedRunC_eq]
    simp only [h60, show isAlphaB 60 = false by decide, Bool.false_eq_true, ite_false, ite_true]
    by_cases hp : peek (p.tail.drop (p.tail.takeWhile isQuotedB).length) = 62
    · simp only [hp, ite_true, and_true]
      by_cases hnil : p.tail.takeWhile isQuotedB = []
      · simp [hnil]
      · simp only [hnil, ite_false, ne_eq, not_false_eq_true, ite_true, Option.map_some]
        rw [strip_wrap _ hnil (fun c hc => quoted_not_angle c (mem_takeWhile' _ c hc))]
    · simp only [hp, ite_false, and_false, Option.map_none]
  · rw [if_neg h60]
    by_cases ha : isAlphaB (peek p) = true
    · have hne : p.takeWhile isAlphaB ≠ [] := by
        cases p with
        | nil => simp [peek] at ha; exact absurd ha (by decide)
        | cons c r => simp [peek] at ha; simp [List.takeWhile_cons, ha]
      rw [if_neg hne, if_pos ha, Option.map_some,
        strip_self _ (fun c hc => alpha_not_angle c (mem_takeWhile' _ c hc))]
    · have : p.takeWhile isAlphaB = [] := by
        cases p with
        | nil => rfl
        | cons c r => simp [peek] at ha; simp [List.takeWhile_cons, ha]
      rw [if_pos this, if_neg ha, if_neg h60]
      rfl

/-! parse_transition_time -/

theorem colon2_eq (t : Bytes) :
    parseDigitsC 2 2 t = (reColon2 (58 :: t)).map (fun dr => (digitsVal dr.1, dr.2)) := by
  rw [parseDigitsC_eq 2 2 (by omega)]
  match t with
  | [] => simp [reColon2]
  | [a] =>
    simp only [reColon2]
    by_cases ha : isDigitB a = true <;> simp [List.takeWhile_cons, ha]
  | a :: b :: r =>
    simp only [reColon2]
    by_cases ha : isDigitB a = true <;> by_cases hb : isDigitB b = true <;>
      simp [List.takeWhile_cons, ha, hb]

theorem reColon2_ne (s : Bytes) (h : peek s ≠ 58) : reColon2 s = none := by
  match s with
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | c :: a :: b :: r => simp [reColon2]; intro e; simp [peek, e] at h

/-- The sign `parse_transition_time` applies: `-` gives -1. -/
def sgnOf (sg : Option UInt8) : Int := if sg = some 45 then -1 else 1

theorem time_eq (mi0 s0 : Int) (p : Bytes) :
    parseTransTimeC mi0 s0 p =
      match reOff p with
      | none => none
      | some ((sg, hd, none, _), r) =>
        if peek r = 58 then none else some ((digitsVal hd * sgnOf sg, mi0, s0), r)
      | some ((sg, hd, some mm, none), r) =>
        if peek r = 58 then none else some ((digitsVal hd * sgnOf sg, digitsVal mm * sgnOf sg, s0), r)
      | some ((sg, hd, some mm, some ss), r) =>
        some ((digitsVal hd * sgnOf sg, digitsVal mm * sgnOf sg, digitsVal ss * sgnOf sg), r) := by
  -- both read the same optional sign
  obtain ⟨sgn, sgo, s1, hC, hP, hs⟩ : ∃ (sgn : Int) (sgo : Option UInt8) (s1 : Bytes),
      ((if peek p = 45 then (-1, p.tail) else if peek p = 43 then (1, p.tail) else (1, p)) : Int × Bytes)
        = (sgn, s1) ∧
      ((if peek p = 43 ∨ peek p = 45 then (some (peek p), p.tail) else (none, p)) : Option UInt8 × Bytes)
        = (sgo, s1) ∧ sgn = sgnOf sgo := by
    by_cases h45 : peek p = 45
    · exact ⟨-1, some 45, p.tail, by simp [h45], by simp [h45], by simp [sgnOf]⟩
    · by_cases h43 : peek p = 43
      · exact ⟨1, some 43, p.tail, by simp [h43], by simp [h43], by simp [sgnOf]⟩
      · exact ⟨1, none, p, by simp [h45, h43], by simp [h45, h43], by simp [sgnOf]⟩
  unfold parseTransTimeC reOff
  rw [hC, hP]
  simp only [bind, Option.bind, parseDigitsC_eq 1 3 (by omega)]
  by_cases hds : (s1.takeWhile isDigitB).take 3 = []
  · simp [hds]
  · have hlen : ¬ ((s1.takeWhile isDigitB).take 3).length < 1 := by
      intro e; apply hds; exact List.eq_nil_of_length_eq_zero (by omega)
    simp only [hlen, ite_false, hds]
    generalize s1.drop ((s1.takeWhile isDigitB).take 3).length = s2
    generalize (s1.takeWhile isDigitB).take 3 = hd
    by_cases h58 : peek s2 = 58
    · obtain ⟨t, rfl⟩ : ∃ t, s2 = 58 :: t := by
        cases s2 with
        | nil => simp [peek] at h58
        | cons c t => simp [peek] at h58; exact ⟨t, by rw [h58]⟩
      simp only [peek, List.headD_cons, ite_true, List.tail_cons, colon2_eq]
      cases hr : reColon2 (58 :: t) with
      | none => simp [peek]
      | some mr =>
        obtain ⟨mm, s3⟩ := mr
        simp only [Option.map_some]
        by_cases h58' : peek s3 = 58
        · obtain ⟨t', rfl⟩ : ∃ t', s3 = 58 :: t' := by
            cases s3 with
            | nil => simp [peek] at h58'
            | cons c t' => simp [peek] at h58'; exact ⟨t', by rw [h58']⟩
          simp only [peek, List.headD_cons, ite_true, List.tail_cons, colon2_eq]
          cases hr2 : reColon2 (58 :: t') with
          | none => simp [peek]
          | some sr => obtain ⟨ss, s4⟩ := sr; simp [hs, Int.mul_comm]
        · simp only [h58', ite_false, reColon2_ne s3 h58', hs]
          have h3 : (s3.head?).getD 0 ≠ 58 := by simpa [peek] using h58'
          simp [h3, Int.mul_comm]
    · simp only [h58, ite_false, reColon2_ne s2 h58, hs]
      have h3 : (s2.head?).getD 0 ≠ 58 := by simpa [peek] using h58
      simp [h3, Int.mul_comm]

/-! Appending a tail that starts at a comma (or nothing) does not change a component. -/

def CommaTail (T : Bytes) : Prop := T = [] ∨ ∃ t, T = 44 :: t

theorem takeWhile_stop {q : UInt8 → Bool} (x T : Bytes) (hq : ∀ t, T = 44 :: t → q 44 = false)
    (hT : CommaTail T) : (x ++ T).takeWhile q = x.takeWhile q ∧
      (∀ n, n = (x.takeWhile q).length → (x ++ T).drop n = x.drop n ++ T) := by
  induction x with
  | nil =>
    rcases hT with rfl | ⟨t, rfl⟩
    · simp
    · simp [List.takeWhile_cons, hq t rfl]
  | cons c r ih =>
    refine ⟨?_, ?_⟩
    · simp only [List.cons_append, List.takeWhile_cons]
      split
      · rw [ih.1]
      · rfl
    · intro n hn
      simp only [List.takeWhile_cons] at hn
      split at hn
      · subst hn
        simp only [List.length_cons, List.cons_append, List.drop_succ_cons]
        exact ih.2 _ rfl
      · subst hn; simp

theorem peek_tail (x T : Bytes) (hT : CommaTail T) (c : UInt8) (hc0 : c ≠ 0) (hc : c ≠ 44) :
    (peek (x ++ T) = c) ↔ (peek x = c) := by
  cases x with
  | nil =>
    rcases hT with rfl | ⟨t, rfl⟩
    · simp
    · simp [peek]; constructor <;> intro e
      · exact absurd e.symm hc
      · exact absurd e.symm hc0
  | cons a r => simp [peek]

theorem tail_nonclass (T : Bytes) (hT : CommaTail T) : ∀ t, T = 44 :: t →
    isAlphaB 44 = false ∧ isQuotedB 44 = false ∧ isDigitB 44 = false := by
  intro _ _; decide

theorem reColon2_tail (x T : Bytes) (hT : CommaTail T) :
    reColon2 (x ++ T) = (reColon2 x).map (fun dr => (dr.1, dr.2 ++ T)) := by
  rcases hT with rfl | ⟨t, rfl⟩
  · simp
  · match x with
    | [] =>
      cases t with
      | nil => rfl
      | cons b r => cases r <;> simp [reColon2]
    | [c] =>
      have h44 : isDigitB 44 = false := by decide
      cases t <;> simp [reColon2, h44]
    | [c, a] =>
      have h44 : isDigitB 44 = false := by decide
      simp [reColon2, h44]
    | c :: a :: b :: r =>
      simp only [reColon2, List.cons_append]
      split <;> simp

theorem drop_succ_of {α : Type} : ∀ (l : List α) (n : Nat) (a : α) (d : List α),
    l.drop n = a :: d → l.drop (n + 1) = d
  | [], n, a, d, h => by simp at h
  | b :: l, 0, a, d, h => by simp at h; simp [h.2]
  | b :: l, n + 1, a, d, h => by simp at h ⊢; exact drop_succ_of l n a d h

theorem reAbbr_tail (x T : Bytes) (hT : CommaTail T) :
    reAbbr (x ++ T) = (reAbbr x).map (fun gr => (gr.1, gr.2 ++ T)) := by
  unfold reAbbr
  have ha := takeWhile_stop (q := isAlphaB) x T (fun _ _ => by decide) hT
  by_cases hx : x = []
  · subst hx
    rcases hT with rfl | ⟨t, rfl⟩
    · simp
    · simp [peek, isAlphaB, inR]
  · have hp : peek (x ++ T) = peek x := by
      cases x with
      | nil => exact absurd rfl hx
      | cons a r => simp [peek]
    rw [hp]
    by_cases hal : isAlphaB (peek x) = true
    · simp only [hal, ite_true, Option.map_some, ha.1, ha.2 _ rfl]
    · simp only [hal, Bool.false_eq_true, ite_false]
      by_cases h60 : peek x = 60
      · simp only [h60, ite_true]
        have htl : (x ++ T).tail = x.tail ++ T := by
          cases x with
          | nil => exact absurd rfl hx
          | cons a r => simp
        rw [htl]
        have hq := takeWhile_stop (q := isQuotedB) x.tail T (fun _ _ => by decide) hT
        rw [hq.1, hq.2 _ rfl]
        have hpk := peek_tail (x.tail.drop (x.tail.takeWhile isQuotedB).length) T hT 62 (by decide) (by decide)
        by_cases hc : x.tail.takeWhile isQuotedB ≠ [] ∧ peek (x.tail.drop (x.tail.takeWhile isQuotedB).length) = 62
        · have hc' : x.tail.takeWhile isQuotedB ≠ [] ∧
              peek (x.tail.drop (x.tail.takeWhile isQuotedB).length ++ T) = 62 := ⟨hc.1, hpk.mpr hc.2⟩
          rw [if_pos hc', if_pos hc, Option.map_some]
          congr 2
          -- drop past the `>` that lies inside x
          obtain ⟨d, hd⟩ : ∃ d, x.tail.drop (x.tail.takeWhile isQuotedB).length = 62 :: d := by
            generalize x.tail.drop (x.tail.takeWhile isQuotedB).length = w at hc
            cases w with
            | nil => simp [peek] at hc
            | cons a w => simp [peek] at hc; exact ⟨w, by rw [hc.2]⟩
          have e := hq.2 _ rfl
          rw [hd, List.cons_append] at e
          show _ = (x.tail.drop ((x.tail.takeWhile isQuotedB).length + 1)) ++ T
          rw [drop_succ_of _ _ _ _ hd]
          exact drop_succ_of _ _ _ _ e
        · have hc' : ¬ (x.tail.takeWhile isQuotedB ≠ [] ∧
              peek (x.tail.drop (x.tail.takeWhile isQuotedB).length ++ T) = 62) :=
            fun e => hc ⟨e.1, hpk.mp e.2⟩
          rw [if_neg hc', if_neg hc]
          rfl
      · simp [h60]

theorem reOff_tail (x T : Bytes) (hT : CommaTail T) :
    reOff (x ++ T) = (reOff x).map (fun or_ => (or_.1, or_.2 ++ T)) := by
  obtain ⟨sgo, s1, hx, hxT⟩ : ∃ (sgo : Option UInt8) (s1 : Bytes),
      ((if peek x = 43 ∨ peek x = 45 then (some (peek x), x.tail) else (none, x)) : Option UInt8 × Bytes)
        = (sgo, s1) ∧
      ((if peek (x ++ T) = 43 ∨ peek (x ++ T) = 45 then (some (peek (x ++ T)), (x ++ T).tail)
        else (none, x ++ T)) : Option UInt8 × Bytes) = (sgo, s1 ++ T) := by
    have h43 := peek_tail x T hT 43 (by decide) (by decide)
    have h45 := peek_tail x T hT 45 (by decide) (by decide)
    by_cases hs : peek x = 43 ∨ peek x = 45
    · have hne : x ≠ [] := by intro e; subst e; simp [peek] at hs
      have hp : peek (x ++ T) = peek x := by
        cases x with
        | nil => exact absurd rfl hne
        | cons a r => simp [peek]
      have htl : (x ++ T).tail = x.tail ++ T := by
        cases x with
        | nil => exact absurd rfl hne
        | cons a r => simp
      refine ⟨some (peek x), x.tail, by simp [hs], ?_⟩
      rw [hp, htl]; simp [hs]
    · have hs' : ¬ (peek (x ++ T) = 43 ∨ peek (x ++ T) = 45) := by rw [h43, h45]; exact hs
      exact ⟨none, x, by simp [hs], by simp [hs']⟩
  unfold reOff
  rw [hx, hxT]
  simp only
  have hd := takeWhile_stop (q := isDigitB) s1 T (fun _ _ => by decide) hT
  rw [hd.1]
  by_cases hds : (s1.takeWhile isDigitB).take 3 = []
  · simp [hds]
  · simp only [hds, ite_false]
    have hdrop : (s1 ++ T).drop ((s1.takeWhile isDigitB).take 3).length =
        s1.drop ((s1.takeWhile isDigitB).take 3).length ++ T := by
      rw [List.drop_append_of_le_length]
      have : ((s1.takeWhile isDigitB).take 3).length ≤ (s1.takeWhile isDigitB).length := by simp; omega
      have : (s1.takeWhile isDigitB).length ≤ s1.length := (List.takeWhile_sublist _).length_le
      omega
    rw [hdrop, reColon2_tail _ _ hT]
    cases hc : reColon2 (s1.drop ((s1.takeWhile isDigitB).take 3).length) with
    | none => simp
    | some mr =>
      obtain ⟨mm, s3⟩ := mr
      simp only [Option.map_some]
      rw [reColon2_tail _ _ hT]
      cases hc2 : reColon2 s3 <;> simp

/-- The shape of what `reOff` matches. -/
def OffShape (o : Option UInt8 × Bytes × Option Bytes × Option Bytes) : Prop :=
  (o.1 = none ∨ o.1 = some 43 ∨ o.1 = some 45) ∧ o.2.1 ≠ [] ∧ o.2.1.length ≤ 3 ∧
    (∀ c ∈ o.2.1, isDigitB c = true) ∧
    (∀ m, o.2.2.1 = some m → ∃ a b, m = [a, b] ∧ isDigitB a = true ∧ isDigitB b = true) ∧
    (∀ m, o.2.2.2 = some m → ∃ a b, m = [a, b] ∧ isDigitB a = true ∧ isDigitB b = true) ∧
    (o.2.2.1 = none → o.2.2.2 = none)

theorem reColon2_some (s : Bytes) (m r : Bytes) (h : reColon2 s = some (m, r)) :
    ∃ a b, m = [a, b] ∧ isDigitB a = true ∧ isDigitB b = true ∧ s = 58 :: a :: b :: r := by
  match s, h with
  | c :: a :: b :: r', h =>
    simp only [reColon2] at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨a, b, rfl, hc.2.1, hc.2.2, by rw [hc.1]⟩
    · cases h

theorem reOff_shape (p : Bytes) (o : Option UInt8 × Bytes × Option Bytes × Option Bytes) (r : Bytes)
    (h : reOff p = some (o, r)) : OffShape o := by
  unfold reOff at h
  obtain ⟨sgo, s1, hs, hsg⟩ : ∃ (sgo : Option UInt8) (s1 : Bytes),
      ((if peek p = 43 ∨ peek p = 45 then (some (peek p), p.tail) else (none, p)) : Option UInt8 × Bytes)
        = (sgo, s1) ∧ (sgo = none ∨ sgo = some 43 ∨ sgo = some 45) := by
    by_cases hc : peek p = 43 ∨ peek p = 45
    · refine ⟨some (peek p), p.tail, by simp [hc], ?_⟩
      rcases hc with e | e <;> simp [e]
    · exact ⟨none, p, by simp [hc], by simp⟩
  rw [hs] at h
  simp only at h
  split at h
  · cases h
  · rename_i hds
    have hdig : ∀ c ∈ (s1.takeWhile isDigitB).take 3, isDigitB c = true :=
      fun c hc => mem_takeWhile' s1 c (List.mem_of_mem_take hc)
    have hl : ((s1.takeWhile isDigitB).take 3).length ≤ 3 := by simp; omega
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact ⟨hsg, hds, hl, hdig, by simp, by simp, by simp⟩
    · rename_i mm s3 hm
      obtain ⟨a, b, rfl, ha, hb, -⟩ := reColon2_some _ _ _ hm
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact ⟨hsg, hds, hl, hdig, fun m e => by simp at e; exact ⟨a, b, e.symm, ha, hb⟩, by simp, by simp⟩
      · rename_i ss s4 hss
        obtain ⟨c, d, rfl, hc, hd, -⟩ := reColon2_some _ _ _ hss
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact ⟨hsg, hds, hl, hdig, fun m e => by simp at e; exact ⟨a, b, e.symm, ha, hb⟩,
          fun m e => by simp at e; exact ⟨c, d, e.symm, hc, hd⟩, by simp⟩

theorem takeWhile_all_stop {q : UInt8 → Bool} (hd R : Bytes) (h : ∀ c ∈ hd, q c = true)
    (hR : ∀ c, R.head? = some c → q c = false) : (hd ++ R).takeWhile q = hd := by
  induction hd with
  | nil =>
    cases R with
    | nil => rfl
    | cons c r => simp [List.takeWhile_cons, hR c rfl]
  | cons a l ih =>
    simp only [List.cons_append, List.takeWhile_cons, h a (by simp), ite_true]
    rw [ih (fun c hc => h c (by simp [hc]))]

theorem reOff_offText (o : Option UInt8 × Bytes × Option Bytes × Option Bytes) (hs : OffShape o) :
    reOff (offText o) = some (o, []) := by
  obtain ⟨sg, hd, mm, ss⟩ := o
  obtain ⟨hsg, hne, hl3, hdig, hmm, hss, hms⟩ := hs
  simp only at hsg hne hl3 hdig hmm hss hms
  -- the text after the hour digits
  have hR : ∀ c, ((mm.map ([58] ++ ·)).getD [] ++ (ss.map ([58] ++ ·)).getD []).head? = some c →
      isDigitB c = false := by
    intro c hc
    cases mm with
    | none => simp [hms rfl] at hc
    | some m => simp at hc; rw [← hc]; decide
  have hfirst : ∀ c, (hd ++ (mm.map ([58] ++ ·)).getD [] ++ (ss.map ([58] ++ ·)).getD []).head? = some c →
      ¬ (c = 43 ∨ c = 45) := by
    intro c hc
    cases hd with
    | nil => exact absurd rfl hne
    | cons a l =>
      simp at hc; subst hc
      have := hdig a (by simp)
      intro e; rcases e with rfl | rfl <;> simp [isDigitB, inR] at this
  have hs1 : ∃ s1, (if peek (offText (sg, hd, mm, ss)) = 43 ∨ peek (offText (sg, hd, mm, ss)) = 45 then
        (some (peek (offText (sg, hd, mm, ss))), (offText (sg, hd, mm, ss)).tail)
      else (none, offText (sg, hd, mm, ss))) = (sg, s1) ∧
      s1 = hd ++ (mm.map ([58] ++ ·)).getD [] ++ (ss.map ([58] ++ ·)).getD [] := by
    unfold offText
    rcases hsg with rfl | rfl | rfl
    · refine ⟨_, ?_, rfl⟩
      have : ¬ (peek ((none : Option UInt8).toList ++ hd ++ (mm.map ([58] ++ ·)).getD [] ++
          (ss.map ([58] ++ ·)).getD []) = 43 ∨ peek ((none : Option UInt8).toList ++ hd ++
          (mm.map ([58] ++ ·)).getD [] ++ (ss.map ([58] ++ ·)).getD []) = 45) := by
        cases hd with
        | nil => exact absurd rfl hne
        | cons a l => simpa [peek] using hfirst a (by simp)
      simp only [Option.toList, List.nil_append] at this ⊢
      simp only [this, ite_false]
    · refine ⟨_, ?_, rfl⟩
      simp [peek, Option.toList]
    · refine ⟨_, ?_, rfl⟩
      simp [peek, Option.toList]
  obtain ⟨s1, h1, rfl⟩ := hs1
  unfold reOff
  rw [h1]
  simp only
  rw [List.append_assoc, takeWhile_all_stop hd _ hdig hR,
    List.take_of_length_le hl3]
  simp only [hne, ite_false, List.drop_left]
  cases mm with
  | none =>
    simp [hms rfl, reColon2]
  | some m =>
    obtain ⟨a, b, rfl, ha, hb⟩ := hmm m rfl
    simp only [Option.map_some, Option.getD_some, List.singleton_append, List.cons_append, List.nil_append,
      reColon2, ha, hb, and_self, ite_true]
    cases ss with
    | none => simp [reColon2]
    | some m2 =>
      obtain ⟨c, d, rfl, hc, hd'⟩ := hss m2 rfl
      simp [reColon2, hc, hd']

theorem digitsVal_nonneg (ds : Bytes) : 0 ≤ digitsVal ds := by
  unfold digitsVal
  suffices ∀ a : Int, 0 ≤ a → 0 ≤ ds.foldl (fun acc c => acc * 10 + ((c.toNat - 48 : Nat) : Int)) a from
    this 0 (Int.le_refl _)
  induction ds with
  | nil => intro a h; exact h
  | cons c r ih =>
    intro a h
    simp only [List.foldl_cons]
    exact ih _ (by have := Int.natCast_nonneg (c.toNat - 48); omega)

theorem reTime_offText (o : Option UInt8 × Bytes × Option Bytes × Option Bytes) (hs : OffShape o) :
    reTime (offText o) = some (decide (o.1 = some 45), digitsVal o.2.1, (o.2.2.1.map digitsVal).getD 0,
      (o.2.2.2.map digitsVal).getD 0) := by
  unfold reTime
  rw [reOff_offText o hs]

theorem delta_eq (p : Bytes) : parseTzDeltaC p =
    match reOff p with
    | none => none
    | some (o, r) =>
      if o.2.2.2 = none ∧ peek r = 58 then none
      else match parseTzDeltaPy (offText o) with
        | .ok v => some (v, r)
        | .error _ => none := by
  unfold parseTzDeltaC
  rw [time_eq]
  cases hr : reOff p with
  | none => rfl
  | some or_ =>
    obtain ⟨⟨sg, hd, mm, ss⟩, r⟩ := or_
    have hs := reOff_shape p _ _ hr
    have hpy := reTime_offText _ hs
    simp only at hpy
    have hh := digitsVal_nonneg hd
    unfold parseTzDeltaPy
    rcases mm with _ | m <;> rcases ss with _ | sv
    · simp only
      rw [hpy]
      by_cases h58 : peek r = 58 <;> by_cases e : sg = some 45 <;> by_cases h24 : digitsVal hd > 24 <;>
        simp [sgnOf, e, h58, h24, bind, Option.bind] <;> omega
    · exact absurd (hs.2.2.2.2.2.2 rfl) (by simp)
    · simp only
      rw [hpy]
      by_cases h58 : peek r = 58 <;> by_cases e : sg = some 45 <;> by_cases h24 : digitsVal hd > 24 <;>
        simp [sgnOf, e, h58, h24, bind, Option.bind] <;> omega
    · simp only
      rw [hpy]
      by_cases e : sg = some 45 <;> by_cases h24 : digitsVal hd > 24 <;>
        simp [sgnOf, e, h24, bind, Option.bind] <;> omega

/-! The date part of a rule, and the slash after it. -/

def ZTail (z : UInt8) (T : Bytes) : Prop := T = [] ∨ ∃ t, T = z :: t

theorem takeWhile_stopZ {q : UInt8 → Bool} (z : UInt8) (hz : q z = false) (x T : Bytes)
    (hT : ZTail z T) : (x ++ T).takeWhile q = x.takeWhile q ∧
      (∀ n, n = (x.takeWhile q).length → (x ++ T).drop n = x.drop n ++ T) := by
  induction x with
  | nil =>
    rcases hT with rfl | ⟨t, rfl⟩
    · simp
    · simp [List.takeWhile_cons, hz]
  | cons c r ih =>
    refine ⟨?_, ?_⟩
    · simp only [List.cons_append, List.takeWhile_cons]
      split
      · rw [ih.1]
      · rfl
    · intro n hn
      simp only [List.takeWhile_cons] at hn
      split at hn
      · subst hn
        simp only [List.length_cons, List.cons_append, List.drop_succ_cons]
        exact ih.2 _ rfl
      · subst hn; simp

theorem peek_tailZ (z : UInt8) (x T : Bytes) (hT : ZTail z T) (c : UInt8) (hc0 : c ≠ 0) (hc : c ≠ z) :
    (peek (x ++ T) = c) ↔ (peek x = c) := by
  cases x with
  | nil =>
    rcases hT with rfl | ⟨t, rfl⟩
    · simp
    · simp [peek]; constructor <;> intro e
      · exact absurd e.symm hc
      · exact absurd e.symm hc0
  | cons a r => simp [peek]

theorem digits_tailZ (z : UInt8) (hz : isDigitB z = false) (min max : Nat) (hm : min ≤ max) (x T : Bytes)
    (hT : ZTail z T) :
    parseDigitsC min max (x ++ T) = (parseDigitsC min max x).map (fun vr => (vr.1, vr.2 ++ T)) := by
  rw [parseDigitsC_eq _ _ hm, parseDigitsC_eq _ _ hm]
  have h := takeWhile_stopZ (q := isDigitB) z hz x T hT
  rw [h.1]
  simp only
  split
  · rfl
  · simp only [Option.map_some]
    congr 2
    rw [List.drop_append_of_le_length]
    have : ((x.takeWhile isDigitB).take max).length ≤ (x.takeWhile isDigitB).length := by simp; omega
    have : (x.takeWhile isDigitB).length ≤ x.length := (List.takeWhile_sublist _).length_le
    omega

theorem tail_app (x T : Bytes) (hx : x ≠ []) : (x ++ T).tail = x.tail ++ T := by
  cases x with
  | nil => exact absurd rfl hx
  | cons a r => simp

theorem ruleDate_tailZ (z : UInt8) (hz : isDigitB z = false) (h77 : (77 : UInt8) ≠ z) (h46 : (46 : UInt8) ≠ z)
    (h74 : (74 : UInt8) ≠ z) (x S : Bytes) (hS : ZTail z S) :
    parseRuleDateC (x ++ S) = (parseRuleDateC x).map (fun dr => (dr.1, dr.2 ++ S)) := by
  have hd : isDigitB z = false := hz
  unfold parseRuleDateC
  have p77 := peek_tailZ z x S hS 77 (by decide) h77
  by_cases hp77 : peek x = 77
  · have hx : x ≠ [] := by intro e; subst e; simp [peek] at hp77
    rw [if_pos (p77.mpr hp77), if_pos hp77, tail_app x S hx]
    simp only [bind, Option.bind]
    rw [digits_tailZ z hd 1 2 (by omega) x.tail S hS]
    cases h1 : parseDigitsC 1 2 x.tail with
    | none => rfl
    | some v1 =>
      obtain ⟨m, r1⟩ := v1
      simp only [Option.map_some]
      have p46 := peek_tailZ z r1 S hS 46 (by decide) h46
      by_cases e1 : peek r1 = 46
      · have hr1 : r1 ≠ [] := by intro e; subst e; simp [peek] at e1
        simp only [p46, e1, ne_eq, not_true_eq_false, ite_false, tail_app r1 S hr1]
        rw [digits_tailZ z hd 1 1 (by omega) r1.tail S hS]
        cases h2 : parseDigitsC 1 1 r1.tail with
        | none => rfl
        | some v2 =>
          obtain ⟨w, r2⟩ := v2
          simp only [Option.map_some]
          have p46' := peek_tailZ z r2 S hS 46 (by decide) h46
          by_cases e2 : peek r2 = 46
          · have hr2 : r2 ≠ [] := by intro e; subst e; simp [peek] at e2
            simp only [p46', e2, ne_eq, not_true_eq_false, ite_false, tail_app r2 S hr2]
            rw [digits_tailZ z hd 1 1 (by omega) r2.tail S hS]
            cases parseDigitsC 1 1 r2.tail <;> rfl
          · simp [p46', e2]
      · simp [p46, e1]
  · rw [if_neg (fun e => hp77 (p77.mp e)), if_neg hp77]
    have p74 := peek_tailZ z x S hS 74 (by decide) h74
    by_cases h74 : peek x = 74
    · have hx : x ≠ [] := by intro e; subst e; simp [peek] at h74
      simp only [p74, h74, ite_true, tail_app x S hx, bind, Option.bind]
      rw [digits_tailZ z hd 1 3 (by omega) x.tail S hS]
      cases parseDigitsC 1 3 x.tail <;> rfl
    · simp only [p74, h74, ite_false, bind, Option.bind]
      rw [digits_tailZ z hd 1 3 (by omega) x S hS]
      cases parseDigitsC 1 3 x <;> rfl

theorem ruleDate_tail (x S : Bytes) (hS : ZTail 47 S) :
    parseRuleDateC (x ++ S) = (parseRuleDateC x).map (fun dr => (dr.1, dr.2 ++ S)) :=
  ruleDate_tailZ 47 (by decide) (by decide) (by decide) (by decide) x S hS

theorem digits11 (c : UInt8) (r : Bytes) :
    parseDigitsC 1 1 (c :: r) = if isDigitB c = true then some (digitsVal [c], r) else none := by
  rw [parseDigitsC_eq 1 1 (by omega)]
  by_cases h : isDigitB c = true <;> simp [h, List.takeWhile_cons]

theorem digits11_nil : parseDigitsC 1 1 [] = none := by
  rw [parseDigitsC_eq 1 1 (by omega)]; rfl

theorem digits_all (q : Bytes) :
    ((q.takeWhile isDigitB).take 3 ≠ [] ∧ q.drop ((q.takeWhile isDigitB).take 3).length = []) ↔
      (1 ≤ q.length ∧ q.length ≤ 3 ∧ q.all isDigitB = true) := by
  have hpre := List.takeWhile_append_dropWhile (p := isDigitB) (l := q)
  constructor
  · intro ⟨hne, hdrop⟩
    have h1 : q.length ≤ ((q.takeWhile isDigitB).take 3).length := by
      have := congrArg List.length hdrop
      rw [List.length_drop, List.length_nil] at this; omega
    have h2 : ((q.takeWhile isDigitB).take 3).length ≤ (q.takeWhile isDigitB).length := by
      rw [List.length_take]; omega
    have h3 : ((q.takeWhile isDigitB).take 3).length ≤ 3 := by rw [List.length_take]; omega
    have hdl : (q.dropWhile isDigitB).length = 0 := by
      have := congrArg List.length hpre
      simp only [List.length_append] at this
      omega
    have htw : q.takeWhile isDigitB = q := by
      rw [List.eq_nil_of_length_eq_zero hdl, List.append_nil] at hpre; exact hpre
    have hlen0 : ((q.takeWhile isDigitB).take 3).length ≠ 0 := by
      intro e; exact hne (List.eq_nil_of_length_eq_zero e)
    have hb : (q.takeWhile isDigitB).length = q.length := by rw [htw]
    refine ⟨by omega, by omega, ?_⟩
    rw [List.all_eq_true]
    intro c hc
    rw [← htw] at hc
    exact mem_takeWhile' q c hc
  · intro ⟨h1, h3, hall⟩
    have htw : q.takeWhile isDigitB = q := by
      have := takeWhile_all_stop (q := isDigitB) q [] (fun c hc => (List.all_eq_true.mp hall) c hc)
        (fun c hc => by simp at hc)
      simpa using this
    rw [htw, List.take_of_length_le h3]
    refine ⟨fun e => by rw [e] at h1; simp at h1, by simp⟩

theorem pow10_nonneg (n : Nat) : (0 : Int) ≤ 10 ^ n := by
  induction n with
  | zero => decide
  | succ n ih => rw [Int.pow_succ]; exact Int.mul_nonneg ih (by decide)

theorem digitsVal_bound (ds : Bytes) (h : ∀ c ∈ ds, isDigitB c = true) :
    0 ≤ digitsVal ds ∧ digitsVal ds < 10 ^ ds.length := by
  unfold digitsVal
  suffices ∀ a : Int, 0 ≤ a →
      0 ≤ ds.foldl (fun acc c => acc * 10 + ((c.toNat - 48 : Nat) : Int)) a ∧
      ds.foldl (fun acc c => acc * 10 + ((c.toNat - 48 : Nat) : Int)) a < (a + 1) * 10 ^ ds.length by
    have := this 0 (Int.le_refl _); simpa using this
  induction ds with
  | nil => intro a ha; simp; omega
  | cons c r ih =>
    intro a ha
    have hc := h c (by simp)
    simp only [isDigitB, inR, Bool.and_eq_true, decide_eq_true_eq] at hc
    simp only [List.foldl_cons, List.length_cons]
    have := ih (fun x hx => h x (by simp [hx])) (a * 10 + ((c.toNat - 48 : Nat) : Int))
      (by have := Int.natCast_nonneg (c.toNat - 48); omega)
    refine ⟨this.1, ?_⟩
    have hv : ((c.toNat - 48 : Nat) : Int) ≤ 9 := by omega
    have hp : (0 : Int) ≤ 10 ^ r.length := pow10_nonneg r.length
    have h2 : (a * 10 + ((c.toNat - 48 : Nat) : Int) + 1) * 10 ^ r.length ≤ (a * 10 + 10) * 10 ^ r.length :=
      Int.mul_le_mul_of_nonneg_right (by omega) hp
    have h3 : (a * 10 + 10) * 10 ^ r.length = (a + 1) * 10 ^ (r.length + 1) := by
      rw [Int.pow_succ, show a * 10 + 10 = (a + 1) * 10 by omega, Int.mul_assoc, Int.mul_comm 10]
    rw [← h3]
    exact Int.lt_of_lt_of_le this.2 h2

theorem dayPart_eq (julian : Bool) (q : Bytes) :
    (if ¬(1 ≤ q.length ∧ q.length ≤ 3 ∧ q.all isDigitB) then
        (.error (.valueError "~Invalid dst start/end date:") : Py TRule)
      else dayOffsetNew (digitsVal q) julian) =
    match (do let (day, p) ← parseDigitsC 1 3 q; pure (RuleDate.day julian day, p) : Option (RuleDate × Bytes)) with
    | some (.cal m w d, []) => calendarOffsetNew m w d
    | some (.day j d, []) => dayOffsetNew d j
    | _ => .error (.valueError "~Invalid dst start/end date:") := by
  rw [parseDigitsC_eq 1 3 (by omega)]
  have hda := digits_all q
  by_cases hc : 1 ≤ q.length ∧ q.length ≤ 3 ∧ q.all isDigitB = true
  · obtain ⟨hne, hdrop⟩ := hda.mpr hc
    have hlen : ¬ ((q.takeWhile isDigitB).take 3).length < 1 := by
      intro e; apply hne; exact List.eq_nil_of_length_eq_zero (by omega)
    have hq : (q.takeWhile isDigitB).take 3 = q := by
      have htw : q.takeWhile isDigitB = q := by
        have := takeWhile_all_stop (q := isDigitB) q [] (fun c hc' => (List.all_eq_true.mp hc.2.2) c hc')
          (fun c h => by simp at h)
        simpa using this
      rw [htw, List.take_of_length_le hc.2.1]
    simp only [hc, and_self, not_true_eq_false, ite_false, hlen, bind, Option.bind, pure, hdrop]
    rw [hq]
  · simp only [hc, not_false_eq_true, ite_true]
    by_cases hl : ((q.takeWhile isDigitB).take 3).length < 1
    · simp only [hl, ite_true, bind, Option.bind]
    · have hd : q.drop ((q.takeWhile isDigitB).take 3).length ≠ [] := fun e =>
        hc (hda.mp ⟨fun e' => by rw [e'] at hl; simp at hl, e⟩)
      simp only [hl, ite_false, bind, Option.bind, pure]
      generalize q.drop ((q.takeWhile isDigitB).take 3).length = rest at hd ⊢
      cases rest with
      | nil => exact absurd rfl hd
      | cons _ _ => rfl

theorem datePy_eq (date : Bytes) :
    parseDatePy date = match parseRuleDateC date with
      | some (.cal m w d, []) => calendarOffsetNew m w d
      | some (.day j d, []) => dayOffsetNew d j
      | _ => .error (.valueError "~Invalid dst start/end date:") := by
  unfold parseDatePy parseRuleDateC
  cases date with
  | nil =>
    simp [peek, parseDigitsC_eq 1 3 (by omega), bind, Option.bind]
  | cons c q =>
    by_cases h77 : c = 77
    · subst h77
      simp only [List.take_succ_cons, List.take_zero, ite_true, peek, List.headD_cons, List.tail_cons]
      unfold reMonthRule
      simp only [bind, Option.bind]
      rw [parseDigitsC_eq 1 2 (by omega)]
      simp only
      by_cases hms : (q.takeWhile isDigitB).take 2 = []
      · simp [hms]
      · have hlen : ¬ ((q.takeWhile isDigitB).take 2).length < 1 := by
          intro e; apply hms; exact List.eq_nil_of_length_eq_zero (by omega)
        simp only [hms, ite_false, hlen]
        generalize q.drop ((q.takeWhile isDigitB).take 2).length = r1
        generalize (q.takeWhile isDigitB).take 2 = ms
        match r1 with
        | [] => simp [peek]
        | e :: r2 =>
          by_cases he : e = 46
          · subst he
            simp only [peek, List.headD_cons, ne_eq, not_true_eq_false, ite_false, List.tail_cons]
            match r2 with
            | [] => simp [digits11_nil]
            | w :: r3 =>
              rw [digits11]
              by_cases hw : isDigitB w = true
              · simp only [hw, ite_true]
                match r3 with
                | [] => simp [peek]
                | f :: r4 =>
                  by_cases hf : f = 46
                  · subst hf
                    simp only [peek, List.headD_cons, not_true_eq_false, ite_false, List.tail_cons]
                    match r4 with
                    | [] => simp [digits11_nil]
                    | d :: r5 =>
                      rw [digits11]
                      by_cases hd : isDigitB d = true
                      · cases r5 <;> simp [hd, hw]
                      · cases r5 <;> simp [hd]
                  · simp [peek, hf]
              · rcases r3 with _ | ⟨f, _ | ⟨d, _ | ⟨g, r⟩⟩⟩
                · simp [hw]
                · simp [hw]
                · by_cases hf : f = 46
                  · subst hf; simp [hw]
                  · simp [hw, hf]
                · simp [hw]
          · simp [peek, he]
    · have hc : ¬ ((c :: q).take 1 = [77]) := by simp [h77]
      simp only [hc, ite_false, peek, List.headD_cons, h77]
      by_cases h74 : c = 74
      · subst h74
        simp only [List.take_succ_cons, List.take_zero, ite_true, List.drop_succ_cons, List.drop_zero,
          List.tail_cons]
        exact dayPart_eq true q
      · have hc' : ¬ ((c :: q).take 1 = [74]) := by simp [h74]
        simp only [hc', ite_false, h74]
        exact dayPart_eq false (c :: q)

theorem splitFirst_decomp (z : UInt8) (x : Bytes) :
    x = (splitFirst z x).1 ++ ((splitFirst z x).2.map (z :: ·)).getD [] ∧ z ∉ (splitFirst z x).1 := by
  unfold splitFirst
  induction x with
  | nil => simp
  | cons c r ih =>
    by_cases hc : c = z
    · subst hc; simp [List.findIdx?_cons]
    · have hne : (c == z) = false := by simp [hc]
      simp only [List.findIdx?_cons, hne, Bool.false_eq_true, ite_false]
      cases h : r.findIdx? (· == z) with
      | none =>
        simp only [h] at ih
        simp only [Option.map_none, Option.getD_none, List.append_nil, List.mem_cons, not_or]
        refine ⟨trivial, Ne.symm hc, by simpa using ih.2⟩
      | some i =>
        simp only [h] at ih
        simp only [Option.map_some, Option.getD_some, List.take_succ_cons, List.drop_succ_cons,
          List.cons_append, List.mem_cons, not_or]
        simp only [Option.map_some, Option.getD_some] at ih
        exact ⟨by rw [← ih.1], Ne.symm hc, ih.2⟩

theorem digits_drop (min max : Nat) (hm : min ≤ max) (p : Bytes) (v : Int) (r : Bytes)
    (h : parseDigitsC min max p = some (v, r)) : ∃ k, r = p.drop k := by
  rw [parseDigitsC_eq _ _ hm] at h
  simp only at h
  split at h
  · cases h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨_, h.2.symm⟩

theorem tail_drop (p : Bytes) : p.tail = p.drop 1 := by cases p <;> rfl

theorem ruleDate_drop (p : Bytes) (dt : RuleDate) (r : Bytes) (h : parseRuleDateC p = some (dt, r)) :
    ∃ k, r = p.drop k := by
  unfold parseRuleDateC at h
  split at h
  · simp only [bind, Option.bind] at h
    split at h
    · cases h
    · rename_i v1 h1
      obtain ⟨k1, e1⟩ := digits_drop 1 2 (by omega) _ _ _ h1
      simp only at h
      split at h
      · cases h
      · split at h
        · cases h
        · rename_i v2 h2
          obtain ⟨k2, e2⟩ := digits_drop 1 1 (by omega) _ _ _ h2
          simp only at h
          split at h
          · cases h
          · split at h
            · cases h
            · rename_i v3 h3
              obtain ⟨k3, e3⟩ := digits_drop 1 1 (by omega) _ _ _ h3
              simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨-, rfl⟩ := h
              refine ⟨1 + k1 + 1 + k2 + 1 + k3, ?_⟩
              rw [e3, tail_drop, e2, tail_drop, e1, tail_drop]
              simp only [List.drop_drop]
  · simp only [bind, Option.bind] at h
    split at h
    · cases h
    · rename_i v1 h1
      obtain ⟨k1, e1⟩ := digits_drop 1 3 (by omega) _ _ _ h1
      simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      split at e1
      · exact ⟨1 + k1, by rw [e1, tail_drop, List.drop_drop]⟩
      · exact ⟨k1, e1⟩

theorem cal_valid (m w d h mi s : Int) (hmi : -99 ≤ mi ∧ mi ≤ 99) (hs : -99 ≤ s ∧ s ≤ 99) :
    calendarruleNew m w d h mi s =
      match calendarOffsetNew m w d with
      | .ok off => if h < -167 ∨ h > 167 then none else some (off.setTime (h, mi, s))
      | .error _ => none := by
  unfold calendarruleNew calendarOffsetNew
  by_cases h1 : 1 ≤ m ∧ m ≤ 12
  · have h1' : ¬ (m < 1 ∨ m > 12) := by omega
    simp only [h1, h1', not_true_eq_false, ite_false, and_self]
    by_cases h2 : 1 ≤ w ∧ w ≤ 5
    · have h2' : ¬ (w < 1 ∨ w > 5) := by omega
      simp only [h2, h2', not_true_eq_false, ite_false, and_self]
      by_cases h3 : 0 ≤ d ∧ d ≤ 6
      · have h3' : ¬ (d < 0 ∨ d > 6) := by omega
        simp only [h3, h3', not_true_eq_false, ite_false, and_self]
        by_cases h4 : h < -167 ∨ h > 167
        · simp [h4]
        · simp only [h4, ite_false, TRule.setTime]
          rw [wrapU8_id m (by omega) (by omega), wrapU8_id w (by omega) (by omega),
            wrapU8_id d (by omega) (by omega), wrapS16_id h (by omega) (by omega),
            wrapS8_id mi (by omega) (by omega), wrapS8_id s (by omega) (by omega)]
      · have h3' : (d < 0 ∨ d > 6) := by omega
        simp only [h3, h3', not_false_eq_true, ite_true, and_self, not_true_eq_false, ite_false]
    · have h2' : (w < 1 ∨ w > 5) := by omega
      simp only [h2, h2', not_false_eq_true, ite_true, and_self, not_true_eq_false, ite_false]
  · have h1' : (m < 1 ∨ m > 12) := by omega
    simp only [h1, h1', not_false_eq_true, ite_true, and_self, not_true_eq_false, ite_false]

theorem day_valid (j : Bool) (d h mi s : Int) (hmi : -99 ≤ mi ∧ mi ≤ 99) (hs : -99 ≤ s ∧ s ≤ 99) :
    dayruleNew j d h mi s =
      match dayOffsetNew d j with
      | .ok off => if h < -167 ∨ h > 167 then none else some (off.setTime (h, mi, s))
      | .error _ => none := by
  unfold dayruleNew dayOffsetNew
  by_cases h1 : (if j then (1 : Int) else 0) ≤ d ∧ d ≤ 365
  · have h1' : ¬ (d < (if j then (1 : Int) else 0) ∨ d > 365) := by omega
    simp only [h1, h1', not_true_eq_false, ite_false, and_self]
    by_cases h4 : h < -167 ∨ h > 167
    · simp [h4]
    · simp only [h4, ite_false, TRule.setTime]
      have hd : 0 ≤ d := by split at h1 <;> omega
      rw [wrapS16_id d (by omega) (by omega), wrapU16_id d (by omega) (by omega),
        wrapS16_id h (by omega) (by omega), wrapS8_id mi (by omega) (by omega),
        wrapS8_id s (by omega) (by omega)]
  · have h1' : (d < (if j then (1 : Int) else 0) ∨ d > 365) := by omega
    simp only [h1, h1', not_false_eq_true, ite_true, and_self, not_true_eq_false, ite_false]

/-- C's rule when it consumes the whole segment. -/
def cRuleExact (x : Bytes) : Option TRule :=
  match parseTransRuleC x with
  | some (r, []) => some r
  | _ => none

theorem time_vals (t : Bytes) (o : Option UInt8 × Bytes × Option Bytes × Option Bytes) (ho : reOff t = some (o, [])) :
    parseTransTimeC 0 0 t = some ((digitsVal o.2.1 * sgnOf o.1, (o.2.2.1.map digitsVal).getD 0 * sgnOf o.1,
      (o.2.2.2.map digitsVal).getD 0 * sgnOf o.1), []) ∧
    reTime t = some (decide (o.1 = some 45), digitsVal o.2.1, (o.2.2.1.map digitsVal).getD 0,
      (o.2.2.2.map digitsVal).getD 0) := by
  have hs := reOff_shape t _ _ ho
  obtain ⟨sg, hd, mm, ss⟩ := o
  refine ⟨?_, by unfold reTime; rw [ho]⟩
  rw [time_eq, ho]
  rcases mm with _ | m <;> rcases ss with _ | sv
  · simp [peek]
  · exact absurd (hs.2.2.2.2.2.2 rfl) (by simp)
  · simp [peek]
  · simp

theorem two_digits_bound (m : Bytes) (h : ∃ a b, m = [a, b] ∧ isDigitB a = true ∧ isDigitB b = true) :
    0 ≤ digitsVal m ∧ digitsVal m ≤ 99 := by
  obtain ⟨a, b, rfl, ha, hb⟩ := h
  have := digitsVal_bound [a, b] (by simp [ha, hb])
  simp at this; omega

theorem rule_eq (x : Bytes) : cRuleExact x = (parseDstStartEndPy x).toOption := by
  have hdec := splitFirst_decomp 47 x
  unfold cRuleExact parseTransRuleC parseDstStartEndPy
  generalize hsp : splitFirst 47 x = sp at hdec
  obtain ⟨date, tm⟩ := sp
  simp only at hdec ⊢
  obtain ⟨hx, hnot⟩ := hdec
  have hS : ZTail 47 ((tm.map (47 :: ·)).getD []) := by
    cases tm with
    | none => exact .inl rfl
    | some t => exact .inr ⟨t, rfl⟩
  rw [hx, ruleDate_tail date _ hS, datePy_eq date]
  simp only [bind, Option.bind]
  cases hd : parseRuleDateC date with
  | none => simp [Except.toOption, Except.bind]
  | some dr =>
    obtain ⟨dt, rest⟩ := dr
    simp only [Option.map_some]
    by_cases hr : rest = []
    · subst hr
      simp only [List.nil_append]
      cases tm with
      | none =>
        simp only [Option.map_none, Option.getD_none, peek, List.headD_nil]
        simp only [show ¬ ((0 : UInt8) = 47) by decide, ite_false]
        cases dt with
        | cal m w d =>
          simp only
          rw [cal_valid m w d 2 0 0 (by omega) (by omega)]
          cases hco : calendarOffsetNew m w d with
          | error e => simp [Except.toOption, Except.bind, bind]
          | ok off =>
            have hoff : off.setTime (2, 0, 0) = off := by
              unfold calendarOffsetNew at hco
              split at hco
              · cases hco
              · split at hco
                · cases hco
                · split at hco
                  · cases hco
                  · cases hco; rfl
            simp [Except.toOption, Except.bind, bind, pure, Except.pure, hoff]
        | day j d =>
          simp only
          rw [day_valid j d 2 0 0 (by omega) (by omega)]
          cases hco : dayOffsetNew d j with
          | error e => simp [Except.toOption, Except.bind, bind]
          | ok off =>
            have hoff : off.setTime (2, 0, 0) = off := by
              unfold dayOffsetNew at hco
              by_cases hc : (if j then (1 : Int) else 0) ≤ d ∧ d ≤ 365
              · simp only [hc, and_self, not_true_eq_false, ite_false, Except.ok.injEq] at hco
                subst hco; rfl
              · simp only [hc, not_false_eq_true, ite_true] at hco
                cases hco
            simp [Except.toOption, Except.bind, bind, pure, Except.pure, hoff]
      | some t =>
        simp only [Option.map_some, Option.getD_some, peek, List.headD_cons, ite_true, List.tail_cons]
        cases ho : reOff t with
        | none =>
          have hC : parseTransTimeC 0 0 t = none := by rw [time_eq, ho]
          have hP : reTime t = none := by unfold reTime; rw [ho]
          simp only [hC, parseTransitionTimePy, hP]
          cases dt with
          | cal m w d => cases hco : calendarOffsetNew m w d <;> simp [hco, Except.toOption, bind, Except.bind]
          | day j d => cases hco : dayOffsetNew d j <;> simp [hco, Except.toOption, bind, Except.bind]
        | some or_ =>
          obtain ⟨o, r'⟩ := or_
          by_cases hr' : r' = []
          · subst hr'
            obtain ⟨hC, hP⟩ := time_vals t o ho
            have hs := reOff_shape t _ _ ho
            have hmb : -99 ≤ (o.2.2.1.map digitsVal).getD 0 * sgnOf o.1 ∧
                (o.2.2.1.map digitsVal).getD 0 * sgnOf o.1 ≤ 99 := by
              cases hm : o.2.2.1 with
              | none => simp
              | some m =>
                have := two_digits_bound m (hs.2.2.2.2.1 m hm)
                simp only [Option.map_some, Option.getD_some]
                unfold sgnOf; split <;> omega
            have hsb : -99 ≤ (o.2.2.2.map digitsVal).getD 0 * sgnOf o.1 ∧
                (o.2.2.2.map digitsVal).getD 0 * sgnOf o.1 ≤ 99 := by
              cases hm : o.2.2.2 with
              | none => simp
              | some m =>
                have := two_digits_bound m (hs.2.2.2.2.2.1 m hm)
                simp only [Option.map_some, Option.getD_some]
                unfold sgnOf; split <;> omega
            have hH := digitsVal_nonneg o.2.1
            simp only [hC, parseTransitionTimePy, hP]
            have hsg : sgnOf o.1 = if decide (o.1 = some 45) = true then -1 else 1 := by
              unfold sgnOf; by_cases e : o.1 = some 45 <;> simp [e]
            cases dt with
            | cal m w d =>
              simp only
              rw [cal_valid _ _ _ _ _ _ hmb hsb]
              cases hco : calendarOffsetNew m w d with
              | error e => simp [Except.toOption, bind, Except.bind]
              | ok off =>
                simp only [bind, Except.bind]
                by_cases h167 : digitsVal o.2.1 > 167
                · have : digitsVal o.2.1 * sgnOf o.1 < -167 ∨ digitsVal o.2.1 * sgnOf o.1 > 167 := by
                    unfold sgnOf; split <;> omega
                  simp [this, h167, Except.toOption]
                · have : ¬ (digitsVal o.2.1 * sgnOf o.1 < -167 ∨ digitsVal o.2.1 * sgnOf o.1 > 167) := by
                    unfold sgnOf; split <;> omega
                  simp only [this, ite_false, h167, Except.toOption, pure, Except.pure]
                  rw [hsg]
                  by_cases e : decide (o.1 = some 45) = true <;> simp [e]
            | day j d =>
              simp only
              rw [day_valid _ _ _ _ _ hmb hsb]
              cases hco : dayOffsetNew d j with
              | error e => simp [Except.toOption, bind, Except.bind]
              | ok off =>
                simp only [bind, Except.bind]
                by_cases h167 : digitsVal o.2.1 > 167
                · have : digitsVal o.2.1 * sgnOf o.1 < -167 ∨ digitsVal o.2.1 * sgnOf o.1 > 167 := by
                    unfold sgnOf; split <;> omega
                  simp [this, h167, Except.toOption]
                · have : ¬ (digitsVal o.2.1 * sgnOf o.1 < -167 ∨ digitsVal o.2.1 * sgnOf o.1 > 167) := by
                    unfold sgnOf; split <;> omega
                  simp only [this, ite_false, h167, Except.toOption, pure, Except.pure]
                  rw [hsg]
                  by_cases e : decide (o.1 = some 45) = true <;> simp [e]
          · have hP : reTime t = none := by
              unfold reTime; rw [ho]
              cases r' with
              | nil => exact absurd rfl hr'
              | cons _ _ => rfl
            have hC : ∀ v, parseTransTimeC 0 0 t ≠ some (v, []) := by
              intro v e
              rw [time_eq, ho] at e
              obtain ⟨sg, hd', mm, ss⟩ := o
              rcases mm with _ | m <;> rcases ss with _ | sv <;> simp at e <;>
                (try (split at e <;> simp at e)) <;>
                first | exact hr' e.2.2 | exact hr' e.2 | exact hr' e.2.symm | skip
            simp only [parseTransitionTimePy, hP]
            cases hct : parseTransTimeC 0 0 t with
            | none =>
              cases dt with
              | cal m w d => cases hco : calendarOffsetNew m w d <;> simp [hco, Except.toOption, bind, Except.bind]
              | day j d => cases hco : dayOffsetNew d j <;> simp [hco, Except.toOption, bind, Except.bind]
            | some vr =>
              obtain ⟨v, rv⟩ := vr
              have hrv : rv ≠ [] := fun e => hC v (by rw [hct, e])
              obtain ⟨⟨h1, m1, s1⟩, -⟩ : ∃ q : (Int × Int × Int) × Unit, True := ⟨((0,0,0),()), trivial⟩
              obtain ⟨vh, vm, vs⟩ := v
              cases rv with
              | nil => exact absurd rfl hrv
              | cons c rr =>
                cases dt with
                | cal m w d =>
                  simp only
                  cases hcr : calendarruleNew m w d vh vm vs <;> cases hco : calendarOffsetNew m w d <;>
                    simp [hcr, hco, Except.toOption, bind, Except.bind, Option.bind]
                | day j d =>
                  simp only
                  cases hcr : dayruleNew j d vh vm vs <;> cases hco : dayOffsetNew d j <;>
                    simp [hcr, hco, Except.toOption, bind, Except.bind, Option.bind]
    · -- leftover date characters: Python's pattern fails, C stops before the slash
      obtain ⟨k, hk⟩ := ruleDate_drop date dt rest hd
      have hpk : peek (rest ++ (tm.map (47 :: ·)).getD []) ≠ 47 := by
        cases rest with
        | nil => exact absurd rfl hr
        | cons c r =>
          simp only [peek, List.cons_append, List.headD_cons]
          intro e; subst e
          apply hnot
          have : (47 : UInt8) ∈ date.drop k := by rw [← hk]; simp
          exact List.mem_of_mem_drop this
      have hpy : (match some (dt, rest) with
          | some (.cal m w d, []) => calendarOffsetNew m w d
          | some (.day j d, []) => dayOffsetNew d j
          | _ => (.error (.valueError "~Invalid dst start/end date:") : Py TRule)) =
          .error (.valueError "~Invalid dst start/end date:") := by
        cases rest with
        | nil => exact absurd rfl hr
        | cons _ _ => cases dt <;> rfl
      rw [hpy]
      simp only [hpk, ite_false]
      have hne : rest ++ (tm.map (47 :: ·)).getD [] ≠ [] := by simp [hr]
      generalize rest ++ (tm.map (47 :: ·)).getD [] = rr at hne
      cases rr with
      | nil => exact absurd rfl hne
      | cons c rr =>
        cases dt with
        | cal m w d =>
          simp only
          cases hcr : calendarruleNew m w d 2 0 0 <;> simp [hcr, Except.toOption, Except.bind, bind, Option.bind]
        | day j d =>
          simp only
          cases hcr : dayruleNew j d 2 0 0 <;> simp [hcr, Except.toOption, Except.bind, bind, Option.bind]

/-! Commas after a rule or a time. -/

theorem commaZ (T : Bytes) (h : CommaTail T) : ZTail 44 T := h

theorem time_tail (x T : Bytes) (hT : CommaTail T) :
    parseTransTimeC 0 0 (x ++ T) = (parseTransTimeC 0 0 x).map (fun vr => (vr.1, vr.2 ++ T)) := by
  rw [time_eq, time_eq, reOff_tail x T hT]
  cases reOff x with
  | none => rfl
  | some or_ =>
    obtain ⟨⟨sg, hd, mm, ss⟩, r⟩ := or_
    have hp := peek_tail r T hT 58 (by decide) (by decide)
    rcases mm with _ | m <;> rcases ss with _ | sv <;> simp only [Option.map_some] <;>
      (try simp only [hp]) <;> split <;> simp

theorem rule_tail (x T : Bytes) (hT : CommaTail T) :
    parseTransRuleC (x ++ T) = (parseTransRuleC x).map (fun rr => (rr.1, rr.2 ++ T)) := by
  unfold parseTransRuleC
  rw [ruleDate_tailZ 44 (by decide) (by decide) (by decide) (by decide) x T (commaZ T hT)]
  simp only [bind, Option.bind]
  cases parseRuleDateC x with
  | none => rfl
  | some dr =>
    obtain ⟨dt, rest⟩ := dr
    simp only [Option.map_some]
    have hp := peek_tail rest T hT 47 (by decide) (by decide)
    by_cases h47 : peek rest = 47
    · have hne : rest ≠ [] := by intro e; subst e; simp [peek] at h47
      simp only [hp, h47, ite_true, tail_app rest T hne, time_tail rest.tail T hT]
      cases parseTransTimeC 0 0 rest.tail with
      | none => rfl
      | some vr =>
        obtain ⟨⟨h, mi, s⟩, rv⟩ := vr
        simp only [Option.map_some]
        cases dt <;> simp only <;> split <;> simp_all
    · simp only [hp, h47, ite_false]
      cases dt <;> simp only <;> split <;> simp_all

/-! What a component consumes is ASCII. -/

def Asc (s : Bytes) : Prop := ∀ c ∈ s, c.toNat < 128

theorem asc_utf8 (s : Bytes) (h : Asc s) : utf8Valid s = true := by
  induction s with
  | nil => rfl
  | cons c r ih =>
    have hc := h c (by simp)
    unfold utf8Valid
    rw [if_pos hc]
    exact ih (fun x hx => h x (by simp [hx]))

theorem asc_append (a b : Bytes) (ha : Asc a) (hb : Asc b) : Asc (a ++ b) := by
  intro c hc
  rcases List.mem_append.mp hc with h | h
  · exact ha c h
  · exact hb c h

theorem asc_takeWhile {q : UInt8 → Bool} (hq : ∀ c, q c = true → c.toNat < 128) (l : Bytes) :
    Asc (l.takeWhile q) := fun c hc => hq c (mem_takeWhile' l c hc)

theorem alpha_asc (c : UInt8) (h : isAlphaB c = true) : c.toNat < 128 := by
  unfold isAlphaB inR at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h; omega
theorem digit_asc (c : UInt8) (h : isDigitB c = true) : c.toNat < 128 := by
  unfold isDigitB inR at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h; omega

theorem quoted_asc (c : UInt8) (h : isQuotedB c = true) : c.toNat < 128 := by
  unfold isQuotedB at h
  by_cases ha : isAlphaB c = true
  · exact alpha_asc c ha
  · by_cases hd : isDigitB c = true
    · exact digit_asc c hd
    · simp [ha, hd] at h
      rcases h with rfl | rfl <;> decide

theorem offText_asc (o : Option UInt8 × Bytes × Option Bytes × Option Bytes) (hs : OffShape o) :
    Asc (offText o) := by
  obtain ⟨sg, hd, mm, ss⟩ := o
  obtain ⟨hsg, -, -, hdig, hmm, hss, -⟩ := hs
  unfold offText
  simp only
  refine asc_append _ _ (asc_append _ _ (asc_append _ _ ?_ ?_) ?_) ?_
  · rcases hsg with rfl | rfl | rfl <;> intro c hc <;> simp at hc <;> subst hc <;> decide
  · exact fun c hc => digit_asc c (hdig c hc)
  · cases mm with
    | none => intro c hc; simp at hc
    | some m =>
      obtain ⟨a, b, rfl, ha, hb⟩ := hmm m rfl
      intro c hc; simp at hc
      rcases hc with rfl | rfl | rfl
      · decide
      · exact digit_asc _ ha
      · exact digit_asc _ hb
  · cases ss with
    | none => intro c hc; simp at hc
    | some m =>
      obtain ⟨a, b, rfl, ha, hb⟩ := hss m rfl
      intro c hc; simp at hc
      rcases hc with rfl | rfl | rfl
      · decide
      · exact digit_asc _ ha
      · exact digit_asc _ hb

theorem delta_bound (o : Option UInt8 × Bytes × Option Bytes × Option Bytes) (hs : OffShape o) (v : Int)
    (h : parseTzDeltaPy (offText o) = .ok v) : -92439 ≤ v ∧ v ≤ 92439 := by
  unfold parseTzDeltaPy at h
  rw [reTime_offText o hs] at h
  simp only at h
  have hH := digitsVal_nonneg o.2.1
  have hm : 0 ≤ (o.2.2.1.map digitsVal).getD 0 ∧ (o.2.2.1.map digitsVal).getD 0 ≤ 99 := by
    cases e : o.2.2.1 with
    | none => simp
    | some m => simpa using two_digits_bound m (hs.2.2.2.2.1 m e)
  have hsx : 0 ≤ (o.2.2.2.map digitsVal).getD 0 ∧ (o.2.2.2.map digitsVal).getD 0 ≤ 99 := by
    cases e : o.2.2.2 with
    | none => simp
    | some m => simpa using two_digits_bound m (hs.2.2.2.2.2.1 m e)
  split at h
  · cases h
  · split at h <;> simp only [Except.ok.injEq] at h <;> omega

theorem pre_take (q : UInt8 → Bool) (k : Nat) : ∀ s : Bytes,
    (s.takeWhile q).take k ++ s.drop ((s.takeWhile q).take k).length = s := by
  intro s
  induction s generalizing k with
  | nil => simp
  | cons c r ih =>
    rw [List.takeWhile_cons]
    split
    · cases k with
      | zero => simp
      | succ k =>
        simp only [List.take_succ_cons, List.length_cons, List.drop_succ_cons, List.cons_append]
        rw [ih k]
    · simp

theorem pre_take_asc (q : UInt8 → Bool) (hq : ∀ c, q c = true → c.toNat < 128) (k : Nat) (s : Bytes) :
    Asc ((s.takeWhile q).take k) := fun c hc => hq c (mem_takeWhile' s c (List.mem_of_mem_take hc))

theorem digits_dec (min max : Nat) (hm : min ≤ max) (p : Bytes) (v : Int) (r : Bytes)
    (h : parseDigitsC min max p = some (v, r)) : ∃ pre, p = pre ++ r ∧ Asc pre := by
  rw [parseDigitsC_eq _ _ hm] at h
  simp only at h
  split at h
  · cases h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨_, (pre_take isDigitB max p).symm, pre_take_asc _ digit_asc _ _⟩

theorem reAbbr_dec (s g r : Bytes) (h : reAbbr s = some (g, r)) : s = g ++ r ∧ Asc g := by
  unfold reAbbr at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have := pre_take isAlphaB (s.takeWhile isAlphaB).length s
    rw [List.take_of_length_le (Nat.le_refl _)] at this
    exact ⟨this.symm, asc_takeWhile alpha_asc s⟩
  · split at h
    · rename_i h60
      simp only at h
      split at h
      · rename_i hc
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hs : s = 60 :: s.tail := by
          cases s with
          | nil => simp [peek] at h60
          | cons c t => simp [peek] at h60; simp [h60]
        have hpre := pre_take isQuotedB (s.tail.takeWhile isQuotedB).length s.tail
        rw [List.take_of_length_le (Nat.le_refl _)] at hpre
        obtain ⟨d, hd⟩ : ∃ d, s.tail.drop (s.tail.takeWhile isQuotedB).length = 62 :: d := by
          generalize s.tail.drop (s.tail.takeWhile isQuotedB).length = w at hc
          cases w with
          | nil => simp [peek] at hc
          | cons a w => simp [peek] at hc; exact ⟨w, by rw [hc.2]⟩
        refine ⟨?_, ?_⟩
        · rw [drop_succ_of _ _ _ _ hd]
          conv => lhs; rw [hs, ← hpre, hd]
          simp
        · apply asc_append _ _ (asc_append _ _ (fun c hc => by simp at hc; subst hc; decide)
            (asc_takeWhile quoted_asc _)) (fun c hc => by simp at hc; subst hc; decide)
      · cases h
    · cases h

theorem reOff_dec (s : Bytes) (o : Option UInt8 × Bytes × Option Bytes × Option Bytes) (r : Bytes)
    (h : reOff s = some (o, r)) : s = offText o ++ r := by
  have hsh := reOff_shape s o r h
  unfold reOff at h
  obtain ⟨sgo, s1, hs, hdec⟩ : ∃ (sgo : Option UInt8) (s1 : Bytes),
      ((if peek s = 43 ∨ peek s = 45 then (some (peek s), s.tail) else (none, s)) : Option UInt8 × Bytes)
        = (sgo, s1) ∧ s = sgo.toList ++ s1 := by
    by_cases hc : peek s = 43 ∨ peek s = 45
    · refine ⟨some (peek s), s.tail, by simp [hc], ?_⟩
      cases s with
      | nil => simp [peek] at hc
      | cons c t => simp [peek, Option.toList]
    · exact ⟨none, s, by simp [hc], by simp [Option.toList]⟩
  rw [hs] at h
  simp only at h
  have hpre := pre_take isDigitB 3 s1
  generalize (s1.takeWhile isDigitB).take 3 = ds at h hpre hsh
  split at h
  · cases h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [hdec]; unfold offText; simp only [Option.map_none, Option.getD_none, List.append_nil]
      rw [List.append_assoc, hpre]
    · rename_i mm s3 hm
      obtain ⟨a, b, rfl, -, -, hm2⟩ := reColon2_some _ _ _ hm
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [hdec]; unfold offText
        simp only [Option.map_some, Option.getD_some, Option.map_none, Option.getD_none, List.append_nil,
          List.singleton_append]
        rw [← hpre, hm2]; simp
      · rename_i ss s4 hss
        obtain ⟨c, d, rfl, -, -, hs2⟩ := reColon2_some _ _ _ hss
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [hdec]; unfold offText
        simp only [Option.map_some, Option.getD_some, List.singleton_append]
        rw [← hpre, hm2, hs2]; simp

theorem time_dec (t : Bytes) (v : Int × Int × Int) (r : Bytes) (h : parseTransTimeC 0 0 t = some (v, r)) :
    ∃ pre, t = pre ++ r ∧ Asc pre := by
  rw [time_eq] at h
  cases ho : reOff t with
  | none => rw [ho] at h; cases h
  | some or_ =>
    obtain ⟨o, r'⟩ := or_
    rw [ho] at h
    have hr : r' = r := by
      obtain ⟨sg, hd, mm, ss⟩ := o
      rcases mm with _ | m <;> rcases ss with _ | sv <;> simp at h <;>
        (try (split at h <;> simp at h)) <;>
        first | exact h.2 | exact h.2.2 | skip
    subst hr
    exact ⟨offText o, reOff_dec t o r' ho, offText_asc o (reOff_shape t o r' ho)⟩

theorem asc_cons (c : UInt8) (hc : c.toNat < 128) (l : Bytes) (hl : Asc l) : Asc (c :: l) := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | h
  · exact hc
  · exact hl x h

theorem peek_cons (p : Bytes) (c : UInt8) (hc : c ≠ 0) (h : peek p = c) : p = c :: p.tail := by
  cases p with
  | nil => simp [peek] at h; exact absurd h.symm hc
  | cons a r => simp [peek] at h; simp [h]

theorem ruleDate_dec (p : Bytes) (dt : RuleDate) (r : Bytes) (h : parseRuleDateC p = some (dt, r)) :
    ∃ pre, p = pre ++ r ∧ Asc pre := by
  unfold parseRuleDateC at h
  split at h
  · rename_i h77
    have hp := peek_cons p 77 (by decide) h77
    simp only [bind, Option.bind] at h
    split at h
    · cases h
    · rename_i v1 h1
      obtain ⟨pre1, e1, a1⟩ := digits_dec 1 2 (by omega) _ _ _ h1
      simp only at h
      split at h
      · cases h
      · rename_i h46
        simp only [ne_eq, Decidable.not_not] at h46
        have hr1 := peek_cons _ 46 (by decide) h46
        split at h
        · cases h
        · rename_i v2 h2
          obtain ⟨pre2, e2, a2⟩ := digits_dec 1 1 (by omega) _ _ _ h2
          simp only at h
          split at h
          · cases h
          · rename_i h46'
            simp only [ne_eq, Decidable.not_not] at h46'
            have hr2 := peek_cons _ 46 (by decide) h46'
            split at h
            · cases h
            · rename_i v3 h3
              obtain ⟨pre3, e3, a3⟩ := digits_dec 1 1 (by omega) _ _ _ h3
              simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨-, rfl⟩ := h
              refine ⟨77 :: pre1 ++ 46 :: pre2 ++ 46 :: pre3, ?_, ?_⟩
              · rw [hp, e1, hr1, e2, hr2, e3]; simp
              · exact asc_append _ _ (asc_append _ _ (asc_cons 77 (by decide) _ a1)
                  (asc_cons 46 (by decide) _ a2)) (asc_cons 46 (by decide) _ a3)
  · simp only [bind, Option.bind] at h
    split at h
    · cases h
    · rename_i v1 h1
      obtain ⟨pre1, e1, a1⟩ := digits_dec 1 3 (by omega) _ _ _ h1
      simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      split at e1
      · rename_i h74
        simp only at e1
        have hp := peek_cons p 74 (by decide) h74
        refine ⟨74 :: pre1, by rw [hp, e1]; simp, ?_⟩
        intro c hc; simp only [List.mem_cons] at hc
        rcases hc with rfl | hc
        · decide
        · exact a1 c hc
      · simp only at e1
        exact ⟨pre1, e1, a1⟩

theorem obind_some {α β : Type} {x : Option α} {f : α → Option β} {b : β} (h : (x >>= f) = some b) :
    ∃ a, x = some a ∧ f a = some b := by
  cases x with
  | none => cases h
  | some a => exact ⟨a, rfl, h⟩

theorem rule_dec (p : Bytes) (rr : TRule) (r : Bytes) (h : parseTransRuleC p = some (rr, r)) :
    ∃ pre, p = pre ++ r ∧ Asc pre := by
  unfold parseTransRuleC at h
  obtain ⟨⟨dt, rest⟩, hd, h⟩ := obind_some h
  obtain ⟨pre1, e1, a1⟩ := ruleDate_dec _ _ _ hd
  simp only at h
  split at h
  · rename_i h47
    have hp := peek_cons rest 47 (by decide) h47
    obtain ⟨⟨⟨h', mi, s⟩, rt⟩, ht, h⟩ := obind_some h
    obtain ⟨pre2, e2, a2⟩ := time_dec _ _ _ ht
    have hrt : r = rt := by
      cases dt <;> simp only at h <;> obtain ⟨rv, -, h⟩ := obind_some h <;>
        simp only [pure, Option.some.injEq, Prod.mk.injEq] at h <;> exact h.2.symm
    subst hrt
    refine ⟨pre1 ++ 47 :: pre2, by rw [e1, hp, e2]; simp, ?_⟩
    exact asc_append _ _ a1 (asc_cons 47 (by decide) _ a2)
  · obtain ⟨_, ht, h⟩ := obind_some h
    simp only [Option.some.injEq] at ht
    subst ht
    have hrt : r = rest := by
      cases dt <;> simp only at h <;> obtain ⟨rv, -, h⟩ := obind_some h <;>
        simp only [pure, Option.some.injEq, Prod.mk.injEq] at h <;> exact h.2.symm
    subst hrt
    exact ⟨pre1, e1, a1⟩

/-! The whole footer. -/

/-- The C rule a Python result describes. -/
def afterToC : After → CRule
  | .tti t => ⟨t, default, 0, none, none, true⟩
  | .tzstr z => ⟨z.std, z.dst, z.dstDiff, some z.start, some z.end, false⟩

theorem cAbbr_tail (x T : Bytes) (hT : CommaTail T) :
    parseAbbrC (x ++ T) = (reAbbr x).map (fun gr => (stripAngle gr.1, gr.2 ++ T)) := by
  rw [abbr_eq, reAbbr_tail x T hT]
  cases reAbbr x <;> rfl

theorem cDelta_tail (x T : Bytes) (hT : CommaTail T) :
    parseTzDeltaC (x ++ T) = (parseTzDeltaC x).map (fun vr => (vr.1, vr.2 ++ T)) := by
  rw [delta_eq, delta_eq, reOff_tail x T hT]
  cases reOff x with
  | none => rfl
  | some or_ =>
    obtain ⟨o, r⟩ := or_
    have hp := peek_tail r T hT 58 (by decide) (by decide)
    simp only [Option.map_some, hp]
    split
    · rfl
    · cases parseTzDeltaPy (offText o) <;> rfl

theorem delta_nil : parseTzDeltaC [] = none := by
  rw [delta_eq]; rfl

theorem delta_comma (t : Bytes) : parseTzDeltaC (44 :: t) = none := by
  rw [delta_eq]
  unfold reOff
  simp [peek, isDigitB, inR]

theorem abbr_comma (t : Bytes) : reAbbr (44 :: t) = none := by
  unfold reAbbr; simp [peek, isAlphaB, inR]

theorem abbr_colon (t : Bytes) : reAbbr (58 :: t) = none := by
  unfold reAbbr; simp [peek, isAlphaB, inR]

theorem pyDelta_ok (o : Option UInt8 × Bytes × Option Bytes × Option Bytes) (hs : OffShape o) :
    ∀ e, parseTzDeltaPy (offText o) = .error e → ∃ m, e = .valueError m := by
  intro e h
  unfold parseTzDeltaPy at h
  rw [reTime_offText o hs] at h
  simp only at h
  split at h
  · simp only [Except.error.injEq] at h; exact ⟨_, h.symm⟩
  · split at h <;> cases h

theorem suffix_ne44 (off r : Bytes) (h44 : (44 : UInt8) ∉ off) (k : Nat) (hk : r = off.drop k) (hr : r ≠ []) :
    peek r ≠ 44 := by
  cases r with
  | nil => exact absurd rfl hr
  | cons c t =>
    simp only [peek, List.headD_cons]
    intro e; subst e
    exact h44 (List.mem_of_mem_drop (by rw [← hk]; simp))

theorem peek_ne_of_not_mem (r : Bytes) (c : UInt8) (h : c ∉ r) (hr : r ≠ []) : peek r ≠ c := by
  cases r with
  | nil => exact absurd rfl hr
  | cons a t => simp only [peek, List.headD_cons]; intro e; subst e; exact h (by simp)

theorem cRuleExact_some (x : Bytes) (r : TRule) (h : cRuleExact x = some r) : parseTransRuleC x = some (r, []) := by
  unfold cRuleExact at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; assumption
  · cases h

theorem rulePy_ok (x : Bytes) (r : TRule) (h : parseDstStartEndPy x = .ok r) :
    parseTransRuleC x = some (r, []) ∧ Asc x := by
  have he := rule_eq x
  rw [h] at he
  have hc := cRuleExact_some x r he
  obtain ⟨pre, e, a⟩ := rule_dec x r [] hc
  rw [List.append_nil] at e
  exact ⟨hc, e ▸ a⟩

theorem rulePy_err (x : Bytes) (h : ∀ r, parseDstStartEndPy x ≠ .ok r) : cRuleExact x = none := by
  rw [rule_eq x]
  cases hp : parseDstStartEndPy x with
  | error e => rfl
  | ok r => exact absurd hp (h r)

/-- The two rules after the first comma: C's tail of `parse_tz_str` and Python's split. -/
theorem rules_eq (b : Bytes) (h0 : (0 : UInt8) ∉ b) (sa da : Bytes) (so dso : Int) (hb1 : -200000 ≤ so ∧ so ≤ 200000)
    (hb2 : -200000 ≤ dso ∧ dso ≤ 200000) :
    let cres : Py CRule :=
      match parseTransRuleC b with
      | none => .error (tzErrC "Malformed transition rule in TZ string:")
      | some (start, p) =>
        if peek p ≠ 44 then .error (tzErrC "Missing transition rules in TZ string:")
        else
        match parseTransRuleC p.tail with
        | none => .error (tzErrC "Malformed transition rule in TZ string:")
        | some («end», p) =>
          if peek p ≠ 0 then .error (tzErrC "Extraneous characters at end of TZ string:")
          else .ok (buildTzruleC sa (some da) so dso (some start) (some «end»))
    let pres : Py After :=
      match splitFirst 44 b with
      | (a, none) =>
        match parseDstStartEndPy a with
        | .error _ => throw (tzErrPy "Invalid TZ string:")
        | .ok _ => throw (tzErrPy "Invalid TZ string:")
      | (a, some c) =>
        match parseDstStartEndPy a, parseDstStartEndPy c with
        | .ok s, .ok e => pure (.tzstr (mkTZStr sa so da dso s e))
        | _, _ => throw (tzErrPy "Invalid TZ string:")
    cres.toOption = pres.toOption.map afterToC ∧ (∀ e, pres = .error e → e.className = "ValueError") ∧
      (∀ a, pres = .ok a → Asc b) := by
  intro cres pres
  have hdec := splitFirst_decomp 44 b
  generalize hsp : splitFirst 44 b = sp at hdec
  obtain ⟨a, se2⟩ := sp
  simp only at hdec
  obtain ⟨hb, h44⟩ := hdec
  have hT : CommaTail ((se2.map (44 :: ·)).getD []) := by
    cases se2 with
    | none => exact .inl rfl
    | some c => exact .inr ⟨c, rfl⟩
  have hpres_err : ∀ e, pres = .error e → e.className = "ValueError" := by
    intro e h
    simp only [pres, hsp] at h
    cases se2 with
    | none =>
      cases h1 : parseDstStartEndPy a <;> simp [h1, throw, throwThe, MonadExceptOf.throw] at h <;>
        subst h <;> rfl
    | some c =>
      cases h1 : parseDstStartEndPy a <;> cases h2 : parseDstStartEndPy c <;>
        simp [h1, h2, throw, throwThe, MonadExceptOf.throw, pure, Except.pure] at h <;> subst h <;> rfl
  refine ⟨?_, hpres_err, ?_⟩
  · simp only [cres, pres, hsp]
    rw [hb, rule_tail a _ hT]
    cases hca : parseTransRuleC a with
    | none =>
      have hpa : ∀ r, parseDstStartEndPy a ≠ .ok r := fun r e => by
        have := (rulePy_ok a r e).1; rw [hca] at this; cases this
      cases se2 with
      | none => cases h : parseDstStartEndPy a with
        | error _ => simp [h, Except.toOption, throw, throwThe, MonadExceptOf.throw]
        | ok r => exact absurd h (hpa r)
      | some c =>
        cases h : parseDstStartEndPy a with
        | error _ => simp [h, Except.toOption, throw, throwThe, MonadExceptOf.throw]
        | ok r => exact absurd h (hpa r)
    | some rr =>
      obtain ⟨st, rest⟩ := rr
      obtain ⟨pre, epre, -⟩ := rule_dec a st rest hca
      have h44r : (44 : UInt8) ∉ rest := fun hm => h44 (by rw [epre]; simp [hm])
      simp only [Option.map_some]
      by_cases hr : rest = []
      · subst hr
        have hpa : parseDstStartEndPy a = .ok st := by
          have := rule_eq a
          unfold cRuleExact at this
          rw [hca] at this
          cases h : parseDstStartEndPy a with
          | error e => rw [h] at this; cases this
          | ok r => rw [h] at this; simp [Except.toOption] at this; rw [this]
        cases se2 with
        | none =>
          simp [peek, hpa, Except.toOption, throw, throwThe, MonadExceptOf.throw]
        | some c =>
          simp only [List.nil_append, Option.map_some, Option.getD_some, peek, List.headD_cons, ne_eq,
            not_true_eq_false, ite_false, List.tail_cons, hpa]
          cases hcc : parseTransRuleC c with
          | none =>
            have hpc : ∀ r, parseDstStartEndPy c ≠ .ok r := fun r e => by
              have := (rulePy_ok c r e).1; rw [hcc] at this; cases this
            cases h : parseDstStartEndPy c with
            | error _ => simp [h, Except.toOption, throw, throwThe, MonadExceptOf.throw]
            | ok r => exact absurd h (hpc r)
          | some rr2 =>
            obtain ⟨en, rest2⟩ := rr2
            by_cases hr2 : rest2 = []
            · subst hr2
              have hpc : parseDstStartEndPy c = .ok en := by
                have := rule_eq c
                unfold cRuleExact at this
                rw [hcc] at this
                cases h : parseDstStartEndPy c with
                | error e => rw [h] at this; cases this
                | ok r => rw [h] at this; simp [Except.toOption] at this; rw [this]
              simp only [peek, List.headD_nil, ne_eq, not_true_eq_false, ite_false, hpc, Except.toOption,
                pure, Except.pure, Option.map_some, afterToC, buildTzruleC, mkTZStr, Option.some.injEq]
              rw [wrap32_id _ (by omega) (by omega)]
            · have hpc : ∀ r, parseDstStartEndPy c ≠ .ok r := fun r e => by
                have := (rulePy_ok c r e).1; rw [hcc] at this; simp at this; first | exact hr2 this.2 | exact hr2 this.2.symm
              have hpk : peek rest2 ≠ 0 := by
                obtain ⟨pre2, epre2, -⟩ := rule_dec c en rest2 hcc
                have : (0 : UInt8) ∉ rest2 := fun hm => h0 (by rw [hb, epre2]; simp [hm])
                exact peek_ne_of_not_mem rest2 0 this hr2
              simp only [hpk, ne_eq, not_false_eq_true, ite_true]
              cases h : parseDstStartEndPy c with
              | error _ =>
                have hpk' : (rest2.head?).getD 0 ≠ 0 := by simpa [peek] using hpk
                simp [h, hpa, hpk', Except.toOption, throw, throwThe, MonadExceptOf.throw]
              | ok r => exact absurd h (hpc r)
      · have hpa : ∀ r, parseDstStartEndPy a ≠ .ok r := fun r e => by
          have := (rulePy_ok a r e).1; rw [hca] at this; simp at this; first | exact hr this.2 | exact hr this.2.symm
        have hpk : peek (rest ++ (se2.map (44 :: ·)).getD []) ≠ 44 := by
          have := peek_ne_of_not_mem rest 44 h44r hr
          cases rest with
          | nil => exact absurd rfl hr
          | cons x t => simpa [peek] using this
        simp only [hpk, ne_eq, not_false_eq_true, ite_true]
        cases se2 with
        | none => cases h : parseDstStartEndPy a with
          | error _ => simp [h, Except.toOption, throw, throwThe, MonadExceptOf.throw]
          | ok r => exact absurd h (hpa r)
        | some c =>
          cases h : parseDstStartEndPy a with
          | error _ => simp [h, Except.toOption, throw, throwThe, MonadExceptOf.throw]
          | ok r => exact absurd h (hpa r)
  · intro x hx
    simp only [pres, hsp] at hx
    cases se2 with
    | none =>
      cases h1 : parseDstStartEndPy a <;> simp [h1, throw, throwThe, MonadExceptOf.throw] at hx
    | some c =>
      cases h1 : parseDstStartEndPy a with
      | error _ => simp [h1, throw, throwThe, MonadExceptOf.throw] at hx
      | ok s =>
        cases h2 : parseDstStartEndPy c with
        | error _ => simp [h1, h2, throw, throwThe, MonadExceptOf.throw] at hx
        | ok e =>
          have a1 := (rulePy_ok a s h1).2
          have a2 := (rulePy_ok c e h2).2
          rw [hb]
          exact asc_append _ _ a1 (asc_cons 44 (by decide) _ a2)

theorem not_mem_append_left {a b : Bytes} {c : UInt8} (h : c ∉ a ++ b) : c ∉ a := fun hm => h (by simp [hm])
theorem not_mem_append_right {a b : Bytes} {c : UInt8} (h : c ∉ a ++ b) : c ∉ b := fun hm => h (by simp [hm])

theorem pyOffStep_eq (o : Option UInt8 × Bytes × Option Bytes × Option Bytes) (hs : OffShape o) (msg : String) :
    pyOffStep (offText o) msg = match parseTzDeltaPy (offText o) with
      | .ok v => .ok v
      | .error _ => .error (tzErrPy msg) := by
  unfold pyOffStep
  cases h : parseTzDeltaPy (offText o) with
  | ok v => rfl
  | error e =>
    obtain ⟨m, rfl⟩ := pyDelta_ok o hs e h
    rfl

theorem takeWhile_ne0 (tz : Bytes) (h0 : (0 : UInt8) ∉ tz) : tz.takeWhile (fun c => decide (c ≠ 0)) = tz := by
  have := takeWhile_all_stop (q := fun c => decide (c ≠ 0)) tz [] (fun c hc => by
    simp only [ne_eq, decide_eq_true_eq]; intro e; subst e; exact h0 hc) (fun c h => by simp at h)
  simpa using this

theorem reTz_none_of_abbr (s : Bytes) (h : reAbbr s = none) : reTz s = none := by
  simp [reTz, h, bind, Option.bind]

theorem reTz_std (s g : Bytes) (h : reAbbr s = some (g, [])) : reTz s = some (g, none, none, none) := by
  simp [reTz, h, bind, Option.bind, pure]

theorem reTz_off_none (s g r1 : Bytes) (h : reAbbr s = some (g, r1)) (hr : r1 ≠ []) (ho : reOff r1 = none) :
    reTz s = none := by
  simp [reTz, h, hr, ho, bind, Option.bind]

theorem reTz_so (s g r1 : Bytes) (h : reAbbr s = some (g, r1)) (hr : r1 ≠ []) (o) (ho : reOff r1 = some (o, [])) :
    reTz s = some (g, some (offText o), none, none) := by
  simp [reTz, h, hr, ho, bind, Option.bind, pure]

theorem reTz_dst_none (s g r1 : Bytes) (h : reAbbr s = some (g, r1)) (hr : r1 ≠ []) (o) (r2 : Bytes)
    (ho : reOff r1 = some (o, r2)) (hr2 : r2 ≠ []) (hd : reAbbr r2 = none) : reTz s = none := by
  simp [reTz, h, hr, ho, hr2, hd, bind, Option.bind]

theorem reTz_dst (s g r1 : Bytes) (h : reAbbr s = some (g, r1)) (hr : r1 ≠ []) (o) (r2 : Bytes)
    (ho : reOff r1 = some (o, r2)) (hr2 : r2 ≠ []) (dg : Bytes) (hd : reAbbr r2 = some (dg, [])) :
    reTz s = some (g, some (offText o), some dg, none) := by
  simp [reTz, h, hr, ho, hr2, hd, bind, Option.bind, pure]

theorem reTz_dso_none (s g r1 : Bytes) (h : reAbbr s = some (g, r1)) (hr : r1 ≠ []) (o) (r2 : Bytes)
    (ho : reOff r1 = some (o, r2)) (hr2 : r2 ≠ []) (dg r3 : Bytes) (hd : reAbbr r2 = some (dg, r3))
    (hr3 : r3 ≠ []) (ho2 : reOff r3 = none) : reTz s = none := by
  simp [reTz, h, hr, ho, hr2, hd, hr3, ho2, bind, Option.bind]

theorem reTz_dso (s g r1 : Bytes) (h : reAbbr s = some (g, r1)) (hr : r1 ≠ []) (o) (r2 : Bytes)
    (ho : reOff r1 = some (o, r2)) (hr2 : r2 ≠ []) (dg r3 : Bytes) (hd : reAbbr r2 = some (dg, r3))
    (hr3 : r3 ≠ []) (o2) (r4 : Bytes) (ho2 : reOff r3 = some (o2, r4)) :
    reTz s = if r4 = [] then some (g, some (offText o), some dg, some (offText o2)) else none := by
  by_cases hr4 : r4 = []
  · subst hr4; simp [reTz, h, hr, ho, hr2, hd, hr3, ho2, bind, Option.bind, pure]
  · simp [reTz, h, hr, ho, hr2, hd, hr3, ho2, hr4, bind, Option.bind]

theorem peek_app_ne (r T : Bytes) (c : UInt8) (hr : r ≠ []) (h : c ∉ r) : peek (r ++ T) ≠ c := by
  cases r with
  | nil => exact absurd rfl hr
  | cons a t => simp only [List.cons_append, peek, List.headD_cons]; intro e; subst e; exact h (by simp)

theorem tz_eq (tz : Bytes) (h0 : (0 : UInt8) ∉ tz) :
    (parseTzStrC tz).toOption = (parseTzStrPy tz).toOption.map afterToC := by
  have hdec := splitFirst_decomp 44 tz
  generalize hsp : splitFirst 44 tz = sp at hdec
  obtain ⟨off, se⟩ := sp
  simp only at hdec
  obtain ⟨hx, h44⟩ := hdec
  have hT : CommaTail ((se.map (44 :: ·)).getD []) := by
    cases se with
    | none => exact .inl rfl
    | some c => exact .inr ⟨c, rfl⟩
  have h0off : (0 : UInt8) ∉ off := fun hm => h0 (by rw [hx]; simp [hm])
  have h0se : ∀ b, se = some b → (0 : UInt8) ∉ b := fun b hb hm => h0 (by rw [hx, hb]; simp [hm])
  unfold parseTzStrC parseTzStrPy
  rw [takeWhile_ne0 tz h0, hsp]
  simp only
  conv => enter [1, 1]; rw [hx]
  rw [cAbbr_tail off _ hT]
  have thr : ∀ (α : Type) (e : PyExc), (throw e : Py α) = .error e := fun _ _ => rfl
  cases ha : reAbbr off with
  | none =>
    rw [reTz_none_of_abbr off ha]; simp [Except.toOption, thr, bind, Except.bind, Functor.map, Except.map, pure, Except.pure]
  | some gr =>
    obtain ⟨g, r1⟩ := gr
    obtain ⟨eoff, -⟩ := reAbbr_dec off g r1 ha
    simp only [Option.map_some]
    by_cases hr1 : r1 = []
    · subst hr1
      rw [reTz_std off g ha]
      cases se with
      | none => simp [delta_nil, Except.toOption, thr, bind, Except.bind, Functor.map, Except.map, pure, Except.pure]
      | some b => simp [delta_comma, Except.toOption, thr, bind, Except.bind, Functor.map, Except.map, pure, Except.pure]
    · rw [cDelta_tail r1 _ hT, delta_eq r1]
      cases ho : reOff r1 with
      | none => rw [reTz_off_none off g r1 ha hr1 ho]; simp [Except.toOption, thr, bind, Except.bind, Functor.map, Except.map, pure, Except.pure]
      | some or_ =>
        obtain ⟨o, r2⟩ := or_
        have hs := reOff_shape r1 o r2 ho
        have er1 := reOff_dec r1 o r2 ho
        have h44r2 : (44 : UInt8) ∉ r2 := fun hm => h44 (by rw [eoff, er1]; simp [hm])
        have h0r2 : (0 : UInt8) ∉ r2 := fun hm => h0off (by rw [eoff, er1]; simp [hm])
        have hdb := delta_bound o hs
        by_cases hr2 : r2 = []
        · subst hr2
          rw [reTz_so off g r1 ha hr1 o ho]
          simp only [show ¬ (o.2.2.2 = none ∧ peek [] = 58) by simp [peek], ite_false]
          rw [pyOffStep_eq o hs]
          cases hdv : parseTzDeltaPy (offText o) with
          | error e => simp [Except.toOption, thr, bind, Except.bind, Functor.map, Except.map, pure, Except.pure]
          | ok v =>
            cases se with
            | none => simp [peek, Except.toOption, afterToC, buildTzruleC, pure, Except.pure, bind, Except.bind, Functor.map, Except.map]
            | some b =>
              simp [peek, abbr_eq, abbr_comma, Except.toOption, thr, bind, Except.bind, Functor.map, Except.map, pure, Except.pure]
        · by_cases hcol : o.2.2.2 = none ∧ peek r2 = 58
          · have : r2 = 58 :: r2.tail := peek_cons r2 58 (by decide) hcol.2
            rw [reTz_dst_none off g r1 ha hr1 o r2 ho hr2 (by rw [this]; exact abbr_colon _)]
            simp [hcol, Except.toOption, thr, bind, Except.bind, Functor.map, Except.map, pure, Except.pure]
          · simp only [hcol, ite_false]
            have hp0 : peek (r2 ++ (se.map (44 :: ·)).getD []) ≠ 0 := peek_app_ne r2 _ 0 hr2 h0r2
            cases hdv : parseTzDeltaPy (offText o) with
            | error e =>
              -- C stops here; Python fails at the STD offset, or earlier in its pattern
              simp only [Option.map_none, Except.toOption]
              cases hd : reAbbr r2 with
              | none => rw [reTz_dst_none off g r1 ha hr1 o r2 ho hr2 hd]; simp [Except.toOption, thr, bind, Except.bind, Functor.map, Except.map, pure, Except.pure]
              | some dr =>
                obtain ⟨dg, r3⟩ := dr
                by_cases hr3 : r3 = []
                · subst hr3
                  rw [reTz_dst off g r1 ha hr1 o r2 ho hr2 dg hd]; simp only [pyOffStep_eq o hs, hdv]; simp [Except.toOption, thr, bind, Except.bind, Functor.map, Except.map, pure, Except.pure]
                · cases ho2 : reOff r3 with
                  | none => rw [reTz_dso_none off g r1 ha hr1 o r2 ho hr2 dg r3 hd hr3 ho2]; simp [Except.toOption, thr, bind, Except.bind, Functor.map, Except.map, pure, Except.pure]
                  | some or2 =>
                    obtain ⟨o2, r4⟩ := or2
                    rw [reTz_dso off g r1 ha hr1 o r2 ho hr2 dg r3 hd hr3 o2 r4 ho2]
                    by_cases hr4 : r4 = []
                    · simp only [hr4, ite_true, pyOffStep_eq o hs, hdv]; simp [Except.toOption, thr, bind, Except.bind, Functor.map, Except.map, pure, Except.pure]
                    · simp [hr4, Except.toOption, thr, bind, Except.bind, Functor.map, Except.map, pure, Except.pure]
            | ok v =>
              have hv := hdb v hdv
              simp only [Option.map_some, hp0, ite_false]
              rw [cAbbr_tail r2 _ hT]
              cases hd : reAbbr r2 with
              | none => rw [reTz_dst_none off g r1 ha hr1 o r2 ho hr2 hd]; simp [Except.toOption, thr, bind, Except.bind, Functor.map, Except.map, pure, Except.pure]
              | some dr =>
                obtain ⟨dg, r3⟩ := dr
                obtain ⟨er2, -⟩ := reAbbr_dec r2 dg r3 hd
                have h44r3 : (44 : UInt8) ∉ r3 := fun hm => h44r2 (by rw [er2]; simp [hm])
                simp only [Option.map_some]
                by_cases hr3 : r3 = []
                · subst hr3
                  rw [reTz_dst off g r1 ha hr1 o r2 ho hr2 dg hd]; simp only [pyOffStep_eq o hs, hdv]
                  cases se with
                  | none => simp [peek, delta_nil, Except.toOption, thr, bind, Except.bind, Functor.map, Except.map, pure, Except.pure]
                  | some b =>
                    have hrl := (rules_eq b (h0se b rfl) (stripAngle g) (stripAngle dg) v (v + 3600)
                      (by omega) (by omega)).1
                    simp only [List.nil_append, Option.map_some, Option.getD_some, peek, List.headD_cons,
                      ite_true, ne_eq, not_true_eq_false, ite_false, List.tail_cons, Option.map, pure,
                      Except.pure, bind, Except.bind]
                    exact hrl
                · have hp44 := peek_app_ne r3 ((se.map (44 :: ·)).getD []) 44 hr3 h44r3
                  simp only [hp44, ite_false]
                  rw [cDelta_tail r3 _ hT, delta_eq r3]
                  cases ho2 : reOff r3 with
                  | none => rw [reTz_dso_none off g r1 ha hr1 o r2 ho hr2 dg r3 hd hr3 ho2]; simp [Except.toOption, thr, bind, Except.bind, Functor.map, Except.map, pure, Except.pure]
                  | some or2 =>
                    obtain ⟨o2, r4⟩ := or2
                    have hs2 := reOff_shape r3 o2 r4 ho2
                    have er3 := reOff_dec r3 o2 r4 ho2
                    have h44r4 : (44 : UInt8) ∉ r4 := fun hm => h44r3 (by rw [er3]; simp [hm])
                    rw [reTz_dso off g r1 ha hr1 o r2 ho hr2 dg r3 hd hr3 o2 r4 ho2]
                    by_cases hr4 : r4 = []
                    · subst hr4
                      simp only [show ¬ (o2.2.2.2 = none ∧ peek [] = 58) by simp [peek], ite_false, ite_true,
                        pyOffStep_eq o hs, hdv, pyOffStep_eq o2 hs2]
                      cases hdv2 : parseTzDeltaPy (offText o2) with
                      | error e => simp [Except.toOption, thr, bind, Except.bind, Functor.map, Except.map, pure, Except.pure]
                      | ok dv =>
                        have hdv' := delta_bound o2 hs2 dv hdv2
                        cases se with
                        | none => simp [peek, Except.toOption, thr, bind, Except.bind, Functor.map, Except.map, pure, Except.pure]
                        | some b =>
                          have hrl := (rules_eq b (h0se b rfl) (stripAngle g) (stripAngle dg) v dv
                            (by omega) (by omega)).1
                          simp only [List.nil_append, Option.map_some, Option.getD_some, peek, List.headD_cons,
                            ne_eq, not_true_eq_false, ite_false, List.tail_cons, pure, Except.pure, bind,
                            Except.bind]
                          exact hrl
                    · simp only [hr4, ite_false]
                      have hp44' := peek_app_ne r4 ((se.map (44 :: ·)).getD []) 44 hr4 h44r4
                      by_cases hcol2 : peek r4 = 58
                      · by_cases hss : o2.2.2.2 = none
                        · simp [hcol2, hss, Except.toOption, thr, bind, Except.bind, Functor.map, Except.map, pure, Except.pure]
                        · simp only [hcol2, hss, and_true, ite_false]
                          cases parseTzDeltaPy (offText o2) <;> simp [hp44', Except.toOption, thr, bind, Except.bind, Functor.map, Except.map, pure, Except.pure]
                      · simp only [hcol2, and_false, ite_false]
                        cases parseTzDeltaPy (offText o2) <;> simp [hp44', Except.toOption, thr, bind, Except.bind, Functor.map, Except.map, pure, Except.pure]

/-- What a successful `fullmatch` covers: ASCII, and offset groups that are `reOff` matches. -/
def GroupsOK (s : Bytes) (so dso : Option Bytes) : Prop :=
  Asc s ∧ (∀ t, so = some t → ∃ o, OffShape o ∧ t = offText o) ∧
    (∀ t, dso = some t → ∃ o, OffShape o ∧ t = offText o)

theorem reTz_ok (s : Bytes) (std : Bytes) (so dst dso : Option Bytes) (h : reTz s = some (std, so, dst, dso)) :
    GroupsOK s so dso := by
  unfold reTz at h
  obtain ⟨⟨g, r1⟩, h1, h⟩ := obind_some h
  obtain ⟨e1, a1⟩ := reAbbr_dec s g r1 h1
  simp only at h
  split at h
  · rename_i hr1
    simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, -, rfl⟩ := h
    refine ⟨by rw [e1, hr1, List.append_nil]; exact a1, by simp, by simp⟩
  · obtain ⟨⟨o, r2⟩, h2, h⟩ := obind_some h
    have hs := reOff_shape r1 o r2 h2
    have e2 := reOff_dec r1 o r2 h2
    simp only at h
    split at h
    · rename_i hr2
      simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, -, rfl⟩ := h
      refine ⟨?_, fun t ht => ⟨o, hs, by simp at ht; exact ht.symm⟩, by simp⟩
      rw [e1, e2, hr2, List.append_nil]; exact asc_append _ _ a1 (offText_asc o hs)
    · obtain ⟨⟨dg, r3⟩, h3, h⟩ := obind_some h
      obtain ⟨e3, a3⟩ := reAbbr_dec r2 dg r3 h3
      simp only at h
      split at h
      · rename_i hr3
        simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl, -, rfl⟩ := h
        refine ⟨?_, fun t ht => ⟨o, hs, by simp at ht; exact ht.symm⟩, by simp⟩
        rw [e1, e2, e3, hr3, List.append_nil]
        exact asc_append _ _ a1 (asc_append _ _ (offText_asc o hs) a3)
      · obtain ⟨⟨o2, r4⟩, h4, h⟩ := obind_some h
        have hs2 := reOff_shape r3 o2 r4 h4
        have e4 := reOff_dec r3 o2 r4 h4
        simp only at h
        split at h
        · rename_i hr4
          simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl, -, rfl⟩ := h
          refine ⟨?_, fun t ht => ⟨o, hs, by simp at ht; exact ht.symm⟩,
            fun t ht => ⟨o2, hs2, by simp at ht; exact ht.symm⟩⟩
          rw [e1, e2, e3, e4, hr4, List.append_nil]
          exact asc_append _ _ a1 (asc_append _ _ (offText_asc o hs) (asc_append _ _ a3 (offText_asc o2 hs2)))
        · cases h

theorem pyTz_props (tz : Bytes) (h0 : (0 : UInt8) ∉ tz) :
    (∀ e, parseTzStrPy tz = .error e → e.className = "ValueError") ∧
    (∀ a, parseTzStrPy tz = .ok a → Asc tz) := by
  have hdec := splitFirst_decomp 44 tz
  generalize hsp : splitFirst 44 tz = sp at hdec
  obtain ⟨off, se⟩ := sp
  simp only at hdec
  obtain ⟨hx, h44⟩ := hdec
  have h0se : ∀ b, se = some b → (0 : UInt8) ∉ b := fun b hb hm => h0 (by rw [hx, hb]; simp [hm])
  have thr : ∀ (α : Type) (e : PyExc), (throw e : Py α) = .error e := fun _ _ => rfl
  unfold parseTzStrPy
  rw [hsp]
  simp only
  cases hre : reTz off with
  | none => exact ⟨fun e h => by simp [thr] at h; subst h; rfl, fun a h => by simp [thr] at h⟩
  | some grp =>
    obtain ⟨stdG, so, dst, dso⟩ := grp
    obtain ⟨aoff, hso, hdso⟩ := reTz_ok off stdG so dst dso hre
    simp only
    cases so with
    | none => exact ⟨fun e h => by simp [thr, bind, Except.bind] at h; subst h; rfl,
        fun a h => by simp [thr, bind, Except.bind] at h⟩
    | some t =>
      obtain ⟨o, hs, rfl⟩ := hso t rfl
      simp only [pyOffStep_eq o hs]
      cases hdv : parseTzDeltaPy (offText o) with
      | error _ => exact ⟨fun e h => by simp [thr, bind, Except.bind] at h; subst h; rfl,
          fun a h => by simp [thr, bind, Except.bind] at h⟩
      | ok v =>
        simp only [bind, Except.bind]
        cases dst with
        | none =>
          simp only [Option.map_none]
          cases se with
          | none =>
            refine ⟨fun e h => by simp [pure, Except.pure] at h, fun a h => ?_⟩
            rw [hx]; simpa using aoff
          | some b => exact ⟨fun e h => by simp [thr] at h; subst h; rfl, fun a h => by simp [thr] at h⟩
        | some dg =>
          simp only [Option.map_some]
          have hvb := delta_bound o hs v hdv
          cases dso with
          | none =>
            simp only [pure, Except.pure]
            cases se with
            | none => exact ⟨fun e h => by simp [thr] at h; subst h; rfl, fun a h => by simp [thr] at h⟩
            | some b =>
              have hr := rules_eq b (h0se b rfl) (stripAngle stdG) (stripAngle dg) v (v + 3600)
                (by omega) (by omega)
              exact ⟨hr.2.1, fun a h => by
                have ab := hr.2.2 a h
                rw [hx]; exact asc_append _ _ aoff (asc_cons 44 (by decide) _ ab)⟩
          | some t2 =>
            obtain ⟨o2, hs2, rfl⟩ := hdso t2 rfl
            simp only [pyOffStep_eq o2 hs2]
            cases hdv2 : parseTzDeltaPy (offText o2) with
            | error _ => exact ⟨fun e h => by simp [thr] at h; subst h; rfl, fun a h => by simp [thr] at h⟩
            | ok dv =>
              have := delta_bound o2 hs2 dv hdv2
              simp only
              cases se with
              | none => exact ⟨fun e h => by simp [thr] at h; subst h; rfl, fun a h => by simp [thr] at h⟩
              | some b =>
                have hr := rules_eq b (h0se b rfl) (stripAngle stdG) (stripAngle dg) v dv
                  (by omega) (by omega)
                exact ⟨hr.2.1, fun a h => by
                  have ab := hr.2.2 a h
                  rw [hx]; exact asc_append _ _ aoff (asc_cons 44 (by decide) _ ab)⟩

end PyLean.Datetime.Zone
