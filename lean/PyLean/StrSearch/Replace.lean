import PyLean.StrSearch.Find
import PyLean.StrSearch.Split
import PyLean.StrSearch.Pad
import PyLean.StrSearch.Strip

/-!
`split`/`rsplit` and `replace`: the dispatch to the specialised loops
(`split_char`, the seven `stringlib_replace_*` helpers, the three branches of
`replace` in unicodeobject.c), the computed default `maxcount`s, and the
overflow checks, against the split-join specification.
-/

set_option linter.deprecated false

namespace PyLean.StrSearch

open PyLean

/-- The number of splits `split(sep, k)`/`replace(old, new, k)` perform at most:
all of them for a negative `k`. -/
def rounds (k : Int) (s : Seq) : Nat := if k < 0 then s.length + 1 else k.toNat

theorem splitN_noocc {p s : Seq} (h : ∀ j, ¬ Occ s p j) (k : Nat) : splitN p k s = [s] := by
  cases k with
  | zero => rfl
  | succ k => simp [splitN, findL_eq_none.mpr h]

theorem countN_noocc {p s : Seq} (h : ∀ j, ¬ Occ s p j) (k : Nat) : countN p k s = 0 := by
  simp [countN, splitN_noocc h]

/-- Rounds beyond the number of matches change nothing. -/
theorem splitN_rounds {p : Seq} (hp : p ≠ []) (s : Seq) (k : Nat) (hk : s.length / p.length + 1 ≤ k) :
    splitN p k s = splitN p (s.length + 1) s := splitN_sat hp k s hk

theorem div_succ_le {a b : Nat} (hb : 1 ≤ b) : a / b + 1 ≤ a + 1 := by
  have := Nat.div_le_self a b; omega

theorem maxSplit_rounds {p : Seq} (hp : p ≠ []) (s : Seq) (hs : (s.length : Int) < ssizeMax) :
    splitN p ssizeMax.toNat s = splitN p (s.length + 1) s := by
  have hpl : p.length ≥ 1 := List.length_pos_iff.mpr hp
  apply splitN_rounds hp
  have := div_succ_le (a := s.length) hpl
  omega

/-- `str.split(sep, k)` for a non-empty `sep` is the greedy split. -/
theorem strSplit_some {s sep : Seq} {k : Int} (hp : sep ≠ []) (hs : (s.length : Int) < ssizeMax)
    (hk1 : ssizeMin ≤ k) (hk2 : k ≤ ssizeMax) :
    strSplit s (some sep) k = .ok (splitN sep (rounds k s) s) := by
  have hpl : sep.length ≥ 1 := List.length_pos_iff.mpr hp
  simp only [strSplit, argSsize_ok hk1 hk2, bind, Except.bind, pure, Except.pure]
  by_cases hc : kindOf s < kindOf sep ∨ s.length < sep.length
  · rw [if_pos hc]
    have : ∀ j, ¬ Occ s sep j := by
      rcases hc with h | h
      · exact not_occ_of_kind h
      · exact not_occ_of_long h
    rw [splitN_noocc this]
  · rw [if_neg hc]
    have hmc : splitN sep (strSepMaxcount s.length sep.length k).toNat s = splitN sep (rounds k s) s := by
      unfold strSepMaxcount rounds
      by_cases hk : k < 0
      · simp only [hk, ↓reduceIte, show sep.length ≠ 0 by omega]
        have hd := div_succ_le (a := s.length) hpl
        rw [if_neg (by omega)]
        apply splitN_rounds hp; omega
      · simp only [hk, ↓reduceIte]
    rw [← hmc]
    unfold stringlibSplit
    rw [if_neg (by omega)]
    split
    · next h1 =>
      obtain ⟨c, rfl⟩ : ∃ c, sep = [c] := by
        match sep, h1 with
        | [c], _ => exact ⟨c, rfl⟩
      simp only [List.head!, splitChar_eq, splitLoop_eq hp]
    · simp only [splitLoop_eq hp]

theorem bytesSplit_some {s sep : Seq} {k : Int} (hp : sep ≠ []) (hs : (s.length : Int) < ssizeMax)
    (hk1 : ssizeMin ≤ k) (hk2 : k ≤ ssizeMax) :
    bytesSplit s (some sep) k = .ok (splitN sep (rounds k s) s) := by
  have hpl : sep.length ≥ 1 := List.length_pos_iff.mpr hp
  simp only [bytesSplit, argSsize_ok hk1 hk2, bind, Except.bind, pure, Except.pure]
  have hmc : splitN sep (if k < 0 then ssizeMax else k).toNat s = splitN sep (rounds k s) s := by
    unfold rounds
    by_cases hk : k < 0
    · simp only [hk, ↓reduceIte]; exact maxSplit_rounds hp s hs
    · simp only [hk, ↓reduceIte]
  rw [← hmc]
  unfold stringlibSplit
  rw [if_neg (by omega)]
  split
  · next h1 =>
    obtain ⟨c, rfl⟩ : ∃ c, sep = [c] := by
      match sep, h1 with
      | [c], _ => exact ⟨c, rfl⟩
    simp only [List.head!, splitChar_eq, splitLoop_eq hp]
  · simp only [splitLoop_eq hp]

/-! ## replace -/

theorem maxCharValue_mono {s p : Seq} (sub : ∀ x ∈ p, x ∈ s) : maxCharValue p ≤ maxCharValue s := by
  have hle : ∀ q : Seq, maxCharValue q ≤ 1114111 := by
    intro q; unfold maxCharValue; split <;> (try split) <;> (try split) <;> omega
  unfold maxCharValue
  by_cases ha : isAscii s = true
  · have : isAscii p = true := by
      unfold isAscii at ha ⊢
      exact List.all_eq_true.mpr fun x hx => List.all_eq_true.mp ha x (sub x hx)
    simp [ha, this]
  · simp only [ha, Bool.false_eq_true, ↓reduceIte]
    by_cases h1 : kindOf s = 1
    · have hb := kindOf_one h1
      have : kindOf p = 1 := kindOf_of_all fun x hx => hb x (sub x hx)
      simp only [h1, ↓reduceIte, this]; split <;> omega
    · simp only [h1, ↓reduceIte]
      by_cases h2 : kindOf s = 2
      · have hb := kindOf_le_two (by omega : kindOf s ≤ 2)
        have : kindOf p ≤ 2 := by
          unfold kindOf; split
          · simp
          · have h' : (p.all fun x => decide (x < 65536)) = true :=
              List.all_eq_true.mpr (by simpa using fun x hx => hb x (sub x hx))
            simp only [h', ↓reduceIte]; omega
        simp only [h2, ↓reduceIte]
        rcases kindOf_cases p with hp | hp | hp <;> simp [hp] <;> (try split) <;> omega
      · simp only [h2, ↓reduceIte]
        have := hle p; unfold maxCharValue at this; exact this

theorem maxCharValue_noocc {s p : Seq} (h : maxCharValue s < maxCharValue p) : ∀ j, ¬ Occ s p j := by
  intro j ho
  have := maxCharValue_mono (s := s) (p := p) (fun x hx => ho.mem hx)
  omega

theorem stringlibCount_rounds {s p : Seq} (hp : p ≠ []) {mc : Int} (hm : 0 < mc) :
    stringlibCount s s.length p mc = countN p mc.toNat s := by
  have hpl : p.length ≠ 0 := by simpa using hp
  unfold stringlibCount fastsearch
  simp only [show ¬ ((s.length : Int) < 0) by omega, hpl, ↓reduceIte, show mc ≠ 0 by omega,
    and_false, or_false]
  by_cases hl : s.length < p.length
  · rw [if_pos hl, countN_noocc (not_occ_of_long hl)]; simp
  · rw [if_neg hl, countN_eq_min hp]
    have := countAll_le hp s
    split <;> omega

theorem replaceChars_prefix (u1 u2 : Nat) (mc : Int) :
    ∀ (s : Seq) (p : Nat), findL [u1] s = some p →
      s.take p ++ replaceChars u1 u2 mc (s.drop p) = replaceChars u1 u2 mc s := by
  intro s
  induction s with
  | nil => intro p h; simp
  | cons c cs ih =>
    intro p h
    by_cases hc : c = u1
    · subst hc
      have : p = 0 := by simp [findL, List.isPrefixOf] at h; omega
      subst this; simp
    · have hnp : ¬ [u1].isPrefixOf (c :: cs) = true := by
        simp [List.isPrefixOf]; exact fun h => hc h.symm
      rw [findL_cons_nomatch hnp] at h
      cases hf : findL [u1] cs with
      | none => rw [hf] at h; cases h
      | some q =>
        rw [hf] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
        simp only [List.take_succ_cons, List.drop_succ_cons, List.cons_append, replaceChars, hc,
          false_and, ↓reduceIte, ih q hf]

theorem splitN_succ_some {p s : Seq} {i : Nat} (h : findL p s = some i) (k : Nat) :
    splitN p (k + 1) s = s.take i :: splitN p k (s.drop (i + p.length)) := by
  simp [splitN, h]

/-- The split-join replacement with `k` rounds, written with `mc`. -/
theorem splitN_mc {p : Seq} (hp : p ≠ []) (s : Seq) (hs : (s.length : Int) < ssizeMax) (k : Int) :
    splitN p (if k < 0 then ssizeMax else k).toNat s = splitN p (rounds k s) s := by
  unfold rounds
  by_cases hk : k < 0
  · simp only [hk, ↓reduceIte]; exact maxSplit_rounds hp s hs
  · simp only [hk, ↓reduceIte]

theorem length_split_join {p : Seq} (new : Seq) (hp : p ≠ []) (k : Nat) (s : Seq) (heq : p.length = new.length) :
    (new.intercalate (splitN p k s)).length = s.length := by
  have := length_intercalate_splitN new hp k s
  rw [heq] at this; simp at this; omega

theorem split_join_single {p : Seq} (new : Seq) (hp : p ≠ []) (k : Nat) (s : Seq)
    (h : (splitN p k s).length = 1) : new.intercalate (splitN p k s) = s := by
  have hr := intercalate_splitN hp k s
  match hs : splitN p k s, h with
  | [x], _ => rw [hs] at hr; simpa using hr

theorem ovf_iff {a b n : Int} (hn : 0 < n) : a > b / n ↔ b < a * n := Int.ediv_lt_iff_lt_mul hn

theorem countN_length {p : Seq} (k : Nat) (s : Seq) : (splitN p k s).length = countN p k s + 1 := by
  have := splitN_ne_nil p k s
  unfold countN
  cases h : splitN p k s with
  | nil => exact absurd h this
  | cons _ _ => simp

theorem stringlibFind_some_or {s p : Seq} (h : p.length ≤ s.length) :
    stringlibFind s p 0 = optOff 0 (findL p s) := stringlibFind_eq h 0

/-- `str.replace` (`replace`, unicodeobject.c:10811-11067) with a non-empty
`old` is the split-join replacement, raising `OverflowError` exactly when the
lengths differ, something is replaced, and the result is longer than
`PY_SSIZE_T_MAX / kind`. -/
theorem strReplace_eq {s old new : Seq} {k : Int} (hp : old ≠ []) (hs : (s.length : Int) < ssizeMax)
    (hk1 : ssizeMin ≤ k) (hk2 : k ≤ ssizeMax) :
    strReplace s old new k =
      if old.length ≠ new.length ∧ (splitN old (rounds k s) s).length ≠ 1 ∧
          ((new.intercalate (splitN old (rounds k s) s)).length : Int) >
            ssizeMax / max (kindOf s : Int) (kindOf new)
      then .error (.overflowError "replace string is too long")
      else .ok (new.intercalate (splitN old (rounds k s) s)) := by
  have hpl : old.length ≥ 1 := List.length_pos_iff.mpr hp
  have hMpos : (0 : Int) < ssizeMax := by unfold ssizeMax; omega
  have hkind : ∀ q : Seq, (1 : Int) ≤ kindOf q := fun q => by rcases kindOf_cases q with h | h | h <;> omega
  -- the result when nothing is replaced
  have hnone : (∀ j, ¬ Occ s old j) →
      (if old.length ≠ new.length ∧ (splitN old (rounds k s) s).length ≠ 1 ∧
          ((new.intercalate (splitN old (rounds k s) s)).length : Int) >
            ssizeMax / max (kindOf s : Int) (kindOf new)
        then (.error (.overflowError "replace string is too long") : Py Seq)
        else .ok (new.intercalate (splitN old (rounds k s) s))) = .ok s := by
    intro h
    rw [splitN_noocc h]; simp
  rw [← splitN_mc hp s hs k]
  rw [← splitN_mc hp s hs k] at hnone
  simp only [strReplace, argSsize_ok hk1 hk2, bind, Except.bind, pure, Except.pure]
  generalize hmc : (if k < 0 then ssizeMax else k) = mc at *
  by_cases hl : s.length < old.length
  · rw [if_pos hl, hnone (not_occ_of_long hl)]
  rw [if_neg hl]
  by_cases h0 : mc = 0
  · rw [if_pos h0]; subst h0; simp [splitN]
  rw [if_neg h0]
  have hmpos : 0 < mc := by
    rw [← hmc]; split <;> omega
  by_cases hmax : maxCharValue s < maxCharValue old
  · rw [if_pos hmax, hnone (maxCharValue_noocc hmax)]
  rw [if_neg hmax]
  by_cases heq : old.length = new.length
  · rw [if_pos heq, if_neg (by omega)]
    simp only [heq, ne_eq, not_true_eq_false, false_and, ↓reduceIte]
    by_cases h1 : new.length = 1
    · rw [if_pos h1]
      obtain ⟨c, rfl⟩ : ∃ c, old = [c] := by
        match old, (show old.length = 1 by omega) with
        | [c], _ => exact ⟨c, rfl⟩
      obtain ⟨d, rfl⟩ : ∃ d, new = [d] := by
        match new, h1 with
        | [d], _ => exact ⟨d, rfl⟩
      simp only [List.head!, findChar_eq, ↓reduceIte]
      cases hf : findL [c] s with
      | none =>
        simp [optIdx, splitN_noocc (findL_eq_none.mp hf)]
      | some q =>
        simp only [optIdx, show ¬ ((q : Int) < 0) by omega, ↓reduceIte, Int.toNat_natCast]
        rw [replaceChars_prefix c d mc s q hf, replaceChars_eq]
    · rw [if_neg h1, stringlibFind_some_or (by omega)]
      cases hf : findL old s with
      | none =>
        simp [optOff, splitN_noocc (findL_eq_none.mp hf)]
      | some i =>
        simp only [optOff, Int.zero_add, show ¬ ((i : Int) < 0) by omega, ↓reduceIte, Int.toNat_natCast]
        obtain ⟨m, hm⟩ : ∃ m, mc.toNat = m + 1 := ⟨mc.toNat - 1, by omega⟩
        rw [hm, splitN_succ_some hf, intercalate_cons_ne (splitN_ne_nil _ _ _),
          replaceInplace_eq new hp, show (mc - 1).toNat = m by omega, ← heq, List.append_assoc]
  · rw [if_neg heq]
    simp only [heq, ne_eq, not_false_eq_true, true_and]
    rw [stringlibCount_rounds hp hmpos]
    have hlen := length_intercalate_splitN new hp mc.toNat s
    have hcl := countN_length (p := old) mc.toNat s
    generalize hn : countN old mc.toNat s = n at *
    by_cases hn0 : (n : Int) = 0
    · rw [if_pos hn0]
      have : n = 0 := by omega
      subst this
      rw [if_neg (by omega)]
      exact (congrArg Except.ok (split_join_single new hp _ s hcl)).symm
    rw [if_neg hn0]
    have hnpos : (0 : Int) < n := by omega
    have hps : (splitN old mc.toNat s).length ≠ 1 := by omega
    simp only [hps, not_false_eq_true, true_and]
    have hrk : (1 : Int) ≤ max (kindOf s : Int) (kindOf new) := by
      have := hkind s; omega
    have hdiv : ssizeMax / max (kindOf s : Int) (kindOf new) ≤ ssizeMax := Int.ediv_le_self _ (by omega)
    have hdivnn : 0 ≤ ssizeMax / max (kindOf s : Int) (kindOf new) := Int.ediv_nonneg (by omega) (by omega)
    by_cases hc1 : old.length < new.length ∧ ((new.length : Int) - old.length) > (ssizeMax - s.length) / n
    · rw [if_pos hc1]
      have h2 := (ovf_iff hnpos).mp hc1.2
      rw [Int.mul_comm] at h2
      generalize (n : Int) * ((new.length : Int) - old.length) = prod at *
      have hgt : ((new.intercalate (splitN old mc.toNat s)).length : Int) >
          ssizeMax / max (kindOf s : Int) (kindOf new) := by omega
      simp only [hgt, ↓reduceIte]
      rfl
    · rw [if_neg hc1]
      have hsmall : (s.length : Int) + n * ((new.length : Int) - old.length) ≤ ssizeMax := by
        by_cases hlt : old.length < new.length
        · have h3 : ¬ ((ssizeMax - s.length) / n < (new.length : Int) - old.length) := fun h => hc1 ⟨hlt, h⟩
          rw [Int.ediv_lt_iff_lt_mul hnpos, Int.mul_comm] at h3
          omega
        · have : (n : Int) * ((new.length : Int) - old.length) ≤ 0 :=
            Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
          omega
      generalize (n : Int) * ((new.length : Int) - old.length) = prod at *
      by_cases hz : (s.length : Int) + prod = 0
      · have hgt : ¬ ((new.intercalate (splitN old mc.toNat s)).length : Int) >
            ssizeMax / max (kindOf s : Int) (kindOf new) := by omega
        rw [if_pos hz]; simp only [hgt, ↓reduceIte]
        congr 1; symm; apply List.eq_nil_of_length_eq_zero; omega
      · rw [if_neg hz]
        by_cases hbig : (s.length : Int) + prod > ssizeMax / max (kindOf s : Int) (kindOf new)
        · have hgt : ((new.intercalate (splitN old mc.toNat s)).length : Int) >
              ssizeMax / max (kindOf s : Int) (kindOf new) := by omega
          rw [if_pos hbig]; simp only [hgt, ↓reduceIte]; rfl
        · have hgt : ¬ ((new.intercalate (splitN old mc.toNat s)).length : Int) >
              ssizeMax / max (kindOf s : Int) (kindOf new) := by omega
          rw [if_neg hbig]; simp only [hgt, ↓reduceIte]
          rw [if_pos (show old.length > 0 by omega)]
          rw [Int.toNat_natCast, replaceLoop_eq new hp, ← hn, splitN_count hp]

theorem countAll_single (c : Nat) : ∀ s : Seq, countAll [c] s = (s.filter (· == c)).length := by
  intro s
  induction s with
  | nil => rw [countAll_none (by simp [findL, List.isPrefixOf])]; rfl
  | cons x xs ih =>
    by_cases hx : x = c
    · subst hx
      rw [countAll_some (by simp) (show findL [x] (x :: xs) = some 0 by simp [findL, List.isPrefixOf])]
      simp [ih]; omega
    · have hnp : ¬ [c].isPrefixOf (x :: xs) = true := by simp [List.isPrefixOf]; exact fun h => hx h.symm
      have hfl : (List.filter (· == c) (x :: xs)).length = (List.filter (· == c) xs).length := by
        simp [List.filter_cons, hx]
      rw [hfl, ← ih]
      cases hf : findL [c] xs with
      | none =>
        rw [countAll_none hf, countAll_none (by rw [findL_cons_nomatch hnp, hf]; rfl)]
      | some i =>
        rw [countAll_some (by simp) (by rw [findL_cons_nomatch hnp, hf]; rfl : findL [c] (x :: xs) = some (i + 1)),
          countAll_some (by simp) hf]
        simp only [List.length_singleton, List.drop_succ_cons]

theorem countChar_eq (s : Seq) (c : Nat) {mc : Int} (hm : 0 < mc) :
    countChar s c mc = countN [c] mc.toNat s := by
  rw [countN_eq_min (by simp), countAll_single, countChar]
  omega

/-- `bytes.replace` (`stringlib_replace` and its helpers, transmogrify.h:276-737)
with a non-empty `old` is the split-join replacement, raising `OverflowError`
exactly when the result is longer than `PY_SSIZE_T_MAX`. -/
theorem bytesReplace_eq {s old new : Seq} {k : Int} (hp : old ≠ []) (hs : (s.length : Int) < ssizeMax)
    (hk1 : ssizeMin ≤ k) (hk2 : k ≤ ssizeMax) :
    bytesReplace s old new k =
      if ((new.intercalate (splitN old (rounds k s) s)).length : Int) > ssizeMax
      then .error (.overflowError "replace bytes is too long")
      else .ok (new.intercalate (splitN old (rounds k s) s)) := by
  have hpl : old.length ≥ 1 := List.length_pos_iff.mpr hp
  have hMpos : (0 : Int) < ssizeMax := by unfold ssizeMax; omega
  have hnone : (∀ j, ¬ Occ s old j) →
      (if ((new.intercalate (splitN old (rounds k s) s)).length : Int) > ssizeMax
        then (.error (.overflowError "replace bytes is too long") : Py Seq)
        else .ok (new.intercalate (splitN old (rounds k s) s))) = .ok s := by
    intro h
    rw [splitN_noocc h]; simp; omega
  rw [← splitN_mc hp s hs k]
  rw [← splitN_mc hp s hs k] at hnone
  simp only [bytesReplace, argSsize_ok hk1 hk2, bind, Except.bind, pure, Except.pure]
  generalize hmc : (if k < 0 then ssizeMax else k) = mc at *
  by_cases hl : (s.length : Int) < old.length
  · rw [if_pos hl, hnone (not_occ_of_long (by omega))]
  rw [if_neg hl]
  by_cases h0 : mc = 0
  · rw [if_pos h0]; subst h0; simp [splitN]; omega
  rw [if_neg h0]
  have hmpos : 0 < mc := by
    rw [← hmc]; split <;> omega
  rw [if_neg (show ¬ ((old.length : Int) = 0) by omega)]
  have hcountL : stringlibCount s s.length old mc = countN old mc.toNat s := stringlibCount_rounds hp hmpos
  have hcountC : old.length = 1 → countChar s old.head! mc = countN old mc.toNat s := by
    intro h1
    obtain ⟨c, rfl⟩ : ∃ c, old = [c] := by
      match old, h1 with
      | [c], _ => exact ⟨c, rfl⟩
    exact countChar_eq s c hmpos
  have hlen := length_intercalate_splitN new hp mc.toNat s
  have hcl := countN_length (p := old) mc.toNat s
  -- counted branches without an overflow check (deletion)
  have shrink : new = [] → ∀ cnt : Int, cnt = countN old mc.toNat s →
      (if cnt = 0 then (.ok s : Py Seq) else .ok (replaceLoop old [] cnt.toNat s)) =
      (if ((new.intercalate (splitN old mc.toNat s)).length : Int) > ssizeMax
        then .error (.overflowError "replace bytes is too long")
        else .ok (new.intercalate (splitN old mc.toNat s))) := by
    intro hn cnt hc
    subst hn
    have : (countN old mc.toNat s : Int) * ((([] : Seq).length : Int) - old.length) ≤ 0 :=
      Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by simp)
    have hL : ¬ ((([] : Seq).intercalate (splitN old mc.toNat s)).length : Int) > ssizeMax := by omega
    simp only [hL, ↓reduceIte]
    by_cases h : cnt = 0
    · have : countN old mc.toNat s = 0 := by omega
      simp only [h, ↓reduceIte]
      rw [split_join_single [] hp _ s (by omega)]
    · simp only [h, ↓reduceIte]
      rw [hc, Int.toNat_natCast, replaceLoop_eq [] hp, splitN_count hp]
  -- counted branches with an overflow check
  have grow : ∀ cnt : Int, cnt = countN old mc.toNat s → ∀ d : Int, d = (new.length : Int) - old.length →
      (if cnt = 0 then (.ok s : Py Seq) else
        if d > (ssizeMax - s.length) / cnt then .error (.overflowError "replace bytes is too long")
        else .ok (replaceLoop old new cnt.toNat s)) =
      (if ((new.intercalate (splitN old mc.toNat s)).length : Int) > ssizeMax
        then .error (.overflowError "replace bytes is too long")
        else .ok (new.intercalate (splitN old mc.toNat s))) := by
    intro cnt hc d hd
    by_cases h : cnt = 0
    · have : countN old mc.toNat s = 0 := by omega
      have hj := split_join_single new hp mc.toNat s (by omega)
      have hL : ¬ ((s.length : Int) > ssizeMax) := by omega
      rw [hj]; simp only [h, hL, ↓reduceIte]
    · simp only [h, ↓reduceIte]
      have hpos : 0 < cnt := by omega
      have hiff := ovf_iff (a := d) (b := ssizeMax - s.length) hpos
      rw [hd, hc, Int.mul_comm] at hiff
      rw [hd, hc]
      generalize (countN old mc.toNat s : Int) * ((new.length : Int) - old.length) = prod at *
      by_cases hov : (new.length : Int) - old.length > (ssizeMax - s.length) / countN old mc.toNat s
      · have hL : ((new.intercalate (splitN old mc.toNat s)).length : Int) > ssizeMax := by
          have := hiff.mp hov; omega
        simp only [hov, hL, ↓reduceIte]
      · have hL : ¬ ((new.intercalate (splitN old mc.toNat s)).length : Int) > ssizeMax := by
          intro h'; exact hov (hiff.mpr (by omega))
        simp only [hov, hL, ↓reduceIte]
        rw [Int.toNat_natCast, replaceLoop_eq new hp, splitN_count hp]
  by_cases hn0 : (new.length : Int) = 0
  · rw [if_pos hn0]
    have hnew : new = [] := List.eq_nil_of_length_eq_zero (by omega)
    by_cases h1 : (old.length : Int) = 1
    · rw [if_pos h1, hcountC (by omega)]
      rw [shrink hnew _ rfl]
    · rw [if_neg h1, hcountL]
      rw [shrink hnew _ rfl]
  rw [if_neg hn0]
  by_cases heq : (old.length : Int) = new.length
  · rw [if_pos heq]
    have heq' : old.length = new.length := by omega
    have hsame := length_split_join new hp mc.toNat s heq'
    have hL : ¬ ((new.intercalate (splitN old mc.toNat s)).length : Int) > ssizeMax := by omega
    simp only [hL, ↓reduceIte]
    by_cases h1 : (old.length : Int) = 1
    · rw [if_pos h1]
      obtain ⟨c, rfl⟩ : ∃ c, old = [c] := by
        match old, (show old.length = 1 by omega) with
        | [c], _ => exact ⟨c, rfl⟩
      obtain ⟨d, rfl⟩ : ∃ d, new = [d] := by
        match new, (show new.length = 1 by simp at heq'; omega) with
        | [d], _ => exact ⟨d, rfl⟩
      simp only [List.head!, findChar_eq, ↓reduceIte]
      cases hf : findL [c] s with
      | none => simp [optIdx, splitN_noocc (findL_eq_none.mp hf)]
      | some q =>
        simp only [optIdx, show ¬ ((q : Int) < 0) by omega, ↓reduceIte, Int.toNat_natCast]
        rw [replaceChars_prefix c d mc s q hf, replaceChars_eq]
    · rw [if_neg h1, stringlibFind_some_or (by omega)]
      cases hf : findL old s with
      | none => simp [optOff, splitN_noocc (findL_eq_none.mp hf)]
      | some i =>
        simp only [optOff, Int.zero_add, show ¬ ((i : Int) = -1) by omega, ↓reduceIte, Int.toNat_natCast]
        obtain ⟨m, hm⟩ : ∃ m, mc.toNat = m + 1 := ⟨mc.toNat - 1, by omega⟩
        rw [hm, splitN_succ_some hf, intercalate_cons_ne (splitN_ne_nil _ _ _),
          replaceInplace_eq new hp, show (mc - 1).toNat = m by omega, List.append_assoc]
  rw [if_neg heq]
  by_cases h1 : (old.length : Int) = 1
  · rw [if_pos h1, hcountC (by omega)]
    rw [← grow _ rfl ((new.length : Int) - 1) (by omega)]
    split
    · rfl
    · split
      · rfl
      · rfl
  · rw [if_neg h1, hcountL]
    rw [← grow _ rfl ((new.length : Int) - old.length) rfl]
    split
    · rfl
    · split
      · rfl
      · rfl

/-! ## Properties -/

/-- `split_char`/`rsplit_char` (split.h:100-140, :240-277), the fast paths for
a one-character separator, agree with the general loops of `STRINGLIB(split)`
and `STRINGLIB(rsplit)` for every string and every `maxcount`. -/
def SplitCharFastPath : Prop :=
  ∀ (c : Nat) (mc : Int) (s : Seq),
    splitChar c mc s = splitLoop [c] mc s ∧ rsplitCharLoop c mc s = rsplitLoop [c] mc s

theorem splitCharFastPath_proven : SplitCharFastPath :=
  fun c mc s => ⟨splitChar_eq c mc s, rsplitCharLoop_eq c mc s⟩

/-- `replace` is consistent with `split` + `join`, for `str` and `bytes`: for
a non-empty `old` and every `count` (negative meaning "all"),
`s.split(old, count)` gives the same pieces for `str` and `bytes`, `old.join`
of them is `s`, and `s.replace(old, new, count) == new.join(s.split(old, count))`,
except that `replace` raises `OverflowError` exactly when the result would
be too long: longer than `PY_SSIZE_T_MAX` for `bytes`, and for `str` longer
than `PY_SSIZE_T_MAX / kind` when the lengths of `old` and `new` differ and
something is replaced (unicodeobject.c:10973-10987). Preconditions: `len(s) <
sys.maxsize` (type invariant) and `count` a valid `Py_ssize_t` (otherwise both
raise the same `OverflowError` from argument parsing). -/
def ReplaceSplitJoin : Prop :=
  ∀ (s old new : Seq) (k : Int), old ≠ [] → (s.length : Int) < ssizeMax →
    ssizeMin ≤ k → k ≤ ssizeMax →
    ∃ ps, strSplit s (some old) k = .ok ps ∧ bytesSplit s (some old) k = .ok ps ∧
      old.intercalate ps = s ∧
      strReplace s old new k =
        (if old.length ≠ new.length ∧ ps.length ≠ 1 ∧
            ((new.intercalate ps).length : Int) > ssizeMax / max (kindOf s : Int) (kindOf new)
         then .error (.overflowError "replace string is too long") else .ok (new.intercalate ps)) ∧
      bytesReplace s old new k =
        (if ((new.intercalate ps).length : Int) > ssizeMax
         then .error (.overflowError "replace bytes is too long") else .ok (new.intercalate ps))

theorem replaceSplitJoin_proven : ReplaceSplitJoin := by
  intro s old new k hp hs hk1 hk2
  exact ⟨_, strSplit_some hp hs hk1 hk2, bytesSplit_some hp hs hk1 hk2, intercalate_splitN hp _ s,
    strReplace_eq hp hs hk1 hk2, bytesReplace_eq hp hs hk1 hk2⟩

theorem maxCharValue_ge (s : Seq) : 127 ≤ maxCharValue s := by
  unfold maxCharValue; split <;> (try split) <;> (try split) <;> omega

/-- The empty-`old` (interleave) branches of `str` and `bytes` `replace` agree. -/
theorem replace_empty_old_str_bytes (s new : Seq) (k : Int) (hs : ∀ x ∈ s, x < 256) (hnew : ∀ x ∈ new, x < 256)
    (hk1 : ssizeMin ≤ k) (hk2 : k ≤ ssizeMax) :
    strReplace s [] new k = bytesReplace s [] new k ∨
    (strReplace s [] new k = .error (.overflowError "replace string is too long") ∧
     bytesReplace s [] new k = .error (.overflowError "replace bytes is too long")) := by
  have hMpos : (0 : Int) < ssizeMax := by unfold ssizeMax; omega
  have ks : kindOf s = 1 := kindOf_of_all hs
  have kn : kindOf new = 1 := kindOf_of_all hnew
  have hmax : ¬ maxCharValue s < maxCharValue ([] : Seq) := by
    have := maxCharValue_ge s; have : maxCharValue ([] : Seq) = 127 := rfl; omega
  simp only [strReplace, bytesReplace, argSsize_ok hk1 hk2, bind, Except.bind, pure, Except.pure, hmax,
    List.length_nil, ↓reduceIte]
  generalize hmc : (if k < 0 then ssizeMax else k) = mc
  by_cases h0 : mc = 0
  · left; simp [h0]
  have hmpos : 0 < mc := by rw [← hmc]; split <;> omega
  by_cases hn : new = []
  · left; subst hn; simp
  have hnl : new.length ≠ 0 := by simpa using hn
  simp [h0, hnl, stringlibCount, ks, kn, show ¬ ((s.length : Int) < 0) by omega, Ne.symm hnl]
  have hsame : (if mc ≤ (s.length : Int) then mc else (s.length : Int) + 1) =
      (if (s.length : Int) < mc then (s.length : Int) + 1 else mc) := by split <;> split <;> omega
  rw [hsame]
  generalize hn' : (if (s.length : Int) < mc then (s.length : Int) + 1 else mc) = n
  have hnpos : 0 < n := by rw [← hn']; split <;> omega
  have hnl0 : 0 < new.length := by omega
  simp only [show ¬ n = 0 by omega, hnl0, true_and, ↓reduceIte]
  by_cases hc : (ssizeMax - (s.length : Int)) / n < new.length
  · right; simp only [hc, ↓reduceIte]; exact ⟨rfl, rfl⟩
  · left
    have h3 := hc
    rw [Int.ediv_lt_iff_lt_mul hnpos, Int.mul_comm] at h3
    have hpos : (0 : Int) < n * new.length := Int.mul_pos hnpos (by omega)
    generalize n * (new.length : Int) = prod at *
    simp only [hc, show ¬ ((s.length : Int) + prod = 0) by omega, show ¬ (ssizeMax < (s.length : Int) + prod) by omega,
      ↓reduceIte]

/-- `str.replace` (three branches in unicodeobject.c) and `bytes.replace`
(seven helpers in transmogrify.h) agree on byte-valued strings for every
`old` (empty included), `new` and `count`: the same result, or both
`OverflowError`. Precondition: `len(s) < sys.maxsize` (type invariant). -/
def ReplaceStrBytes : Prop :=
  ∀ (s old new : Seq) (k : Int), (∀ x ∈ s, x < 256) → (∀ x ∈ old, x < 256) → (∀ x ∈ new, x < 256) →
    (s.length : Int) < ssizeMax →
    strReplace s old new k = bytesReplace s old new k ∨
    (strReplace s old new k = .error (.overflowError "replace string is too long") ∧
     bytesReplace s old new k = .error (.overflowError "replace bytes is too long"))

theorem replaceStrBytes_proven : ReplaceStrBytes := by
  intro s old new k hs hold hnew hlen
  have hMpos : (0 : Int) < ssizeMax := by unfold ssizeMax; omega
  by_cases hk : ssizeMin ≤ k ∧ k ≤ ssizeMax
  case neg => left; simp [strReplace, bytesReplace, argSsize_err hk, bind, Except.bind]
  obtain ⟨hk1, hk2⟩ := hk
  have ks : kindOf s = 1 := kindOf_of_all hs
  have kn : kindOf new = 1 := kindOf_of_all hnew
  by_cases hp : old = []
  case neg =>
    rw [strReplace_eq hp hlen hk1 hk2, bytesReplace_eq hp hlen hk1 hk2, ks, kn]
    simp only [Int.natCast_one, Int.max_self, Int.ediv_one]
    generalize hps : splitN old (rounds k s) s = ps
    have hc := countN_length (p := old) (rounds k s) s
    have hl := length_intercalate_splitN new hp (rounds k s) s
    rw [hps] at hc hl
    by_cases hbig : ((new.intercalate ps).length : Int) > ssizeMax
    · right
      have h1 : old.length ≠ new.length := by
        intro h; rw [h] at hl; simp at hl; omega
      have h2 : ps.length ≠ 1 := by
        intro h; have : countN old (rounds k s) s = 0 := by omega
        rw [this] at hl; simp at hl; omega
      simp [h1, h2, hbig]
    · left; simp [hbig]
  subst hp
  exact replace_empty_old_str_bytes s new k hs hnew hk1 hk2

/-! ## Whitespace split -/

/-- An upper bound on the number of words, as `split_whitespace` sees them. -/
def wsBound (isSp : Nat → Bool) : Seq → Nat
  | [] => 0
  | x :: xs => if isSp x then (xs.length + 1) / 2 else (xs.length + 2) / 2

theorem splitWs_small (isSp : Nat → Bool) {rest : Seq} (h : wsBound isSp rest = 0) (mc : Int) :
    splitWs isSp mc rest = [] := by
  have hd : rest.dropWhile isSp = [] := by
    match rest, h with
    | [], _ => rfl
    | [x], h =>
      simp only [wsBound, List.length_nil] at h
      split at h
      · next hx => simp [List.dropWhile_cons_of_pos hx]
      · omega
    | x :: y :: ys, h => simp only [wsBound, List.length_cons] at h; split at h <;> omega
  rw [splitWs]
  split
  · split
    · rfl
    · next c cs h' => rw [hd] at h'; cases h'
  · simp [hd]

theorem splitWs_congr {f g : Nat → Bool} :
    ∀ (rest : Seq) (mc : Int), (∀ x ∈ rest, f x = g x) → splitWs f mc rest = splitWs g mc rest := by
  intro rest
  induction rest using (measure List.length).wf.induction with
  | _ rest ih =>
    intro mc h
    have hd : rest.dropWhile f = rest.dropWhile g := dropWhile_congr h
    rw [splitWs, splitWs]
    by_cases hm : mc > 0
    · simp only [hm, ↓reduceIte]
      split
      · next h1 =>
        split
        · rfl
        · next c cs h2 => rw [← hd, h1] at h2; cases h2
      · next c cs h1 =>
        split
        · next h2 => rw [← hd, h1] at h2; cases h2
        · next c' cs' h2 =>
          rw [← hd, h1] at h2
          obtain ⟨rfl, rfl⟩ := List.cons.inj h2
          have hsub : ∀ x ∈ c :: cs, x ∈ rest := fun x hx =>
            (List.dropWhile_suffix (l := rest) f).subset (by rw [h1]; exact hx)
          have hcs : ∀ x ∈ cs, f x = g x := fun x hx => h x (hsub x (List.mem_cons_of_mem c hx))
          have hn : ∀ x ∈ cs, (!f x) = (!g x) := fun x hx => by rw [hcs x hx]
          rw [takeWhile_congr hn, dropWhile_congr hn]
          congr 1
          have := dropWhile_length_le (fun x => !g x) cs
          have h3 := dropWhile_length_le f rest
          rw [h1] at h3; simp only [List.length_cons] at h3
          exact ih _ (show (cs.dropWhile (fun x => !g x)).length < rest.length by omega) _
            (fun x hx => hcs x ((List.dropWhile_suffix _).subset hx))
    · simp only [hm, ↓reduceIte, hd]

theorem splitWs_sat (isSp : Nat → Bool) :
    ∀ (rest : Seq) (mc mc' : Int), (wsBound isSp rest : Int) ≤ mc → (wsBound isSp rest : Int) ≤ mc' →
      splitWs isSp mc rest = splitWs isSp mc' rest := by
  intro rest
  induction rest using (measure List.length).wf.induction with
  | _ rest ih =>
    intro mc mc' h1 h2
    by_cases h0 : wsBound isSp rest = 0
    · rw [splitWs_small isSp h0, splitWs_small isSp h0]
    have hm : mc > 0 := by omega
    have hm' : mc' > 0 := by omega
    rw [splitWs, splitWs]
    simp only [hm, hm', ↓reduceIte]
    split
    · rfl
    · next c cs hr =>
      congr 1
      have hlen_r := dropWhile_length_le isSp rest
      rw [hr] at hlen_r
      simp only [List.length_cons] at hlen_r
      generalize hr2 : cs.dropWhile (fun x => !isSp x) = r2
      have hr2len : r2.length ≤ cs.length := by rw [← hr2]; exact dropWhile_length_le _ cs
      have hb2 : wsBound isSp r2 ≤ r2.length / 2 := by
        match r2, hr2 with
        | [], _ => simp [wsBound]
        | y :: ys, h =>
          have := List.head_dropWhile_not (fun x => !isSp x) (l := cs) (by rw [h]; simp)
          simp only [h, List.head_cons, Bool.not_eq_false'] at this
          simp [wsBound, this]
      -- the bound drops by one per word
      have hstep : wsBound isSp r2 + 1 ≤ wsBound isSp rest := by
        match rest, hr with
        | x :: xs, hr =>
          have hw : wsBound isSp (x :: xs) =
              if isSp x then (xs.length + 1) / 2 else (xs.length + 2) / 2 := rfl
          rw [hw]
          by_cases hx : isSp x = true
          · rw [if_pos hx]
            rw [List.dropWhile_cons_of_pos hx] at hr
            have := dropWhile_length_le isSp xs
            rw [hr] at this; simp only [List.length_cons] at this; omega
          · rw [if_neg hx]
            rw [List.dropWhile_cons_of_neg hx] at hr
            obtain ⟨-, rfl⟩ := List.cons.inj hr
            omega
        | [], hr => simp at hr
      exact ih r2 (show r2.length < rest.length by omega) (mc - 1) (mc' - 1) (by omega) (by omega)

/-- The `maxcount` that `str.split()` computes, `(len - 1) / 2 + 1`, covers every word. -/
theorem strWsMaxcount_bound (isSp : Nat → Bool) (s : Seq) :
    (wsBound isSp s : Int) ≤ strWsMaxcount s.length (-1) := by
  have hb : wsBound isSp s ≤ (s.length + 1) / 2 := by
    cases s with
    | nil => simp [wsBound]
    | cons x xs => simp only [wsBound, List.length_cons]; split <;> omega
  simp only [strWsMaxcount, show (-1 : Int) < 0 by decide, ↓reduceIte]
  rcases hl : s.length with _ | n
  · rw [hl] at hb; simp at hb
    have : Int.tdiv (((0 : Nat) : Int) - 1) 2 = 0 := by decide
    omega
  · rw [hl] at hb
    rw [show ((n + 1 : Nat) : Int) - 1 = (n : Int) by omega, Int.tdiv_eq_ediv_of_nonneg (by omega)]
    omega

theorem wsBound_le (isSp : Nat → Bool) (s : Seq) : wsBound isSp s ≤ s.length := by
  cases s with
  | nil => simp [wsBound]
  | cons x xs => simp only [wsBound, List.length_cons]; split <;> omega

theorem wsBound_reverse_le (isSp : Nat → Bool) (s : Seq) : wsBound isSp s.reverse ≤ (s.length + 1) / 2 := by
  cases h : s.reverse with
  | nil => simp [wsBound]
  | cons x xs =>
    have : s.length = xs.length + 1 := by rw [← List.length_reverse, h]; simp
    simp only [wsBound]; split <;> omega

theorem wsBound_le_half (isSp : Nat → Bool) (s : Seq) : wsBound isSp s ≤ (s.length + 1) / 2 := by
  cases s with
  | nil => simp [wsBound]
  | cons x xs => simp only [wsBound, List.length_cons]; split <;> omega

/-- Characters that `str.isspace()` accepts but `bytes.isspace()` does not
are exactly where `Py_UNICODE_ISSPACE` and `Py_ISSPACE` differ on bytes. -/
theorem uniSpace_byteSpace {x : Nat} (h1 : x < 256) (h2 : strOnlySpace x = false) : uniSpace x = byteSpace x := by
  simp only [strOnlySpace, Bool.or_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne] at h2
  simp only [uniSpace, byteSpace]
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  omega

theorem rsplitLoop_none {p s : Seq} (h : rfindL p s = none) (mc : Int) : rsplitLoop p mc s = [s] := by
  rw [rsplitLoop]
  split
  · split
    · next pos h' => rw [h] at h'; cases h'
    · rfl
  · rfl

/-- `str.split`/`rsplit` and `bytes.split`/`rsplit` agree on byte-valued
strings for every separator and `maxsplit`, provided (for `sep=None`) the
string has none of the characters only `str` treats as whitespace
(\x1c-\x1f, \x85, \xa0). This covers the different default `maxcount`s:
`str` computes `(len - 1) / 2 + 1` (whitespace) and `len / len(sep) + 1`
(unicodeobject.c:10579-10614) where `bytes` uses `PY_SSIZE_T_MAX`.
Precondition: `len(s) < sys.maxsize` (type invariant). -/
def SplitStrBytes : Prop :=
  ∀ (s : Seq) (sep : Option Seq) (k : Int), (∀ x ∈ s, x < 256) → (s.length : Int) < ssizeMax →
    (∀ p, sep = some p → ∀ x ∈ p, x < 256) →
    (sep = none → ∀ x ∈ s, strOnlySpace x = false) →
    strSplit s sep k = bytesSplit s sep k ∧ strRSplit s sep k = bytesRSplit s sep k

theorem splitStrBytes_proven : SplitStrBytes := by
  intro s sep k hs hlen hsep hws
  have hMpos : (0 : Int) < ssizeMax := by unfold ssizeMax; omega
  by_cases hk : ssizeMin ≤ k ∧ k ≤ ssizeMax
  case neg =>
    simp [strSplit, bytesSplit, strRSplit, bytesRSplit, argSsize_err hk, bind, Except.bind]
  obtain ⟨hk1, hk2⟩ := hk
  cases sep with
  | none =>
    have hcong : ∀ x ∈ s, uniSpace x = byteSpace x := fun x hx => uniSpace_byteSpace (hs x hx) (hws rfl x hx)
    have hcongr : ∀ x ∈ s.reverse, uniSpace x = byteSpace x := fun x hx => hcong x (List.mem_reverse.mp hx)
    simp only [strSplit, bytesSplit, strRSplit, bytesRSplit, argSsize_ok hk1 hk2, bind, Except.bind,
      pure, Except.pure, rsplitWs]
    rw [splitWs_congr s _ hcong, splitWs_congr s.reverse _ hcongr]
    have hb := wsBound_le_half byteSpace s
    have hbr := wsBound_reverse_le byteSpace s
    have hm : ∀ q : Seq, q.length = s.length → wsBound byteSpace q ≤ (s.length + 1) / 2 →
        splitWs byteSpace (strWsMaxcount s.length k) q =
          splitWs byteSpace (if k < 0 then ssizeMax else k) q := by
      intro q hq hbq
      by_cases hneg : k < 0
      · simp only [strWsMaxcount, hneg, ↓reduceIte]
        apply splitWs_sat
        · have := strWsMaxcount_bound byteSpace s
          simp only [strWsMaxcount, show (-1 : Int) < 0 by decide, ↓reduceIte] at this
          have hb' := wsBound_le_half byteSpace s
          rcases hl : s.length with _ | n
          · rw [hl] at hbq; simp at hbq ⊢
            have : Int.tdiv (((0 : Nat) : Int) - 1) 2 = 0 := by decide
            omega
          · rw [hl] at hbq
            rw [show ((n + 1 : Nat) : Int) - 1 = (n : Int) by omega, Int.tdiv_eq_ediv_of_nonneg (by omega)]
            omega
        · omega
      · simp [strWsMaxcount, hneg]
    rw [hm s rfl hb, hm s.reverse (by simp) hbr]
    exact ⟨rfl, rfl⟩
  | some p =>
    have hp' := hsep p rfl
    by_cases hp : p = []
    · subst hp
      have h1 : kindOf ([] : Seq) = 1 := rfl
      have h2 := kindOf_cases s
      have h3 : ¬ (kindOf s < kindOf ([] : Seq)) := by omega
      simp [strSplit, bytesSplit, strRSplit, bytesRSplit, argSsize_ok hk1 hk2, bind, Except.bind,
        stringlibSplit, stringlibRSplit, h3]
    constructor
    · rw [strSplit_some hp hlen hk1 hk2, bytesSplit_some hp hlen hk1 hk2]
    · have hpl : p.length ≥ 1 := List.length_pos_iff.mpr hp
      have hk' := bytes_kind hs hp'
      simp only [strRSplit, bytesRSplit, argSsize_ok hk1 hk2, bind, Except.bind, pure, Except.pure]
      by_cases hl : s.length < p.length
      · simp only [hk', hl, or_true, ↓reduceIte]
        unfold stringlibRSplit
        rw [if_neg (by omega)]
        have hnone : rfindL p s = none := rfindL_eq_none.mpr (not_occ_of_long hl)
        split
        · next h1 =>
          obtain ⟨c, rfl⟩ : ∃ c, p = [c] := by
            match p, h1 with
            | [c], _ => exact ⟨c, rfl⟩
          simp only [List.head!, rsplitCharLoop_eq, rsplitLoop_none hnone]; rfl
        · simp only [rsplitLoop_none hnone]; rfl
      · simp only [hk', hl, or_false, ↓reduceIte]
        unfold stringlibRSplit
        have hd := div_succ_le (a := s.length) hpl
        have hmc : rsplitLoop p (strSepMaxcount s.length p.length k) s =
            rsplitLoop p (if k < 0 then ssizeMax else k) s := by
          by_cases hneg : k < 0
          · simp only [strSepMaxcount, hneg, ↓reduceIte, show p.length ≠ 0 by omega]
            rw [if_neg (by omega)]
            apply rsplitLoop_sat hp <;> omega
          · simp [strSepMaxcount, hneg]
        simp only [show ¬ p.length = 0 by omega, ↓reduceIte]
        by_cases h1 : p.length = 1
        · rw [if_pos h1, if_pos h1]
          obtain ⟨c, rfl⟩ : ∃ c, p = [c] := by
            match p, h1 with
            | [c], _ => exact ⟨c, rfl⟩
          simp only [List.head!, rsplitCharLoop_eq, hmc]
        · rw [if_neg h1, if_neg h1, hmc]

end PyLean.StrSearch
