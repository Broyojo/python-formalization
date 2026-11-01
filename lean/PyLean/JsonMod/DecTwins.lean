import PyLean.JsonMod.DecString
import PyLean.JsonMod.DecNumber
import PyLean.JsonMod.DecSteps

/-!
The C and pure-Python decoders agree at every non-negative index, up to the
messages of two string errors (`ErrRel`).
-/

namespace PyLean.JsonMod

open PyLean

/-! ### Lengths of the `NUMBER_RE` groups -/

theorem reSign_len (t : PStr) : (reSign t).1.length + (reSign t).2.length = t.length := by
  cases t with
  | nil => rfl
  | cons c r => rw [reSign_cons]; split <;> simp <;> omega

theorem reInt_len {t ip : PStr} (h : reInt t = some ip) : ip.length ≤ t.length := by
  cases t with
  | nil => simp [reInt] at h
  | cons c r =>
    rw [reInt_cons] at h
    split at h
    · cases h; simp
    · split at h
      · cases h; simp [Nat.min_le_right]
      · cases h

theorem reFrac_len (t : PStr) : (reFrac t).length ≤ t.length := by
  cases t with
  | nil => simp [reFrac]
  | cons c r =>
    rw [reFrac_cons]
    split
    · split <;> simp [Nat.min_le_right]
    · simp

theorem reExp_len (t : PStr) : (reExp t).length ≤ t.length := by
  cases t with
  | nil => simp [reExp]
  | cons e r =>
    by_cases he : e = 101 ∨ e = 69
    · cases r with
      | nil => rw [reExp_nosign e [] he (by simp)]; simp [digitsLen]
      | cons c r' =>
        by_cases hc : c = 45 ∨ c = 43
        · rw [reExp_sign e c r' he hc]; split <;> simp [Nat.min_le_right]
        · rw [reExp_nosign e _ he (by intro c'' r'' h; simp at h; omega)]; split <;> simp [Nat.min_le_right]
    · rw [reExp_not e r he]; simp

theorem numberRe_len {t i fr ex : PStr} (h : numberRe t = some (i, fr, ex)) :
    i.length + fr.length + ex.length ≤ t.length := by
  unfold numberRe at h
  have hs := reSign_len t
  generalize hsg : reSign t = p at h hs
  obtain ⟨sign, t1⟩ := p
  simp only at h hs
  cases hi : reInt t1 with
  | none => rw [hi] at h; cases h
  | some ip =>
    rw [hi] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have h1 := reInt_len hi
    have h2 := reFrac_len (t1.drop ip.length)
    have h3 := reExp_len ((t1.drop ip.length).drop (reFrac (t1.drop ip.length)).length)
    simp only [List.length_drop, List.length_append] at h2 h3 ⊢
    omega

/-! ### Relations -/

/-- Converting `StopIteration` to `JSONDecodeError` keeps the relation. -/
def stopConv : DErr → DErr
  | .stop i => .jde "Expecting value" i
  | e => e

theorem ErrRel.stopConv {s : PStr} {pe ce : DErr} (h : ErrRel s pe ce) :
    ErrRel s (JsonMod.stopConv pe) ce := by
  rcases h with h | ⟨i, h1, h2⟩ | ⟨q, ch, h1, h2, h3, h4⟩ | ⟨q, ch, h1, h2, h3, h4⟩
  · subst h
    cases pe with
    | stop i => exact Or.inr (Or.inl ⟨i, rfl, rfl⟩)
    | jde m p => exact Or.inl rfl
    | exc e => exact Or.inl rfl
  · subst h1; exact Or.inr (Or.inl ⟨i, rfl, h2⟩)
  · subst h4; exact Or.inr (Or.inr (Or.inl ⟨q, ch, h1, h2, h3, rfl⟩))
  · subst h4; exact Or.inr (Or.inr (Or.inr ⟨q, ch, h1, h2, h3, rfl⟩))

theorem ResRel.fuel {α : Type} {s : PStr} : ResRel (α := α) s fuelOut fuelOut := ResRel.err_eq _

/-- `scanstring` at a non-negative position `e >= 1`. -/
theorem scanstring_rel (s : PStr) (strict : Bool) (e : Nat) (h1 : 1 ≤ e) (h2 : e ≤ s.length) :
    ResRel s (pyScanstring s (e : Int) strict) (cScanstring s e strict) := by
  unfold pyScanstring cScanstring
  have hb : ((e : Int) - 1) = ((e - 1 : Nat) : Int) := by omega
  have hn : ¬ s.length < e := by omega
  simp only [hb, clampPos_nat h2, hn, ↓reduceIte, cScanLoop_none]
  exact scanLoop_rel s strict (e - 1) (s.length + 1) (s.length + 1) e [] (by omega) (by omega) h2

/-- `JVal` of an object: `object_pairs_hook(pairs)` or `dict(pairs)`. -/
def accOf (cfg : DCfg) (pairs : List (PStr × JVal)) : List (PStr × JVal) :=
  if cfg.pairsHook.isSome then pairs else dictOf pairs

theorem dictOf_append (ps : List (PStr × JVal)) (k : PStr) (v : JVal) :
    dictOf (ps ++ [(k, v)]) = dictSet k v (dictOf ps) := by
  simp [dictOf, List.foldl_append]

theorem cAddPair_accOf (cfg : DCfg) (pairs : List (PStr × JVal)) (k : PStr) (v : JVal) :
    cAddPair cfg (accOf cfg pairs) k v = accOf cfg (pairs ++ [(k, v)]) := by
  unfold cAddPair accOf
  split <;> simp [dictOf_append]

theorem pyMkObj_accOf (cfg : DCfg) (pairs : List (PStr × JVal)) :
    pyMkObj cfg pairs = cFinish cfg (accOf cfg pairs) := by
  unfold pyMkObj cFinish accOf
  cases cfg.pairsHook <;> rfl

theorem cArrAfter_close {s : PStr} {e : Nat} {i : Int} (h : cArrAfter s e = .close i) :
    ∃ m : Nat, i = m ∧ m ≤ s.length := by
  unfold cArrAfter at h
  dsimp only at h
  split at h
  · cases h; exact ⟨_, rfl, by omega⟩
  · split at h
    · cases h
    · split at h <;> cases h

theorem cArrAfter_next {s : PStr} {e : Nat} {i : Int} (h : cArrAfter s e = .next i) : ∃ m : Nat, i = m := by
  unfold cArrAfter at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · cases h; exact ⟨_, rfl⟩

theorem cObjAfter_close {s : PStr} {e : Nat} {i : Int} (h : cObjAfter s e = .close i) :
    ∃ m : Nat, i = m ∧ m ≤ s.length := by
  unfold cObjAfter at h
  dsimp only at h
  split at h
  · cases h; exact ⟨_, rfl, by omega⟩
  · split at h
    · cases h
    · split at h <;> cases h

theorem cObjAfter_next {s : PStr} {e : Nat} {i : Int} (h : cObjAfter s e = .next i) : ∃ m : Nat, i = m := by
  unfold cObjAfter at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · cases h; exact ⟨_, rfl⟩

/-- `string[idx:idx + k] == lit` against the guarded reads of `scan_once_unicode`. -/
theorem lit_twin (s : PStr) (idx : Nat) (lit : String) (hk : 1 ≤ (cs lit).length) :
    (pySlice s (idx : Int) ((idx : Int) + ((cs lit).length : Nat)) = cs lit) ↔ litAt s idx lit = true := by
  rw [pySlice_nat]
  unfold litAt
  constructor
  · intro h
    have := congrArg List.length h
    simp only [List.length_take, List.length_drop] at this
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, h, and_true]
    omega
  · intro h
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    exact h.2

theorem litAt_le {s : PStr} {idx : Nat} {lit : String} (h : litAt s idx lit = true) (hk : 1 ≤ (cs lit).length) :
    idx + (cs lit).length ≤ s.length := by
  unfold litAt at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  omega

theorem ResRel.ok {α : Type} {s : PStr} (v : α) (k : Nat) (hk : k ≤ s.length) :
    ResRel s (.ok (v, (k : Int))) (.ok (v, k)) := Or.inl ⟨v, k, hk, rfl, rfl⟩

/-- A callback's result ending at `k`. -/
theorem ResRel.map {α : Type} {s : PStr} (r : DR α) (k : Nat) (hk : k ≤ s.length) :
    ResRel s (r.map (·, (k : Int))) (r.map (·, k)) := by
  cases r with
  | ok v => exact ResRel.ok v k hk
  | error e => exact ResRel.err_eq e

/-- Propagating an error from a nested call. -/
theorem ResRel.bind {α β : Type} {s : PStr} {py : DR (α × Int)} {c : DR (α × Nat)}
    (h : ResRel s py c) (fp : α × Int → DR (β × Int)) (fc : α × Nat → DR (β × Nat))
    (hok : ∀ v (k : Nat), k ≤ s.length → ResRel s (fp (v, k)) (fc (v, k))) :
    ResRel s (match py with | .ok r => fp r | .error e => .error e)
      (match c with | .ok r => fc r | .error e => .error e) := by
  rcases h with ⟨v, k, hk, rfl, rfl⟩ | ⟨pe, ce, rfl, rfl, he⟩
  · exact hok v k hk
  · exact Or.inr ⟨pe, ce, rfl, rfl, he⟩

/-- The same, where Python turns `StopIteration` into `JSONDecodeError`. -/
theorem ResRel.bindConv {α β : Type} {s : PStr} {py : DR (α × Int)} {c : DR (α × Nat)}
    (h : ResRel s py c) (fp : α × Int → DR (β × Int)) (fc : α × Nat → DR (β × Nat))
    (hok : ∀ v (k : Nat), k ≤ s.length → ResRel s (fp (v, k)) (fc (v, k))) :
    ResRel s (match py with
        | .error (.stop i) => .error (.jde "Expecting value" i)
        | .error err => .error err
        | .ok r => fp r)
      (match c with | .error err => .error err | .ok r => fc r) := by
  rcases h with ⟨v, k, hk, rfl, rfl⟩ | ⟨pe, ce, rfl, rfl, he⟩
  · exact hok v k hk
  · right
    refine ⟨stopConv pe, ce, ?_, rfl, he.stopConv⟩
    cases pe <;> rfl

theorem numberRe_head {t i fr ex : PStr} (h : numberRe t = some (i, fr, ex)) :
    ∃ c r, t = c :: r ∧ ((c = 45 ∧ ∃ d r', r = d :: r' ∧ isDigit d = true) ∨ (c ≠ 45 ∧ isDigit c = true)) := by
  unfold numberRe at h
  cases t with
  | nil => simp [reSign, reInt] at h
  | cons c r =>
    refine ⟨c, r, rfl, ?_⟩
    rw [reSign_cons] at h
    by_cases h45 : c = 45
    · subst h45
      simp only [↓reduceIte] at h
      left
      refine ⟨rfl, ?_⟩
      cases r with
      | nil => simp [reInt] at h
      | cons d r' =>
        refine ⟨d, r', rfl, ?_⟩
        rw [reInt_cons] at h
        by_cases h48 : d = 48
        · subst h48; rfl
        · by_cases h19 : 49 ≤ d ∧ d ≤ 57
          · simp [isDigit]; omega
          · simp [h48, h19] at h
    · simp only [h45, ↓reduceIte] at h
      right
      refine ⟨h45, ?_⟩
      rw [reInt_cons] at h
      by_cases h48 : c = 48
      · subst h48; rfl
      · by_cases h19 : 49 ≤ c ∧ c ≤ 57
        · simp [isDigit]; omega
        · simp [h48, h19] at h

theorem litAt_le' {s : PStr} {idx : Nat} {lit : String} (h : litAt s idx lit = true) (k : Nat)
    (hk : (cs lit).length = k) (hk1 : 1 ≤ k) : idx + k ≤ s.length := by
  have := litAt_le h (by omega)
  rw [hk] at this
  exact this

theorem accOf_nil (cfg : DCfg) : accOf cfg [] = [] := by
  unfold accOf; split <;> rfl

theorem lit_twin' (s : PStr) (idx : Nat) (lit : String) (k : Nat) (hk : (cs lit).length = k) (hk1 : 1 ≤ k) :
    (pySlice s (idx : Int) ((idx : Int) + (k : Int)) = cs lit) ↔ litAt s idx lit = true := by
  have := lit_twin s idx lit (by omega)
  rw [hk] at this
  exact this

theorem sim (cfg : DCfg) (s : PStr) : ∀ n : Nat,
    (∀ idx : Nat, ResRel s (pyScanOnce cfg s n (idx : Int)) (cScanOnce cfg s n idx)) ∧
    (∀ (e : Nat) (acc : List JVal), ResRel s (pyArrLoop cfg s n (e : Int) acc) (cArrLoop cfg s n e acc)) ∧
    (∀ (q : Nat) (pairs : List (PStr × JVal)), s[q]? = some 34 →
      ResRel s (pyObjLoop cfg s n ((q : Int) + 1) pairs) (cObjBody cfg s n q (accOf cfg pairs))) := by
  intro n
  induction n with
  | zero =>
    refine ⟨fun idx => ?_, fun e acc => ?_, fun q pairs _ => ?_⟩ <;>
      simp only [pyScanOnce, cScanOnce, pyArrLoop, cArrLoop, pyObjLoop, cObjBody] <;> exact ResRel.fuel
  | succ n ih =>
    obtain ⟨ihS, ihA, ihO⟩ := ih
    refine ⟨fun idx => ?_, fun e acc => ?_, fun q pairs hq => ?_⟩
    · -- scan_once
      simp only [pyScanOnce, cScanOnce, pyIndex_nat]
      by_cases hl : idx ≥ s.length
      · have : s[idx]? = none := List.getElem?_eq_none_iff.mpr hl
        simp only [this, hl, ↓reduceIte]
        exact ResRel.err_eq _
      · have hlt : idx < s.length := by omega
        have hs : s[idx]? = some (s.getD idx 0) := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
        generalize hc : s.getD idx 0 = c at hs
        simp only [hs, hl, ↓reduceIte]
        by_cases h34 : c = 34
        · subst h34
          simp only [↓reduceIte]
          rw [show (idx : Int) + 1 = ((idx + 1 : Nat) : Int) by omega]
          rcases scanstring_rel s cfg.strict (idx + 1) (by omega) (by omega) with
            ⟨v, k, hk, h1, h2⟩ | ⟨pe, ce, h1, h2, he⟩
          · rw [h1, h2]; exact ResRel.ok _ k hk
          · rw [h1, h2]; exact Or.inr ⟨pe, ce, rfl, rfl, he⟩
        simp only [h34, ↓reduceIte]
        by_cases h123 : c = 123
        · subst h123
          simp only [↓reduceIte]
          rw [show (idx : Int) + 1 = ((idx + 1 : Nat) : Int) by omega, slice_nat]
          by_cases hq : (s[idx + 1]?).toList = [34]
          · have hq' : s[idx + 1]? = some 34 := by
              cases h : s[idx + 1]? with
              | none => rw [h] at hq; simp at hq
              | some d => rw [h] at hq; simp at hq; rw [hq]
            have hw : wsEnd s (idx + 1) = idx + 1 := wsEnd_of_not_ws hq' (by rfl)
            simp only [hq, ne_eq, not_true_eq_false, ↓reduceIte]
            rw [hw]
            have hlt1 : idx + 1 < s.length := (List.getElem?_eq_some_iff.mp hq').1
            have hnl1 : ¬ s.length ≤ idx + 1 := by omega
            simp only [List.getD_eq_getElem?_getD, hq', Option.getD_some, ge_iff_le, hnl1, false_or,
              Nat.reduceEqDiff, not_false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false]
            have := ihO (idx + 1) [] hq'
            rwa [accOf_nil] at this
          · simp only [hq, ne_eq, not_false_eq_true, ↓reduceIte]
            rw [skipSlice0' s (idx + 1) (by omega)]
            generalize hw : wsEnd s (idx + 1) = w
            have hwl : w ≤ s.length := hw ▸ wsEnd_le (by omega)
            cases hd : s[w]? with
            | none =>
              have : s.length ≤ w := by have := List.getElem?_eq_none_iff.mp hd; omega
              simp [this]
              exact ResRel.err_eq _
            | some d =>
              have hwlt : w < s.length := (List.getElem?_eq_some_iff.mp hd).1
              have hnl : ¬ w ≥ s.length := by omega
              simp only [Option.toList_some, List.cons.injEq, and_true, hnl, false_or, getD_of_some hd]
              by_cases h125 : d = 125
              · subst h125
                simp only [↓reduceIte, ne_eq, not_true_eq_false, pyMkObj_accOf, accOf_nil]
                rw [show (w : Int) + 1 = ((w + 1 : Nat) : Int) by omega]
                exact ResRel.map _ (w + 1) (by omega)
              · simp only [h125, ↓reduceIte, ne_eq, not_false_eq_true]
                by_cases hd34 : d = 34
                · subst hd34
                  simp only [not_true_eq_false, ↓reduceIte]
                  have := ihO w [] hd
                  rwa [accOf_nil] at this
                · simp only [hd34, not_false_eq_true, ↓reduceIte]
                  exact ResRel.err_eq _
        simp only [h123, ↓reduceIte]
        by_cases h91 : c = 91
        · subst h91
          simp only [↓reduceIte]
          rw [show (idx : Int) + 1 = ((idx + 1 : Nat) : Int) by omega, slice_nat]
          rw [skipSlice' s (idx + 1) (by omega)]
          generalize hw : wsEnd s (idx + 1) = w
          have hwl : w ≤ s.length := hw ▸ wsEnd_le (by omega)
          cases hd : s[w]? with
          | none =>
            have : s.length ≤ w := by have := List.getElem?_eq_none_iff.mp hd; omega
            simp only [Option.toList_none, reduceCtorEq, ↓reduceIte, ge_iff_le, this, true_or]
            exact ihA w []
          | some d =>
            have hwlt : w < s.length := (List.getElem?_eq_some_iff.mp hd).1
            have hnl : ¬ w ≥ s.length := by omega
            simp only [Option.toList_some, List.cons.injEq, and_true, hnl, false_or, getD_of_some hd]
            by_cases h93 : d = 93
            · subst h93
              simp only [↓reduceIte, ne_eq, not_true_eq_false]
              exact ResRel.ok _ (w + 1) (by omega)
            · simp only [h93, ↓reduceIte, ne_eq, not_false_eq_true]
              exact ihA w []
        simp only [h91, ↓reduceIte]
        have L4n := lit_twin' s idx "null" 4 (by decide) (by decide)
        have L4t := lit_twin' s idx "true" 4 (by decide) (by decide)
        have L5 := lit_twin' s idx "false" 5 (by decide) (by decide)
        push_cast at L4n L4t L5
        simp only [L4n, L4t, L5]
        by_cases hn : c = 110 ∧ litAt s idx "null" = true
        · simp only [hn, and_self, ↓reduceIte]
          exact ResRel.ok (s := s) JVal.null (idx + 4) (litAt_le' hn.2 4 (by decide) (by decide))
        simp only [hn, ↓reduceIte]
        by_cases ht : c = 116 ∧ litAt s idx "true" = true
        · simp only [ht, and_self, ↓reduceIte]
          exact ResRel.ok (s := s) (JVal.bool true) (idx + 4) (litAt_le' ht.2 4 (by decide) (by decide))
        simp only [ht, ↓reduceIte]
        by_cases hf : c = 102 ∧ litAt s idx "false" = true
        · simp only [hf, and_self, ↓reduceIte]
          exact ResRel.ok (s := s) (JVal.bool false) (idx + 5) (litAt_le' hf.2 5 (by decide) (by decide))
        simp only [hf, ↓reduceIte]
        unfold pyScanNumber
        rw [clampPos_nat (by omega)]
        have L3 := lit_twin' s idx "NaN" 3 (by decide) (by decide)
        have L8 := lit_twin' s idx "Infinity" 8 (by decide) (by decide)
        have L9 := lit_twin' s idx "-Infinity" 9 (by decide) (by decide)
        push_cast at L3 L8 L9
        simp only [L3, L8, L9]
        rcases matchNumber_twin cfg s idx hlt with ⟨h1, h2⟩ | ⟨i, fr, ex, h1, h2⟩
        · rw [h1]
          simp only []
          by_cases hN : c = 78 ∧ litAt s idx "NaN" = true
          · simp only [hN, and_self, ↓reduceIte, cConst]
            rw [show (idx : Int) + 3 = ((idx + 3 : Nat) : Int) by omega,
              show (cs "NaN").length = 3 by decide]
            exact ResRel.map _ (idx + 3) (litAt_le' hN.2 3 (by decide) (by decide))
          simp only [hN, ↓reduceIte]
          by_cases hI : c = 73 ∧ litAt s idx "Infinity" = true
          · simp only [hI, and_self, ↓reduceIte, cConst]
            rw [show (idx : Int) + 8 = ((idx + 8 : Nat) : Int) by omega,
              show (cs "Infinity").length = 8 by decide]
            exact ResRel.map _ (idx + 8) (litAt_le' hI.2 8 (by decide) (by decide))
          simp only [hI, ↓reduceIte]
          by_cases hM : c = 45 ∧ litAt s idx "-Infinity" = true
          · simp only [hM, and_self, ↓reduceIte, cConst]
            rw [show (idx : Int) + 9 = ((idx + 9 : Nat) : Int) by omega,
              show (cs "-Infinity").length = 9 by decide]
            exact ResRel.map _ (idx + 9) (litAt_le' hM.2 9 (by decide) (by decide))
          simp only [hM, ↓reduceIte, h2]
          exact ResRel.err_eq _
        · rw [h1]
          simp only []
          obtain ⟨c0, r, hcr, hhead⟩ := numberRe_head h1
          have hc0 : c0 = c := by
            rw [drop_cons hlt] at hcr
            simp only [List.cons.injEq] at hcr
            rw [← hcr.1, hc]
          subst hc0
          have hN : ¬ (c0 = 78 ∧ litAt s idx "NaN" = true) := by
            rintro ⟨rfl, -⟩; rcases hhead with ⟨h, -⟩ | ⟨-, h⟩ <;> simp_all [isDigit]
          have hI : ¬ (c0 = 73 ∧ litAt s idx "Infinity" = true) := by
            rintro ⟨rfl, -⟩; rcases hhead with ⟨h, -⟩ | ⟨-, h⟩ <;> simp_all [isDigit]
          have hM : ¬ (c0 = 45 ∧ litAt s idx "-Infinity" = true) := by
            rintro ⟨rfl, hl9⟩
            rcases hhead with ⟨-, d, r', hr, hd⟩ | ⟨h, -⟩
            · have := (lit_twin' s idx "-Infinity" 9 (by decide) (by decide)).mpr hl9
              rw [pySlice_nat, hcr, hr] at this
              simp [cs] at this
              simp [this.1, isDigit] at hd
            · exact h rfl
          simp only [hN, hI, hM, ↓reduceIte, h2]
          have hL := numberRe_len h1
          simp only [List.length_drop] at hL
          by_cases hfl : fr ≠ [] ∨ ex ≠ []
          · simp only [hfl, ↓reduceIte]
            exact ResRel.map _ _ (by omega)
          · simp only [hfl, ↓reduceIte]
            exact ResRel.map _ _ (by omega)
    · -- array loop
      simp only [pyArrLoop, cArrLoop]
      rcases ihS e with ⟨v, k, hk, h1, h2⟩ | ⟨pe, ce, h1, h2, he⟩
      · rw [h1, h2]
        simp only []
        rw [arrAfter_twin s k hk]
        cases ha : cArrAfter s k with
        | close i =>
          obtain ⟨m, rfl, hm⟩ := cArrAfter_close ha
          simpa using ResRel.ok (s := s) (JVal.arr (acc ++ [v])) m hm
        | err x => exact ResRel.err_eq x
        | next i =>
          obtain ⟨m, rfl⟩ := cArrAfter_next ha
          simpa using ihA m (acc ++ [v])
      · rw [h1, h2]
        right
        refine ⟨stopConv pe, ce, ?_, rfl, he.stopConv⟩
        cases pe <;> rfl
    · -- object loop
      have hql : q < s.length := (List.getElem?_eq_some_iff.mp hq).1
      simp only [pyObjLoop, cObjBody]
      rw [show (q : Int) + 1 = ((q + 1 : Nat) : Int) by omega]
      rcases scanstring_rel s cfg.strict (q + 1) (by omega) (by omega) with
        ⟨key, k, hk, h1, h2⟩ | ⟨pe, ce, h1, h2, he⟩
      · rw [h1, h2]
        simp only []
        rw [objColon_twin s k hk]
        by_cases hcol : wsEnd s k ≥ s.length ∨ s.getD (wsEnd s k) 0 ≠ 58
        · simp only [hcol, ↓reduceIte]
          exact ResRel.err_eq _
        · simp only [hcol, ↓reduceIte]
          rcases ihS (wsEnd s (wsEnd s k + 1)) with ⟨v, k2, hk2, h3, h4⟩ | ⟨pe, ce, h3, h4, he⟩
          · rw [h3, h4]
            simp only []
            rw [objAfter_twin s k2 hk2]
            cases ha : cObjAfter s k2 with
            | close i =>
              obtain ⟨m, rfl, hm⟩ := cObjAfter_close ha
              simp only [Int.toNat_natCast, pyMkObj_accOf, cAddPair_accOf]
              exact ResRel.map _ m hm
            | err x => exact ResRel.err_eq x
            | next i =>
              obtain ⟨m, rfl⟩ := cObjAfter_next ha
              simp only [Int.toNat_natCast, cAddPair_accOf]
              by_cases hnq : m ≥ s.length ∨ s.getD m 0 ≠ 34
              · simp only [hnq, ↓reduceIte]
                exact ResRel.err_eq _
              · simp only [hnq, ↓reduceIte]
                have hlt : m < s.length := by omega
                have hm : s[m]? = some 34 := by
                  rw [List.getElem?_eq_getElem hlt]
                  simp only [Option.some.injEq]
                  have := hnq
                  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some] at this
                  omega
                exact ihO m _ hm
          · rw [h3, h4]
            right
            refine ⟨stopConv pe, ce, ?_, rfl, he.stopConv⟩
            cases pe <;> rfl
      · rw [h1, h2]
        exact Or.inr ⟨pe, ce, rfl, rfl, he⟩

end PyLean.JsonMod
