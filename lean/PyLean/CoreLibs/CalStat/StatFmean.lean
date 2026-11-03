import PyLean.CoreLibs.CalStat.StatLinReg
import PyLean.CoreLibs.Warn.Model

/-!
`fmean` (Lib/statistics.py:182-222) over a fallible iterable, with the `except` clauses decided by
a class relation `H` (`PyLean.CoreLibs.Warn.Hier`) rather than by exact class names, and its value on
int data: `math.fsum` of ints is exact while the sum of the magnitudes stays below `2**53`, so
`fmean` is the correctly rounded mean.
-/

namespace PyLean.CoreLibs.CalStat

open PyLean
open PyLean.CoreLibs.Warn (Hier HierOk isA)

/-- An iterable as `fmean` meets it: the outcome of `len(data)`, and what iterating it does: the
items it yields, then the end (`fin = none`) or the exception `e` its `__next__` raises
(`fin = some e`). A `StopIteration` raised by `__next__` of a C iterator or of a class with
`__next__` is the end of the iteration, so it is `none` here; a generator that lets one escape from
its body raises `RuntimeError` instead (PEP 479), which is `some` of that `RuntimeError`. -/
structure PyIter where
  len : Py Nat
  items : List PyN
  fin : Option PyExc

/-- A list: `len` is its length and iteration ends normally. -/
def PyIter.ofList (xs : List PyN) : PyIter := ⟨.ok xs.length, xs, none⟩

/-- `math.fsum(iterable)`, Modules/mathmodule.c:1281-1396: each item is converted (:1299-1305)
(`ASSIGN_DOUBLE`) and added to the partials before the next one is fetched; an exception from
`__next__` ends the loop and propagates (`if (PyErr_Occurred()) goto _fsum_error`). -/
def fsumIt (items : List PyN) (fin : Option PyExc) : Py Flt := do
  let st ← items.foldlM (fun st v => do fsumStep st (← asDouble v.v)) ({} : FsumState)
  match fin with
  | some e => .error e
  | none => fsumEnd st

/-- The loop of `math.sumprod(p, q)`, Modules/mathmodule.c:2178-2203, with `p` a fallible iterator
and `q` a list: `p_i = p_next(p_it)` comes first, so an exception of `p` at step `k` wins over `q`
being exhausted at `k`; a `StopIteration` set by `tp_iternext` is cleared and counts as the end
(:2180-2186); `p_stopped != q_stopped` is the `ValueError` (:2199-2201). -/
def sumprodItLoop : SP → List PyN → Option PyExc → List PyN → Py Val
  | st, [], fin, qs =>
    match fin with
    | some e => .error e
    | none =>
      match qs with
      | [] => do
        let st ← if st.intEnabled then spFinalizeInt st else pure st
        let st ← if st.fltEnabled then spFinalizeFlt st else pure st
        return st.total
      | _ :: _ => .error (.valueError "Inputs are not the same length")
  | _, _ :: _, _, [] => .error (.valueError "Inputs are not the same length")
  | st, p :: ps, fin, q :: qs => do sumprodItLoop (← spStep st p q) ps fin qs

/-- `try: n = len(data) except TypeError: ...`, statistics.py:194-200: the iterator path counts the
items it consumes (`n = next(counter) - 1`). -/
def fmeanLen (H : Hier) (data : PyIter) : Py Nat :=
  match data.len with
  | .ok n => .ok n
  | .error e => if isA H e "TypeError" then .ok data.items.length else .error e

/-- `list(weights)` unless `weights` is a list or tuple, statistics.py:209-210. -/
def listOf (w : PyIter) : Py (List PyN) :=
  match w.fin with
  | some e => .error e
  | none => .ok w.items

/-- `try: num = sumprod(data, weights) except ValueError: raise StatisticsError(...)`,
statistics.py:212-215. -/
def fmeanNum (H : Hier) (data : PyIter) (wl : List PyN) : Py Val :=
  match sumprodItLoop {} data.items data.fin wl with
  | .error e =>
    if isA H e "ValueError" then .error (statErr "data and weights must be the same length")
    else .error e
  | .ok v => .ok v

/-- `fmean(data, weights)`, Lib/statistics.py:182-222.

* No weights: `len(data)`; a `TypeError` (in the sense of `H`: the class or a subclass) sends it
  to the iterator path `fsum(compress(data, count(1)))`, which counts the items as they are
  consumed; any other exception of `len` propagates. Either way `fsum` meets the items and then the
  exception of the iterator, if any.
* Weights: `list(weights)` unless it is a list or tuple (its exception propagates); `sumprod(data,
  weights)` where a `ValueError` (in the sense of `H`), the length mismatch or one raised by the
  data iterator, becomes the length `StatisticsError`; then `fsum(weights)` and the zero check. -/
def fmeanIt (H : Hier) (data : PyIter) (weights : Option PyIter) : Py Val := do
  match weights with
  | none =>
    let n ← fmeanLen H data
    let total ← fsumIt data.items data.fin
    if n = 0 then throw (statErr "fmean requires at least one data point")
    vdiv (.flt total) (.int n)
  | some w =>
    let wl ← listOf w
    let num ← fmeanNum H data wl
    let den ← fsumV (wl.map (·.v))
    if !den.truthy then throw (statErr "sum of weights must be non-zero")
    vdiv num (.flt den)

/-! ## `fsum` of small ints is exact -/

/-- `0` is `+0.0`, any other value the finite float of that value. -/
def ofQ (q : Rat) : Flt := if q = 0 then .zero false else .fin q

def absSum : List Int → Nat
  | [] => 0
  | a :: as => a.natAbs + absSum as

def sumI : List Int → Int
  | [] => 0
  | a :: as => a + sumI as

theorem intToFlt_ofQ (i : Int) (h : i.natAbs < 2 ^ 53) : intToFlt i = .ok (ofQ (i : Rat)) := by
  rw [intToFlt_small i h]
  unfold ofQ
  by_cases h0 : i = 0
  · subst h0; rfl
  · have : ¬ ((i : Rat) = 0) := by simpa using h0
    rw [if_neg h0, if_neg this]

/-- `x + y` of two floats holding integers whose sum is below `2**53`. -/
theorem add_ofQ (a b : Int) (ha : a.natAbs < 2 ^ 53) (hb : b.natAbs < 2 ^ 53) (hab : (a + b).natAbs < 2 ^ 53) :
    Flt.add (ofQ a) (ofQ b) = ofQ ((a + b : Int) : Rat) := by
  unfold ofQ
  by_cases h1 : a = 0
  · subst h1
    by_cases h2 : b = 0
    · subst h2; simp [Flt.add]
    · have : ¬ ((b : Rat) = 0) := by simpa using h2
      simp [Flt.add, this, h2]
  · have h1' : ¬ ((a : Rat) = 0) := by simpa using h1
    by_cases h2 : b = 0
    · subst h2; simp [Flt.add, h1']
    · have h2' : ¬ ((b : Rat) = 0) := by simpa using h2
      simp only [h1', h2', ite_false, Flt.add]
      have e : (a : Rat) + (b : Rat) = ((a + b : Int) : Rat) := by rw [Rat.intCast_add]
      rw [e]
      by_cases h3 : a + b = 0
      · have : ((a + b : Int) : Rat) = 0 := by rw [h3]; rfl
        rw [this]; simp [Flt.ofRat]
      · have h3' : ¬ (((a + b : Int) : Rat) = 0) := fun h => h3 (Rat.intCast_eq_zero_iff.mp h)
        rw [if_neg h3', ofRat_int _ h3 hab]

theorem neg_ofQ (a : Int) : Flt.neg (ofQ a) = (if a = 0 then .zero true else ofQ ((-a : Int) : Rat)) := by
  unfold ofQ
  by_cases h : a = 0
  · subst h; simp [Flt.neg]
  · have h' : ¬ ((a : Rat) = 0) := fun h0 => h (Rat.intCast_eq_zero_iff.mp h0)
    have h'' : ¬ (((-a : Int) : Rat) = 0) := fun h0 => h (by have := Rat.intCast_eq_zero_iff.mp h0; omega)
    rw [if_neg h', if_neg h, if_neg h'']
    simp only [Flt.neg, Rat.intCast_neg]

theorem sub_ofQ (a b : Int) (ha : a.natAbs < 2 ^ 53) (hb : b.natAbs < 2 ^ 53) (hab : (a - b).natAbs < 2 ^ 53) :
    Flt.eq (Flt.sub (ofQ a) (ofQ b)) (ofQ ((a - b : Int) : Rat)) = true ∧
      (Flt.sub (ofQ a) (ofQ b) = ofQ ((a - b : Int) : Rat) ∨ (a - b = 0)) := by
  unfold Flt.sub
  rw [neg_ofQ]
  by_cases hb0 : b = 0
  · subst hb0
    simp only [ite_true, Int.sub_zero]
    unfold ofQ
    by_cases ha0 : a = 0
    · subst ha0; simp [Flt.add, Flt.eq]
    · have : ¬ ((a : Rat) = 0) := by simpa using ha0
      simp [this, Flt.add, Flt.eq, ha0]
  · rw [if_neg hb0, add_ofQ a (-b) ha (by omega) (by omega)]
    have e : a + -b = a - b := by omega
    rw [e]
    refine ⟨?_, Or.inl rfl⟩
    unfold ofQ; split <;> simp [Flt.eq]

theorem toRat_ofQ (q : Rat) : (ofQ q).toRat = q := by
  unfold ofQ; split
  · rename_i h; rw [h]; rfl
  · rfl

theorem lt_ofQ (x y : Rat) : Flt.lt (ofQ x) (ofQ y) = decide (x < y) := by
  have := toRat_ofQ x
  have := toRat_ofQ y
  unfold ofQ at *
  split <;> split <;> simp_all [Flt.lt, Flt.toRat] <;> exact decide_eq_decide.mpr Iff.rfl

theorem natAbs_cast (x : Int) : (if (x : Rat) < 0 then -(x : Rat) else (x : Rat)) = ((x.natAbs : Nat) : Rat) := by
  split
  · rename_i hc
    have : x < 0 := Rat.intCast_neg_iff.mp hc
    rw [← Rat.intCast_natCast, show (x.natAbs : Int) = -x by omega, Rat.intCast_neg]
  · rename_i hc
    have : 0 ≤ x := by
      have h2 : ¬ ((x : Rat) < 0) := hc
      rw [Rat.intCast_neg_iff] at h2; omega
    rw [← Rat.intCast_natCast, show (x.natAbs : Int) = x by omega]

theorem abs_ofQ (a : Int) : Flt.abs (ofQ (a : Rat)) = ofQ ((a.natAbs : Nat) : Rat) := by
  unfold ofQ
  by_cases h : a = 0
  · subst h; simp [Flt.abs]
  · have h' : ¬ ((a : Rat) = 0) := fun h0 => h (Rat.intCast_eq_zero_iff.mp h0)
    have h'' : ¬ (((a.natAbs : Nat) : Rat) = 0) := by
      intro h0; apply h; have := Rat.natCast_eq_zero_iff.mp h0; omega
    rw [if_neg h', if_neg h'']
    simp only [Flt.abs]
    rw [natAbs_cast]

theorem lt_abs_ofQ (a b : Int) :
    Flt.lt (Flt.abs (ofQ a)) (Flt.abs (ofQ b)) = decide (a.natAbs < b.natAbs) := by
  rw [abs_ofQ, abs_ofQ, lt_ofQ]
  simp [Rat.natCast_lt_natCast]

/-- The partials `fsum` keeps for an exact running sum `S` of ints: none for `0`, else `[S]`. -/
def partialsOf (S : Int) : List Flt := if S = 0 then [] else [.fin (S : Rat)]

theorem ofRat_zero' : Flt.ofRat 0 = .zero false := by simp [Flt.ofRat]

theorem sub_self_ofQ (b : Rat) : Flt.sub (ofQ b) (ofQ b) = .zero false := by
  unfold ofQ
  split
  · simp [Flt.sub, Flt.add, Flt.neg]
  · simp only [Flt.sub, Flt.neg, Flt.add]
    rw [show b + -b = 0 by grind, ofRat_zero']

theorem yr_ofQ (a b : Int) (ha : a.natAbs < 2 ^ 53) (hb : b.natAbs < 2 ^ 53) (hab : (a + b).natAbs < 2 ^ 53) :
    Flt.sub (ofQ ((a + b : Int) : Rat)) (ofQ (a : Rat)) = ofQ (b : Rat) := by
  by_cases hb0 : b = 0
  · subst hb0
    rw [Int.add_zero, sub_self_ofQ]
    simp [ofQ]
  · obtain ⟨-, h2⟩ := sub_ofQ (a + b) a hab ha (by omega)
    have e : a + b - a = b := by omega
    rw [e] at h2
    rcases h2 with h2 | h2
    · exact h2
    · exact absurd h2 hb0

/-- One pass of the partials loop on the single partial `S` and a new int `i`: the pair is
ordered by magnitude as at mathmodule.c:1311-1312, `hi = x + y` is exact, `lo` is `0.0` and dropped. -/
theorem fsumInner_int (S i : Int) (hS0 : S ≠ 0) (hS : S.natAbs < 2 ^ 53) (hi : i.natAbs < 2 ^ 53)
    (hSi : (S + i).natAbs < 2 ^ 53) :
    fsumInner [ofQ (S : Rat)] (ofQ (i : Rat)) [] = ([], ofQ ((S + i : Int) : Rat)) := by
  simp only [fsumInner, lt_abs_ofQ]
  by_cases hlt : i.natAbs < S.natAbs
  · simp only [hlt, decide_true, ite_true]
    rw [add_ofQ S i hS hi hSi, yr_ofQ S i hS hi hSi, sub_self_ofQ]
    simp [Flt.eq, Flt.pz]
  · simp only [hlt, decide_false, Bool.false_eq_true, ite_false]
    have hiS : (i + S).natAbs < 2 ^ 53 := by rw [Int.add_comm]; exact hSi
    rw [add_ofQ i S hi hS hiS, yr_ofQ i S hi hS hiS, sub_self_ofQ, Int.add_comm i S]
    simp [Flt.eq, Flt.pz]

theorem fsumStep_int (S i : Int) (hS : S.natAbs < 2 ^ 53) (hi : i.natAbs < 2 ^ 53)
    (hSi : (S + i).natAbs < 2 ^ 53) (st : FsumState) (hp : st.partials = partialsOf S) :
    fsumStep st (ofQ (i : Rat)) = .ok { st with partials := partialsOf (S + i) } := by
  unfold fsumStep
  rw [hp]
  have hfin : ∀ T : Int, T ≠ 0 → (ofQ (T : Rat)).isFinite = true ∧ Flt.eq (ofQ (T : Rat)) Flt.pz = false := by
    intro T hT
    have : ¬ ((T : Rat) = 0) := fun h0 => hT (Rat.intCast_eq_zero_iff.mp h0)
    simp [ofQ, this, Flt.isFinite, Flt.eq, Flt.pz, Ne.symm this]
  have hz : Flt.eq (ofQ ((0 : Int) : Rat)) Flt.pz = true := rfl
  by_cases hS0 : S = 0
  · subst hS0
    simp only [partialsOf, ite_true, fsumInner, List.reverse_nil, Int.zero_add]
    by_cases hi0 : i = 0
    · subst hi0; simp only [hz, ite_true]
    · obtain ⟨h1, h2⟩ := hfin i hi0
      simp only [h2, h1, Bool.false_eq_true, ite_false, Bool.not_true, List.nil_append, hi0]
      unfold ofQ
      have : ¬ ((i : Rat) = 0) := fun h0 => hi0 (Rat.intCast_eq_zero_iff.mp h0)
      rw [if_neg this]
  · have hfS : partialsOf S = [ofQ (S : Rat)] := by
      unfold partialsOf ofQ
      have : ¬ ((S : Rat) = 0) := fun h0 => hS0 (Rat.intCast_eq_zero_iff.mp h0)
      rw [if_neg hS0, if_neg this]
    rw [hfS, fsumInner_int S i hS0 hS hi hSi]
    simp only
    by_cases h0 : S + i = 0
    · rw [h0, hz]
      simp [partialsOf]
    · obtain ⟨h1, h2⟩ := hfin (S + i) h0
      simp only [h2, h1, Bool.false_eq_true, ite_false, Bool.not_true, List.nil_append]
      unfold partialsOf ofQ
      have : ¬ (((S + i : Int) : Rat) = 0) := fun h0' => h0 (Rat.intCast_eq_zero_iff.mp h0')
      rw [if_neg h0, if_neg this]

theorem absSum_bound (as : List Int) (S : Int) (h : S.natAbs + absSum as < 2 ^ 53) :
    ∀ a ∈ as, a.natAbs < 2 ^ 53 := by
  induction as generalizing S with
  | nil => simp
  | cons b bs ih =>
    intro a ha
    simp only [absSum] at h
    rcases List.mem_cons.mp ha with rfl | hm
    · omega
    · exact ih (S + b) (by omega) a hm

theorem fsum_fold_int (as : List Int) (S : Int) (st : FsumState) (hp : st.partials = partialsOf S)
    (hs : st.special = Flt.pz) (h : S.natAbs + absSum as < 2 ^ 53) :
    (ints as).foldlM (fun st v => do fsumStep st (← asDouble v.v)) st =
      .ok { st with partials := partialsOf (S + sumI as) } := by
  induction as generalizing S st with
  | nil =>
    cases st
    simp only at hp
    simp only [ints, List.map_nil, List.foldlM_nil, sumI, Int.add_zero, hp]
    rfl
  | cons a as ih =>
    simp only [absSum] at h
    have ha : a.natAbs < 2 ^ 53 := by omega
    have hS : S.natAbs < 2 ^ 53 := by omega
    have hSa : (S + a).natAbs < 2 ^ 53 := by omega
    simp only [ints, List.map_cons, List.foldlM_cons]
    have hd : asDouble (Val.int a).toN.v = .ok (ofQ (a : Rat)) := by
      show intToFlt a = _
      exact intToFlt_ofQ a ha
    rw [bind_ok hd]
    rw [bind_ok (fsumStep_int S a hS ha hSa st hp)]
    have := ih (S + a) { st with partials := partialsOf (S + a) } rfl hs (by omega)
    simp only [ints] at this
    rw [this]
    simp only [sumI, Int.add_assoc]

theorem fsumFinish_partialsOf (S : Int) : fsumFinish (partialsOf S).reverse = ofQ (S : Rat) := by
  unfold partialsOf ofQ
  by_cases h : S = 0
  · subst h; rfl
  · have : ¬ ((S : Rat) = 0) := by simpa using h
    simp [h, this, fsumFinish, fsumFinish.go]

/-- `math.fsum` of ints whose magnitudes add up to less than `2**53` is their exact sum. -/
theorem fsumIt_ints (as : List Int) (h : absSum as < 2 ^ 53) :
    fsumIt (ints as) none = .ok (ofQ (sumI as : Rat)) := by
  unfold fsumIt
  have := fsum_fold_int as 0 {} rfl rfl (by simpa using h)
  rw [bind_ok this]
  simp only [fsumEnd, Int.zero_add]
  have : Flt.eq Flt.pz Flt.pz = true := rfl
  simp only [this, Bool.not_true, Bool.false_eq_true, ite_false]
  rw [fsumFinish_partialsOf]

theorem fsumV_ints (as : List Int) (h : absSum as < 2 ^ 53) :
    fsumV ((ints as).map (·.v)) = .ok (ofQ (sumI as : Rat)) := by
  have := fsumIt_ints as h
  unfold fsumIt at this
  unfold fsumV
  rw [List.foldlM_map]
  exact this

/-! ## `fmean` of ints -/

theorem rat_natAbs (x : Int) : (x : Rat) = ((x.natAbs : Nat) : Rat) ∨ (x : Rat) = -((x.natAbs : Nat) : Rat) := by
  rcases Int.natAbs_eq x with h | h
  · left; conv => lhs; rw [h]
    exact Rat.intCast_natCast _
  · right; conv => lhs; rw [h]
    rw [Rat.intCast_neg, Rat.intCast_natCast]

theorem inv_neg' (B : Rat) : (-B)⁻¹ = -(B⁻¹) := by
  by_cases h : B = 0
  · subst h; simp
  · have h1 := Rat.inv_mul_cancel (-B) (by grind)
    have h2 := Rat.mul_inv_cancel B h
    grind

theorem quot_not_tiny (a b : Int) (ha : a ≠ 0) (hb0 : b ≠ 0) (hb : b.natAbs < 2 ^ 53) :
    Flt.pow2 (-1074) ≤ (a : Rat) / (b : Rat) ∨ (a : Rat) / (b : Rat) ≤ -Flt.pow2 (-1074) := by
  have hB : (0 : Rat) < ((b.natAbs : Nat) : Rat) := Rat.natCast_pos.mpr (by omega)
  have hA : (1 : Rat) ≤ ((a.natAbs : Nat) : Rat) := by
    have : 1 ≤ a.natAbs := by omega
    exact_mod_cast this
  have hB2 : ((b.natAbs : Nat) : Rat) < Flt.pow2 53 := by
    rw [pow2_eq]
    have e2 : PyLean.Binary64.pw (53 : Int) = ((2 ^ 53 : Nat) : Rat) := PyLean.Binary64.pw_natCast 53
    rw [e2]; exact Rat.natCast_lt_natCast.mpr hb
  have hsmall : Flt.pow2 (-1074) * ((b.natAbs : Nat) : Rat) ≤ 1 := by
    have h53 : Flt.pow2 (-1074) * Flt.pow2 53 ≤ 1 := by
      rw [pow2_eq, pow2_eq, ← PyLean.Binary64.pw_add]
      have := PyLean.Binary64.pw_le (show (-1074 + 53 : Int) ≤ 0 by decide)
      simpa [PyLean.Binary64.pw] using this
    have hp := pow2_pos (-1074)
    have := Rat.mul_le_mul_of_nonneg_left (Rat.le_of_lt hB2) (Rat.le_of_lt hp)
    generalize Flt.pow2 (-1074) = P at *
    generalize Flt.pow2 53 = Q at *
    grind
  have key : Flt.pow2 (-1074) ≤ ((a.natAbs : Nat) : Rat) / ((b.natAbs : Nat) : Rat) :=
    le_div_of_mul_le hB (by generalize Flt.pow2 (-1074) = P at *; grind)
  have hBne : ((b.natAbs : Nat) : Rat) ≠ 0 := by grind
  rcases rat_natAbs a with h1 | h1 <;> rcases rat_natAbs b with h2 | h2 <;> rw [h1, h2] <;>
    generalize ((a.natAbs : Nat) : Rat) = A at * <;>
    generalize ((b.natAbs : Nat) : Rat) = B at * <;>
    generalize Flt.pow2 (-1074) = P at * <;>
    simp only [Rat.div_def, inv_neg'] at * <;> grind

theorem div_ofQ_int (a b : Int) (hb0 : b ≠ 0) (hb : b.natAbs < 2 ^ 53) :
    Flt.div (ofQ (a : Rat)) (ofQ (b : Rat)) =
      if a = 0 then .zero (decide (b < 0)) else Flt.ofRat ((a : Rat) / (b : Rat)) := by
  have hb' : ¬ ((b : Rat) = 0) := fun h0 => hb0 (Rat.intCast_eq_zero_iff.mp h0)
  unfold ofQ
  rw [if_neg hb']
  by_cases ha : a = 0
  · subst ha
    simp only [Rat.intCast_zero, ite_true, Flt.div]
    simp [Rat.intCast_neg_iff]
  · have ha' : ¬ ((a : Rat) = 0) := fun h0 => ha (Rat.intCast_eq_zero_iff.mp h0)
    rw [if_neg ha', if_neg ha]
    simp only [Flt.div]
    have hne := ofRat_ne_zero_of_abs (quot_not_tiny a b ha hb0 hb)
    cases hr : Flt.ofRat ((a : Rat) / (b : Rat)) with
    | zero z => exact absurd hr (hne z)
    | _ => rfl

theorem sumprodItLoop_none (st : SP) (ps qs : List PyN) :
    sumprodItLoop st ps none qs = sumprodLoop st ps qs := by
  induction ps generalizing st qs with
  | nil => cases qs <;> rfl
  | cons p ps ih =>
    cases qs with
    | nil => rfl
    | cons q qs =>
      simp only [sumprodItLoop, sumprodLoop]
      cases spStep st p q with
      | error e => rfl
      | ok st' => exact ih st' qs

theorem sumprodItLoop_err (xs ws : List Int) (st : SP) (S : Int) (h : SpInv st S) (e : PyExc)
    (hl : xs.length ≤ ws.length) : sumprodItLoop st (ints xs) (some e) (ints ws) = .error e := by
  induction xs generalizing ws st S with
  | nil => rfl
  | cons a as ih =>
    cases ws with
    | nil => simp at hl
    | cons b bs =>
      simp only [ints, List.map_cons, sumprodItLoop]
      obtain ⟨st', e', i'⟩ := spStep_int st S a b h
      rw [bind_ok e']
      have := ih bs st' (S + a * b) i' (by simp at hl; omega)
      simpa [ints] using this

theorem sumprodLoop_mismatch (xs ws : List Int) (st : SP) (S : Int) (h : SpInv st S)
    (hl : xs.length ≠ ws.length) :
    sumprodLoop st (ints xs) (ints ws) = .error (.valueError "Inputs are not the same length") := by
  induction xs generalizing ws st S with
  | nil =>
    cases ws with
    | nil => simp at hl
    | cons _ _ => rfl
  | cons a as ih =>
    cases ws with
    | nil => rfl
    | cons b bs =>
      simp only [ints, List.map_cons, sumprodLoop]
      obtain ⟨st', e', i'⟩ := spStep_int st S a b h
      rw [bind_ok e']
      have := ih bs st' (S + a * b) i' (by simp at hl; omega)
      simpa [ints] using this

theorem spInv_init : SpInv {} 0 := ⟨0, rfl, rfl, rfl, fun _ => rfl, fun _ => rfl⟩

/-- `fmean` without weights of int data, Lib/statistics.py:192-207. `data` is a sequence whose
`len()` is its length, or an object whose `len()` raises a `TypeError` (an iterator; `H` decides
what `except TypeError` catches). While the magnitudes add up to less than `2**53`, `fsum` is exact
and the result is the mean `sum(data) / n` correctly rounded; empty data raises `StatisticsError`;
an exception of the iterator after the items propagates; an exception of `len()` that is not a
`TypeError` propagates before anything is iterated. `n` is below `2**53`, the count of items of
any list that fits in memory (`2**53` pointers are 64 PiB). -/
def FmeanInts : Prop :=
  ∀ (H : Hier) (xs : List Int) (lenR : Py Nat) (fin : Option PyExc),
    absSum xs < 2 ^ 53 → xs.length < 2 ^ 53 →
    ((lenR = .ok xs.length ∨ ∃ e, lenR = .error e ∧ isA H e "TypeError" = true) →
      (fin = none → fmeanIt H ⟨lenR, ints xs, fin⟩ none =
        if xs = [] then .error (.named "StatisticsError" "fmean requires at least one data point")
        else .ok (.flt (Flt.ofRat ((sumI xs : Rat) / (xs.length : Rat))))) ∧
      (∀ e, fin = some e → fmeanIt H ⟨lenR, ints xs, fin⟩ none = .error e)) ∧
    (∀ e, lenR = .error e → isA H e "TypeError" = false → fmeanIt H ⟨lenR, ints xs, fin⟩ none = .error e)

theorem fmeanInts_proven : FmeanInts := by
  intro H xs lenR fin hab hlen
  have hlenI : (ints xs).length = xs.length := by simp [ints]
  refine ⟨?_, ?_⟩
  · intro hl
    have hn : fmeanLen H ⟨lenR, ints xs, fin⟩ = .ok xs.length := by
      rcases hl with h | ⟨e, h, he⟩
      · simp only [fmeanLen, h]
      · simp only [fmeanLen, h, he, ite_true, hlenI]
    refine ⟨?_, ?_⟩
    · intro hf
      subst hf
      simp only [fmeanIt]
      rw [bind_ok hn, bind_ok (fsumIt_ints xs hab)]
      by_cases h0 : xs = []
      · subst h0
        simp [throw, throwThe, MonadExcept.throw, MonadExceptOf.throw, statErr]
        rfl
      · have hl0 : xs.length ≠ 0 := by simpa using h0
        simp only [hl0, ite_false, h0]
        have hnI : intToFlt (xs.length : Int) = .ok (ofQ ((xs.length : Int) : Rat)) :=
          intToFlt_ofQ _ (by omega)
        simp only [vdiv, arith, divOp, hnI, bind, Except.bind, fltDiv]
        have hq : ofQ ((xs.length : Int) : Rat) = .fin ((xs.length : Int) : Rat) := by
          unfold ofQ
          have : ¬ (((xs.length : Int) : Rat) = 0) := fun h => hl0 (by
            have := Rat.intCast_eq_zero_iff.mp h; omega)
          rw [if_neg this]
        rw [hq]
        simp only [pure, Except.pure]
        rw [← hq, div_ofQ_int _ _ (by omega) (by omega)]
        have hlpos : ¬ ((xs.length : Int) < 0) := by omega
        split
        · rename_i hs
          rw [hs]
          simp [hlpos, Rat.div_def, ofRat_zero']
        · simp only [Rat.intCast_natCast]
    · intro e hf
      subst hf
      simp only [fmeanIt]
      rw [bind_ok hn]
      unfold fsumIt
      have := fsum_fold_int xs 0 {} rfl rfl (by simpa using hab)
      rw [bind_ok this]
      rfl
  · intro e hl he
    have : fmeanLen H ⟨lenR, ints xs, fin⟩ = .error e := by
      simp only [fmeanLen, hl, he, Bool.false_eq_true, ite_false]
    simp only [fmeanIt]
    rw [this]
    rfl

/-- `fmean` with weights, Lib/statistics.py:209-222, for int data and a list of int weights. While
`sum(data[i] * weights[i])` and the magnitudes of the weights stay below `2**53` (`sumprod` of ints is
exact for every size, `sumprod_ints`), the result is `sumprod(data, weights) / sum(weights)` correctly
rounded (a zero numerator gives a zero with the sign of the total weight, as `0 / w` does); a zero total
weight raises; a length mismatch is `sumprod`'s `ValueError`, which `except ValueError` turns into the
length error (`HierOk`: `ValueError` is under `ValueError`); an exception of the data iterator met
before the weights run out comes through the same `except ValueError` (`H`), so a `ValueError` of
the iterator also becomes the length error and anything else propagates. -/
def FmeanWeightedInts : Prop :=
  ∀ (H : Hier) (xs ws : List Int) (lenR : Py Nat) (fin : Option PyExc),
    absSum ws < 2 ^ 53 → (dotI xs ws).natAbs < 2 ^ 53 →
    (fin = none → xs.length = ws.length → sumI ws ≠ 0 →
      fmeanIt H ⟨lenR, ints xs, fin⟩ (some (PyIter.ofList (ints ws))) =
        .ok (.flt (if dotI xs ws = 0 then .zero (decide (sumI ws < 0))
          else Flt.ofRat ((dotI xs ws : Rat) / (sumI ws : Rat))))) ∧
    (fin = none → xs.length = ws.length → sumI ws = 0 →
      fmeanIt H ⟨lenR, ints xs, fin⟩ (some (PyIter.ofList (ints ws))) =
        .error (.named "StatisticsError" "sum of weights must be non-zero")) ∧
    (HierOk H → fin = none → xs.length ≠ ws.length →
      fmeanIt H ⟨lenR, ints xs, fin⟩ (some (PyIter.ofList (ints ws))) =
        .error (.named "StatisticsError" "data and weights must be the same length")) ∧
    (∀ e, fin = some e → xs.length ≤ ws.length →
      fmeanIt H ⟨lenR, ints xs, fin⟩ (some (PyIter.ofList (ints ws))) =
        if isA H e "ValueError" then .error (.named "StatisticsError" "data and weights must be the same length")
        else .error e)

theorem fmeanWeightedInts_proven : FmeanWeightedInts := by
  intro H xs ws lenR fin hw hd
  have hden := fsumV_ints ws hw
  have hsw : (sumI ws).natAbs < 2 ^ 53 := by
    have : ∀ l : List Int, (sumI l).natAbs ≤ absSum l := by
      intro l; induction l with
      | nil => simp [sumI, absSum]
      | cons a l ih => simp only [sumI, absSum]; omega
    have := this ws; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hf hl hs
    subst hf
    have hnum : fmeanNum H ⟨lenR, ints xs, none⟩ (ints ws) = .ok (.int (dotI xs ws)) := by
      have := sumprod_ints xs ws hl
      simp only [sumprod] at this
      simp only [fmeanNum, sumprodItLoop_none, this]
    simp only [fmeanIt, PyIter.ofList, listOf]
    rw [ok_bind', bind_ok hnum, bind_ok hden]
    have ht : (ofQ ((sumI ws : Int) : Rat)).truthy = true := by
      unfold ofQ
      have : ¬ (((sumI ws : Int) : Rat) = 0) := fun h => hs (Rat.intCast_eq_zero_iff.mp h)
      rw [if_neg this]; rfl
    simp only [ht, Bool.not_true, Bool.false_eq_true, ite_false]
    simp only [vdiv, arith, divOp, intToFlt_ofQ _ hd, bind, Except.bind, fltDiv]
    have hq : ofQ ((sumI ws : Int) : Rat) = .fin ((sumI ws : Int) : Rat) := by
      unfold ofQ
      have : ¬ (((sumI ws : Int) : Rat) = 0) := fun h => hs (Rat.intCast_eq_zero_iff.mp h)
      rw [if_neg this]
    rw [hq]
    simp only [pure, Except.pure]
    rw [← hq, div_ofQ_int _ _ hs hsw]
  · intro hf hl hs
    subst hf
    have hnum : fmeanNum H ⟨lenR, ints xs, none⟩ (ints ws) = .ok (.int (dotI xs ws)) := by
      have := sumprod_ints xs ws hl
      simp only [sumprod] at this
      simp only [fmeanNum, sumprodItLoop_none, this]
    simp only [fmeanIt, PyIter.ofList, listOf]
    rw [ok_bind', bind_ok hnum, bind_ok hden, hs]
    rfl
  · intro hH hf hl
    subst hf
    have hm := sumprodLoop_mismatch xs ws {} 0 spInv_init hl
    have hv : isA H (.valueError "Inputs are not the same length") "ValueError" = true := by
      have := hH "ValueError" "ValueError" (by decide)
      simp only [isA, PyExc.className]
      rw [this]; decide
    have hnum : fmeanNum H ⟨lenR, ints xs, none⟩ (ints ws) =
        .error (statErr "data and weights must be the same length") := by
      simp only [fmeanNum, sumprodItLoop_none, hm, hv, ite_true]
    simp only [fmeanIt, PyIter.ofList, listOf]
    rw [ok_bind', hnum]
    rfl
  · intro e hf hl
    subst hf
    have hnum : fmeanNum H ⟨lenR, ints xs, some e⟩ (ints ws) =
        if isA H e "ValueError" then .error (statErr "data and weights must be the same length")
        else .error e := by
      simp only [fmeanNum, sumprodItLoop_err xs ws {} 0 spInv_init e hl]
    simp only [fmeanIt, PyIter.ofList, listOf]
    rw [ok_bind', hnum]
    split <;> rfl

end PyLean.CoreLibs.CalStat
