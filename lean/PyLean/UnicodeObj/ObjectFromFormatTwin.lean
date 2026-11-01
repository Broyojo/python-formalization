import PyLean.UnicodeObj.ObjectFromFormatProps
import PyLean.UnicodeObj.FormatProps

/-!
`PyUnicode_FromFormat` against Python's `%` operator: two separate implementations of the layout of
an integer, unicodeobject.c:2970-3009 and unicodeobject.c:14762-14884 with 15320-15469.

Both sides are brought to one form: spaces, sign, zeros, digits, spaces.
-/

namespace PyLean.UnicodeObj

open PyLean PyLean.Binary64

/-- The form of an integer. -/
def nf (sign : Str) (ds : Str) (a b c : Nat) : Str :=
  List.replicate a 32 ++ sign ++ List.replicate b 48 ++ ds ++ List.replicate c 32

theorem rep_if (n c : Nat) (b : Bool) :
    (if (n != 0 && b) = true then List.replicate n c else []) =
      if b = true then List.replicate n c else [] := by
  cases b <;> cases n <;> simp

theorem digits_ge {b : Nat} (fuel n : Nat) (acc : Str) (h : ∀ c ∈ acc, 48 ≤ c) :
    ∀ c ∈ natDigits b fuel n acc, 48 ≤ c := by
  induction fuel generalizing n acc with
  | zero => simpa [natDigits] using h
  | succ fuel ih =>
    have hd : 48 ≤ hexLower (n % b) := by
      simp only [hexLower]
      split <;> omega
    have hc : ∀ c ∈ hexLower (n % b) :: acc, 48 ≤ c := by
      intro c hm
      rcases List.mem_cons.1 hm with rfl | hm
      · exact hd
      · exact h c hm
    simp only [natDigits]
    split
    · exact hc
    · exact ih _ _ hc

theorem digitsOf_ge (b n : Nat) : ∀ c ∈ digitsOf b n, 48 ≤ c :=
  digits_ge _ _ [] (by simp)

/-- `intLayout` in the form, with its own numbers. -/
theorem intLayout_nf {ds : Str} (hd : ∀ c ∈ ds, 48 ≤ c) (hne : ds ≠ []) (sg : Bool) (width prec : Int)
    (z l : Bool) :
    let s : Int := if sg then 1 else 0
    let n : Int := ds.length
    let P1 := max prec n
    let W := max width (P1 + s)
    let P := if (z && !l) = true then W - s else P1
    let sp := (max (W - P - s) 0).toNat
    intLayout ((if sg then [45] else []) ++ ds) width prec z l =
      nf (if sg then [45] else []) ds (if l then 0 else sp) (max (P - n) 0).toNat
        (if l then sp else 0) := by
  intro s n P1 W P sp
  have hh : (((if sg then [45] else []) ++ ds).head? == some 45) = sg := by
    cases sg with
    | true => simp
    | false =>
      cases ds with
      | nil => exact absurd rfl hne
      | cons d r =>
        have := hd d List.mem_cons_self
        have hne' : d ≠ 45 := by omega
        simp [hne']
  unfold intLayout nf
  dsimp only
  rw [hh]
  have ht : (if sg = true then ((if sg then [45] else []) ++ ds).tail
      else (if sg then [45] else []) ++ ds) = ds := by
    cases sg <;> simp
  rw [ht]
  simp only [rep_if]
  cases l <;> simp [sp, P, W, P1, s, n] <;> rfl

/-- The digits fit the `int`/`str` limit: `n < 10^k` has at most `k` digits. -/
theorem natDigits_len (k : Nat) : ∀ (fuel n : Nat) (acc : Str), n < 10 ^ (k + 1) →
    (natDigits 10 fuel n acc).length ≤ acc.length + (k + 1) := by
  induction k with
  | zero =>
    intro fuel n acc hn
    cases fuel with
    | zero => simp [natDigits]
    | succ fuel =>
      have : n / 10 = 0 := by omega
      simp [natDigits, this]
  | succ k ih =>
    intro fuel n acc hn
    cases fuel with
    | zero => simp [natDigits]
    | succ fuel =>
      simp only [natDigits]
      split
      · simp
      · have hn' : n / 10 < 10 ^ (k + 1) := by
          rw [Nat.pow_succ] at hn
          omega
        have := ih fuel (n / 10) (hexLower (n % 10) :: acc) hn'
        simp only [List.length_cons] at this
        omega

theorem digits_limit {n : Nat} (hn : n ≤ 2 ^ 64) : (digitsOf 10 n).length ≤ 4300 := by
  have h : n < 10 ^ 20 := by
    have : (2 : Nat) ^ 64 < 10 ^ 20 := by decide
    omega
  have := natDigits_len 19 (n + 1) n [] h
  simp only [List.length_nil] at this
  unfold digitsOf
  omega

theorem formatLongStr_form {v prec : Int} {t base : Nat}
    (hb : ((t = 100 ∨ t = 105 ∨ t = 117) ∧ base = 10) ∨ (t = 111 ∧ base = 8) ∨ (t = 120 ∧ base = 16))
    (hlim : base = 10 → (digitsOf base v.natAbs).length ≤ 4300) (hp : prec ≤ 2 ^ 31 - 4) :
    formatLongStr v false prec t =
      .ok ((if v < 0 then [45] else []) ++
        List.replicate (prec - (digitsOf base v.natAbs).length).toNat 48 ++
        digitsOf base v.natAbs) := by
  obtain ⟨hd, hm⟩ := digitsOf_spec base v.natAbs
  have h0 : ¬prec > 2 ^ 31 - 1 - 3 := by omega
  have hbase : (if t == 111 then 8 else if t == 120 || t == 88 then 16 else 10) = base := by
    rcases hb with ⟨h | h | h, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals first | rfl | (subst h; rfl)
  simp only [formatLongStr, h0, if_false, hbase, longFormat, bind, Except.bind]
  generalize digitsOf base v.natAbs = ds at *
  obtain ⟨d, r, rfl⟩ : ∃ d r, ds = d :: r := by
    cases ds with
    | nil => exact absurd rfl hd
    | cons d r => exact ⟨d, r, rfl⟩
  have hd45 : (d == 45) = false := by simpa using hm d List.mem_cons_self
  have hl : base = 10 → ¬4300 < r.length + 1 := by
    intro e
    have := hlim e
    simp only [List.length_cons] at this
    omega
  have hz : prec.toNat - (r.length + 1) = (prec - ((r.length : Int) + 1)).toNat := by omega
  by_cases hq : prec > (r.length : Int) + 1
  · rcases hb with ⟨rfl | rfl | rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> by_cases hv : v < 0 <;>
      simp [hv, hd45, hl, hq, hz]
  · have hz0 : (prec - ((r.length : Int) + 1)).toNat = 0 := by omega
    rcases hb with ⟨rfl | rfl | rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> by_cases hv : v < 0 <;>
      simp [hv, hd45, hl, hq, hz0]

/-- `formatArgTail` with no `#`, the sign known to be `-`, and the body found. -/
theorem pctTail_form (arg : FArg) (ha : arg.flags.alt = false) (fill : Nat) (sg : Bool) (sc : Nat)
    (len : Int) (pidx : Nat) (str body : Str) (hb : (str.drop pidx).take len.toNat = body) :
    let W : Int := if arg.width < len then len else arg.width
    let W1 : Int := if (sg && decide (W > len)) = true then W - 1 else W
    let e := (W1 - len).toNat
    formatArgTail arg fill sg sc len pidx str =
      (if (sg && fill != 32) = true then [sc] else []) ++
        List.replicate (if arg.flags.ljust = true then 0 else e) fill ++
        (if (fill == 32 && sg) = true then [sc] else []) ++ body ++
        List.replicate (if arg.flags.ljust = true then e else 0) 32 := by
  intro W W1 e
  unfold formatArgTail
  simp only [ha, Bool.false_and, if_false, Bool.false_eq_true, hb]
  cases hl : arg.flags.ljust with
  | true =>
    simp [W1, W, e]
    repeat' split
    all_goals omega
  | false =>
    simp [W1, W, e]
    generalize (if sg = true ∧ len < (if arg.width < len then len else arg.width) then
      (if arg.width < len then len else arg.width) - 1
      else if arg.width < len then len else arg.width) = x
    by_cases h : len < x
    · simp [h]
    · have e0 : (x - len).toNat = 0 := by omega
      simp [h, e0]

/-- The first test of `unicode_format_arg_output`, for the integers. -/
def EarlyOut (arg : FArg) (str : Str) : Prop :=
  (arg.width == -1 ∨ arg.width ≤ (str.length : Int)) ∧
    (arg.prec == -1 ∨ arg.prec ≥ (str.length : Int)) ∧ !arg.flags.sign ∧ !arg.flags.blank

instance (arg : FArg) (str : Str) : Decidable (EarlyOut arg str) := by
  unfold EarlyOut
  exact inferInstance

theorem pctOutput_early {arg : FArg} {str : Str} (h : EarlyOut arg str) :
    formatArgOutput arg true str = str := by
  unfold formatArgOutput
  exact if_pos h

theorem pctOutput_signed {arg : FArg} {x : Str} (h : ¬EarlyOut arg (45 :: x))
    (h1 : arg.ch ≠ 115) (h2 : arg.ch ≠ 114) (h3 : arg.ch ≠ 97) :
    formatArgOutput arg true (45 :: x) =
      formatArgTail arg (if arg.flags.zero = true then 48 else 32) true 45 (x.length : Int) 1
        (45 :: x) := by
  unfold EarlyOut at h
  unfold formatArgOutput
  dsimp only
  rw [if_neg h]
  simp [h1, h2, h3]

theorem pctOutput_plain {arg : FArg} {x : Str} {d : Nat} (h : ¬EarlyOut arg (d :: x))
    (h1 : arg.ch ≠ 115) (h2 : arg.ch ≠ 114) (h3 : arg.ch ≠ 97) (hd : 48 ≤ d)
    (hs : arg.flags.sign = false) (hb : arg.flags.blank = false) :
    formatArgOutput arg true (d :: x) =
      formatArgTail arg (if arg.flags.zero = true then 48 else 32) false 0
        ((x.length : Int) + 1) 0 (d :: x) := by
  have e1 : d ≠ 45 := by omega
  have e2 : d ≠ 43 := by omega
  unfold EarlyOut at h
  unfold formatArgOutput
  dsimp only
  rw [if_neg h]
  simp [h1, h2, h3, e1, e2, hs, hb]

theorem wid_true (width len : Int) :
    ((if (true && decide ((if width < len then len else width) > len)) = true then
        (if width < len then len else width) - 1 else if width < len then len else width) - len).toNat =
      (max (max width (len + 1) - len - 1) 0).toNat := by
  simp only [Bool.true_and, decide_eq_true_eq]
  repeat' split
  all_goals omega

theorem wid_false (width len : Int) :
    ((if (false && decide ((if width < len then len else width) > len)) = true then
        (if width < len then len else width) - 1 else if width < len then len else width) - len).toNat =
      (max (max width len - len) 0).toNat := by
  simp only [Bool.false_and, Bool.false_eq_true, if_false]
  split <;> omega

theorem rep_add (a b c : Nat) :
    List.replicate (a + b) c = List.replicate a c ++ List.replicate b c := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.add_right_comm, List.replicate_succ, List.replicate_succ, ih]
    rfl

theorem nf_congr {sign ds : Str} {a b c a' b' c' : Nat} (h1 : a = a') (h2 : b = b') (h3 : c = c') :
    nf sign ds a b c = nf sign ds a' b' c' := by
  subst h1 h2 h3
  rfl

/-- The output of `%` in the form, with the numbers of `intLayout_nf`. -/
theorem output_eq {ds : Str} (hd : ∀ c ∈ ds, 48 ≤ c) (hne : ds ≠ []) (sg : Bool) (width prec : Int)
    (z l : Bool) (ch : Nat) (h1 : ch ≠ 115) (h2 : ch ≠ 114) (h3 : ch ≠ 97) (hw : -1 ≤ width)
    (hp : -1 ≤ prec) :
    let s : Int := if sg then 1 else 0
    let n : Int := ds.length
    let P1 := max prec n
    let W := max width (P1 + s)
    let P := if (z && !l) = true then W - s else P1
    let sp := (max (W - P - s) 0).toNat
    formatArgOutput { ch := ch, flags := { ljust := l, zero := z }, width := width, prec := prec } true
        ((if sg then [45] else []) ++ List.replicate (prec - ds.length).toNat 48 ++ ds) =
      nf (if sg then [45] else []) ds (if l then 0 else sp) (max (P - n) 0).toNat
        (if l then sp else 0) := by
  intro s n P1 W P sp
  have hnpos : 0 < ds.length := List.length_pos_iff.2 hne
  generalize hk : (prec - ds.length).toNat = k
  have hP1 : P1 = n + k := by
    simp only [P1, n]
    omega
  generalize harg : ({ ch := ch, flags := { ljust := l, zero := z }, width := width, prec := prec } :
    FArg) = arg
  have hL : arg.flags.ljust = l := by rw [← harg]
  have hZ : arg.flags.zero = z := by rw [← harg]
  have hA : arg.flags.alt = false := by rw [← harg]
  have hS : arg.flags.sign = false := by rw [← harg]
  have hB : arg.flags.blank = false := by rw [← harg]
  have hC : arg.ch = ch := by rw [← harg]
  have hWd : arg.width = width := by rw [← harg]
  have hPr : arg.prec = prec := by rw [← harg]
  cases sg with
  | true =>
    have hs1 : s = 1 := rfl
    have hstr : (if (true : Bool) = true then [45] else []) ++ List.replicate k 48 ++ ds =
        45 :: (List.replicate k 48 ++ ds) := by simp
    rw [hstr]
    have hlen : ((List.replicate k 48 ++ ds).length : Int) = P1 := by
      simp only [List.length_append, List.length_replicate]
      rw [hP1]
      simp only [n]
      omega
    by_cases hE : EarlyOut arg (45 :: (List.replicate k 48 ++ ds))
    · rw [pctOutput_early hE]
      have hw2 : width ≤ P1 + 1 := by
        have := hE.1
        simp only [List.length_cons, hWd, beq_iff_eq] at this
        omega
      have hWs : W = max width (P1 + s) := rfl
      have h0 : sp = 0 := by
        simp only [sp, P]
        split <;> omega
      have hB2 : (max (P - n) 0).toNat = k := by
        simp only [P]
        split <;> omega
      rw [hB2, h0]
      simp [nf]
    · rw [pctOutput_signed hE (by rw [hC]; exact h1) (by rw [hC]; exact h2) (by rw [hC]; exact h3)]
      have t := pctTail_form arg hA (if arg.flags.zero = true then 48 else 32) true 45
        ((List.replicate k 48 ++ ds).length : Int) 1 (45 :: (List.replicate k 48 ++ ds))
        (List.replicate k 48 ++ ds)
        (by simp only [List.drop_succ_cons, List.drop_zero, Int.toNat_natCast, List.take_length])
      dsimp only at t
      rw [t, hL, hZ, hWd, hlen, wid_true]
      generalize hE2 : (max (max width (P1 + 1) - P1 - 1) 0).toNat = E
      have hWs : W = max width (P1 + s) := rfl
      cases z with
      | true =>
        cases l with
        | true =>
          have hP : P = P1 := by
            simp only [P, Bool.not_true, Bool.and_false, Bool.false_eq_true, if_false]
          have hsp : sp = E := by
            simp only [sp]
            rw [hP]
            omega
          have hb2 : (max (P - n) 0).toNat = k := by
            rw [hP]
            omega
          rw [hsp, hb2]
          simp [nf]
        | false =>
          have hP : P = W - s := by
            simp only [P, Bool.not_false, Bool.and_self, if_true]
          have hsp : sp = 0 := by
            simp only [sp]
            rw [hP]
            omega
          have hb2 : (max (P - n) 0).toNat = E + k := by
            rw [hP]
            omega
          rw [hsp, hb2]
          simp [nf]
          rw [rep_add, List.append_assoc]
      | false =>
        have hP : P = P1 := by
          simp only [P, Bool.false_and, Bool.false_eq_true, if_false]
        have hsp : sp = E := by
          simp only [sp]
          rw [hP]
          omega
        have hb2 : (max (P - n) 0).toNat = k := by
          rw [hP]
          omega
        rw [hsp, hb2]
        cases l <;> simp [nf]
  | false =>
    have hs0 : s = 0 := rfl
    have hstr : (if (false : Bool) = true then [45] else []) ++ List.replicate k 48 ++ ds =
        List.replicate k 48 ++ ds := by simp
    rw [hstr]
    obtain ⟨d, x, hdx⟩ : ∃ d x, List.replicate k 48 ++ ds = d :: x := by
      cases he : List.replicate k 48 ++ ds with
      | nil =>
        have := congrArg List.length he
        simp only [List.length_append, List.length_nil] at this
        omega
      | cons d x => exact ⟨d, x, rfl⟩
    have hd48 : 48 ≤ d := by
      have hm : d ∈ List.replicate k 48 ++ ds := by
        rw [hdx]
        exact List.mem_cons_self
      rcases List.mem_append.1 hm with hm | hm
      · rw [List.eq_of_mem_replicate hm]
        omega
      · exact hd d hm
    have hlen : ((x.length : Int) + 1) = P1 := by
      have := congrArg List.length hdx
      simp only [List.length_append, List.length_replicate, List.length_cons] at this
      rw [hP1]
      simp only [n]
      omega
    by_cases hE : EarlyOut arg (d :: x)
    · rw [hdx, pctOutput_early hE, ← hdx]
      have hw2 : width ≤ P1 := by
        have := hE.1
        simp only [List.length_cons, hWd, beq_iff_eq] at this
        omega
      have hWs : W = max width (P1 + s) := rfl
      have h0 : sp = 0 := by
        simp only [sp, P]
        split <;> omega
      have hB2 : (max (P - n) 0).toNat = k := by
        simp only [P]
        split <;> omega
      rw [hB2, h0]
      simp [nf]
    · rw [hdx, pctOutput_plain hE (by rw [hC]; exact h1) (by rw [hC]; exact h2) (by rw [hC]; exact h3)
        hd48 hS hB]
      have t := pctTail_form arg hA (if arg.flags.zero = true then 48 else 32) false 0
        ((x.length : Int) + 1) 0 (d :: x) (d :: x) (by
          simp only [List.drop_zero]
          have : ((x.length : Int) + 1).toNat = (d :: x).length := by
            simp only [List.length_cons]
            omega
          rw [this, List.take_length])
      dsimp only at t
      rw [t, hL, hZ, hWd, hlen, wid_false, ← hdx]
      generalize hE2 : (max (max width P1 - P1) 0).toNat = E
      have hWs : W = max width (P1 + s) := rfl
      cases z with
      | true =>
        cases l with
        | true =>
          have hP : P = P1 := by
            simp only [P, Bool.not_true, Bool.and_false, Bool.false_eq_true, if_false]
          have hsp : sp = E := by
            simp only [sp]
            rw [hP]
            omega
          have hb2 : (max (P - n) 0).toNat = k := by
            rw [hP]
            omega
          rw [hsp, hb2]
          simp [nf]
        | false =>
          have hP : P = W - s := by
            simp only [P, Bool.not_false, Bool.and_self, if_true]
          have hsp : sp = 0 := by
            simp only [sp]
            rw [hP]
            omega
          have hb2 : (max (P - n) 0).toNat = E + k := by
            rw [hP]
            omega
          rw [hsp, hb2]
          simp [nf]
          rw [rep_add, List.append_assoc]
      | false =>
        have hP : P = P1 := by
          simp only [P, Bool.false_and, Bool.false_eq_true, if_false]
        have hsp : sp = E := by
          simp only [sp]
          rw [hP]
          omega
        have hb2 : (max (P - n) 0).toNat = k := by
          rw [hP]
          omega
        rw [hsp, hb2]
        cases l <;> simp [nf]

/-- What `%` gives for a result of `mainFormatLong`. -/
def percentOut (arg : FArg) : Py FOut → Py Str
  | .ok (.direct s) => .ok s
  | .ok (.viaOutput s signed) => .ok (formatArgOutput arg signed s)
  | .error e => .error e

/-- The range of the C type of a conversion: the argument is a value of that type, and `%d` of a
wider value is a value that was wrapped first. -/
def SignedFits (sizemod : Nat) (v : Int) : Prop :=
  -(2 ^ (sizeBits sizemod - 1) : Int) ≤ v ∧ v < 2 ^ (sizeBits sizemod - 1)

def UnsignedFits (sizemod : Nat) (v : Int) : Prop :=
  0 ≤ v ∧ v < 2 ^ sizeBits sizemod

theorem sizeBits_cases (sm : Nat) : sizeBits sm = 32 ∨ sizeBits sm = 64 := by
  unfold sizeBits
  split <;> simp

theorem wrapS_fits {sm : Nat} {v : Int} (h : SignedFits sm v) : wrapS (sizeBits sm) v = v := by
  unfold SignedFits at h
  rcases sizeBits_cases sm with e | e
  · rw [e] at h ⊢
    have hu : ((wrapU 32 v : Nat) : Int) = v % 4294967296 := by
      unfold wrapU
      omega
    unfold wrapS
    dsimp only
    generalize wrapU 32 v = u at hu ⊢
    split <;> omega
  · rw [e] at h ⊢
    have hu : ((wrapU 64 v : Nat) : Int) = v % 18446744073709551616 := by
      unfold wrapU
      omega
    unfold wrapS
    dsimp only
    generalize wrapU 64 v = u at hu ⊢
    split <;> omega

theorem wrapU_fits {sm : Nat} {v : Int} (h : UnsignedFits sm v) :
    wrapU (sizeBits sm) v = v.natAbs := by
  unfold UnsignedFits at h
  rcases sizeBits_cases sm with e | e <;> rw [e] at h ⊢ <;>
    · simp only [wrapU]
      omega

theorem main_direct (v : Int) (arg : FArg) (hw : arg.width = -1) (hp : arg.prec = -1)
    (hs : arg.flags.sign = false) (hb : arg.flags.blank = false) (hc : arg.ch ≠ 88) :
    mainFormatLong (.int v) arg =
      (longFormat v (if arg.ch == 111 then 8 else if arg.ch == 120 then 16 else 10)
        arg.flags.alt).map .direct := by
  have hc' : (arg.ch != 88) = true := by simpa using hc
  simp only [mainFormatLong, FObj.asLong, bind, Except.bind, pure, Except.pure, hw, hp, hs, hb,
    Bool.not_false, beq_self_eq_true, Bool.true_and, hc', if_true]
  cases longFormat v _ _ <;> rfl

theorem main_via (v : Int) (arg : FArg) (h : ¬(arg.width = -1 ∧ arg.prec = -1)) :
    mainFormatLong (.int v) arg =
      (formatLongStr v arg.flags.alt arg.prec arg.ch).map (fun s => FOut.viaOutput s true) := by
  have hb : (arg.width == -1 && arg.prec == -1) = false := by
    cases h1 : arg.width == -1 <;> cases h2 : arg.prec == -1 <;> simp_all
  simp only [mainFormatLong, FObj.asLong, bind, Except.bind, pure, Except.pure, Bool.true_and, hb,
    Bool.false_and, Bool.false_eq_true, if_false]
  cases formatLongStr v _ _ _ <;> rfl

/-- `PyUnicode_FromFormat` and Python's `%` lay an integer out the same way: for every value of the
C type of the conversion, every width and precision, and the flags `-` and `0` in any combination.
These are separate implementations, one over a `sprintf` buffer and one over `str(int)`, with
different rules for what a zero flag does to the precision. `%x`, `%o` and `%u` of a negative value
are excluded because C prints it as unsigned, which `sprintInt` shows: that is the conversion, not
the layout. Width and precision are what a format can write, or -1 for none. The bound on the
precision is the `OverflowError` of `_PyUnicode_FormatLong`. -/
def IntMatchesPercent : Prop :=
  ∀ (v width prec : Int) (zero ljust : Bool) (sm c : Nat),
    ((c = 100 ∨ c = 105) ∧ SignedFits sm v ∨ (c = 117 ∨ c = 111 ∨ c = 120) ∧ UnsignedFits sm v) →
    -1 ≤ width → -1 ≤ prec → prec ≤ 2 ^ 31 - 4 →
    percentOut { ch := c, flags := { ljust := ljust, zero := zero }, width := width, prec := prec }
      (mainFormatLong (.int v)
        { ch := c, flags := { ljust := ljust, zero := zero }, width := width, prec := prec }) =
      .ok (intLayout (sprintInt c sm v) width prec zero ljust)

/-- The buffer of `sprintf`, in terms of the digits. -/
theorem sprint_form {c sm : Nat} {v : Int} {base : Nat}
    (h : ((c = 100 ∨ c = 105) ∧ SignedFits sm v ∧ base = 10) ∨
      ((c = 117 ∧ base = 10 ∨ c = 111 ∧ base = 8 ∨ c = 120 ∧ base = 16) ∧ UnsignedFits sm v)) :
    sprintInt c sm v = (if decide (v < 0) = true then [45] else []) ++ digitsOf base v.natAbs := by
  rcases h with ⟨hc, hf, rfl⟩ | ⟨hc, hf⟩
  · unfold sprintInt
    dsimp only
    rw [wrapS_fits hf]
    rcases hc with rfl | rfl <;> simp
  · have hn : ¬v < 0 := by
      have := hf.1
      omega
    unfold sprintInt
    dsimp only
    rw [wrapU_fits hf]
    rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [hn]

theorem intMatchesPercent_proven : IntMatchesPercent := by
  intro v width prec zero ljust sm c hc hw hp hp2
  obtain ⟨base, hb⟩ : ∃ base,
      ((c = 100 ∨ c = 105) ∧ SignedFits sm v ∧ base = 10) ∨
      ((c = 117 ∧ base = 10 ∨ c = 111 ∧ base = 8 ∨ c = 120 ∧ base = 16) ∧ UnsignedFits sm v) := by
    rcases hc with ⟨h1, h2⟩ | ⟨h1 | h1 | h1, h2⟩
    · exact ⟨10, .inl ⟨h1, h2, rfl⟩⟩
    · exact ⟨10, .inr ⟨.inl ⟨h1, rfl⟩, h2⟩⟩
    · exact ⟨8, .inr ⟨.inr (.inl ⟨h1, rfl⟩), h2⟩⟩
    · exact ⟨16, .inr ⟨.inr (.inr ⟨h1, rfl⟩), h2⟩⟩
  rw [sprint_form hb]
  have hlim : base = 10 → (digitsOf base v.natAbs).length ≤ 4300 := by
    intro e
    subst e
    apply digits_limit
    rcases hb with ⟨_, ⟨h1, h2⟩, _⟩ | ⟨_, ⟨h1, h2⟩⟩ <;>
      · rcases sizeBits_cases sm with e | e <;> simp only [e] at h1 h2 <;> omega
  have hd := digitsOf_ge base v.natAbs
  have hne := (digitsOf_spec base v.natAbs).1
  have hfl : formatLongStr v false prec c = .ok ((if decide (v < 0) = true then [45] else []) ++
      List.replicate (prec - (digitsOf base v.natAbs).length).toNat 48 ++
      digitsOf base v.natAbs) := by
    have := @formatLongStr_form v prec c base (by
      rcases hb with ⟨h1, _, rfl⟩ | ⟨h1 | h1 | h1, _⟩
      · exact .inl ⟨by omega, rfl⟩
      · exact .inl ⟨by omega, h1.2⟩
      · exact .inr (.inl h1)
      · exact .inr (.inr h1)) hlim hp2
    simpa using this
  have hN := intLayout_nf hd hne (decide (v < 0)) width prec zero ljust
  dsimp only at hN
  rw [hN]
  have hc1 : c ≠ 115 ∧ c ≠ 114 ∧ c ≠ 97 ∧ c ≠ 88 := by
    rcases hb with ⟨h1 | h1, _⟩ | ⟨h1 | h1 | h1, _⟩
    all_goals
      first
      | (subst h1; decide)
      | (rw [h1.1]; decide)
  have hO := output_eq hd hne (decide (v < 0)) width prec zero ljust c hc1.1 hc1.2.1 hc1.2.2.1 hw hp
  dsimp only at hO
  rw [← hO]
  by_cases hD : width = -1 ∧ prec = -1
  · obtain ⟨rfl, rfl⟩ := hD
    have hbase : (if c == 111 then 8 else if c == 120 then 16 else 10) = base := by
      rcases hb with ⟨h1 | h1, _, rfl⟩ | ⟨⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩, _⟩
      all_goals (subst h1; rfl)
    have hL : longFormat v base false =
        .ok ((if decide (v < 0) = true then [45] else []) ++ digitsOf base v.natAbs) := by
      unfold longFormat
      dsimp only
      rw [if_neg]
      · cases hv : decide (v < 0) <;> simp at hv <;> simp [hv]
      · intro hn
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hn
        have := hlim hn.1
        omega
    have hz : ((-1 : Int) - (digitsOf base v.natAbs).length).toNat = 0 := by omega
    rw [hz]
    simp only [List.replicate_zero, List.nil_append]
    rw [main_direct v _ rfl rfl rfl rfl hc1.2.2.2, pctOutput_early]
    · simp only [hbase, hL]
      simp [percentOut, Except.map]
    · exact ⟨.inl rfl, .inl rfl, rfl, rfl⟩
  · rw [main_via v _ hD]
    simp only [hfl]
    rfl

end PyLean.UnicodeObj
