import PyLean.Ipaddress.Parse6Props

/-! `CompressRFC5952`: which zero run `_BaseV6._compress_hextets` turns into `::`.

The round trip (`v6RoundTrip_proven`) holds for any run of two or more zero hextets, so it does
not pin the choice. This file does: the first longest run of at least two zero hextets is
compressed, and nothing is compressed when no two adjacent hextets are zero (RFC 5952 4.2.1-4.2.3,
and the `compressed` attribute in `Doc/library/ipaddress.rst`).

Plan: (1) the loop of `compressHextets` (`cstep`, `Lib/ipaddress.py:1804-1820`) looks at a hextet
only through `hextet == '0'`, so the fold equals a fold `mstep` over the Bool mask; (2) for a
hextet `'%x' % v` with `v < 2**16`, `hextet == '0'` iff `v == 0` (`hexStr_facts`); (3) for each
of the 256 masks of length 8, `decide` checks that the fold ends on the first longest run, or on a
run of length at most one when no two adjacent hextets are zero; (4) `cfinish`
(`Lib/ipaddress.py:1822-1833`) then gives the stated string. -/

namespace PyLean.Ipaddress

open PyLean

/-- The eight hextet values of `ip_int`, high first: `int(hex_str[x:x+4], 16)` for
`hex_str = '%032x' % ip_int` (`Lib/ipaddress.py:1855-1856`). -/
def hextetVals (n : Nat) : List Nat := (List.range 8).map fun i => n / 65536 ^ (7 - i) % 65536

/-- `vs[s:s+L]` is in range and every value in it is zero. -/
def ZeroRun (vs : List Nat) (s L : Nat) : Prop :=
  s + L ≤ vs.length ∧ ∀ i, s ≤ i → i < s + L → vs[i]? = some 0

/-- `cls._string_from_ip_int(ip_int=None)`, `Lib/ipaddress.py:1835-1859`, for every class that
inherits it and every argument: `None` and every int. With the default `ip_int=None` it reads
`cls._ip` (:1849-1850): for `IPv6Address` and `IPv6Interface` the slot descriptor (:1919), and
`int()` of that raises `TypeError`; `IPv6Network` has no `_ip`, so the lookup raises
`AttributeError`. Above `_ALL_ONES` it raises `ValueError('IPv6 address is too large')`
(:1852-1853, the docstring's "Raises"). For every class:

* for every `ip_int` in `[0, 2**128)`, with `vs` its eight hextet values: if no two adjacent
  hextets are zero, the result is `':'.join('%x' % v for v in vs)`, so a single zero hextet is
  never compressed (RFC 5952 4.2.2); if `[s, s + L)` is a run of zeros with `L ≥ 2`, every run of
  zeros is shorter or equally long, and every equally long run starts at `s` or later (the first
  longest run, RFC 5952 4.2.1 and 4.2.3), the output is `':'.join(vs[:s]) + '::' +
  ':'.join(vs[s+L:])`, each value as `'%x'`. The hypotheses on `s` and `L` describe the run; they
  are not assumptions about the input, and such a run exists whenever two adjacent hextets are
  zero;
* the check at :1852 is one-sided, so a negative `ip_int = -m` is formatted too: `'%032x' % -m` is
  `-` and the hex digits of `m` padded to 31, of which the slices (:1856) read only the first 32
  characters, i.e. the leading 31 hex digits of `m` (`m // 16**(k-31)` for `m` of `k` digits, `m`
  itself when it has at most 31), and the first slice `-xyz` is the negative number `-0xxyz`. So
  the result is the text of that 31-digit value, with `-` before it when its top group is
  non-zero; in particular for `0 < m < 2**112` it is the text of `m` itself (`-1` gives `'::1'`),
  and the method gives the same string for `-m` and `m`. -/
def CompressRFC5952 : Prop :=
  stringFromIpInt6Py .address none = .error (.typeError
    "int() argument must be a string, a bytes-like object or a real number, not 'member_descriptor'") ∧
  stringFromIpInt6Py .interface none = .error (.typeError
    "int() argument must be a string, a bytes-like object or a real number, not 'member_descriptor'") ∧
  stringFromIpInt6Py .network none =
    .error (.named "AttributeError" "type object 'IPv6Network' has no attribute '_ip'") ∧
  ∀ cls : V6Cls,
  (∀ n : Int, 2 ^ 128 ≤ n → stringFromIpInt6Py cls (some n) = .error (.valueError "IPv6 address is too large")) ∧
  (∀ n : Nat, n < 2 ^ 128 →
    ((∀ s, ¬ ZeroRun (hextetVals n) s 2) →
      stringFromIpInt6Py cls (some (n : Int)) = .ok (joinOn1 ':' ((hextetVals n).map hexStr))) ∧
    (∀ s L, 2 ≤ L → ZeroRun (hextetVals n) s L →
      (∀ s' L', ZeroRun (hextetVals n) s' L' → L' < L ∨ (L' = L ∧ s ≤ s')) →
      stringFromIpInt6Py cls (some (n : Int)) = .ok (joinOn1 ':' (((hextetVals n).take s).map hexStr) ++
        [':', ':'] ++ joinOn1 ':' (((hextetVals n).drop (s + L)).map hexStr)))) ∧
  (∀ m k : Nat, 0 < m → m < 16 ^ k → (k ≤ 31 ∨ 16 ^ (k - 1) ≤ m) →
    stringFromIpInt6Py cls (some (-(m : Int))) =
      .ok ((if 2 ^ 112 ≤ m / 16 ^ (k - 31) then ['-'] else []) ++ stringFromIpInt6 (m / 16 ^ (k - 31)))) ∧
  (∀ m : Nat, 0 < m → m < 2 ^ 112 →
    stringFromIpInt6Py cls (some (-(m : Int))) = stringFromIpInt6Py cls (some (m : Int)))

/-! ## (1) The loop sees only the mask -/

/-- `cstep` with `hextet == '0'` already evaluated. -/
def mstep (st : Int × Nat × Int × Nat) (zi : Bool × Nat) : Int × Nat × Int × Nat :=
  let (bs, bl, ds, dl) := st
  let (z, i) := zi
  if z then
    let dl := dl + 1
    let ds := if ds = -1 then (i : Int) else ds
    if dl > bl then (ds, dl, ds, dl) else (bs, bl, ds, dl)
  else (bs, bl, -1, 0)

theorem cstep_mstep (st : Int × Nat × Int × Nat) (h : List Char) (i : Nat) :
    cstep st (h, i) = mstep st (decide (h = ['0']), i) := by
  obtain ⟨bs, bl, ds, dl⟩ := st
  by_cases hh : h = ['0'] <;> simp [cstep, mstep, hh]

theorem fold_mask (l : List (List Char)) (k : Nat) (st : Int × Nat × Int × Nat) :
    (l.zipIdx k).foldl cstep st = ((l.map fun h => decide (h = ['0'])).zipIdx k).foldl mstep st := by
  induction l generalizing k st with
  | nil => rfl
  | cons a l ih => simp only [List.zipIdx_cons, List.map_cons, List.foldl_cons, cstep_mstep, ih]

/-! ## (3) All 256 masks -/

/-- `m[s:s+L]` is in range and all `True`. -/
def runB (m : List Bool) (s L : Nat) : Bool :=
  decide (s + L ≤ m.length) && (List.range L).all fun j => m.getD (s + j) false

/-- The fold over the mask ends on the first longest run if that run has length at least two, and
otherwise no two adjacent entries are `True`. -/
def maskOK (m : List Bool) : Bool :=
  let st := m.zipIdx.foldl mstep (-1, 0, -1, 0)
  if st.2.1 > 1 then
    decide (0 ≤ st.1) && runB m st.1.toNat st.2.1 &&
      (List.range 9).all fun s' => (List.range 9).all fun L' =>
        !runB m s' L' || decide (L' < st.2.1 ∨ (L' = st.2.1 ∧ st.1.toNat ≤ s'))
  else (List.range 9).all fun s => !runB m s 2

theorem maskOK_all : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    maskOK [b0, b1, b2, b3, b4, b5, b6, b7] = true := by decide

theorem maskOK_len8 (m : List Bool) (h : m.length = 8) : maskOK m = true :=
  match m, h with
  | [b0, b1, b2, b3, b4, b5, b6, b7], _ => maskOK_all b0 b1 b2 b3 b4 b5 b6 b7

/-! ## (2) The mask of the hextet values -/

theorem getD_mask (vs : List Nat) (k : Nat) :
    (vs.map fun v => decide (v = 0)).getD k false = true ↔ vs[k]? = some 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases vs[k]? <;> simp

theorem runB_iff (vs : List Nat) (s L : Nat) :
    runB (vs.map fun v => decide (v = 0)) s L = true ↔ ZeroRun vs s L := by
  simp only [runB, ZeroRun, Bool.and_eq_true, decide_eq_true_eq, List.length_map, List.all_eq_true,
    List.mem_range, getD_mask]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun i hi1 hi2 => ?_⟩
    have := h2 (i - s) (by omega)
    rwa [show s + (i - s) = i by omega] at this
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun j hj => h2 (s + j) (by omega) (by omega)⟩

theorem zeroRun_mono (vs : List Nat) (s L L' : Nat) (h : ZeroRun vs s L) (hl : L' ≤ L) :
    ZeroRun vs s L' :=
  ⟨by have := h.1; omega, fun i h1 h2 => h.2 i h1 (by omega)⟩

theorem zeroRun_lt (vs : List Nat) (s L : Nat) (h : ZeroRun vs s L) (hl : vs.length = 8) :
    s < 9 ∧ L < 9 := by
  have := h.1; omega

theorem hextetVals_length (n : Nat) : (hextetVals n).length = 8 := by simp [hextetVals]

theorem hextetVals_lt (n : Nat) : ∀ v ∈ hextetVals n, v < 65536 := by
  intro v hv
  simp only [hextetVals, List.mem_map] at hv
  obtain ⟨i, -, rfl⟩ := hv
  exact Nat.mod_lt _ (by decide)

theorem hextetsOf_vals (n : Nat) : hextetsOf n = (hextetVals n).map hexStr := by
  unfold hextetsOf hextetVals
  rw [List.map_map]
  rfl

theorem mask_vals (n : Nat) :
    (hextetsOf n).map (fun h => decide (h = ['0'])) = (hextetVals n).map fun v => decide (v = 0) := by
  rw [hextetsOf_vals, List.map_map]
  apply List.map_congr_left
  intro v hv
  simp only [Function.comp_apply, decide_eq_decide]
  refine ⟨(hexStr_facts v (hextetVals_lt n v hv)).2.2.2.2, fun h => ?_⟩
  subst h; exact hexStr_0

/-! ## (4) The joined string -/

theorem joinOn1_append (sep : Char) (A C : List (List Char)) (hA : A ≠ []) (hC : C ≠ []) :
    joinOn1 sep (A ++ C) = joinOn1 sep A ++ sep :: joinOn1 sep C := by
  induction A with
  | nil => exact absurd rfl hA
  | cons a A ih =>
    cases A with
    | nil =>
      cases C with
      | nil => exact absurd rfl hC
      | cons c C => simp [joinOn1]
    | cons a' A' =>
      have := ih (by simp)
      simp only [List.cons_append, joinOn1] at this ⊢
      rw [this]
      simp

theorem joinOn1_dc (A B : List (List Char)) (p q : Prop) [Decidable p] [Decidable q]
    (hp : p ↔ A = []) (hq : q ↔ B = []) :
    joinOn1 ':' ((if p then [[]] else []) ++ A ++ [[]] ++ (if q then [[]] else B)) =
      joinOn1 ':' A ++ [':', ':'] ++ joinOn1 ':' B := by
  by_cases hp' : p <;> by_cases hq' : q
  · have hA := hp.mp hp'; have hB := hq.mp hq'; subst hA hB
    simp [hp', hq', joinOn1]
  · have hA := hp.mp hp'; have hB : B ≠ [] := fun e => hq' (hq.mpr e); subst hA
    simp only [hp', hq', ↓reduceIte, List.nil_append, List.cons_append]
    cases B with
    | nil => exact absurd rfl hB
    | cons b B => simp [joinOn1]
  · have hA : A ≠ [] := fun e => hp' (hp.mpr e); have hB := hq.mp hq'; subst hB
    simp only [hp', hq', ↓reduceIte, List.nil_append]
    rw [List.append_assoc, joinOn1_append ':' A ([[]] ++ [[]]) hA (by simp)]
    simp [joinOn1]
  · have hA : A ≠ [] := fun e => hp' (hp.mpr e); have hB : B ≠ [] := fun e => hq' (hq.mpr e)
    simp only [hp', hq', ↓reduceIte, List.nil_append]
    rw [List.append_assoc, joinOn1_append ':' A _ hA (by simp)]
    cases B with
    | nil => exact absurd rfl hB
    | cons b B => simp [joinOn1]

/-! ## The property -/

theorem compressRFC5952_core : ∀ n : Nat, n < 2 ^ 128 →
    ((∀ s, ¬ ZeroRun (hextetVals n) s 2) →
      stringFromIpInt6 n = joinOn1 ':' ((hextetVals n).map hexStr)) ∧
    (∀ s L, 2 ≤ L → ZeroRun (hextetVals n) s L →
      (∀ s' L', ZeroRun (hextetVals n) s' L' → L' < L ∨ (L' = L ∧ s ≤ s')) →
      stringFromIpInt6 n = joinOn1 ':' (((hextetVals n).take s).map hexStr) ++ [':', ':'] ++
        joinOn1 ':' (((hextetVals n).drop (s + L)).map hexStr)) := by
  intro n _
  have hlen := hextetVals_length n
  have hok := maskOK_len8 ((hextetVals n).map fun v => decide (v = 0)) (by simp [hlen])
  have hc : stringFromIpInt6 n = joinOn1 ':' (cfinish (hextetsOf n)
      ((((hextetVals n).map fun v => decide (v = 0))).zipIdx.foldl mstep (-1, 0, -1, 0))) := by
    rw [stringFromIpInt6, compress_eq, fold_mask, mask_vals]
  rw [hc]
  unfold maskOK at hok
  generalize ((hextetVals n).map fun v => decide (v = 0)).zipIdx.foldl mstep (-1, 0, -1, 0) = st
    at hok ⊢
  obtain ⟨bs, bl, ds, dl⟩ := st
  simp only at hok
  by_cases hgt : bl > 1
  · simp only [hgt, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      List.mem_range, Bool.or_eq_true, Bool.not_eq_true'] at hok
    obtain ⟨⟨h0, hrun⟩, hbest⟩ := hok
    obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le h0
    simp only [Int.toNat_natCast] at hrun hbest
    rw [runB_iff] at hrun
    refine ⟨fun hno => absurd (zeroRun_mono _ b bl 2 hrun (by omega)) (hno b), ?_⟩
    intro s L hL hsL hfirst
    have hlt := zeroRun_lt _ s L hsL hlen
    have h1 : L < bl ∨ (L = bl ∧ b ≤ s) := by
      rcases hbest s hlt.1 L hlt.2 with h | h
      · rw [(runB_iff _ s L).mpr hsL] at h; exact absurd h (by decide)
      · exact h
    have h2 := hfirst b bl hrun
    obtain ⟨rfl, rfl⟩ : s = b ∧ L = bl := by omega
    have hb8 := hrun.1
    rw [hlen] at hb8
    have hhl : (hextetsOf n).length = 8 := by simp [hextetsOf]
    unfold cfinish
    simp only [hgt, ↓reduceIte, Int.toNat_natCast, Int.natCast_eq_zero]
    have hshape : (if s + L = (hextetsOf n).length then hextetsOf n ++ [[]] else hextetsOf n).take s ++
        [[]] ++ (if s + L = (hextetsOf n).length then hextetsOf n ++ [[]] else hextetsOf n).drop (s + L) =
        (hextetsOf n).take s ++ [[]] ++ (if s + L = 8 then [[]] else (hextetsOf n).drop (s + L)) := by
      by_cases he : s + L = 8
      · simp only [hhl, he, ↓reduceIte]
        rw [List.take_append_of_le_length (by omega), List.drop_left']
        simp [hhl]
      · simp [hhl, he]
    rw [hshape, hextetsOf_vals, ← List.map_take, ← List.map_drop]
    have := joinOn1_dc (((hextetVals n).take s).map hexStr) (((hextetVals n).drop (s + L)).map hexStr)
      (s = 0) (s + L = 8) (by rw [← List.length_eq_zero_iff]; simp only [List.length_map,
        List.length_take, hlen]; omega)
      (by rw [← List.length_eq_zero_iff]; simp only [List.length_map, List.length_drop, hlen]; omega)
    rw [← this]
    by_cases h0 : s = 0 <;> simp [h0, List.append_assoc]
  · simp only [hgt, ↓reduceIte, List.all_eq_true, List.mem_range, Bool.not_eq_true'] at hok
    unfold cfinish
    simp only [hgt, ↓reduceIte]
    refine ⟨fun _ => by rw [hextetsOf_vals], ?_⟩
    intro s L hL hsL _
    have hlt := zeroRun_lt _ s L hsL hlen
    have := hok s hlt.1
    have h2 := (runB_iff _ s 2).mpr (zeroRun_mono _ s L 2 hsL hL)
    rw [this] at h2
    exact absurd h2 (by decide)

/-! ## Negative ints -/

theorem cfinish_cons_swap (x y : List Char) (T : List (List Char)) (bs : Int) (bl : Nat) (ds : Int)
    (dl : Nat) (h : bl > 1 → 1 ≤ bs) :
    ∃ R, cfinish (x :: T) (bs, bl, ds, dl) = x :: R ∧ cfinish (y :: T) (bs, bl, ds, dl) = y :: R := by
  by_cases hgt : bl > 1
  · obtain ⟨b, rfl⟩ : ∃ b : Nat, bs = ((b + 1 : Nat) : Int) :=
      ⟨bs.toNat - 1, by have := h hgt; omega⟩
    have hne : ¬ (((b + 1 : Nat) : Int) = 0) := by omega
    have htn : ((b + 1 : Nat) : Int).toNat = b + 1 := by simp
    have key : ∀ z : List Char, cfinish (z :: T) (((b + 1 : Nat) : Int), bl, ds, dl) =
        z :: ((if b + bl + 1 = T.length + 1 then T ++ [[]] else T).take b ++ [[]] ++
          (if b + bl + 1 = T.length + 1 then T ++ [[]] else T).drop (b + bl)) := by
      intro z
      unfold cfinish
      simp only [hgt, ↓reduceIte, htn, hne, List.length_cons]
      rw [show b + 1 + bl = b + bl + 1 by omega]
      by_cases he : b + bl + 1 = T.length + 1
      · rw [if_pos he, if_pos he]
        all_goals rfl
      · rw [if_neg he, if_neg he]
        all_goals rfl
    exact ⟨_, key x, key y⟩
  · refine ⟨T, ?_, ?_⟩ <;> simp [cfinish, hgt]

/-- With a first hextet other than `'0'`, the compression keeps it in front, whatever it is. -/
theorem compress_head (x y : List Char) (T : List (List Char)) (hx : x ≠ ['0']) (hy : y ≠ ['0'])
    (hT : T.length = 7) :
    ∃ R, compressHextets (x :: T) = x :: R ∧ compressHextets (y :: T) = y :: R := by
  have hm : ∀ z : List Char, z ≠ ['0'] →
      ((z :: T).map fun h => decide (h = ['0'])) = false :: T.map fun h => decide (h = ['0']) := by
    intro z hz; simp [hz]
  rw [compress_eq, compress_eq, fold_mask, fold_mask, hm x hx, hm y hy]
  have hok := maskOK_len8 (false :: T.map fun h => decide (h = ['0'])) (by simp [hT])
  unfold maskOK at hok
  generalize (false :: T.map fun h => decide (h = ['0'])).zipIdx.foldl mstep (-1, 0, -1, 0) = st
    at hok ⊢
  obtain ⟨bs, bl, ds, dl⟩ := st
  simp only at hok
  apply cfinish_cons_swap
  intro hgt
  simp only [hgt, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨h0, hrun⟩, -⟩ := hok
  rcases Nat.eq_zero_or_pos bs.toNat with hz | hz
  · exfalso
    rw [hz] at hrun
    simp only [runB, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hrun
    have := hrun.2 0 (by omega)
    simp at this
  · omega

theorem map_range8_if {β : Type} (a : β) (f : Nat → β) :
    (List.range 8).map (fun i => if i = 0 then a else f i) = a :: ((List.range 8).map f).tail := rfl

/-- The hextets of a negative int `-m`: `v`, the leading 31 hex digits of `m`, is below `16**31`;
the first hextet is `'%x'` of minus its top three digits, the other seven are those of `v`. -/
theorem hextetsOfInt_neg (m k : Nat) (hm : 0 < m) (hk : m < 16 ^ k)
    (hk' : k ≤ 31 ∨ 16 ^ (k - 1) ≤ m) :
    m / 16 ^ (k - 31) < 16 ^ 31 ∧
    hextetsOfInt (-(m : Int)) =
      fmtX (-((m / 16 ^ (k - 31) / 16 ^ 28 : Nat) : Int)) :: (hextetsOf (m / 16 ^ (k - 31))).tail := by
  have hv : m / 16 ^ (k - 31) < 16 ^ 31 := by
    rw [Nat.div_lt_iff_lt_mul (pow16_pos _), ← Nat.pow_add]
    exact Nat.lt_of_lt_of_le hk (Nat.pow_le_pow_right (by decide) (by omega))
  refine ⟨hv, ?_⟩
  obtain ⟨B, hB⟩ := fmt032x_neg m k hm hk hk'
  generalize m / 16 ^ (k - 31) = v at hv hB ⊢
  have hu : v / 16 ^ 28 < 4096 := by
    rw [Nat.div_lt_iff_lt_mul (pow16_pos _)]
    exact Nat.lt_of_lt_of_le hv (by decide)
  unfold hextetsOfInt
  rw [hB]
  have hmap : (List.range 8).map
      (fun i => fmtX (intHex (((('-' :: digitsW 31 v) ++ B).drop (4 * i)).take 4))) =
      (List.range 8).map (fun i => if i = 0 then fmtX (-((v / 16 ^ 28 : Nat) : Int))
        else hexStr (v / 65536 ^ (7 - i) % 65536)) := by
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [slice_zero, intHex_neg3, Nat.mod_eq_of_lt hu, if_pos rfl]
    · rw [slice_hi _ _ _ i hpos hi, intHex_digits4, fmtX_nat, if_neg (show i ≠ 0 by omega),
        show 28 - 4 * i = 4 * (7 - i) by omega, Nat.pow_mul]
      all_goals rfl
  rw [hmap, map_range8_if]
  all_goals rfl

/-- `_string_from_ip_int(-m)` for `m > 0` with `k` hex digits (or `k <= 31` with `m < 16**k`): the
text of `v = m // 16**(k-31)`, after a `-` when `v >= 2**112`. -/
theorem stringFromIpInt6Int_neg (m k : Nat) (hm : 0 < m) (hk : m < 16 ^ k)
    (hk' : k ≤ 31 ∨ 16 ^ (k - 1) ≤ m) :
    stringFromIpInt6Int (-(m : Int)) =
      (if 2 ^ 112 ≤ m / 16 ^ (k - 31) then ['-'] else []) ++ stringFromIpInt6 (m / 16 ^ (k - 31)) := by
  obtain ⟨hv, hh⟩ := hextetsOfInt_neg m k hm hk hk'
  unfold stringFromIpInt6Int stringFromIpInt6
  rw [hh]
  generalize m / 16 ^ (k - 31) = v at hv ⊢
  have hu : v / 16 ^ 28 < 4096 := by
    rw [Nat.div_lt_iff_lt_mul (pow16_pos _)]
    exact Nat.lt_of_lt_of_le hv (by decide)
  have hval : v / 65536 ^ 7 % 65536 = v / 16 ^ 28 := by
    rw [show (65536 : Nat) ^ 7 = 16 ^ 28 from rfl]
    exact Nat.mod_eq_of_lt (by omega)
  have hhead : hextetsOf v = hexStr (v / 16 ^ 28) :: (hextetsOf v).tail := by
    rw [← hval]; rfl
  have hT : (hextetsOf v).tail.length = 7 := by simp [hextetsOf]
  rw [hhead, List.tail_cons, fmtX_neg]
  generalize (hextetsOf v).tail = T at hT ⊢
  by_cases hu0 : v / 16 ^ 28 = 0
  · have hlt : ¬ 2 ^ 112 ≤ v := by
      intro h
      have h' : 16 ^ 28 ≤ v := by rw [show (16 : Nat) ^ 28 = 2 ^ 112 from rfl]; exact h
      have := Nat.div_pos h' (pow16_pos 28)
      omega
    rw [if_pos hu0, if_neg hlt, List.nil_append, hu0]
  · have h2 : 2 ^ 112 ≤ v := by
      have := (Nat.le_div_iff_mul_le (pow16_pos 28)).mp (show 1 ≤ v / 16 ^ 28 by omega)
      rw [show (2 : Nat) ^ 112 = 16 ^ 28 from rfl]
      omega
    rw [if_neg hu0, if_pos h2]
    have hne : hexStr (v / 16 ^ 28) ≠ ['0'] :=
      fun h => hu0 ((hexStr_facts _ (by omega)).2.2.2.2 h)
    obtain ⟨R, h1, h3⟩ := compress_head ('-' :: hexStr (v / 16 ^ 28)) (hexStr (v / 16 ^ 28)) T
      (by simp) hne hT
    rw [h1, h3]
    cases R <;> rfl

theorem compressRFC5952_proven : CompressRFC5952 := by
  refine ⟨rfl, rfl, rfl, fun cls => ⟨fun n hn => ?_, fun n hn => ?_, fun m k hm hk hk' => ?_,
    fun m hm h112 => ?_⟩⟩
  · have e1 : (2 : Int) ^ 128 = 340282366920938463463374607431768211456 := by decide
    have e2 : allOnes 128 = 340282366920938463463374607431768211455 := by decide
    have hgt : n > ((allOnes 128 : Nat) : Int) := by rw [e2]; rw [e1] at hn; omega
    unfold stringFromIpInt6Py
    dsimp only
    rw [if_pos hgt]
  · rw [stringFromIpInt6Py_nat cls n hn]
    obtain ⟨c1, c2⟩ := compressRFC5952_core n hn
    exact ⟨fun h => by rw [c1 h], fun s L h1 h2 h3 => by rw [c2 s L h1 h2 h3]⟩
  · have hle : ¬ (-(m : Int) > ((allOnes 128 : Nat) : Int)) := by omega
    unfold stringFromIpInt6Py
    dsimp only
    rw [if_neg hle, stringFromIpInt6Int_neg m k hm hk hk']
  · have hk : m < 16 ^ 31 := Nat.lt_of_lt_of_le h112 (by decide)
    have hle : ¬ (-(m : Int) > ((allOnes 128 : Nat) : Int)) := by omega
    have hlt : ¬ 2 ^ 112 ≤ m := by omega
    rw [stringFromIpInt6Py_nat cls m (Nat.lt_of_lt_of_le h112 (by decide))]
    unfold stringFromIpInt6Py
    dsimp only
    rw [if_neg hle, stringFromIpInt6Int_neg m 31 hm hk (Or.inl (Nat.le_refl 31)), Nat.sub_self,
      Nat.pow_zero, Nat.div_one, if_neg hlt, List.nil_append]

end PyLean.Ipaddress
