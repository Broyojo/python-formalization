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

/-- `cls._string_from_ip_int(ip_int)`, `Lib/ipaddress.py:1835-1859`, for every class that inherits
it and every argument. Above `_ALL_ONES` it raises `ValueError('IPv6 address is too large')`
(:1852-1853, the docstring's "Raises"); with the default `ip_int=None` it reads `cls._ip`
(:1849-1850): for `IPv6Address` and `IPv6Interface` the slot descriptor (:1919), and `int()` of
that raises `TypeError`; `IPv6Network` has no `_ip`, so the lookup raises `AttributeError`. For
every class and every `ip_int < 2**128`, with `vs` its eight hextet values:

* if no two adjacent hextets are zero, the result is `':'.join('%x' % v for v in vs)`, so a single
  zero hextet is never compressed (RFC 5952 4.2.2);
* if `[s, s + L)` is a run of zeros with `L ≥ 2`, every run of zeros is shorter or equally long,
  and every equally long run starts at `s` or later (the first longest run, RFC 5952 4.2.1 and
  4.2.3), the output is `':'.join(vs[:s]) + '::' + ':'.join(vs[s+L:])`, each value as `'%x'`.

The hypotheses on `s` and `L` describe the run; they are not assumptions about the input, and
such a run exists whenever two adjacent hextets are zero. -/
def CompressRFC5952 : Prop :=
  stringFromIpInt6Py .address none = .error (.typeError
    "int() argument must be a string, a bytes-like object or a real number, not 'member_descriptor'") ∧
  stringFromIpInt6Py .interface none = .error (.typeError
    "int() argument must be a string, a bytes-like object or a real number, not 'member_descriptor'") ∧
  stringFromIpInt6Py .network none =
    .error (.named "AttributeError" "type object 'IPv6Network' has no attribute '_ip'") ∧
  ∀ cls : V6Cls,
  (∀ n : Nat, 2 ^ 128 ≤ n → stringFromIpInt6Py cls (some n) = .error (.valueError "IPv6 address is too large")) ∧
  ∀ n : Nat, n < 2 ^ 128 →
    ((∀ s, ¬ ZeroRun (hextetVals n) s 2) →
      stringFromIpInt6Py cls (some n) = .ok (joinOn1 ':' ((hextetVals n).map hexStr))) ∧
    (∀ s L, 2 ≤ L → ZeroRun (hextetVals n) s L →
      (∀ s' L', ZeroRun (hextetVals n) s' L' → L' < L ∨ (L' = L ∧ s ≤ s')) →
      stringFromIpInt6Py cls (some n) = .ok (joinOn1 ':' (((hextetVals n).take s).map hexStr) ++ [':', ':'] ++
        joinOn1 ':' (((hextetVals n).drop (s + L)).map hexStr)))

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

theorem compressRFC5952_proven : CompressRFC5952 := by
  refine ⟨rfl, rfl, rfl, fun cls => ⟨fun n hn => ?_, fun n hn => ?_⟩⟩
  · have : n > allOnes 128 := by unfold allOnes; omega
    simp [stringFromIpInt6Py, this]
  · have hle : ¬ n > allOnes 128 := by unfold allOnes; omega
    have hpy : stringFromIpInt6Py cls (some n) = .ok (stringFromIpInt6 n) := by
      simp [stringFromIpInt6Py, hle]
    obtain ⟨c1, c2⟩ := compressRFC5952_core n hn
    rw [hpy]
    exact ⟨fun h => by rw [c1 h], fun s L h1 h2 h3 => by rw [c2 s L h1 h2 h3]⟩

end PyLean.Ipaddress
