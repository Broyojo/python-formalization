import PyLean.Ipaddress.Parse6

/-! `V6RoundTrip`: parsing `str()` of an IPv6 address gives the address and its scope id back.
The plan in the docstring of `V6RoundTrip`: hex digits (1), the run invariant of
`_compress_hextets` (2), `split` with maxsplit on a join (3), the parse of the 29 shapes
`_compress_hextets` can output (4), the IPv4-mapped form (5), and the scope suffix (6). -/

namespace PyLean.Ipaddress

open PyLean

/-! ## Hex digits -/

def hdB (k : Nat) : Bool :=
  isHexC (hd k) && hexValC (hd k) == k

theorem hdB_all : ∀ k, k < 16 → hdB k = true := by decide

theorem hd_hex (k : Nat) (h : k < 16) : isHexC (hd k) = true ∧ hexValC (hd k) = k := by
  have := hdB_all k h
  simp only [hdB, Bool.and_eq_true, beq_iff_eq] at this
  exact this

theorem hd_zero (k : Nat) (h : k < 16) (h0 : hd k = '0') : k = 0 := by
  have := (hd_hex k h).2
  rw [h0] at this
  rw [← this]; decide

theorem hexStr_facts (v : Nat) (hv : v < 65536) :
    parseHextet (hexStr v) = .ok v ∧ (hexStr v).all isHexC = true ∧ hexStr v ≠ [] ∧
      (hexStr v).length ≤ 4 ∧ (hexStr v = ['0'] → v = 0) := by
  unfold hexStr
  by_cases h1 : v < 16
  · obtain ⟨a1, a2⟩ := hd_hex v h1
    simp only [h1, ↓reduceIte]
    refine ⟨?_, by simp [a1], by simp, by simp, ?_⟩
    · simp [parseHextet, a1, hexVal, a2]
    · intro e; simp only [List.cons.injEq, and_true] at e; exact hd_zero v h1 e
  · by_cases h2 : v < 256
    · obtain ⟨a1, a2⟩ := hd_hex (v / 16) (by omega)
      obtain ⟨b1, b2⟩ := hd_hex (v % 16) (by omega)
      simp only [h1, h2, ↓reduceIte]
      refine ⟨?_, by simp [a1, b1], by simp, by simp, by simp⟩
      simp [parseHextet, a1, b1, hexVal, a2, b2]; omega
    · by_cases h3 : v < 4096
      · obtain ⟨a1, a2⟩ := hd_hex (v / 256) (by omega)
        obtain ⟨b1, b2⟩ := hd_hex (v / 16 % 16) (by omega)
        obtain ⟨c1, c2⟩ := hd_hex (v % 16) (by omega)
        simp only [h1, h2, h3, ↓reduceIte]
        refine ⟨?_, by simp [a1, b1, c1], by simp, by simp, by simp⟩
        simp [parseHextet, a1, b1, c1, hexVal, a2, b2, c2]; omega
      · obtain ⟨a1, a2⟩ := hd_hex (v / 4096) (by omega)
        obtain ⟨b1, b2⟩ := hd_hex (v / 256 % 16) (by omega)
        obtain ⟨c1, c2⟩ := hd_hex (v / 16 % 16) (by omega)
        obtain ⟨d1, d2⟩ := hd_hex (v % 16) (by omega)
        simp only [h1, h2, h3, ↓reduceIte]
        refine ⟨?_, by simp [a1, b1, c1, d1], by simp, by simp, by simp⟩
        simp [parseHextet, a1, b1, c1, d1, hexVal, a2, b2, c2, d2]; omega

theorem not_mem_of_hex (p : List Char) (h : p.all isHexC = true) (c : Char) (hc : isHexC c = false) :
    c ∉ p := by
  intro m
  have := List.all_eq_true.mp h c m
  rw [hc] at this; exact Bool.false_ne_true this

/-! ## `split` with maxsplit -/

theorem splitMax_ne_nil (sep : Char) (m : Nat) (s : List Char) : splitMax sep m s ≠ [] := by
  cases s with
  | nil => simp [splitMax]
  | cons c cs =>
    unfold splitMax
    split
    · simp
    · split <;> simp

theorem splitMax_nosep (sep : Char) (m : Nat) (p : List Char) (h : sep ∉ p) :
    splitMax sep m p = [p] := by
  induction p with
  | nil => simp [splitMax]
  | cons c cs ih =>
    have hc : c ≠ sep := by intro e; subst e; simp at h
    have h' : sep ∉ cs := by intro m; exact h (by simp [m])
    simp [splitMax, hc, ih h']

theorem splitMax_append (sep : Char) (m : Nat) (p t : List Char) (h : sep ∉ p) (hm : 0 < m) :
    splitMax sep m (p ++ sep :: t) = p :: splitMax sep (m - 1) t := by
  induction p with
  | nil => simp [splitMax, hm]
  | cons c cs ih =>
    have hc : c ≠ sep := by intro e; subst e; simp at h
    have h' : sep ∉ cs := by intro m; exact h (by simp [m])
    simp [splitMax, hc, ih h']

theorem splitMax_join (sep : Char) (parts : List (List Char)) (m : Nat) (hne : parts ≠ [])
    (hlen : parts.length ≤ m + 1) (h : ∀ p ∈ parts, sep ∉ p) :
    splitMax sep m (joinOn1 sep parts) = parts := by
  induction parts generalizing m with
  | nil => exact absurd rfl hne
  | cons p ps ih =>
    cases ps with
    | nil => simp [joinOn1, splitMax_nosep sep m p (h p (by simp))]
    | cons q qs =>
      simp only [List.length_cons] at hlen
      simp only [joinOn1]
      rw [splitMax_append sep m p _ (h p (by simp)) (by omega),
        ih (m - 1) (by simp) (by simp; omega) (fun r hr => h r (by simp [hr]))]

/-! ## `_compress_hextets` -/

/-- The loop body of `compressHextets`. -/
def cstep (st : Int × Nat × Int × Nat) (hi : List Char × Nat) : Int × Nat × Int × Nat :=
  let (bs, bl, ds, dl) := st
  let (h, i) := hi
  if h = ['0'] then
    let dl := dl + 1
    let ds := if ds = -1 then (i : Int) else ds
    if dl > bl then (ds, dl, ds, dl) else (bs, bl, ds, dl)
  else (bs, bl, -1, 0)

/-- What `compressHextets` does after the loop. -/
def cfinish (hs : List (List Char)) (st : Int × Nat × Int × Nat) : List (List Char) :=
  let (bs, bl, _, _) := st
  if bl > 1 then
    let e := bs.toNat + bl
    let hs := if e = hs.length then hs ++ [[]] else hs
    let hs := hs.take bs.toNat ++ [[]] ++ hs.drop e
    if bs = 0 then [] :: hs else hs
  else hs

theorem compress_eq (hs : List (List Char)) :
    compressHextets hs = cfinish hs (hs.zipIdx.foldl cstep (-1, 0, -1, 0)) := rfl

/-- After `k` hextets: the best run is empty or `[b, b + bl)` within the first `k`, all `'0'`; the
current run is empty (`-1`, `0`) or `[d, k)`, all `'0'`. -/
def CInv (hs : List (List Char)) (k : Nat) (st : Int × Nat × Int × Nat) : Prop :=
  (st.2.1 = 0 ∨ ∃ b : Nat, st.1 = b ∧ b + st.2.1 ≤ k ∧
      ∀ i, b ≤ i → i < b + st.2.1 → hs[i]? = some ['0']) ∧
  ((st.2.2.1 = -1 ∧ st.2.2.2 = 0) ∨ ∃ d : Nat, st.2.2.1 = d ∧ d + st.2.2.2 = k ∧
      ∀ i, d ≤ i → i < k → hs[i]? = some ['0'])

theorem cstep_inv (hs : List (List Char)) (k : Nat) (st : Int × Nat × Int × Nat) (h : List Char)
    (hk : hs[k]? = some h) (hI : CInv hs k st) : CInv hs (k + 1) (cstep st (h, k)) := by
  obtain ⟨bs, bl, ds, dl⟩ := st
  obtain ⟨hb, hd⟩ := hI
  simp only at hb hd
  simp only [cstep, CInv]
  by_cases hh : h = ['0']
  · subst hh
    simp only [↓reduceIte]
    have hcur : ∃ d : Nat, (if ds = -1 then (k : Int) else ds) = d ∧ d + (dl + 1) = k + 1 ∧
        ∀ i, d ≤ i → i < k + 1 → hs[i]? = some ['0'] := by
      rcases hd with ⟨h1, h2⟩ | ⟨d, h1, h2, h3⟩
      · refine ⟨k, by simp [h1], by omega, fun i hi1 hi2 => ?_⟩
        rw [show i = k by omega]; exact hk
      · have hne : ds ≠ -1 := by omega
        refine ⟨d, by simp [h1], by omega, fun i hi1 hi2 => ?_⟩
        by_cases hik : i < k
        · exact h3 i hi1 hik
        · rw [show i = k by omega]; exact hk
    obtain ⟨d, hd1, hd2, hd3⟩ := hcur
    by_cases hgt : dl + 1 > bl
    · simp only [hgt, ↓reduceIte]
      refine ⟨Or.inr ⟨d, hd1, by omega, fun i h1 h2 => hd3 i h1 (by omega)⟩, Or.inr ⟨d, hd1, hd2, hd3⟩⟩
    · simp only [hgt, ↓reduceIte]
      refine ⟨?_, Or.inr ⟨d, hd1, hd2, hd3⟩⟩
      rcases hb with h1 | ⟨b, h1, h2, h3⟩
      · exact Or.inl h1
      · exact Or.inr ⟨b, h1, by omega, h3⟩
  · simp only [hh, ↓reduceIte]
    refine ⟨?_, by simp⟩
    rcases hb with h1 | ⟨b, h1, h2, h3⟩
    · exact Or.inl h1
    · exact Or.inr ⟨b, h1, by omega, h3⟩

theorem fold_inv (hs : List (List Char)) : ∀ (l : List (List Char)) (k : Nat) (st : Int × Nat × Int × Nat),
    (∀ j, l[j]? = hs[k + j]?) → CInv hs k st →
    CInv hs (k + l.length) ((l.zipIdx k).foldl cstep st) := by
  intro l
  induction l with
  | nil => intro k st _ hI; simpa using hI
  | cons a l ih =>
    intro k st hl hI
    simp only [List.zipIdx_cons, List.foldl_cons, List.length_cons]
    have h0 := hl 0
    simp only [List.getElem?_cons_zero, Nat.add_zero] at h0
    have := ih (k + 1) (cstep st (a, k))
      (fun j => by have := hl (j + 1); simp only [List.getElem?_cons_succ] at this; rw [this]; congr 1; omega)
      (cstep_inv hs k st a h0.symm hI)
    rwa [show k + 1 + l.length = k + (l.length + 1) by omega] at this

/-- `_compress_hextets` returns its input, or replaces a run `[b, b + bl)` of `'0'` hextets, at
least two long, by `''`, with an extra `''` at either end of the address. -/
theorem compress_shape (hs : List (List Char)) :
    compressHextets hs = hs ∨ ∃ b bl : Nat, 2 ≤ bl ∧ b + bl ≤ hs.length ∧
      (∀ i, b ≤ i → i < b + bl → hs[i]? = some ['0']) ∧
      compressHextets hs = (if b = 0 then [[]] else []) ++ hs.take b ++ [[]] ++
        (if b + bl = hs.length then [[]] else hs.drop (b + bl)) := by
  have hf := fold_inv hs hs 0 (-1, 0, -1, 0) (by simp) (by simp [CInv])
  rw [compress_eq]
  generalize hs.zipIdx.foldl cstep (-1, 0, -1, 0) = st at hf ⊢
  obtain ⟨bs, bl, ds, dl⟩ := st
  simp only [CInv, Nat.zero_add] at hf
  obtain ⟨hb, -⟩ := hf
  unfold cfinish
  by_cases hgt : bl > 1
  · rcases hb with h1 | ⟨b, h1, h2, h3⟩
    · omega
    · right
      refine ⟨b, bl, by omega, h2, h3, ?_⟩
      subst h1
      simp only [hgt, ↓reduceIte, Int.toNat_natCast, Int.natCast_eq_zero]
      by_cases he : b + bl = hs.length
      · simp only [he, ↓reduceIte]
        rw [List.take_append_of_le_length (by omega), List.drop_left]
        by_cases h0 : b = 0 <;> simp [h0]
      · simp only [he, ↓reduceIte]
        by_cases h0 : b = 0 <;> simp [h0]
  · left; simp [hgt]

/-! ## Parsing the compressed form -/

theorem join_length_le (sep : Char) (c : Nat) (P : List (List Char)) (hl : ∀ p ∈ P, p.length ≤ c) :
    (joinOn1 sep P).length ≤ (c + 1) * P.length := by
  induction P with
  | nil => simp [joinOn1]
  | cons p ps ih =>
    cases ps with
    | nil => have := hl p (by simp); simp [joinOn1]; omega
    | cons q qs =>
      have := hl p (by simp)
      have := ih (fun r hr => hl r (by simp [hr]))
      simp only [joinOn1, List.length_append, List.length_cons] at this ⊢
      rw [Nat.mul_succ]
      omega

theorem join_parse_facts (P : List (List Char)) (hP : ∀ p ∈ P, p.all isHexC = true) (hl : ∀ p ∈ P, p.length ≤ 4)
    (h2 : 2 ≤ P.length) (h9 : P.length ≤ 9) :
    splitMax ':' 9 (joinOn1 ':' P) = P ∧ (joinOn1 ':' P).isEmpty = false ∧
      ¬ (joinOn1 ':' P).length > 45 := by
  refine ⟨splitMax_join ':' P 9 (by intro e; subst e; simp at h2) (by omega)
      (fun p hp => not_mem_of_hex p (hP p hp) ':' (by decide)), ?_, ?_⟩
  · match P, h2 with
    | p :: q :: qs, _ => simp [joinOn1]
  · have := join_length_le ':' 4 P hl; omega

theorem head!_cons' {α : Type} [Inhabited α] (a : α) (l : List α) : (a :: l).head! = a := rfl

/-- A hextet string and its value. -/
def HexGood (h : List Char) (v : Nat) : Prop :=
  parseHextet h = .ok v ∧ h.all isHexC = true ∧ h ≠ [] ∧ h.length ≤ 4 ∧ (h = ['0'] → v = 0)

theorem foldl_rep (k a : Nat) :
    (List.replicate k 0).foldl (fun v h => v * 65536 + h) a = a * 65536 ^ k := by
  induction k generalizing a with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, List.foldl_cons, ih, Nat.pow_succ]; simp [Nat.mul_assoc, Nat.mul_comm]

theorem combine_zeros (hi lo : List Nat) (k : Nat) :
    combine hi k lo = combine (hi ++ List.replicate k 0 ++ lo) 0 [] := by
  simp [combine, List.foldl_append, foldl_rep]

def AllHexGood (P : List (List Char)) : Prop := ∀ p ∈ P, p.all isHexC = true ∧ p.length ≤ 4

theorem allHexGood_nil : AllHexGood [] := by simp [AllHexGood]

theorem allHexGood_cons (p : List Char) (l : List (List Char)) (h : p.all isHexC = true ∧ p.length ≤ 4)
    (t : AllHexGood l) : AllHexGood (p :: l) := by
  intro q hq
  simp only [List.mem_cons] at hq
  rcases hq with rfl | hq
  · exact h
  · exact t q hq

theorem parse_join (P : List (List Char)) (hA : AllHexGood P) (h2 : 2 ≤ P.length) (h9 : P.length ≤ 9)
    (r : Py Nat)
    (H : ∀ s, splitMax ':' 9 s = P → s.isEmpty = false → ¬ s.length > 45 → ipIntFromString6 s = r) :
    ipIntFromString6 (joinOn1 ':' P) = r := by
  obtain ⟨a, b, c⟩ := join_parse_facts P (fun p hp => (hA p hp).1) (fun p hp => (hA p hp).2) h2 h9
  exact H _ a b c

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 2000000 in
/-- `_ip_int_from_string` of `':'.join(_compress_hextets(H))`, for any eight hextet strings that
`_parse_hextet` reads as `v0 .. v7` (and `'0'` only for 0): the 29 shapes of `compress_shape`, one
by one. -/
theorem compressed_parse (h0 h1 h2 h3 h4 h5 h6 h7 : List Char) (v0 v1 v2 v3 v4 v5 v6 v7 : Nat)
    (G0 : HexGood h0 v0) (G1 : HexGood h1 v1) (G2 : HexGood h2 v2) (G3 : HexGood h3 v3) (G4 : HexGood h4 v4)
    (G5 : HexGood h5 v5) (G6 : HexGood h6 v6) (G7 : HexGood h7 v7) :
    ipIntFromString6 (joinOn1 ':' (compressHextets [h0, h1, h2, h3, h4, h5, h6, h7])) =
      .ok (combine [v0, v1, v2, v3, v4, v5, v6, v7] 0 []) := by
  obtain ⟨p0, a0, e0, l0, z0⟩ := G0
  obtain ⟨p1, a1, e1, l1, z1⟩ := G1
  obtain ⟨p2, a2, e2, l2, z2⟩ := G2
  obtain ⟨p3, a3, e3, l3, z3⟩ := G3
  obtain ⟨p4, a4, e4, l4, z4⟩ := G4
  obtain ⟨p5, a5, e5, l5, z5⟩ := G5
  obtain ⟨p6, a6, e6, l6, z6⟩ := G6
  obtain ⟨p7, a7, e7, l7, z7⟩ := G7
  have d0 := not_mem_of_hex h0 a0 '.' (by decide)
  have d1 := not_mem_of_hex h1 a1 '.' (by decide)
  have d2 := not_mem_of_hex h2 a2 '.' (by decide)
  have d3 := not_mem_of_hex h3 a3 '.' (by decide)
  have d4 := not_mem_of_hex h4 a4 '.' (by decide)
  have d5 := not_mem_of_hex h5 a5 '.' (by decide)
  have d6 := not_mem_of_hex h6 a6 '.' (by decide)
  have d7 := not_mem_of_hex h7 a7 '.' (by decide)
  have k0 : h0.all isHexC = true ∧ h0.length ≤ 4 := ⟨a0, l0⟩
  have k1 : h1.all isHexC = true ∧ h1.length ≤ 4 := ⟨a1, l1⟩
  have k2 : h2.all isHexC = true ∧ h2.length ≤ 4 := ⟨a2, l2⟩
  have k3 : h3.all isHexC = true ∧ h3.length ≤ 4 := ⟨a3, l3⟩
  have k4 : h4.all isHexC = true ∧ h4.length ≤ 4 := ⟨a4, l4⟩
  have k5 : h5.all isHexC = true ∧ h5.length ≤ 4 := ⟨a5, l5⟩
  have k6 : h6.all isHexC = true ∧ h6.length ≤ 4 := ⟨a6, l6⟩
  have k7 : h7.all isHexC = true ∧ h7.length ≤ 4 := ⟨a7, l7⟩
  have knil : ([] : List Char).all isHexC = true ∧ ([] : List Char).length ≤ 4 := ⟨rfl, by decide⟩
  rcases compress_shape [h0, h1, h2, h3, h4, h5, h6, h7] with hc | ⟨b, bl, hb2, hb, hrun, hc⟩
  · rw [hc]
    refine parse_join _ ?_ (by simp) (by simp) _ ?_
    · repeat' (first | exact allHexGood_nil | refine allHexGood_cons _ _ ?_ ?_ | assumption)
    intro s hs he hl
    unfold ipIntFromString6
    simp [hs, he, hl, ipv6Suffix, ipv6Layout, ipv6Hextets, skipScan, p0, p1, p2, p3, p4, p5, p6, p7, d0, d1, d2, d3, d4, d5, d6, d7,
      e0, e1, e2, e3, e4, e5, e6, e7, parseHextets, head!_cons', Except.map]
    simp only [pure, Except.pure, Except.ok.injEq]
  · have y0 : b ≤ 0 → 0 < b + bl → v0 = 0 := fun x y => z0 (by simpa using hrun 0 x y)
    have y1 : b ≤ 1 → 1 < b + bl → v1 = 0 := fun x y => z1 (by simpa using hrun 1 x y)
    have y2 : b ≤ 2 → 2 < b + bl → v2 = 0 := fun x y => z2 (by simpa using hrun 2 x y)
    have y3 : b ≤ 3 → 3 < b + bl → v3 = 0 := fun x y => z3 (by simpa using hrun 3 x y)
    have y4 : b ≤ 4 → 4 < b + bl → v4 = 0 := fun x y => z4 (by simpa using hrun 4 x y)
    have y5 : b ≤ 5 → 5 < b + bl → v5 = 0 := fun x y => z5 (by simpa using hrun 5 x y)
    have y6 : b ≤ 6 → 6 < b + bl → v6 = 0 := fun x y => z6 (by simpa using hrun 6 x y)
    have y7 : b ≤ 7 → 7 < b + bl → v7 = 0 := fun x y => z7 (by simpa using hrun 7 x y)
    clear hrun
    simp only [List.length_cons, List.length_nil] at hb
    rw [hc]; clear hc
    obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 := by
      omega
    all_goals
      obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl : bl = 2 ∨ bl = 3 ∨ bl = 4 ∨ bl = 5 ∨ bl = 6 ∨ bl = 7 ∨ bl = 8 := by
        omega
    all_goals try (exfalso; omega)
    all_goals
      simp (failIfUnchanged := false) only [Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceAdd, Nat.le_refl,
        Nat.zero_le, false_implies, true_implies, Nat.not_succ_le_zero, Nat.lt_irrefl] at y0 y1 y2 y3 y4 y5 y6 y7
      subst_vars
    all_goals
      simp only [Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte, List.take_succ_cons, List.take_zero,
        List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_nil, List.cons_append,
        List.nil_append, List.append_nil]
      refine parse_join _ ?_ (by simp) (by simp) _ ?_
      · repeat' (first | exact allHexGood_nil | refine allHexGood_cons _ _ ?_ ?_ | assumption)
      intro s hs he hl
      unfold ipIntFromString6
      simp [hs, he, hl, ipv6Suffix, ipv6Layout, ipv6Hextets, skipScan, p0, p1, p2, p3, p4, p5, p6, p7, d0, d1, d2, d3, d4, d5, d6, d7,
        e0, e1, e2, e3, e4, e5, e6, e7, parseHextets, head!_cons', Except.map]
      simp only [pure, Except.pure, Except.ok.injEq]
      rw [combine_zeros]
      rfl

theorem dstep (n k K : Nat) (hK : K = k + 1) :
    n / 65536 ^ K * 65536 + n / 65536 ^ k % 65536 = n / 65536 ^ k := by
  subst hK
  rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]
  exact Nat.div_add_mod' _ _

theorem combine_digits (n : Nat) (hn : n < 2 ^ 128) :
    combine [n / 65536 ^ 7 % 65536, n / 65536 ^ 6 % 65536, n / 65536 ^ 5 % 65536, n / 65536 ^ 4 % 65536,
      n / 65536 ^ 3 % 65536, n / 65536 ^ 2 % 65536, n / 65536 ^ 1 % 65536, n / 65536 ^ 0 % 65536] 0 [] = n := by
  have h7 : n / 65536 ^ 7 < 65536 := by
    rw [Nat.div_lt_iff_lt_mul (by decide)]
    exact Nat.lt_of_lt_of_le hn (by decide)
  simp only [combine, List.foldl_cons, List.foldl_nil, Nat.pow_zero, Nat.mul_one, Nat.zero_mul,
    Nat.zero_add]
  rw [Nat.mod_eq_of_lt h7, dstep n 6 7 rfl, dstep n 5 6 rfl, dstep n 4 5 rfl, dstep n 3 4 rfl,
    dstep n 2 3 rfl, dstep n 1 2 rfl, dstep n 0 1 rfl, Nat.pow_zero, Nat.div_one]

theorem range8 : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := by simp [List.range_succ]

theorem hextetsOf_eq (n : Nat) : hextetsOf n = [hexStr (n / 65536 ^ 7 % 65536), hexStr (n / 65536 ^ 6 % 65536),
    hexStr (n / 65536 ^ 5 % 65536), hexStr (n / 65536 ^ 4 % 65536), hexStr (n / 65536 ^ 3 % 65536),
    hexStr (n / 65536 ^ 2 % 65536), hexStr (n / 65536 ^ 1 % 65536), hexStr (n / 65536 ^ 0 % 65536)] := by
  unfold hextetsOf
  rw [range8]
  simp only [List.map_cons, List.map_nil, Nat.reduceSub]

theorem good_of (v : Nat) (hv : v < 65536) : HexGood (hexStr v) v := hexStr_facts v hv

/-- The address without the IPv4-mapped form. -/
theorem plain_roundtrip (n : Nat) (hn : n < 2 ^ 128) : ipIntFromString6 (stringFromIpInt6 n) = .ok n := by
  unfold stringFromIpInt6
  rw [hextetsOf_eq, compressed_parse _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (good_of _ (Nat.mod_lt _ (by decide)))
    (good_of _ (Nat.mod_lt _ (by decide))) (good_of _ (Nat.mod_lt _ (by decide)))
    (good_of _ (Nat.mod_lt _ (by decide))) (good_of _ (Nat.mod_lt _ (by decide)))
    (good_of _ (Nat.mod_lt _ (by decide))) (good_of _ (Nat.mod_lt _ (by decide)))
    (good_of _ (Nat.mod_lt _ (by decide))), combine_digits n hn]

theorem hexStr_ffff : hexStr 65535 = ['f', 'f', 'f', 'f'] := by decide

theorem hexStr_0 : hexStr 0 = ['0'] := by decide

theorem compress_ffff : compressHextets [['0'], ['0'], ['0'], ['0'], ['0'], ['0'], ['0'], ['f', 'f', 'f', 'f']] =
    [[], [], ['f', 'f', 'f', 'f']] := by decide

theorem ffff_str : stringFromIpInt6 65535 = [':', ':', 'f', 'f', 'f', 'f'] := by
  rw [stringFromIpInt6, hextetsOf_eq]
  simp only [Nat.reducePow, Nat.reduceDiv, Nat.reduceMod, hexStr_0, hexStr_ffff, compress_ffff]
  rfl

/-! ## The IPv4-mapped form -/

set_option maxRecDepth 20000 in
theorem octet_len_all : ∀ d, d < 256 → (toString d).toList.length ≤ 3 := by decide

theorem ipv4Str_facts (m : Nat) :
    (ipv4Str m).all quadC = true ∧ (ipv4Str m).length ≤ 15 ∧ '.' ∈ ipv4Str m := by
  have o1 := octet_repr (m / 2 ^ 24 % 256) (Nat.mod_lt _ (by decide))
  have o2 := octet_repr (m / 2 ^ 16 % 256) (Nat.mod_lt _ (by decide))
  have o3 := octet_repr (m / 2 ^ 8 % 256) (Nat.mod_lt _ (by decide))
  have o4 := octet_repr (m % 256) (Nat.mod_lt _ (by decide))
  have q1 := octet_len_all (m / 2 ^ 24 % 256) (Nat.mod_lt _ (by decide))
  have q2 := octet_len_all (m / 2 ^ 16 % 256) (Nat.mod_lt _ (by decide))
  have q3 := octet_len_all (m / 2 ^ 8 % 256) (Nat.mod_lt _ (by decide))
  have q4 := octet_len_all (m % 256) (Nat.mod_lt _ (by decide))
  simp only [ipv4Str, stringFromIpInt4, toBytes4, List.map_cons, List.map_nil]
  refine ⟨all_join quadC '.' _ (by decide) ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl | rfl)
    · exact digits_quad _ o1.2.1
    · exact digits_quad _ o2.2.1
    · exact digits_quad _ o3.2.1
    · exact digits_quad _ o4.2.1
  · have := join_length_le '.' 3 [(toString (m / 2 ^ 24 % 256)).toList, (toString (m / 2 ^ 16 % 256)).toList,
      (toString (m / 2 ^ 8 % 256)).toList, (toString (m % 256)).toList] (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl | rfl | rfl) <;> assumption)
    simp only [List.length_cons, List.length_nil] at this
    have h2 : (joinOn1 '.' [(toString (m / 2 ^ 24 % 256)).toList, (toString (m / 2 ^ 16 % 256)).toList,
      (toString (m / 2 ^ 8 % 256)).toList, (toString (m % 256)).toList]).length =
        (toString (m / 2 ^ 24 % 256)).toList.length + (toString (m / 2 ^ 16 % 256)).toList.length +
        (toString (m / 2 ^ 8 % 256)).toList.length + (toString (m % 256)).toList.length + 3 := by
      simp [joinOn1]; omega
    omega
  · simp [joinOn1]

theorem quad_not (p : List Char) (h : p.all quadC = true) (c : Char) (hc : quadC c = false) : c ∉ p := by
  intro m
  have := List.all_eq_true.mp h c m
  rw [hc] at this; exact Bool.false_ne_true this

theorem parse_ffff : parseHextet ['f', 'f', 'f', 'f'] = .ok 65535 := rfl

theorem mapped_combine (n m : Nat) (hm : m < 2 ^ 32) (hn : n = 2 ^ 32 * 65535 + m) :
    combine [] 5 [65535, m / 65536 % 65536, m % 65536] = n := by
  have h1 : m / 65536 % 65536 = m / 65536 := Nat.mod_eq_of_lt (by omega)
  simp only [combine, List.foldl_cons, List.foldl_nil, Nat.zero_mul, Nat.zero_add]
  omega

/-- The IPv4-mapped address: `"::ffff:" ++ str(ipv4_mapped)`. -/
theorem mapped_roundtrip (n : Nat) (hq : n / 2 ^ 32 = 65535) :
    ipIntFromString6 (stringFromIpInt6 (n / 2 ^ 32) ++ ':' :: ipv4Str (n % 2 ^ 32)) = .ok n := by
  have hm : n % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  obtain ⟨qa, ql, qd⟩ := ipv4Str_facts (n % 2 ^ 32)
  have hv4 := v4RoundTrip_proven (n % 2 ^ 32) hm
  obtain ⟨pa, -, ea, -, -⟩ := hexStr_facts (n % 2 ^ 32 / 65536 % 65536) (Nat.mod_lt _ (by decide))
  obtain ⟨pb, -, eb, -, -⟩ := hexStr_facts (n % 2 ^ 32 % 65536) (Nat.mod_lt _ (by decide))
  have hn : n = 2 ^ 32 * 65535 + n % 2 ^ 32 := by
    have := Nat.div_add_mod n (2 ^ 32); rw [hq] at this; omega
  rw [hq, ffff_str]
  generalize n % 2 ^ 32 = m at hm hv4 pa pb ea eb hn qa ql qd ⊢
  generalize ipv4Str m = q at qa ql qd hv4
  have hc : ':' ∉ q := quad_not q qa ':' (by decide)
  have hj : [':', ':', 'f', 'f', 'f', 'f'] ++ ':' :: q = joinOn1 ':' [[], [], ['f', 'f', 'f', 'f'], q] := by
    simp [joinOn1]
  have hs := splitMax_join ':' [[], [], ['f', 'f', 'f', 'f'], q] 9 (by simp) (by simp) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl | rfl)
    · simp
    · simp
    · decide
    · exact hc)
  have hl : ¬ ([':', ':', 'f', 'f', 'f', 'f'] ++ ':' :: q).length > 45 := by simp; omega
  rw [hj] at hl ⊢
  have he : (joinOn1 ':' [[], [], ['f', 'f', 'f', 'f'], q]).isEmpty = false := by simp [joinOn1]
  generalize joinOn1 ':' [[], [], ['f', 'f', 'f', 'f'], q] = s at hs hl he ⊢
  unfold ipIntFromString6
  simp [hs, he, hl, qd, hv4, ipv6Suffix, ipv6Layout, ipv6Hextets, skipScan, pa, pb, ea, eb, parse_ffff, parseHextets, head!_cons', Except.map]
  simp only [pure, Except.pure, Except.ok.injEq]
  exact mapped_combine n m hm hn

/-! ## Characters, the scope id, and the theorem -/

theorem compress_mem (hs : List (List Char)) : ∀ p ∈ compressHextets hs, p ∈ hs ∨ p = [] := by
  intro p hp
  rcases compress_shape hs with hc | ⟨b, bl, -, -, -, hc⟩
  · rw [hc] at hp; exact Or.inl hp
  · rw [hc] at hp
    simp only [List.mem_append] at hp
    rcases hp with ((h | h) | h) | h
    · split at h <;> simp_all
    · exact Or.inl (List.mem_of_mem_take h)
    · simp_all
    · split at h
      · simp_all
      · exact Or.inl (List.mem_of_mem_drop h)

/-- A character of `str()` of an IPv6 address without its scope id. -/
def v6C (c : Char) : Bool := isHexC c || c == ':' || c == '.'

theorem v6C_of_hex (p : List Char) (h : p.all isHexC = true) : p.all v6C = true := by
  simp only [List.all_eq_true] at h ⊢
  intro c hc; simp [v6C, h c hc]

theorem digit_hex (c : Char) (h : isDigitC c = true) : isHexC c = true := by
  simp only [isDigitC, isHexC, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h ⊢
  omega

theorem v6C_of_quad (p : List Char) (h : p.all quadC = true) : p.all v6C = true := by
  simp only [List.all_eq_true] at h ⊢
  intro c hc
  have := h c hc
  simp only [quadC, Bool.or_eq_true] at this
  rcases this with h1 | h1
  · simp [v6C, digit_hex c h1]
  · simp only [beq_iff_eq] at h1; subst h1; decide

theorem v6C_not (p : List Char) (h : p.all v6C = true) (c : Char) (hc : v6C c = false) : c ∉ p := by
  intro m
  have := List.all_eq_true.mp h c m
  rw [hc] at this; exact Bool.false_ne_true this

theorem plain_chars (n : Nat) : (stringFromIpInt6 n).all v6C = true := by
  unfold stringFromIpInt6
  apply all_join v6C ':' _ (by decide)
  intro p hp
  rcases compress_mem _ p hp with h | h
  · unfold hextetsOf at h
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp h
    exact v6C_of_hex _ (hexStr_facts _ (Nat.mod_lt _ (by decide))).2.1
  · subst h; rfl

/-- `str()` of the address before the scope id: the IPv4-mapped form or `_string_from_ip_int`. -/
def base6 (n : Nat) : List Char :=
  if n / 2 ^ 32 = 0xFFFF then stringFromIpInt6 (n / 2 ^ 32) ++ ':' :: ipv4Str (n % 2 ^ 32)
  else stringFromIpInt6 n

theorem base6_ok (n : Nat) (hn : n < 2 ^ 128) :
    (base6 n).all v6C = true ∧ ipIntFromString6 (base6 n) = .ok n := by
  unfold base6
  by_cases hq : n / 2 ^ 32 = 0xFFFF
  · simp only [hq, ↓reduceIte]
    refine ⟨?_, by have := mapped_roundtrip n hq; rwa [hq] at this⟩
    rw [ffff_str]
    simp only [List.all_append, List.all_cons, Bool.and_eq_true]
    exact ⟨by decide, by decide, v6C_of_quad _ (ipv4Str_facts _).1⟩
  · simp only [hq, ↓reduceIte]
    exact ⟨plain_chars n, plain_roundtrip n hn⟩

theorem span_loop_app (p : Char → Bool) (a t acc : List Char) (h : ∀ c ∈ a, p c = true) :
    List.span.loop p (a ++ t) acc = List.span.loop p t (a.reverse ++ acc) := by
  induction a generalizing acc with
  | nil => simp
  | cons c a ih =>
    simp only [List.cons_append, List.span.loop, h c (by simp)]
    rw [ih (c :: acc) (fun d hd => h d (by simp [hd]))]
    simp

theorem partition_none (a : List Char) (h : '%' ∉ a) : partitionPct a = (a, false, []) := by
  have := span_loop_app (fun x => decide (x ≠ '%')) a [] [] (fun c hc => by
    have : c ≠ '%' := fun e => h (e ▸ hc)
    simp [this])
  simp only [List.append_nil] at this
  simp only [partitionPct, List.span]
  rw [this]
  simp [List.span.loop]

theorem partition_some (a x : List Char) (h : '%' ∉ a) : partitionPct (a ++ '%' :: x) = (a, true, x) := by
  have := span_loop_app (fun x => decide (x ≠ '%')) a ('%' :: x) [] (fun c hc => by
    have : c ≠ '%' := fun e => h (e ▸ hc)
    simp [this])
  simp only [partitionPct, List.span]
  rw [this]
  simp [List.span.loop]

theorem shiftRight32 (n : Nat) : n >>> 32 = n / 2 ^ 32 := Nat.shiftRight_eq_div_pow n 32

theorem and32 (n : Nat) : n &&& 0xFFFFFFFF = n % 2 ^ 32 := by
  rw [show (0xFFFFFFFF : Nat) = 2 ^ 32 - 1 by rfl]; exact Nat.and_two_pow_sub_one_eq_mod n 32

theorem ipv4Mapped_eq (n : Nat) :
    ipv4Mapped n = if n / 2 ^ 32 = 0xFFFF then some (n % 2 ^ 32) else none := by
  simp only [ipv4Mapped, shiftRight32, and32]

/-- `str()` of an IPv6 address with a 128-bit `_ip` succeeds, with the text `ipv6Str` gives. -/
theorem ipv6StrPy_eq (n : Nat) (hn : n < 2 ^ 128) (sc : Option (List Char)) :
    ipv6StrPy n sc = .ok (ipv6Str n sc) := by
  have hle : ¬ n > allOnes 128 := by unfold allOnes; omega
  have hq' : ¬ (65535 : Nat) > allOnes 128 := by unfold allOnes; decide
  unfold ipv6StrPy ipv6Str
  rw [ipv4Mapped_eq]
  by_cases hq : n / 2 ^ 32 = 0xFFFF
  · simp only [hq, ↓reduceIte, ipv4MappedToStr, ipv4Mapped_eq, stringFromIpInt6Py, shiftRight32, hq']
    cases sc <;> rfl
  · simp only [hq, ↓reduceIte, stringFromIpInt6Py, hle]
    cases sc <;> rfl

/-- `IPv6Address(str(IPv6Address(n) with scope sc))` gives `n` and `sc` back. -/
theorem v6RoundTrip_proven : V6RoundTrip := by
  intro n sc hn hsc
  refine ⟨ipv6Str n sc, ipv6StrPy_eq n hn sc, ?_⟩
  show ipv6InitStr (ipv6Str n sc) = .ok (n, sc)
  obtain ⟨hc, hp⟩ := base6_ok n hn
  have hslash : '/' ∉ base6 n := v6C_not _ hc '/' (by decide)
  have hpct : '%' ∉ base6 n := v6C_not _ hc '%' (by decide)
  have hstr : ipv6Str n sc = match sc with | some x => base6 n ++ '%' :: x | none => base6 n := by
    cases sc with
    | none => rfl
    | some x =>
      have hx := (hsc x rfl).1
      simp only [ipv6Str, base6]
      have hx' : x.isEmpty = false := by simpa using hx
      simp only [hx', Bool.false_eq_true, ↓reduceIte]
  rw [hstr]
  cases sc with
  | none =>
    simp [ipv6InitStr, splitScopeId, hslash, partition_none _ hpct, hp, bind, Except.bind, pure,
      Except.pure]
  | some x =>
    obtain ⟨hx0, hx1, hx2⟩ := hsc x rfl
    have hs : '/' ∉ base6 n ++ '%' :: x := by simp [hslash, hx2]
    have hx0' : x.isEmpty = false := by cases x <;> simp_all
    simp [ipv6InitStr, splitScopeId, hs, partition_some _ _ hpct, hp, hx0', hx1, bind, Except.bind,
      pure, Except.pure, Functor.map, Except.map]

end PyLean.Ipaddress
