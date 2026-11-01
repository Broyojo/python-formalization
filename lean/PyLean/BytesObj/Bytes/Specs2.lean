import PyLean.BytesObj.Bytes.Specs

/-!
What the search, comparison, subscript and `hex` methods compute, stated without their code.
-/

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch
open PyLean.RangeSlice (Slice sliceUnpack)

/-! ## find, index, count, in -/

theorem bytesFindObj_bytes (s sub : Seq) (st en : Option Int) (fwd : Bool) :
    bytesFindObj s (.bytes sub) st en fwd = bytesFind s (.buf sub) st en fwd := rfl

theorem bytesCountObj_bytes (s sub : Seq) (st en : Option Int) :
    bytesCountObj s (.bytes sub) st en = bytesCount s (.buf sub) st en := rfl

/-- `b.find(sub, start, end)` is the least index, and `rfind` the greatest, at which `sub` occurs
within the normalised bounds, or -1 when there is none; `index` and `rindex` give the same answer and
raise where `find` gives -1. Hypothesis: the type invariant that both are bytes. -/
def BytesFindExtreme : Prop :=
  ∀ (s sub : Seq) (st en : Option Int), (∀ x ∈ s, x < 256) → (∀ x ∈ sub, x < 256) →
    let a := (adjustIndices (argStart st) (argEnd en) s.length).1
    let b := (adjustIndices (argStart st) (argEnd en) s.length).2
    (∃ r, bytesFindObj s (.bytes sub) st en true = .ok r ∧
      ((r = -1 ∧ ∀ i, ¬ InRange s sub a b i) ∨
        ∃ i : Nat, r = i ∧ InRange s sub a b i ∧ ∀ j, InRange s sub a b j → i ≤ j)) ∧
    (∃ r, bytesFindObj s (.bytes sub) st en false = .ok r ∧
      ((r = -1 ∧ ∀ i, ¬ InRange s sub a b i) ∨
        ∃ i : Nat, r = i ∧ InRange s sub a b i ∧ ∀ j, InRange s sub a b j → j ≤ i)) ∧
    ∀ (fwd : Bool) (r : Int), bytesFindObj s (.bytes sub) st en fwd = .ok r →
      bytesIndexObj s (.bytes sub) st en fwd =
        if r = -1 then .error (.valueError "subsection not found") else .ok r

theorem bytesFindExtreme_proven : BytesFindExtreme := by
  intro s sub st en hs hsub
  dsimp only
  have hf := fun fwd => (findStrBytes_proven s sub st en fwd hs hsub).1
  have h := findExtreme_proven s sub st en
  dsimp only at h
  refine ⟨⟨_, hf true, h.1⟩, ⟨_, hf false, h.2⟩, fun fwd r hr => ?_⟩
  rw [bytesFindObj_bytes] at hr
  have h2 : bytesFindInternal s (.buf sub) (argStart st) (argEnd en) fwd = .ok r := hr
  have h3 : bytesIndexObj s (.bytes sub) st en fwd = bytesIndex s (.buf sub) st en fwd := rfl
  rw [h3]
  simp only [bytesIndex, h2, bind, Except.bind, pure, Except.pure]
  split <;> rfl

/-- `b.count(sub, start, end)` for a non-empty `sub` is the number of rounds of the loop that repeats
`find` from the end of the previous match; for an empty `sub` it is the number of positions in the
normalised bounds. Hypotheses: bytes, and `len(s) < sys.maxsize` (every object). -/
def BytesCountSpec : Prop :=
  ∀ (s sub : Seq) (st en : Option Int), (∀ x ∈ s, x < 256) → (∀ x ∈ sub, x < 256) →
    (s.length : Int) < ssizeMax →
    (sub ≠ [] → bytesCountObj s (.bytes sub) st en = .ok (countByFind s sub en (s.length + 1) st)) ∧
    (let a := (adjustIndices (argStart st) (argEnd en) s.length).1
     let b := (adjustIndices (argStart st) (argEnd en) s.length).2
     bytesCountObj s (.bytes []) st en = .ok (if b < a then 0 else b - a + 1))

theorem bytesCountSpec_proven : BytesCountSpec := by
  intro s sub st en hs hsub hlen
  constructor
  · intro hne
    rw [bytesCountObj_bytes, (findStrBytes_proven s sub st en true hs hsub).2.2.1,
      countRepeatedFind_proven s sub st en hne hlen]
  · dsimp only
    rw [bytesCountObj_bytes]
    have hb := adjust_snd_le (argStart st) (argEnd en) s.length (by omega)
    have ha := adjust_fst_nonneg (argStart st) (argEnd en) s.length
    simp only [bytesCount, parseFindsByte, bind, Except.bind, pure, Except.pure]
    generalize adjustIndices (argStart st) (argEnd en) s.length = ab at *
    obtain ⟨a, b⟩ := ab
    simp only at ha hb ⊢
    congr 1
    simp only [stringlibCount, List.length_nil]
    unfold ssizeMax at hlen ⊢
    by_cases h : b < a
    · have h' : b - a < 0 := by omega
      rw [if_pos h', if_pos h]
    · have h' : ¬ b - a < 0 := by omega
      have h'' : b - a < 2 ^ 63 - 1 := by omega
      rw [if_neg h', if_pos trivial, if_pos h'', if_neg h]

/-- `p in b` for a bytes-like `p` is exactly "`p` occurs in `b`", at any place and any length. -/
def ContainsSub : Prop :=
  ∀ s p : Seq, ∃ r, bytesContains s (.bytes p) = .ok r ∧ (r = true ↔ ∃ i, Occ s p i)

theorem containsSub_proven : ContainsSub := by
  intro s p
  refine ⟨decide (stringlibFind s p 0 ≥ 0), rfl, ?_⟩
  simp only [decide_eq_true_eq]
  by_cases hp : p = []
  · subst hp
    simp only [stringlibFind, List.length_nil, ↓reduceIte, ge_iff_le, Int.le_refl, true_iff]
    exact ⟨0, by simp [Occ]⟩
  by_cases hl : p.length ≤ s.length
  · rw [stringlibFind_eq hl]
    have hc := findL_correct p s
    cases hf : findL p s with
    | none =>
      rw [hf] at hc
      simp only [optOff]
      constructor
      · intro h; omega
      · rintro ⟨i, hi⟩; exact absurd hi (hc i)
    | some i =>
      rw [hf] at hc
      simp only [optOff]
      exact ⟨fun _ => ⟨i, hc.1⟩, fun _ => by omega⟩
  · have hn : p.length ≠ 0 := by simpa using hp
    have h1 : stringlibFind s p 0 = -1 := by
      have hlt : s.length < p.length := by omega
      simp [stringlibFind, hn, fastsearch, hlt]
    rw [h1]
    constructor
    · intro h; omega
    · rintro ⟨i, hi⟩
      have := hi.1
      omega

/-! ## startswith, endswith -/

theorem matchAt_occ (s p : Seq) (i : Int) (h0 : 0 ≤ i) (h : i + p.length ≤ s.length) :
    matchAt s p i = true ↔ Occ s p i.toNat := by
  unfold matchAt
  rw [isPrefixOf_eq_true_iff, Occ, List.length_drop]
  constructor
  · intro ⟨_, h2⟩; exact ⟨by omega, h2⟩
  · intro ⟨_, h2⟩; exact ⟨by omega, h2⟩

/-- `startswith` and `endswith` on the normalised bounds `a`, `b`: the bounds leave room for `p`, and
`p` occurs at `a` (at `b - len(p)`). A wrong anchor or a constant fails this. -/
def TailmatchSpec : Prop :=
  ∀ (s p : Seq) (st en : Int),
    let a := (adjustIndices st en s.length).1
    let b := (adjustIndices st en s.length).2
    (bytesTailmatch s p st en false = true ↔ a + p.length ≤ b ∧ Occ s p a.toNat) ∧
    (bytesTailmatch s p st en true = true ↔ a + p.length ≤ b ∧ Occ s p (b - p.length).toNat)

theorem tailmatchSpec_proven : TailmatchSpec := by
  intro s p st en
  dsimp only
  have ha := adjust_fst_nonneg st en s.length
  have hb := adjust_snd_le st en s.length (by omega)
  simp only [bytesTailmatch]
  generalize adjustIndices st en s.length = ab at *
  obtain ⟨a, b⟩ := ab
  simp only at ha hb ⊢
  by_cases hc : a + p.length ≤ b
  · have h1 : ¬ a > (s.length : Int) - p.length := by omega
    have h2 : ¬ b - a < p.length := by omega
    have h3 : ¬ a > s.length := by omega
    have h4 : ¬ b - (b - (p.length : Int)) < p.length := by omega
    have h5 : (if b - p.length > a then b - p.length else a) = b - p.length := by
      split <;> omega
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte, h1, h2, h3, h4, h5, hc,
      true_and, false_or]
    exact ⟨matchAt_occ s p a ha (by omega), matchAt_occ s p (b - p.length) (by omega) (by omega)⟩
  · have h2 : b - a < p.length := by omega
    have h3 : b - a < p.length ∨ a > s.length := Or.inl h2
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte, h2, h3, hc, false_and,
      iff_false]
    constructor
    · split <;> simp
    · simp

/-! ## Ordering -/

/-- The first difference, unsigned bytes; a proper prefix comes first. -/
def lexCmp : Seq → Seq → Int
  | [], [] => 0
  | [], _ :: _ => -1
  | _ :: _, [] => 1
  | a :: as, b :: bs => if a < b then -1 else if a > b then 1 else lexCmp as bs

theorem memcmp_lex : ∀ a b : Seq,
    let c := memcmp (min a.length b.length) a b
    (c ≠ 0 → c = lexCmp a b) ∧ (c = 0 → (lexCmp a b = 0 ↔ a.length = b.length) ∧
      (lexCmp a b < 0 ↔ a.length < b.length) ∧ (lexCmp a b > 0 ↔ a.length > b.length))
  | [], [] => by simp [memcmp, lexCmp]
  | [], _ :: _ => by simp [memcmp, lexCmp]
  | _ :: _, [] => by simp [memcmp, lexCmp]
  | x :: xs, y :: ys => by
    have hm : min (x :: xs).length (y :: ys).length = min xs.length ys.length + 1 := by
      simp only [List.length_cons]; omega
    have ih := memcmp_lex xs ys
    dsimp only at ih ⊢
    rw [hm]
    simp only [memcmp, lexCmp, List.length_cons]
    by_cases h1 : x < y
    · simp [h1]
    · by_cases h2 : x > y
      · simp [h1, h2]
      · simp only [h1, h2, ↓reduceIte]
        refine ⟨ih.1, fun h => ?_⟩
        obtain ⟨a1, a2, a3⟩ := ih.2 h
        refine ⟨?_, ?_, ?_⟩ <;> omega

theorem lexCmp_range : ∀ a b : Seq, lexCmp a b = -1 ∨ lexCmp a b = 0 ∨ lexCmp a b = 1
  | [], [] => by simp [lexCmp]
  | [], _ :: _ => by simp [lexCmp]
  | _ :: _, [] => by simp [lexCmp]
  | x :: xs, y :: ys => by
    simp only [lexCmp]
    split
    · simp
    · split
      · simp
      · exact lexCmp_range xs ys

theorem lexCmp_eq : ∀ a b : Seq, lexCmp a b = 0 ↔ a = b
  | [], [] => by simp [lexCmp]
  | [], _ :: _ => by simp [lexCmp]
  | _ :: _, [] => by simp [lexCmp]
  | x :: xs, y :: ys => by
    simp only [lexCmp, List.cons.injEq]
    by_cases h1 : x < y
    · simp only [h1, ↓reduceIte]
      constructor
      · intro h; omega
      · intro h; omega
    · by_cases h2 : x > y
      · simp only [h1, h2, ↓reduceIte]
        constructor
        · intro h; omega
        · intro h; omega
      · simp only [h1, h2, ↓reduceIte, lexCmp_eq xs ys]
        have : x = y := by omega
        simp [this]

theorem rich_sign (op : CmpOp) (x y : Int) (h1 : x < 0 ↔ y < 0) (h2 : x > 0 ↔ y > 0) :
    richResult op x 0 = richResult op y 0 := by
  have h3 : x = 0 ↔ y = 0 := by omega
  have h4 : x ≤ 0 ↔ y ≤ 0 := by omega
  have h5 : x ≥ 0 ↔ y ≥ 0 := by omega
  cases op <;> simp [richResult, h1, h3, h4, h5] <;> omega

theorem rich_lens (op : CmpOp) (p q y : Int) (h0 : y = 0 ↔ p = q) (h1 : y < 0 ↔ p < q)
    (h2 : y > 0 ↔ p > q) : richResult op p q = richResult op y 0 := by
  cases op <;> simp only [richResult, decide_eq_decide] <;> omega

/-- Every ordering of `bytes` is the sign of the first difference, a proper prefix coming first, and
`lexCmp` is zero exactly on equal strings. A comparison that used signed bytes, the length first or
only the first byte fails this. -/
def RichLex : Prop :=
  ∀ a b : Seq,
    (∀ op : CmpOp, op ≠ .eq → op ≠ .ne → bytesRichcompare a b op = richResult op (lexCmp a b) 0) ∧
    (lexCmp a b = 0 ↔ a = b) ∧ lexCmp a b = - lexCmp b a

theorem lexCmp_anti : ∀ a b : Seq, lexCmp a b = - lexCmp b a
  | [], [] => by simp [lexCmp]
  | [], _ :: _ => by simp [lexCmp]
  | _ :: _, [] => by simp [lexCmp]
  | x :: xs, y :: ys => by
    simp only [lexCmp]
    have ih := lexCmp_anti xs ys
    by_cases h1 : x < y
    · have : ¬ y < x := by omega
      simp [h1, this]
    · by_cases h2 : y < x
      · simp [h1, h2]
      · simp only [h1, h2, gt_iff_lt, ↓reduceIte]
        exact ih

theorem richLex_proven : RichLex := by
  intro a b
  refine ⟨fun op h1 h2 => ?_, lexCmp_eq a b, lexCmp_anti a b⟩
  have hcm := memcmp_lex a b
  dsimp only at hcm
  have hr := lexCmp_range a b
  unfold bytesRichcompare
  rw [if_neg (by simp [h1, h2])]
  dsimp only
  generalize hc : (if min a.length b.length > 0 then
      let d := (a.headD 0 : Int) - (b.headD 0 : Int)
      if d = 0 then memcmp (min a.length b.length) a b else d
    else 0) = c
  have hsign : (c ≠ 0 → (c < 0 ↔ lexCmp a b < 0) ∧ (c > 0 ↔ lexCmp a b > 0)) ∧
      (c = 0 → (lexCmp a b = 0 ↔ a.length = b.length) ∧
        (lexCmp a b < 0 ↔ a.length < b.length) ∧ (lexCmp a b > 0 ↔ a.length > b.length)) := by
    subst hc
    cases a with
    | nil =>
      cases b with
      | nil => simp [lexCmp]
      | cons y ys => simp [lexCmp]
    | cons x xs =>
      cases b with
      | nil => simp [lexCmp]
      | cons y ys =>
        have hm : min (x :: xs).length (y :: ys).length > 0 := by simp only [List.length_cons]; omega
        simp only [hm, ↓reduceIte, List.headD_cons]
        by_cases hd : (x : Int) - (y : Int) = 0
        · simp only [hd, ↓reduceIte]
          refine ⟨fun h => ?_, hcm.2⟩
          rw [hcm.1 h]
          omega
        · simp only [hd, ↓reduceIte]
          have hl : lexCmp (x :: xs) (y :: ys) = if x < y then -1 else 1 := by
            simp only [lexCmp]
            by_cases h3 : x < y
            · simp [h3]
            · have h4 : x > y := by omega
              simp [h3, h4]
          rw [hl]
          refine ⟨fun _ => ?_, fun h => False.elim h⟩
          split <;> omega
  by_cases hc0 : c = 0
  · rw [if_neg (by simpa using hc0)]
    obtain ⟨a1, a2, a3⟩ := hsign.2 hc0
    exact rich_lens op _ _ _ (by omega) (by omega) (by omega)
  · rw [if_pos hc0]
    obtain ⟨a1, a2⟩ := hsign.1 hc0
    exact rich_sign op _ _ a1 a2

/-! ## Subscript -/

/-- `b[i]`: a negative index counts from the end, anything else out of range raises; `b[s]`: the
elements `a, a+c, ...` of `range(*s.indices(len(b)))`, each in bounds, in that order. Hypotheses: the
index fits a `Py_ssize_t` (the other case is `subIndex`) and the step is not zero (`ValueError`). -/
def SubscriptSpec : Prop :=
  (∀ (s : Seq) (i : Int), ssizeMin ≤ i → i ≤ ssizeMax → (s.length : Int) ≤ ssizeMax →
    (i < -(s.length : Int) ∨ i ≥ s.length → bytesGetItem s i = .error (.indexError "index out of range")) ∧
    (-(s.length : Int) ≤ i → i < 0 → bytesGetItem s i = .ok (s.getD (i + s.length).toNat 0)) ∧
    (0 ≤ i → i < s.length → bytesGetItem s i = .ok (s.getD i.toNat 0))) ∧
  (∀ (s : Seq) (sl : Slice), sl.step ≠ some 0 → (s.length : Int) ≤ ssizeMax →
    ∃ (a b c L : Int) (r : Seq), RangeSlice.sliceIndices sl s.length = .ok (a, b, c) ∧
      RangeSlice.IsLen a b c L ∧ bytesGetSlice s sl = .ok r ∧ (r.length : Int) = L ∧
      ∀ k : Nat, (k : Int) < L → 0 ≤ a + k * c ∧ a + k * c < s.length ∧
        r[k]? = s[(a + k * c).toNat]?)

theorem bytesGetItem_eq (s : Seq) (i : Int) (h1 : ssizeMin ≤ i) (h2 : i ≤ ssizeMax) :
    bytesGetItem s i =
      (let j := if i < 0 then i + s.length else i
       if j < 0 ∨ j ≥ s.length then .error (.indexError "index out of range")
       else .ok (s.getD j.toNat 0)) := by
  have hs : Sequences.subIndex i = .ok i := by
    simp only [Sequences.subIndex, Sequences.asSsizeExc]
    rw [if_pos ⟨h1, h2⟩]
  simp only [bytesGetItem, hs, bind, Except.bind, pure, Except.pure]
  split <;> rfl

theorem subscriptSpec_proven : SubscriptSpec := by
  constructor
  · intro s i h1 h2 hl
    rw [bytesGetItem_eq s i h1 h2]
    refine ⟨fun h => ?_, fun h3 h4 => ?_, fun h3 h4 => ?_⟩
    · dsimp only
      rw [if_pos (by split <;> omega)]
    · dsimp only
      rw [if_pos h4, if_neg (by omega)]
    · dsimp only
      rw [if_neg (by omega), if_neg (by omega)]
  · intro s sl h0 hlen
    obtain ⟨a, b, c, L, st, sp, c', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
      Sequences.adjust_spec sl s.length (by omega) hlen h0
    have hb := RangeSlice.indices_in_bounds a b c s.length L h2 h3
    have hne : sl.step.getD 1 ≠ 0 := by
      cases hst : sl.step with
      | none => simp
      | some v =>
        intro e
        exact h0 (by simp_all)
    have hstep : -ssizeMax ≤ c' ∧ c' ≤ ssizeMax := by
      have e := RangeSlice.sliceUnpack_eq sl h0
      rw [h5] at e
      simp only [Except.ok.injEq, Prod.mk.injEq] at e
      rw [e.2.2]
      have hc := RangeSlice.clampStep_sign _ hne
      exact ⟨hc.2.2.1, hc.2.2.2.1⟩
    have hL : 0 ≤ L := h2.1
    have hcc : ∀ k : Nat, (k : Int) < L → a + k * c' = a + k * c := by
      intro k hk
      cases k with
      | zero => simp
      | succ k =>
        have hk' : (1 : Int) < L := by
          have : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by simp
          omega
        have h0a := hb 0 (by omega) (by omega)
        have h1b := hb 1 (by omega) (by omega)
        have hu := h11 1 (by omega) (by omega)
        simp only [Int.one_mul, Int.zero_mul, Int.add_zero] at h0a h1b hu
        have hcc : c' = c := by
          unfold RangeSlice.toU RangeSlice.two64 at hu
          unfold ssizeMax at hstep hlen
          omega
        rw [hcc]
    have hget : ∀ k : Nat, (k : Int) < L → 0 ≤ a + k * c ∧ a + k * c < s.length := by
      intro k hk
      exact hb k (by omega) hk
    have hunf : bytesGetSlice s sl = (if L ≤ 0 then .ok [] else
        if a = 0 ∧ c' = 1 ∧ L = s.length then .ok s else
        if c' = 1 then .ok ((s.drop a.toNat).take L.toNat) else
        .ok ((slicePositions a c' L.toNat).map (fun p => s.getD p.toNat 0))) := by
      simp only [bytesGetSlice, bind, Except.bind, h5, h6, pure, Except.pure]
    by_cases hL0 : L ≤ 0
    · rw [if_pos hL0] at hunf
      exact ⟨a, b, c, L, [], h1, h2, hunf, by simp; omega, fun k hk => by omega⟩
    rw [if_neg hL0] at hunf
    by_cases hc1 : c' = 1
    · have hc : c = 1 := h7.1 hc1
      subst hc
      have hend : a + L ≤ s.length := by
        have := hget (L.toNat - 1) (by omega)
        have h2 : ((L.toNat - 1 : Nat) : Int) = L - 1 := by omega
        rw [h2] at this
        omega
      have ha0 : 0 ≤ a := by
        have := hget 0 (by omega)
        simpa using this.1
      have hmain : bytesGetSlice s sl = .ok ((s.drop a.toNat).take L.toNat) := by
        rw [hunf]
        by_cases hfull : a = 0 ∧ c' = 1 ∧ L = s.length
        · rw [if_pos hfull]
          obtain ⟨e1, _, e3⟩ := hfull
          subst e1
          have : L.toNat = s.length := by omega
          simp [this]
        · rw [if_neg hfull, if_pos hc1]
      refine ⟨a, b, 1, L, _, h1, h2, hmain, ?_, fun k hk => ?_⟩
      · simp only [List.length_take, List.length_drop]
        omega
      · have hk1 := hget k hk
        refine ⟨hk1.1, hk1.2, ?_⟩
        rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop]
        congr 1
        simp only [Int.mul_one]
        omega
    · have hne : ¬ (a = 0 ∧ c' = 1 ∧ L = s.length) := fun h => hc1 h.2.1
      rw [if_neg hne, if_neg hc1] at hunf
      refine ⟨a, b, c, L, _, h1, h2, hunf, ?_, fun k hk => ?_⟩
      · simp only [List.length_map, slicePositions, List.length_range]
        omega
      · have hk1 := hget k hk
        refine ⟨hk1.1, hk1.2, ?_⟩
        have hkL : k < L.toNat := by omega
        have hs : (a + k * c).toNat < s.length := by omega
        simp only [slicePositions, List.getElem?_map, List.getElem?_range hkL, Option.map_some,
          hcc k hk, List.getElem?_eq_getElem hs, List.getD_eq_getElem?_getD, Option.getD_some]

/-! ## hex -/

theorem joinWrite_cons (sep a : Seq) (gs : List Seq) (h : gs ≠ []) :
    joinWrite sep (a :: gs) = a ++ sep ++ joinWrite sep gs := by
  cases gs with
  | nil => exact absurd rfl h
  | cons b r => rfl

theorem joinWrite_snoc (sep x : Seq) (gs : List Seq) (h : gs ≠ []) :
    joinWrite sep (gs ++ [x]) = joinWrite sep gs ++ sep ++ x := by
  induction gs with
  | nil => exact absurd rfl h
  | cons a r ih =>
    cases r with
    | nil => rfl
    | cons b r' =>
      simp only [List.cons_append]
      rw [joinWrite_cons _ _ _ (by simp), joinWrite_cons _ _ (b :: r') (by simp)]
      have := ih (by simp)
      simp only [List.cons_append] at this
      rw [this]
      simp [List.append_assoc]

/-- A separated run of hex pairs: the groups, in order, with `sep` between them. -/
def hexJoin (sep : Nat) (gs : List Seq) : Seq :=
  joinWrite [sep] (gs.map fun g => g.flatMap hexPair)

theorem chunkLeft_groups (sep abs : Nat) (ha : 0 < abs) : ∀ (k : Nat) (bs : Seq), bs ≠ [] →
    (bs.length - 1) / abs = k → ∃ gs : List Seq, gs ≠ [] ∧ bs = gs.flatten ∧
      (∀ g ∈ gs.dropLast, g.length = abs) ∧
      (∀ g, gs.getLast? = some g → 0 < g.length ∧ g.length ≤ abs) ∧
      chunkLeft sep abs k bs = hexJoin sep gs := by
  intro k
  induction k with
  | zero =>
    intro bs hb hk
    have hp : 0 < bs.length := List.length_pos_iff.mpr hb
    have hle : bs.length ≤ abs := by
      have := (Nat.div_eq_zero_iff.mp hk)
      omega
    exact ⟨[bs], by simp, by simp, by simp, by simpa using ⟨hp, hle⟩, by simp [chunkLeft, hexJoin, joinWrite]⟩
  | succ k ih =>
    intro bs hb hk
    have hp : 0 < bs.length := List.length_pos_iff.mpr hb
    have hge : abs ≤ bs.length - 1 := by
      apply Nat.le_of_not_lt
      intro h
      rw [Nat.div_eq_of_lt h] at hk
      omega
    have hd : (bs.drop abs).length = bs.length - abs := by simp
    have hne : bs.drop abs ≠ [] := by
      intro h
      rw [h] at hd
      simp at hd
      omega
    have hk' : ((bs.drop abs).length - 1) / abs = k := by
      rw [hd]
      have h1 := Nat.div_eq_sub_div ha hge
      rw [hk] at h1
      have h2 : bs.length - abs - 1 = bs.length - 1 - abs := by omega
      rw [h2]
      omega
    obtain ⟨gs, g0, g1, g2, g3, g4⟩ := ih _ hne hk'
    refine ⟨bs.take abs :: gs, by simp, ?_, ?_, ?_, ?_⟩
    · simp only [List.flatten_cons, ← g1, List.take_append_drop]
    · rw [List.dropLast_cons_of_ne_nil g0]
      intro g hg
      rcases List.mem_cons.1 hg with rfl | hg
      · simp; omega
      · exact g2 g hg
    · intro g hg
      rw [List.getLast?_cons_of_ne_nil g0] at hg
      exact g3 g hg
    · have hm : gs.map (fun g => g.flatMap hexPair) ≠ [] := by simpa using g0
      simp only [chunkLeft, hexJoin, List.map_cons]
      rw [joinWrite_cons _ _ _ hm, g4, hexJoin]

theorem chunkRight_groups (sep abs : Nat) (ha : 0 < abs) : ∀ (k : Nat) (bs : Seq), bs ≠ [] →
    (bs.length - 1) / abs = k → ∃ gs : List Seq, gs ≠ [] ∧ bs = gs.flatten ∧
      (∀ g ∈ gs.tail, g.length = abs) ∧
      (∀ g, gs.head? = some g → 0 < g.length ∧ g.length ≤ abs) ∧
      chunkRight sep abs k bs = hexJoin sep gs := by
  intro k
  induction k with
  | zero =>
    intro bs hb hk
    have hp : 0 < bs.length := List.length_pos_iff.mpr hb
    have hle : bs.length ≤ abs := by
      have := (Nat.div_eq_zero_iff.mp hk)
      omega
    exact ⟨[bs], by simp, by simp, by simp, by simpa using ⟨hp, hle⟩, by simp [chunkRight, hexJoin, joinWrite]⟩
  | succ k ih =>
    intro bs hb hk
    have hp : 0 < bs.length := List.length_pos_iff.mpr hb
    have hge : abs ≤ bs.length - 1 := by
      apply Nat.le_of_not_lt
      intro h
      rw [Nat.div_eq_of_lt h] at hk
      omega
    have hd : (bs.take (bs.length - abs)).length = bs.length - abs := by
      simp only [List.length_take]; omega
    have hne : bs.take (bs.length - abs) ≠ [] := by
      intro h
      rw [h] at hd
      simp at hd
      omega
    have hk' : ((bs.take (bs.length - abs)).length - 1) / abs = k := by
      rw [hd]
      have h1 := Nat.div_eq_sub_div ha hge
      rw [hk] at h1
      have h2 : bs.length - abs - 1 = bs.length - 1 - abs := by omega
      rw [h2]
      omega
    obtain ⟨gs, g0, g1, g2, g3, g4⟩ := ih _ hne hk'
    refine ⟨gs ++ [bs.drop (bs.length - abs)], by simp, ?_, ?_, ?_, ?_⟩
    · simp only [List.flatten_append, ← g1, List.flatten_cons, List.flatten_nil, List.append_nil,
        List.take_append_drop]
    · cases gs with
      | nil => exact absurd rfl g0
      | cons g r =>
        intro h hm
        simp only [List.cons_append, List.tail_cons, List.mem_append, List.mem_singleton] at hm
        rcases hm with hm | rfl
        · exact g2 h (by simpa using hm)
        · simp only [List.length_drop]; omega
    · cases gs with
      | nil => exact absurd rfl g0
      | cons g r =>
        intro h hm
        exact g3 h (by simpa using hm)
    · have hm : gs.map (fun g => g.flatMap hexPair) ≠ [] := by simpa using g0
      simp only [chunkRight, hexJoin, List.map_append, List.map_cons, List.map_nil]
      rw [joinWrite_snoc _ _ _ hm, g4, hexJoin]

end PyLean.BytesObj.Bytes
