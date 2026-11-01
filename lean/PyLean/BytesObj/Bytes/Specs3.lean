import PyLean.BytesObj.Bytes.Specs2

/-!
`hex`, `fromhex`, `repr`, concatenation and `join`, stated without their code.
-/

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

/-! ## `hex` with a separator -/

theorem tdiv_ssizeMax : Int.tdiv ssizeMax 2 = 4611686018427387903 := by decide

theorem strhex_eval (s : Seq) (c : Nat) (n : Int) (o : Obj) (ho : o = .str [c] ∨ o = .bytes [c])
    (hc : c < 128) (hlen : (s.length : Int) * 2 + 1 < 2 ^ 62) :
    strhexImpl s (some o) n false =
      if (n.natAbs : Int) ≥ s.length ∨ n = 0 then .ok (s.flatMap hexPair)
      else if n < 0 then .ok (chunkLeft c n.natAbs ((s.length - 1) / n.natAbs) s)
      else .ok (chunkRight c n.natAbs ((s.length - 1) / n.natAbs) s) := by
  have hc1 : ¬ c ≥ 256 := by omega
  have hc2 : ¬ c > 127 := by omega
  have hres : ¬ ((s.length : Int) ≥ Int.tdiv ssizeMax 2 -
      (if n ≠ 0 ∧ (s.length : Int) > 0 then Int.tdiv ((s.length : Int) - 1) (n.natAbs : Int) else 0)) := by
    rw [tdiv_ssizeMax]
    split
    · rename_i h
      have h0 : (0 : Int) ≤ (s.length : Int) - 1 := by omega
      rw [Int.tdiv_eq_ediv_of_nonneg h0]
      have h1 := Int.ediv_le_self (n.natAbs : Int) h0
      omega
    · omega
  have hhead : strhexImpl s (some o) n false =
      (let group : Int := n
       let abs : Nat := group.natAbs
       let arglen : Int := s.length
       let resultlen : Int := if group ≠ 0 ∧ arglen > 0 then Int.tdiv (arglen - 1) abs else 0
       if arglen ≥ Int.tdiv ssizeMax 2 - resultlen then .error memoryError
       else
         let group := if (abs : Int) ≥ arglen then 0 else group
         let abs := if (group = 0) then 0 else abs
         if group = 0 then .ok (s.flatMap hexPair)
         else
           let chunks := (s.length - 1) / abs
           if group < 0 then .ok (chunkLeft c abs chunks s) else .ok (chunkRight c abs chunks s)) := by
    rcases ho with rfl | rfl
    · simp only [strhexImpl, objLength, bind, Except.bind, pure, Except.pure, List.length_cons,
        List.length_nil, List.headD_cons, hc1, hc2, ne_eq, Nat.zero_add, not_true_eq_false, ↓reduceIte,
        false_and, Option.isSome_some, Bool.true_eq_false, Option.getD_some, throw, throwThe,
        MonadExcept.throw]
      split <;> rfl
    · simp only [strhexImpl, objLength, bind, Except.bind, pure, Except.pure, List.length_cons,
        List.length_nil, List.headD_cons, hc1, hc2, ne_eq, Nat.zero_add, not_true_eq_false, ↓reduceIte,
        false_and, Option.isSome_some, Bool.true_eq_false, Option.getD_some, throw, throwThe,
        MonadExcept.throw]
      split <;> rfl
  rw [hhead]
  dsimp only
  rw [if_neg hres]
  by_cases hz : (n.natAbs : Int) ≥ s.length ∨ n = 0
  · have h1 : (if (n.natAbs : Int) ≥ (s.length : Int) then 0 else n) = 0 := by
      split
      · rfl
      · omega
    rw [if_pos hz, h1, if_pos rfl]
  · have hge : ¬ (n.natAbs : Int) ≥ s.length := fun h => hz (Or.inl h)
    have hn0 : ¬ n = 0 := fun h => hz (Or.inr h)
    rw [if_neg hz, if_neg hge, if_neg hn0, if_neg hn0]

/-- `b.hex(sep, n)`: without a group (or with `|n|` at least the length) all hex pairs; with
`n < 0` the bytes in groups of `|n|` from the left, the last one short; with `n > 0` the same from the
right, the first one short; `sep` stands between groups and nowhere else. Hypotheses: `sep` is one
ASCII character, `n` fits the C `int` (the other cases are `OverflowError` and `ValueError`, and
`bytesHex` mirrors them), and the output fits, that is `3 * len(b) < sys.maxsize / 2`. -/
def HexGroups : Prop :=
  ∀ (s : Seq) (c : Nat) (n : Int) (o : Obj), (o = .str [c] ∨ o = .bytes [c]) → c < 128 →
    -2147483648 ≤ n → n ≤ 2147483647 → (s.length : Int) * 2 + 1 < 2 ^ 62 →
    ∃ r, bytesHex s (some o) n = .ok r ∧
      (((n.natAbs : Int) ≥ s.length ∨ n = 0) → r = s.flatMap hexPair) ∧
      (n < 0 → (n.natAbs : Int) < s.length → ∃ gs : List Seq, s = gs.flatten ∧
        (∀ g ∈ gs.dropLast, g.length = n.natAbs) ∧
        (∀ g, gs.getLast? = some g → 0 < g.length ∧ g.length ≤ n.natAbs) ∧ r = hexJoin c gs) ∧
      (0 < n → (n.natAbs : Int) < s.length → ∃ gs : List Seq, s = gs.flatten ∧
        (∀ g ∈ gs.tail, g.length = n.natAbs) ∧
        (∀ g, gs.head? = some g → 0 < g.length ∧ g.length ≤ n.natAbs) ∧ r = hexJoin c gs)

theorem hexGroups_proven : HexGroups := by
  intro s c n o ho hc h1 h2 hlen
  have hnot : ¬ (n < -2147483648 ∨ n > 2147483647) := by omega
  have he : bytesHex s (some o) n = strhexImpl s (some o) n false := by
    simp only [bytesHex]
    rw [if_neg hnot]
  rw [he, strhex_eval s c n o ho hc hlen]
  by_cases hz : (n.natAbs : Int) ≥ s.length ∨ n = 0
  · rw [if_pos hz]
    refine ⟨_, rfl, fun _ => rfl, fun h3 h4 => ?_, fun h3 h4 => ?_⟩ <;> omega
  · rw [if_neg hz]
    have hne : s ≠ [] := by
      intro h
      subst h
      simp only [List.length_nil] at hz
      omega
    have hpos : 0 < n.natAbs := by omega
    by_cases hs : n < 0
    · rw [if_pos hs]
      obtain ⟨gs, _, g1, g2, g3, g4⟩ := chunkLeft_groups c n.natAbs hpos _ s hne rfl
      exact ⟨_, rfl, fun h => absurd h hz, fun _ _ => ⟨gs, g1, g2, g3, g4⟩, fun h => by omega⟩
    · rw [if_neg hs]
      obtain ⟨gs, _, g1, g2, g3, g4⟩ := chunkRight_groups c n.natAbs hpos _ s hne rfl
      exact ⟨_, rfl, fun h => absurd h hz, fun h => by omega, fun _ _ => ⟨gs, g1, g2, g3, g4⟩⟩

/-! ## `fromhex` -/

/-- The grammar of `fromhex`, by position in the input: skip ASCII whitespace, otherwise two digits
make a byte; the first offending position is reported, and a digit with nothing after it is the odd
count. No pointers, no terminator. -/
def hexSpec : Nat → Seq → Py Seq
  | _, [] => .ok []
  | i, [c] =>
    if isSpaceC c then .ok []
    else if digitValue c ≥ 16 then .error (invalidAt i)
    else .error oddDigits
  | i, c :: d :: r =>
    if isSpaceC c then hexSpec (i + 1) (d :: r)
    else if digitValue c ≥ 16 then .error (invalidAt i)
    else if digitValue d ≥ 16 then .error (invalidAt (i + 1))
    else (hexSpec (i + 2) r).map fun t => (digitValue c * 16 + digitValue d) :: t

theorem hexSpec_space (i c : Nat) (t : Seq) (h : isSpaceC c = true) :
    hexSpec i (c :: t) = hexSpec (i + 1) t := by
  cases t with
  | nil => simp [hexSpec, h]
  | cons d r => simp [hexSpec, h]

theorem read_cons {mem : Seq} {j x : Nat} {tl : Seq} (h : mem.drop j = x :: tl) :
    memRead mem j = .ok x := by
  have h2 : mem[j]? = some x := by
    have := congrArg (fun l => l[0]?) h
    simpa using this
  simp [memRead, h2]

theorem drop_next {mem : Seq} {j x : Nat} {tl : Seq} (h : mem.drop j = x :: tl) :
    mem.drop (j + 1) = tl := by
  have := congrArg (fun l => l.drop 1) h
  simpa [List.drop_drop, Nat.add_comm] using this

theorem skip_spec (mem : Seq) : ∀ (t : Seq) (i fuel : Nat), mem.drop (i + 1) = t ++ [0] →
    t.length < fuel → ∃ k, k ≤ t.length ∧ skipSpaces mem fuel i = .ok (i + 1 + k) ∧
      hexSpec (i + 1) t = hexSpec (i + 1 + k) (t.drop k) ∧
      (∀ c, (t.drop k).head? = some c → isSpaceC c = false) := by
  intro t
  induction t with
  | nil =>
    intro i fuel hm hf
    cases fuel with
    | zero => omega
    | succ f =>
      have hr := read_cons (by simpa using hm : mem.drop (i + 1) = 0 :: [])
      refine ⟨0, by simp, ?_, rfl, by simp⟩
      have h0 : isSpaceC 0 = false := rfl
      simp only [skipSpaces, hr, h0, Bool.false_eq_true, ↓reduceIte]
  | cons d t' ih =>
    intro i fuel hm hf
    cases fuel with
    | zero => simp at hf
    | succ f =>
      have hm' : mem.drop (i + 1) = d :: (t' ++ [0]) := by simpa using hm
      have hr := read_cons hm'
      cases hd : isSpaceC d with
      | false =>
        refine ⟨0, by simp, ?_, rfl, ?_⟩
        · simp only [skipSpaces, hr, hd, Bool.false_eq_true, ↓reduceIte]
        · intro c hc
          simp only [List.drop_zero, List.head?_cons, Option.some.injEq] at hc
          subst hc
          exact hd
      | true =>
        obtain ⟨k, k1, k2, k3, k4⟩ := ih (i + 1) f (drop_next hm') (by simpa using hf)
        refine ⟨k + 1, by simpa using k1, ?_, ?_, ?_⟩
        · simp only [skipSpaces, hr, hd, ↓reduceIte, k2]
          congr 1
          omega
        · rw [hexSpec_space _ _ _ hd, k3]
          have e : i + 1 + 1 + k = i + 1 + (k + 1) := by omega
          rw [e]
          simp
        · simpa using k4

/-- The part of the loop of `_PyBytes_FromHex` after the whitespace, bytesobject.c:2583-2600. -/
def hexBody (mem : Seq) (len fuel j : Nat) (out : Seq) : Py Seq :=
  match memRead mem j with
  | .error e => .error e
  | .ok t =>
    let top := digitValue t
    if top ≥ 16 then .error (invalidAt j)
    else
      match memRead mem (j + 1) with
      | .error e => .error e
      | .ok b =>
        let bot := digitValue b
        if bot ≥ 16 then
          if j + 1 ≥ len then .error oddDigits else .error (invalidAt (j + 1))
        else fromHexLoop mem len fuel (j + 2) (out ++ [top * 16 + bot])

theorem loop_unfold (mem : Seq) (len f i : Nat) (out : Seq) :
    fromHexLoop mem len (f + 1) i out =
      if i < len then
        match memRead mem i with
        | .error e => .error e
        | .ok c =>
          match (if isSpaceC c then skipSpaces mem (mem.length + 1) i else .ok i : Py Nat) with
          | .error e => .error e
          | .ok j => if j ≥ len ∧ isSpaceC c then .ok out else hexBody mem len f j out
      else .ok out := rfl

theorem except_map_append (x : Py Seq) (out : Seq) (d : Nat) :
    Except.map (fun u => out ++ [d] ++ u) x = Except.map (out ++ ·) (x.map (d :: ·)) := by
  cases x <;> simp [Except.map]

theorem fromHexLoop_spec (mem : Seq) (len : Nat) : ∀ (n : Nat) (rest : Seq) (i fuel : Nat) (out : Seq),
    rest.length ≤ n → mem.drop i = rest ++ [0] → len = i + rest.length → rest.length < fuel →
    fromHexLoop mem len fuel i out = (hexSpec i rest).map (out ++ ·) := by
  intro n
  induction n with
  | zero =>
    intro rest i fuel out hn hm hl hf
    have hr : rest = [] := by simpa using hn
    subst hr
    cases fuel with
    | zero => simp at hf
    | succ f => simp [loop_unfold, hl, hexSpec, Except.map]
  | succ n ih =>
    intro rest i fuel out hn hm hl hf
    cases fuel with
    | zero => omega
    | succ f =>
    have body : ∀ (j t0 : Nat) (t1 : Seq), t0 :: t1 ≠ [] → mem.drop j = t0 :: t1 ++ [0] →
        len = j + 1 + t1.length → t1.length + 1 ≤ n + 1 → t1.length + 1 ≤ f + 1 → isSpaceC t0 = false →
        hexBody mem len f j out = (hexSpec j (t0 :: t1)).map (out ++ ·) := by
      intro j t0 t1 _ hm0 hl0 hn0 hf0 hsp
      have hm1 : mem.drop j = t0 :: (t1 ++ [0]) := by simpa using hm0
      have h0 := read_cons hm1
      have hm2 := drop_next hm1
      cases t1 with
      | nil =>
        have h1 := read_cons (by simpa using hm2 : mem.drop (j + 1) = 0 :: [])
        have hz : digitValue 0 = 37 := rfl
        have hge : j + 1 ≥ len := by simp at hl0; omega
        by_cases hd : digitValue t0 ≥ 16
        · simp [hexBody, h0, hd, hexSpec, hsp, Except.map]
        · simp [hexBody, h0, hd, h1, hz, hge, hexSpec, hsp, Except.map]
      | cons d r =>
        have hm3 : mem.drop (j + 1) = d :: (r ++ [0]) := by simpa using hm2
        have h1 := read_cons hm3
        have hm4 := drop_next hm3
        by_cases hd : digitValue t0 ≥ 16
        · simp [hexBody, h0, hd, hexSpec, hsp, Except.map]
        · by_cases he : digitValue d ≥ 16
          · have hge : ¬ j + 1 ≥ len := by simp at hl0; omega
            simp [hexBody, h0, hd, h1, he, hge, hexSpec, hsp, Except.map]
          · simp only [hexBody, h0, hd, h1, he, if_false, hexSpec, hsp, Bool.false_eq_true]
            rw [ih r (j + 2) f _ (by simp at hn0; omega) hm4 (by simp at hl0; omega)
              (by simp at hf0; omega)]
            exact except_map_append _ _ _
    cases rest with
    | nil => simp [loop_unfold, hl, hexSpec, Except.map]
    | cons c t =>
      have hm1 : mem.drop i = c :: (t ++ [0]) := by simpa using hm
      have h0 := read_cons hm1
      have hlt : i < len := by simp at hl; omega
      rw [loop_unfold, if_pos hlt, h0]
      cases hc : isSpaceC c with
      | false =>
        simp only [hc, Bool.false_eq_true, ↓reduceIte, and_false]
        exact body i c t (by simp) hm (by simp at hl; omega) hn (by simp at hf; omega) hc
      | true =>
        have hml : t.length < mem.length + 1 := by
          have h1 : (mem.drop i).length = t.length + 2 := by rw [hm]; simp
          have h2 : (mem.drop i).length ≤ mem.length := by simp
          omega
        obtain ⟨k, k1, k2, k3, k4⟩ := skip_spec mem t i (mem.length + 1) (drop_next hm1) hml
        simp only [hc, ↓reduceIte, k2, and_true]
        rw [hexSpec_space _ _ _ hc, k3]
        have hdk : mem.drop (i + 1 + k) = t.drop k ++ [0] := by
          rw [← List.drop_append_of_le_length k1, ← drop_next hm1, List.drop_drop]
        have hul : (t.drop k).length = t.length - k := by simp
        simp only [List.length_cons] at hl hn hf
        generalize t.drop k = u at hdk hul k4 ⊢
        cases u with
        | nil =>
          have hge : i + 1 + k ≥ len := by simp at hul; omega
          simp [hge, hexSpec, Except.map]
        | cons t0 t1 =>
          simp only [List.length_cons] at hul
          have hnge : ¬ i + 1 + k ≥ len := by omega
          rw [if_neg hnge]
          exact body (i + 1 + k) t0 t1 (by simp) hdk (by omega) (by omega) (by omega) (k4 t0 rfl)

/-- `bytes.fromhex` is the grammar `hexSpec` for every `bytes` and `bytearray`, embedded NUL and all,
and for every ASCII `str`; a non-ASCII `str` is refused at its first non-ASCII position. The pointer
loop's reads past the end are not visible for these arguments. -/
def FromHexSpec : Prop :=
  ∀ s : Seq, bytesFromHex (.bytes s) = hexSpec 0 s ∧ bytesFromHex (.bytearray s) = hexSpec 0 s ∧
    ((∀ c ∈ s, c < 128) → bytesFromHex (.str s) = hexSpec 0 s) ∧
    (∀ i, s.findIdx? (fun c => decide (c ≥ 128)) = some i → bytesFromHex (.str s) = .error (invalidAt i))

theorem fromHexSpec_proven : FromHexSpec := by
  intro s
  have h : fromHexRaw (s ++ [0]) s.length = hexSpec 0 s := by
    unfold fromHexRaw
    rw [fromHexLoop_spec _ _ s.length s 0 _ _ (Nat.le_refl _) (by simp) (by simp) (by omega)]
    cases hexSpec 0 s <;> simp [Except.map]
  refine ⟨h, h, fun ha => ?_, fun i hi => ?_⟩
  · have hn : s.findIdx? (fun c => decide (c ≥ 128)) = none := by
      rw [List.findIdx?_eq_none_iff]
      intro c hc
      have := ha c hc
      simp
      omega
    simp only [bytesFromHex, hn, h]
  · simp only [bytesFromHex, hi]

/-! ## `repr` -/

theorem reprScan_ok : ∀ (s : Seq) (n sq dq : Int), n + 4 * s.length ≤ ssizeMax →
    ∃ n', n' ≤ n + 4 * s.length ∧ reprScan s n sq dq = .ok (n', sq + s.count 39, dq + s.count 34) := by
  intro s
  induction s with
  | nil =>
    intro n sq dq _
    exact ⟨n, by simp, by simp [reprScan]⟩
  | cons c rest ih =>
    intro n sq dq h
    have hl : ((c :: rest).length : Int) = rest.length + 1 := by simp
    rw [hl] at h ⊢
    have ht : ∃ incr : Int, (if c = 39 then ((1 : Int), sq + 1, dq) else if c = 34 then (1, sq, dq + 1)
        else if c = 92 ∨ c = 9 ∨ c = 10 ∨ c = 13 then (2, sq, dq)
        else if c < 32 ∨ c ≥ 127 then (4, sq, dq) else (1, sq, dq)) =
        (incr, sq + (if c = 39 then 1 else 0), dq + (if c = 34 then 1 else 0)) ∧ 1 ≤ incr ∧ incr ≤ 4 := by
      by_cases h1 : c = 39
      · subst h1
        exact ⟨1, by simp, by omega, by omega⟩
      by_cases h2 : c = 34
      · subst h2
        exact ⟨1, by simp, by omega, by omega⟩
      by_cases h3 : c = 92 ∨ c = 9 ∨ c = 10 ∨ c = 13
      · exact ⟨2, by rw [if_neg h1, if_neg h2, if_pos h3]; simp [h1, h2], by omega, by omega⟩
      by_cases h4 : c < 32 ∨ c ≥ 127
      · exact ⟨4, by rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4]; simp [h1, h2], by omega, by omega⟩
      · exact ⟨1, by rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4]; simp [h1, h2], by omega, by omega⟩
    obtain ⟨incr, h1, h2, h3⟩ := ht
    simp only [reprScan, h1]
    unfold ssizeMax at h ih ⊢
    rw [if_neg (by omega)]
    obtain ⟨n', a1, a2⟩ := ih (n + incr) (sq + (if c = 39 then 1 else 0))
      (dq + (if c = 34 then 1 else 0)) (by omega)
    refine ⟨n', by omega, ?_⟩
    have e1 : (List.count 39 (c :: rest) : Int) = List.count 39 rest + (if c = 39 then 1 else 0) := by
      by_cases h5 : c = 39
      · subst h5
        simp
      · simp [List.count_cons, h5]
    have e2 : (List.count 34 (c :: rest) : Int) = List.count 34 rest + (if c = 34 then 1 else 0) := by
      by_cases h5 : c = 34
      · subst h5
        simp
      · simp [List.count_cons, h5]
    rw [a2, e1, e2]
    simp only [Except.ok.injEq, Prod.mk.injEq, true_and]
    constructor <;> omega

theorem hexDigit_print (d : Nat) (h : d < 16) : 32 ≤ hexDigit d ∧ hexDigit d < 127 := by
  unfold hexDigit
  split <;> omega

theorem reprByte_print (q c : Nat) (hq : q = 39 ∨ q = 34) (hc : c < 256) :
    ∀ x ∈ reprByte q c, 32 ≤ x ∧ x < 127 := by
  intro x hx
  have h1 := hexDigit_print (c / 16) (by omega)
  have h2 := hexDigit_print (c % 16) (by omega)
  simp only [reprByte] at hx
  repeat' (split at hx)
  all_goals
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    omega

/-- `repr(b)`: the quote is `"` only in smart mode for a body with `'` and no `"`; the text is
printable ASCII; printable bytes other than the quote and the backslash stand for themselves, and
the quote appears only escaped. With `ReprDecodeRoundTrip`, which undoes the body, this pins `repr`
up to the choice of escape. Hypotheses: bytes, and `repr` fits. -/
def ReprSpec : Prop :=
  ∀ (s : Seq) (smart : Bool), (∀ c ∈ s, c < 256) → (s.length : Int) * 5 + 3 ≤ ssizeMax →
    let q : Nat := if smart = true ∧ 39 ∈ s ∧ 34 ∉ s then 34 else 39
    bytesRepr s smart = .ok ([98, q] ++ reprBody q s ++ [q]) ∧
    (∀ x ∈ reprBody q s, 32 ≤ x ∧ x < 127) ∧
    (∀ c ∈ s, 32 ≤ c → c < 127 → c ≠ q → c ≠ 92 → reprByte q c = [c]) ∧
    (reprByte q q = [92, q])

theorem reprSpec_proven : ReprSpec := by
  intro s smart hs hl
  dsimp only
  have hqq : (if smart = true ∧ 39 ∈ s ∧ 34 ∉ s then 34 else 39) = 39 ∨
      (if smart = true ∧ 39 ∈ s ∧ 34 ∉ s then 34 else 39) = 34 := by
    split
    · exact Or.inr rfl
    · exact Or.inl rfl
  obtain ⟨n', h1, h2⟩ := reprScan_ok s 3 0 0 (by omega)
  have hsq : (((0 : Int) + (s.count 39 : Nat)) ≠ 0) ↔ 39 ∈ s := by
    rw [← List.count_pos_iff]
    omega
  have hdq : (((0 : Int) + (s.count 34 : Nat)) = 0) ↔ 34 ∉ s := by
    rw [← List.count_pos_iff]
    omega
  have hcl : (s.count 39 : Int) ≤ s.length := by exact_mod_cast List.count_le_length
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hno : ¬ (n' > ssizeMax - ((0 : Int) + (s.count 39 : Nat))) := by
      unfold ssizeMax at hl ⊢
      omega
    simp only [bytesRepr, bind, Except.bind, h2, pure, Except.pure, hsq, hdq, hno, ↓reduceIte, ite_self]
  · intro x hx
    simp only [reprBody, List.mem_flatMap] at hx
    obtain ⟨c, hc, hxc⟩ := hx
    exact reprByte_print _ c hqq (hs c hc) x hxc
  · intro c _ h1 h2 h3 h4
    simp only [reprByte]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  · simp [reprByte]

/-! ## strip, by method -/

/-- `StripSpec` for `bytes.strip`, `lstrip` and `rstrip`: `None` is the whitespace of `do_strip`, a
set is the membership of `do_xstrip`. -/
def BytesStripSpec : Prop :=
  ∀ (s : Seq) (chars : Option Seq) (t : StripType),
    let mem : Nat → Bool := match chars with
      | none => byteSpace
      | some cs => fun c => cs.contains c
    let r := bytesStrip s chars t
    ∃ pre post, s = pre ++ r ++ post ∧ (∀ c ∈ pre, mem c = true) ∧ (∀ c ∈ post, mem c = true) ∧
      (t = .right → pre = []) ∧ (t = .left → post = []) ∧
      (t ≠ .right → ∀ c, r.head? = some c → mem c = false) ∧
      (t ≠ .left → ∀ c, r.getLast? = some c → mem c = false)

theorem bytesStripSpec_proven : BytesStripSpec := by
  intro s chars t
  cases chars with
  | none => exact stripSpec_proven _ t s
  | some cs => exact stripSpec_proven _ t s

/-! ## Concatenation, `join`, `removesuffix` -/

/-- `b + c` for bytes, on both paths of `PyBytes_Concat`: the unique-object in-place resize and the
general one give the concatenation. Hypothesis: `malloc` succeeds. -/
def ConcatValue : Prop :=
  ∀ (v w : Seq) (u : Bool), (v.length : Int) + w.length + 33 < 2 ^ 47 →
    pyBytesConcat (some v) (some (.bytes w)) u = (some (v ++ w), none)

theorem concatValue_proven : ConcatValue := by
  intro v w u hsz
  have h1 := concatSpec_proven.1 v w hsz
  have h2 : pyBytesConcat (some v) (some (.bytes w)) false = (some (v ++ w), none) := by
    simp [pyBytesConcat, h1]
  cases u with
  | false => exact h2
  | true =>
    rw [concatSpec_proven.2.2 v (.bytes w) (by simpa [Obj.buffer?] using hsz)]
    exact h2

/-- `sep.join(xs)` writes the items with `sep` between them and nowhere else. -/
def JoinIntercalate : Prop :=
  ∀ (sep : Seq) (xs : List Seq), joinWrite sep xs = sep.intercalate xs

theorem joinIntercalate_proven : JoinIntercalate := by
  intro sep xs
  induction xs with
  | nil => rfl
  | cons a r ih =>
    cases r with
    | nil => simp [joinWrite, List.intercalate]
    | cons b r' =>
      rw [joinWrite_cons _ _ _ (by simp), ih]
      simp [List.intercalate, List.intersperse_cons_cons, List.append_assoc]

/-- A suffix that does not match leaves the bytes alone, the half of `removesuffix` that `RemoveAffix`
leaves out. -/
def RemoveSuffixMiss : Prop :=
  ∀ s p : Seq, p.isSuffixOf s = false → bytesRemovesuffix s p = s

theorem removeSuffixMiss_proven : RemoveSuffixMiss := by
  intro s p h
  unfold bytesRemovesuffix
  rw [if_neg]
  rintro ⟨h1, _, h3⟩
  have h4 : p.isSuffixOf s = true := by
    rw [List.isSuffixOf_iff_suffix, List.suffix_iff_eq_drop]
    have h5 := (isPrefixOf_eq_true_iff.1 h3).2
    rw [List.take_of_length_le (by simp; omega)] at h5
    exact h5.symm
  simp [h4] at h

end PyLean.BytesObj.Bytes
