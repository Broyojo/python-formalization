import PyLean.TextLibs.UrlBrackets

/-!
The `str` and `bytes` twins of `urllib.parse`: the netloc attributes of the `str` and `bytes`
result classes, and `urlsplit` on ASCII `bytes` against `urlsplit` on the decoded `str`.
And the NFKC check of `_checknetloc`.
-/

namespace PyLean.TextLibs.Url

open PyLean

set_option linter.unusedSimpArgs false

/-! ## Membership in the parts of `partition` -/

theorem mem_part_fst {c x : Nat} {l : Str} (h : x ∈ (part c l).1) : x ∈ l := by
  rw [← part_rebuild c l]; exact List.mem_append_left _ h

theorem mem_part_snd {c x : Nat} {l y : Str} (hy : (part c l).2 = some y) (h : x ∈ y) : x ∈ l := by
  rw [← part_rebuild c l, hy]; simp [opt, h]

theorem mem_rpart_snd {c x : Nat} {l : Str} (h : x ∈ (rpart c l).2) : x ∈ l := by
  unfold rpart at h
  rcases hp : part c l.reverse with ⟨a, _ | b⟩
  · rw [hp] at h; simp at h
    exact List.mem_reverse.1 (mem_part_fst (c := c) (by rw [hp]; exact h))
  · rw [hp] at h; simp at h
    exact List.mem_reverse.1 (mem_part_fst (c := c) (by rw [hp]; exact h))

theorem hostinfo_sub (n : Str) : ∀ x ∈ ((hostinfoS (some n)).1.getD []), x ∈ n := by
  intro x hx
  unfold hostinfoS at hx
  simp only at hx
  have hsub : ∀ y, y ∈ (rpart 64 n).2 → y ∈ n := fun y hy => mem_rpart_snd hy
  generalize (rpart 64 n).2 = hp at hx hsub
  rcases hb : part 91 hp with ⟨before, _ | br⟩
  · simp only [hb] at hx
    exact hsub x (mem_part_fst (c := 58) hx)
  · simp only [hb, Option.getD_some] at hx
    exact hsub x (mem_part_snd (c := 91) (by rw [hb]) (mem_part_fst (c := 93) hx))

/-! ## The `bytes` mixin against the `str` mixin -/

theorem toNat_toUInt8 (a : Nat) (h : a < 256) : (Nat.toUInt8 a).toNat = a := by
  simp [Nat.toUInt8]; omega

theorem toUInt8_inj (a b : Nat) (ha : a < 256) (hb : b < 256) : Nat.toUInt8 a = Nat.toUInt8 b ↔ a = b := by
  constructor
  · intro e
    have := congrArg UInt8.toNat e
    rwa [toNat_toUInt8 a ha, toNat_toUInt8 b hb] at this
  · intro e; rw [e]

/-- All code points below 256: the type invariant of a `bytes` value. -/
def Lt256 (s : Str) : Prop := ∀ c ∈ s, c < 256

theorem ofB8_toB8 (s : Str) (hs : Lt256 s) : ofB8 (toB8 s) = s := by
  induction s with
  | nil => rfl
  | cons c r ih =>
    simp only [toB8, ofB8, List.map_cons, List.map_map] at ih ⊢
    rw [toNat_toUInt8 c (hs c List.mem_cons_self), ih (fun x hx => hs x (List.mem_cons_of_mem _ hx))]

theorem bpart_toB8 (c : Nat) (hc : c < 256) : ∀ s : Str, Lt256 s →
    bpart (Nat.toUInt8 c) (toB8 s) = (toB8 (part c s).1, (part c s).2.map toB8)
  | [], _ => rfl
  | x :: r, hs => by
    have hx := hs x List.mem_cons_self
    have ih := bpart_toB8 c hc r (fun y hy => hs y (List.mem_cons_of_mem _ hy))
    simp only [toB8, List.map_cons] at ih ⊢
    rw [bpart, part_cons]
    by_cases hxc : x = c
    · subst hxc; simp [toB8]
    · have : (Nat.toUInt8 x == Nat.toUInt8 c) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        rw [toUInt8_inj x c hx hc]; exact hxc
      simp only [this, Bool.false_eq_true, ite_false, if_neg hxc, ih, List.map_cons]

theorem lt256_reverse (s : Str) (hs : Lt256 s) : Lt256 s.reverse := fun c hc => hs c (List.mem_reverse.1 hc)

theorem toB8_reverse (s : Str) : toB8 s.reverse = (toB8 s).reverse := by simp [toB8]

theorem brpart_toB8 (c : Nat) (hc : c < 256) (s : Str) (hs : Lt256 s) :
    brpart (Nat.toUInt8 c) (toB8 s) = ((rpart c s).1.map toB8, toB8 (rpart c s).2) := by
  unfold brpart rpart
  rw [← toB8_reverse, bpart_toB8 c hc _ (lt256_reverse s hs)]
  rcases part c s.reverse with ⟨a, _ | b⟩ <;> simp [toB8_reverse]

theorem lt256_part_fst (c : Nat) (s : Str) (hs : Lt256 s) : Lt256 (part c s).1 :=
  fun x hx => hs x (mem_part_fst hx)

theorem lt256_part_snd (c : Nat) (s : Str) (hs : Lt256 s) : ∀ y, (part c s).2 = some y → Lt256 y :=
  fun _ hy x hx => hs x (mem_part_snd hy hx)

theorem lt256_rpart_snd (c : Nat) (s : Str) (hs : Lt256 s) : Lt256 (rpart c s).2 :=
  fun x hx => hs x (mem_rpart_snd hx)

theorem mem_rpart_fst {c x : Nat} {l y : Str} (hy : (rpart c l).1 = some y) (h : x ∈ y) : x ∈ l := by
  unfold rpart at hy
  rcases hp : part c l.reverse with ⟨a, _ | b⟩
  · rw [hp] at hy; simp at hy
  · rw [hp] at hy
    simp only [Option.some.injEq] at hy
    subst hy
    exact List.mem_reverse.1 (mem_part_snd (c := c) (l := l.reverse) (by rw [hp]) (List.mem_reverse.1 h))

/-- The `bytes` `_userinfo` is the `str` one on the code points, byte for byte. -/
theorem userinfoB_toB8 (n : Str) (hn : Lt256 n) :
    userinfoB (some (toB8 n)) = ((userinfoS (some n)).1.map toB8, (userinfoS (some n)).2.map toB8) := by
  simp only [userinfoB, userinfoS]
  rw [show (64 : UInt8) = Nat.toUInt8 64 from rfl, brpart_toB8 64 (by omega) n hn]
  rcases hr : rpart 64 n with ⟨_ | ui, hi⟩
  · rfl
  · have hui : Lt256 ui := fun x hx => hn x (mem_rpart_fst (by rw [hr]) hx)
    simp only [Option.map_some]
    rw [show (58 : UInt8) = Nat.toUInt8 58 from rfl, bpart_toB8 58 (by omega) ui hui]

theorem hostinfoB_toB8 (n : Str) (hn : Lt256 n) :
    hostinfoB (some (toB8 n)) = ((hostinfoS (some n)).1.map toB8, (hostinfoS (some n)).2.map toB8) := by
  simp only [hostinfoB, hostinfoS]
  rw [show (64 : UInt8) = Nat.toUInt8 64 from rfl, brpart_toB8 64 (by omega) n hn]
  have hhi := lt256_rpart_snd 64 n hn
  generalize (rpart 64 n).2 = hi at hhi ⊢
  rw [show (91 : UInt8) = Nat.toUInt8 91 from rfl, bpart_toB8 91 (by omega) hi hhi]
  rcases hb : part 91 hi with ⟨before, _ | br⟩
  · simp only [Option.map_none]
    rw [show (58 : UInt8) = Nat.toUInt8 58 from rfl, bpart_toB8 58 (by omega) hi hhi]
    rcases part 58 hi with ⟨h, _ | p⟩
    · simp [toB8]
    · cases p <;> simp [toB8]
  · have hbr : Lt256 br := lt256_part_snd 91 hi hhi br (by rw [hb])
    simp only [Option.map_some]
    rw [show (93 : UInt8) = Nat.toUInt8 93 from rfl, bpart_toB8 93 (by omega) br hbr]
    rcases hq : part 93 br with ⟨h, _ | q⟩
    · simp [toB8, bpart, part]
    · have hq' : Lt256 q := lt256_part_snd 93 br hbr q (by rw [hq])
      simp only [Option.map_some, Option.getD_some]
      rw [show (58 : UInt8) = Nat.toUInt8 58 from rfl, bpart_toB8 58 (by omega) q hq']
      rcases part 58 q with ⟨w, _ | p⟩
      · simp [toB8]
      · cases p <;> simp [toB8]

theorem ofB8_toB8_opt (o : Option Str) (h : ∀ s, o = some s → Lt256 s) : (o.map toB8).map ofB8 = o := by
  cases o with
  | none => rfl
  | some s => simp [ofB8_toB8 s (h s rfl)]

theorem userinfoS_sub (n : Str) :
    (∀ s, (userinfoS (some n)).1 = some s → ∀ x ∈ s, x ∈ n) ∧
    (∀ s, (userinfoS (some n)).2 = some s → ∀ x ∈ s, x ∈ n) := by
  simp only [userinfoS]
  rcases hr : rpart 64 n with ⟨_ | ui, hi⟩
  · simp
  · have hsub : ∀ x ∈ ui, x ∈ n := fun x hx => mem_rpart_fst (by rw [hr]) hx
    simp only
    constructor
    · intro s hs x hx
      simp only [Option.some.injEq] at hs
      subst hs
      exact hsub x (mem_part_fst hx)
    · intro s hs x hx
      exact hsub x (mem_part_snd hs hx)

theorem hostinfoS_snd_sub (n : Str) : ∀ s, (hostinfoS (some n)).2 = some s → ∀ x ∈ s, x ∈ n := by
  intro s hs x hx
  simp only [hostinfoS] at hs
  have hsub : ∀ y, y ∈ (rpart 64 n).2 → y ∈ n := fun y hy => mem_rpart_snd hy
  generalize (rpart 64 n).2 = hp at hs hsub
  rcases hb : part 91 hp with ⟨before, _ | br⟩
  · simp only [hb] at hs
    split at hs
    · cases hs
    · cases hs
      rcases hq : (part 58 hp).2 with _ | q
      · simp [hq] at hx
      · simp [hq] at hx; exact hsub x (mem_part_snd hq hx)
  · simp only [hb, Option.getD_some] at hs
    split at hs
    · cases hs
    · cases hs
      have hbr : ∀ y ∈ br, y ∈ hp := fun y hy => mem_part_snd (c := 91) (by rw [hb]) hy
      rcases hq : (part 93 br).2 with _ | q
      · simp [hq, part] at hx
      · simp only [hq, Option.getD_some] at hx
        have hqq : ∀ y ∈ q, y ∈ hp := fun y hy => hbr y (mem_part_snd hq hy)
        rcases hw : (part 58 q).2 with _ | w
        · simp [hw] at hx
        · simp [hw] at hx; exact hsub x (hqq x (mem_part_snd hw hx))

theorem blower_toNat (c : Nat) (h : c < 256) : (blower (Nat.toUInt8 c)).toNat = UnicodeObj.pyToLower c := by
  unfold blower
  simp only [UInt8.le_iff_toNat_le, toNat_toUInt8 c h, show (65 : UInt8).toNat = 65 from rfl,
    show (90 : UInt8).toNat = 90 from rfl, UnicodeObj.pyToLower, UnicodeObj.pyIsUpper]
  split
  · next hc => simp [UInt8.toNat_add, toNat_toUInt8 c h, hc.1, hc.2]; omega
  · next hc =>
    rw [toNat_toUInt8 c h]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    rw [if_neg hc]

theorem ofB8_lower (a : Str) (ha : Lt256 a) : ofB8 ((toB8 a).map blower) = a.map UnicodeObj.pyToLower := by
  induction a with
  | nil => rfl
  | cons c r ih =>
    simp only [toB8, ofB8, List.map_cons, List.map_map] at ih ⊢
    rw [blower_toNat c (ha c List.mem_cons_self), ih (fun x hx => ha x (List.mem_cons_of_mem _ hx))]

/-- For every result whose netloc is a `bytes` value (every code point below 256) or `None`,
the `bytes` result classes (`_NetlocResultMixinBytes`, splitting with `bytes.rpartition(b'@')`,
`bytes.partition(b':')`, `b'['`, `b']'`) give the same `username`, `password` and `port` as the
`str` classes (`_NetlocResultMixinStr`) on the same code points, and, for an ASCII netloc, the
same `hostname` (`bytes.lower()` agreeing with `str.lower()` on ASCII). The `port` errors embed a
repr (`'x'` against `b'x'`), so both are `~` messages of the same class. Source: (a), the two
classes are twins (Lib/urllib/parse.py:212-277), and the docs ("all return values ... provide
either an encode() method ... or a decode() method"). -/
def NetlocTwin : Prop :=
  ∀ (fields : List (Option Str)) (k : Option Bool),
    (∀ n, fields.getD 1 none = some n → Lt256 n) →
    username { fields, isBytes := true, keep := k } = username { fields, isBytes := false, keep := k } ∧
    password { fields, isBytes := true, keep := k } = password { fields, isBytes := false, keep := k } ∧
    port { fields, isBytes := true, keep := k } = port { fields, isBytes := false, keep := k } ∧
    ((∀ n, fields.getD 1 none = some n → ∀ c ∈ n, c < 128) →
      hostname { fields, isBytes := true, keep := k } = hostname { fields, isBytes := false, keep := k })

theorem netlocTwin_proven : NetlocTwin := by
  intro fields k h256
  simp only [username, password, hostname, port, Res.netloc, ite_true, Bool.false_eq_true, ite_false]
  generalize hn : fields.getD 1 none = n at h256
  cases n with
  | none => exact ⟨rfl, rfl, rfl, fun _ => rfl⟩
  | some n =>
    have hn256 := h256 n rfl
    have hu := userinfoS_sub n
    simp only [Option.map_some, userinfoB_toB8 n hn256, hostinfoB_toB8 n hn256]
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact ofB8_toB8_opt _ (fun s hs x hx => hn256 x (hu.1 s hs x hx))
    · exact ofB8_toB8_opt _ (fun s hs x hx => hn256 x (hu.2 s hs x hx))
    · rw [ofB8_toB8_opt _ (fun s hs x hx => hn256 x (hostinfoS_snd_sub n s hs x hx))]
    · intro hasc
      have hasc' := hasc n rfl
      have hsub : ∀ s, (hostinfoS (some n)).1 = some s → ∀ x ∈ s, x ∈ n := by
        intro s hs x hx
        apply hostinfo_sub n x
        rw [hs]; exact hx
      generalize (hostinfoS (some n)).1 = h at hsub ⊢
      cases h with
      | none => rfl
      | some h =>
        have hh256 : Lt256 h := fun x hx => hn256 x (hsub h rfl x hx)
        simp only [Option.map_some]
        have he : (toB8 h).isEmpty = h.isEmpty := by simp [toB8]
        rw [he]
        split
        · rfl
        · rw [show (37 : UInt8) = Nat.toUInt8 37 from rfl, bpart_toB8 37 (by omega) h hh256]
          have ha : UnicodeObj.isAscii (part 37 h).1 = true := by
            simp only [UnicodeObj.isAscii, List.all_eq_true, decide_eq_true_eq]
            intro c hc
            exact hasc' c (hsub h rfl c (mem_part_fst hc))
          have hlow : UnicodeObj.unicodeLower (part 37 h).1 = .ok ((part 37 h).1.map UnicodeObj.pyToLower) := by
            simp [UnicodeObj.unicodeLower, ha, UnicodeObj.asciiUpperOrLower]
          rw [hlow]
          have hz : ∀ z, (part 37 h).2 = some z → Lt256 z := lt256_part_snd 37 h hh256
          have h1 := ofB8_lower _ (lt256_part_fst 37 h hh256)
          unfold ofB8 at h1
          rcases hzz : (part 37 h).2 with _ | z
          · simp [Except.map, ofB8, h1]
          · have h2 := ofB8_toB8 z (hz z hzz)
            unfold ofB8 at h2
            simp only [Except.map, ofB8, List.map_append, List.map_cons, Option.map_some, h1, h2]
            rfl

/-! ## `urlsplit` on `bytes` -/

theorem decodeArgs_ascii (x : Str) (hx : ∀ c ∈ x, c < 128) :
    coerceArgs [.bytes x false, .none] = .ok ([some (.s x), none], true) := by
  cases x with
  | nil => rfl
  | cons c r =>
    have hd : decodeArg (.bytes (c :: r) false) = .ok (some (.s (c :: r))) := by
      simp [decodeArg, Arg.truthy, asciiDecode_ascii _ _ hx, Except.map]
    have hn : decodeArg .none = .ok none := rfl
    simp [coerceArgs, mixLoop, firstNotNone, Arg.truthy, Arg.isStr, decodeArgs, hd, hn, bind,
      Except.bind, pure, Except.pure]

def AsciiFields (fs : List (Option Str)) : Prop := ∀ f ∈ fs, ∀ s, f = some s → ∀ c ∈ s, c < 128

theorem mapM_encField_ascii (fs : List (Option Str)) (h : AsciiFields fs) :
    fs.mapM (encField .ascii .strict) = .ok fs := by
  induction fs with
  | nil => rfl
  | cons f r ih =>
    have ih' := ih (fun g hg => h g (List.mem_cons_of_mem _ hg))
    have hf : encField .ascii .strict f = .ok f := by
      cases f with
      | none => rfl
      | some s =>
        simp [encField, encodeWith, ucs1Encode_below s 128 .strict noNames (h (some s) List.mem_cons_self s rfl),
          Except.map]
    simp [List.mapM_cons, hf, ih', bind, Except.bind, pure, Except.pure]

theorem mapM_decField_ascii (fs : List (Option Str)) (h : AsciiFields fs) :
    fs.mapM (decField .ascii .strict) = .ok fs := by
  induction fs with
  | nil => rfl
  | cons f r ih =>
    have ih' := ih (fun g hg => h g (List.mem_cons_of_mem _ hg))
    have hf : decField .ascii .strict f = .ok f := by
      cases f with
      | none => rfl
      | some s =>
        simp [decField, decodeWith, asciiDecode_ascii s .strict (h (some s) List.mem_cons_self s rfl),
          Except.map]
    simp [List.mapM_cons, hf, ih', bind, Except.bind, pure, Except.pure]

theorem ascii_sub_filter (u : Str) (hu : ∀ c ∈ u, c < 128) : ∀ c ∈ removeUnsafe (lstripC0 u), c < 128 := by
  intro c hc
  simp only [removeUnsafe, List.mem_filter] at hc
  exact hu c ((List.dropWhile_suffix _).subset hc.1.1.1)

theorem pyToLower_lt (d : Nat) (h : d < 128) : UnicodeObj.pyToLower d < 128 := by
  unfold UnicodeObj.pyToLower
  split
  · next hu => unfold UnicodeObj.pyIsUpper at hu; simp at hu; omega
  · exact h

/-- Every field of `splitPure` of an ASCII URL is ASCII. -/
theorem splitPure_ascii (u : Str) (frag : Bool) (hu : ∀ c ∈ u, c < 128) :
    ∀ f ∈ [(splitPure u frag).1, (splitPure u frag).2.1, some (splitPure u frag).2.2.1,
      (splitPure u frag).2.2.2.1, (splitPure u frag).2.2.2.2], ∀ s, f = some s → ∀ c ∈ s, c < 128 := by
  have h0 := ascii_sub_filter u hu
  unfold splitPure restOf fragStage queryStage
  generalize removeUnsafe (lstripC0 u) = cl at h0
  have hsch : ∀ s, (schemeOf cl).1 = some s → ∀ c ∈ s, c < 128 := by
    intro s hs c hc
    unfold schemeOf at hs
    rcases hf : cl.findIdx? (· == 58) with _ | i
    · simp only [hf] at hs; cases hs
    · simp only [hf] at hs
      by_cases hc' : (decide (i > 0) && isAsciiAlpha (cl.headD 0) && (cl.take i).all isSchemeChar) = true
      · rw [if_pos hc'] at hs
        simp only [Option.some.injEq] at hs
        subst hs
        simp only [List.mem_map] at hc
        obtain ⟨d, hd, rfl⟩ := hc
        have := h0 d (List.mem_of_mem_take hd)
        exact pyToLower_lt d this
      · rw [if_neg hc'] at hs; cases hs
  have hrest : ∀ c ∈ (schemeOf cl).2, c < 128 := by
    intro c hc
    unfold schemeOf at hc
    rcases hf : cl.findIdx? (· == 58) with _ | i
    · simp only [hf] at hc; exact h0 c hc
    · simp only [hf] at hc
      by_cases hc' : (decide (i > 0) && isAsciiAlpha (cl.headD 0) && (cl.take i).all isSchemeChar) = true
      · rw [if_pos hc'] at hc; exact h0 c (List.mem_of_mem_drop hc)
      · rw [if_neg hc'] at hc; exact h0 c hc
  generalize schemeOf cl = sr at hsch hrest
  obtain ⟨s, r⟩ := sr
  simp only at hsch hrest ⊢
  have hn : ∀ x, (netPure r).1 = some x → ∀ c ∈ x, c < 128 := by
    intro x hx c hc
    unfold netPure at hx
    split at hx
    · simp at hx; subst hx; exact hrest c (List.mem_of_mem_drop ((List.takeWhile_prefix _).subset hc))
    · cases hx
  have hnr : ∀ c ∈ (netPure r).2, c < 128 := by
    intro c hc
    unfold netPure at hc
    split at hc
    · exact hrest c (List.mem_of_mem_drop ((List.dropWhile_suffix _).subset hc))
    · exact hrest c hc
  generalize netPure r = nr at hn hnr
  obtain ⟨n, rest⟩ := nr
  simp only at hn hnr ⊢
  have hfq : ∀ (a : Str), (∀ c ∈ a, c < 128) → ∀ (d : Nat) (b : Bool),
      (∀ c ∈ (if b && a.contains d then part d a else (a, none)).1, c < 128) ∧
      ∀ y, (if b && a.contains d then part d a else (a, none)).2 = some y → ∀ c ∈ y, c < 128 := by
    intro a ha d b
    split
    · exact ⟨fun c hc => ha c (mem_part_fst hc), fun y hy c hc => ha c (mem_part_snd hy hc)⟩
    · exact ⟨ha, fun y hy => by cases hy⟩
  obtain ⟨hf1, hf2⟩ := hfq rest hnr 35 frag
  generalize (if frag && rest.contains 35 then part 35 rest else (rest, none)) = P at hf1 hf2
  obtain ⟨a, f⟩ := P
  simp only at hf1 hf2 ⊢
  obtain ⟨hq1, hq2⟩ := hfq a hf1 63 true
  simp only [Bool.true_and] at hq1 hq2 ⊢
  generalize (if a.contains 63 then part 63 a else (a, none)) = Q at hq1 hq2
  obtain ⟨p, q⟩ := Q
  simp only at hq1 hq2 ⊢
  intro g hg t ht c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact hsch t ht c hc
  · exact hn t ht c hc
  · cases ht; exact hq1 c hc
  · exact hq2 t ht c hc
  · exact hf2 t ht c hc

/-- For every ASCII `bytes` URL, `urlsplit` on it is `urlsplit` on the decoded `str` followed by
`encode('ascii')`, and `decode('ascii')` of the `bytes` result is the `str` result, for every
`allow_fragments` and `missing_as_none`. Source: (a), the `bytes` path against the `str` path, and
the docs' "Parsing ASCII Encoded Bytes" section. -/
def BytesTwin : Prop :=
  ∀ (nfkc : Str → Str) (ipk : Str → Option Bool) (x : Str) (frag mn : Bool), (∀ c ∈ x, c < 128) →
    urlsplit nfkc ipk (.bytes x false) .none frag mn =
      (urlsplit nfkc ipk (.str x) .none frag mn).bind (fun r => resEncode r .ascii .strict) ∧
    ∀ r, urlsplit nfkc ipk (.str x) .none frag mn = .ok r →
      ∃ rb, urlsplit nfkc ipk (.bytes x false) .none frag mn = .ok rb ∧ resDecode rb .ascii .strict = .ok r

/-- The five fields `urlsplit` builds. -/
def fields5 (mn : Bool) (sp : Split) : List (Option Str) :=
  [fillMissing mn sp.1, fillMissing mn sp.2.1, some sp.2.2.1, fillMissing mn sp.2.2.2.1, fillMissing mn sp.2.2.2.2]

theorem fill_ascii (mn : Bool) (sp : Split)
    (h : AsciiFields [sp.1, sp.2.1, some sp.2.2.1, sp.2.2.2.1, sp.2.2.2.2]) : AsciiFields (fields5 mn sp) := by
  have hf : ∀ g, g ∈ [sp.1, sp.2.1, some sp.2.2.1, sp.2.2.2.1, sp.2.2.2.2] →
      ∀ s, fillMissing mn g = some s → ∀ c ∈ s, c < 128 := by
    intro g hg s hs c hc
    unfold fillMissing at hs
    split at hs
    · exact h g hg s hs c hc
    · cases g with
      | none => simp at hs; subst hs; simp at hc
      | some t => simp at hs; subst hs; exact h _ hg _ rfl c hc
  intro f hf' s hs c hc
  simp only [fields5, List.mem_cons, List.not_mem_nil, or_false] at hf'
  rcases hf' with rfl | rfl | rfl | rfl | rfl
  · exact hf _ (by simp) s hs c hc
  · exact hf _ (by simp) s hs c hc
  · exact h _ (by simp) s hs c hc
  · exact hf _ (by simp) s hs c hc
  · exact hf _ (by simp) s hs c hc

theorem mkRes_ascii (isB : Bool) (fs : List (Option Str)) (k : Bool) (h : AsciiFields fs) :
    mkRes isB fs k = .ok { fields := fs, isBytes := isB, keep := some k } := by
  cases isB with
  | false => rfl
  | true =>
    simp [mkRes, resEncode, mapM_encField_ascii fs h, bind, Except.bind, pure, Except.pure]

theorem urlsplit_core_eq (nfkc : Str → Str) (ipk : Str → Option Bool) (a : Arg) (x : Str) (isB : Bool)
    (frag mn : Bool) (hc : coerceArgs [a, .none] = .ok ([some (.s x), none], isB))
    (hl : lruHash [a, .none] = .ok ()) (hx : ∀ c ∈ x, c < 128) :
    urlsplit nfkc ipk a .none frag mn =
      (urlsplitCore nfkc ipk (.s x) none frag).bind (fun sp =>
        .ok { fields := fields5 mn sp, isBytes := isB, keep := some mn }) := by
  unfold urlsplit
  simp only [hl, hc, bind, Except.bind]
  simp only [List.headD_cons, Option.getD_some, List.getD_cons_succ, List.getD_cons_zero]
  rcases hx' : urlsplitCore nfkc ipk (.s x) none frag with e | sp
  · rfl
  · have hsp := urlsplitCore_ok nfkc ipk x frag sp hx'
    subst hsp
    have hfa := fill_ascii mn _ (splitPure_ascii x frag hx)
    simp only [Except.bind]
    exact mkRes_ascii isB _ mn hfa

theorem bytesTwin_proven : BytesTwin := by
  intro nfkc ipk x frag mn hx
  have hcb := decodeArgs_ascii x hx
  have hcs : coerceArgs [.str x, .none] = .ok ([some (.s x), none], false) :=
    coerceArgs_str [some x, none] ⟨x, by simp⟩
  have eb := urlsplit_core_eq nfkc ipk (.bytes x false) x true frag mn hcb rfl hx
  have es := urlsplit_core_eq nfkc ipk (.str x) x false frag mn hcs rfl hx
  rw [eb, es]
  rcases hx' : urlsplitCore nfkc ipk (.s x) none frag with e | sp
  · exact ⟨rfl, fun r hr => by simp [Except.bind] at hr⟩
  · have hsp := urlsplitCore_ok nfkc ipk x frag sp hx'
    subst hsp
    have hfa := fill_ascii mn _ (splitPure_ascii x frag hx)
    refine ⟨?_, fun r hr => ?_⟩
    · simp [Except.bind, resEncode, mapM_encField_ascii _ hfa, bind, pure, Except.pure]
    · simp only [Except.bind] at hr
      cases hr
      refine ⟨_, rfl, ?_⟩
      simp [resDecode, mapM_decField_ascii _ hfa, bind, Except.bind, pure, Except.pure]

/-! ## `_checknetloc` -/

/-- The netloc without `@`, `:`, `#`, `?`, :515-518. -/
def nfkcInput (n : Str) : Str := (((n.filter (· != 64)).filter (· != 58)).filter (· != 35)).filter (· != 63)

/-- The documented rejection: a non-ASCII netloc whose NFKC form (of `nfkcInput`) changes and
contains `/`, `?`, `#`, `@` or `:`. -/
def BadNfkc (nfkc : Str → Str) (n : Str) : Prop :=
  ¬(∀ c ∈ n, c < 128) ∧ nfkc (nfkcInput n) ≠ nfkcInput n ∧
    ∃ c ∈ [47, 63, 35, 64, 58], c ∈ nfkc (nfkcInput n)

theorem checknetloc_iff (nfkc : Str → Str) (n : Str) :
    checknetloc nfkc (some n) = .ok () ↔ ¬BadNfkc nfkc n := by
  unfold checknetloc BadNfkc
  simp only [nfkcInput]
  generalize hm : (((n.filter (· != 64)).filter (· != 58)).filter (· != 35)).filter (· != 63) = m
  by_cases ha : (n.isEmpty || n.all (· < 128)) = true
  · rw [if_pos ha]
    simp only [true_iff, not_and]
    intro hn
    exfalso; apply hn
    intro c hc
    rcases Bool.or_eq_true _ _ ▸ ha with h | h
    · simp at h; subst h; simp at hc
    · exact of_decide_eq_true (List.all_eq_true.1 h c hc)
  · rw [if_neg ha]
    have hna : ¬(∀ c ∈ n, c < 128) := by
      intro h; apply ha; simp only [Bool.or_eq_true, List.all_eq_true, decide_eq_true_eq]; exact Or.inr h
    by_cases he : (m == nfkc m) = true
    · rw [if_pos he]
      simp only [beq_iff_eq] at he
      simp only [true_iff, not_and]
      intro _ hne; exact absurd he.symm hne
    · rw [if_neg he]
      simp only [beq_iff_eq] at he
      split
      · next hany =>
        simp only [List.any_eq_true, List.contains_iff_mem] at hany
        constructor
        · intro h; cases h
        · intro h; exfalso; apply h
          exact ⟨hna, fun e => he e.symm, hany⟩
      · next hany =>
        simp only [List.any_eq_true, List.contains_iff_mem, not_exists, not_and] at hany
        simp only [true_iff, not_and]
        intro _ _ ⟨c, hc, hc2⟩
        exact hany c hc hc2

theorem netlocStage_nobr (ipk : Str → Option Bool) (r n : Str) (hn : (netPure r).1 = some n)
    (h91 : 91 ∉ n) (h93 : 93 ∉ n) : netlocStage ipk r = .ok (netPure r) := by
  unfold netPure at hn ⊢
  unfold netlocStage
  split at hn
  · next h2 =>
    simp at hn
    rw [if_pos (by simp [h2]), if_pos h2, splitnetloc_eq r h2]
    simp only
    rw [← hn] at h91 h93
    have e : notDelim = fun c => !isDelim c := rfl
    rw [e] at h91 h93
    simp [h91, h93, e]
  · cases hn

/-- For every URL whose netloc (as `urlsplit` splits it) has no brackets, and every NFKC oracle,
`urlsplit` accepts the URL exactly when the netloc is not one the docs reject: non-ASCII, with an
NFKC form (without `@`, `:`, `#`, `?`) that changes and contains `/`, `?`, `#`, `@` or `:`.
Source: the docs of `urlsplit` ("Characters in the netloc attribute that decompose under NFKC
normalization (as used by the IDNA encoding) into any of /, ?, #, @, or : will raise a
ValueError"). -/
def NfkcCheck : Prop :=
  ∀ (nfkc : Str → Str) (ipk : Str → Option Bool) (u n : Str), (splitPure u true).2.1 = some n →
    91 ∉ n → 93 ∉ n →
    ((∃ r, urlsplit nfkc ipk (.str u) .none true true = .ok r) ↔ ¬BadNfkc nfkc n)

theorem nfkcCheck_proven : NfkcCheck := by
  intro nfkc ipk u n hn h91 h93
  have hcs : coerceArgs [.str u, .none] = .ok ([some (.s u), none], false) :=
    coerceArgs_str [some u, none] ⟨u, by simp⟩
  have hsplit : urlsplit nfkc ipk (.str u) .none true true =
      (urlsplitCore nfkc ipk (.s u) none true).bind (fun sp =>
        .ok { fields := fields5 true sp, isBytes := false, keep := some true }) := by
    unfold urlsplit
    simp only [lruHash, hcs, bind, Except.bind]
    simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.false_or, Bool.false_eq_true, ite_false,
      List.headD_cons, Option.getD_some, List.getD_cons_succ, List.getD_cons_zero]
    rcases urlsplitCore nfkc ipk (.s u) none true with e | sp
    · rfl
    · rfl
  have hcore : urlsplitCore nfkc ipk (.s u) none true =
      (checknetloc nfkc (some n)).bind (fun _ => .ok (splitPure u true)) := by
    unfold urlsplitCore
    simp only [bind, Except.bind, pure, Except.pure, schemeStage_none]
    unfold splitPure restOf at hn ⊢
    generalize schemeOf (removeUnsafe (lstripC0 u)) = sr at hn ⊢
    obtain ⟨s, r⟩ := sr
    simp only at hn ⊢
    have hr : (netPure r).1 = some n := by
      revert hn; generalize netPure r = nr; obtain ⟨a, b⟩ := nr; simp
    rw [netlocStage_nobr ipk r n hr h91 h93]
    simp only
    rcases hnp : netPure r with ⟨n', rest⟩
    rw [hnp] at hr
    simp only at hr
    subst hr
    simp only
  rw [hsplit, hcore, ← checknetloc_iff]
  constructor
  · rintro ⟨r, hr⟩
    rcases hc : checknetloc nfkc (some n) with e | v
    · rw [hc] at hr; cases hr
    · cases v; rfl
  · intro hc
    rw [hc]
    exact ⟨_, rfl⟩

/-! ## `port` -/

theorem part_absent (c : Nat) (l : Str) (h : c ∉ l) : part c l = (l, none) := by
  rcases part_cases c l with ⟨a, b, hp, he, _⟩ | ⟨hp, _⟩
  · exfalso; apply h; rw [he]; simp
  · exact hp

theorem rpart_absent (c : Nat) (l : Str) (h : c ∉ l) : rpart c l = (none, l) := by
  unfold rpart
  rw [part_absent c l.reverse (by simpa using h)]
  simp

/-- For every result (`str` or `bytes`) and every netloc: a port that `port` returns is in
0-65535; every error it raises is a `ValueError`; when the netloc is `host:digits` with no `@`,
`[` or `:` in the host and at most 4300 ASCII digits, `port` is their value or the range error;
and a netloc with no `@`, `[` or `:` has no port. A `bytes` netloc has its code points below 256
(a type invariant). Source: the docs of `urlsplit` ("Port number as integer, if present";
"Reading the port attribute will raise a ValueError if an invalid port is specified"). -/
def PortSpec : Prop :=
  ∀ (fields : List (Option Str)) (k : Option Bool) (b : Bool),
    (b = true → ∀ n, fields.getD 1 none = some n → Lt256 n) →
    let r : Res := { fields, isBytes := b, keep := k }
    (∀ p, port r = .ok (some p) → p ≤ 65535) ∧
    (∀ e, port r = .error e → e.className = "ValueError") ∧
    (∀ h d, fields.getD 1 none = some (h ++ 58 :: d) → (∀ c ∈ h, c ≠ 64 ∧ c ≠ 91 ∧ c ≠ 58) →
      64 ∉ d → d ≠ [] → d.all isAsciiDigit = true → d.length ≤ 4300 →
      port r = if digitsVal d ≤ 65535 then .ok (some (digitsVal d))
        else .error (.valueError "Port out of range 0-65535")) ∧
    (∀ h, fields.getD 1 none = some h → (∀ c ∈ h, c ≠ 64 ∧ c ≠ 91 ∧ c ≠ 58) → port r = .ok none)

theorem portOf_cases (s : Str) (r : Py (Option Nat)) (h : portOf (some s) = r) :
    (r = .error (.valueError "~Port could not be cast to integer value")) ∨
    (∃ e, intOfDigits s = .error e ∧ r = .error e) ∨
    (∃ n, intOfDigits s = .ok n ∧ n ≤ 65535 ∧ r = .ok (some n)) ∨
    (∃ n, intOfDigits s = .ok n ∧ ¬ n ≤ 65535 ∧ r = .error (.valueError "Port out of range 0-65535")) := by
  subst h
  simp only [portOf]
  by_cases hc : (!s.isEmpty && s.all isAsciiDigit) = true
  · simp only [hc, ite_true]
    rcases hi : intOfDigits s with e | n
    · exact Or.inr (Or.inl ⟨e, rfl, rfl⟩)
    · by_cases hn : n ≤ 65535
      · exact Or.inr (Or.inr (Or.inl ⟨n, rfl, hn, by simp [hn]⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨n, rfl, hn, by simp [hn]⟩))
  · simp only [Bool.not_eq_true] at hc
    simp [hc]

theorem intOfDigits_err (s : Str) (e : PyExc) (h : intOfDigits s = .error e) : e.className = "ValueError" := by
  unfold intOfDigits at h
  split at h
  · cases h; rfl
  · cases h

theorem portOf_range (x : Option Str) (p : Nat) (h : portOf x = .ok (some p)) : p ≤ 65535 := by
  cases x with
  | none => simp [portOf] at h
  | some s =>
    rcases portOf_cases s _ h with h1 | ⟨e, _, h2⟩ | ⟨n, _, hn, h3⟩ | ⟨n, _, _, h4⟩
    · cases h1
    · cases h2
    · cases h3; exact hn
    · cases h4

theorem portOf_err (x : Option Str) (e : PyExc) (h : portOf x = .error e) : e.className = "ValueError" := by
  cases x with
  | none => simp [portOf] at h
  | some s =>
    rcases portOf_cases s _ h with h1 | ⟨e', he, h2⟩ | ⟨n, _, _, h3⟩ | ⟨n, _, _, h4⟩
    · cases h1; rfl
    · cases h2; exact intOfDigits_err s _ he
    · cases h3
    · cases h4; rfl

theorem portSpec_proven : PortSpec := by
  intro fields k b hb
  have hport : port { fields, isBytes := b, keep := k } = port { fields, isBytes := false, keep := k } := by
    cases b
    · rfl
    · exact (netlocTwin_proven fields k (hb rfl)).2.2.1
  simp only
  rw [hport]
  refine ⟨fun p hp => portOf_range _ p hp, fun e he => portOf_err _ e he, ?_, ?_⟩
  · intro h d hn hh h64 hd hall hlen
    have h64' : 64 ∉ h ++ 58 :: d := by
      simp only [List.mem_append, List.mem_cons, not_or]
      exact ⟨fun m => (hh 64 m).1 rfl, by decide, h64⟩
    have h91 : 91 ∉ h ++ 58 :: d := by
      simp only [List.mem_append, List.mem_cons, not_or]
      refine ⟨fun m => (hh 91 m).2.1 rfl, by decide, fun m => ?_⟩
      have := List.all_eq_true.1 hall 91 m
      simp [isAsciiDigit] at this
    have h58 : 58 ∉ h := fun m => (hh 58 m).2.2 rfl
    have hx : (hostinfoS (some (h ++ 58 :: d))).2 = some d := by
      simp only [hostinfoS, rpart_absent 64 _ h64', part_absent 91 _ h91, part_prefix 58 h d h58,
        Option.getD_some]
      simp [List.isEmpty_iff, hd]
    have hd' : (!d.isEmpty && d.all isAsciiDigit) = true := by simp [hd, hall]
    have hp : portOf (some d) = if digitsVal d ≤ 65535 then .ok (some (digitsVal d))
        else .error (.valueError "Port out of range 0-65535") := by
      simp only [portOf, hd', ite_true, intOfDigits, show ¬ d.length > 4300 by omega, ite_false]
    unfold port
    simp only [Res.netloc, hn, Bool.false_eq_true, ite_false, hx, hp]
  · intro h hn hh
    have h64 : 64 ∉ h := fun m => (hh 64 m).1 rfl
    have h91 : 91 ∉ h := fun m => (hh 91 m).2.1 rfl
    have h58 : 58 ∉ h := fun m => (hh 58 m).2.2 rfl
    unfold port
    simp only [Res.netloc, hn]
    simp [hostinfoS, rpart_absent 64 _ h64, part_absent 91 _ h91, part_absent 58 _ h58, portOf]

end PyLean.TextLibs.Url
