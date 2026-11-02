import PyLean.TextLibs.UrlSplitThm

/-!
The bracket checks of `urlsplit` (`_check_bracketed_netloc`, `_check_bracketed_host`) against
`_hostinfo`, and two refutations: the round trip with `allow_fragments=False`, and brackets that
are only in the userinfo.
-/

namespace PyLean.TextLibs.Url

open PyLean

set_option linter.unusedSimpArgs false

/-- `_check_bracketed_netloc` passing means `_hostinfo`'s hostname passes `_check_bracketed_host`. -/
theorem checkBracketed_hostinfo (ipk : Str → Option Bool) (n : Str)
    (h : checkBracketedNetloc ipk n = .ok ()) :
    checkBracketedHost ipk ((hostinfoS (some n)).1.getD []) = .ok () := by
  unfold checkBracketedNetloc at h
  unfold hostinfoS
  simp only
  generalize (rpart 64 n).2 = hp at h ⊢
  rcases hb : part 91 hp with ⟨before, _ | bracketed⟩
  · simp only [hb] at h ⊢; exact h
  · simp only [hb] at h ⊢
    split at h
    · cases h
    · generalize part 93 bracketed = P at h ⊢
      obtain ⟨hn, port⟩ := P
      simp only at h ⊢
      split at h
      · cases h
      · exact h

theorem netlocStage_check (ipk : Str → Option Bool) (url : Str) (n rest : Str)
    (h : netlocStage ipk url = .ok (some n, rest)) (h91 : 91 ∈ n) : checkBracketedNetloc ipk n = .ok () := by
  unfold netlocStage at h
  split at h
  · simp only at h
    generalize hs : splitnetloc url 2 = S at h
    obtain ⟨n', rest'⟩ := S
    simp only at h
    split at h
    · cases h
    · split at h
      · rcases hc : checkBracketedNetloc ipk n' with e | u
        · rw [hc] at h; cases h
        · rw [hc] at h; cases h; cases u; exact hc
      · next h1 h2 =>
        cases h
        exfalso
        apply h1
        simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', List.contains_iff_mem] at h2 ⊢
        by_cases h93 : 93 ∈ n
        · exact absurd ⟨h91, h93⟩ h2
        · left; exact ⟨h91, by simpa using h93⟩
  · cases h

theorem urlsplitCore_check (nfkc : Str → Str) (ipk : Str → Option Bool) (u : Str) (frag : Bool) (x : Split)
    (h : urlsplitCore nfkc ipk (.s u) none frag = .ok x) :
    ∀ n, x.2.1 = some n → 91 ∈ n → checkBracketedNetloc ipk n = .ok () := by
  intro n hn h91
  unfold urlsplitCore at h
  simp only [bind, Except.bind, pure, Except.pure, schemeStage_none] at h
  generalize schemeOf (removeUnsafe (lstripC0 u)) = sr at h
  obtain ⟨s, r⟩ := sr
  simp only at h
  rcases hs : netlocStage ipk r with e | y
  · rw [hs] at h; cases h
  · rw [hs] at h
    obtain ⟨n', rest⟩ := y
    simp only at h
    split at h
    · cases h
    · cases h
      simp at hn
      subst hn
      exact netlocStage_check ipk r n rest hs h91

/-- Whenever `urlsplit` accepts a URL whose netloc contains `[`, the hostname that the result's
`_hostinfo` reads (and `.hostname` lower-cases) passed `_check_bracketed_host`: it is an IPv6
address or an IPvFuture literal, as `ipaddress.ip_address` (the oracle `ipk`) and the regular
expression of :548 decide. Source: (a), the comment at :528-529 ("this function must mirror the
splitting done in NetlocResultMixins._hostinfo()"), and the docs' IPv6 support. -/
def BracketedHostValid : Prop :=
  ∀ (nfkc : Str → Str) (ipk : Str → Option Bool) (u : Str) (frag mn : Bool) (r : Res),
    urlsplit nfkc ipk (.str u) .none frag mn = .ok r →
    ∀ n, r.netloc = some n → 91 ∈ n → checkBracketedHost ipk ((hostinfoS (some n)).1.getD []) = .ok ()

theorem bracketedHostValid_proven : BracketedHostValid := by
  intro nfkc ipk u frag mn r h n hn h91
  have hc : coerceArgs [.str u, .none] = .ok ([some (.s u), none], false) :=
    coerceArgs_str [some u, none] ⟨u, by simp⟩
  unfold urlsplit at h
  simp only [lruHash, bind, Except.bind, hc] at h
  simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.false_or, Bool.false_eq_true, ite_false,
    List.headD_cons, Option.getD_some, List.getD_cons_succ, List.getD_cons_zero] at h
  rcases hx : urlsplitCore nfkc ipk (.s u) none frag with e | x
  · rw [hx] at h; cases h
  · rw [hx] at h
    have hchk := urlsplitCore_check nfkc ipk u frag x hx
    obtain ⟨s, n', p, q, f⟩ := x
    simp only [mkRes, pure, Except.pure, Bool.false_eq_true, ite_false] at h
    cases h
    simp only [Res.netloc, List.getD_cons_succ, List.getD_cons_zero, fillMissing] at hn
    apply checkBracketed_hostinfo
    apply hchk n _ h91
    simp only
    split at hn
    · exact hn
    · cases n' with
      | none => simp at hn; subst hn; simp at h91
      | some m => simp at hn; exact congrArg some hn

/-- `http://u:p[s]@example.com/` as code points. -/
def userinfoCex : Str :=
  [104, 116, 116, 112, 58, 47, 47, 117, 58, 112, 91, 115, 93, 64, 101, 120, 97, 109, 112, 108, 101,
   46, 99, 111, 109, 47]

/-- For every URL whose netloc is ASCII and whose `[` and `]` (both present, so matched as the
docs require) are all in the userinfo, before the last `@`, `urlsplit` does not raise. Source:
the CVE-2025-0938 discussion of python/cpython#105704 and the comment at :528-529: brackets are
only meaningful around the host. -/
def BracketsOnlyInUserinfo : Prop :=
  ∀ (nfkc : Str → Str) (ipk : Str → Option Bool) (u n : Str), (splitPure u true).2.1 = some n →
    (∀ c ∈ n, c < 128) → 91 ∈ n → 93 ∈ n → 91 ∉ (rpart 64 n).2 → 93 ∉ (rpart 64 n).2 →
    ∃ r, urlsplit nfkc ipk (.str u) .none true true = .ok r

/-- `ipaddress.ip_address('example.com')` raises, so the oracle answers `none`; the reproducer
shows CPython's `ValueError`. -/
theorem bracketsOnlyInUserinfo_refuted : ¬BracketsOnlyInUserinfo := by
  intro h
  obtain ⟨r, hr⟩ := h id (fun _ => none) userinfoCex
    [117, 58, 112, 91, 115, 93, 64, 101, 120, 97, 109, 112, 108, 101, 46, 99, 111, 109]
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have : urlsplit id (fun _ => none) (.str userinfoCex) .none true true =
      .error (.valueError "~does not appear to be an IPv4 or IPv6 address") := by decide
  rw [this] at hr
  cases hr

/-- `http://h#x` as code points. -/
def nofragCex : Str := [104, 116, 116, 112, 58, 47, 47, 104, 35, 120]

/-- The round trip of `SplitRoundTrip` for every value of `allow_fragments`. -/
def SplitRoundTripAll : Prop :=
  ∀ (nfkc : Str → Str) (ipk : Str → Option Bool) (u : Str) (frag : Bool) (r : Res),
    urlsplit nfkc ipk (.str u) .none frag true = .ok r → splitGeturl r = .ok (.str (normURL u))

/-- With `allow_fragments=False`, `urlsplit('http://h#x')` ends the netloc at `#` but keeps `#x` as
the path, and `urlunsplit` puts a `/` before it: `'http://h/#x'`. -/
theorem splitRoundTripAll_refuted : ¬SplitRoundTripAll := by
  intro h
  have hs : urlsplit id (fun _ => none) (.str nofragCex) .none false true =
      .ok { fields := [some [104, 116, 116, 112], some [104], some [35, 120], none, none], isBytes := false,
            keep := some true } := by decide
  have := h id (fun _ => none) nofragCex false _ hs
  revert this
  decide

/-! ## `urldefrag` -/

theorem mem_dropWhile (p : Nat → Bool) (x : Nat) (hx : p x = false) : ∀ l : Str, x ∈ l → x ∈ l.dropWhile p
  | [], h => h
  | c :: r, h => by
    simp only [List.dropWhile_cons]
    split
    · next hc =>
      rcases List.mem_cons.1 h with e | e
      · subst e; simp [hx] at hc
      · exact mem_dropWhile p x hx r e
    · exact h

theorem hash_clean (u : Str) (h : 35 ∈ u) : 35 ∈ removeUnsafe (lstripC0 u) := by
  have h1 : 35 ∈ lstripC0 u := mem_dropWhile isC0Space 35 (by decide) u h
  simp only [removeUnsafe, List.mem_filter]
  exact ⟨⟨⟨h1, by decide⟩, by decide⟩, by decide⟩

theorem hash_schemeOf (c : Str) (h : 35 ∈ c) : 35 ∈ (schemeOf c).2 := by
  unfold schemeOf
  rcases hf : c.findIdx? (· == 58) with _ | i
  · exact h
  · simp only
    split
    · next hc =>
      simp only [Bool.and_eq_true] at hc
      have hall := List.all_eq_true.1 hc.2
      have hd := findIdx_drop 58 c i hf
      have hsplit := List.take_append_drop i c
      rw [hd] at hsplit
      rw [← hsplit] at h
      rcases List.mem_append.1 h with m | m
      · have := hall 35 m
        simp [isSchemeChar, isAsciiAlpha, isAsciiDigit] at this
      · rcases List.mem_cons.1 m with e | e
        · cases e
        · exact e
    · exact h

theorem hash_netPure (r : Str) (h : 35 ∈ r) : 35 ∈ (netPure r).2 := by
  unfold netPure
  split
  · next h2 =>
    have hr : r = [47, 47] ++ ((r.drop 2).takeWhile notDelim ++ (r.drop 2).dropWhile notDelim) := by
      rw [List.takeWhile_append_dropWhile, ← h2, List.take_append_drop]
    rw [hr] at h
    rcases List.mem_append.1 h with m | m
    · simp at m
    · rcases List.mem_append.1 m with m | m
      · have := takeWhile_notDelim _ 35 m
        simp [isDelim] at this
      · exact m
  · exact h

theorem part_some_of_mem (c : Nat) (l : Str) (h : c ∈ l) : ∃ f, (part c l).2 = some f := by
  rcases part_cases c l with ⟨a, b, hp, _, _⟩ | ⟨_, hn⟩
  · exact ⟨b, by rw [hp]⟩
  · exact absurd h hn

theorem defrag_frag (u : Str) (h : 35 ∈ u) : ∃ f, (splitPure u true).2.2.2.2 = some f := by
  have h1 := hash_schemeOf _ (hash_clean u h)
  unfold splitPure restOf
  simp only [fragStage, Bool.true_and, part_if]
  generalize schemeOf (removeUnsafe (lstripC0 u)) = sr at h1 ⊢
  obtain ⟨s, r⟩ := sr
  have h2 := hash_netPure r h1
  generalize netPure r = nr at h2 ⊢
  obtain ⟨n, rest⟩ := nr
  exact part_some_of_mem 35 rest h2

theorem unsplitPure_frag (s n : Option Str) (p : Str) (q : Option Str) (f : Str) :
    unsplitPure s n p q (some f) = unsplitPure s n p q none ++ [35] ++ f := by
  cases n <;> cases s <;> cases q <;> simp [unsplitPure] <;> split <;> simp

theorem no_hash_unsplit (s n : Option Str) (p : Str) (q : Option Str) (hs : SplitShape s n p q) :
    35 ∉ unsplitPure s n p q none := by
  obtain ⟨hsc, hn, _, hp, hq⟩ := hs
  have hsch : ∀ x, s = some x → 35 ∉ x := by
    intro x hx m
    have := List.all_eq_true.1 (hsc x hx).2.1 35 m
    simp [isSchemeChar, isAsciiAlpha, isAsciiDigit] at this
  have hnet : ∀ x, n = some x → 35 ∉ x := by
    intro x hx m
    have := hn x hx 35 m
    simp [isDelim] at this
  cases n with
  | none =>
    cases s with
    | none => cases q with
      | none => simp only [unsplitPure]; split <;> simp [hp]
      | some q' => simp only [unsplitPure]; split <;> simp [hp, hq q' rfl]
    | some s' => cases q with
      | none => simp only [unsplitPure]; split <;> split <;> simp [hp, hsch s' rfl]
      | some q' => simp only [unsplitPure]; split <;> split <;> simp [hp, hsch s' rfl, hq q' rfl]
  | some n' =>
    cases s with
    | none => cases q with
      | none => simp only [unsplitPure]; split <;> simp [hp, hnet n' rfl]
      | some q' => simp only [unsplitPure]; split <;> simp [hp, hnet n' rfl, hq q' rfl]
    | some s' => cases q with
      | none => simp only [unsplitPure]; split <;> split <;> simp [hp, hnet n' rfl, hsch s' rfl]
      | some q' => simp only [unsplitPure]; split <;> split <;> simp [hp, hnet n' rfl, hsch s' rfl, hq q' rfl]

/-- For every `str` URL and every pair of library oracles, when `urldefrag(url,
missing_as_none=True)` does not raise: without a `#` it returns the URL unmodified and no
fragment, and `geturl()` is the URL; with a `#` the first part has no `#`, the fragment is a
string, and `geturl()` is the URL normalized as `urlsplit` documents.
Source: the docs of `urldefrag` and of `geturl()`. -/
def DefragRoundTrip : Prop :=
  ∀ (nfkc : Str → Str) (ipk : Str → Option Bool) (u : Str) (r : Res),
    urldefrag nfkc ipk (.str u) true = .ok r →
    (35 ∉ u → r.fields = [some u, none] ∧ defragGeturl r = .ok (.str u)) ∧
    (35 ∈ u → ∃ d f, r.fields = [some d, some f] ∧ 35 ∉ d ∧ defragGeturl r = .ok (.str (normURL u)))

theorem defragRoundTrip_proven : DefragRoundTrip := by
  intro nfkc ipk u r h
  have hc : coerceArgs [.str u] = .ok ([some (.s u)], false) := coerceArgs_str [some u] ⟨u, by simp⟩
  unfold urldefrag at h
  simp only [bind, Except.bind, hc, List.headD_cons, pure, Except.pure] at h
  by_cases h35 : 35 ∈ u
  · have hcont : u.contains 35 = true := by simpa using h35
    rw [if_pos hcont] at h
    rcases hx : urlsplitCore nfkc ipk (.s u) none true with e | x
    · rw [hx] at h; cases h
    · rw [hx] at h
      have hxs := urlsplitCore_ok nfkc ipk u true x hx
      subst hxs
      obtain ⟨f, hf⟩ := defrag_frag u h35
      have hl : urlunsplitCore (Option.map V.s (splitPure u true).1) (Option.map V.s (splitPure u true).2.1)
          (some (V.s (splitPure u true).2.2.1)) (Option.map V.s (splitPure u true).2.2.2.1) none =
          .ok (some (.s (unsplitPure (splitPure u true).1 (splitPure u true).2.1 (splitPure u true).2.2.1
            (splitPure u true).2.2.2.1 none))) :=
        urlunsplitCore_lift (splitPure u true).1 (splitPure u true).2.1 (splitPure u true).2.2.1
          (splitPure u true).2.2.2.1 none
      simp only [hl, pure, Except.pure, mkRes, Bool.false_eq_true, ite_false, hf, Bool.not_true,
        Option.isNone_some, Bool.and_false] at h
      cases h
      refine ⟨fun hn => absurd h35 hn, fun _ => ⟨_, f, rfl, no_hash_unsplit _ _ _ _ (splitPure_shape u), ?_⟩⟩
      have hreb := split_rebuild u
      rw [hf, unsplitPure_frag] at hreb
      simp only [defragGeturl, truthy, List.isEmpty_iff, Option.isSome_some, Bool.true_and,
        Option.getD_some]
      rw [← hreb]
      simp [add, coerceStr, bind, Except.bind]
  · have hcont : u.contains 35 = false := by simpa using h35
    rw [if_neg (by rw [hcont]; decide)] at h
    simp only [pure, Except.pure, mkRes] at h
    cases h
    refine ⟨fun _ => ⟨rfl, ?_⟩, fun h' => absurd h' h35⟩
    simp [defragGeturl, truthy, coerceStr]

end PyLean.TextLibs.Url
