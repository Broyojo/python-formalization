import PyLean.TextLibs.UrlSplitProps

/-!
The round trips of `urlsplit`/`urlunsplit`, `urlparse`/`urlunparse` and `urldefrag` with
`missing_as_none=True`, through the real argument coercion and result objects.
-/

namespace PyLean.TextLibs.Url

open PyLean

set_option linter.unusedSimpArgs false

/-- The cleaned URL starts with a scheme (RFC 3986: `ALPHA *( ALPHA / DIGIT / "+" / "-" / "." )`)
followed by `:`. -/
def HasScheme (l : Str) : Prop :=
  ∃ a b, l = a ++ 58 :: b ∧ a ≠ [] ∧ isAsciiAlpha (a.headD 0) = true ∧ a.all isSchemeChar = true

theorem findIdx_prefix (a b : Str) (c : Nat) (h : c ∉ a) : (a ++ c :: b).findIdx? (· == c) = some a.length := by
  induction a with
  | nil => simp [List.findIdx?_cons]
  | cons x r ih =>
    have hx : x ≠ c := fun e => h (e ▸ List.mem_cons_self)
    simp only [List.cons_append, List.findIdx?_cons, beq_iff_eq, hx, Bool.false_eq_true, ite_false,
      ih (fun m => h (List.mem_cons_of_mem _ m))]
    simp

theorem schemeOf_none (l : Str) (r : Str) (h : schemeOf l = (none, r)) : ¬HasScheme l := by
  rintro ⟨a, b, rfl, hne, ha, hall⟩
  have h58 : 58 ∉ a := by
    intro m
    have := List.all_eq_true.1 hall 58 m
    simp [isSchemeChar, isAsciiAlpha, isAsciiDigit] at this
  unfold schemeOf at h
  rw [findIdx_prefix a b 58 h58] at h
  have hlen : a.length > 0 := List.length_pos_iff.2 hne
  have hhead : (a ++ 58 :: b).headD 0 = a.headD 0 := by
    cases a with
    | nil => exact absurd rfl hne
    | cons x r => rfl
  simp only [List.take_left', hhead, ha, hall, hlen, decide_true, Bool.and_self, ite_true] at h
  cases h

/-! ## Argument coercion for `str` arguments -/

def toArgStr : Option Str → Arg
  | some x => .str x
  | none => .none

theorem mixLoop_str (l : List (Option Str)) (si : Option Bool) (hsi : si = none ∨ si = some true) :
    ∃ si', mixLoop si (l.map toArgStr) = .ok si' ∧ (si' = none ∨ si' = some true) := by
  induction l generalizing si with
  | nil => exact ⟨si, rfl, hsi⟩
  | cons x r ih =>
    cases x with
    | none =>
      simp only [List.map_cons, toArgStr, mixLoop, Arg.truthy, Bool.false_eq_true, ite_false]
      exact ih si hsi
    | some s =>
      simp only [List.map_cons, toArgStr, mixLoop, Arg.isStr]
      split
      · rcases hsi with rfl | rfl
        · exact ih (some true) (Or.inr rfl)
        · simp only [bne_self_eq_false, Bool.false_eq_true, ite_false]; exact ih (some true) (Or.inr rfl)
      · exact ih si hsi

theorem firstNotNone_str (l : List (Option Str)) (h : ∃ x, some x ∈ l) :
    firstNotNone (l.map toArgStr) = some true := by
  induction l with
  | nil => obtain ⟨x, hx⟩ := h; simp at hx
  | cons y r ih =>
    cases y with
    | none =>
      simp only [List.map_cons, toArgStr, firstNotNone]
      apply ih
      obtain ⟨x, hx⟩ := h
      simp at hx
      exact ⟨x, hx⟩
    | some s => rfl

theorem toV_toArgStr (x : Option Str) : (toArgStr x).toV = lift x := by
  cases x <;> rfl

/-- `_coerce_args` on `str`s and `None`s, at least one of them a `str`: the `str` path. -/
theorem coerceArgs_str (l : List (Option Str)) (h : ∃ x, some x ∈ l) :
    coerceArgs (l.map toArgStr) = .ok (l.map lift, false) := by
  obtain ⟨si, hmix, hsi⟩ := mixLoop_str l none (Or.inl rfl)
  have hv : List.map Arg.toV (List.map toArgStr l) = l.map lift := by
    simp only [List.map_map]
    congr 1
    funext x
    exact toV_toArgStr x
  unfold coerceArgs
  rcases hsi with rfl | rfl
  · simp only [bind, Except.bind, hmix, firstNotNone_str l h]
    rw [if_pos (by decide)]
    simp only [pure, Except.pure, hv]
  · simp only [bind, Except.bind, hmix]
    rw [if_pos (by decide)]
    simp only [pure, Except.pure, hv]

theorem toComp_str (fields : List (Option Str)) (k : Option Bool) :
    ({ fields, isBytes := false, keep := k } : Res).toComp = { parts := fields.map toArgStr, keep := k } := by
  simp only [Res.toComp]
  congr 1
  apply List.map_congr_left
  intro x _
  cases x <;> rfl

/-! ## `urlsplit` -/

theorem urlsplit_str (nfkc : Str → Str) (ipk : Str → Option Bool) (u : Str) (frag : Bool) (r : Res)
    (h : urlsplit nfkc ipk (.str u) .none frag true = .ok r) :
    r = { fields := [(splitPure u frag).1, (splitPure u frag).2.1, some (splitPure u frag).2.2.1,
        (splitPure u frag).2.2.2.1, (splitPure u frag).2.2.2.2], isBytes := false, keep := some true } := by
  have hc : coerceArgs [.str u, .none] = .ok ([some (.s u), none], false) :=
    coerceArgs_str [some u, none] ⟨u, by simp⟩
  unfold urlsplit at h
  simp only [lruHash, bind, Except.bind, hc] at h
  simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.false_or, Bool.false_eq_true, ite_false,
    List.headD_cons, Option.getD_some, List.getD_cons_succ, List.getD_cons_zero] at h
  rcases hx : urlsplitCore nfkc ipk (.s u) none frag with e | x
  · rw [hx] at h; cases h
  · rw [hx] at h
    have := urlsplitCore_ok nfkc ipk u frag x hx
    subst this
    simp only [fillMissing, ite_true, mkRes, pure, Except.pure] at h
    cases h
    rfl

/-- The components `urlsplit` returns avoid their delimiters. -/
def SplitShape (s n : Option Str) (p : Str) (q : Option Str) : Prop :=
  (∀ x, s = some x → x ≠ [] ∧ x.all isSchemeChar = true ∧ x.all (fun c => !UnicodeObj.pyIsUpper c) = true) ∧
  (∀ x, n = some x → ∀ c ∈ x, isDelim c = false) ∧ 63 ∉ p ∧ 35 ∉ p ∧ (∀ x, q = some x → 35 ∉ x)

theorem takeWhile_notDelim (l : Str) : ∀ c ∈ l.takeWhile notDelim, isDelim c = false := by
  induction l with
  | nil => simp
  | cons x r ih =>
    intro c hc
    by_cases hx : notDelim x = true
    · simp only [List.takeWhile_cons, hx, ite_true, List.mem_cons] at hc
      rcases hc with rfl | hc
      · simp [notDelim] at hx; exact hx
      · exact ih c hc
    · simp [List.takeWhile_cons, hx] at hc

theorem part_fst_not (c : Nat) (l : Str) : c ∉ (part c l).1 := by
  rcases part_cases c l with ⟨a, b, hp, _, hn⟩ | ⟨hp, hn⟩
  · rw [hp]; exact hn
  · rw [hp]; exact hn

theorem part_fst_sub (c d : Nat) (l : Str) (h : d ∉ l) : d ∉ (part c l).1 := by
  intro m
  apply h
  have := part_rebuild c l
  rw [← this]
  exact List.mem_append_left _ m

theorem part_snd_sub (c d : Nat) (l : Str) (h : d ∉ l) (x : Str) (hx : (part c l).2 = some x) : d ∉ x := by
  intro m
  apply h
  have := part_rebuild c l
  rw [hx] at this
  rw [← this]
  simp [opt, m]

theorem splitPure_shape (u : Str) :
    SplitShape (splitPure u true).1 (splitPure u true).2.1 (splitPure u true).2.2.1 (splitPure u true).2.2.2.1 := by
  unfold splitPure restOf
  simp only [fragStage, queryStage, Bool.true_and, part_if]
  generalize hs : schemeOf (removeUnsafe (lstripC0 u)) = sr
  obtain ⟨s, r⟩ := sr
  simp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    subst hx
    refine ⟨schemeOf_ne _ x r hs, ?_, ?_⟩
    all_goals
      unfold schemeOf at hs
      split at hs
      · split at hs
        · next hc =>
          simp only [Prod.mk.injEq, Option.some.injEq] at hs
          rw [← hs.1]
          simp only [Bool.and_eq_true] at hc
          have hall := hc.2
          simp only [List.all_eq_true, List.mem_map] at hall ⊢
          try (intro c hc'; obtain ⟨d, hd, rfl⟩ := hc'; have := hall d hd
               simp [isSchemeChar, isAsciiAlpha, isAsciiDigit, UnicodeObj.pyToLower, UnicodeObj.pyIsUpper] at this ⊢
               split <;> simp_all <;> omega)
        · cases hs
      · cases hs
  · intro x hx
    unfold netPure at hx
    split at hx
    · simp at hx; subst hx; exact takeWhile_notDelim _
    · cases hx
  · exact part_fst_not 63 _
  · exact part_fst_sub 63 35 _ (part_fst_not 35 _)
  · intro x hx
    exact part_snd_sub 63 35 _ (part_fst_not 35 _) x hx

/-- `urlunsplit` on a `str` result whose `_keep_empty` is true. -/
theorem urlunsplit_keep (s n : Option Str) (p : Str) (q f : Option Str) (ke : Option Bool)
    (hke : ke = none ∨ ke = some true) :
    urlunsplit { parts := [s, n, some p, q, f].map toArgStr, keep := some true } ke =
      .ok (.str (unsplitPure s n p q f)) := by
  have hk : ∀ ps, keepOf { parts := ps, keep := some true } ke = .ok true := by
    intro ps; rcases hke with rfl | rfl <;> rfl
  have hl : urlunsplitCore (lift s) (lift n) (lift (some p)) (lift q) (lift f) =
      .ok (some (.s (unsplitPure s n p q f))) := urlunsplitCore_lift s n p q f
  unfold urlunsplit
  rw [coerceArgs_str [s, n, some p, q, f] ⟨p, by simp⟩]
  simp only [bind, Except.bind, List.map_cons, List.map_nil, hk, Bool.not_true, Bool.false_eq_true,
    ite_false, hl]
  rfl

/-- For every `str` URL and every pair of library oracles, when `urlsplit(url, missing_as_none=True)`
does not raise, `urlunsplit` of the result (with `keep_empty` unspecified or true) and its `geturl()`
give back the URL with leading C0 controls and spaces stripped, tabs and newlines removed and the
scheme lower-cased; the scheme is `None` only when the URL does not start with an RFC 3986 scheme;
and the netloc has no `/`, `?`, `#`, the path no `?`, `#`, the query no `#`.
Source: the docs of `urlunsplit` ("This allows rebuilding a URL that was parsed with option
missing_as_none=True") and of `urlsplit`. -/
def SplitRoundTrip : Prop :=
  ∀ (nfkc : Str → Str) (ipk : Str → Option Bool) (u : Str) (r : Res),
    urlsplit nfkc ipk (.str u) .none true true = .ok r →
    splitGeturl r = .ok (.str (normURL u)) ∧ urlunsplit r.toComp (some true) = .ok (.str (normURL u)) ∧
    (r.fields.headD none = none → ¬HasScheme (removeUnsafe (lstripC0 u))) ∧
    ∃ s n p q f, r.fields = [s, n, some p, q, f] ∧ SplitShape s n p q

theorem splitRoundTrip_proven : SplitRoundTrip := by
  intro nfkc ipk u r h
  have hr := urlsplit_str nfkc ipk u true r h
  subst hr
  have hg := urlunsplit_keep (splitPure u true).1 (splitPure u true).2.1 (splitPure u true).2.2.1
    (splitPure u true).2.2.2.1 (splitPure u true).2.2.2.2
  rw [split_rebuild] at hg
  refine ⟨?_, ?_, ?_, ⟨_, _, _, _, _, rfl, splitPure_shape u⟩⟩
  · simp only [splitGeturl, toComp_str]
    exact hg none (Or.inl rfl)
  · simp only [toComp_str]
    exact hg (some true) (Or.inr rfl)
  · intro hn
    simp only [List.headD_cons] at hn
    unfold splitPure at hn
    revert hn
    rcases hs : schemeOf (removeUnsafe (lstripC0 u)) with ⟨_ | s, r'⟩
    · intro _; exact schemeOf_none _ r' hs
    · intro hn; simp at hn

/-! ## `urlparse` -/

theorem findIdx_drop (c : Nat) : ∀ (l : Str) (j : Nat), l.findIdx? (· == c) = some j → l.drop j = c :: l.drop (j + 1)
  | [], j, h => by simp at h
  | x :: r, j, h => by
    simp only [List.findIdx?_cons] at h
    by_cases hx : x = c
    · simp [hx] at h; subst h; simp [hx]
    · simp only [beq_iff_eq, hx, Bool.false_eq_true, ite_false] at h
      cases hr : r.findIdx? (· == c) with
      | none => simp [hr] at h
      | some j' =>
        simp [hr] at h; subst h
        simp only [List.drop_succ_cons]
        exact findIdx_drop c r j' hr

theorem findIdx_none_not (c : Nat) : ∀ (l : Str), l.findIdx? (· == c) = none → c ∉ l
  | [], _ => by simp
  | x :: r, h => by
    simp only [List.findIdx?_cons] at h
    by_cases hx : x = c
    · simp [hx] at h
    · simp only [beq_iff_eq, hx, Bool.false_eq_true, ite_false] at h
      cases hr : r.findIdx? (· == c) with
      | none =>
        have := findIdx_none_not c r hr
        simp only [List.mem_cons, not_or]; exact ⟨fun e => hx e.symm, this⟩
      | some j' => simp [hr] at h

theorem splitparams_rebuild (url : Str) (h : 59 ∈ url) :
    (splitparams url).1 ++ opt 59 (splitparams url).2 = url := by
  unfold splitparams splitparamsMn
  by_cases hs : url.contains 47 = true
  · rw [if_pos hs]
    generalize rfindSlash url = r
    rcases hj : (url.drop r).findIdx? (· == 59) with _ | j
    · simp [opt]
    · simp only [opt]
      have := findIdx_drop 59 (url.drop r) j hj
      rw [List.drop_drop, List.drop_drop] at this
      conv => rhs; rw [← List.take_append_drop (r + j) url]
      rw [this, Nat.add_assoc]
  · rw [if_neg hs]
    rcases hj : url.findIdx? (· == 59) with _ | i
    · exact absurd h (findIdx_none_not 59 url hj)
    · simp only [opt]
      have := findIdx_drop 59 url i hj
      conv => rhs; rw [← List.take_append_drop i url, this]

/-- What `_urlparse` does to the path, :486-489. -/
def paramsOf (s : Option Str) (p : Str) : Str × Option Str :=
  if usesParams.contains (s.getD []) && p.contains 59 then splitparams p else (p, none)

theorem paramsOf_rebuild (s : Option Str) (p : Str) : (paramsOf s p).1 ++ opt 59 (paramsOf s p).2 = p := by
  unfold paramsOf
  split
  · next h =>
    simp only [Bool.and_eq_true, List.contains_iff_mem] at h
    exact splitparams_rebuild p h.2
  · simp [opt]

theorem urlsplit_of_core (nfkc : Str → Str) (ipk : Str → Option Bool) (u : Str) (frag : Bool) (x : Split)
    (hx : urlsplitCore nfkc ipk (.s u) none frag = .ok x) :
    urlsplit nfkc ipk (.str u) .none frag true =
      .ok { fields := [x.1, x.2.1, some x.2.2.1, x.2.2.2.1, x.2.2.2.2], isBytes := false, keep := some true } := by
  have hc : coerceArgs [.str u, .none] = .ok ([some (.s u), none], false) :=
    coerceArgs_str [some u, none] ⟨u, by simp⟩
  unfold urlsplit
  simp only [lruHash, bind, Except.bind, hc]
  simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.false_or, Bool.false_eq_true, ite_false,
    List.headD_cons, Option.getD_some, List.getD_cons_succ, List.getD_cons_zero, hx]
  simp only [fillMissing, ite_true, mkRes, pure, Except.pure, Bool.false_eq_true, ite_false]
  rfl

theorem urlparse_str (nfkc : Str → Str) (ipk : Str → Option Bool) (u : Str) (frag : Bool) (r : Res)
    (h : urlparse nfkc ipk (.str u) .none frag true = .ok r) :
    let x := splitPure u frag
    r = { fields := [x.1, x.2.1, some (paramsOf x.1 x.2.2.1).1, (paramsOf x.1 x.2.2.1).2, x.2.2.2.1, x.2.2.2.2],
          isBytes := false, keep := some true } ∧
    urlsplit nfkc ipk (.str u) .none frag true =
      .ok { fields := [x.1, x.2.1, some x.2.2.1, x.2.2.2.1, x.2.2.2.2], isBytes := false, keep := some true } := by
  have hc : coerceArgs [.str u, .none] = .ok ([some (.s u), none], false) :=
    coerceArgs_str [some u, none] ⟨u, by simp⟩
  unfold urlparse at h
  simp only [bind, Except.bind, hc] at h
  simp only [List.headD_cons, Option.getD_some, List.getD_cons_succ, List.getD_cons_zero] at h
  unfold urlparseCore at h
  simp only [bind, Except.bind] at h
  rcases hx : urlsplitCore nfkc ipk (.s u) none frag with e | x
  · rw [hx] at h; cases h
  · rw [hx] at h
    have hxs := urlsplitCore_ok nfkc ipk u frag x hx
    refine ⟨?_, by rw [urlsplit_of_core nfkc ipk u frag x hx, hxs]⟩
    subst hxs
    simp only [pure, Except.pure, fillMissing, ite_true, mkRes] at h
    cases h
    rfl

theorem urlunparse_keep (s n : Option Str) (p : Str) (a q f : Option Str) (ke : Option Bool)
    (hke : ke = none ∨ ke = some true) :
    urlunparse { parts := [s, n, some p, a, q, f].map toArgStr, keep := some true } ke =
      .ok (.str (unsplitPure s n (p ++ opt 59 a) q f)) := by
  have hk : ∀ ps, keepOf { parts := ps, keep := some true } ke = .ok true := by
    intro ps; rcases hke with rfl | rfl <;> rfl
  unfold urlunparse
  rw [coerceArgs_str [s, n, some p, a, q, f] ⟨p, by simp⟩]
  simp only [bind, Except.bind, List.map_cons, List.map_nil, hk, Bool.not_true, Bool.false_eq_true,
    ite_false]
  cases a with
  | none =>
    have hl := urlunsplitCore_lift s n p q f
    simp only [show lift (none : Option Str) = none from rfl, show lift (some p) = some (.s p) from rfl,
      Option.isSome_none, Bool.false_eq_true, ite_false, opt, List.append_nil, hl]
    rfl
  | some x =>
    have hl := urlunsplitCore_lift s n (p ++ [59] ++ x) q f
    simp only [show lift (some x) = some (.s x) from rfl, show lift (some p) = some (.s p) from rfl,
      Option.isSome_some, ite_true, pyStr, opt, hl]
    simp only [List.append_assoc, List.singleton_append]
    rfl

/-- For every `str` URL and every pair of library oracles, when `urlparse(url, missing_as_none=True)`
does not raise, `urlunparse` of the result (with `keep_empty` unspecified or true) and its
`geturl()` give back the URL normalized as for `urlsplit`, and `urlparse` is `urlsplit` with the
path split into path and params. Source: the docs of `urlunparse` ("This allows rebuilding a URL
that was parsed with option missing_as_none=True") and of `urlparse` ("similar to urlsplit(), but
additionally splits the path component on path and params"). -/
def ParseRoundTrip : Prop :=
  ∀ (nfkc : Str → Str) (ipk : Str → Option Bool) (u : Str) (r : Res),
    urlparse nfkc ipk (.str u) .none true true = .ok r →
    parseGeturl r = .ok (.str (normURL u)) ∧ urlunparse r.toComp (some true) = .ok (.str (normURL u)) ∧
    ∃ s n p a q f, r.fields = [s, n, some p, a, q, f] ∧
      urlsplit nfkc ipk (.str u) .none true true =
        .ok { fields := [s, n, some (p ++ opt 59 a), q, f], isBytes := false, keep := some true }

theorem parseRoundTrip_proven : ParseRoundTrip := by
  intro nfkc ipk u r h
  obtain ⟨hr, hs⟩ := urlparse_str nfkc ipk u true r h
  subst hr
  have hg := urlunparse_keep (splitPure u true).1 (splitPure u true).2.1
    (paramsOf (splitPure u true).1 (splitPure u true).2.2.1).1
    (paramsOf (splitPure u true).1 (splitPure u true).2.2.1).2 (splitPure u true).2.2.2.1 (splitPure u true).2.2.2.2
  rw [paramsOf_rebuild, split_rebuild] at hg
  refine ⟨?_, ?_, ⟨_, _, _, _, _, _, rfl, ?_⟩⟩
  · simp only [parseGeturl, toComp_str]
    exact hg none (Or.inl rfl)
  · simp only [toComp_str]
    exact hg (some true) (Or.inr rfl)
  · rw [paramsOf_rebuild]; exact hs

end PyLean.TextLibs.Url
