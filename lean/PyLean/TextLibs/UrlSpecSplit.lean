import PyLean.TextLibs.UrlSpecBrackets

/-!
When `urlsplit`, `urlparse` and `urldefrag` succeed, and what they raise: for every `str` URL,
every `scheme` default (`None` or a `str`), every `allow_fragments` and both values of
`missing_as_none`, each returns its fields exactly when the netloc passes the three documented
checks (matched brackets, an accepted bracketed host, the NFKC check), and raises the check's
`ValueError` otherwise.
-/

namespace PyLean.TextLibs.Url

open PyLean

set_option linter.unusedSimpArgs false

/-! ## The checks of `_urlsplit` on the netloc, :615-619 and :624 -/

/-- The bracket checks of :615-619. -/
def bracketChk (ipk : Str → Option Bool) : Option Str → Py Unit
  | none => .ok ()
  | some n =>
    if (91 ∈ n ∧ 93 ∉ n) ∨ (93 ∈ n ∧ 91 ∉ n) then .error (.valueError "Invalid IPv6 URL")
    else if 91 ∈ n then checkBracketedNetloc ipk n else .ok ()

/-- Every check `_urlsplit` makes, in order. -/
def netlocChk (nfkc : Str → Str) (ipk : Str → Option Bool) (n : Option Str) : Py Unit :=
  (bracketChk ipk n).bind (fun _ => checknetloc nfkc n)

/-- The netlocs `urlsplit` accepts: none at all, or one with both brackets or neither, an accepted
bracketed host (`BracketOk`) when it has `[`, and not the documented NFKC rejection. -/
def NetlocOk (nfkc : Str → Str) (ipk : Str → Option Bool) : Option Str → Prop
  | none => True
  | some x => (91 ∈ x ↔ 93 ∈ x) ∧ (91 ∈ x → ∀ hi, AfterAt x hi → BracketOk ipk hi) ∧ ¬BadNfkc nfkc x

theorem netlocChk_iff (nfkc : Str → Str) (ipk : Str → Option Bool) (n : Option Str) :
    netlocChk nfkc ipk n = .ok () ↔ NetlocOk nfkc ipk n := by
  cases n with
  | none => simp [netlocChk, bracketChk, NetlocOk, checknetloc, Except.bind]
  | some x =>
    simp only [netlocChk, bracketChk, NetlocOk]
    have hck := checknetloc_iff nfkc x
    obtain ⟨hi, hhi⟩ := afterAt_exists x
    have hbr := checkBracketedNetloc_iff ipk x hi hhi
    have hall : (∀ hi', AfterAt x hi' → BracketOk ipk hi') ↔ BracketOk ipk hi := by
      constructor
      · intro h; exact h hi hhi
      · intro h hi' h'; rw [← afterAt_unique x hi hi' hhi h']; exact h
    by_cases h91 : 91 ∈ x <;> by_cases h93 : 93 ∈ x
    · have hc1 : ¬((91 ∈ x ∧ 93 ∉ x) ∨ (93 ∈ x ∧ 91 ∉ x)) := by
        rintro (⟨_, h⟩ | ⟨_, h⟩)
        · exact h h93
        · exact h h91
      rw [if_neg hc1, if_pos h91]
      constructor
      · intro h
        rcases hc : checkBracketedNetloc ipk x with e | v
        · rw [hc] at h; cases h
        · rw [hc] at h
          cases v
          exact ⟨⟨fun _ => h93, fun _ => h91⟩, fun _ => hall.2 (hbr.1 hc), hck.1 h⟩
      · rintro ⟨_, hb, hn⟩
        rw [hbr.2 (hall.1 (hb h91))]
        exact hck.2 hn
    · simp [h91, h93, Except.bind]
    · simp [h91, h93, Except.bind]
    · have hc1 : ¬((91 ∈ x ∧ 93 ∉ x) ∨ (93 ∈ x ∧ 91 ∉ x)) := by
        rintro (⟨h, _⟩ | ⟨h, _⟩)
        · exact h91 h
        · exact h93 h
      rw [if_neg hc1, if_neg h91]
      show checknetloc nfkc (some x) = .ok () ↔ _
      rw [hck]
      constructor
      · intro h; exact ⟨⟨fun a => absurd a h91, fun a => absurd a h93⟩, fun a => absurd a h91, h⟩
      · intro h; exact h.2.2

theorem netlocStage_eq (ipk : Str → Option Bool) (r : Str) :
    netlocStage ipk r = (bracketChk ipk (netPure r).1).map (fun _ => netPure r) := by
  unfold netlocStage netPure
  by_cases h2 : r.take 2 = [47, 47]
  · rw [if_pos (by simp [h2]), if_pos h2, splitnetloc_eq r h2]
    simp only [bracketChk]
    have e : notDelim = fun c => !isDelim c := rfl
    rw [← e]
    generalize (r.drop 2).takeWhile notDelim = n
    by_cases h91 : 91 ∈ n <;> by_cases h93 : 93 ∈ n <;> simp [h91, h93, Except.map]
  · rw [if_neg (by simpa using h2), if_neg h2]
    rfl

/-- The scheme of `_urlsplit` with a `scheme` default: the URL's own scheme, else the default. -/
def schemeWith (s : Option Str) (sco : Option Str) : Option Str :=
  match s with
  | some x => some x
  | none => sco.map (fun x => removeUnsafe (stripC0 x))

theorem schemeStage_eq (url : Str) (sc : Option Str) :
    schemeStage url sc = .ok (match schemeOf url with
      | (some x, r) => (some x, r)
      | (none, r) => (sc, r)) := by
  rcases hf : url.findIdx? (· == 58) with _ | i
  · simp [schemeStage, schemeOf, hf]
  · by_cases h : (decide (i > 0) && isAsciiAlpha (url.headD 0) && (url.take i).all isSchemeChar) = true
    · have hs : (url.take i).all isSchemeChar = true := by
        simp only [Bool.and_eq_true] at h; exact h.2
      simp only [schemeStage, schemeOf, hf, h, ite_true]
      simp [UnicodeObj.unicodeLower, isSchemeChar_ascii _ hs, UnicodeObj.asciiUpperOrLower, Except.map]
    · simp only [schemeStage, schemeOf, hf, h, Bool.false_eq_true, ite_false]

/-- `_urlsplit` on a `str` and a `str`-or-`None` default: the checks, then the pure split. -/
theorem urlsplitCore_eq (nfkc : Str → Str) (ipk : Str → Option Bool) (u : Str) (sco : Option Str)
    (frag : Bool) :
    urlsplitCore nfkc ipk (.s u) (sco.map V.s) frag =
      (netlocChk nfkc ipk (splitPure u frag).2.1).map (fun _ =>
        (schemeWith (splitPure u frag).1 sco, (splitPure u frag).2.1, (splitPure u frag).2.2.1,
          (splitPure u frag).2.2.2.1, (splitPure u frag).2.2.2.2)) := by
  unfold urlsplitCore
  cases sco <;>
  · simp only [Option.map_none, Option.map_some, bind, Except.bind, pure, Except.pure, schemeStage_eq]
    unfold splitPure restOf
    generalize schemeOf (removeUnsafe (lstripC0 u)) = sr
    obtain ⟨s, r⟩ := sr
    cases s <;>
    · simp only [netlocStage_eq, netlocChk, Except.map, Except.bind, schemeWith]
      generalize netPure r = np
      obtain ⟨n, rest⟩ := np
      simp only
      cases bracketChk ipk n <;> (try simp only) <;> cases checknetloc nfkc n <;> rfl

/-! ## `urlsplit`, `urlparse`, `urldefrag` -/

/-- What `urlsplit` returns for a `str` URL that passes the checks. -/
def splitRes (u : Str) (sco : Option Str) (frag mn : Bool) : Res :=
  { fields := [fillMissing mn (schemeWith (splitPure u frag).1 sco), fillMissing mn (splitPure u frag).2.1,
      some (splitPure u frag).2.2.1, fillMissing mn (splitPure u frag).2.2.2.1,
      fillMissing mn (splitPure u frag).2.2.2.2],
    isBytes := false, keep := some mn }

/-- The path and params of `_urlparse`, :486-489. -/
def pathParams (s : Option Str) (p : Str) : Str × Option Str :=
  if usesParams.contains (s.getD []) && p.contains 59 then splitparamsMn p true else (p, none)

/-- What `urlparse` returns for a `str` URL that passes the checks. -/
def parseRes (u : Str) (sco : Option Str) (frag mn : Bool) : Res :=
  let s := schemeWith (splitPure u frag).1 sco
  let pp := pathParams s (splitPure u frag).2.2.1
  { fields := [fillMissing mn s, fillMissing mn (splitPure u frag).2.1, some pp.1, fillMissing mn pp.2,
      fillMissing mn (splitPure u frag).2.2.2.1, fillMissing mn (splitPure u frag).2.2.2.2],
    isBytes := false, keep := some mn }

/-- What `urldefrag` returns for a `str` URL with a `#` that passes the checks. -/
def defragRes (u : Str) (mn : Bool) : Res :=
  let x := splitPure u true
  { fields := [some (unsplitPure x.1 x.2.1 x.2.2.1 x.2.2.2.1 none), fillMissing mn x.2.2.2.2],
    isBytes := false, keep := some mn }

/-- What `urldefrag` returns for a URL without `#`: the URL and no fragment. -/
def defragNoHash (u : Str) (mn : Bool) : Res :=
  { fields := [some u, fillMissing mn none], isBytes := false, keep := some mn }

theorem coerce_two (u : Str) (sco : Option Str) :
    coerceArgs [.str u, toArgStr sco] = .ok ([some (.s u), sco.map V.s], false) := by
  have := coerceArgs_str [some u, sco] ⟨u, by simp⟩
  simpa [lift, toArgStr] using this

theorem urlsplit_eq (nfkc : Str → Str) (ipk : Str → Option Bool) (u : Str) (sco : Option Str) (frag mn : Bool) :
    urlsplit nfkc ipk (.str u) (toArgStr sco) frag mn =
      (netlocChk nfkc ipk (splitPure u frag).2.1).map (fun _ => splitRes u sco frag mn) := by
  have hl : lruHash [.str u, toArgStr sco] = .ok () := by cases sco <;> rfl
  unfold urlsplit
  simp only [hl, coerce_two, bind, Except.bind, List.headD_cons, Option.getD_some, List.getD_cons_succ,
    List.getD_cons_zero, urlsplitCore_eq]
  cases netlocChk nfkc ipk (splitPure u frag).2.1 with
  | error e => rfl
  | ok v => rfl

theorem urlparse_eq (nfkc : Str → Str) (ipk : Str → Option Bool) (u : Str) (sco : Option Str) (frag mn : Bool) :
    urlparse nfkc ipk (.str u) (toArgStr sco) frag mn =
      (netlocChk nfkc ipk (splitPure u frag).2.1).map (fun _ => parseRes u sco frag mn) := by
  unfold urlparse urlparseCore
  simp only [coerce_two, bind, Except.bind, List.headD_cons, Option.getD_some, List.getD_cons_succ,
    List.getD_cons_zero, urlsplitCore_eq]
  cases netlocChk nfkc ipk (splitPure u frag).2.1 with
  | error e => rfl
  | ok v => rfl

theorem urldefrag_eq (nfkc : Str → Str) (ipk : Str → Option Bool) (u : Str) (mn : Bool) :
    urldefrag nfkc ipk (.str u) mn =
      if 35 ∈ u then (netlocChk nfkc ipk (splitPure u true).2.1).map (fun _ => defragRes u mn)
      else .ok (defragNoHash u mn) := by
  have hc : coerceArgs [.str u] = .ok ([some (.s u)], false) := coerceArgs_str [some u] ⟨u, by simp⟩
  unfold urldefrag
  simp only [hc, bind, Except.bind, List.headD_cons, pure, Except.pure]
  by_cases h35 : 35 ∈ u
  · have hcont : u.contains 35 = true := by simpa using h35
    rw [if_pos hcont, if_pos h35]
    have := urlsplitCore_eq nfkc ipk u none true
    simp only [Option.map_none] at this
    rw [this]
    cases netlocChk nfkc ipk (splitPure u true).2.1 with
    | error e => rfl
    | ok v =>
      simp only [Except.map, schemeWith]
      have hl := urlunsplitCore_lift (splitPure u true).1 (splitPure u true).2.1 (splitPure u true).2.2.1
        (splitPure u true).2.2.2.1 none
      have hs : (match (splitPure u true).1 with
          | some x => some x
          | none => Option.map (fun x => removeUnsafe (stripC0 x)) none) = (splitPure u true).1 := by
        cases (splitPure u true).1 <;> rfl
      simp only [hs]
      simp only [lift, Option.map_none] at hl
      rw [hl]
      simp only [pure, Except.pure, mkRes, defragRes, fillMissing]
      cases mn <;> cases (splitPure u true).2.2.2.2 <;> simp [bind, Except.bind]
  · have hcont : u.contains 35 = false := by simpa using h35
    rw [if_neg (by simp [h35]), if_neg h35]
    cases mn <;> simp [pure, Except.pure, mkRes, fillMissing, defragNoHash, bind, Except.bind]

/-- For every `str` URL, every `scheme` default (`None` or a `str`), every `allow_fragments` and
both values of `missing_as_none`, and every pair of library oracles (`unicodedata.normalize('NFKC',
_)` and `ipaddress.ip_address`): `urlsplit`, `urlparse` and (for a URL with `#`) `urldefrag`
succeed exactly when the netloc is accepted (`NetlocOk`: no netloc, or both brackets or neither,
an accepted bracketed host, and not the NFKC rejection), and then return their fields: the
scheme (lower-cased, or the default stripped of C0 controls and spaces when the URL has none),
netloc, path (and params when the scheme uses them), query and fragment, with `''` for a missing
part when `missing_as_none` is false. A netloc with only one kind of bracket raises
`ValueError('Invalid IPv6 URL')`, and every other refusal is the `ValueError` of the failing
check. `urlparse` and `urldefrag` raise exactly when `urlsplit` does (`urldefrag` only splits a
URL with `#`). Source: the docs of `urlsplit` ("ValueError ... if the netloc contains invalid IPv6
or IPvFuture brackets"; "Characters in the netloc attribute that decompose under NFKC
normalization ... into any of /, ?, #, @, or : will raise a ValueError"; "The scheme argument
provides the default value of the scheme"; `missing_as_none`), of `urlparse` and of `urldefrag`
("If there is no fragment identifier in url, return url unmodified and an empty string or None"). -/
def UrlsplitSpec : Prop :=
  ∀ (nfkc : Str → Str) (ipk : Str → Option Bool) (u : Str) (sco : Option Str) (frag mn : Bool),
    (∀ r, urlsplit nfkc ipk (.str u) (toArgStr sco) frag mn = .ok r ↔
      r = splitRes u sco frag mn ∧ NetlocOk nfkc ipk (splitPure u frag).2.1) ∧
    (∀ r, urlparse nfkc ipk (.str u) (toArgStr sco) frag mn = .ok r ↔
      r = parseRes u sco frag mn ∧ NetlocOk nfkc ipk (splitPure u frag).2.1) ∧
    (∀ x, (splitPure u frag).2.1 = some x → ((91 ∈ x ∧ 93 ∉ x) ∨ (93 ∈ x ∧ 91 ∉ x)) →
      urlsplit nfkc ipk (.str u) (toArgStr sco) frag mn = .error (.valueError "Invalid IPv6 URL") ∧
      urlparse nfkc ipk (.str u) (toArgStr sco) frag mn = .error (.valueError "Invalid IPv6 URL")) ∧
    (∀ e, netlocChk nfkc ipk (splitPure u frag).2.1 = .error e →
      urlsplit nfkc ipk (.str u) (toArgStr sco) frag mn = .error e ∧
      urlparse nfkc ipk (.str u) (toArgStr sco) frag mn = .error e ∧
      (35 ∈ u → frag = true → urldefrag nfkc ipk (.str u) mn = .error e)) ∧
    (35 ∉ u → urldefrag nfkc ipk (.str u) mn = .ok (defragNoHash u mn)) ∧
    (35 ∈ u → ∀ r, urldefrag nfkc ipk (.str u) mn = .ok r ↔
      r = defragRes u mn ∧ NetlocOk nfkc ipk (splitPure u true).2.1)

theorem netloc_frag (u : Str) (frag : Bool) : (splitPure u frag).2.1 = (splitPure u true).2.1 := by
  unfold splitPure restOf; rfl

theorem urlsplitSpec_proven : UrlsplitSpec := by
  intro nfkc ipk u sco frag mn
  have iffOf : ∀ {β : Type} (f : Unit → β) (r : β) (n : Option Str),
      ((netlocChk nfkc ipk n).map f = .ok r ↔ r = f () ∧ NetlocOk nfkc ipk n) := by
    intro β f r n
    rw [← netlocChk_iff]
    cases netlocChk nfkc ipk n with
    | error e => simp [Except.map]
    | ok v => cases v; simp [Except.map, eq_comm]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r; rw [urlsplit_eq]; exact iffOf _ r _
  · intro r; rw [urlparse_eq]; exact iffOf _ r _
  · intro x hx hb
    have he : netlocChk nfkc ipk (splitPure u frag).2.1 = .error (.valueError "Invalid IPv6 URL") := by
      rw [hx]; simp [netlocChk, bracketChk, hb, Except.bind]
    rw [urlsplit_eq, urlparse_eq, he]
    try exact ⟨rfl, rfl⟩
  · intro e he
    refine ⟨by rw [urlsplit_eq, he]; try rfl, by rw [urlparse_eq, he]; try rfl, fun h35 hf => ?_⟩
    subst hf
    rw [urldefrag_eq, if_pos h35, he]; try rfl
  · intro h35; rw [urldefrag_eq, if_neg h35]
  · intro h35 r; rw [urldefrag_eq, if_pos h35]; exact iffOf _ r _

end PyLean.TextLibs.Url
