import PyLean.TextLibs.UrlSpecSplit

/-!
`urlunsplit`, `urlunparse` and `DefragResult.geturl` on every value of `keep_empty` and of the
result's `_keep_empty`: the `ValueError` for `keep_empty=True` on a `missing_as_none=False`
result, the false branch (falsy components dropped, the empty netloc kept for `uses_netloc`
schemes), and `_urlunsplit`'s two insertions stated on their own: `'//'` before a path that
starts with `//` when there is no netloc, and `'/'` before a relative path after a netloc.
-/

namespace PyLean.TextLibs.Url

open PyLean

set_option linter.unusedSimpArgs false

/-- `if not x: x = None` on a `str` or `None`. -/
def dropE : Option Str → Option Str
  | some [] => none
  | x => x

/-- The netloc the `keep_empty`-false branch gives, :643-647 / :673-677: a non-empty netloc is
kept; otherwise `''` when the scheme is non-empty, in `uses_netloc`, and the path is empty or
starts with `/`; otherwise `None`. -/
def fixN (s n : Option Str) (p : Str) : Option Str :=
  match n with
  | some (c :: m) => some (c :: m)
  | _ =>
    match s with
    | some (c :: x) => if (c :: x) ∈ usesNetloc ∧ (p = [] ∨ p.take 1 = [47]) then some [] else none
    | _ => none

def cannotMsg : String :=
  "Cannot distinguish between empty and not defined URI components in the result of parsing URL with missing_as_none=False"

theorem truthy_lift (x : Option Str) : truthy (lift x) = (match x with | some (_ :: _) => true | _ => false) := by
  rcases x with _ | _ | ⟨c, r⟩ <;> rfl

theorem noneIfFalse_lift (x : Option Str) : noneIfFalse (lift x) = lift (dropE x) := by
  rcases x with _ | _ | ⟨c, r⟩ <;> rfl

theorem fixNetloc_lift (s n : Option Str) (p : Str) :
    fixNetloc (lift s) (lift n) (some (.s p)) = lift (fixN s n p) := by
  unfold fixNetloc fixN
  rcases n with _ | _ | ⟨c, m⟩
  · rcases s with _ | _ | ⟨d, x⟩
    · rfl
    · rfl
    · simp only [truthy, lift, Option.map_none, Option.map_some, List.isEmpty_cons, Bool.not_false,
        Bool.not_true, inList, startsSlash, Bool.true_and]
      by_cases hu : (d :: x) ∈ usesNetloc
      · by_cases hp : p = [] ∨ p.take 1 = [47]
        · rcases hp with rfl | hp
          · simp [hu]
          · have : p ≠ [] := by intro e; subst e; simp at hp
            simp [hu, hp, this, List.isEmpty_iff]
        · simp only [not_or] at hp
          simp [hu, hp.1, hp.2, List.isEmpty_iff]
      · simp [hu]
  · rcases s with _ | _ | ⟨d, x⟩
    · rfl
    · rfl
    · simp only [truthy, lift, Option.map_none, Option.map_some, List.isEmpty_cons, List.isEmpty_nil,
        Bool.not_false, Bool.not_true, inList, startsSlash, Bool.true_and]
      by_cases hu : (d :: x) ∈ usesNetloc
      · by_cases hp : p = [] ∨ p.take 1 = [47]
        · rcases hp with rfl | hp
          · simp [hu]
          · have : p ≠ [] := by intro e; subst e; simp at hp
            simp [hu, hp, this, List.isEmpty_iff]
        · simp only [not_or] at hp
          simp [hu, hp.1, hp.2, List.isEmpty_iff]
      · simp [hu]
  · rfl

theorem keepOf_cases (c : Comp) (ke : Option Bool) :
    (ke = some true → c.keep = some false → keepOf c ke = .error (.valueError cannotMsg)) ∧
    ((ke = some true ∧ c.keep ≠ some false) ∨ (ke = none ∧ c.keep = some true) → keepOf c ke = .ok true) ∧
    (ke = some false ∨ (ke = none ∧ c.keep ≠ some true) → keepOf c ke = .ok false) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h1 h2; subst h1; simp [keepOf, h2, cannotMsg]
  · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩)
    · rcases hk : c.keep with _ | _ | _
      · simp [keepOf, hk]
      · exact absurd hk h
      · simp [keepOf, hk]
    · simp [keepOf, h]
  · rintro (rfl | ⟨rfl, h⟩)
    · rfl
    · rcases hk : c.keep with _ | _ | _
      · simp [keepOf, hk]
      · simp [keepOf, hk]
      · exact absurd hk h

/-- For every tuple of `str` components (`None` allowed except for the path), every
`keep_empty` (`None` for unspecified) and every `_keep_empty` of the tuple (`None` when it has
none): `urlunsplit` and `urlunparse` raise `ValueError('Cannot distinguish ...')` for
`keep_empty=True` on a result of `missing_as_none=False`; when `keep_empty` is true (or
unspecified on a `missing_as_none=True` result) they join every component that is not `None`;
otherwise they first turn every false component into `None`, keeping an empty netloc only for a
non-empty scheme in `uses_netloc` with an empty path or one starting with `/`. Joining
(`_urlunsplit`) writes `scheme:` for a non-empty scheme, `//netloc` with a `/` added before a
path that does not start with one, `//` before a path that starts with `//` when there is no
netloc, then `?query` and `#fragment`; `urlunparse` first appends `;params` to the path. In
particular, without a netloc, a path `//p` becomes `////p`, which `urlsplit` reads back as an
empty netloc and the path `//p`. Source: the docstrings of `urlunsplit` and `urlunparse` ("This
may result in a slightly different, but equivalent URL ... keep_empty is false or components is
the result of the urlsplit() call with missing_as_none=False"), the docs of `keep_empty`, and RFC
3986 section 3.3 ("If a URI does not contain an authority component, then the path cannot begin
with two slash characters"; "If a URI contains an authority component, then the path component
must either be empty or begin with a slash"). -/
def UnsplitSpec : Prop :=
  (∀ (s n : Option Str) (p : Str) (q f : Option Str) (k ke : Option Bool),
    (ke = some true → k = some false →
      urlunsplit { parts := [s, n, some p, q, f].map toArgStr, keep := k } ke = .error (.valueError cannotMsg)) ∧
    ((ke = some true ∧ k ≠ some false) ∨ (ke = none ∧ k = some true) →
      urlunsplit { parts := [s, n, some p, q, f].map toArgStr, keep := k } ke = .ok (.str (unsplitPure s n p q f))) ∧
    (ke = some false ∨ (ke = none ∧ k ≠ some true) →
      urlunsplit { parts := [s, n, some p, q, f].map toArgStr, keep := k } ke =
        .ok (.str (unsplitPure (dropE s) (fixN s n p) p (dropE q) (dropE f))))) ∧
  (∀ (s n : Option Str) (p : Str) (a q f : Option Str) (k ke : Option Bool),
    (ke = some true → k = some false →
      urlunparse { parts := [s, n, some p, a, q, f].map toArgStr, keep := k } ke = .error (.valueError cannotMsg)) ∧
    ((ke = some true ∧ k ≠ some false) ∨ (ke = none ∧ k = some true) →
      urlunparse { parts := [s, n, some p, a, q, f].map toArgStr, keep := k } ke =
        .ok (.str (unsplitPure s n (p ++ opt 59 a) q f))) ∧
    (ke = some false ∨ (ke = none ∧ k ≠ some true) →
      urlunparse { parts := [s, n, some p, a, q, f].map toArgStr, keep := k } ke =
        .ok (.str (unsplitPure (dropE s) (fixN s n p) (p ++ opt 59 (dropE a)) (dropE q) (dropE f))))) ∧
  (∀ (s : Option Str) (n : Str) (p : Str) (q f : Option Str),
    unsplitPure s (some n) p q f =
      (match s with | some (c :: x) => (c :: x) ++ [58] | _ => []) ++ [47, 47] ++ n ++
        (if p ≠ [] ∧ p.take 1 ≠ [47] then 47 :: p else p) ++ opt 63 q ++ opt 35 f) ∧
  (∀ (s : Option Str) (p : Str) (q f : Option Str), p.take 2 = [47, 47] →
    unsplitPure s none p q f =
      (match s with | some (c :: x) => (c :: x) ++ [58] | _ => []) ++ [47, 47] ++ p ++ opt 63 q ++ opt 35 f) ∧
  (∀ (s : Option Str) (p : Str) (q f : Option Str), p.take 2 ≠ [47, 47] →
    unsplitPure s none p q f =
      (match s with | some (c :: x) => (c :: x) ++ [58] | _ => []) ++ p ++ opt 63 q ++ opt 35 f) ∧
  (∀ (nfkc : Str → Str) (ipk : Str → Option Bool) (p : Str), p.take 2 = [47, 47] → 63 ∉ p → 35 ∉ p →
    (∀ c ∈ p, c ≠ 9 ∧ c ≠ 10 ∧ c ≠ 13) →
    urlunsplit { parts := [none, none, some p, none, none].map toArgStr, keep := some true } none =
      .ok (.str ([47, 47] ++ p)) ∧
    urlsplit nfkc ipk (.str ([47, 47] ++ p)) .none true true =
      .ok { fields := [none, some [], some p, none, none], isBytes := false, keep := some true })

theorem unsplit_body (c : Comp) (ke : Option Bool) (s n : Option Str) (p : Str) (q f : Option Str)
    (hc : c.parts = [s, n, some p, q, f].map toArgStr) :
    urlunsplit c ke = (keepOf c ke).bind (fun keep =>
      if !keep then .ok (.str (unsplitPure (dropE s) (fixN s n p) p (dropE q) (dropE f)))
      else .ok (.str (unsplitPure s n p q f))) := by
  unfold urlunsplit
  rw [hc, coerceArgs_str [s, n, some p, q, f] ⟨p, by simp⟩]
  simp only [bind, Except.bind, List.map_cons, List.map_nil]
  have hp : lift (some p) = some (.s p) := rfl
  cases keepOf c ke with
  | error e => rfl
  | ok keep =>
    cases keep
    · simp only [Bool.not_false, ite_true, hp]
      rw [noneIfFalse_lift, fixNetloc_lift, noneIfFalse_lift, noneIfFalse_lift, urlunsplitCore_lift]
      rfl
    · simp only [Bool.not_true, Bool.false_eq_true, ite_false, hp]
      rw [urlunsplitCore_lift]
      rfl

theorem unparse_body (c : Comp) (ke : Option Bool) (s n : Option Str) (p : Str) (a q f : Option Str)
    (hc : c.parts = [s, n, some p, a, q, f].map toArgStr) :
    urlunparse c ke = (keepOf c ke).bind (fun keep =>
      if !keep then .ok (.str (unsplitPure (dropE s) (fixN s n p) (p ++ opt 59 (dropE a)) (dropE q) (dropE f)))
      else .ok (.str (unsplitPure s n (p ++ opt 59 a) q f))) := by
  unfold urlunparse
  rw [hc, coerceArgs_str [s, n, some p, a, q, f] ⟨p, by simp⟩]
  simp only [bind, Except.bind, List.map_cons, List.map_nil]
  have hp : lift (some p) = some (.s p) := rfl
  have hpar : ∀ a' s' n' q' f' : Option Str,
      urlunsplitCore (lift s') (lift n')
        (if (lift a').isSome = true then some (V.s (pyStr (some (V.s p)) ++ [59] ++ pyStr (lift a'))) else some (.s p))
        (lift q') (lift f') = .ok (some (.s (unsplitPure s' n' (p ++ opt 59 a') q' f'))) := by
    intro a' s' n' q' f'
    cases a' with
    | none =>
      have := urlunsplitCore_lift s' n' p q' f'
      simp only [lift, Option.map_none, Option.isSome_none, Bool.false_eq_true, ite_false] at this ⊢
      rw [this]; simp [opt]
    | some x =>
      have := urlunsplitCore_lift s' n' (p ++ [59] ++ x) q' f'
      simp only [lift, Option.map_some, Option.isSome_some, ite_true, pyStr] at this ⊢
      rw [this]; simp [opt]
  cases keepOf c ke with
  | error e => rfl
  | ok keep =>
    cases keep
    · simp only [Bool.not_false, ite_true, hp]
      rw [noneIfFalse_lift, fixNetloc_lift, noneIfFalse_lift, noneIfFalse_lift, noneIfFalse_lift, hpar]
      rfl
    · simp only [Bool.not_true, Bool.false_eq_true, ite_false, hp]
      rw [hpar]
      rfl

theorem filter_ne_self (p : Str) (d : Nat) (h : d ∉ p) : p.filter (· != d) = p := by
  induction p with
  | nil => rfl
  | cons c r ih =>
    have hc : c ≠ d := fun e => h (e ▸ List.mem_cons_self)
    simp [List.filter_cons, hc, ih (fun m => h (List.mem_cons_of_mem _ m))]

theorem unsplitSpec_proven : UnsplitSpec := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s n p q f k ke
    have hb := unsplit_body { parts := [s, n, some p, q, f].map toArgStr, keep := k } ke s n p q f rfl
    obtain ⟨k1, k2, k3⟩ := keepOf_cases { parts := [s, n, some p, q, f].map toArgStr, keep := k } ke
    refine ⟨fun h1 h2 => ?_, fun h => ?_, fun h => ?_⟩
    · rw [hb, k1 h1 h2]; rfl
    · rw [hb, k2 h]; rfl
    · rw [hb, k3 h]; rfl
  · intro s n p a q f k ke
    have hb := unparse_body { parts := [s, n, some p, a, q, f].map toArgStr, keep := k } ke s n p a q f rfl
    obtain ⟨k1, k2, k3⟩ := keepOf_cases { parts := [s, n, some p, a, q, f].map toArgStr, keep := k } ke
    refine ⟨fun h1 h2 => ?_, fun h => ?_, fun h => ?_⟩
    · rw [hb, k1 h1 h2]; rfl
    · rw [hb, k2 h]; rfl
    · rw [hb, k3 h]; rfl
  · intro s n p q f
    rcases s with _ | _ | ⟨c, x⟩ <;> rcases q with _ | q <;> rcases f with _ | f <;>
      simp [unsplitPure, opt]
  · intro s p q f hp
    rcases s with _ | _ | ⟨c, x⟩ <;> rcases q with _ | q <;> rcases f with _ | f <;>
      simp [unsplitPure, hp, opt]
  · intro s p q f hp
    rcases s with _ | _ | ⟨c, x⟩ <;> rcases q with _ | q <;> rcases f with _ | f <;>
      simp [unsplitPure, hp, opt]
  · intro nfkc ipk p hp h63 h35 hc
    obtain ⟨r, rfl⟩ : ∃ r, p = 47 :: 47 :: r := by
      rcases p with _ | ⟨a, _ | ⟨b, r⟩⟩
      · simp at hp
      · simp at hp
      · simp at hp; exact ⟨r, by rw [hp.1, hp.2]⟩
    constructor
    · have hb := unsplit_body ⟨[none, none, some (47 :: 47 :: r), none, none].map toArgStr, some true⟩
        none none none (47 :: 47 :: r) none none rfl
      rw [hb]
      simp [keepOf, unsplitPure, Except.bind]
    · have hsp : splitPure ([47, 47] ++ 47 :: 47 :: r) true = (none, some [], 47 :: 47 :: r, none, none) := by
        have hl : lstripC0 ([47, 47] ++ 47 :: 47 :: r) = [47, 47] ++ 47 :: 47 :: r := by
          simp [lstripC0, List.dropWhile_cons, isC0Space]
        have hr : removeUnsafe ([47, 47] ++ 47 :: 47 :: r) = [47, 47] ++ 47 :: 47 :: r := by
          have h9 : 9 ∉ ([47, 47] ++ 47 :: 47 :: r) := by
            intro m; simp at m; exact (hc 9 (by simp [m])).1 rfl
          have h13 : 13 ∉ ([47, 47] ++ 47 :: 47 :: r) := by
            intro m; simp at m; exact (hc 13 (by simp [m])).2.2 rfl
          have h10 : 10 ∉ ([47, 47] ++ 47 :: 47 :: r) := by
            intro m; simp at m; exact (hc 10 (by simp [m])).2.1 rfl
          unfold removeUnsafe
          rw [filter_ne_self _ 9 h9, filter_ne_self _ 13 h13, filter_ne_self _ 10 h10]
        have hs : schemeOf ([47, 47] ++ 47 :: 47 :: r) = (none, [47, 47] ++ 47 :: 47 :: r) := by
          unfold schemeOf
          split
          · simp [isAsciiAlpha]
          · rfl
        unfold splitPure restOf netPure
        rw [hl, hr, hs]
        simp only [List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero, ite_true,
          List.drop_succ_cons, List.drop_zero]
        have hnd : notDelim 47 = false := by decide
        simp only [List.takeWhile_cons, List.dropWhile_cons, hnd, Bool.false_eq_true, ite_false]
        have hf : fragStage true (47 :: 47 :: r) = (47 :: 47 :: r, none) := by
          simp [fragStage, h35]
        have hq : queryStage (47 :: 47 :: r) = (47 :: 47 :: r, none) := by
          simp [queryStage, h63]
        simp [hf, hq]
      have := urlsplit_eq nfkc ipk ([47, 47] ++ 47 :: 47 :: r) none true true
      simp only [toArgStr] at this
      rw [this]
      unfold splitRes
      rw [hsp]
      simp [netlocChk, bracketChk, checknetloc, Except.bind, Except.map, schemeWith, fillMissing]

/-! ## `DefragResult.geturl` -/

/-- A `str` (`false`) or `bytes` (`true`) return value. -/
def wrapArg (isB : Bool) (x : Str) : Arg := if isB then .bytes x false else .str x

/-- For every `DefragResult` or `DefragResultBytes` (url and fragment as `urldefrag` builds them)
and every `_keep_empty` (`None` when unset): `geturl()` is the url followed by `#` and the
fragment when the fragment is non-empty, or empty but not `None` with `_keep_empty` true; and the
url alone otherwise. Source: the docs of `geturl()` for `DefragResult` ("the fragment ... is
dropped if it is empty or None, unless missing_as_none was true") and of `urldefrag`. -/
def DefragGeturlSpec : Prop :=
  ∀ (url : Str) (fr : Option Str) (isB : Bool) (k : Option Bool),
    defragGeturl { fields := [some url, fr], isBytes := isB, keep := k } =
      .ok (wrapArg isB (url ++ match fr with
        | some f => if f ≠ [] ∨ k = some true then 35 :: f else []
        | none => []))

theorem defragGeturlSpec_proven : DefragGeturlSpec := by
  intro url fr isB k
  unfold defragGeturl wrapArg
  rcases fr with _ | ⟨_ | ⟨c, f⟩⟩
  · cases isB <;> simp [truthy, coerceStr]
  · rcases k with _ | _ | _ <;> cases isB <;> simp [truthy, coerceStr, add, bind, Except.bind]
  · cases isB <;> simp [truthy, coerceStr, add, bind, Except.bind]

end PyLean.TextLibs.Url
