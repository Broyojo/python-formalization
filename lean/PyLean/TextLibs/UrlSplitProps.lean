import PyLean.TextLibs.UrlSplit

/-!
`urlunsplit(urlsplit(u, missing_as_none=True)) == u`, up to the normalization `urlsplit`
documents, and the same for `urlparse`/`urlunparse` and `urldefrag`.
-/

namespace PyLean.TextLibs.Url

open PyLean

set_option linter.unusedSimpArgs false

/-! ## The pure shape of `_urlsplit` -/

def notDelim (c : Nat) : Bool := !isDelim c

/-- The scheme split off at :606-612, as `schemeStage` computes it when `scheme` is `None`. -/
def schemeOf (url : Str) : Option Str × Str :=
  match url.findIdx? (· == 58) with
  | some i =>
    if i > 0 && isAsciiAlpha (url.headD 0) && (url.take i).all isSchemeChar then
      (some ((url.take i).map UnicodeObj.pyToLower), url.drop (i + 1))
    else (none, url)
  | none => (none, url)

/-- What `netlocStage` returns when it does not raise. -/
def netPure (url : Str) : Option Str × Str :=
  if url.take 2 = [47, 47] then (some ((url.drop 2).takeWhile notDelim), (url.drop 2).dropWhile notDelim)
  else (none, url)

/-- Netloc, path, query and fragment of what follows the scheme. -/
def restOf (url : Str) (frag : Bool) : Option Str × Str × Option Str × Option Str :=
  let (netloc, url) := netPure url
  let (url, fragment) := fragStage frag url
  let (url, query) := queryStage url
  (netloc, url, query, fragment)

/-- `_urlsplit(u)` when no check raises. -/
def splitPure (u : Str) (frag : Bool) : Split :=
  let (s, r) := schemeOf (removeUnsafe (lstripC0 u))
  let (n, p, q, f) := restOf r frag
  (s, n, p, q, f)

/-- The URL `urlsplit` documents getting back: leading C0 controls and spaces stripped, tabs and
newlines removed, the scheme in lower case. -/
def normURL (u : Str) : Str :=
  match schemeOf (removeUnsafe (lstripC0 u)) with
  | (some s, r) => s ++ [58] ++ r
  | (none, r) => r

theorem isSchemeChar_ascii (s : Str) (h : s.all isSchemeChar = true) : UnicodeObj.isAscii s = true := by
  simp only [List.all_eq_true] at h
  simp only [UnicodeObj.isAscii, List.all_eq_true, decide_eq_true_eq]
  intro c hc
  have := h c hc
  simp [isSchemeChar, isAsciiAlpha, isAsciiDigit] at this
  omega

theorem schemeStage_none (url : Str) : schemeStage url none = .ok (schemeOf url) := by
  rcases hf : url.findIdx? (· == 58) with _ | i
  · simp [schemeStage, schemeOf, hf]
  · by_cases h : (decide (i > 0) && isAsciiAlpha (url.headD 0) && (url.take i).all isSchemeChar) = true
    · have hs : (url.take i).all isSchemeChar = true := by
        simp only [Bool.and_eq_true] at h; exact h.2
      simp only [schemeStage, schemeOf, hf, h, ite_true]
      simp [UnicodeObj.unicodeLower, isSchemeChar_ascii _ hs, UnicodeObj.asciiUpperOrLower, Except.map]
    · simp only [schemeStage, schemeOf, hf, h, Bool.false_eq_true, ite_false]

theorem netlocStage_ok (ipk : Str → Option Bool) (url : Str) (y : Option Str × Str)
    (h : netlocStage ipk url = .ok y) : y = netPure url := by
  unfold netlocStage at h
  unfold netPure
  by_cases h2 : url.take 2 = [47, 47]
  · rw [if_pos (by simp [h2])] at h
    rw [if_pos h2]
    rw [splitnetloc_eq url h2] at h
    simp only at h
    split at h
    · cases h
    · split at h
      · cases hc : checkBracketedNetloc ipk _ with
        | error e => rw [hc] at h; cases h
        | ok u => rw [hc] at h; cases h; rfl
      · cases h; rfl
  · rw [if_neg (by simpa using h2)] at h
    rw [if_neg h2]
    cases h; rfl

/-- When `_urlsplit` does not raise, it returns `splitPure`. -/
theorem urlsplitCore_ok (nfkc : Str → Str) (ipk : Str → Option Bool) (u : Str) (frag : Bool) (x : Split)
    (h : urlsplitCore nfkc ipk (.s u) none frag = .ok x) : x = splitPure u frag := by
  unfold urlsplitCore at h
  simp only [bind, Except.bind, pure, Except.pure, schemeStage_none] at h
  unfold splitPure restOf
  generalize schemeOf (removeUnsafe (lstripC0 u)) = sr at h ⊢
  obtain ⟨s, r⟩ := sr
  simp only at h ⊢
  rcases hn : netlocStage ipk r with e | y
  · rw [hn] at h; cases h
  · rw [hn] at h
    have := netlocStage_ok ipk r y hn
    subst this
    rcases hy : netPure r with ⟨n, rest⟩
    simp only [hy] at h ⊢
    split at h
    · cases h
    · cases h; rfl

/-! ## `_urlunsplit` on strings -/

theorem urlunsplitCore_lift (s n : Option Str) (p : Str) (q f : Option Str) :
    urlunsplitCore (lift s) (lift n) (some (.s p)) (lift q) (lift f) = .ok (some (.s (unsplitPure s n p q f))) := by
  cases n <;> cases s <;> cases q <;> cases f <;>
    simp [urlunsplitCore, unsplitPure, lift, add, truthy, startsSlash, sliceIsSlashes, bind, Except.bind,
      pure, Except.pure] <;>
    (repeat' split) <;> simp_all

/-! ## Rebuilding -/

/-- `x + sep + y` when the part is present. -/
def opt (c : Nat) : Option Str → Str
  | some y => c :: y
  | none => []

theorem part_if (c : Nat) (l : Str) : (if l.contains c then part c l else (l, none)) = part c l := by
  split
  · rfl
  · next h =>
    rcases part_cases c l with ⟨a, b, hp, he, _⟩ | ⟨hp, _⟩
    · exfalso; apply h; rw [he]; simp
    · exact hp.symm

theorem part_rebuild (c : Nat) (l : Str) : (part c l).1 ++ opt c (part c l).2 = l := by
  rcases part_cases c l with ⟨a, b, hp, he, _⟩ | ⟨hp, _⟩
  · rw [hp]; exact he.symm
  · rw [hp]; simp [opt]

theorem part_fst_cons (c x : Nat) (t : Str) (h : x ≠ c) : (part c (x :: t)).1 = x :: (part c t).1 := by
  rw [part_cons, if_neg h]

theorem part_fst_hit (c : Nat) (t : Str) : (part c (c :: t)).1 = [] := by
  rw [part_cons, if_pos rfl]

theorem part_fst_nil (c : Nat) : (part c []).1 = [] := by simp [part]

/-- The path, query and fragment of `fragStage` then `queryStage`, rebuilt. -/
theorem fq_rebuild (url : Str) :
    ((part 63 (part 35 url).1).1 ++ opt 63 (part 63 (part 35 url).1).2) ++ opt 35 (part 35 url).2 = url := by
  rw [part_rebuild, part_rebuild]

theorem prefix_take2 (p x : Str) (h : p.take 2 = [47, 47]) : (p ++ x).take 2 = [47, 47] := by
  match p, h with
  | a :: b :: t, h => simp at h ⊢; exact h

theorem fq_path_prefix (url : Str) : ∃ x, url = (part 63 (part 35 url).1).1 ++ x := by
  refine ⟨opt 63 (part 63 (part 35 url).1).2 ++ opt 35 (part 35 url).2, ?_⟩
  conv => lhs; rw [← fq_rebuild url]
  simp

/-- What follows the netloc starts with `/`, `?`, `#` or is empty, so the path is empty or starts
with `/`. -/
theorem fq_path_slash (R : Str) (hR : R = [] ∨ ∃ x t, R = x :: t ∧ isDelim x = true) :
    let p := (part 63 (part 35 R).1).1
    ¬(p ≠ [] ∧ p.take 1 ≠ [47]) := by
  intro p
  rcases hR with rfl | ⟨x, t, rfl, hx⟩
  · simp [p, part_fst_nil]
  · simp only [isDelim, Bool.or_eq_true, beq_iff_eq] at hx
    rcases hx with (rfl | rfl) | rfl
    · rw [show p = (part 63 (part 35 (47 :: t)).1).1 from rfl, part_fst_cons 35 47 t (by decide),
        part_fst_cons 63 47 _ (by decide)]
      simp
    · rw [show p = (part 63 (part 35 (63 :: t)).1).1 from rfl, part_fst_cons 35 63 t (by decide),
        part_fst_hit]
      simp
    · rw [show p = (part 63 (part 35 (35 :: t)).1).1 from rfl, part_fst_hit, part_fst_nil]
      simp

theorem dropWhile_shape (l : Str) : l.dropWhile notDelim = [] ∨
    ∃ x t, l.dropWhile notDelim = x :: t ∧ isDelim x = true := by
  induction l with
  | nil => simp
  | cons c r ih =>
    by_cases h : notDelim c = true
    · simp only [List.dropWhile_cons, h, ite_true]; exact ih
    · simp only [List.dropWhile_cons, h, Bool.false_eq_true, ite_false]
      right; refine ⟨c, r, rfl, ?_⟩
      simp [notDelim] at h; exact h

theorem unsplitPure_scheme (s : Str) (hs : s ≠ []) (n : Option Str) (p : Str) (q f : Option Str) :
    unsplitPure (some s) n p q f = s ++ [58] ++ unsplitPure none n p q f := by
  cases n <;> cases q <;> cases f <;> simp [unsplitPure, hs]

/-- What follows the scheme is rebuilt (with `allow_fragments` true). -/
theorem rest_rebuild (r : Str) :
    unsplitPure none (restOf r true).1 (restOf r true).2.1 (restOf r true).2.2.1 (restOf r true).2.2.2 = r := by
  simp only [restOf, fragStage, queryStage, Bool.true_and, part_if]
  unfold netPure
  by_cases h2 : r.take 2 = [47, 47]
  · rw [if_pos h2]
    simp only
    have hr : r = [47, 47] ++ ((r.drop 2).takeWhile notDelim ++ (r.drop 2).dropWhile notDelim) := by
      rw [List.takeWhile_append_dropWhile, ← h2, List.take_append_drop]
    generalize (r.drop 2).takeWhile notDelim = N at hr
    generalize hRd : (r.drop 2).dropWhile notDelim = R at hr
    have hshape := dropWhile_shape (r.drop 2)
    rw [hRd] at hshape
    have hslash := fq_path_slash R hshape
    simp only at hslash
    have hreb := fq_rebuild R
    generalize (part 35 R) = P35 at hslash hreb ⊢
    obtain ⟨a, f⟩ := P35
    generalize (part 63 a) = P63 at hslash hreb ⊢
    obtain ⟨p, q⟩ := P63
    simp only at hslash hreb
    rw [hr]
    simp only [unsplitPure, if_neg hslash]
    cases q <;> cases f <;> simp [opt] at hreb ⊢ <;> rw [← hreb] <;> simp
  · rw [if_neg h2]
    simp only
    have hreb := fq_rebuild r
    obtain ⟨x, hx⟩ := fq_path_prefix r
    generalize (part 35 r) = P35 at hreb hx ⊢
    obtain ⟨a, f⟩ := P35
    generalize (part 63 a) = P63 at hreb hx ⊢
    obtain ⟨p, q⟩ := P63
    simp only at hreb hx
    have hp2 : ¬ p.take 2 = [47, 47] := by
      intro h; apply h2; rw [hx]; exact prefix_take2 p x h
    simp only [unsplitPure, if_neg hp2]
    cases q <;> cases f <;> simp [opt] at hreb ⊢ <;> exact hreb

theorem schemeOf_ne (u : Str) (s r : Str) (h : schemeOf u = (some s, r)) : s ≠ [] := by
  unfold schemeOf at h
  rcases hf : u.findIdx? (· == 58) with _ | i
  · rw [hf] at h; cases h
  · rw [hf] at h
    simp only at h
    split at h
    · next hc =>
      simp only [Prod.mk.injEq, Option.some.injEq] at h
      rw [← h.1]
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      have hlt := findIdx_lt hf
      intro e
      rw [List.map_eq_nil_iff, List.take_eq_nil_iff] at e
      rcases e with e | e
      · omega
      · subst e; simp at hlt
    · cases h

/-- `_urlunsplit` of `splitPure` is `normURL`. -/
theorem split_rebuild (u : Str) :
    unsplitPure (splitPure u true).1 (splitPure u true).2.1 (splitPure u true).2.2.1
      (splitPure u true).2.2.2.1 (splitPure u true).2.2.2.2 = normURL u := by
  unfold splitPure normURL
  rcases hs : schemeOf (removeUnsafe (lstripC0 u)) with ⟨_ | s, r⟩
  · simp only
    exact rest_rebuild r
  · simp only
    rw [unsplitPure_scheme s (schemeOf_ne _ s r hs), rest_rebuild r]

end PyLean.TextLibs.Url
