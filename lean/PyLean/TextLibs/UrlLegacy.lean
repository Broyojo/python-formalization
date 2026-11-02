import PyLean.TextLibs.UrlTwins

/-!
The private split helpers of `Lib/urllib/parse.py` (:1287-1407), which `urllib.request` still
uses: each one cuts its argument at the right occurrence of its delimiter and loses nothing.
-/

namespace PyLean.TextLibs.Url

open PyLean

set_option linter.unusedSimpArgs false

theorem rpart_some {c : Nat} {s a b : Str} (h : rpart c s = (some a, b)) : s = a ++ c :: b ∧ c ∉ b := by
  unfold rpart at h
  rcases hp : part c s.reverse with ⟨x, _ | y⟩
  · rw [hp] at h; simp at h
  · rw [hp] at h
    simp only [Prod.mk.injEq, Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨he, hn⟩ := part_some hp
    refine ⟨?_, by simpa using hn⟩
    have := congrArg List.reverse he
    simp at this
    rw [this]

theorem rpart_none {c : Nat} {s b : Str} (h : rpart c s = (none, b)) : b = s ∧ c ∉ s := by
  unfold rpart at h
  rcases hp : part c s.reverse with ⟨x, _ | y⟩
  · rw [hp] at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    obtain ⟨he, hn⟩ := part_none hp
    subst he
    exact ⟨by simp, by simpa using hn⟩
  · rw [hp] at h; simp at h

theorem splitOn_parts (d : Nat) (s : Str) : ∀ x ∈ splitOn [d] s, d ∉ x := by
  induction s with
  | nil => simp [splitOn_nil]
  | cons c r ih =>
    by_cases hc : c = d
    · subst hc
      rw [splitOn_one_hit]
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · simp
      · exact ih x hx
    · rw [splitOn_one_miss d c r hc]
      have hne := splitOn_ne_nil [d] r
      revert ih
      generalize splitOn [d] r = l at hne ⊢
      intro ih
      match l, hne with
      | y :: t, _ =>
        intro x hx
        simp only [consHead, List.mem_cons] at hx
        rcases hx with rfl | hx
        · simp only [List.mem_cons, not_or]; exact ⟨fun e => hc e.symm, ih y (by simp)⟩
        · exact ih x (by simp [hx])

/-- `x` cut at `c`: the parts and the delimiter give `x` back, and `c` does not occur on the side
the helper searches from. -/
def CutLast (c : Nat) (s : Str) : Str × Option Str → Prop
  | (p, some q) => s = p ++ c :: q ∧ c ∉ q
  | (p, none) => p = s ∧ c ∉ s

def CutFirst (c : Nat) (s : Str) : Str × Option Str → Prop
  | (p, some q) => s = p ++ c :: q ∧ c ∉ p
  | (p, none) => p = s ∧ c ∉ s

/-- For every `str`: `_splituser` and `_splitquery`/`_splittag` cut at the last `@`, `?`, `#`;
`_splitpasswd` and `_splitvalue` at the first `:`, `=`; `_splitattr` splits at every `;` and joins
back; `_splitport` returns a non-empty run of ASCII digits after the last `:`, or the input (less
a trailing `:`) and `None`; and `_splitnport` reads that port as an int. In each case nothing is
lost. Source: the docstrings of the helpers (`splituser('user[:passwd]@host[:port]') -->
'user[:passwd]', 'host[:port]'` and the like), and (a) `_splitnport` against `_splitport`. -/
def LegacySplit : Prop :=
  ∀ s : Str,
    (match splituser s with
      | (some u, h) => s = u ++ 64 :: h ∧ 64 ∉ h
      | (none, h) => h = s ∧ 64 ∉ s) ∧
    CutLast 63 s (splitquery s) ∧ CutLast 35 s (splittag s) ∧
    CutFirst 58 s (splitpasswd s) ∧ CutFirst 61 s (splitvalue s) ∧
    (joinWith [59] ((splitattr s).1 :: (splitattr s).2) = s ∧
      ∀ x ∈ (splitattr s).1 :: (splitattr s).2, 59 ∉ x) ∧
    (match splitport s with
      | (h, some p) => s = h ++ 58 :: p ∧ p ≠ [] ∧ p.all isAsciiDigit = true
      | (h, none) => h = s ∨ s = h ++ [58]) ∧
    (∀ h p d, splitport s = (h, some p) → p.length ≤ 4300 → splitnport s d = .ok (h, some (digitsVal p)))

theorem legacySplit_proven : LegacySplit := by
  intro s
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold splituser
    rcases hr : rpart 64 s with ⟨_ | u, h⟩
    · exact rpart_none hr
    · exact rpart_some hr
  · unfold splitquery
    rcases hr : rpart 63 s with ⟨_ | p, q⟩
    · exact rpart_none hr |>.2 |> fun h => ⟨rfl, h⟩
    · exact rpart_some hr
  · unfold splittag
    rcases hr : rpart 35 s with ⟨_ | p, q⟩
    · exact rpart_none hr |>.2 |> fun h => ⟨rfl, h⟩
    · exact rpart_some hr
  · unfold splitpasswd
    rcases hp : part 58 s with ⟨u, _ | p⟩
    · exact part_none hp
    · exact part_some hp
  · unfold splitvalue
    rcases hp : part 61 s with ⟨u, _ | p⟩
    · exact part_none hp
    · exact part_some hp
  · unfold splitattr
    have hj := joinWith_splitOn 59 s
    have hn := splitOn_parts 59 s
    have hne := splitOn_ne_nil [59] s
    generalize splitOn [59] s = l at hj hn hne
    match l, hne with
    | w :: r, _ => exact ⟨hj, hn⟩
  · rcases hr : rpart 58 s with ⟨_ | h, p⟩
    · have e : splitport s = (s, none) := by simp [splitport, hr]
      rw [e]; exact Or.inl rfl
    · obtain ⟨he, _⟩ := rpart_some hr
      by_cases hall : p.all isAsciiDigit = true
      · by_cases hp : p = []
        · have e : splitport s = (h, none) := by simp [splitport, hr, hall, hp]
          rw [e]; subst hp; exact Or.inr he
        · have e : splitport s = (h, some p) := by simp [splitport, hr, hall, hp]
          rw [e]; exact ⟨he, hp, hall⟩
      · have e : splitport s = (s, none) := by simp [splitport, hr, hall]
        rw [e]; exact Or.inl rfl
  · intro h p d hsp hlen
    rcases hr : rpart 58 s with ⟨_ | h', p'⟩
    · simp [splitport, hr] at hsp
    · by_cases hall : p'.all isAsciiDigit = true
      · by_cases hp : p' = []
        · simp [splitport, hr, hall, hp] at hsp
        · simp [splitport, hr, hall, hp] at hsp
          obtain ⟨rfl, rfl⟩ := hsp
          simp [splitnport, hr, hp, hall, intOfDigits, show ¬ p'.length > 4300 by omega, Except.map]
          rfl
      · simp [splitport, hr, hall] at hsp

end PyLean.TextLibs.Url
