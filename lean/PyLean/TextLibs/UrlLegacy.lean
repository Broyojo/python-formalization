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

/-- `rpart` at a decomposition `s = h ++ c :: p` with no `c` in `p`. -/
theorem rpart_of (c : Nat) (h p : Str) (hp : c ∉ p) : rpart c (h ++ c :: p) = (some h, p) := by
  unfold rpart
  have : (h ++ c :: p).reverse = p.reverse ++ c :: h.reverse := by simp
  rw [this, part_prefix c _ _ (by simpa using hp)]
  simp

/-- The message of `int(s)` beyond the default limit of 4300 digits
(`sys.int_info.default_max_str_digits`, Objects/longobject.c). -/
def digitLimitMsg (n : Nat) : String :=
  s!"Exceeds the limit (4300 digits) for integer string conversion: value has {n} digits; use sys.set_int_max_str_digits() to increase the limit"

/-- For every `str`: `_splituser` and `_splitquery`/`_splittag` cut at the last `@`, `?`, `#`;
`_splitpasswd` and `_splitvalue` at the first `:`, `=`; `_splitattr` splits at every `;` and joins
back. `_splitport` (the regular expression `(.*):([0-9]*)`, fully matched) cuts at the last `:`
when only ASCII digits follow it, giving the host and the digits (`None` for none), and otherwise
returns the input and `None`. `_splitnport` cuts at the last `:` too: without one it returns the
input and `defport`; with an empty port the host and `defport`; with ASCII digits their value
(`int(port)`, which refuses more than the documented 4300 digits with its `ValueError`); and with
anything else the host and `None`. Source: the docstrings of the helpers
(`splituser('user[:passwd]@host[:port]') --> 'user[:passwd]', 'host[:port]'`; `_splitnport`:
"Return given default port if no ':' found ... Return None if ':' but not a valid number"), and
the `int` limit of the docs' "Integer string conversion length limitation". -/
def LegacySplit : Prop :=
  ∀ s : Str,
    (match splituser s with
      | (some u, h) => s = u ++ 64 :: h ∧ 64 ∉ h
      | (none, h) => h = s ∧ 64 ∉ s) ∧
    CutLast 63 s (splitquery s) ∧ CutLast 35 s (splittag s) ∧
    CutFirst 58 s (splitpasswd s) ∧ CutFirst 61 s (splitvalue s) ∧
    (joinWith [59] ((splitattr s).1 :: (splitattr s).2) = s ∧
      ∀ x ∈ (splitattr s).1 :: (splitattr s).2, 59 ∉ x) ∧
    (58 ∉ s → splitport s = (s, none)) ∧
    (∀ h p, s = h ++ 58 :: p → 58 ∉ p →
      splitport s = if p.all isAsciiDigit = true then (h, if p = [] then none else some p) else (s, none)) ∧
    (∀ d : Int, 58 ∉ s → splitnport s d = .ok (s, some d)) ∧
    (∀ (d : Int) h p, s = h ++ 58 :: p → 58 ∉ p →
      splitnport s d =
        if p = [] then .ok (h, some d)
        else if p.all isAsciiDigit = true then
          (if p.length ≤ 4300 then .ok (h, some (digitsVal p : Int))
           else .error (.valueError (digitLimitMsg p.length)))
        else .ok (h, none))

theorem legacySplit_proven : LegacySplit := by
  intro s
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · intro h58
    simp [splitport, rpart_absent 58 s h58]
  · intro h p hs hp
    subst hs
    simp only [splitport, rpart_of 58 h p hp]
    by_cases hall : p.all isAsciiDigit = true
    · simp only [hall, ite_true]
      by_cases hp0 : p = [] <;> simp [hp0]
    · simp [hall]
  · intro d h58
    simp [splitnport, rpart_absent 58 s h58]
  · intro d h p hs hp
    subst hs
    simp only [splitnport, rpart_of 58 h p hp]
    by_cases hp0 : p = []
    · simp [hp0]
    · simp only [List.isEmpty_iff, hp0, ite_false]
      by_cases hall : p.all isAsciiDigit = true
      · simp only [hall, ite_true, intOfDigits]
        by_cases hl : p.length ≤ 4300
        · simp [hl, show ¬ p.length > 4300 by omega, Except.map]; rfl
        · simp [hl, show p.length > 4300 by omega, Except.map, digitLimitMsg]; rfl
      · simp [hall]

/-! ## `_splittype` and `_splithost` -/

theorem mem_takeWhile_p {p : Nat → Bool} {x : Nat} : ∀ {l : Str}, x ∈ l.takeWhile p → p x = true
  | [], h => by simp at h
  | c :: r, h => by
    rw [List.takeWhile_cons] at h
    split at h
    · next hc =>
      rcases List.mem_cons.1 h with rfl | h
      · exact hc
      · exact mem_takeWhile_p h
    · simp at h

theorem takeWhile_prefix (p : Nat → Bool) (a b : Str) (ha : ∀ c ∈ a, p c = true)
    (hb : ∀ x t, b = x :: t → p x = false) : (a ++ b).takeWhile p = a := by
  induction a with
  | nil =>
    cases b with
    | nil => rfl
    | cons x t => simp [List.takeWhile_cons, hb x t rfl]
  | cons c r ih =>
    simp only [List.cons_append, List.takeWhile_cons, ha c List.mem_cons_self, ite_true]
    rw [ih (fun x hx => ha x (List.mem_cons_of_mem _ hx))]

/-- For every `str` URL: `_splittype` (`re.match('([^/:]+):(.*)', url, re.DOTALL)`) returns the
lower-cased text before the first `:` and the rest when that text is non-empty and has no `/`,
and `(None, url)` when the URL has no such prefix. `_splithost` (`re.match('//([^/#?]*)(.*)',
url, re.DOTALL)`) returns, for a URL starting `//`, the text up to the next `/`, `#` or `?` and
the rest, with a `/` put before a rest that starts with `#` or `?`; and `(None, url)` for any other
URL. Source: the docstrings (`splittype('type:opaquestring') --> 'type', 'opaquestring'`,
`splithost('//host[:port]/path') --> 'host[:port]', '/path'`) and the regular expressions at
Lib/urllib/parse.py:1248 and :1269. -/
def TypeHostSplit : Prop :=
  ∀ url : Str,
    (∀ a b, url = a ++ 58 :: b → a ≠ [] → 47 ∉ a → 58 ∉ a →
      splittype url = (UnicodeObj.unicodeLower a).map (fun l => (some l, b))) ∧
    ((∀ a b, url = a ++ 58 :: b → a ≠ [] → 47 ∉ a → 58 ∉ a → False) → splittype url = .ok (none, url)) ∧
    (∀ h r, url = 47 :: 47 :: (h ++ r) → (∀ c ∈ h, c ≠ 47 ∧ c ≠ 35 ∧ c ≠ 63) →
      (∀ x t, r = x :: t → x = 47 ∨ x = 35 ∨ x = 63) →
      splithost url = (some h, match r with
        | [] => []
        | x :: t => if x = 47 then x :: t else 47 :: x :: t)) ∧
    (url.take 2 ≠ [47, 47] → splithost url = (none, url))

theorem typeHostSplit_proven : TypeHostSplit := by
  intro url
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b hu ha h47 h58
    subst hu
    have ht : (a ++ 58 :: b).takeWhile (fun c => c != 47 && c != 58) = a :=
      takeWhile_prefix _ a _ (fun c hc => by
        have : c ≠ 47 := fun e => h47 (e ▸ hc)
        have : c ≠ 58 := fun e => h58 (e ▸ hc)
        simp_all) (fun x t he => by cases he; simp)
    have hne : a.isEmpty = false := by cases a <;> simp_all
    simp only [splittype, ht, hne, Bool.not_false, List.drop_left', List.take_succ_cons,
      List.take_zero, Bool.true_and, ite_true]
    simp
  · intro hno
    simp only [splittype]
    split
    · next hc =>
      exfalso
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hc
      obtain ⟨hne, hd⟩ := hc
      generalize hrun : url.takeWhile (fun c => c != 47 && c != 58) = run at hne hd
      have hpre : url = run ++ url.drop run.length := by
        conv => lhs; rw [← List.take_append_drop run.length url]
        rw [← hrun, take_takeWhile]
      obtain ⟨x, t, hxt⟩ : ∃ x t, url.drop run.length = x :: t := by
        cases h : url.drop run.length with
        | nil => rw [h] at hd; simp at hd
        | cons x t => exact ⟨x, t, rfl⟩
      rw [hxt] at hd
      simp at hd
      subst hd
      apply hno run t (by rw [hxt] at hpre; exact hpre) (by simpa using hne)
      · intro m
        rw [← hrun] at m
        have := mem_takeWhile_p m
        simp at this
      · intro m
        rw [← hrun] at m
        have := mem_takeWhile_p m
        simp at this
    · rfl
  · intro h r hu hh hr
    subst hu
    have ht : (h ++ r).takeWhile (fun c => c != 47 && c != 35 && c != 63) = h :=
      takeWhile_prefix _ h r (fun c hc => by
        obtain ⟨a1, a2, a3⟩ := hh c hc
        simp [a1, a2, a3]) (fun x t he => by
          rcases hr x t he with rfl | rfl | rfl <;> simp [he])
    simp only [splithost, List.take_succ_cons, List.take_zero, ite_true, List.drop_succ_cons,
      List.drop_zero, ht, List.drop_left']
    cases r with
    | nil => simp
    | cons x t =>
      rcases hr x t rfl with rfl | rfl | rfl <;> simp
  · intro h2
    simp [splithost, h2]

end PyLean.TextLibs.Url
