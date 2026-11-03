import PyLean.TextLibs.UrlSpecUnquote

/-!
The netloc attributes of a `str` result, written out: where `_userinfo` and `_hostinfo` cut the
netloc, and what `hostname` lower-cases. With `NetlocTwin` (the `bytes` mixin agrees with these
on `bytes` netlocs) this pins both mixins.
-/

namespace PyLean.TextLibs.Url

open PyLean

set_option linter.unusedSimpArgs false

/-- `hi` is the text after the last `@` of the netloc `n` (all of `n` when it has none). -/
def AfterAt (n hi : Str) : Prop := (64 ∉ n ∧ hi = n) ∨ ∃ ui, n = ui ++ 64 :: hi ∧ 64 ∉ hi

theorem afterAt_rpart (n hi : Str) (h : AfterAt n hi) : (rpart 64 n).2 = hi := by
  rcases h with ⟨h64, rfl⟩ | ⟨ui, rfl, h64⟩
  · rw [rpart_absent 64 _ h64]
  · rw [rpart_of 64 ui hi h64]

/-- For every `str` result (`SplitResult`, `ParseResult`) and every netloc:
`username` and `password` are `None` without a netloc or without `@`; otherwise they come from the
text before the last `@`: the username up to its first `:` and the password after it (`None`
without a `:`). `_hostinfo` reads the text after the last `@`: without `[`, the host is the text
up to its first `:` and the port the rest; with `[`, the host is the text after the first `[` up
to the next `]` (or to the end), and the port is the text after the first `:` that follows the
`]`; an empty port is `None`. `hostname` is `None` for an empty host, and otherwise the host
with the part before its first `%` lower-cased by `str.lower()` and the zone after it kept as
it is. Source: the docs of `urlsplit` (the `username`, `password`, `hostname` attributes; "Scoped
IPv6 address may have zone info, which must not be lowercased", :190-191), and RFC 3986 section
3.2 (`[ userinfo "@" ] host [ ":" port ]`, `userinfo` read as `user:password`). -/
def NetlocAttrSpec : Prop :=
  ∀ (fields : List (Option Str)) (k : Option Bool),
    (fields.getD 1 none = none →
      username { fields, isBytes := false, keep := k } = none ∧
      password { fields, isBytes := false, keep := k } = none ∧
      hostname { fields, isBytes := false, keep := k } = .ok none ∧
      port { fields, isBytes := false, keep := k } = .ok none) ∧
    (∀ n, fields.getD 1 none = some n →
      (64 ∉ n → username { fields, isBytes := false, keep := k } = none ∧
        password { fields, isBytes := false, keep := k } = none) ∧
      (∀ ui hi, n = ui ++ 64 :: hi → 64 ∉ hi →
        (58 ∉ ui → username { fields, isBytes := false, keep := k } = some ui ∧
          password { fields, isBytes := false, keep := k } = none) ∧
        (∀ u p, ui = u ++ 58 :: p → 58 ∉ u →
          username { fields, isBytes := false, keep := k } = some u ∧
          password { fields, isBytes := false, keep := k } = some p)) ∧
      (∀ hi, AfterAt n hi →
        (91 ∉ hi → 58 ∉ hi → hostinfoS (some n) = (some hi, none)) ∧
        (91 ∉ hi → ∀ h p, hi = h ++ 58 :: p → 58 ∉ h →
          hostinfoS (some n) = (some h, if p = [] then none else some p)) ∧
        (∀ x y, hi = x ++ 91 :: y → 91 ∉ x →
          (93 ∉ y → hostinfoS (some n) = (some y, none)) ∧
          (∀ h z, y = h ++ 93 :: z → 93 ∉ h →
            (58 ∉ z → hostinfoS (some n) = (some h, none)) ∧
            (∀ w p, z = w ++ 58 :: p → 58 ∉ w →
              hostinfoS (some n) = (some h, if p = [] then none else some p))))) ∧
      (∀ h, (hostinfoS (some n)).1 = some h →
        (h = [] → hostname { fields, isBytes := false, keep := k } = .ok none) ∧
        (h ≠ [] → 37 ∉ h → hostname { fields, isBytes := false, keep := k } = (UnicodeObj.unicodeLower h).map some) ∧
        (∀ a z, h = a ++ 37 :: z → 37 ∉ a →
          hostname { fields, isBytes := false, keep := k } = (UnicodeObj.unicodeLower a).map (fun l => some (l ++ 37 :: z)))))

theorem netlocAttrSpec_proven : NetlocAttrSpec := by
  intro fields k
  refine ⟨?_, ?_⟩
  · intro hn
    simp only [username, password, hostname, port, Res.netloc, Bool.false_eq_true, ite_false, hn]
    simp [userinfoS, hostinfoS, portOf]
  · intro n hn
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h64
      simp only [username, password, Res.netloc, Bool.false_eq_true, ite_false, hn]
      simp [userinfoS, rpart_absent 64 n h64]
    · intro ui hi hu h64
      subst hu
      refine ⟨?_, ?_⟩
      · intro h58
        simp only [username, password, Res.netloc, Bool.false_eq_true, ite_false, hn]
        simp [userinfoS, rpart_of 64 ui hi h64, part_absent 58 ui h58]
      · intro u p hup h58
        subst hup
        simp only [username, password, Res.netloc, Bool.false_eq_true, ite_false, hn]
        simp only [userinfoS]
        rw [rpart_of 64 (u ++ 58 :: p) hi h64]
        simp [part_prefix 58 u p h58]
    · intro hi hhi
      have hr := afterAt_rpart n hi hhi
      refine ⟨?_, ?_, ?_⟩
      · intro h91 h58
        simp [hostinfoS, hr, part_absent 91 hi h91, part_absent 58 hi h58]
      · intro h91 h p hs h58
        subst hs
        simp only [hostinfoS, hr, part_absent 91 _ h91, part_prefix 58 h p h58, Option.getD_some]
        by_cases hp : p = [] <;> simp [hp]
      · intro x y hs h91
        subst hs
        refine ⟨?_, ?_⟩
        · intro h93
          simp [hostinfoS, hr, part_prefix 91 x y h91, part_absent 93 y h93, part]
        · intro h z hy h93
          subst hy
          refine ⟨?_, ?_⟩
          · intro h58
            simp [hostinfoS, hr, part_prefix 91 x _ h91, part_prefix 93 h z h93, part_absent 58 z h58]
          · intro w p hz h58
            subst hz
            simp only [hostinfoS, hr, part_prefix 91 x _ h91, part_prefix 93 h _ h93, Option.getD_some,
              part_prefix 58 w p h58]
            by_cases hp : p = [] <;> simp [hp]
    · intro h hh
      refine ⟨?_, ?_, ?_⟩
      · intro he
        subst he
        simp only [hostname, Res.netloc, Bool.false_eq_true, ite_false, hn, hh]
        simp
      · intro hne h37
        have hne' : h.isEmpty = false := by cases h <;> simp_all
        simp only [hostname, Res.netloc, hn, hh, Bool.false_eq_true, ite_false, hne',
          part_absent 37 h h37]
        cases UnicodeObj.unicodeLower h <;> simp [Except.map]
      · intro a z hs h37
        subst hs
        have hne' : (a ++ 37 :: z).isEmpty = false := by simp
        simp only [hostname, Res.netloc, hn, hh, Bool.false_eq_true, ite_false, hne',
          part_prefix 37 a z h37]

end PyLean.TextLibs.Url
