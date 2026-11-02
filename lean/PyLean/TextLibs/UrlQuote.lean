import PyLean.TextLibs.UrlModel

/-!
Lemmas about the list helpers of `UrlModel` and the codecs on ASCII text, used by the
quoting and query-string properties.
-/

namespace PyLean.TextLibs.Url

open PyLean

set_option linter.unusedSimpArgs false

/-! ## `splitOn` with a one-character separator -/

theorem splitOn_nil (sep : Str) : splitOn sep [] = [[]] := by
  rw [splitOn]

theorem splitOn_ne_nil (sep s : Str) : splitOn sep s ≠ [] := by
  cases s with
  | nil => simp [splitOn_nil]
  | cons c r =>
    rw [splitOn]
    split
    · simp
    · split <;> simp

theorem splitOn_one_hit (d : Nat) (r : Str) : splitOn [d] (d :: r) = [] :: splitOn [d] r := by
  rw [splitOn]
  simp [List.isPrefixOf]

/-- Put `c` in front of the first part. -/
def consHead (c : Nat) : List Str → List Str
  | [] => [[c]]
  | h :: t => (c :: h) :: t

theorem splitOn_one_miss (d c : Nat) (r : Str) (h : c ≠ d) :
    splitOn [d] (c :: r) = consHead c (splitOn [d] r) := by
  rw [splitOn]
  have : ¬ ([d] ≠ [] ∧ [d].isPrefixOf (c :: r) = true) := by
    simp [List.isPrefixOf]
    intro e
    exact h e.symm
  rw [if_neg this]
  cases splitOn [d] r <;> rfl

/-- Splitting a string with no `d` gives the string. -/
theorem splitOn_one_none (d : Nat) (s : Str) (h : d ∉ s) : splitOn [d] s = [s] := by
  induction s with
  | nil => exact splitOn_nil _
  | cons c r ih =>
    have hc : c ≠ d := fun e => h (e ▸ List.mem_cons_self)
    rw [splitOn_one_miss d c r hc, ih (fun m => h (List.mem_cons_of_mem _ m))]
    rfl

/-- Splitting `x ++ d :: rest` where `x` has no `d`. -/
theorem splitOn_one_prefix (d : Nat) (x rest : Str) (h : d ∉ x) :
    splitOn [d] (x ++ d :: rest) = x :: splitOn [d] rest := by
  induction x with
  | nil => exact splitOn_one_hit d rest
  | cons c x' ih =>
    have hc : c ≠ d := fun e => h (e ▸ List.mem_cons_self)
    rw [List.cons_append, splitOn_one_miss d c _ hc, ih (fun m => h (List.mem_cons_of_mem _ m))]
    rfl

/-- `d.join(l).split(d) == l` when no part contains `d`. -/
theorem splitOn_joinWith (d : Nat) (l : List Str) (hl : l ≠ []) (h : ∀ x ∈ l, d ∉ x) :
    splitOn [d] (joinWith [d] l) = l := by
  induction l with
  | nil => exact absurd rfl hl
  | cons x r ih =>
    cases r with
    | nil =>
      simp only [joinWith]
      exact splitOn_one_none d x (h x List.mem_cons_self)
    | cons y t =>
      have ih' := ih (by simp) (fun z hz => h z (List.mem_cons_of_mem _ hz))
      simp only [joinWith] at ih' ⊢
      rw [List.append_assoc, List.singleton_append, splitOn_one_prefix d x _ (h x List.mem_cons_self), ih']

/-! ## Unquoting is a left-to-right scan -/

/-- What `_unquote_impl` computes, read left to right: a `%` followed by two hex digits is
a byte, any other character is itself. -/
def scan : Str → Str
  | [] => []
  | c :: r =>
    if c = 37 then
      match r with
      | h1 :: h2 :: t =>
        if isHex h1 && isHex h2 then (hexVal h1 * 16 + hexVal h2) :: scan t
        else 37 :: scan (h1 :: h2 :: t)
      | [a] => 37 :: scan [a]
      | [] => [37]
    else c :: scan r
termination_by s => s.length
decreasing_by all_goals (try simp_wf) <;> (try simp_all) <;> omega

theorem scan_nil : scan [] = [] := by rw [scan.eq_def]

theorem scan_other (c : Nat) (r : Str) (h : c ≠ 37) : scan (c :: r) = c :: scan r := by
  rw [scan.eq_def (c :: r)]
  simp [h]

theorem scan_pct3 (h1 h2 : Nat) (t : Str) : scan (37 :: h1 :: h2 :: t) =
    if isHex h1 && isHex h2 then (hexVal h1 * 16 + hexVal h2) :: scan t
    else 37 :: scan (h1 :: h2 :: t) := by
  rw [scan.eq_def (37 :: h1 :: h2 :: t)]
  simp

theorem scan_pct0 : scan [37] = 37 :: scan [] := by
  rw [scan.eq_def [37]]
  simp [scan_nil]

theorem scan_pct1 (a : Nat) : scan [37, a] = 37 :: scan [a] := by
  rw [scan.eq_def [37, a]]
  simp

theorem isHex_ne_pct (c : Nat) (h : isHex c = true) : c ≠ 37 := by
  intro e; subst e; simp [isHex, isAsciiDigit] at h

/-- `bits[0]` followed by the loop over `bits[1:]`. -/
def joinBits : List Str → Str
  | first :: items => first ++ unquoteItems items
  | [] => []

theorem joinBits_consHead (c : Nat) (l : List Str) (hl : l ≠ []) :
    joinBits (consHead c l) = c :: joinBits l := by
  cases l with
  | nil => exact absurd rfl hl
  | cons x u => rfl

/-- The first bit after a `%`: `unquoteItems` looks at its first two characters. -/
theorem unquoteItems_split (r : Str) :
    unquoteItems (splitOn [37] r) =
      (match r with
        | h1 :: h2 :: t =>
          if isHex h1 && isHex h2 then (hexVal h1 * 16 + hexVal h2) :: joinBits (splitOn [37] t)
          else 37 :: joinBits (splitOn [37] r)
        | _ => 37 :: joinBits (splitOn [37] r)) := by
  match r with
  | [] => simp [splitOn_nil, unquoteItems, joinBits]
  | [a] =>
    by_cases ea : a = 37
    · subst ea; rw [splitOn_one_hit, splitOn_nil]; simp [unquoteItems, joinBits]
    · rw [splitOn_one_miss 37 a _ ea, splitOn_nil]; simp [consHead, unquoteItems, joinBits]
  | h1 :: h2 :: t =>
    simp only
    by_cases e1 : h1 = 37
    · subst e1
      have : (isHex 37 && isHex h2) = false := by simp [isHex, isAsciiDigit]
      rw [this, splitOn_one_hit]
      simp [unquoteItems, joinBits]
    · by_cases e2 : h2 = 37
      · subst e2
        have : (isHex h1 && isHex 37) = false := by simp [isHex, isAsciiDigit]
        rw [this, splitOn_one_miss 37 h1 _ e1, splitOn_one_hit]
        simp [consHead, unquoteItems, joinBits]
      · rw [splitOn_one_miss 37 h1 _ e1, splitOn_one_miss 37 h2 _ e2]
        have hne := splitOn_ne_nil [37] t
        generalize splitOn [37] t = l at hne ⊢
        cases l with
        | nil => exact absurd rfl hne
        | cons x u =>
          simp only [consHead, unquoteItems, joinBits]
          split <;> simp

theorem joinBits_split_lt : ∀ n (s : Str), s.length < n → joinBits (splitOn [37] s) = scan s
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, s, h =>
    match s with
    | [] => by simp [splitOn_nil, joinBits, unquoteItems, scan_nil]
    | c :: r => by
      by_cases hc : c = 37
      · subst hc
        rw [splitOn_one_hit]
        simp only [joinBits, List.nil_append]
        rw [unquoteItems_split]
        match r with
        | [] => simp [splitOn_nil, joinBits, unquoteItems, scan_pct0, scan_nil]
        | [a] =>
          simp only
          rw [scan_pct1, joinBits_split_lt n [a] (by simp at h ⊢; omega)]
        | h1 :: h2 :: t =>
          simp only
          rw [scan_pct3]
          split
          · rw [joinBits_split_lt n t (by simp at h ⊢; omega)]
          · rw [joinBits_split_lt n (h1 :: h2 :: t) (by simp at h ⊢; omega)]
      · rw [splitOn_one_miss 37 c r hc, scan_other c r hc, joinBits_consHead _ _ (splitOn_ne_nil _ _),
          joinBits_split_lt n r (by simp at h ⊢; omega)]

theorem joinBits_split (s : Str) : joinBits (splitOn [37] s) = scan s :=
  joinBits_split_lt (s.length + 1) s (by omega)

theorem joinWith_consHead (d c : Nat) (l : List Str) (hl : l ≠ []) :
    joinWith [d] (consHead c l) = c :: joinWith [d] l := by
  match l with
  | [x] => rfl
  | x :: y :: u => rfl

/-- `d.join(s.split(d)) == s`. -/
theorem joinWith_splitOn (d : Nat) (s : Str) : joinWith [d] (splitOn [d] s) = s := by
  induction s with
  | nil => rw [splitOn_nil]; rfl
  | cons c r ih =>
    by_cases hc : c = d
    · subst hc
      rw [splitOn_one_hit]
      have hne := splitOn_ne_nil [c] r
      revert ih
      generalize splitOn [c] r = l at hne ⊢
      intro ih
      match l, hne with
      | x :: u, _ => simp [joinWith] at ih ⊢; exact ih
    · rw [splitOn_one_miss d c r hc, joinWith_consHead _ _ _ (splitOn_ne_nil _ _), ih]

theorem splitOn_single {d : Nat} {s x : Str} (h : splitOn [d] s = [x]) : x = s := by
  have := joinWith_splitOn d s
  rw [h] at this
  exact this

/-- `_unquote_impl` on a `bytes`. -/
theorem unquoteImpl_bytes (x : Str) : unquoteImpl (.bytes x false) = .ok (scan x) := by
  rw [← joinBits_split]
  cases x with
  | nil => simp [unquoteImpl, Arg.truthy, splitOn_nil, joinBits, unquoteItems]; rfl
  | cons c r =>
    unfold unquoteImpl
    simp only [Arg.truthy, List.isEmpty_cons, Bool.not_false, Bool.false_eq_true, ite_false]
    rcases hsp : splitOn [37] (c :: r) with _ | ⟨x, _ | ⟨y, u⟩⟩
    · exact absurd hsp (splitOn_ne_nil _ _)
    · have := splitOn_single hsp
      subst this
      simp [hsp, joinBits, unquoteItems]; rfl
    · simp [hsp, joinBits]; rfl

end PyLean.TextLibs.Url
