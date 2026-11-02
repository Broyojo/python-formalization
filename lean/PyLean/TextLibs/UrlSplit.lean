import PyLean.TextLibs.UrlQuery

/-!
The pure shape of `_urlsplit` (what it returns when no check raises) and of `_urlunsplit` on
strings, with the list lemmas the round-trip proofs use.
-/

namespace PyLean.TextLibs.Url

open PyLean

set_option linter.unusedSimpArgs false

/-! ## `partition` -/

theorem part_cons (c x : Nat) (r : Str) : part c (x :: r) =
    if x = c then ([], some r) else (x :: (part c r).1, (part c r).2) := by
  rw [part]; simp

theorem part_some : ∀ {c : Nat} {s a b : Str}, part c s = (a, some b) → s = a ++ c :: b ∧ c ∉ a
  | c, [], a, b, h => by simp [part] at h
  | c, x :: r, a, b, h => by
    rw [part_cons] at h
    by_cases hx : x = c
    · rw [if_pos hx] at h; cases h; exact ⟨by rw [hx]; rfl, List.not_mem_nil⟩
    · rw [if_neg hx] at h
      have h1 : a = x :: (part c r).1 := (Prod.mk.inj h).1.symm
      have h2 : (part c r).2 = some b := (Prod.mk.inj h).2
      have ih := part_some (c := c) (s := r) (a := (part c r).1) (b := b) (Prod.ext rfl h2)
      subst h1
      refine ⟨congrArg (List.cons x) ih.1, ?_⟩
      simp only [List.mem_cons, not_or]; exact ⟨fun e => hx e.symm, ih.2⟩

theorem part_none : ∀ {c : Nat} {s a : Str}, part c s = (a, none) → a = s ∧ c ∉ s
  | c, [], a, h => by simp [part] at h; simp [h]
  | c, x :: r, a, h => by
    rw [part_cons] at h
    by_cases hx : x = c
    · rw [if_pos hx] at h; cases h
    · rw [if_neg hx] at h
      have h1 : a = x :: (part c r).1 := (Prod.mk.inj h).1.symm
      have h2 : (part c r).2 = none := (Prod.mk.inj h).2
      have ih := part_none (c := c) (s := r) (a := (part c r).1) (Prod.ext rfl h2)
      subst h1
      refine ⟨by simp [ih.1], ?_⟩
      simp only [List.mem_cons, not_or]; exact ⟨fun e => hx e.symm, ih.2⟩

theorem part_cases (c : Nat) (s : Str) :
    (∃ a b, part c s = (a, some b) ∧ s = a ++ c :: b ∧ c ∉ a) ∨ (part c s = (s, none) ∧ c ∉ s) := by
  rcases h : part c s with ⟨a, _ | b⟩
  · exact Or.inr (by have := part_none h; rw [this.1]; exact ⟨rfl, this.2⟩)
  · exact Or.inl ⟨a, b, rfl, part_some h⟩

/-! ## `_splitnetloc` -/

def isDelim (c : Nat) : Bool := c == 47 || c == 63 || c == 35

def omin : Option Nat → Option Nat → Option Nat
  | none, b => b
  | a, none => a
  | some a, some b => some (min a b)

theorem findIdx_or (d : Str) (p q : Nat → Bool) :
    omin (d.findIdx? p) (d.findIdx? q) = d.findIdx? (fun x => p x || q x) := by
  induction d with
  | nil => rfl
  | cons x r ih =>
    simp only [List.findIdx?_cons]
    rw [← ih]
    cases hp : p x <;> cases hq : q x <;> cases List.findIdx? p r <;> cases List.findIdx? q r <;>
      simp [omin] <;> omega

theorem findIdx_lt {p : Nat → Bool} {d : Str} {j : Nat} (h : d.findIdx? p = some j) : j < d.length := by
  induction d generalizing j with
  | nil => simp at h
  | cons x r ih =>
    simp only [List.findIdx?_cons] at h
    split at h
    · simp at h; subst h; simp
    · cases hr : r.findIdx? p with
      | none => simp [hr] at h
      | some j' => simp [hr] at h; subst h; have := ih hr; simp; omega

theorem findIdx_takeWhile {p : Nat → Bool} {d : Str} {j : Nat} (h : d.findIdx? p = some j) :
    (d.takeWhile (fun c => !p c)).length = j := by
  induction d generalizing j with
  | nil => simp at h
  | cons x r ih =>
    simp only [List.findIdx?_cons] at h
    by_cases hx : p x = true
    · simp [hx] at h; subst h; simp [List.takeWhile_cons, hx]
    · cases hr : r.findIdx? p with
      | none => simp [hx, hr] at h
      | some j' => simp [hx, hr] at h; subst h; simp [List.takeWhile_cons, hx, ih hr]

theorem findIdx_none_takeWhile {p : Nat → Bool} {d : Str} (h : d.findIdx? p = none) :
    (d.takeWhile (fun c => !p c)).length = d.length := by
  induction d with
  | nil => rfl
  | cons x r ih =>
    simp only [List.findIdx?_cons] at h
    by_cases hx : p x = true
    · simp [hx] at h
    · cases hr : r.findIdx? p with
      | none => simp [List.takeWhile_cons, hx, ih hr]
      | some j' => simp [hx, hr] at h

theorem take_takeWhile (p : Nat → Bool) : ∀ d : Str, d.take (d.takeWhile p).length = d.takeWhile p
  | [] => rfl
  | x :: r => by by_cases h : p x = true <;> simp [List.takeWhile_cons, h, take_takeWhile p r]

theorem drop_takeWhile (p : Nat → Bool) : ∀ d : Str, d.drop (d.takeWhile p).length = d.dropWhile p
  | [] => rfl
  | x :: r => by
    by_cases h : p x = true <;> simp [List.takeWhile_cons, List.dropWhile_cons, h, drop_takeWhile p r]

def mn (x : Nat) : Option Nat → Nat
  | none => x
  | some j => min x (j + 2)

theorem mn3 (L : Nat) (a b c : Option Nat) : mn (mn (mn L a) b) c = mn L (omin (omin a b) c) := by
  cases a <;> cases b <;> cases c <;> simp only [mn, omin] <;> omega

/-- `_splitnetloc(url, 2)`: the part after `//` up to the first `/`, `?` or `#`, and the rest. -/
theorem splitnetloc_eq (url : Str) (h : url.take 2 = [47, 47]) :
    splitnetloc url 2 = ((url.drop 2).takeWhile (fun c => !isDelim c),
      (url.drop 2).dropWhile (fun c => !isDelim c)) := by
  obtain ⟨d, rfl⟩ : ∃ d, url = [47, 47] ++ d := ⟨url.drop 2, by rw [← h, List.take_append_drop]⟩
  have hd : ([47, 47] ++ d).drop 2 = d := rfl
  have hstep : ∀ (dl c : Nat), minFound dl ((d.findIdx? (· == c)).map (· + 2)) =
      mn dl (d.findIdx? (· == c)) := by
    intro dl c; cases d.findIdx? (· == c) <;> rfl
  have hor : omin (omin (d.findIdx? (· == 47)) (d.findIdx? (· == 63))) (d.findIdx? (· == 35)) =
      d.findIdx? isDelim := by
    rw [findIdx_or, findIdx_or]; rfl
  have hlen : ([47, 47] ++ d).length = d.length + 2 := by
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have hfold : mn (d.length + 2) (d.findIdx? isDelim) = (d.takeWhile (fun c => !isDelim c)).length + 2 := by
    rcases hj : d.findIdx? isDelim with _ | j
    · simp [mn, findIdx_none_takeWhile hj]
    · have := findIdx_lt hj
      simp only [mn, findIdx_takeWhile hj]; omega
  unfold splitnetloc
  simp only [hd, hstep, List.foldl_cons, List.foldl_nil, mn3, hor, hlen, hfold]
  show ((List.take (_ + 2) (47 :: 47 :: d)).drop 2, List.drop (_ + 2) (47 :: 47 :: d)) = _
  simp only [List.take_succ_cons, List.drop_succ_cons, List.drop_zero, List.drop_one, List.tail_cons,
    take_takeWhile, drop_takeWhile]

/-! ## `_urlunsplit` on strings -/

/-- `_urlunsplit` when every component is a `str` or `None`. -/
def unsplitPure (scheme netloc : Option Str) (url : Str) (query fragment : Option Str) : Str :=
  let url := match netloc with
    | some n => [47, 47] ++ n ++ (if url ≠ [] ∧ url.take 1 ≠ [47] then 47 :: url else url)
    | none => if url.take 2 = [47, 47] then [47, 47] ++ url else url
  let url := match scheme with
    | some s => if s ≠ [] then s ++ [58] ++ url else url
    | none => url
  let url := match query with
    | some q => url ++ [63] ++ q
    | none => url
  match fragment with
  | some f => url ++ [35] ++ f
  | none => url

end PyLean.TextLibs.Url
