import PyLean.UnicodeObj.FormatProps
import PyLean.UnicodeObj.FormatNumber
import PyLean.UnicodeObj.FormatPercent

/-!
Properties of float and complex formatting over the exact binary64 model.
-/

namespace PyLean.UnicodeObj

open PyLean

/-- `parse_number` splits the number with nothing lost: the digits, the decimal point, the
fraction and the remainder add up to its length, for every string. -/
def ParseNumberSplit : Prop :=
  ∀ s : Str,
    (parseNumber s).1 + (if (parseNumber s).2.1 = true then 1 else 0) + (parseNumber s).2.2.1 +
      (parseNumber s).2.2.2 = s.length

theorem take_drop_length (p : Nat → Bool) (l : List Nat) :
    (l.takeWhile p).length + (l.dropWhile p).length = l.length := by
  rw [← List.length_append, List.takeWhile_append_dropWhile]

theorem split_rest (rest : List Nat) :
    (if (parseRest rest).1 = true then 1 else 0) + (parseRest rest).2.1 + (parseRest rest).2.2 =
      rest.length := by
  simp only [parseRest]
  by_cases hd : (rest.head? == some 46) = true
  · simp only [hd, if_true]
    have h2 := take_drop_length pyDigit rest.tail
    cases rest with
    | nil => simp at hd
    | cons x xs =>
      simp only [List.tail_cons, List.length_cons] at *
      omega
  · simp only [hd, if_false, Bool.false_eq_true]
    have h2 := take_drop_length pyDigit rest
    omega

theorem parseNumberSplit_proven : ParseNumberSplit := by
  intro s
  have h1 := take_drop_length pyDigit s
  have h2 := split_rest (s.dropWhile pyDigit)
  show (s.takeWhile pyDigit).length + (if (parseRest (s.dropWhile pyDigit)).1 = true then 1 else 0) +
    (parseRest (s.dropWhile pyDigit)).2.1 + (parseRest (s.dropWhile pyDigit)).2.2 = s.length
  omega

/-- `format(v, '')` is `str(v)` for an int, and `format(s, '')` is `s`: the empty-spec branch
of the dispatchers, which goes through `format_obj` for a subclass. -/
def FormatEmptySpec : Prop :=
  (∀ (v : Int) (name : String) (shown : Str),
    formatLongAdvanced v name [] shown = .ok (some shown)) ∧
  (∀ s : Str, formatStrAdvanced s [] = .ok s)

theorem formatEmptySpec_proven : FormatEmptySpec :=
  ⟨fun _ _ _ => rfl, fun _ => rfl⟩

/-! ## The text `parse_number` measures -/

theorem take_tw (p : Nat → Bool) (s : List Nat) : s.take (s.takeWhile p).length = s.takeWhile p := by
  induction s with
  | nil => rfl
  | cons a t ih =>
    simp only [List.takeWhile_cons]
    split <;> simp [ih]

theorem drop_tw (p : Nat → Bool) (s : List Nat) : s.drop (s.takeWhile p).length = s.dropWhile p := by
  induction s with
  | nil => rfl
  | cons a t ih =>
    simp only [List.takeWhile_cons, List.dropWhile_cons]
    split <;> simp [ih]

/-- What follows the integer digits and the decimal point. -/
def restOf (s : Str) : Str :=
  let d := s.dropWhile pyDigit
  if (d.head? == some 46) = true then d.tail else d

theorem splitNumber_eq (s : Str) :
    splitNumber s = (s.takeWhile pyDigit, (s.dropWhile pyDigit).head? == some 46,
      (restOf s).takeWhile pyDigit, (restOf s).dropWhile pyDigit) := by
  simp only [splitNumber, parseNumber, parseRest, take_tw, drop_tw, restOf]

theorem splitNumber_join (s : Str) :
    s.takeWhile pyDigit ++ (if ((s.dropWhile pyDigit).head? == some 46) = true then [46] else []) ++
      (restOf s).takeWhile pyDigit ++ (restOf s).dropWhile pyDigit = s := by
  have h0 : s.takeWhile pyDigit ++ s.dropWhile pyDigit = s := List.takeWhile_append_dropWhile
  have h1 : (restOf s).takeWhile pyDigit ++ (restOf s).dropWhile pyDigit = restOf s :=
    List.takeWhile_append_dropWhile
  rw [List.append_assoc, h1, List.append_assoc]
  suffices h : (if ((s.dropWhile pyDigit).head? == some 46) = true then [46] else []) ++ restOf s =
      s.dropWhile pyDigit by rw [h, h0]
  unfold restOf
  cases hd : s.dropWhile pyDigit with
  | nil => simp
  | cons a t => by_cases ha : a = 46 <;> simp [ha]

/-! ## The grouping loops -/

/-- What the loop's count means: it is the length of what the loop wrote. -/
theorem groupLoop_count (grouping : List Nat) (sep : Str) :
    ∀ (fuel i prev : Nat) (useSep : Bool) (rem mw : Int) (rev : List Nat) (count : Nat)
      (out : List Nat) (it n : Nat) (o : List Nat) (it' : Nat),
      groupLoop grouping sep fuel i prev useSep rem mw rev count out it = .ok (n, o, it') →
      rem = rev.length → o.length + count = n + out.length := by
  intro fuel
  induction fuel with
  | zero =>
    intro i prev useSep rem mw rev count out it n o it' h _
    simp [groupLoop] at h
  | succ fuel ih =>
    intro i prev useSep rem mw rev count out it n o it' h hrem
    simp only [groupLoop] at h
    generalize groupNext grouping i prev = g at h
    obtain ⟨len0, i', prev'⟩ := g
    simp only at h
    split at h
    · obtain ⟨len, hlen⟩ : ∃ len : Int, len = min (len0 : Int) (max (max rem mw) 1) := ⟨_, rfl⟩
      rw [← hlen] at h
      obtain ⟨z, hz⟩ : ∃ z : Int, z = max 0 (len - rem) := ⟨_, rfl⟩
      obtain ⟨k, hk⟩ : ∃ k : Int, k = max 0 (min rem len) := ⟨_, rfl⟩
      rw [← hz, ← hk] at h
      have hkr : k.toNat ≤ rev.length := by omega
      simp only [groupPiece] at h
      have hlenout : (List.replicate z.toNat 48 ++ (rev.take k.toNat).reverse ++
          (if useSep = true then sep else []) ++ out).length =
          z.toNat + k.toNat + (if useSep = true then sep.length else 0) + out.length := by
        cases useSep <;> simp [List.length_take, Nat.min_eq_left hkr] <;> omega
      split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        omega
      · have := ih _ _ true (rem - k) _ (rev.drop k.toNat) _ _ _ n o it' h
          (by rw [List.length_drop]; omega)
        omega
    · obtain ⟨len, hlen⟩ : ∃ len : Int, len = max (max rem mw) 1 := ⟨_, rfl⟩
      rw [← hlen] at h
      obtain ⟨z, hz⟩ : ∃ z : Int, z = max 0 (len - rem) := ⟨_, rfl⟩
      obtain ⟨k, hk⟩ : ∃ k : Int, k = max 0 (min rem len) := ⟨_, rfl⟩
      rw [← hz, ← hk] at h
      have hkr : k.toNat ≤ rev.length := by omega
      simp only [groupPiece, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      cases useSep <;> simp [List.length_take, Nat.min_eq_left hkr] <;> omega

theorem groupLoopFwd_count (grouping : List Nat) (sep : Str) :
    ∀ (fuel i prev : Nat) (useSep : Bool) (rem mw : Int) (ds : Str) (count : Nat)
      (out : Str) (n : Nat) (o : Str),
      groupLoopFwd grouping sep fuel i prev useSep rem mw ds count out = .ok (n, o) →
      rem = ds.length → o.length + count = n + out.length := by
  intro fuel
  induction fuel with
  | zero =>
    intro i prev useSep rem mw ds count out n o h _
    simp [groupLoopFwd] at h
  | succ fuel ih =>
    intro i prev useSep rem mw ds count out n o h hrem
    simp only [groupLoopFwd] at h
    generalize groupNext grouping i prev = g at h
    obtain ⟨len0, i', prev'⟩ := g
    simp only at h
    split at h
    · obtain ⟨len, hlen⟩ : ∃ len : Int, len = min (len0 : Int) (max (max rem mw) 1) := ⟨_, rfl⟩
      rw [← hlen] at h
      obtain ⟨z, hz⟩ : ∃ z : Int, z = max 0 (len - rem) := ⟨_, rfl⟩
      obtain ⟨k, hk⟩ : ∃ k : Int, k = max 0 (min rem len) := ⟨_, rfl⟩
      rw [← hz, ← hk] at h
      have hkr : k.toNat ≤ ds.length := by omega
      simp only [groupPieceFwd] at h
      have hlenout : (out ++ (if useSep = true then sep else []) ++ ds.take k.toNat ++
          List.replicate z.toNat 48).length =
          z.toNat + k.toNat + (if useSep = true then sep.length else 0) + out.length := by
        cases useSep <;> simp [List.length_take, Nat.min_eq_left hkr] <;> omega
      split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        omega
      · have := ih _ _ true (rem - k) _ (ds.drop k.toNat) _ _ n o h
          (by rw [List.length_drop]; omega)
        omega
    · obtain ⟨len, hlen⟩ : ∃ len : Int, len = max (max rem mw) 1 := ⟨_, rfl⟩
      rw [← hlen] at h
      obtain ⟨z, hz⟩ : ∃ z : Int, z = max 0 (len - rem) := ⟨_, rfl⟩
      obtain ⟨k, hk⟩ : ∃ k : Int, k = max 0 (min rem len) := ⟨_, rfl⟩
      rw [← hz, ← hk] at h
      have hkr : k.toNat ≤ ds.length := by omega
      simp only [groupPieceFwd, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      cases useSep <;> simp [List.length_take, Nat.min_eq_left hkr] <;> omega

def PendingBinary64 : Prop := False

end PyLean.UnicodeObj
