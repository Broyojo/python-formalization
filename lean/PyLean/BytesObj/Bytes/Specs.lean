import PyLean.BytesObj.Bytes.ByteArrayProps4
import PyLean.StrSearch

/-!
What the `bytes` methods compute, independently of how. The twin and round-trip properties say
two functions agree, or that one undoes the other, and a wrong pair can satisfy those; the
statements here pin each function by itself.
-/

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

/-! ## Classes -/

/-- The tables behind `isspace`, `isalpha`, `isdigit`, `isalnum`, Python/pyctype.c, in bytes. A class
test on a byte string is "non-empty and every byte in the class", for these sets. -/
def ClassTables : Prop :=
  ∀ s : Seq,
    bytesIsSpace s = (decide (s ≠ []) && s.all fun c => decide (c = 32 ∨ (9 ≤ c ∧ c ≤ 13))) ∧
    bytesIsAlpha s = (decide (s ≠ []) && s.all fun c => decide ((65 ≤ c ∧ c ≤ 90) ∨ (97 ≤ c ∧ c ≤ 122))) ∧
    bytesIsDigit s = (decide (s ≠ []) && s.all fun c => decide (48 ≤ c ∧ c ≤ 57)) ∧
    bytesIsAlnum s = (decide (s ≠ []) &&
      s.all fun c => decide ((65 ≤ c ∧ c ≤ 90) ∨ (97 ≤ c ∧ c ≤ 122) ∨ (48 ≤ c ∧ c ≤ 57)))

theorem classTables_proven : ClassTables := by
  intro s
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [bytesIsSpace, classShortcut_proven]
    congr 2
    funext c
    apply Bool.eq_iff_iff.mpr
    simp [isSpaceC, byteSpace]
    omega
  · rw [bytesIsAlpha, classShortcut_proven]
    congr 2
  · rw [bytesIsDigit, classShortcut_proven]
    congr 2
  · rw [bytesIsAlnum, classShortcut_proven]
    congr 2
    funext c
    apply Bool.eq_iff_iff.mpr
    simp [isAlnumC, isAlphaC, isDigitC, isUpperC, isLowerC]
    omega

/-! ## Case -/

/-- A byte with a case. -/
def casedC (c : Nat) : Bool := isUpperC c || isLowerC c

theorem toLower_cases (c : Nat) :
    ((65 ≤ c ∧ c ≤ 90) ∧ toLowerC c = c + 32) ∨ (¬ (65 ≤ c ∧ c ≤ 90) ∧ toLowerC c = c) := by
  by_cases h : 65 ≤ c ∧ c ≤ 90
  · exact Or.inl ⟨h, if_pos h⟩
  · exact Or.inr ⟨h, if_neg h⟩

theorem toUpper_cases (c : Nat) :
    ((97 ≤ c ∧ c ≤ 122) ∧ toUpperC c = c - 32) ∨ (¬ (97 ≤ c ∧ c ≤ 122) ∧ toUpperC c = c) := by
  by_cases h : 97 ≤ c ∧ c ≤ 122
  · exact Or.inl ⟨h, if_pos h⟩
  · exact Or.inr ⟨h, if_neg h⟩

theorem swap_cases (c : Nat) :
    ((97 ≤ c ∧ c ≤ 122) ∧ swapC c = c - 32) ∨ ((65 ≤ c ∧ c ≤ 90) ∧ swapC c = c + 32) ∨
      (¬ (97 ≤ c ∧ c ≤ 122) ∧ ¬ (65 ≤ c ∧ c ≤ 90) ∧ swapC c = c) := by
  by_cases h1 : 97 ≤ c ∧ c ≤ 122
  · refine Or.inl ⟨h1, ?_⟩
    rw [swapC, if_pos (show isLowerC c = true from decide_eq_true h1), toUpperC, if_pos h1]
  · have hl : ¬ isLowerC c = true := fun h => h1 (of_decide_eq_true h)
    by_cases h2 : 65 ≤ c ∧ c ≤ 90
    · refine Or.inr (Or.inl ⟨h2, ?_⟩)
      rw [swapC, if_neg hl, if_pos (show isUpperC c = true from decide_eq_true h2), toLowerC, if_pos h2]
    · have hu : ¬ isUpperC c = true := fun h => h2 (of_decide_eq_true h)
      refine Or.inr (Or.inr ⟨h1, h2, ?_⟩)
      rw [swapC, if_neg hl, if_neg hu]

theorem upper_toLower (c : Nat) : isUpperC (toLowerC c) = false := by
  rcases toLower_cases c with ⟨h, e⟩ | ⟨h, e⟩ <;> rw [e] <;> exact decide_eq_false (by omega)

theorem lower_toUpper (c : Nat) : isLowerC (toUpperC c) = false := by
  rcases toUpper_cases c with ⟨h, e⟩ | ⟨h, e⟩ <;> rw [e] <;> exact decide_eq_false (by omega)

theorem lower_toLower (c : Nat) : isLowerC (toLowerC c) = casedC c := by
  apply Bool.eq_iff_iff.mpr
  rcases toLower_cases c with ⟨h, e⟩ | ⟨h, e⟩ <;> rw [e] <;>
    simp only [casedC, isUpperC, isLowerC, Bool.or_eq_true, decide_eq_true_eq] <;> omega

theorem upper_toUpper (c : Nat) : isUpperC (toUpperC c) = casedC c := by
  apply Bool.eq_iff_iff.mpr
  rcases toUpper_cases c with ⟨h, e⟩ | ⟨h, e⟩ <;> rw [e] <;>
    simp only [casedC, isUpperC, isLowerC, Bool.or_eq_true, decide_eq_true_eq] <;> omega

theorem lower_swap (c : Nat) : isLowerC (swapC c) = isUpperC c := by
  apply Bool.eq_iff_iff.mpr
  rcases swap_cases c with ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, h', e⟩ <;> rw [e] <;>
    simp only [isUpperC, isLowerC, decide_eq_true_eq] <;> omega

theorem upper_swap (c : Nat) : isUpperC (swapC c) = isLowerC c := by
  apply Bool.eq_iff_iff.mpr
  rcases swap_cases c with ⟨h, e⟩ | ⟨h, e⟩ | ⟨h, h', e⟩ <;> rw [e] <;>
    simp only [isUpperC, isLowerC, decide_eq_true_eq] <;> omega

theorem lower_lower (c : Nat) : toLowerC (toLowerC c) = toLowerC c := by
  simp only [toLowerC]
  repeat' split
  all_goals omega

theorem titleMap_lower (b : Bool) (s : Seq) : bytesLower (titleMap b s) = bytesLower s := by
  induction s generalizing b with
  | nil => rfl
  | cons c rest ih =>
    have hr : ∀ b', (titleMap b' rest).map toLowerC = rest.map toLowerC := ih
    simp only [titleMap, bytesLower]
    split
    · split <;> simp [hr, low_up_c]
    · split
      · split <;> simp [hr, lower_lower]
      · simp [hr]

theorem map_fix (f : Nat → Nat) (l : Seq) (h : ∀ c ∈ l, f c = c) : l.map f = l := by
  induction l with
  | nil => rfl
  | cons a as ih => simp [h a (by simp), ih (fun c hc => h c (by simp [hc]))]

/-- What the case maps do, for every byte string, by the classes of the result: `lower` leaves no
uppercase letter and has a lowercase one exactly when the input has a cased byte, so `b.lower()` is
`islower` exactly then, and likewise for `upper`; `swapcase` exchanges `isupper` and `islower`;
`title` changes only the case of letters; and a string with no cased byte is left alone. With
`CaseMaps` and `TitleIstitle` this separates each map from the identity and from a constant. -/
def CaseLaws : Prop :=
  ∀ s : Seq,
    ((bytesLower s).all (fun c => !isUpperC c) = true) ∧ bytesIsLower (bytesLower s) = s.any casedC ∧
    ((bytesUpper s).all (fun c => !isLowerC c) = true) ∧ bytesIsUpper (bytesUpper s) = s.any casedC ∧
    bytesIsUpper (bytesSwapcase s) = bytesIsLower s ∧ bytesIsLower (bytesSwapcase s) = bytesIsUpper s ∧
    bytesLower (bytesTitle s) = bytesLower s ∧
    ((∀ c ∈ s, casedC c = false) → bytesLower s = s ∧ bytesUpper s = s ∧ bytesSwapcase s = s)

theorem caseLaws_proven : CaseLaws := by
  intro s
  have h1 : ((bytesLower s).all fun c => !isUpperC c) = true := by
    simp [bytesLower, List.all_map, upper_toLower]
  have h2 : (bytesLower s).any isLowerC = s.any casedC := by
    simp only [bytesLower, List.any_map]
    congr 1
    funext c
    exact lower_toLower c
  have h3 : ((bytesUpper s).all fun c => !isLowerC c) = true := by
    simp [bytesUpper, List.all_map, lower_toUpper]
  have h4 : (bytesUpper s).any isUpperC = s.any casedC := by
    simp only [bytesUpper, List.any_map]
    congr 1
    funext c
    exact upper_toUpper c
  have hA : ∀ (t u : Nat → Bool), (∀ c, t (swapC c) = u c) →
      (bytesSwapcase s).any t = s.any u ∧
        ((bytesSwapcase s).all fun c => !t c) = s.all fun c => !u c := by
    intro t u h
    constructor
    · simp only [bytesSwapcase, List.any_map]
      congr 1
      funext c
      exact h c
    · simp only [bytesSwapcase, List.all_map]
      congr 1
      funext c
      simp [h c]
  have hl := casedSpec_proven s
  have hs := casedSpec_proven (bytesSwapcase s)
  refine ⟨h1, ?_, h3, ?_, ?_, ?_, titleMap_lower false s, fun hn => ?_⟩
  · rw [(casedSpec_proven _).1, h1, h2, Bool.true_and]
  · rw [(casedSpec_proven _).2, h3, h4, Bool.true_and]
  · rw [hs.2, hl.1, (hA isUpperC isLowerC upper_swap).1, (hA isLowerC isUpperC lower_swap).2,
      Bool.and_comm]
  · rw [hs.1, hl.2, (hA isLowerC isUpperC lower_swap).1, (hA isUpperC isLowerC upper_swap).2,
      Bool.and_comm]
  · have hc : ∀ c ∈ s, ¬ (97 ≤ c ∧ c ≤ 122) ∧ ¬ (65 ≤ c ∧ c ≤ 90) := by
      intro c hm
      have h := hn c hm
      simp only [casedC, Bool.or_eq_false_iff, isUpperC, isLowerC, decide_eq_false_iff_not] at h
      exact ⟨h.2, h.1⟩
    refine ⟨map_fix _ _ fun c hm => if_neg (hc c hm).2, map_fix _ _ fun c hm => if_neg (hc c hm).1,
      map_fix _ _ fun c hm => ?_⟩
    rcases swap_cases c with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, e⟩
    · exact absurd h (hc c hm).1
    · exact absurd h (hc c hm).2
    · exact e

/-! ## maketrans -/

theorem mk_hit (frm to p : Seq) (i : Nat) (hi : i < frm.length) (hl : frm.length = to.length)
    (hp : ∀ c ∈ frm, c < p.length) (hlast : frm[i] ∉ frm.drop (i + 1)) :
    (maketransLoop p frm to)[frm[i]]? = to[i]? := by
  induction frm generalizing to p i with
  | nil => simp at hi
  | cons f fs ih =>
    cases to with
    | nil => simp at hl
    | cons t ts =>
      simp only [maketransLoop]
      cases i with
      | zero =>
        simp only [List.getElem_cons_zero, List.drop_succ_cons, List.drop_zero] at hlast ⊢
        rw [maketransLoop_outside _ _ _ _ hlast]
        simp [List.getElem?_set_self, hp f (by simp)]
      | succ i =>
        simp only [List.getElem_cons_succ, List.getElem?_cons_succ]
        apply ih
        · simpa using hl
        · intro c hc
          rw [List.length_set]
          exact hp c (by simp [hc])
        · simpa using hlast

/-- `bytes.maketrans(frm, to)` sends each byte of `frm` to the byte of `to` at the place of its last
occurrence (`p[frm[i]] = to[i]`, bytes_methods.c:374-376). Hypotheses: equal lengths, and bytes. -/
def MaketransHit : Prop :=
  ∀ frm to : Seq, frm.length = to.length → (∀ c ∈ frm, c < 256) →
    ∃ t, bytesMaketrans frm to = .ok t ∧ ∀ (i : Nat) (h : i < frm.length), frm[i] ∉ frm.drop (i + 1) →
      t[frm[i]]? = to[i]?

theorem maketransHit_proven : MaketransHit := by
  intro frm to hl hb
  refine ⟨maketransLoop (List.range 256) frm to, by simp [bytesMaketrans, hl], fun i h hlast => ?_⟩
  exact mk_hit frm to _ i h hl (by simpa using hb) hlast

/-! ## strip -/

theorem dropWhile_head (p : Nat → Bool) (l : Seq) (c : Nat) (h : (l.dropWhile p).head? = some c) :
    p c = false := by
  induction l with
  | nil => simp at h
  | cons a as ih =>
    simp only [List.dropWhile_cons] at h
    split at h
    · exact ih h
    · rename_i hp
      simp only [List.head?_cons, Option.some.injEq] at h
      subst h
      simpa using hp

theorem drop_takeWhile (p : Nat → Bool) (l : Seq) : l.drop (l.takeWhile p).length = l.dropWhile p := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [List.takeWhile_cons, List.dropWhile_cons]
    cases h : p a <;> simp [ih]

theorem mem_takeWhile_p (p : Nat → Bool) (l : Seq) (c : Nat) (h : c ∈ l.takeWhile p) : p c = true := by
  induction l with
  | nil => simp at h
  | cons a as ih =>
    simp only [List.takeWhile_cons] at h
    split at h
    · rename_i hp
      rcases List.mem_cons.1 h with rfl | h
      · exact hp
      · exact ih h
    · simp at h

theorem reverse_split (mem : Nat → Bool) (m : Seq) :
    (m.reverse.dropWhile mem).reverse ++ (m.reverse.takeWhile mem).reverse = m := by
  have h := List.takeWhile_append_dropWhile (p := mem) (l := m.reverse)
  have h2 := congrArg List.reverse h
  rwa [List.reverse_append, List.reverse_reverse] at h2

theorem take_reverse_drop (mem : Nat → Bool) (m : Seq) :
    m.take (m.reverse.dropWhile mem).length = (m.reverse.dropWhile mem).reverse := by
  have key : ∀ a b m : Seq, a.reverse ++ b = m → m.take a.length = a.reverse := by
    intro a b m h
    subst h
    exact List.take_left' (by simp)
  exact key _ _ _ (reverse_split mem m)

theorem stripWith_left (mem : Nat → Bool) (s : Seq) : stripWith mem .left s = s.dropWhile mem := by
  simp only [stripWith, ne_eq, reduceCtorEq, not_false_eq_true, ↓reduceIte, not_true_eq_false,
    drop_takeWhile]
  exact List.take_of_length_le (by simp [← drop_takeWhile mem s])

theorem stripWith_right (mem : Nat → Bool) (s : Seq) :
    stripWith mem .right s = (s.reverse.dropWhile mem).reverse := by
  simp only [stripWith, ne_eq, reduceCtorEq, not_false_eq_true, ↓reduceIte, not_true_eq_false,
    List.drop_zero, Nat.zero_add, Nat.sub_zero]
  exact take_reverse_drop mem s

theorem stripWith_both (mem : Nat → Bool) (s : Seq) :
    stripWith mem .both s = ((s.dropWhile mem).reverse.dropWhile mem).reverse := by
  simp only [stripWith, ne_eq, reduceCtorEq, not_false_eq_true, ↓reduceIte, Nat.add_sub_cancel_left,
    drop_takeWhile]
  exact take_reverse_drop mem _

/-- `lstrip`, `rstrip` and `strip` (`do_xstrip`, `do_strip`, bytesobject.c:1994-2061) for any set:
the result is a piece of the input, whatever was removed on either side is in the set, only the
sides asked for lose anything, and a stripped side of the result is not in the set. `id` and
`fun _ => []` both fail this. -/
def StripSpec : Prop :=
  ∀ (mem : Nat → Bool) (t : StripType) (s : Seq),
    let r := stripWith mem t s
    ∃ pre post, s = pre ++ r ++ post ∧ (∀ c ∈ pre, mem c = true) ∧ (∀ c ∈ post, mem c = true) ∧
      (t = .right → pre = []) ∧ (t = .left → post = []) ∧
      (t ≠ .right → ∀ c, r.head? = some c → mem c = false) ∧
      (t ≠ .left → ∀ c, r.getLast? = some c → mem c = false)

theorem stripSpec_proven : StripSpec := by
  intro mem t s
  dsimp only
  have htw : ∀ c ∈ s.takeWhile mem, mem c = true := mem_takeWhile_p mem s
  have hsp := List.takeWhile_append_dropWhile (p := mem) (l := s)
  have hrev : ∀ m : Seq, ∀ c ∈ (m.reverse.takeWhile mem).reverse, mem c = true :=
    fun m c hc => mem_takeWhile_p mem _ c (List.mem_reverse.1 hc)
  have hlast : ∀ m : Seq, ∀ c, (m.reverse.dropWhile mem).reverse.getLast? = some c → mem c = false := by
    intro m c hc
    apply dropWhile_head mem m.reverse
    simpa using hc
  cases t with
  | left =>
    rw [stripWith_left]
    refine ⟨s.takeWhile mem, [], by simpa using hsp.symm, htw, by simp, by simp, fun _ => rfl,
      fun _ c hc => dropWhile_head mem s c hc, by simp⟩
  | right =>
    rw [stripWith_right]
    refine ⟨[], (s.reverse.takeWhile mem).reverse, ?_, by simp, hrev s, fun _ => rfl, by simp, by simp,
      fun _ c hc => hlast s c hc⟩
    simpa using (reverse_split mem s).symm
  | both =>
    rw [stripWith_both]
    refine ⟨s.takeWhile mem, ((s.dropWhile mem).reverse.takeWhile mem).reverse, ?_, htw, hrev _,
      by simp, by simp, fun _ c hc => ?_, fun _ c hc => hlast _ c hc⟩
    · rw [List.append_assoc, reverse_split mem (s.dropWhile mem), hsp]
    · have hd : (s.dropWhile mem).head? = some c := by
        have h := reverse_split mem (s.dropWhile mem)
        rw [← h, List.head?_append, hc]
        rfl
      exact dropWhile_head mem s c hd

/-! ## translate -/

theorem translateSlow_filter (s t del : Seq) :
    translateSlow s (some t) del = (s.filter fun c => decide (c ∉ del)).map (fun c => t.getD c 0) := by
  induction s with
  | nil => rfl
  | cons c rest ih =>
    by_cases h : c ∈ del
    · simpa [translateSlow, List.filterMap_cons, h] using ih
    · simpa [translateSlow, List.filterMap_cons, h] using ih

/-- `b.translate(table, delete=d)`, bytesobject.c:2159-2270: the bytes outside `d`, each sent through
the table; no table keeps them, and a table of another length is refused. -/
def TranslateSpec : Prop :=
  ∀ s t del : Seq,
    (t.length = 256 → bytesTranslate s (.bytes t) (some (.bytes del)) =
      .ok ((s.filter fun c => decide (c ∉ del)).map fun c => t.getD c 0)) ∧
    (t.length = 256 → bytesTranslate s (.bytes t) none = .ok (s.map fun c => t.getD c 0)) ∧
    (t.length ≠ 256 → bytesTranslate s (.bytes t) none =
      .error (.valueError "translation table must be 256 characters long")) ∧
    bytesTranslate s .none (some (.bytes del)) = .ok (s.filter fun c => decide (c ∉ del))

theorem translateSpec_proven : TranslateSpec := by
  intro s t del
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, ?_⟩
  · unfold bytesTranslate
    simp only [tableArg, getBuffer, Obj.buffer?, bind, Except.bind, pure, Except.pure, Option.map,
      Option.getD, h, ne_eq, not_true_eq_false, ↓reduceIte]
    cases del with
    | nil =>
      have hk : s.filter (fun c => decide (c ∉ ([] : Seq))) = s := List.filter_eq_self.mpr (by simp)
      simp only [translateFast, hk]
    | cons d ds => simp only [translateSlow_filter]
  · unfold bytesTranslate
    simp only [tableArg, getBuffer, Obj.buffer?, bind, Except.bind, pure, Except.pure, Option.map,
      Option.getD, h, ne_eq, not_true_eq_false, ↓reduceIte, translateFast]
  · unfold bytesTranslate
    simp only [tableArg, getBuffer, Obj.buffer?, bind, Except.bind, pure, Except.pure, Option.map,
      Option.getD, h, ne_eq, not_false_eq_true, ↓reduceIte]
    rfl
  · rw [← translateTwins_proven.2.2 s del]
    rfl

end PyLean.BytesObj.Bytes
