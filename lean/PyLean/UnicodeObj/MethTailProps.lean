import PyLean.UnicodeObj.MethTail
import PyLean.UnicodeObj.MethStripProps

/-!
Properties of `tailmatch` and of `startswith`, `endswith`, `removeprefix`, `removesuffix`.
-/

namespace PyLean.UnicodeObj

open PyLean

/-- What `startswith`/`endswith` test: `sub` is a prefix (direction <= 0) or suffix
(direction > 0) of `s[start:end]`, Python's slice of the code points; and, as CPython has
always answered, nothing matches when the adjusted `start` plus `len(sub)` passes the clipped
`end` (so `'abc'.startswith('', 4)` and `'abc'.startswith('', 2, 1)` are `False`). -/
def tailDoc (s sub : Str) (start «end» : Int) (direction : Int) : Bool :=
  let a : Int := if start < 0 then max 0 (start + s.length) else start
  let b : Int := clipIndex s.length «end»
  if a + sub.length > b then false
  else
    let w := (s.drop a.toNat).take (b - a).toNat
    if direction > 0 then sub.isSuffixOf w else sub.isPrefixOf w

/-- For all strings, `start`, `end` and directions, `tailmatch` answers 1 exactly when
`tailDoc` holds and 0 otherwise, through either comparison: the `memcmp` for one kind and the
loop after the first and last characters for two kinds. Type invariants: `Str.Valid`. -/
def TailmatchDoc : Prop :=
  ∀ (s sub : Str) (start «end» direction : Int), Str.Valid s → Str.Valid sub →
    tailmatch s sub start «end» direction = if tailDoc s sub start «end» direction then 1 else 0

open Classical in
theorem tailLoop_eq (rd rs : Int → Nat) (e : Int) : ∀ k (i : Nat), (e - i).toNat = k →
    tailLoop rd rs e i =
      if (∀ j : Nat, i ≤ j → (j : Int) < e → rd j = rs j) then 1 else 0 := by
  intro k
  induction k with
  | zero =>
    intro i h
    rw [tailLoop, if_neg (by omega), if_pos]
    intro j hj hje; omega
  | succ k ih =>
    intro i h
    rw [tailLoop, if_pos (by omega)]
    by_cases hd : rd i ≠ rs i
    · rw [if_pos hd, if_neg]
      intro hall; exact hd (hall i (Nat.le_refl _) (by omega))
    · rw [if_neg hd, ih (i + 1) (by omega)]
      have hd' : rd i = rs i := by simpa using hd
      by_cases hall : ∀ j : Nat, i ≤ j → (j : Int) < e → rd j = rs j
      · rw [if_pos hall, if_pos (fun j hj hje => hall j (by omega) hje)]
      · rw [if_neg hall, if_neg]
        intro h2; apply hall
        intro j hj hje
        rcases Nat.eq_or_lt_of_le hj with rfl | hlt
        · exact hd'
        · exact h2 j hlt hje

theorem adjust_fst (start e : Int) (n : Nat) :
    (StrSearch.adjustIndices start e n).1 = if start < 0 then max 0 (start + n) else start := by
  simp only [StrSearch.adjustIndices]
  repeat' split
  all_goals omega

/-- Two lists of one length `n ≥ 1` are equal exactly when their first and last elements and
every element in between are. -/
theorem eq_iff_ends (W sub : List Nat) (n : Nat) (hW : W.length = n) (hs : sub.length = n)
    (hn : 1 ≤ n) :
    W = sub ↔ (W.getD 0 0 = sub.getD 0 0 ∧ W.getD (n - 1) 0 = sub.getD (n - 1) 0 ∧
      ∀ j : Nat, 1 ≤ j → j < n - 1 → W.getD j 0 = sub.getD j 0) := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl, fun _ _ _ => rfl⟩
  · rintro ⟨h0, hl, hm⟩
    apply List.ext_getElem (by omega)
    intro j h1 h2
    have := (if hj0 : j = 0 then by subst hj0; exact h0
      else if hjl : j = n - 1 then by subst hjl; exact hl
      else hm j (by omega) (by omega) : W.getD j 0 = sub.getD j 0)
    rwa [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
      List.getElem?_eq_getElem h2, Option.getD_some, Option.getD_some] at this

theorem window_getD (s : Str) (off n i : Nat) (hi : i < n) (hn : off + n ≤ s.length) :
    ((s.drop off).take n).getD i 0 = s.getD (off + i) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi,
    List.getElem?_drop]

theorem tailmatchDoc_proven : TailmatchDoc := by
  intro s sub start e dir hs hsub
  obtain ⟨hb, he0, hen, hs0, -⟩ := adjust_facts start e s.length
  have ha := adjust_fst start e s.length
  unfold tailmatch tailDoc
  rw [← ha, hb]
  generalize StrSearch.adjustIndices start e s.length = p at *
  obtain ⟨st, en⟩ := p
  simp only at he0 hen hs0 ⊢
  by_cases hlt : en - sub.length < st
  · rw [if_pos hlt, if_pos (show st + (sub.length : Int) > en by omega)]
    rfl
  · rw [if_neg hlt, if_neg (show ¬ (st + (sub.length : Int) > en) by omega)]
    have hfit : st + sub.length ≤ en := by omega
    -- the window the direction picks
    generalize hoff : (if dir > 0 then en - sub.length else st) = off
    have hoff0 : 0 ≤ off ∧ off + sub.length ≤ s.length := by
      subst hoff; split <;> omega
    have hW : (if dir > 0 then sub.isSuffixOf ((s.drop st.toNat).take (en - st).toNat)
        else sub.isPrefixOf ((s.drop st.toNat).take (en - st).toNat)) =
        decide ((s.drop off.toNat).take sub.length = sub) := by
      have hlen : ((s.drop st.toNat).take (en - st).toNat).length = (en - st).toNat := by
        simp; omega
      split
      · next hd =>
        have e1 : off = en - sub.length := by rw [← hoff, if_pos hd]
        rw [Bool.eq_iff_iff, List.isSuffixOf_iff_suffix, decide_eq_true_iff,
          List.suffix_iff_eq_drop, hlen, List.drop_take, List.drop_drop]
        have e2 : st.toNat + ((en - st).toNat - sub.length) = off.toNat := by omega
        have e3 : (en - st).toNat - ((en - st).toNat - sub.length) = sub.length := by omega
        rw [e2, e3]
        exact ⟨fun h => h.symm, fun h => h.symm⟩
      · next hd =>
        have e1 : off = st := by rw [← hoff, if_neg hd]
        rw [Bool.eq_iff_iff, List.isPrefixOf_iff_prefix, decide_eq_true_iff,
          List.prefix_iff_eq_take, List.take_take, e1]
        rw [show min sub.length (en - st).toNat = sub.length by omega]
        exact ⟨fun h => h.symm, fun h => h.symm⟩
    rw [hW]
    by_cases h0 : sub.length = 0
    · rw [if_pos h0, List.eq_nil_of_length_eq_zero h0]; simp
    · rw [if_neg h0]
      have hn : 1 ≤ sub.length := by omega
      have hWl : ((s.drop off.toNat).take sub.length).length = sub.length := by
        simp; omega
      have key := eq_iff_ends _ sub sub.length hWl rfl hn
      have hrd : ∀ i : Int, 0 ≤ i → i < sub.length →
          s.getD (off + i).toNat 0 = ((s.drop off.toNat).take sub.length).getD i.toNat 0 := by
        intro i hi0 hi
        rw [window_getD s off.toNat sub.length i.toNat (by omega) (by omega)]
        congr 1; omega
      have t0 : (0 : Int).toNat = 0 := rfl
      have t1 : ((sub.length : Int) - 1).toNat = sub.length - 1 := by omega
      have r0 := hrd 0 (by omega) (by omega)
      have r1 := hrd (sub.length - 1) (by omega) (by omega)
      rw [t0] at r0
      rw [t1] at r1
      simp only [r0, r1, t0, t1]
      by_cases hends : ((s.drop off.toNat).take sub.length).getD 0 0 = sub.getD 0 0 ∧
          ((s.drop off.toNat).take sub.length).getD (sub.length - 1) 0 = sub.getD (sub.length - 1) 0
      · rw [if_pos hends]
        split
        · unfold StrSearch.window
          rw [show ((sub.length : Int)).toNat = sub.length by omega]
          by_cases heq : (s.drop off.toNat).take sub.length = sub
          · rw [if_pos heq, decide_eq_true heq]; rfl
          · rw [if_neg heq, decide_eq_false heq]; rfl
        · rw [tailLoop_eq _ _ _ _ 1 rfl]
          have hmid : (∀ j : Nat, 1 ≤ j → (j : Int) < (sub.length : Int) - 1 →
              s.getD (off + j).toNat 0 = sub.getD (j : Int).toNat 0) ↔
              (∀ j : Nat, 1 ≤ j → j < sub.length - 1 →
                ((s.drop off.toNat).take sub.length).getD j 0 = sub.getD j 0) := by
            constructor
            · intro h j hj1 hj2
              have := h j hj1 (by omega)
              rw [hrd j (by omega) (by omega)] at this
              simpa using this
            · intro h j hj1 hj2
              rw [hrd j (by omega) (by omega)]
              simpa using h j hj1 (by omega)
          by_cases hm : ∀ j : Nat, 1 ≤ j → j < sub.length - 1 →
              ((s.drop off.toNat).take sub.length).getD j 0 = sub.getD j 0
          · rw [if_pos (hmid.2 hm), decide_eq_true (key.2 ⟨hends.1, hends.2, hm⟩)]; rfl
          · rw [if_neg (fun h => hm (hmid.1 h)),
              decide_eq_false (fun h => hm (key.1 h).2.2)]; rfl
      · rw [if_neg hends, decide_eq_false (fun h => hends ⟨(key.1 h).1, (key.1 h).2.1⟩)]; rfl

/-- The C API: `PyUnicode_Tailmatch(str, substr, start, end, direction)` "Return 1 if substr
matches unicode[start:end] at the given tail end (direction == -1 means to do a prefix match,
direction == 1 a suffix match), 0 otherwise", with `TypeError` for an argument that is not a
`str`, the first one checked first. For all arguments. -/
def TailmatchApi : Prop :=
  ∀ (str substr : Arg) (start «end» direction : Int),
    ((∀ t, str ≠ .str t) → pyUnicodeTailmatch str substr start «end» direction =
      .error (.typeError s!"must be str, not {str.tpName}")) ∧
    (∀ s, Str.Valid s → (∀ t, substr ≠ .str t) →
      pyUnicodeTailmatch (.str s) substr start «end» direction =
        .error (.typeError s!"must be str, not {substr.tpName}")) ∧
    (∀ s sub, Str.Valid s → Str.Valid sub →
      pyUnicodeTailmatch (.str s) (.str sub) start «end» direction =
        .ok (if tailDoc s sub start «end» direction then 1 else 0))

theorem tailmatchApi_proven : TailmatchApi := by
  intro str substr start e dir
  refine ⟨?_, ?_, ?_⟩
  · intro h
    cases str with
    | str t => exact absurd rfl (h t)
    | _ => rfl
  · intro s _ h
    cases substr with
    | str t => exact absurd rfl (h t)
    | _ => rfl
  · intro s sub hs hsub
    show Except.ok (tailmatch s sub start e dir) = _
    rw [tailmatchDoc_proven s sub start e dir hs hsub]

/-- `str.startswith` and `str.endswith` for every string, every `Py_ssize_t` start and end:
a `str` argument answers `tailDoc`; a tuple of `str` answers whether any element does; in a
tuple, the first element that is not a `str` raises `TypeError` unless an earlier element
matched; any other argument raises `TypeError`. Type invariants: `Str.Valid`. -/
def StartsEndsDoc : Prop :=
  ∀ (s : Str) (a b : Int), Str.Valid s →
    ∀ (name : String) (dir : Int), (name = "startswith" ∧ dir = -1 ∨ name = "endswith" ∧ dir = 1) →
      (∀ sub, Str.Valid sub → startsEndsImpl name dir s (.str sub) a b = .ok (tailDoc s sub a b dir)) ∧
      (∀ subs : List Str, (∀ t ∈ subs, Str.Valid t) →
        startsEndsImpl name dir s (.tuple (subs.map .str)) a b =
          .ok (subs.any fun t => tailDoc s t a b dir)) ∧
      (∀ (subs : List Str) (x : Arg) (rest : List Arg), (∀ t ∈ subs, Str.Valid t) →
        (∀ t, x ≠ .str t) →
        startsEndsImpl name dir s (.tuple (subs.map .str ++ x :: rest)) a b =
          if subs.any (fun t => tailDoc s t a b dir) then .ok true
          else .error (.typeError s!"tuple for {name} must only contain str, not {x.tpName}")) ∧
      (∀ x : Arg, (∀ t, x ≠ .str t) → (∀ l, x ≠ .tuple l) →
        startsEndsImpl name dir s x a b =
          .error (.typeError s!"{name} first arg must be str or a tuple of str, not {x.tpName}"))

theorem tailmatch_ne (s sub : Str) (a b dir : Int) (hs : Str.Valid s) (hsub : Str.Valid sub) :
    (tailmatch s sub a b dir ≠ 0) = tailDoc s sub a b dir := by
  rw [tailmatchDoc_proven s sub a b dir hs hsub]
  cases tailDoc s sub a b dir <;> simp

theorem startsEndsDoc_proven : StartsEndsDoc := by
  intro s a b hs name dir _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro sub hsub
    simp only [startsEndsImpl, tailmatch_ne s sub a b dir hs hsub, Bool.decide_eq_true]
  · intro subs hsubs
    simp only [startsEndsImpl]
    induction subs with
    | nil => rfl
    | cons t ts ih =>
      have ht := hsubs t List.mem_cons_self
      simp only [List.map_cons, tailTuple, List.any_cons]
      simp only [tailmatch_ne s t a b dir hs ht]
      by_cases hd : tailDoc s t a b dir = true
      · simp [hd]
      · rw [if_neg hd, ih (fun x hx => hsubs x (List.mem_cons_of_mem _ hx))]
        simp [hd]
  · intro subs x rest hsubs hx
    simp only [startsEndsImpl]
    induction subs with
    | nil =>
      cases x with
      | str t => exact absurd rfl (hx t)
      | _ => rfl
    | cons t ts ih =>
      have ht := hsubs t List.mem_cons_self
      simp only [List.map_cons, List.cons_append, tailTuple, List.any_cons]
      simp only [tailmatch_ne s t a b dir hs ht]
      by_cases hd : tailDoc s t a b dir = true
      · simp [hd]
      · rw [if_neg hd, ih (fun x hx => hsubs x (List.mem_cons_of_mem _ hx))]
        simp [hd]
  · intro x h1 h2
    cases x with
    | str t => exact absurd rfl (h1 t)
    | tuple l => exact absurd rfl (h2 l)
    | _ => rfl

/-- `str.removeprefix`: "If the string starts with the prefix string, return
string[len(prefix):]. Otherwise, return a copy of the original string." `str.removesuffix`:
"If the string ends with the suffix string and that suffix is not empty, return
string[:-len(suffix)]. Otherwise, return a copy of the original string." Any argument that is
not a `str` raises `TypeError`. For every string; type invariants: `Str.Valid`, and a length
that is a `Py_ssize_t`. -/
def RemoveAffixDoc : Prop :=
  ∀ (s : Str), Str.Valid s → (s.length : Int) ≤ ssizeMax →
    (∀ p, Str.Valid p → unicodeRemoveprefix s (.str p) =
      .ok (if p.isPrefixOf s then s.drop p.length else s)) ∧
    (∀ p, Str.Valid p → unicodeRemovesuffix s (.str p) =
      .ok (if p ≠ [] ∧ p.isSuffixOf s then s.take (s.length - p.length) else s)) ∧
    (∀ x : Arg, (∀ t, x ≠ .str t) →
      unicodeRemoveprefix s x = .error (badStrArgument "removeprefix" x) ∧
      unicodeRemovesuffix s x = .error (badStrArgument "removesuffix" x))

theorem tailDoc_whole (s p : Str) (dir : Int) (hlen : (s.length : Int) ≤ ssizeMax) :
    tailDoc s p 0 ssizeMax dir = if dir > 0 then p.isSuffixOf s else p.isPrefixOf s := by
  unfold tailDoc clipIndex
  have hc : (if ssizeMax < 0 then (max 0 (ssizeMax + s.length)).toNat
      else (min ssizeMax s.length).toNat) = s.length := by
    unfold ssizeMax at hlen ⊢; split <;> omega
  simp only [hc, show ¬ ((0 : Int) < 0) from Int.lt_irrefl 0, if_false, Int.toNat_zero,
    List.drop_zero, Int.zero_add]
  rw [List.take_of_length_le (by omega)]
  by_cases hl : (p.length : Int) > s.length
  · rw [if_pos hl]
    have h1 : p.isPrefixOf s = false := by
      rw [Bool.eq_false_iff]; intro h
      have := (List.isPrefixOf_iff_prefix.1 h).length_le; omega
    have h2 : p.isSuffixOf s = false := by
      rw [Bool.eq_false_iff]; intro h
      have := (List.isSuffixOf_iff_suffix.1 h).length_le; omega
    split <;> simp [h1, h2]
  · rw [if_neg hl]

theorem removeAffixDoc_proven : RemoveAffixDoc := by
  intro s hs hlen
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    simp only [unicodeRemoveprefix]
    rw [tailmatchDoc_proven s p 0 ssizeMax (-1) hs hp, tailDoc_whole s p _ hlen]
    simp only [show ¬ ((-1 : Int) > 0) by omega, if_false]
    by_cases h : p.isPrefixOf s = true
    · have hle := (List.isPrefixOf_iff_prefix.1 h).length_le
      have e1 : (if p.isPrefixOf s = true then (1 : Int) else 0) = 1 := if_pos h
      rw [e1, if_pos (show (1 : Int) ≠ 0 by decide), if_pos h,
        substring_ok s p.length s.length hle (Nat.le_refl _), List.take_of_length_le (by simp)]
    · have e1 : (if p.isPrefixOf s = true then (1 : Int) else 0) = 0 := if_neg h
      rw [e1, if_neg (show ¬ ((0 : Int) ≠ 0) by decide), if_neg h]
  · intro p hp
    simp only [unicodeRemovesuffix]
    rw [tailmatchDoc_proven s p 0 ssizeMax 1 hs hp, tailDoc_whole s p _ hlen]
    simp only [show ((1 : Int) > 0) by omega, if_true]
    by_cases h : p.isSuffixOf s = true
    · have hle := (List.isSuffixOf_iff_suffix.1 h).length_le
      have e1 : (if p.isSuffixOf s = true then (1 : Int) else 0) = 1 := if_pos h
      rw [e1, if_pos (show (1 : Int) ≠ 0 by decide)]
      by_cases hp0 : p = []
      · subst hp0
        rw [if_neg (fun hh => hh.1 rfl)]
        simp [pyUnicodeSubstring]
      · rw [if_pos ⟨hp0, h⟩]
        have e : ((s.length : Int) - p.length) = ((s.length - p.length : Nat) : Int) := by omega
        have := substring_ok s 0 (s.length - p.length) (Nat.zero_le _) (by omega)
        simp only [List.drop_zero, Nat.sub_zero] at this
        rw [e]
        exact this
    · have e1 : (if p.isSuffixOf s = true then (1 : Int) else 0) = 0 := if_neg h
      rw [e1, if_neg (show ¬ ((0 : Int) ≠ 0) by decide), if_neg (fun hh => h hh.2)]
  · intro x hx
    cases x with
    | str t => exact absurd rfl (hx t)
    | _ => exact ⟨rfl, rfl⟩

end PyLean.UnicodeObj
