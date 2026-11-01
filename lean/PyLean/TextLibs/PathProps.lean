import PyLean.TextLibs.PathModel

/-! Properties of the path functions. -/

namespace PyLean.TextLibs.Path

open PyLean

set_option linter.unusedSimpArgs false

/-! ### `splitext` -/

theorem take_drop_int (p : List Nat) (d : Int) : p.take d.toNat ++ p.drop d.toNat = p :=
  List.take_append_drop _ _

theorem rfind_lt (c : Nat) (s : List Nat) : rfind c s < s.length := by
  unfold rfind
  split <;> omega

theorem rfind_get (c : Nat) (s : List Nat) (h : 0 ≤ rfind c s) :
    s.getD (rfind c s).toNat 0 = c := by
  unfold rfind at h ⊢
  cases hf : s.reverse.findIdx? (· == c) with
  | none =>
    rw [hf] at h
    simp at h
  | some i =>
    simp only [hf]
    obtain ⟨hi, h1, _⟩ := List.findIdx?_eq_some_iff_getElem.1 hf
    have hl : i < s.length := by simpa using hi
    have h2 : s.reverse[i] = c := by simpa using h1
    rw [List.getElem_reverse] at h2
    have e : ((s.length : Int) - 1 - (i : Int)).toNat = s.length - 1 - i := by omega
    rw [e]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (by omega)]
    simpa using h2

/-- `_splitext`: `root + ext == p`, always; an extension starts with a dot; and it is cut off only from
a last component that has something other than dots before it, so `.bashrc` and `...` have none. -/
def SplitextLaw : Prop :=
  ∀ (p : List Nat) (sep : Nat) (altsep : Option Nat) (r e : List Nat),
    splitextL p sep altsep = (r, e) →
    r ++ e = p ∧ (e ≠ [] → e.head? = some 46 ∧ sep ∉ e ∧ (∀ a, altsep = some a → a ∉ e))

theorem no_after_rfind (c : Nat) (s : List Nat) (i : Nat) (hi : i < s.length) (h : (i : Int) > rfind c s) :
    s[i] ≠ c := by
  unfold rfind at h
  cases hf : s.reverse.findIdx? (· == c) with
  | none =>
    have h1 := List.findIdx?_eq_none_iff.1 hf s[i] (by simp [List.getElem_mem])
    simpa using h1
  | some k =>
    rw [hf] at h
    obtain ⟨hk1, _, h4⟩ := List.findIdx?_eq_some_iff_getElem.1 hf
    have hk2 : k < s.length := by simpa using hk1
    have hj : s.length - 1 - i < k := by
      simp only at h
      omega
    have h5 := h4 _ hj
    simp only [List.getElem_reverse] at h5
    have h6 : ∀ (a b : Nat) (ha : a < s.length) (hb : b < s.length), a = b → s[a] = s[b] := by
      intro a b _ _ h
      subst h
      rfl
    rw [h6 i (s.length - 1 - (s.length - 1 - i)) hi (by omega) (by omega)]
    simpa using h5

theorem not_mem_drop (c : Nat) (s : List Nat) (d : Nat) (h : (d : Int) > rfind c s) : c ∉ s.drop d := by
  intro hm
  obtain ⟨i, hi, h1⟩ := List.getElem_of_mem hm
  have hl : i < s.length - d := by simpa using hi
  have h2 : s[d + i]'(by omega) = c := by simpa using h1
  exact no_after_rfind c s (d + i) (by omega) (by omega) h2

theorem rfind_ge (c : Nat) (s : List Nat) : -1 ≤ rfind c s := by
  unfold rfind
  cases hf : s.reverse.findIdx? (· == c) with
  | none => simp
  | some k =>
    obtain ⟨hk1, _, _⟩ := List.findIdx?_eq_some_iff_getElem.1 hf
    have hk2 : k < s.length := by simpa using hk1
    simp only
    omega

theorem splitextLaw_proven : SplitextLaw := by
  intro p sep altsep r e h
  unfold splitextL at h
  simp only at h
  have hsep : sepIdx p sep altsep ≥ rfind sep p := by
    unfold sepIdx
    cases altsep <;> simp <;> omega
  have halt : ∀ a, altsep = some a → sepIdx p sep altsep ≥ rfind a p := by
    intro a ha
    subst ha
    simp only [sepIdx]
    omega
  generalize sepIdx p sep altsep = si at h hsep halt
  by_cases hd : rfind 46 p > si
  · rw [if_pos hd] at h
    have h0 : 0 ≤ rfind 46 p := by
      have := rfind_ge sep p
      omega
    have hg := rfind_get 46 p h0
    split at h
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨List.take_append_drop _ _, fun _ => ⟨?_, ?_, ?_⟩⟩
      · have hl := rfind_lt 46 p
        rw [List.head?_drop, List.getElem?_eq_getElem (by omega)]
        simp only [Option.some.injEq]
        simp only [List.getD_eq_getElem?_getD] at hg
        rw [List.getElem?_eq_getElem (by omega)] at hg
        simpa using hg
      · exact not_mem_drop sep p _ (by omega)
      · intro a ha
        have := halt a ha
        exact not_mem_drop a p _ (by omega)
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by simp, by simp⟩
  · rw [if_neg hd] at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by simp, by simp⟩

/-! ### `splitroot` and `split` -/

theorem take_three (p : List Nat) (j : Nat) : p.take j ++ ((p.drop j).take 1 ++ p.drop (j + 1)) = p := by
  have : p.drop (j + 1) = (p.drop j).drop 1 := by simp [List.drop_drop, Nat.add_comm]
  rw [this, List.take_append_drop, List.take_append_drop]

/-- `ntpath.splitroot`: the three parts are the path, the root is at most one separator, and the three
shapes are told apart: `X:`, a lone leading separator, and neither. -/
def NtSplitrootLaw : Prop :=
  ∀ p : List Nat,
    let (d, r, t) := splitrootN p
    d ++ r ++ t = p ∧ r.length ≤ 1 ∧
    (∀ c rest, p = c :: 58 :: rest → isSepN c = false → d = [c, 58]) ∧
    (∀ c rest, p = c :: rest → isSepN c = true → (rest.head?.map isSepN != some true) →
      d = [] ∧ r = [c] ∧ t = rest) ∧
    ((p.head?.map isSepN != some true) → p.getD 1 0 != 58 → d = [] ∧ r = [] ∧ t = p)

theorem toBack_getD (p : List Nat) (i : Nat) (h : i < p.length) :
    (toBack p).getD i 0 = if p.getD i 0 == 47 then 92 else p.getD i 0 := by
  simp [toBack, List.getD_eq_getElem?_getD, h]

theorem ntSplitrootLaw_proven : NtSplitrootLaw := by
  intro p
  match hp : p with
  | [] => simp [splitrootN, toBack]
  | c :: rest =>
    have hsep : (toBack (c :: rest)).head? = some 92 ↔ isSepN c = true := by
      simp only [toBack, List.map_cons, List.head?_cons, Option.some.injEq, isSepN, Bool.or_eq_true, beq_iff_eq]
      split <;> simp_all
    have hconcat : ∀ d r t, splitrootN (c :: rest) = (d, r, t) → d ++ r ++ t = c :: rest ∧ r.length ≤ 1 := by
      intro d r t h
      unfold splitrootN at h
      simp only at h
      split at h
      · split at h
        · split at h
          · simp only [Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            simp
          · split at h
            · simp only [Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              simp
            · simp only [Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl⟩ := h
              rw [List.append_assoc]
              exact ⟨take_three _ _, by simp; omega⟩
        · simp only [Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          simp
      · split at h
        · split at h
          · simp only [Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            rw [List.append_assoc]
            exact ⟨take_three _ _, by simp; omega⟩
          · simp only [Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            exact ⟨by simpa using List.take_append_drop 2 (c :: rest), by simp⟩
        · simp only [Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          simp
    generalize hs : splitrootN (c :: rest) = x
    obtain ⟨d, r, t⟩ := x
    obtain ⟨h1, h2⟩ := hconcat d r t hs
    simp only
    refine ⟨h1, h2, fun c2 rest2 he hn => ?_, fun c2 rest2 he hn hr => ?_, fun hn hd => ?_⟩
    · simp only [List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have hb : ¬((toBack (c :: 58 :: rest2)).head? = some 92) := by
        rw [hsep]
        simpa using hn
      have hg : (toBack (c :: 58 :: rest2)).getD 1 0 = 58 := by simp [toBack]
      have hl : (toBack (c :: 58 :: rest2)).length > 1 := by simp [toBack]
      have hb2 : ((toBack (c :: 58 :: rest2)).head? == some 92) = false := by simpa using hb
      have hc2 : (toBack (c :: 58 :: rest2)).length > 1 ∧
          ((toBack (c :: 58 :: rest2)).getD 1 0 == 58) = true := ⟨hl, by rw [hg]; rfl⟩
      unfold splitrootN at hs
      simp only [hb2, Bool.false_eq_true, if_false] at hs
      rw [if_pos hc2] at hs
      split at hs
      · have := congrArg Prod.fst hs
        simpa using this.symm
      · have := congrArg Prod.fst hs
        simpa using this.symm
    · simp only [List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have hb : (toBack (c :: rest)).head? = some 92 := hsep.2 hn
      have hg : ¬((toBack (c :: rest)).getD 1 0 == 92 ∧ (toBack (c :: rest)).length > 1) := by
        cases rest with
        | nil => simp [toBack]
        | cons y t2 =>
          have hy : isSepN y = false := by simpa using hr
          intro h3
          have h4 : (if y == 47 then 92 else y) = 92 := by simpa [toBack] using h3.1
          simp only [isSepN, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hy
          split at h4 <;> simp_all
      have hb2 : ((toBack (c :: rest)).head? == some 92) = true := by simpa using hb
      unfold splitrootN at hs
      simp only [hb2, if_true] at hs
      rw [if_neg (by simpa using hg)] at hs
      cases hs
      simp
    · have hc : isSepN c = false := by simpa using hn
      have hb : ¬((toBack (c :: rest)).head? = some 92) := by
        rw [hsep]
        simp [hc]
      have hg : ¬((toBack (c :: rest)).length > 1 ∧ (toBack (c :: rest)).getD 1 0 == 58) := by
        intro h3
        cases rest with
        | nil => simp [toBack] at h3
        | cons y t2 =>
          have hy : y ≠ 58 := by simpa using hd
          have h4 : (if y == 47 then 92 else y) = 58 := by simpa [toBack] using h3.2
          split at h4 <;> simp_all
      have hb2 : ((toBack (c :: rest)).head? == some 92) = false := by simpa using hb
      unfold splitrootN at hs
      simp only [hb2, Bool.false_eq_true, if_false] at hs
      rw [if_neg (by simpa using hg)] at hs
      cases hs
      exact ⟨rfl, rfl, rfl⟩

/-- `posixpath.split`: the tail has no slash, and the head is the rest with its trailing slashes
stripped, unless it is all slashes. -/
def PosixSplitLaw : Prop :=
  ∀ (p : List Nat) (k : Bool) (h t : PV), splitP (.val ⟨k, p⟩) = .ok (h, t) →
    47 ∉ t.s ∧ ∃ n, p = h.s ++ List.replicate n 47 ++ t.s

theorem rstrip_parts (q : Nat → Bool) (l : List Nat) (c : Nat) (hc : ∀ x, q x = true → x = c) :
    ∃ n, l = rstrip q l ++ List.replicate n c := by
  have key : ∀ (m : List Nat), ∃ n, m = List.replicate n c ++ m.dropWhile q := by
    intro m
    induction m with
    | nil => exact ⟨0, rfl⟩
    | cons x r ih =>
      by_cases hx : q x = true
      · obtain ⟨n, hn⟩ := ih
        refine ⟨n + 1, ?_⟩
        rw [List.dropWhile_cons, if_pos hx, List.replicate_succ, List.cons_append, hc x hx, ← hn]
      · exact ⟨0, by simp [List.dropWhile_cons, hx]⟩
  obtain ⟨n, hn⟩ := key l.reverse
  refine ⟨n, ?_⟩
  have := congrArg List.reverse hn
  simp only [List.reverse_reverse, List.reverse_append, List.reverse_replicate] at this
  exact this

theorem posixSplitLaw_proven : PosixSplitLaw := by
  intro p k h t hs
  simp only [splitP, fspath, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hs
  obtain ⟨rfl, rfl⟩ := hs
  simp only
  constructor
  · apply not_mem_drop
    omega
  · have hc := rstrip_parts isSepP (p.take (rfind 47 p + 1).toNat) 47 (by simpa [isSepP] using fun x h => h)
    split
    · obtain ⟨n, hn⟩ := hc
      refine ⟨n, ?_⟩
      rw [← hn, List.take_append_drop]
    · exact ⟨0, by simp⟩

/-! ### `join` -/

/-- `posixpath.join` of two values of a kind: an absolute second part replaces the first, an empty
first part gives the second, a first part ending in `/` gets no second slash, and otherwise one goes
between them. An empty second part leaves a trailing slash, as the docstring says. -/
def JoinLaw : Prop :=
  ∀ (a b : List Nat) (k : Bool),
    joinP (.val ⟨k, a⟩) [.val ⟨k, b⟩] =
      .ok ⟨k, if b.head? == some 47 ∨ a.isEmpty then b
        else if a.getLast? == some 47 then a ++ b else a ++ [47] ++ b⟩

theorem joinLaw_proven : JoinLaw := by
  intro a b k
  simp only [joinP, fspath, bind, Except.bind, joinP.go, joinStep, bne_self_eq_false,
    Bool.false_eq_true, if_false]
  by_cases h1 : b.head? == some 47 ∨ a.isEmpty
  · simp only [if_pos h1]
  · simp only [if_neg h1]
    by_cases h2 : a.getLast? == some 47
    · simp only [h2, if_true]
    · simp only [h2, if_false, Bool.false_eq_true]

/-- Mixing `str` and `bytes` is the same error whichever way the `bytes` got there. Through an
`os.PathLike` it is reported as that object not being a path. -/
def JoinMixMessage : Prop :=
  ∀ (a b : List Nat) (c : String),
    joinP (.val ⟨false, a⟩) [.fsp c (.ok (some ⟨true, b⟩)) ""] = .error mixErr

/-- The exception of a result. -/
def errOf {α : Type} : Py α → Option PyExc
  | .error e => some e
  | .ok _ => none

theorem joinMixMessage_refuted : ¬JoinMixMessage := by
  intro h
  have := congrArg errOf (h [] [] "PL")
  revert this
  decide +kernel

/-- An exception from `__fspath__` reaches the caller of `join`. A `TypeError` or `AttributeError` is
replaced by a message that says the object is not a path. -/
def JoinKeepsFspathError : Prop :=
  ∀ (a : List Nat) (e : PyExc) (c : String),
    joinP (.val ⟨false, a⟩) [.fsp c (.error e) ""] = .error e

theorem joinKeepsFspathError_refuted : ¬JoinKeepsFspathError := by
  intro h
  have := congrArg errOf (h [] (.typeError "mine") "PL")
  revert this
  decide +kernel

/-- `ntpath.join` of two values of a kind, when the second has a drive and a root: it is the result,
whatever came first. -/
def NtJoinAbsolute : Prop :=
  ∀ (a b d r t : List Nat) (k : Bool), splitrootN b = (d, r, t) → d ≠ [] → r ≠ [] →
    d ++ r ++ t = b → joinN (.val ⟨k, a⟩) [.val ⟨k, b⟩] = .ok ⟨k, b⟩

theorem ntJoinAbsolute_proven : NtJoinAbsolute := by
  intro a b d r t k h1 h2 h3 h4
  have hr : r.isEmpty = false := by simpa using h3
  have hd : d.isEmpty = false := by simpa using h2
  simp only [joinN, fspath, bind, Except.bind, joinN.go, joinStepN, h1, hr, hd]
  simp [cat, ← h4, hr, List.append_assoc]

/-- Other exceptions from `__fspath__` do reach it. -/
def JoinPassesOtherErrors : Prop :=
  ∀ (a m : List Nat) (msg c : String) (rest : List PathArg),
    joinP (.val ⟨false, a⟩) (.fsp c (.error (.valueError msg)) "" :: rest) = .error (.valueError msg)

theorem joinPassesOtherErrors_proven : JoinPassesOtherErrors := by
  intro a m msg c rest
  simp only [joinP, fspath, bind, Except.bind, joinP.go, joinStep]

/-! ### `normpath` -/

/-- `normpathN` of a path with no drive and no root keeps it that way. -/
def noRoot (p : List Nat) : Bool :=
  let (d, r, _) := splitrootN p
  d.isEmpty && r.isEmpty

/-- `ntpath.normpath` does not change what a path refers to in the way of turning a relative path
into one with a drive: the docs say it collapses separators and up-level references. -/
def NtNormpathKeepsRelative : Prop :=
  ∀ p : List Nat, noRoot p = true → noRoot (normpathN p) = true

theorem ntNormpathKeepsRelative_refuted : ¬NtNormpathKeepsRelative := by
  intro h
  have := h [46, 92, 99, 58, 92, 119] (by decide +kernel)
  revert this
  decide +kernel

/-- C `_Py_normpath_and_size` and the Python fallback of `posixpath.normpath` agree, on every path. -/
def PosixNormpathTwin : Prop := ∀ p : List Nat, normpathC p = normpathPy p

/-- `posixpath.normpath` is idempotent. -/
def PosixNormpathIdempotent : Prop := ∀ p : List Nat, normpathPy (normpathPy p) = normpathPy p

end PyLean.TextLibs.Path
