import PyLean.Pickle.LongLineProps

/-! The narrowed `INT` line property: C's strtol fast path against `int()`. -/

namespace PyLean.Pickle

open PyLean

theorem skipSpace_suffix (l : Bytes) : ∃ pre, l = pre ++ skipSpace l := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons a l ih =>
    simp only [skipSpace]
    split
    · obtain ⟨pre, hp⟩ := ih
      exact ⟨a :: pre, by simpa using hp⟩
    · exact ⟨[], rfl⟩

theorem signSplit_suffix (l : Bytes) : ∃ pre, l = pre ++ (signSplit l).2 := by
  unfold signSplit
  split
  · exact ⟨[0x2b], rfl⟩
  · exact ⟨[0x2d], rfl⟩
  · exact ⟨[], rfl⟩

theorem mem_takeWhile_true {p : UInt8 → Bool} {l : Bytes} {x : UInt8} (h : x ∈ l.takeWhile p) :
    p x = true := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    rw [List.takeWhile_cons] at h
    split at h
    · rcases List.mem_cons.mp h with e | e
      · subst e; assumption
      · exact ih e
    · simp at h

theorem scanDigits_all (ds : Bytes) (h : ∀ c ∈ ds, isDigit c = true) (p : Bool) (hne : ds ≠ []) :
    scanDigits p ds = (ds.map (fun c => c.toNat - 48), true, []) := by
  induction ds generalizing p with
  | nil => exact absurd rfl hne
  | cons a ds ih =>
    have ha := h a List.mem_cons_self
    cases ds with
    | nil => simp [scanDigits, ha]
    | cons b r =>
      have := ih (fun c hc => h c (List.mem_cons_of_mem _ hc)) false (by simp)
      rw [scanDigits, if_pos ha, this]
      simp

/-- `lfsBase` on a run of digits. -/
theorem lfsBase_digits (neg : Bool) (ds : Bytes) (h : ∀ c ∈ ds, isDigit c = true) (hne : ds ≠ [])
    (hlen : ds.length ≤ maxStrDigits) :
    lfsBase neg ds = .ok (if neg then -(digitsVal (ds.map (fun c => c.toNat - 48)) : Int)
      else digitsVal (ds.map (fun c => c.toNat - 48))) := by
  have hscan := scanDigits_all ds h false hne
  cases ds with
  | nil => exact absurd rfl hne
  | cons a r =>
    have ha : a ≠ 0x5f := by
      intro e; subst e; have := h _ List.mem_cons_self; simp [isDigit] at this
    have hmap : (List.map (fun c : UInt8 => c.toNat - 48) (a :: r)) ≠ [] := by simp
    have hl : ¬ (List.map (fun c : UInt8 => c.toNat - 48) (a :: r)).length > maxStrDigits := by
      simpa using hlen
    unfold lfsBase
    split
    · rename_i heq; simp at heq; exact absurd heq.1 ha
    · rw [hscan]
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hmap, skipSpace, ne_eq, not_true_eq_false, hl]

theorem split_last_nl (a t body : Bytes) (h : a ++ nl :: t = body ++ [nl]) (hb : nl ∉ body) :
    t = [] ∧ a = body := by
  induction a generalizing body with
  | nil =>
    cases body with
    | nil => simpa using h
    | cons b bs =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (show nl ∈ b :: bs by rw [h.1]; exact List.mem_cons_self) hb
  | cons x a ih =>
    cases body with
    | nil =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
      have := h.2
      simp at this
    | cons b bs =>
      simp only [List.cons_append, List.cons.injEq] at h
      have := ih bs h.2 (fun m => hb (List.mem_cons_of_mem _ m))
      exact ⟨this.1, by rw [h.1, this.2]⟩

theorem isSpace_nl : isSpace nl = true := by decide
theorem isDigit_nl : isDigit nl = false := by decide

/-- The structure of a line on which C's strtol succeeds. -/
theorem strtol_fast (body : Bytes) (hnl : nl ∉ body) (hz : (0 : UInt8) ∉ body) (hne : body ≠ [])
    (hlim : (body.filter isDigit).length ≤ maxStrDigits) (x : Int) (c : Nat)
    (hs : strtol (body ++ [nl]) = (x, c, false))
    (hend : (body ++ [nl]).getD c 0 = nl ∨ (body ++ [nl]).getD c 0 = 0) :
    pyLongFromString (body ++ [nl]) = .ok x ∧
      ∃ pre ds, body = pre ++ ds ∧ ds ≠ [] ∧ ∀ c ∈ ds, isDigit c = true := by
  have hz' : (0 : UInt8) ∉ body ++ [nl] := by
    simp only [List.mem_append, List.mem_singleton, not_or]
    exact ⟨hz, by decide⟩
  generalize hS : body ++ [nl] = s at *
  have hcstr : s.takeWhile (· ≠ 0) = s := takeWhile_ne_zero_of_not_mem hz'
  unfold strtol at hs
  rw [hcstr] at hs
  dsimp only at hs
  obtain ⟨p1, hp1⟩ := skipSpace_suffix s
  obtain ⟨p2, hp2⟩ := signSplit_suffix (skipSpace s)
  generalize hq : signSplit (skipSpace s) = q at *
  obtain ⟨neg, s2⟩ := q
  dsimp only at hs hp2
  have hsplit : s = (p1 ++ p2) ++ s2 := by rw [List.append_assoc, ← hp2]; exact hp1
  have hdr : s2 = s2.takeWhile isDigit ++ s2.dropWhile isDigit := (List.takeWhile_append_dropWhile).symm
  have hdig : ∀ c ∈ s2.takeWhile isDigit, isDigit c = true := fun _ h => mem_takeWhile_true h
  generalize s2.takeWhile isDigit = ds at *
  generalize s2.dropWhile isDigit = rest at *
  by_cases hds : ds = []
  · rw [if_pos hds] at hs
    simp only [Prod.mk.injEq] at hs
    obtain ⟨_, hc, _⟩ := hs
    subst hc
    cases body with
    | nil => exact absurd rfl hne
    | cons b bs =>
      subst hS
      have h0 : b ≠ 0 := fun e => hz (e ▸ List.mem_cons_self)
      have h1 : b ≠ nl := fun e => hnl (e ▸ List.mem_cons_self)
      simp only [List.cons_append, List.getD_cons_zero] at hend
      rcases hend with h | h
      · exact absurd h h1
      · exact absurd h h0
  rw [if_neg hds] at hs
  have hxc : x = (if neg then -(digitsVal (ds.map (fun c => c.toNat - 48)) : Int)
        else digitsVal (ds.map (fun c => c.toNat - 48))) ∧
      c = s.length - (s2.length - ds.length) := by
    generalize (if neg = true then -(digitsVal (ds.map (fun c => c.toNat - 48)) : Int)
        else digitsVal (ds.map (fun c => c.toNat - 48))) = v at hs ⊢
    split at hs
    · simp at hs
    split at hs
    · simp at hs
    · simp only [Prod.mk.injEq, and_true] at hs
      exact ⟨hs.1.symm, hs.2.symm⟩
  obtain ⟨hx, hc⟩ := hxc
  subst hdr
  have hlen : s.length = (p1 ++ p2).length + ds.length + rest.length := by
    rw [hsplit]; simp [Nat.add_assoc]
  have hc2 : c = ((p1 ++ p2) ++ ds).length := by
    rw [hc, hlen]; simp only [List.length_append]; omega
  have hs3 : s = ((p1 ++ p2) ++ ds) ++ rest := by simp [hsplit, List.append_assoc]
  -- the byte after the digits
  cases rest with
  | nil =>
    exfalso
    rw [List.append_nil] at hs3
    obtain ⟨d', e, hde⟩ : ∃ d' e, ds = d' ++ [e] := ⟨_, _, (List.dropLast_concat_getLast hds).symm⟩
    subst hde
    rw [← hS, ← List.append_assoc] at hs3
    have := (List.append_inj' hs3 rfl).2
    simp only [List.cons.injEq, and_true] at this
    have h1 := hdig _ (List.mem_append_right _ (List.mem_singleton.mpr rfl))
    rw [← this, isDigit_nl] at h1
    simp at h1
  | cons r t =>
    have hget : s.getD c 0 = r := by
      rw [hs3, hc2, List.getD_eq_getElem?_getD]
      simp
    rw [hget] at hend
    have hr : r = nl := by
      rcases hend with h | h
      · exact h
      · exfalso; apply hz'; rw [hs3, ← h]; simp
    subst hr
    rw [← hS] at hs3
    have hb := split_last_nl _ _ _ hs3.symm hnl
    obtain ⟨ht, hbody⟩ := hb
    subst ht
    constructor
    · have e1 : pyLongFromString s = lfsBase neg (ds ++ [nl]) := by
        unfold pyLongFromString
        rw [hq]
      have hmem : ds.length ≤ maxStrDigits := by
        refine Nat.le_trans ?_ hlim
        rw [← hbody, List.filter_append, List.length_append]
        have : ds.filter isDigit = ds := List.filter_eq_self.mpr (fun c hc => hdig c hc)
        rw [this]; omega
      rw [e1, lfsBase_append_space neg ds isSpace_nl, lfsBase_digits neg ds hdig hds hmem, hx]
    · exact ⟨p1 ++ p2, ds, hbody.symm, hds, hdig⟩

def sameB {α : Type} [DecidableEq α] : Py α → Py α → Bool
  | .ok a, .ok b => decide (a = b)
  | .error _, .error _ => true
  | _, _ => false

theorem sameOutcome_of_sameB {α : Type} [DecidableEq α] {a b : Py α} (h : sameB a b = true) :
    SameOutcome a b := by
  cases a <;> cases b <;> simp_all [sameB, SameOutcome]

def boolB (a d : UInt8) : Bool :=
  (d == 0x30 || d == 0x31) && (isSpace a || a == 0x2b || (a == 0x2d && d == 0x30))

/-- The 3-byte lines ending in a digit: all that remains of the bool spellings. -/
def checkAD (a k : Nat) : Bool :=
  a == 0 || a == 10 || boolB a.toUInt8 (48 + k).toUInt8 ||
    sameB (cLoadIntLine [a.toUInt8, (48 + k).toUInt8, nl]) (pyLoadIntLine [a.toUInt8, (48 + k).toUInt8, nl])

set_option maxRecDepth 100000 in
theorem two_byte_all : ∀ a < 256, ∀ k < 10, checkAD a k = true := by decide +kernel

/-- `IntLineTwinsNoNul` without lines of more than 4300 digits. -/
def IntLineTwinsNarrow : Prop :=
  ∀ body : Bytes, nl ∉ body → (0 : UInt8) ∉ body → ¬ BoolSpelling body →
    (body.filter isDigit).length ≤ maxStrDigits →
    SameOutcome (cLoadIntLine (body ++ [nl])) (pyLoadIntLine (body ++ [nl]))

theorem boolSpelling_of_boolB {a d : UInt8} (h : boolB a d = true) : BoolSpelling [a, d] := by
  simp only [boolB, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  exact ⟨a, d, rfl, h.1, by rcases h.2 with (h | h) | h <;> simp_all⟩

theorem two_byte_case (a d : UInt8) (hd : isDigit d = true) (ha0 : a ≠ 0) (ha1 : a ≠ nl)
    (hb : ¬ BoolSpelling [a, d]) :
    SameOutcome (cLoadIntLine ([a, d] ++ [nl])) (pyLoadIntLine ([a, d] ++ [nl])) := by
  have hdn : 48 ≤ d.toNat ∧ d.toNat ≤ 57 := by
    simp only [isDigit, Bool.and_eq_true, decide_eq_true_eq] at hd
    exact ⟨UInt8.le_iff_toNat_le.mp hd.1, UInt8.le_iff_toNat_le.mp hd.2⟩
  have hc := two_byte_all a.toNat a.toNat_lt (d.toNat - 48) (by omega)
  have e1 : a.toNat.toUInt8 = a := by simp
  have e2 : (48 + (d.toNat - 48)).toUInt8 = d := by
    rw [show 48 + (d.toNat - 48) = d.toNat by omega]; simp
  simp only [checkAD, e1, e2, Bool.or_eq_true, beq_iff_eq] at hc
  rcases hc with ((h | h) | h) | h
  · exact absurd (by simpa using UInt8.toNat_inj.mp (by simpa using h)) ha0
  · exact absurd (UInt8.toNat_inj.mp (by simpa [nl] using h)) ha1
  · exact absurd (boolSpelling_of_boolB h) hb
  · exact sameOutcome_of_sameB h

theorem intLineTwinsNarrow_proven : IntLineTwinsNarrow := by
  intro body hnl hz hb hlim
  by_cases hne : body = []
  · subst hne
    exact sameOutcome_of_sameB (by decide +kernel)
  have hz' : (0 : UInt8) ∉ body ++ [nl] := by
    simp only [List.mem_append, List.mem_singleton, not_or]
    exact ⟨hz, by decide⟩
  have hlen2 : ¬ (body ++ [nl]).length < 2 := by
    have : body.length ≠ 0 := by simpa using hne
    simp; omega
  have hpy : ∀ v, pyLongFromString (body ++ [nl]) = .ok v → pyIntOfBytes (body ++ [nl]) = .ok v := by
    intro v h
    unfold pyIntOfBytes
    dsimp only
    rw [takeWhile_ne_zero_of_not_mem hz', h]
    simp
  rcases hst : strtol (body ++ [nl]) with ⟨x, c, e⟩
  by_cases hfast : e = false ∧ ((body ++ [nl]).getD c 0 = nl ∨ (body ++ [nl]).getD c 0 = 0)
  · obtain ⟨he, hend⟩ := hfast
    subst he
    obtain ⟨hparse, pre, ds, hbody, hds, hdig⟩ := strtol_fast body hnl hz hne hlim x c hst hend
    by_cases h2 : body.length = 2
    · match body, h2 with
      | [a, d], _ =>
        have hd : isDigit d = true := by
          obtain ⟨d', f, hde⟩ : ∃ d' f, ds = d' ++ [f] := ⟨_, _, (List.dropLast_concat_getLast hds).symm⟩
          subst hde
          have h3 : [a] ++ [d] = (pre ++ d') ++ [f] := by simpa using hbody
          have := (List.append_inj' h3 rfl).2
          simp only [List.cons.injEq, and_true] at this
          rw [this]
          exact hdig _ (List.mem_append_right _ (List.mem_singleton.mpr rfl))
        exact two_byte_case a d hd (fun e => hz (e ▸ List.mem_cons_self))
          (fun e => hnl (e ▸ List.mem_cons_self)) hb
    · have hl3 : ¬ ((body ++ [nl]).length = 3) := by simp; omega
      have hp0 : ¬ (body ++ [nl] = [0x30, 0x30, nl]) := fun e => hl3 (by rw [e]; rfl)
      have hp1 : ¬ (body ++ [nl] = [0x30, 0x31, nl]) := fun e => hl3 (by rw [e]; rfl)
      unfold cLoadIntLine pyLoadIntLine
      rw [if_neg hlen2, if_neg hp0, if_neg hp1, hst, hpy x hparse]
      dsimp only
      generalize (body ++ [nl]).getD c 0 = b0 at hend ⊢
      have hc : ¬ ((false || (b0 != nl && b0 != 0)) = true) := by
        rcases hend with h | h <;> simp [h]
      rw [if_neg hc, if_neg (fun h => hl3 h.1)]
      simp [SameOutcome, Functor.map, Except.map]
  · have hl : ¬ (body ++ [nl] = [0x30, 0x30, nl]) := by
      intro h; rw [h] at hst; apply hfast
      have : strtol [0x30, 0x30, nl] = (0, 2, false) := by decide +kernel
      rw [this] at hst
      simp only [Prod.mk.injEq] at hst
      rw [h, ← hst.2.1, ← hst.2.2]
      exact ⟨rfl, Or.inl rfl⟩
    have hl1 : ¬ (body ++ [nl] = [0x30, 0x31, nl]) := by
      intro h; rw [h] at hst; apply hfast
      have : strtol [0x30, 0x31, nl] = (1, 2, false) := by decide +kernel
      rw [this] at hst
      simp only [Prod.mk.injEq] at hst
      rw [h, ← hst.2.1, ← hst.2.2]
      exact ⟨rfl, Or.inl rfl⟩
    unfold cLoadIntLine pyLoadIntLine
    rw [if_neg hlen2, if_neg hl, if_neg hl1, hst]
    dsimp only
    generalize (body ++ [nl]).getD c 0 = b0 at hfast ⊢
    have hcond : (e || (b0 != nl && b0 != 0)) = true := by
      cases e with
      | true => rfl
      | false =>
        have : ¬ (b0 = nl ∨ b0 = 0) := fun h => hfast ⟨rfl, h⟩
        simp only [not_or] at this
        simp [this.1, this.2]
    rw [if_pos hcond]
    unfold cLongFromLine pyIntOfBytes
    dsimp only
    rw [takeWhile_ne_zero_of_not_mem hz']
    cases hp : pyLongFromString (body ++ [nl]) <;> simp [SameOutcome, Functor.map, Except.map]

end PyLean.Pickle
