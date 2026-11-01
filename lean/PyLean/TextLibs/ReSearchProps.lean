import PyLean.TextLibs.ReCompileProps

/-!
The literal-prefix search of `SRE(search)`, `Modules/_sre/sre_lib.h:1829-1878`, against the search it
replaces. `searchOuter` and `searchInner` are the KMP scan: on a partial match they move the pattern
along by the overlap table and never look at the same text twice. `NaiveR` tries each start in turn,
and runs the rest of the pattern wherever the prefix occurs. The scan tries the same starts in the
same order, with the same state, however the prefix overlaps itself.
-/

namespace PyLean.TextLibs.Re

open PyLean

set_option linter.unusedSimpArgs false

/-- The `INFO` words of a prefix of two or more characters: the prefix, then its overlap table. -/
structure PrefixBlock (e : Env) (pfx plen : Nat) (P : List Nat) : Prop where
  len : P.length = plen
  two : 2 ≤ plen
  word : ∀ i, i < plen → e.c (pfx + i) = P.getD i 0
  over : ∀ i, 1 ≤ i → i ≤ plen → e.c (pfx + plen - 1 + i) = (overlapTable P).getD (i - 1) 0

/-- `P` occurs at `q`, inside `end`. -/
def Occurs (e : Env) (P : List Nat) (q : Nat) : Prop :=
  q + P.length ≤ e.endp ∧ ∀ j, j < P.length → e.ch (q + j) = P.getD j 0

/-- The search without the scan: each start in turn, and the rest of the pattern where `P` occurs.
The state after a failed attempt is the one `RESET_CAPTURE_GROUP` leaves. -/
inductive NaiveR (e : Env) (code skip fl : Nat) (P : List Nat) : Nat → SSt → SR → Prop
  | stop {q st} : q + P.length > e.endp → NaiveR e code skip fl P q st (some (false, st))
  | miss {q st r} : q + P.length ≤ e.endp → ¬Occurs e P q → NaiveR e code skip fl P (q + 1) st r →
      NaiveR e code skip fl P q st r
  | lit {q st} : Occurs e P q → fl &&& 2 ≠ 0 →
      NaiveR e code skip fl P q st (some (true, { st with start := q, ptr := q + skip }))
  | hit {q st st2} : Occurs e P q → ¬(fl &&& 2 ≠ 0) →
      matchAt e e.mfuel (code + 2 * skip) false { st with start := q, ptr := q + skip } = some (true, st2) →
      NaiveR e code skip fl P q st (some (true, st2))
  | fail {q st st2 r} : Occurs e P q → ¬(fl &&& 2 ≠ 0) →
      matchAt e e.mfuel (code + 2 * skip) false { st with start := q, ptr := q + skip } = some (false, st2) →
      NaiveR e code skip fl P (q + 1) (resetGroups st2) r → NaiveR e code skip fl P q st r

/-- Two results that say the same: a found match in the same state, or nothing. -/
def Same : SR → SR → Prop
  | some (true, a), some (true, b) => a = b
  | some (false, _), some (false, _) => True
  | _, _ => False

theorem same_refl (r : SR) (h : r ≠ none) : Same r r := by
  match r, h with
  | some (true, _), _ => exact rfl
  | some (false, _), _ => exact trivial
  | none, h => exact absurd rfl h

theorem same_trans {a b c : SR} (h1 : Same a b) (h2 : Same b c) : Same a c := by
  match a, b, c, h1, h2 with
  | some (true, _), some (true, _), some (true, _), h1, h2 => exact h1.trans h2
  | some (false, _), some (false, _), some (false, _), _, _ => exact trivial

theorem naive_past {e : Env} {code skip fl : Nat} {P : List Nat} {q : Nat} {st : SSt} {r : SR}
    (h : NaiveR e code skip fl P q st r) (hq : q + P.length > e.endp) : r = some (false, st) := by
  cases h with
  | stop _ => rfl
  | miss h1 _ _ => omega
  | lit h1 _ => have := h1.1; omega
  | hit h1 _ _ => have := h1.1; omega
  | fail h1 _ _ _ => have := h1.1; omega

theorem naive_some {e : Env} {code skip fl : Nat} {P : List Nat} {q : Nat} {st : SSt} {r : SR}
    (h : NaiveR e code skip fl P q st r) : r ≠ none := by
  induction h with
  | stop _ => simp
  | miss _ _ _ ih => exact ih
  | lit _ _ => simp
  | hit _ _ _ => simp
  | fail _ _ _ _ ih => exact ih

/-- Starts where `P` does not occur can be stepped over. -/
theorem naive_skip {e : Env} {code skip fl : Nat} {P : List Nat} (hP : 1 ≤ P.length) {st : SSt} {r : SR} :
    ∀ (n a b : Nat), b = a + n → (∀ q, a ≤ q → q < b → ¬Occurs e P q) →
    NaiveR e code skip fl P b st r → ∃ r', NaiveR e code skip fl P a st r' ∧ Same r r' := by
  intro n
  induction n with
  | zero =>
    intro a b hb _ h
    subst hb
    exact ⟨r, h, same_refl r (naive_some h)⟩
  | succ n ih =>
    intro a b hb hn h
    by_cases hq : a + P.length > e.endp
    · have hq2 : b + P.length > e.endp := by omega
      have := naive_past h hq2
      subst this
      exact ⟨_, .stop hq, trivial⟩
    · obtain ⟨r', h1, h2⟩ := ih (a + 1) b (by omega) (fun q h3 h4 => hn q (by omega) h4) h
      exact ⟨r', .miss (by omega) (hn a (by omega) (by omega)) h1, h2⟩

/-- `i` characters of `P` end just before `ptr`. -/
def Partial (e : Env) (P : List Nat) (ptr i : Nat) : Prop :=
  i ≤ ptr ∧ ∀ j, j < i → e.ch (ptr - i + j) = P.getD j 0

/-- The table's move skips no occurrence: a start between the old one and the new one would make a
border longer than the longest. -/
theorem no_occ_between {e : Env} {P : List Nat} {K i : Nat} (hi : 1 ≤ i) (hiP : i ≤ P.length)
    (hw : Partial e P K i) (ht : IsMaxBorder P (i - 1) ((overlapTable P).getD (i - 1) 0)) :
    ∀ q, K - i < q → q < K - (overlapTable P).getD (i - 1) 0 → ¬Occurs e P q := by
  intro q h1 h2 hocc
  have hK := hw.1
  have hle := ht.1.1
  have hm : K - q ≤ i - 1 := by omega
  have hb : Border P (i - 1) (K - q) := by
    refine ⟨hm, fun j hj => ?_⟩
    have e1 := hocc.2 j (by omega)
    have e2 := hw.2 (i - (K - q) + j) (by omega)
    rw [show K - i + (i - (K - q) + j) = q + j by omega] at e2
    rw [← e1, e2]
    congr 1
    omega
  have := ht.2 _ hb
  omega

/-- What the table's move leaves is a partial match. -/
theorem partial_border {e : Env} {P : List Nat} {K i t : Nat} (hw : Partial e P K i)
    (ht : Border P (i - 1) t) (hi : 1 ≤ i) : Partial e P K t := by
  have h0 := ht.1
  have hK := hw.1
  refine ⟨by omega, fun j hj => ?_⟩
  have e1 := ht.2 j hj
  have e2 := hw.2 (i - t + j) (by omega)
  rw [e1, show K - t + j = K - i + (i - t + j) by omega, e2]
  congr 1
  omega

theorem outer_succ (e : Env) (code plen skip fl pfx fuel ptr : Nat) (st : SSt) :
    searchOuter e code plen skip fl pfx (fuel + 1) ptr st =
      if ptr ≥ e.endp then some (false, st)
      else
        if !(e.ch ptr == e.c pfx) then
          if ptr + 1 ≥ e.endp then some (false, st)
          else searchOuter e code plen skip fl pfx fuel (ptr + 1) st
        else if ptr + 1 ≥ e.endp then some (false, st)
        else searchInner e code plen skip fl pfx fuel (ptr + 1) 1 { st with mustAdvance := false } := by
  rw [searchOuter]

theorem inner_succ (e : Env) (code plen skip fl pfx fuel ptr i : Nat) (st : SSt) :
    searchInner e code plen skip fl pfx (fuel + 1) ptr i st =
      let next (ptr i : Nat) (st : SSt) : SR :=
        let i := e.c (pfx + plen - 1 + i)
        if i != 0 then searchInner e code plen skip fl pfx fuel ptr i st
        else searchOuter e code plen skip fl pfx fuel ptr st
      if e.ch ptr == e.c (pfx + i) then
        let i := i + 1
        if i != plen then
          let ptr := ptr + 1
          if ptr ≥ e.endp then some (false, st)
          else searchInner e code plen skip fl pfx fuel ptr i st
        else
          let st := { st with start := ptr + 1 - plen, ptr := ptr + 1 + skip - plen }
          if fl &&& 2 != 0 then some (true, st)
          else
            match matchAt e e.mfuel (code + 2 * skip) false st with
            | none => none
            | some (true, st) => some (true, st)
            | some (false, st) =>
              let ptr := ptr + 1
              if ptr ≥ e.endp then some (false, st)
              else next ptr i (resetGroups st)
      else next ptr i st := by
  rw [searchInner]
  rfl

theorem st_clear (st : SSt) (h : st.mustAdvance = false) : { st with mustAdvance := false } = st := by
  cases st
  simp_all

theorem reset_must (st : SSt) (h : st.mustAdvance = false) : (resetGroups st).mustAdvance = false := h

section Scan

variable {e : Env} {code skip fl pfx plen : Nat} {P : List Nat}

/-- Each state a scan can be in: the two functions, by the fuel they share. -/
theorem scan_go (hb : PrefixBlock e pfx plen P)
    (hM : ∀ (s : SSt) (r : Bool × SSt), s.mustAdvance = false →
      matchAt e e.mfuel (code + 2 * skip) false s = some r → r.2.mustAdvance = false) :
    ∀ fuel : Nat,
    (∀ (ptr : Nat) (st : SSt) (r : Bool × SSt), st.mustAdvance = false →
      searchOuter e code plen skip fl pfx fuel ptr st = some r →
      ∃ r', NaiveR e code skip fl P ptr st r' ∧ Same (some r) r') ∧
    (∀ (ptr i : Nat) (st : SSt) (r : Bool × SSt), st.mustAdvance = false → 1 ≤ i → i < plen →
      ptr < e.endp → Partial e P ptr i →
      searchInner e code plen skip fl pfx fuel ptr i st = some r →
      ∃ r', NaiveR e code skip fl P (ptr - i) st r' ∧ Same (some r) r') := by
  have hP := hb.len
  have h2 := hb.two
  have hP1 : 1 ≤ P.length := by omega
  have hT := overlapTableLaw_proven P
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨fun ptr st r _ h => ?_, fun ptr i st r _ _ _ _ _ h => ?_⟩
    · simp [searchOuter] at h
    · simp [searchInner] at h
  | succ fuel ih =>
    obtain ⟨ihO, ihI⟩ := ih
    /- The move by the table, from `i` characters ending before `K`. -/
    have move : ∀ (K i : Nat) (st : SSt) (r : Bool × SSt), st.mustAdvance = false → 1 ≤ i → i ≤ plen →
        K < e.endp → Partial e P K i →
        (let i := e.c (pfx + plen - 1 + i)
         if i != 0 then searchInner e code plen skip fl pfx fuel K i st
         else searchOuter e code plen skip fl pfx fuel K st) = some r →
        ∃ r', NaiveR e code skip fl P (K - i + 1) st r' ∧ Same (some r) r' ∧ True ∨
          NaiveR e code skip fl P (K - (overlapTable P).getD (i - 1) 0) st r' ∧ Same (some r) r' := by
      intro K i st r hm h1 h3 hK hw h
      have hover := hb.over i h1 h3
      have hMax := hT.2 (i - 1) (by omega)
      simp only [hover] at h
      generalize ht : (overlapTable P).getD (i - 1) 0 = t at *
      by_cases h0 : t = 0
      · subst h0
        simp only [bne_self_eq_false, Bool.false_eq_true, if_false] at h
        obtain ⟨r', h4, h5⟩ := ihO K st r hm h
        exact ⟨r', .inr ⟨by simpa using h4, h5⟩⟩
      · have hne : (t != 0) = true := by simpa using h0
        simp only [hne, if_true] at h
        have hle := hMax.1.1
        obtain ⟨r', h4, h5⟩ := ihI K t st r hm (by omega) (by omega) hK
          (partial_border hw hMax.1 h1) h
        exact ⟨r', .inr ⟨h4, h5⟩⟩
    have moved : ∀ (a K i : Nat) (st : SSt) (r : Bool × SSt), st.mustAdvance = false → 1 ≤ i → i ≤ plen →
        K < e.endp → Partial e P K i → a = K - i + 1 →
        (let i := e.c (pfx + plen - 1 + i)
         if i != 0 then searchInner e code plen skip fl pfx fuel K i st
         else searchOuter e code plen skip fl pfx fuel K st) = some r →
        ∃ r', NaiveR e code skip fl P a st r' ∧ Same (some r) r' := by
      intro a K i st r hm h1 h3 hK hw ha h
      obtain ⟨r', h4⟩ := move K i st r hm h1 h3 hK hw h
      have hMax := hT.2 (i - 1) (by omega)
      have hle := hMax.1.1
      have hKi := hw.1
      rcases h4 with ⟨h5, h6, _⟩ | ⟨h5, h6⟩
      · exact ⟨r', ha ▸ h5, h6⟩
      · obtain ⟨r2, h7, h8⟩ := naive_skip hP1 (K - (overlapTable P).getD (i - 1) 0 - a) a _ (by omega)
          (fun q h9 h10 => no_occ_between h1 (by omega) hw hMax q (by omega) h10) h5
        exact ⟨r2, h7, same_trans h6 h8⟩
    refine ⟨fun ptr st r hm h => ?_, fun ptr i st r hm h1 h3 hK hw h => ?_⟩
    · rw [outer_succ] at h
      have hw0 := hb.word 0 (by omega)
      rw [Nat.add_zero] at hw0
      by_cases hend : ptr ≥ e.endp
      · rw [if_pos hend] at h
        cases h
        exact ⟨_, .stop (by omega), trivial⟩
      · rw [if_neg hend] at h
        by_cases hhit : (!(e.ch ptr == e.c pfx)) = true
        · rw [if_pos hhit] at h
          by_cases hend2 : ptr + 1 ≥ e.endp
          · rw [if_pos hend2] at h
            cases h
            exact ⟨_, .stop (by omega), trivial⟩
          · rw [if_neg hend2] at h
            obtain ⟨r', h4, h5⟩ := ihO (ptr + 1) st r hm h
            have hne : e.ch ptr ≠ e.c pfx := by simpa using hhit
            obtain ⟨r2, h7, h8⟩ := naive_skip hP1 1 ptr (ptr + 1) rfl (fun q h9 h10 hocc => by
              have : q = ptr := by omega
              subst this
              have := hocc.2 0 (by omega)
              rw [Nat.add_zero, ← hw0] at this
              exact hne this) h4
            exact ⟨r2, h7, same_trans h5 h8⟩
        · rw [if_neg hhit] at h
          have heq : e.ch ptr = e.c pfx := by simpa using hhit
          by_cases hend2 : ptr + 1 ≥ e.endp
          · rw [if_pos hend2] at h
            cases h
            exact ⟨_, .stop (by omega), trivial⟩
          · rw [if_neg hend2, st_clear st hm] at h
            have hw1 : Partial e P (ptr + 1) 1 := by
              refine ⟨by omega, fun j hj => ?_⟩
              have : j = 0 := by omega
              subst this
              simpa [heq] using hw0
            have := ihI (ptr + 1) 1 st r hm (by omega) (by omega) (by omega) hw1 h
            simpa using this
    · rw [inner_succ] at h
      have hq : ptr - i + i = ptr := by have := hw.1; omega
      have hword := hb.word i h3
      by_cases hc : (e.ch ptr == e.c (pfx + i)) = true
      · rw [if_pos hc] at h
        have hc' : e.ch ptr = P.getD i 0 := by
          rw [← hword]
          simpa using hc
        have hw2 : Partial e P (ptr + 1) (i + 1) := by
          refine ⟨by have := hw.1; omega, fun j hj => ?_⟩
          by_cases hji : j = i
          · subst hji
            rw [show ptr + 1 - (j + 1) + j = ptr by have := hw.1; omega]
            exact hc'
          · rw [show ptr + 1 - (i + 1) + j = ptr - i + j by have := hw.1; omega]
            exact hw.2 j (by omega)
        by_cases hlast : (i + 1 != plen) = true
        · simp only [hlast, if_true] at h
          have hne : i + 1 ≠ plen := by simpa using hlast
          by_cases hend : ptr + 1 ≥ e.endp
          · simp only [hend, if_true] at h
            cases h
            exact ⟨_, .stop (by omega), trivial⟩
          · simp only [hend, if_false] at h
            have := ihI (ptr + 1) (i + 1) st r hm (by omega) (by omega) (by omega) hw2 h
            rwa [show ptr + 1 - (i + 1) = ptr - i by have := hw.1; omega] at this
        · have heqi : i + 1 = plen := by simpa using hlast
          simp only [hlast, Bool.false_eq_true, if_false] at h
          have hocc : Occurs e P (ptr - i) := by
            refine ⟨by omega, fun j hj => ?_⟩
            have := hw2.2 j (by omega)
            rwa [show ptr + 1 - (i + 1) + j = ptr - i + j by have := hw.1; omega] at this
          have hst : ({ st with start := ptr + 1 - plen, ptr := ptr + 1 + skip - plen } : SSt) =
              { st with start := ptr - i, ptr := ptr - i + skip } := by
            have e1 : ptr + 1 - plen = ptr - i := by omega
            have e2 : ptr + 1 + skip - plen = ptr - i + skip := by have := hw.1; omega
            rw [e1, e2]
          rw [hst] at h
          by_cases hlit : (fl &&& 2) ≠ 0
          · have : (fl &&& 2 != 0) = true := by simpa using hlit
            simp only [this, if_true] at h
            cases h
            exact ⟨_, .lit hocc hlit, rfl⟩
          · have : (fl &&& 2 != 0) = false := by simpa using hlit
            simp only [this, Bool.false_eq_true, if_false] at h
            cases hmatch : matchAt e e.mfuel (code + 2 * skip) false
                { st with start := ptr - i, ptr := ptr - i + skip } with
            | none =>
              rw [hmatch] at h
              cases h
            | some x =>
              obtain ⟨ok, st2⟩ := x
              rw [hmatch] at h
              have hm2 : st2.mustAdvance = false :=
                hM { st with start := ptr - i, ptr := ptr - i + skip } (ok, st2) hm hmatch
              cases ok with
              | true =>
                cases h
                exact ⟨_, .hit hocc hlit hmatch, rfl⟩
              | false =>
                by_cases hend : ptr + 1 ≥ e.endp
                · simp only [hend, if_true] at h
                  cases h
                  exact ⟨_, .fail hocc hlit hmatch (.stop (by omega)), trivial⟩
                · simp only [hend, if_false] at h
                  have hw3 : Partial e P (ptr + 1) plen := heqi ▸ hw2
                  rw [heqi] at h
                  obtain ⟨r2, h7, h8⟩ := moved (ptr - i + 1) (ptr + 1) plen _ r (reset_must st2 hm2)
                    (by omega) (Nat.le_refl _) (by omega) hw3 (by omega) h
                  exact ⟨r2, .fail hocc hlit hmatch h7, h8⟩
      · rw [if_neg hc] at h
        have hne : e.ch ptr ≠ e.c (pfx + i) := by simpa using hc
        obtain ⟨r2, h7, h8⟩ := moved (ptr - i + 1) ptr i st r hm h1 (by omega) hK hw rfl h
        have hno : ¬Occurs e P (ptr - i) := by
          intro hocc
          have := hocc.2 i (by omega)
          rw [hq, ← hword] at this
          exact hne this
        by_cases hend : ptr - i + P.length > e.endp
        · have hq2 : ptr - i + 1 + P.length > e.endp := by omega
          have h9 := naive_past h7 hq2
          subst h9
          exact ⟨_, .stop hend, by
            cases r with
            | mk a b =>
              cases a with
              | true => exact absurd h8 (by simp [Same])
              | false => exact trivial⟩
        · exact ⟨r2, .miss (by omega) hno h7, h8⟩

end Scan

/-- The prefix scan finds what trying each start finds: the same match at the same start, in the
same state, or nothing. For every prefix and every text, whatever the rest of the pattern does; a
result the model can give at all is the naive one.

The hypotheses are the shape of the `INFO` block, which `_compile_info` writes, and that
`SRE(match)` never sets `must_advance`, which holds by inspection of `sre_lib.h`: it only reads it. -/
def SearchPrefixLaw : Prop :=
  ∀ (e : Env) (code skip fl pfx plen fuel ptr : Nat) (P : List Nat) (st : SSt) (r : Bool × SSt),
    PrefixBlock e pfx plen P →
    (∀ (s : SSt) (r : Bool × SSt), s.mustAdvance = false →
      matchAt e e.mfuel (code + 2 * skip) false s = some r → r.2.mustAdvance = false) →
    st.mustAdvance = false →
    searchOuter e code plen skip fl pfx fuel ptr st = some r →
    ∃ r', NaiveR e code skip fl P ptr st r' ∧ Same (some r) r'

theorem searchPrefixLaw_proven : SearchPrefixLaw := by
  intro e code skip fl pfx plen fuel ptr P st r hb hM hm h
  exact (scan_go hb hM fuel).1 ptr st r hm h

/-! ### The prefix itself -/

theorem getD_app_right (a b : List Nat) (i : Nat) : (a ++ b).getD (a.length + i) 0 = b.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

/-- `compileInfoW` writes the words `PrefixBlock` asks for. -/
def CompiledPrefixBlock : Prop :=
  ∀ (w : Nat × Nat) (p : List Node) (flags : Nat) (P : List Nat) (skip : Option Nat) (got : Bool)
    (rest : List Nat) (s : Array Nat) (endp : Nat) (ma : Bool),
    w.1 ≠ 0 → ¬(hasFlag flags FLAG_IGNORECASE = true ∧ hasFlag flags FLAG_LOCALE = true) →
    literalPrefix (p.length + 64) p flags [] none = (P, skip, got) → 2 ≤ P.length →
    PrefixBlock ⟨(compileInfoW w p flags ++ rest).toArray, s, endp, ma⟩ 7 P.length P

theorem compiledPrefixBlock_proven : CompiledPrefixBlock := by
  intro w p flags P skip got rest s endp ma h0 hloc hlit h2
  obtain ⟨lo, hi⟩ := w
  have hl : (hasFlag flags FLAG_IGNORECASE && hasFlag flags FLAG_LOCALE) = false := by
    cases h1 : hasFlag flags FLAG_IGNORECASE <;> cases h3 : hasFlag flags FLAG_LOCALE <;> simp_all
  have hne : P.isEmpty = false := by
    cases P with
    | nil => simp at h2
    | cons _ _ => rfl
  have hc : ∃ m l h0 n, compileInfoW (lo, hi) p flags =
      [OP_INFO, n, m, l, h0, P.length, skip.getD P.length] ++ P ++ overlapTable P := by
    simp only [ne_eq] at h0
    simp only [compileInfoW, if_neg h0, hl, Bool.false_eq_true, if_false, hlit, Bool.false_or,
      hne, Bool.not_false, if_true, List.length_cons, List.cons_append, List.append_assoc, List.nil_append,
      Bool.not_true]
    exact ⟨_, _, _, _, rfl⟩
  obtain ⟨m, l, h3, n, hc⟩ := hc
  have hat : ∀ i, (compileInfoW (lo, hi) p flags ++ rest).toArray.getD (7 + i) 0 =
      (P ++ overlapTable P ++ rest).getD i 0 := by
    intro i
    rw [hc]
    simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, List.getElem?_append,
      Nat.add_comm 7 i]
  have hO := (overlapTableLaw_proven P).1
  refine ⟨rfl, h2, fun i hlt => ?_, fun i h4 h5 => ?_⟩
  · show (compileInfoW (lo, hi) p flags ++ rest).toArray.getD (7 + i) 0 = _
    rw [hat, List.append_assoc, getD_app_left _ _ _ hlt]
  · show (compileInfoW (lo, hi) p flags ++ rest).toArray.getD (7 + P.length - 1 + i) 0 = _
    rw [show 7 + P.length - 1 + i = 7 + (P.length + (i - 1)) by omega, hat, List.append_assoc,
      getD_app_right, getD_app_left _ _ _ (by omega)]

/-- The first characters a match must have. -/
def HoldsAt (c : SemCfg) (X : List Nat) (pos : Nat) : Prop :=
  ∀ j, j < X.length → pos + j < c.endp ∧ c.ch (pos + j) = X.getD j 0

theorem holds_nil (c : SemCfg) (pos : Nat) : HoldsAt c [] pos := fun _ h => by simp at h

theorem holds_cons {c : SemCfg} {a pos : Nat} {X : List Nat} (h1 : pos < c.endp) (h2 : c.ch pos = a)
    (h3 : HoldsAt c X (pos + 1)) : HoldsAt c (a :: X) pos := by
  intro j hj
  cases j with
  | zero => simpa using ⟨h1, h2⟩
  | succ j =>
    have := h3 j (by simpa using hj)
    rw [show pos + 1 + j = pos + (j + 1) by omega] at this
    simpa using this

theorem holds_append {c : SemCfg} {X Y : List Nat} {pos : Nat} (h1 : HoldsAt c X pos)
    (h2 : HoldsAt c Y (pos + X.length)) : HoldsAt c (X ++ Y) pos := by
  intro j hj
  by_cases h : j < X.length
  · rw [getD_app_left _ _ _ h]
    exact h1 j h
  · have := h2 (j - X.length) (by simp at hj; omega)
    rw [show pos + X.length + (j - X.length) = pos + j by omega] at this
    refine ⟨this.1, ?_⟩
    rw [this.2]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]

theorem sem_cons (c : SemCfg) (f : Nat) (n : Node) (ns : List Node) (flags pos : Nat) (st : SemSt)
    (k : Nat → SemSt → SemR) :
    semSeq c (f + 1) (n :: ns) flags pos st k =
      semNode c f n flags pos st (fun p st => semSeq c f ns flags p st k) := by
  rw [semSeq]

/-- A literal the prefix keeps is that character: `_get_iscased` and `_compile` agree on what is
cased, and an uncased literal compiles to `LITERAL`. -/
theorem litEq_uncased (flags a c : Nat)
    (hloc : ¬(hasFlag flags FLAG_IGNORECASE = true ∧ hasFlag flags FLAG_LOCALE = true))
    (hun : match getIscased flags with
      | some f => f a = false
      | none => True)
    (h : litEq flags a c = true) : c = a := by
  unfold litEq at h
  by_cases hi : hasFlag flags FLAG_IGNORECASE = true
  · have hl : hasFlag flags FLAG_LOCALE = false := by
      cases h1 : hasFlag flags FLAG_LOCALE
      · rfl
      · exact absurd ⟨hi, h1⟩ hloc
    simp only [hi, hl, Bool.not_true, Bool.false_eq_true, if_false] at h
    unfold getIscased at hun
    simp only [hi, Bool.not_true, Bool.false_eq_true, if_false] at hun
    unfold caseFor at h
    by_cases hu : hasFlag flags FLAG_UNICODE = true
    · simp only [hi, hl, hu, Bool.not_false, Bool.and_self, if_true] at h hun
      simp only [hun, Bool.not_false, if_true] at h
      simpa using h
    · have hu' : hasFlag flags FLAG_UNICODE = false := by simpa using hu
      simp only [hi, hl, hu', Bool.not_false, Bool.and_self, if_true, Bool.false_eq_true, if_false]
        at h hun
      simp only [hun, Bool.not_false, if_true] at h
      simpa using h
  · have hi' : hasFlag flags FLAG_IGNORECASE = false := by simpa using hi
    simp only [hi', Bool.not_false, if_true] at h
    simpa using h

/-- `_get_literal_prefix`: wherever the semantics finds a match, the text there starts with the
prefix; and when the whole list was literal, the continuation runs right after it. -/
theorem prefix_sound (c : SemCfg) : ∀ (fuel : Nat) (items : List Node) (flags : Nat) (acc P : List Nat)
    (skip s : Option Nat) (got : Bool), literalPrefix fuel items flags acc skip = (P, s, got) →
    ¬(hasFlag flags FLAG_IGNORECASE = true ∧ hasFlag flags FLAG_LOCALE = true) →
    ∃ X, P = acc ++ X ∧ ∀ (f pos : Nat) (st : SemSt) (k : Nat → SemSt → SemR) (r : Nat × SemSt),
      semSeq c f items flags pos st k = some (some r) →
      HoldsAt c X pos ∧ (got = true → ∃ st', k (pos + X.length) st' = some (some r)) := by
  intro fuel
  induction fuel with
  | zero =>
    intro items flags acc P skip s got h _
    simp only [literalPrefix, Prod.mk.injEq] at h
    obtain ⟨rfl, _, rfl⟩ := h
    exact ⟨[], by simp, fun _ _ _ _ _ _ => ⟨holds_nil _ _, by simp⟩⟩
  | succ fuel ih =>
    intro items flags acc P skip s got h hloc
    match items with
    | [] =>
      simp only [literalPrefix, Prod.mk.injEq] at h
      obtain ⟨rfl, _, rfl⟩ := h
      refine ⟨[], by simp, fun f pos st k r hs => ⟨holds_nil _ _, fun _ => ?_⟩⟩
      cases f with
      | zero => simp [semSeq] at hs
      | succ f => exact ⟨st, by simpa [semSeq] using hs⟩
    | n :: ns =>
      have stop : ∀ (P : List Nat) (hP : P = acc), got = false →
          ∃ X, P = acc ++ X ∧ ∀ (f pos : Nat) (st : SemSt) (k : Nat → SemSt → SemR) (r : Nat × SemSt),
            semSeq c f (n :: ns) flags pos st k = some (some r) →
            HoldsAt c X pos ∧ (got = true → ∃ st', k (pos + X.length) st' = some (some r)) := by
        intro P hP hg
        exact ⟨[], by simp [hP], fun _ _ _ _ _ _ => ⟨holds_nil _ _, by simp [hg]⟩⟩
      match n with
      | .literal av =>
        have step : literalPrefix fuel ns flags (acc ++ [av]) skip = (P, s, got) →
            (match getIscased flags with
             | some f => f av = false
             | none => True) →
            ∃ X, P = acc ++ X ∧ ∀ (f pos : Nat) (st : SemSt) (k : Nat → SemSt → SemR) (r : Nat × SemSt),
              semSeq c f (.literal av :: ns) flags pos st k = some (some r) →
              HoldsAt c X pos ∧ (got = true → ∃ st', k (pos + X.length) st' = some (some r)) := by
          intro h1 hun
          obtain ⟨X, h2, h3⟩ := ih ns flags _ P skip s got h1 hloc
          refine ⟨av :: X, by simp [h2], fun f pos st k r hs => ?_⟩
          cases f with
          | zero => simp [semSeq] at hs
          | succ f =>
            rw [sem_cons] at hs
            cases f with
            | zero => simp [semNode] at hs
            | succ f =>
              have hl : semNode c (f + 1) (.literal av) flags pos st
                  (fun p st => semSeq c (f + 1) ns flags p st k) =
                  if (decide (pos < c.endp) && litEq flags av (c.ch pos)) = true then
                    semSeq c (f + 1) ns flags (pos + 1) st k
                  else some none := by
                simp only [semNode] <;> rfl
              rw [hl] at hs
              by_cases hc : (decide (pos < c.endp) && litEq flags av (c.ch pos)) = true
              · rw [if_pos hc] at hs
                simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
                have ha := litEq_uncased flags av _ hloc hun hc.2
                obtain ⟨h4, h5⟩ := h3 _ _ _ _ _ hs
                refine ⟨holds_cons hc.1 ha h4, fun hg => ?_⟩
                obtain ⟨st', h6⟩ := h5 hg
                refine ⟨st', ?_⟩
                rw [List.length_cons, show pos + (X.length + 1) = pos + 1 + X.length by omega]
                exact h6
              · rw [if_neg hc] at hs
                cases hs
        simp only [literalPrefix] at h
        cases hf : getIscased flags with
        | none =>
          rw [hf] at h
          exact step h (by rw [hf]; trivial)
        | some g =>
          rw [hf] at h
          simp only at h
          cases hv : g av with
          | true =>
            rw [hv] at h
            simp only [if_true, Prod.mk.injEq] at h
            exact stop P h.1.symm h.2.2.symm
          | false =>
            rw [hv] at h
            simp only [Bool.false_eq_true, if_false] at h
            exact step h (by rw [hf]; exact hv)
      | .subpattern group add del p =>
        simp only [literalPrefix] at h
        generalize hf1 : combineFlags flags add del = flags1 at h
        split at h
        · simp only [Prod.mk.injEq] at h
          exact stop P h.1.symm h.2.2.symm
        · rename_i hl
          have hl' : ¬(hasFlag flags1 FLAG_IGNORECASE = true ∧ hasFlag flags1 FLAG_LOCALE = true) := by
            intro h1
            apply hl
            simp [h1.1, h1.2]
          generalize hp : literalPrefix fuel p flags1 [] none = q at h
          obtain ⟨p1, s1, gotAll⟩ := q
          obtain ⟨X1, h2, h3⟩ := ih p flags1 [] p1 none s1 gotAll hp hl'
          simp only [List.nil_append] at h2
          subst h2
          simp only at h
          /- A success of the subpattern is one of its body, with a continuation that ends in `ns`. -/
          have body : ∀ (f pos : Nat) (st : SemSt) (k : Nat → SemSt → SemR) (r : Nat × SemSt),
              semSeq c (f + 1) (.subpattern group add del p :: ns) flags pos st k = some (some r) →
              HoldsAt c p1 pos ∧ (gotAll = true → ∃ st', semSeq c f ns flags (pos + p1.length) st' k = some (some r)) := by
            intro f pos st k r hs
            rw [sem_cons] at hs
            cases f with
            | zero => simp [semNode] at hs
            | succ f =>
              match group with
              | none =>
                have e : semNode c (f + 1) (.subpattern none add del p) flags pos st
                    (fun p st => semSeq c (f + 1) ns flags p st k) =
                    semSeq c f p (combineFlags flags add del) pos st
                      (fun p st => semSeq c (f + 1) ns flags p st k) := by
                  simp only [semNode] <;> rfl
                rw [e, hf1] at hs
                obtain ⟨h4, h5⟩ := h3 _ _ _ _ _ hs
                exact ⟨h4, h5⟩
              | some 0 =>
                have e : semNode c (f + 1) (.subpattern (some 0) add del p) flags pos st
                    (fun p st => semSeq c (f + 1) ns flags p st k) =
                    semSeq c f p (combineFlags flags add del) pos st
                      (fun p st => semSeq c (f + 1) ns flags p st k) := by
                  simp only [semNode] <;> rfl
                rw [e, hf1] at hs
                obtain ⟨h4, h5⟩ := h3 _ _ _ _ _ hs
                exact ⟨h4, h5⟩
              | some (g + 1) =>
                have e : semNode c (f + 1) (.subpattern (some (g + 1)) add del p) flags pos st
                    (fun p st => semSeq c (f + 1) ns flags p st k) =
                    semSeq c f p (combineFlags flags add del) pos (setMark st (2 * g) pos)
                      (fun q st => semSeq c (f + 1) ns flags q
                        { (setMark st (2 * g + 1) q) with last := some (g + 1) } k) := by
                  simp only [semNode] <;> rfl
                rw [e, hf1] at hs
                obtain ⟨h4, h5⟩ := h3 _ _ _ _ _ hs
                refine ⟨h4, fun hg => ?_⟩
                obtain ⟨st', h6⟩ := h5 hg
                exact ⟨_, h6⟩
          cases gotAll with
          | true =>
            simp only [if_true] at h
            obtain ⟨X2, h4, h5⟩ := ih ns flags _ P _ s got h hloc
            refine ⟨p1 ++ X2, by simp [h4], fun f pos st k r hs => ?_⟩
            cases f with
            | zero => simp [semSeq] at hs
            | succ f =>
              obtain ⟨h6, h7⟩ := body f pos st k r hs
              obtain ⟨st', h8⟩ := h7 rfl
              obtain ⟨h9, h10⟩ := h5 _ _ _ _ _ h8
              refine ⟨holds_append h6 h9, fun hg => ?_⟩
              obtain ⟨st2, h11⟩ := h10 hg
              refine ⟨st2, ?_⟩
              rw [List.length_append, ← Nat.add_assoc]
              exact h11
          | false =>
            simp only [Bool.false_eq_true, if_false, Prod.mk.injEq] at h
            obtain ⟨h4, _, h5⟩ := h
            refine ⟨p1, h4.symm, fun f pos st k r hs => ?_⟩
            cases f with
            | zero => simp [semSeq] at hs
            | succ f =>
              exact ⟨(body f pos st k r hs).1, by simp [← h5]⟩
      | .notLiteral _ =>
        simp only [literalPrefix, Prod.mk.injEq] at h
        exact stop P h.1.symm h.2.2.symm
      | .any =>
        simp only [literalPrefix, Prod.mk.injEq] at h
        exact stop P h.1.symm h.2.2.symm
      | .in_ _ =>
        simp only [literalPrefix, Prod.mk.injEq] at h
        exact stop P h.1.symm h.2.2.symm
      | .at_ _ =>
        simp only [literalPrefix, Prod.mk.injEq] at h
        exact stop P h.1.symm h.2.2.symm
      | .groupref _ =>
        simp only [literalPrefix, Prod.mk.injEq] at h
        exact stop P h.1.symm h.2.2.symm
      | .grouprefExists _ _ _ =>
        simp only [literalPrefix, Prod.mk.injEq] at h
        exact stop P h.1.symm h.2.2.symm
      | .branch _ =>
        simp only [literalPrefix, Prod.mk.injEq] at h
        exact stop P h.1.symm h.2.2.symm
      | .repeat_ _ _ _ _ =>
        simp only [literalPrefix, Prod.mk.injEq] at h
        exact stop P h.1.symm h.2.2.symm
      | .atomic _ =>
        simp only [literalPrefix, Prod.mk.injEq] at h
        exact stop P h.1.symm h.2.2.symm
      | .assert_ _ _ =>
        simp only [literalPrefix, Prod.mk.injEq] at h
        exact stop P h.1.symm h.2.2.symm
      | .assertNot _ _ =>
        simp only [literalPrefix, Prod.mk.injEq] at h
        exact stop P h.1.symm h.2.2.symm
      | .failure =>
        simp only [literalPrefix, Prod.mk.injEq] at h
        exact stop P h.1.symm h.2.2.symm

/-- `_get_literal_prefix`: the declarative semantics matches only where the text starts with the
prefix, so a search that starts nowhere else loses nothing. The hypothesis is the guard of
`_compile_info`, which writes no prefix under `IGNORECASE|LOCALE`. -/
def LiteralPrefixSound : Prop :=
  ∀ (c : SemCfg) (p : List Node) (flags fuel f pos : Nat) (P : List Nat) (skip : Option Nat) (got : Bool)
    (st : SemSt) (k : Nat → SemSt → SemR) (r : Nat × SemSt),
    ¬(hasFlag flags FLAG_IGNORECASE = true ∧ hasFlag flags FLAG_LOCALE = true) →
    literalPrefix fuel p flags [] none = (P, skip, got) →
    semSeq c f p flags pos st k = some (some r) → HoldsAt c P pos

theorem literalPrefixSound_proven : LiteralPrefixSound := by
  intro c p flags fuel f pos P skip got st k r hl h hs
  obtain ⟨X, h1, h2⟩ := prefix_sound c fuel p flags [] P none skip got h hl
  simp only [List.nil_append] at h1
  subst h1
  exact (h2 f pos st k r hs).1

end PyLean.TextLibs.Re
