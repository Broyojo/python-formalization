import PyLean.TextLibs.BinasciiB64d

/-!
The padding and length refusals of `binascii.a2b_base32`, exactly, on inputs made of data characters
and then pad characters: "Invalid base32-encoded string: ... cannot be 1, 3, or 6 more than a multiple
of 8", "Incorrect padding", "Excess padding not allowed" and "Leading padding not allowed".
-/

namespace PyLean.TextLibs.Binascii

open PyLean

set_option linter.unusedSimpArgs false

theorem decStep32_props (st : Dec32) (v : Nat) (h : st.octa < 8) :
    (decStep32 st v).octa = (st.octa + 1) % 8 ∧ (decStep32 st v).pads = st.pads ∧
      (decStep32 st v).out.length + st.octa * 5 / 8 = st.out.length + (st.octa + 1) * 5 / 8 := by
  obtain ⟨q, p, l, o⟩ := st
  simp only at h
  rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [decStep32]

theorem slow32_dataRun (t : Nat → Nat) (p : Bool) (ig : Option (List Nat)) (h61 : 32 ≤ t 61) :
    ∀ (ds : List Nat) (st : Dec32), (∀ x ∈ ds, t x < 32) → st.pads = 0 → st.octa < 8 →
      ∃ st', (∀ rest, slow32 t p ig (ds ++ rest) st = slow32 t p ig rest st') ∧ st'.octa = (st.octa + ds.length) % 8 ∧
        st'.pads = 0 ∧ st'.out.length + st.octa * 5 / 8 = st.out.length + (st.octa + ds.length) * 5 / 8 := by
  intro ds
  induction ds with
  | nil => intro st _ hp hq; exact ⟨st, fun _ => rfl, by simp; omega, hp, rfl⟩
  | cons x xs ih =>
    intro st hd hp hq
    have hx := hd x (by simp)
    obtain ⟨h1, h2, h3⟩ := decStep32_props st (t x) hq
    obtain ⟨st', e, q', p', o'⟩ := ih (decStep32 st (t x)) (fun y hy => hd y (by simp [hy])) (by rw [h2, hp])
      (by rw [h1]; omega)
    refine ⟨st', fun rest => ?_, ?_, p', ?_⟩
    · rw [List.cons_append, slow32_data t p ig x _ st hx h61 hp]; exact e rest
    · rw [q', h1]; simp; omega
    · rw [h1] at o'
      simp only [List.length_cons]
      omega

theorem slow32_pads (t : Nat → Nat) (ig : Option (List Nat)) (hi : ign ig 61 = false) (st : Dec32)
    (hq : st.octa = 2 ∨ st.octa = 4 ∨ st.octa = 5 ∨ st.octa = 7) :
    ∀ (m j : Nat), st.octa + j ≤ 8 →
      slow32 t true ig (List.replicate m 61) { st with pads := j } =
        if st.octa + j + m ≤ 8 then .ok { st with pads := j + m } else .error (err "Excess padding not allowed") := by
  have hc : (st.octa == 2 || st.octa == 4 || st.octa == 5 || st.octa == 7) = true := by
    rcases hq with h | h | h | h <;> simp [h]
  have hn : (st.octa == 1 || st.octa == 3 || st.octa == 6) = false := by
    rcases hq with h | h | h | h <;> simp [h]
  intro m
  induction m with
  | zero => intro j hj; rw [if_pos (by omega)]; rfl
  | succ m ih =>
    intro j hj
    rw [List.replicate_succ]
    simp only [slow32, beq_self_eq_true, Bool.and_self, if_true, Bool.true_and, hc]
    by_cases hv : st.octa + (j + 1) ≤ 8
    · rw [if_pos (by simpa using hv)]
      have h2 := ih (j + 1) hv
      have e : st.octa + (j + 1) + m = st.octa + j + (m + 1) := by omega
      rw [e, show j + 1 + m = j + (m + 1) by omega] at h2
      exact h2
    · rw [if_neg (by simpa using hv), hi]
      simp only [Bool.false_eq_true, if_false, hn]
      rw [if_neg (by omega), if_neg (by rcases hq with h | h | h | h <;> omega)]

def invMsg32 (n : Nat) : String :=
  s!"Invalid base32-encoded string: number of data characters ({n}) cannot be 1, 3, or 6 more than a multiple of 8"

theorem invMsg32_ne (n : Nat) (m : String) (hm : m.length < 50) : invMsg32 n ≠ m := by
  intro h
  have := congrArg String.length h
  simp only [invMsg32, String.length_append] at this
  have : 50 ≤ (toString "Invalid base32-encoded string: number of data characters (").length := by decide
  omega

theorem fin32_eval (p k : Bool) (st : Dec32) :
    fin32 p k st =
      if (st.octa == 1 || st.octa == 3 || st.octa == 6) = true then
        .error (err (invMsg32 (st.out.length / 5 * 8 + st.octa)))
      else if p = true ∧ st.octa ≠ 0 ∧ st.octa + st.pads < 8 then .error (err "Incorrect padding")
      else if k = true ∧ st.left ≠ 0 then .error (err "Non-zero padding bits") else .ok st.out := by
  simp only [fin32, bind, Except.bind, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw, pure, Except.pure,
    invMsg32]
  repeat' split
  all_goals rfl

/-- What `a2b_base32(t + b'=' * m)` does with `n` data characters in `t`. -/
def padOutcome32 (n m : Nat) : Option String :=
  if n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 6 then some (invMsg32 n)
  else if m = 0 then (if n % 8 = 0 then none else some "Incorrect padding")
  else if n % 8 = 0 then some (if n = 0 then "Leading padding not allowed" else "Excess padding not allowed")
  else if n % 8 + m > 8 then some "Excess padding not allowed"
  else if n % 8 + m < 8 then some "Incorrect padding" else none

/-- The padding and length refusals of `a2b_base32`, exactly, on data characters followed by `m` pad
characters, for every 32-byte alphabet, `ignorechars` without `'='`, and `canonical`. With `n` data
characters and `q = n % 8`: `q` of 1, 3 or 6 is "Invalid base32-encoded string: ... (n) ...", whatever
follows; no pads is "Incorrect padding" unless `q = 0` (so `b'AAAAAAA'` raises it); pads after a whole
group are "Leading padding not allowed" (nothing before) or "Excess padding not allowed"; pads past
`8 - q` are "Excess padding not allowed"; fewer than `8 - q` are "Incorrect padding". Every other message
is `canonical`'s, and the input is accepted (with `canonical=False`) exactly when none of these applies. -/
def B32PadShape : Prop :=
  ∀ (t : List Nat) (m : Nat) (alpha : AlphaArg) (g : List Nat) (k : Bool),
    (alphaChars32 alpha).length = 32 → (∀ x ∈ t, x ∈ alphaChars32 alpha ∧ x ≠ 61) → 61 ∉ g →
    (∀ msg, msg ≠ "Non-zero padding bits" →
      (a2bB32 (.bytes (t ++ List.replicate m 61)) true alpha (.bytes g) k = .error (err msg) ↔
        padOutcome32 t.length m = some msg)) ∧
    (padOutcome32 t.length m = none ↔
      ∃ r, a2bB32 (.bytes (t ++ List.replicate m 61)) true alpha (.bytes g) false = .ok r)

theorem b32PadShape_proven : B32PadShape := by
  intro t m alpha g k hA ht hg
  have h61 := tbl32_61 alpha hA
  have hd : ∀ x ∈ t, tbl32 alpha x < 32 := fun x hx => (tbl32_lt alpha hA x).mpr (ht x hx)
  have hi : ign (if g.isEmpty then none else some g) 61 = false := ign_g g 61 hg
  have key : ∀ kk, (∀ msg, padOutcome32 t.length m = some msg →
        a2bB32 (.bytes (t ++ List.replicate m 61)) true alpha (.bytes g) kk = .error (err msg)) ∧
      (padOutcome32 t.length m = none → ∃ st : Dec32,
        a2bB32 (.bytes (t ++ List.replicate m 61)) true alpha (.bytes g) kk =
          if kk = true ∧ st.left ≠ 0 then .error (err "Non-zero padding bits") else .ok st.out) := by
    intro kk
    rw [a2bB32_eq alpha hA, core32_slow _ _ _ h61]
    obtain ⟨st, e, hq, hp, ho⟩ := slow32_dataRun (tbl32 alpha) true (if g.isEmpty then none else some g) h61 t {} hd
      rfl (by decide)
    rw [e]
    have hq' : st.octa = t.length % 8 := by simpa using hq
    have ho' : st.out.length = t.length * 5 / 8 := by simpa using ho
    have hnum : st.out.length / 5 * 8 + st.octa = t.length := by rw [ho', hq']; omega
    generalize hn : t.length = n at hq' ho' hnum
    have hst : ({ st with pads := 0 } : Dec32) = st := by cases st; simp_all
    by_cases h1 : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 6
    · have hpo : padOutcome32 n m = some (invMsg32 n) := by simp only [padOutcome32, if_pos h1]
      have hb : (st.octa == 1 || st.octa == 3 || st.octa == 6) = true := by
        rcases h1 with h | h | h <;> simp [hq', h]
      refine ⟨fun msg hm => ?_, fun hm => (by rw [hpo] at hm; cases hm)⟩
      rw [hpo] at hm
      cases hm
      cases m with
      | zero =>
        simp only [List.replicate_zero, slow32, Except.bind, fin32_eval, hb, if_true, hnum]
      | succ m' =>
        have hc : (st.octa == 2 || st.octa == 4 || st.octa == 5 || st.octa == 7) = false := by
          rcases h1 with h | h | h <;> simp [hq', h]
        rw [List.replicate_succ]
        simp only [slow32, beq_self_eq_true, Bool.and_self, if_true, Bool.true_and, hc, Bool.false_and,
          Bool.false_eq_true, if_false, hi, hb]
        simp only [Except.bind, fin32_eval, hb, if_true, hnum]
    · have hb : (st.octa == 1 || st.octa == 3 || st.octa == 6) = false := by
        simp only [hq']; simp only [not_or] at h1
        simp [h1.1, h1.2.1, h1.2.2]
      by_cases h0 : m = 0
      · subst h0
        simp only [List.replicate_zero, slow32, Except.bind, fin32_eval, hb, Bool.false_eq_true, if_false]
        by_cases hz : n % 8 = 0
        · have hpo : padOutcome32 n 0 = none := by unfold padOutcome32; rw [if_neg h1, if_pos rfl, if_pos hz]
          refine ⟨fun msg hm => (by rw [hpo] at hm; cases hm), fun _ => ⟨st, ?_⟩⟩
          rw [if_neg (by rintro ⟨-, h2, -⟩; omega)]
        · have hpo : padOutcome32 n 0 = some "Incorrect padding" := by
            unfold padOutcome32; rw [if_neg h1, if_pos rfl, if_neg hz]
          refine ⟨fun msg hm => ?_, fun hm => (by rw [hpo] at hm; cases hm)⟩
          rw [hpo] at hm; cases hm
          rw [if_pos ⟨by simp, by omega, by omega⟩]
      · obtain ⟨m', rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
        by_cases hz : n % 8 = 0
        · have hpo : padOutcome32 n (m' + 1) =
              some (if n = 0 then "Leading padding not allowed" else "Excess padding not allowed") := by
            simp only [padOutcome32, if_neg h1, if_neg (show ¬ (m' + 1 = 0) by omega), if_pos hz]
          refine ⟨fun msg hm => ?_, fun hm => (by rw [hpo] at hm; cases hm)⟩
          rw [hpo] at hm; cases hm
          have hc : (st.octa == 2 || st.octa == 4 || st.octa == 5 || st.octa == 7) = false := by simp [hq', hz]
          rw [List.replicate_succ]
          simp only [slow32, beq_self_eq_true, Bool.and_self, if_true, Bool.true_and, hc, Bool.false_and,
            Bool.false_eq_true, if_false, hi, hb]
          have he : st.out.isEmpty = true ↔ n = 0 := by
            rw [List.isEmpty_iff, ← List.length_eq_zero_iff, ho']; omega
          by_cases hn0 : n = 0
          · have : st.out.isEmpty = true := he.mpr hn0
            simp [this, hn0, hq', hz]; rfl
          · have : st.out.isEmpty = false := by
              cases h : st.out.isEmpty
              · rfl
              · exact absurd (he.mp h) hn0
            simp [this, hn0]; rfl
        · have hq2 : st.octa = 2 ∨ st.octa = 4 ∨ st.octa = 5 ∨ st.octa = 7 := by omega
          rw [← hst, slow32_pads (tbl32 alpha) _ hi st hq2 (m' + 1) 0 (by omega)]
          by_cases hover : st.octa + 0 + (m' + 1) ≤ 8
          · rw [if_pos hover]
            simp only [Except.bind, fin32_eval]
            have hb' : (({ st with pads := 0 + (m' + 1) } : Dec32).octa == 1 || ({ st with pads := 0 + (m' + 1) } : Dec32).octa == 3 ||
                ({ st with pads := 0 + (m' + 1) } : Dec32).octa == 6) = false := hb
            rw [if_neg (by rw [hb']; decide)]
            by_cases hlt : st.octa + (0 + (m' + 1)) < 8
            · have hpo : padOutcome32 n (m' + 1) = some "Incorrect padding" := by
                unfold padOutcome32
                rw [if_neg h1, if_neg (by omega), if_neg hz, if_neg (by omega), if_pos (by omega)]
              refine ⟨fun msg hm => ?_, fun hm => (by rw [hpo] at hm; cases hm)⟩
              rw [hpo] at hm; cases hm
              rw [if_pos ⟨by simp, by simp; omega, by simp; omega⟩]
            · have hpo : padOutcome32 n (m' + 1) = none := by
                unfold padOutcome32
                rw [if_neg h1, if_neg (by omega), if_neg hz, if_neg (by omega), if_neg (by omega)]
              refine ⟨fun msg hm => (by rw [hpo] at hm; cases hm), fun _ => ⟨st, ?_⟩⟩
              rw [if_neg (by rintro ⟨-, -, h3⟩; simp at h3; omega)]
          · rw [if_neg hover]
            have hpo : padOutcome32 n (m' + 1) = some "Excess padding not allowed" := by
              unfold padOutcome32
              rw [if_neg h1, if_neg (by omega), if_neg hz, if_pos (by omega)]
            refine ⟨fun msg hm => ?_, fun hm => (by rw [hpo] at hm; cases hm)⟩
            rw [hpo] at hm; cases hm
            rfl
  refine ⟨fun msg hmsg => ⟨fun h => ?_, fun h => (key k).1 msg h⟩, ⟨fun h => ?_, fun ⟨r, hr⟩ => ?_⟩⟩
  · cases hpo : padOutcome32 t.length m with
    | some msg0 =>
      rw [(key k).1 msg0 hpo] at h
      rw [err_inj _ _ h]
    | none =>
      obtain ⟨st, hst⟩ := (key k).2 hpo
      rw [hst] at h
      split at h
      · exact absurd (err_inj _ _ h).symm hmsg
      · cases h
  · obtain ⟨st, hst⟩ := (key false).2 h
    exact ⟨st.out, by rw [hst]; simp⟩
  · cases hpo : padOutcome32 t.length m with
    | none => rfl
    | some msg0 => rw [(key false).1 msg0 hpo] at hr; cases hr

end PyLean.TextLibs.Binascii
