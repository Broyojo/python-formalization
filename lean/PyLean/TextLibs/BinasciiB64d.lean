import PyLean.TextLibs.BinasciiB64c

/-!
The strict-mode padding refusals of `binascii.a2b_base64`, exactly, on inputs made of data characters
and then pad characters.
-/

namespace PyLean.TextLibs.Binascii

open PyLean

set_option linter.unusedSimpArgs false

theorem slow64_data (c : B64) (h61 : 64 ≤ c.tbl 61) : ∀ (t : List Nat) (st : Dec), (∀ x ∈ t, c.tbl x < 64) →
    st.pads = 0 → st.quad < 4 → ∃ st', (∀ rest, slow64 c (t ++ rest) st = slow64 c rest st') ∧
      st'.quad = (st.quad + t.length) % 4 ∧
      st'.pads = 0 ∧ st'.out.length + bytes64 st.quad = st.out.length + bytes64 (st.quad + t.length) := by
  intro t
  induction t with
  | nil => intro st _ hp hq; exact ⟨st, fun _ => rfl, by simp; omega, hp, rfl⟩
  | cons x xs ih =>
    intro st hd hp hq
    have hx := hd x (by simp)
    have hst : decStep st (c.tbl x) = decStep { st with pads := 0 } (c.tbl x) := by
      cases st; simp_all
    obtain ⟨h1, h2, h3⟩ := decStep_quad st (c.tbl x) hq
    obtain ⟨st', e, q', p', o'⟩ := ih (decStep { st with pads := 0 } (c.tbl x)) (fun y hy => hd y (by simp [hy])) h2
      (by rw [h1]; omega)
    refine ⟨st', fun rest => ?_, ?_, p', ?_⟩
    · rw [List.cons_append, slow_data c x _ st hx h61 hp, hst]; exact e rest
    · rw [q', h1]; simp; omega
    · rw [h1] at o'
      simp only [List.length_cons]
      simp only [bytes64] at o' h3 ⊢
      omega

theorem slow64_pads (c : B64) (hs : c.strict = true) (hp : c.padded = true) (hi : ign c.ig 61 = false)
    (st : Dec) (hq : 2 ≤ st.quad) (hq4 : st.quad < 4) :
    ∀ (m j : Nat), st.quad + j ≤ 4 →
      slow64 c (List.replicate m 61) { st with pads := j } =
        if st.quad + j + m ≤ 4 then .ok { st with pads := j + m } else .error (err "Excess padding not allowed") := by
  intro m
  induction m with
  | zero => intro j hj; rw [if_pos (by omega)]; rfl
  | succ m ih =>
    intro j hj
    rw [List.replicate_succ]
    simp only [slow64, hp, beq_self_eq_true, Bool.and_self, if_true]
    by_cases hv : st.quad ≥ 2 ∧ st.quad + (j + 1) ≤ 4
    · rw [if_pos hv]
      have h2 := ih (j + 1) hv.2
      have e : st.quad + (j + 1) + m = st.quad + j + (m + 1) := by omega
      rw [e, show j + 1 + m = j + (m + 1) by omega] at h2
      exact h2
    · rw [if_neg hv]
      simp only [hs, hi, Bool.not_true, Bool.or_false, Bool.false_eq_true, if_false]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- What `a2b_base64(t + b'=' * m, strict_mode=True)` does with `n` data characters in `t`. -/
def padOutcome64 (n m : Nat) : Option String :=
  if n % 4 = 1 then some (invMsg64 n)
  else if m = 0 then (if n % 4 = 0 then none else some "Incorrect padding")
  else if n % 4 = 0 then some (if n = 0 then "Leading padding not allowed" else "Excess padding not allowed")
  else if n % 4 + m > 4 then some "Excess padding not allowed"
  else if n % 4 + m < 4 then some "Incorrect padding" else none

/-- The strict padding refusals of `a2b_base64`, exactly, on data characters followed by `m` pad
characters, for every 64-byte alphabet, `ignorechars` without `'='`, and `canonical`. With `n` data
characters and `q = n % 4`: `q = 1` is "Invalid base64-encoded string: ... (n) ...", whatever follows;
no pads is "Incorrect padding" unless `q = 0`; pads after a whole group are "Leading padding not allowed"
(nothing before) or "Excess padding not allowed"; pads past `4 - q` are "Excess padding not allowed";
fewer than `4 - q` are "Incorrect padding". Every other message is `canonical`'s; and the input is
accepted (with `canonical=False`) exactly when none of these applies. `b'AAAA='` raises "Excess padding
not allowed". -/
def B64StrictPadShape : Prop :=
  ∀ (t : List Nat) (m : Nat) (alpha : AlphaArg) (g : Option (List Nat)) (k : Bool),
    (alphaChars alpha).length = 64 → (∀ x ∈ t, x ∈ alphaChars alpha ∧ x ≠ 61) → (∀ l, g = some l → 61 ∉ l) →
    (∀ msg, msg ≠ "Non-zero padding bits" →
      (a2bB64 (.bytes (t ++ List.replicate m 61)) (some true) true alpha (g.map .bytes) k = .error (err msg) ↔
        padOutcome64 t.length m = some msg)) ∧
    (padOutcome64 t.length m = none ↔
      ∃ r, a2bB64 (.bytes (t ++ List.replicate m 61)) (some true) true alpha (g.map .bytes) false = .ok r)

theorem fin64_eval (c : B64) (k : Bool) (st : Dec) :
    fin64 c k st =
      if st.quad = 1 then .error (err (invMsg64 (st.out.length / 3 * 4 + 1)))
      else if c.padded = true ∧ st.quad ≠ 0 ∧ st.quad + st.pads < 4 then .error (err "Incorrect padding")
      else if k = true ∧ st.left ≠ 0 then .error (err "Non-zero padding bits") else .ok st.out := by
  simp only [fin64, bind, Except.bind, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw, pure, Except.pure,
    invMsg64]
  repeat' split
  all_goals rfl

theorem b64StrictPadShape_proven : B64StrictPadShape := by
  intro t m alpha g k hA ht hg
  have h61 := tbl64_61 _ hA
  have hd : ∀ x ∈ t, revT (alphaChars alpha) (some 61) x < 64 := fun x hx => (tbl64_lt _ hA x).mpr (ht x hx)
  have hi : ign (igEff (some true) g) 61 = false := ign_eff _ g 61 hg
  have key : ∀ kk, (∀ msg, padOutcome64 t.length m = some msg →
        a2bB64 (.bytes (t ++ List.replicate m 61)) (some true) true alpha (g.map .bytes) kk = .error (err msg)) ∧
      (padOutcome64 t.length m = none → ∃ st : Dec,
        a2bB64 (.bytes (t ++ List.replicate m 61)) (some true) true alpha (g.map .bytes) kk =
          if kk = true ∧ st.left ≠ 0 then .error (err "Non-zero padding bits") else .ok st.out) := by
    intro kk
    rw [a2bB64_eq' alpha hA, core_slow _ h61]
    simp only [Option.getD_some]
    obtain ⟨st, e, hq, hp, ho⟩ := slow64_data ⟨true, true, revT (alphaChars alpha) (some 61), igEff (some true) g⟩
      h61 t {} hd rfl (by decide)
    rw [e]
    have hq' : st.quad = t.length % 4 := by simpa using hq
    have ho' : st.out.length = bytes64 t.length := by simpa [bytes64] using ho
    have hnum : t.length % 4 = 1 → st.out.length / 3 * 4 + 1 = t.length := by
      intro h; rw [ho']; simp only [bytes64]; omega
    generalize hn : t.length = n at hq' ho' hnum
    have hst : ({ st with pads := 0 } : Dec) = st := by cases st; simp_all
    have he : (st.out.isEmpty = true) ↔ n = 0 ∨ n % 4 ≠ 0 ∧ False ∨ (st.out.length = 0) ∧ n % 4 ≠ 0 := by
      rw [List.isEmpty_iff, ← List.length_eq_zero_iff]; constructor
      · intro h; by_cases hz : n % 4 = 0
        · left; rw [ho'] at h; simp only [bytes64] at h; omega
        · right; right; exact ⟨h, hz⟩
      · intro h; rcases h with h | ⟨_, h⟩ | ⟨h, _⟩
        · rw [ho', h]; rfl
        · exact absurd h id
        · exact h
    by_cases h1 : n % 4 = 1
    · have hpo : padOutcome64 n m = some (invMsg64 n) := by simp [padOutcome64, h1]
      refine ⟨fun msg hm => ?_, fun hm => (by rw [hpo] at hm; cases hm)⟩
      rw [hpo] at hm
      cases hm
      cases m with
      | zero =>
        simp only [List.replicate_zero, slow64, Except.bind, fin64_eval, hq', h1, if_true, hnum h1]
      | succ m' =>
        rw [List.replicate_succ]
        simp only [slow64, beq_self_eq_true, Bool.and_self, if_true, Bool.true_and, hq', h1,
          show ¬ (1 ≥ 2 ∧ 1 + (st.pads + 1) ≤ 4) by omega, if_false, hi, Bool.not_true, Bool.or_false,
          Bool.false_eq_true]
        simp only [Except.bind, fin64_eval, h1, if_true, hnum h1]
    · by_cases h0 : m = 0
      · subst h0
        simp only [List.replicate_zero, slow64, Except.bind, fin64_eval]
        rw [if_neg (by omega)]
        by_cases hz : n % 4 = 0
        · have hpo : padOutcome64 n 0 = none := by simp [padOutcome64, h1, hz]
          refine ⟨fun msg hm => (by rw [hpo] at hm; cases hm), fun _ => ⟨st, ?_⟩⟩
          rw [if_neg (by rintro ⟨-, h2, -⟩; omega)]
        · have hpo : padOutcome64 n 0 = some "Incorrect padding" := by simp [padOutcome64, h1, hz]
          refine ⟨fun msg hm => ?_, fun hm => (by rw [hpo] at hm; cases hm)⟩
          rw [hpo] at hm; cases hm
          rw [if_pos ⟨by simp, by omega, by omega⟩]
      · obtain ⟨m', rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
        by_cases hz : n % 4 = 0
        · have hpo : padOutcome64 n (m' + 1) =
              some (if n = 0 then "Leading padding not allowed" else "Excess padding not allowed") := by
            simp [padOutcome64, h1, hz]
          refine ⟨fun msg hm => ?_, fun hm => (by rw [hpo] at hm; cases hm)⟩
          rw [hpo] at hm; cases hm
          rw [List.replicate_succ]
          simp only [slow64, beq_self_eq_true, Bool.and_self, if_true, Bool.true_and, hq', hz,
            show ¬ (0 ≥ 2 ∧ 0 + (st.pads + 1) ≤ 4) by omega, if_false, hi, Bool.not_true, Bool.or_false,
            Bool.false_eq_true, show ¬ (0 : Nat) = 1 by decide]
          by_cases hn0 : n = 0
          · have : st.out.isEmpty = true := he.mpr (.inl hn0)
            simp [this, hn0]; rfl
          · have : st.out.isEmpty = false := by
              cases h : st.out.isEmpty
              · rfl
              · rcases he.mp h with h' | ⟨_, h'⟩ | ⟨_, h'⟩
                · exact absurd h' hn0
                · exact absurd h' id
                · exact absurd hz h'
            simp [this, hn0]; rfl
        · have hq2 : 2 ≤ st.quad := by omega
          rw [← hst, slow64_pads ⟨true, true, revT (alphaChars alpha) (some 61), igEff (some true) g⟩ rfl rfl hi st hq2
            (by omega) (m' + 1) 0 (by omega)]
          by_cases hover : st.quad + 0 + (m' + 1) ≤ 4
          · rw [if_pos hover]
            simp only [Except.bind, fin64_eval]
            rw [if_neg (by first | omega | (simp; omega))]
            by_cases hlt : st.quad + (0 + (m' + 1)) < 4
            · have hpo : padOutcome64 n (m' + 1) = some "Incorrect padding" := by
                unfold padOutcome64
                rw [if_neg h1, if_neg (by omega), if_neg hz, if_neg (by omega), if_pos (by omega)]
              refine ⟨fun msg hm => ?_, fun hm => (by rw [hpo] at hm; cases hm)⟩
              rw [hpo] at hm; cases hm
              rw [if_pos ⟨by simp, by simp; omega, by simp; omega⟩]
            · have hpo : padOutcome64 n (m' + 1) = none := by
                unfold padOutcome64
                rw [if_neg h1, if_neg (by omega), if_neg hz, if_neg (by omega), if_neg (by omega)]
              refine ⟨fun msg hm => (by rw [hpo] at hm; cases hm), fun _ => ⟨st, ?_⟩⟩
              rw [if_neg (by rintro ⟨-, -, h3⟩; simp at h3; omega)]
          · rw [if_neg hover]
            have hpo : padOutcome64 n (m' + 1) = some "Excess padding not allowed" := by
              unfold padOutcome64
              rw [if_neg h1, if_neg (by omega), if_neg hz, if_pos (by omega)]
            refine ⟨fun msg hm => ?_, fun hm => (by rw [hpo] at hm; cases hm)⟩
            rw [hpo] at hm; cases hm
            rfl
  refine ⟨fun msg hmsg => ⟨fun h => ?_, fun h => (key k).1 msg h⟩, ⟨fun h => ?_, fun ⟨r, hr⟩ => ?_⟩⟩
  · cases hpo : padOutcome64 t.length m with
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
  · cases hpo : padOutcome64 t.length m with
    | none => rfl
    | some msg0 => rw [(key false).1 msg0 hpo] at hr; cases hr

end PyLean.TextLibs.Binascii
