import PyLean.TextLibs.BinasciiB85f

/-!
The end-of-input refusals of `binascii.a2b_base64`, exactly: "Invalid base64-encoded string: number of
data characters (n) cannot be 1 more than a multiple of 4", "Incorrect padding", and the strict
"Excess padding not allowed" and "Leading padding not allowed".
-/

namespace PyLean.TextLibs.Binascii

open PyLean

set_option linter.unusedSimpArgs false

/-- The bytes written after `m` data characters from the start: three per group and one per character
after the first of a group. -/
def bytes64 (m : Nat) : Nat := m / 4 * 3 + (m % 4 - 1)

def invMsg64 (n : Nat) : String :=
  s!"Invalid base64-encoded string: number of data characters ({n}) cannot be 1 more than a multiple of 4"

/-- The number of `'='` since the last data character, when `padded`. -/
def tpads64 (p : Bool) (isData : Nat → Bool) (acc : Nat) (s : List Nat) : Nat :=
  s.foldl (fun a x => if isData x then 0 else if p && x == 61 then a + 1 else a) acc

theorem decStep_quad (st : Dec) (v : Nat) (h : st.quad < 4) :
    (decStep { st with pads := 0 } v).quad = (st.quad + 1) % 4 ∧ (decStep { st with pads := 0 } v).pads = 0 ∧
      (decStep { st with pads := 0 } v).out.length + bytes64 st.quad = st.out.length + bytes64 (st.quad + 1) := by
  obtain ⟨q, p, l, o⟩ := st
  simp only at h
  rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3) with rfl | rfl | rfl | rfl <;>
    simp [decStep, bytes64]

/-- The non-strict loop never fails, and ends with the count of data characters, the pads since the last
one, and three bytes per group. -/
theorem slow64_lenient (p : Bool) (t : Nat → Nat) (ig : Option (List Nat)) (h61 : 64 ≤ t 61) :
    ∀ (s : List Nat) (st : Dec), st.quad < 4 → ∃ st', slow64 ⟨false, p, t, ig⟩ s st = .ok st' ∧
      st'.quad = (st.quad + (s.filter (fun x => decide (t x < 64))).length) % 4 ∧
      st'.pads = tpads64 p (fun x => decide (t x < 64)) st.pads s ∧
      st'.out.length + bytes64 st.quad = st.out.length + bytes64 (st.quad + (s.filter (fun x => decide (t x < 64))).length) := by
  intro s
  induction s with
  | nil => intro st hq; exact ⟨st, rfl, by simp; omega, rfl, rfl⟩
  | cons x xs ih =>
    intro st hq
    by_cases hd : t x < 64
    · have hx : (x == 61) = false := by apply beq_false_of_ne; intro e; subst e; omega
      obtain ⟨h1, h2, h3⟩ := decStep_quad st (t x) hq
      obtain ⟨st', e, q', p', o'⟩ := ih (decStep { st with pads := 0 } (t x)) (by rw [h1]; omega)
      refine ⟨st', ?_, ?_, ?_, ?_⟩
      · simp only [slow64, hx, Bool.and_false, Bool.false_eq_true, if_false, if_neg (Nat.not_le.mpr hd)]
        simpa using e
      · rw [q', h1, List.filter_cons_of_pos (by simpa using hd)]; simp; omega
      · rw [p', h2]; simp [tpads64, hd]
      · rw [List.filter_cons_of_pos (by simpa using hd), List.length_cons]
        have : bytes64 ((st.quad + 1) % 4 + (xs.filter (fun x => decide (t x < 64))).length) + bytes64 (st.quad + 1) =
            bytes64 (st.quad + ((xs.filter (fun x => decide (t x < 64))).length + 1)) + bytes64 ((st.quad + 1) % 4) := by
          simp only [bytes64]; omega
        rw [h1] at o'
        simp only [bytes64] at o' h3 this ⊢
        omega
    · rw [List.filter_cons_of_neg (by simpa using hd)]
      by_cases hp : (p && x == 61) = true
      · have hx : x = 61 := by simp at hp; exact hp.2
        obtain ⟨st', e, q', p', o'⟩ := ih { st with pads := st.pads + 1 } hq
        refine ⟨st', ?_, q', ?_, o'⟩
        · simp only [slow64, hp, if_true]
          split
          · exact e
          · simp only [Bool.not_false, Bool.true_or, if_true]; exact e
        · rw [p']; simp only [tpads64, List.foldl_cons]; congr 1; simp [hd, hp]
      · have hp' : (p && x == 61) = false := by simpa using hp
        obtain ⟨st', e, q', p', o'⟩ := ih st hq
        refine ⟨st', ?_, q', ?_, o'⟩
        · simp only [slow64, hp', Bool.false_eq_true, if_false, if_pos (Nat.not_lt.mp hd), Bool.false_and]
          exact e
        · rw [p']; simp only [tpads64, List.foldl_cons]; congr 1; simp [hd, hp']

theorem a2bB64_eq' (alpha : AlphaArg) (hA : (alphaChars alpha).length = 64) :
    ∀ s strict p g k, a2bB64 (.bytes s) strict p alpha (Option.map Data.bytes g) k =
      a2b64Core ⟨strict.getD g.isSome, p, revT (alphaChars alpha) (some 61), igEff strict g⟩ k s := by
  rcases a2bB64_cases alpha with ⟨e, he⟩ | ⟨_, he⟩
  · cases alpha with
    | absent =>
      have := he [] none true none false
      simp [a2bB64, asciiBuffer, alphaDec, bufOpt, decTable, a2b64Core, fast64, a2b64Run, bind, Except.bind,
        pure, Except.pure] at this
    | bytes a =>
      simp only [alphaChars] at hA
      have := he [] none true none false
      simp [a2bB64, asciiBuffer, alphaDec, bufOpt, decTable, hA, a2b64Core, fast64, a2b64Run, bind, Except.bind,
        pure, Except.pure] at this
    | other t => simp [alphaChars] at hA
  · exact he

theorem err_inj (a b : String) {α : Type} (h : (Except.error (err a) : Py α) = .error (err b)) : a = b := by
  simp only [err, Except.error.injEq, PyExc.named.injEq, true_and] at h
  exact h

theorem invMsg64_ne (n : Nat) (m : String) (hm : m.length < 50) : invMsg64 n ≠ m := by
  intro h
  have := congrArg String.length h
  simp only [invMsg64, String.length_append] at this
  have : 50 ≤ (toString "Invalid base64-encoded string: number of data characters (").length := by decide
  omega

/-- The two end-of-input refusals of `a2b_base64` with `strict_mode=False`, exactly, for every input,
`padded`, 64-byte alphabet, `ignorechars` and `canonical`. With `n` data characters (alphabet bytes but
`'='`) and, when `padded`, `tp` pad characters after the last of them: the decoder raises "Invalid
base64-encoded string: number of data characters (n) cannot be 1 more than a multiple of 4" exactly when
`n % 4 = 1`, and "Incorrect padding" exactly when `padded` and `n % 4` is 2 or 3 and `n % 4 + tp < 4`. A
body without either check does not satisfy this. -/
def B64LenientRefusals : Prop :=
  ∀ (s : List Nat) (p : Bool) (alpha : AlphaArg) (g : Option (List Nat)) (k : Bool),
    (alphaChars alpha).length = 64 →
    (a2bB64 (.bytes s) (some false) p alpha (g.map .bytes) k =
        .error (err (invMsg64 (s.filter (fun x => decide (x ∈ alphaChars alpha) && x != 61)).length)) ↔
      (s.filter (fun x => decide (x ∈ alphaChars alpha) && x != 61)).length % 4 = 1) ∧
    (a2bB64 (.bytes s) (some false) p alpha (g.map .bytes) k = .error (err "Incorrect padding") ↔
      p = true ∧ (s.filter (fun x => decide (x ∈ alphaChars alpha) && x != 61)).length % 4 ≠ 1 ∧
        (s.filter (fun x => decide (x ∈ alphaChars alpha) && x != 61)).length % 4 ≠ 0 ∧
        (s.filter (fun x => decide (x ∈ alphaChars alpha) && x != 61)).length % 4 +
          tpads64 p (fun x => decide (x ∈ alphaChars alpha) && x != 61) 0 s < 4)

theorem isData_eq (alpha : AlphaArg) (hA : (alphaChars alpha).length = 64) :
    (fun x => decide (x ∈ alphaChars alpha) && x != 61) = (fun x => decide (revT (alphaChars alpha) (some 61) x < 64)) := by
  funext x
  have := tbl64_lt _ hA x
  by_cases h : revT (alphaChars alpha) (some 61) x < 64
  · obtain ⟨h1, h2⟩ := this.mp h
    simp [h, h1, h2]
  · have : ¬(x ∈ alphaChars alpha ∧ x ≠ 61) := fun h' => h (this.mpr h')
    by_cases h1 : x ∈ alphaChars alpha
    · have h2 : x = 61 := by
        by_cases h2 : x = 61
        · exact h2
        · exact absurd ⟨h1, h2⟩ this
      simp [h, h1, h2, tbl64_61 _ hA]
    · simp [h, h1]

theorem b64LenientRefusals_proven : B64LenientRefusals := by
  intro s p alpha g k hA
  rw [isData_eq alpha hA, a2bB64_eq' alpha hA, core_slow _ (tbl64_61 _ hA)]
  simp only [Option.getD_some]
  obtain ⟨st, hs, hq, hp, ho⟩ := slow64_lenient p (revT (alphaChars alpha) (some 61)) (igEff (some false) g)
    (tbl64_61 _ hA) s {} (by decide)
  rw [hs]
  simp only [Nat.zero_add, Nat.zero_mod] at hq
  have ho' : st.out.length = bytes64 (s.filter (fun x => decide (revT (alphaChars alpha) (some 61) x < 64))).length := by
    have : bytes64 ({} : Dec).quad = 0 := rfl
    simpa [this] using ho
  generalize (s.filter (fun x => decide (revT (alphaChars alpha) (some 61) x < 64))).length = n at hq ho'
  generalize hT : tpads64 p (fun x => decide (revT (alphaChars alpha) (some 61) x < 64)) 0 s = tp at hp
  have hp' : st.pads = tp := by rw [hp, ← hT]
  simp only [Except.bind, fin64, bind, Except.bind, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw, pure,
    Except.pure]
  have hnum : st.out.length / 3 * 4 + 1 = n ∨ n % 4 ≠ 1 := by
    by_cases h : n % 4 = 1
    · left; rw [ho']; simp only [bytes64]; omega
    · right; exact h
  by_cases h1 : n % 4 = 1
  · rw [if_pos (by omega)]
    have hn : st.out.length / 3 * 4 + 1 = n := by rcases hnum with h | h; exact h; exact absurd h1 h
    refine ⟨⟨fun _ => h1, fun _ => by simp only [invMsg64, hn]⟩, ⟨fun h => ?_, fun ⟨_, h, _⟩ => absurd h1 h⟩⟩
    exact absurd (err_inj _ _ h) (invMsg64_ne _ _ (by decide))
  · rw [if_neg (by omega)]
    by_cases h2 : p = true ∧ st.quad ≠ 0 ∧ st.quad + st.pads < 4
    · rw [if_pos h2]
      refine ⟨⟨fun h => absurd (err_inj _ _ h).symm (invMsg64_ne _ _ (by decide)), fun h => absurd h h1⟩,
        ⟨fun _ => ⟨h2.1, h1, by omega, by omega⟩, fun _ => rfl⟩⟩
    · rw [if_neg h2]
      have hc : ∀ m, (if (k = true ∧ st.left ≠ 0) then (Except.error (err "Non-zero padding bits") : Py (List Nat))
          else .ok st.out) ≠ .error (err m) ∨ m = "Non-zero padding bits" := by
        intro m
        split
        · by_cases hm : m = "Non-zero padding bits"
          · right; exact hm
          · left; intro h; exact hm (err_inj _ _ h).symm
        · left; intro h; cases h
      refine ⟨⟨fun h => ?_, fun h => absurd h h1⟩, ⟨fun h => ?_, fun ⟨a, _, b, c⟩ => absurd ⟨a, by omega, by omega⟩ h2⟩⟩
      · rcases hc (invMsg64 n) with hc | hc
        · exact absurd h hc
        · exact absurd hc (invMsg64_ne _ _ (by decide))
      · rcases hc "Incorrect padding" with hc | hc
        · exact absurd h hc
        · exact absurd hc (by decide)

end PyLean.TextLibs.Binascii
