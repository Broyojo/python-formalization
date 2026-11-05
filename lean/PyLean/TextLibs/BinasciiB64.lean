import PyLean.TextLibs.BinasciiEq3

/-!
`binascii.a2b_base64` and `binascii.b2a_base64` of 3.15.2 over every option: `strict_mode` (and its
default from `ignorechars`), `padded`, `alphabet`, `ignorechars`, `canonical`, `wrapcol` and `newline`.

The proofs first take the fast path out of the decoder, for any table that does not read `'='` as
data (every table `get_reverse_table` builds puts the pad on top): the slow loop alone, `slow64`, gives
the same result. The statements are about `a2bB64` and `b2aB64`, the C functions with their clinic
wrappers.
-/

namespace PyLean.TextLibs.Binascii

open PyLean

set_option linter.unusedSimpArgs false

/-- The slow loop of `binascii_a2b_base64_impl`, `Modules/binascii.c:811-898`, run to the end of the
input: the `goto fastpath` after a fourth character is replaced by going on with the loop, which
`slow64_run` shows changes nothing. -/
def slow64 (c : B64) : List Nat → Dec → Py Dec
  | [], st => .ok st
  | x :: xs, st =>
    if c.padded && x == 61 then
      let pads := st.pads + 1
      let st' := { st with pads }
      if st.quad ≥ 2 ∧ st.quad + pads ≤ 4 then slow64 c xs st'
      else if !c.strict || ign c.ig 61 then slow64 c xs st'
      else if st.quad = 1 then .ok st'
      else .error (err (if st.quad = 0 ∧ st.out.isEmpty then "Leading padding not allowed"
                        else "Excess padding not allowed"))
    else
      let v := c.tbl x
      if v ≥ 64 then
        if c.strict && !ign c.ig x then
          .error (err (if x = 61 then "Padding not allowed" else "Only base64 data is allowed"))
        else slow64 c xs st
      else if st.pads ≠ 0 ∧ c.strict ∧ !ign c.ig 61 then
        .error (err (if st.quad + st.pads = 4 then "Excess data after padding"
                     else "Discontinuous padding not allowed"))
      else slow64 c xs (decStep { st with pads := 0 } v)

/-- The checks after the loop, `Modules/binascii.c:900-933`. -/
def fin64 (c : B64) (canonical : Bool) (st : Dec) : Py (List Nat) := do
  if st.quad = 1 then
    throw (err s!"Invalid base64-encoded string: number of data characters \
      ({st.out.length / 3 * 4 + 1}) cannot be 1 more than a multiple of 4")
  if c.padded ∧ st.quad ≠ 0 ∧ st.quad + st.pads < 4 then throw (err "Incorrect padding")
  if canonical ∧ st.left ≠ 0 then throw (err "Non-zero padding bits")
  return st.out

theorem slow_data (c : B64) (x : Nat) (xs : List Nat) (st : Dec) (hx : c.tbl x < 64) (h61 : 64 ≤ c.tbl 61)
    (hp : st.pads = 0) : slow64 c (x :: xs) st = slow64 c xs (decStep st (c.tbl x)) := by
  have hne : (x == 61) = false := by
    apply beq_false_of_ne
    intro e
    subst e
    omega
  have hst : { st with pads := 0 } = st := by cases st; simp_all
  simp only [slow64, hne, Bool.and_false, Bool.false_eq_true, if_false, if_neg (by omega : ¬ c.tbl x ≥ 64), hp,
    ne_eq, not_true_eq_false, false_and, hst]

/-- `base64_decode_quad` does what four turns of the slow loop do, for any table. -/
theorem slow_quad (c : B64) (h61 : 64 ≤ c.tbl 61) (a b cc d : Nat) (o r out : List Nat)
    (hq : quad64 c.tbl a b cc d = some o) :
    slow64 c (a :: b :: cc :: d :: r) ⟨0, 0, 0, out⟩ = slow64 c r ⟨0, 0, 0, out ++ o⟩ := by
  simp only [quad64] at hq
  by_cases hn : c.tbl a ≥ 64 ∨ c.tbl b ≥ 64 ∨ c.tbl cc ≥ 64 ∨ c.tbl d ≥ 64
  · rw [if_pos hn] at hq
    cases hq
  · rw [if_neg hn] at hq
    simp only [not_or, Nat.not_le] at hn
    obtain ⟨n1, n2, n3, n4⟩ := hn
    rw [slow_data c a _ _ n1 h61 rfl, slow_data c b _ _ n2 h61 rfl, slow_data c cc _ _ n3 h61 rfl,
      slow_data c d _ _ n4 h61 rfl, decStep_group]
    simp only [Option.some.injEq] at hq
    subst hq
    have e2 : (c.tbl b % 16 * 16 + c.tbl cc / 4) % 256 = (c.tbl b * 16 + c.tbl cc / 4) % 256 := by omega
    have e3 : (c.tbl cc % 4 * 64 + c.tbl d) % 256 = (c.tbl cc * 64 + c.tbl d) % 256 := by omega
    rw [e2, e3]

/-- `base64_decode_fast` can be taken out from a clean position. -/
theorem slow_fast (c : B64) (h61 : 64 ≤ c.tbl 61) : ∀ (n : Nat) (s out : List Nat), s.length ≤ n →
    slow64 c s ⟨0, 0, 0, out⟩ = slow64 c (fast64 c.tbl s out).1 ⟨0, 0, 0, (fast64 c.tbl s out).2⟩ := by
  intro n
  induction n with
  | zero =>
    intro s out h
    have : s = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp [fast64]
  | succ n ih =>
    intro s out h
    match s, h with
    | a :: b :: cc :: d :: r, h =>
      rw [fast64]
      cases hq : quad64 c.tbl a b cc d with
      | none => rfl
      | some o =>
        simp only
        rw [slow_quad c h61 a b cc d o r out hq]
        exact ih r (out ++ o) (by simp at h; omega)
    | [], _ => simp [fast64]
    | [_], _ => simp [fast64]
    | [_, _], _ => simp [fast64]
    | [_, _, _], _ => simp [fast64]

/-- The loop with its `goto fastpath` is the slow loop alone. -/
theorem slow64_run (c : B64) (h61 : 64 ≤ c.tbl 61) : ∀ (f : Nat) (s : List Nat) (st : Dec), s.length < f →
    a2b64Run c f s st = slow64 c s st := by
  intro f
  induction f with
  | zero => intro _ _ h; omega
  | succ f ih =>
    intro s st h
    cases s with
    | nil => rfl
    | cons x xs =>
      have hl : xs.length < f := by simpa using h
      simp only [a2b64Run, slow64]
      split
      · split
        · exact ih _ _ hl
        · split
          · exact ih _ _ hl
          · rfl
      · split
        · split
          · rfl
          · exact ih _ _ hl
        · split
          · rfl
          · split
            · rename_i hq
              obtain ⟨q, p, l, o⟩ := st
              simp only at hq
              subst hq
              simp only [decStep]
              have hf := fast_len c.tbl xs.length xs (o ++ [(l * 64 + c.tbl x) % 256]) (Nat.le_refl _)
              rw [ih _ _ (by omega)]
              exact (slow_fast c h61 xs.length xs _ (Nat.le_refl _)).symm
            · exact ih _ _ hl

/-- `binascii_a2b_base64_impl` from the fast path on is the slow loop and the final checks. -/
theorem core_slow (c : B64) (h61 : 64 ≤ c.tbl 61) (k : Bool) (s : List Nat) :
    a2b64Core c k s = (slow64 c s {}).bind (fin64 c k) := by
  have hf := fast_len c.tbl s.length s [] (Nat.le_refl _)
  have h1 : a2b64Run c (s.length + 1) (fast64 c.tbl s []).1 { out := (fast64 c.tbl s []).2 } = slow64 c s {} := by
    rw [slow64_run c h61 _ _ _ (by omega)]
    exact (slow_fast c h61 s.length s [] (Nat.le_refl _)).symm
  simp only [a2b64Core]
  rw [h1]
  cases slow64 c s {} with
  | error e => rfl
  | ok st => rfl

/-! ### Characters the loop skips -/

/-- The characters the loop passes over without a change of state: not in the alphabet, not the pad
character of a padded decode, and either the mode is not strict or `ignorechars` names them. -/
def skip64 (c : B64) (x : Nat) : Bool :=
  decide (c.tbl x ≥ 64) && !(c.padded && x == 61) && (!c.strict || ign c.ig x)

theorem slow_filter (c : B64) : ∀ (s : List Nat) (st : Dec),
    slow64 c s st = slow64 c (s.filter (fun x => !skip64 c x)) st := by
  intro s
  induction s with
  | nil => intro st; rfl
  | cons x xs ih =>
    intro st
    by_cases hs : skip64 c x = true
    · rw [List.filter_cons_of_neg (by simp [hs])]
      simp only [skip64, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hs
      obtain ⟨⟨h1, h2⟩, h3⟩ := hs
      have h4 : (c.strict && !ign c.ig x) = false := by
        cases hc : c.strict <;> simp_all
      simp only [slow64, h2, Bool.false_eq_true, if_false, if_pos h1, h4]
      exact ih st
    · rw [List.filter_cons_of_pos (by simpa using hs)]
      simp only [slow64]
      split
      · split
        · exact ih _
        · split
          · exact ih _
          · rfl
      · split
        · split
          · rfl
          · exact ih _
        · split
          · rfl
          · exact ih _

/-! ### Decoding what the encoder writes, with any alphabet -/

/-- An alphabet `get_reverse_table` can invert: 64 distinct bytes, none of them `'='`. -/
def GoodAlpha64 (a : List Nat) : Prop := a.length = 64 ∧ a.Nodup ∧ 61 ∉ a

theorem good_b64 : GoodAlpha64 b64Alpha := ⟨by decide, by decide +kernel, by decide +kernel⟩

theorem getD_mem (a : List Nat) (v : Nat) (h : v < a.length) : a.getD v 0 ∈ a := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_mem _

theorem tblA (a : List Nat) (ha : GoodAlpha64 a) (v : Nat) (hv : v < 64) :
    revT a (some 61) (a.getD v 0) = v := by
  obtain ⟨hl, hn, h61⟩ := ha
  apply revT_index a (some 61) v hn (by omega)
  intro e
  have e' : a.getD v 0 = 61 := (Option.some.inj e).symm
  apply h61
  rw [← e']
  exact getD_mem a v (by omega)

theorem tblA_mem (a : List Nat) (ha : GoodAlpha64 a) (v : Nat) (hv : v < 64) : a.getD v 0 ∈ a :=
  getD_mem a v (by rw [ha.1]; omega)

/-- What the encoder writes before wrapping and the newline. -/
def unwrapped64 (a d : List Nat) (padded : Bool) : List Nat :=
  (fastEnc64 a d).1 ++ tail64 a (fastEnc64 a d).2 ++ List.replicate (if padded then pads64 d.length else 0) 61

theorem fastEnc64_three (a : List Nat) (x y z : Nat) (r : List Nat) :
    fastEnc64 a (x :: y :: z :: r) =
      ([a.getD ((x * 65536 + y * 256 + z) / 2 ^ 18 % 64) 0, a.getD ((x * 65536 + y * 256 + z) / 2 ^ 12 % 64) 0,
        a.getD ((x * 65536 + y * 256 + z) / 2 ^ 6 % 64) 0, a.getD ((x * 65536 + y * 256 + z) % 64) 0] ++
        (fastEnc64 a r).1, (fastEnc64 a r).2) := rfl

theorem dec_enc (c : B64) (a : List Nat) (ha : GoodAlpha64 a) (ht : c.tbl = revT a (some 61)) (k : Bool) :
    ∀ (n : Nat) (d out : List Nat), d.length ≤ n → (∀ x ∈ d, x < 256) →
      ∃ st, slow64 c (unwrapped64 a d c.padded) ⟨0, 0, 0, out⟩ = .ok st ∧ fin64 c k st = .ok (out ++ d) := by
  have h61 : 64 ≤ c.tbl 61 := by rw [ht, revT_pad, ha.1]; exact Nat.le_refl 64
  have hv : ∀ v, v < 64 → c.tbl (a.getD v 0) = v := fun v h => by rw [ht]; exact tblA a ha v h
  have hpad : ∀ (st : Dec) (r : List Nat), c.padded = true → 2 ≤ st.quad → st.quad + st.pads + 1 ≤ 4 →
      slow64 c (61 :: r) st = slow64 c r { st with pads := st.pads + 1 } := by
    intro st r hp h1 h2
    simp only [slow64, hp, beq_self_eq_true, Bool.and_self, if_true]
    rw [if_pos ⟨h1, by omega⟩]
  intro n
  induction n with
  | zero =>
    intro d out h _
    have : d = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    refine ⟨⟨0, 0, 0, out⟩, ?_, ?_⟩
    · simp [unwrapped64, fastEnc64, tail64, pads64, slow64]
    · simp [fin64, bind, Except.bind, pure, Except.pure]
  | succ n ih =>
    intro d out h hb
    match d, h, hb with
    | [], _, _ =>
      refine ⟨⟨0, 0, 0, out⟩, ?_, ?_⟩
      · simp [unwrapped64, fastEnc64, tail64, pads64, slow64]
      · simp [fin64, bind, Except.bind, pure, Except.pure]
    | [x], _, hb =>
      have hx : x < 256 := hb x (by simp)
      have e : unwrapped64 a [x] c.padded =
          [a.getD (x / 4 % 64) 0, a.getD (x * 16 % 64) 0] ++ List.replicate (if c.padded then 2 else 0) 61 := by
        simp [unwrapped64, fastEnc64, tail64, pads64]
      rw [e]
      simp only [List.cons_append, List.nil_append]
      rw [slow_data c _ _ _ (by rw [hv _ (by omega)]; omega) h61 rfl, hv _ (by omega),
        slow_data c _ _ _ (by rw [hv _ (by omega)]; omega) h61 (by simp [decStep]), hv _ (by omega)]
      have e1 : ((x / 4 % 64) * 4 + (x * 16 % 64) / 16) % 256 = x := by omega
      have e2 : (x * 16 % 64) % 16 = 0 := by omega
      simp only [decStep, e1, e2]
      cases hp : c.padded with
      | true =>
        simp only [if_true, List.replicate_succ, List.replicate_zero]
        rw [hpad _ _ hp (by simp) (by simp), hpad _ _ hp (by simp) (by simp)]
        refine ⟨_, rfl, ?_⟩
        simp [fin64, hp, bind, Except.bind, pure, Except.pure]
      | false =>
        simp only [Bool.false_eq_true, if_false, List.replicate_zero]
        refine ⟨_, rfl, ?_⟩
        simp [fin64, hp, bind, Except.bind, pure, Except.pure]
    | [x, y], _, hb =>
      have hx : x < 256 := hb x (by simp)
      have hy : y < 256 := hb y (by simp)
      have e : unwrapped64 a [x, y] c.padded =
          [a.getD ((x * 256 + y) / 2 ^ 10 % 64) 0, a.getD ((x * 256 + y) / 2 ^ 4 % 64) 0,
            a.getD ((x * 256 + y) * 4 % 64) 0] ++ List.replicate (if c.padded then 1 else 0) 61 := by
        simp [unwrapped64, fastEnc64, tail64, pads64]
      rw [e]
      simp only [List.cons_append, List.nil_append]
      rw [slow_data c _ _ _ (by rw [hv _ (by omega)]; omega) h61 rfl, hv _ (by omega),
        slow_data c _ _ _ (by rw [hv _ (by omega)]; omega) h61 (by simp [decStep]), hv _ (by omega),
        slow_data c _ _ _ (by rw [hv _ (by omega)]; omega) h61 (by simp [decStep]), hv _ (by omega)]
      have e1 : (((x * 256 + y) / 2 ^ 10 % 64) * 4 + ((x * 256 + y) / 2 ^ 4 % 64) / 16) % 256 = x := by omega
      have e2 : (((x * 256 + y) / 2 ^ 4 % 64) % 16 * 16 + ((x * 256 + y) * 4 % 64) / 4) % 256 = y := by omega
      have e3 : ((x * 256 + y) * 4 % 64) % 4 = 0 := by omega
      simp only [decStep, e1, e2, e3, List.append_assoc, List.cons_append, List.nil_append]
      cases hp : c.padded with
      | true =>
        simp only [if_true, List.replicate_succ, List.replicate_zero]
        rw [hpad _ _ hp (by simp) (by simp)]
        refine ⟨_, rfl, ?_⟩
        simp [fin64, hp, bind, Except.bind, pure, Except.pure]
      | false =>
        simp only [Bool.false_eq_true, if_false, List.replicate_zero]
        refine ⟨_, rfl, ?_⟩
        simp [fin64, hp, bind, Except.bind, pure, Except.pure]
    | x :: y :: z :: r, h, hb =>
      have hx : x < 256 := hb x (by simp)
      have hy : y < 256 := hb y (by simp)
      have hz : z < 256 := hb z (by simp)
      have e : unwrapped64 a (x :: y :: z :: r) c.padded =
          [a.getD ((x * 65536 + y * 256 + z) / 2 ^ 18 % 64) 0, a.getD ((x * 65536 + y * 256 + z) / 2 ^ 12 % 64) 0,
            a.getD ((x * 65536 + y * 256 + z) / 2 ^ 6 % 64) 0, a.getD ((x * 65536 + y * 256 + z) % 64) 0] ++
            unwrapped64 a r c.padded := by
        have hl : (x :: y :: z :: r).length = r.length + 3 := by simp
        simp only [unwrapped64, fastEnc64_three, hl, pads64_step, List.append_assoc]
      rw [e]
      generalize hw : x * 65536 + y * 256 + z = w
      have q1 : w / 2 ^ 18 % 64 < 64 := Nat.mod_lt _ (by decide)
      have q2 : w / 2 ^ 12 % 64 < 64 := Nat.mod_lt _ (by decide)
      have q3 : w / 2 ^ 6 % 64 < 64 := Nat.mod_lt _ (by decide)
      have q4 : w % 64 < 64 := Nat.mod_lt _ (by decide)
      simp only [List.cons_append, List.nil_append]
      rw [slow_data c _ _ _ (by rw [hv _ q1]; exact q1) h61 rfl, hv _ q1,
        slow_data c _ _ _ (by rw [hv _ q2]; exact q2) h61 (by simp [decStep]), hv _ q2,
        slow_data c _ _ _ (by rw [hv _ q3]; exact q3) h61 (by simp [decStep]), hv _ q3,
        slow_data c _ _ _ (by rw [hv _ q4]; exact q4) h61 (by simp [decStep]), hv _ q4]
      rw [decStep_group]
      have e1 : (w / 2 ^ 18 % 64 * 4 + w / 2 ^ 12 % 64 / 16) % 256 = x := by omega
      have e2 : (w / 2 ^ 12 % 64 % 16 * 16 + w / 2 ^ 6 % 64 / 4) % 256 = y := by omega
      have e3 : (w / 2 ^ 6 % 64 % 4 * 64 + w % 64) % 256 = z := by omega
      rw [e1, e2, e3]
      obtain ⟨st, h1, h2⟩ := ih r (out ++ [x, y, z]) (by simp at h; omega) (fun q hq => hb q (by simp [hq]))
      refine ⟨st, h1, ?_⟩
      rw [h2]
      simp

theorem fastEnc64_mem (a : List Nat) (ha : a.length = 64) : ∀ (n : Nat) (d : List Nat), d.length ≤ n →
    ∀ x ∈ (fastEnc64 a d).1, x ∈ a := by
  intro n
  induction n with
  | zero =>
    intro d h x hx
    have : d = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp [fastEnc64] at hx
  | succ n ih =>
    intro d h x hx
    match d, h with
    | [], _ => simp [fastEnc64] at hx
    | [_], _ => simp [fastEnc64] at hx
    | [_, _], _ => simp [fastEnc64] at hx
    | p :: q :: r :: t, h =>
      rw [fastEnc64_three] at hx
      simp only [List.cons_append, List.nil_append, List.mem_cons] at hx
      rcases hx with hx | hx | hx | hx | hx
      all_goals first
        | (subst hx; exact getD_mem a _ (by rw [ha]; exact Nat.mod_lt _ (by decide)))
        | exact ih t (by simp at h; omega) x hx

theorem unwrapped64_mem (a : List Nat) (ha : a.length = 64) (d : List Nat) (p : Bool) :
    ∀ x ∈ unwrapped64 a d p, x ∈ a ∨ (x = 61 ∧ p = true) := by
  intro x hx
  simp only [unwrapped64, List.mem_append] at hx
  rcases hx with (hx | hx) | hx
  · exact .inl (fastEnc64_mem a ha d.length d (Nat.le_refl _) x hx)
  · left
    generalize (fastEnc64 a d).2 = r at hx
    match r with
    | [] => simp [tail64] at hx
    | [_] =>
      simp only [tail64, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with hx | hx <;> (subst hx; exact getD_mem a _ (by rw [ha]; exact Nat.mod_lt _ (by decide)))
    | [_, _] =>
      simp only [tail64, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with hx | hx | hx <;> (subst hx; exact getD_mem a _ (by rw [ha]; exact Nat.mod_lt _ (by decide)))
    | _ :: _ :: _ :: _ => simp [tail64] at hx
  · right
    cases p
    · simp at hx
    · exact ⟨List.eq_of_mem_replicate hx, rfl⟩

/-- The table of a member of an alphabet of distinct bytes is below its length. -/
theorem revT_mem_lt (a : List Nat) (ha : GoodAlpha64 a) (x : Nat) (hx : x ∈ a) : revT a (some 61) x < 64 := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have e : a[i] = a.getD i 0 := by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
  rw [e, tblA a ha i (by rw [ha.1] at hi; exact hi)]
  rw [ha.1] at hi
  exact hi

theorem sizeT_ok (w : Int) (n : Nat) (h : sizeT w = .ok n) : w = (n : Int) := by
  unfold sizeT at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h
      omega

/-- The decoder's alphabet argument for an encoder's `Option` alphabet. -/
def decAlphaOf : Option (List Nat) → AlphaArg
  | none => .absent
  | some a => .bytes a

/-- `a2b_base64(b2a_base64(d, padded=p, wrapcol=w, newline=n, alphabet=a), padded=p, alphabet=a,
strict_mode=s, ignorechars=g, canonical=k) == d`, for every `bytes` value `d` and every value of every
option, as long as the decoder can see past the newlines: the alphabet is 64 distinct bytes without
`'='` (and without `'\n'` when there are newlines), and when the decoding is strict and there are
newlines, `ignorechars` names `'\n'`. `strict_mode` not given defaults to whether `ignorechars` is
given. This pins `padded`, `alphabet`, `wrapcol` and `newline` of the encoder against the decoder and
the decoder's `ignorechars`; it says nothing about how strictly it rejects, which is `B64StrictLaw`. -/
def B64RoundTripAll : Prop :=
  ∀ (d : List Nat) (alpha : Option (List Nat)) (padded : Bool) (wrapcol : Int) (newline : Bool)
    (strict : Option Bool) (g : Option (List Nat)) (canonical : Bool) (out : List Nat),
    (∀ x ∈ d, x < 256) →
    (∀ a, alpha = some a → GoodAlpha64 a ∧ ((wrapcol ≠ 0 ∨ newline = true) → 10 ∉ a)) →
    (strict.getD g.isSome = true → (wrapcol ≠ 0 ∨ newline = true) → ∃ l, g = some l ∧ 10 ∈ l) →
    b2aB64 (.bytes d) padded wrapcol newline (alpha.map .bytes) = .ok out →
    a2bB64 (.bytes out) strict padded (decAlphaOf alpha) (g.map .bytes) canonical = .ok d

theorem b64RoundTripAll_proven : B64RoundTripAll := by
  intro d alpha p w nl strict g k out hd ha hg h
  -- the encoder
  obtain ⟨n, hsz⟩ : ∃ n, sizeT w = .ok n := by
    cases hs : sizeT w with
    | ok n => exact ⟨n, rfl⟩
    | error e =>
      simp only [b2aB64, bufData, hs, bind, Except.bind] at h
      cases h
  have hn : w = (n : Int) := sizeT_ok w n hsz
  obtain ⟨A, hA, hA10, hAlpha, hEnc⟩ : ∃ A, GoodAlpha64 A ∧ ((w ≠ 0 ∨ nl = true) → 10 ∉ A) ∧
      decTable alpha (revT b64Alpha (some 61)) 64 (some 61) = .ok (revT A (some 61)) ∧
      out = b2a64Core A d p n nl := by
    cases alpha with
    | none =>
      refine ⟨b64Alpha, good_b64, fun _ => by decide +kernel, rfl, ?_⟩
      simp only [b2aB64, bufData, bufOpt, encTable, Option.map, bind, Except.bind, pure, Except.pure, hsz] at h
      cases h
      rfl
    | some a =>
      obtain ⟨hga, ha10⟩ := ha a rfl
      refine ⟨a, hga, ha10, ?_, ?_⟩
      · simp [decTable, hga.1]
      · simp only [b2aB64, bufData, bufOpt, encTable, Option.map, bind, Except.bind, pure, Except.pure, hsz,
          hga.1, ne_eq, not_true_eq_false, if_false] at h
        cases h
        rfl
  subst hEnc
  -- the decoder
  have hgd : bufOpt (g.map .bytes) = .ok g := by cases g <;> rfl
  have hal : alphaDec "a2b_base64" (decAlphaOf alpha) = .ok alpha := by
    cases alpha <;> rfl
  simp only [a2bB64, asciiBuffer, hal, hgd, bind, Except.bind, hAlpha]
  generalize hs : strict.getD g.isSome = s at hg
  generalize hig : (if !s || g.isNone || g == some [] then none else g) = ig
  have hc61 : 64 ≤ revT A (some 61) 61 := by rw [revT_pad, hA.1]; exact Nat.le_refl 64
  rw [core_slow ⟨s, p, revT A (some 61), ig⟩ hc61 k, slow_filter]
  let c : B64 := ⟨s, p, revT A (some 61), ig⟩
  have hU : ∀ x ∈ unwrapped64 A d p, (!skip64 c x) = true := by
    intro x hx
    rcases unwrapped64_mem A hA.1 d p x hx with hx | ⟨rfl, hp⟩
    · have := revT_mem_lt A hA x hx
      simp [skip64, c, Nat.not_le.mpr this]
    · simp [skip64, c, hp]
  have hN : (w ≠ 0 ∨ nl = true) → (!skip64 c 10) = false := by
    intro hw
    have h10 : revT A (some 61) 10 = 255 := revT_large A (some 61) 10 (by simp) (fun x hx e => hA10 hw (e ▸ hx))
    have hi : (!s || ign ig 10) = true := by
      cases hs' : s with
      | false => rfl
      | true =>
        obtain ⟨l, rfl, hl⟩ := hg hs' hw
        have hne : l ≠ [] := List.ne_nil_of_mem hl
        rw [hs'] at hig
        have : ig = some l := by
          rw [← hig]
          simp [hne]
        subst this
        simp [ign, hl]
    simp [skip64, c, h10, hi]
  have hfilt : (b2a64Core A d p n nl).filter (fun x => !skip64 c x) = unwrapped64 A d p := by
    have e : b2a64Core A d p n nl =
        (if (if n = 0 then 0 else if n < 4 then 4 else n / 4 * 4) ≠ 0 then
          wraplinesC (unwrapped64 A d p) (if n = 0 then 0 else if n < 4 then 4 else n / 4 * 4)
         else unwrapped64 A d p) ++ (if nl then [10] else []) := by
      simp only [b2a64Core, unwrapped64, pads64]
      cases nl <;> simp
    rw [e, List.filter_append]
    have hnl : (if nl then [10] else []).filter (fun x => !skip64 c x) = [] := by
      cases hnl : nl with
      | false => rfl
      | true => simp [hN (.inr hnl)]
    rw [hnl, List.append_nil]
    by_cases h0 : n = 0
    · subst h0
      simp only [if_true, ne_eq, not_true_eq_false, if_false]
      exact List.filter_eq_self.mpr hU
    · have hpos : 0 < (if n < 4 then 4 else n / 4 * 4) := by split <;> omega
      rw [if_neg h0, if_pos (by omega)]
      exact wraplinesC_filterP _ hpos _ (hN (.inl (by omega))) _ _ (Nat.le_refl _) hU
  rw [hfilt]
  obtain ⟨st, h1, h2⟩ := dec_enc c A hA rfl k d.length d [] (Nat.le_refl _) hd
  have e0 : ({} : Dec) = ⟨0, 0, 0, []⟩ := rfl
  rw [e0, h1]
  exact h2

end PyLean.TextLibs.Binascii
