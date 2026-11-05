import PyLean.TextLibs.BinasciiEq

/-!
What `Lib/base64.py` of 3.15.2 adds on top of the C codecs for base64 and base16: `padded=False` in
`urlsafe_b64decode`, the alphabet of `urlsafe_b64encode`, `wrapcol` in `encodebytes`, and the lower case
check of `b16decode`.
-/

namespace PyLean.TextLibs.Binascii

open PyLean

set_option linter.unusedSimpArgs false

/-! ### `padded=False` -/

/-- The options of `a2b_base64(s, strict_mode=False, padded=False)`. -/
def np : B64 := ⟨false, false, revT b64Alpha (some 61), none⟩

theorem np_padded : np.padded = false := rfl
theorem np_strict : np.strict = false := rfl
theorem np_tbl : np.tbl = revT b64Alpha (some 61) := rfl
theorem np_ig : np.ig = none := rfl

/-- With `padded=False` a `=` is a character outside the alphabet, skipped like any other, so the
state differs from the default one only in the count of pads. -/
theorem np_run : ∀ (f : Nat) (s : List Nat) (st r : Dec), s.length < f → a2bLoop false s 0 st = .ok r →
    a2b64Run np f s { st with pads := 0 } = .ok { r with pads := 0 } := by
  intro f
  induction f with
  | zero => intro _ _ _ h; omega
  | succ f ih =>
    intro s st r hl h
    cases s with
    | nil =>
      simp only [a2bLoop, Except.ok.injEq] at h
      subst h
      rfl
    | cons x xs =>
      have hxs : xs.length < f := by simpa using hl
      by_cases hx : x = 61
      · subst hx
        have h1 : a2bLoop false xs 0 { st with pads := st.pads + 1 } = .ok r := by
          rw [← h, a2bLoop]
          simp only [if_true]
          split
          · exact a2bLoop_i _ _ _ _ _
          · simp only [Bool.not_false, if_true]
            exact a2bLoop_i _ _ _ _ _
        have h2 := ih xs _ r hxs h1
        simp only [a2b64Run, np_padded, Bool.false_and, Bool.false_eq_true, if_false, np_tbl, revT64, if_true,
          np_strict, ge_iff_le, Nat.le_refl]
        exact h2
      · have hne : (x == 61) = false := by simpa using hx
        rw [a2bLoop, if_neg hx] at h
        simp only [Bool.false_eq_true, if_false, and_false] at h
        simp only [a2b64Run, np_padded, Bool.false_and, Bool.false_eq_true, if_false, np_tbl, revT64, if_neg hx,
          np_strict, and_false]
        split
        · rename_i h64
          rw [if_pos h64] at h
          exact ih xs _ r hxs ((a2bLoop_i _ _ _ _ _).trans h)
        · rename_i h64
          rw [if_neg h64] at h
          have hp : ({ st with pads := 0 } : Dec).pads = 0 := rfl
          simp only [hp, ne_eq, not_true_eq_false, false_and, if_false]
          have h' := (a2bLoop_i false xs 0 _ _).trans h
          split
          · rename_i hq
            obtain ⟨q, p, l, o⟩ := st
            simp only at hq
            subst hq
            simp only [decStep] at h' ⊢
            have hf := fast_len (revT b64Alpha (some 61)) xs.length xs (o ++ [(l * 64 + a2bChar x) % 256]) (Nat.le_refl _)
            rw [fast_loop false xs.length xs _ (Nat.le_refl _) 0] at h'
            exact ih _ _ r (by omega) h'
          · have hd : ∀ (t : Dec), t.pads = 0 → (decStep t (a2bChar x)).pads = 0 := by
              intro t ht
              simp only [decStep]
              split <;> exact ht
            have := ih xs _ r hxs h'
            have e : { decStep { st with pads := 0 } (a2bChar x) with pads := 0 } =
                decStep { st with pads := 0 } (a2bChar x) := by
              generalize hg : decStep { st with pads := 0 } (a2bChar x) = g
              have := hd { st with pads := 0 } rfl
              rw [hg] at this
              cases g
              simp_all
            rw [e] at this
            exact this

/-- `padded=False` can only accept more: what the default mode decodes, it decodes to the same bytes. -/
theorem pad_irrelevant (s d : List Nat) (h : a2bBase64Bytes false s = .ok d) : a2b64Core np false s = .ok d := by
  simp only [a2bBase64Bytes, bind, Except.bind] at h
  cases hl : a2bLoop false s 0 {} with
  | error e =>
    rw [hl] at h
    cases h
  | ok r =>
    rw [hl] at h
    simp only at h
    have hq : r.quad ≠ 1 := by
      intro e
      simp [e, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw] at h
    rw [if_neg hq] at h
    split at h
    · simp [throw, throwThe, MonadExcept.throw, MonadExceptOf.throw] at h
    · have hd : r.out = d := by simpa [pure, Except.pure] using h
      have h1 : a2bLoop false (fast64 (revT b64Alpha (some 61)) s []).1 0
          ⟨0, 0, 0, (fast64 (revT b64Alpha (some 61)) s []).2⟩ = .ok r := by
        rw [← fast_loop false s.length s [] (Nat.le_refl _) 0]
        exact hl
      have hf := fast_len (revT b64Alpha (some 61)) s.length s [] (Nat.le_refl _)
      have h2 := np_run (s.length + 1) _ _ r (by omega) h1
      simp only [a2b64Core, np_tbl, bind, Except.bind]
      have h3 : a2b64Run np (s.length + 1) (fast64 (revT b64Alpha (some 61)) s []).1
          { out := (fast64 (revT b64Alpha (some 61)) s []).2 } = .ok { r with pads := 0 } := h2
      rw [h3]
      simp [hq, np_padded, hd, pure, Except.pure]

/-! ### The urlsafe alphabet -/

theorem url_chars : ∀ v, v < 64 → urlAlpha.getD v 0 = tr plusSlash dashUnderscore (b64Alpha.getD v 0) := by
  decide +kernel

theorem fastEnc_url : ∀ (n : Nat) (d : List Nat), d.length ≤ n →
    (fastEnc64 urlAlpha d).1 = (fastEnc64 b64Alpha d).1.map (tr plusSlash dashUnderscore) ∧
      (fastEnc64 urlAlpha d).2 = (fastEnc64 b64Alpha d).2 := by
  intro n
  induction n with
  | zero =>
    intro d h
    have : d = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    exact ⟨rfl, rfl⟩
  | succ n ih =>
    intro d h
    match d, h with
    | [], _ => exact ⟨rfl, rfl⟩
    | [_], _ => exact ⟨rfl, rfl⟩
    | [_, _], _ => exact ⟨rfl, rfl⟩
    | a :: b :: c :: r, h =>
      obtain ⟨h1, h2⟩ := ih r (by simp at h; omega)
      simp only [fastEnc64]
      refine ⟨?_, h2⟩
      rw [h1]
      simp only [List.cons_append, List.nil_append, List.map_cons]
      rw [url_chars _ (Nat.mod_lt _ (by decide)), url_chars _ (Nat.mod_lt _ (by decide)),
        url_chars _ (Nat.mod_lt _ (by decide)), url_chars _ (Nat.mod_lt _ (by decide))]

theorem tail_url (s : List Nat) : tail64 urlAlpha s = (tail64 b64Alpha s).map (tr plusSlash dashUnderscore) := by
  match s with
  | [] => rfl
  | [a] =>
    simp only [tail64, List.map_cons, List.map_nil]
    rw [url_chars _ (Nat.mod_lt _ (by decide)), url_chars _ (Nat.mod_lt _ (by decide))]
  | [a, b] =>
    simp only [tail64, List.map_cons, List.map_nil]
    rw [url_chars _ (Nat.mod_lt _ (by decide)), url_chars _ (Nat.mod_lt _ (by decide)),
      url_chars _ (Nat.mod_lt _ (by decide))]
  | _ :: _ :: _ :: _ => rfl

theorem tr_pad : tr plusSlash dashUnderscore 61 = 61 := by decide

theorem url_core (d : List Nat) (hd : ∀ x ∈ d, x < 256) :
    b2a64Core urlAlpha d true 0 false = translate plusSlash dashUnderscore (enc d 0) := by
  have h := b2a64Core_eq d hd false
  have e : enc d 0 = b2a64Core b64Alpha d true 0 false := by rw [h, b2aBase64_eq_enc]
  rw [e]
  obtain ⟨h1, h2⟩ := fastEnc_url d.length d (Nat.le_refl _)
  have ht : translate plusSlash dashUnderscore =
      List.map (tr plusSlash dashUnderscore) := rfl
  rw [ht]
  simp only [b2a64Core, Bool.false_eq_true, if_false, if_true, ne_eq, not_true_eq_false, List.map_append, h1, h2,
    tail_url, List.map_replicate, tr_pad, List.append_assoc]

/-- `urlsafe_b64decode(urlsafe_b64encode(d), padded=q) == d`, for every `bytes` value and for both values
of `padded`: its default in `urlsafe_b64decode` is `False`, and `urlsafe_b64encode` pads by default. -/
def UrlsafeRoundTripC : Prop :=
  ∀ (q : Bool) (d out : List Nat), (∀ x ∈ d, x < 256) → pyUrlsafeEnc (.bytes d) true = .ok out →
    pyUrlsafeDec (.bytes out) q = .ok d

theorem url_alpha_len : urlAlpha.length = 64 := by decide

theorem urlsafeRoundTripC_proven : UrlsafeRoundTripC := by
  intro q d out hd h
  have h1 : out = translate plusSlash dashUnderscore (enc d 0) := by
    have : pyUrlsafeEnc (.bytes d) true = .ok (b2a64Core urlAlpha d true 0 false) := by
      simp [pyUrlsafeEnc, b2aB64, bufData, sizeT, bufOpt, encTable, url_alpha_len, bind, Except.bind, pure, Except.pure]
    rw [this, url_core d hd] at h
    cases h
    rfl
  subst h1
  have nd : ∀ c ∈ enc d 0, c ≠ 45 ∧ c ≠ 95 := by
    rw [← b2aBase64_eq_enc]
    exact b2a_no_dash d
  have hb := base64RoundTrip_proven false d hd
  rw [b2aBase64_eq_enc] at hb
  simp only [pyUrlsafeDec, bytesFromDecodeData, bind, Except.bind]
  rw [translate_back _ nd]
  cases q with
  | true =>
    have := a2bB64_eq false (.bytes (enc d 0))
    rw [this]
    simpa [a2bBase64, asciiBuffer, bind, Except.bind] using hb
  | false =>
    have h2 := pad_irrelevant _ _ hb
    simpa [a2bB64, asciiBuffer, alphaDec, bufOpt, decTable, bind, Except.bind, pure, Except.pure, np] using h2

/-! ### base16 -/

theorem upper_hex_lt : ∀ v, v < 16 →
    (if 97 ≤ hexDigit v ∧ hexDigit v ≤ 122 then hexDigit v - 32 else hexDigit v) < 97 := by
  decide

theorem upperHex_loop (ig : Option (List Nat)) : ∀ (d out : List Nat), (∀ x ∈ d, x < 256) →
    a2bHexIg ig (upper (b2aHex d)) none out = .ok (out ++ d) ∧ ∀ c ∈ upper (b2aHex d), c < 97 := by
  intro d
  induction d with
  | nil => intro out _; simp [b2aHex, a2bHexIg, upper]
  | cons x r ih =>
    intro out h
    have hx : x < 256 := h x (by simp)
    obtain ⟨t1, -⟩ := upper_hex (x / 16) (by omega)
    obtain ⟨u1, -⟩ := upper_hex (x % 16) (by omega)
    have l1 := upper_hex_lt (x / 16) (by omega)
    have l2 := upper_hex_lt (x % 16) (by omega)
    have e : (x / 16) * 16 + x % 16 = x := by omega
    have hr := fun o => ih o (fun y hy => h y (by simp [hy]))
    constructor
    · simp only [b2aHex, upper, List.map_cons, a2bHexIg, t1, u1]
      rw [if_neg (by omega), if_neg (by omega), e]
      have := (hr (out ++ [x])).1
      simp only [upper] at this
      rw [this]
      simp
    · intro c hc
      simp only [b2aHex, upper, List.map_cons, List.mem_cons] at hc
      rcases hc with rfl | rfl | hc
      · exact l1
      · exact l2
      · exact (hr []).2 c hc

/-- `b16decode(b16encode(d)) == d`: only upper case digits are written, so the check for lower case
of the default `casefold=False` has nothing to find, and the filter that follows it leaves them. -/
def B16RoundTripC : Prop :=
  ∀ (d out : List Nat), (∀ x ∈ d, x < 256) → pyB16encode (.bytes d) 0 = .ok out →
    pyB16decode (.bytes out) false (.bytes []) = .ok d

theorem b16RoundTripC_proven : B16RoundTripC := by
  intro d out hd h
  have h1 : out = upper (b2aHex d) := by
    simp [pyB16encode, bufData, bind, Except.bind, pure, Except.pure] at h
    exact h.symm
  subst h1
  obtain ⟨h2, h3⟩ := upperHex_loop none d [] hd
  have hl : ∀ c ∈ upper (b2aHex d), c < 97 := h3
  have hany : ([97, 98, 99, 100, 101, 102] : List Nat).any
      (fun b => (upper (b2aHex d)).contains b && !([] : List Nat).contains b) = false := by
    apply List.any_eq_false.mpr
    intro b hb hc
    have hm : b ∈ upper (b2aHex d) := by
      have : (upper (b2aHex d)).contains b = true := by simpa using hc
      simpa using this
    have := hl b hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    omega
  have hf : (upper (b2aHex d)).filter (fun c => !([97, 98, 99, 100, 101, 102] : List Nat).contains c) =
      upper (b2aHex d) := by
    apply List.filter_eq_self.mpr
    intro c hc
    have := hl c hc
    have hn : ¬ c ∈ ([97, 98, 99, 100, 101, 102] : List Nat) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      omega
    simpa using hn
  simp only [pyB16decode, bytesFromDecodeData, toBytesIg, toBytesView, bind, Except.bind, Bool.not_false, if_true, hany,
    Bool.false_eq_true, if_false, hf, a2bHexI, asciiBuffer, bufData, List.isEmpty_nil]
  simpa using h2

/-! ### `encodebytes` -/

theorem pads64_eq (d : List Nat) (hd : ∀ x ∈ d, x < 256) (left : Nat) : enc d left = enc d 0 := by
  rw [← enc_c d.length d (Nat.le_refl _) hd left, ← enc_c d.length d (Nat.le_refl _) hd 0]

theorem enc_append : ∀ (n : Nat) (a b : List Nat), a.length = 3 * n → (∀ x ∈ a, x < 256) → (∀ x ∈ b, x < 256) →
    enc (a ++ b) 0 = enc a 0 ++ enc b 0 := by
  intro n
  induction n with
  | zero =>
    intro a b h _ _
    have : a = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp [enc, b2aLoop]
  | succ n ih =>
    intro a b h ha hb
    match a, h, ha with
    | x :: y :: z :: r, h, ha =>
      have hx : x < 256 := ha x (by simp)
      have hy : y < 256 := ha y (by simp)
      have hz : z < 256 := ha z (by simp)
      have hr : ∀ c ∈ r, c < 256 := fun c hc => ha c (by simp [hc])
      have hrb : ∀ c ∈ r ++ b, c < 256 := by
        intro c hc
        rcases List.mem_append.mp hc with h1 | h1
        · exact hr c h1
        · exact hb c h1
      have e : (x :: y :: z :: r) ++ b = x :: y :: z :: (r ++ b) := rfl
      rw [e, enc_three x y z hx hy hz, enc_three x y z hx hy hz, pads64_eq _ hrb, pads64_eq _ hr,
        ih r b (by simp at h; omega) hr hb]
      simp

theorem wrap_stream : ∀ (n : Nat) (d : List Nat), d.length ≤ n → (∀ x ∈ d, x < 256) → d ≠ [] →
    ∀ (f g : Nat), (enc d 0).length ≤ f → d.length + 1 ≤ g →
    wraplines 76 f (enc d 0) ++ [10] = encodeStream g d := by
  intro n
  induction n with
  | zero =>
    intro d h _ hne
    exact absurd (List.eq_nil_of_length_eq_zero (by omega)) hne
  | succ n ih =>
    intro d h hd hne f g hf hg
    obtain ⟨g, rfl⟩ : ∃ k, g = k + 1 := ⟨g - 1, by omega⟩
    match d, hd, hne with
    | x :: t, hd, _ =>
      rw [stream_cons, b2aBase64_true]
      generalize hs : x :: t = s at *
      have hlen := enc_length s.length s (Nat.le_refl _) hd 0
      by_cases hl : s.length ≤ MAXBINSIZE
      · rw [List.take_of_length_le hl, List.drop_of_length_le hl, stream_nil, List.append_nil]
        have h76 : (enc s 0).length ≤ 76 := by
          simp only [MAXBINSIZE] at hl
          omega
        have hw : wraplines 76 f (enc s 0) = enc s 0 := by
          cases f with
          | zero => rfl
          | succ f => rw [wraplines, if_pos h76]
        rw [hw]
      · have h57 : (s.take MAXBINSIZE).length = MAXBINSIZE := by
          simp only [List.length_take]
          omega
        have hsa : ∀ y ∈ s.take MAXBINSIZE, y < 256 := fun y hy => hd y (List.mem_of_mem_take hy)
        have hsb : ∀ y ∈ s.drop MAXBINSIZE, y < 256 := fun y hy => hd y (List.mem_of_mem_drop hy)
        have hsplit : enc s 0 = enc (s.take MAXBINSIZE) 0 ++ enc (s.drop MAXBINSIZE) 0 := by
          have := enc_append 19 _ _ (by rw [h57]; rfl) hsa hsb
          rwa [List.take_append_drop] at this
        have h1 : (enc (s.take MAXBINSIZE) 0).length = 76 := by
          rw [enc_length _ _ (Nat.le_refl _) hsa 0, h57]
          rfl
        have hdne : s.drop MAXBINSIZE ≠ [] := by
          intro e
          have := congrArg List.length e
          simp only [List.length_drop, List.length_nil] at this
          omega
        have h2 : (enc (s.drop MAXBINSIZE) 0).length ≠ 0 := by
          rw [enc_length _ _ (Nat.le_refl _) hsb 0, List.length_drop]
          simp only [MAXBINSIZE] at hl ⊢
          omega
        have hlen2 : (enc s 0).length = 76 + (enc (s.drop MAXBINSIZE) 0).length := by
          rw [hsplit, List.length_append, h1]
        obtain ⟨f, rfl⟩ : ∃ k, f = k + 1 := ⟨f - 1, by omega⟩
        rw [wraplines, if_neg (by omega)]
        have et : (enc s 0).take 76 = enc (s.take MAXBINSIZE) 0 := by
          rw [hsplit, List.take_left' h1]
        have ed : (enc s 0).drop 76 = enc (s.drop MAXBINSIZE) 0 := by
          rw [hsplit, List.drop_left' h1]
        rw [et, ed]
        have := ih (s.drop MAXBINSIZE)
          (by simp only [List.length_drop, MAXBINSIZE] at h hl ⊢; omega) hsb hdne f g (by omega)
          (by simp only [List.length_drop, MAXBINSIZE] at hl hg ⊢; omega)
        rw [← this]
        simp [List.append_assoc]

/-- `encodebytes`, with its `wrapcol=76`, is what it was when it cut the input into slices of 57 bytes. -/
theorem pyEncodebytes_eq (d : List Nat) (hd : ∀ x ∈ d, x < 256) : pyEncodebytes d = encodebytes d := by
  have hc : (fastEnc64 b64Alpha d).1 ++ tail64 b64Alpha (fastEnc64 b64Alpha d).2 ++
      List.replicate ((3 - d.length % 3) % 3 * 4 / 3) 61 = enc d 0 :=
    enc_c d.length d (Nat.le_refl _) hd 0
  have e : b2a64Core b64Alpha d true 76 true = wraplines 76 (enc d 0).length (enc d 0) ++ [10] := by
    simp [b2a64Core, hc, wraplinesC_eq 76 (by decide) (enc d 0).length (enc d 0) (Nat.le_refl _)]
  cases d with
  | nil =>
    have : pyEncodebytes [] = [] := by decide
    rw [this]
    rfl
  | cons x t =>
    have hne : (enc (x :: t) 0).length ≠ 0 := by
      rw [enc_length _ _ (Nat.le_refl _) hd 0]
      simp only [List.length_cons]
      omega
    have hw := wrap_stream _ (x :: t) (Nat.le_refl _) hd (by simp) _ (x :: t).length.succ (Nat.le_refl _) (Nat.le_refl _)
    have hbeq : (wraplines 76 (enc (x :: t) 0).length (enc (x :: t) 0) ++ [10] == [10]) = false := by
      have hlenw : (wraplines 76 (enc (x :: t) 0).length (enc (x :: t) 0)) ≠ [] := by
        cases hf : (enc (x :: t) 0).length with
        | zero => exact absurd hf hne
        | succ m =>
          rw [wraplines]
          split
          · intro h0
            rw [h0] at hf
            simp at hf
          · simp [List.take_eq_nil_iff]
      apply beq_false_of_ne
      intro h0
      have := congrArg List.length h0
      simp only [List.length_append, List.length_cons, List.length_nil] at this
      exact hlenw (List.eq_nil_of_length_eq_zero (by omega))
    simp only [pyEncodebytes, e, hbeq, Bool.false_eq_true, if_false]
    exact hw

/-- `decodebytes(encodebytes(d)) == d`, for every `bytes` value. -/
def DecodebytesRoundTripC : Prop :=
  ∀ d : List Nat, (∀ x ∈ d, x < 256) →
    a2bB64 (.bytes (pyEncodebytes d)) (some false) true .absent none false = .ok d

theorem decodebytesRoundTripC_proven : DecodebytesRoundTripC := by
  intro d hd
  rw [a2bB64_eq, pyEncodebytes_eq d hd]
  exact decodebytesRoundTrip_proven d hd

/-- Every line `encodebytes` writes but the last holds exactly 76 characters and its newline. -/
def EncodebytesLineLengthC : Prop :=
  ∀ d : List Nat, (∀ x ∈ d, x < 256) → MAXBINSIZE < d.length →
    (pyEncodebytes d).take 77 = b2a64Core b64Alpha (d.take MAXBINSIZE) true 0 true ∧
      (b2a64Core b64Alpha (d.take MAXBINSIZE) true 0 false).length = 76

theorem encodebytesLineLengthC_proven : EncodebytesLineLengthC := by
  intro d hd hl
  have hb : ∀ x ∈ d.take MAXBINSIZE, x < 256 := fun y hy => hd y (List.mem_of_mem_take hy)
  obtain ⟨h1, h2⟩ := encodebytesLineLength_proven d hd hl
  rw [pyEncodebytes_eq d hd, b2a64Core_eq _ hb, b2a64Core_eq _ hb, b2aBase64_true, b2aBase64_eq_enc]
  exact ⟨h1, h2⟩

/-- The `base64.encode` of a file is `encodebytes` of its bytes, when no call fails. -/
def EncodeFileAgreesC : Prop :=
  ∀ f : FileSim, Steady f → (∀ x ∈ f.data, x < 256) → (∀ e, .raises e ∉ f.reads) → (∀ e, .error e ∉ f.writes) →
    ∀ fuel, f.data.length + 1 ≤ fuel →
    ∃ g ext, encodeFile fuel f = (g, .ok ()) ∧ g.written = f.written ++ ext ∧
      ext.flatten = pyEncodebytes f.data

theorem encodeFileAgreesC_proven : EncodeFileAgreesC := by
  intro f hs hb h1 h2 fuel hf
  rw [pyEncodebytes_eq _ hb]
  exact encodeFileAgrees_proven f hs h1 h2 fuel hf

/-- `base64.decode` over the lines `readline` finds in `encodebytes(d)` writes `d` back. -/
def DecodeFileRoundTripC : Prop :=
  ∀ (d : List Nat) (f : FileSim), (∀ x ∈ d, x < 256) → f.writes = [] →
    ∃ g, decodeFile (((splitLines ((pyEncodebytes d).length + 1) (pyEncodebytes d)).map .ok) ++ [.ok []]) f =
        (g, .ok ()) ∧ g.written.flatten = f.written.flatten ++ d

theorem decodeFileRoundTripC_proven : DecodeFileRoundTripC := by
  intro d f hd hw
  rw [pyEncodebytes_eq d hd]
  exact decodeFileRoundTrip_proven d f hd hw

/-- `standard_b64encode` and `standard_b64decode` are `b64encode` and `b64decode`, `Lib/base64.py:135-150`. -/
def pyStandardEnc (s : Data) : Py (List Nat) := pyB64encode s none true 0
def pyStandardDec (s : Data) : Py (List Nat) := pyB64decode s none none true none false

/-- The `standard_` names round-trip like `b64encode`. -/
def StandardRoundTripC : Prop :=
  ∀ d out : List Nat, (∀ x ∈ d, x < 256) → pyStandardEnc (.bytes d) = .ok out → pyStandardDec (.bytes out) = .ok d

theorem standardRoundTripC_proven : StandardRoundTripC := by
  intro d out hd h
  exact b64ModuleRoundTripC_proven false d out hd h

end PyLean.TextLibs.Binascii
