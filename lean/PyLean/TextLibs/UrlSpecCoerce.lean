import PyLean.TextLibs.UrlSpecUnsplit

/-!
`_coerce_args` and `_decode_args` on every argument list: mixing `str` with non-empty `bytes`
raises `TypeError`, non-ASCII `bytes` raise `UnicodeDecodeError`, and otherwise the arguments
pass through (`str`) or are decoded as ASCII (`bytes`). And the result classes' `encode` and
`decode` with every codec of the model and every error handler.
-/

namespace PyLean.TextLibs.Url

open PyLean
open PyLean.UnicodeObj (ErrHandler)

set_option linter.unusedSimpArgs false

/-! ## `_coerce_args` -/

theorem mixLoop_mix : ∀ (args : List Arg) (si : Option Bool),
    ((∃ a ∈ args, a.truthy = true ∧ a.isStr = true) ∨ si = some true) →
    ((∃ a ∈ args, a.truthy = true ∧ a.isStr = false) ∨ si = some false) →
    mixLoop si args = .error (.typeError "Cannot mix str and non-str arguments")
  | [], si, h1, h2 => by
    rcases h1 with ⟨a, ha, _⟩ | h1
    · simp at ha
    · rcases h2 with ⟨a, ha, _⟩ | h2
      · simp at ha
      · rw [h1] at h2; cases h2
  | a :: r, si, h1, h2 => by
    unfold mixLoop
    by_cases ht : a.truthy = true
    · rw [if_pos ht]
      cases si with
      | none =>
        apply mixLoop_mix r (some a.isStr)
        · rcases h1 with ⟨b, hb, hbt, hbs⟩ | h1
          · rcases List.mem_cons.1 hb with rfl | hb
            · right; rw [hbs]
            · left; exact ⟨b, hb, hbt, hbs⟩
          · cases h1
        · rcases h2 with ⟨b, hb, hbt, hbs⟩ | h2
          · rcases List.mem_cons.1 hb with rfl | hb
            · right; rw [hbs]
            · left; exact ⟨b, hb, hbt, hbs⟩
          · cases h2
      | some b =>
        dsimp only
        by_cases hd : (a.isStr != b) = true
        · rw [if_pos hd]
        · rw [if_neg hd]
          simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hd
          apply mixLoop_mix r (some b)
          · rcases h1 with ⟨c, hc, hct, hcs⟩ | h1
            · rcases List.mem_cons.1 hc with rfl | hc
              · right; rw [← hd, hcs]
              · left; exact ⟨c, hc, hct, hcs⟩
            · right; exact h1
          · rcases h2 with ⟨c, hc, hct, hcs⟩ | h2
            · rcases List.mem_cons.1 hc with rfl | hc
              · right; rw [← hd, hcs]
              · left; exact ⟨c, hc, hct, hcs⟩
            · right; exact h2
    · rw [if_neg ht]
      apply mixLoop_mix r si
      · rcases h1 with ⟨b, hb, hbt, hbs⟩ | h1
        · rcases List.mem_cons.1 hb with rfl | hb
          · exact absurd hbt ht
          · left; exact ⟨b, hb, hbt, hbs⟩
        · right; exact h1
      · rcases h2 with ⟨b, hb, hbt, hbs⟩ | h2
        · rcases List.mem_cons.1 hb with rfl | hb
          · exact absurd hbt ht
          · left; exact ⟨b, hb, hbt, hbs⟩
        · right; exact h2

/-- Without mixing, the first loop finds the kind of the true arguments. -/
theorem mixLoop_same (k : Bool) : ∀ (args : List Arg) (si : Option Bool), (si = none ∨ si = some k) →
    (∀ a ∈ args, a.truthy = true → a.isStr = k) →
    mixLoop si args = .ok (if (∃ a ∈ args, a.truthy = true) then some k else si)
  | [], si, _, _ => by simp [mixLoop]
  | a :: r, si, hsi, hall => by
    unfold mixLoop
    by_cases ht : a.truthy = true
    · rw [if_pos ht]
      have hk := hall a List.mem_cons_self ht
      have ih := mixLoop_same k r (some k) (Or.inr rfl) (fun b hb => hall b (List.mem_cons_of_mem _ hb))
      rcases hsi with rfl | rfl
      · simp only [hk]
        rw [ih]
        simp only [if_pos (⟨a, List.mem_cons_self, ht⟩ : ∃ b ∈ a :: r, b.truthy = true)]
        split <;> rfl
      · simp only [hk, bne_self_eq_false, Bool.false_eq_true, ite_false]
        rw [ih]
        simp only [if_pos (⟨a, List.mem_cons_self, ht⟩ : ∃ b ∈ a :: r, b.truthy = true)]
        split <;> rfl
    · rw [if_neg ht]
      rw [mixLoop_same k r si hsi (fun b hb => hall b (List.mem_cons_of_mem _ hb))]
      have hiff : (∃ b ∈ a :: r, b.truthy = true) ↔ (∃ b ∈ r, b.truthy = true) := by
        constructor
        · rintro ⟨b, hb, hbt⟩
          rcases List.mem_cons.1 hb with rfl | hb
          · exact absurd hbt ht
          · exact ⟨b, hb, hbt⟩
        · rintro ⟨b, hb, hbt⟩; exact ⟨b, List.mem_cons_of_mem _ hb, hbt⟩
      simp only [hiff]

/-- An argument after `_decode_args`, when it succeeds: a true `bytes` decoded, `''` for any other
value that is not `None`. -/
def decodedV : Arg → Option V
  | .none => none
  | .bytes b _ => some (.s b)
  | .str _ => some (.s [])

theorem asciiDriver_raises (input : Str) :
    ∀ (s : Str) (fuel pos : Nat) (out : Str), s.length < fuel → (∃ c ∈ s, 128 ≤ c) →
      (UnicodeObj.decodeDriver UnicodeObj.stepAscii .strict "ascii" .unknown input fuel pos s out).raises
        "UnicodeDecodeError"
  | [], _, _, _, _, ⟨c, hc, _⟩ => by simp at hc
  | _ :: _, 0, _, _, hl, _ => by simp at hl
  | c :: r, fuel + 1, pos, out, hl, hex => by
    by_cases hc : c < 128
    · simp only [UnicodeObj.decodeDriver, UnicodeObj.stepAscii, if_pos hc, List.drop_one, List.tail_cons]
      apply asciiDriver_raises input r fuel _ _ (by simp at hl; omega)
      obtain ⟨d, hd, hld⟩ := hex
      rcases List.mem_cons.1 hd with rfl | hd
      · omega
      · exact ⟨d, hd, hld⟩
    · simp only [UnicodeObj.decodeDriver, UnicodeObj.stepAscii, if_neg hc, UnicodeObj.decodeHandlerCall]
      refine ⟨_, rfl, ?_⟩
      unfold UnicodeObj.decodeError; split <;> rfl

theorem asciiDecode_raises (b : Str) (h : ∃ c ∈ b, 128 ≤ c) :
    (UnicodeObj.asciiDecode b .strict).raises "UnicodeDecodeError" := by
  unfold UnicodeObj.asciiDecode
  obtain ⟨e, he, hc⟩ := asciiDriver_raises b b (b.length + 1) 0 [] (by omega) h
  exact ⟨e, by simp only [bind, Except.bind, he], hc⟩

theorem decodeArgs_ok (args : List Arg) (hs : ∀ a ∈ args, a.truthy = true → a.isStr = false)
    (ha : ∀ a ∈ args, ∀ b ba, a = .bytes b ba → ∀ c ∈ b, c < 128) :
    decodeArgs args = .ok (args.map decodedV) := by
  induction args with
  | nil => rfl
  | cons a r ih =>
    have ih' := ih (fun b hb => hs b (List.mem_cons_of_mem _ hb)) (fun b hb => ha b (List.mem_cons_of_mem _ hb))
    have hd : decodeArg a = .ok (decodedV a) := by
      unfold decodeArg
      cases a with
      | none => rfl
      | str s =>
        have : (Arg.str s).truthy = false := by
          cases hc : (Arg.str s).truthy
          · rfl
          · have := hs _ List.mem_cons_self hc
            simp [Arg.isStr] at this
        rw [if_neg (by simp [this])]
        have hs0 : s = [] := by simpa [Arg.truthy] using this
        subst hs0; rfl
      | bytes b ba =>
        by_cases hb : (Arg.bytes b ba).truthy = true
        · rw [if_pos hb]
          simp [asciiDecode_ascii b .strict (ha _ List.mem_cons_self b ba rfl), Except.map, decodedV]
        · rw [if_neg hb]
          have hb0 : b = [] := by simpa [Arg.truthy] using hb
          subst hb0; rfl
    simp only [decodeArgs, hd, ih', bind, Except.bind, pure, Except.pure, List.map_cons]

theorem decodeArgs_raises (args : List Arg) (hs : ∀ a ∈ args, a.truthy = true → a.isStr = false)
    (hn : ∃ a ∈ args, ∃ b ba, a = .bytes b ba ∧ ∃ c ∈ b, 128 ≤ c) :
    (decodeArgs args).raises "UnicodeDecodeError" := by
  induction args with
  | nil => obtain ⟨a, ha, _⟩ := hn; simp at ha
  | cons a r ih =>
    unfold decodeArgs
    by_cases hbad : ∃ b ba, a = .bytes b ba ∧ ∃ c ∈ b, 128 ≤ c
    · obtain ⟨b, ba, rfl, c, hc, hc128⟩ := hbad
      have ht : (Arg.bytes b ba).truthy = true := by
        cases b with
        | nil => simp at hc
        | cons _ _ => rfl
      have hd : (decodeArg (.bytes b ba)).raises "UnicodeDecodeError" := by
        unfold decodeArg
        rw [if_pos ht]
        obtain ⟨e, he, hcl⟩ := asciiDecode_raises b ⟨c, hc, hc128⟩
        exact ⟨e, by simp [he, Except.map], hcl⟩
      exact raises_bind _ _ _ hd
    · have hn' : ∃ a ∈ r, ∃ b ba, a = .bytes b ba ∧ ∃ c ∈ b, 128 ≤ c := by
        obtain ⟨x, hx, hxb⟩ := hn
        rcases List.mem_cons.1 hx with rfl | hx
        · exact absurd hxb hbad
        · exact ⟨x, hx, hxb⟩
      obtain ⟨e, he, hcl⟩ := ih (fun b hb => hs b (List.mem_cons_of_mem _ hb)) hn'
      have hok : ∃ v, decodeArg a = .ok v := by
        unfold decodeArg
        cases a with
        | none => exact ⟨_, rfl⟩
        | str s =>
          by_cases ht : (Arg.str s).truthy = true
          · have := hs _ List.mem_cons_self ht; simp [Arg.isStr] at this
          · rw [if_neg ht]; exact ⟨_, rfl⟩
        | bytes b ba =>
          by_cases ht : (Arg.bytes b ba).truthy = true
          · rw [if_pos ht]
            have hasc : ∀ c ∈ b, c < 128 := by
              intro c hc
              exact Nat.lt_of_not_le (fun hge => hbad ⟨b, ba, rfl, c, hc, hge⟩)
            exact ⟨some (.s b), by simp [asciiDecode_ascii b .strict hasc, Except.map]⟩
          · rw [if_neg ht]; exact ⟨_, rfl⟩
      obtain ⟨v, hv⟩ := hok
      exact ⟨e, by simp [hv, he, bind, Except.bind], hcl⟩

/-- For every list of arguments (`None`, `str`, `bytes`, `bytearray`): `_coerce_args` raises
`TypeError('Cannot mix str and non-str arguments')` when a true `str` and a true non-`str` are
both present. Otherwise, when every true argument is a `str` and there is one, it returns the
arguments unchanged with the identity as the result coercion; when every true argument is
`bytes`/`bytearray` and there is one, it decodes them with ASCII (each true one decoded, every
other non-`None` one `''`) and encodes the result, and raises `UnicodeDecodeError` when a true
one has a byte from 128. Through `urlsplit`: non-ASCII `bytes` raise `UnicodeDecodeError`, and a
`str` URL with a non-empty `bytes` scheme raises the `TypeError`. Source: the docs ("Attempting
to mix str data with bytes or bytearray in a single function call will raise TypeError, while
attempting to pass in non-ASCII byte values will trigger UnicodeDecodeError"). -/
def CoerceSpec : Prop :=
  (∀ args : List Arg, (∃ a ∈ args, a.truthy = true ∧ a.isStr = true) →
    (∃ a ∈ args, a.truthy = true ∧ a.isStr = false) →
    coerceArgs args = .error (.typeError "Cannot mix str and non-str arguments")) ∧
  (∀ args : List Arg, (∃ a ∈ args, a.truthy = true) → (∀ a ∈ args, a.truthy = true → a.isStr = true) →
    coerceArgs args = .ok (args.map Arg.toV, false)) ∧
  (∀ args : List Arg, (∃ a ∈ args, a.truthy = true) → (∀ a ∈ args, a.truthy = true → a.isStr = false) →
    (∀ a ∈ args, ∀ b ba, a = .bytes b ba → ∀ c ∈ b, c < 128) →
    coerceArgs args = .ok (args.map decodedV, true)) ∧
  (∀ args : List Arg, (∃ a ∈ args, a.truthy = true) → (∀ a ∈ args, a.truthy = true → a.isStr = false) →
    (∃ a ∈ args, ∃ b ba, a = .bytes b ba ∧ ∃ c ∈ b, 128 ≤ c) →
    (coerceArgs args).raises "UnicodeDecodeError") ∧
  (∀ (nfkc : Str → Str) (ipk : Str → Option Bool) (x : Str) (frag mn : Bool), (∃ c ∈ x, 128 ≤ c) →
    (urlsplit nfkc ipk (.bytes x false) .none frag mn).raises "UnicodeDecodeError") ∧
  (∀ (nfkc : Str → Str) (ipk : Str → Option Bool) (u b : Str) (frag mn : Bool), u ≠ [] → b ≠ [] →
    urlsplit nfkc ipk (.str u) (.bytes b false) frag mn =
      .error (.typeError "Cannot mix str and non-str arguments"))

theorem coerce_decode (args : List Arg) (hex : ∃ a ∈ args, a.truthy = true)
    (hs : ∀ a ∈ args, a.truthy = true → a.isStr = false) :
    coerceArgs args = (decodeArgs args).bind (fun vs => .ok (vs, true)) := by
  have hm := mixLoop_same false args none (Or.inl rfl) hs
  rw [if_pos hex] at hm
  unfold coerceArgs
  simp only [bind, Except.bind, hm]
  rw [if_neg (by decide)]
  rfl

theorem coerceSpec_proven : CoerceSpec := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro args h1 h2
    unfold coerceArgs
    simp only [bind, Except.bind, mixLoop_mix args none (Or.inl h1) (Or.inl h2)]
  · intro args hex hs
    have hm := mixLoop_same true args none (Or.inl rfl) hs
    rw [if_pos hex] at hm
    unfold coerceArgs
    simp only [bind, Except.bind, hm]
    rw [if_pos (by decide)]
    rfl
  · intro args hex hs ha
    rw [coerce_decode args hex hs, decodeArgs_ok args hs ha]
    rfl
  · intro args hex hs hn
    rw [coerce_decode args hex hs]
    exact raises_bind _ _ _ (decodeArgs_raises args hs hn)
  · intro nfkc ipk x frag mn hx
    have hne : x ≠ [] := by rintro rfl; obtain ⟨c, hc, _⟩ := hx; simp at hc
    have ht : (Arg.bytes x false).truthy = true := by cases x <;> simp_all [Arg.truthy]
    unfold urlsplit
    simp only [lruHash, List.any_cons, List.any_nil, Bool.or_false, Bool.false_or, Bool.false_eq_true,
      ite_false]
    show ((coerceArgs [.bytes x false, .none]) >>= _).raises _
    apply raises_bind
    rw [coerce_decode _ ⟨_, List.mem_cons_self, ht⟩ (by
      intro a ha _
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl <;> rfl)]
    apply raises_bind
    exact decodeArgs_raises _ (by
      intro a ha _
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl <;> rfl) ⟨_, List.mem_cons_self, x, false, rfl, hx⟩
  · intro nfkc ipk u b frag mn hu hb
    have h1 : (Arg.str u).truthy = true := by cases u <;> simp_all [Arg.truthy]
    have h2 : (Arg.bytes b false).truthy = true := by cases b <;> simp_all [Arg.truthy]
    unfold urlsplit
    simp only [lruHash, List.any_cons, List.any_nil, Bool.or_false, Bool.false_or, Bool.false_eq_true,
      ite_false]
    show ((coerceArgs [.str u, .bytes b false]) >>= _) = _
    unfold coerceArgs
    simp only [bind, Except.bind]
    rw [mixLoop_mix _ none (Or.inl ⟨_, List.mem_cons_self, h1, rfl⟩)
      (Or.inl ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h2, rfl⟩)]

/-! ## `_ResultMixinStr.encode` and `_ResultMixinBytes.decode` -/

theorem mapM_encField_fits (e : Enc) (h : ErrHandler) (fs : List (Option Str))
    (hf : ∀ x, some x ∈ fs → ∀ c ∈ x, e.fits c) :
    fs.mapM (encField e h) = .ok (fs.map (·.map e.bytesOf)) := by
  induction fs with
  | nil => rfl
  | cons f r ih =>
    have ih' := ih (fun x hx => hf x (List.mem_cons_of_mem _ hx))
    have hfe : encField e h f = .ok (f.map e.bytesOf) := by
      cases f with
      | none => rfl
      | some s => simp [encField, encodeWith_fits e h s (hf s List.mem_cons_self), Except.map]
    simp [List.mapM_cons, hfe, ih', bind, Except.bind, pure, Except.pure]

theorem mapM_decField_fits (e : Enc) (h : ErrHandler) (fs : List (Option Str))
    (hf : ∀ x, some x ∈ fs → ∀ c ∈ x, e.fits c) :
    (fs.map (·.map e.bytesOf)).mapM (decField e h) = .ok fs := by
  induction fs with
  | nil => rfl
  | cons f r ih =>
    have ih' := ih (fun x hx => hf x (List.mem_cons_of_mem _ hx))
    have hfd : decField e h (f.map e.bytesOf) = .ok f := by
      cases f with
      | none => rfl
      | some s => simp [decField, decodeWith_fits e h s (hf s List.mem_cons_self), Except.map]
    simp [List.mapM_cons, hfd, ih', bind, Except.bind, pure, Except.pure]

theorem mapM_raises {α β : Type} (g : α → Py β) (cls : String) (fs : List α)
    (hok : ∀ x ∈ fs, (∃ y, g x = .ok y) ∨ (g x).raises cls) (hbad : ∃ x ∈ fs, (g x).raises cls) :
    (fs.mapM g).raises cls := by
  induction fs with
  | nil => obtain ⟨x, hx, _⟩ := hbad; simp at hx
  | cons a r ih =>
    rw [List.mapM_cons]
    rcases hok a List.mem_cons_self with ⟨y, hy⟩ | hr
    · by_cases hb : ∃ x ∈ r, (g x).raises cls
      · obtain ⟨e, he, hc⟩ := ih (fun x hx => hok x (List.mem_cons_of_mem _ hx)) hb
        exact ⟨e, by simp [hy, he, bind, Except.bind], hc⟩
      · exfalso
        obtain ⟨x, hx, hxr⟩ := hbad
        rcases List.mem_cons.1 hx with rfl | hx
        · obtain ⟨e, he, _⟩ := hxr; rw [hy] at he; cases he
        · exact hb ⟨x, hx, hxr⟩
    · exact raises_bind _ _ _ hr

theorem encodeWith_strict_cases (e : Enc) (s : Str) :
    (∃ y, encodeWith e .strict s = .ok y) ∨ (encodeWith e .strict s).raises "UnicodeEncodeError" := by
  by_cases hu : ∃ c ∈ s, e.unfit c = true
  · exact Or.inr (encodeWith_strict_raises e s hu)
  · left
    have hok : ∀ c ∈ s, e.unfit c = false := by
      intro c hc
      cases hh : e.unfit c
      · rfl
      · exact absurd ⟨c, hc, hh⟩ hu
    cases e with
    | utf8 => exact ⟨_, utf8Encode_plain s .strict (fun c hc => by simpa [Enc.unfit] using hok c hc)⟩
    | ascii =>
      exact ⟨_, ucs1Encode_below s 128 .strict noNames (fun c hc => by
        have := hok c hc; simp [Enc.unfit] at this; omega)⟩
    | latin1 =>
      exact ⟨_, ucs1Encode_below s 256 .strict noNames (fun c hc => by
        have := hok c hc; simp [Enc.unfit] at this; omega)⟩

/-- For every result and every codec of the model (UTF-8, ASCII, Latin-1): when the codec can
write every field, `encode(encoding, errors)` encodes each non-`None` field (any handler) and
copies `_keep_empty`, and `decode` with the same codec (any handler) gives the result back; with
`errors='strict'`, a field with a character the codec cannot write raises `UnicodeEncodeError`;
and `decode('ascii')` (the default) of a field with a byte from 128 raises `UnicodeDecodeError`.
Source: the docs ("encode() ... decode() ... the encoding and errors arguments ... as for
str.encode() and bytes.decode()"), and the round trip of `encode` and `decode`. -/
def ResCodecSpec : Prop :=
  (∀ (r : Res) (e : Enc) (h h' : ErrHandler), (∀ x, some x ∈ r.fields → ∀ c ∈ x, e.fits c) →
    resEncode r e h = .ok { fields := r.fields.map (·.map e.bytesOf), isBytes := true, keep := r.keep } ∧
    resDecode { fields := r.fields.map (·.map e.bytesOf), isBytes := true, keep := r.keep } e h' =
      .ok { fields := r.fields, isBytes := false, keep := r.keep }) ∧
  (∀ (r : Res) (e : Enc), (∃ x, some x ∈ r.fields ∧ ∃ c ∈ x, e.unfit c = true) →
    (resEncode r e .strict).raises "UnicodeEncodeError") ∧
  (∀ r : Res, (∃ x, some x ∈ r.fields ∧ ∃ c ∈ x, 128 ≤ c) → (resDecode r .ascii .strict).raises "UnicodeDecodeError")

theorem resCodecSpec_proven : ResCodecSpec := by
  refine ⟨?_, ?_, ?_⟩
  · intro r e h h' hf
    constructor
    · simp [resEncode, mapM_encField_fits e h r.fields hf, bind, Except.bind, pure, Except.pure]
    · simp [resDecode, mapM_decField_fits e h' r.fields hf, bind, Except.bind, pure, Except.pure]
  · intro r e hbad
    unfold resEncode
    apply raises_bind
    apply mapM_raises
    · intro x _
      cases x with
      | none => exact Or.inl ⟨_, rfl⟩
      | some s =>
        rcases encodeWith_strict_cases e s with ⟨y, hy⟩ | ⟨err, he, hc⟩
        · exact Or.inl ⟨some y, by simp [encField, hy, Except.map]⟩
        · exact Or.inr ⟨err, by simp [encField, he, Except.map], hc⟩
    · obtain ⟨x, hx, hu⟩ := hbad
      obtain ⟨err, he, hc⟩ := encodeWith_strict_raises e x hu
      exact ⟨some x, hx, err, by simp [encField, he, Except.map], hc⟩
  · intro r hbad
    unfold resDecode
    apply raises_bind
    apply mapM_raises
    · intro x _
      cases x with
      | none => exact Or.inl ⟨_, rfl⟩
      | some s =>
        by_cases hs : ∃ c ∈ s, 128 ≤ c
        · obtain ⟨err, he, hc⟩ := asciiDecode_raises s hs
          exact Or.inr ⟨err, by simp [decField, decodeWith, he, Except.map], hc⟩
        · have hasc : ∀ c ∈ s, c < 128 := by
            intro c hc; exact Nat.lt_of_not_le (fun h => hs ⟨c, hc, h⟩)
          exact Or.inl ⟨some s, by simp [decField, decodeWith, asciiDecode_ascii s .strict hasc, Except.map]⟩
    · obtain ⟨x, hx, hn⟩ := hbad
      obtain ⟨err, he, hc⟩ := asciiDecode_raises x hn
      exact ⟨some x, hx, err, by simp [decField, decodeWith, he, Except.map], hc⟩

end PyLean.TextLibs.Url
