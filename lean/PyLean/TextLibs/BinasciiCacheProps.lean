import PyLean.TextLibs.BinasciiCache
import PyLean.TextLibs.BinasciiB32b

/-!
What `get_reverse_table` and its cache do: the length refusal first, a raising `__hash__` passed on,
a corrupt entry refused; with only exact `bytes` keys stored, every decoder gets the table of its
alphabet's value, the one the static tables and `revT` describe; and a `bytes` subclass whose
`__hash__` and `__eq__` match a stored alphabet gets that alphabet's table.
-/

namespace PyLean.TextLibs.Binascii

open PyLean

set_option linter.unusedSimpArgs false

/-! ### The table built on a miss -/

theorem revT_snoc (l : List Nat) (x : Nat) (ch : Nat) :
    revT (l ++ [x]) none ch = if x = ch then l.length else revT l none ch := by
  simp only [revT, List.zipIdx_append, List.reverse_append, List.zipIdx_singleton, List.reverse_singleton,
    List.singleton_append, List.find?_cons]
  by_cases h : x = ch
  · simp [h]
  · have : (x == ch) = false := by simpa using h
    simp [this, h]

theorem getD_set_ne (l : List Nat) (j k ch : Nat) (h : j ≠ ch) : (l.set j k).getD ch 255 = l.getD ch 255 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set_ne h]

theorem getD_set_eq (l : List Nat) (j k : Nat) (h : j < l.length) : (l.set j k).getD j 255 = k := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_self h]
  rfl

theorem fold_rev (a : List Nat) (ha : ∀ x ∈ a, x < 256) (R : List Nat) (hR : R.length = 256)
    (hR2 : ∀ ch, R.getD ch 255 = 255) : ∀ k, k ≤ a.length →
    ((List.range k).foldl (fun out i => out.set (a.getD i 0) i) R).length = 256 ∧
    ∀ ch, ((List.range k).foldl (fun out i => out.set (a.getD i 0) i) R).getD ch 255 = revT (a.take k) none ch := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨hR, fun ch => ?_⟩
    rw [List.range_zero, List.foldl_nil, hR2]
    simp [revT]
  | succ k ih =>
    intro hk
    obtain ⟨h1, h2⟩ := ih (by omega)
    have hx : a.getD k 0 < 256 := ha _ (getD_mem a k (by omega))
    have ht : a.take (k + 1) = a.take k ++ [a.getD k 0] := by
      rw [List.take_add_one, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      simp
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨by rw [List.length_set, h1], fun ch => ?_⟩
    rw [ht, revT_snoc]
    have hl : (List.take k a).length = k := by simp; omega
    rw [hl]
    by_cases he : a.getD k 0 = ch
    · subst he
      rw [if_pos rfl, getD_set_eq _ _ _ (by rw [h1]; exact hx)]
    · rw [if_neg he, getD_set_ne _ _ _ _ he, h2]

theorem replicate_facts : (List.replicate 256 255).length = 256 ∧ ∀ ch, (List.replicate 256 255).getD ch 255 = 255 := by
  refine ⟨List.length_replicate, fun ch => ?_⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

/-- The built table is `revT` of the alphabet, entry by entry, and has 256 entries. -/
theorem buildRev_spec (a : List Nat) (size : Nat) (pad : Option Nat) (hl : a.length = size)
    (ha : ∀ x ∈ a, x < 256) (hp : ∀ p, pad = some p → p < 256) :
    (buildRev a size pad).length = 256 ∧ ∀ ch, ch < 256 → (buildRev a size pad).getD ch 255 = revT a pad ch := by
  subst hl
  unfold buildRev
  generalize hR : List.replicate 256 255 = R
  have ⟨hR1, hR2⟩ := replicate_facts
  rw [hR] at hR1 hR2
  obtain ⟨h1, h2⟩ := fold_rev a ha R hR1 hR2 a.length (Nat.le_refl _)
  rw [List.take_length] at h2
  generalize (List.range a.length).foldl (fun out i => out.set (a.getD i 0) i) R = F at h1 h2
  cases pad with
  | none =>
    exact ⟨h1, fun ch _ => h2 ch⟩
  | some p =>
    have hp' := hp p rfl
    refine ⟨by rw [List.length_set, h1], fun ch _ => ?_⟩
    by_cases he : p = ch
    · subst he
      rw [getD_set_eq _ _ _ (by rw [h1]; exact hp')]
      simp [revT]
    · rw [getD_set_ne _ _ _ _ he, h2]
      have : (some p == some ch) = false := by simpa using he
      simp [revT, this]

/-! ### A cache with only exact `bytes` keys -/

/-- The pad character each decoder passes, by alphabet size. -/
def padFor (size : Nat) : Option Nat := if size = 85 then none else some 61

/-- Every entry was stored by a decoder from an exact `bytes` alphabet, under its own hash, with the
table built from it. -/
def Coherent (c : RCache) : Prop :=
  ∀ e ∈ c, ∃ v, e.1 = .bytes v ∧ e.2.1 = .ofBytes v ∧ e.2.2 = .table (buildRev v v.length (padFor v.length)) ∧
    ∀ x ∈ v, x < 256

theorem lookup_coherent (c : RCache) (hc : Coherent c) (v : List Nat) :
    rcLookup c (.bytes v) (.ofBytes v) = .ok none ∨
      rcLookup c (.bytes v) (.ofBytes v) = .ok (some (.table (buildRev v v.length (padFor v.length)))) := by
  induction c with
  | nil => left; rfl
  | cons e r ih =>
    have hr : Coherent r := fun x hx => hc x (by simp [hx])
    obtain ⟨w, h1, h2, h3, _⟩ := hc e (by simp)
    obtain ⟨k, h, val⟩ := e
    simp only at h1 h2 h3
    subst h1 h2 h3
    simp only [rcLookup, keyEqC]
    by_cases hw : w = v
    · subst hw
      right
      simp
    · have : (HTok.ofBytes w == HTok.ofBytes v) = false := by simpa using hw
      rw [if_neg (by simpa using this)]
      exact ih hr

/-- What `get_reverse_table` does. The length is checked before anything is hashed, and that refusal
leaves the cache as it was; a raising `__hash__` passes through; a stored value that is not a 256-byte
`bytes` is refused with "Broken binascii cache". With only exact `bytes` keys stored, an exact `bytes`
alphabet of the right length gets the table of its own value, whether it was stored or is built now:
256 entries, each the last index of that byte in the alphabet, the pad character on top; and the cache
keeps only such keys. -/
def ReverseTableLaw : Prop :=
  (∀ (c : RCache) (a : AObj) (size : Nat) (pad : Option Nat), a.value.length ≠ size →
    getReverseTable c a size pad = (.error (.valueError s!"alphabet must have length {size}"), c)) ∧
  (∀ (c : RCache) (oid : Nat) (v : List Nat) (e : PyExc) (eqv : List Nat → Py Bool) (size : Nat) (pad : Option Nat),
    v.length = size → getReverseTable c (.sub oid v (.error e) eqv) size pad = (.error e, c)) ∧
  (∀ (c : RCache) (a : AObj) (size : Nat) (pad : Option Nat) (h : HTok), a.value.length = size → a.hash = .ok h →
    rcLookup c a h = .ok (some .other) → getReverseTable c a size pad = (.error brokenCache, c)) ∧
  (∀ (c : RCache) (v : List Nat), Coherent c → (v.length = 64 ∨ v.length = 32 ∨ v.length = 85) →
    (∀ x ∈ v, x < 256) →
    ∃ t c', getReverseTable c (.bytes v) v.length (padFor v.length) = (.ok t, c') ∧ Coherent c' ∧
      t.length = 256 ∧ ∀ ch, ch < 256 → t.getD ch 255 = revT v (padFor v.length) ch)

theorem reverseTableLaw_proven : ReverseTableLaw := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c a size pad h
    simp [getReverseTable, h]
  · intro c oid v e eqv size pad h
    simp [getReverseTable, AObj.value, AObj.hash, h]
  · intro c a size pad h hl hh hlk
    simp [getReverseTable, hl, hh, hlk]
  · intro c v hc hs hv
    have hp : ∀ p, padFor v.length = some p → p < 256 := by
      intro p hp
      simp only [padFor] at hp
      split at hp
      · cases hp
      · cases hp; decide
    obtain ⟨hlen, hspec⟩ := buildRev_spec v v.length (padFor v.length) rfl hv hp
    rcases lookup_coherent c hc v with h | h
    · refine ⟨buildRev v v.length (padFor v.length), c ++ [(.bytes v, .ofBytes v, .table (buildRev v v.length (padFor v.length)))],
        ?_, ?_, hlen, hspec⟩
      · simp [getReverseTable, AObj.value, AObj.hash, h]
      · intro e he
        simp only [List.mem_append, List.mem_singleton] at he
        rcases he with he | he
        · exact hc e he
        · subst he; exact ⟨v, rfl, rfl, rfl, hv⟩
    · refine ⟨buildRev v v.length (padFor v.length), c, ?_, hc, hlen, hspec⟩
      simp [getReverseTable, AObj.value, AObj.hash, h, hlen]

/-! ### The decoders through the cache -/

theorem table_fun (v : List Nat) (pad : Option Nat) (t : List Nat) (hv : ∀ x ∈ v, x < 256)
    (hp : ∀ p, pad = some p → p < 256) (hl : t.length = 256)
    (hs : ∀ ch, ch < 256 → t.getD ch 255 = revT v pad ch) : (fun ch => t.getD ch 255) = revT v pad := by
  funext ch
  by_cases h : ch < 256
  · exact hs ch h
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rw [revT_large v pad ch]
    · rfl
    · intro e; have := hp ch e; omega
    · intro x hx e; have := hv x hx; omega

theorem decTableC_coherent (c : RCache) (hc : Coherent c) (v : List Nat) (hv : ∀ x ∈ v, x < 256) (dflt : Nat → Nat)
    (size : Nat) (hs : size = 64 ∨ size = 32 ∨ size = 85) :
    (decTableC c (some (.bytes v)) dflt size (padFor size)).1 = decTable (some v) dflt size (padFor size) ∧
      Coherent (decTableC c (some (.bytes v)) dflt size (padFor size)).2 := by
  by_cases hl : v.length = size
  · subst hl
    obtain ⟨t, c', h1, h2, h3, h4⟩ := reverseTableLaw_proven.2.2.2 c v hc hs hv
    have hp : ∀ p, padFor v.length = some p → p < 256 := by
      intro p hp
      simp only [padFor] at hp
      split at hp
      · cases hp
      · cases hp; decide
    simp only [decTableC, h1, decTable, ne_eq, not_true_eq_false, if_false]
    exact ⟨by rw [table_fun v _ t hv hp h3 h4], h2⟩
  · have h1 := reverseTableLaw_proven.1 c (.bytes v) size (padFor size) (by simpa [AObj.value] using hl)
    simp only [decTableC, h1, decTable, hl, ne_eq, not_false_eq_true, if_true]
    exact ⟨by first | trivial | rfl, hc⟩

/-- With only exact `bytes` alphabets stored, the decoders through the cache are the decoders with the
table of their alphabet's value (`a2bB64`, `a2bB32`, `a2bB85`, about which the other statements are),
and the cache keeps only exact `bytes` keys. So everything proved of those holds of the real functions
until a `bytes` subclass alphabet is passed. -/
def DecodersCoherent : Prop :=
  ∀ (c : RCache) (v : List Nat), Coherent c → (∀ x ∈ v, x < 256) →
    (∀ d strict p ig k, (a2bB64S c d strict p (.obj (.bytes v)) ig k).1 = a2bB64 d strict p (.bytes v) ig k ∧
        Coherent (a2bB64S c d strict p (.obj (.bytes v)) ig k).2) ∧
    (∀ d p ig k, (a2bB32S c d p (.obj (.bytes v)) ig k).1 = a2bB32 d p (.bytes v) ig k ∧
        Coherent (a2bB32S c d p (.obj (.bytes v)) ig k).2) ∧
    (∀ d ig k, (a2bB85S c d (.obj (.bytes v)) ig k).1 = a2bB85 d (.bytes v) ig k ∧
        Coherent (a2bB85S c d (.obj (.bytes v)) ig k).2)

theorem decodersCoherent_proven : DecodersCoherent := by
  intro c v hc hv
  have t64 := decTableC_coherent c hc v hv (revT b64Alpha (some 61)) 64 (.inl rfl)
  have t32 := decTableC_coherent c hc v hv (revT b32Alpha none) 32 (.inr (.inl rfl))
  have t85 := decTableC_coherent c hc v hv (revT b85Alpha none) 85 (.inr (.inr rfl))
  simp only [padFor] at t64 t32 t85
  simp only [show (64 : Nat) = 85 ↔ False by decide, show (32 : Nat) = 85 ↔ False by decide, if_false,
    if_true] at t64 t32 t85
  refine ⟨fun d strict p ig k => ?_, fun d p ig k => ?_, fun d ig k => ?_⟩
  · unfold a2bB64S a2bB64
    cases asciiBuffer d with
    | error e => exact ⟨rfl, hc⟩
    | ok s =>
      cases hb : bufOpt ig with
      | error e => simp [alphaDecC, alphaDec, hb, bind, Except.bind]; exact hc
      | ok g =>
        simp only [alphaDecC, alphaDec, hb, bind, Except.bind]
        cases h : decTableC c (some (.bytes v)) (revT b64Alpha (some 61)) 64 (some 61) with
        | mk r c' =>
          rw [h] at t64
          simp only at t64
          obtain ⟨e1, e2⟩ := t64
          cases r with
          | error e => simp only [← e1]; exact ⟨by first | trivial | rfl, e2⟩
          | ok t => simp only [← e1]; exact ⟨by first | trivial | rfl, e2⟩
  · unfold a2bB32S a2bB32
    cases asciiBuffer d with
    | error e => exact ⟨rfl, hc⟩
    | ok s =>
      cases hb : bufData ig with
      | error e => simp [alphaDecC, alphaDec, hb, bind, Except.bind]; exact hc
      | ok g =>
        simp only [alphaDecC, alphaDec, hb, bind, Except.bind]
        cases h : decTableC c (some (.bytes v)) (revT b32Alpha none) 32 (some 61) with
        | mk r c' =>
          rw [h] at t32
          simp only at t32
          obtain ⟨e1, e2⟩ := t32
          cases r with
          | error e => simp only [← e1]; exact ⟨by first | trivial | rfl, e2⟩
          | ok t => simp only [← e1]; exact ⟨by first | trivial | rfl, e2⟩
  · unfold a2bB85S a2bB85
    cases asciiBuffer d with
    | error e => exact ⟨rfl, hc⟩
    | ok s =>
      cases hb : bufData ig with
      | error e => simp [alphaDecC, alphaDec, hb, bind, Except.bind]; exact hc
      | ok g =>
        simp only [alphaDecC, alphaDec, hb, bind, Except.bind]
        cases h : decTableC c (some (.bytes v)) (revT b85Alpha none) 85 none with
        | mk r c' =>
          rw [h] at t85
          simp only at t85
          obtain ⟨e1, e2⟩ := t85
          cases r with
          | error e => simp only [← e1]; exact ⟨by first | trivial | rfl, e2⟩
          | ok t => simp only [← e1]; exact ⟨by first | trivial | rfl, e2⟩

/-! ### A subclass that matches a stored alphabet -/

/-- `a2b_base64` decodes by the bytes of its alphabet, whatever was decoded before: with any one earlier
call, `a2b_base64(s, alphabet=a, strict_mode=True)` is what it is with the plain `bytes` value of `a`.
False: the cache is keyed by the object, so a `bytes` subclass whose `__hash__` is that of a stored
alphabet and whose `__eq__` says yes is given the stored alphabet's table. After
`a2b_base64(b'AAAA', alphabet=URLSAFE_BASE64_ALPHABET)`, an `Alpha(BASE64_ALPHABET)` with
`__hash__ = hash(URLSAFE_BASE64_ALPHABET)` and `__eq__` always true decodes `b'+/8='` (which
`b2a_base64(b'\xfb\xff', alphabet=a)` writes) as URL-safe data, and the strict mode refuses it. -/
def AlphabetValueOnly : Prop :=
  ∀ (s0 : List Nat) (a0 : AObj) (s : List Nat) (a : AObj),
    (a2bB64S (a2bB64S [] (.bytes s0) none true (.obj a0) none false).2 (.bytes s) (some true) true (.obj a) none false).1 =
      a2bB64 (.bytes s) (some true) true (.bytes a.value) none false

/-- `class Alpha(bytes)` with `__hash__` returning `hash(URLSAFE_BASE64_ALPHABET)` and `__eq__` always
true, holding `BASE64_ALPHABET`. -/
def alphaSub : AObj := .sub 0 b64Alpha (.ok (.ofBytes urlAlpha)) (fun _ => .ok true)

theorem alphabetValueOnly_refuted : ¬AlphabetValueOnly := by
  intro h
  have := h [65, 65, 65, 65] (.bytes urlAlpha) [43, 47, 56, 61] alphaSub
  revert this
  decide +kernel

end PyLean.TextLibs.Binascii
