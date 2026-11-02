import PyLean.TextLibs.UrlRoundTrip

/-!
`parse_qsl` reads back what `urlencode` writes, for `str` pairs and for `bytes` pairs.
-/

namespace PyLean.TextLibs.Url

open PyLean
open PyLean.UnicodeObj (ErrHandler utf8EncodeChar isSurrogate maxUnicode)

set_option linter.unusedSimpArgs false

/-- What `quote_plus(k)` writes for a `str` (default `safe=''`, UTF-8). -/
def qpS (k : Str) : Str :=
  if k.contains 32 then spToPlus ((Enc.utf8.bytesOf k).flatMap (quoteByte [32]))
  else (Enc.utf8.bytesOf k).flatMap (quoteByte [])

/-- What `quote_plus(b)` writes for a `bytes` (default `safe=''`). -/
def qpB (b : Str) : Str :=
  if b.contains 32 then spToPlus (b.flatMap (quoteByte [32])) else b.flatMap (quoteByte [])

def Scalar (s : Str) : Prop := ∀ c ∈ s, c ≤ maxUnicode ∧ isSurrogate c = false

theorem quotePlus_str_default (k : Str) (hk : Scalar k) :
    quotePlus (.str k) (.str []) none none = .ok (qpS k) := by
  unfold quotePlus qpS
  by_cases hsp : k.contains 32 = true
  · simp only [hsp, Bool.not_true, Bool.false_eq_true, ite_false, ite_true, bind, Except.bind, addSpace,
      List.nil_append]
    rw [quote_str_eq none k (.str [32]) [32] none hk (by simp [safeBytes])]
    rfl
  · simp only [Bool.not_eq_true] at hsp
    simp only [hsp, Bool.not_false, ite_true, Bool.false_eq_true, ite_false]
    exact quote_str_eq none k (.str []) [] none hk (by simp [safeBytes])

theorem quotePlus_bytes_default (b : Str) :
    quotePlus (.bytes b false) (.str []) none none = .ok (qpB b) := by
  unfold quotePlus qpB
  by_cases hsp : b.contains 32 = true
  · simp only [hsp, Bool.not_true, Bool.false_eq_true, ite_false, ite_true, bind, Except.bind, addSpace,
      List.nil_append]
    simp only [quote, Option.isSome_none, Bool.false_eq_true, ite_false]
    rw [quoteFromBytes_eq b false (.str [32]) [32] (by simp [safeBytes])]
    rfl
  · simp only [Bool.not_eq_true] at hsp
    simp only [hsp, Bool.not_false, ite_true, Bool.false_eq_true, ite_false]
    simp only [quote, Option.isSome_none, Bool.false_eq_true, ite_false]
    exact quoteFromBytes_eq b false (.str []) [] (by simp [safeBytes])

theorem unquotePlus_getD (q : Str) (enc : Option Enc) (h : Option ErrHandler) :
    unquotePlus (.str q) enc h = unquotePlus (.str q) (some (enc.getD .utf8)) (some (h.getD .replace)) := by
  simp [unquotePlus, unquote]

theorem unquotePlus_qpS (k : Str) (hk : Scalar k) (h : Option ErrHandler) :
    unquotePlus (.str (qpS k)) (some .utf8) h = .ok k := by
  obtain ⟨q, hq, hu⟩ := (quotePlusRoundTrip_proven none k (.str []) [] none h hk (by simp [safeBytes])).2
    (by simp) (by simp)
  rw [quotePlus_str_default k hk] at hq
  cases hq
  rw [unquotePlus_getD] at hu ⊢
  simpa using hu

/-- No `&` or `=` survives quoting. -/
theorem hexU_ne_eq (x : Nat) : hexU x ≠ 61 := by
  simp only [hexU]; split <;> omega

theorem quoteByte_no (safe : Str) (b d : Nat) (hd : alwaysSafe d = false) (hds : d ∉ safe)
    (hd37 : d ≠ 37) (hhex : ∀ x, hexU x ≠ d) : d ∉ quoteByte safe b := by
  unfold quoteByte
  split
  · next hk =>
    simp
    intro e; subst e
    simp [hd] at hk; exact hds hk
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨hd37, fun e => hhex _ e.symm, fun e => hhex _ e.symm⟩

theorem no_in_flatMap (safe x : Str) (d : Nat) (hd : alwaysSafe d = false) (hds : d ∉ safe)
    (hd37 : d ≠ 37) (hhex : ∀ y, hexU y ≠ d) : d ∉ x.flatMap (quoteByte safe) := by
  simp only [List.mem_flatMap, not_exists, not_and]
  intro b _
  exact quoteByte_no safe b d hd hds hd37 hhex

theorem no_in_spToPlus (q : Str) (d : Nat) (hd : d ∉ q) (h32 : d ≠ 43) : d ∉ spToPlus q := by
  simp only [spToPlus, List.mem_map, not_exists, not_and]
  intro c hc e
  by_cases h : c = 32
  · subst h; simp at e; exact h32 e.symm
  · simp [h] at e; subst e; exact hd hc

theorem hexU_amp (x : Nat) : hexU x ≠ 38 := by simp only [hexU]; split <;> omega

theorem qpS_no (k : Str) (d : Nat) (hd : d = 38 ∨ d = 61) : d ∉ qpS k := by
  have h1 : alwaysSafe d = false := by rcases hd with rfl | rfl <;> decide
  have h2 : d ≠ 37 := by omega
  have h3 : ∀ y, hexU y ≠ d := by rcases hd with rfl | rfl; exact hexU_amp; exact hexU_ne_eq
  unfold qpS
  split
  · exact no_in_spToPlus _ d (no_in_flatMap _ _ d h1 (by simp; omega) h2 h3) (by omega)
  · exact no_in_flatMap _ _ d h1 (by simp) h2 h3

theorem qpB_no (k : Str) (d : Nat) (hd : d = 38 ∨ d = 61) : d ∉ qpB k := by
  have h1 : alwaysSafe d = false := by rcases hd with rfl | rfl <;> decide
  have h2 : d ≠ 37 := by omega
  have h3 : ∀ y, hexU y ≠ d := by rcases hd with rfl | rfl; exact hexU_amp; exact hexU_ne_eq
  unfold qpB
  split
  · exact no_in_spToPlus _ d (no_in_flatMap _ _ d h1 (by simp; omega) h2 h3) (by omega)
  · exact no_in_flatMap _ _ d h1 (by simp) h2 h3

theorem scan_qpB (b : Str) (hb : ∀ x ∈ b, x < 256) :
    scan ((qpB b).map (fun c => if c == 43 then 32 else c)) = b := by
  unfold qpB
  split
  · simp only [spToPlus]
    rw [map_space_plus _ (plus_not_quoted _ _ (by simp))]
    exact scan_quote [32] (by simp) b hb
  · rw [map_plus_id _ (plus_not_quoted _ _ (by simp))]
    exact scan_quote [] (by simp) b hb

/-- `part c (x ++ c :: y)` when `x` has no `c`. -/
theorem part_prefix (c : Nat) (x y : Str) (h : c ∉ x) : part c (x ++ c :: y) = (x, some y) := by
  induction x with
  | nil => simp [part]
  | cons a r ih =>
    have ha : a ≠ c := fun e => h (e ▸ List.mem_cons_self)
    simp only [List.cons_append, part, beq_iff_eq, ha, if_false]
    rw [ih (fun m => h (List.mem_cons_of_mem _ m))]

/-- The loop of `parse_qsl` over `k=v` fields whose `k` has no `=`. -/
theorem qslLoop_fields (o : QslOpts) (ho : o.keepBlank = true) (unq : Str → Py Str)
    (l : List (Str × Str)) (ek ev : Str → Str) (hk : ∀ p ∈ l, 61 ∉ ek p.1)
    (hu1 : ∀ p ∈ l, unq (ek p.1) = .ok p.1) (hu2 : ∀ p ∈ l, unq (ev p.2) = .ok p.2) :
    qslLoop o unq (l.map (fun p => ek p.1 ++ [61] ++ ev p.2)) = .ok l := by
  induction l with
  | nil => rfl
  | cons p r ih =>
    have ih' := ih (fun q hq => hk q (List.mem_cons_of_mem _ hq))
      (fun q hq => hu1 q (List.mem_cons_of_mem _ hq)) (fun q hq => hu2 q (List.mem_cons_of_mem _ hq))
    have hne : (ek p.1 ++ [61] ++ ev p.2).isEmpty = false := by simp
    have hpart : part 61 (ek p.1 ++ [61] ++ ev p.2) = (ek p.1, some (ev p.2)) := by
      rw [List.append_assoc, List.singleton_append, part_prefix 61 _ _ (hk p List.mem_cons_self)]
    simp only [List.map_cons, qslLoop, hne, hpart, ho, Bool.not_false, Bool.true_or, Bool.or_true, ite_true,
      Option.isNone_some, Bool.false_and, Bool.false_eq_true, ite_false, Option.getD_some,
      hu1 p List.mem_cons_self, hu2 p List.mem_cons_self, bind, Except.bind, pure, Except.pure, ih',
      List.singleton_append]

theorem encodeLoop_str (pairs : List (Str × Str)) (hps : ∀ p ∈ pairs, Scalar p.1 ∧ Scalar p.2) :
    encodeLoop {} (pairs.map (fun p => [QV.str p.1, QV.str p.2])) =
      .ok (pairs.map (fun p => qpS p.1 ++ [61] ++ qpS p.2)) := by
  induction pairs with
  | nil => rfl
  | cons p r ih =>
    have ih' := ih (fun q hq => hps q (List.mem_cons_of_mem _ hq))
    have h1 := quotePlus_str_default _ (hps p List.mem_cons_self).1
    have h2 := quotePlus_str_default _ (hps p List.mem_cons_self).2
    simp only [List.map_cons, encodeLoop, quoteQV, callVia, QV.text, bind, Except.bind, pure, Except.pure]
    simp only [show ({} : EncOpts).via = .plus from rfl, show ({} : EncOpts).safe = .str [] from rfl,
      show ({} : EncOpts).encoding = none from rfl, show ({} : EncOpts).errors = none from rfl,
      show ({} : EncOpts).doseq = false from rfl, ite_self, h1, h2, Bool.not_false, ite_true, ih']
    rfl

theorem encodeLoop_bytes (pairs : List (Str × Str)) :
    encodeLoop {} (pairs.map (fun p => [QV.bytes p.1, QV.bytes p.2])) =
      .ok (pairs.map (fun p => qpB p.1 ++ [61] ++ qpB p.2)) := by
  induction pairs with
  | nil => rfl
  | cons p r ih =>
    simp only [List.map_cons, encodeLoop, quoteQV, callVia, bind, Except.bind, pure, Except.pure]
    simp only [show ({} : EncOpts).via = .plus from rfl, show ({} : EncOpts).safe = .str [] from rfl,
      show ({} : EncOpts).doseq = false from rfl, quotePlus_bytes_default, Bool.not_false, ite_true, ite_false,
      Bool.false_eq_true, ih]
    rfl

theorem joinWith_nil_iff (l : List Str) (hl : ∀ x ∈ l, x ≠ []) : joinWith [38] l = [] ↔ l = [] := by
  constructor
  · intro h
    match l with
    | [] => rfl
    | [x] => simp [joinWith] at h; exact absurd h (hl x (by simp))
    | x :: y :: t => simp [joinWith] at h
  · intro h; subst h; rfl

/-- `parse_qsl(urlencode(pairs), keep_blank_values=True) == pairs` for every list of `str` pairs
without surrogates, given as a sequence of 2-tuples or as a mapping; and for every list of `bytes`
pairs, read back from the ASCII `bytes` of `urlencode`'s result. All other arguments are the
defaults. Source: (a), a round trip; the docs of `urlencode` ("convert such lists of pairs into
query strings") and `parse_qsl`. -/
def QslRoundTrip : Prop :=
  (∀ pairs : List (Str × Str), (∀ p ∈ pairs, Scalar p.1 ∧ Scalar p.2) →
    (∃ q, urlencode (.seq (pairs.map (fun p => (true, [QV.str p.1, QV.str p.2])))) {} = .ok q ∧
      parseQsl (.str q) { keepBlank := true } = .ok pairs) ∧
    (∃ q, urlencode (.mapping (pairs.map (fun p => (QV.str p.1, QV.str p.2)))) {} = .ok q ∧
      parseQsl (.str q) { keepBlank := true } = .ok pairs)) ∧
  (∀ pairs : List (Str × Str), (∀ p ∈ pairs, (∀ b ∈ p.1, b < 256) ∧ (∀ b ∈ p.2, b < 256)) →
    ∃ q, urlencode (.seq (pairs.map (fun p => (true, [QV.bytes p.1, QV.bytes p.2])))) {} = .ok q ∧
      parseQsl (.bytes q false) { keepBlank := true } = .ok pairs)

theorem split_fields (pairs : List (Str × Str)) (ek ev : Str → Str) (hp : pairs ≠ [])
    (hk : ∀ p ∈ pairs, 38 ∉ ek p.1 ∧ 38 ∉ ev p.2) :
    splitOn [38] (joinWith [38] (pairs.map (fun p => ek p.1 ++ [61] ++ ev p.2))) =
      pairs.map (fun p => ek p.1 ++ [61] ++ ev p.2) := by
  apply splitOn_joinWith
  · simp; exact hp
  · intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨p, hp', rfl⟩ := hx
    simp only [List.mem_append, List.mem_singleton]
    intro h
    rcases h with (h | h) | h
    · exact (hk p hp').1 h
    · exact absurd h (by decide)
    · exact (hk p hp').2 h

theorem joined_ne (pairs : List (Str × Str)) (ek ev : Str → Str) (hp : pairs ≠ []) :
    (joinWith [38] (pairs.map (fun p => ek p.1 ++ [61] ++ ev p.2))).isEmpty = false := by
  rw [List.isEmpty_eq_false_iff]
  intro h
  rw [joinWith_nil_iff _ (fun x hx => by
    simp only [List.mem_map] at hx; obtain ⟨p, _, rfl⟩ := hx; simp)] at h
  exact hp (List.map_eq_nil_iff.1 h)

theorem qslRoundTrip_proven : QslRoundTrip := by
  have seqMap : ∀ (pairs : List (Str × Str)) (f : Str × Str → List QV) (l : List Str),
      encodeLoop {} (pairs.map f) = .ok l →
      urlencode (.seq (pairs.map (fun p => (true, f p)))) {} = .ok (joinWith [38] l) := by
    intro pairs f l hl
    cases pairs with
    | nil => simp [encodeLoop] at hl; subst hl; rfl
    | cons p r =>
      have e : f p :: List.map (fun x => x.2) (List.map (fun p => (true, f p)) r) = (p :: r).map f := by
        simp [Function.comp_def]
      simp only [urlencode, List.map_cons, bind, Except.bind, pure, Except.pure]
      rw [e, hl]
  have mapMap : ∀ (pairs : List (Str × Str)) (f : Str × Str → QV × QV) (l : List Str),
      encodeLoop {} (pairs.map (fun p => [(f p).1, (f p).2])) = .ok l →
      urlencode (.mapping (pairs.map f)) {} = .ok (joinWith [38] l) := by
    intro pairs f l hl
    have e : (List.map (fun p => [p.1, p.2]) (List.map f pairs)) = pairs.map (fun p => [(f p).1, (f p).2]) := by
      simp [Function.comp_def]
    simp only [urlencode, bind, Except.bind, pure, Except.pure]
    rw [e, hl]
  have strTail : ∀ (pairs : List (Str × Str)), (∀ p ∈ pairs, Scalar p.1 ∧ Scalar p.2) →
      parseQsl (.str (joinWith [38] (pairs.map (fun p => qpS p.1 ++ [61] ++ qpS p.2)))) { keepBlank := true } =
        .ok pairs := by
    intro pairs hps
    by_cases hp : pairs = []
    · subst hp; rfl
    · have hloop := qslLoop_fields { keepBlank := true } rfl
        (fun s => unquotePlus (.str s) (some .utf8) (some .replace)) pairs qpS qpS
        (fun p _ => qpS_no _ _ (Or.inr rfl))
        (fun p hp => unquotePlus_qpS _ (hps p hp).1 _) (fun p hp => unquotePlus_qpS _ (hps p hp).2 _)
      simp only [parseQsl, bind, Except.bind, pure, Except.pure, joined_ne pairs qpS qpS hp,
        Bool.false_eq_true, ite_false,
        split_fields pairs qpS qpS hp (fun p _ => ⟨qpS_no _ _ (Or.inl rfl), qpS_no _ _ (Or.inl rfl)⟩)]
      exact hloop
  refine ⟨fun pairs hps => ⟨?_, ?_⟩, fun pairs hps => ?_⟩
  · refine ⟨joinWith [38] (pairs.map (fun p => qpS p.1 ++ [61] ++ qpS p.2)), ?_, strTail pairs hps⟩
    exact seqMap pairs (fun p => [QV.str p.1, QV.str p.2]) _ (encodeLoop_str pairs hps)
  · refine ⟨joinWith [38] (pairs.map (fun p => qpS p.1 ++ [61] ++ qpS p.2)), ?_, strTail pairs hps⟩
    exact mapMap pairs (fun p => (QV.str p.1, QV.str p.2)) _ (encodeLoop_str pairs hps)
  · refine ⟨joinWith [38] (pairs.map (fun p => qpB p.1 ++ [61] ++ qpB p.2)), ?_, ?_⟩
    · exact seqMap pairs (fun p => [QV.bytes p.1, QV.bytes p.2]) _ (encodeLoop_bytes pairs)
    · by_cases hp : pairs = []
      · subst hp; rfl
      · have hloop := qslLoop_fields { keepBlank := true } rfl
          (fun s => unquoteToBytes (.bytes (s.map (fun c => if c == 43 then 32 else c)) false)) pairs qpB qpB
          (fun p _ => qpB_no _ _ (Or.inr rfl))
          (fun p hp => by simp only [unquoteToBytes, unquoteImpl_bytes, scan_qpB _ (hps p hp).1])
          (fun p hp => by simp only [unquoteToBytes, unquoteImpl_bytes, scan_qpB _ (hps p hp).2])
        have he : asciiEnc [38] = .ok [38] := rfl
        simp only [parseQsl, bind, Except.bind, pure, Except.pure, joined_ne pairs qpB qpB hp,
          Bool.false_eq_true, ite_false, he,
          split_fields pairs qpB qpB hp (fun p _ => ⟨qpB_no _ _ (Or.inl rfl), qpB_no _ _ (Or.inl rfl)⟩)]
        exact hloop

end PyLean.TextLibs.Url
