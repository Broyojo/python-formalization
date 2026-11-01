import PyLean.LongObj.PylongStr

/-!
`int(str)` end to end: `_str_to_int_inner`, `int_from_string` and
`pylong_int_from_string` meet the contract `long_from_string_base` relies on, which
closes the grammar theorems of `FromString.lean`, and printing and parsing round-trip.

Strings of two million digits or more go through `_dec_str_to_int_inner`; below that
every path here is free of `decimal`.
-/

namespace PyLean.LongObj

open PyLean PyLean.MathInt

theorem digit_range : ∀ c, c < 256 → digitValue c < 10 → 48 ≤ c ∧ c ≤ 57 := by decide +kernel

theorem dv_of_range : ∀ c, c < 256 → 48 ≤ c → c ≤ 57 → digitValue c < 10 := by decide +kernel

theorem not_space_of_digit : ∀ c, c < 256 → digitValue c < 10 → StrSearch.uniSpace c = false := by
  decide +kernel

/-- ASCII digits and nothing else. -/
def AsciiDigits (s : List Nat) : Prop := ∀ c ∈ s, 48 ≤ c ∧ c ≤ 57

theorem dv_of_ascii {s : List Nat} (h : AsciiDigits s) : ∀ c ∈ s, digitValue c < 10 := fun c hc =>
  dv_of_range c (by have := h c hc; omega) (h c hc).1 (h c hc).2

theorem transform_ascii {s : List Nat} (h : ∀ c ∈ s, c < 128) :
    transformDecimalAndSpace s = s := by
  unfold transformDecimalAndSpace
  rw [if_pos (List.all_eq_true.2 (fun c hc => by simpa using h c hc))]

theorem ten_cast : ((10 : Nat) : Int) = 10 := rfl

/-- `int(s)` on at most 2048 ASCII digits, the leaf of `_str_to_int_inner`. -/
theorem leaf_ok {f lim : Nat} {s : List Nat} (hs : AsciiDigits s) (hne : s ≠ [])
    (hlen : s.length ≤ 2048) (hl : lim = 0 ∨ 2048 ≤ lim) :
    pylongLeaf (f + 1) lim s = .ok (hv 10 0 s : Nat) := by
  have hasc : ∀ c ∈ s, c < 128 := fun c hc => by have := hs c hc; omega
  have hdv := dv_of_ascii hs
  have hdp : DigitPart 10 s := digitPart_of_all s hne hdv
  have hl' : IsLit 10 (transformDecimalAndSpace s) false 10 s := by
    rw [transform_ascii hasc]
    exact ⟨[], [], [], [], by simp, fun _ h => by simp at h, fun _ h => by simp at h,
      Or.inl ⟨rfl, rfl⟩, .plain (by decide), hdp⟩
  have hc := cnt_le_length s
  have e := pyLongFromUnicodeObject_lit (pyl := pylongHook (fun s => do
    let v ← intOfStrF f lim s 10
    return v.toInt)) (lim := lim) (u := s) (fun _ h => absurd h (by omega)) (Or.inr (by decide)) hl'
    (by omega)
  have hnh : ¬ limitHit lim (cnt s) 10 := by
    rintro ⟨_, _, h3, h4⟩
    omega
  rw [if_neg hnh, ten_cast] at e
  unfold pylongLeaf
  rw [intOfStrF, e]
  simp only [bindOk, pureOk]
  rw [Long.toInt_ofInt]
  rfl

theorem slice_split (s : List Nat) {a m b : Nat} (h1 : a ≤ m) (h2 : m ≤ b) :
    slice s a b = slice s a m ++ slice s m b := by
  unfold slice
  rw [show b - a = (m - a) + (b - m) by omega, List.take_add, List.drop_drop,
    show a + (m - a) = m by omega]

theorem length_slice {s : List Nat} {a b : Nat} (h1 : a ≤ b) (h2 : b ≤ s.length) :
    (slice s a b).length = b - a := by
  unfold slice
  simp
  omega

theorem mem_slice {s : List Nat} {a b c : Nat} (h : c ∈ slice s a b) : c ∈ s := by
  unfold slice at h
  exact List.mem_of_mem_drop (List.mem_of_mem_take h)

theorem hv_digits_append {l₁ l₂ : List Nat} (h : AsciiDigits l₂) :
    hv 10 0 (l₁ ++ l₂) = hv 10 0 l₁ * 10 ^ l₂.length + hv 10 0 l₂ := by
  have hc : cnt l₂ = l₂.length := cnt_of_digits (b := 10) (by decide) l₂ (dv_of_ascii h)
  have := hv_add 10 l₂ (hv 10 0 l₁) 0 0
  simpa [hv_append, hc] using this

theorem sti_spec {leaf : List Nat → Py Int} {w5 : PowDict Nat} {s : List Nat} {L : Nat}
    (hs : AsciiDigits s) (hL : L = s.length)
    (hleaf : ∀ a b, a < b → b ≤ L → b - a ≤ 2048 →
      leaf (slice s a b) = .ok (hv 10 0 (slice s a b) : Nat))
    (hk : ∀ x, Reach 2048 L x → 2048 < x → dGet (x >>> 1) w5 = some (5 ^ (x >>> 1))) :
    ∀ (f a b : Nat), b - a < f → a < b → b ≤ L → Reach 2048 L (b - a) →
      stiInner leaf w5 s f a b = .ok (hv 10 0 (slice s a b) : Nat)
  | 0, _, _, h, _, _, _ => by omega
  | f + 1, a, b, h, hab, hb, hr => by
    rw [stiInner]
    by_cases hw : b - a ≤ 2048
    · rw [if_pos hw]
      exact hleaf a b hab hb hw
    · rw [if_neg hw]
      have hM : 2048 < b - a := by omega
      obtain ⟨mid, hmid⟩ : ∃ mid, (a + b + 1) >>> 1 = mid := ⟨_, rfl⟩
      have hm : mid = (a + b + 1) / 2 := by rw [← hmid, shr1]
      have hlow : (b - a) >>> 1 = b - mid := by rw [shr1]; omega
      have hhigh : (b - a) - (b - a) >>> 1 = mid - a := by rw [hlow]; omega
      have r1 : Reach 2048 L (b - mid) := hlow ▸ Reach.lo hr hM
      have r2 : Reach 2048 L (mid - a) := hhigh ▸ Reach.hi hr hM
      have e1 := sti_spec hs hL hleaf hk f mid b (by omega) (by omega) hb r1
      have e2 := sti_spec hs hL hleaf hk f a mid (by omega) (by omega) (by omega) r2
      have e3 := hk _ hr hM
      rw [hlow] at e3
      simp only [hmid, e1, e2, bindOk, e3, pureOk]
      congr 1
      have hsl : AsciiDigits (slice s mid b) := fun c hc => hs c (mem_slice hc)
      have hsplit := slice_split s (a := a) (m := mid) (b := b) (by omega) (by omega)
      have hlen := length_slice (s := s) (a := mid) (b := b) (by omega) (by omega)
      have h10 : 10 ^ (b - mid) = 5 ^ (b - mid) * 2 ^ (b - mid) := by rw [← Nat.mul_pow]
      rw [hsplit, hv_digits_append hsl, hlen, h10]
      push_cast
      rw [Int.add_comm, Int.mul_assoc]

theorem strToIntInner_spec {leaf : List Nat → Py Int} {s : List Nat} (hs : AsciiDigits s)
    (hne : s ≠ []) (hleaf : ∀ a b, a < b → b ≤ s.length → b - a ≤ 2048 →
      leaf (slice s a b) = .ok (hv 10 0 (slice s a b) : Nat)) :
    strToIntInner leaf s = .ok (hv 10 0 s : Nat) := by
  obtain ⟨d, e, hv', hk⟩ := computePowersNat_spec s.length 5 2048 false
  have hkey : ∀ x, Reach 2048 s.length x → 2048 < x → dGet (x >>> 1) d = some (5 ^ (x >>> 1)) := by
    intro x hr hx
    have := dGet_key hv' hk hr hx
    simpa [whichOf_false] using this
  have hpos : 0 < s.length := List.length_pos_iff.2 hne
  have hsp := sti_spec hs rfl hleaf hkey (s.length + 1) 0 s.length (by omega) hpos
    (Nat.le_refl _) (by simpa using Reach.top)
  have hall : slice s 0 s.length = s := by simp [slice]
  rw [hall] at hsp
  unfold strToIntInner
  simp only [e, bindOk, hsp]

theorem digitPart_last {b : Nat} {l : List Nat} (h : DigitPart b l) :
    ∃ t c, l = t ++ [c] ∧ digitValue c < b := by
  induction h with
  | @one c hc => exact ⟨[], c, rfl, hc⟩
  | @cons c r _ _ ih =>
    obtain ⟨t, x, rfl, hx⟩ := ih
    exact ⟨c :: t, x, rfl, hx⟩
  | @us c r _ _ ih =>
    obtain ⟨t, x, rfl, hx⟩ := ih
    exact ⟨c :: uscore :: t, x, rfl, hx⟩

theorem rstripU_body {body : List Nat} (hd : DigitPart 10 body) (hb : ∀ c ∈ body, c < 256) :
    rstripU body = body := by
  obtain ⟨t, c, rfl, hc⟩ := digitPart_last hd
  have hsp := not_space_of_digit c (hb c (by simp)) hc
  unfold rstripU
  rw [List.reverse_append, List.reverse_singleton, List.singleton_append, List.dropWhile_cons,
    if_neg (by simp [hsp])]
  simp

theorem hv_filter (b : Nat) : ∀ (l : List Nat) (acc : Nat),
    hv b acc (l.filter (· ≠ uscore)) = hv b acc l
  | [], _ => rfl
  | c :: l, acc => by
    rw [List.filter_cons, hv_cons]
    by_cases hc : c = uscore
    · simp only [hc, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, if_false, if_true]
      exact hv_filter b l acc
    · simp only [ne_eq, hc, not_false_eq_true, decide_true, if_true, if_false]
      rw [hv_cons, if_neg hc]
      exact hv_filter b l _

theorem length_filter : ∀ l : List Nat, (l.filter (· ≠ uscore)).length = cnt l
  | [] => rfl
  | c :: l => by
    rw [List.filter_cons]
    by_cases hc : c = uscore
    · simp only [hc, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, if_false, cnt,
        if_true, Nat.zero_add]
      exact length_filter l
    · simp only [ne_eq, hc, not_false_eq_true, decide_true, if_true, cnt, if_false,
        List.length_cons]
      rw [length_filter l]
      omega

/-- `pylong_int_from_string` and `int_from_string` meet the contract of
`long_from_string_base`, below the `_decimal` switch. -/
theorem hook_ok (f lim : Nat) : HookOK (pylongHook (pylongLeaf (f + 1) lim)) lim 2000000 := by
  intro body hdp hbytes hN hc hl
  have hs := rstripU_body hdp hbytes
  obtain ⟨s, hsd⟩ : ∃ s, body.filter (· ≠ uscore) = s := ⟨_, rfl⟩
  have hlen : s.length = cnt body := by rw [← hsd]; exact length_filter body
  have hval : hv 10 0 s = hv 10 0 body := by rw [← hsd]; exact hv_filter 10 body 0
  have hvb := digitPart_valid hdp
  have hd : AsciiDigits s := by
    intro c hc'
    rw [← hsd] at hc'
    obtain ⟨h1, h2⟩ := List.mem_filter.1 hc'
    have hne : c ≠ uscore := by simpa using h2
    exact digit_range c (hbytes c h1) ((hvb c h1).resolve_left hne)
  have hne : s ≠ [] := by
    intro h0
    rw [h0] at hlen
    simp at hlen
    omega
  have hlim : lim = 0 ∨ 2048 ≤ lim := by omega
  have hleaf : ∀ a b, a < b → b ≤ s.length → b - a ≤ 2048 →
      pylongLeaf (f + 1) lim (slice s a b) = .ok (hv 10 0 (slice s a b) : Nat) := by
    intro a b hab hb hw
    apply leaf_ok (fun c hc' => hd c (mem_slice hc')) _ _ hlim
    · intro h0
      have := length_slice (s := s) (Nat.le_of_lt hab) hb
      rw [h0] at this
      simp at this
      omega
    · rw [length_slice (Nat.le_of_lt hab) hb]
      exact hw
  have e := strToIntInner_spec hd hne hleaf
  unfold pylongHook intFromString
  simp only [hs, hsd]
  rw [if_neg (by omega)]
  simp only [e, bindOk, pureOk, Int.natAbs_natCast, hval]

theorem intOfStr_eq (lim : Nat) (u : List Nat) (base : Int) :
    intOfStr lim u base = pyLongFromUnicodeObject (pylongHook (pylongLeaf 2 lim)) lim u base := rfl

/-! ## The properties -/

/-- `int(bytes, base)` accepts exactly the literals of the documented grammar, with their
value, unless the digit limit applies. Below two million digits. -/
def IntBytesGrammar : Prop :=
  ∀ (lim base : Nat) (s : List Nat), (base = 0 ∨ (2 ≤ base ∧ base ≤ 36)) → (∀ c ∈ s, c < 256) →
    s.length < 2000000 →
    (∀ neg rb body, IsLit base s neg rb body → intOfBytes lim s (base : Int) =
      if limitHit lim (cnt body) rb then .error (.valueError (limitToIntMsg lim (cnt body)))
      else .ok (Long.ofInt (litValue neg rb body))) ∧
    (∀ v, intOfBytes lim s (base : Int) = .ok v →
      ∃ neg rb body, IsLit base s neg rb body ∧ v = Long.ofInt (litValue neg rb body))

theorem cnt_le_of_isLit {base rb : Nat} {neg : Bool} {s body : List Nat}
    (h : IsLit base s neg rb body) : cnt body ≤ s.length := by
  obtain ⟨ws1, sg, pre, ws2, rfl, _⟩ := h
  have := cnt_le_length body
  simp only [List.length_append]
  omega

theorem hook_at {lim : Nat} {body : List Nat} (hc : cnt body < 2000000)
    (hd : DigitPart 10 body) (hb : ∀ c ∈ body, c < 256) :
    HookAt (pylongHook (pylongLeaf 2 lim)) lim body :=
  hook_ok 1 lim body hd hb hc

theorem body_bytes {base rb : Nat} {neg : Bool} {s body : List Nat}
    (h : IsLit base s neg rb body) (hb : ∀ c ∈ s, c < 256) : ∀ c ∈ body, c < 256 := by
  obtain ⟨ws1, sg, pre, ws2, rfl, _⟩ := h
  intro c hc
  exact hb c (by simp [hc])

theorem intBytesGrammar_proven : IntBytesGrammar := by
  intro lim base s hbase hb hN
  have hmax : s.length ≤ 2 ^ 58 := by omega
  refine ⟨?_, ?_⟩
  · intro neg rb body hl
    have hc := cnt_le_of_isLit hl
    refine pyLongFromBytes_lit (pyl := pylongHook (pylongLeaf 2 lim)) ?_ hbase hl (by omega)
    rintro rfl
    obtain ⟨ws1, sg, pre, ws2, _, _, _, _, _, hdp⟩ := id hl
    exact hook_at (by omega) hdp (body_bytes hl hb)
  · intro v h
    exact pyLongFromBytes_inv (hook_ok 1 lim) hbase hmax hN hb h

/-- `int(str, base)`: the same, after `_PyUnicode_TransformDecimalAndSpaceToASCII`. -/
def IntStrGrammar : Prop :=
  ∀ (lim base : Nat) (u : List Nat), (base = 0 ∨ (2 ≤ base ∧ base ≤ 36)) → u.length < 2000000 →
    (∀ neg rb body, IsLit base (transformDecimalAndSpace u) neg rb body →
      intOfStr lim u (base : Int) =
        if limitHit lim (cnt body) rb then .error (.valueError (limitToIntMsg lim (cnt body)))
        else .ok (Long.ofInt (litValue neg rb body))) ∧
    (∀ v, intOfStr lim u (base : Int) = .ok v →
      ∃ neg rb body, IsLit base (transformDecimalAndSpace u) neg rb body ∧
        v = Long.ofInt (litValue neg rb body))

theorem transform_ascii_output : ∀ u : List Nat, ∀ c ∈ transformLoop u, c < 128 := by
  intro u
  induction u with
  | nil => intro c h; simp [transformLoop] at h
  | cons x u ih =>
    intro c h
    rw [transformLoop] at h
    split at h
    · rcases List.mem_cons.1 h with rfl | h
      · omega
      · exact ih c h
    · split at h
      · rcases List.mem_cons.1 h with rfl | h
        · omega
        · exact ih c h
      · split at h
        · rename_i z hz
          have hz2 := List.find?_some hz
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hz2
          rcases List.mem_cons.1 h with rfl | h
          · omega
          · exact ih c h
        · simp at h
          omega

theorem transform_ascii_all (u : List Nat) : ∀ c ∈ transformDecimalAndSpace u, c < 128 := by
  intro c hc
  unfold transformDecimalAndSpace at hc
  split at hc
  · rename_i h
    simpa using List.all_eq_true.1 h c hc
  · exact transform_ascii_output u c hc

theorem length_transformLoop : ∀ u : List Nat, (transformLoop u).length ≤ u.length
  | [] => Nat.le_refl _
  | x :: u => by
    have := length_transformLoop u
    rw [transformLoop]
    split
    · simp; omega
    · split
      · simp; omega
      · split
        · simp; omega
        · simp

theorem length_transform (u : List Nat) : (transformDecimalAndSpace u).length ≤ u.length := by
  unfold transformDecimalAndSpace
  split
  · exact Nat.le_refl _
  · exact length_transformLoop u

theorem intStrGrammar_proven : IntStrGrammar := by
  intro lim base u hbase hN
  have hlen := length_transform u
  have hb : ∀ c ∈ transformDecimalAndSpace u, c < 256 := fun c hc => by
    have := transform_ascii_all u c hc
    omega
  refine ⟨?_, ?_⟩
  · intro neg rb body hl
    have hc := cnt_le_of_isLit hl
    rw [intOfStr_eq]
    refine pyLongFromUnicodeObject_lit ?_ hbase hl (by omega)
    rintro rfl
    obtain ⟨ws1, sg, pre, ws2, _, _, _, _, _, hdp⟩ := id hl
    exact hook_at (by omega) hdp (body_bytes hl hb)
  · intro v h
    rw [intOfStr_eq] at h
    exact pyLongFromUnicodeObject_inv (hook_ok 1 lim) hbase (by omega) (by omega) hb h

/-! ## Round trips -/

/-- `int(str(n)) == n` within the limit. Below two million digits. -/
def RoundTripDecimal : Prop :=
  ∀ (lim : Nat) (v : Int), ValidLimit lim → (lim = 0 ∨ numDigits v ≤ lim) →
    numDigits v < 2000000 →
    (longToDecimalString lim (Long.ofInt v) >>= fun s => intOfStr lim (s.map Char.toNat) 10) =
      .ok (Long.ofInt v)

/-- The sign and digits of `str(v)` as code points. -/
theorem decStr_bytes (v : Int) : (decStr v).map Char.toNat =
    (if decide (v < 0) then [45] else []) ++ [] ++ digitBytes 10 v.natAbs := by
  unfold decStr digitBytes
  by_cases h : v < 0 <;> simp [h]

theorem litValue_natAbs (b : Nat) (hb : b = 2 ∨ b = 8 ∨ b = 10 ∨ b = 16) (v : Int) :
    litValue (decide (v < 0)) b (digitBytes b v.natAbs) = v := by
  rw [litValue_printed hb]
  by_cases h : v < 0 <;> simp [h] <;> omega

theorem printed_ascii {b : Nat} (hb : b = 2 ∨ b = 8 ∨ b = 10 ∨ b = 16) {neg : Bool} {pre : List Nat}
    (hp : ∀ c ∈ pre, c < 128) (V : Nat) :
    ∀ c ∈ (if neg then [45] else []) ++ pre ++ digitBytes b V, c < 128 := by
  intro c hc
  rcases List.mem_append.1 hc with h | h
  · rcases List.mem_append.1 h with h | h
    · cases neg
      · simp at h
      · simp at h
        omega
    · exact hp c h
  · exact digitBytes_ascii hb V c h

theorem cnt_digitBytes {b : Nat} (hb : b = 2 ∨ b = 8 ∨ b = 10 ∨ b = 16) (V : Nat) :
    cnt (digitBytes b V) = (Nat.toDigits b V).length := by
  rw [cnt_of_digits (b := b) (by omega) _ (digitBytes_spec hb V).2.1]
  simp [digitBytes]

theorem roundTripDecimal_proven : RoundTripDecimal := by
  intro lim v hlim hl hN
  have hD : ¬ (lim > 0 ∧ numDigits v > lim) := by omega
  have hstr : longToDecimalString lim (Long.ofInt v) = .ok (decStr v) := by
    rw [longToDecimalString_eq hlim]
    by_cases hs : sizeOf' v ≤ 1000
    · rw [if_pos hs, if_neg hD]
    · rw [if_neg hs]
      have : ¬ (lim > 0 ∧ lim / 90 ≤ (sizeOf' v - 11) / 10) := by
        rintro ⟨h1, h2⟩
        have := precheck_digits (by omega) h1 h2
        omega
      rw [if_neg this]
  rw [hstr]
  simp only [bindOk]
  have hb10 : (10 : Nat) = 2 ∨ (10 : Nat) = 8 ∨ (10 : Nat) = 10 ∨ (10 : Nat) = 16 := by omega
  rw [decStr_bytes]
  have hl' := isLit_printed (base := 10) (pre := []) (decide (v < 0)) v.natAbs hb10
    (.plain (by decide))
  rw [← transform_ascii (printed_ascii hb10 (by simp) v.natAbs)] at hl'
  have hcnt : cnt (digitBytes 10 v.natAbs) < 2000000 := by
    rw [cnt_digitBytes hb10]
    exact hN
  have e := pyLongFromUnicodeObject_lit (pyl := pylongHook (pylongLeaf 2 lim)) (lim := lim)
    (fun _ => hook_at hcnt (digitPart_of_all _ (digitBytes_spec hb10 _).1 (digitBytes_spec hb10 _).2.1)
      (fun c hc => by have := digitBytes_ascii hb10 _ c hc; omega))
    (Or.inr (by decide)) hl' (by omega)
  have hnh : ¬ limitHit lim (cnt (digitBytes 10 v.natAbs)) 10 := by
    rintro ⟨_, _, h3, h4⟩
    rw [cnt_digitBytes hb10] at h4
    have : numDigits v = (Nat.toDigits 10 v.natAbs).length := rfl
    omega
  rw [if_neg hnh, litValue_natAbs 10 hb10, ten_cast] at e
  rw [intOfStr_eq]
  exact e

/-- `int(format(n, 'b'/'o'/'x'), base) == n`, and the same through `bin`, `oct`, `hex` with
`base` the radix or 0: power-of-two bases are free of the limit. -/
def RoundTripRadix : Prop :=
  ∀ (lim : Nat) (v : Int) (b : Nat), (b = 2 ∨ b = 8 ∨ b = 16) →
    (Nat.toDigits b v.natAbs).length ≤ 2 ^ 58 → sizeOf' v ≤ maxLongDigits →
    (longFormatBinary (Long.ofInt v) b false >>= fun s =>
      intOfStr lim (s.map Char.toNat) (b : Int)) = .ok (Long.ofInt v) ∧
    (longFormatBinary (Long.ofInt v) b true >>= fun s =>
      intOfStr lim (s.map Char.toNat) (b : Int)) = .ok (Long.ofInt v) ∧
    (longFormatBinary (Long.ofInt v) b true >>= fun s =>
      intOfStr lim (s.map Char.toNat) 0) = .ok (Long.ofInt v)

theorem radix_mark {b : Nat} (hb : b = 2 ∨ b = 8 ∨ b = 16) :
    lower (if b = 16 then 'x' else if b = 8 then 'o' else 'b').toNat = radixLetter b ∧
      (if b = 16 then 'x' else if b = 8 then 'o' else 'b').toNat < 128 := by
  rcases hb with rfl | rfl | rfl <;> decide

theorem format_bytes (v : Int) (b : Nat) (alt : Bool) :
    ((if decide (v < 0) = true then ['-'] else []) ++
      (if alt then ['0', if b = 16 then 'x' else if b = 8 then 'o' else 'b'] else []) ++
      Nat.toDigits b v.natAbs).map Char.toNat =
    (if decide (v < 0) then [45] else []) ++
      (if alt then [48, (if b = 16 then 'x' else if b = 8 then 'o' else 'b').toNat] else []) ++
      digitBytes b v.natAbs := by
  unfold digitBytes
  cases alt <;> by_cases h : v < 0 <;> simp [h]

theorem roundTripRadix_proven : RoundTripRadix := by
  intro lim v b hb hlen hsz
  have hb4 : b = 2 ∨ b = 8 ∨ b = 10 ∨ b = 16 := by omega
  obtain ⟨hmark, hmark2⟩ := radix_mark hb
  have hspec := fun alt => longFormatBinary_spec (Long.ofInt v) b alt hb (digitsOf_digits _)
    (normal_digitsOf _) (by
      intro hn
      have : v < 0 := by simpa [ofInt_neg_flag] using hn
      rw [ofInt_ds, Ne, digitsOf_eq_nil]
      omega) (by rw [length_ofInt]; exact hsz)
  rw [val_ofInt, ofInt_neg_flag] at *
  have hrun : ∀ (alt : Bool) (base : Nat), (base = 0 ∨ (2 ≤ base ∧ base ≤ 36)) →
      LitForm base (if alt then [48, (if b = 16 then 'x' else if b = 8 then 'o' else 'b').toNat]
        else []) b (digitBytes b v.natAbs) →
      (longFormatBinary (Long.ofInt v) b alt >>= fun s =>
        intOfStr lim (s.map Char.toNat) (base : Int)) = .ok (Long.ofInt v) := by
    intro alt base hbase hf
    rw [hspec alt]
    simp only [bindOk]
    rw [format_bytes]
    have hp : ∀ c ∈ (if alt then [48, (if b = 16 then 'x' else if b = 8 then 'o' else 'b').toNat]
        else []), c < 128 := by
      cases alt
      · simp
      · intro c hc
        simp only [if_true, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · decide
        · exact hmark2
    have hl' := isLit_printed (decide (v < 0)) v.natAbs hb4 hf
    rw [← transform_ascii (printed_ascii hb4 hp v.natAbs)] at hl'
    have hcnt : cnt (digitBytes b v.natAbs) ≤ 2 ^ 58 := by
      rw [cnt_digitBytes hb4]; exact hlen
    have e := pyLongFromUnicodeObject_lit (pyl := pylongHook (pylongLeaf 2 lim)) (lim := lim)
      (fun h => absurd h (by omega)) hbase hl' hcnt
    have hnh : ¬ limitHit lim (cnt (digitBytes b v.natAbs)) b := by
      rintro ⟨h1, _⟩
      rcases hb with rfl | rfl | rfl <;> exact h1 (by decide)
    rw [if_neg hnh, litValue_natAbs b hb4] at e
    rw [intOfStr_eq]
    exact e
  have hpre : IsRadixPrefix b [48, (if b = 16 then 'x' else if b = 8 then 'o' else 'b').toNat] :=
    ⟨hb, _, hmark, Or.inl rfl⟩
  have hbr : 2 ≤ b ∧ b ≤ 36 := by omega
  have hbne : b ≠ 0 := by omega
  refine ⟨hrun false b (Or.inr hbr) (.plain hbne), hrun true b (Or.inr hbr) ?_, ?_⟩
  · exact .radix hbne hpre
  · exact hrun true 0 (Or.inl rfl) (.autoRadix hpre)

end PyLean.LongObj
