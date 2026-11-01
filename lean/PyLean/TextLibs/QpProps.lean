import PyLean.TextLibs.BinasciiRest

/-!
The round trip of the C quoted-printable codec, `binascii.b2a_qp` then `binascii.a2b_qp`. The encoder
runs on its model in `BinasciiRest.lean`, with its line-length logic and the rewrite of trailing
whitespace. The proof reads the encoder's output as a sequence of tokens, each of which the decoder
turns into known bytes whatever follows it.
-/

namespace PyLean.TextLibs.Binascii

open PyLean

/-- The decoder with enough fuel. -/
def qd (h : Bool) (x : List Nat) : List Nat := a2bQpLoop h (x.length + 1) x

theorem qpSkipLine_len : ∀ t : List Nat, (qpSkipLine t).length ≤ t.length
  | [] => by simp [qpSkipLine]
  | c :: r => by
    by_cases hc : c = 10
    · subst hc; simp [qpSkipLine]
    · have := qpSkipLine_len r
      have e : qpSkipLine (c :: r) = qpSkipLine r := by simp [qpSkipLine, hc]
      rw [e]
      simp only [List.length_cons]
      omega

theorem a2b_fuel (h : Bool) : ∀ (f g : Nat) (x : List Nat), x.length < f → x.length < g →
    a2bQpLoop h f x = a2bQpLoop h g x := by
  intro f
  induction f with
  | zero => intro _ _ h1; omega
  | succ f ih =>
    intro g x h1 h2
    cases g with
    | zero => omega
    | succ g =>
      cases x with
      | nil => simp [a2bQpLoop]
      | cons c r =>
        simp only [List.length_cons] at h1 h2
        by_cases hc : c = 61
        · subst hc
          match r, h1, h2 with
          | [], _, _ => simp [a2bQpLoop]
          | 10 :: t, h1, h2 =>
            simp only [a2bQpLoop, if_true]
            simp only [List.length_cons] at h1 h2
            exact ih _ _ (by omega) (by omega)
          | 13 :: t, h1, h2 =>
            simp only [a2bQpLoop, if_true]
            have := qpSkipLine_len t
            simp only [List.length_cons] at h1 h2
            exact ih _ _ (by omega) (by omega)
          | 61 :: t, h1, h2 =>
            simp only [a2bQpLoop, if_true]
            simp only [List.length_cons] at h1 h2
            rw [ih g t (by omega) (by omega)]
          | [a], h1, h2 =>
            by_cases h10 : a = 10
            · subst h10; simp only [a2bQpLoop, if_true]; exact ih _ _ (by simp at h1 ⊢; omega) (by simp at h2 ⊢; omega)
            by_cases h13 : a = 13
            · subst h13; simp only [a2bQpLoop, if_true]; exact ih _ _ (by simp [qpSkipLine]; omega) (by simp [qpSkipLine]; omega)
            by_cases h61 : a = 61
            · subst h61; simp only [a2bQpLoop, if_true]; rw [ih g [] (by simp; omega) (by simp; omega)]
            have : ∀ k, a2bQpLoop h (k + 1) [61, a] = 61 :: a2bQpLoop h k [a] := by
              intro k
              rw [a2bQpLoop] <;> simp [h10, h13, h61]
            rw [this f, this g, ih g [a] (by simp at h1 ⊢; omega) (by simp at h2 ⊢; omega)]
          | a :: b :: t, h1, h2 =>
            by_cases h10 : a = 10
            · subst h10; simp only [a2bQpLoop, if_true]; exact ih _ _ (by simp at h1 ⊢; omega) (by simp at h2 ⊢; omega)
            by_cases h13 : a = 13
            · subst h13
              simp only [a2bQpLoop, if_true]
              have := qpSkipLine_len (b :: t)
              simp only [List.length_cons] at h1 h2 this
              exact ih _ _ (by omega) (by omega)
            by_cases h61 : a = 61
            · subst h61
              simp only [a2bQpLoop, if_true]
              simp only [List.length_cons] at h1 h2
              rw [ih g (b :: t) (by simp; omega) (by simp; omega)]
            have e : ∀ k, a2bQpLoop h (k + 1) (61 :: a :: b :: t) =
                if isHexChar a && isHexChar b then
                  (digitValue a * 16 + digitValue b) % 256 :: a2bQpLoop h k t
                else 61 :: a2bQpLoop h k (a :: b :: t) := by
              intro k
              rw [a2bQpLoop] <;> simp [h10, h13, h61]
            rw [e f, e g]
            simp only [List.length_cons] at h1 h2
            split
            · rw [ih g t (by omega) (by omega)]
            · rw [ih g (a :: b :: t) (by simp; omega) (by simp; omega)]
        · simp only [a2bQpLoop, if_neg hc]
          rw [ih g r (by omega) (by omega)]

theorem qd_nil (h : Bool) : qd h [] = [] := rfl

/-- What a character other than `=` decodes to. -/
def qdc (h : Bool) (c : Nat) : Nat := if h && c == 95 then 32 else c

theorem qd_plain (h : Bool) (c : Nat) (hc : c ≠ 61) (r : List Nat) : qd h (c :: r) = qdc h c :: qd h r := by
  simp only [qd, List.length_cons, a2bQpLoop, if_neg hc, qdc]
  rw [a2b_fuel h (r.length + 1) (r.length + 1) r (by omega) (by omega)]
  split <;> rfl

theorem qd_soft (h : Bool) (t : List Nat) : qd h (61 :: 10 :: t) = qd h t := by
  simp only [qd, List.length_cons, a2bQpLoop, if_true]
  exact a2b_fuel h _ _ _ (by omega) (by omega)

theorem qd_softcr (h : Bool) (t : List Nat) : qd h (61 :: 13 :: 10 :: t) = qd h t := by
  simp only [qd, List.length_cons, a2bQpLoop, if_true, qpSkipLine]
  exact a2b_fuel h _ _ _ (by omega) (by omega)

theorem qd_hex (h : Bool) (a b : Nat) (t : List Nat) (h10 : a ≠ 10) (h13 : a ≠ 13) (h61 : a ≠ 61)
    (hx : (isHexChar a && isHexChar b) = true) :
    qd h (61 :: a :: b :: t) = (digitValue a * 16 + digitValue b) % 256 :: qd h t := by
  have e : ∀ k, a2bQpLoop h (k + 1) (61 :: a :: b :: t) =
      (digitValue a * 16 + digitValue b) % 256 :: a2bQpLoop h k t := by
    intro k
    rw [a2bQpLoop] <;> simp [h10, h13, h61, hx]
  simp only [qd, List.length_cons]
  rw [e]
  rw [a2b_fuel h _ (t.length + 1) t (by omega) (by omega)]

/-- `s` decodes to `ds`, whatever comes after it. -/
def Seg (h : Bool) (s ds : List Nat) : Prop := ∀ t, qd h (s ++ t) = ds ++ qd h t

theorem seg_nil (h : Bool) : Seg h [] [] := fun _ => rfl

theorem seg_append {h : Bool} {a b c d : List Nat} (h1 : Seg h a b) (h2 : Seg h c d) :
    Seg h (a ++ c) (b ++ d) := by
  intro t
  rw [List.append_assoc, h1, h2, List.append_assoc]

theorem seg_plain (h : Bool) (c : Nat) (hc : c ≠ 61) : Seg h [c] [qdc h c] :=
  fun t => qd_plain h c hc t

theorem seg_soft (h crlf : Bool) : Seg h (qpSoft crlf) [] := by
  intro t
  cases crlf
  · exact qd_soft h t
  · exact qd_softcr h t

theorem hex_facts : ∀ b, b < 256 →
    ∃ x y, toHex b = [x, y] ∧ x ≠ 10 ∧ x ≠ 13 ∧ x ≠ 61 ∧ y ≠ 32 ∧ y ≠ 9 ∧
      (isHexChar x && isHexChar y) = true ∧ (digitValue x * 16 + digitValue y) % 256 = b := by
  have key : ∀ b, b < 256 →
      ((toHex b)[0]! != 10 && (toHex b)[0]! != 13 && (toHex b)[0]! != 61 && (toHex b)[1]! != 32 &&
        (toHex b)[1]! != 9 && isHexChar (toHex b)[0]! && isHexChar (toHex b)[1]! &&
        (digitValue (toHex b)[0]! * 16 + digitValue (toHex b)[1]!) % 256 == b) = true := by
    decide +kernel
  intro b hb
  have := key b hb
  simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at this
  refine ⟨(toHex b)[0]!, (toHex b)[1]!, by simp [toHex], ?_⟩
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := this
  exact ⟨h1, h2, h3, h4, h5, by rw [h6, h7]; rfl, h8⟩

theorem seg_hex (h : Bool) (b : Nat) (hb : b < 256) : Seg h (61 :: toHex b) [b] := by
  obtain ⟨x, y, e, h1, h2, h3, _, _, h6, h7⟩ := hex_facts b hb
  intro t
  rw [e]
  have := qd_hex h x y t h1 h2 h3 h6
  rw [h7] at this
  exact this

/-- The invariant on the output so far. The second part is what the line end needs, when it rewrites a
trailing space or tab. -/
structure Inv (h : Bool) (out ds : List Nat) : Prop where
  seg : Seg h out.reverse ds
  tail : ∀ ch t, out = ch :: t → (ch = 32 ∨ ch = 9) → ∃ ds', ds = ds' ++ [ch] ∧ Seg h t.reverse ds'

theorem inv_soft {h : Bool} {out ds : List Nat} (crlf : Bool) (hi : Inv h out ds) :
    Inv h ((qpSoft crlf).reverse ++ out) ds := by
  constructor
  · simpa using seg_append hi.seg (seg_soft h crlf)
  · intro ch t he hch
    have := congrArg List.head? he
    cases crlf <;> simp [qpSoft] at this <;> omega

theorem inv_enc {h : Bool} {out ds : List Nat} (b : Nat) (hb : b < 256) (hi : Inv h out ds) :
    Inv h ((toHex b).reverse ++ [61] ++ out) (ds ++ [b]) := by
  obtain ⟨x, y, e, _, _, _, h4, h5, _, _⟩ := hex_facts b hb
  constructor
  · have := seg_append hi.seg (seg_hex h b hb)
    simpa [e] using this
  · intro ch t he hch
    simp only [e, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.cons.injEq] at he
    omega

theorem inv_plain {h : Bool} {out ds : List Nat} (c : Nat) (hc : c ≠ 61) (hi : Inv h out ds) :
    Inv h (c :: out) (ds ++ [qdc h c]) := by
  constructor
  · simpa using seg_append hi.seg (seg_plain h c hc)
  · intro ch t he hch
    simp only [List.cons.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    refine ⟨ds, ?_, hi.seg⟩
    have : qdc h c = c := by simp only [qdc]; split <;> simp_all
    rw [this]

/-- The rewrite of `Modules/binascii.c:1192-1201`. -/
theorem inv_line_end {h : Bool} {out ds : List Nat} (hi : Inv h out ds) : Inv h (qpProtect out) ds := by
  cases out with
  | nil => exact hi
  | cons ch t =>
    simp only [qpProtect]
    split
    · rename_i hc
      have hc' : ch = 32 ∨ ch = 9 := by simpa using hc
      obtain ⟨ds', e, hs⟩ := hi.tail ch t rfl hc'
      have hlt : ch < 256 := by omega
      obtain ⟨x, y, ex, _, _, _, h4, h5, _, _⟩ := hex_facts ch hlt
      constructor
      · have := seg_append hs (seg_hex h ch hlt)
        rw [e]
        simpa [ex] using this
      · intro c' t' he hch
        simp only [ex, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
          List.cons.injEq] at he
        omega
    · exact hi

/-- No `\r\n` in the data. -/
def noCL : List Nat → Bool
  | [] => true
  | a :: r => !(a == 13 && r.head? == some 10) && noCL r

/-- What the proof needs: with `istext`, a `\r\n` or a lone `\n` would be rewritten to the other. -/
def QCond (o : QpOpts) (crlf : Bool) (d : List Nat) : Prop :=
  o.istext = false ∨ (crlf = false ∧ noCL d = true)

theorem b2a_inv (o : QpOpts) (crlf : Bool) : ∀ (fuel : Nat) (d : List Nat) (ll : Nat) (out ds : List Nat),
    d.length < fuel → (∀ x ∈ d, x < 256) → QCond o crlf d → Inv o.header out ds →
    Seg o.header (b2aQpLoop o crlf fuel d ll out).reverse (ds ++ d) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ h; omega
  | succ f ih =>
    intro d ll out ds hl hb hc hi
    cases d with
    | nil => simpa [b2aQpLoop] using hi.seg
    | cons b r =>
      have hb0 : b < 256 := hb b (by simp)
      have hbr : ∀ x ∈ r, x < 256 := fun x hx => hb x (by simp [hx])
      simp only [List.length_cons] at hl
      have hcr : QCond o crlf r := by
        rcases hc with h | ⟨h1, h2⟩
        · exact .inl h
        · simp only [noCL, Bool.and_eq_true] at h2
          exact .inr ⟨h1, h2.2⟩
      have eds : ∀ ds' : List Nat, ds' = ds ++ [b] → ds' ++ r = ds ++ b :: r := by
        intro ds' e; subst e; simp
      by_cases he : qpMustEncode o ll b r.head? = true
      · have step : ∀ (o' : List Nat) (l' : Nat), Inv o.header o' ds →
            Seg o.header (b2aQpLoop o crlf f r (l' + 3) ((toHex b).reverse ++ [61] ++ o')).reverse (ds ++ b :: r) := by
          intro o' l' hi'
          rw [← eds _ rfl]
          exact ih r _ _ _ (by omega) hbr hcr (inv_enc b hb0 hi')
        simp only [b2aQpLoop, he, if_true]
        split
        · exact step _ _ (inv_soft crlf hi)
        · exact step _ _ hi
      · simp only [b2aQpLoop, he, Bool.false_eq_true, if_false]
        by_cases hh : (o.istext && (b == 10 || (b == 13 && r.head? == some 10))) = true
        · simp only [hh, if_true]
          simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hh
          obtain ⟨hit, hh⟩ := hh
          rcases hc with hc | ⟨h1, h2⟩
          · simp [hc] at hit
          · subst h1
            have hb10 : b = 10 := by
              rcases hh with hh | ⟨h3, h4⟩
              · exact hh
              · simp only [noCL, h3, h4] at h2
                simp at h2
            subst hb10
            have hp := inv_plain 10 (by decide) (inv_line_end hi)
            have hq : qdc o.header 10 = 10 := by simp [qdc]
            rw [hq] at hp
            have := ih r 0 _ (ds ++ [10]) (by omega) hbr hcr hp
            rw [← eds _ rfl]
            exact this
        · simp only [hh, Bool.false_eq_true, if_false]
          have hne : b ≠ 61 := by
            intro h6
            subst h6
            apply he
            simp [qpMustEncode]
          have h95 : ¬ (o.header = true ∧ b = 95) := by
            rintro ⟨h1, rfl⟩
            apply he
            simp [qpMustEncode, h1]
          have hcdec : qdc o.header (if o.header && b == 32 then 95 else b) = b := by
            by_cases h3 : o.header = true ∧ b = 32
            · obtain ⟨h1, rfl⟩ := h3
              simp [qdc, h1]
            · have : (o.header && b == 32) = false := by
                cases hh' : o.header <;> simp
                intro h4
                exact h3 ⟨hh', h4⟩
              simp only [this, Bool.false_eq_true, if_false, qdc]
              split
              · rename_i h4
                simp only [Bool.and_eq_true, beq_iff_eq] at h4
                exact absurd h4 h95
              · rfl
          have hcne : (if o.header && b == 32 then 95 else b) ≠ 61 := by
            split
            · decide
            · exact hne
          have step : ∀ (o' : List Nat) (l' : Nat), Inv o.header o' ds →
              Seg o.header (b2aQpLoop o crlf f r (l' + 1) ((if o.header && b == 32 then 95 else b) :: o')).reverse
                (ds ++ b :: r) := by
            intro o' l' hi'
            rw [← eds _ rfl]
            have := inv_plain (if o.header && b == 32 then 95 else b) hcne hi'
            rw [hcdec] at this
            exact ih r _ _ _ (by omega) hbr hcr this
          split
          · exact step _ _ (inv_soft crlf hi)
          · exact step _ _ hi

theorem noCL_get : ∀ (d : List Nat) (i : Nat), noCL d = true → d[i]? = some 13 → d[i + 1]? ≠ some 10 := by
  intro d
  induction d with
  | nil => intro i _ h; simp at h
  | cons a r ih =>
    intro i h1 h2
    simp only [noCL, Bool.and_eq_true] at h1
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h2
      subst h2
      intro h3
      cases r with
      | nil => simp at h3
      | cons b t =>
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at h3
        subst h3
        simp at h1
    | succ i =>
      simp only [List.getElem?_cons_succ] at h2 ⊢
      exact ih i h1.2 h2

theorem noCL_crlf (d : List Nat) (h : noCL d = true) : qpCrlf d = false := by
  unfold qpCrlf
  split
  · rename_i i he
    obtain ⟨hl, hp, _⟩ := List.findIdx?_eq_some_iff_getElem.mp he
    have h10 : d[i + 1]? = some 10 := by
      rw [List.getElem?_eq_getElem hl]
      simpa using hp
    cases hd : d[i]? == some 13 with
    | false => rfl
    | true =>
      have : d[i]? = some 13 := by simpa using hd
      exact absurd h10 (noCL_get d i h this)
  · rfl

/-- `binascii.a2b_qp(binascii.b2a_qp(d, ...), header=header) == d`. `quotetabs` and `header` are free,
and all byte values are covered. Precondition: `istext=False`, or no `\r\n` in `d`. That is the case
`QpRoundTrip` refutes, so nothing is hidden. -/
def QpRoundTripNarrow : Prop :=
  ∀ (d : List Nat) (o : QpOpts), (∀ x ∈ d, x < 256) → (o.istext = false ∨ noCL d = true) →
    a2bQp (.bytes (b2aQp d o)) o.header = .ok d

theorem qpRoundTripNarrow_proven : QpRoundTripNarrow := by
  intro d o hb hc
  have hq : QCond o (qpCrlf d) d := by
    rcases hc with h | h
    · exact .inl h
    · exact .inr ⟨noCL_crlf d h, h⟩
  have hs := b2a_inv o (qpCrlf d) (d.length + 1) d 0 [] [] (by omega) hb hq
    ⟨seg_nil _, by simp⟩
  have := hs []
  simp only [List.nil_append, List.append_nil, qd_nil] at this
  simp only [a2bQp, asciiBuffer, bind, Except.bind, pure, Except.pure, b2aQp]
  exact congrArg _ this

/-- The round trip for all data. False: a `\r\n` is a line end to the encoder in text mode, and a mixed
text comes back with one kind of line end. -/
def QpRoundTrip : Prop :=
  ∀ (d : List Nat) (o : QpOpts), (∀ x ∈ d, x < 256) → a2bQp (.bytes (b2aQp d o)) o.header = .ok d

theorem qpRoundTrip_refuted : ¬QpRoundTrip := by
  intro h
  have := h [10, 13, 10] ⟨false, true, false⟩ (by decide)
  revert this
  decide

end PyLean.TextLibs.Binascii
