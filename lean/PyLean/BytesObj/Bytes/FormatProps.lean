import PyLean.BytesObj.Bytes.Format
import PyLean.BytesObj.Bytes.Basic

/-!
Properties of `_PyBytes_FormatEx`.
-/

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

/-! ## The field writer is exact -/

/-- The `assert((res - before) == alloc)` of bytesobject.c:1136, for every flag
combination, sign, width and length: the writes of lines 988-1040 produce exactly the
`alloc` bytes reserved at lines 970-983, so the preallocation can neither overflow
nor leave a gap. Hypotheses are the invariants at that point: `len` bytes are
available in `pbuf`, `width ≥ len` (line 971), the fill is a space or `0`, and when the
`0x` prefix is written the field has at least the two prefix bytes
(`_PyUnicode_FormatLong` keeps them under `F_ALT`). -/
def FieldAllocExact : Prop :=
  ∀ (fl : Fl) (c : Int) (fill sign : Nat) (width len : Int) (pbuf : Seq),
    (fill = 32 ∨ fill = 48) → 0 ≤ len → len ≤ pbuf.length → len ≤ width →
    (hasPrefix fl c = true → 2 ≤ len) →
    ((fieldWrites fl c fill sign width len pbuf).length : Int) = fieldAlloc sign width len

theorem fieldAllocExact_proven : FieldAllocExact := by
  intro fl c fill sign width len pbuf hfill h0 hp hw hpre
  have h2 : hasPrefix fl c = true → 2 ≤ len := hpre
  unfold fieldWrites fieldAlloc
  dsimp only
  by_cases hs : sign = 0 <;> by_cases hf : fill = 32 <;> by_cases hx : hasPrefix fl c = true <;>
    by_cases hl : fl.ljust = true
  all_goals
    (try have h2' := h2 hx)
    simp only [hs, hf, hx, hl, ne_eq, not_true_eq_false, not_false_eq_true, false_and, true_and,
      and_true, and_false, Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_true, ite_false,
      decide_true, decide_false, reduceCtorEq, if_true, if_false, List.length_append,
      List.length_take, List.length_drop, List.length_replicate, List.length_cons, List.length_nil]
    (try subst hs)
    repeat' split
    all_goals (try simp only [List.length_append, List.length_take, List.length_drop,
      List.length_replicate, List.length_cons, List.length_nil])
    all_goals omega

/-! ## Characters of a digit string -/

theorem digitChar_ok : ∀ d, d < 16 →
    (Nat.digitChar d).toNat ≠ 45 ∧ (Nat.digitChar d).toNat ≠ 43 := by
  decide

theorem toDigits_chars (b n : Nat) (hb : 1 < b) (hb2 : b ≤ 16) :
    ∀ c ∈ Nat.toDigits b n, c.toNat ≠ 45 ∧ c.toNat ≠ 43 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro c hc
    rw [Nat.toDigits_eq_if hb] at hc
    split at hc
    · rename_i h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      exact digitChar_ok n (by omega)
    · rename_i h
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with hc | hc
      · exact ih (n / b) (Nat.div_lt_self (by omega) hb) c hc
      · subst hc
        exact digitChar_ok _ (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega)) hb2)

/-- A digit string, as codes: non-empty, with no sign byte in front. -/
theorem digits_head (b n : Nat) (hb : 1 < b) (hb2 : b ≤ 16) :
    ∃ d ds, digitsBase b n = d :: ds ∧ d ≠ 45 ∧ d ≠ 43 := by
  unfold digitsBase
  cases h : Nat.toDigits b n with
  | nil => exact absurd h Nat.toDigits_ne_nil
  | cons c cs =>
    have := toDigits_chars b n hb hb2 c (by simp [h])
    exact ⟨c.toNat, cs.map Char.toNat, by simp, this.1, this.2⟩

/-! ## Fast path and slow path -/

/-- Lines 958-1040 for the text of an int, `width = -1`. -/
def renderLong (fl : Fl) (c : Int) (temp : Seq) : Seq :=
  let (sign, pbuf, len) := signStep true fl temp temp.length
  let width : Int := if (-1 : Int) < len then len else -1
  fieldWrites fl c 32 sign width len pbuf

/-- The slow path for an int with no flag but `#`: `formatlong`, then the field. -/
def slowLong (v : Int) (c : Int) (alt : Bool) : Py Seq := do
  let temp ← formatLong (.int v) { alt } (-1) c.toNat
  return renderLong { alt } c temp

/-- Fast path against slow path. `%d %i %u %o %x` of an exact int with no width,
precision or sign flag (`_PyLong_FormatBytesWriter`, bytesobject.c:924-957) gives the
same text as the general path through `formatlong` and the field writer, for every
int, also where both raise (the digit limit). `X` has no fast path. The hypothesis is
the `llen > INT_MAX` guard of `_PyUnicode_FormatLong`, which the fast path does not
have: the text must have fewer than `INT_MAX` bytes. -/
def FastSlowLong : Prop :=
  ∀ (v : Int) (c : Int) (alt : Bool), (c = 100 ∨ c = 105 ∨ c = 117 ∨ c = 111 ∨ c = 120) →
    (∀ t, numberToBase v (if c = 111 then 8 else if c = 120 then 16 else 10) = .ok t →
      (t.length : Int) ≤ intMax) →
    fastLong v c alt = slowLong v c alt

theorem intRepr_shape (v : Int) (t : Seq) (h : intRepr v = .ok t) :
    t = (if v < 0 then [45] else []) ++ digitsBase 10 v.natAbs := by
  unfold intRepr Fractions.strInt at h
  by_cases hd : Fractions.numDigits v.natAbs > Fractions.maxStrDigits
  · simp [hd, bind, Except.bind] at h
  · simp only [hd, if_false, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst h
    by_cases hv : v < 0 <;> simp [hv, digitsBase]

theorem fieldWrites_plain (fl : Fl) (c : Int) (hpre : hasPrefix fl c = false)
    (hl : fl.ljust = false) (t : Seq) :
    fieldWrites fl c 32 0 (t.length : Int) (t.length : Int) t = t := by
  simp [fieldWrites, hpre, hl]

theorem fieldWrites_neg (fl : Fl) (c : Int) (hpre : hasPrefix fl c = false)
    (hl : fl.ljust = false) (t : Seq) :
    fieldWrites fl c 32 45 (t.length : Int) (t.length : Int) t = 45 :: t := by
  simp [fieldWrites, hpre, hl]

theorem formatLongText_dec (t : Seq) (alt : Bool) (type : Nat) (h1 : type ≠ 111) (h2 : type ≠ 120)
    (h3 : type ≠ 88) : formatLongText t alt (-1) type = t := by
  have hnum : ¬ ((-1 : Int) > (t.length : Int) - (0 + (if t.headD 0 = 45 then 1 else 0))) := by
    split <;> omega
  simp only [formatLongText, h1, h2, h3, or_self, ite_false, and_false, hnum, if_false, decide_false]

theorem formatLongText_alt (t : Seq) (type : Nat) (hb : type = 111 ∨ type = 120)
    (hl : 2 ≤ t.length) : formatLongText t true (-1) type = t := by
  have h3 : ¬ (type = 88) := by omega
  have hb2 : type = 111 ∨ type = 120 ∨ type = 88 := by omega
  have hnum : ¬ ((-1 : Int) > (t.length : Int) - (2 + (if t.headD 0 = 45 then 1 else 0))) := by
    split <;> omega
  unfold formatLongText
  simp only [if_pos hb2, Bool.not_true, Bool.false_eq_true, false_and, ite_false]
  rw [if_neg hnum, if_neg h3]

theorem formatLongText_bare (t : Seq) (type : Nat) (hb : type = 111 ∨ type = 120)
    (hl : 2 ≤ t.length) :
    formatLongText t false (-1) type = dropMarker (t.headD 0 = 45) t := by
  have h3 : ¬ (type = 88) := by omega
  have hb2 : type = 111 ∨ type = 120 ∨ type = 88 := by omega
  have hnum : ¬ ((-1 : Int) > (t.length : Int) - (2 + (if t.headD 0 = 45 then 1 else 0))) := by
    split <;> omega
  unfold formatLongText
  simp only [if_pos hb2, Bool.not_false, true_and, ite_true]
  rw [if_neg hnum, if_neg h3]

theorem signStep_plain (fl : Fl) (d : Nat) (ds : Seq) (len : Int) (h45 : d ≠ 45) (h43 : d ≠ 43)
    (hs : fl.sign = false) (hb : fl.blank = false) :
    signStep true fl (d :: ds) len = (0, d :: ds, len) := by
  unfold signStep
  simp only [ite_true]
  split
  · rename_i h; simp at h; omega
  · rename_i h; simp at h; omega
  · simp [hs, hb]

theorem renderLong_of (fl : Fl) (c : Int) (temp pbuf : Seq) (sign : Nat) (len : Int)
    (h : signStep true fl temp temp.length = (sign, pbuf, len)) (hl : 0 ≤ len) :
    renderLong fl c temp = fieldWrites fl c 32 sign len len pbuf := by
  have h1 : (-1 : Int) < len := by omega
  simp [renderLong, h, h1]

theorem signStep_neg_len (fl : Fl) (rest : Seq) :
    signStep true fl (45 :: rest) ((45 :: rest).length : Int) = (45, rest, (rest.length : Int)) := by
  have : (((rest.length + 1 : Nat) : Int) - 1) = rest.length := by omega
  simp [signStep, this]

/-- The result of `PyNumber_ToBase`: sign, marker, digits. -/
theorem numberToBase_based (v : Int) (b : Nat) (hb : b ≠ 10) :
    numberToBase v b = .ok ((if v < 0 then [45] else []) ++
      (if b = 8 then asc "0o" else asc "0x") ++ digitsBase b v.natAbs) := by
  simp [numberToBase, hb]

theorem fieldWrites_alt (fl : Fl) (c : Int) (hpre : hasPrefix fl c = true)
    (hl : fl.ljust = false) (s : Nat) (a b : Nat) (t : Seq) (hs : s = 0 ∨ s = 45) :
    fieldWrites fl c 32 s ((a :: b :: t).length : Int) ((a :: b :: t).length : Int) (a :: b :: t) =
      (if s = 0 then [] else [s]) ++ a :: b :: t := by
  have h3 : ((t.length : Int) + 1 + 1 - 2) = t.length := by omega
  have h4 : ¬ ((t.length : Int) < 0) := by omega
  rcases hs with rfl | rfl <;> simp only [fieldWrites, List.length_cons] <;>
    simp [hpre, hl, h3, h4]

theorem slowLong_eq (v c : Int) (alt : Bool) :
    slowLong v c alt = (do
      let temp ← unicodeFormatLong v alt (-1) c.toNat
      return renderLong { alt } c temp) := rfl

theorem ufl_ok (v : Int) (alt : Bool) (type : Nat) (t : Seq)
    (h : numberToBase v (longBase type) = .ok t) (hl : (t.length : Int) ≤ intMax) :
    unicodeFormatLong v alt (-1) type = .ok (formatLongText t alt (-1) type) := by
  have h1 : ¬ ((-1 : Int) > intMax - 3) := by decide
  have h2 : ¬ ((t.length : Int) > intMax) := by omega
  simp [unicodeFormatLong, h, h1, h2, bind, Except.bind, pure, Except.pure]

theorem ufl_err (v : Int) (alt : Bool) (type : Nat) (e : PyExc)
    (h : numberToBase v (longBase type) = .error e) :
    unicodeFormatLong v alt (-1) type = .error e := by
  have h1 : ¬ ((-1 : Int) > intMax - 3) := by decide
  simp [unicodeFormatLong, h, h1, bind, Except.bind, pure, Except.pure]

/-- The decimal conversions. -/
theorem fastSlow_dec (v : Int) (type : Nat) (alt : Bool) (ht : type = 100 ∨ type = 105 ∨ type = 117)
    (hlen : ∀ t, intRepr v = .ok t → (t.length : Int) ≤ intMax) :
    intRepr v = slowLong v type alt := by
  have hbase : longBase type = 10 := by
    rcases ht with rfl | rfl | rfl <;> rfl
  have hto : ((type : Int)).toNat = type := by simp
  have hN10 : numberToBase v 10 = intRepr v := by simp [numberToBase]
  have hpre : hasPrefix { alt } (type : Int) = false := by
    rcases ht with rfl | rfl | rfl <;> simp [hasPrefix]
  rw [slowLong_eq, hto]
  cases hr : intRepr v with
  | error e =>
    rw [ufl_err v alt type e (by rw [hbase, hN10, hr])]
    rfl
  | ok t =>
    rw [ufl_ok v alt type t (by rw [hbase, hN10, hr]) (hlen t hr)]
    have hs := intRepr_shape v t hr
    obtain ⟨d, ds, hd, h45, h43⟩ := digits_head 10 v.natAbs (by decide) (by decide)
    simp only [bind, Except.bind, pure, Except.pure]
    congr 1
    rw [formatLongText_dec _ _ _ (by omega) (by omega) (by omega)]
    by_cases hv : v < 0
    · have ht' : t = 45 :: d :: ds := by rw [hs, hd]; simp [hv]
      subst ht'
      rw [renderLong_of _ _ _ _ _ _ (signStep_neg_len _ _) (by omega),
        fieldWrites_neg _ _ hpre rfl]
    · have ht' : t = d :: ds := by rw [hs, hd]; simp [hv]
      subst ht'
      rw [renderLong_of _ _ _ _ _ _ (signStep_plain _ _ _ _ h45 h43 rfl rfl) (by omega),
        fieldWrites_plain _ _ hpre rfl]

theorem asc_0x : asc "0x" = [48, 120] := by decide
theorem asc_0o : asc "0o" = [48, 111] := by decide

/-- Text of the based conversions. -/
theorem fastSlow_based (v : Int) (type b x : Nat) (alt : Bool)
    (hb : (type = 111 ∧ b = 8 ∧ x = 111) ∨ (type = 120 ∧ b = 16 ∧ x = 120))
    (hlen : ∀ t, numberToBase v b = .ok t → (t.length : Int) ≤ intMax) :
    (.ok ((if v < 0 then [45] else []) ++ (if alt then [48, x] else []) ++ digitsBase b v.natAbs) : Py Seq)
      = slowLong v type alt := by
  have hbase : longBase type = b := by
    rcases hb with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ <;> rfl
  have hto : ((type : Int)).toNat = type := by simp
  have hN : numberToBase v b = .ok ((if v < 0 then [45] else []) ++ [48, x] ++ digitsBase b v.natAbs) := by
    rcases hb with ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩
    · rw [numberToBase_based v 8 (by decide)]; simp [asc_0o]
    · rw [numberToBase_based v 16 (by decide)]; simp [asc_0x]
  obtain ⟨d, ds, hd, h45, h43⟩ := digits_head b v.natAbs (by omega) (by omega)
  rw [slowLong_eq, hto, ufl_ok v alt type _ (by rw [hbase]; exact hN) (hlen _ hN), hd]
  have ht2 : type = 111 ∨ type = 120 := by omega
  simp only [bind, Except.bind, pure, Except.pure]
  congr 1
  have hprefix : hasPrefix { alt } (type : Int) = alt := by
    rcases hb with ⟨rfl, _, _⟩ | ⟨rfl, _, _⟩ <;> cases alt <;> rfl
  cases alt with
  | true =>
    by_cases hv : v < 0
    · simp only [hv, if_true, List.cons_append, List.nil_append]
      rw [formatLongText_alt _ type ht2 (by simp)]
      rw [renderLong_of _ _ _ _ _ _ (signStep_neg_len _ _) (by omega)]
      rw [fieldWrites_alt _ _ hprefix rfl 45 48 x (d :: ds) (Or.inr rfl)]
      simp
    · simp only [hv, if_false, List.cons_append, List.nil_append]
      rw [formatLongText_alt _ type ht2 (by simp)]
      rw [renderLong_of _ _ _ _ _ _ (signStep_plain _ _ _ _ (by decide) (by decide) rfl rfl) (by omega)]
      rw [fieldWrites_alt _ _ hprefix rfl 0 48 x (d :: ds) (Or.inl rfl)]
      simp
  | false =>
    by_cases hv : v < 0
    · simp only [hv, if_true, List.cons_append, List.nil_append, Bool.false_eq_true, if_false]
      rw [formatLongText_bare _ type ht2 (by simp)]
      simp only [dropMarker, List.headD_cons, decide_true, if_true, List.drop_succ_cons, List.drop_zero]
      rw [renderLong_of _ _ _ _ _ _ (signStep_neg_len _ _) (by omega),
        fieldWrites_neg _ _ hprefix rfl]
    · simp only [hv, if_false, List.cons_append, List.nil_append, Bool.false_eq_true]
      rw [formatLongText_bare _ type ht2 (by simp)]
      have h48 : ((48 : Nat) = 45) = False := by simp
      simp only [dropMarker, List.headD_cons, h48, decide_false, Bool.false_eq_true, if_false,
        List.drop_succ_cons, List.drop_zero]
      rw [renderLong_of _ _ _ _ _ _ (signStep_plain _ _ _ _ h45 h43 rfl rfl) (by omega),
        fieldWrites_plain _ _ hprefix rfl]

theorem fastSlowLong_proven : FastSlowLong := by
  intro v c alt hc hlen
  rcases hc with rfl | rfl | rfl | rfl | rfl
  · have := fastSlow_dec v 100 alt (by simp) (fun t h => hlen t (by simpa [numberToBase] using h))
    simpa [fastLong] using this
  · have := fastSlow_dec v 105 alt (by simp) (fun t h => hlen t (by simpa [numberToBase] using h))
    simpa [fastLong] using this
  · have := fastSlow_dec v 117 alt (by simp) (fun t h => hlen t (by simpa [numberToBase] using h))
    simpa [fastLong] using this
  · have := fastSlow_based v 111 8 111 alt (by simp) (fun t h => hlen t (by simpa using h))
    cases alt <;> simpa [fastLong, asc_0o] using this
  · have := fastSlow_based v 120 16 120 alt (by simp) (fun t h => hlen t (by simpa using h))
    cases alt <;> simpa [fastLong, asc_0x] using this

end PyLean.BytesObj.Bytes
