import PyLean.Decimal.Props
import PyLean.Decimal.TupleProps
import PyLean.Decimal.ContextExact

/-!
`Decimal.__hash__`, `Decimal.as_tuple` and `IEEEContext` of `_pydecimal`, stated over their whole
domains.
-/

namespace PyLean.Decimal

open PyLean

/-! ## `__hash__` -/

/-- `_pydecimal.Decimal.__hash__` (_pydecimal.py:988-1012; the comment at :991-993 and Built-in
Types, "Hashing of numeric types": the hash of a Decimal agrees with the hash of a numerically equal
int, float or Fraction), for every value:

* a finite `±c·10^e` hashes to `hash(Fraction(d))` (the numeric hash of its exact value modulo
  `2**61 - 1`), unless its coefficient has more than 4300 digits, where `int(self._int)` (:1010)
  raises the int/str-limit `ValueError`;
* so for every int `n` within the limit, `hash(Decimal(n)) == hash(n)`;
* outside NaNs and that limit it is the C twin's hash;
* `±Infinity` hash to `±314159` (`sys.hash_info.inf`, the hash of `float('inf')`); a signaling NaN
  raises `TypeError`, a quiet NaN hashes by identity (`none`, not modelled). -/
def HashExactPy : Prop :=
  (∀ (neg : Bool) (c : Nat) (e : Int),
    pyHash (.fin neg c e) =
      if maxStrDigits < numDigits c then .error (.valueError (limitToIntMsg (numDigits c)))
      else .ok (some (PyLean.Fractions.hash (PyLean.Fractions.ofDecimal neg c e)))) ∧
  (∀ n : Int, numDigits n.natAbs ≤ maxStrDigits → (pyFromInt n >>= pyHash) = .ok (some (intHash n))) ∧
  (∀ d : Dec, nanKind d = 0 → (∀ neg c e, d = .fin neg c e → numDigits c ≤ maxStrDigits) →
    pyHash d = cHash d) ∧
  (∀ neg : Bool, pyHash (.inf neg) = .ok (some (if neg then -314159 else 314159))) ∧
  (∀ (neg : Bool) (p : Nat), pyHash (.nan neg true p) = .error (.typeError "Cannot hash a signaling NaN value.") ∧
    pyHash (.nan neg false p) = .ok none)

theorem pyHash_fin (neg : Bool) (c : Nat) (e : Int) :
    pyHash (.fin neg c e) =
      if maxStrDigits < numDigits c then .error (.valueError (limitToIntMsg (numDigits c)))
      else .ok (some (PyLean.Fractions.hash (PyLean.Fractions.ofDecimal neg c e))) := by
  simp only [pyHash, intLimit, gt_iff_lt, hashFinite, ← PyLean.Fractions.hashMatchesDecimal_proven neg c e]
  by_cases h : maxStrDigits < numDigits c
  · rw [if_pos h, if_pos h]; rfl
  · rw [if_neg h, if_neg h]; rfl

theorem hashExactPy_proven : HashExactPy := by
  refine ⟨pyHash_fin, fun n hn => ?_, fun d hd hb => ?_, fun neg => ?_, fun neg p => ⟨rfl, rfl⟩⟩
  · have h2 : PyLean.Fractions.ofDecimal (decide (n < 0)) n.natAbs 0 = PyLean.Fractions.ofInt n := by
      simp only [PyLean.Fractions.ofDecimal, PyLean.Fractions.ofInt]
      have hn : (if n < 0 then -(n.natAbs : Int) else n.natAbs) = n := by
        split <;> omega
      simp [hn]
    have hs : strLimit n.natAbs = .ok () := by
      unfold strLimit; rw [if_neg (Nat.not_lt.mpr hn)]
    have hf : pyFromInt n = .ok (.fin (decide (n < 0)) n.natAbs 0) := by
      simp only [pyFromInt, hs]; rfl
    rw [hf]
    show pyHash (.fin (decide (n < 0)) n.natAbs 0) = _
    rw [pyHash_fin, if_neg (Nat.not_lt.mpr hn), h2, PyLean.Fractions.hashMatchesInt_proven n]
    rfl
  · cases d with
    | fin neg c e =>
      have hc := hb neg c e rfl
      simp only [pyHash, cHash, intLimit, gt_iff_lt, if_neg (Nat.not_lt.mpr hc)]
      rfl
    | inf neg => rfl
    | nan neg s p => cases s <;> simp [nanKind] at hd
  · cases neg <;> rfl

/-! ## `as_tuple` -/

theorem asTuple_digits (c : Nat) :
    (Nat.toDigits 10 c).map (fun ch => PyVal.int (ch.toNat - 48)) =
      digs ((Nat.toDigits 10 c).map (fun ch => ch.toNat - 48)) := by
  simp only [digs, List.map_map]
  apply List.map_congr_left
  intro ch hch
  have h := isDigit_iff'.mp (mem_toDigits_isDigit hch)
  simp only [Function.comp, PyVal.int.injEq]
  omega

theorem toDigits_ks (c : Nat) :
    ((Nat.toDigits 10 c).map (fun ch => ch.toNat - 48)).map Nat.digitChar = Nat.toDigits 10 c := by
  rw [List.map_map]
  conv => rhs; rw [← List.map_id (Nat.toDigits 10 c)]
  apply List.map_congr_left
  intro ch hch
  exact digitChar_of_isDigit (mem_toDigits_isDigit hch)

theorem ks_le9 (c : Nat) : ∀ k ∈ (Nat.toDigits 10 c).map (fun ch => ch.toNat - 48), k ≤ 9 := by
  intro k hk
  simp only [List.mem_map] at hk
  obtain ⟨ch, hch, rfl⟩ := hk
  have h := isDigit_iff'.mp (mem_toDigits_isDigit hch)
  omega

/-- The coefficient `_pydecimal`'s tuple constructor rebuilds from `as_tuple`'s digits of `c`:
`_int` itself. -/
theorem collect_toDigits (c : Nat) :
    ∃ kept, pyFromTuple.collect ((Nat.toDigits 10 c).map (fun ch => PyVal.int (ch.toNat - 48))) [] = .ok kept ∧
      (if kept = [] then ['0'] else kept.flatMap PyVal.pyStr) = Nat.toDigits 10 c ∧
      (c ≠ 0 → kept.flatMap PyVal.pyStr = Nat.toDigits 10 c) := by
  have hk := ks_le9 c
  rw [asTuple_digits, collect_nil _ hk]
  refine ⟨_, rfl, ?_⟩
  have hv : digitsValue (((Nat.toDigits 10 c).map (fun ch => ch.toNat - 48)).map Nat.digitChar) = c := by
    rw [toDigits_ks, digitsValue_toDigits]
  have hfl := flatMap_digs (((Nat.toDigits 10 c).map (fun ch => ch.toNat - 48)).dropWhile (· == 0))
    (fun k hk' => hk k (List.dropWhile_subset _ hk'))
  rcases toDigits_digs _ hk with ⟨h0, hz⟩ | ⟨h0, ht⟩
  · rw [hv] at hz
    subst hz
    simp only [h0, List.map_nil, ↓reduceIte]
    refine ⟨rfl, fun h => absurd rfl h⟩
  · rw [hv] at ht
    have hne : List.map (fun k : Nat => PyVal.int (k : Int))
        (((Nat.toDigits 10 c).map (fun ch => ch.toNat - 48)).dropWhile (· == 0)) ≠ [] := by simpa using h0
    simp only [hne, ↓reduceIte]
    simp only [digs] at hfl
    rw [hfl, ← ht]
    exact ⟨rfl, fun _ => rfl⟩

/-- `Decimal.as_tuple()` (_pydecimal.py:1014-1019, "To show the internals exactly as they are") and
the tuple form of the constructor (:642-685; decimal docs: `Decimal((0, (1, 4, 1, 4), -3))`):
for every value `d`, `as_tuple` is the sign, the digits of `_int` as ints (each in `0..9`, reading
as the coefficient or the NaN payload) and the exponent or `'F'`/`'n'`/`'N'`, and
`Decimal(d.as_tuple())` rebuilds exactly `d`'s attributes `_sign`, `_int`, `_exp`. -/
def AsTupleExactPy : Prop :=
  (∀ (neg : Bool) (c : Nat) (e : Int),
    asTuple (.fin neg c e) = (.int (if neg then 1 else 0),
      digs ((Nat.toDigits 10 c).map (fun ch => ch.toNat - 48)), .int e) ∧
    (∀ k ∈ (Nat.toDigits 10 c).map (fun ch => ch.toNat - 48), k ≤ 9) ∧
    digitsValue (((Nat.toDigits 10 c).map (fun ch => ch.toNat - 48)).map Nat.digitChar) = c) ∧
  (∀ d : Dec, let t := asTuple d; pyFromTuple t.1 (some t.2.1) t.2.2 = .ok d.toPyObj)

theorem asTupleExactPy_proven : AsTupleExactPy := by
  refine ⟨fun neg c e => ⟨?_, ks_le9 c, by rw [toDigits_ks, digitsValue_toDigits]⟩, fun d => ?_⟩
  · simp only [asTuple, asTuple_digits]
  · cases d with
    | fin neg c e =>
      obtain ⟨kept, hk, h1, _⟩ := collect_toDigits c
      have hs : pySign (.int (if neg then 1 else 0)) = .ok neg := by cases neg <;> rfl
      simp only [asTuple, pyFromTuple, hs, hk, bind, Except.bind, pure, Except.pure, PyVal.asInt?,
        Dec.toPyObj, reduceCtorEq, ↓reduceIte, h1]
    | inf neg => cases neg <;> rfl
    | nan neg s p =>
      have hs : pySign (.int (if neg then 1 else 0)) = .ok neg := by cases neg <;> rfl
      by_cases hp : p = 0
      · subst hp
        cases s <;> simp only [asTuple, pyFromTuple, hs, bind, Except.bind, pure, Except.pure,
          Dec.toPyObj, ↓reduceIte, pyFromTuple.collect, List.flatMap_nil] <;> rfl
      · obtain ⟨kept, hk, _, h2⟩ := collect_toDigits p
        cases s <;> simp only [asTuple, pyFromTuple, hs, hk, hp, bind, Except.bind, pure, Except.pure,
          Dec.toPyObj, ↓reduceIte, h2 hp] <;> rfl

/-! ## `IEEEContext` -/

/-- `IEEEContext(bits)` (_pydecimal.py:427-445; decimal docs: "a context object initialized to the
proper values for one of the IEEE interchange formats"), for every `DefaultContext` and every int
`bits`: a `bits` that is not positive, above `IEEE_CONTEXT_MAX_BITS = 512` or not a multiple of 32 is
the `ValueError` with the source's message; otherwise it is `Context()` (its exceptions included)
with `prec = 9·bits/32 - 2`, `Emax = 3·2**(bits/16 + 3)`, `Emin = 1 - Emax`, `ROUND_HALF_EVEN`,
`clamp = 1` and no trap set; so decimal32, decimal64 and decimal128 have the IEEE 754 parameters
`(7, 96)`, `(16, 384)` and `(34, 6144)`. Scope: an int argument (a float or other object reaches
`ctx.prec = ...` with a non-int and is refused there). -/
def ieeeOf (c : PyContext) (bits : Int) : PyContext :=
  { c with
    prec := 9 * (bits / 32) - 2
    emax := 3 * 2 ^ (bits / 16 + 3).toNat
    emin := 1 - 3 * 2 ^ (bits / 16 + 3).toNat
    rounding := .halfEven
    roundingObj := none
    clamp := 1
    traps := pySignals.map (fun s => (s, false))
    trapsExtra := [] }

def IEEEContextExact : Prop :=
  (∀ (dc : PyContext) (bits : Int), (bits ≤ 0 ∨ bits > 512 ∨ bits % 32 ≠ 0) →
    ieeeContext dc bits = .error (.valueError "argument must be a multiple of 32, with a maximum of 512")) ∧
  (∀ (dc : PyContext) (bits : Int), ¬ (bits ≤ 0 ∨ bits > 512 ∨ bits % 32 ≠ 0) →
    ieeeContext dc bits = (fun c => ieeeOf c bits) <$> pyContextNew dc {}) ∧
  (9 * ((32 : Int) / 32) - 2 = 7 ∧ 3 * 2 ^ ((32 : Int) / 16 + 3).toNat = (96 : Int)) ∧
  (9 * ((64 : Int) / 32) - 2 = 16 ∧ 3 * 2 ^ ((64 : Int) / 16 + 3).toNat = (384 : Int)) ∧
  (9 * ((128 : Int) / 32) - 2 = 34 ∧ 3 * 2 ^ ((128 : Int) / 16 + 3).toNat = (6144 : Int))

theorem setSignalDict_false :
    setSignalDict (.dict (keyed (pySignals.map (fun s => (s, false))))) =
      .ok (pySignals.map (fun s => (s, false)), []) := by decide

theorem ieeeContextExact_proven : IEEEContextExact := by
  refine ⟨fun dc bits h => ?_, fun dc bits h => ?_, by decide, by decide, by decide⟩
  · unfold ieeeContext
    rw [if_pos (show bits ≤ 0 ∨ bits > ieeeMaxBits ∨ bits % 32 ≠ 0 by simpa only [ieeeMaxBits] using h)]
    rfl
  · have hb : 32 ≤ bits ∧ bits ≤ 512 := by omega
    have h1 : ¬ (9 * (bits / 32) - 2 < 1) := by omega
    have hE : (96 : Int) ≤ 3 * 2 ^ (bits / 16 + 3).toNat := by
      have h0 : 2 ^ 5 ≤ 2 ^ (bits / 16 + 3).toNat := Nat.pow_le_pow_right (by decide) (by omega)
      have h' : ((2 ^ (bits / 16 + 3).toNat : Nat) : Int) = (2 : Int) ^ (bits / 16 + 3).toNat :=
        Int.natCast_pow 2 _
      omega
    have h2 : ¬ ((3 * 2 ^ (bits / 16 + 3).toNat : Int) < 0) := by omega
    have h3 : ¬ ((1 - 3 * 2 ^ (bits / 16 + 3).toNat : Int) > 0) := by omega
    unfold ieeeContext
    rw [if_neg (show ¬ (bits ≤ 0 ∨ bits > ieeeMaxBits ∨ bits % 32 ≠ 0) by simpa only [ieeeMaxBits] using h)]
    cases hc : pyContextNew dc {} with
    | error x => rfl
    | ok c =>
      simp only [bind, Except.bind, pySetattr, setIntegerCheck, intValue, h1, h2, h3, ↓reduceIte,
        roundingOfName, setSignalDict_false, pure, Except.pure, Functor.map, Except.map, ieeeOf]
      rfl

end PyLean.Decimal
