import PyLean.LongObj.Digits

/-!
`int` to string, `Objects/longobject.c` (CPython 3.14.7): the base-`10^9` loop of
`long_to_decimal_string_internal` with its pre-check and exact digit count, and
the shift-and-mask loop of `long_format_binary`.

`interp->long_state.max_str_digits` is the explicit parameter `lim`
(`sys.set_int_max_str_digits` allows `0`, meaning no limit, or at least `640`,
sysmodule.c:4733).

Output buffers are filled right to left in C (`*--p = ...`): the model conses
onto `acc`, and the final length check stands for `assert(p == start)`. A theorem
of the form `f x = .ok s` therefore also says that the computed `strlen`/`sz` is
exactly the number of characters written, so the writes stay inside the buffer.
`pout` writes are capacity-checked in the same way.
-/

namespace PyLean.LongObj

open PyLean PyLean.MathInt

/-! ## Constants -/

/-- `_PY_LONG_MAX_STR_DIGITS_THRESHOLD`, pycore_long.h:42. -/
def strDigitsThreshold : Nat := 640
/-- `_PY_LONG_DEFAULT_MAX_STR_DIGITS`, pycore_long.h:29. -/
def defaultMaxStrDigits : Nat := 4300
/-- `_PyLong_DECIMAL_SHIFT`, longintrepr.h:48. -/
def decShift : Nat := 9
/-- `_PyLong_DECIMAL_BASE`, longintrepr.h:49. -/
def decBase : Nat := 10 ^ 9

/-- `sys.set_int_max_str_digits` admits `0` or anything from the threshold up,
sysmodule.c:4733. -/
def ValidLimit (lim : Nat) : Prop := lim = 0 ∨ strDigitsThreshold ≤ lim

/-- `_MAX_STR_DIGITS_ERROR_FMT_TO_STR`, longobject.c:33. -/
def limitToStrMsg (lim : Nat) : String :=
  s!"Exceeds the limit ({lim} digits) for integer string conversion; use sys.set_int_max_str_digits() to increase the limit"

/-! ## Decimal conversion, base `10^9` limbs -/

/-- The inner `for (j = 0; j < size; j++)` loop, longobject.c:2178-2183. -/
def decStep : List Nat → Nat → Py (List Nat × Nat)
  | [], hi => .ok ([], hi)
  | p :: ps, hi => do
    let z ← chk64 ((p <<< 30) ||| hi)
    let hi' ← chk32 (z / decBase)
    let p' ← chk32 (z - hi' * decBase)
    let (r, h) ← decStep ps hi'
    return (p' :: r, h)

/-- `while (hi) { pout[size++] = hi % DECIMAL_BASE; hi /= DECIMAL_BASE; }`,
longobject.c:2184-2187. `cap` is the allocated size of `scratch`. -/
def pushHi (cap : Nat) : Nat → List Nat → Nat → Py (List Nat)
  | 0, _, _ => .error .modelFuel
  | f + 1, pout, hi =>
    if hi ≠ 0 then
      if pout.length < cap then pushHi cap f (pout ++ [hi % decBase]) (hi / decBase)
      else .error cOverflow
    else .ok pout

/-- The outer loop `for (i = size_a; --i >= 0; )`, longobject.c:2176-2193, reading
`pin` from the top digit; `SIGCHECK` has no effect on a value. -/
def decLoop (cap : Nat) : List Nat → List Nat → Py (List Nat)
  | [], pout => .ok pout
  | d :: ds, pout => do
    let (p, hi) ← decStep pout d
    let p' ← pushHi cap 3 p hi
    decLoop cap ds p'

/-- `while (rem >= tenpow) { tenpow *= 10; strlen++; }`, longobject.c:2203-2206;
`tenpow` is a `digit`. Returns the number of `strlen++`. -/
def lenLoop : Nat → Nat → Nat → Nat → Py Nat
  | 0, _, _, _ => .error .modelFuel
  | f + 1, rem, tenpow, n =>
    if rem ≥ tenpow then do
      let t ← chk32 (tenpow * 10)
      lenLoop f rem t (n + 1)
    else .ok n

/-- `*--p = '0' + rem % 10; rem /= 10;` repeated `j` times, longobject.c:2247-2250. -/
def writeFixed : Nat → Nat → List Char → List Char
  | 0, _, acc => acc
  | j + 1, rem, acc => writeFixed j (rem / 10) (Char.ofNat (48 + rem % 10) :: acc)

/-- `do { *--p = '0' + rem % 10; rem /= 10; } while (rem != 0);`,
longobject.c:2254-2257. -/
def writeTop : Nat → Nat → List Char → Py (List Char)
  | 0, _, _ => .error .modelFuel
  | f + 1, rem, acc =>
    let acc' := Char.ofNat (48 + rem % 10) :: acc
    if rem / 10 ≠ 0 then writeTop f (rem / 10) acc' else .ok acc'

/-- The `for` loop over `pout[0..size-2]` and the top limb, longobject.c:2245-2257. -/
def writeLimbs : List Nat → List Char → Py (List Char)
  | [], _ => .error cOverflow
  | [t], acc => writeTop 10 t acc
  | p :: q :: ps, acc => writeLimbs (q :: ps) (writeFixed decShift p acc)

/-- Lines 2086-2240 of `long_to_decimal_string_internal`: everything after the
switch to `_pylong`. All three output targets (`PyUnicode_New`, `writer`,
`bytes_writer`) receive the same characters. -/
def decCore (lim : Nat) (x : Long) : Py (List Char) := do
  let size_a := x.ds.length
  let d := (33 * decShift) / (10 * 30 - 33 * decShift)
  let size := 1 + size_a + size_a / d
  longAlloc size
  let pout ← decLoop size x.ds.reverse []
  let pout := if pout.length = 0 then [0] else pout
  let negative := if x.neg then 1 else 0
  let n ← lenLoop 11 (pout.getLastD 0) 10 0
  let strlen := negative + 1 + (pout.length - 1) * decShift + n
  if strlen > strDigitsThreshold ∧ lim > 0 ∧ strlen - negative > lim then
    throw (.valueError (limitToStrMsg lim))
  else
    let acc ← writeLimbs pout []
    let acc := if x.neg then '-' :: acc else acc
    if acc.length = strlen then return acc else throw cOverflow

/-- The pre-check at longobject.c:2125-2135, based on `10/3 >= log2(10)`. -/
def decPreCheck (lim size_a : Nat) : Py Unit :=
  if size_a ≥ 10 * strDigitsThreshold / (3 * 30) + 2 then
    if lim > 0 ∧ lim / (3 * 30) ≤ (size_a - 11) / 10 then
      .error (.valueError (limitToStrMsg lim))
    else .ok ()
  else .ok ()

/-- `long_to_decimal_string_internal(aa, ...)`, longobject.c:2096-2318; `pyl` is
`pylong_int_to_decimal_string` (the switch at :2137-2146). -/
def longToDecimalWith (pyl : Long → Py (List Char)) (lim : Nat) (x : Long) : Py (List Char) := do
  let size_a := x.ds.length
  decPreCheck lim size_a
  if size_a > 1000 then pyl x else decCore lim x

/-! ## Power-of-two bases -/

/-- `bit_length_digit(x)`, longobject.c:966, through `_Py_bit_length`. -/
def bitLengthDigit (x : Nat) : Nat := bitLength x

/-- `PY_SSIZE_T_MAX`. -/
def ssizeMax : Nat := 2 ^ 63 - 1

/-- `cdigit += (cdigit < 10) ? '0' : 'a'-10;`, longobject.c:2428. -/
def hexCharC (cdigit : Nat) : Char :=
  Char.ofNat (cdigit + (if cdigit < 10 then 48 else 97 - 10))

/-- The `do { ... } while` loop of `WRITE_DIGITS`, longobject.c:2425-2432. `last`
is `i == size_a-1`. `accumbits` is a C `int`; on the last digit it may go below
zero, where it is no longer read, so saturating `Nat` subtraction changes nothing. -/
def fmtWhile (base bits : Nat) (last : Bool) :
    Nat → Nat → Nat → List Char → Py (Nat × Nat × List Char)
  | 0, _, _, _ => .error .modelFuel
  | f + 1, accum, ab, acc =>
    let acc' := hexCharC (accum &&& (base - 1)) :: acc
    let ab' := ab - bits
    let accum' := accum >>> bits
    if (if last then decide (accum' > 0) else decide (ab' ≥ bits)) then
      fmtWhile base bits last f accum' ab' acc'
    else .ok (accum', ab', acc')

/-- The `for (i = 0; i < size_a; ++i)` loop, longobject.c:2421-2433. -/
def fmtLoop (base bits : Nat) : List Nat → Nat → Nat → List Char → Py (List Char)
  | [], _, _, acc => .ok acc
  | d :: ds, accum, ab, acc => do
    let a ← chk64 (accum ||| (d <<< ab))
    let (a', ab', acc') ← fmtWhile base bits ds.isEmpty 64 a (ab + 30) acc
    fmtLoop base bits ds a' ab' acc'

/-- `long_format_binary(aa, base, alternate, ...)`, longobject.c:2335-2500, for
`base` one of 2, 8, 16. All output targets receive the same characters. -/
def longFormatBinary (x : Long) (base : Nat) (alternate : Bool) : Py (List Char) := do
  let size_a := x.ds.length
  let negative := if x.neg then 1 else 0
  let bits := if base = 16 then 4 else if base = 8 then 3 else 1
  let sz ←
    if size_a = 0 then pure 1
    else if size_a > (ssizeMax - 3) / 30 then
      throw (.overflowError "int too large to format")
    else
      let size_a_in_bits := (size_a - 1) * 30 + bitLengthDigit (x.ds.getLastD 0)
      pure (negative + (size_a_in_bits + (bits - 1)) / bits)
  let sz := if alternate then sz + 2 else sz
  let acc ← if size_a = 0 then pure ['0'] else fmtLoop base bits x.ds 0 0 []
  let acc :=
    if alternate then
      '0' :: (if base = 16 then 'x' else if base = 8 then 'o' else 'b') :: acc
    else acc
  let acc := if x.neg then '-' :: acc else acc
  if acc.length = sz then return acc else throw cOverflow

/-- `_PyLong_Format(obj, base)`, longobject.c:2503-2514. -/
def pyLongFormatWith (pyl : Long → Py (List Char)) (lim : Nat) (x : Long) (base : Nat) :
    Py (List Char) :=
  if base = 10 then longToDecimalWith pyl lim x else longFormatBinary x base true

/-- `_PyLong_FormatWriter(writer, obj, base, alternate)`, longobject.c:2517-2527,
and `_PyLong_FormatBytesWriter(...)`, longobject.c@3.14.7:2449-2466: the same dispatch
into a writer. -/
def pyLongFormatWriterWith (pyl : Long → Py (List Char)) (lim : Nat) (x : Long) (base : Nat)
    (alternate : Bool) : Py (List Char) :=
  if base = 10 then longToDecimalWith pyl lim x else longFormatBinary x base alternate

/-! ## Digit strings -/

/-! `bindOk` and `pureOk` restate `bind_ok` and `pure_ok` without being `rfl`
theorems. As a definitional rewrite under `simp`, `bind_ok` leaves the kernel to
compare `chk32 (z / decBase) >>= f` against an unrelated continuation, and it runs
out of memory unfolding the arithmetic in `chk32`'s condition. -/
theorem bindOk {α β : Type} (a : α) (f : α → Py β) : (Except.ok a >>= f) = f a :=
  Eq.trans rfl rfl
theorem pureOk {α : Type} (a : α) : (pure a : Py α) = .ok a := Eq.trans rfl rfl

/-- The low `E` digits of `x` in base `b`, most significant first, zeros kept. -/
def zdigits (b : Nat) : Nat → Nat → List Char
  | 0, _ => []
  | E + 1, x => zdigits b E (x / b) ++ [(x % b).digitChar]

theorem length_zdigits (b E x : Nat) : (zdigits b E x).length = E := by
  induction E generalizing x <;> simp [zdigits, *]

theorem zdigits_add_mul {b : Nat} (hb : 0 < b) :
    ∀ E x t, zdigits b E (x + b ^ E * t) = zdigits b E x
  | 0, _, _ => rfl
  | E + 1, x, t => by
    have e : x + b ^ (E + 1) * t = x + b * (b ^ E * t) := by
      rw [Nat.pow_succ, Nat.mul_comm (b ^ E) b, Nat.mul_assoc]
    have h1 : (x + b ^ (E + 1) * t) / b = x / b + b ^ E * t := by
      rw [e, Nat.add_mul_div_left _ _ hb]
    have h2 : (x + b ^ (E + 1) * t) % b = x % b := by
      rw [e, Nat.add_mul_mod_self_left]
    simp only [zdigits, h1, h2, zdigits_add_mul hb E]

theorem toDigits_add_pow {b : Nat} (hb : 1 < b) :
    ∀ E t x, 0 < t → x < b ^ E →
      Nat.toDigits b (t * b ^ E + x) = Nat.toDigits b t ++ zdigits b E x
  | 0, t, x, _, hx => by
    have : x = 0 := by simpa using hx
    subst this
    simp [zdigits]
  | E + 1, t, x, ht, hx => by
    have hb0 : 0 < b := by omega
    have hlt : x / b < b ^ E := by
      apply Nat.div_lt_of_lt_mul
      rw [Nat.pow_succ, Nat.mul_comm] at hx
      exact hx
    have hmod : x % b < b := Nat.mod_lt _ hb0
    have e : t * b ^ (E + 1) + x = b * (t * b ^ E + x / b) + x % b := by
      rw [Nat.pow_succ, Nat.mul_add, ← Nat.mul_assoc t, Nat.mul_comm (t * b ^ E) b, Nat.add_assoc,
        Nat.div_add_mod]
    have hpos : 0 < t * b ^ E + x / b :=
      Nat.lt_of_lt_of_le (Nat.mul_pos ht (Nat.pow_pos hb0)) (Nat.le_add_right _ _)
    rw [e, ← Nat.toDigits_append_toDigits hb hpos hmod, toDigits_add_pow hb E t (x / b) ht hlt,
      Nat.toDigits_of_lt_base hmod]
    simp [zdigits, List.append_assoc]

theorem digitChar_of_lt_ten : ∀ d, d < 10 → Char.ofNat (48 + d) = d.digitChar := by decide

theorem writeFixed_eq : ∀ j rem acc, writeFixed j rem acc = zdigits 10 j rem ++ acc
  | 0, _, _ => rfl
  | j + 1, rem, acc => by
    simp [writeFixed, zdigits, writeFixed_eq j,
      digitChar_of_lt_ten (rem % 10) (Nat.mod_lt _ (by decide))]

theorem writeTop_eq (f : Nat) : ∀ rem acc, rem < 10 ^ (f + 1) →
    writeTop (f + 1) rem acc = .ok (Nat.toDigits 10 rem ++ acc) := by
  induction f with
  | zero =>
    intro rem acc h
    have h0 : ¬ rem / 10 ≠ 0 := by omega
    have hm : rem % 10 = rem := by omega
    simp only [writeTop, h0, ite_false, Nat.toDigits_of_lt_base (show rem < 10 by omega), hm,
      digitChar_of_lt_ten rem (by omega), List.singleton_append]
  | succ f ih =>
    intro rem acc h
    by_cases h0 : rem / 10 ≠ 0
    · have hlt : rem / 10 < 10 ^ (f + 1) := by
        apply Nat.div_lt_of_lt_mul
        rw [Nat.pow_succ 10 (f + 1), Nat.mul_comm] at h
        exact h
      have hge : 10 ≤ rem := by omega
      rw [writeTop]
      simp only [if_pos h0]
      rw [ih _ _ hlt, Nat.toDigits_of_base_le (by decide) hge,
        digitChar_of_lt_ten _ (Nat.mod_lt _ (by decide))]
      simp [List.append_assoc]
    · have hm : rem % 10 = rem := by omega
      simp only [writeTop, h0, ite_false, Nat.toDigits_of_lt_base (show rem < 10 by omega), hm,
        digitChar_of_lt_ten rem (by omega), List.singleton_append]

/-! ## Limb vectors -/

/-- Value of a little-endian vector of limbs of base `B`. -/
def limbVal (B : Nat) : List Nat → Nat
  | [] => 0
  | p :: ps => p + B * limbVal B ps

theorem limbVal_nil (B : Nat) : limbVal B [] = 0 := Eq.trans rfl rfl
theorem limbVal_cons (B p : Nat) (ps : List Nat) :
    limbVal B (p :: ps) = p + B * limbVal B ps := Eq.trans rfl rfl

theorem limbVal_append (B : Nat) : ∀ a b : List Nat,
    limbVal B (a ++ b) = limbVal B a + B ^ a.length * limbVal B b
  | [], b => by simp [limbVal_nil]
  | x :: xs, b => by
    simp only [List.cons_append, limbVal_cons, limbVal_append B xs, List.length_cons, Nat.pow_succ]
    rw [Nat.mul_add, Nat.add_assoc, ← Nat.mul_assoc B, Nat.mul_comm B (B ^ xs.length)]

def Limbs (l : List Nat) : Prop := ∀ p ∈ l, p < decBase

theorem decBase_eq : decBase = 1000000000 := by decide

theorem normal_top_pos : ∀ {l : List Nat}, Normal l → l ≠ [] → 0 < limbVal decBase l
  | [], _, h => absurd rfl h
  | [t], hn, _ => by
    have : t ≠ 0 := by simpa using hn (by simp)
    simp only [limbVal_cons, limbVal_nil]
    omega
  | x :: y :: ys, hn, _ => by
    have := normal_top_pos (normal_of_cons hn) (by simp)
    rw [limbVal_cons]
    have hB : 0 < decBase * limbVal decBase (y :: ys) := Nat.mul_pos (by decide) this
    omega

/-! ## The base conversion loop -/

theorem decStep_spec : ∀ (ps : List Nat) (hi : Nat), Limbs ps → hi < 2 ^ 30 →
    ∃ r h, decStep ps hi = .ok (r, h) ∧ r.length = ps.length ∧ Limbs r ∧ h < 2 ^ 30 ∧
      limbVal decBase r + decBase ^ ps.length * h = limbVal decBase ps * 2 ^ 30 + hi ∧
      (Normal ps → ps ≠ [] → h ≠ 0)
  | [], hi, _, h => ⟨[], hi, rfl, rfl, fun _ h => by simp at h, h, by simp [limbVal_nil],
      fun _ h => absurd rfl h⟩
  | p :: ps, hi, hp, h => by
    have hpB : p < decBase := hp p (by simp)
    have hps : Limbs ps := fun x hx => hp x (by simp [hx])
    have hz : (p <<< 30) ||| hi = p * 2 ^ 30 + hi := by
      rw [← Nat.shiftLeft_add_eq_or_of_lt h, Nat.shiftLeft_eq]
    obtain ⟨z, hzd⟩ : ∃ z, p * 2 ^ 30 + hi = z := ⟨_, rfl⟩
    rw [hzd] at hz
    have hB := decBase_eq
    have hz64 : z < 2 ^ 64 := by rw [hB] at hpB; omega
    have hzB : z < decBase * 2 ^ 30 := by rw [hB] at hpB ⊢; omega
    have hq : z / decBase < 2 ^ 30 := Nat.div_lt_of_lt_mul hzB
    have hq32 : z / decBase < 2 ^ 32 := by omega
    have hdm := Nat.div_add_mod z decBase
    have hmlt : z % decBase < decBase := Nat.mod_lt _ (by rw [hB]; omega)
    have hrem : z - z / decBase * decBase = z % decBase := by
      rw [Nat.mul_comm (z / decBase)]
      omega
    have hrem32 : z % decBase < 2 ^ 32 := Nat.lt_trans hmlt (by rw [hB]; omega)
    obtain ⟨r, h', e, hl, hr, hlt, hv, hn⟩ := decStep_spec ps (z / decBase) hps hq
    refine ⟨z % decBase :: r, h', ?_, by simp [hl], ?_, hlt, ?_, ?_⟩
    · simp only [decStep, hz, chk64_ok hz64, bindOk, chk32_ok hq32, hrem, chk32_ok hrem32, e,
        pureOk]
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hmlt
      · exact hr x hx
    · have hlen : decBase ^ (ps.length + 1) = decBase * decBase ^ ps.length := Nat.pow_succ'
      rw [limbVal_cons, limbVal_cons, List.length_cons, hlen]
      obtain ⟨A, hA⟩ : ∃ A, limbVal decBase ps = A := ⟨_, rfl⟩
      obtain ⟨R, hR⟩ : ∃ R, limbVal decBase r = R := ⟨_, rfl⟩
      rw [hA] at hv ⊢
      rw [hR] at hv ⊢
      have hv' : decBase * R + decBase * decBase ^ ps.length * h' =
          decBase * (A * 2 ^ 30) + decBase * (z / decBase) := by
        rw [Nat.mul_assoc, ← Nat.mul_add, hv, Nat.mul_add]
      have e1 : (p + decBase * A) * 2 ^ 30 = p * 2 ^ 30 + decBase * (A * 2 ^ 30) := by
        rw [Nat.add_mul, Nat.mul_assoc]
      rw [Nat.add_assoc, hv', e1]
      omega
    · intro hN _
      by_cases hne : ps = []
      · subst hne
        have hp0 : p ≠ 0 := by simpa using hN (by simp)
        have heq : h' = z / decBase := by
          rw [decStep] at e
          have := Except.ok.inj e
          simpa using (congrArg Prod.snd this).symm
        rw [heq]
        have h1 : decBase ≤ z := by rw [hB]; omega
        have := Nat.div_pos h1 (by rw [hB]; omega)
        omega
      · exact hn (normal_of_cons hN) hne

theorem limbs_append {a b : List Nat} (ha : Limbs a) (hb : Limbs b) : Limbs (a ++ b) := by
  intro x hx
  rcases List.mem_append.1 hx with h | h
  · exact ha x h
  · exact hb x h

theorem pushHi_spec (cap : Nat) (f : Nat) : ∀ (p : List Nat) (hi : Nat), Limbs p →
    hi < decBase ^ f → limbVal decBase p + decBase ^ p.length * hi < decBase ^ cap →
    ∃ r, pushHi cap (f + 1) p hi = .ok r ∧ Limbs r ∧
      limbVal decBase r = limbVal decBase p + decBase ^ p.length * hi ∧
      (hi = 0 → r = p) ∧ (hi ≠ 0 → Normal r) := by
  have hB := decBase_eq
  induction f with
  | zero =>
    intro p hi hl h1 _
    have : hi = 0 := by simpa using h1
    subst this
    exact ⟨p, by simp [pushHi], hl, by simp, fun _ => rfl, fun h => absurd rfl h⟩
  | succ f ih =>
    intro p hi hl h1 h2
    by_cases h0 : hi = 0
    · subst h0
      exact ⟨p, by simp [pushHi], hl, by simp, fun _ => rfl, fun h => absurd rfl h⟩
    · have hcap : p.length < cap := by
        have hp : decBase ^ p.length ≤ decBase ^ p.length * hi :=
          Nat.le_mul_of_pos_right _ (by omega)
        have : decBase ^ p.length < decBase ^ cap := by omega
        exact (Nat.pow_lt_pow_iff_right (by rw [hB]; omega)).1 this
      have hmlt : hi % decBase < decBase := Nat.mod_lt _ (by rw [hB]; omega)
      have hl' : Limbs (p ++ [hi % decBase]) := limbs_append hl (by
        intro x hx
        simp only [List.mem_singleton] at hx
        subst hx; exact hmlt)
      have hdiv : hi / decBase < decBase ^ f := by
        apply Nat.div_lt_of_lt_mul
        rw [Nat.pow_succ, Nat.mul_comm] at h1
        exact h1
      have hval : limbVal decBase (p ++ [hi % decBase]) +
          decBase ^ (p ++ [hi % decBase]).length * (hi / decBase) =
          limbVal decBase p + decBase ^ p.length * hi := by
        rw [limbVal_append]
        simp only [limbVal_cons, limbVal_nil, Nat.mul_zero, Nat.add_zero, List.length_append,
          List.length_cons, List.length_nil, Nat.zero_add, Nat.pow_succ]
        rw [Nat.add_assoc, Nat.mul_assoc, ← Nat.mul_add, Nat.mod_add_div]
      obtain ⟨r, e, h3, h4, h5, h6⟩ := ih _ _ hl' hdiv (by rw [hval]; exact h2)
      refine ⟨r, ?_, h3, by rw [h4, hval], fun h => absurd h h0, fun _ => ?_⟩
      · rw [pushHi, if_pos h0, if_pos hcap]; exact e
      · by_cases hd : hi / decBase = 0
        · rw [h5 hd]
          apply normal_concat
          have : hi % decBase = hi := Nat.mod_eq_of_lt (by
            have := Nat.div_add_mod hi decBase
            rw [hd] at this
            have := Nat.mod_lt hi (show 0 < decBase by rw [hB]; omega)
            omega)
          rw [this]; exact h0
        · exact h6 hd

/-- Horner in base `2^30` over top-first digits. -/
def tv (acc : Nat) (l : List Nat) : Nat := l.foldl (fun a d => a * 2 ^ 30 + d) acc

theorem tv_cons (acc d : Nat) (l : List Nat) : tv acc (d :: l) = tv (acc * 2 ^ 30 + d) l := rfl

theorem le_tv : ∀ (l : List Nat) (acc : Nat), acc ≤ tv acc l
  | [], _ => Nat.le_refl _
  | d :: l, acc => by
    rw [tv_cons]
    have := le_tv l (acc * 2 ^ 30 + d)
    have : acc ≤ acc * 2 ^ 30 := Nat.le_mul_of_pos_right _ (by decide)
    omega

theorem tv_reverse (ds : List Nat) : tv 0 ds.reverse = val ds := by
  have key : ∀ (ds : List Nat) (acc : Nat),
      tv acc ds.reverse = acc * 2 ^ (30 * ds.length) + val ds := by
    intro ds
    induction ds with
    | nil => intro acc; simp [tv]
    | cons d ds ih =>
      intro acc
      have h1 : tv acc (d :: ds).reverse = tv acc ds.reverse * 2 ^ 30 + d := by
        simp [tv, List.foldl_append]
      have h2 : 2 ^ (30 * (ds.length + 1)) = 2 ^ (30 * ds.length) * 2 ^ 30 := by
        rw [show 30 * (ds.length + 1) = 30 * ds.length + 30 by omega, Nat.pow_add]
      rw [h1, ih, val_cons, List.length_cons, h2, Nat.add_mul, Nat.mul_assoc,
        Nat.mul_comm (val ds), Nat.add_assoc, Nat.add_comm (2 ^ 30 * val ds) d]
  simpa using key ds 0

theorem decLoop_spec (cap : Nat) : ∀ (ds p : List Nat), (∀ d ∈ ds, d < 2 ^ 30) → Limbs p →
    Normal p → tv (limbVal decBase p) ds < decBase ^ cap →
    ∃ r, decLoop cap ds p = .ok r ∧ Limbs r ∧ Normal r ∧
      limbVal decBase r = tv (limbVal decBase p) ds
  | [], p, _, hl, hn, _ => ⟨p, rfl, hl, hn, rfl⟩
  | d :: ds, p, hd, hl, hn, hb => by
    have hd0 : d < 2 ^ 30 := hd d (by simp)
    have hds : ∀ x ∈ ds, x < 2 ^ 30 := fun x hx => hd x (by simp [hx])
    obtain ⟨q, h, e, hql, hql', hlt, hv, hnz⟩ := decStep_spec p d hl hd0
    have hsmall : limbVal decBase p * 2 ^ 30 + d ≤ tv (limbVal decBase p) (d :: ds) := by
      rw [tv_cons]; exact le_tv _ _
    have hlt2 : h < decBase ^ 2 := by
      have : decBase ^ 2 = 1000000000000000000 := by rw [decBase_eq]
      rw [this]; omega
    obtain ⟨r, e2, h1, h2, h3, h4⟩ := pushHi_spec cap 2 q h hql' hlt2 (by
      rw [hql, hv]; omega)
    have hr : limbVal decBase r = limbVal decBase p * 2 ^ 30 + d := by rw [h2, hql, hv]
    have hnr : Normal r := by
      by_cases h0 : h = 0
      · rw [h3 h0]
        by_cases hp : p = []
        · subst hp
          have : q = [] := List.length_eq_zero_iff.1 hql
          rw [this]; exact normal_nil
        · exact absurd h0 (hnz hn hp)
      · exact h4 h0
    obtain ⟨r', e3, h5, h6, h7⟩ := decLoop_spec cap ds r hds h1 hnr (by
      rw [hr, ← tv_cons]; exact hb)
    refine ⟨r', ?_, h5, h6, ?_⟩
    · simp only [decLoop, e, bindOk, e2, e3]
    · rw [h7, hr, tv_cons]

theorem cap_bound (s : Nat) : 2 ^ (30 * s) ≤ decBase ^ (1 + s + s / 99) := by
  have h1 : (2 : Nat) ^ 2970 ≤ decBase ^ 100 := by decide +kernel
  have h2 : ∀ r, r < 99 → 2 ^ (30 * r) ≤ decBase ^ (1 + r) := by decide +kernel
  have hs := Nat.div_add_mod s 99
  have hr := Nat.mod_lt s (show 0 < 99 by decide)
  generalize s / 99 = q at *
  generalize s % 99 = r at *
  subst hs
  have e1 : 30 * (99 * q + r) = 2970 * q + 30 * r := by omega
  have e2 : 1 + (99 * q + r) + q = 100 * q + (1 + r) := by omega
  rw [e1, e2, Nat.pow_add, Nat.pow_add, Nat.pow_mul 2 2970 q, Nat.pow_mul decBase 100 q]
  exact Nat.mul_le_mul (Nat.pow_le_pow_left h1 q) (h2 r hr)

theorem lenLoop_spec {rem : Nat} (hrem : rem < 10 ^ 9) :
    ∀ f k n, 1 ≤ k → k ≤ 9 → 10 ≤ k + f → (k = 1 ∨ 10 ^ (k - 1) ≤ rem) →
      k ≤ (Nat.toDigits 10 rem).length ∧
      lenLoop f rem (10 ^ k) n = .ok (n + (Nat.toDigits 10 rem).length - k)
  | 0, k, _, _, h2, h3, _ => by omega
  | f + 1, k, n, h1, h2, h3, h4 => by
    by_cases h : rem ≥ 10 ^ k
    · have hk : k < 9 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 10)).1 (by omega)
      have e : 10 ^ k * 10 = 10 ^ (k + 1) := (Nat.pow_succ ..).symm
      have hle : 10 ^ (k + 1) ≤ 10 ^ 9 := Nat.pow_le_pow_right (by decide) hk
      have h32 : 10 ^ k * 10 < 2 ^ 32 := by rw [e]; omega
      obtain ⟨a, b⟩ := lenLoop_spec hrem f (k + 1) (n + 1) (by omega) (by omega) (by omega)
        (Or.inr (by simpa using h))
      refine ⟨by omega, ?_⟩
      simp only [lenLoop, h, ite_true, ge_iff_le, chk32_ok h32, bindOk]
      rw [e, b]
      congr 1
      omega
    · have hlt : rem < 10 ^ k := by omega
      have hle := (Nat.length_toDigits_le_iff (b := 10) (by decide) (by omega : 0 < k)).2 hlt
      have hpos : 0 < (Nat.toDigits 10 rem).length :=
        List.length_pos_iff.2 Nat.toDigits_ne_nil
      have hge : k ≤ (Nat.toDigits 10 rem).length := by
        by_cases hk : k = 1
        · omega
        · rcases h4 with h4 | h4
          · omega
          · apply Nat.le_of_not_lt
            intro hc
            have := (Nat.length_toDigits_le_iff (b := 10) (n := rem) (k := k - 1) (by decide)
              (by omega)).1 (by omega)
            omega
      refine ⟨hge, ?_⟩
      simp only [lenLoop, h, ite_false]
      congr 1
      omega

theorem getLastD_cons_cons (a b : Nat) (l : List Nat) :
    (a :: b :: l).getLastD 0 = (b :: l).getLastD 0 := by
  simp [List.getLastD_eq_getLast?, List.getLast?_cons_cons]

theorem writeLimbs_spec : ∀ (p : List Nat) (acc : List Char), p ≠ [] → Limbs p →
    (1 < p.length → Normal p) →
    writeLimbs p acc = .ok (Nat.toDigits 10 (limbVal decBase p) ++ acc) ∧
    (Nat.toDigits 10 (limbVal decBase p)).length =
      (p.length - 1) * decShift + (Nat.toDigits 10 (p.getLastD 0)).length
  | [], _, h, _, _ => absurd rfl h
  | [t], acc, _, hl, _ => by
    have ht : t < decBase := hl t (by simp)
    have e : limbVal decBase [t] = t := by simp [limbVal_cons, limbVal_nil]
    rw [e]
    refine ⟨?_, by simp⟩
    have h10 : t < 10 ^ (9 + 1) := by
      rw [decBase_eq] at ht
      omega
    rw [writeLimbs]
    exact writeTop_eq 9 t acc h10
  | p :: q :: ps, acc, _, hl, hn => by
    have hN := hn (by simp)
    have hN' := normal_of_cons hN
    have hlq : Limbs (q :: ps) := fun x hx => hl x (List.mem_cons_of_mem _ hx)
    obtain ⟨a, b⟩ := writeLimbs_spec (q :: ps) (writeFixed decShift p acc) (by simp) hlq
      (fun _ => hN')
    have hpos := normal_top_pos hN' (by simp)
    have hp : p < decBase := hl p (by simp)
    have e : limbVal decBase (p :: q :: ps) = limbVal decBase (q :: ps) * 10 ^ 9 + p := by
      rw [limbVal_cons, Nat.add_comm, Nat.mul_comm]
      rfl
    have hdig := toDigits_add_pow (b := 10) (by decide) 9 _ p hpos (by
      rw [decBase_eq] at hp
      exact hp)
    constructor
    · rw [writeLimbs, a, writeFixed_eq, e, hdig, List.append_assoc]
      rfl
    · rw [e, hdig, List.length_append, length_zdigits, b, getLastD_cons_cons]
      simp only [List.length_cons, decShift]

      have : (ps.length + 1 + 1 - 1) * 9 = (ps.length + 1 - 1) * 9 + 9 := by
        rw [show ps.length + 1 + 1 - 1 = (ps.length + 1 - 1) + 1 by omega, Nat.add_mul]
      omega

/-- `decCore` is exact, every intermediate fits its C type, `scratch` is big enough,
and the limit fires exactly when the digit count exceeds it. -/
theorem decCore_spec (lim : Nat) (x : Long) (hd : IsDigits x.ds)
    (hs : 1 + x.ds.length + x.ds.length / 99 ≤ maxLongDigits) :
    decCore lim x =
      if (if x.neg then 1 else 0) + (Nat.toDigits 10 (val x.ds)).length > strDigitsThreshold ∧
          lim > 0 ∧ (Nat.toDigits 10 (val x.ds)).length > lim then
        .error (.valueError (limitToStrMsg lim))
      else .ok ((if x.neg then ['-'] else []) ++ Nat.toDigits 10 (val x.ds)) := by
  have hbound : tv (limbVal decBase []) x.ds.reverse < decBase ^ (1 + x.ds.length + x.ds.length / 99) := by
    rw [limbVal_nil, tv_reverse]
    exact Nat.lt_of_lt_of_le (val_lt hd) (cap_bound _)
  have hr : ∀ d ∈ x.ds.reverse, d < 2 ^ 30 := fun d h => hd d (List.mem_reverse.1 h)
  obtain ⟨r, e, hl, hn, hv⟩ := decLoop_spec _ x.ds.reverse [] hr (fun _ h => by simp at h)
    normal_nil hbound
  rw [limbVal_nil, tv_reverse] at hv
  have hshift : (33 * decShift) / (10 * 30 - 33 * decShift) = 99 := by decide
  obtain ⟨p, hpdef⟩ : ∃ p, p = if r.length = 0 then [0] else r := ⟨_, rfl⟩
  have hpne : p ≠ [] := by
    rw [hpdef]; split
    · simp
    · rename_i h; intro h'; rw [h'] at h; simp at h
  have hpl : Limbs p := by
    rw [hpdef]; split
    · intro y hy
      simp only [List.mem_singleton] at hy
      rw [hy, decBase_eq]; omega
    · exact hl
  have hpn : 1 < p.length → Normal p := by
    rw [hpdef]; split
    · simp
    · intro _; exact hn
  have hpv : limbVal decBase p = val x.ds := by
    rw [hpdef]; split
    · rename_i h
      have h0 : r = [] := List.length_eq_zero_iff.1 h
      rw [h0, limbVal_nil] at hv
      simp [limbVal_cons, limbVal_nil, ← hv]
    · exact hv
  obtain ⟨hw, hlen⟩ := writeLimbs_spec p [] hpne hpl hpn
  have htop : p.getLastD 0 < 10 ^ 9 := by
    have : p.getLastD 0 ∈ p := by
      obtain ⟨q, t, rfl⟩ : ∃ q t, p = q ++ [t] :=
        ⟨p.dropLast, p.getLast hpne, (List.dropLast_concat_getLast hpne).symm⟩
      simp
    exact hpl _ this
  obtain ⟨hk, hll⟩ := lenLoop_spec htop 11 1 0 (by omega) (by omega) (by omega) (Or.inl rfl)
  rw [Nat.pow_one, Nat.zero_add] at hll
  rw [hpv] at hw hlen
  obtain ⟨D, hD⟩ : ∃ D, (Nat.toDigits 10 (val x.ds)).length = D := ⟨_, rfl⟩
  rw [hD] at hlen
  obtain ⟨N, hN⟩ : ∃ N, (if x.neg then 1 else 0) = N := ⟨_, rfl⟩
  have hstr : N + 1 + (p.length - 1) * decShift + ((Nat.toDigits 10 (p.getLastD 0)).length - 1)
      = N + D := by omega
  unfold decCore
  simp only [hshift, longAlloc_ok hs, bindOk, e, ← hpdef, hll, hN, hstr, Nat.add_sub_cancel_left,
    hD]
  by_cases hc : N + D > strDigitsThreshold ∧ lim > 0 ∧ D > lim
  · rw [if_pos hc, if_pos hc]
    rfl
  · rw [if_neg hc, if_neg hc]
    simp only [hw, bindOk, List.append_nil]
    have hlenfinal : (if x.neg = true then '-' :: Nat.toDigits 10 (val x.ds)
        else Nat.toDigits 10 (val x.ds)).length = N + D := by
      cases h : x.neg <;> simp [h] at hN ⊢ <;> omega
    rw [if_pos hlenfinal]
    cases h : x.neg <;> simp [pureOk]

/-! ## The pre-check -/

/-- The pre-check rejects only values past the limit: `10/3 >= log2(10)`. -/
theorem decPreCheck_sound {lim V : Nat} (hlim : 0 < lim) (hV : 1 ≤ V)
    (hs : lim / (3 * 30) ≤ (digitCount V - 11) / 10)
    (hs2 : 11 ≤ digitCount V) : (Nat.toDigits 10 V).length > lim := by
  have h1 : (10 : Nat) ^ 90 ≤ 2 ^ 300 := by decide +kernel
  obtain ⟨_, hbig⟩ := (digitCount_spec V).2 hV
  obtain ⟨s, hsdef⟩ : ∃ s, digitCount V = s := ⟨_, rfl⟩
  rw [hsdef] at hs hs2 hbig
  obtain ⟨k, hk⟩ : ∃ k, (s - 11) / 10 = k := ⟨_, rfl⟩
  rw [hk] at hs
  have hlim2 : lim < 90 * (k + 1) := by omega
  have hsk : 300 * (k + 1) ≤ 30 * (s - 1) := by omega
  apply Nat.lt_of_not_le
  intro hle
  have hlt : V < 10 ^ lim := (Nat.length_toDigits_le_iff (by decide) hlim).1 hle
  have h2 : 10 ^ lim ≤ 2 ^ (30 * (s - 1)) := by
    calc 10 ^ lim ≤ 10 ^ (90 * (k + 1)) := Nat.pow_le_pow_right (by decide) (by omega)
      _ = (10 ^ 90) ^ (k + 1) := Nat.pow_mul ..
      _ ≤ (2 ^ 300) ^ (k + 1) := Nat.pow_le_pow_left h1 _
      _ = 2 ^ (300 * (k + 1)) := (Nat.pow_mul ..).symm
      _ ≤ 2 ^ (30 * (s - 1)) := Nat.pow_le_pow_right (by decide) hsk
  omega

/-! ## Power-of-two bases -/

theorem hexCharC_eq : ∀ d, d < 16 → hexCharC d = d.digitChar := by decide

theorem shrBase {base bits : Nat} (hb : base = 2 ^ bits) (x : Nat) : x >>> bits = x / base := by
  rw [hb, Nat.shiftRight_eq_div_pow]

theorem fmtWhile_step {base bits : Nat} (hb : base = 2 ^ bits) (h4 : base ≤ 16)
    (last : Bool) (f accum ab : Nat) (acc : List Char) :
    fmtWhile base bits last (f + 1) accum ab acc =
      if (if last then decide (accum / base > 0) else decide (ab - bits ≥ bits)) = true then
        fmtWhile base bits last f (accum / base) (ab - bits) ((accum % base).digitChar :: acc)
      else .ok (accum / base, ab - bits, (accum % base).digitChar :: acc) := by
  have h1 : accum &&& (base - 1) = accum % base := by
    subst hb; exact Nat.and_two_pow_sub_one_eq_mod accum bits
  have hpos : 0 < base := by rw [hb]; exact Nat.pow_pos (by decide)
  have h2 := hexCharC_eq (accum % base) (Nat.lt_of_lt_of_le (Nat.mod_lt _ hpos) h4)
  rw [fmtWhile]
  simp only [h1, h2, shrBase hb]

theorem fmtWhile_mid {base bits : Nat} (hb : base = 2 ^ bits) (h1 : 1 ≤ bits) (h4 : base ≤ 16) :
    ∀ k f accum r acc, r < bits →
      fmtWhile base bits false (f + k + 1) accum ((k + 1) * bits + r) acc =
        .ok (accum / base ^ (k + 1), r, zdigits base (k + 1) accum ++ acc) := by
  intro k
  induction k with
  | zero =>
    intro f accum r acc hr
    rw [fmtWhile_step hb h4]
    have e : (0 + 1) * bits + r - bits = r := by omega
    have hn : ¬ (decide (r ≥ bits) = true) := by simp; omega
    simp only [e, hn, Bool.false_eq_true, if_false, ite_false, Nat.pow_one, zdigits]
    simp [zdigits]
  | succ k ih =>
    intro f accum r acc hr
    rw [show f + (k + 1) + 1 = (f + k + 1) + 1 by omega, fmtWhile_step hb h4]
    have e : (k + 1 + 1) * bits + r - bits = (k + 1) * bits + r := by
      rw [Nat.add_mul (k + 1) 1 bits]; omega
    have hge : (k + 1) * bits + r ≥ bits := by
      rw [Nat.add_mul k 1 bits]; omega
    simp only [e, hge, decide_true, ite_true, if_true, Bool.false_eq_true, ite_false]
    rw [ih f (accum / base) r _ hr]
    have hd : accum / base / base ^ (k + 1) = accum / base ^ (k + 1 + 1) := by
      rw [Nat.div_div_eq_div_mul, Nat.pow_succ' (n := k + 1)]
    rw [hd]
    simp [zdigits, List.append_assoc]

theorem fmtWhile_last {base bits : Nat} (hb : base = 2 ^ bits) (h2 : 2 ≤ base) (h4 : base ≤ 16)
    (f : Nat) : ∀ accum ab acc, 0 < accum → accum < base ^ (f + 1) →
      ∃ ab', fmtWhile base bits true (f + 1) accum ab acc =
        .ok (0, ab', Nat.toDigits base accum ++ acc) := by
  induction f with
  | zero =>
    intro accum ab acc _ hlt
    have h : accum < base := by simpa using hlt
    have hd : accum / base = 0 := Nat.div_eq_of_lt h
    have hm : accum % base = accum := Nat.mod_eq_of_lt h
    refine ⟨ab - bits, ?_⟩
    rw [fmtWhile_step hb h4]
    simp [hd, hm, Nat.toDigits_of_lt_base h]
  | succ f ih =>
    intro accum ab acc hpos hlt
    by_cases h : accum < base
    · have hd : accum / base = 0 := Nat.div_eq_of_lt h
      have hm : accum % base = accum := Nat.mod_eq_of_lt h
      refine ⟨ab - bits, ?_⟩
      rw [fmtWhile_step hb h4]
      simp [hd, hm, Nat.toDigits_of_lt_base h]
    · have hge : base ≤ accum := by omega
      have hdpos : 0 < accum / base := Nat.div_pos hge (by omega)
      have hdlt : accum / base < base ^ (f + 1) := by
        apply Nat.div_lt_of_lt_mul
        rw [Nat.pow_succ base (f + 1), Nat.mul_comm] at hlt
        exact hlt
      obtain ⟨ab', e⟩ := ih (accum / base) (ab - bits) ((accum % base).digitChar :: acc) hdpos hdlt
      refine ⟨ab', ?_⟩
      rw [fmtWhile_step hb h4]
      simp only [hdpos, decide_true, ite_true, if_true, gt_iff_lt]
      rw [e, Nat.toDigits_of_base_le (by omega) hge]
      simp [List.append_assoc]

theorem or_shift_eq {accum d ab : Nat} (h : accum < 2 ^ ab) :
    accum ||| (d <<< ab) = accum + 2 ^ ab * d := by
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt h, Nat.shiftLeft_eq, Nat.add_comm,
    Nat.mul_comm]

theorem fmtLoop_spec {base bits : Nat} (hb : base = 2 ^ bits) (h1 : 1 ≤ bits) (h4 : base ≤ 16) :
    ∀ (ds : List Nat) (accum ab : Nat) (acc : List Char), ds ≠ [] → IsDigits ds → Normal ds →
      ab < bits → accum < 2 ^ ab →
      fmtLoop base bits ds accum ab acc =
        .ok (Nat.toDigits base (accum + 2 ^ ab * val ds) ++ acc)
  | [], _, _, _, h, _, _, _, _ => absurd rfl h
  | d :: ds, accum, ab, acc, _, hd, hn, hab, hacc => by
    have hbits : bits ≤ 4 := by
      apply Nat.le_of_not_lt
      intro hc
      have : 2 ^ 5 ≤ 2 ^ bits := Nat.pow_le_pow_right (by decide) hc
      omega
    have h2 : 2 ≤ base := by
      rw [hb]
      exact Nat.le_trans (by decide) (Nat.pow_le_pow_right (by decide) h1)
    obtain ⟨hd0, hds⟩ := isDigits_cons.1 hd
    obtain ⟨a, ha⟩ : ∃ a, accum + 2 ^ ab * d = a := ⟨_, rfl⟩
    have hlt : a < 2 ^ (ab + 30) := by
      rw [← ha, Nat.pow_add]
      have : 2 ^ ab * (d + 1) ≤ 2 ^ ab * 2 ^ 30 := Nat.mul_le_mul_left _ hd0
      rw [Nat.mul_add] at this
      omega
    have h64 : a < 2 ^ 64 :=
      Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) (by omega))
    have hor : accum ||| (d <<< ab) = a := by rw [or_shift_eq hacc, ha]
    by_cases hne : ds = []
    · subst hne
      have hd1 : d ≠ 0 := by simpa using hn (by simp)
      have hapos : 0 < a := by
        rw [← ha]
        have : 0 < 2 ^ ab * d := Nat.mul_pos (Nat.pow_pos (by decide)) (by omega)
        omega
      have hlt64 : a < base ^ (63 + 1) := Nat.lt_of_lt_of_le h64 (Nat.pow_le_pow_left h2 _)
      obtain ⟨ab', e⟩ := fmtWhile_last hb h2 h4 63 a (ab + 30) acc hapos hlt64
      have ev : accum + 2 ^ ab * val [d] = a := by
        rw [← ha]; simp [val_cons]
      rw [ev]
      simp only [fmtLoop, hor, chk64_ok h64, bindOk, List.isEmpty_nil, e]
    · obtain ⟨k, r, hk, hr⟩ : ∃ k r, ab + 30 = (k + 1) * bits + r ∧ r < bits := by
        refine ⟨(ab + 30) / bits - 1, (ab + 30) % bits, ?_, Nat.mod_lt _ (by omega)⟩
        have hdm := Nat.div_add_mod (ab + 30) bits
        have hq : 1 ≤ (ab + 30) / bits := Nat.div_pos (by omega) (by omega)
        rw [Nat.sub_add_cancel hq, Nat.mul_comm]
        exact hdm.symm
      have hkf : k + 1 ≤ 34 := by
        have : (k + 1) * 1 ≤ (k + 1) * bits := Nat.mul_le_mul_left _ h1
        omega
      obtain ⟨g, hg⟩ : ∃ g, 64 = g + k + 1 := ⟨64 - k - 1, by omega⟩
      have ew := fmtWhile_mid hb h1 h4 k g a r acc hr
      have hP : 2 ^ (ab + 30) = base ^ (k + 1) * 2 ^ r := by
        rw [hb, ← Nat.pow_mul, ← Nat.pow_add, hk, Nat.mul_comm bits]
      have hPpos : 0 < base ^ (k + 1) := Nat.pow_pos (by omega)
      have hdiv : a / base ^ (k + 1) < 2 ^ r := by
        apply Nat.div_lt_of_lt_mul
        rw [← hP]; exact hlt
      have hN' := normal_of_cons hn
      have hpos : 0 < val ds := by
        rcases Nat.eq_zero_or_pos (val ds) with h0 | h0
        · exact absurd (eq_nil_of_val_zero hN' h0) hne
        · exact h0
      have ih := fmtLoop_spec hb h1 h4 ds (a / base ^ (k + 1)) r (zdigits base (k + 1) a ++ acc) hne
        hds hN' hr hdiv
      have htotal : accum + 2 ^ ab * val (d :: ds) =
          (a / base ^ (k + 1) + 2 ^ r * val ds) * base ^ (k + 1) + a % base ^ (k + 1) := by
        rw [val_cons, Nat.mul_add, ← Nat.add_assoc, ha, ← Nat.mul_assoc, ← Nat.pow_add, hP,
          Nat.add_mul, Nat.mul_comm (2 ^ r), Nat.mul_assoc (base ^ (k + 1)),
          Nat.mul_comm (base ^ (k + 1)), Nat.mul_comm (val ds)]
        have := Nat.div_add_mod a (base ^ (k + 1))
        rw [Nat.mul_comm (base ^ (k + 1))] at this
        omega
      have hzd : zdigits base (k + 1) a = zdigits base (k + 1) (a % base ^ (k + 1)) := by
        have := zdigits_add_mul (b := base) (by omega) (k + 1) (a % base ^ (k + 1))
          (a / base ^ (k + 1))
        rw [Nat.mod_add_div] at this
        exact this
      have htp : 0 < a / base ^ (k + 1) + 2 ^ r * val ds := by
        have : 0 < 2 ^ r * val ds := Nat.mul_pos (Nat.pow_pos (by decide)) hpos
        exact Nat.add_pos_right _ this
      rw [htotal, toDigits_add_pow (by omega) (k + 1) _ _ htp (Nat.mod_lt _ hPpos), ← hzd]
      have hemp : ds.isEmpty = false := by
        cases ds with
        | nil => exact absurd rfl hne
        | cons _ _ => rfl
      simp only [fmtLoop, hor, chk64_ok h64, bindOk, hemp]
      rw [show ab + 30 = (k + 1) * bits + r from hk, hg, ew]
      simp only [bindOk, ih, List.append_assoc]

/-- `size_a_in_bits` rounded up to characters is the number of characters. -/
theorem length_toDigits_binary {base bits V T : Nat} (hb : base = 2 ^ bits) (h1 : 1 ≤ bits)
    (hbits : bits ≤ 4) (hT : 1 ≤ T) (hlo : 2 ^ (T - 1) ≤ V) (hhi : V < 2 ^ T) :
    (Nat.toDigits base V).length = (T + (bits - 1)) / bits := by
  have h2 : 1 < base := by
    rw [hb]
    exact Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide) h1)
  obtain ⟨L, hL⟩ : ∃ L, (T + (bits - 1)) / bits = L := ⟨_, rfl⟩
  have hLpos : 0 < L := by
    rw [← hL]; exact Nat.div_pos (by omega) (by omega)
  have hdm := Nat.div_add_mod (T + (bits - 1)) bits
  have hml := Nat.mod_lt (T + (bits - 1)) (show 0 < bits by omega)
  rw [hL] at hdm
  have hup : T ≤ bits * L := by omega
  have hlow : bits * (L - 1) ≤ T - 1 := by
    obtain ⟨M, rfl⟩ : ∃ M, L = M + 1 := ⟨L - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    rw [Nat.mul_add] at hdm
    omega
  rw [hL]
  apply Nat.le_antisymm
  · apply (Nat.length_toDigits_le_iff h2 hLpos).2
    calc V < 2 ^ T := hhi
      _ ≤ 2 ^ (bits * L) := Nat.pow_le_pow_right (by decide) hup
      _ = base ^ L := by rw [hb, Nat.pow_mul]
  · by_cases hL1 : L = 1
    · subst hL1
      exact List.length_pos_iff.2 Nat.toDigits_ne_nil
    · apply Nat.le_of_not_lt
      intro hc
      have hle : (Nat.toDigits base V).length ≤ L - 1 := by omega
      have := (Nat.length_toDigits_le_iff h2 (by omega : 0 < L - 1)).1 hle
      have h3 : base ^ (L - 1) ≤ 2 ^ (T - 1) := by
        rw [hb, ← Nat.pow_mul]
        exact Nat.pow_le_pow_right (by decide) hlow
      omega

/-- `long_format_binary` writes exactly `sz` characters: the digits of the value in
base 2, 8 or 16, with the sign and optional prefix. -/
theorem longFormatBinary_spec (x : Long) (base : Nat) (alt : Bool)
    (hbase : base = 2 ∨ base = 8 ∨ base = 16) (hd : IsDigits x.ds) (hn : Normal x.ds)
    (hz : x.neg = true → x.ds ≠ []) (hs : x.ds.length ≤ maxLongDigits) :
    longFormatBinary x base alt = .ok ((if x.neg then ['-'] else []) ++
      (if alt then ['0', if base = 16 then 'x' else if base = 8 then 'o' else 'b'] else []) ++
      Nat.toDigits base (val x.ds)) := by
  obtain ⟨bits, hbits, h1, h4, hb4⟩ : ∃ bits, (if base = 16 then 4 else if base = 8 then 3 else 1)
      = bits ∧ 1 ≤ bits ∧ bits ≤ 4 ∧ base = 2 ^ bits := by
    rcases hbase with rfl | rfl | rfl
    · exact ⟨1, by decide, by decide, by decide, by decide⟩
    · exact ⟨3, by decide, by decide, by decide, by decide⟩
    · exact ⟨4, by decide, by decide, by decide, by decide⟩
  have h16 : base ≤ 16 := by rcases hbase with rfl | rfl | rfl <;> decide
  have hne : ¬ x.ds.length > (ssizeMax - 3) / 30 := by
    have : (ssizeMax - 3) / 30 = maxLongDigits := by decide
    omega
  by_cases h0 : x.ds = []
  · have hneg : x.neg = false := by
      cases h : x.neg with
      | false => rfl
      | true => exact absurd h0 (hz h)
    unfold longFormatBinary
    simp only [h0, List.length_nil, hneg, hbits, val_nil, Bool.false_eq_true, if_false, if_true,
      pureOk, bindOk, Nat.toDigits_zero]
    cases alt <;> simp [pureOk, bindOk]
  · obtain ⟨l, t, hl⟩ : ∃ l t, x.ds = l ++ [t] :=
      ⟨x.ds.dropLast, x.ds.getLast h0, (List.dropLast_concat_getLast h0).symm⟩
    have hNl : Normal (l ++ [t]) := hl ▸ hn
    have ht : t ≠ 0 := by simpa using hNl (by simp)
    have hld : IsDigits l := (isDigits_append.1 (hl ▸ hd)).1
    have hlast : x.ds.getLastD 0 = t := by rw [hl]; simp
    have hV : val x.ds = val l + 2 ^ (30 * l.length) * t := by
      rw [hl, val_append]; simp
    have hbit : bitLength (val x.ds) = 30 * l.length + bitLength t := by
      rw [hV]
      exact bitLength_add_shift _ _ _ (val_lt hld) (by omega)
    have hlen : x.ds.length = l.length + 1 := by rw [hl]; simp
    have hVpos : 1 ≤ val x.ds := by
      rw [hV]
      have : 0 < 2 ^ (30 * l.length) * t := Nat.mul_pos (Nat.pow_pos (by decide)) (by omega)
      omega
    obtain ⟨b1, b2⟩ := bitLength_bounds _ hVpos
    have hT1 : 1 ≤ bitLength (val x.ds) := by
      rw [hbit]
      have : 1 ≤ bitLength t := (bitLength_facts t).2.1 (by omega) |>.2
      omega
    have hsz := length_toDigits_binary hb4 h1 h4 hT1 b1 b2
    have hsz' : ((x.ds.length - 1) * 30 + bitLengthDigit (x.ds.getLastD 0) + (bits - 1)) / bits =
        (Nat.toDigits base (val x.ds)).length := by
      rw [hsz, hbit, hlast, hlen, Nat.add_sub_cancel, Nat.mul_comm l.length 30]
      rfl
    have hloop := fmtLoop_spec hb4 h1 h16 x.ds 0 0 [] h0 hd hn (by omega) (by decide)
    rw [Nat.pow_zero, Nat.one_mul, Nat.zero_add, List.append_nil] at hloop
    have hs1 : x.ds.length ≠ 0 := by omega
    obtain ⟨D, hD⟩ : ∃ D, Nat.toDigits base (val x.ds) = D := ⟨_, rfl⟩
    rw [hD] at hloop hsz' ⊢
    unfold longFormatBinary
    simp only [hbits, if_neg hs1, if_neg hne, pureOk, bindOk, hsz', hloop]
    cases hneg : x.neg <;> cases alt <;> simp [pureOk]
    all_goals omega

end PyLean.LongObj
