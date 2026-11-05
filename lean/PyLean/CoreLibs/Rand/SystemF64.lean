import PyLean.CoreLibs.Rand.SystemProps
import PyLean.CoreLibs.Rand.DistFormula

/-!
`SystemRandom` (Lib/random.py:895-931), `Random.__init_subclass__` and `main --test`,
over binary64.

`SystemRandom` reads `os.urandom`, an abstract `raw` with the contract `RawValid` (`n`
bytes, each below 256). Each statement says what the method returns as a function of the
bytes `raw` gives, so a method that read a different number of bytes, kept other bits,
or raised where CPython returns, fails it.
-/

namespace PyLean.CoreLibs.Rand

open PyLean PyLean.Binary64 PyLean.Binary64.F64 RM Flt

/-! ### `SystemRandom.random`, Lib/random.py:906-908 -/

theorem recip_bpf [RandLibm] :
    (1.1102230246251565e-16 : F64).isFinite = true ∧ (1.1102230246251565e-16 : F64).toRat = pw (-53) := by
  show (F64R.ofDecimal 11102230246251565 true 32).isFinite = true ∧
    (F64R.ofDecimal 11102230246251565 true 32).toRat = pw (-53)
  decide +kernel

/-- `SystemRandom.random()` reads exactly `os.urandom(7)` and returns
`(int.from_bytes(b) >> 3) * 2 ** -53`, which is exact: the numerator is below `2 ** 53`,
so the result is the rational `m / 2 ** 53` in `[0, 1)`. An `os.urandom` failure
propagates. -/
def SysRandomExact : Prop :=
  ∀ [RandLibm] (σ : Type) (raw : Nat → RM σ (List Nat)), RawValid raw → ∀ s : σ,
    (∀ e s', raw 7 s = (.error e, s') → (sysRandom raw : RM σ F64) s = (.error e, s')) ∧
    (∀ b s', raw 7 s = (.ok b, s') → ∃ x : F64, (sysRandom raw : RM σ F64) s = (.ok x, s') ∧
      x.isFinite = true ∧ x.toRat = ((fromBytesBE b >>> 3 : Nat) : Rat) / 9007199254740992 ∧
      fromBytesBE b >>> 3 < 2 ^ 53)

theorem urandom7 {σ : Type} (raw : Nat → RM σ (List Nat)) :
    osUrandom raw (.int 7) = raw 7 := by
  simp only [osUrandom, RM.bind_apply]
  funext s
  simp [IntArg.index, ssizeMax, ssizeMin, RM.lift_apply]

theorem sysRandomExact_proven : SysRandomExact := by
  intro _ σ raw hraw s
  have hdef : (sysRandom raw : RM σ F64) s =
      (sysRandomNum raw >>= fun m => RM.lift (pyFloat (m : Int)) >>= fun x =>
        Pure.pure (x * 1.1102230246251565e-16)) s := rfl
  have hnum : sysRandomNum raw = (raw 7 >>= fun b => Pure.pure (fromBytesBE b >>> 3)) := by
    unfold sysRandomNum; rw [urandom7]
  refine ⟨fun e s' h => ?_, fun b s' h => ?_⟩
  · rw [hdef, hnum]
    simp only [RM.bind_apply, h]
  · obtain ⟨hlen, hbytes⟩ := hraw 7 s b s' h
    have hlt := fromBytesBE_lt b hbytes
    rw [hlen] at hlt
    have hm : fromBytesBE b >>> 3 < 2 ^ 53 := by
      rw [Nat.shiftRight_eq_div_pow]
      apply Nat.div_lt_of_lt_mul
      have : (2 : Nat) ^ 3 * 2 ^ 53 = 256 ^ 7 := by decide
      omega
    generalize hM : fromBytesBE b >>> 3 = m at hm ⊢
    have hsm : (m : Int).natAbs < 2 ^ 53 := by simpa using hm
    obtain ⟨hf, hv⟩ := ofInt_small hsm
    rw [Rat.intCast_natCast] at hv
    have hoi : (Flt.ofInt (m : Int) : Option F64) = some (F64.ofInt m) := by
      show F64R.ofIntOpt _ = _
      simp [F64R.ofIntOpt, isInf_false_of_finite hf]
    have hpf : (pyFloat (m : Int) : Py F64) = .ok (F64.ofInt m) := by simp [pyFloat, hoi]
    obtain ⟨cf, cv⟩ := recip_bpf
    have hp : pw (-53) * 9007199254740992 = 1 := by decide +kernel
    have hp0 : (0 : Rat) < pw (-53) := pw_pos _
    have hmr : (m : Rat) < 9007199254740992 := by
      have := Rat.natCast_lt_natCast.2 hm
      simpa using this
    have hm0 : (0 : Rat) ≤ (m : Rat) := Rat.natCast_nonneg
    have h1 := abs_toRat_lt (show F64.one.isFinite = true by decide +kernel)
    rw [show F64.one.toRat = 1 by decide +kernel, abs_of_nonneg (by decide)] at h1
    have hq0 : (0 : Rat) ≤ (m : Rat) * pw (-53) := Rat.mul_nonneg hm0 (Rat.le_of_lt hp0)
    have hq1 : (m : Rat) * pw (-53) < 1 := by
      have := Rat.mul_lt_mul_of_pos_right hmr hp0
      rw [Rat.mul_comm 9007199254740992, hp] at this
      exact this
    have hlim : Rat.abs ((m : Rat) * pw (-53)) < overflowLimit := by
      rw [abs_of_nonneg hq0]; grind
    have hval : (m : Rat) * pw (-53) = (m : Rat) / 9007199254740992 := by
      have hN : (9007199254740992 : Rat) ≠ 0 := by decide
      rw [Rat.div_def]
      have : pw (-53) = (9007199254740992 : Rat)⁻¹ := by decide +kernel
      rw [this]
    refine ⟨F64.mul (F64.ofInt m) 1.1102230246251565e-16, ?_, ?_, ?_, hm⟩
    · rw [hdef, hnum]
      simp only [RM.bind_apply, h, RM.pure_apply, hM, RM.lift_apply, hpf]
      rfl
    · rw [F64Order.mul_eq hf cf]
      apply F64Order.rnd_isFinite
      rw [hv, cv]; exact hlim
    · rw [F64Order.mul_eq hf cf, hv, cv, ← hval]
      unfold F64Order.rnd
      by_cases h0 : (m : Rat) * pw (-53) = 0
      · rw [if_pos h0, zero_toRat, h0]
      · rw [if_neg h0]
        have hrep : Rep binary64 ((m : Rat) * pw (-53)) := ⟨m, -53, hm, by decide, Or.inl rfl⟩
        exact ofRat_exact hrep hlim

/-! ### `SystemRandom.getrandbits`, Lib/random.py:910-916 -/

/-- `SystemRandom.getrandbits(k)`: a negative `k`, `int` or `float`, raises the
`ValueError` before any read; an `int` `k >= 0` reads exactly `(k + 7) // 8` bytes and
returns `int.from_bytes(b) >> (numbytes * 8 - k)`, which is below `2 ** k`; a float
`k >= 0` (or NaN) raises `TypeError` from `os.urandom`. -/
def SysGetrandbitsExact : Prop :=
  ∀ [RandLibm] (σ : Type) (raw : Nat → RM σ (List Nat)), RawValid raw →
    (∀ (k : Int) (s : σ), k < 0 → sysGetrandbitsArg raw (.arg (.int k) : SysBitsArg F64) s =
      (.error (.valueError "number of bits must be non-negative"), s)) ∧
    (∀ (k : Nat) (s : σ), (((k : Int) + 7) / 8) ≤ ssizeMax →
      sysGetrandbitsArg raw (.arg (.int k) : SysBitsArg F64) s =
        match raw ((k + 7) / 8) s with
        | (.ok b, s') => (.ok (fromBytesBE b >>> ((k + 7) / 8 * 8 - k)), s')
        | (.error e, s') => (.error e, s')) ∧
    (∀ (k r : Nat) (s s' : σ), sysGetrandbitsArg raw (.arg (.int k) : SysBitsArg F64) s = (.ok r, s') →
      r < 2 ^ k) ∧
    (∀ (x : F64) (s : σ), Flt.lt x 0.0 = true → sysGetrandbitsArg raw (.flt x) s =
      (.error (.valueError "number of bits must be non-negative"), s)) ∧
    (∀ (x : F64) (s : σ), Flt.lt x 0.0 = false → sysGetrandbitsArg raw (.flt x) s =
      (.error (.typeError "'float' object cannot be interpreted as an integer"), s))

theorem sysGetrandbitsExact_proven : SysGetrandbitsExact := by
  intro _ σ raw hraw
  obtain ⟨hvalid, hneg⟩ := sysGetrandbitsBound_proven σ F64 raw hraw
  refine ⟨fun k s h => hneg k s h, fun k s hk => ?_, fun k r s s' h => hvalid k r s s' h,
    fun x s h => ?_, fun x s h => ?_⟩
  · have hdef : sysGetrandbitsArg raw (.arg (.int (k : Int)) : SysBitsArg F64) =
        (osUrandom raw (.int (((k : Int) + 7) / 8)) >>= fun b =>
          Pure.pure (fromBytesBE b >>> (((k : Int) + 7) / 8 * 8 - k).toNat)) := by
      simp only [sysGetrandbitsArg, sysGetrandbits]
      rfl
    have hu : osUrandom raw (.int (((k : Int) + 7) / 8)) = raw ((k + 7) / 8) := by
      funext t
      simp only [osUrandom, RM.bind_apply, IntArg.index, RM.lift_apply]
      rw [if_neg (by simp only [ssizeMin] at *; omega), if_neg (by omega)]
      have e : (((k : Int) + 7) / 8).toNat = (k + 7) / 8 := by omega
      rw [e]
    rw [hdef, hu, RM.bind_apply]
    have hsh : (((k : Int) + 7) / 8 * 8 - k).toNat = (k + 7) / 8 * 8 - k := by omega
    cases raw ((k + 7) / 8) s with
    | mk r t => cases r <;> simp [hsh]
  · simp only [sysGetrandbitsArg, h, if_true]; rfl
  · simp only [sysGetrandbitsArg, h, Bool.false_eq_true, if_false]; rfl

/-! ### `SystemRandom.randbytes`, Lib/random.py:918-922 -/

/-- `SystemRandom.randbytes(n)` is `os.urandom(n)`: for an `int` `n` in `Py_ssize_t`
range, a negative one raises `ValueError` before any read and a non-negative one returns
exactly the `n` bytes the operating system gives; a larger one raises `OverflowError`
and a non-integer `TypeError`. -/
def SysRandbytesExact : Prop :=
  ∀ (σ : Type) (raw : Nat → RM σ (List Nat)) (s : σ),
    (∀ n : Int, ssizeMin ≤ n → n < 0 → sysRandbytes raw (.int n) s =
      (.error (.valueError "size cannot be negative"), s)) ∧
    (∀ n : Int, 0 ≤ n → n ≤ ssizeMax → sysRandbytes raw (.int n) s = raw n.toNat s) ∧
    (∀ n : Int, ssizeMax < n → sysRandbytes raw (.int n) s =
      (.error (.overflowError "Python int too large to convert to C ssize_t"), s)) ∧
    (∀ ty : String, sysRandbytes raw (.other ty) s =
      (.error (.typeError s!"'{ty}' object cannot be interpreted as an integer"), s))

theorem sysRandbytesExact_proven : SysRandbytesExact := by
  intro σ raw s
  have hdef : ∀ n : Int, sysRandbytes raw (.int n) =
      (if n > ssizeMax ∨ n < ssizeMin then
        RM.raise (.overflowError "Python int too large to convert to C ssize_t")
       else if n < 0 then RM.raise (.valueError "size cannot be negative")
       else raw n.toNat) := fun _ => rfl
  refine ⟨fun n h1 h2 => ?_, fun n h1 h2 => ?_, fun n h => ?_, fun ty => rfl⟩
  · rw [hdef, if_neg (by simp only [ssizeMax, ssizeMin] at *; omega), if_pos h2]; rfl
  · rw [hdef, if_neg (by simp only [ssizeMax, ssizeMin] at *; omega), if_neg (by omega)]
  · rw [hdef, if_pos (Or.inl h)]; rfl

/-! ### `SystemRandom.seed` and `_notimplemented`, Lib/random.py:924-931 -/

/-- `SystemRandom.seed(*args, **kwds)` returns `None` for every argument and reads no
entropy, so `SystemRandom(x)` (`Random.__init__` calling `self.seed(x)`) succeeds for every
`x`, including a type that `Random(x)` rejects with `TypeError`. -/
def SysSeedStub : Prop :=
  ∀ (σ : Type) (ent : Entropy) (s : σ),
    (∀ (β : Type) (args : β), (sysSeed args : RM σ Unit) s = (.ok (), s)) ∧
    (∀ x : SeedArg, (sysInit x : RM σ (Option F64)) s = (.ok none, s)) ∧
    ∃ e, (pyInit ent .other : Py (Obj F64)) = .error e ∧ e.className = "TypeError"

theorem sysSeedStub_proven : SysSeedStub := by
  intro σ ent s
  exact ⟨fun _ _ => rfl, fun _ => rfl, ⟨_, rfl, rfl⟩⟩

/-- `getstate` and `setstate` of `SystemRandom` are `_notimplemented`, which raises
`NotImplementedError('System entropy source does not have state.')` for every argument
without reading entropy; so `__reduce__`, and with it `pickle.dumps` and `copy.copy`,
raise the same. -/
def SysNotImplemented : Prop :=
  ∀ (σ : Type) (s : σ),
    (∀ (β α : Type) (args : β), (sysNotImplemented args : RM σ α) s =
      (.error (.named "NotImplementedError" "System entropy source does not have state."), s)) ∧
    (sysReduce : RM σ Unit) s =
      (.error (.named "NotImplementedError" "System entropy source does not have state."), s)

theorem sysNotImplemented_proven : SysNotImplemented := fun _ _ => ⟨fun _ _ _ => rfl, rfl⟩

/-! ### `Random.__init_subclass__`, Lib/random.py:225-243 -/

/-- The data model's convention for `__init_subclass__` (Doc/reference/datamodel.rst,
"Customizing class creation": "one should take out the needed keyword arguments and pass
the others over to the base class"): a hook passes control and the remaining keywords to
the next one in the MRO. Stated for `Random`'s hook: creating a class runs the same user
hooks, and raises the same `TypeError` for unexpected keywords, as it would without
`Random`'s hook in the chain. False: `Random.__init_subclass__` takes `**kwargs` and never
calls `super().__init_subclass__(**kwargs)`, so a mixin hook after `Random` in the MRO never
runs, and `class C(Random, flag=1)` succeeds where `object.__init_subclass__` would reject
`flag`. -/
def InitSubclassChains : Prop :=
  ∀ (cls : String) (mro : List ClsDict) (kwargs : List String) (rest : List SubclassHook),
    (runInitSubclass cls mro kwargs (.random :: rest)).map Prod.fst =
      (runInitSubclass cls mro kwargs rest).map Prod.fst

theorem initSubclassChains_refuted : ¬ InitSubclassChains := by
  intro h
  have := h "C" [] [] [.cooperative "M", .object]
  simp [runInitSubclass, Except.map, bind, Except.bind, pure, Except.pure] at this

/-- What `Random.__init_subclass__` does to the chain: the hooks before it run (they
chain to it), it assigns `_randbelow` from the MRO, and nothing after it runs, whatever
the keywords. -/
def InitSubclassStops : Prop :=
  ∀ (cls : String) (mro : List ClsDict) (kwargs : List String) (pre : List String)
    (rest : List SubclassHook),
    runInitSubclass cls mro kwargs (pre.map .cooperative ++ .random :: rest) =
      .ok (pre, initSubclass mro)

theorem initSubclassStops_proven : InitSubclassStops := by
  intro cls mro kwargs pre rest
  induction pre with
  | nil => rfl
  | cons n pre ih =>
    simp only [List.map_cons, List.cons_append, runInitSubclass, ih]
    rfl

/-! ### `main --test N`, Lib/random.py:1060-1062 -/

/-- `python -m random --test N` with `N < 2` raises `statistics.StatisticsError` from
`_test`: for `N <= 0` before any draw ("fmean requires at least one data point"), for
`N = 1` after one `random()` ("stdev requires at least two data points"); for `N >= 2` it
runs the rest of `_test` and returns `""`. -/
def MainTest : Prop :=
  ∀ [RandLibm] (σ : Type) (below : Nat → RM σ Nat) (g : Gen σ F64) (args : CliArgs F64) (h : String)
    (rest : Int → RM σ Unit) (t : Int) (s : σ),
    (args.choice = none ∨ args.choice = some []) → args.integer = none → args.float = none →
    args.test = some t →
    (t < 0 → cliMain below g args h rest s =
      (.error (.named "StatisticsError" "fmean requires at least one data point"), s)) ∧
    (t = 1 → ∀ u s1, g.random s = (u, s1) → cliMain below g args h rest s =
      (.error (.named "StatisticsError" "stdev requires at least two data points"), s1)) ∧
    (2 ≤ t → cliMain below g args h rest s =
      (rest t >>= fun _ => (Pure.pure (CliOut.str "") : RM σ (CliOut F64))) s)

theorem mainTest_proven : MainTest := by
  intro _ σ below g args h rest t s hc hi hf ht
  have hmain : t ≠ 0 → cliMain below g args h rest =
      (cliTest g rest t >>= fun _ => (Pure.pure (CliOut.str "") : RM σ (CliOut F64))) := by
    intro h0
    rcases hc with hc | hc <;> simp only [cliMain, hc, hi, hf, ht, if_pos h0]
  refine ⟨fun h0 => ?_, fun h1 u s1 hu => ?_, fun h2 => ?_⟩
  · rw [hmain (by omega)]
    simp only [cliTest, if_pos (show t ≤ 0 by omega), RM.bind_apply, RM.raise_apply]
  · rw [hmain (by omega)]
    subst h1
    simp only [cliTest, RM.bind_apply]
    simp [rnd, hu]
  · rw [hmain (by omega)]
    simp only [cliTest, if_neg (show ¬ t ≤ 0 by omega), if_neg (show ¬ t = 1 by omega)]

end PyLean.CoreLibs.Rand
