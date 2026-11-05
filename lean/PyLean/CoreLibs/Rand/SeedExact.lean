import PyLean.CoreLibs.Rand.SeedProps

/-!
What `Random.seed` passes to `super().seed` (Lib/random.py:146-174), and `__getstate__`.
-/

namespace PyLean.CoreLibs.Rand

open PyLean

variable {F : Type}

/-- `Random.seed(a, version)` hands `super().seed` (the C `random_seed`) exactly:
`None` as `None`; an `int` as itself (a subclass such as `bool` as a subclass instance);
a `float` as an object hashed by `hash(a)`; for version 1, a `str` or `bytes` as the int
of the version 1 string hash of its code points (`bytes` decoded as Latin-1); for
version 2, a `str` (UTF-8 encoded, a lone surrogate raising `UnicodeEncodeError`),
`bytes` or `bytearray` `b` as `int.from_bytes(b + sha512(b).digest())`; for any other
version a `str` or `bytes` as itself (hashed) and a `bytearray` as itself (unhashable, so
the C code raises `TypeError`); and any other type is the `TypeError` before the C call.
After a successful C call the object holds the new state and `gauss_next = None`; when
anything raises, the object is unchanged. -/
def SeedReaches : Prop :=
  ∀ (F : Type) (ent : Entropy) (o : Obj F),
    (∀ (a : SeedArg) (v : Int), pySeed ent a v o =
      match seedConvert a v with
      | .error e => (.error e, o)
      | .ok c =>
        match randomSeed o.core c ent with
        | .error e => (.error e, o)
        | .ok s => (.ok (), { core := s, gaussNext := none })) ∧
    (∀ v, seedConvert .none v = .ok .none) ∧
    (∀ v n, seedConvert (.int n) v = .ok (.exactInt n)) ∧
    (∀ v n, seedConvert (.intSub n) v = .ok (.intSubclass n)) ∧
    (∀ v h, seedConvert (.float h) v = .ok (.hashable h)) ∧
    (∀ cps h, seedConvert (.str cps h) 1 = .ok (.exactInt (seedV1 cps))) ∧
    (∀ b h, seedConvert (.bytes b h) 1 = .ok (.exactInt (seedV1 b))) ∧
    (∀ cps h, seedConvert (.str cps h) 2 =
      (do let b ← utf8Encode cps; pure (.exactInt ((fromBytesBE (b ++ Sha512.digest b) : Nat) : Int)))) ∧
    (∀ b h, seedConvert (.bytes b h) 2 = .ok (.exactInt (fromBytesBE (b ++ Sha512.digest b) : Nat))) ∧
    (∀ b, seedConvert (.bytearray b) 2 = .ok (.exactInt (fromBytesBE (b ++ Sha512.digest b) : Nat))) ∧
    (∀ v cps h, v ≠ 1 → v ≠ 2 → seedConvert (.str cps h) v = .ok (.hashable h)) ∧
    (∀ v b h, v ≠ 1 → v ≠ 2 → seedConvert (.bytes b h) v = .ok (.hashable h)) ∧
    (∀ v b, v ≠ 2 → seedConvert (.bytearray b) v = .ok (.unhashable "bytearray")) ∧
    (∀ v, seedConvert .other v =
      .error (.typeError "The only supported seed types are:\nNone, int, float, str, bytes, and bytearray."))

theorem seedReaches_proven : SeedReaches := by
  intro F ent o
  refine ⟨fun a v => ?_, fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl, fun _ _ => rfl, fun cps h => ?_, fun _ _ => rfl, fun _ => rfl,
    fun v cps h h1 h2 => ?_, fun v b h h1 h2 => ?_, fun v b h1 => ?_, fun _ => rfl⟩
  · simp only [pySeed]
    cases seedConvert a v with
    | error e => rfl
    | ok c => rfl
  · simp only [seedConvert, if_neg (show (2 : Int) ≠ 1 by decide), if_pos rfl, seedV2, ite_true]
  · simp only [seedConvert, if_neg h1, if_neg h2]
  · simp only [seedConvert, if_neg h1, if_neg h2]
  · simp only [seedConvert, if_neg h1]

/-- `__getstate__` (Lib/random.py:213-214) returns `self.getstate()`, so the dunder pair
round-trips like the public one: `__setstate__(__getstate__())` restores the object
exactly, `gauss_next` included, from any valid state, whatever the target held. (Pickling
itself goes through `__reduce__`; this is the protocol a caller that uses the dunders
directly, or a subclass that drops `__reduce__`, relies on.) -/
def DunderStateRoundTrip : Prop :=
  ∀ (F : Type) (o o' : Obj F), o.core.WF →
    pyDunderGetstate o = pyGetstate o ∧
    pyDunderSetstate (pyDunderGetstate o).toArg o' = (.ok (), o)

theorem dunderStateRoundTrip_proven : DunderStateRoundTrip :=
  fun _ o o' h => ⟨rfl, stateRoundTrip_one o o' h⟩

end PyLean.CoreLibs.Rand
