import PyLean.CoreLibs.Rand.ExactProps
import PyLean.CoreLibs.Rand.Seed

/-!
Properties of `Random.__init__`, `seed`, `getstate`, `setstate` and pickling in
`Lib/random.py`, and of `Random` as a core generator.
-/

namespace PyLean.CoreLibs.Rand

open PyLean Flt

variable {F : Type}

/-! ### `Random` as a generator -/

/-- `Random` meets the `getrandbits` contract for every allocator, and `random()`
uses exactly two words. -/
def MtGenValid : Prop :=
  ∀ (F : Type),
  ∀ [Flt F] (m : Nat → Bool),
    (mtGen (F := F) m).Valid ∧ (∀ s, ((mtGen (F := F) m).random s).2 = advance 2 s)

theorem mtGenValid_proven : MtGenValid := by
  intro F
  intro _ m
  refine ⟨?_, fun s => ?_⟩
  · intro k r s s' h
    simp only [mtGen] at h
    have hc : uint64Converter (.int (k : Int)) = (if (k : Int) ≥ 2 ^ 64 then
        .error (.overflowError "Python int too large for C uint64_t") else .ok k) := by
      simp only [uint64Converter, IntArg.index, bind, Except.bind]
      rw [if_neg (by omega)]
      split <;> simp
    rw [hc] at h
    by_cases hk : (k : Int) ≥ 2 ^ 64
    · rw [if_pos hk] at h
      cases h
    · rw [if_neg hk] at h
      exact getrandbitsBound_proven m k s s' r h
  · simp [mtGen, randomParts, advance]

/-- The argument conversion of `getrandbits(k)`: `k` goes through `__index__`, a
negative `k` is a `ValueError`, and `k ≥ 2**64` an `OverflowError`, all before any
draw. -/
def GetrandbitsArgErrors : Prop :=
  ∀ (F : Type),
  ∀ [Flt F] (m : Nat → Bool) (s : State),
    (∀ k : Int, k < 0 → (mtGen (F := F) m).getrandbits (.int k) s =
      (.error (.valueError "Cannot convert negative int"), s)) ∧
    (∀ k : Int, k ≥ 2 ^ 64 → (mtGen (F := F) m).getrandbits (.int k) s =
      (.error (.overflowError "Python int too large for C uint64_t"), s)) ∧
    (∀ ty : String, (mtGen (F := F) m).getrandbits (.other ty) s =
      (.error (.typeError s!"'{ty}' object cannot be interpreted as an integer"), s)) ∧
    (∀ b : Bool, (mtGen (F := F) m).getrandbits (.bool b) s =
      (mtGen (F := F) m).getrandbits (.int (if b then 1 else 0)) s) ∧
    (mtGen (F := F) m).getrandbits (.int 0) s = (.ok 0, s)

theorem getrandbitsArgErrors_proven : GetrandbitsArgErrors := by
  intro F
  intro _ m s
  refine ⟨fun k h => ?_, fun k h => ?_, fun ty => rfl, fun b => rfl, rfl⟩
  · simp only [mtGen, uint64Converter, IntArg.index, bind, Except.bind]
    rw [if_pos h]
  · simp only [mtGen, uint64Converter, IntArg.index, bind, Except.bind]
    rw [if_neg (by omega), if_pos h]

/-! ### `seed` -/

/-- `str`, `bytes` and `bytearray` seeds agree under version 2 (the default): a
string seeds like its UTF-8 bytes (Lib/random.py:165-167). A lone surrogate has no
UTF-8 form and raises `UnicodeEncodeError` before anything is written. -/
def SeedStrBytesAgree : Prop :=
  ∀ (F : Type),
  ∀ (ent : Entropy) (cps b : List Nat) (h h' : Int) (o : Obj F),
    utf8Encode cps = .ok b →
    pySeed ent (.str cps h) 2 o = pySeed ent (.bytes b h') 2 o ∧
    pySeed ent (.bytes b h') 2 o = pySeed ent (.bytearray b) 2 o

theorem seedStrBytesAgree_proven : SeedStrBytesAgree := by
  intro F
  intro ent cps b h h' o hb
  constructor
  · simp [pySeed, seedConvert, hb, bind, Except.bind, pure, Except.pure]
  · simp [pySeed, seedConvert]

theorem seedV1_fold : ∀ (l : List Nat) (x : Nat), l ≠ [] → l.foldl seedV1Step x < 2 ^ 64
  | [], _, h => absurd rfl h
  | [c], x, _ => by
    simp only [List.foldl, seedV1Step]
    exact Nat.and_lt_two_pow _ (by decide)
  | c :: d :: rest, x, _ => by
    simp only [List.foldl]
    exact seedV1_fold (d :: rest) _ (by simp)

/-- The version 1 hash, Lib/random.py:148-152, is a non-negative 64-bit value (for a
string that fits in `Py_ssize_t`), so the `-2 if x == -1` branch at :152 is dead, and
`str` and `bytes` agree, as bytes decode as latin-1 (:147). -/
def SeedV1Hash : Prop :=
  ∀ (F : Type),
  (∀ cps : List Nat, cps.length < 2 ^ 63 →
    0 ≤ seedV1 cps ∧ seedV1 cps < 2 ^ 64 ∧ seedV1 cps ≠ -2) ∧
  (∀ (ent : Entropy) (cps : List Nat) (h h' : Int) (o : Obj F),
    pySeed ent (.str cps h) 1 o = pySeed ent (.bytes cps h') 1 o)

theorem seedV1_nat (cps : List Nat) : seedV1 cps =
    (((cps.foldl seedV1Step (seedV1Init cps)) ^^^ cps.length : Nat) : Int) := by
  simp only [seedV1]
  rw [if_neg (by omega)]

theorem seedV1Hash_proven : SeedV1Hash := by
  intro F
  refine ⟨fun cps hl => ?_, fun ent cps h h' o => ?_⟩
  · rw [seedV1_nat]
    have hx : cps.foldl seedV1Step (seedV1Init cps) < 2 ^ 64 := by
      cases cps with
      | nil => simp [seedV1Init]
      | cons c cs => exact seedV1_fold _ _ (by simp)
    have hlen : cps.length < 2 ^ 64 := by omega
    have := Nat.xor_lt_two_pow hx hlen
    omega
  · simp [pySeed, seedConvert]

/-- Types other than `None`, `int`, `float`, `str`, `bytes` and `bytearray` raise the
documented `TypeError`, for every `version` (since 3.11), without touching the object. -/
def SeedUnsupportedType : Prop :=
  ∀ (F : Type),
  ∀ (ent : Entropy) (version : Int) (o : Obj F),
    pySeed ent .other version o =
      (.error (.typeError "The only supported seed types are:\nNone, int, float, str, bytes, and bytearray."), o)

theorem seedUnsupportedType_proven : SeedUnsupportedType := fun _ _ _ _ => rfl

/-- `seed` either replaces the state and clears `gauss_next`, or (when it raises)
changes nothing. -/
def SeedAllOrNothing : Prop :=
  ∀ (F : Type),
  ∀ (ent : Entropy) (a : SeedArg) (version : Int) (o o' : Obj F),
    (pySeed ent a version o = (.ok (), o') → o'.gaussNext = none) ∧
    (∀ e, pySeed ent a version o = (.error e, o') → o' = o)

theorem seedAllOrNothing_proven : SeedAllOrNothing := by
  intro F
  intro ent a version o o'
  constructor
  · intro h
    simp only [pySeed] at h
    split at h
    · cases h
    · split at h
      · cases h
      · simp only [Prod.mk.injEq] at h
        rw [← h.2]
  · intro e h
    simp only [pySeed] at h
    split at h
    · simp only [Prod.mk.injEq] at h
      exact h.2.symm
    · split at h
      · simp only [Prod.mk.injEq] at h
        exact h.2.symm
      · simp at h

theorem fromBytesBE_append (a d : List Nat) :
    fromBytesBE (a ++ d) = fromBytesBE a * 256 ^ d.length + fromBytesBE d := by
  have gen : ∀ (d : List Nat) (acc : Nat),
      d.foldl (fun acc x => acc * 256 + x) acc
        = acc * 256 ^ d.length + d.foldl (fun acc x => acc * 256 + x) 0 := by
    intro d
    induction d with
    | nil => intro acc; simp
    | cons x xs ih =>
      intro acc
      simp only [List.foldl_cons, List.length_cons]
      rw [ih (acc * 256 + x), ih (0 * 256 + x)]
      simp only [Nat.zero_mul, Nat.zero_add, Nat.add_mul, Nat.pow_succ]
      rw [Nat.mul_assoc, Nat.mul_comm 256 (256 ^ xs.length), Nat.add_assoc]
  simp only [fromBytesBE, List.foldl_append]
  exact gen d _

theorem fold_lt : ∀ (d : List Nat) (acc k : Nat), (∀ x ∈ d, x < 256) → acc < 256 ^ k →
    d.foldl (fun acc x => acc * 256 + x) acc < 256 ^ (k + d.length)
  | [], _, _, _, h => by simpa using h
  | x :: xs, acc, k, hd, h => by
    simp only [List.foldl_cons, List.length_cons]
    have hx := hd x (by simp)
    have hstep : acc * 256 + x < 256 ^ (k + 1) := by
      rw [Nat.pow_succ]
      have : (acc + 1) * 256 ≤ 256 ^ k * 256 := Nat.mul_le_mul_right _ h
      rw [Nat.add_mul] at this
      omega
    have := fold_lt xs (acc * 256 + x) (k + 1) (fun y hy => hd y (by simp [hy])) hstep
    rw [show k + (xs.length + 1) = k + 1 + xs.length by omega]
    exact this

theorem fromBytesBE_lt (d : List Nat) (h : ∀ x ∈ d, x < 256) : fromBytesBE d < 256 ^ d.length := by
  have := fold_lt d 0 0 h (by decide)
  simpa [fromBytesBE] using this

namespace Sha512

theorem compress_length (h : List UInt64) (hh : h.length = 8) (block : List Nat) :
    (compress h block).length = 8 := by
  have hstep : ∀ (w : Array UInt64) (l : List Nat) (st : List UInt64), st.length = 8 →
      (l.foldl (round w) st).length = 8 := by
    intro w l
    induction l with
    | nil => intro st hs; exact hs
    | cons t ts ih =>
      intro st hs
      simp only [List.foldl_cons]
      apply ih
      match st, hs with
      | [_, _, _, _, _, _, _, _], _ => rfl
  simp only [compress, List.length_zipWith]
  rw [hstep _ _ h hh, hh]
  rfl

theorem blocks_length : ∀ (n : Nat) (h : List UInt64) (msg : List Nat), h.length = 8 →
    (blocks n h msg).length = 8
  | 0, _, _, hh => hh
  | n + 1, h, msg, hh => blocks_length n _ _ (compress_length h hh _)

theorem digest_spec (msg : List Nat) : (digest msg).length = 64 ∧ ∀ x ∈ digest msg, x < 256 := by
  have hb := blocks_length ((pad msg).length / 128) H0 (pad msg) rfl
  simp only [digest]
  constructor
  · generalize blocks ((pad msg).length / 128) H0 (pad msg) = h at hb
    match h, hb with
    | [_, _, _, _, _, _, _, _], _ => simp [List.flatMap]
  · intro x hx
    simp only [List.mem_flatMap, List.mem_map] at hx
    obtain ⟨_, _, i, _, rfl⟩ := hx
    exact Nat.mod_lt _ (by decide)

end Sha512

/-- "For version 2 (the default), all of the bits are used" (Lib/random.py:139):
the int built from a `bytes` seed holds the seed itself in its upper bits and the
512-bit digest below them. -/
def SeedV2AllBits : Prop :=
  ∀ b : List Nat,
    seedV2 b / (2 : Int) ^ 512 = fromBytesBE b ∧
    seedV2 b % (2 : Int) ^ 512 = fromBytesBE (Sha512.digest b) ∧
    (Sha512.digest b).length = 64

theorem seedV2AllBits_proven : SeedV2AllBits := by
  intro b
  have ⟨hlen, hbytes⟩ := Sha512.digest_spec b
  have hlt := fromBytesBE_lt _ hbytes
  rw [hlen] at hlt
  have hp : (256 : Nat) ^ 64 = 2 ^ 512 := by
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
  rw [hp] at hlt
  have hval : seedV2 b = ((fromBytesBE b * 2 ^ 512 + fromBytesBE (Sha512.digest b) : Nat) : Int) := by
    simp only [seedV2]
    rw [fromBytesBE_append, hlen, hp]
  have hdiv : (fromBytesBE b * 2 ^ 512 + fromBytesBE (Sha512.digest b)) / 2 ^ 512 = fromBytesBE b := by
    rw [Nat.mul_comm, Nat.mul_add_div (Nat.two_pow_pos 512), Nat.div_eq_of_lt hlt, Nat.add_zero]
  have hmod : (fromBytesBE b * 2 ^ 512 + fromBytesBE (Sha512.digest b)) % 2 ^ 512
      = fromBytesBE (Sha512.digest b) := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
  refine ⟨?_, ?_, hlen⟩
  · rw [hval]
    exact_mod_cast hdiv
  · rw [hval]
    exact_mod_cast hmod

/-! ### `__init__` -/

/-- `Random(x)` and `r.seed(x)` give the same object, whatever `r` held. -/
def InitMatchesSeed : Prop :=
  ∀ (F : Type),
  ∀ (ent : Entropy) (x : SeedArg) (o : Obj F), o.core.mt.size = N →
    match pySeed ent x 2 o with
    | (.ok (), o') => pyInit ent x = .ok o'
    | (.error e, _) => pyInit (F := F) ent x = .error e

theorem pySeed_arg (ent : Entropy) (x : SeedArg) (o : Obj F) :
    pySeed ent x 2 o =
      match (do let a ← seedConvert x 2; randomSeed o.core a ent) with
      | .error e => (.error e, o)
      | .ok s => (.ok (), { core := s, gaussNext := none }) := by
  simp only [pySeed, bind, Except.bind]
  cases seedConvert x 2 with
  | error e => rfl
  | ok a => rfl

theorem initMatchesSeed_proven : InitMatchesSeed := by
  intro F
  intro ent x o ho
  have key : ∀ a : CArg, randomSeed o.core a ent = randomSeed genericNew a ent :=
    fun a => randomSeed_indep a ent ho genericNew_size
  simp only [pyInit]
  rw [pySeed_arg, pySeed_arg]
  simp only [bind, Except.bind, key]
  cases seedConvert x 2 with
  | error e => rfl
  | ok a =>
    simp only
    cases randomSeed genericNew a ent with
    | error e => rfl
    | ok s => rfl

/-! ### `getstate`, `setstate` -/

/-- `setstate(getstate())` restores the object exactly, from any object, including
`gauss_next`. Since every state reached by `advance` is valid, this covers a state
captured mid-stream: the continuation of the stream is the same. -/
def StateRoundTrip : Prop :=
  ∀ (F : Type),
  ∀ (o o' : Obj F), o.core.WF →
    pySetstate (pyGetstate o).toArg o' = (.ok (), o) ∧
    (∀ n, pySetstate (pyGetstate { o with core := advance n o.core }).toArg o'
      = (.ok (), { o with core := advance n o.core }))

theorem stateRoundTrip_one (o o' : Obj F) (h : o.core.WF) :
    pySetstate (pyGetstate o).toArg o' = (.ok (), o) := by
  have hc := cSetstate_getstate h
  simp only [pySetstate, PyState.toArg, pyGetstate, applyC, hc]
  cases o
  rfl

theorem stateRoundTrip_proven : StateRoundTrip := by
  intro F
  intro o o' h
  exact ⟨stateRoundTrip_one o o' h, fun n => stateRoundTrip_one _ o' (advance_wf n h)⟩

/-- A `setstate` that raises leaves the C state as it was (`new_state`,
_randommodule.c:461, and bpo-29960). -/
def SetstateFailureKeepsCore : Prop :=
  ∀ (F : Type),
  ∀ (st : SetArg F) (o o' : Obj F) (e : PyExc),
    pySetstate st o = (.error e, o') → o'.core = o.core

theorem applyC_error {st : CStateArg} {o o' : Obj F} {e : PyExc}
    (h : applyC st o = (.error e, o')) : o'.core = o.core := by
  simp only [applyC] at h
  split at h
  · simp only [Prod.mk.injEq] at h
    rw [h.2]
  · simp at h

theorem setstateFailureKeepsCore_proven : SetstateFailureKeepsCore := by
  intro F
  intro st o o' e h
  unfold pySetstate at h
  repeat' split at h
  all_goals first
    | (simp only [Prod.mk.injEq] at h
       have := h.2
       subst this
       rfl)
    | (dsimp only at h
       have := applyC_error h
       exact this)

/-- A `setstate` that raises leaves the whole object as it was. The C part is atomic
(`SetstateFailureKeepsCore`), but `Lib/random.py:184` unpacks into `self.gauss_next`
before the C call, so a rejected state still replaces `gauss_next`, and the next
`gauss()` returns the value from the rejected state. -/
def SetstateAtomic : Prop :=
  ∀ (F : Type) (st : SetArg F) (o o' : Obj F) (e : PyExc),
    pySetstate st o = (.error e, o') → o'.gaussNext = o.gaussNext

theorem setstateAtomic_refuted : ¬ SetstateAtomic := by
  intro h
  have := h Bool (.seq 3 { value := some 3, text := "3" } (.list []) (some true))
    { core := genericNew, gaussNext := none }
    { core := genericNew, gaussNext := some true }
    (.typeError "state vector must be a tuple") rfl
  cases this

/-- A version 2 state (signed words from Python 2.x-3.1) is the same as the version 3
state with each element reduced modulo `2**32` (Lib/random.py:188-196), and
`__setstate__` agrees with `setstate`. Any other version is a `ValueError` naming it,
and a state of the wrong length fails to unpack. -/
def SetstateVersions : Prop :=
  ∀ (F : Type),
  (∀ (xs ys : List Elem) (g : Option F) (o : Obj F) (t : String) (t' : String), modElems xs = .ok ys →
    pySetstate (.seq 3 { value := some 2, text := t } (.tuple xs) g) o =
      pySetstate (.seq 3 { value := some 3, text := t' } (.tuple ys) g) o ∧
    pySetstate (.seq 3 { value := some 2, text := t } (.list xs) g) o =
      pySetstate (.seq 3 { value := some 3, text := t' } (.tuple ys) g) o) ∧
  (∀ (len : Nat) (v : VersionV) (i : InternalArg) (g : Option F) (o : Obj F),
    v.value ≠ some 3 → v.value ≠ some 2 →
    pySetstate (.seq len v i g) o =
      (.error (.valueError s!"state with version {v.text} passed to Random.setstate() of version 3"), o)) ∧
  (∀ (len : Nat) (v : VersionV) (i : InternalArg) (g : Option F) (o : Obj F),
    (v.value = some 3 ∨ v.value = some 2) → len ≠ 3 →
    pySetstate (.seq len v i g) o = (.error (unpackError len), o)) ∧
  (∀ (st : SetArg F) (o : Obj F), pyDunderSetstate st o = pySetstate st o)

theorem setstateVersions_proven : SetstateVersions := by
  intro F
  refine ⟨fun xs ys g o t t' h => ?_, fun len v i g o h3 h2 => ?_, fun len v i g o h h3 => ?_,
    fun _ _ => rfl⟩
  · constructor
    · simp [pySetstate, h]
    · simp [pySetstate, h]
  · unfold pySetstate
    dsimp only
    split
    · rename_i h4
      exact absurd h4 h3
    · rename_i h4
      exact absurd h4 h2
    · rfl
  · simp only [pySetstate]
    rcases h with h | h <;> simp [h, h3]

/-- Pickling a `Random` round-trips: `__reduce__` gives `(cls, (), self.getstate())`;
the unpickler builds a fresh instance (whatever entropy it reads) and calls
`__setstate__`, which restores the object exactly. -/
def PickleRoundTrip : Prop :=
  ∀ (F : Type),
  ∀ (ent : Entropy) (o o0 : Obj F), o.core.WF → pyInit ent .none = .ok o0 →
    pyUnpickle ent (pyReduce o) = .ok o ∧ pyDunderGetstate o = pyReduce o

theorem pickleRoundTrip_proven : PickleRoundTrip := by
  intro F
  intro ent o o0 h h0
  refine ⟨?_, rfl⟩
  simp only [pyUnpickle, bind, Except.bind, h0, pyDunderSetstate, pyReduce]
  rw [stateRoundTrip_one o o0 h]
  rfl

end PyLean.CoreLibs.Rand
