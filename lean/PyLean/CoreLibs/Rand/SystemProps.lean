import PyLean.CoreLibs.Rand.SeedProps
import PyLean.CoreLibs.Rand.DistProps
import PyLean.CoreLibs.Rand.System

/-!
Properties of `SystemRandom`, `__init_subclass__` and the command line of
`Lib/random.py`.
-/

namespace PyLean.CoreLibs.Rand

open PyLean RM Flt

variable {σ F : Type}

/-! ### `SystemRandom` -/

theorem osUrandom_post {raw : Nat → RM σ (List Nat)} (hraw : RawValid raw) (n : Int) :
    Post (osUrandom raw (.int n)) (fun b => b.length = n.toNat ∧ ∀ x ∈ b, x < 256) := by
  have hdef : osUrandom raw (.int n) =
      (if n > ssizeMax ∨ n < ssizeMin then
        RM.raise (.overflowError "Python int too large to convert to C ssize_t")
       else if n < 0 then RM.raise (.valueError "size cannot be negative")
       else raw n.toNat) := rfl
  rw [hdef]
  split
  · exact Post.raise
  · split
    · exact Post.raise
    · intro s b s' h
      exact hraw _ s b s' h

/-- `SystemRandom.random()`: `(int.from_bytes(_urandom(7)) >> 3) * RECIP_BPF`, given
the contract of `os.urandom`, has a numerator below `2**53`, so the int converts to
a float exactly and the result is `m / 2**53` in `[0, 1)`, the same shape as the
Mersenne Twister. -/
def SysRandomBound : Prop :=
  ∀ (σ : Type) (raw : Nat → RM σ (List Nat)), RawValid raw → Post (sysRandomNum raw) (· < 2 ^ 53)

theorem sysRandomBound_proven : SysRandomBound := by
  intro σ raw hraw
  unfold sysRandomNum
  refine Post.bind (osUrandom_post hraw 7) (fun b hb => Post.pure ?_)
  obtain ⟨hlen, hbytes⟩ := hb
  have hlt := fromBytesBE_lt b hbytes
  have h7 : b.length = 7 := by simpa using hlen
  rw [h7] at hlt
  rw [Nat.shiftRight_eq_div_pow]
  apply Nat.div_lt_of_lt_mul
  have : (2 : Nat) ^ 3 * 2 ^ 53 = 256 ^ 7 := by decide
  omega

/-- `SystemRandom.getrandbits(k)` meets the same contract as the C one: below `2**k`
for `k ≥ 0`, and a negative `k` is a `ValueError`. So `SystemRandom` is a valid core
generator, and everything proved for the sequence layer applies to it. -/
def SysGetrandbitsBound : Prop :=
  ∀ (σ F : Type) [Flt F] (raw : Nat → RM σ (List Nat)), RawValid raw →
    (sysGen (F := F) raw).Valid ∧
    (∀ (k : Int) (s : σ), k < 0 → sysGetrandbits raw (.int k) s =
      (.error (.valueError "number of bits must be non-negative"), s))

theorem sysGetrandbitsBound_proven : SysGetrandbitsBound := by
  intro σ F _ raw hraw
  refine ⟨?_, fun k s h => ?_⟩
  · intro k r s s' h
    have hdef : sysGetrandbits raw (.int (k : Int)) =
        (osUrandom raw (.int (((k : Int) + 7) / 8)) >>= fun b =>
          Pure.pure (fromBytesBE b >>> (((k : Int) + 7) / 8 * 8 - k).toNat)) := by
      simp only [sysGetrandbits]
      rfl
    have hp : Post (sysGetrandbits raw (.int (k : Int))) (· < 2 ^ k) := by
      rw [hdef]
      refine Post.bind (osUrandom_post hraw _) (fun b hb => Post.pure ?_)
      obtain ⟨hlen, hbytes⟩ := hb
      have hlt := fromBytesBE_lt b hbytes
      have hB : ((((k : Int) + 7) / 8).toNat) = (k + 7) / 8 := by omega
      rw [hlen, hB] at hlt
      have hsh : (((k : Int) + 7) / 8 * 8 - k).toNat = (k + 7) / 8 * 8 - k := by omega
      rw [hsh, Nat.shiftRight_eq_div_pow]
      apply Nat.div_lt_of_lt_mul
      have h1 : (256 : Nat) ^ ((k + 7) / 8) = 2 ^ ((k + 7) / 8 * 8) := by
        rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul, Nat.mul_comm]
      have h2 : (2 : Nat) ^ ((k + 7) / 8 * 8 - k) * 2 ^ k = 2 ^ ((k + 7) / 8 * 8) := by
        rw [← Nat.pow_add]
        congr 1
        omega
      rw [h2, ← h1]
      exact hlt
    exact hp s r s' h
  · simp only [sysGetrandbits]
    show (RM.bind (RM.lift (.ok k)) _) s = _
    simp only [RM.bind, RM.lift]
    rw [if_pos h]
    rfl

/-- `SystemRandom.randbytes(n)` is `os.urandom(n)`: `n` bytes for `n ≥ 0`, and a
negative `n` is a `ValueError` from `os.urandom`. -/
def SysRandbytes : Prop :=
  ∀ (σ : Type) (raw : Nat → RM σ (List Nat)), RawValid raw →
    (∀ n : Int, Post (sysRandbytes raw (.int n)) (fun b => b.length = n.toNat ∧ ∀ x ∈ b, x < 256)) ∧
    (∀ (n : Int) (s : σ), ssizeMin ≤ n → n < 0 → sysRandbytes raw (.int n) s =
      (.error (.valueError "size cannot be negative"), s))

theorem sysRandbytes_proven : SysRandbytes := by
  intro σ raw hraw
  refine ⟨fun n => osUrandom_post hraw n, fun n s h1 h2 => ?_⟩
  have hdef : sysRandbytes raw (.int n) =
      (if n > ssizeMax ∨ n < ssizeMin then
        RM.raise (.overflowError "Python int too large to convert to C ssize_t")
       else if n < 0 then RM.raise (.valueError "size cannot be negative")
       else raw n.toNat) := rfl
  rw [hdef, if_neg (by simp only [ssizeMax, ssizeMin] at *; omega), if_pos h2]
  rfl

/-- `SystemRandom` has no state: `seed` does nothing, whatever its arguments, and
`getstate`, `setstate` (and so pickling and `copy`) raise `NotImplementedError`. -/
def SysNoState : Prop :=
  ∀ (σ β α : Type) (args : β) (s : σ),
    (sysSeed args : RM σ Unit) s = (.ok (), s) ∧
    (sysNotImplemented args : RM σ α) s =
      (.error (.named "NotImplementedError" "System entropy source does not have state."), s)

theorem sysNoState_proven : SysNoState := fun _ _ _ _ _ => ⟨rfl, rfl⟩

/-! ### `__init_subclass__` -/

/-- A class that defines none of the three names. -/
def ClsDict.silent (c : ClsDict) : Prop :=
  c.randbelow = none ∧ c.hasGetrandbits = false ∧ c.hasRandom = false

/-- `__init_subclass__` picks by the first class in the MRO that defines one of the
names: `_randbelow` is inherited as it stands; within one class `getrandbits` beats
`random`, so a subclass with both uses `getrandbits` (`SystemRandom`), and one that
only overrides `random()` gets `_randbelow_without_getrandbits`. An MRO ending in
`Random`, which defines `_randbelow`, always ends with an answer. -/
def InitSubclassPick : Prop :=
  (∀ (pre post : List ClsDict) (c : ClsDict), (∀ d ∈ pre, d.silent) →
    initSubclass (pre ++ c :: post) =
      match c.randbelow with
      | some f => some f
      | none =>
        if c.hasGetrandbits then some "_randbelow_with_getrandbits"
        else if c.hasRandom then some "_randbelow_without_getrandbits"
        else initSubclass post) ∧
  (∀ (pre : List ClsDict) (f : String) (post : List ClsDict) (g : Bool) (r : Bool),
    (initSubclass (pre ++ { randbelow := some f, hasGetrandbits := g, hasRandom := r } :: post)).isSome)

theorem initSubclass_silent : ∀ (pre post : List ClsDict), (∀ d ∈ pre, d.silent) →
    initSubclass (pre ++ post) = initSubclass post
  | [], _, _ => rfl
  | d :: pre, post, h => by
    obtain ⟨h1, h2, h3⟩ := h d (by simp)
    simp only [List.cons_append, initSubclass, h1, h2, h3, Bool.false_eq_true, if_false]
    exact initSubclass_silent pre post (fun x hx => h x (by simp [hx]))

theorem initSubclass_isSome : ∀ (pre post : List ClsDict) (c : ClsDict), c.randbelow.isSome →
    (initSubclass (pre ++ c :: post)).isSome
  | [], post, c, h => by
    simp only [List.nil_append, initSubclass]
    cases hc : c.randbelow with
    | none => simp [hc] at h
    | some f => rfl
  | d :: pre, post, c, h => by
    simp only [List.cons_append, initSubclass]
    split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · exact initSubclass_isSome pre post c h

theorem initSubclassPick_proven : InitSubclassPick := by
  refine ⟨fun pre post c h => ?_, fun pre f post g r => initSubclass_isSome pre post _ rfl⟩
  rw [initSubclass_silent pre _ h]
  rfl

/-! ### The command line -/

/-- The namespace `_parse_args` gives for `python -m random VAL` with an integer
`VAL`. -/
def posArgs (n : Int) (x : Option F) (w : List String) : CliArgs F :=
  { choice := none, integer := none, float := none, test := none,
    input := [{ asInt := some n, asFloat := x, words := w }], inputStrs := [toString n] }

/-- The namespace for `python -m random --integer N`. -/
def optArgs (n : Int) : CliArgs F :=
  { choice := none, integer := some n, float := none, test := none, input := [], inputStrs := [] }

/-- `randint` on an empty range raises a `ValueError`, whatever the message becomes. -/
theorem randint_empty (below : Nat → RM σ Nat) (a b : Int) (h : b < a) (s : σ) :
    ∃ m, randint below (.int a) (.int b) s = (.error (.valueError m), s) := by
  have key : ∀ x : Int, (∃ r, intStr x = .ok r) ∨ (∃ r, intStr x = .error (.valueError r)) := by
    intro x
    unfold intStr
    split
    · exact Or.inr ⟨_, rfl⟩
    · exact Or.inl ⟨_, rfl⟩
  rw [randint_int, if_pos h]
  rcases key a with ⟨ra, ha⟩ | ⟨ra, ha⟩
  · rcases key b with ⟨rb, hb⟩ | ⟨rb, hb⟩
    · refine ⟨s!"empty range in randint({ra}, {rb})", ?_⟩
      simp only [raiseValue, ha, hb, bind, Except.bind, pure, Except.pure]
    · exact ⟨rb, by simp only [raiseValue, ha, hb, bind, Except.bind]⟩
  · exact ⟨ra, by simp only [raiseValue, ha, bind, Except.bind]⟩

/-- The help text promises, for a positional argument, "integer: same as --integer"
(Lib/random.py@3.14.7:1041). False for `N < 1`: `randint(1, N)` raises `ValueError`, and the
`except ValueError` at :1071 meant for `int(val)` catches it too, so
`python -m random 0` prints `0.0` and `python -m random -5` a float in `(-5, 0]`,
where `--integer` raises. -/
def MainPositionalMatchesOption : Prop :=
  ∀ (σ F : Type) [Flt F] (below : Nat → RM σ Nat) (g : Gen σ F) (n : Int) (x : Option F)
    (w : List String) (h : String),
    cliMain below g (posArgs n x w) h = cliMain below g (optArgs n) h

theorem mainPositionalMatchesOption_refuted : ¬ MainPositionalMatchesOption := by
  intro h
  let below : Nat → RM Unit Nat := fun _ s => (.ok 0, s)
  let g : Gen Unit NanF := ⟨fun s => (.num, s), fun _ s => (.ok 0, s)⟩
  have e := congrFun (h Unit NanF below g 0 none [] "") ()
  obtain ⟨m, hm⟩ := randint_empty below 1 0 (by decide) ()
  have lhs : (cliMain below g (posArgs 0 none []) "" ()).1.toBool = true := by
    have hpos : cliMain below g (posArgs 0 none []) "" () =
        tryValue (randint below (.int 1) (.int 0) >>= fun r => Pure.pure (CliOut.int r))
          (do
            let y : NanF ← RM.lift (pyFloat 0)
            let r ← cliUniform g y
            return CliOut.flt r) () := rfl
    rw [hpos]
    simp only [tryValue, RM.bind_apply, hm]
    rfl
  have rhs : (cliMain below g (optArgs 0) "" ()).1.toBool = false := by
    have hopt : cliMain below g (optArgs 0) "" =
        (randint below (.int 1) (.int 0) >>= fun r => Pure.pure (CliOut.int r)) := rfl
    rw [hopt]
    simp only [RM.bind_apply, hm]
    rfl
  rw [e, rhs] at lhs
  cases lhs

/-- `except ValueError:` does nothing to a computation that raises no `ValueError`. -/
theorem tryValue_no_error {α : Type} (x handler : RM σ α) (s : σ)
    (h : ∀ m t, x s ≠ (.error (.valueError m), t)) : tryValue x handler s = x s := by
  unfold tryValue
  cases hx : x s with
  | mk r t =>
    cases r with
    | ok a => rfl
    | error e =>
      cases e with
      | valueError m => exact absurd hx (h m t)
      | _ => rfl

/-- With `N ≥ 1` the positional form and `--integer` are the same call (given a
`_randbelow` that raises no `ValueError`, as both real ones), and the result is in
`[1, N]`. The excluded `N < 1` is exactly the refuted entry above. -/
def MainPositionalPositive : Prop :=
  ∀ (σ F : Type) [Flt F] (below : Nat → RM σ Nat) (g : Gen σ F) (n : Int) (x : Option F)
    (w : List String) (h : String), 1 ≤ n →
    (∀ m s t e, below m s = (.error e, t) → e.className ≠ "ValueError") →
    cliMain below g (posArgs n x w) h = cliMain below g (optArgs n) h ∧
    (BelowValid below → Post (cliMain below g (optArgs n) h) (fun o =>
      match o with
      | .int r => 1 ≤ r ∧ r ≤ n
      | _ => False))

theorem mainPositionalPositive_proven : MainPositionalPositive := by
  intro σ F _ below g n x w h hn hb
  have hopt : cliMain below g (optArgs n) h =
      (randint below (.int 1) (.int n) >>= fun r => Pure.pure (CliOut.int r)) := rfl
  constructor
  · funext s
    have hpos : cliMain below g (posArgs n x w) h s =
        tryValue (randint below (.int 1) (.int n) >>= fun r => Pure.pure (CliOut.int r))
          (do
            let y : F ← RM.lift (pyFloat n)
            let r ← cliUniform g y
            return CliOut.flt r) s := rfl
    rw [hpos, hopt]
    apply tryValue_no_error
    intro m t he
    rw [randint_int, if_neg (by omega)] at he
    simp only [RM.bind_apply] at he
    cases hx : below (n - 1 + 1).toNat s with
    | mk r u =>
      rw [hx] at he
      cases r with
      | ok j => cases he
      | error e =>
        simp only [Prod.mk.injEq, Except.error.injEq] at he
        apply hb _ s u e hx
        rw [he.1]
        rfl
  · intro hv
    rw [hopt]
    have hp : Post (randint below (.int 1) (.int n)) (fun r => 1 ≤ r ∧ r ≤ n) :=
      fun st a t he => (randintSpec_proven σ below 1 n st).2.2 hv st a t he
    exact Post.bind hp (fun r hr => Post.pure hr)

/-- `main`'s other branches: `--choice` picks from its list, and no argument at all
returns the help text. -/
def MainChoices : Prop :=
  ∀ (σ F : Type) [Flt F] (below : Nat → RM σ Nat) (g : Gen σ F) (h : String), BelowValid below →
    (∀ (c : String) (cs : List String) (args : CliArgs F), args.choice = some (c :: cs) →
      Post (cliMain below g args h) (fun o =>
        match o with
        | .str w => w ∈ c :: cs
        | _ => False)) ∧
    (∀ (args : CliArgs F), args.choice = none → args.integer = none → args.float = none →
      args.test = none → args.input = [] → ∀ s, cliMain below g args h s = (.ok (.str h), s))

theorem mainChoices_proven : MainChoices := by
  intro σ F _ below g h hv
  constructor
  · intro c cs args hc
    unfold cliMain
    rw [hc]
    refine Post.bind ((choiceSpec_proven σ String below hv).2.2 (c :: cs)) (fun w hw => Post.pure hw)
  · intro args h1 h2 h3 h4 h5 s
    simp only [cliMain, cliMain.mainRest, h1, h2, h3, h4, h5]
    rfl

end PyLean.CoreLibs.Rand
