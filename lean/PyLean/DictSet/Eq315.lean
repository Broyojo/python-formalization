import PyLean.DictSet.Props315

/-!
`dict == dict` (CPython 3.15.2, `Objects/dictobject.c:4621-4712`), with comparisons that may raise
and may change either operand.
-/

namespace PyLean.DictSet

open PyLean

variable {K V : Type} [DecidableEq K]

/-- `dict_equal_lock_held`, `dict_equal` and `dict_richcompare`, step by step, for every key
protocol and every value comparison, which may raise or change either dict. The sizes are compared
once, at the start. Each turn reads entry `i` of `a` as `a` is now, and its bound
`dk_nentries` too: past the bound the dicts are equal. A NULL key or a NULL value (a shared key a
split `a` has no value for) is skipped. Otherwise the key is looked up in `b` with its stored hash:
an exception is the result, no value means unequal, and a value is compared with `a`'s; an exception
or a no ends it, a yes goes on to `i + 1` from the state the callbacks left. `==` and `!=` are this
answer and its negation; any other operator, and any operand that is not a dict, is
`NotImplemented`. -/
def EqualBody : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (veq : V → V → DM K V Bool)
    (alias : Bool) (fuel i : Nat) (b a : PyDict K V),
    eqLeft alias b = some a →
    (a.used ≠ b.used → dictEqual315 P veq alias fuel b = (.ok false, b)) ∧
    (a.used = b.used → dictEqual315 P veq alias fuel b = dictEqualLive P veq alias fuel 0 b) ∧
    (a.body.nentries ≤ i → dictEqualLive P veq alias (fuel + 1) i b = (.ok true, b)) ∧
    (i < a.body.nentries → (eqEntry a i = none ∨ ∃ key h, eqEntry a i = some (key, none, h)) →
      dictEqualLive P veq alias (fuel + 1) i b = dictEqualLive P veq alias fuel (i + 1) b) ∧
    (i < a.body.nentries → ∀ key aval hash, eqEntry a i = some (key, some aval, hash) →
      (∀ e s, dictLookup P key hash b = (.error e, s) →
        dictEqualLive P veq alias (fuel + 1) i b = (.error e, s)) ∧
      (∀ ix s, dictLookup P key hash b = (.ok (ix, none), s) →
        dictEqualLive P veq alias (fuel + 1) i b = (.ok false, s)) ∧
      (∀ ix bval s, dictLookup P key hash b = (.ok (ix, some bval), s) →
        (∀ e s', veq aval bval s = (.error e, s') →
          dictEqualLive P veq alias (fuel + 1) i b = (.error e, s')) ∧
        (∀ s', veq aval bval s = (.ok false, s') →
          dictEqualLive P veq alias (fuel + 1) i b = (.ok false, s')) ∧
        (∀ s', veq aval bval s = (.ok true, s') →
          dictEqualLive P veq alias (fuel + 1) i b = dictEqualLive P veq alias fuel (i + 1) s')))

theorem equalBody_proven : EqualBody := by
  intro K V _ P veq alias fuel i b a ha
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h hn => ?_, fun h key aval hash he => ?_⟩
  · have : (a.used != b.used) = true := by simpa using h
    simp [dictEqual315, ha, this]
  · have : (a.used != b.used) = false := by simpa using h
    simp [dictEqual315, ha, this]
  · simp [dictEqualLive, ha, h]
  · have hlt : ¬ (i ≥ a.body.nentries) := by omega
    rcases hn with hn | ⟨key, hh, hn⟩
    · simp [dictEqualLive, ha, hlt, hn]
    · simp [dictEqualLive, ha, hlt, hn]
  · have hlt : ¬ (i ≥ a.body.nentries) := by omega
    refine ⟨fun e s hl => ?_, fun ix s hl => ?_, fun ix bval s hl => ⟨fun e s' hv => ?_, fun s' hv => ?_,
      fun s' hv => ?_⟩⟩
    · simp [dictEqualLive, ha, hlt, he, hl]
    · simp [dictEqualLive, ha, hlt, he, hl]
    · simp [dictEqualLive, ha, hlt, he, hl, hv]
    · simp [dictEqualLive, ha, hlt, he, hl, hv]
    · simp [dictEqualLive, ha, hlt, he, hl, hv]

/-- `dict_richcompare` (:4694-4712), for every protocol. -/
def RichcompareBody : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (veq : V → V → DM K V Bool)
    (alias : Bool) (fuel : Nat) (vIsAny wIsAny : Bool) (op : CmpOp) (b : PyDict K V),
    (¬(vIsAny = true ∧ wIsAny = true) →
      dictRichcompare315 P vIsAny wIsAny op veq alias fuel b = (.ok none, b)) ∧
    (op ≠ .eq → op ≠ .ne → dictRichcompare315 P vIsAny wIsAny op veq alias fuel b = (.ok none, b)) ∧
    (vIsAny = true → wIsAny = true → op = .eq ∨ op = .ne →
      dictRichcompare315 P vIsAny wIsAny op veq alias fuel b =
        match dictEqual315 P veq alias fuel b with
        | (.ok c, s) => (.ok (some (if op = .eq then c else !c)), s)
        | (.error e, s) => (.error e, s))

theorem richcompareBody_proven : RichcompareBody := by
  intro K V _ P veq alias fuel vIsAny wIsAny op b
  refine ⟨fun h => ?_, fun h1 h2 => ?_, fun h1 h2 h3 => ?_⟩
  · have : (!vIsAny || !wIsAny) = true := by
      cases vIsAny <;> cases wIsAny <;> simp_all
    simp [dictRichcompare315, this]
  · cases vIsAny <;> cases wIsAny <;> cases op <;> simp_all [dictRichcompare315]
  · simp only [dictRichcompare315, h1, h2, Bool.not_true, Bool.or_self, Bool.false_eq_true, if_false]
    have ho : (op == .eq || op == .ne) = true := by rcases h3 with h | h <;> simp [h]
    rw [if_pos ho]
    simp only [M.bind_run]
    rcases dictEqual315 P veq alias fuel b with ⟨r, s⟩
    cases r with
    | error e => rfl
    | ok c =>
      rcases h3 with h | h <;> subst h <;> cases c <;> rfl

/-! ### A comparison that empties the left operand -/

/-- Distinct ints, `hash(n)` is `n`. -/
def eqIntProto : Proto Nat (PyDict Nat Nat) :=
  { hash := fun k => .ok k, isStr := fun _ => false, isStrLike := fun _ => false
    strEq := fun a b => a == b, reprStr := fun _ => "", repr := fun _ => .ok "", typeName := fun _ => ""
    eq := fun a b s => (.ok (a == b), s) }

/-- `aval == bval` for an `aval` of 7: it clears the left operand and answers yes. -/
def eqClearsLeft : Nat → Nat → DM Nat Nat Bool := fun x y s =>
  if x = 7 then
    (.ok true, { s with peer := s.peer.map fun p => (dictClear p.toDict).toPeer })
  else (.ok (x == y), s)

def eqLeftOperand : PyDict Nat Nat :=
  (dictSetItem eqIntProto 2 3 (dictSetItem eqIntProto 1 7 ({ ident := 1 } : PyDict Nat Nat)).2).2
def eqRightOperand : PyDict Nat Nat :=
  (dictSetItem eqIntProto 2 4 (dictSetItem eqIntProto 1 5 ({ ident := 2 } : PyDict Nat Nat)).2).2

/-- `a == b` is `True` for `a = {1: X, 2: 3}`, `b = {1: 5, 2: 4}` when `X == 5` clears `a` and
answers yes: the loop reads `a`'s bound again after each comparison (:4633), finds it 0, and ends
as if every pair had matched, though `a[2]` was 3 and `b[2]` is 4. On record, not a bug report:
CPython 3.15.2 prints `True`. -/
def EqualReadsLeftLive : Prop :=
  (dictEqual315 eqIntProto eqClearsLeft false 16
      { eqRightOperand with peer := some eqLeftOperand.toPeer }).1 = .ok true ∧
  assocGet (fun a b => a == b) (dictAssoc eqLeftOperand) 2 = some 3 ∧
  assocGet (fun a b => a == b) (dictAssoc eqRightOperand) 2 = some 4

theorem equalReadsLeftLive_proven : EqualReadsLeftLive := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

end PyLean.DictSet
