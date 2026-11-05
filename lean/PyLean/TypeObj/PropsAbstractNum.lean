import PyLean.TypeObj.PropsMisc

/-!
The number protocol of `Objects/abstract.c`, every branch: `binary_op1` and `binary_op` with
`binop_type_error`, `PyNumber_Add`, `PyNumber_Multiply` with `sequence_repeat`, `binary_iop`,
`PyNumber_InPlaceAdd`, `ternary_iop`, `PyNumber_InPlacePower` and
`_PyNumber_InPlacePowerNoMod`, and `PyNumber_AsSsize_t`.

`binary_op1` is stated against a list of candidate slot functions (`binopCandidates`): the
documented rule that a right operand whose type is a proper subclass, with a different slot
function, goes first; otherwise the left operand, then the right one; a slot shared by both
operands runs once. `firstAnswer` calls the candidates in order and stops at the first result
that is not `NotImplemented` or at the first exception. Every theorem is over every `rt`, so
slot functions are arbitrary user code that may raise and re-enter, and type names are read in
the world after the calls, as the C code reads `Py_TYPE(v)->tp_name` after them.
-/

namespace PyLean.TypeObj

/-- The slot functions `binary_op1` tries, in order (`Objects/abstract.c:940-990`): `slotw` is
dropped when both operands have the same type or the same slot function; when both remain, a
right operand whose type is a subtype of the left one's goes first. -/
def binopCandidates (w : World) (v u : Val) (s : Slot) : List SlotFn :=
  let sv := slotIn w v s
  let sw := if typeOf w u ≠ typeOf w v then (if slotIn w u s = sv then none else slotIn w u s)
    else none
  match sv, sw with
  | some a, some b => if isSubtype w (typeOf w u) (typeOf w v) then [b, a] else [a, b]
  | some a, none => [a]
  | none, some b => [b]
  | none, none => []

/-- Call each candidate in turn; the first result that is not `NotImplemented` is the answer,
and an exception stops the search. All candidates declining is `NotImplemented`. -/
def firstAnswer (rt : Rt) (s : Slot) (v u : Val) : List SlotFn → M Val
  | [] => pure .notImpl
  | f :: fs => do
    match ← callNbBinary rt s f v u with
    | .notImpl => firstAnswer rt s v u fs
    | x => pure x

/-- The `TypeError` of `binop_type_error`, `Objects/abstract.c:999-1008`, written out. -/
def binopMsg (w : World) (v u : Val) (op : String) : String :=
  "unsupported operand type(s) for " ++ trunc 100 op ++ ": '" ++ trunc 100 (typeName w v) ++
    "' and '" ++ trunc 100 (typeName w u) ++ "'"

theorem firstAnswer_two_err (rt : Rt) (s : Slot) (v u : Val) (a b : SlotFn) (w : World) :
    firstAnswer rt s v u [a, b] w =
      match callNbBinary rt s a v u w with
      | .ok .notImpl w1 => firstAnswer rt s v u [b] w1
      | .ok x w1 => .ok x w1
      | .err e w1 => .err e w1 := by
  simp only [firstAnswer, M.bind_app]
  cases callNbBinary rt s a v u w with
  | err e w1 => rfl
  | ok x w1 => cases x <;> rfl

/-- **`binary_op1` tries exactly the candidate slots, in order.** For every pair of operands,
every slot and every behaviour of the slot functions: the subclass-first rule, the left-then-right
order, one call for a shared slot function, `NotImplemented` passing to the next candidate, a
real result or an exception ending the search. `Objects/abstract.c:940-990`. -/
def BinaryOp1Candidates : Prop :=
  ∀ (rt : Rt) (v u : Val) (s : Slot) (w : World),
    binaryOp1 rt v u s w = firstAnswer rt s v u (binopCandidates w v u s) w

theorem firstAnswer_one (rt : Rt) (s : Slot) (v u : Val) (a : SlotFn) :
    firstAnswer rt s v u [a] = callNbBinary rt s a v u := by
  funext w
  simp only [firstAnswer, M.bind_app]
  cases callNbBinary rt s a v u w with
  | err e w1 => rfl
  | ok x w1 => cases x <;> rfl

/-- Case on one call result and finish by evaluation. -/
macro "close_call " t:term : tactic =>
  `(tactic| (cases h : ($t) with
    | err e w1 => simp [h]
    | ok a w1 => (cases a <;> simp [h])))

theorem binaryOp1Candidates_proven : BinaryOp1Candidates := by
  intro rt v u s w
  unfold binaryOp1 binopCandidates
  rcases hv : slotIn w v s with _ | sv <;> rcases hu : slotIn w u s with _ | su <;>
    by_cases ht : typeOf w u = typeOf w v
  -- no left slot
  · simp [hv, hu, ht, firstAnswer]
  · simp [hv, hu, ht, firstAnswer]
  · simp [hv, hu, ht, firstAnswer]
  · simp [hv, hu, ht, firstAnswer_one]
  -- left slot only, or the same type
  · simp [hv, hu, ht, firstAnswer_one]; close_call callNbBinary rt s sv v u w
  · simp [hv, hu, ht, firstAnswer_one]; close_call callNbBinary rt s sv v u w
  · simp [hv, hu, ht, firstAnswer_one]; close_call callNbBinary rt s sv v u w
  -- both slots, different types
  · by_cases hsame : su = sv
    · subst hsame
      simp [hv, hu, ht, firstAnswer_one]; close_call callNbBinary rt s su v u w
    · by_cases hsub : isSubtype w (typeOf w u) (typeOf w v) = true
      · simp only [M.bind_app, getW_app, hv, hu, ht, hsame, hsub, bne_iff_ne, ne_eq,
          not_false_eq_true, ite_true, beq_iff_eq, Option.some.injEq, ite_false,
          firstAnswer_two_err, firstAnswer_one]
        cases h : callNbBinary rt s su v u w with
        | err e w1 => simp [h]
        | ok a w1 =>
          cases a <;> simp [h] <;> close_call callNbBinary rt s sv v u w1
      · simp only [M.bind_app, getW_app, hv, hu, ht, hsame, hsub, bne_iff_ne, ne_eq,
          not_false_eq_true, ite_true, beq_iff_eq, Option.some.injEq, ite_false,
          Bool.false_eq_true, M.pure_app, firstAnswer_two_err, firstAnswer_one]
        cases h : callNbBinary rt s sv v u w with
        | err e w1 => simp [h]
        | ok a w1 =>
          cases a <;> simp [h] <;> close_call callNbBinary rt s su v u w1

end PyLean.TypeObj
