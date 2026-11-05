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

@[simp] theorem toString_string (s : String) : toString s = s := rfl

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

/-! ## `binary_op` and `binop_type_error` -/

/-- **`binary_op`, every branch.** The answer of the candidate slots is returned as it is; an
exception from a slot propagates; when every candidate declines, the result is the `TypeError`
`unsupported operand type(s) for <op>: '<type of v>' and '<type of w>'` of `binop_type_error`,
with both names cut to 100 bytes and read after the calls. So `binary_op` never returns
`NotImplemented`. `Objects/abstract.c:999-1019`. -/
def BinaryOpExact : Prop :=
  ∀ (rt : Rt) (v u : Val) (s : Slot) (name : String) (w : World),
    binaryOp rt v u s name w =
      match firstAnswer rt s v u (binopCandidates w v u s) w with
      | .ok .notImpl w1 => .err (.exc B.TypeError (binopMsg w1 v u name) none) w1
      | .ok x w1 => .ok x w1
      | .err e w1 => .err e w1

theorem binaryOpExact_proven : BinaryOpExact := by
  intro rt v u s name w
  rw [← binaryOp1Candidates_proven]
  unfold binaryOp
  cases h : binaryOp1 rt v u s w with
  | err e w1 => simp [h]
  | ok a w1 =>
    cases a <;> simp [h, binopTypeError, binopMsg, typeErr, raiseC]

/-! ## `PyNumber_Add` and `PyNumber_Multiply` -/

/-- **`PyNumber_Add`, every branch**: the number slots first (in `binary_op1` order); their
answer or exception is final; only if all decline is `sq_concat` of the left operand called, and
only of the left; with no `sq_concat`, the `TypeError` for `+`. `Objects/abstract.c:1138-1154`. -/
def NumberAddExact : Prop :=
  ∀ (rt : Rt) (v u : Val) (w : World),
    pyNumberAdd rt v u w =
      match firstAnswer rt .nb_add v u (binopCandidates w v u .nb_add) w with
      | .ok .notImpl w1 =>
        match slotIn w1 v .sq_concat with
        | some f => callSqConcat rt f v u w1
        | none => .err (.exc B.TypeError (binopMsg w1 v u "+") none) w1
      | .ok x w1 => .ok x w1
      | .err e w1 => .err e w1

theorem numberAddExact_proven : NumberAddExact := by
  intro rt v u w
  rw [← binaryOp1Candidates_proven]
  unfold pyNumberAdd
  cases h : binaryOp1 rt v u .nb_add w with
  | err e w1 => simp [h]
  | ok a w1 =>
    cases a <;> simp [h]
    cases slotIn w1 v .sq_concat <;> simp [binopTypeError, binopMsg, typeErr, raiseC]

/-- `sequence_repeat(f, seq, n)`, `Objects/abstract.c:1157-1173`, written out: an index count,
converted with `OverflowError` on overflow, or the `TypeError` for a non-index count. -/
def seqRepeatSpec (rt : Rt) (f : SlotFn) (seq n : Val) (w : World) : R Val :=
  if indexCheck w n then
    match numberAsSsize rt n (some B.OverflowError) w with
    | .ok count w1 => callSqRepeat f seq count w1
    | .err e w1 => .err e w1
  else .err (.exc B.TypeError
    ("can't multiply sequence by non-int of type '" ++ trunc 200 (typeName w n) ++ "'") none) w

/-- **`PyNumber_Multiply`, every branch**: the number slots first; if all decline, the left
operand's `sq_repeat` repeats it by the right operand, else the right operand's `sq_repeat`
repeats it by the left one, each through `sequence_repeat`; with neither, the `TypeError` for
`*`. `Objects/abstract.c:1176-1192`, with `sequence_repeat` at `:1157-1173`. -/
def NumberMultiplyExact : Prop :=
  ∀ (rt : Rt) (v u : Val) (w : World),
    pyNumberMultiply rt v u w =
      match firstAnswer rt .nb_multiply v u (binopCandidates w v u .nb_multiply) w with
      | .ok .notImpl w1 =>
        match slotIn w1 v .sq_repeat, slotIn w1 u .sq_repeat with
        | some f, _ => seqRepeatSpec rt f v u w1
        | none, some f => seqRepeatSpec rt f u v w1
        | none, none => .err (.exc B.TypeError (binopMsg w1 v u "*") none) w1
      | .ok x w1 => .ok x w1
      | .err e w1 => .err e w1

theorem sequenceRepeat_spec (rt : Rt) (f : SlotFn) (seq n : Val) (w : World) :
    sequenceRepeat rt f seq n w = seqRepeatSpec rt f seq n w := by
  unfold sequenceRepeat seqRepeatSpec
  by_cases hi : indexCheck w n = true
  · simp only [M.bind_app, getW_app, hi, ite_true]
    cases numberAsSsize rt n (some B.OverflowError) w <;> rfl
  · simp [hi, typeErr, raiseC]

theorem numberMultiplyExact_proven : NumberMultiplyExact := by
  intro rt v u w
  rw [← binaryOp1Candidates_proven]
  unfold pyNumberMultiply
  cases h : binaryOp1 rt v u .nb_multiply w with
  | err e w1 => simp [h]
  | ok a w1 =>
    cases a <;> simp [h]
    cases slotIn w1 v .sq_repeat <;> cases slotIn w1 u .sq_repeat <;>
      simp [sequenceRepeat_spec, binopTypeError, binopMsg, typeErr, raiseC]

/-! ## In-place operators -/

/-- The first stage of `binary_iop1`, `Objects/abstract.c:1234-1245`: the in-place slot of the
left operand, or `NotImplemented` when it has none. -/
def inplaceFirst (rt : Rt) (v u : Val) (islot : Slot) (w : World) : R Val :=
  match slotIn w v islot with
  | some f => binaryIop1.callInplace rt f (binaryIop1.nbOpOfISlot islot).idunder v u w
  | none => .ok .notImpl w

/-- **`binary_iop`, every branch**: the left operand's in-place slot first; its answer or
exception is final; if it declines or is missing, the binary slots in `binary_op1` order; if
those decline too, `binop_type_error` with the in-place operator name.
`Objects/abstract.c:1228-1269`. -/
def BinaryIopExact : Prop :=
  ∀ (rt : Rt) (v u : Val) (islot s : Slot) (name : String) (w : World),
    binaryIop rt v u islot s name w =
      match inplaceFirst rt v u islot w with
      | .ok .notImpl w1 =>
        match firstAnswer rt s v u (binopCandidates w1 v u s) w1 with
        | .ok .notImpl w2 => .err (.exc B.TypeError (binopMsg w2 v u name) none) w2
        | .ok x w2 => .ok x w2
        | .err e w2 => .err e w2
      | .ok x w1 => .ok x w1
      | .err e w1 => .err e w1

theorem binaryIop1_spec (rt : Rt) (v u : Val) (islot s : Slot) (w : World) :
    binaryIop1 rt v u islot s w =
      match inplaceFirst rt v u islot w with
      | .ok .notImpl w1 => binaryOp1 rt v u s w1
      | .ok x w1 => .ok x w1
      | .err e w1 => .err e w1 := by
  unfold binaryIop1 inplaceFirst
  cases hs : slotIn w v islot with
  | none => simp [hs]
  | some f =>
    simp only [M.bind_app, getW_app, hs]
    cases h : binaryIop1.callInplace rt f (binaryIop1.nbOpOfISlot islot).idunder v u w with
    | err e w1 => rfl
    | ok a w1 => cases a <;> rfl

theorem binaryIopExact_proven : BinaryIopExact := by
  intro rt v u islot s name w
  unfold binaryIop
  simp only [M.bind_app, binaryIop1_spec]
  cases h : inplaceFirst rt v u islot w with
  | err e w1 => simp
  | ok a w1 =>
    cases a <;> simp
    all_goals
      rw [← binaryOp1Candidates_proven]
      cases h2 : binaryOp1 rt v u s w1 with
      | err e w2 => simp
      | ok b w2 => cases b <;> simp [binopTypeError, binopMsg, typeErr, raiseC]

/-- **`PyNumber_InPlaceAdd`, every branch**: `__iadd__` (the `nb_inplace_add` slot), then the
`+` number slots; if all decline and the left operand's type has `tp_as_sequence`, its
`sq_inplace_concat`, else its `sq_concat`; otherwise the `TypeError` for `+=`.
`Objects/abstract.c:1307-1327`. -/
def NumberInPlaceAddExact : Prop :=
  ∀ (rt : Rt) (v u : Val) (w : World),
    pyNumberInPlaceAdd rt v u w =
      match inplaceFirst rt v u .nb_inplace_add w with
      | .ok .notImpl w1 =>
        match firstAnswer rt .nb_add v u (binopCandidates w1 v u .nb_add) w1 with
        | .ok .notImpl w2 =>
          if hasGroup w2 (typeOf w2 v) .sequence then
            match slotIn w2 v .sq_inplace_concat, slotIn w2 v .sq_concat with
            | some f, _ => callSqInplaceConcat rt f v u w2
            | none, some f => callSqConcat rt f v u w2
            | none, none => .err (.exc B.TypeError (binopMsg w2 v u "+=") none) w2
          else .err (.exc B.TypeError (binopMsg w2 v u "+=") none) w2
        | .ok x w2 => .ok x w2
        | .err e w2 => .err e w2
      | .ok x w1 => .ok x w1
      | .err e w1 => .err e w1

theorem numberInPlaceAddExact_proven : NumberInPlaceAddExact := by
  intro rt v u w
  unfold pyNumberInPlaceAdd
  simp only [M.bind_app, binaryIop1_spec]
  cases h : inplaceFirst rt v u .nb_inplace_add w with
  | err e w1 => simp
  | ok a w1 =>
    cases a <;> simp
    all_goals
      rw [← binaryOp1Candidates_proven]
      cases h2 : binaryOp1 rt v u .nb_add w1 with
      | err e w2 => simp
      | ok b w2 =>
        cases b <;> simp
        all_goals
          by_cases hg : hasGroup w2 (typeOf w2 v) .sequence = true
          · simp only [hg, ite_true]
            cases slotIn w2 v .sq_inplace_concat <;> cases slotIn w2 v .sq_concat <;>
              simp [binopTypeError, binopMsg, typeErr, raiseC]
          · simp [hg, binopTypeError, binopMsg, typeErr, raiseC]

/-- **`ternary_iop`, every branch** (as `PyNumber_InPlacePower` uses it): with no
`nb_inplace_power` on the left operand's type, straight to `ternary_op` with `"**="`; with the
`slot_nb_inplace_power` of a class, `__ipow__(v, w)` (two arguments, whatever `z` is): its
result or exception is final, and `NotImplemented` falls back to `ternary_op` in the world after
the call. No builtin type fills `nb_inplace_power`. `Objects/abstract.c:1272-1287`,
`Objects/typeobject.c:10971-10975`. -/
def TernaryIopExact : Prop :=
  ∀ (rt : Rt) (v u z : Val) (w : World),
    (slotIn w v .nb_inplace_power = none →
      ternaryIop rt v u z w = ternaryOp rt v u z "**=" w) ∧
    (slotIn w v .nb_inplace_power = some .generic →
      ternaryIop rt v u z w =
        match vectorcallMethod rt "__ipow__" [v, u] w with
        | .ok .notImpl w1 => ternaryOp rt v u z "**=" w1
        | .ok x w1 => .ok x w1
        | .err e w1 => .err e w1)

theorem ternaryIopExact_proven : TernaryIopExact := by
  intro rt v u z w
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp [ternaryIop, h]
  · simp only [ternaryIop, M.bind_app, getW_app, h]
    cases vectorcallMethod rt "__ipow__" [v, u] w with
    | err e w1 => rfl
    | ok a w1 => cases a <;> rfl

/-- **`PyNumber_InPlacePower` and `_PyNumber_InPlacePowerNoMod`**: `x **= y` is
`ternary_iop(x, y, None)`; when no operand has a power slot and `x` has no `__ipow__`, the error
names two types for `z = None` and three otherwise, after `**=`. `Objects/abstract.c:1359-1369`,
`ternary_op` at `:1101-1119`. -/
def InPlacePowerExact : Prop :=
  ∀ (rt : Rt) (v u z : Val) (w : World),
    pyNumberInPlacePowerNoMod rt v u w = ternaryIop rt v u .none w ∧
    pyNumberInPlacePower rt v u z w = ternaryIop rt v u z w ∧
    (slotIn w v .nb_inplace_power = none → slotIn w v .nb_power = none →
      slotIn w u .nb_power = none → slotIn w z .nb_power = none →
      pyNumberInPlacePower rt v u z w =
        .err (.exc B.TypeError
          (if z.is .none then binopMsg w v u "**="
           else "unsupported operand type(s) for " ++ trunc 100 "**=" ++ ": '" ++
             trunc 100 (typeName w v) ++ "', '" ++
             trunc 100 (typeName w u) ++ "', '" ++ trunc 100 (typeName w z) ++ "'") none) w)

theorem inPlacePowerExact_proven : InPlacePowerExact := by
  intro rt v u z w
  refine ⟨rfl, rfl, fun h0 h1 h2 h3 => ?_⟩
  simp only [pyNumberInPlacePower, ternaryIop, M.bind_app, getW_app, h0, M.pure_app]
  unfold ternaryOp
  by_cases hz : z.is .none = true
  · simp [h1, h2, h3, hz, binopMsg, typeErr, raiseC]
  · simp [h1, h2, h3, hz, typeErr, raiseC]

/-! ## `PyNumber_AsSsize_t` -/

/-- **`PyNumber_AsSsize_t`, every branch**: an exception from `_PyNumber_Index` propagates; a
value in `Py_ssize_t` range is returned; out of range, `err = NULL` clips to `PY_SSIZE_T_MIN` or
`PY_SSIZE_T_MAX` by sign, and any other `err` is raised with `cannot fit '<type>' into an
index-sized integer`, the type of the original `item` read after `__index__` ran. For an exact
`int` no user code runs. `Objects/abstract.c:1468-1515`. -/
def AsSsizeExact : Prop :=
  ∀ (rt : Rt) (item : Val) (err : Option Addr) (w : World),
    numberAsSsize rt item err w =
      (match numberIndex rt item w with
      | .err e w1 => .err e w1
      | .ok v w1 =>
        let i := (intOf w1 v).getD 0
        if inSsize i then .ok i w1
        else match err with
          | none => .ok (if i < 0 then PyLean.ssizeMin else PyLean.ssizeMax) w1
          | some e => .err (.exc e ("cannot fit '" ++ trunc 200 (typeName w1 item) ++
              "' into an index-sized integer") none) w1) ∧
    ∀ i : Int, numberAsSsize rt (.int i) err w =
      if inSsize i then .ok i w
      else match err with
        | none => .ok (if i < 0 then PyLean.ssizeMin else PyLean.ssizeMax) w
        | some e => .err (.exc e ("cannot fit '" ++ trunc 200 (typeName w (.int i)) ++
            "' into an index-sized integer") none) w

theorem asSsizeExact_proven : AsSsizeExact := by
  intro rt item err w
  refine ⟨?_, fun i => ?_⟩
  · unfold numberAsSsize pyNumberIndex
    simp only [M.bind_app, getW_app]
    cases numberIndex rt item w with
    | err e w1 => rfl
    | ok v w1 =>
      simp only [M.pure_app]
      by_cases hi : inSsize ((intOf w1 v).getD 0) = true
      · simp [hi]
      · cases err <;> simp [hi, raiseC]
  · unfold numberAsSsize pyNumberIndex numberIndex
    simp only [M.bind_app, getW_app, intOf, M.pure_app, Option.getD_some]
    by_cases hi : inSsize i = true
    · simp [hi]
    · cases err <;> simp [hi, raiseC]

end PyLean.TypeObj
