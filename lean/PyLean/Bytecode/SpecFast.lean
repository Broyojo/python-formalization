import PyLean.Bytecode.SpecHeap
import PyLean.Bytecode.SpecLocals

/-!
What the fast paths of the specialized instructions do, stated on the macros themselves.

`execOp` runs a specialized form under `withDeopt`, so the statements "specialized = generic"
elsewhere in this directory would also hold of a fast path that always exits. The statements here
close that gap: for each guard and each macro, the exact inputs on which it runs to completion,
what it then leaves, and that on every other input it exits (`DEOPT_IF`/`EXIT_IF`, the `.deopt`
label). A guard that rejected a valid operand, one that accepted an invalid operand, a body that
always exits, or a body with its operands swapped each fails one conjunct.

The conditions are written out independently of the model's helpers: `Compact` is the range of
`_PyLong_IsCompact` (one 30-bit digit, `Include/cpython/longintrepr.h`), which is also the range
`is_medium_int` (`Objects/longobject.c:53-58`) accepts for a result, so `_PyCompactLong_Add` and
friends (`:3870`, `:3915`, `:4362`) return `NULL` exactly outside it. The allocation failure on
the same `NULL` path, and `PyFloat_FromDouble`/`PyUnicode_Concat` running out of memory, are not
modelled.
-/

namespace PyLean.Bytecode

open Uop

/-- Unfold the monad plumbing of a step rule on an explicit stack. -/
syntax "bc_simp" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| bc_simp $[[$xs,*]]?) => do
    let xs := (xs.map (·.getElems)).getD #[]
    `(tactic| simp [bind, EStateM.bind, BM.lift, RM.lift, liftM, monadLift, MonadLift.monadLift,
        pure, EStateM.pure, throw, throwThe, MonadExcept.throw, EStateM.throw, MonadExceptOf.throw,
        guardTop, peekN, popN, pushAll, stk, stkK, deoptIf, getObj, $xs,*])

/-- The instruction exited to its generic form. -/
def Deopts (r : EStateM.Result Err St Unit) : Prop := ∃ s', r = .error .deopt s'

/-- `_PyLong_IsCompact`: at most one 30-bit digit. -/
def Compact (i : Int) : Prop := -(2 ^ 30 : Int) < i ∧ i < 2 ^ 30

instance (i : Int) : Decidable (Compact i) := by unfold Compact; infer_instance

theorem isCompact_iff (i : Int) : isCompact i = true ↔ Compact i := by
  simp [isCompact, Compact]

theorem isCompact_false (i : Int) : isCompact i = false ↔ ¬ Compact i := by
  rw [← isCompact_iff]; simp

/-- `_PyLong_CheckExactAndCompact`. -/
def CompactInt (v : Val) : Prop := ∃ i, v = .int i ∧ Compact i
/-- `PyFloat_CheckExact`. -/
def IsFloat (v : Val) : Prop := ∃ f, v = .float f
/-- `PyUnicode_CheckExact`. -/
def IsStr (v : Val) : Prop := ∃ t, v = .str t
/-- `PyStackRef_BoolCheck`. -/
def IsBool (v : Val) : Prop := ∃ b, v = .bool b
/-- `PyList_CheckExact`. -/
def IsList (rt : Rt) (v : Val) : Prop := ∃ a items, v = .ref a ∧ rt.heap[a]? = some (.list items)
/-- `PyTuple_CheckExact`. -/
def IsTuple (rt : Rt) (v : Val) : Prop := ∃ a items, v = .ref a ∧ rt.heap[a]? = some (.tuple items)
/-- `PyUnicode_CheckExact` and `PyUnicode_IS_COMPACT_ASCII`: every code point below 128. -/
def IsAsciiStr (v : Val) : Prop := ∃ t, v = .str t ∧ ∀ c ∈ t.toList, c.toNat < 128

/-- A guard on the top of the stack: it passes, changing nothing, exactly when `P` holds, and
otherwise exits with the state as it was. -/
def GuardTos (g : M Unit) (P : Rt → Val → Prop) : Prop :=
  ∀ (regs : Regs) (rest : List Val) (x : Val), Live regs.rt x →
    (P regs.rt x → g ⟨regs, x :: rest⟩ = .ok () ⟨regs, x :: rest⟩) ∧
    (¬ P regs.rt x → g ⟨regs, x :: rest⟩ = .error .deopt ⟨regs, x :: rest⟩)

/-- A guard on the second value (`nos`); the top `y` is not inspected. -/
def GuardNos (g : M Unit) (P : Rt → Val → Prop) : Prop :=
  ∀ (regs : Regs) (rest : List Val) (x y : Val), Live regs.rt x →
    (P regs.rt x → g ⟨regs, y :: x :: rest⟩ = .ok () ⟨regs, y :: x :: rest⟩) ∧
    (¬ P regs.rt x → g ⟨regs, y :: x :: rest⟩ = .error .deopt ⟨regs, y :: x :: rest⟩)

theorem guardTos_of (bad : List Val → BM Bool) (P : Rt → Val → Prop)
    (h : ∀ (regs : Regs) x, Live regs.rt x → ∃ b, bad [x] regs = .ok b regs ∧ (b = false ↔ P regs.rt x)) :
    GuardTos (guardTop 1 bad) P := by
  intro regs rest x hx
  obtain ⟨b, hb, hp⟩ := h regs x hx
  rw [guardTop_one regs rest bad x b hb]
  cases b <;> simp_all

theorem guardNos_of (bad : List Val → BM Bool) (P : Rt → Val → Prop)
    (h : ∀ (regs : Regs) x y, Live regs.rt x →
      ∃ b, bad [x, y] regs = .ok b regs ∧ (b = false ↔ P regs.rt x)) :
    GuardNos (guardTop 2 bad) P := by
  intro regs rest x y hx
  obtain ⟨b, hb, hp⟩ := h regs x y hx
  rw [guardTop_two regs rest bad x y b hb]
  cases b <;> simp_all

theorem notCompactInt_iff (v : Val) : notCompactInt v = false ↔ CompactInt v := by
  cases v <;> simp [notCompactInt, CompactInt, isCompact_iff]

theorem notFloat_iff (v : Val) : notFloat v = false ↔ IsFloat v := by
  cases v <;> simp [notFloat, IsFloat]

theorem notStr_iff (v : Val) : notStr v = false ↔ IsStr v := by
  cases v <;> simp [notStr, IsStr]

theorem notList_spec (regs : Regs) (x : Val) (hx : Live regs.rt x) :
    ∃ b, notList x regs = .ok b regs ∧ (b = false ↔ IsList regs.rt x) := by
  cases x with
  | ref a =>
    obtain ⟨o, ho⟩ := live_obj hx
    cases o with
    | list items => exact ⟨false, notList_list regs ho, by simp [IsList, ho]⟩
    | _ => exact ⟨true, notList_other regs ho (by simp), by simp [IsList, ho]⟩
  | _ => exact ⟨true, notList_nonref regs _ (by simp), by simp [IsList]⟩

theorem notTuple_spec (regs : Regs) (x : Val) (hx : Live regs.rt x) :
    ∃ b, notTuple x regs = .ok b regs ∧ (b = false ↔ IsTuple regs.rt x) := by
  cases x with
  | ref a =>
    obtain ⟨o, ho⟩ := live_obj hx
    cases o with
    | tuple items => exact ⟨false, notTuple_tuple regs ho, by simp [IsTuple, ho]⟩
    | _ => exact ⟨true, notTuple_other regs ho (by simp), by simp [IsTuple, ho]⟩
  | _ => exact ⟨true, notTuple_nonref regs _ (by simp), by simp [IsTuple]⟩

/-- `PySlice_Check`; `slice` cannot be subclassed. -/
def IsSlice (rt : Rt) (v : Val) : Prop :=
  ∃ a st sp se, v = .ref a ∧ rt.heap[a]? = some (.slice st sp se)

theorem notSlice_spec (regs : Regs) (x : Val) (hx : Live regs.rt x) :
    ∃ b, notSlice x regs = .ok b regs ∧ (b = false ↔ IsSlice regs.rt x) := by
  cases x with
  | ref a =>
    obtain ⟨o, ho⟩ := live_obj hx
    cases o with
    | slice st sp se => exact ⟨false, by bc_simp [notSlice, ho], by simp [IsSlice, ho]⟩
    | _ => exact ⟨true, by bc_simp [notSlice, ho], by simp [IsSlice, ho]⟩
  | _ => exact ⟨true, by bc_simp [notSlice], by simp [IsSlice]⟩

theorem ascii_any_false (t : String) :
    (t.toList.any fun c => asciiLimit ≤ c.toNat) = false ↔ ∀ c ∈ t.toList, c.toNat < 128 := by
  rw [← Bool.not_eq_true, List.any_eq_true]
  constructor
  · intro h c hc
    exact Nat.lt_of_not_le fun h2 => h ⟨c, hc, decide_eq_true h2⟩
  · rintro h ⟨c, hc, h2⟩
    exact Nat.not_le_of_lt (h c hc) (of_decide_eq_true h2)

/-! ## The guards -/

/-- The type guards of the `BINARY_OP`, `COMPARE_OP`, `TO_BOOL` and `STORE_SUBSCR` families,
`Python/bytecodes.c`: `_GUARD_TOS_INT` (`:640-643`) and `_GUARD_NOS_INT` (`:635-638`) ask for a
compact exact int, `_GUARD_TOS_FLOAT`/`_GUARD_NOS_FLOAT` (`:768-776`) for an exact float,
`_GUARD_TOS_UNICODE`/`_GUARD_NOS_UNICODE` (`:570-578`) for an exact str, `_GUARD_NOS_COMPACT_ASCII`
(`:564-568`) for an exact str of ASCII code points, `_GUARD_TOS_LIST`/`_GUARD_NOS_LIST`
(`:530-538`) for an exact list, `_GUARD_NOS_TUPLE`/`_GUARD_TOS_TUPLE` (`:1230-1238`) for an exact
tuple, `_GUARD_TOS_SLICE` (`:540-543`) for a slice, and `TO_BOOL_BOOL` (`:514-517`) is a guard for
a bool. Each passes without changing anything on the
values it asks for and exits with the state unchanged on every other value. -/
def GuardRules : Prop :=
  GuardTos _GUARD_TOS_INT (fun _ => CompactInt) ∧ GuardNos _GUARD_NOS_INT (fun _ => CompactInt) ∧
  GuardTos _GUARD_TOS_FLOAT (fun _ => IsFloat) ∧ GuardNos _GUARD_NOS_FLOAT (fun _ => IsFloat) ∧
  GuardTos _GUARD_TOS_UNICODE (fun _ => IsStr) ∧ GuardNos _GUARD_NOS_UNICODE (fun _ => IsStr) ∧
  GuardNos _GUARD_NOS_COMPACT_ASCII (fun _ => IsAsciiStr) ∧
  GuardTos _GUARD_TOS_LIST IsList ∧ GuardNos _GUARD_NOS_LIST IsList ∧
  GuardNos _GUARD_NOS_TUPLE IsTuple ∧
  GuardTos TO_BOOL_BOOL (fun _ => IsBool) ∧
  GuardTos _GUARD_TOS_TUPLE IsTuple ∧ GuardTos _GUARD_TOS_SLICE IsSlice

theorem guardRules_proven : GuardRules := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact guardTos_of _ _ fun regs x _ => ⟨_, rfl, notCompactInt_iff x⟩
  · exact guardNos_of _ _ fun regs x y _ => ⟨_, rfl, notCompactInt_iff x⟩
  · exact guardTos_of _ _ fun regs x _ => ⟨_, rfl, notFloat_iff x⟩
  · exact guardNos_of _ _ fun regs x y _ => ⟨_, rfl, notFloat_iff x⟩
  · exact guardTos_of _ _ fun regs x _ => ⟨_, rfl, notStr_iff x⟩
  · exact guardNos_of _ _ fun regs x y _ => ⟨_, rfl, notStr_iff x⟩
  · refine guardNos_of _ _ fun regs x y _ => ?_
    cases x with
    | str t => exact ⟨_, rfl, by simp only [ascii_any_false, IsAsciiStr]; simp⟩
    | _ => exact ⟨true, rfl, by simp [IsAsciiStr]⟩
  · exact guardTos_of _ _ fun regs x hx => notList_spec regs x hx
  · exact guardNos_of _ _ fun regs x y hx => notList_spec regs x hx
  · exact guardNos_of _ _ fun regs x y hx => notTuple_spec regs x hx
  · refine guardTos_of _ _ fun regs x _ => ?_
    cases x with
    | bool b => exact ⟨false, rfl, by simp [IsBool]⟩
    | _ => exact ⟨true, rfl, by simp [IsBool]⟩
  · exact guardTos_of _ _ fun regs x hx => notTuple_spec regs x hx
  · exact guardTos_of _ _ fun regs x hx => notSlice_spec regs x hx

theorem guard_tos_int_pass {regs : Regs} {rest : List Val} {i : Int} (h : Compact i) :
    _GUARD_TOS_INT ⟨regs, .int i :: rest⟩ = .ok () ⟨regs, .int i :: rest⟩ :=
  (guardRules_proven.1 regs rest _ (by simp [Live])).1 ⟨i, rfl, h⟩

theorem guard_nos_int_pass {regs : Regs} {rest : List Val} {i : Int} (y : Val) (h : Compact i) :
    _GUARD_NOS_INT ⟨regs, y :: .int i :: rest⟩ = .ok () ⟨regs, y :: .int i :: rest⟩ :=
  (guardRules_proven.2.1 regs rest _ y (by simp [Live])).1 ⟨i, rfl, h⟩

theorem guard_tos_int_fail {regs : Regs} {rest : List Val} {r : Val} (h : ¬ CompactInt r) :
    _GUARD_TOS_INT ⟨regs, r :: rest⟩ = .error .deopt ⟨regs, r :: rest⟩ := by
  have he : _GUARD_TOS_INT ⟨regs, r :: rest⟩ = if notCompactInt r then
      .error .deopt ⟨regs, r :: rest⟩ else .ok () ⟨regs, r :: rest⟩ := intKind.tos_eval regs rest r
  have hb : notCompactInt r = true := by
    cases hb : notCompactInt r
    · exact absurd ((notCompactInt_iff r).1 hb) h
    · rfl
  simp [he, hb]

/-! ## `TO_BOOL` -/

/-- The `TO_BOOL` specializations on the value they were made for, `Python/bytecodes.c:514-588`:
`TO_BOOL_INT` (`_GUARD_TOS_INT + _TO_BOOL_INT + _POP_TOP_INT`, `:519-528`) answers `i != 0` for a
compact int, `TO_BOOL_NONE` (`:556-562`) `False` for `None`, `TO_BOOL_STR` (`:580-589`) whether a
str is non-empty, `TO_BOOL_LIST` (`:545-554`) whether a list is non-empty, `TO_BOOL_BOOL` leaves a
bool as it is; and each exits on every other value. `_TO_BOOL_INT` itself is `(value -- res, v)`:
it pushes the answer under the operand, which `_POP_TOP_INT` then drops. -/
def ToBoolFast : Prop := ∀ (regs : Regs) (rest : List Val) (v : Val), Live regs.rt v →
  (∀ i, _TO_BOOL_INT ⟨regs, .int i :: rest⟩ = .ok () ⟨regs, .int i :: .bool (i != 0) :: rest⟩) ∧
  (∀ i, v = .int i → Compact i → TO_BOOL_INT ⟨regs, v :: rest⟩ = .ok () ⟨regs, .bool (i != 0) :: rest⟩) ∧
  (¬ CompactInt v → TO_BOOL_INT ⟨regs, v :: rest⟩ = .error .deopt ⟨regs, v :: rest⟩) ∧
  (v = .none → TO_BOOL_NONE ⟨regs, v :: rest⟩ = .ok () ⟨regs, .bool false :: rest⟩) ∧
  (v ≠ .none → Deopts (TO_BOOL_NONE ⟨regs, v :: rest⟩)) ∧
  (∀ t, v = .str t → TO_BOOL_STR ⟨regs, v :: rest⟩ = .ok () ⟨regs, .bool (t != "") :: rest⟩) ∧
  (¬ IsStr v → TO_BOOL_STR ⟨regs, v :: rest⟩ = .error .deopt ⟨regs, v :: rest⟩) ∧
  (∀ a items, v = .ref a → regs.rt.heap[a]? = some (.list items) →
    TO_BOOL_LIST ⟨regs, v :: rest⟩ = .ok () ⟨regs, .bool (items.size != 0) :: rest⟩) ∧
  (¬ IsList regs.rt v → TO_BOOL_LIST ⟨regs, v :: rest⟩ = .error .deopt ⟨regs, v :: rest⟩) ∧
  (IsBool v → TO_BOOL_BOOL ⟨regs, v :: rest⟩ = .ok () ⟨regs, v :: rest⟩) ∧
  (¬ IsBool v → TO_BOOL_BOOL ⟨regs, v :: rest⟩ = .error .deopt ⟨regs, v :: rest⟩)

theorem toBoolFast_proven : ToBoolFast := by
  intro regs rest v hv
  have G := guardRules_proven
  refine ⟨fun i => ?_, fun i hi hc => ?_, fun hn => ?_, fun hn => ?_, fun hn => ?_, fun t ht => ?_,
    fun hn => ?_, fun a items ha hl => ?_, fun hn => ?_, fun hb => ?_, fun hb => ?_⟩
  · bc_simp [_TO_BOOL_INT]
  · subst hi
    have hg := guard_tos_int_pass (regs := regs) (rest := rest) hc
    show (do _GUARD_TOS_INT; _TO_BOOL_INT; _POP_TOP_INT) _ = _
    simp only [bind, EStateM.bind, hg]
    bc_simp [_TO_BOOL_INT, _POP_TOP_INT]
  · have hg := (G.1 regs rest v hv).2 hn
    show (do _GUARD_TOS_INT; _TO_BOOL_INT; _POP_TOP_INT) _ = _
    simp only [bind, EStateM.bind, hg]
  · subst hn; bc_simp [TO_BOOL_NONE]
  · refine ⟨⟨regs, rest⟩, ?_⟩
    cases v <;> first | exact absurd rfl hn | bc_simp [TO_BOOL_NONE]
  · subst ht
    have hg := (G.2.2.2.2.1 regs rest _ hv).1 ⟨t, rfl⟩
    show (do _GUARD_TOS_UNICODE; _TO_BOOL_STR) _ = _
    simp only [bind, EStateM.bind, hg]
    bc_simp [_TO_BOOL_STR]
  · have hg := (G.2.2.2.2.1 regs rest _ hv).2 hn
    show (do _GUARD_TOS_UNICODE; _TO_BOOL_STR) _ = _
    simp only [bind, EStateM.bind, hg]
  · subst ha
    have hg := (G.2.2.2.2.2.2.2.1 regs rest _ hv).1 ⟨a, items, rfl, hl⟩
    show (do _GUARD_TOS_LIST; _TO_BOOL_LIST) _ = _
    simp only [bind, EStateM.bind, hg]
    bc_simp [_TO_BOOL_LIST, hl]
  · have hg := (G.2.2.2.2.2.2.2.1 regs rest _ hv).2 hn
    show (do _GUARD_TOS_LIST; _TO_BOOL_LIST) _ = _
    simp only [bind, EStateM.bind, hg]
  · exact (G.2.2.2.2.2.2.2.2.2.2.1 regs rest v hv).1 hb
  · exact (G.2.2.2.2.2.2.2.2.2.2.1 regs rest v hv).2 hb

/-! ## Arithmetic -/

/-- A compact-int arithmetic uop `(left, right -- res, l, r)` on compact operands: the result
when it is compact again, and otherwise `EXIT_IF(PyStackRef_IsNull(res))`. -/
def IntUop (m : M Unit) (op : Int → Int → Int) : Prop :=
  ∀ (regs : Regs) (rest : List Val) (a b : Int), Compact a → Compact b →
    (Compact (op a b) → m ⟨regs, .int b :: .int a :: rest⟩ = .ok () ⟨regs, .int (op a b) :: rest⟩) ∧
    (¬ Compact (op a b) → Deopts (m ⟨regs, .int b :: .int a :: rest⟩))

/-- A compact-int arithmetic macro: it answers `op left right` exactly when both operands and the
result are compact ints, and exits otherwise. -/
def IntArith (m : M Unit) (op : Int → Int → Int) : Prop :=
  ∀ (regs : Regs) (rest : List Val) (l r : Val),
    (∀ a b, l = .int a → r = .int b → Compact a → Compact b → Compact (op a b) →
      m ⟨regs, r :: l :: rest⟩ = .ok () ⟨regs, .int (op a b) :: rest⟩) ∧
    (¬ (∃ a b, l = .int a ∧ r = .int b ∧ Compact a ∧ Compact b ∧ Compact (op a b)) →
      Deopts (m ⟨regs, r :: l :: rest⟩))

theorem intUop_of (body : List Val → BM (List Val)) (op : Int → Int → Int)
    (hb : ∀ a b, body [.int a, .int b] = compactResult (op a b)) : IntUop (stk 2 1 body) op := by
  intro regs rest a b _ _
  constructor
  · intro hc
    have : isCompact (op a b) = true := (isCompact_iff _).2 hc
    bc_simp [hb, compactResult, this]
  · intro hc
    have : isCompact (op a b) = false := (isCompact_false _).2 hc
    exact ⟨⟨regs, rest⟩, by bc_simp [hb, compactResult, this]⟩

theorem intArith_of (body : M Unit) (op : Int → Int → Int) (hb : IntUop body op) :
    IntArith (do _GUARD_TOS_INT; _GUARD_NOS_INT; body) op := by
  intro regs rest l r
  have ht : _GUARD_TOS_INT ⟨regs, r :: l :: rest⟩ = if notCompactInt r then
      .error .deopt ⟨regs, r :: l :: rest⟩ else .ok () ⟨regs, r :: l :: rest⟩ :=
    intKind.tos_eval regs (l :: rest) r
  have hn : _GUARD_NOS_INT ⟨regs, r :: l :: rest⟩ = if notCompactInt l then
      .error .deopt ⟨regs, r :: l :: rest⟩ else .ok () ⟨regs, r :: l :: rest⟩ :=
    intKind.nos_eval regs rest l r
  constructor
  · rintro a b rfl rfl ha hb' hab
    have h1 : notCompactInt (.int b) = false := (notCompactInt_iff _).2 ⟨b, rfl, hb'⟩
    have h2 : notCompactInt (.int a) = false := (notCompactInt_iff _).2 ⟨a, rfl, ha⟩
    simp only [bind, EStateM.bind, ht, hn, h1, h2, Bool.false_eq_true, ite_false]
    exact (hb regs rest a b ha hb').1 hab
  · intro hne
    by_cases hr : notCompactInt r = true
    · exact ⟨⟨regs, r :: l :: rest⟩, by simp [bind, EStateM.bind, ht, hr]⟩
    · by_cases hl : notCompactInt l = true
      · exact ⟨⟨regs, r :: l :: rest⟩, by simp [bind, EStateM.bind, ht, hn, hr, hl]⟩
      · simp only [Bool.not_eq_true] at hr hl
        obtain ⟨a, rfl, ha⟩ := (notCompactInt_iff _).1 hl
        obtain ⟨b, rfl, hb'⟩ := (notCompactInt_iff _).1 hr
        have hab : ¬ Compact (op a b) := fun h => hne ⟨a, b, rfl, rfl, ha, hb', h⟩
        obtain ⟨s', hs'⟩ := (hb regs rest a b ha hb').2 hab
        exact ⟨s', by simp only [bind, EStateM.bind, ht, hn, hr, hl, Bool.false_eq_true, ite_false]; exact hs'⟩

/-- The compact-int forms of `BINARY_OP`, `Python/bytecodes.c:657-709`: each uop answers
`left * right`, `left + right` or `left - right` on compact operands when the result is compact
and otherwise exits, and each macro (`_GUARD_TOS_INT + _GUARD_NOS_INT + uop + _POP_TOP_INT +
_POP_TOP_INT`) answers exactly when both operands and the result are compact ints. The left
operand is the second value on the stack. -/
def BinaryIntFast : Prop :=
  IntUop _BINARY_OP_MULTIPLY_INT (· * ·) ∧ IntArith BINARY_OP_MULTIPLY_INT (· * ·) ∧
  IntUop _BINARY_OP_ADD_INT (· + ·) ∧ IntArith BINARY_OP_ADD_INT (· + ·) ∧
  IntUop _BINARY_OP_SUBTRACT_INT (· - ·) ∧ IntArith BINARY_OP_SUBTRACT_INT (· - ·)

theorem binaryIntFast_proven : BinaryIntFast := by
  have hm : IntUop _BINARY_OP_MULTIPLY_INT (· * ·) := intUop_of _ _ fun _ _ => rfl
  have ha : IntUop _BINARY_OP_ADD_INT (· + ·) := intUop_of _ _ fun _ _ => rfl
  have hs : IntUop _BINARY_OP_SUBTRACT_INT (· - ·) := intUop_of _ _ fun _ _ => rfl
  exact ⟨hm, intArith_of _ _ hm, ha, intArith_of _ _ ha, hs, intArith_of _ _ hs⟩

/-- A uop on two values of one type that always answers `op left right`. -/
def KindUop (m : M Unit) (K : Val → Prop) (op : Val → Val → Val) : Prop :=
  ∀ (regs : Regs) (rest : List Val) (l r : Val), K l → K r →
    m ⟨regs, r :: l :: rest⟩ = .ok () ⟨regs, op l r :: rest⟩

/-- A binary64 or str macro: it answers `op left right` exactly when both operands are of the
type, and otherwise exits with the state unchanged. -/
def KindArith (m : M Unit) (K : Val → Prop) (op : Val → Val → Val) : Prop :=
  ∀ (regs : Regs) (rest : List Val) (l r : Val),
    (K l → K r → m ⟨regs, r :: l :: rest⟩ = .ok () ⟨regs, op l r :: rest⟩) ∧
    (¬ (K l ∧ K r) → m ⟨regs, r :: l :: rest⟩ = .error .deopt ⟨regs, r :: l :: rest⟩)

/-- `fadd` and friends lifted to values. -/
def fop (f : UInt64 → UInt64 → UInt64) : Val → Val → Val
  | .float a, .float b => .float (f a b)
  | _, _ => .null

/-- Concatenation lifted to values. -/
def sconcat : Val → Val → Val
  | .str a, .str b => .str (a ++ b)
  | _, _ => .null

theorem kindArith_of (K : Kind) (P : Val → Prop) (hP : ∀ v, K.bad v = false ↔ P v)
    (body : M Unit) (op : Val → Val → Val) (hb : KindUop body P op) :
    KindArith (do K.tos; K.nos; body) P op := by
  intro regs rest l r
  have ht := K.tos_eval regs (l :: rest) r
  have hn := K.nos_eval regs rest l r
  constructor
  · intro hl hr
    have h1 := (hP r).2 hr
    have h2 := (hP l).2 hl
    simp only [bind, EStateM.bind, ht, hn, h1, h2, Bool.false_eq_true, ite_false]
    exact hb regs rest l r hl hr
  · intro hlr
    by_cases hr : K.bad r = true
    · simp [bind, EStateM.bind, ht, hr]
    · simp only [Bool.not_eq_true] at hr
      cases hl : K.bad l
      · exact absurd ⟨(hP l).1 hl, (hP r).1 hr⟩ hlr
      · simp [bind, EStateM.bind, ht, hn, hr, hl]

theorem floatUop_of (body : List Val → BM (List Val)) (f : UInt64 → UInt64 → UInt64)
    (hb : ∀ a b, body [.float a, .float b] = pure [.float (f a b)]) :
    KindUop (stk 2 1 body) IsFloat (fop f) := by
  rintro regs rest _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
  bc_simp [hb, fop]

/-- The binary64 forms of `BINARY_OP`, `Python/bytecodes.c:778-842`, and `BINARY_OP_ADD_UNICODE`,
`:945-963`: each uop answers the IEEE-754 product, sum or difference (`Binary64.F64`) of two
exact floats, or the concatenation of two exact strs, `left` being the second value on the
stack; each macro (`_GUARD_TOS_* + _GUARD_NOS_* + uop + _POP_TOP_* + _POP_TOP_*`) answers
exactly when both operands have the type and exits with the state unchanged otherwise. -/
def BinaryKindFast : Prop :=
  KindUop _BINARY_OP_MULTIPLY_FLOAT IsFloat (fop fmul) ∧
  KindArith BINARY_OP_MULTIPLY_FLOAT IsFloat (fop fmul) ∧
  KindUop _BINARY_OP_ADD_FLOAT IsFloat (fop fadd) ∧ KindArith BINARY_OP_ADD_FLOAT IsFloat (fop fadd) ∧
  KindUop _BINARY_OP_SUBTRACT_FLOAT IsFloat (fop fsub) ∧
  KindArith BINARY_OP_SUBTRACT_FLOAT IsFloat (fop fsub) ∧
  KindUop _BINARY_OP_ADD_UNICODE IsStr sconcat ∧ KindArith BINARY_OP_ADD_UNICODE IsStr sconcat

theorem binaryKindFast_proven : BinaryKindFast := by
  have hm : KindUop _BINARY_OP_MULTIPLY_FLOAT IsFloat (fop fmul) := floatUop_of _ _ fun _ _ => rfl
  have ha : KindUop _BINARY_OP_ADD_FLOAT IsFloat (fop fadd) := floatUop_of _ _ fun _ _ => rfl
  have hs : KindUop _BINARY_OP_SUBTRACT_FLOAT IsFloat (fop fsub) := floatUop_of _ _ fun _ _ => rfl
  have hu : KindUop _BINARY_OP_ADD_UNICODE IsStr sconcat := by
    rintro regs rest _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    bc_simp [_BINARY_OP_ADD_UNICODE, sconcat]
  exact ⟨hm, kindArith_of floatKind _ notFloat_iff _ _ hm, ha, kindArith_of floatKind _ notFloat_iff _ _ ha,
    hs, kindArith_of floatKind _ notFloat_iff _ _ hs, hu, kindArith_of strKind _ notStr_iff _ _ hu⟩

/-! ## Subscripts -/

/-- `if (index < 0) index += PyList_GET_SIZE(list)`, `Python/bytecodes.c:1144-1146` and
`:1434-1436`. -/
def normIndex (i : Int) (n : Nat) : Int := if i < 0 then i + n else i

/-- `BINARY_OP_SUBSCR_LIST_INT`, `Python/bytecodes.c:1134-1162`: on an exact list and a compact
int it answers the item, a negative index counting from the end (new in 3.15), and it exits on
any other operands and on an index outside the list after that adjustment. -/
def SubscrListFast : Prop := ∀ (regs : Regs) (rest : List Val) (l r : Val), Live regs.rt l →
  (∀ a items i v, l = .ref a → regs.rt.heap[a]? = some (.list items) → r = .int i → Compact i →
    0 ≤ normIndex i items.size → items[(normIndex i items.size).toNat]? = some v →
    BINARY_OP_SUBSCR_LIST_INT ⟨regs, r :: l :: rest⟩ = .ok () ⟨regs, v :: rest⟩) ∧
  (¬ (∃ a items i v, l = .ref a ∧ regs.rt.heap[a]? = some (.list items) ∧ r = .int i ∧ Compact i ∧
      0 ≤ normIndex i items.size ∧ items[(normIndex i items.size).toNat]? = some v) →
    Deopts (BINARY_OP_SUBSCR_LIST_INT ⟨regs, r :: l :: rest⟩))

theorem live_int (rt : Rt) (i : Int) : Live rt (.int i) := by simp [Live]
theorem live_str (rt : Rt) (t : String) : Live rt (.str t) := by simp [Live]

theorem subscrListFast_proven : SubscrListFast := by
  intro regs rest l r hl
  obtain ⟨gti, _, _, _, _, _, _, _, gnl, _, _, _, _⟩ := guardRules_proven
  constructor
  · rintro a items i v rfl ho rfl hc hn hv
    have h1 := (gti regs (.ref a :: rest) _ (live_int _ i)).1 ⟨i, rfl, hc⟩
    have h2 := (gnl regs rest _ (.int i) hl).1 ⟨a, items, rfl, ho⟩
    show (do _GUARD_TOS_INT; _GUARD_NOS_LIST; _BINARY_OP_SUBSCR_LIST_INT) _ = _
    simp only [bind, EStateM.bind, h1, h2]
    unfold normIndex at hn hv
    by_cases hneg : i < 0
    · simp only [hneg, ite_true] at hn hv
      have : ¬ (i + items.size < 0) := by omega
      bc_simp [_BINARY_OP_SUBSCR_LIST_INT, ho, hneg, this, hv]
    · simp only [hneg, ite_false] at hn hv
      bc_simp [_BINARY_OP_SUBSCR_LIST_INT, ho, hneg, hv]
  · intro hne
    by_cases hr : CompactInt r
    · obtain ⟨i, rfl, hc⟩ := hr
      have h1 := guard_tos_int_pass (regs := regs) (rest := l :: rest) hc
      by_cases hli : IsList regs.rt l
      · have h2 := (gnl regs rest l (.int i) hl).1 hli
        obtain ⟨a, items, rfl, ho⟩ := hli
        refine ⟨⟨regs, rest⟩, ?_⟩
        show (do _GUARD_TOS_INT; _GUARD_NOS_LIST; _BINARY_OP_SUBSCR_LIST_INT) _ = _
        simp only [bind, EStateM.bind, h1, h2]
        have hno : ∀ v, ¬ (0 ≤ normIndex i items.size ∧ items[(normIndex i items.size).toNat]? = some v) :=
          fun v ⟨h3, h4⟩ => hne ⟨a, items, i, v, rfl, ho, rfl, hc, h3, h4⟩
        unfold normIndex at hno
        by_cases hneg : i < 0
        · simp only [hneg, ite_true] at hno
          by_cases hz : i + items.size < 0
          · bc_simp [_BINARY_OP_SUBSCR_LIST_INT, ho, hneg, hz]
          · have hz' : 0 ≤ i + items.size := by omega
            cases hv : items[(i + (items.size : Int)).toNat]? with
            | none => bc_simp [_BINARY_OP_SUBSCR_LIST_INT, ho, hneg, hz, hv]
            | some v => exact absurd ⟨hz', hv⟩ (hno v)
        · simp only [hneg, ite_false] at hno
          have hz' : 0 ≤ i := by omega
          cases hv : items[i.toNat]? with
          | none => bc_simp [_BINARY_OP_SUBSCR_LIST_INT, ho, hneg, hv]
          | some v => exact absurd ⟨hz', hv⟩ (hno v)
      · exact ⟨_, by simp only [BINARY_OP_SUBSCR_LIST_INT, bind, EStateM.bind, h1,
          (gnl regs rest l (.int i) hl).2 hli]; rfl⟩
    · exact ⟨_, by simp only [BINARY_OP_SUBSCR_LIST_INT, bind, EStateM.bind, guard_tos_int_fail hr]; rfl⟩

end PyLean.Bytecode
