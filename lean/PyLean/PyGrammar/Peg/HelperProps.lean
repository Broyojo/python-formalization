import PyLean.PyGrammar.Peg.ImportProps

/-!
What the action helpers of `Parser/action_helpers.c` compute, helper by helper: the node they
build, the exception they raise (class, message, location), and the state they leave. Each
statement unfolds the helper's mirror in `Peg/Actions.lean` through `callHelper` (the dispatch the
grammar actions use), so a helper with another message, another check order or another result
fails it.

Allocation failures (`_PyArena_Malloc`, `_Py_asdl_*_seq_new`, `PyUnicodeWriter_*` returning `NULL`
with `MemoryError` set) are out of scope throughout: the model has no allocator.
-/

namespace PyLean.PyGrammar.Peg

open Lexer

/-! ### `_PyPegen_check_fstring_conversion` and `result_token_with_metadata` -/

/-- `conv_token->metadata`, as `result_token_with_metadata` stores it. -/
def tokMeta (t : Ast) : Ast :=
  match t with
  | .tok t => (t.metadata.map Ast.str).getD .null
  | _ => .null

/-- The message of the adjacency check, `Parser/action_helpers.c:1009-1013`. -/
def convAdjMsg (p : PS) : String :=
  s!"{chStr (tokPrefix p)}-string: conversion type must come right after the exclamation mark"

/-- The message of the conversion-character check, `Parser/action_helpers.c:1019-1022`, `%R`
being `repr` of the name. -/
def convCharMsg (p : PS) (id : List Nat) : String :=
  s!"{chStr (tokPrefix p)}-string: invalid conversion character {cpsStr (Unparse.strRepr id)}: expected 's', 'r', or 'a'"

/-- `_PyPegen_check_fstring_conversion(p, conv_token, conv)` (`Parser/action_helpers.c:1005-1027`,
`fstring_conversion` and `tstring_conversion` in `Grammar/python.gram:976-977,989-990`), for the
`!` token `bang` and the `NAME` `conv` after it:
* when `conv` does not start where `!` ends (another line, or a gap), `NULL` and "f-string:
  conversion type must come right after the exclamation mark" over `!` .. the name, checked first;
* otherwise, a name other than `s`, `r`, `a` (longer than one character, or another one) gives
  `NULL` and "f-string: invalid conversion character 'ab': expected 's', 'r', or 'a'" at the name,
  with `repr` of the name;
* otherwise the result record of the name and the `!` token's metadata, state unchanged.
The prefix letter is the tokenizer's current mode (`t` in a t-string). Hypothesis: `conv` is a
`Name` (the grammar passes a `NAME`). -/
def CheckFstringConversion : Prop := ∀ (bang conv : Ast) (p : PS),
  (((locOf bang).lineno ≠ (locOf conv).lineno ∨ (locOf bang).endColOffset ≠ (locOf conv).colOffset) →
    callHelper .check_fstring_conversion [bang, conv] p =
      (.null, (raiseRange "SyntaxError" bang conv (convAdjMsg p) p).2)) ∧
  ((locOf bang).lineno = (locOf conv).lineno → (locOf bang).endColOffset = (locOf conv).colOffset →
    ∀ id, fieldOf conv "id" = .ident id →
    ((id = [ch! 's'] ∨ id = [ch! 'r'] ∨ id = [ch! 'a']) →
      callHelper .check_fstring_conversion [bang, conv] p =
        (rec_ .PResultTokenWithMetadata [conv, tokMeta bang], p)) ∧
    (¬(id = [ch! 's'] ∨ id = [ch! 'r'] ∨ id = [ch! 'a']) →
      callHelper .check_fstring_conversion [bang, conv] p =
        (.null, (raiseErrorKnownLocation "SyntaxError" (locOf conv).lineno (locOf conv).colOffset
          (locOf conv).endLineno (locOf conv).endColOffset (convCharMsg p id) p).2)))

theorem conv_cond (id : List Nat) :
    (decide (id.length > 1) || !(id.headD 0 == ch! 's' || id.headD 0 == ch! 'r' ||
      id.headD 0 == ch! 'a')) = true ↔ ¬(id = [ch! 's'] ∨ id = [ch! 'r'] ∨ id = [ch! 'a']) := by
  match id with
  | [] => decide
  | [x] =>
    simp only [List.length_singleton, List.headD_cons, List.cons.injEq, and_true]
    by_cases h1 : x = ch! 's'
    · subst h1; decide
    · by_cases h2 : x = ch! 'r'
      · subst h2; decide
      · by_cases h3 : x = ch! 'a'
        · subst h3; decide
        · simp [h1, h2, h3]
  | x :: y :: r => simp

theorem checkFstringConversion_proven : CheckFstringConversion := by
  intro bang conv p
  have hc : callHelper .check_fstring_conversion [bang, conv] p = checkFstringConversion bang conv p :=
    rfl
  rw [hc]
  refine ⟨fun h => ?_, fun h1 h2 id hid => ⟨fun hok => ?_, fun hbad => ?_⟩⟩
  · have hn : notAdjacent bang conv = true := by
      simp only [notAdjacent]
      rcases h with h | h <;> simp [h]
    simp only [checkFstringConversion, hn, bind, StateT.bind, get, getThe, MonadStateOf.get,
      StateT.get, pure, StateT.pure, ↓reduceIte]
    unfold convAdjMsg
    rfl
  · have hn : notAdjacent bang conv = false := by simp [notAdjacent, h1, h2]
    have hk : ¬ ((decide (id.length > 1) || !(id.headD 0 == ch! 's' || id.headD 0 == ch! 'r' ||
        id.headD 0 == ch! 'a')) = true) := fun h => (conv_cond id).1 h hok
    simp only [checkFstringConversion, hn, hid, bind, StateT.bind, get, getThe, MonadStateOf.get,
      StateT.get, pure, StateT.pure, Bool.false_eq_true, ↓reduceIte, hk, tokMeta]
    rfl
  · have hn : notAdjacent bang conv = false := by simp [notAdjacent, h1, h2]
    have hk := (conv_cond id).2 hbad
    simp only [checkFstringConversion, hn, hid, bind, StateT.bind, get, getThe, MonadStateOf.get,
      StateT.get, pure, StateT.pure, Bool.false_eq_true, ↓reduceIte, hk]
    unfold convCharMsg
    rfl

/-! ### `_PyPegen_get_expr_name` -/

/-- The `SystemError` of `_PyPegen_get_expr_name` on a `Slice` at `l`, written out. -/
def sliceNameErr (fs : List Ast) (l : Option Loc) : PyError :=
  { cls := "SystemError"
    msg := s!"unexpected expression in assignment {(29 : Int)} (line {(locOf (.node .Slice fs l)).lineno})" }

/-- The name `_PyPegen_get_expr_name` gives a node, through `callHelper`. -/
def ExprNameIs (c : Ctor) (fs : List Ast) (l : Option Loc) (nm : String) : Prop :=
  ∀ p : PS, callHelper .get_expr_name [.node c fs l] p = (.str (nm.toList.map Char.toNat), p)

/-- `_PyPegen_get_expr_name` (`Parser/action_helpers.c:1083-1159`), the switch on `e->kind`, case
by case, for any fields and location: the 28 named kinds (`BoolOp`, `BinOp` and `UnaryOp` all
"expression"; `JoinedStr`/`FormattedValue` "f-string expression", `TemplateStr`/`Interpolation`
"t-string expression"), and `Constant` by the identity of its value (`None`, `False`, `True`,
`Ellipsis`, otherwise "literal"); state unchanged. Among expression kinds only `Slice`, the one
kind absent from the switch, reaches the default case: `NULL` with `SystemError` "unexpected
expression in assignment 29 (line <lineno>)" (`%d` of `Slice_kind` and of `e->lineno`). No rule
passes a `Slice` (every caller in `Grammar/python.gram` passes a target, an expression or a
pattern); were one passed, the callers' `%s` of `NULL` would be `strlen(NULL)` in
`unicode_fromformat_write_utf8` (`Objects/unicodeobject.c:2630`), where the model formats "". -/
def ExprNameTable : Prop := ∀ (fs : List Ast) (l : Option Loc),
  ExprNameIs .Attribute fs l "attribute" ∧ ExprNameIs .Subscript fs l "subscript" ∧
  ExprNameIs .Starred fs l "starred" ∧ ExprNameIs .Name fs l "name" ∧
  ExprNameIs .List fs l "list" ∧ ExprNameIs .Tuple fs l "tuple" ∧
  ExprNameIs .Lambda fs l "lambda" ∧ ExprNameIs .Call fs l "function call" ∧
  ExprNameIs .BoolOp fs l "expression" ∧ ExprNameIs .BinOp fs l "expression" ∧
  ExprNameIs .UnaryOp fs l "expression" ∧ ExprNameIs .GeneratorExp fs l "generator expression" ∧
  ExprNameIs .Yield fs l "yield expression" ∧ ExprNameIs .YieldFrom fs l "yield expression" ∧
  ExprNameIs .Await fs l "await expression" ∧ ExprNameIs .ListComp fs l "list comprehension" ∧
  ExprNameIs .SetComp fs l "set comprehension" ∧ ExprNameIs .DictComp fs l "dict comprehension" ∧
  ExprNameIs .Dict fs l "dict literal" ∧ ExprNameIs .Set fs l "set display" ∧
  ExprNameIs .JoinedStr fs l "f-string expression" ∧
  ExprNameIs .FormattedValue fs l "f-string expression" ∧
  ExprNameIs .TemplateStr fs l "t-string expression" ∧
  ExprNameIs .Interpolation fs l "t-string expression" ∧
  ExprNameIs .Compare fs l "comparison" ∧ ExprNameIs .IfExp fs l "conditional expression" ∧
  ExprNameIs .NamedExpr fs l "named expression" ∧
  ExprNameIs .Constant (.const .none :: fs) l "None" ∧
  ExprNameIs .Constant (.const .false_ :: fs) l "False" ∧
  ExprNameIs .Constant (.const .true_ :: fs) l "True" ∧
  ExprNameIs .Constant (.const .ellipsis :: fs) l "ellipsis" ∧
  (∀ v : PyConst, (match v with | .none | .false_ | .true_ | .ellipsis => False | _ => True) →
    ExprNameIs .Constant (.const v :: fs) l "literal") ∧
  (∀ p : PS, callHelper .get_expr_name [.node .Slice fs l] p =
    (.null, (setErr (sliceNameErr fs l) p).2)) ∧
  (∀ c : Ctor, c.asdlType? = some .expr_ → c ≠ .Slice → (exprName (.node c fs l)).isSome)

theorem exprNameTable_proven : ExprNameTable := by
  intro fs l
  refine ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ => rfl, fun v hv _ => ?_, fun p => ?_, fun c hc hs => ?_⟩
  · cases v <;> first | exact absurd hv id | rfl
  · have he : exprNameErr (.node .Slice fs l) = sliceNameErr fs l := by
      simp only [exprNameErr, sliceNameErr, exprKindOf, exprKindNum]
    have hc : callHelper .get_expr_name [.node .Slice fs l] p =
        (.null, (setErr (exprNameErr (.node .Slice fs l)) p).2) := rfl
    rw [hc, he]
  · cases c <;> first | rfl | exact absurd rfl hs | exact absurd hc (by decide) | (simp only [exprName]; split <;> rfl)

/-! ### `_PyPegen_arguments_parsing_error`, `_PyPegen_nonparen_genexp_in_call`,
`_PyPegen_get_last_comprehension_item` -/

/-- `_PyPegen_arguments_parsing_error(p, e)` (`Parser/action_helpers.c:1271-1288`, called by
`invalid_arguments` on a call whose positional argument follows keywords): `NULL` and the
`SyntaxError` `RAISE_SYNTAX_ERROR` raises at the last token, "positional argument follows keyword
argument unpacking" when some keyword of the call is a `**` unpacking (its `arg` is `NULL`),
"positional argument follows keyword argument" otherwise. -/
def ArgumentsParsingError : Prop := ∀ (e : Ast) (p : PS),
  ((∃ k ∈ seqOf (fieldOf e "keywords"), fieldOf k "arg" = .null) →
    callHelper .arguments_parsing_error [e] p =
      (.null, (raiseError0 "SyntaxError" "positional argument follows keyword argument unpacking" p).2)) ∧
  ((∀ k ∈ seqOf (fieldOf e "keywords"), fieldOf k "arg" ≠ .null) →
    callHelper .arguments_parsing_error [e] p =
      (.null, (raiseError0 "SyntaxError" "positional argument follows keyword argument" p).2))

/-- The `kwarg_unpacking` loop of `_PyPegen_arguments_parsing_error`. -/
def kwUnpackOf (e : Ast) : Bool :=
  (seqOf (fieldOf e "keywords")).any fun k =>
    match fieldOf k "arg" with
    | .null => true
    | _ => false

theorem argumentsParsingError_eq (e : Ast) (p : PS) : callHelper .arguments_parsing_error [e] p =
    (.null, (raiseError0 "SyntaxError" (argumentErrorMessage (kwUnpackOf e)) p).2) := rfl

theorem argumentsParsingError_proven : ArgumentsParsingError := by
  intro e p
  rw [argumentsParsingError_eq]
  refine ⟨fun ⟨k, hk, ha⟩ => ?_, fun h => ?_⟩
  · have hany : kwUnpackOf e = true := List.any_eq_true.2 ⟨k, hk, by rw [ha]⟩
    rw [hany]
    rfl
  · have hany : kwUnpackOf e = false := by
      unfold kwUnpackOf
      rw [List.any_eq_false]
      intro k hk
      have := h k hk
      cases hf : fieldOf k "arg" <;> simp_all
    rw [hany]
    rfl

/-- `_PyPegen_get_last_comprehension_item` (`Parser/action_helpers.c:1161-1167`): the last `if` of
the comprehension, or its `iter` when it has none (`ifs` `NULL` or empty). -/
def LastComprehensionItem : Prop := ∀ (c : Ast),
  (seqOf (fieldOf c "ifs") = [] → lastComprehensionItem c = fieldOf c "iter") ∧
  (∀ xs x, seqOf (fieldOf c "ifs") = xs ++ [x] → lastComprehensionItem c = x)

theorem lastComprehensionItem_proven : LastComprehensionItem := by
  intro c
  refine ⟨fun h => ?_, fun xs x h => ?_⟩
  · simp [lastComprehensionItem, h]
  · simp [lastComprehensionItem, h]

/-- `_PyPegen_nonparen_genexp_in_call(p, args, comprehensions)` (`Parser/action_helpers.c:1290-1313`,
`invalid_arguments`' `a=args b=for_if_clauses`): with at most one positional argument in the call
(`dict((a, b) for a, b in x)`), `NULL` and no exception, state unchanged; with more,
`NULL` and "Generator expression must be parenthesized" from the last positional argument to the
last item (`_PyPegen_get_last_comprehension_item`) of the last comprehension. -/
def NonparenGenexp : Prop := ∀ (call comps : Ast) (p : PS),
  ((seqOf (fieldOf call "args")).length ≤ 1 →
    callHelper .nonparen_genexp_in_call [call, comps] p = (.null, p)) ∧
  (1 < (seqOf (fieldOf call "args")).length →
    callHelper .nonparen_genexp_in_call [call, comps] p =
      (.null, (raiseRange "SyntaxError" ((seqOf (fieldOf call "args")).getLastD .null)
        (lastComprehensionItem ((seqOf comps).getLastD .null))
        "Generator expression must be parenthesized" p).2))

theorem nonparenGenexp_proven : NonparenGenexp := by
  intro call comps p
  have hc : callHelper .nonparen_genexp_in_call [call, comps] p = nonparenGenexp call comps p := rfl
  rw [hc]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp [nonparenGenexp, h, pure, StateT.pure]
  · have h' : ¬ (seqOf (fieldOf call "args")).length ≤ 1 := by omega
    simp only [nonparenGenexp, h', bind, StateT.bind, pure, StateT.pure, decide_false,
      Bool.false_eq_true, ↓reduceIte]
    rfl

/-! ### `_PyPegen_check_legacy_stmt`, `_PyPegen_check_barry_as_flufl`,
`_PyPegen_ensure_imaginary`, `_PyPegen_ensure_real` -/

theorem int_pair_ne {a b : Int} (p q : PS) (h : a ≠ b) :
    ((Ast.int a, p) : Ast × PS) ≠ (Ast.int b, q) :=
  fun e => h (Ast.int.inj (Prod.mk.inj e).1)

/-- `_PyPegen_check_legacy_stmt(p, name)` (`Parser/action_helpers.c:950-962`): 1 for a `Name` whose
id is `print` or `exec`, 0 for any other name and for any other node; state unchanged. -/
def CheckLegacyStmt : Prop := ∀ (e : Ast) (p : PS),
  (∀ id rest l, e = .node .Name (.ident id :: rest) l →
    (callHelper .check_legacy_stmt [e] p = (.int 1, p) ↔ (id = "print".toList.map Char.toNat ∨
      id = "exec".toList.map Char.toNat)) ∧
    (callHelper .check_legacy_stmt [e] p = (.int 0, p) ↔ ¬(id = "print".toList.map Char.toNat ∨
      id = "exec".toList.map Char.toNat))) ∧
  ((∀ fs l, e ≠ .node .Name fs l) → callHelper .check_legacy_stmt [e] p = (.int 0, p))

theorem checkLegacyStmt_proven : CheckLegacyStmt := by
  intro e p
  refine ⟨fun id rest l he => ?_, fun h => ?_⟩
  · subst he
    have hp : "print".toList.map Char.toNat = [112, 114, 105, 110, 116] := by decide
    have hx : "exec".toList.map Char.toNat = [101, 120, 101, 99] := by decide
    rw [hp, hx]
    by_cases h : id = [112, 114, 105, 110, 116] ∨ id = [101, 120, 101, 99]
    · have hl : isLegacyStmt (.node .Name (.ident id :: rest) l) = true := by
        rcases h with h | h <;> simp [isLegacyStmt, h]
      have e1 : callHelper .check_legacy_stmt [.node .Name (.ident id :: rest) l] p = (.int 1, p) := by
        simp only [callHelper, List.getD_cons_zero, hl, ↓reduceIte, pure, StateT.pure]
      rw [e1]
      exact ⟨⟨fun _ => h, fun _ => rfl⟩, ⟨fun e => absurd e (int_pair_ne p p (by decide)),
        fun hh => absurd h hh⟩⟩
    · have hl : isLegacyStmt (.node .Name (.ident id :: rest) l) = false := by
        simp only [isLegacyStmt]
        simp only [not_or] at h
        simp [h.1, h.2]
      have e1 : callHelper .check_legacy_stmt [.node .Name (.ident id :: rest) l] p = (.int 0, p) := by
        simp only [callHelper, List.getD_cons_zero, hl, Bool.false_eq_true, ↓reduceIte, pure,
          StateT.pure]
      rw [e1]
      exact ⟨⟨fun e => absurd e (int_pair_ne p p (by decide)), fun hh => absurd hh h⟩,
        ⟨fun _ => h, fun _ => rfl⟩⟩
  · have hl : isLegacyStmt e = false := by
      unfold isLegacyStmt
      split
      · rename_i id rest l
        exact absurd rfl (h _ l)
      · rfl
    simp only [callHelper, List.getD_cons_zero, hl, Bool.false_eq_true, ↓reduceIte, pure,
      StateT.pure]

/-- `_PyPegen_check_barry_as_flufl(p, t)` (`Parser/action_helpers.c:934-948`, the `NOTEQUAL` of
`compare_op_bitwise_or_pair`/`noteq_bitwise_or`), on a `!=` or `<>` token: under `from __future__
import barry_as_FLUFL`, `!=` raises "with Barry as BDFL, use '<>' instead of '!='" and gives -1,
`<>` gives 0; without it, `!=` gives 0 and `<>` a nonzero value (`strcmp`, whose magnitude the
grammar never reads: it tests the result for truth), with no exception. Hypothesis: the token is
`NOTEQUAL`, so its text is `!=` or `<>` (`assert(t->type == NOTEQUAL)`). -/
def CheckBarry : Prop := ∀ (t : Token) (p : PS),
  (p.flagBarry = true → t.bytes = [33, 61] →
    callHelper .check_barry_as_flufl [.tok t] p = (.int (-1),
      (raiseError0 "SyntaxError" "with Barry as BDFL, use '<>' instead of '!='" p).2)) ∧
  (p.flagBarry = true → t.bytes = [60, 62] → callHelper .check_barry_as_flufl [.tok t] p = (.int 0, p)) ∧
  (p.flagBarry = false → t.bytes = [33, 61] → callHelper .check_barry_as_flufl [.tok t] p = (.int 0, p)) ∧
  (p.flagBarry = false → t.bytes = [60, 62] →
    ∃ v, v ≠ 0 ∧ callHelper .check_barry_as_flufl [.tok t] p = (.int v, p))

theorem checkBarry_proven : CheckBarry := by
  intro t p
  have hc : callHelper .check_barry_as_flufl [.tok t] p = checkBarry (.tok t) p := rfl
  rw [hc]
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 h2 => ⟨1, by decide, ?_⟩⟩
  · simp only [checkBarry, h1, h2, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      pure, StateT.pure]
    simp only [show ([33, 61] : List Nat) != [60, 62] from rfl, Bool.and_self, ↓reduceIte]
    rfl
  · simp [checkBarry, h1, h2, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      pure, StateT.pure]
  · simp [checkBarry, h1, h2, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      pure, StateT.pure]
  · simp [checkBarry, h1, h2, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      pure, StateT.pure]

/-- `_PyPegen_ensure_imaginary` and `_PyPegen_ensure_real` (`Parser/action_helpers.c:853-871`, the
two halves of a complex literal pattern `1 + 2j`): the imaginary one passes a `Constant` holding
a `complex` through, the real one a `Constant` holding anything else; every other node raises at
the node, "imaginary number required in complex literal" or "real number required in complex
literal", and gives `NULL`. -/
def EnsureComplexParts : Prop := ∀ (e : Ast) (p : PS),
  let l := locOf e
  let imErr := (raiseErrorKnownLocation "SyntaxError" l.lineno l.colOffset l.endLineno
    l.endColOffset "imaginary number required in complex literal" p).2
  let reErr := (raiseErrorKnownLocation "SyntaxError" l.lineno l.colOffset l.endLineno
    l.endColOffset "real number required in complex literal" p).2
  (isComplexConst e = true →
    callHelper .ensure_imaginary [e] p = (e, p) ∧ callHelper .ensure_real [e] p = (.null, reErr)) ∧
  (isConstant e = true → isComplexConst e = false →
    callHelper .ensure_real [e] p = (e, p) ∧ callHelper .ensure_imaginary [e] p = (.null, imErr)) ∧
  (isConstant e = false →
    callHelper .ensure_real [e] p = (.null, reErr) ∧ callHelper .ensure_imaginary [e] p = (.null, imErr))

theorem complex_const (e : Ast) (h : isComplexConst e = true) : isConstant e = true := by
  unfold isComplexConst at h
  split at h
  · rfl
  · exact absurd h (by simp)

theorem ensureComplexParts_proven : EnsureComplexParts := by
  intro e p
  have hi : callHelper .ensure_imaginary [e] p = ensureImaginary e p := rfl
  have hr : callHelper .ensure_real [e] p = ensureReal e p := rfl
  simp only [hi, hr]
  refine ⟨fun h => ?_, fun h1 h2 => ?_, fun h => ?_⟩
  · have hc := complex_const e h
    refine ⟨?_, ?_⟩
    · simp [ensureImaginary, h, hc, pure, StateT.pure]
    · simp only [ensureReal, h, hc, bind, StateT.bind, pure, StateT.pure, Bool.not_true,
        Bool.or_true, ↓reduceIte]
      rfl
  · refine ⟨?_, ?_⟩
    · simp [ensureReal, h1, h2, pure, StateT.pure]
    · simp only [ensureImaginary, h1, h2, bind, StateT.bind, pure, StateT.pure, Bool.and_false,
        Bool.not_false, ↓reduceIte]
      rfl
  · have hc : isComplexConst e = false := by
      cases hh : isComplexConst e
      · rfl
      · rw [complex_const e hh] at h; exact absurd h (by simp)
    refine ⟨?_, ?_⟩
    · simp only [ensureReal, h, bind, StateT.bind, pure, StateT.pure, Bool.not_false,
        Bool.true_or, ↓reduceIte]
      rfl
    · simp only [ensureImaginary, h, bind, StateT.bind, pure, StateT.pure, Bool.false_and,
        Bool.not_false, ↓reduceIte]
      rfl

/-! ### String concatenation: `_PyPegen_concatenate_strings`, `_build_concatenated_bytes`,
`_build_concatenated_unicode`, `_build_concatenated_str`, `_build_concatenated_joined_str`,
`_PyPegen_concatenate_tstrings` -/

theorem bytes_isConstant {e : Ast} (h : isBytesConst e = true) : isConstant e = true := by
  unfold isBytesConst at h
  split at h
  · rfl
  · exact absurd h (by simp)

/-- `_PyPegen_concatenate_strings(p, strings, EXTRA)` (`Parser/action_helpers.c:1970-2029`, the
`strings` rule's `(fstring|string)+`, python.gram:1013), on a non-empty sequence, through
`callHelper`:
* a bytes literal next to anything that is not bytes (a str or an f-string) raises "cannot mix
  bytes and nonbytes literals" at the last token and gives `NULL`;
* one literal alone is returned as it is (its own node and location);
* two or more bytes literals are one bytes `Constant` of their concatenation, with the `kind` of
  the first, over `EXTRA` (`_build_concatenated_bytes`, `:1689-1739`);
* two or more str literals likewise one str `Constant` (`_build_concatenated_unicode`,
  `:1741-1786`), so `u"a" "b"` keeps `kind` `u` and `"a" u"b"` has none;
* with an f-string among str literals, a `JoinedStr` over `EXTRA` of `_build_concatenated_str`
  (`_build_concatenated_joined_str`, `:1943-1954`).
State unchanged except by the raise. -/
def ConcatenateStrings : Prop := ∀ (xs : List Ast) (l c el ec : Int) (p : PS),
  (xs.any isBytesConst = true → xs.any (fun e => !isBytesConst e) = true →
    callHelper .concatenate_strings [.seq xs, .int l, .int c, .int el, .int ec] p =
      (.null, (raiseError0 "SyntaxError" "cannot mix bytes and nonbytes literals" p).2)) ∧
  (∀ x, xs = [x] → isConstant x = true →
    callHelper .concatenate_strings [.seq xs, .int l, .int c, .int el, .int ec] p = (x, p)) ∧
  (∀ x y r, xs = x :: y :: r → xs.all isBytesConst = true →
    callHelper .concatenate_strings [.seq xs, .int l, .int c, .int el, .int ec] p =
      (mkAt .Constant [.const (.bytes (xs.flatMap constBytes)), constKind x] ⟨l, c, el, ec⟩, p)) ∧
  (∀ x y r, xs = x :: y :: r → xs.all (fun e => isConstant e && !isBytesConst e) = true →
    callHelper .concatenate_strings [.seq xs, .int l, .int c, .int el, .int ec] p =
      (mkAt .Constant [.const (.str (xs.flatMap constStr)), constKind x] ⟨l, c, el, ec⟩, p)) ∧
  (xs.any (fun e => !isConstant e) = true → xs.any isBytesConst = false →
    callHelper .concatenate_strings [.seq xs, .int l, .int c, .int el, .int ec] p =
      (mkAt .JoinedStr [.seq (buildConcatenatedStr (.seq xs))] ⟨l, c, el, ec⟩, p))

theorem any_not_bytes {xs : List Ast} (h : xs.any (fun e => !isBytesConst e) = true) :
    (xs.any (fun e => isConstant e && !isBytesConst e) || xs.any (fun e => !isConstant e)) = true := by
  obtain ⟨e, he, hne⟩ := List.any_eq_true.1 h
  cases hk : isConstant e
  · exact Bool.or_eq_true_iff.2 (Or.inr (List.any_eq_true.2 ⟨e, he, by simp [hk]⟩))
  · exact Bool.or_eq_true_iff.2 (Or.inl (List.any_eq_true.2 ⟨e, he, by simp_all⟩))

theorem concatenateStrings_proven : ConcatenateStrings := by
  intro xs l c el ec p
  have hc : callHelper .concatenate_strings [.seq xs, .int l, .int c, .int el, .int ec] p =
      concatenateStrings (.seq xs) l c el ec p := rfl
  simp only [hc]
  refine ⟨fun hb hn => ?_, fun x hx hk => ?_, fun x y r hx ha => ?_, fun x y r hx ha => ?_,
    fun hf hb => ?_⟩
  · have hu := any_not_bytes hn
    simp only [concatenateStrings, seqOf, hu, hb, Bool.and_self, ↓reduceIte, bind, StateT.bind,
      pure, StateT.pure]
    rfl
  · subst hx
    cases hb : isBytesConst x <;>
      simp [concatenateStrings, seqOf, hb, hk, bind, StateT.bind, pure, StateT.pure]
  · subst hx
    have hall : ∀ e ∈ x :: y :: r, isBytesConst e = true := fun e he => List.all_eq_true.1 ha e he
    have hb : (x :: y :: r).any isBytesConst = true := List.any_eq_true.2 ⟨x, by simp, hall x (by simp)⟩
    have hu : (x :: y :: r).any (fun e => isConstant e && !isBytesConst e) = false :=
      List.any_eq_false.2 (fun e he => by simp [hall e he])
    have hf : (x :: y :: r).any (fun e => !isConstant e) = false :=
      List.any_eq_false.2 (fun e he => by simp [bytes_isConstant (hall e he)])
    simp only [concatenateStrings, seqOf, hu, hf, hb, Bool.or_self, Bool.false_and,
      Bool.false_eq_true, ↓reduceIte, Bool.not_false, bind, StateT.bind, pure, StateT.pure]
  · subst hx
    have hall : ∀ e ∈ x :: y :: r, (isConstant e && !isBytesConst e) = true :=
      fun e he => List.all_eq_true.1 ha e he
    have hb : (x :: y :: r).any isBytesConst = false :=
      List.any_eq_false.2 (fun e he => by have := hall e he; simp_all)
    have hf : (x :: y :: r).any (fun e => !isConstant e) = false :=
      List.any_eq_false.2 (fun e he => by have := hall e he; simp_all)
    simp only [concatenateStrings, seqOf, hf, hb, Bool.or_false, Bool.and_false,
      Bool.false_eq_true, ↓reduceIte, Bool.not_false, bind, StateT.bind, pure, StateT.pure]
  · simp only [concatenateStrings, seqOf, hf, hb, Bool.or_true, Bool.and_false,
      Bool.false_eq_true, ↓reduceIte, Bool.not_true, bind, StateT.bind, pure, StateT.pure]

/-- A node with its constructor replaced. -/
def retag (c : Ctor) : Ast → Ast
  | .node _ fs l => .node c fs l
  | a => a

/-- `_PyPegen_concatenate_tstrings(p, strings, EXTRA)` (`Parser/action_helpers.c:1956-1968`,
python.gram:1014 `tstring+`): a `TemplateStr` over `EXTRA` of `_build_concatenated_str`, state
unchanged; and the t-string twin of the f-string path: for the same parts (an interpolation among
them, no bytes), the `TemplateStr` is the `JoinedStr` `_PyPegen_concatenate_strings` builds, with
the constructor changed and nothing else. -/
def ConcatenateTstrings : Prop := ∀ (xs : List Ast) (l c el ec : Int) (p : PS),
  callHelper .concatenate_tstrings [.seq xs, .int l, .int c, .int el, .int ec] p =
    (mkAt .TemplateStr [.seq (buildConcatenatedStr (.seq xs))] ⟨l, c, el, ec⟩, p) ∧
  (xs.any (fun e => !isConstant e) = true → xs.any isBytesConst = false →
    callHelper .concatenate_tstrings [.seq xs, .int l, .int c, .int el, .int ec] p =
      ((retag .TemplateStr
        (callHelper .concatenate_strings [.seq xs, .int l, .int c, .int el, .int ec] p).1), p))

theorem concatenateTstrings_proven : ConcatenateTstrings := by
  intro xs l c el ec p
  have h1 : callHelper .concatenate_tstrings [.seq xs, .int l, .int c, .int el, .int ec] p =
      (mkAt .TemplateStr [.seq (buildConcatenatedStr (.seq xs))] ⟨l, c, el, ec⟩, p) := rfl
  refine ⟨h1, fun hf hb => ?_⟩
  rw [h1, (concatenateStrings_proven xs l c el ec p).2.2.2.2 hf hb]
  rfl

/-- The text of a value sequence: the characters of each `Constant` str, and each other node. -/
def textView : List Ast → List (Sum Nat Ast)
  | [] => []
  | e :: r => (if isConstant e then (constStr e).map Sum.inl else [Sum.inr e]) ++ textView r

/-- The flattening loop of `_build_concatenated_str` (`Parser/action_helpers.c:1810-1836`): the
values of each `JoinedStr` and `TemplateStr`, every other node as itself. -/
def concatFlat (strings : Ast) : List Ast :=
  (seqOf strings).flatMap fun e =>
    match e with
    | .node .JoinedStr (v :: _) _ | .node .TemplateStr (v :: _) _ => seqOf v
    | e => [e]

/-- No two `Constant`s next to each other. -/
def NoAdjConst : List Ast → Prop
  | a :: b :: r => ¬(isConstant a = true ∧ isConstant b = true) ∧ NoAdjConst (b :: r)
  | _ => True

/-- `_build_concatenated_str` (`Parser/action_helpers.c:1788-1941`), what its flattening and
folding loops make of any sequence of parts: (a) the text is kept, character by character and
node by node, in order (no part dropped, duplicated or moved, no character lost: `f'a' 'b'
f'{c}' 'd'` reads `a b {c} d`); (b) every run of adjacent constants is folded into one, so no two
constants are adjacent in the result; (c) no empty str constant is left ("Drop all empty contanst
strings", `:1931-1935`). Together these fix the result up to the constants' kinds and
locations. -/
def ConcatFolds : Prop := ∀ strings : Ast,
  textView (buildConcatenatedStr strings) = textView (concatFlat strings) ∧
  NoAdjConst (buildConcatenatedStr strings) ∧
  (buildConcatenatedStr strings).all (fun e => !isEmptyStrConst e) = true

theorem textView_append (a b : List Ast) : textView (a ++ b) = textView a ++ textView b := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, textView, ih, List.append_assoc]

theorem textView_consts (ys : List Ast) (h : ∀ y ∈ ys, isConstant y = true) :
    textView ys = (ys.flatMap constStr).map Sum.inl := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
    have hy := h y (by simp)
    have := ih (fun z hz => h z (by simp [hz]))
    simp [textView, hy, this, List.map_append]

theorem takeWhile_const (xs : List Ast) : ∀ y ∈ xs.takeWhile isConstant, isConstant y = true := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    intro y hy
    cases hx : isConstant x
    · simp [List.takeWhile, hx] at hy
    · simp only [List.takeWhile, hx, List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact hx
      · exact ih y hy

theorem dropWhile_head (xs : List Ast) : ∀ y ∈ (xs.dropWhile isConstant).head?, isConstant y = false := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    intro y hy
    cases hx : isConstant x
    · simp only [List.dropWhile, hx, List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      subst hy; exact hx
    · simp only [List.dropWhile, hx] at hy
      exact ih y hy

theorem foldConsts_spec (xs : List Ast) (acc : List Nat) (last : Ast) :
    (foldConsts xs acc last).1 = acc ++ (xs.takeWhile isConstant).flatMap constStr ∧
    (foldConsts xs acc last).2.2 = xs.dropWhile isConstant := by
  induction xs generalizing acc last with
  | nil => simp [foldConsts]
  | cons x xs ih =>
    unfold foldConsts
    split
    · rename_i h
      obtain ⟨h1, h2⟩ := ih (acc ++ constStr x) x
      refine ⟨?_, ?_⟩
      · rw [h1]; simp [List.takeWhile, h, List.append_assoc]
      · rw [h2]; simp [List.dropWhile, h]
    · rename_i h
      simp [List.takeWhile, List.dropWhile, h]

theorem isConstant_mkAt (s : List Nat) (k : Ast) (l : Loc) :
    isConstant (mkAt .Constant [.const (.str s), k] l) = true := rfl

theorem constStr_mkAt (s : List Nat) (k : Ast) (l : Loc) :
    constStr (mkAt .Constant [.const (.str s), k] l) = s := rfl

theorem emptyConst_facts (e : Ast) (h : isEmptyStrConst e = true) :
    isConstant e = true ∧ constStr e = [] := by
  unfold isEmptyStrConst at h
  split at h
  · exact ⟨rfl, rfl⟩
  · exact absurd h (by simp)

theorem nextIsConstant_head (rest : List Ast) (h : nextIsConstant rest = false) :
    ∀ y ∈ rest.head?, isConstant y = false := by
  cases rest with
  | nil => simp
  | cons y r => simpa [nextIsConstant] using h

theorem foldLoop_text : ∀ (f : Nat) (xs : List Ast), xs.length < f →
    textView (foldLoop f xs) = textView xs := by
  intro f
  induction f with
  | zero => intro xs h; simp at h
  | succ f ih =>
    intro xs h
    cases xs with
    | nil => simp [foldLoop]
    | cons e rest =>
      simp only [List.length_cons] at h
      have hlen := foldConsts_len rest (constStr e) e
      obtain ⟨h1, h2⟩ := foldConsts_spec rest (constStr e) e
      rw [foldLoop]
      split
      · rename_i hc
        have he : isConstant e = true := (Bool.and_eq_true_iff.1 hc).1
        have htv : textView (e :: rest) = ((foldConsts rest (constStr e) e).1).map Sum.inl ++
            textView (foldConsts rest (constStr e) e).2.2 := by
          rw [h1, h2]
          have hs : e :: rest = (e :: rest.takeWhile isConstant) ++ rest.dropWhile isConstant := by
            simp [List.takeWhile_append_dropWhile]
          rw [hs, textView_append, textView_consts (e :: rest.takeWhile isConstant) (by
            intro y hy
            simp only [List.mem_cons] at hy
            rcases hy with rfl | hy
            · exact he
            · exact takeWhile_const rest y hy)]
          simp [List.map_append]
        dsimp only
        split
        · rename_i hs
          rw [ih _ (by omega), htv]
          simp [List.isEmpty_iff.1 hs]
        · rw [textView, isConstant_mkAt, if_pos rfl, constStr_mkAt, ih _ (by omega), htv]
      · split
        · rename_i hemp
          rw [ih _ (by omega)]
          have := emptyConst_facts e hemp
          simp [textView, this.1, this.2]
        · simp only [textView]
          rw [ih _ (by omega)]

theorem noAdj_cons (x : Ast) (L : List Ast) :
    NoAdjConst (x :: L) ↔
      (∀ y ∈ L.head?, ¬(isConstant x = true ∧ isConstant y = true)) ∧ NoAdjConst L := by
  cases L with
  | nil => simp [NoAdjConst]
  | cons y r => simp [NoAdjConst]

theorem foldLoop_head : ∀ (f : Nat) (xs : List Ast), xs.length < f →
    (∀ y ∈ xs.head?, isConstant y = false) → ∀ z ∈ (foldLoop f xs).head?, isConstant z = false := by
  intro f xs h hx
  cases f with
  | zero => simp at h
  | succ f =>
    cases xs with
    | nil => simp [foldLoop]
    | cons y r =>
      have hy : isConstant y = false := hx y (by simp)
      have hne : isEmptyStrConst y = false := by
        cases hq : isEmptyStrConst y
        · rfl
        · rw [(emptyConst_facts y hq).1] at hy; exact absurd hy (by simp)
      intro z hz
      rw [foldLoop] at hz
      simp only [hy, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hne, List.head?_cons,
        Option.mem_def, Option.some.injEq] at hz
      subst hz; exact hy

theorem foldLoop_noAdj : ∀ (f : Nat) (xs : List Ast), xs.length < f → NoAdjConst (foldLoop f xs) := by
  intro f
  induction f with
  | zero => intro xs h; simp at h
  | succ f ih =>
    intro xs h
    cases xs with
    | nil => simp [foldLoop, NoAdjConst]
    | cons e rest =>
      simp only [List.length_cons] at h
      have hlen := foldConsts_len rest (constStr e) e
      obtain ⟨_, h2⟩ := foldConsts_spec rest (constStr e) e
      rw [foldLoop]
      split
      · dsimp only
        split
        · exact ih _ (by omega)
        · rw [noAdj_cons]
          refine ⟨fun y hy hb => ?_, ih _ (by omega)⟩
          have := foldLoop_head f _ (by omega) (by rw [h2]; exact dropWhile_head rest) y hy
          rw [this] at hb; exact absurd hb.2 (by simp)
      · rename_i hc
        split
        · exact ih _ (by omega)
        · rw [noAdj_cons]
          refine ⟨fun y hy hb => ?_, ih _ (by omega)⟩
          have hn : nextIsConstant rest = false := by
            cases hq : nextIsConstant rest
            · rfl
            · exact absurd (by simp [hb.1, hq]) hc
          have := foldLoop_head f rest (by omega) (nextIsConstant_head rest hn) y hy
          rw [this] at hb; exact absurd hb.2 (by simp)

theorem concatFolds_proven : ConcatFolds := by
  intro strings
  have hb : buildConcatenatedStr strings = foldLoop ((concatFlat strings).length + 1) (concatFlat strings) := rfl
  rw [hb]
  exact ⟨foldLoop_text _ _ (by omega), foldLoop_noAdj _ _ (by omega),
    concatNormalForm_proven _ _ (by omega)⟩

/-! ### `_PyPegen_setup_full_format_spec` -/

/-- The parts of a format spec that are not empty str constants (`Parser/action_helpers.c:1041-1065`). -/
def keptOf (xs : List Ast) : List Ast := xs.filter (fun e => !isEmptyStrConst e)

/-- `_PyPegen_setup_full_format_spec(p, colon, spec, EXTRA)` (`Parser/action_helpers.c:1029-1081`,
`fstring_full_format_spec`/`tstring_full_format_spec`, python.gram:978-979,993-994), through
`callHelper`: `NULL` spec gives `NULL`; otherwise the empty str constants are dropped, and of what
is left (`kept`):
* nothing, or one constant: a `JoinedStr` of it over `EXTRA` (the 3.11 shape, `:1037-1039`);
* two or more constants (and nothing else): `_PyPegen_concatenate_strings` makes them one
  `Constant`, which becomes the format spec itself, not a `JoinedStr`;
* anything with a replacement field in it: the `JoinedStr` of `_build_concatenated_str`;
each wrapped with the `:` token's metadata, state unchanged. Hypothesis for the last two: no bytes
constant (format spec parts are str). -/
def SetupFullFormatSpec : Prop := ∀ (colon : Ast) (xs : List Ast) (l c el ec : Int) (p : PS),
  callHelper .setup_full_format_spec [colon, .null, .int l, .int c, .int el, .int ec] p = (.null, p) ∧
  (keptOf xs = [] → callHelper .setup_full_format_spec [colon, .seq xs, .int l, .int c, .int el, .int ec] p =
    (rec_ .PResultTokenWithMetadata [mkAt .JoinedStr [.seq []] ⟨l, c, el, ec⟩, tokMeta colon], p)) ∧
  (∀ x, keptOf xs = [x] → isConstant x = true →
    callHelper .setup_full_format_spec [colon, .seq xs, .int l, .int c, .int el, .int ec] p =
      (rec_ .PResultTokenWithMetadata [mkAt .JoinedStr [.seq [x]] ⟨l, c, el, ec⟩, tokMeta colon], p)) ∧
  (∀ x y r, keptOf xs = x :: y :: r → (keptOf xs).all (fun e => isConstant e && !isBytesConst e) = true →
    callHelper .setup_full_format_spec [colon, .seq xs, .int l, .int c, .int el, .int ec] p =
      (rec_ .PResultTokenWithMetadata
        [mkAt .Constant [.const (.str ((keptOf xs).flatMap constStr)), constKind x] ⟨l, c, el, ec⟩,
          tokMeta colon], p)) ∧
  ((keptOf xs).any (fun e => !isConstant e) = true → (keptOf xs).any isBytesConst = false →
    callHelper .setup_full_format_spec [colon, .seq xs, .int l, .int c, .int el, .int ec] p =
      (rec_ .PResultTokenWithMetadata
        [mkAt .JoinedStr [.seq (buildConcatenatedStr (.seq (keptOf xs)))] ⟨l, c, el, ec⟩,
          tokMeta colon], p))

theorem setupFullFormatSpec_proven : SetupFullFormatSpec := by
  intro colon xs l c el ec p
  have hc : ∀ spec, callHelper .setup_full_format_spec [colon, spec, .int l, .int c, .int el, .int ec] p =
      setupFullFormatSpec colon spec l c el ec p := fun _ => rfl
  simp only [hc]
  refine ⟨rfl, fun hk => ?_, fun x hk hx => ?_, fun x y r hk ha => ?_, fun hf hb => ?_⟩
  · have hk : xs.filter (fun e => !isEmptyStrConst e) = [] := hk
    simp only [setupFullFormatSpec, seqOf, hk, bind, StateT.bind, pure, StateT.pure, ↓reduceIte,
      tokMeta]
    rfl
  · have hk : xs.filter (fun e => !isEmptyStrConst e) = [x] := hk
    simp only [setupFullFormatSpec, seqOf, hk, hx, bind, StateT.bind, pure, StateT.pure, ↓reduceIte,
      tokMeta]
    rfl
  · have ha' : (x :: y :: r).all (fun e => isConstant e && !isBytesConst e) = true := hk ▸ ha
    rw [hk]
    have hk : xs.filter (fun e => !isEmptyStrConst e) = x :: y :: r := hk
    have hcs := (concatenateStrings_proven (x :: y :: r) l c el ec p).2.2.2.1 x y r rfl ha'
    have hcs' : concatenateStrings (.seq (x :: y :: r)) l c el ec p =
        (mkAt .Constant [.const (.str ((x :: y :: r).flatMap constStr)), constKind x] ⟨l, c, el, ec⟩, p) :=
      hcs
    simp only [setupFullFormatSpec, seqOf, hk, Bool.false_eq_true, ↓reduceIte, bind, StateT.bind,
      hcs', pure, StateT.pure, tokMeta]
    rfl
  · have hcs := (concatenateStrings_proven _ l c el ec p).2.2.2.2 hf hb
    have hcs' : concatenateStrings (.seq (xs.filter (fun e => !isEmptyStrConst e))) l c el ec p =
        (mkAt .JoinedStr [.seq (buildConcatenatedStr (.seq (keptOf xs)))]
          ⟨l, c, el, ec⟩, p) := hcs
    have hf : (xs.filter (fun e => !isEmptyStrConst e)).any (fun e => !isConstant e) = true := hf
    unfold keptOf
    unfold keptOf at hcs'
    dsimp only [setupFullFormatSpec, seqOf, bind]
    rw [if_neg ?_]
    · simp only [StateT.bind, hcs', pure, StateT.pure, tokMeta]
      rfl
    · intro hsimp
      split at hsimp
      · rename_i heq
        rw [heq] at hf
        simp at hf
      · rename_i x heq
        rw [heq] at hf
        simp at hf
        rw [hf] at hsimp
        exact absurd hsimp (by simp)
      · exact absurd hsimp (by simp)

/-- The documented shape of a format spec (`Doc/library/ast.rst:319-320`, "``format_spec`` is a
:class:`JoinedStr` node representing the formatting of the value", and `:402-405` for
`Interpolation`), at the helper that builds it: whatever `_PyPegen_setup_full_format_spec` returns
(not `NULL`) carries a `JoinedStr`. This is what python/cpython#122300 restored for one constant
(gh-122308, the `n == 1` branch at `:1076`). -/
def FormatSpecIsJoinedStr : Prop := ∀ (colon : Ast) (xs : List Ast) (l c el ec : Int) (p : PS)
  (r : Ast) (s : PS),
  callHelper .setup_full_format_spec [colon, .seq xs, .int l, .int c, .int el, .int ec] p = (r, s) →
  r ≠ .null → (recField r 0).ctor? = some .JoinedStr

/-- The format spec of `f'{x:\N{DIGIT ONE}b}'`: the lexer ends a `FSTRING_MIDDLE` at the `}` of
`\N{...}`, so the spec arrives as two decoded constants, `"1"` and `"b"`, and the two-constant
branch makes it a `Constant`. -/
theorem formatSpecIsJoinedStr_refuted : ¬ FormatSpecIsJoinedStr := by
  intro h
  let c1 : Ast := mkAt .Constant [.const (.str [49]), .null] ⟨1, 5, 1, 18⟩
  let c2 : Ast := mkAt .Constant [.const (.str [98]), .null] ⟨1, 18, 1, 19⟩
  have e := (setupFullFormatSpec_proven .null [c1, c2] 1 4 1 19 default).2.2.2.1 c1 c2 [] rfl rfl
  have := h .null [c1, c2] 1 4 1 19 default _ _ e (by simp [rec_])
  have h2 : ∀ t, (recField (rec_ .PResultTokenWithMetadata [mkAt .Constant
      [.const (.str t), constKind c1] ⟨1, 4, 1, 19⟩, tokMeta .null]) 0).ctor? =
      some .Constant := fun _ => rfl
  rw [h2] at this
  cases Option.some.inj this

/-! ### `_get_interpolation_conversion`, `_PyPegen_formatted_value`, `_PyPegen_interpolation` -/

/-- `_get_interpolation_conversion(p, debug, conversion, format)` (`Parser/action_helpers.c:1526-1541`):
the first character of the conversion name when there is one (`!r` is 114); with none, `'r'`
(114) for a debug `=` without a format spec; -1 otherwise. -/
def InterpolationConversion : Prop := ∀ (debug fmt : Ast),
  (∀ (nm : List Nat) (rest : List Ast) (l : Option Loc) (m : Ast) (x : Nat),
    interpolationConversion debug
      (rec_ .PResultTokenWithMetadata [.node .Name (.ident (x :: nm) :: rest) l, m]) fmt = x) ∧
  (debug ≠ .null → fmt = .null → interpolationConversion debug .null fmt = 114) ∧
  (debug = .null → interpolationConversion debug .null fmt = -1) ∧
  (fmt ≠ .null → interpolationConversion debug .null fmt = -1)

theorem interpolationConversion_proven : InterpolationConversion := by
  intro debug fmt
  refine ⟨fun nm rest l m x => rfl, fun hd hf => ?_, fun hd => ?_, fun hf => ?_⟩
  · subst hf
    cases debug <;> first | exact absurd rfl hd | rfl
  · subst hd; rfl
  · cases debug <;> cases fmt <;> first | exact absurd rfl hf | rfl

/-- Where the debug text ends and which metadata it is, `Parser/action_helpers.c:1595-1609` and
`:1656-1670`: the conversion's (its name's line and column), else the format spec's (its line,
its column + 1), else the closing brace's (the end of the field). -/
def DebugInfoSource : Prop := ∀ (conv fmt closing : Ast) (el ec : Int),
  (conv ≠ .null → debugInfo conv fmt closing el ec =
    ((locOf (recField conv 0)).lineno, (locOf (recField conv 0)).colOffset, recField conv 1)) ∧
  (conv = .null → fmt ≠ .null → debugInfo conv fmt closing el ec =
    ((locOf (recField fmt 0)).lineno, (locOf (recField fmt 0)).colOffset + 1, recField fmt 1)) ∧
  (conv = .null → fmt = .null → debugInfo conv fmt closing el ec = (el, ec, tokMeta closing))

theorem debugInfoSource_proven : DebugInfoSource := by
  intro conv fmt closing el ec
  refine ⟨fun hc => ?_, fun hc hf => ?_, fun hc hf => ?_⟩
  · cases conv <;> first | exact absurd rfl hc | rfl
  · subst hc
    cases fmt <;> first | exact absurd rfl hf | rfl
  · subst hc; subst hf; rfl

/-- The wrapper both helpers put around a debug field (`f'{x=}'`): a `JoinedStr` of the debug text
(a `Constant` of the metadata, from just after `{` to just before where the text ends) and the
node, from `{` to where the text ends; no debug `=`, the node alone. -/
def wrapDebug (debug inner : Ast) (l c : Int) (di : Int × Int × Ast) : Ast :=
  match debug with
  | .null => inner
  | _ => mkAt .JoinedStr [.seq [mkAt .Constant [metaConst di.2.2, .null] ⟨l, c + 1, di.1, di.2.1 - 1⟩,
      inner]] ⟨l, c, di.1, di.2.1⟩

/-- `_PyPegen_formatted_value` (`Parser/action_helpers.c:1640-1687`) and `_PyPegen_interpolation`
(`:1577-1638`), the f-string and t-string replacement fields, side by side through `callHelper`:
the same conversion (`_get_interpolation_conversion`), the same format spec (the result of the
format-spec record), the same location and the same debug wrapper (`wrapDebug`, with the same
debug text and end); the `Interpolation` also keeps the expression's text, the metadata the debug
text is made of, without the trailing `=` and the whitespace after it when there is a debug `=`
(`_strip_interpolation_debug_expr`). State unchanged. -/
def FormattedValueInterpolation : Prop := ∀ (e debug conv fmt closing : Ast) (l c el ec : Int)
  (p : PS),
  callHelper .formatted_value [e, debug, conv, fmt, closing, .int l, .int c, .int el, .int ec] p =
    (wrapDebug debug (mkAt .FormattedValue [e, .int (interpolationConversion debug conv fmt),
      recField fmt 0] ⟨l, c, el, ec⟩) l c (debugInfo conv fmt closing el ec), p) ∧
  callHelper .interpolation [e, debug, conv, fmt, closing, .int l, .int c, .int el, .int ec] p =
    (wrapDebug debug (mkAt .Interpolation [e,
      (match (debugInfo conv fmt closing el ec).2.2 with
       | .str s => .const (.str (match debug with
          | .null => s
          | _ => stripInterpolationDebugExpr s))
       | _ => .null),
      .int (interpolationConversion debug conv fmt), recField fmt 0] ⟨l, c, el, ec⟩) l c
      (debugInfo conv fmt closing el ec), p)

theorem formattedValueInterpolation_proven : FormattedValueInterpolation := by
  intro e debug conv fmt closing l c el ec p
  refine ⟨?_, ?_⟩
  · show (formattedValue e debug conv fmt closing l c el ec, p) = _
    unfold formattedValue wrapDebug
    cases debug <;> rfl
  · show (interpolation e debug conv fmt closing l c el ec, p) = _
    unfold interpolation wrapDebug
    generalize debugInfo conv fmt closing el ec = di
    obtain ⟨dl, dc, md⟩ := di
    cases debug <;> cases md <;> rfl

/-! ### f-strings and t-strings: `_PyPegen_constant_from_token`, `_PyPegen_decode_fstring_part`,
`_get_resized_exprs`, `_PyPegen_joined_str`, `_PyPegen_template_str`,
`_PyPegen_constant_from_string` -/

/-- The parts a value contributes to `_get_resized_exprs`'s result when it is not a constant: the
two values of a debug `JoinedStr` (`:1384-1402`), the node itself otherwise. -/
def pairParts : Ast → List Ast
  | .node .JoinedStr (v :: _) _ => seqOf v
  | e => [e]

/-- The location `_PyPegen_joined_str` and `_PyPegen_template_str` give: from the start token to
the end token. -/
def jsLoc (a b : Token) : Loc := ⟨a.lineno, a.colOffset, b.endLineno, b.endColOffset⟩

theorem pairParts_other (x : Ast) (h : ∀ v r l, x = .node .JoinedStr (v :: r) l → False) :
    pairParts x = [x] := by
  unfold pairParts
  split
  · rename_i v r l
    exact absurd rfl (h v r l)
  · rfl

/-- `_get_resized_exprs`' loop (`Parser/action_helpers.c:1378-1416`) over parts that are not
constants (nothing to decode): debug pairs spliced in, everything else kept, in order, no state
change. -/
theorem resizedLoop_noconst (isRaw tstr : Bool) (b : Ast) :
    ∀ (items acc : List Ast), (∀ e ∈ items, isConstant e = false) →
    (∀ e ∈ items, ∀ v r l, e = .node .JoinedStr (v :: r) l → (seqOf v).length = 2) →
    resizedLoop isRaw tstr b items acc = pure (some (acc.reverse ++ items.flatMap pairParts)) := by
  intro items
  induction items with
  | nil => intro acc _ _; simp [resizedLoop]
  | cons x xs ih =>
    intro acc hc hj
    have hc' : ∀ e ∈ xs, isConstant e = false := fun e he => hc e (by simp [he])
    have hj' : ∀ e ∈ xs, ∀ v r l, e = .node .JoinedStr (v :: r) l → (seqOf v).length = 2 :=
      fun e he => hj e (by simp [he])
    have hx := hc x (by simp)
    have hjx := hj x (by simp)
    rw [resizedLoop.eq_def]
    dsimp only
    split
    · rename_i values r l
      have h2 := hjx values r l rfl
      split
      · rename_i f s hv
        rw [ih _ hc' hj']
        simp [pairParts, hv]
      · rename_i hv
        match hq : seqOf values, h2 with
        | [f, s], _ => exact absurd hq (hv f s)
    · simp [isConstant] at hx
    · rw [ih _ hc' hj']
      simp [List.flatMap_cons, pairParts_other x (by assumption)]

/-- The `SystemError` of `_get_resized_exprs`, `Parser/action_helpers.c:1389-1394`. -/
def resizedErr (tstr : Bool) (line : Int) : PyError :=
  { cls := "SystemError"
    msg := if tstr then s!"unexpected TemplateStr node without debug data in t-string at line {line}"
      else s!"unexpected JoinedStr node without debug data in f-string at line {line}" }

/-- `_PyPegen_joined_str` and `_PyPegen_template_str` (`Parser/action_helpers.c:1433-1455`) over
parts with nothing to decode (replacement fields, debug pairs): the parts in order, each debug
`JoinedStr` (`f'{x=}'`: its text and its field) spliced in, as a `JoinedStr` (a `TemplateStr`)
from the start token to the end token, state unchanged; and a `JoinedStr` part that is not a
debug pair (two values) stops it with `SystemError` "unexpected JoinedStr node without debug data
in f-string at line <n>" ("TemplateStr ... t-string" for a t-string). -/
def JoinedStrParts : Prop := ∀ (a b : Token) (items : List Ast) (p : PS),
  ((∀ e ∈ items, isConstant e = false) →
    (∀ e ∈ items, ∀ v r l, e = .node .JoinedStr (v :: r) l → (seqOf v).length = 2) →
    callHelper .joined_str [.tok a, .seq items, .tok b] p =
      (mkAt .JoinedStr [.seq (items.flatMap pairParts)] (jsLoc a b), p) ∧
    callHelper .template_str [.tok a, .seq items, .tok b] p =
      (mkAt .TemplateStr [.seq (items.flatMap pairParts)] (jsLoc a b), p)) ∧
  (∀ (pre post : List Ast) (v : Ast) (r : List Ast) (lb : Loc),
    items = pre ++ .node .JoinedStr (v :: r) (some lb) :: post →
    (∀ e ∈ pre, isConstant e = false) →
    (∀ e ∈ pre, ∀ v r l, e = .node .JoinedStr (v :: r) l → (seqOf v).length = 2) →
    (seqOf v).length ≠ 2 →
    callHelper .joined_str [.tok a, .seq items, .tok b] p =
      (.null, (setErr (resizedErr false lb.lineno) p).2) ∧
    callHelper .template_str [.tok a, .seq items, .tok b] p =
      (.null, (setErr (resizedErr true lb.lineno) p).2))

theorem resizedLoop_append (isRaw tstr : Bool) (b : Ast) :
    ∀ (pre rest acc : List Ast), (∀ e ∈ pre, isConstant e = false) →
    (∀ e ∈ pre, ∀ v r l, e = .node .JoinedStr (v :: r) l → (seqOf v).length = 2) →
    resizedLoop isRaw tstr b (pre ++ rest) acc =
      resizedLoop isRaw tstr b rest ((pre.flatMap pairParts).reverse ++ acc) := by
  intro pre
  induction pre with
  | nil => intro rest acc _ _; rfl
  | cons x xs ih =>
    intro rest acc hc hj
    have hc' : ∀ e ∈ xs, isConstant e = false := fun e he => hc e (by simp [he])
    have hj' : ∀ e ∈ xs, ∀ v r l, e = .node .JoinedStr (v :: r) l → (seqOf v).length = 2 :=
      fun e he => hj e (by simp [he])
    have hx := hc x (by simp)
    have hjx := hj x (by simp)
    rw [List.cons_append, resizedLoop.eq_def]
    dsimp only
    split
    · rename_i values r l
      have h2 := hjx values r l rfl
      split
      · rename_i f s hv
        rw [ih _ _ hc' hj']
        simp [pairParts, hv, List.reverse_append]
      · rename_i hv
        match hq : seqOf values, h2 with
        | [f, s], _ => exact absurd hq (hv f s)
    · simp [isConstant] at hx
    · rw [ih _ _ hc' hj']
      simp [List.flatMap_cons, pairParts_other x (by assumption), List.reverse_append]

theorem joinedStrParts_proven : JoinedStrParts := by
  intro a b items p
  refine ⟨fun hc hj => ?_, fun pre post v r lb hi hc hj hv => ?_⟩
  · have hl : ∀ t, getResizedExprs (.tok a) (.seq items) (.tok b) t =
        pure (some (items.flatMap pairParts)) := by
      intro t
      simp only [getResizedExprs, seqOf]
      rw [resizedLoop_noconst _ _ _ items [] hc hj]
      simp
    refine ⟨?_, ?_⟩
    · (simp only [callHelper, List.getD_cons_zero, List.getD_cons_succ, hl, pure_bind]) <;> rfl
    · (simp only [callHelper, List.getD_cons_zero, List.getD_cons_succ, hl, pure_bind]) <;> rfl
  · have hl : ∀ t, getResizedExprs (.tok a) (.seq items) (.tok b) t =
        (do setErr (resizedErr t lb.lineno); return none) := by
      intro t
      simp only [getResizedExprs, seqOf, hi]
      rw [resizedLoop_append _ _ _ pre _ [] hc hj, resizedLoop.eq_def]
      dsimp only
      split
      · rename_i hq
        exact absurd (by rw [hq]; rfl) hv
      · rfl
    refine ⟨?_, ?_⟩
    · (simp only [callHelper, List.getD_cons_zero, List.getD_cons_succ, hl]) <;> rfl
    · (simp only [callHelper, List.getD_cons_zero, List.getD_cons_succ, hl]) <;> rfl

end PyLean.PyGrammar.Peg
