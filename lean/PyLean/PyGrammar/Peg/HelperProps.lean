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

end PyLean.PyGrammar.Peg
