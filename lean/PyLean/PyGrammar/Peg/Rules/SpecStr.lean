import PyLean.PyGrammar.Peg.Rules.SpecInv4
import PyLean.PyGrammar.Peg.Rules.Lazy

/-! The string rules (`Grammar/python.gram:969-1014`) and their `invalid_` rules as equations
(`Spec.lean`). Each action is the helper the grammar names, with the values it is given: the
model's `callHelper` mirrors of `_PyPegen_constant_from_token`, `_PyPegen_constant_from_string`,
`_PyPegen_decoded_constant_from_token`, `_PyPegen_joined_str`, `_PyPegen_template_str`, and the
functions `formattedValue`, `interpolation`, `checkFstringConversion`, `setupFullFormatSpec`,
`concatenateStrings`, `buildConcatenatedStr` (`Parser/action_helpers.c`). Tokens: `FSTRING_START`
59, `FSTRING_MIDDLE` 60, `FSTRING_END` 61, `TSTRING_START` 62, `TSTRING_MIDDLE` 63, `TSTRING_END`
64, `{` 25, `}` 26, `=` 22, `!` 54, `:` 11; rules `annotated_rhs` 12. -/

namespace PyLean.PyGrammar.Peg

open Lexer

/-! ### Loops and groups -/

/-- `_loop0_78: fstring_format_spec*`, `_loop0_79: fstring_middle*`, `_loop0_80:
tstring_format_spec*`, `_loop0_81: tstring_middle*`, `_loop1_82: (fstring|string)+` over
`_tmp_156`, `_loop1_83: tstring+`. -/
def StringLoops : Prop :=
  Loop0Over 355 164 ∧ Loop0Over 356 160 ∧ Loop0Over 357 167 ∧ Loop0Over 358 170 ∧
  Loop1Over 359 433 ∧ Loop1Over 360 171 ∧
  PlainSpec 433 [⟨[.call (.rule 165)], false, oVar0⟩, ⟨[.call (.rule 172)], false, oVar0⟩]
theorem stringLoops_proven : StringLoops :=
  ⟨loop0Over_of rfl, loop0Over_of rfl, loop0Over_of rfl, loop0Over_of rfl, loop1Over_of rfl,
    loop1Over_of rfl, by plain_spec⟩

/-- `_tmp_152: '=' | '!' | ':' | '}'`, `_tmp_153: '!' | ':' | '}'`, `_tmp_154: '!' NAME`,
`_tmp_155: ':' | '}'`. -/
def FieldGroups : Prop :=
  TokGroup 429 [22, 54, 11, 26] ∧ TokGroup 430 [54, 11, 26] ∧
  PlainSpec 431 [⟨[.call (.tok 54), .call .name], false, oDummy⟩] ∧ TokGroup 432 [11, 26]
theorem fieldGroups_proven : FieldGroups :=
  ⟨tokGroup_of (by simp) rfl, tokGroup_of (by simp) rfl, by plain_spec, tokGroup_of (by simp) rfl⟩

/-! ### f-strings -/

/-- `fstring_middle[expr_ty]: fstring_replacement_field | t=FSTRING_MIDDLE {
_PyPegen_constant_from_token(p, t) }` (`Grammar/python.gram:969-971`). -/
def FstringMiddle : Prop := PlainSpec 160 [
  ⟨[.call (.rule 161)], false, oVar0⟩,
  ⟨[.call (.tok 60)], false, oState (fun env s => callHelper .constant_from_token [env.getD 0 .null] s)⟩]
theorem fstringMiddle_proven : FstringMiddle := by plain_spec

/-- `fstring_replacement_field[expr_ty]` (`Grammar/python.gram:972-975`):
```
    | '{' a=annotated_rhs debug_expr='='? conversion=[fstring_conversion] format=[fstring_full_format_spec] rbrace='}' {
        _PyPegen_formatted_value(p, a, debug_expr, conversion, format, rbrace, EXTRA) }
    | invalid_fstring_replacement_field
```
-/
def FstringReplacementField : Prop := ExtraSpec 161 [
  ⟨[.call (.tok 25), .call (.rule 12), .opt (.tok 22), .opt (.rule 162), .opt (.rule 163), .call (.tok 26)], false,
    oPureX (fun env l => formattedValue (env.getD 1 .null) (env.getD 2 .null) (env.getD 3 .null)
      (env.getD 4 .null) (env.getD 5 .null) l.lineno l.colOffset l.endLineno l.endColOffset)⟩,
  ⟨[.call (.rule 269)], true, oVar0⟩]
theorem fstringReplacementField_proven : FstringReplacementField := by extra_spec

/-- `fstring_conversion[ResultTokenWithMetadata*]: conv_token="!" conv=NAME {
_PyPegen_check_fstring_conversion(p, conv_token, conv) }` (`Grammar/python.gram:976-977`). -/
def FstringConversion : Prop := PlainSpec 162 [
  ⟨[.call (.tok 54), .call .name], false,
    oState (fun env s => checkFstringConversion (env.getD 0 .null) (env.getD 1 .null) s)⟩]
theorem fstringConversion_proven : FstringConversion := by plain_spec

/-- `fstring_full_format_spec[ResultTokenWithMetadata*]: colon=':' spec=fstring_format_spec* {
_PyPegen_setup_full_format_spec(p, colon, (asdl_expr_seq *) spec, EXTRA) }`
(`Grammar/python.gram:978-979`). -/
def FstringFullFormatSpec : Prop := ExtraSpec 163 [
  ⟨[.call (.tok 11), .call (.rule 355)], false, oStateX (fun env l s =>
    setupFullFormatSpec (env.getD 0 .null) (env.getD 1 .null) l.lineno l.colOffset l.endLineno l.endColOffset s)⟩]
theorem fstringFullFormatSpec_proven : FstringFullFormatSpec := by extra_spec

/-- `fstring_format_spec[expr_ty]: t=FSTRING_MIDDLE { _PyPegen_decoded_constant_from_token(p, t) } |
fstring_replacement_field` (`Grammar/python.gram:980-982`). -/
def FstringFormatSpec : Prop := PlainSpec 164 [
  ⟨[.call (.tok 60)], false,
    oState (fun env s => callHelper .decoded_constant_from_token [env.getD 0 .null] s)⟩,
  ⟨[.call (.rule 161)], false, oVar0⟩]
theorem fstringFormatSpec_proven : FstringFormatSpec := by plain_spec

/-- `fstring[expr_ty]: a=FSTRING_START b=fstring_middle* c=FSTRING_END { _PyPegen_joined_str(p, a,
(asdl_expr_seq*)b, c) }` (`Grammar/python.gram:983-984`). -/
def FstringRule : Prop := PlainSpec 165 [
  ⟨[.call (.tok 59), .call (.rule 356), .call (.tok 61)], false,
    oState (fun env s => callHelper .joined_str [env.getD 0 .null, env.getD 1 .null, env.getD 2 .null] s)⟩]
theorem fstringRule_proven : FstringRule := by plain_spec

/-! ### t-strings -/

/-- `tstring_format_spec_replacement_field[expr_ty]` (`Grammar/python.gram:986-989`): as
`fstring_replacement_field` with `tstring_full_format_spec` (168) and
`invalid_tstring_replacement_field` (271); the action is `_PyPegen_formatted_value` (a field
nested in a t-string's format spec is a `FormattedValue`). -/
def TstringFormatSpecReplacementField : Prop := ExtraSpec 166 [
  ⟨[.call (.tok 25), .call (.rule 12), .opt (.tok 22), .opt (.rule 162), .opt (.rule 168), .call (.tok 26)], false,
    oPureX (fun env l => formattedValue (env.getD 1 .null) (env.getD 2 .null) (env.getD 3 .null)
      (env.getD 4 .null) (env.getD 5 .null) l.lineno l.colOffset l.endLineno l.endColOffset)⟩,
  ⟨[.call (.rule 271)], true, oVar0⟩]
theorem tstringFormatSpecReplacementField_proven : TstringFormatSpecReplacementField := by extra_spec

/-- `tstring_format_spec[expr_ty]: t=TSTRING_MIDDLE { _PyPegen_decoded_constant_from_token(p, t) }
| tstring_format_spec_replacement_field` (`Grammar/python.gram:990-992`). -/
def TstringFormatSpec : Prop := PlainSpec 167 [
  ⟨[.call (.tok 63)], false,
    oState (fun env s => callHelper .decoded_constant_from_token [env.getD 0 .null] s)⟩,
  ⟨[.call (.rule 166)], false, oVar0⟩]
theorem tstringFormatSpec_proven : TstringFormatSpec := by plain_spec

/-- `tstring_full_format_spec[ResultTokenWithMetadata*]: colon=':' spec=tstring_format_spec* {
_PyPegen_setup_full_format_spec(p, colon, (asdl_expr_seq *) spec, EXTRA) }`
(`Grammar/python.gram:993-994`). -/
def TstringFullFormatSpec : Prop := ExtraSpec 168 [
  ⟨[.call (.tok 11), .call (.rule 357)], false, oStateX (fun env l s =>
    setupFullFormatSpec (env.getD 0 .null) (env.getD 1 .null) l.lineno l.colOffset l.endLineno l.endColOffset s)⟩]
theorem tstringFullFormatSpec_proven : TstringFullFormatSpec := by extra_spec

/-- `tstring_replacement_field[expr_ty]` (`Grammar/python.gram:995-998`):
```
    | '{' a=annotated_rhs debug_expr='='? conversion=[fstring_conversion] format=[tstring_full_format_spec] rbrace='}' {
        _PyPegen_interpolation(p, a, debug_expr, conversion, format, rbrace, EXTRA) }
    | invalid_tstring_replacement_field
```
-/
def TstringReplacementField : Prop := ExtraSpec 169 [
  ⟨[.call (.tok 25), .call (.rule 12), .opt (.tok 22), .opt (.rule 162), .opt (.rule 168), .call (.tok 26)], false,
    oPureX (fun env l => interpolation (env.getD 1 .null) (env.getD 2 .null) (env.getD 3 .null)
      (env.getD 4 .null) (env.getD 5 .null) l.lineno l.colOffset l.endLineno l.endColOffset)⟩,
  ⟨[.call (.rule 271)], true, oVar0⟩]
theorem tstringReplacementField_proven : TstringReplacementField := by extra_spec

/-- `tstring_middle[expr_ty]: tstring_replacement_field | t=TSTRING_MIDDLE {
_PyPegen_constant_from_token(p, t) }` (`Grammar/python.gram:999-1001`). -/
def TstringMiddle : Prop := PlainSpec 170 [
  ⟨[.call (.rule 169)], false, oVar0⟩,
  ⟨[.call (.tok 63)], false, oState (fun env s => callHelper .constant_from_token [env.getD 0 .null] s)⟩]
theorem tstringMiddle_proven : TstringMiddle := by plain_spec

def tstringVersionMsg : String := "t-strings are only supported in Python 3.14 and greater"

/-- The action of `tstring`: `_PyPegen_template_str(p, a, b, c)` under `CHECK_VERSION(expr_ty, 14,
"t-strings are", ...)`: its `NULL` sets `error_indicator`; a node below feature version 14 raises
"t-strings are only supported in Python 3.14 and greater". -/
@[irreducible] def oTstring : Array Ast → Int × Int → PS → Option Ast × PS := fun env _ s =>
  let r := callHelper .template_str [env.getD 0 .null, env.getD 1 .null, env.getD 2 .null] s
  match r.1 with
  | .null =>
    if r.2.errOccurred then (none, { r.2 with errorIndicator := true })
    else (some .null, { r.2 with errorIndicator := true })
  | n =>
    if (r.2.featureVersion : Int) < 14 then
      (none, { (raiseError0 "SyntaxError" tstringVersionMsg { r.2 with errorIndicator := true }).2 with
        errorIndicator := true })
    else pureRes n r.2

/-- `tstring[expr_ty] (memo): a=TSTRING_START b=tstring_middle* c=TSTRING_END { CHECK_VERSION(expr_ty,
14, "t-strings are", _PyPegen_template_str(p, a, (asdl_expr_seq*)b, c)) }`
(`Grammar/python.gram:1002-1008`). -/
def TstringRule : Prop := MemoSpec 171 [
  ⟨[.call (.tok 62), .call (.rule 358), .call (.tok 64)], false, oTstring⟩]

theorem evalA_cv_null' {env : Array Ast} {ex : Extra} {v : Int} {m : String} {node : AE} {s s1 : PS}
    (hn : evalA env ex node s = (.null, s1)) :
    evalA env ex (.checkVersion (.int v) (.str m) node) s = (.null, { s1 with errorIndicator := true }) := by
  simp only [evalA, bind, StateT.bind, hn, pure, StateT.pure, modify, modifyGet, MonadStateOf.modifyGet,
    StateT.modifyGet, MonadState.modifyGet]

theorem tstringRule_proven : TstringRule := by
  intro f p q h hn
  rw [callRule_memo_plain rfl rfl rfl rfl rfl h hn]
  refine congrArg (memoDone p.mark _) (runAlts_spec f _ _ ?_ _ _ _)
  refine altsAre_cons rfl rfl (fun env st s => ?_) altsAre_nil
  unfold oTstring
  rw [altResult_plain rfl rfl]
  dsimp only
  generalize hr : callHelper .template_str [env.getD 0 .null, env.getD 1 .null, env.getD 2 .null] s = r
  obtain ⟨n, s1⟩ := r
  have hnode : ∀ ex, evalA env ex (.call .template_str [.var 0, .var 1, .var 2]) s = (n, s1) := by
    intro ex
    rw [← hr]
    rfl
  have hmsg : s!"{cpsStr ("t-strings are".toList.map Char.toNat)} only supported in Python 3.{(14 : Int)} and greater" = tstringVersionMsg := by
    decide +kernel
  dsimp only
  cases n
  case null =>
    rw [evalA_cv_null' (hnode {})]
    cases he : s1.errOccurred <;> simp_all [nonNull, PS.errOccurred]
  all_goals
    by_cases hv : (s1.featureVersion : Int) < 14
    · rw [evalA_cv_low' (hnode {}) (by intro h; cases h) hv, hmsg]
      have he := (raises_raiseError0 "SyntaxError" tstringVersionMsg).2 { s1 with errorIndicator := true }
      generalize raiseError0 "SyntaxError" tstringVersionMsg { s1 with errorIndicator := true } = r at he
      obtain ⟨u, r⟩ := r
      simp only at he
      simp [hv, nonNull, he]
    · rw [evalA_cv_ok' (hnode {}) (by intro h; cases h) hv]
      simp only [hv, ↓reduceIte, pureRes]

/-! ### `string`, `strings` -/

/-- `string[expr_ty]: s[Token*]=STRING { _PyPegen_constant_from_string(p, s) }`
(`Grammar/python.gram:1010`). -/
def StringRule : Prop := PlainSpec 172 [
  ⟨[.call .string], false, oState (fun env s => callHelper .constant_from_string [env.getD 0 .null] s)⟩]
theorem stringRule_proven : StringRule := by plain_spec

/-- `strings[expr_ty] (memo)` (`Grammar/python.gram:1011-1014`):
```
    | invalid_string_tstring_concat
    | a[asdl_expr_seq*]=(fstring|string)+ { _PyPegen_concatenate_strings(p, a, EXTRA) }
    | a[asdl_expr_seq*]=tstring+ { _PyPegen_concatenate_tstrings(p, a, EXTRA) }
```
-/
def StringsRule : Prop := MemoExtraSpec 173 [
  ⟨[.call (.rule 273)], true, oVar0⟩,
  ⟨[.call (.rule 359)], false, oStateX (fun env l s =>
    concatenateStrings (env.getD 0 .null) l.lineno l.colOffset l.endLineno l.endColOffset s)⟩,
  ⟨[.call (.rule 360)], false,
    oPureX (fun env l => mkAt .TemplateStr [.seq (buildConcatenatedStr (env.getD 0 .null))] l)⟩]
theorem stringsRule_proven : StringsRule := by memo_extra_spec

/-! ### `invalid_` rules of the strings -/

/-- `invalid_fstring_replacement_field` (`Grammar/python.gram:1587-1603`): the eleven
alternatives in order, `{` followed by `=`, `!`, `:`, `}` raising "valid expression required
before ..." at that token; then no `annotated_rhs`, then the expected next part, each with
`PyErr_Occurred() ? NULL : RAISE_SYNTAX_ERROR_ON_NEXT_TOKEN(...)`; the conversion character
alternative has no action. `fstring_format_spec*` is `_loop0_78` (355). -/
def InvalidFstringReplacementField : Prop := PlainSpec 269 [
  ⟨[.call (.tok 25), .call (.tok 22)], false, oKL 1 "f-string: valid expression required before '='"⟩,
  ⟨[.call (.tok 25), .call (.tok 54)], false, oKL 1 "f-string: valid expression required before '!'"⟩,
  ⟨[.call (.tok 25), .call (.tok 11)], false, oKL 1 "f-string: valid expression required before ':'"⟩,
  ⟨[.call (.tok 25), .call (.tok 26)], false, oKL 1 "f-string: valid expression required before '}'"⟩,
  ⟨[.call (.tok 25), .look false (.rule 12)], false, oNext "f-string: expecting a valid expression after '{'"⟩,
  ⟨[.call (.tok 25), .call (.rule 12), .look false (.rule 429)], false,
    oNextIf "f-string: expecting '=', or '!', or ':', or '}'"⟩,
  ⟨[.call (.tok 25), .call (.rule 12), .call (.tok 22), .look false (.rule 430)], false,
    oNextIf "f-string: expecting '!', or ':', or '}'"⟩,
  ⟨[.call (.tok 25), .call (.rule 12), .opt (.tok 22), .call (.rule 270)], false, oDummy⟩,
  ⟨[.call (.tok 25), .call (.rule 12), .opt (.tok 22), .opt (.rule 431), .look false (.rule 432)], false,
    oNextIf "f-string: expecting ':' or '}'"⟩,
  ⟨[.call (.tok 25), .call (.rule 12), .opt (.tok 22), .opt (.rule 431), .call (.tok 11), .call (.rule 355),
    .look false (.tok 26)], false, oNextIf "f-string: expecting '}', or format specs"⟩,
  ⟨[.call (.tok 25), .call (.rule 12), .opt (.tok 22), .opt (.rule 431), .look false (.tok 26)], false,
    oNextIf "f-string: expecting '}'"⟩]
theorem invalidFstringReplacementField_proven : InvalidFstringReplacementField := by plain_spec

/-- `invalid_tstring_replacement_field` (`Grammar/python.gram:1609-1625`): the t-string twin,
with "t-string: ..." messages and `invalid_tstring_conversion_character` (272). Its tenth
alternative is `'{' annotated_rhs '='? ['!' NAME] ':' fstring_format_spec* !'}'`
(python.gram:1622): the f-string format-spec loop `_loop0_78` (355), as the statement records,
not `tstring_format_spec*` (`_loop0_80`, 357). Inside it, `fstring_replacement_field`'s own
`invalid_fstring_replacement_field` can raise an "f-string: ..." message for a t-string
(`TstringFieldMessages`, refuted). -/
def InvalidTstringReplacementField : Prop := PlainSpec 271 [
  ⟨[.call (.tok 25), .call (.tok 22)], false, oKL 1 "t-string: valid expression required before '='"⟩,
  ⟨[.call (.tok 25), .call (.tok 54)], false, oKL 1 "t-string: valid expression required before '!'"⟩,
  ⟨[.call (.tok 25), .call (.tok 11)], false, oKL 1 "t-string: valid expression required before ':'"⟩,
  ⟨[.call (.tok 25), .call (.tok 26)], false, oKL 1 "t-string: valid expression required before '}'"⟩,
  ⟨[.call (.tok 25), .look false (.rule 12)], false, oNext "t-string: expecting a valid expression after '{'"⟩,
  ⟨[.call (.tok 25), .call (.rule 12), .look false (.rule 429)], false,
    oNextIf "t-string: expecting '=', or '!', or ':', or '}'"⟩,
  ⟨[.call (.tok 25), .call (.rule 12), .call (.tok 22), .look false (.rule 430)], false,
    oNextIf "t-string: expecting '!', or ':', or '}'"⟩,
  ⟨[.call (.tok 25), .call (.rule 12), .opt (.tok 22), .call (.rule 272)], false, oDummy⟩,
  ⟨[.call (.tok 25), .call (.rule 12), .opt (.tok 22), .opt (.rule 431), .look false (.rule 432)], false,
    oNextIf "t-string: expecting ':' or '}'"⟩,
  ⟨[.call (.tok 25), .call (.rule 12), .opt (.tok 22), .opt (.rule 431), .call (.tok 11), .call (.rule 355),
    .look false (.tok 26)], false, oNextIf "t-string: expecting '}', or format specs"⟩,
  ⟨[.call (.tok 25), .call (.rule 12), .opt (.tok 22), .opt (.rule 431), .look false (.tok 26)], false,
    oNextIf "t-string: expecting '}'"⟩]
theorem invalidTstringReplacementField_proven : InvalidTstringReplacementField := by plain_spec

/-- `invalid_fstring_conversion_character` (`Grammar/python.gram:1605-1607`), and its t-string
twin (1627-1629):
```
    | '!' &(':' | '}') { RAISE_SYNTAX_ERROR_ON_NEXT_TOKEN("f-string: missing conversion character") }
    | '!' !NAME { RAISE_SYNTAX_ERROR_ON_NEXT_TOKEN("f-string: invalid conversion character") }
```
-/
def InvalidFstringConversionCharacter : Prop := PlainSpec 270 [
  ⟨[.call (.tok 54), .look true (.rule 432)], false, oNext "f-string: missing conversion character"⟩,
  ⟨[.call (.tok 54), .look false .name], false, oNext "f-string: invalid conversion character"⟩]
theorem invalidFstringConversionCharacter_proven : InvalidFstringConversionCharacter := by plain_spec
def InvalidTstringConversionCharacter : Prop := PlainSpec 272 [
  ⟨[.call (.tok 54), .look true (.rule 432)], false, oNext "t-string: missing conversion character"⟩,
  ⟨[.call (.tok 54), .look false .name], false, oNext "t-string: invalid conversion character"⟩]
theorem invalidTstringConversionCharacter_proven : InvalidTstringConversionCharacter := by plain_spec

def mixMsg : String := "cannot mix t-string literals with string or bytes literals"

/-- `invalid_string_tstring_concat` (`Grammar/python.gram:1631-1635`):
```
    | a=(fstring|string)+ b[expr_ty]=tstring {
        RAISE_SYNTAX_ERROR_KNOWN_RANGE(PyPegen_last_item(a, expr_ty), b, "cannot mix t-string literals with string or bytes literals") }
    | a=tstring+ b[expr_ty]=(fstring|string) {
        RAISE_SYNTAX_ERROR_KNOWN_RANGE(PyPegen_last_item(a, expr_ty), b, "cannot mix t-string literals with string or bytes literals") }
```
Over the last literal of the first kind .. the first of the other. -/
def InvalidStringTstringConcat : Prop := PlainSpec 273 [
  ⟨[.call (.rule 359), .call (.rule 171)], false, fun env _ s =>
    (none, raisedAt ((seqOf (env.getD 0 .null)).getLastD .null) (env.getD 1 .null) mixMsg s)⟩,
  ⟨[.call (.rule 360), .call (.rule 433)], false, fun env _ s =>
    (none, raisedAt ((seqOf (env.getD 0 .null)).getLastD .null) (env.getD 1 .null) mixMsg s)⟩]
theorem invalidStringTstringConcat_proven : InvalidStringTstringConcat := by plain_spec

/-! ### With their loops and groups -/

def FstringRuleG : Prop := FstringRule ∧ StringLoops
theorem fstringRuleG_proven : FstringRuleG := ⟨fstringRule_proven, stringLoops_proven⟩
def FstringFullFormatSpecG : Prop := FstringFullFormatSpec ∧ StringLoops
theorem fstringFullFormatSpecG_proven : FstringFullFormatSpecG := ⟨fstringFullFormatSpec_proven, stringLoops_proven⟩
def TstringFullFormatSpecG : Prop := TstringFullFormatSpec ∧ StringLoops
theorem tstringFullFormatSpecG_proven : TstringFullFormatSpecG := ⟨tstringFullFormatSpec_proven, stringLoops_proven⟩
def TstringRuleG : Prop := TstringRule ∧ StringLoops
theorem tstringRuleG_proven : TstringRuleG := ⟨tstringRule_proven, stringLoops_proven⟩
def StringsRuleG : Prop := StringsRule ∧ StringLoops
theorem stringsRuleG_proven : StringsRuleG := ⟨stringsRule_proven, stringLoops_proven⟩
def InvalidStringTstringConcatG : Prop := InvalidStringTstringConcat ∧ StringLoops
theorem invalidStringTstringConcatG_proven : InvalidStringTstringConcatG := ⟨invalidStringTstringConcat_proven, stringLoops_proven⟩
def InvalidFstringConversionCharacterG : Prop := InvalidFstringConversionCharacter ∧ FieldGroups
theorem invalidFstringConversionCharacterG_proven : InvalidFstringConversionCharacterG := ⟨invalidFstringConversionCharacter_proven, fieldGroups_proven⟩
def InvalidTstringConversionCharacterG : Prop := InvalidTstringConversionCharacter ∧ FieldGroups
theorem invalidTstringConversionCharacterG_proven : InvalidTstringConversionCharacterG := ⟨invalidTstringConversionCharacter_proven, fieldGroups_proven⟩
def InvalidFstringReplacementFieldG : Prop := InvalidFstringReplacementField ∧ FieldGroups ∧ StringLoops
theorem invalidFstringReplacementFieldG_proven : InvalidFstringReplacementFieldG := ⟨invalidFstringReplacementField_proven, fieldGroups_proven, stringLoops_proven⟩
def InvalidTstringReplacementFieldG : Prop := InvalidTstringReplacementField ∧ FieldGroups ∧ StringLoops
theorem invalidTstringReplacementFieldG_proven : InvalidTstringReplacementFieldG := ⟨invalidTstringReplacementField_proven, fieldGroups_proven, stringLoops_proven⟩

/-! ### The t-string twin of the f-string messages -/

/-- `f'` and `t'`, and `'` + newline, as bytes. -/
def fQuote : List Nat := [102, 39]
def tQuote : List Nat := [116, 39]
def quoteNl : List Nat := [39, 10]

/-- `invalid_tstring_replacement_field` is `invalid_fstring_replacement_field` with "t-string:"
for "f-string:" (python.gram:1587-1625). The statement: for every text between the quotes, when
the f-string ends in "f-string: <m>", the same t-string ends in "t-string: <m>". -/
def TstringFieldMessages : Prop := ∀ (body : List Nat) (m : String),
  errMsgOf (parseStr {} (fQuote ++ body ++ quoteNl) .file) = some ("f-string: " ++ m) →
  errMsgOf (parseStr {} (tQuote ++ body ++ quoteNl) .file) = some ("t-string: " ++ m)

set_option maxRecDepth 100000 in
/-- The body `{x:{a:}` (bytes 123 120 58 123 97 58 125): both raise "...: expecting '}', or
format specs", but the t-string's comes from `fstring_format_spec*` in
`invalid_tstring_replacement_field` (python.gram:1622), whose nested `fstring_replacement_field`
runs `invalid_fstring_replacement_field` and says "f-string: expecting '}', or format specs". -/
theorem tstringFieldMessages_refuted : ¬ TstringFieldMessages := fun h =>
  absurd (h [123, 120, 58, 123, 97, 58, 125] "expecting '}', or format specs" (by decide +kernel))
    (by decide +kernel)

end PyLean.PyGrammar.Peg
