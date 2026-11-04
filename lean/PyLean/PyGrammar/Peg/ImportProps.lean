import PyLean.PyGrammar.Peg.ErrorProps

/-!
What the helpers added to `Parser/action_helpers.c` and `Parser/pegen_errors.c` in 3.15 compute.
Each statement has a side that fails for a function that always raises or never does.
-/

namespace PyLean.PyGrammar.Peg

open Lexer

theorem raiseDecodeKnown_some (p : PS) (l : Loc) (e : PyError) (h : p.tok.err = some e) (t : String)
    (ht : decodeErrType e.cls = some t) :
    raiseDecodeKnown l p = (-1, (raiseErrorKnownLocation "SyntaxError" l.lineno l.colOffset l.endLineno
      l.endColOffset s!"({t}) {e.msg}" { p with tok := { p.tok with err := none } }).2) := by
  have e1 : raiseDecodeKnown l p = (-1, (raiseDecodeBody (some l) p.tok.err p).2) := rfl
  rw [e1, h]
  simp only [raiseDecodeBody, ht]
  rfl

/-- `_Pypegen_raise_decode_error_known_location`: a decode error becomes a `SyntaxError` naming its
kind, on the line of the node it is given; any other exception is left alone. -/
def RaiseDecodeKnown : Prop := ∀ (p : PS) (l : Loc) (e : PyError), p.tok.err = some e →
  (∀ t, decodeErrType e.cls = some t →
    ∃ x : PyError, (raiseDecodeKnown l p).2.tok.err = some x ∧ x.cls = "SyntaxError" ∧
      x.msg = s!"({t}) {e.msg}" ∧ x.lineno = some l.lineno) ∧
  (decodeErrType e.cls = none → (raiseDecodeKnown l p).2 = p)

theorem raiseDecodeKnown_proven : RaiseDecodeKnown := by
  intro p l e h
  constructor
  · intro t ht
    rw [raiseDecodeKnown_some p l e h t ht]
    have fresh : Fresh { p with tok := { p.tok with err := none } } := by
      simp [Fresh, PS.errOccurred]
    obtain ⟨x, h1, h2, h3, h4, _⟩ := raiseKnownLocation_err _ "SyntaxError" s!"({t}) {e.msg}"
      l.lineno (if l.colOffset == -5 then -5 else l.colOffset + 1) l.endLineno
      (if l.endColOffset == -5 then -5 else l.endColOffset + 1) fresh
    exact ⟨x, h1, h2, h3, h4⟩
  · intro ht
    have e1 : raiseDecodeKnown l p = (-1, (raiseDecodeBody (some l) p.tok.err p).2) := rfl
    rw [e1, h]
    simp only [raiseDecodeBody, ht]
    rfl

/-- `_PyPegen_raise_error_for_missing_comma`: silent on `print x` and `exec x`, and outside
brackets. Otherwise it raises, on the last line of `a` if `a` spans lines, to stop a multi-line
string concatenation being blamed on its first line. -/
def MissingComma : Prop := ∀ (a b : Ast) (p : PS),
  (isLegacyStmt a = true → raiseErrorForMissingComma a b p = (.null, p)) ∧
  ((p.tokenAt (p.mark - 1)).level = 0 → raiseErrorForMissingComma a b p = (.null, p)) ∧
  (isLegacyStmt a = false → (p.tokenAt (p.mark - 1)).level ≠ 0 → Fresh p →
    (raiseErrorForMissingComma a b p).1 = .null ∧
    ∃ e : PyError, (raiseErrorForMissingComma a b p).2.tok.err = some e ∧ e.cls = "SyntaxError" ∧
      e.msg = "invalid syntax. Perhaps you forgot a comma?" ∧
      e.lineno = some (if (locOf a).endLineno > (locOf a).lineno then (locOf a).endLineno
        else (locOf a).lineno))

theorem missingComma_proven : MissingComma := by
  intro a b p
  refine ⟨fun h => ?_, fun h => ?_, fun h1 h2 fresh => ?_⟩
  · simp [raiseErrorForMissingComma, h, bind, StateT.bind, pure, StateT.pure]
  · by_cases hl : isLegacyStmt a = true
    · simp [raiseErrorForMissingComma, hl, bind, StateT.bind, pure, StateT.pure]
    · simp [raiseErrorForMissingComma, hl, h, bind, StateT.bind, pure, StateT.pure, get, getThe,
        MonadStateOf.get, StateT.get]
  · by_cases hs : (locOf a).endLineno > (locOf a).lineno
    · have e3 : raiseErrorForMissingComma a b p = (.null,
          (raiseErrorKnownLocation "SyntaxError" (locOf a).endLineno (locOf a).colOffset
            (locOf a).endLineno (locOf a).endColOffset
            "invalid syntax. Perhaps you forgot a comma?" p).2) := by
        simp [raiseErrorForMissingComma, h1, h2, hs, bind, StateT.bind, pure, StateT.pure, get, getThe, MonadStateOf.get, StateT.get]
        cases raiseErrorKnownLocation "SyntaxError" (locOf a).endLineno (locOf a).colOffset
          (locOf a).endLineno (locOf a).endColOffset "invalid syntax. Perhaps you forgot a comma?" p
        rfl
      rw [e3]
      obtain ⟨x, q1, q2, q3, q4, _⟩ := raiseKnownLocation_err p "SyntaxError"
        "invalid syntax. Perhaps you forgot a comma?" (locOf a).endLineno
        (if (locOf a).colOffset == -5 then -5 else (locOf a).colOffset + 1) (locOf a).endLineno
        (if (locOf a).endColOffset == -5 then -5 else (locOf a).endColOffset + 1) fresh
      exact ⟨rfl, x, q1, q2, q3, by rw [q4, if_pos hs]⟩
    · have e3 : raiseErrorForMissingComma a b p = (.null,
          (raiseErrorKnownLocation "SyntaxError" (locOf a).lineno (locOf a).colOffset
            (locOf b).endLineno (locOf b).endColOffset
            "invalid syntax. Perhaps you forgot a comma?" p).2) := by
        simp [raiseErrorForMissingComma, h1, h2, hs, bind, StateT.bind, pure, StateT.pure, get, getThe, MonadStateOf.get, StateT.get]
        cases raiseErrorKnownLocation "SyntaxError" (locOf a).lineno (locOf a).colOffset
          (locOf b).endLineno (locOf b).endColOffset "invalid syntax. Perhaps you forgot a comma?" p
        rfl
      rw [e3]
      obtain ⟨x, q1, q2, q3, q4, _⟩ := raiseKnownLocation_err p "SyntaxError"
        "invalid syntax. Perhaps you forgot a comma?" (locOf a).lineno
        (if (locOf a).colOffset == -5 then -5 else (locOf a).colOffset + 1) (locOf b).endLineno
        (if (locOf b).endColOffset == -5 then -5 else (locOf b).endColOffset + 1) fresh
      exact ⟨rfl, x, q1, q2, q3, by rw [q4, if_neg hs]⟩

/-- The `SyntaxError` of `_PyErr_RaiseSyntaxError`, `Python/errors.c:1956-1973`, `text` `None`. -/
def syntaxErrAt (msg : String) (a b c e : Int) : PyError :=
  { cls := "SyntaxError", msg := msg, lineno := some a, offset := some b, endLineno := some c,
    endOffset := some e, text := none }

/-- The state after `_PyErr_EmitSyntaxWarning` recorded the warning. -/
def warned (p : PS) (msg : String) (lineno : Int) : PS :=
  { p with tok := { p.tok with warnings := ("SyntaxWarning", msg, lineno) :: p.tok.warnings } }

/-- The state after `_PyErr_EmitSyntaxWarning` raised the `SyntaxError` in place of the warning. -/
def warnRaised (p : PS) (msg : String) (l : Loc) : PS :=
  { p with tok := { p.tok with err := some (syntaxErrAt msg l.lineno (l.colOffset + 1) l.endLineno
    (l.endColOffset + 1)) } }

/-- `_warn_relative_import_of_lazy`: on the first pass, it warns about `from . lazy import x`, where
space separates the dots from the name, and says how many dots. `from .lazy import x` is left
alone, and so is everything on the second pass. Under a filter that makes `SyntaxWarning` an error
(`-W error`), the warning becomes a `SyntaxError` with the same message at the module name, columns
one-based (`_PyErr_EmitSyntaxWarning`, `Python/errors.c:1984-1994`), and the result is -1; otherwise
it is 0. The last element of `dots` is a token, as the grammar's `('.' | '...')+` gives. -/
def WarnRelativeLazy : Prop := ∀ (dots module : Ast) (p : PS) (d : Token),
  (seqOf dots).getLast? = some (.tok d) →
  (p.callInvalidRules = true → warnRelativeImportOfLazy dots module p = (0, p)) ∧
  (d.endLineno = (locOf module).lineno → d.endColOffset = (locOf module).colOffset →
    warnRelativeImportOfLazy dots module p = (0, p)) ∧
  (p.callInvalidRules = false →
    ¬(d.endLineno = (locOf module).lineno ∧ d.endColOffset = (locOf module).colOffset) →
    (p.cfg.warnErrors.contains "SyntaxWarning" = false →
      warnRelativeImportOfLazy dots module p = (0, warned p (lazyMsg dots) (locOf module).lineno)) ∧
    (p.cfg.warnErrors.contains "SyntaxWarning" = true →
      warnRelativeImportOfLazy dots module p = (-1, warnRaised p (lazyMsg dots) (locOf module))))

theorem warnLazy_second (dots module : Ast) (p : PS) (h : p.callInvalidRules = true) :
    warnRelativeImportOfLazy dots module p = (0, p) := by
  simp [warnRelativeImportOfLazy, h, bind, StateT.bind, pure, StateT.pure, get, getThe,
    MonadStateOf.get, StateT.get]

theorem warnLazy_fire (dots module : Ast) (p : PS) (d : Token) (hd : (seqOf dots).getLast? = some (.tok d))
    (h1 : p.callInvalidRules = false)
    (h2 : ¬(d.endLineno = (locOf module).lineno ∧ d.endColOffset = (locOf module).colOffset)) :
    warnRelativeImportOfLazy dots module p = emitSyntaxWarning (lazyMsg dots) (locOf module).lineno
      ((locOf module).colOffset + 1) (locOf module).endLineno ((locOf module).endColOffset + 1) p := by
  have hn : ¬((d.endLineno == (locOf module).lineno && d.endColOffset == (locOf module).colOffset)
      = true) := by
    simpa using h2
  simp only [warnRelativeImportOfLazy, h1, hd, hn, bind, StateT.bind, pure, StateT.pure, get, getThe,
    MonadStateOf.get, StateT.get, Bool.false_eq_true, ↓reduceIte]

theorem emit_ok (msg : String) (a b c e : Int) (p : PS)
    (h : p.cfg.warnErrors.contains "SyntaxWarning" = false) :
    emitSyntaxWarning msg a b c e p = (0, warned p msg a) := by
  simp only [emitSyntaxWarning, h, bind, StateT.bind, pure, StateT.pure, get, getThe,
    MonadStateOf.get, StateT.get, Bool.false_eq_true, ↓reduceIte, modify, modifyGet,
    MonadStateOf.modifyGet, StateT.modifyGet, MonadState.modifyGet]
  rfl

theorem emit_err (msg : String) (a b c e : Int) (p : PS)
    (h : p.cfg.warnErrors.contains "SyntaxWarning" = true) :
    emitSyntaxWarning msg a b c e p =
      (-1, { p with tok := { p.tok with err := some (syntaxErrAt msg a b c e) } }) := by
  simp only [emitSyntaxWarning, h, bind, StateT.bind, pure, StateT.pure, get, getThe,
    MonadStateOf.get, StateT.get, ↓reduceIte, setErr, modify, modifyGet,
    MonadStateOf.modifyGet, StateT.modifyGet, MonadState.modifyGet]
  rfl

theorem warnRelativeLazy_proven : WarnRelativeLazy := by
  intro dots module p d hd
  refine ⟨fun h => warnLazy_second dots module p h, fun h1 h2 => ?_, fun h1 h2 => ?_⟩
  · by_cases h : p.callInvalidRules = true
    · exact warnLazy_second dots module p h
    · simp [warnRelativeImportOfLazy, h, hd, h1, h2, bind, StateT.bind, pure, StateT.pure, get,
        getThe, MonadStateOf.get, StateT.get]
  · rw [warnLazy_fire dots module p d hd h1 h2]
    exact ⟨fun h => emit_ok _ _ _ _ _ p h, fun h => emit_err _ _ _ _ _ p h⟩

/-- `_PyPegen_checked_from_import`: `lazy from __future__` is refused; a failed warning
(`Parser/action_helpers.c:2108-2110`, `-W error` on `from . lazy import x`) gives `NULL` with the
state the warning left; otherwise the result is the `ImportFrom` of the module, the names, the
number of dots, and whether `lazy` was there; and only a `from __future__ import barry_as_FLUFL`
turns on `<>` for the tokenizer and the parser. The module is a `Name`, as `dotted_name`
guarantees, which is what `.id` reads. -/
def CheckedFromImport : Prop := ∀ (dots m names lazy : Ast) (l c el ec : Int) (p : PS),
  (countDots dots = 0 → isFutureModule m = true → hasValue lazy = true → Fresh p →
    (checkedFromImport dots m names lazy l c el ec p).1 = .null ∧
    ∃ e : PyError, (checkedFromImport dots m names lazy l c el ec p).2.tok.err = some e ∧
      e.cls = "SyntaxError" ∧ e.msg = "lazy from __future__ import is not allowed") ∧
  (countDots dots > 0 → hasValue lazy = false → isLazyModule m = true →
    (warnRelativeImportOfLazy dots m p).1 < 0 →
    checkedFromImport dots m names lazy l c el ec p = (.null, (warnRelativeImportOfLazy dots m p).2)) ∧
  (¬(countDots dots = 0 ∧ isFutureModule m = true ∧ hasValue lazy = true) →
    ¬(countDots dots > 0 ∧ hasValue lazy = false ∧ isLazyModule m = true ∧
      (warnRelativeImportOfLazy dots m p).1 < 0) →
    (checkedFromImport dots m names lazy l c el ec p).1 = mkAst .ImportFrom
      [fieldOf m "id", names, .int (countDots dots), .int (if hasValue lazy then 1 else 0),
       .int l, .int c, .int el, .int ec]) ∧
  (countDots dots = 0 → isFutureModule m = true → hasValue lazy = false →
    (seqOf names).any isBarryAlias = true →
    (checkedFromImport dots m names lazy l c el ec p).2.tok.barryAsBdfl = true ∧
    (checkedFromImport dots m names lazy l c el ec p).2.flagBarry = true) ∧
  (¬(countDots dots = 0 ∧ isFutureModule m = true) →
    (checkedFromImport dots m names lazy l c el ec p).2.tok.barryAsBdfl = p.tok.barryAsBdfl)

theorem emit_keeps_barry (msg : String) (a b c e : Int) (p : PS) :
    (emitSyntaxWarning msg a b c e p).2.tok.barryAsBdfl = p.tok.barryAsBdfl := by
  cases h : p.cfg.warnErrors.contains "SyntaxWarning"
  · rw [emit_ok _ _ _ _ _ p h]
    rfl
  · rw [emit_err _ _ _ _ _ p h]

theorem warn_keeps_barry (dots m : Ast) (p : PS) :
    (warnRelativeImportOfLazy dots m p).2.tok.barryAsBdfl = p.tok.barryAsBdfl := by
  by_cases h : p.callInvalidRules = true
  · rw [warnLazy_second dots m p h]
  · cases hl : (seqOf dots).getLast? with
    | none => simp [warnRelativeImportOfLazy, h, hl, bind, StateT.bind, pure, StateT.pure, get, getThe, MonadStateOf.get, StateT.get]
    | some x =>
      cases x with
      | tok d =>
        by_cases q : d.endLineno = (locOf m).lineno ∧ d.endColOffset = (locOf m).colOffset
        · simp [warnRelativeImportOfLazy, h, hl, q, bind, StateT.bind, pure, StateT.pure, get, getThe, MonadStateOf.get, StateT.get]
        · rw [warnLazy_fire dots m p d hl (by simpa using h) q]
          exact emit_keeps_barry _ _ _ _ _ p
      | _ => simp [warnRelativeImportOfLazy, h, hl, bind, StateT.bind, pure, StateT.pure, get, getThe, MonadStateOf.get, StateT.get]

/-- `checkedFromImport` on the `lazy` path, as the warning's result decides. -/
theorem checked_lazy_path (dots m names lazy : Ast) (l c el ec : Int) (p : PS)
    (hn : ¬((countDots dots == 0 && isFutureModule m) = true))
    (hw : (decide (countDots dots > 0) && !hasValue lazy && isLazyModule m) = true) :
    checkedFromImport dots m names lazy l c el ec p =
      if (warnRelativeImportOfLazy dots m p).1 < 0 then (.null, (warnRelativeImportOfLazy dots m p).2)
      else (mkAst .ImportFrom
        [fieldOf m "id", names, .int (countDots dots), .int (if hasValue lazy then 1 else 0),
         .int l, .int c, .int el, .int ec], (warnRelativeImportOfLazy dots m p).2) := by
  simp only [checkedFromImport, hn, hw, bind, StateT.bind, pure, StateT.pure, get, getThe,
    MonadStateOf.get, StateT.get, Bool.false_eq_true, ↓reduceIte]
  cases warnRelativeImportOfLazy dots m p with
  | mk r q =>
    by_cases hr : r < 0
    · simp only [hr, ↓reduceIte]
      rfl
    · simp only [hr, ↓reduceIte]
      rfl

theorem checkedFromImport_proven : CheckedFromImport := by
  intro dots m names lazy l c el ec p
  refine ⟨fun h1 h2 h3 fresh => ?_, fun h1 h2 h3 h4 => ?_, fun h hw' => ?_, fun h1 h2 h3 h4 => ?_,
    fun h => ?_⟩
  · have e : checkedFromImport dots m names lazy l c el ec p = (.null,
        (raiseRange "SyntaxError" lazy lazy "lazy from __future__ import is not allowed" p).2) := by
      simp [checkedFromImport, h1, h2, h3, bind, StateT.bind, pure, StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
        MonadState.modifyGet, get, getThe, MonadStateOf.get, StateT.get]
      cases raiseRange "SyntaxError" lazy lazy "lazy from __future__ import is not allowed" p
      rfl
    rw [e]
    obtain ⟨x, q1, q2, q3, _⟩ := raiseKnownLocation_err p "SyntaxError"
      "lazy from __future__ import is not allowed" (locOf lazy).lineno
      (if (locOf lazy).colOffset == -5 then -5 else (locOf lazy).colOffset + 1) (locOf lazy).endLineno
      (if (locOf lazy).endColOffset == -5 then -5 else (locOf lazy).endColOffset + 1) fresh
    exact ⟨rfl, x, q1, q2, q3⟩
  · have hn : ¬((countDots dots == 0 && isFutureModule m) = true) := by
      simp only [Bool.and_eq_true, beq_iff_eq, not_and]
      intro h0
      omega
    have hw : (decide (countDots dots > 0) && !hasValue lazy && isLazyModule m) = true := by
      simp [h1, h2, h3]
    rw [checked_lazy_path dots m names lazy l c el ec p hn hw, if_pos h4]
  · by_cases hf : countDots dots = 0 ∧ isFutureModule m = true
    · have hz : hasValue lazy = false := by
        cases hv : hasValue lazy with
        | false => rfl
        | true => exact (h ⟨hf.1, hf.2, hv⟩).elim
      cases hb : (seqOf names).any isBarryAlias <;>
        simp [checkedFromImport, hf.1, hf.2, hz, hb, bind, StateT.bind, pure, StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
        MonadState.modifyGet, get, getThe, MonadStateOf.get, StateT.get]
    · have hn : ¬((countDots dots == 0 && isFutureModule m) = true) := by
        simpa using hf
      by_cases hw : (decide (countDots dots > 0) && !hasValue lazy && isLazyModule m) = true
      · rw [checked_lazy_path dots m names lazy l c el ec p hn hw]
        have hr : ¬ (warnRelativeImportOfLazy dots m p).1 < 0 := by
          intro hr
          simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hw
          exact hw' ⟨hw.1.1, hw.1.2, hw.2, hr⟩
        rw [if_neg hr]
      · simp only [checkedFromImport, hn, hw, bind, StateT.bind, pure, StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
        MonadState.modifyGet, get, getThe, MonadStateOf.get, StateT.get]
        rfl
  · have e : (checkedFromImport dots m names lazy l c el ec p).2 =
        { p with flagBarry := true, tok := { p.tok with barryAsBdfl := true } } := by
      simp [checkedFromImport, h1, h2, h3, h4, bind, StateT.bind, pure, StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
        MonadState.modifyGet, get, getThe, MonadStateOf.get, StateT.get]
    rw [e]
    exact ⟨rfl, rfl⟩
  · have hn : ¬((countDots dots == 0 && isFutureModule m) = true) := by
      simpa using h
    by_cases hw : (decide (countDots dots > 0) && !hasValue lazy && isLazyModule m) = true
    · rw [checked_lazy_path dots m names lazy l c el ec p hn hw]
      split
      · exact warn_keeps_barry dots m p
      · exact warn_keeps_barry dots m p
    · simp only [checkedFromImport, hn, hw, bind, StateT.bind, pure, StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
        MonadState.modifyGet, get, getThe, MonadStateOf.get, StateT.get]
      rfl

/-- `compile` raises nothing from the decoder but a `SyntaxError`: a string that does not decode is
invalid source, and its two sibling paths, `_PyPegen_decode_fstring_part` and
`_PyPegen_constant_from_string`, say so. -/
def decodeIsSyntax (src : List Nat) : Bool :=
  match parseStr {} src .file with
  | .error e => e.cls != "UnicodeDecodeError"
  | .ok _ => true

def DecodeErrorsAreSyntaxErrors : Prop := ∀ src : List Nat, decodeIsSyntax src = true

/-- `f'{x:\N{foo}}'`: `_PyPegen_decoded_constant_from_token` returns `NULL` with the decode error
still set. -/
def badSpec : List Nat := [102, 39, 123, 120, 58, 92, 78, 123, 102, 111, 111, 125, 125, 39]

set_option maxRecDepth 100000 in
theorem decodeErrorsAreSyntaxErrors_refuted : ¬ DecodeErrorsAreSyntaxErrors := fun h =>
  absurd (h badSpec) (by decide +kernel)

end PyLean.PyGrammar.Peg
