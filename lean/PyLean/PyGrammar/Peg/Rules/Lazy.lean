import PyLean.PyGrammar.Peg.Interp

/-! `lazy import` and the diagnostics of `invalid_import`, run on real text. -/

namespace PyLean.PyGrammar.Peg

open Lexer

/-- The message of the exception a parse ends in, if it ends in one. -/
def errMsgOf : Except PyError Ast → Option String
  | .error e => some e.msg
  | .ok _ => none

/-- `"import"` and `"lazy import"` as bytes. -/
def importBytes : List Nat := [105, 109, 112, 111, 114, 116]
def lazyImportBytes : List Nat := [108, 97, 122, 121, 32] ++ importBytes

/-- 3.15 lets `import_name` and `import_from` start with the soft keyword `lazy`
(`Grammar/python.gram:227-235`), and `invalid_import_from_targets` diagnoses `lazy from x import`
like `from x import`. The statement: whatever follows, when `import ...` gets the targeted
`invalid_import` message "Expected one or more names after 'import'", so does
`lazy import ...`. -/
def LazyImportDiagnosed : Prop := ∀ rest : List Nat,
  errMsgOf (parseStr {} (importBytes ++ rest) .file) =
      some "Expected one or more names after 'import'" →
  errMsgOf (parseStr {} (lazyImportBytes ++ rest) .file) =
      some "Expected one or more names after 'import'"

set_option maxRecDepth 100000 in
/-- `lazy import\n`: `invalid_import` starts with `'import'`, so at `lazy` it fails, and the
second pass ends in the generic "invalid syntax". -/
theorem lazyImportDiagnosed_refuted : ¬ LazyImportDiagnosed := fun h =>
  absurd (h [10] (by decide +kernel)) (by decide +kernel)

end PyLean.PyGrammar.Peg
