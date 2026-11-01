import PyLean.PyIO.Spec

/-!
`io.StringIO` (C) vs `_pyio.StringIO` (a `TextIOWrapper` over a UTF-8
`BytesIO`): refuted agreement statements. Each counterexample is evaluated
on the models of both twins.
-/

namespace PyLean.PyIO

open PyLean

/-- Two runs (constructor plus operations) agree: both constructors raise
exceptions of the same class, or both succeed and every operation agrees up
to the exception message. -/
def sameRun : Py (List (Py Val)) → Py (List (Py Val)) → Bool
  | .ok a, .ok b => allSameClass a b
  | .error e₁, .error e₂ => e₁.className == e₂.className
  | _, _ => false

def SameRun (a b : Py (List (Py Val))) : Prop := sameRun a b = true

instance (a b : Py (List (Py Val))) : Decidable (SameRun a b) := inferInstanceAs (Decidable (_ = true))

/-- The legal `newline` arguments: `None`, `''`, `'\n'`, `'\r'`, `'\r\n'`
(Doc/library/io.rst, `TextIOWrapper`/`StringIO`). -/
def LegalNewline (nl : Option (List Nat)) : Prop :=
  nl = none ∨ nl = some [] ∨ nl = some [10] ∨ nl = some [13] ∨ nl = some [13, 10]

instance (nl : Option (List Nat)) : Decidable (LegalNewline nl) := by
  unfold LegalNewline; infer_instance

/-- The C constructor accepts exactly the legal `newline` values. -/
def CStringIONewlineLegal : Prop :=
  ∀ nl : Option (List Nat), (SC.init none nl).toBool = true ↔ LegalNewline nl

/-- `io.StringIO(newline='\x00')` is accepted: the C check reads the UTF-8
bytes of `newline` as a NUL-terminated string (stringio.c:708-715), so
`'\x00'` looks like `''`. `_pyio` raises `ValueError`. -/
theorem cStringIONewlineLegal_refuted : ¬CStringIONewlineLegal := by
  intro h
  have := (h (some [0])).mp (by decide)
  revert this
  decide

/-- The Python constructor accepts exactly the legal `newline` values. -/
def PyStringIONewlineLegal : Prop :=
  ∀ nl : Option (List Nat), (TP.init none nl).toBool = true ↔ LegalNewline nl

theorem pyStringIONewlineLegal_proven : PyStringIONewlineLegal := by
  intro nl
  cases nl with
  | none => simp [TP.init, TP.init.build, LegalNewline, Except.toBool]
  | some l =>
    unfold TP.init
    by_cases hl : l = [] ∨ l = [10] ∨ l = [13] ∨ l = [13, 10]
    · simp only [hl, Bool.not_true, Bool.false_eq_true, ite_false, decide_true]
      simp [TP.init.build, LegalNewline, Except.toBool]
      rcases hl with h | h | h | h <;> simp [h]
    · have : ¬ LegalNewline (some l) := by
        unfold LegalNewline; simp only [reduceCtorEq, false_or, Option.some.injEq]; exact hl
      simp only [this, iff_false]
      simp [hl, Except.toBool, decide_eq_true_eq]

/-- For every legal `newline` and every sequence of writes into a fresh
`StringIO()`, the twins agree on every result, `getvalue()` included. -/
def StringIOWritesTwins : Prop :=
  ∀ (nl : Option (List Nat)) (ws : List (List Nat)), LegalNewline nl →
    SameRun (runSC none nl (ws.map SOp.write ++ [.getvalue])) (runSPy none nl (ws.map SOp.write ++ [.getvalue]))

/-- `newline=None`: `write('a\r')` then `write('\nb')`. The C StringIO
translates every write on its own (`_PyIncrementalNewlineDecoder_decode(...,
1 /* always final */)`, stringio.c:199-200), so the lone `\r` becomes `\n`
and `getvalue()` is `'a\n\nb'`; `_pyio` translates the stored text as a
whole and returns `'a\nb'` (as a file written in two pieces would). -/
theorem stringIOWritesTwins_refuted : ¬StringIOWritesTwins := by
  intro h
  have := h none [[97, 13], [10, 98]] (by decide)
  revert this
  decide

/-- Constructing `StringIO(value, newline)` and then writing `s` gives the same
results in both twins (the position after construction is 0). -/
def StringIOInitWriteTwins : Prop :=
  ∀ nl v s, LegalNewline nl →
    SameRun (runSC (some v) nl [.write s, .getvalue]) (runSPy (some v) nl [.write s, .getvalue])

/-- `StringIO('é').write('x')`: C overwrites the first character (`'x'`);
`_pyio` overwrites the first *byte* of the UTF-8 encoding and `getvalue()`
raises `UnicodeDecodeError`. -/
theorem stringIOInitWriteTwins_refuted : ¬StringIOInitWriteTwins := by
  intro h
  have := h (some [10]) [233] [120] (by decide)
  revert this
  decide

/-- After `read(k)`, `write(s)` overwrites at the read position in both
twins (ASCII text, so byte and character positions coincide). -/
def StringIOReadWriteTwins : Prop :=
  ∀ v k s, v.all (· < 128) = true → s.all (· < 128) = true →
    SameRun (runSC (some v) (some [10]) [.read (some k), .write s, .getvalue])
      (runSPy (some v) (some [10]) [.read (some k), .write s, .getvalue])

/-- `StringIO('abcdef')`, `read(1)`, `write('X')`: C gives `'aXcdef'`; the
`_pyio` `TextIOWrapper` has already read a 2048-byte chunk ahead, its
`BytesIO` is at the end, and the write appends: `'abcdefX'`. -/
theorem stringIOReadWriteTwins_refuted : ¬StringIOReadWriteTwins := by
  intro h
  have := h [97, 98, 99, 100, 101, 102] 1 [88] (by decide) (by decide)
  revert this
  decide

/-- The read operations: none of them closes or writes. -/
def SOp.IsRead : SOp → Prop
  | .read _ | .readline _ | .readlines _ | .next => True
  | _ => False

instance (o : SOp) : Decidable o.IsRead := by unfold SOp.IsRead; split <;> infer_instance

/-- After any sequence of reads on an open stream, `tell()` returns a
position in both twins. -/
def StringIOTellAfterReads : Prop :=
  ∀ v nl ops, LegalNewline nl → (∀ o ∈ ops, SOp.IsRead o) →
    (∀ rs, runSC (some v) nl (ops ++ [.tell]) = .ok rs → (rs.getLast?.map Except.toBool) = some true) ∧
    (∀ rs, runSPy (some v) nl (ops ++ [.tell]) = .ok rs → (rs.getLast?.map Except.toBool) = some true)

/-- `_pyio.StringIO('a\nb\nc\n').readlines(1)` stops after the first line
inside `for line in self`, which left `TextIOWrapper._telling` false
(`__next__`, _pyio.py:2629-2636), so `tell()` raises
`OSError('telling position disabled by next() call')`. -/
theorem stringIOTellAfterReads_refuted : ¬StringIOTellAfterReads := by
  intro h
  have h2 := (h [97, 10, 98, 10, 99, 10] (some [10]) [.readlines (some 1)] (by decide) (by decide)).2
  have e : runSPy (some [97, 10, 98, 10, 99, 10]) (some [10]) ([.readlines (some 1)] ++ [.tell]) =
      .ok [.ok (.list [.str [97, 10]]), .error (osError "telling position disabled by next() call")] := by
    decide
  have := h2 _ e
  revert this
  decide

/-- On an open stream, reading the `newlines` attribute never raises (both
twins), after any reads. -/
def StringIONewlinesAttr : Prop :=
  ∀ v nl ops, LegalNewline nl → (∀ o ∈ ops, SOp.IsRead o) →
    (∀ rs, runSC (some v) nl (ops ++ [.newlines]) = .ok rs → (rs.getLast?.map Except.toBool) = some true) ∧
    (∀ rs, runSPy (some v) nl (ops ++ [.newlines]) = .ok rs → (rs.getLast?.map Except.toBool) = some true)

/-- `_pyio.StringIO('a\nb')` (default `newline='\n'`), `read()`, then
`newlines`: the plain UTF-8 decoder has no `newlines` attribute and
`TextIOWrapper.newlines` (_pyio.py:2731-2733) raises `AttributeError`. -/
theorem stringIONewlinesAttr_refuted : ¬StringIONewlinesAttr := by
  intro h
  have h2 := (h [97, 10, 98] (some [10]) [.read none] (by decide) (by decide)).2
  have e : runSPy (some [97, 10, 98]) (some [10]) ([.read none] ++ [.newlines]) =
      .ok [.ok (.str [97, 10, 98]),
        .error (.named "AttributeError" "'IncrementalDecoder' object has no attribute 'newlines'")] := by
    decide
  have := h2 _ e
  revert this
  decide

end PyLean.PyIO
