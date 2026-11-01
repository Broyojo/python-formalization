import PyLean.TextLibs.CsvProps

/-!
Properties of `csv.reader` and `csv.writer` over fallible, re-entrant objects. An input iterator or
a row is a script, so these quantify over everything such an object can do that the C code sees.
-/

namespace PyLean.TextLibs.Csv

open PyLean PyLean.TextLibs

set_option linter.unusedSimpArgs false

/-! ### Reader: one step of the loop -/

theorem iterNext_ret (d : Dialect) (f : Nat) (c : RCtx) (o : Obj) (r : List Step)
    (h : c.acts = .ret o :: r) :
    iterNext d (f + 1) c = ({ c with acts := r }, .ok (some o)) := by
  simp [iterNext, h]

theorem iterNext_raise (d : Dialect) (f : Nat) (c : RCtx) (e : PyExc) (r : List Step)
    (h : c.acts = .raise e :: r) :
    iterNext d (f + 1) c = ({ c with acts := r }, .error e) := by
  simp [iterNext, h]

theorem iterNext_stop (d : Dialect) (f : Nat) (c : RCtx) (r : List Step)
    (h : c.acts = .stop :: r) :
    iterNext d (f + 1) c = ({ c with acts := r }, .ok Option.none) := by
  simp [iterNext, h]

theorem iterNext_nil (d : Dialect) (f : Nat) (c : RCtx) (h : c.acts = []) :
    iterNext d (f + 1) c = (c, .ok Option.none) := by
  simp [iterNext, h]

/-! ### Reader: failures -/

/-- An exception from the input iterator passes through unchanged, and the reader is not left in a
bad state: the next `__next__` starts a fresh record from the next line, whatever was half read.
This is `Reader_iternext_lock_held`'s `lineobj == NULL` branch with an exception set. -/
def IterRaisePasses : Prop :=
  ∀ (d : Dialect) (fuel : Nat) (c : RCtx) (e : PyExc) (rest : List Step),
    c.acts = .raise e :: rest →
    readerNext d (fuel + 3) c = ({ c with acts := rest, s := parseReset c.s }, .error e)

theorem iterRaisePasses_proven : IterRaisePasses := by
  intro d fuel c e rest h
  simp [readerNext, readerLoop, iterNext, h]

/-- The input iterator ending with no open field or quote is `StopIteration`, and ending in the
middle of a quoted field raises `csv.Error` in strict mode. Without `strict`, the open field is
saved and returned as a row. -/
def EofLaw : Prop :=
  ∀ (d : Dialect) (fuel : Nat) (c : RCtx) (rest : List Step),
    let c0 := { c with acts := rest }
    c.acts = .stop :: rest →
    (c.s.field = [] → c.s.state ≠ .IN_QUOTED_FIELD →
      readerLoop d (fuel + 2) c = (c0, .ok Option.none)) ∧
    ((c.s.field ≠ [] ∨ c.s.state = .IN_QUOTED_FIELD) → d.strict = true →
      readerLoop d (fuel + 2) c = (c0, .error (csvErr "unexpected end of data"))) ∧
    (∀ s, (c.s.field ≠ [] ∨ c.s.state = .IN_QUOTED_FIELD) → d.strict = false →
      parseSaveField d c.s = .ok s →
      readerLoop d (fuel + 2) c =
        ({ c0 with s := { s with fields := [], nullFields := true } }, .ok (some s.fields)))

theorem eofLaw_proven : EofLaw := by
  intro d fuel c rest c0 h
  have hi : iterNext d (fuel + 1) c = (c0, .ok Option.none) := iterNext_stop d fuel c rest h
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_, fun s h1 h2 h3 => ?_⟩
  · simp only [readerLoop, hi]
    simp [c0, h1, h2]
  · simp only [readerLoop, hi]
    have hc' : (!c.s.field.isEmpty) = true ∨ c.s.state = .IN_QUOTED_FIELD := by
      simpa [List.isEmpty_eq_false_iff] using h1
    simp only [c0, hc', if_true, h2]
  · simp only [readerLoop, hi]
    have hc' : (!c.s.field.isEmpty) = true ∨ c.s.state = .IN_QUOTED_FIELD := by
      simpa [List.isEmpty_eq_false_iff] using h1
    simp only [c0, hc', if_true, h2, Bool.false_eq_true, if_false, h3]

/-- An item that is not a string raises `csv.Error` naming its type, and is consumed. The line
counter does not move, because the check at `Modules/_csv.c:958` comes before the increment. A
subclass of `str` is a line like any other. -/
def NotStrLine : Prop :=
  ∀ (d : Dialect) (fuel : Nat) (c : RCtx) (o : Obj) (rest : List Step),
    c.acts = .ret o :: rest → o.asStr = Option.none →
    readerLoop d (fuel + 2) c = ({ c with acts := rest }, .error (csvErr
      s!"iterator should return strings, not {o.ty.tp} (the file should be opened in text mode)"))

theorem notStrLine_proven : NotStrLine := by
  intro d fuel c o rest h1 h2
  simp only [readerLoop, iterNext_ret d fuel c o rest h1, h2]

/-- A failure while parsing a line raises it, and keeps the state C left behind: the counter has
already moved, and the characters before the failure are parsed. -/
def ParseFailureKeeps : Prop :=
  ∀ (d : Dialect) (fuel : Nat) (c : RCtx) (o : Obj) (l : List Nat) (rest : List Step) (s : RSt) (e : PyExc),
    c.acts = .ret o :: rest → o.asStr = some l → c.s.nullFields = false →
    parseLine d c.limit c.s l = (s, some e) →
    readerLoop d (fuel + 2) c =
      ({ c with acts := rest, lineNum := (c.lineNum + 1) % 2 ^ 64, s := s }, .error e)

theorem parseFailureKeeps_proven : ParseFailureKeeps := by
  intro d fuel c o l rest s e h1 h2 h3 h4
  simp only [readerLoop, iterNext_ret d fuel c o rest h1, h2, h3, Bool.false_eq_true, if_false]
  simp only [h4]

/-! ### Reader: re-entry -/

/-- The guard `iterator has already advanced the reader`, `Modules/_csv.c:968-973`: if the input
iterator's `__next__` runs the reader to the end of a row and then returns a line, the outer call
raises instead of adding to a row that has been handed out. `l` is any line that ends a record. -/
def AlreadyAdvanced : Prop :=
  ∀ (d : Dialect) (fuel : Nat) (lim : Int) (l : List Nat) (o : Obj) (s : RSt) (l2 : List Nat)
    (rest : List Step),
    parseLine d lim (parseReset {}) l = (s, Option.none) → s.state = .START_RECORD → o.asStr = some l2 →
    (readerNext d (fuel + 7) { acts := .eff .advance :: .ret (.str l) :: .ret o :: rest, limit := lim }).2 =
      .error (csvErr "iterator has already advanced the reader")

theorem readerNext_succ (d : Dialect) (f : Nat) (c : RCtx) :
    readerNext d (f + 1) c = readerLoop d f { c with s := parseReset c.s } := by
  simp [readerNext]

theorem iterNext_advance (d : Dialect) (f : Nat) (c : RCtx) (r : List Step)
    (h : c.acts = .eff .advance :: r) :
    iterNext d (f + 1) c =
      match readerNext d f { c with acts := r } with
      | (c', .error e) => if fatal e then (c', .error e) else iterNext d f c'
      | (c', .ok _) => iterNext d f c' := by
  cases hr : readerNext d f { c with acts := r } with
  | mk c' res => cases res <;> simp [iterNext, h, hr]

/-- One line that completes a record: the row is handed out and `self->fields` becomes `NULL`. -/
theorem loop_line (d : Dialect) (f : Nat) (c : RCtx) (o : Obj) (l : List Nat) (rest : List Step)
    (s : RSt) (h1 : c.acts = .ret o :: rest) (h2 : o.asStr = some l) (h3 : c.s.nullFields = false)
    (h4 : parseLine d c.limit c.s l = (s, Option.none)) (h5 : s.state = .START_RECORD) :
    readerLoop d (f + 2) c =
      ({ c with acts := rest, lineNum := (c.lineNum + 1) % 2 ^ 64,
                s := { s with fields := [], nullFields := true } }, .ok (some s.fields)) := by
  simp only [readerLoop, iterNext_ret d f c o rest h1, h2, h3, Bool.false_eq_true, if_false]
  simp only [h4, h5, if_true]

theorem alreadyAdvanced_proven : AlreadyAdvanced := by
  intro d fuel lim l o s l2 rest h1 h2 h3
  have hreset : parseReset (parseReset ({} : RSt)) = parseReset {} := rfl
  have hinner : readerNext d (fuel + 4)
      { s := parseReset {}, acts := .ret (.str l) :: .ret o :: rest, limit := lim } =
      ({ s := { s with fields := [], nullFields := true }, lineNum := 1, acts := .ret o :: rest,
         limit := lim }, .ok (some s.fields)) := by
    rw [readerNext_succ]
    exact loop_line d (fuel + 1) _ (.str l) l _ s rfl rfl rfl h1 h2
  rw [readerNext_succ, show fuel + 6 = (fuel + 4) + 2 from rfl]
  simp only [readerLoop]
  rw [iterNext_advance d (fuel + 4) _ (.ret (.str l) :: .ret o :: rest) rfl]
  have hc : ({ s := parseReset {}, acts := .eff .advance :: .ret (.str l) :: .ret o :: rest, limit := lim } : RCtx) =
      { s := parseReset {}, acts := .eff .advance :: .ret (.str l) :: .ret o :: rest, limit := lim } := rfl
  simp only [hinner]
  rw [iterNext_ret d (fuel + 3) _ o rest rfl]
  simp only [h3, if_true]

/-- The reader does not survive every re-entry: when the iterator's `__next__` runs the reader to the
end of input with a quoted field open, and then itself ends, the outer call saves a field into the
`NULL` `self->fields`. The guard above only covers an iterator that returns a line. This statement,
that no script crashes the reader, is false, and the script below is a plain Python class. -/
def ReaderNoCrash : Prop :=
  ∀ (d : Dialect) (fuel : Nat) (acts : List Step) (lim : Int),
    (readerNext d fuel { acts, limit := lim }).2 ≠ .error CRASH

theorem readerNoCrash_refuted : ¬ReaderNoCrash := by
  intro h
  exact h excel 16 [.eff .advance, .ret (.str [34, 97]), .stop, .stop] 131072 (by decide +kernel)

/-- With the fix to the crash, the condition is exactly this one: the end of input is reached with
`fields` gone and a quoted field still open. The crash needs `strict` off, and no script reaches it
through the other test, `field_len != 0`, because a row is only handed out with an empty field. -/
def CrashNeedsOpenQuote : Prop :=
  ∀ (d : Dialect) (c : RCtx) (fuel : Nat) (rest : List Step),
    c.acts = .stop :: rest → c.s.nullFields = true → c.s.field = [] → c.s.state ≠ .IN_QUOTED_FIELD →
    (readerLoop d (fuel + 2) c).2 = .ok Option.none

theorem crashNeedsOpenQuote_proven : CrashNeedsOpenQuote := by
  intro d c fuel rest h1 _ h3 h4
  exact congrArg Prod.snd ((eofLaw_proven d fuel c rest h1).1 h3 h4)

/-- `csv.field_size_limit` called from the input iterator applies to the line it returns, because
`parse_add_char` reads the limit for each character. -/
def LimitIsLive : Prop :=
  ∀ (d : Dialect) (fuel : Nat) (c : RCtx) (o : Obj) (n : Int) (rest : List Step),
    -(2 ^ 63) ≤ n → n ≤ 2 ^ 63 - 1 →
    c.acts = .eff (.setLimit (.int n)) :: .ret o :: rest →
    iterNext d (fuel + 2) c = ({ c with acts := rest, limit := n }, .ok (some o))

theorem limitIsLive_proven : LimitIsLive := by
  intro d fuel c o n rest h1 h2 h
  have hl : applyLimit c.limit (.int n) = n := by
    simp only [applyLimit, fieldSizeLimit]
    rw [if_neg (by omega)]
  simp [iterNext, h, hl]

/-! ### `parse_save_field` and `parse_add_char` -/

/-- `parse_add_char` raises exactly at the field limit, and otherwise appends one character. -/
def AddCharLimit : Prop :=
  ∀ (lim : Int) (s : RSt) (c : Nat),
    ((s.field.length : Int) ≥ lim →
      parseAddChar lim s c = .error (csvErr s!"field larger than field limit ({lim})")) ∧
    ((s.field.length : Int) < lim → parseAddChar lim s c = .ok { s with field := s.field ++ [c] })

theorem addCharLimit_proven : AddCharLimit := by
  intro lim s c
  constructor <;> intro h
  · simp [parseAddChar, h]
  · simp [parseAddChar, Int.not_le.mpr h]

/-- What `parse_save_field` appends, for every quoting style: with `QUOTE_NOTNULL` and `QUOTE_STRINGS`
an unquoted empty field is `None`; with `QUOTE_NONNUMERIC` and `QUOTE_STRINGS` an unquoted non-empty
field is `float(field)`, whose failure raises and keeps the field; everything else is a string. -/
def SaveFieldLaw : Prop :=
  ∀ (d : Dialect) (s : RSt), s.nullFields = false →
    (s.unquoted = true → s.field = [] → (d.quoting = QUOTE_NOTNULL ∨ d.quoting = QUOTE_STRINGS) →
      parseSaveField d s = .ok { s with fields := s.fields ++ [.none] }) ∧
    (s.unquoted = true → s.field ≠ [] → (d.quoting = QUOTE_NONNUMERIC ∨ d.quoting = QUOTE_STRINGS) →
      (∀ x, PyLean.Binary64.PyFloat_FromString (.str s.field) = .ok x →
        parseSaveField d s = .ok { s with field := [], fields := s.fields ++ [.float x] }) ∧
      (∀ e, PyLean.Binary64.PyFloat_FromString (.str s.field) = .error e →
        parseSaveField d s = .error e)) ∧
    (s.unquoted = false → parseSaveField d s = .ok { s with field := [], fields := s.fields ++ [.str s.field] }) ∧
    ((d.quoting = QUOTE_MINIMAL ∨ d.quoting = QUOTE_ALL ∨ d.quoting = QUOTE_NONE) →
      parseSaveField d s = .ok { s with field := [], fields := s.fields ++ [.str s.field] })

theorem saveFieldLaw_proven : SaveFieldLaw := by
  intro d s hn
  have ha : ∀ (t : RSt) (f : Field), t.nullFields = false →
      appendField t f = .ok { t with fields := t.fields ++ [f] } := by
    intro t f h
    simp [appendField, h]
  refine ⟨fun h1 h2 h3 => ?_, fun h1 h2 h3 => ⟨fun x hx => ?_, fun e he => ?_⟩, fun h1 => ?_, fun h => ?_⟩
  · simp only [parseSaveField]
    rw [if_pos ⟨h1, by simp [h2], h3⟩]
    exact ha s .none hn
  · have hne : s.field.isEmpty = false := List.isEmpty_eq_false_iff.2 h2
    have hA : ¬(s.unquoted = true ∧ s.field.isEmpty = true ∧ (d.quoting = QUOTE_NOTNULL ∨ d.quoting = QUOTE_STRINGS)) := by
      simp [hne]
    simp only [parseSaveField]
    rw [if_neg hA, if_pos ⟨h1, by simp [hne], h3⟩, hx]
    exact ha { s with field := [] } (.float x) hn
  · have hne : s.field.isEmpty = false := List.isEmpty_eq_false_iff.2 h2
    have hA : ¬(s.unquoted = true ∧ s.field.isEmpty = true ∧ (d.quoting = QUOTE_NOTNULL ∨ d.quoting = QUOTE_STRINGS)) := by
      simp [hne]
    simp only [parseSaveField]
    rw [if_neg hA, if_pos ⟨h1, by simp [hne], h3⟩, he]
  · have hA : ¬(s.unquoted = true ∧ s.field.isEmpty = true ∧ (d.quoting = QUOTE_NOTNULL ∨ d.quoting = QUOTE_STRINGS)) := by
      simp [h1]
    have hB : ¬(s.unquoted = true ∧ (!s.field.isEmpty) = true ∧ (d.quoting = QUOTE_NONNUMERIC ∨ d.quoting = QUOTE_STRINGS)) := by
      simp [h1]
    simp only [parseSaveField]
    rw [if_neg hA, if_neg hB]
    exact ha { s with field := [] } (.str s.field) hn
  · have hq : ¬(d.quoting = QUOTE_NOTNULL ∨ d.quoting = QUOTE_STRINGS) := by
      rcases h with h | h | h <;> simp [h] <;> decide
    have hq2 : ¬(d.quoting = QUOTE_NONNUMERIC ∨ d.quoting = QUOTE_STRINGS) := by
      rcases h with h | h | h <;> simp [h] <;> decide
    have hA : ¬(s.unquoted = true ∧ s.field.isEmpty = true ∧ (d.quoting = QUOTE_NOTNULL ∨ d.quoting = QUOTE_STRINGS)) :=
      fun x => hq x.2.2
    have hB : ¬(s.unquoted = true ∧ (!s.field.isEmpty) = true ∧ (d.quoting = QUOTE_NONNUMERIC ∨ d.quoting = QUOTE_STRINGS)) :=
      fun x => hq2 x.2.2
    simp only [parseSaveField]
    rw [if_neg hA, if_neg hB]
    exact ha { s with field := [] } (.str s.field) hn

/-- After `\r` or `\n` ends a record, any other character on the same input line is an error, a
further newline is ignored, and the end of the line finishes the record. -/
def EatCrnl : Prop :=
  ∀ (d : Dialect) (lim : Int) (s : RSt) (c : Nat), s.state = .EAT_CRNL →
    (isNl c = false → c ≠ EOL → parseProcessChar d lim s c = .error (csvErr
      "new-line character seen in unquoted field - do you need to open the file with newline=''?")) ∧
    (isNl c = true → parseProcessChar d lim s c = .ok s) ∧
    parseProcessChar d lim s EOL = .ok { s with state := .START_RECORD }

theorem eatCrnl_proven : EatCrnl := by
  intro d lim s c h
  refine ⟨fun h2 h3 => ?_, fun h2 => ?_, ?_⟩
  · unfold parseProcessChar
    simp [h, h2, h3]
  · unfold parseProcessChar
    simp [h, h2]
  · unfold parseProcessChar
    have : isNl EOL = false := by decide
    simp [h, this]

/-! ### Writer -/

/-- `writerow` of an object with no iterator is `csv.Error`, because a `TypeError` from
`PyObject_GetIter` is replaced, while any other exception from it passes through, and the writer is
untouched. `writerows` does not replace it: there the `TypeError` itself comes out. -/
def WriterIterFails : Prop :=
  ∀ (d : Dialect) (fuel : Nat) (c : WCtx) (seq : Obj) (e : PyExc),
    seq.getIter = .error e →
    writerowM d (fuel + 1) c seq =
      (c, .error (if isTypeError e then csvErr s!"iterable expected, not {seq.ty.tp}" else e)) ∧
    writerowsM d fuel c seq = (c, .error e)

theorem writerIterFails_proven : WriterIterFails := by
  intro d fuel c seq e h
  constructor
  · simp [writerowM, h]
  · simp [writerowsM, h]

/-- The end of `csv_writerow_lock_held`: `write` is called once with the record and its terminator,
and whatever object it returns is the result of `writerow`, or what it raises. -/
def WriteResult : Prop :=
  ∀ (d : Dialect) (fuel : Nat) (c : WCtx) (nf : Bool) (r : Py Obj) (rest : List (List Eff × Py Obj)),
    ¬(c.numFields > 0 ∧ c.buf.isEmpty = true) → c.calls = ([], r) :: rest →
    finishRow d (fuel + 3) c nf =
      ({ c with buf := c.buf ++ d.lineterminator, written := c.written ++ [c.buf ++ d.lineterminator],
                calls := rest }, r)

theorem writeResult_proven : WriteResult := by
  intro d fuel c nf r rest h1 h2
  simp only [finishRow]
  rw [if_neg h1]
  simp [callWrite, runEffs, h2]

/-- `write` raising makes `writerow` raise. The record has already been passed on, so the call is on
record, and `writerows` stops there: the rows after it are not written. -/
def WritesStopAtFailure : Prop :=
  ∀ (d : Dialect) (fuel : Nat) (c c' : WCtx) (row : Obj) (rest : List Step) (e : PyExc),
    writerowM d fuel c row = (c', .error e) →
    writerowsLoop d fuel c (.ret row :: rest) = (c', .error e)

theorem writesStopAtFailure_proven : WritesStopAtFailure := by
  intro d fuel c c' row rest e h
  simp [writerowsLoop, h]

/-- A row iterator or `str()` that raises ends `writerow` with that exception and without a call to
`write`. Here the iterator raises after `pre`, a prefix of string fields that append without error. -/
def FieldRaises : Prop :=
  ∀ (d : Dialect) (fuel : Nat) (c : WCtx) (s : List Nat) (e : PyExc) (r : List Step) (nf : Bool) (b : List Nat) (n : Int),
    joinAppend d c.buf c.numFields (some s) (initialQuoted d (.str s)) = .ok (b, n) →
    fieldLoop d (fuel + 2) c (.ret (.str s) :: .raise e :: r) nf =
      ({ c with buf := b, numFields := n }, .error e)

theorem fieldRaises_proven : FieldRaises := by
  intro d fuel c s e r nf b n h
  simp [fieldLoop, Obj.asStr, h]

/-- A field whose `str()` raises ends the row with that exception, after its own effects ran. -/
def StrRaises : Prop :=
  ∀ (d : Dialect) (fuel : Nat) (c : WCtx) (f : Obj) (e : PyExc) (r : List Step) (nf : Bool),
    f.asStr = Option.none → f.isNone = false → f.pyStr = ([], .error e) →
    fieldLoop d (fuel + 2) c (.ret f :: r) nf = (c, .error e)

theorem strRaises_proven : StrRaises := by
  intro d fuel c f e r nf h1 h2 h3
  simp [fieldLoop, h1, h2, h3, runEffs]

/-- `join_reset`: whatever a failed row left in the record buffer, the next `writerow` starts clean,
so an empty row writes only the terminator. -/
def WriterowResets : Prop :=
  ∀ (d : Dialect) (fuel : Nat) (c : WCtx), c.calls = [] →
    (writerowM d (fuel + 4) c (iterObj [])).1.written = c.written ++ [d.lineterminator]

theorem writerowResets_proven : WriterowResets := by
  intro d fuel c h
  simp [writerowM, iterObj, Obj.getIter, fieldLoop, finishRow, callWrite, h]

/-- `self->num_fields` is a C `int`, incremented with no check at `Modules/_csv.c:1297`, and
`join_append_data` writes a delimiter when it is positive. The statement is the invariant the
delimiter logic needs: once a field has been appended, the count stays positive. It is false at
`INT_MAX`: the next field wraps the count negative, and no delimiter is written for the next
`2 ^ 31` fields. A row of `2 ^ 31 + 5` empty strings shows it on CPython. -/
def NumFieldsPositive : Prop :=
  ∀ (d : Dialect) (buf : List Nat) (n : Int) (t : List Nat) (q : Bool) (b : List Nat) (n' : Int),
    1 ≤ n → n ≤ 2 ^ 31 - 1 → joinAppend d buf n (some t) q = .ok (b, n') → 1 ≤ n'

theorem numFieldsPositive_refuted : ¬NumFieldsPositive := by
  intro h
  have := h excel [] (2 ^ 31 - 1) [] false [44] (-(2 ^ 31)) (by decide) (by decide) (by decide +kernel)
  revert this
  decide

/-- Below `INT_MAX` the count is exact, so for every row shorter than `2 ^ 31` fields the delimiter
logic works: a field after the first gets one delimiter. The delimiter is the first thing written
for the field. -/
def JoinDelimiter : Prop :=
  ∀ (d : Dialect) (buf : List Nat) (n : Int) (t : List Nat) (q : Bool) (b : List Nat) (n' : Int),
    0 ≤ n → n < 2 ^ 31 - 1 → joinAppend d buf n (some t) q = .ok (b, n') →
    n' = n + 1 ∧ (n ≥ 1 → b.take (buf.length + 1) = buf ++ [d.delimiter]) ∧
    (n = 0 → b.take buf.length = buf)

theorem joinAppend_ok {d : Dialect} {buf : List Nat} {n : Int} {f : Option (List Nat)} {q : Bool}
    {b : List Nat} {n' : Int} (h : joinAppend d buf n f q = .ok (b, n')) :
    ∃ body q1 q2, joinField d (f.getD []) q1 = .ok (body, q2) ∧ n' = cIntWrap (n + 1) ∧
      b = buf ++ (if n > 0 then [d.delimiter] else []) ++ (if q2 then [d.quotechar] else []) ++ body ++
        (if q2 then [d.quotechar] else []) := by
  unfold joinAppend at h
  dsimp only at h
  split at h
  · split at h
    · obtain ⟨_, he, _⟩ := bind_ok h
      cases he
    · obtain ⟨q1, _, h⟩ := bind_ok h
      obtain ⟨⟨body, q2⟩, h2, h⟩ := bind_ok h
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨hb, hn⟩ := h
      exact ⟨body, q1, q2, h2, hn.symm, by simp only [← hb, List.append_assoc]⟩
  · obtain ⟨q1, _, h⟩ := bind_ok h
    obtain ⟨⟨body, q2⟩, h2, h⟩ := bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨hb, hn⟩ := h
    exact ⟨body, q1, q2, h2, hn.symm, by simp only [← hb, List.append_assoc]⟩

theorem joinDelimiter_proven : JoinDelimiter := by
  intro d buf n t q b n' h1 h2 h
  obtain ⟨body, _, q2, _, hn, hb⟩ := joinAppend_ok h
  have hw : cIntWrap (n + 1) = n + 1 := by
    unfold cIntWrap
    omega
  refine ⟨hn.trans hw, fun h3 => ?_, fun h3 => ?_⟩
  · have hp : n > 0 := by omega
    rw [hb, if_pos hp]
    simp only [List.append_assoc]
    rw [← List.append_assoc buf [d.delimiter]]
    exact List.take_left' (by simp)
  · have hp : ¬(n > 0) := by omega
    rw [hb, if_neg hp]
    simp only [List.append_nil, List.append_assoc]
    exact List.take_left' rfl

end PyLean.TextLibs.Csv
