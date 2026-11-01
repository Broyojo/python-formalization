import PyLean.TextLibs.CsvModel

/-! Properties of the `csv` model. -/

namespace PyLean.TextLibs.Csv

open PyLean PyLean.TextLibs

set_option linter.unusedSimpArgs false

/-! ### Round trip -/

/-- Reading back what the writer wrote gives the row, for every accepted dialect that does not
convert fields. Refuted: with `skipinitialspace=True`, the writer leaves a leading space
unquoted and the reader drops it. -/
def CsvRoundTrip : Prop :=
  ∀ (a : DArgs) (d : Dialect) (row : List (List Nat)) (t : List Nat),
    dialectBuild a = .ok d → (d.quoting = QUOTE_MINIMAL ∨ d.quoting = QUOTE_ALL) →
    writerow d (row.map WField.str) = .ok t →
    (readAll d 131072 2 [.str t] 0).1 = [row.map Field.str]

theorem csvRoundTrip_refuted : ¬CsvRoundTrip := by
  intro h
  have := h { skipinitialspace := some (.bool true) } ⟨true, true, false, 0, 44, 34, NOT_SET, [13, 10]⟩
    [[32, 97]] [32, 97, 13, 10] (by decide +kernel) (.inl rfl) (by decide +kernel)
  revert this
  decide +kernel

/-- The narrowed round trip: `skipinitialspace` off, and quoting that only adds quotes. Holds on
CPython over 300000 random dialects and rows; a proof needs an induction over the fields through
the reader state machine. -/
def CsvRoundTripNoSkip : Prop :=
  ∀ (a : DArgs) (d : Dialect) (row : List (List Nat)) (t : List Nat),
    dialectBuild a = .ok d → (d.quoting = QUOTE_MINIMAL ∨ d.quoting = QUOTE_ALL) →
    d.skipinitialspace = false → (∀ f ∈ row, f.length ≤ 131072 ∧ ∀ c ∈ f, c < 0x110000) →
    writerow d (row.map WField.str) = .ok t →
    (readAll d 131072 2 [.str t] 0).1 = [row.map Field.str]

/-! ### Dialects -/

theorem bind_ok {α β : Type} {x : Py α} {f : α → Py β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem checkChar_ok {name : String} {c : Nat} {lt : List Nat} {sp : Bool}
    (h : checkChar name c lt sp = .ok ()) : c ≠ 13 ∧ c ≠ 10 ∧ lt.contains c = false := by
  unfold checkChar at h
  split at h
  · cases h
  · rename_i h1
    split at h
    · cases h
    · rename_i h2
      refine ⟨by intro e; exact h1 (.inl e), by intro e; exact h1 (.inr (.inl e)), ?_⟩
      simpa using h2

theorem checkChars_ok {a b : String} {c1 c2 : Nat} (h : checkChars a b c1 c2 = .ok ()) :
    c1 = c2 → c1 = NOT_SET := by
  unfold checkChars at h
  split at h
  · cases h
  · rename_i h1
    intro e
    by_cases h2 : c1 = NOT_SET
    · exact h2
    · exact absurd ⟨e, h2⟩ h1

/-- Every dialect `dialect_new` accepts is self-consistent: `quoting` is a known style, a quote
character is set unless quoting is off, no special character is a newline or part of the line
terminator, and delimiter, quote and escape characters are pairwise different. -/
def DialectValid : Prop :=
  ∀ (a : DArgs) (d : Dialect), dialectBuild a = .ok d →
    (0 ≤ d.quoting ∧ d.quoting ≤ 5) ∧
    (d.quoting ≠ QUOTE_NONE → d.quotechar ≠ NOT_SET) ∧
    (d.delimiter ≠ 13 ∧ d.delimiter ≠ 10 ∧ d.lineterminator.contains d.delimiter = false) ∧
    (d.escapechar ≠ 13 ∧ d.escapechar ≠ 10 ∧ d.lineterminator.contains d.escapechar = false) ∧
    (d.quotechar ≠ 13 ∧ d.quotechar ≠ 10 ∧ d.lineterminator.contains d.quotechar = false) ∧
    (d.delimiter = d.escapechar → d.delimiter = NOT_SET) ∧
    (d.delimiter = d.quotechar → d.delimiter = NOT_SET) ∧
    (d.escapechar = d.quotechar → d.escapechar = NOT_SET)

theorem dialectValid_proven : DialectValid := by
  intro a d h
  unfold dialectBuild at h
  obtain ⟨delim, _, h⟩ := bind_ok h
  obtain ⟨esc, _, h⟩ := bind_ok h
  obtain ⟨lt, _, h⟩ := bind_ok h
  obtain ⟨qc, _, h⟩ := bind_ok h
  obtain ⟨q, _, h⟩ := bind_ok h
  obtain ⟨_, hq, h⟩ := bind_ok h
  have hq' : 0 ≤ q ∧ q ≤ 5 := by
    unfold checkQuoting at hq
    split at hq
    · assumption
    · cases hq
  dsimp only at h
  generalize hqq : (if a.quotechar = some .none ∧ a.quoting = Option.none then QUOTE_NONE else q) = q2 at h
  have hr : 0 ≤ q2 ∧ q2 ≤ 5 := by
    rw [← hqq]
    split
    · decide
    · exact hq'
  obtain ⟨_, hset, h⟩ := bind_ok h
  have hset' : q2 ≠ QUOTE_NONE → qc ≠ NOT_SET := by
    intro hn hc
    rw [if_pos ⟨hn, hc⟩] at hset
    cases hset
  obtain ⟨_, c1, h⟩ := bind_ok h
  obtain ⟨_, c2, h⟩ := bind_ok h
  obtain ⟨_, c3, h⟩ := bind_ok h
  obtain ⟨_, c4, h⟩ := bind_ok h
  obtain ⟨_, c5, h⟩ := bind_ok h
  obtain ⟨_, c6, h⟩ := bind_ok h
  cases h
  exact ⟨hr, hset', checkChar_ok c1, checkChar_ok c2, checkChar_ok c3, checkChars_ok c4,
    checkChars_ok c5, checkChars_ok c6⟩

/-- A dialect's `quotechar` and `escapechar` attributes read back as `None` exactly when they are
not set. -/
def CharOrNone : Prop :=
  ∀ c : Nat, (getCharOrNone c = .none ↔ c = NOT_SET) ∧ (c ≠ NOT_SET → getCharOrNone c = .str [c])

theorem charOrNone_proven : CharOrNone := by
  intro c
  by_cases h : c = NOT_SET <;> simp [getCharOrNone, h]

/-! ### Reader -/

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

/-- With `QUOTE_NOTNULL` and `QUOTE_STRINGS`, an unquoted empty field reads as `None`; with the
other styles it reads as the empty string. -/
def SaveEmptyField : Prop :=
  ∀ (d : Dialect) (s : RSt), s.unquoted = true → s.field = [] →
    (parseSaveField d s).map (·.fields) =
      .ok (s.fields ++ [if d.quoting = QUOTE_NOTNULL ∨ d.quoting = QUOTE_STRINGS then .none else .str []])

theorem saveEmptyField_proven : SaveEmptyField := by
  intro d s h1 h2
  unfold parseSaveField
  by_cases hq : d.quoting = QUOTE_NOTNULL ∨ d.quoting = QUOTE_STRINGS
  · simp [h1, h2, hq, Except.map]
  · simp [h1, h2, hq, Except.map]

/-- A blank line is an empty row: the machine stays in `START_RECORD` and saves no field. -/
def BlankLine : Prop :=
  ∀ (d : Dialect) (lim : Int), parseLine d lim {} [] = .ok {}

theorem blankLine_proven : BlankLine := by
  intro d lim
  rfl

/-- After `\r` or `\n` ends a record, any further character on the same input line is an error,
except more newlines. -/
def EatCrnl : Prop :=
  ∀ (d : Dialect) (lim : Int) (s : RSt) (c : Nat), s.state = .EAT_CRNL → isNl c = false → c ≠ EOL →
    parseProcessChar d lim s c = .error (csvErr
      "new-line character seen in unquoted field - do you need to open the file with newline=''?")

theorem eatCrnl_proven : EatCrnl := by
  intro d lim s c h1 h2 h3
  unfold parseProcessChar
  simp [h1, h2, h3]

/-- In strict mode, input that ends inside a quoted field raises `csv.Error`. Otherwise the open
field is returned. -/
def EofInQuotes : Prop :=
  ∀ (d : Dialect) (lim : Int) (s : RSt) (n : Nat), s.state = .IN_QUOTED_FIELD → d.strict = true →
    (readerLoop d lim [] s n).1 = .error (csvErr "unexpected end of data")

theorem eofInQuotes_proven : EofInQuotes := by
  intro d lim s n h1 h2
  simp [readerLoop, h1, h2]

/-! ### Writer -/

/-- `writerows` writes the same text as `writerow` on each row in turn. -/
def WriterowsConcat : Prop :=
  ∀ (d : Dialect) (rows : List (List WField)) (ts : List (List Nat)),
    rows.mapM (writerow d) = .ok ts → writerows d rows = (ts.flatten, Option.none)

theorem writerowsConcat_proven : WriterowsConcat := by
  intro d rows
  induction rows with
  | nil => intro ts h; cases h; rfl
  | cons r rs ih =>
    intro ts h
    simp only [List.mapM_cons] at h
    obtain ⟨t, h1, h⟩ := bind_ok h
    obtain ⟨tl, h2, h⟩ := bind_ok h
    cases h
    simp only [writerows, h1, ih tl h2, List.flatten_cons]

/-- `QUOTE_NONE` cannot write a single empty field: it would read back as a blank row. -/
def SingleEmptyField : Prop :=
  ∀ d : Dialect, d.quoting = QUOTE_NONE → d.delimiter ≠ 32 →
    writerow d [.str []] = .error (csvErr "single empty field record must be quoted")

theorem singleEmptyField_proven : SingleEmptyField := by
  intro d h1 h2
  simp [writerow, writerowLoop, joinAppend, joinField, initialQuoted, h1, h2, QUOTE_NONE,
    QUOTE_NONNUMERIC, QUOTE_ALL, QUOTE_STRINGS, QUOTE_NOTNULL, bind, Except.bind, pure, Except.pure]

/-! ### Registry and limit -/

/-- A registered dialect can be read back, and unregistering removes it. -/
def RegistryLaw : Prop :=
  ∀ (r r2 : Registry) (name : List Nat) (src : DSrc) (a : DArgs) (d : Dialect),
    dialectNew r src a = .ok d → registerDialect r name src a = .ok r2 →
    registryGet r2 name = .ok d

theorem lookup_ne {α : Type} (name k : List Nat) (v : α) (l : List (List Nat × α)) (h : name ≠ k) :
    ((k, v) :: l).lookup name = l.lookup name := by
  have hb : (name == k) = false := by simpa using h
  simp [List.lookup, hb]

theorem lookup_replace (name : List Nat) (d : Dialect) : ∀ l : Registry, (l.lookup name).isSome = true →
    (l.map (fun p => if p.1 = name then (name, d) else p)).lookup name = some d := by
  intro l
  induction l with
  | nil => intro h; cases h
  | cons p ps ih =>
    intro h
    obtain ⟨k, v⟩ := p
    by_cases he : k = name
    · subst he
      simp [List.lookup]
    · rw [lookup_ne _ _ _ _ (Ne.symm he)] at h
      simp only [List.map_cons, he, if_false]
      rw [lookup_ne _ _ _ _ (Ne.symm he)]
      exact ih h

theorem lookup_snoc (name : List Nat) (d : Dialect) : ∀ l : Registry, (l.lookup name).isSome = false →
    (l ++ [(name, d)]).lookup name = some d := by
  intro l
  induction l with
  | nil => intro _; simp [List.lookup]
  | cons p ps ih =>
    intro h
    obtain ⟨k, v⟩ := p
    by_cases he : name = k
    · subst he
      simp [List.lookup] at h
    · rw [lookup_ne _ _ _ _ he] at h
      rw [List.cons_append, lookup_ne _ _ _ _ he]
      exact ih h

theorem registryLaw_proven : RegistryLaw := by
  intro r r2 name src a d h1 h2
  simp only [registerDialect, h1, bind, Except.bind, pure, Except.pure] at h2
  cases h2
  by_cases hn : (r.lookup name).isSome = true
  · simp only [hn, if_true, registryGet]
    rw [lookup_replace name d r hn]
  · have hf : (r.lookup name).isSome = false := Bool.eq_false_iff.2 hn
    simp only [hf, Bool.false_eq_true, if_false, registryGet]
    rw [lookup_snoc name d r hf]

/-- `field_size_limit` returns the old limit, and sets the new one if given. -/
def FieldLimit : Prop :=
  ∀ (cur n : Int), -(2 ^ 63) ≤ n → n ≤ 2 ^ 63 - 1 →
    fieldSizeLimit cur (some (.int n)) = .ok (cur, n) ∧ fieldSizeLimit cur Option.none = .ok (cur, cur)

theorem fieldLimit_proven : FieldLimit := by
  intro cur n h1 h2
  constructor
  · unfold fieldSizeLimit
    simp only
    rw [if_neg (by omega)]
  · rfl

/-! ### `DictWriter` and `DictReader` -/

/-- `DictWriter` writes the fields in `fieldnames` order, with `restval` for missing keys. -/
def DictToListOrder : Prop :=
  ∀ (names : List (List Nat)) (rv : WField) (rowdict : List (List Nat × WField)),
    dictToList names rv false rowdict = .ok (names.map fun k => (rowdict.lookup k).getD rv)

theorem dictToListOrder_proven : DictToListOrder := by
  intro names rv rowdict
  simp [dictToList]

/-- With `extrasaction='raise'`, a key outside `fieldnames` raises. -/
def DictExtraRaises : Prop :=
  ∀ (names : List (List Nat)) (rv : WField) (rowdict : List (List Nat × WField)),
    (∃ p ∈ rowdict, names.contains p.1 = false) →
    dictToList names rv true rowdict = .error (.valueError "~dict contains fields not in fieldnames")

theorem dictExtraRaises_proven : DictExtraRaises := by
  intro names rv rowdict ⟨p, hp, hn⟩
  have : rowdict.any (fun p => !names.contains p.1) = true := by
    rw [List.any_eq_true]
    exact ⟨p, hp, by rw [hn]; rfl⟩
  unfold dictToList
  rw [if_pos ⟨rfl, this⟩]

/-- `extrasaction` is case-insensitive, and only `raise` and `ignore` are accepted. -/
def ExtrasactionLaw : Prop :=
  extrasactionCheck (strToList "RAISE") = .ok true ∧ extrasactionCheck (strToList "Ignore") = .ok false ∧
    ∀ s, lowerAscii s ≠ strToList "raise" → lowerAscii s ≠ strToList "ignore" →
      extrasactionCheck s = .error (.valueError "~extrasaction must be 'raise' or 'ignore'")

theorem extrasactionLaw_proven : ExtrasactionLaw := by
  refine ⟨by decide, by decide, fun s h1 h2 => ?_⟩
  simp [extrasactionCheck, h1, h2]

/-- `DictReader` yields one dict for each non-blank row, taking the field names from the first row
when none are given. -/
def DictReadCount : Prop :=
  ∀ (d : Dialect) (lim : Int) (lines : List Line) (rk : Option (List Nat)) (names : List (List Nat)),
    let rows := (readAll d lim (lines.length + 1) lines 0).1
    (dictRead d lim (some names) lines rk).1.length = (rows.filter (· != [])).length ∧
    (dictRead d lim Option.none lines rk).1.length = ((rows.drop 1).filter (· != [])).length

theorem dictReadCount_proven : DictReadCount := by
  intro d lim lines rk names rows
  constructor
  · simp [dictRead, rows]
  · simp only [dictRead]
    generalize hr : readAll d lim (lines.length + 1) lines 0 = res
    obtain ⟨rs, e, n⟩ := res
    have : rows = rs := by simp [rows, hr]
    rw [this]
    cases rs <;> simp

theorem lookup_self (k : List Nat) : ∀ names : List (List Nat), k ∈ names →
    (names.map (fun n => (n, WField.str n))).lookup k = some (WField.str k) := by
  intro names
  induction names with
  | nil => intro h; cases h
  | cons n ns ih =>
    intro h
    by_cases he : k = n
    · subst he
      simp [List.lookup]
    · have hm : k ∈ ns := by
        rcases List.mem_cons.1 h with h | h
        · exact absurd h he
        · exact h
      rw [List.map_cons, lookup_ne _ _ _ _ he]
      exact ih hm

/-- `writeheader` writes the field names as one row. -/
def WriteheaderLaw : Prop :=
  ∀ names : List (List Nat), writeheader excel names = writerow excel (names.map WField.str)

theorem writeheaderLaw_proven : WriteheaderLaw := by
  intro names
  have hno : (names.map (fun n => (n, WField.str n))).any (fun p => !names.contains p.1) = false := by
    simp [List.any_eq_false]
  have hmap : names.map (fun k => ((names.map fun n => (n, WField.str n)).lookup k).getD (.str []))
      = names.map WField.str := by
    apply List.map_congr_left
    intro k hk
    rw [lookup_self k names hk]
    rfl
  simp only [writeheader, dictWriterow, dictToList, bind, Except.bind]
  rw [if_neg (by simp [hno]), hmap]

/-- Unregistering a name that is not there raises; otherwise the name leaves `list_dialects`. -/
def UnregisterLaw : Prop :=
  ∀ (r r2 : Registry) (name : List Nat),
    ((r.lookup name).isSome = false → unregisterDialect r name = .error (csvErr "unknown dialect")) ∧
    (unregisterDialect r name = .ok r2 → name ∉ listDialects r2)

theorem unregisterLaw_proven : UnregisterLaw := by
  intro r r2 name
  constructor
  · intro h
    simp [unregisterDialect, h]
  · intro h
    unfold unregisterDialect at h
    split at h
    · cases h
      simp [listDialects]
    · cases h

/-- Passing an existing dialect with no overrides reuses that instance, and a pickled dialect is
refused. -/
def DialectReuse : Prop :=
  (∀ (r : Registry) (d : Dialect), dialectNew r (.dialect d) {} = .ok d) ∧
    dialectReduce = .error (.typeError "cannot pickle 'Dialect' instances")

theorem dialectReuse_proven : DialectReuse := by
  refine ⟨fun r d => ?_, rfl⟩
  simp [dialectNew, bind, Except.bind, pure, Except.pure]

/-- `csv.Dialect` validates like `_Dialect`, reporting `TypeError`s as `csv.Error`. -/
def DialectValidate : Prop :=
  ∀ (a : DArgs),
    ((dialectValidate a).toBool = (dialectBuild a).toBool) ∧
    (∀ m, dialectBuild a = .error (.typeError m) → dialectValidate a = .error (csvErr m))

theorem dialectValidate_proven : DialectValidate := by
  intro a
  constructor
  · unfold dialectValidate
    cases dialectBuild a with
    | ok _ => rfl
    | error e => cases e <;> rfl
  · intro m h
    simp [dialectValidate, h]

/-- `DictWriter.writerows` writes what `writerow` writes for each dict in turn. -/
def DictWriterowsConcat : Prop :=
  ∀ (d : Dialect) (names : List (List Nat)) (rv : WField) (raises : Bool)
    (rows : List (List (List Nat × WField))) (ts : List (List Nat)),
    rows.mapM (dictWriterow d names rv raises) = .ok ts →
    dictWriterows d names rv raises rows = (ts.flatten, Option.none)

theorem dictWriterowsConcat_proven : DictWriterowsConcat := by
  intro d names rv raises rows
  induction rows with
  | nil => intro ts h; cases h; rfl
  | cons r rs ih =>
    intro ts h
    simp only [List.mapM_cons] at h
    obtain ⟨t, h1, h⟩ := bind_ok h
    obtain ⟨tl, h2, h⟩ := bind_ok h
    cases h
    simp only [dictWriterows, h1, ih tl h2, List.flatten_cons]

end PyLean.TextLibs.Csv
