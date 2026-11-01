import PyLean.TextLibs.CsvModel

/-!
Properties of the `csv` model: dialects, the registry and the field limit. Each statement says
exactly what the function does on all inputs, failure branches included, so that it depends on the
body. `Obj.str` holds code points; where that matters the hypothesis says so and is a type
invariant of `str`.
-/

namespace PyLean.TextLibs.Csv

open PyLean PyLean.TextLibs

set_option linter.unusedSimpArgs false

theorem bind_ok {α β : Type} {x : Py α} {f : α → Py β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-! ### The conversions -/

/-- `_set_char` takes the default for a missing argument and otherwise exactly a string of one
character: a subclass of `str` counts, and nothing else does. -/
def SetCharLaw : Prop :=
  ∀ (name : String) (src : Option Obj) (dflt v : Nat),
    setChar name src dflt = .ok v ↔
      (src = Option.none ∧ v = dflt) ∨ ∃ o, src = some o ∧ o.asStr = some [v]

theorem setCharLaw_proven : SetCharLaw := by
  intro name src dflt v
  cases src with
  | none => simp [setChar, eq_comm]
  | some o =>
    simp only [setChar, reduceCtorEq, false_and, false_or, Option.some.injEq, exists_eq_left']
    cases h : o.asStr with
    | none => simp
    | some l =>
      match l with
      | [] => simp
      | [c] => simp
      | a :: b :: t => simp

/-- `_set_char_or_none` also takes `None`, as `NOT_SET`. -/
def SetCharOrNoneLaw : Prop :=
  ∀ (name : String) (src : Option Obj) (dflt v : Nat),
    setCharOrNone name src dflt = .ok v ↔
      (src = Option.none ∧ v = dflt) ∨ (src = some .none ∧ v = NOT_SET) ∨
        ∃ o, src = some o ∧ o.asStr = some [v]

theorem setCharOrNoneLaw_proven : SetCharOrNoneLaw := by
  intro name src dflt v
  cases src with
  | none => simp [setCharOrNone, eq_comm]
  | some o =>
    cases o with
    | none => simp [setCharOrNone, Obj.asStr, eq_comm]
    | str s =>
      simp only [setCharOrNone, Obj.asStr, reduceCtorEq, false_and, false_or, Option.some.injEq,
        exists_eq_left']
      match s with
      | [] => simp
      | [c] => simp
      | a :: b :: t => simp
    | strSub t s k =>
      simp only [setCharOrNone, Obj.asStr, reduceCtorEq, false_and, false_or, Option.some.injEq,
        exists_eq_left']
      match s with
      | [] => simp
      | [c] => simp
      | a :: b :: t => simp
    | int n => simp [setCharOrNone, Obj.asStr]
    | bool b => simp [setCharOrNone, Obj.asStr]
    | dialect t d => simp [setCharOrNone, Obj.asStr]
    | other t a b c d e f => simp [setCharOrNone, Obj.asStr]
    | func c => simp [setCharOrNone, Obj.asStr]

/-- `_set_str` takes the default for a missing argument and otherwise exactly a `str` or a
subclass; the empty string is allowed. -/
def SetStrLaw : Prop :=
  ∀ (name : String) (src : Option Obj) (dflt v : List Nat),
    setStr name src dflt = .ok v ↔
      (src = Option.none ∧ v = dflt) ∨ ∃ o, src = some o ∧ o.asStr = some v

theorem setStrLaw_proven : SetStrLaw := by
  intro name src dflt v
  cases src with
  | none => simp [setStr, eq_comm]
  | some o =>
    simp only [setStr, reduceCtorEq, false_and, false_or, Option.some.injEq, exists_eq_left']
    cases h : o.asStr with
    | none => simp
    | some l => simp

/-- `_set_int` takes the default for a missing argument and otherwise exactly an `int` that fits a C
`int`: a `bool` is refused, because `PyLong_CheckExact` is false for it, and too large a value is an
`OverflowError` rather than a `TypeError`. -/
def SetIntLaw : Prop :=
  ∀ (name : String) (src : Option Obj) (dflt v : Int),
    (setInt name src dflt = .ok v ↔
      (src = Option.none ∧ v = dflt) ∨
        (src = some (.int v) ∧ -(2 ^ 31) ≤ v ∧ v ≤ 2 ^ 31 - 1)) ∧
    ∀ n : Int, (n < -(2 ^ 31) ∨ n > 2 ^ 31 - 1) →
      setInt name (some (.int n)) dflt =
        .error (.overflowError "Python int too large to convert to C int")

theorem setIntLaw_proven : SetIntLaw := by
  intro name src dflt v
  constructor
  · cases src with
    | none => simp [setInt, eq_comm]
    | some o =>
      cases o with
      | int n =>
        simp only [setInt]
        by_cases h : n < -(2 ^ 31) ∨ n > 2 ^ 31 - 1
        · rw [if_pos h]
          constructor
          · intro e; cases e
          · rintro (⟨h1, _⟩ | ⟨h1, h2, h3⟩)
            · cases h1
            · have : n = v := by simpa using h1
              omega
        · rw [if_neg h]
          constructor
          · intro e
            have hv : n = v := by simpa using e
            subst hv
            exact .inr ⟨rfl, by omega, by omega⟩
          · rintro (⟨h1, _⟩ | ⟨h1, _⟩)
            · cases h1
            · have : n = v := by simpa using h1
              rw [this]
      | none => simp [setInt]
      | str s => simp [setInt]
      | strSub t s k => simp [setInt]
      | bool b => simp [setInt]
      | dialect t d => simp [setInt]
      | other t a b c d e f => simp [setInt]
      | func c => simp [setInt]
  · intro n h
    simp only [setInt]
    rw [if_pos h]

/-! ### What `dialect_new` builds -/

/-- What a successful `dialectBuild` establishes, step by step. -/
structure BuildFacts (a : DArgs) (d : Dialect) : Prop where
  delim : setChar "delimiter" a.delimiter 44 = .ok d.delimiter
  dq : setBool a.doublequote true = .ok d.doublequote
  esc : setCharOrNone "escapechar" a.escapechar NOT_SET = .ok d.escapechar
  lt : setStr "lineterminator" a.lineterminator [13, 10] = .ok d.lineterminator
  qc : setCharOrNone "quotechar" a.quotechar 34 = .ok d.quotechar
  skip : setBool a.skipinitialspace false = .ok d.skipinitialspace
  strict : setBool a.strict false = .ok d.strict
  q0 : ∃ q, setInt "quoting" a.quoting QUOTE_MINIMAL = .ok q ∧ checkQuoting q = .ok () ∧
    d.quoting = if isNoneArg a.quotechar = true ∧ a.quoting.isNone = true then QUOTE_NONE else q
  set : d.quoting ≠ QUOTE_NONE → d.quotechar ≠ NOT_SET
  c1 : checkChar "delimiter" d.delimiter d.lineterminator true = .ok ()
  c2 : checkChar "escapechar" d.escapechar d.lineterminator (!d.skipinitialspace) = .ok ()
  c3 : checkChar "quotechar" d.quotechar d.lineterminator (!d.skipinitialspace) = .ok ()
  c4 : checkChars "delimiter" "escapechar" d.delimiter d.escapechar = .ok ()
  c5 : checkChars "delimiter" "quotechar" d.delimiter d.quotechar = .ok ()
  c6 : checkChars "escapechar" "quotechar" d.escapechar d.quotechar = .ok ()

theorem build_ok {a : DArgs} {d : Dialect} (h : dialectBuild a = .ok d) : BuildFacts a d := by
  unfold dialectBuild at h
  obtain ⟨delim, h1, h⟩ := bind_ok h
  obtain ⟨dq, h2, h⟩ := bind_ok h
  obtain ⟨esc, h3, h⟩ := bind_ok h
  obtain ⟨lt, h4, h⟩ := bind_ok h
  obtain ⟨qc, h5, h⟩ := bind_ok h
  obtain ⟨q, h6, h⟩ := bind_ok h
  obtain ⟨skip, h7, h⟩ := bind_ok h
  obtain ⟨strict, h8, h⟩ := bind_ok h
  obtain ⟨_, h9, h⟩ := bind_ok h
  dsimp only at h
  generalize hqq : (if isNoneArg a.quotechar = true ∧ a.quoting.isNone = true then QUOTE_NONE else q) = q2 at h
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
  exact ⟨h1, h2, h3, h4, h5, h7, h8, ⟨q, h6, h9, hqq.symm⟩, hset', c1, c2, c3, c4, c5, c6⟩

theorem checkChar_ok {name : String} {c : Nat} {lt : List Nat} {sp : Bool}
    (h : checkChar name c lt sp = .ok ()) :
    c ≠ 13 ∧ c ≠ 10 ∧ (c = 32 → sp = true) ∧ lt.contains c = false := by
  unfold checkChar at h
  split at h
  · cases h
  · rename_i h1
    split at h
    · cases h
    · rename_i h2
      refine ⟨by intro e; exact h1 (.inl e), by intro e; exact h1 (.inr (.inl e)), ?_, ?_⟩
      · intro e
        cases sp with
        | true => rfl
        | false => exact absurd (.inr (.inr ⟨e, rfl⟩)) h1
      · simpa using h2

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

theorem checkQuoting_ok {q : Int} (h : checkQuoting q = .ok ()) : 0 ≤ q ∧ q ≤ 5 := by
  unfold checkQuoting at h
  split at h
  · assumption
  · cases h

/-- Every dialect that `dialect_new` accepts is self-consistent: `quoting` is a known style, a quote
character is set unless quoting is off, no special character is a newline or in the line terminator,
a space is neither escape nor quote character under `skipinitialspace`, and delimiter, quote and
escape characters are pairwise different. -/
def DialectValid : Prop :=
  ∀ (a : DArgs) (d : Dialect), dialectBuild a = .ok d →
    (0 ≤ d.quoting ∧ d.quoting ≤ 5) ∧
    (d.quoting ≠ QUOTE_NONE → d.quotechar ≠ NOT_SET) ∧
    (d.delimiter ≠ 13 ∧ d.delimiter ≠ 10 ∧ d.lineterminator.contains d.delimiter = false) ∧
    (d.escapechar ≠ 13 ∧ d.escapechar ≠ 10 ∧ d.lineterminator.contains d.escapechar = false) ∧
    (d.quotechar ≠ 13 ∧ d.quotechar ≠ 10 ∧ d.lineterminator.contains d.quotechar = false) ∧
    (d.skipinitialspace = true → d.escapechar ≠ 32 ∧ d.quotechar ≠ 32) ∧
    (d.delimiter = d.escapechar → d.delimiter = NOT_SET) ∧
    (d.delimiter = d.quotechar → d.delimiter = NOT_SET) ∧
    (d.escapechar = d.quotechar → d.escapechar = NOT_SET)

theorem dialectValid_proven : DialectValid := by
  intro a d h
  have f := build_ok h
  obtain ⟨q, _, hq, hd⟩ := f.q0
  have hr : 0 ≤ d.quoting ∧ d.quoting ≤ 5 := by
    rw [hd]
    split
    · decide
    · exact checkQuoting_ok hq
  have c1 := checkChar_ok f.c1
  have c2 := checkChar_ok f.c2
  have c3 := checkChar_ok f.c3
  refine ⟨hr, f.set, ⟨c1.1, c1.2.1, c1.2.2.2⟩, ⟨c2.1, c2.2.1, c2.2.2.2⟩, ⟨c3.1, c3.2.1, c3.2.2.2⟩,
    fun hs => ⟨fun e => ?_, fun e => ?_⟩, checkChars_ok f.c4, checkChars_ok f.c5, checkChars_ok f.c6⟩
  · have := c2.2.2.1 e
    simp [hs] at this
  · have := c3.2.2.1 e
    simp [hs] at this

/-- A dialect stores what it was given: each attribute is the converted argument, or the default
when the argument was missing. The boolean attributes are the argument's truth value, and `quoting`
is `QUOTE_NONE` when `quotechar=None` was given without `quoting`. -/
def DialectStores : Prop :=
  ∀ (a : DArgs) (d : Dialect), dialectBuild a = .ok d →
    ((a.delimiter = Option.none ∧ d.delimiter = 44) ∨
      ∃ o, a.delimiter = some o ∧ o.asStr = some [d.delimiter]) ∧
    ((a.escapechar = Option.none ∧ d.escapechar = NOT_SET) ∨
      (a.escapechar = some .none ∧ d.escapechar = NOT_SET) ∨
      ∃ o, a.escapechar = some o ∧ o.asStr = some [d.escapechar]) ∧
    ((a.quotechar = Option.none ∧ d.quotechar = 34) ∨
      (a.quotechar = some .none ∧ d.quotechar = NOT_SET) ∨
      ∃ o, a.quotechar = some o ∧ o.asStr = some [d.quotechar]) ∧
    ((a.lineterminator = Option.none ∧ d.lineterminator = [13, 10]) ∨
      ∃ o, a.lineterminator = some o ∧ o.asStr = some d.lineterminator) ∧
    (∀ o, a.doublequote = some o → o.isTrue = .ok d.doublequote) ∧
    (a.doublequote = Option.none → d.doublequote = true) ∧
    (∀ o, a.skipinitialspace = some o → o.isTrue = .ok d.skipinitialspace) ∧
    (a.skipinitialspace = Option.none → d.skipinitialspace = false) ∧
    (∀ o, a.strict = some o → o.isTrue = .ok d.strict) ∧
    (a.strict = Option.none → d.strict = false) ∧
    (isNoneArg a.quotechar = true → a.quoting = Option.none → d.quoting = QUOTE_NONE) ∧
    (a.quoting = Option.none → isNoneArg a.quotechar = false → d.quoting = QUOTE_MINIMAL)

theorem dialectStores_proven : DialectStores := by
  intro a d h
  have f := build_ok h
  obtain ⟨q, hq, _, hd⟩ := f.q0
  refine ⟨(setCharLaw_proven _ _ _ _).1 f.delim, (setCharOrNoneLaw_proven _ _ _ _).1 f.esc,
    (setCharOrNoneLaw_proven _ _ _ _).1 f.qc, (setStrLaw_proven _ _ _ _).1 f.lt, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro o e
    have := f.dq
    rw [e] at this
    exact this
  · intro e
    have := f.dq
    rw [e] at this
    simpa [setBool] using this.symm
  · intro o e
    have := f.skip
    rw [e] at this
    exact this
  · intro e
    have := f.skip
    rw [e] at this
    simpa [setBool] using this.symm
  · intro o e
    have := f.strict
    rw [e] at this
    exact this
  · intro e
    have := f.strict
    rw [e] at this
    simpa [setBool] using this.symm
  · intro h1 h2
    rw [hd, if_pos (by simp [h1, h2])]
  · intro h1 h2
    have hq0 : q = QUOTE_MINIMAL := by
      rw [h1] at hq
      simpa [setInt, eq_comm] using hq
    rw [hd, if_neg (by simp [h2]), hq0]

/-- A raising `__bool__` on `doublequote` raises out of `dialect_new`, once `delimiter`, which is
converted first, has been accepted. It is not treated as false. The same goes for `strict`, the last
conversion, after all the others. -/
def DialectBoolRaises : Prop :=
  (∀ (a : DArgs) (o : Obj) (e : PyExc) (c : Nat),
    setChar "delimiter" a.delimiter 44 = .ok c → a.doublequote = some o → o.isTrue = .error e →
    dialectBuild a = .error e) ∧
  ∀ (a : DArgs) (d0 : Dialect) (o : Obj) (e : PyExc),
    dialectBuild { a with strict := Option.none } = .ok d0 → a.strict = some o → o.isTrue = .error e →
    dialectBuild a = .error e

theorem dialectBoolRaises_proven : DialectBoolRaises := by
  constructor
  · intro a o e c h1 h2 h3
    simp [dialectBuild, h1, h2, h3, setBool, bind, Except.bind]
  · intro a d0 o e h1 h2 h3
    have f := build_ok h1
    obtain ⟨q, hq, _, _⟩ := f.q0
    have hd : setChar "delimiter" a.delimiter 44 = .ok d0.delimiter := f.delim
    have hb : setBool a.doublequote true = .ok d0.doublequote := f.dq
    have he : setCharOrNone "escapechar" a.escapechar NOT_SET = .ok d0.escapechar := f.esc
    have hl : setStr "lineterminator" a.lineterminator [13, 10] = .ok d0.lineterminator := f.lt
    have hc : setCharOrNone "quotechar" a.quotechar 34 = .ok d0.quotechar := f.qc
    have hq' : setInt "quoting" a.quoting QUOTE_MINIMAL = .ok q := hq
    have hs : setBool a.skipinitialspace false = .ok d0.skipinitialspace := f.skip
    have hst : setBool a.strict false = .error e := by simp [setBool, h2, h3]
    simp only [dialectBuild, hd, hb, he, hl, hc, hq', hs, hst, bind, Except.bind]

theorem setCharOrNone_get (name : String) (c dflt : Nat) :
    setCharOrNone name (some (getCharOrNone c)) dflt = .ok c := by
  unfold getCharOrNone
  by_cases h : c = NOT_SET
  · simp [h, setCharOrNone]
  · simp [h, setCharOrNone, Obj.asStr]

theorem attrs_of_dialect (t : TyName) (d : Dialect) :
    dialectAttrs (.dialect t d) {} =
      { dialect := Option.none
        delimiter := some (getCharOrNone d.delimiter)
        doublequote := some (.bool d.doublequote)
        escapechar := some (getCharOrNone d.escapechar)
        lineterminator := some (.str d.lineterminator)
        quotechar := some (getCharOrNone d.quotechar)
        quoting := some (.int d.quoting)
        skipinitialspace := some (.bool d.skipinitialspace)
        strict := some (.bool d.strict) } := rfl

/-- Reading the attributes of a dialect back through its getters and building a new dialect from
them gives the same settings. This is `_csv.Dialect(d, x=...)` with no real override, and it goes
through every getter, every conversion and every check. `d.delimiter` is a character, which is the
type invariant of a `str` of length one: `NOT_SET` is outside the range of code points. -/
def DialectRebuild : Prop :=
  ∀ (a : DArgs) (d : Dialect) (t : TyName), dialectBuild a = .ok d → d.delimiter ≠ NOT_SET →
    dialectBuild (dialectAttrs (.dialect t d) {}) = .ok d

theorem dialectRebuild_proven : DialectRebuild := by
  intro a d t h hn
  have f := build_ok h
  obtain ⟨q, _, hq, hd⟩ := f.q0
  have hr : 0 ≤ d.quoting ∧ d.quoting ≤ 5 := by
    rw [hd]
    split
    · decide
    · exact checkQuoting_ok hq
  rw [attrs_of_dialect]
  have s1 : setChar "delimiter" (some (getCharOrNone d.delimiter)) 44 = .ok d.delimiter := by
    simp [getCharOrNone, hn, setChar, Obj.asStr]
  have s2 := setCharOrNone_get "escapechar" d.escapechar NOT_SET
  have s3 := setCharOrNone_get "quotechar" d.quotechar 34
  have s4 : setInt "quoting" (some (.int d.quoting)) QUOTE_MINIMAL = .ok d.quoting := by
    simp only [setInt]
    rw [if_neg (by omega)]
  have s5 : checkQuoting d.quoting = .ok () := by
    unfold checkQuoting
    rw [if_pos hr]
  have s6 : (if d.quoting ≠ QUOTE_NONE ∧ d.quotechar = NOT_SET then
      (Except.error (.typeError "quotechar must be set if quoting enabled") : Py Unit) else .ok ()) =
      .ok () := by
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact f.set h1 h2
  simp only [dialectBuild, s1, s2, s3, s4, s5, s6, setBool, setStr, Obj.isTrue, Obj.asStr, bind,
    Except.bind, pure, Except.pure, isNoneArg, Option.isNone_some, Bool.false_eq_true, and_false,
    if_false, f.c1, f.c2, f.c3, f.c4, f.c5, f.c6]

/-! ### `dialect_new` and `_call_dialect` -/

theorem parse_one (o : Obj) : parseDialectArgs ⟨[o], []⟩ =
    .ok [some o, Option.none, Option.none, Option.none, Option.none, Option.none, Option.none,
      Option.none, Option.none] := rfl

/-- `dialect_new` on an object that is neither a string nor a `Dialect`: always a new dialect, from
its attributes. -/
theorem new_other (r : Registry) (ty : TyName) (o : Obj) (h1 : o.asStr = Option.none)
    (h2 : ∀ t d, o ≠ .dialect t d) :
    dialectNew r ty ⟨[o], []⟩ =
      Except.bind (dialectBuild (dialectAttrs o { dialect := some o })) fun d => .ok (.fresh ty d) := by
  cases o with
  | str s => cases h1
  | strSub t s k => cases h1
  | dialect t d => exact absurd rfl (h2 t d)
  | none => rfl
  | int n => rfl
  | bool b => rfl
  | other t a b c d e f => rfl
  | func c => rfl

/-- A `Dialect` passed with no overrides is the same object back, by value or through the registry
under its name, which is the "Can we reuse this instance?" branch and what `_call_dialect` hands to
`csv.reader` and `csv.writer`. An object that is not a `Dialect` is never reused, even with no
overrides: `PyObject_TypeCheck` is the first test. -/
def DialectReuse : Prop :=
  (∀ (r : Registry) (ty t : TyName) (d : Dialect),
    dialectNew r ty ⟨[.dialect t d], []⟩ = .ok (.same t d)) ∧
  (∀ (r : Registry) (ty t : TyName) (d : Dialect) (k : List Nat),
    r.lookup k = some (.dialect t d) → dialectNew r ty ⟨[.str k], []⟩ = .ok (.same t d)) ∧
  (∀ (r : Registry) (t : TyName) (d : Dialect),
    callDialect r (some (.dialect t d)) [] = .ok (.same t d)) ∧
  (∀ (r : Registry) (ty : TyName) (o : Obj) (res : DRes),
    o.asStr = Option.none → (∀ t d, o ≠ .dialect t d) → dialectNew r ty ⟨[o], []⟩ = .ok res →
    ∃ t d, res = .fresh t d)

theorem dialectReuse_proven : DialectReuse := by
  refine ⟨fun r ty t d => ?_, fun r ty t d k h => ?_, fun r t d => ?_, fun r ty o res h1 h2 h3 => ?_⟩
  · simp [dialectNew, parse_one, argsOf, Obj.asStr, bind, Except.bind, pure, Except.pure]
  · simp [dialectNew, parse_one, argsOf, Obj.asStr, getDialectFromRegistry, Obj.dictFind, Obj.dictKey,
      h, bind, Except.bind, pure, Except.pure, Functor.map, Except.map]
  · simp [callDialect, dialectNew, parse_one, argsOf, Obj.asStr, bind, Except.bind, pure, Except.pure]
  · rw [new_other r ty o h1 h2] at h3
    cases hb : dialectBuild (dialectAttrs o { dialect := some o }) with
    | error e =>
      rw [hb] at h3
      cases h3
    | ok d =>
      rw [hb] at h3
      cases h3
      exact ⟨_, _, rfl⟩

/-- `DIALECT_GETATTR` clears every failure, not only `AttributeError`, so an object whose attributes
all raise gives the default dialect, and a fresh one. -/
def GetattrCleared : Prop :=
  ∀ (r : Registry) (ty : TyName) (o : Obj),
    o.asStr = Option.none → (∀ t d, o ≠ .dialect t d) → (∀ n, ∃ e, o.getattr n = .error e) →
    dialectNew r ty ⟨[o], []⟩ =
      .ok (.fresh ty ⟨true, false, false, QUOTE_MINIMAL, 44, 34, NOT_SET, [13, 10]⟩)

theorem getattrCleared_proven : GetattrCleared := by
  intro r ty o h1 h2 h3
  have hg : ∀ n, getattrOr o Option.none n = Option.none := by
    intro n
    obtain ⟨e, he⟩ := h3 n
    simp [getattrOr, he]
  have hb : dialectBuild ({ dialect := some o } : DArgs) =
      .ok ⟨true, false, false, QUOTE_MINIMAL, 44, 34, NOT_SET, [13, 10]⟩ := rfl
  have ha : dialectAttrs o ({ dialect := some o } : DArgs) = { dialect := some o } := by
    simp only [dialectAttrs, hg]
  rw [new_other r ty o h1 h2, ha, hb]
  rfl

/-! ### The registry -/

/-- A registered dialect can be read back by name, and it is the object `_call_dialect` made. -/
def RegistryLaw : Prop :=
  ∀ (r r2 : Registry) (name : List Nat) (inst : Option Obj) (kw : List (List Nat × Obj)) (d : DRes),
    callDialect r inst kw = .ok d →
    csvRegisterDialect r ⟨.str name :: inst.toList, kw⟩ = .ok r2 →
    csvGetDialect r2 (.str name) = .ok d.obj

theorem lookup_ne {α : Type} (name k : List Nat) (v : α) (l : List (List Nat × α)) (h : name ≠ k) :
    ((k, v) :: l).lookup name = l.lookup name := by
  have hb : (name == k) = false := by simpa using h
  simp [List.lookup, hb]

theorem lookup_replace (name : List Nat) (d : Obj) : ∀ l : Registry, (l.lookup name).isSome = true →
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

theorem lookup_snoc (name : List Nat) (d : Obj) : ∀ l : Registry, (l.lookup name).isSome = false →
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

theorem registrySet_get (r : Registry) (k : List Nat) (d : Obj) :
    (registrySet r k d).lookup k = some d := by
  unfold registrySet
  by_cases h : (r.lookup k).isSome = true
  · rw [if_pos h]
    exact lookup_replace k d r h
  · rw [if_neg h]
    exact lookup_snoc k d r (Bool.eq_false_iff.2 h)

theorem registryLaw_proven : RegistryLaw := by
  intro r r2 name inst kw d h1 h2
  have hu : unpack12 "register_dialect" (.str name :: inst.toList) = .ok (.str name, inst) := by
    cases inst <;> rfl
  simp only [csvRegisterDialect, hu, Obj.asStr, h1, bind, Except.bind, pure, Except.pure, Obj.dictFind,
    Obj.dictKey] at h2
  by_cases hp : (r.lookup name).isSome = true
  · simp only [hp, if_true] at h2
    cases h2
    simp [csvGetDialect, getDialectFromRegistry, Obj.dictFind, Obj.dictKey, registrySet_get]
  · simp only [hp, if_false] at h2
    cases h2
    have hf := Bool.eq_false_iff.2 hp
    simp [csvGetDialect, getDialectFromRegistry, Obj.dictFind, Obj.dictKey, lookup_snoc name _ r hf]

/-- `register_dialect` checks the name's type before anything about the dialect: a name that is not
a string raises `TypeError` even if the keyword arguments are invalid. A subclass of `str` whose
`__hash__` raises fails at `PyDict_SetItem`, and the dialect it built is not registered. -/
def RegisterNameChecks : Prop :=
  (∀ (r : Registry) (o : Obj) (kw : List (List Nat × Obj)), o.asStr = Option.none →
    csvRegisterDialect r ⟨[o], kw⟩ = .error (.typeError "dialect name must be a string")) ∧
  ∀ (r : Registry) (t : TyName) (s : List Nat) (e : PyExc) (kw : List (List Nat × Obj)) (d : DRes),
    callDialect r Option.none kw = .ok d →
    csvRegisterDialect r ⟨[.strSub t s (.hashRaises e)], kw⟩ =
      .error (dictHashErr (.strSub t s (.hashRaises e)) e)

theorem registerNameChecks_proven : RegisterNameChecks := by
  constructor
  · intro r o kw h
    simp [csvRegisterDialect, unpack12, h, bind, Except.bind]
    rfl
  · intro r t s e kw d h
    simp [csvRegisterDialect, unpack12, h, Obj.asStr, Obj.dictFind, Obj.dictKey, bind, Except.bind]
    rfl

/-- `get_dialect` on every kind of name: a `TypeError` from `__hash__` gains the key's type, any
other failure of `__hash__` or `__eq__` passes through, a key that matches nothing is `csv.Error`,
and an equal key finds the dialect whatever object it is. -/
def GetDialectLaw : Prop :=
  ∀ (r : Registry) (name : Obj),
    (∀ m, name.dictKey = .hashRaises (.typeError m) → csvGetDialect r name =
      .error (.typeError s!"cannot use '{name.ty.full}' as a dict key ({m})")) ∧
    (∀ e, name.dictKey = .eqRaises e → csvGetDialect r name = .error e) ∧
    (name.dictKey = .noMatch → csvGetDialect r name = .error (csvErr "unknown dialect")) ∧
    (∀ k d, name.dictKey = .equals k → r.lookup k = some d → csvGetDialect r name = .ok d) ∧
    (∀ k, name.dictKey = .equals k → r.lookup k = Option.none →
      csvGetDialect r name = .error (csvErr "unknown dialect"))

theorem getDialectLaw_proven : GetDialectLaw := by
  intro r name
  refine ⟨fun m h => ?_, fun e h => ?_, fun h => ?_, fun k d h h2 => ?_, fun k h h2 => ?_⟩ <;>
    simp [csvGetDialect, getDialectFromRegistry, Obj.dictFind, h, dictHashErr, *]

/-- `unregister_dialect`: on an empty registry `PyDict_Pop` does not hash, so even an unhashable name
is `csv.Error`. On a non-empty one a raising `__hash__` raises, a name that is there leaves
`list_dialects`, and one that is not is `csv.Error`. -/
def UnregisterLaw : Prop :=
  (∀ name : Obj, csvUnregisterDialect [] name = .error (csvErr "unknown dialect")) ∧
  ∀ (r r2 : Registry) (name : Obj), r ≠ [] →
    (∀ e, name.dictKey = .hashRaises e → csvUnregisterDialect r name = .error (dictHashErr name e)) ∧
    (∀ k, name.dictKey = .equals k → (r.lookup k).isSome = false →
      csvUnregisterDialect r name = .error (csvErr "unknown dialect")) ∧
    (∀ k, name.dictKey = .equals k → csvUnregisterDialect r name = .ok r2 →
      k ∉ csvListDialects r2)

theorem unregisterLaw_proven : UnregisterLaw := by
  refine ⟨fun name => rfl, fun r r2 name hr => ⟨fun e h => ?_, fun k h h2 => ?_, fun k h h2 => ?_⟩⟩
  · have : r.isEmpty = false := by cases r <;> simp_all
    simp [csvUnregisterDialect, this, Obj.dictFind, h]
  · have : r.isEmpty = false := by cases r <;> simp_all
    simp [csvUnregisterDialect, this, Obj.dictFind, h, h2]
  · have hne : r.isEmpty = false := by cases r <;> simp_all
    simp only [csvUnregisterDialect, hne, Bool.false_eq_true, if_false, Obj.dictFind, h] at h2
    by_cases hk : (r.lookup k).isSome = true
    · simp only [hk, if_true] at h2
      cases h2
      simp [csvListDialects]
    · simp only [hk, if_false] at h2
      cases h2

/-! ### The field limit -/

/-- `field_size_limit` for every argument, with no assumption on its size. Without an argument, or
with an exact `int` that fits `Py_ssize_t`, it returns the old limit. An `int` that does not fit is
an `OverflowError`, and anything else is a `TypeError`, including a `bool`. A failure means no new
limit is in force. -/
def FieldLimit : Prop :=
  ∀ (cur : Int),
    fieldSizeLimit cur Option.none = .ok (cur, cur) ∧
    (∀ n : Int, -(2 ^ 63) ≤ n → n ≤ 2 ^ 63 - 1 → fieldSizeLimit cur (some (.int n)) = .ok (cur, n)) ∧
    (∀ n : Int, (n < -(2 ^ 63) ∨ n > 2 ^ 63 - 1) → fieldSizeLimit cur (some (.int n)) =
      .error (.overflowError "Python int too large to convert to C ssize_t")) ∧
    (∀ o : Obj, (∀ n, o ≠ .int n) → fieldSizeLimit cur (some o) =
      .error (.typeError "limit must be an integer")) ∧
    (∀ (o : Obj) (x y : Int), fieldSizeLimit cur (some o) = .ok (x, y) → x = cur) ∧
    (∀ (o : Obj), (∀ n, o ≠ .int n) → applyLimit cur o = cur)

theorem fieldLimit_proven : FieldLimit := by
  intro cur
  refine ⟨rfl, fun n h1 h2 => ?_, fun n h => ?_, fun o h => ?_, fun o x y h => ?_, fun o h => ?_⟩
  · simp only [fieldSizeLimit]
    rw [if_neg (by omega)]
  · simp only [fieldSizeLimit]
    rw [if_pos h]
  · cases o with
    | int n => exact absurd rfl (h n)
    | _ => rfl
  · cases o with
    | int n =>
      simp only [fieldSizeLimit] at h
      split at h
      · cases h
      · cases h; rfl
    | _ => cases h
  · cases o with
    | int n => exact absurd rfl (h n)
    | _ => rfl

end PyLean.TextLibs.Csv
