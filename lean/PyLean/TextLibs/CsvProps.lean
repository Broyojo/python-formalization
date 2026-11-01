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
    | dialectX t d l a i => simp [setCharOrNone, Obj.asStr]
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
      | dialectX t d l a i => simp [setInt]
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
    (h2 : o.asDialect = Option.none) :
    dialectNew r ty ⟨[o], []⟩ = dialectFresh ty (dialectAttrs o { dialect := some o }) := by
  cases o with
  | str s => cases h1
  | strSub t s k => cases h1
  | dialect t d => cases h2
  | dialectX t d l a i => cases h2
  | none => rfl
  | int n => rfl
  | bool b => rfl
  | other t a b c d e f => rfl
  | func c => rfl

/-- A dialect is not a string. -/
theorem asStr_of_dialect {o : Obj} {d : Dialect} (h : o.asDialect = some d) : o.asStr = Option.none := by
  cases o <;> first | rfl | cases h

/-- `dialect_new` with one positional object, whatever the keywords, once they parse. -/
theorem new_pos (r : Registry) (ty : TyName) (o : Obj) (kw : List (List Nat × Obj)) (vals : List (Option Obj))
    (hs : o.asStr = Option.none) (hp : parseDialectArgs ⟨[o], kw⟩ = .ok vals)
    (hd : (argsOf vals).dialect = some o) :
    dialectNew r ty ⟨[o], kw⟩ =
      let a := argsOf vals
      let noOverrides := a.delimiter.isNone && a.doublequote.isNone && a.escapechar.isNone &&
        a.lineterminator.isNone && a.quotechar.isNone && a.quoting.isNone &&
        a.skipinitialspace.isNone && a.strict.isNone
      match o.asDialect with
      | some d => if noOverrides then .ok (.same o d) else dialectFresh ty (dialectAttrs o a)
      | Option.none => dialectFresh ty (dialectAttrs o a) := by
  simp only [dialectNew, hp, bind, Except.bind, hd, hs, pure, Except.pure]
  rfl

/-- A `Dialect` passed with no overrides is the same object back, by value or through the registry
under its name, whichever class it is: that is the "Can we reuse this instance?" branch. An object
that is not a `Dialect` is never reused, even with no overrides: `PyObject_TypeCheck` is the first
test. What `type_call` then does to a reused instance is `CallDialectLaw`. -/
def DialectReuse : Prop :=
  (∀ (r : Registry) (ty : TyName) (o : Obj) (d : Dialect),
    o.asDialect = some d → dialectNew r ty ⟨[o], []⟩ = .ok (.same o d)) ∧
  (∀ (r : Registry) (ty : TyName) (k : List Nat) (key o : Obj) (d : Dialect),
    regFind r k = .ok (some (key, o)) → o.asDialect = some d →
    dialectNew r ty ⟨[.str k], []⟩ = .ok (.same o d)) ∧
  (∀ (r : Registry) (ty : TyName) (o : Obj) (res : DRes),
    o.asStr = Option.none → o.asDialect = Option.none → dialectNew r ty ⟨[o], []⟩ = .ok res →
    ∃ t d l, res = .fresh t d l)

theorem dialectReuse_proven : DialectReuse := by
  refine ⟨fun r ty o d h => ?_, fun r ty k key o d h h2 => ?_, fun r ty o res h1 h2 h3 => ?_⟩
  · rw [new_pos r ty o [] _ (asStr_of_dialect h) (parse_one o) rfl]
    simp only [h]
    rfl
  · have hg : getDialectFromRegistry r (.str k) = .ok o := by
      simp only [getDialectFromRegistry, regLookup, Obj.dictKey, h]
    simp [dialectNew, parse_one, argsOf, Obj.asStr, hg, h2, bind, Except.bind, pure, Except.pure,
      Functor.map, Except.map]
  · rw [new_other r ty o h1 h2] at h3
    cases hb : dialectBuild (dialectAttrs o { dialect := some o }) with
    | error e =>
      simp [dialectFresh, hb, bind, Except.bind] at h3
    | ok d =>
      simp [dialectFresh, hb, bind, Except.bind, pure, Except.pure] at h3
      exact ⟨_, _, _, h3.symm⟩

/-- `DIALECT_GETATTR` clears every failure, not only `AttributeError`, so an object whose attributes
all raise gives the default dialect, and a fresh one. -/
def GetattrCleared : Prop :=
  ∀ (r : Registry) (ty : TyName) (o : Obj),
    o.asStr = Option.none → o.asDialect = Option.none → (∀ n, ∃ e, o.getattr n = .error e) →
    dialectNew r ty ⟨[o], []⟩ =
      .ok (.fresh ty ⟨true, false, false, QUOTE_MINIMAL, 44, 34, NOT_SET, [13, 10]⟩ (.str [13, 10]))

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
  rw [new_other r ty o h1 h2, ha]
  simp [dialectFresh, hb, ltObj, bind, Except.bind, pure, Except.pure]

/-- A keyword beats the attribute, `Modules/_csv.c:504-511`: `DIALECT_GETATTR` only fills what is
still `NULL`. With a keyword present an object is not reused, even a `Dialect`, and the new object
is built from the keywords and the attributes of the old one. -/
def DialectKeywords : Prop :=
  (∀ (o x : Obj) (n : String), getattrOr o (some x) n = some x) ∧
  ∀ (r : Registry) (ty : TyName) (o : Obj) (kw : List (List Nat × Obj)) (vals : List (Option Obj)),
    o.asStr = Option.none → parseDialectArgs ⟨[o], kw⟩ = .ok vals → (argsOf vals).dialect = some o →
    ((argsOf vals).delimiter.isSome ∨ (argsOf vals).doublequote.isSome ∨ (argsOf vals).escapechar.isSome ∨
      (argsOf vals).lineterminator.isSome ∨ (argsOf vals).quotechar.isSome ∨ (argsOf vals).quoting.isSome ∨
      (argsOf vals).skipinitialspace.isSome ∨ (argsOf vals).strict.isSome) →
    dialectNew r ty ⟨[o], kw⟩ = dialectFresh ty (dialectAttrs o (argsOf vals))

theorem none_of_some {x : Option Obj} (h : x.isSome = true) : x.isNone = false := by
  cases x <;> simp_all

theorem dialectKeywords_proven : DialectKeywords := by
  refine ⟨fun o x n => rfl, fun r ty o kw vals hs hp hd hk => ?_⟩
  rw [new_pos r ty o kw vals hs hp hd]
  have hn : ((argsOf vals).delimiter.isNone && (argsOf vals).doublequote.isNone &&
      (argsOf vals).escapechar.isNone && (argsOf vals).lineterminator.isNone &&
      (argsOf vals).quotechar.isNone && (argsOf vals).quoting.isNone &&
      (argsOf vals).skipinitialspace.isNone && (argsOf vals).strict.isNone) = false := by
    rcases hk with h | h | h | h | h | h | h | h <;> simp [none_of_some h]
  simp only [hn]
  cases o.asDialect <;> rfl

/-- `PyArg_ParseTupleAndKeywords` fails first: nothing is looked up or built. Ten arguments are one
too many, and a keyword that names no parameter is `TypeError`. -/
def DialectArgErrors : Prop :=
  (∀ (r : Registry) (ty : TyName) (a : Args) (e : PyExc), parseDialectArgs a = .error e →
    dialectNew r ty a = .error e) ∧
  (∀ a : Args, a.pos.length + a.kw.length > dialectKws.length →
    parseDialectArgs a = .error (.typeError
      s!"function takes at most {dialectKws.length} {if a.pos.length == 0 then "keyword " else ""}arguments ({a.pos.length + a.kw.length} given)")) ∧
  (∀ (k : List Nat) (v : Obj), (∀ n ∈ dialectKws, strToList n ≠ k) →
    parseDialectArgs ⟨[], [(k, v)]⟩ = .error (.typeError "~this function got an unexpected keyword argument"))

theorem dialectArgErrors_proven : DialectArgErrors := by
  refine ⟨fun r ty a e h => ?_, fun a h => ?_, fun k v h => ?_⟩
  · simp [dialectNew, h, bind, Except.bind]
  · unfold parseDialectArgs
    rw [if_pos h]
  · have hk : ∀ n ∈ dialectKws, ([(k, v)] : List (List Nat × Obj)).lookup (strToList n) = Option.none := by
      intro n hn
      have hne : (strToList n == k) = false := by simpa using h n hn
      simp [List.lookup, hne]
    have hc : (dialectKws.drop 0).countP (fun n => (([(k, v)] : List (List Nat × Obj)).lookup (strToList n)).isSome) = 0 := by
      apply List.countP_eq_zero.2
      intro n hn
      simpa [hk n (by simpa using hn)]
    unfold parseDialectArgs
    simp only [List.length_nil, List.length_cons]
    rw [if_neg (by decide)]
    simp only [hc]
    rfl

/-- A name that is not registered is `csv.Error`, whatever keywords come with it. -/
def DialectUnknownName : Prop :=
  ∀ (r : Registry) (ty : TyName) (name : Obj) (s : List Nat) (kw : List (List Nat × Obj))
    (vals : List (Option Obj)),
    name.asStr = some s → parseDialectArgs ⟨[name], kw⟩ = .ok vals → (argsOf vals).dialect = some name →
    regLookup r name = .ok Option.none → dialectNew r ty ⟨[name], kw⟩ = .error (csvErr "unknown dialect")

theorem dialectUnknownName_proven : DialectUnknownName := by
  intro r ty name s kw vals h1 h2 h3 h4
  have hg : getDialectFromRegistry r name = .error (csvErr "unknown dialect") := by
    simp only [getDialectFromRegistry, h4]
  simp [dialectNew, h2, h3, h1, hg, bind, Except.bind, Functor.map, Except.map]

/-- What `dialect_new` builds satisfies `DialectValid`, by any route: keywords, attributes, or both.
Only a reused instance skips the checks, because it passed them when it was made. -/
def DialectNewValid : Prop :=
  ∀ (r : Registry) (ty t : TyName) (a : Args) (d : Dialect) (l : Obj),
    dialectNew r ty a = .ok (.fresh t d l) → t = ty ∧ ∃ b, dialectBuild b = .ok d ∧ l = ltObj b

theorem fresh_inv {ty t : TyName} {b : DArgs} {d : Dialect} {l : Obj}
    (h : dialectFresh ty b = .ok (.fresh t d l)) : t = ty ∧ ∃ b', dialectBuild b' = .ok d ∧ l = ltObj b' := by
  unfold dialectFresh at h
  cases hb : dialectBuild b with
  | error e => simp [hb, bind, Except.bind] at h
  | ok x =>
    simp [hb, bind, Except.bind, pure, Except.pure] at h
    obtain ⟨h1, h2, h3⟩ := h
    subst h1 h2 h3
    exact ⟨rfl, b, hb, rfl⟩

theorem dialectNewValid_proven : DialectNewValid := by
  intro r ty t a d l h
  unfold dialectNew at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  cases hp : parseDialectArgs a with
  | error e =>
    rw [hp] at h
    cases h
  | ok vals =>
    rw [hp] at h
    simp only at h
    generalize (argsOf vals).dialect = dd at h
    cases dd with
    | none => exact fresh_inv h
    | some o =>
      simp only at h
      cases hs : o.asStr with
      | some x =>
        simp only [hs, Functor.map, Except.map] at h
        cases hg : getDialectFromRegistry r o with
        | error e =>
          rw [hg] at h
          cases h
        | ok q =>
          rw [hg] at h
          simp only at h
          cases hd : q.asDialect with
          | none =>
            rw [hd] at h
            exact fresh_inv h
          | some z =>
            rw [hd] at h
            simp only at h
            split at h
            · cases h
            · exact fresh_inv h
      | none =>
        simp only [hs] at h
        cases hd : o.asDialect with
        | none =>
          rw [hd] at h
          exact fresh_inv h
        | some z =>
          rw [hd] at h
          simp only at h
          split at h
          · cases h
          · exact fresh_inv h

/-- An attribute of a subclass shadows the C field, `Modules/_csv.c:507`: `DIALECT_GETATTR` reads what
the instance's class says, and clears it if it raises. Without one it reads the getter. -/
def SubclassAttrs : Prop :=
  ∀ (t : TyName) (d : Dialect) (l : Option Obj) (at_ : List (String × Except PyExc Obj))
    (i : Except PyExc Unit) (n : String),
    (∀ x, at_.lookup n = some (.ok x) → getattrOr (.dialectX t d l at_ i) Option.none n = some x) ∧
    (∀ e, at_.lookup n = some (.error e) → getattrOr (.dialectX t d l at_ i) Option.none n = Option.none) ∧
    (at_.lookup n = Option.none → (.dialectX t d l at_ i : Obj).getattr n = dialectGetattr d l t n)

theorem subclassAttrs_proven : SubclassAttrs := by
  intro t d l a i n
  refine ⟨fun x h => ?_, fun e h => ?_, fun h => ?_⟩ <;> simp [getattrOr, Obj.getattr, h]

/-- `Dialect_get_lineterminator` returns the object in the slot, not a copy of its text: a `str`
subclass stays one, and a keyword's object is what is stored. A slot `_set_str` has not filled gives
`NULL`. -/
def LineterminatorStored : Prop :=
  (∀ o : Obj, dialectGetLineterminator (some o) = .stored o) ∧
  dialectGetLineterminator Option.none = .null ∧
  (∀ (a : DArgs) (o : Obj), a.lineterminator = some o → ltObj a = o) ∧
  ∀ (t : TyName) (d : Dialect) (o : Obj) (i : Except PyExc Unit),
    (.dialectX t d (some o) [] i : Obj).getattr "lineterminator" = .ok o

theorem lineterminatorStored_proven : LineterminatorStored := by
  refine ⟨fun o => rfl, rfl, fun a o h => ?_, fun t d o i => rfl⟩
  simp [ltObj, h]

/-- The getter never returns `NULL` without an exception: that is the rule for a C function called
from Python. -/
def LineterminatorNotNull : Prop :=
  ∀ (t : TyName) (d : Dialect) (l : Option Obj) (i : Except PyExc Unit),
    (.dialectX t d l [] i : Obj).getattr "lineterminator" ≠ .error nullReturn

theorem lineterminatorNotNull_refuted : ¬LineterminatorNotNull := by
  intro h
  exact h dialectTy excel Option.none (.ok ()) rfl

/-- `_call_dialect`: `type_call` runs `tp_init` on what `dialect_new` returned, and for a reused
subclass instance that is its own `__init__`, which can raise. A new instance has `object_init`, so
keywords skip that `__init__`. With no instance and no keywords the result is the default dialect. -/
def CallDialectLaw : Prop :=
  (∀ (r : Registry) (t : TyName) (d : Dialect) (l : Option Obj) (a : List (String × Except PyExc Obj))
    (e : PyExc), callDialect r (some (.dialectX t d l a (.error e))) [] = .error e) ∧
  (∀ (r : Registry) (t : TyName) (d : Dialect) (l : Option Obj) (a : List (String × Except PyExc Obj))
    (u : Unit), ∃ res, callDialect r (some (.dialectX t d l a (.ok u))) [] = .ok res ∧
      res.dialect = d ∧ (∃ o, res = .same o d)) ∧
  (∀ (r : Registry) (t : TyName) (d : Dialect), ∃ res,
    callDialect r (some (.dialect t d)) [] = .ok res ∧ res.dialect = d) ∧
  (∀ (r : Registry) (o : Obj) (kw : List (List Nat × Obj)) (vals : List (Option Obj)),
    o.asStr = Option.none → parseDialectArgs ⟨[o], kw⟩ = .ok vals → (argsOf vals).dialect = some o →
    (argsOf vals).delimiter.isSome = true →
    callDialect r (some o) kw = dialectFresh dialectTy (dialectAttrs o (argsOf vals))) ∧
  (∀ (r : Registry) (kw : List (List Nat × Obj)) (x : Dialect) (l : Obj),
    dialectNew r dialectTy ⟨[], kw⟩ = .ok (.fresh dialectTy x l) →
    callDialect r Option.none kw = .ok (.fresh dialectTy x l)) ∧
  (∃ res, callDialect [] Option.none [] = .ok res ∧ res.dialect = excel)

/-- `_call_dialect` on a reusable instance hands it back: nothing there can fail. It can, because
`type_call` runs a subclass's `__init__` on it, with the instance as an argument. -/
def ReuseNeverFails : Prop :=
  ∀ (r : Registry) (o : Obj) (d : Dialect), o.asDialect = some d →
    ∃ res, callDialect r (some o) [] = .ok res

theorem dialectFresh_tp (ty : TyName) (a : DArgs) : (do tpInit (← dialectFresh ty a)) = dialectFresh ty a := by
  unfold dialectFresh
  cases dialectBuild a <;> rfl

theorem callDialectLaw_proven : CallDialectLaw := by
  have hr : ∀ (r : Registry) (o : Obj) (d : Dialect), o.asDialect = some d →
      callDialect r (some o) [] = tpInit (.same o d) := by
    intro r o d h
    simp [callDialect, typeCall, dialectReuse_proven.1 r dialectTy o d h, bind, Except.bind]
  refine ⟨fun r t d l a e => ?_, fun r t d l a u => ?_, fun r t d => ?_, fun r o kw vals h1 h2 h3 h4 => ?_,
    fun r kw x l h => ?_, ?_⟩
  · rw [hr r _ d rfl]
    rfl
  · exact ⟨.same (.dialectX t d l a (.ok u)) d, by rw [hr r _ d rfl]; rfl, rfl, _, rfl⟩
  · exact ⟨.same (.dialect t d) d, by rw [hr r _ d rfl]; rfl, rfl⟩
  · have hn := dialectKeywords_proven.2 r dialectTy o kw vals h1 h2 h3 (.inl h4)
    simp only [callDialect, typeCall, hn]
    exact dialectFresh_tp _ _
  · simp [callDialect, typeCall, h, bind, Except.bind, tpInit]
  · exact ⟨_, rfl, rfl⟩

theorem reuseNeverFails_refuted : ¬ReuseNeverFails := by
  intro h
  obtain ⟨res, hr⟩ := h [] (.dialectX dialectTy excel Option.none [] (.error .modelFuel)) excel rfl
  rw [callDialectLaw_proven.1] at hr
  cases hr

/-- `Dialect_reduce`: a dialect cannot be pickled or copied through `__reduce__` or `__reduce_ex__`,
with the name of its own class in the message, unless that class defines the method. -/
def DialectNoPickle : Prop :=
  (∀ (t : TyName) (d : Dialect) (m : String),
    dialectPickle (.dialect t d) m = .error (.typeError s!"cannot pickle '{t.short}' instances")) ∧
  (∀ (t : TyName) (d : Dialect) (l : Option Obj) (a : List (String × Except PyExc Obj))
    (i : Except PyExc Unit) (m : String), a.lookup m = Option.none →
    dialectPickle (.dialectX t d l a i) m = .error (.typeError s!"cannot pickle '{t.short}' instances")) ∧
  (∀ (t : TyName) (d : Dialect) (l : Option Obj) (a : List (String × Except PyExc Obj))
    (i : Except PyExc Unit) (m : String) (x : Obj), a.lookup m = some (.ok x) →
    dialectPickle (.dialectX t d l a i) m = .ok ())

theorem dialectNoPickle_proven : DialectNoPickle := by
  refine ⟨fun t d m => rfl, fun t d l a i m h => ?_, fun t d l a i m x h => ?_⟩ <;>
    simp [dialectPickle, h, dialectReduce]

/-! ### The registry -/

theorem lookup_ne {α : Type} (name k : List Nat) (v : α) (l : List (List Nat × α)) (h : name ≠ k) :
    ((k, v) :: l).lookup name = l.lookup name := by
  have hb : (name == k) = false := by simpa using h
  simp [List.lookup, hb]

/-- An exact `str` answers to its own text and nothing else. -/
theorem answers_str (s k : List Nat) : keyAnswers (.str s) k = .ok (s == k) := rfl

theorem regPut_find (name d : Obj) (k : List Nat) (hn : keyAnswers name k = .ok true) :
    ∀ (l l2 : Registry), regPut name d l k = .ok l2 → ∃ x, regFind l2 k = .ok (some (x, d)) := by
  intro l
  induction l with
  | nil =>
    intro l2 h
    cases h
    exact ⟨name, by simp [regFind, hn]⟩
  | cons p ps ih =>
    intro l2 h
    obtain ⟨key, v⟩ := p
    simp only [regPut] at h
    cases hk : keyAnswers key k with
    | error e =>
      rw [hk] at h
      cases h
    | ok b =>
      rw [hk] at h
      cases b with
      | true =>
        cases h
        exact ⟨key, by simp [regFind, hk]⟩
      | false =>
        simp only [bind, Except.bind, pure, Except.pure] at h
        cases hp : regPut name d ps k with
        | error e =>
          rw [hp] at h
          cases h
        | ok l3 =>
          rw [hp] at h
          cases h
          obtain ⟨x, hx⟩ := ih l3 hp
          exact ⟨x, by simp [regFind, hk, hx]⟩

/-- A registered dialect can be read back by name, and it is the object `_call_dialect` made, in
whatever state callbacks left the registry between `:1632` and `:1635`, and whatever keys it holds. -/
def RegistryLaw : Prop :=
  ∀ (r r2 : Registry) (during : Registry → Registry) (name : List Nat) (inst : Option Obj)
    (kw : List (List Nat × Obj)) (d : DRes),
    callDialect r inst kw = .ok d →
    csvRegisterDialect r during ⟨.str name :: inst.toList, kw⟩ = (r2, .ok ()) →
    csvGetDialect r2 (.str name) = .ok d.obj

theorem registryLaw_proven : RegistryLaw := by
  intro r r2 during name inst kw d h1 h2
  have hu : unpack12 "register_dialect" (.str name :: inst.toList) = .ok (.str name, inst) := by
    cases inst <;> rfl
  simp only [csvRegisterDialect, hu, Obj.asStr, h1] at h2
  have hs : regSet (during r) (.str name) d.obj = regPut (.str name) d.obj (during r) name := rfl
  rw [hs] at h2
  cases hp : regPut (.str name) d.obj (during r) name with
  | error e =>
    rw [hp] at h2
    simp at h2
  | ok l =>
    rw [hp] at h2
    simp only [Prod.mk.injEq] at h2
    obtain ⟨h3, _⟩ := h2
    subst h3
    obtain ⟨x, hx⟩ := regPut_find _ _ name (by simp [answers_str]) _ _ hp
    simp [csvGetDialect, getDialectFromRegistry, regLookup, Obj.dictKey, hx]

/-- `PyDict_SetItem` at `:1635` works on the registry as the callbacks left it, not as it was at
`:1632`: a failed `_call_dialect` keeps their effects and adds nothing, and a key they removed or
added is seen. -/
def RegisterSeesCallbacks : Prop :=
  ∀ (r : Registry) (during : Registry → Registry) (name : Obj) (s : List Nat)
    (kw : List (List Nat × Obj)),
    name.asStr = some s →
    (∀ e, callDialect r Option.none kw = .error e →
      csvRegisterDialect r during ⟨[name], kw⟩ = (during r, .error e)) ∧
    (∀ d r2, callDialect r Option.none kw = .ok d → regSet (during r) name d.obj = .ok r2 →
      csvRegisterDialect r during ⟨[name], kw⟩ = (r2, .ok ())) ∧
    (∀ d e, callDialect r Option.none kw = .ok d → regSet (during r) name d.obj = .error e →
      csvRegisterDialect r during ⟨[name], kw⟩ = (during r, .error e))

theorem registerSeesCallbacks_proven : RegisterSeesCallbacks := by
  intro r during name s kw hs
  refine ⟨fun e h => ?_, fun d r2 h h2 => ?_, fun d e h h2 => ?_⟩ <;>
    simp [csvRegisterDialect, unpack12, hs, h, *]

/-- A `str` subclass stays the key, with its own `__hash__` and `__eq__`: `list_dialects` returns the
object, and a key that compares unequal to everything is listed and cannot be found by its text. -/
def SubclassKeyKept : Prop :=
  ∀ (t : TyName) (s : List Nat) (r : Registry) (d : Obj),
    regSet r (.strSub t s .noMatch) d = .ok (r ++ [(.strSub t s .noMatch, d)]) ∧
    (∀ e, regSet r (.strSub t s (.hashRaises e)) d = .error (dictHashErr (.strSub t s (.hashRaises e)) e)) ∧
    csvListDialects [(.strSub t s .noMatch, d)] = [.strSub t s .noMatch] ∧
    csvGetDialect [(.strSub t s .noMatch, d)] (.str s) = .error (csvErr "unknown dialect")

theorem subclassKeyKept_proven : SubclassKeyKept := by
  intro t s r d
  refine ⟨rfl, fun e => rfl, rfl, ?_⟩
  simp [csvGetDialect, getDialectFromRegistry, regLookup, Obj.dictKey, regFind, keyAnswers]

/-- `register_dialect` checks the name's type before anything about the dialect: a name that is not
a string raises `TypeError` even if the keyword arguments are invalid. A subclass of `str` whose
`__hash__` raises fails at `PyDict_SetItem`, and the dialect it built is not registered. -/
def RegisterNameChecks : Prop :=
  (∀ (r : Registry) (during : Registry → Registry) (o : Obj) (kw : List (List Nat × Obj)),
    o.asStr = Option.none →
    csvRegisterDialect r during ⟨[o], kw⟩ = (r, .error (.typeError "dialect name must be a string"))) ∧
  ∀ (r : Registry) (during : Registry → Registry) (t : TyName) (s : List Nat) (e : PyExc)
    (kw : List (List Nat × Obj)) (d : DRes),
    callDialect r Option.none kw = .ok d →
    csvRegisterDialect r during ⟨[.strSub t s (.hashRaises e)], kw⟩ =
      (during r, .error (dictHashErr (.strSub t s (.hashRaises e)) e))

theorem registerNameChecks_proven : RegisterNameChecks := by
  constructor
  · intro r during o kw h
    simp [csvRegisterDialect, unpack12, h]
  · intro r during t s e kw d h
    simp [csvRegisterDialect, unpack12, h, Obj.asStr, regSet, Obj.dictKey]

/-- `get_dialect` on every kind of name: a `TypeError` from `__hash__` gains the key's type, any
other failure of `__hash__` or `__eq__` passes through, a key that matches nothing is `csv.Error`,
and an equal key finds the dialect whatever object it is, unless a stored key's `__eq__` raises. -/
def GetDialectLaw : Prop :=
  ∀ (r : Registry) (name : Obj),
    (∀ m, name.dictKey = .hashRaises (.typeError m) → csvGetDialect r name =
      .error (.typeError s!"cannot use '{name.ty.full}' as a dict key ({m})")) ∧
    (∀ e, name.dictKey = .eqRaises e → csvGetDialect r name = .error e) ∧
    (name.dictKey = .noMatch → csvGetDialect r name = .error (csvErr "unknown dialect")) ∧
    (∀ k key d, name.dictKey = .equals k → regFind r k = .ok (some (key, d)) → csvGetDialect r name = .ok d) ∧
    (∀ k, name.dictKey = .equals k → regFind r k = .ok Option.none →
      csvGetDialect r name = .error (csvErr "unknown dialect")) ∧
    (∀ k e, name.dictKey = .equals k → regFind r k = .error e → csvGetDialect r name = .error e)

theorem getDialectLaw_proven : GetDialectLaw := by
  intro r name
  refine ⟨fun m h => ?_, fun e h => ?_, fun h => ?_, fun k key d h h2 => ?_, fun k h h2 => ?_,
    fun k e h h2 => ?_⟩ <;>
    simp [csvGetDialect, getDialectFromRegistry, regLookup, h, dictHashErr, *]

/-- `unregister_dialect`: on an empty registry `PyDict_Pop` does not hash, so even an unhashable name
is `csv.Error`. On a non-empty one a raising `__hash__` raises, a name that is there leaves the
registry, and one that is not is `csv.Error`. -/
def UnregisterLaw : Prop :=
  (∀ name : Obj, csvUnregisterDialect [] name = .error (csvErr "unknown dialect")) ∧
  ∀ (r r2 : Registry) (name : Obj), r ≠ [] →
    (∀ e, name.dictKey = .hashRaises e → csvUnregisterDialect r name = .error (dictHashErr name e)) ∧
    (∀ k, name.dictKey = .equals k → regDel r k = .ok Option.none →
      csvUnregisterDialect r name = .error (csvErr "unknown dialect")) ∧
    (∀ k, name.dictKey = .equals k → regDel r k = .ok (some r2) → csvUnregisterDialect r name = .ok r2)

theorem unregisterLaw_proven : UnregisterLaw := by
  refine ⟨fun name => rfl, fun r r2 name hr => ⟨fun e h => ?_, fun k h h2 => ?_, fun k h h2 => ?_⟩⟩
  · have : r.isEmpty = false := by cases r <;> simp_all
    simp [csvUnregisterDialect, this, h]
  · have : r.isEmpty = false := by cases r <;> simp_all
    simp [csvUnregisterDialect, this, h, h2]
  · have : r.isEmpty = false := by cases r <;> simp_all
    simp [csvUnregisterDialect, this, h, h2]

/-- A name that is removed from a list of distinct exact strings is no longer listed. -/
theorem regDel_not_listed (k : List Nat) : ∀ (l l2 : Registry),
    (∀ p ∈ l, ∃ s, p.1 = .str s) → (l.map (·.1)).Nodup → regDel l k = .ok (some l2) →
    .str k ∉ csvListDialects l2 := by
  intro l
  induction l with
  | nil => intro l2 _ _ h; cases h
  | cons p ps ih =>
    intro l2 hs hn h
    obtain ⟨key, v⟩ := p
    obtain ⟨s, hk⟩ := hs (key, v) (by simp)
    simp only at hk
    subst hk
    simp only [regDel, answers_str] at h
    by_cases he : s = k
    · subst he
      simp only [beq_self_eq_true] at h
      cases h
      simp only [List.map_cons, List.nodup_cons] at hn
      exact hn.1
    · have hb : (s == k) = false := by simpa using he
      simp only [hb] at h
      cases hd : regDel ps k with
      | error e =>
        rw [hd] at h
        cases h
      | ok x =>
        rw [hd] at h
        cases x with
        | none => cases h
        | some r2 =>
          cases h
          simp only [List.map_cons, List.nodup_cons] at hn
          have h3 := ih r2 (fun q hq => hs q (by simp [hq])) hn.2 hd
          simp only [csvListDialects, List.map_cons, List.mem_cons, not_or]
          refine ⟨?_, h3⟩
          intro h4
          cases h4
          exact he rfl

/-- `list_dialects` is the keys in dict order: a new name comes last, a name set again keeps its
place, and a name that is removed is gone. -/
def ListDialectsLaw : Prop :=
  (∀ (r : Registry) (t : TyName) (s : List Nat) (d : Obj) (r2 : Registry),
    regSet r (.strSub t s .noMatch) d = .ok r2 → csvListDialects r2 = csvListDialects r ++ [.strSub t s .noMatch]) ∧
  (∀ (k : List Nat) (d : Obj), ∀ (l l2 : Registry), regPut (.str k) d l k = .ok l2 →
    (∃ e ∈ l, keyAnswers e.1 k = .ok true) → csvListDialects l2 = csvListDialects l) ∧
  (∀ (k : List Nat) (d : Obj), ∀ (l l2 : Registry), regPut (.str k) d l k = .ok l2 →
    (∀ e ∈ l, keyAnswers e.1 k = .ok false) → csvListDialects l2 = csvListDialects l ++ [.str k]) ∧
  (∀ (k : List Nat) (l l2 : Registry), (∀ p ∈ l, ∃ s, p.1 = .str s) → (l.map (·.1)).Nodup →
    regDel l k = .ok (some l2) → .str k ∉ csvListDialects l2)

theorem put_new (k : List Nat) (d : Obj) : ∀ (l l2 : Registry), regPut (.str k) d l k = .ok l2 →
    (∀ e ∈ l, keyAnswers e.1 k = .ok false) → csvListDialects l2 = csvListDialects l ++ [.str k] := by
  intro l
  induction l with
  | nil =>
    intro l2 h _
    cases h
    rfl
  | cons p ps ih =>
    intro l2 h hn
    obtain ⟨key, v⟩ := p
    have hk : keyAnswers key k = .ok false := hn (key, v) (by simp)
    simp only [regPut, hk, bind, Except.bind, pure, Except.pure] at h
    cases hp : regPut (.str k) d ps k with
    | error e =>
      rw [hp] at h
      cases h
    | ok l3 =>
      rw [hp] at h
      cases h
      have := ih l3 hp fun e he => hn e (by simp [he])
      simp only [csvListDialects, List.map_cons, List.cons_append] at this ⊢
      rw [this]

theorem put_old (k : List Nat) (d : Obj) : ∀ (l l2 : Registry), regPut (.str k) d l k = .ok l2 →
    (∃ e ∈ l, keyAnswers e.1 k = .ok true) → csvListDialects l2 = csvListDialects l := by
  intro l
  induction l with
  | nil =>
    intro l2 _ h
    obtain ⟨e, h1, _⟩ := h
    simp at h1
  | cons p ps ih =>
    intro l2 h hn
    obtain ⟨key, v⟩ := p
    obtain ⟨e, h1, h2⟩ := hn
    simp only [regPut] at h
    cases hk : keyAnswers key k with
    | error x =>
      rw [hk] at h
      cases h
    | ok b =>
      rw [hk] at h
      cases b with
      | true =>
        cases h
        rfl
      | false =>
        simp only [bind, Except.bind, pure, Except.pure] at h
        cases hp : regPut (.str k) d ps k with
        | error x =>
          rw [hp] at h
          cases h
        | ok l3 =>
          rw [hp] at h
          cases h
          simp only [List.mem_cons] at h1
          rcases h1 with rfl | h1
          · simp only at h2
            rw [hk] at h2
            cases h2
          · have := ih l3 hp ⟨e, h1, h2⟩
            simp only [csvListDialects, List.map_cons] at this ⊢
            rw [this]

theorem listDialectsLaw_proven : ListDialectsLaw := by
  refine ⟨fun r t s d r2 h => ?_, fun k d l l2 h h2 => put_old k d l l2 h h2,
    fun k d l l2 h h2 => put_new k d l l2 h h2, fun k l l2 h1 h2 h3 => regDel_not_listed k l l2 h1 h2 h3⟩
  simp only [regSet, Obj.dictKey] at h
  cases h
  simp only [csvListDialects, List.map_append, List.map_cons, List.map_nil]

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
