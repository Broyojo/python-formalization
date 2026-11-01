import PyLean.TextLibs.CsvIoProps

/-!
Properties of `writerows` and of `Lib/csv.py`: `Dialect`, `DictReader` and `DictWriter`, on top of
the fallible reader and writer.
-/

namespace PyLean.TextLibs.Csv

open PyLean PyLean.TextLibs

set_option linter.unusedSimpArgs false

/-! ### `writerows` -/

/-- `writerows` returns `None`, whatever `write` returned. A step of the row iterator that raises
is the result, and the rows before it stay written. -/
def WriterowsResult : Prop :=
  ∀ (d : Dialect) (fuel : Nat) (steps : List Step) (c c' : WCtx) (o : Obj),
    writerowsLoop d fuel c steps = (c', .ok o) → o.isNone = true

theorem writerowsResult_proven : WriterowsResult := by
  intro d fuel steps
  induction steps with
  | nil =>
    intro c c' o h
    simp only [writerowsLoop, Prod.mk.injEq, Except.ok.injEq] at h
    rw [← h.2]
    rfl
  | cons st r ih =>
    intro c c' o h
    cases st with
    | stop =>
      simp only [writerowsLoop, Prod.mk.injEq, Except.ok.injEq] at h
      rw [← h.2]
      rfl
    | raise e => simp [writerowsLoop] at h
    | eff e =>
      simp only [writerowsLoop] at h
      split at h
      · simp at h
      · exact ih _ _ _ h
    | ret row =>
      simp only [writerowsLoop] at h
      split at h
      · simp at h
      · exact ih _ _ _ h

/-! ### `Dialect._validate` -/

/-- `csv.Dialect` accepts what `_csv.Dialect` accepts. A `TypeError` becomes `csv.Error` with the same
text, and any other exception, such as the `ValueError` of a bad character, passes through. -/
def DialectValidate : Prop :=
  ∀ (r : Registry) (self : Obj),
    (∀ x, dialectNew r dialectTy ⟨[self], []⟩ = .ok x → dialectInit r self = .ok ()) ∧
    (∀ m, dialectNew r dialectTy ⟨[self], []⟩ = .error (.typeError m) →
      dialectInit r self = .error (csvErr m)) ∧
    (∀ e, isTypeError e = false → dialectNew r dialectTy ⟨[self], []⟩ = .error e →
      dialectInit r self = .error e)

theorem dialectValidate_proven : DialectValidate := by
  intro r self
  refine ⟨fun x h => ?_, fun m h => ?_, fun e he h => ?_⟩
  · simp [dialectInit, dialectValidate, h]
  · simp [dialectInit, dialectValidate, h]
  · cases e <;> simp_all [dialectInit, dialectValidate, isTypeError]

/-! ### `DictWriter` -/

theorem dictToList_bad {names : List (List Nat)} {rv : Obj} {r : List (List Nat × Obj)}
    (h : r.any (fun p => !names.contains p.1) = true) :
    dictToList names rv true r = .error (.valueError "~dict contains fields not in fieldnames") := by
  unfold dictToList
  rw [if_pos ⟨rfl, h⟩]

theorem dictToList_good {names : List (List Nat)} {rv : Obj} {r : List (List Nat × Obj)}
    (h : ∀ p ∈ r, names.contains p.1 = true) :
    dictToList names rv true r = .ok (names.map fun k => .ret ((r.lookup k).getD rv)) := by
  have hr : r.any (fun p => !names.contains p.1) = false := by
    rw [List.any_eq_false]
    intro q hq
    rw [h q hq]
    decide
  unfold dictToList
  rw [if_neg (fun x => absurd x.2 (by rw [hr]; decide))]

/-- `DictWriter` hands the writer the fields in `fieldnames` order, one `next()` each, with `restval`
for a missing key. With `extrasaction='ignore'` a key outside `fieldnames` is dropped. -/
def DictToListOrder : Prop :=
  ∀ (names : List (List Nat)) (rv : Obj) (rowdict : List (List Nat × Obj)),
    dictToList names rv false rowdict = .ok (names.map fun k => .ret ((rowdict.lookup k).getD rv))

theorem dictToListOrder_proven : DictToListOrder := by
  intro names rv rowdict
  simp [dictToList]

/-- With `extrasaction='raise'`, a key outside `fieldnames` raises `ValueError` and nothing reaches
the writer: `write` is not called and the record buffer is untouched. -/
def DictExtraRaises : Prop :=
  ∀ (d : Dialect) (fuel : Nat) (names : List (List Nat)) (rv : Obj) (c : WCtx)
    (rowdict : List (List Nat × Obj)),
    (∃ p ∈ rowdict, names.contains p.1 = false) →
    dictWriterow d fuel names rv true c rowdict =
      (c, .error (.valueError "~dict contains fields not in fieldnames"))

theorem dictExtraRaises_proven : DictExtraRaises := by
  intro d fuel names rv c rowdict ⟨p, hp, hn⟩
  have : rowdict.any (fun p => !names.contains p.1) = true := by
    rw [List.any_eq_true]
    exact ⟨p, hp, by rw [hn]; rfl⟩
  simp [dictWriterow, dictToList_bad this]

/-- A dict that passes the check is written as the row of its values. -/
def DictWriterowIsRow : Prop :=
  ∀ (d : Dialect) (fuel : Nat) (names : List (List Nat)) (rv : Obj) (c : WCtx)
    (rowdict : List (List Nat × Obj)),
    (∀ p ∈ rowdict, names.contains p.1 = true) →
    dictWriterow d fuel names rv true c rowdict =
      writerowM d fuel c (iterObj (names.map fun k => .ret ((rowdict.lookup k).getD rv)))

theorem dictWriterowIsRow_proven : DictWriterowIsRow := by
  intro d fuel names rv c rowdict h
  simp only [dictWriterow, dictToList_good h]

/-- `DictWriter.writerows` feeds the rows through `map`, which is lazy: the first dict with an extra
key becomes a raise from the row iterator, in its place, so the rows before it are written and the
ones after it are not looked at. -/
def MapStepsStop : Prop :=
  ∀ (names : List (List Nat)) (rv : Obj) (pre : List (List (List Nat × Obj)))
    (bad : List (List Nat × Obj)) (post : List (List (List Nat × Obj))),
    (∀ r ∈ pre, ∀ p ∈ r, names.contains p.1 = true) →
    (∃ p ∈ bad, names.contains p.1 = false) →
    mapSteps names rv true (pre ++ bad :: post) =
      pre.map (fun r => Step.ret (iterObj (names.map fun k => .ret ((r.lookup k).getD rv)))) ++
        [.raise (.valueError "~dict contains fields not in fieldnames")]

theorem mapStepsStop_proven : MapStepsStop := by
  intro names rv pre bad post h1 ⟨p, hp, hn⟩
  induction pre with
  | nil =>
    have : bad.any (fun p => !names.contains p.1) = true := by
      rw [List.any_eq_true]
      exact ⟨p, hp, by rw [hn]; rfl⟩
    simp only [List.nil_append, mapSteps, dictToList_bad this, List.map_nil]
  | cons r rs ih =>
    have hg : ∀ q ∈ r, names.contains q.1 = true := h1 r (by simp)
    have := ih (fun x hx => h1 x (by simp [hx]))
    simp only [List.cons_append, mapSteps, dictToList_good hg, this, List.map_cons]

theorem lookup_self_str (k : List Nat) : ∀ names : List (List Nat), k ∈ names →
    (names.map (fun n => (n, Obj.str n))).lookup k = some (Obj.str k) := by
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

/-- `writeheader` writes the field names as one row, repeated names included, and returns what
`write` returned. -/
def WriteheaderLaw : Prop :=
  ∀ (d : Dialect) (fuel : Nat) (c : WCtx) (names : List (List Nat)),
    writeheader d fuel c names = writerowM d fuel c (iterObj (names.map fun n => .ret (.str n)))

theorem writeheaderLaw_proven : WriteheaderLaw := by
  intro d fuel c names
  have hno : (names.map (fun n => (n, Obj.str n))).any (fun p => !names.contains p.1) = false := by
    simp [List.any_eq_false]
  have hmap : names.map (fun k => Step.ret (((names.map fun n => (n, Obj.str n)).lookup k).getD (.str []))) =
      names.map fun n => Step.ret (.str n) := by
    apply List.map_congr_left
    intro k hk
    rw [lookup_self_str k names hk]
    rfl
  simp only [writeheader, dictWriterow, dictToList]
  rw [if_neg (by simp [hno]), hmap]

/-- `extrasaction` is case-insensitive, and only `raise` and `ignore` are accepted. -/
def ExtrasactionLaw : Prop :=
  extrasactionCheck (strToList "RAISE") = .ok true ∧ extrasactionCheck (strToList "Ignore") = .ok false ∧
    ∀ s, lowerAsciiS s ≠ strToList "raise" → lowerAsciiS s ≠ strToList "ignore" →
      extrasactionCheck s = .error (.valueError "~extrasaction must be 'raise' or 'ignore'")

theorem extrasactionLaw_proven : ExtrasactionLaw := by
  refine ⟨by decide, by decide, fun s h1 h2 => ?_⟩
  simp [extrasactionCheck, h1, h2]

/-! ### `DictReader` -/

theorem zip_fst_sublist : ∀ (a b : List Field), ((a.zip b).map Prod.fst).Sublist a
  | [], _ => by simp
  | _ :: _, [] => by simp
  | x :: xs, y :: ys => by
    simp only [List.zip_cons_cons, List.map_cons]
    exact (zip_fst_sublist xs ys).cons₂ x

theorem dictSet_new (d : List (Field × DVal)) (k : Field) (v : DVal)
    (h : d.any (fun p => keyEq p.1 k) = false) : dictSet d k v = d ++ [(k, v)] := by
  simp [dictSet, h]

/-- No key of `d` is equal to `k`. -/
def Fresh (d : List (Field × DVal)) (k : Field) : Prop := d.any (fun p => keyEq p.1 k) = false

theorem fold_distinct : ∀ (ps : List (Field × Field)) (d : List (Field × DVal)),
    ((ps.map Prod.fst)).Pairwise (fun a b => keyEq a b = false) →
    (∀ p ∈ ps, Fresh d p.1) →
    ps.foldl (fun d p => dictSet d p.1 (.field p.2)) d = d ++ ps.map fun p => (p.1, DVal.field p.2) := by
  intro ps
  induction ps with
  | nil => intro d _ _; simp
  | cons p ps ih =>
    intro d h1 h2
    simp only [List.map_cons, List.pairwise_cons] at h1
    simp only [List.foldl_cons]
    rw [dictSet_new d p.1 _ (h2 p (by simp))]
    have hf : ∀ q ∈ ps, Fresh (d ++ [(p.1, DVal.field p.2)]) q.1 := by
      intro q hq
      have h3 := h2 q (by simp [hq])
      have h4 := h1.1 q.1 (List.mem_map.2 ⟨q, hq, rfl⟩)
      simp only [Fresh, List.any_append, List.any_cons, List.any_nil, Bool.or_false] at h3 ⊢
      simp [h3, h4]
    rw [ih _ h1.2 hf]
    simp

/-- A row with as many fields as there are distinct names is the dict of the two, in order. A longer
row keeps the extras as a list under `restkey`, last, and a shorter one gets `restval` for the
missing names. -/
def DictRowLaw : Prop :=
  ∀ (names row : List Field) (rk : Field),
    names.Pairwise (fun a b => keyEq a b = false) →
    (names.length = row.length →
      dictRow names row rk = (names.zip row).map fun p => (p.1, DVal.field p.2)) ∧
    (names.length < row.length → (∀ k ∈ names, keyEq k rk = false) →
      dictRow names row rk =
        (names.zip row).map (fun p => (p.1, DVal.field p.2)) ++ [(rk, .rest (row.drop names.length))])

theorem dictRowLaw_proven : DictRowLaw := by
  intro names row rk hp
  have hz : ((names.zip row).map Prod.fst).Pairwise (fun a b => keyEq a b = false) := by
    exact hp.sublist (zip_fst_sublist names row)
  have hfold := fold_distinct (names.zip row) [] hz (by intro p _; simp [Fresh])
  constructor
  · intro h
    simp only [dictRow, hfold]
    rw [if_neg (by omega), if_neg (by omega)]
    simp
  · intro h h2
    simp only [dictRow, hfold]
    rw [if_pos h]
    have hn : ((names.zip row).map fun p => (p.1, DVal.field p.2)).any (fun p => keyEq p.1 rk) = false := by
      rw [List.any_eq_false]
      intro q hq
      obtain ⟨z, hz1, hz2⟩ := List.mem_map.1 hq
      have : z.1 ∈ names := (List.of_mem_zip hz1).1
      rw [← hz2]
      simp [h2 z.1 this]
    simp only [List.nil_append]
    rw [dictSet_new _ _ _ hn]

/-- With no field names given, the first row of the file becomes the names, so the first `__next__`
reads two rows and the dict of the second comes out. A first row that is not there is
`StopIteration`. -/
def DictReaderHeader : Prop :=
  ∀ (d : Dialect) (fuel blanks : Nat) (r : DR) (c1 c2 : RCtx) (h row : List Field),
    r.names = Option.none → r.lineNum = 0 →
    readerNext d fuel r.c = (c1, .ok (some h)) → readerNext d fuel c1 = (c2, .ok (some row)) →
    row ≠ [] →
    (drNext d fuel (blanks + 1) r).2 = .ok (some (dictRow h row r.restkey))

theorem dictReaderHeader_proven : DictReaderHeader := by
  intro d fuel blanks r c1 c2 h row h1 h2 h3 h4 h5
  have hne : row.isEmpty = false := List.isEmpty_eq_false_iff.2 h5
  simp [drNext, drFieldnames, h1, h2, h3, h4, drSkipBlank, hne]

/-- Blank rows do not reach the caller: `__next__` reads on past them, and a raise while it does
passes through. -/
def DictReaderSkipsBlank : Prop :=
  ∀ (d : Dialect) (fuel n : Nat) (c c1 : RCtx) (row : List Field),
    (row ≠ [] → drSkipBlank d fuel (n + 1) c row = (c, .ok (some row))) ∧
    (∀ e, readerNext d fuel c = (c1, .error e) → drSkipBlank d fuel (n + 1) c [] = (c1, .error e)) ∧
    (readerNext d fuel c = (c1, .ok Option.none) →
      drSkipBlank d fuel (n + 1) c [] = (c1, .ok Option.none)) ∧
    (readerNext d fuel c = (c1, .ok (some row)) →
      drSkipBlank d fuel (n + 1) c [] = drSkipBlank d fuel n c1 row)

theorem dictReaderSkipsBlank_proven : DictReaderSkipsBlank := by
  intro d fuel n c c1 row
  refine ⟨fun h => ?_, fun e h => ?_, fun h => ?_, fun h => ?_⟩
  · have hne : row.isEmpty = false := List.isEmpty_eq_false_iff.2 h
    simp [drSkipBlank, hne]
  · simp [drSkipBlank, h]
  · simp [drSkipBlank, h]
  · simp [drSkipBlank, h]

/-- `DictReader.__init__` passes `dialect` and the keywords to `reader`, and every failure of
`csv_reader` comes out of the constructor. -/
def DictReaderInit : Prop :=
  ∀ (reg : Registry) (lim : Int) (f dialect : Obj) (names : Option (List Field)) (rk : Field)
    (kw : List (List Nat × Obj)) (e : PyExc),
    csvReader reg lim ⟨[f, dialect], kw⟩ = .error e →
    drInit reg lim f names rk dialect kw = .error e

theorem dictReaderInit_proven : DictReaderInit := by
  intro reg lim f dialect names rk kw e h
  simp [drInit, h, bind, Except.bind]

/-! ### `csv_reader` and `csv_writer` -/

/-- `csv.reader` fails in the order of its body: argument count, then `iter()` of the input, then the
dialect. So a non-iterable input is reported even with a bad dialect. A new reader starts with the
script of its input, at line 0. -/
def CsvReaderOrder : Prop :=
  ∀ (reg : Registry) (lim : Int) (it : Obj) (dialect : Option Obj) (kw : List (List Nat × Obj)),
    (∀ e, it.getIter = .error e → csvReader reg lim ⟨it :: dialect.toList, kw⟩ = .error e) ∧
    (∀ steps e, it.getIter = .ok steps → callDialect reg dialect kw = .error e →
      csvReader reg lim ⟨it :: dialect.toList, kw⟩ = .error e) ∧
    (∀ steps r, it.getIter = .ok steps → callDialect reg dialect kw = .ok r →
      csvReader reg lim ⟨it :: dialect.toList, kw⟩ = .ok (r.dialect, { acts := steps, limit := lim }))

theorem csvReaderOrder_proven : CsvReaderOrder := by
  intro reg lim it dialect kw
  have hu : unpack12 "reader" (it :: dialect.toList) = .ok (it, dialect) := by
    cases dialect <;> rfl
  refine ⟨fun e h => ?_, fun steps e h h2 => ?_, fun steps r h h2 => ?_⟩ <;>
    simp [csvReader, hu, h, bind, Except.bind, pure, Except.pure, *]

/-- `csv.writer` needs a callable `write` attribute. `AttributeError` and a value that is not callable
are the same `TypeError`; any other exception from the attribute passes through; and all of these
come before the dialect is looked at. -/
def CsvWriterOrder : Prop :=
  ∀ (reg : Registry) (f : Obj) (kw : List (List Nat × Obj)),
    (∀ m, f.getattr "write" = .error (.named "AttributeError" m) →
      csvWriter reg ⟨[f], kw⟩ = .error (.typeError "argument 1 must have a \"write\" method")) ∧
    (∀ o, f.getattr "write" = .ok o → (∀ c, o ≠ .func c) →
      csvWriter reg ⟨[f], kw⟩ = .error (.typeError "argument 1 must have a \"write\" method")) ∧
    (∀ e, (∀ m, e ≠ .named "AttributeError" m) → f.getattr "write" = .error e →
      csvWriter reg ⟨[f], kw⟩ = .error e) ∧
    (∀ calls r, f.getattr "write" = .ok (.func calls) → callDialect reg Option.none kw = .ok r →
      csvWriter reg ⟨[f], kw⟩ = .ok (r.dialect, { calls := calls }))

theorem csvWriterOrder_proven : CsvWriterOrder := by
  intro reg f kw
  refine ⟨fun m h => ?_, fun o h h2 => ?_, fun e h h2 => ?_, fun calls r h h2 => ?_⟩
  · simp [csvWriter, unpack12, optionalWrite, h, bind, Except.bind, pure, Except.pure]
    rfl
  · have ho : optionalWrite f = .ok (some o) := by simp [optionalWrite, h]
    simp only [csvWriter, unpack12, ho, bind, Except.bind, pure, Except.pure]
    cases o with
    | func c => exact absurd rfl (h2 c)
    | _ => rfl
  · have ho : optionalWrite f = .error e := by
      unfold optionalWrite
      rw [h2]
      cases e with
      | named cls m =>
        by_cases hc : cls = "AttributeError"
        · subst hc
          exact absurd rfl (h m)
        · simp [hc]
      | _ => rfl
    simp [csvWriter, unpack12, ho, bind, Except.bind]
  · have ho : optionalWrite f = .ok (some (.func calls)) := by simp [optionalWrite, h]
    simp [csvWriter, unpack12, ho, h2, bind, Except.bind, pure, Except.pure]

end PyLean.TextLibs.Csv
