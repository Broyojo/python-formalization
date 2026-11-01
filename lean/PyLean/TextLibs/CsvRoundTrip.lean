import PyLean.TextLibs.CsvDictProps

/-! `reader(writer(rows)) == rows`, on the reader and writer themselves. -/

namespace PyLean.TextLibs.Csv

open PyLean PyLean.TextLibs

/-- A row of strings, as the iterator `writerow` draws from. -/
def rowObj (row : List (List Nat)) : Obj := iterObj (row.map fun f => .ret (.str f))

/-- Reading back what `writerow` passed to `write` gives the row, for every accepted dialect that does
not convert fields. Refuted: with `skipinitialspace=True`, the writer leaves a leading space unquoted
and the reader drops it. The counterexample takes the plain-character path of `join_append_data`. -/
def CsvRoundTrip : Prop :=
  ∀ (a : DArgs) (d : Dialect) (row : List (List Nat)) (fuel : Nat) (c : WCtx) (o : Obj) (t : List Nat),
    dialectBuild a = .ok d → (d.quoting = QUOTE_MINIMAL ∨ d.quoting = QUOTE_ALL) →
    writerowM d fuel {} (rowObj row) = (c, .ok o) → c.written = [t] →
    (readerNext d fuel { acts := [.ret (.str t)], limit := 131072 }).2 =
      .ok (some (row.map Field.str))

theorem csvRoundTrip_refuted : ¬CsvRoundTrip := by
  intro h
  have := h { skipinitialspace := some (.bool true) } ⟨true, true, false, 0, 44, 34, NOT_SET, [13, 10]⟩
    [[32, 97]] 16 { buf := [32, 97, 13, 10], numFields := 1, written := [[32, 97, 13, 10]] } .none
    [32, 97, 13, 10] (by decide +kernel) (.inl rfl) rfl rfl
  revert this
  decide +kernel

end PyLean.TextLibs.Csv
