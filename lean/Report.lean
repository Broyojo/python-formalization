import PyLean.All

/-!
Registry export for `scripts/check_coverage.py`, run with
`lake env lean Report.lean`. One tab-separated line per entry:
id, status, source file, comma-separated function names.
-/

open PyLean PyLean.Registry

#eval show IO Unit from do
  for e in allEntries do
    let status := match e.status with
      | .proven => "proven"
      | .refuted => "refuted"
      | .open => "open"
    IO.println s!"{e.id}\t{status}\t{e.pyFile}\t{",".intercalate e.pyFns}"
