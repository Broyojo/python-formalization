import Lean.Data.Json
import PyLean

/-!
Differential-testing driver. Reads one JSON case per line on stdin,
`{"mod": "<module>", "fn": "<name>", ...args}`, and writes one JSON result per
line: `{"ok": <value>}` or `{"exc": "<class>", "msg": "<message>"}`. Each module
supplies its handler in `PyLean/<Module>/Diff.lean`.
-/

open Lean PyLean.Diff

def handlers : List (String × Handler) := [
  ("ipaddress", PyLean.Ipaddress.handler),
  ("datetime", PyLean.Datetime.handler),
  ("fractions", PyLean.Fractions.handler),
  ("rangeslice", PyLean.RangeSlice.handler),
  ("mathint", PyLean.MathInt.handler),
  ("strsearch", PyLean.StrSearch.handler),
  ("accel", PyLean.Accel.handler)
]

def runCase (j : Json) : Except String Json := do
  let mod ← getStr j "mod"
  let fn ← getStr j "fn"
  let some h := handlers.lookup mod | throw s!"unknown mod {mod}"
  let some r := h fn j | throw s!"unknown fn {mod}.{fn}"
  r

partial def loop (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  let out := match Json.parse line.trimAscii.toString >>= runCase with
    | .ok r => r
    | .error e => Json.mkObj [("harness_error", toJson e)]
  stdout.putStrLn out.compress
  stdout.flush
  loop stdin stdout

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout)
