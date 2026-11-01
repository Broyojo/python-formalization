import PyLean.DiffCore
import PyLean.TextLibs.TextwrapModel

/-! `textwrap.*` difftest cases; see `difftest/textlibs_diff.py`. -/

namespace PyLean.TextLibs.Textwrap

open Lean PyLean PyLean.Diff

def nats (j : Json) : Except String (List Nat) := do
  (← j.getArr?).toList.mapM Json.getNat?

def run (fn : String) (j : Json) : Except String Json := do
  match fn with
  | "textwrap.chunks" =>
    let chunks ← (← (← field j "chunks").getArr?).toList.mapM nats
    let t : TW := {
      width := ← getInt j "width"
      initial := ← nats (← field j "initial")
      subsequent := ← nats (← field j "subsequent")
      dropWs := ← getBool j "drop"
      breakLong := ← getBool j "blw"
      breakHyph := ← getBool j "boh"
      maxLines := match j.getObjVal? "max" with
        | .ok v => v.getInt?.toOption
        | .error _ => none
      placeholder := ← nats (← field j "ph") }
    -- The fuel runs out exactly where CPython never returns; the driver reports that as this value.
    match wrapChunks t chunks with
    | .error .modelFuel => return encPy (fun (r : String) => toJson r) (.ok "hang")
    | r => return encPy (fun (r : List (List Nat)) => toJson r) r
  | _ => throw s!"unknown fn {fn}"

end PyLean.TextLibs.Textwrap
