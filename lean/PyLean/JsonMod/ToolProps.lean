import PyLean.JsonMod.Tool
import PyLean.JsonMod.RoundTripTop

/-!
Properties of `Lib/json/tool.py`.
-/

namespace PyLean.JsonMod

open PyLean

theorem colorMatch_pos {s : PStr} {g : CGroup} {n : Nat} (h : colorMatch s = some (g, n)) : 1 ≤ n := by
  unfold colorMatch at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h; omega)

/-- The theme with no colours. -/
def plainTheme : Theme := { color := fun _ => [], reset := [] }

theorem colorize_plain : ∀ (f : Nat) (s : PStr), s.length < f → colorizeLoop plainTheme f s = s := by
  intro f
  induction f with
  | zero => intro s h; omega
  | succ f ih =>
    intro s h
    cases s with
    | nil => rfl
    | cons c t =>
      simp only [colorizeLoop]
      cases hm : colorMatch (c :: t) with
      | none =>
        simp only [List.length_cons] at h
        simp only
        rw [ih t (by omega)]
      | some p =>
        obtain ⟨g, n⟩ := p
        have hn := colorMatch_pos hm
        simp only [plainTheme, List.nil_append, List.append_nil]
        have hd : ((c :: t).drop n).length < f := by
          simp only [List.length_drop, List.length_cons] at h ⊢
          omega
        have := ih ((c :: t).drop n) hd
        simp only [plainTheme] at this
        rw [this, List.take_append_drop]

/-- `_colorize_json` only inserts theme strings: with a theme of empty strings,
every text comes back unchanged, valid JSON or not. -/
def ColorizeStrip : Prop := ∀ s : PStr, colorizeJson plainTheme s = s

theorem colorizeStrip_proven : ColorizeStrip := fun s => colorize_plain _ s (by omega)

/-- `python -m json.tool` on an invalid document writes nothing and ends with
`SystemExit` carrying the text of the exception. -/
def ToolInvalid : Prop :=
  ∀ (o : ToolOpts) (env : ToolEnv) (input : PStr) (m : String), o.jsonLines = false →
    jsonLoads loadsC {} (.str input) = .error (.named "JSONDecodeError" m) →
    toolMain o env input = { out := [], exit := some (.named "SystemExit" m) }

theorem toolInvalid_proven : ToolInvalid := by
  intro o env input m h1 h2
  simp [toolMain, h1, jsonLoad, h2, yRaise, toolExc, isValueError, PyExc.message]

/-- With `--json-lines` the lines before the first bad one are processed: the
output is what the good lines write, and the exception ends the run. -/
def ToolLinesPrefix : Prop :=
  ∀ (o : ToolOpts) (env : ToolEnv) (l : PStr) (ls : List PStr) (obj : JVal),
    jsonLoads loadsC {} (.str l) = .ok obj →
    toolLines o env (l :: ls) = yThen (toolWrite o env obj) (toolLines o env ls)

theorem toolLinesPrefix_proven : ToolLinesPrefix := by
  intro o env l ls obj h
  simp [toolLines, h]

/-- Open. `python -m json.tool` keeps the document: a value without floats, on
which `json-roundtrip` applies, comes back from the text written, for every
indent option and `--compact`. The output ends in a newline, which `json-roundtrip`
does not cover. -/
def ToolRoundTrip : Prop :=
  ∀ (o : ToolOpts) (env : ToolEnv) (input : PStr) (obj : JVal), o.jsonLines = false → o.sortKeys = false →
    env.theme = none → (∀ c, env.wr c = none) →
    jsonLoads loadsC {} (.str input) = .ok obj →
    EVal.toJ (obj.toE env.fl) = some obj → EVal.clean o.ensureAscii (obj.toE env.fl) = true →
    (toolMain o env input).exit = none →
    jsonLoads loadsC {} (.str (toolMain o env input).out) = .ok obj

end PyLean.JsonMod
