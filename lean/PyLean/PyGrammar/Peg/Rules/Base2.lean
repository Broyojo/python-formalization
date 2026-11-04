import PyLean.PyGrammar.Peg.Rules.Base

/-! More tools for `Peg/Rules/`: the forced token `&&'x'` and `CHECK_VERSION`. -/

namespace PyLean.PyGrammar.Peg

open Lexer

/-- `_PyPegen_expect_forced_token` (`Parser/pegen.c:435-454`) returning `NULL` always leaves
`error_indicator` set: either `p->error_indicator` was set on entry, `_PyPegen_fill_token` failed,
or `RAISE_ERROR_KNOWN_LOCATION` reported "expected 'x'". -/
theorem forcedToken_null_ei {ty : Nat} {x : String} {p s : PS} (h : forcedToken ty x p = (.null, s)) :
    s.errorIndicator = true := by
  unfold forcedToken at h
  dsimp only at h
  split at h
  · cases h
    assumption
  · split at h
    · rename_i hok
      cases h
      exact ensureToken_ei p (by simpa using hok)
    · split at h
      · cases h
        exact raiseKnownLocation_ei _ _ _ _ _ _ _
      · cases h

theorem tg_forced {ty : Nat} {x : String} {s s' : PS} {v : Ast} (h : forcedToken ty x s = (v, s')) :
    TokGrows s s' := by
  have := (spec_forcedTok (fun _ => default) ty x s).grows.toks
  rwa [h] at this

/-- `CHECK_VERSION(type, v, msg, node)` (`Parser/pegen.h`, `INVALID_VERSION_CHECK`) with a
non-`NULL` node and `p->feature_version >= v`: the node. -/
theorem evalA_cv_ok {env : Array Ast} {ex : Extra} {v : Int} {m : String} {node : AE} {s : PS}
    {n : Ast} (hn : evalA env ex node s = (n, s)) (hnn : n ≠ .null)
    (hv : ¬ (s.featureVersion : Int) < v) :
    evalA env ex (.checkVersion (.int v) (.str m) node) s = (n, s) := by
  simp only [evalA, bind, StateT.bind, hn, pure, StateT.pure, get, getThe, MonadStateOf.get,
    StateT.get]
  cases n with
  | null => exact absurd rfl hnn
  | _ => simp [hv, StateT.pure]; rfl

/-- `CHECK_VERSION` with a non-`NULL` node and `p->feature_version < v`: `error_indicator` set and
`RAISE_SYNTAX_ERROR("%s only supported in Python 3.%i and greater", msg, v)`, result `NULL`. -/
theorem evalA_cv_low {env : Array Ast} {ex : Extra} {v : Int} {m : String} {node : AE} {s : PS}
    {n : Ast} (hn : evalA env ex node s = (n, s)) (hnn : n ≠ .null)
    (hv : (s.featureVersion : Int) < v) :
    evalA env ex (.checkVersion (.int v) (.str m) node) s =
      (.null, (raiseError0 "SyntaxError"
        s!"{cpsStr (m.toList.map Char.toNat)} only supported in Python 3.{v} and greater"
        { s with errorIndicator := true }).2) := by
  simp only [evalA, bind, StateT.bind, hn, pure, StateT.pure, get, getThe, MonadStateOf.get,
    StateT.get]
  cases n with
  | null => exact absurd rfl hnn
  | _ =>
    simp only [hv, ↓reduceIte, modify, modifyGet, MonadStateOf.modifyGet,
      StateT.modifyGet, MonadState.modifyGet, StateT.bind]
    rfl

/-- The rule-level outcome of a `CHECK_VERSION` that failed: whatever `emit_action` does with the
`NULL`, the rule function returns `NULL` with the version error raised. -/
theorem cv_low_result {r : Option Ast × PS} {s : PS} (msg : String)
    (hr : r = if ((!nonNull Ast.null ||
        (raiseError0 "SyntaxError" msg { s with errorIndicator := true }).2.errorIndicator) &&
        (raiseError0 "SyntaxError" msg { s with errorIndicator := true }).2.errOccurred) = true then
        (none, { (raiseError0 "SyntaxError" msg { s with errorIndicator := true }).2 with
          errorIndicator := true })
      else (some .null, (raiseError0 "SyntaxError" msg { s with errorIndicator := true }).2)) :
    (r.1.getD .null, r.2.leave).1 = .null ∧ (r.1.getD .null, r.2.leave).2.errorIndicator = true ∧
      (r.1.getD .null, r.2.leave).2.tok =
        (raiseError0 "SyntaxError" msg { s with errorIndicator := true }).2.tok := by
  have hei := (frame_raiseError0 "SyntaxError" msg { s with errorIndicator := true }).grows.err rfl
  subst hr
  generalize raiseError0 "SyntaxError" msg { s with errorIndicator := true } = r at hei ⊢
  split <;> simp [hei, PS.leave]

end PyLean.PyGrammar.Peg
