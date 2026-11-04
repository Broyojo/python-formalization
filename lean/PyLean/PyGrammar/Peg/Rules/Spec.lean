import PyLean.PyGrammar.Peg.Rules.Invalid3

/-! Rule statements as equations, for rules with many alternatives or long items.

A rule's text is written in the statement as a list of `SAlt`: the items of each alternative (in
the order of `Grammar/python.gram`, with their lookaheads, options and cuts), whether it is an
`invalid_` alternative, and what its action does, as an explicit function of the values the items
bound: the exception it raises (class, message, location) or the node it builds. `specAlts` runs
that list the way `handle_alt_normal` of `Tools/peg_generator/pegen/c_generator.py` does: the
`call_invalid_rules` guard, the `error_indicator` check, the `&&` chain of the items
(`runItems`, `join_conditions`), the mark reset after a failed alternative, the cut, and `NULL`
past the last. `runAlts_spec` matches it to the rule's data in `GrammarData.lean`, so a rule
with its alternatives in another order, an item or lookahead dropped, another message, location
or node fails the statement.

Sub-rules called by an item are `callRule` on their own data, and are pinned by their own
statements (the `Tmp`, `Loop` and gather statements next to each rule). -/

namespace PyLean.PyGrammar.Peg

open Lexer

/-- One alternative as the rule text gives it: its items, whether it is an `invalid_`
alternative (tried only when `p->call_invalid_rules`), and its action: from the values the items
bound (oldest first), the start location of the rule (`EXTRA`), and the state after the last item,
the result (`some v`: `_res = v`, `goto done`; `none`: the error return) and the state. -/
structure SAlt where
  items : List Item
  inv : Bool := false
  out : Array Ast → Int × Int → PS → Option Ast × PS

/-- The alternatives of a rule function, `handle_alt_normal`, with the actions of `SAlt`. -/
def specAlts : Nat → List SAlt → Nat → Int × Int → PS → Option Ast × PS
  | 0, _, _, _, p => (none, (outOfFuel p).2)
  | _ + 1, [], _, _, p => (some .null, p)
  | f + 1, a :: rest, m, st, p =>
    if a.inv && !p.callInvalidRules then specAlts f rest m st p
    else if p.errorIndicator then (none, p)
    else
      let r := runItems f a.items #[] false p
      match r.1.1 with
      | some env => a.out env st r.2
      | none =>
        let q := { r.2 with mark := m }
        if r.1.2 then (none, q) else specAlts f rest m st q

/-- The end of a rule function that is not `(memo)`: `_res`, or `NULL` on the error return, and
`p->level--`. -/
def finish (a : Option Ast × PS) : Ast × PS := (a.1.getD .null, a.2.leave)

/-- `a` is the data of the alternative the text `x` describes. -/
def AltIs (a : Alt) (x : SAlt) : Prop :=
  a.items = x.items ∧ a.guardInvalid = x.inv ∧
    ∀ env st s, altResult a false env st s = x.out env st s

/-- Each alternative of the data is the one the text gives, in order. -/
def AltsAre : List Alt → List SAlt → Prop
  | [], [] => True
  | a :: as, x :: xs => AltIs a x ∧ AltsAre as xs
  | _, _ => False

theorem runAlts_spec : ∀ (f : Nat) (as : List Alt) (xs : List SAlt), AltsAre as xs →
    ∀ m st s, runAlts f as false m st s = specAlts f xs m st s := by
  intro f
  induction f with
  | zero => intro as xs _ m st s; simp [runAlts, specAlts]
  | succ f ih =>
    intro as xs h m st s
    match as, xs, h with
    | [], [], _ => simp [runAlts, specAlts]
    | a :: as, x :: xs, ⟨⟨h1, h2, h3⟩, hrest⟩ =>
      simp only [runAlts, specAlts, h1, h2, h3]
      by_cases hg : (x.inv && !s.callInvalidRules) = true
      · simp only [hg, ↓reduceIte]
        exact ih _ _ hrest _ _ _
      · simp only [hg, Bool.false_eq_true, ↓reduceIte]
        by_cases he : s.errorIndicator = true
        · simp [he]
        · simp only [he, Bool.false_eq_true, ↓reduceIte]
          generalize runItems f x.items #[] false s = r
          obtain ⟨⟨o, c⟩, s'⟩ := r
          cases o with
          | some env => rfl
          | none => cases c <;> simp [ih _ _ hrest]

/-! ### Actions -/

/-- `RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, msg)` over the values `i` and `j`. -/
@[irreducible] def oKR (i j : Nat) (m : String) : Array Ast → Int × Int → PS → Option Ast × PS :=
  fun env _ s => (none, raisedAt (env.getD i .null) (env.getD j .null) m s)

/-- `RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, msg)` over the value `i`. -/
@[irreducible] def oKL (i : Nat) (m : String) : Array Ast → Int × Int → PS → Option Ast × PS :=
  fun env _ s => (none, raisedAt (env.getD i .null) (env.getD i .null) m s)

/-- `_PyPegen_raise_error(p, cls, use_mark, msg)` and the error return: `RAISE_SYNTAX_ERROR`
(`use_mark` 0, located at the last token read), `RAISE_SYNTAX_ERROR_ON_NEXT_TOKEN` (1, at the
token under the mark), `RAISE_INDENTATION_ERROR` (`IndentationError`, 0). The error return needs
an exception set; reading the next token for `use_mark` can fail without one (`emit_action` then
keeps the `NULL` as the result). -/
def raisedMsg (cls : String) (useMark : Bool) (m : String) (s : PS) : Option Ast × PS :=
  let r := (raiseError cls useMark m s).2
  if r.errOccurred then (none, { r with errorIndicator := true }) else (some .null, r)

@[irreducible] def oMsg (cls : String) (useMark : Bool) (m : Array Ast → String) :
    Array Ast → Int × Int → PS → Option Ast × PS :=
  fun env _ s => raisedMsg cls useMark (m env) s

/-- `RAISE_SYNTAX_ERROR_STARTING_FROM(a, msg)`: from `a`'s start to the end of the current line
(`-5` is `CURRENT_POS`). -/
def raisedFrom (a : Ast) (m : String) (s : PS) : PS :=
  { (raiseErrorKnownLocation "SyntaxError" (locOf a).lineno (locOf a).colOffset (-5) (-5) m s).2
    with errorIndicator := true }

@[irreducible] def oFrom (i : Nat) (m : String) : Array Ast → Int × Int → PS → Option Ast × PS :=
  fun env _ s => (none, raisedFrom (env.getD i .null) m s)

/-- An action that computes a value without touching the parser: `emit_action`'s
`if (_res == NULL && PyErr_Occurred())` turns a `NULL` into the error return. -/
def pureRes (v : Ast) (s : PS) : Option Ast × PS :=
  if ((!nonNull v || s.errorIndicator) && s.errOccurred) = true then
    (none, { s with errorIndicator := true }) else (some v, s)

@[irreducible] def oPure (v : Array Ast → Ast) : Array Ast → Int × Int → PS → Option Ast × PS :=
  fun env _ s => pureRes (v env) s

/-- `EXTRA` of an alternative that started at `st`: to the end of the last token that is not
`NEWLINE`, `INDENT`, `DEDENT` or `ENDMARKER`. -/
def locFrom (st : Int × Int) (s : PS) : Loc :=
  let e := lastNonWhitespaceToken s
  ⟨st.1, st.2, e.endLineno, e.endColOffset⟩

/-- A node-building action with `EXTRA`. -/
@[irreducible] def oPureX (v : Array Ast → Loc → Ast) : Array Ast → Int × Int → PS → Option Ast × PS :=
  fun env st s => pureRes (v env (locFrom st s)) s

/-- The default action of a one-item alternative: its value. -/
@[irreducible] def oVar0 : Array Ast → Int × Int → PS → Option Ast × PS := fun env _ s => (some (env.getD 0 .null), s)

/-! ### Each action form against `altResult` -/

theorem errOcc_raiseEKL (cls m : String) (a b c d : Int) (s : PS) :
    (raiseErrorKnownLocation cls a b c d m s).2.errOccurred = true :=
  (raises_raiseErrorKnownLocation cls m a b c d).2 s


theorem evalA_ite (env : Array Ast) (ex : Extra) (c a b : AE) (s : PS) :
    evalA env ex (.ite c a b) s =
      if truth (evalA env ex c s).1 then evalA env ex a (evalA env ex c s).2
      else evalA env ex b (evalA env ex c s).2 := by
  simp only [evalA, bind, StateT.bind]
  generalize evalA env ex c s = r
  obtain ⟨v, s'⟩ := r
  by_cases h : truth v = true <;> simp [h]

theorem evalA_kr (env : Array Ast) (ex : Extra) (i j : Nat) (m : String) (s : PS)
    (hm : msgOf [.str (m.toList.map Char.toNat)] = m) :
    evalA env ex (.call .RAISE_SYNTAX_ERROR_KNOWN_RANGE [.var i, .var j, .str m]) s =
      (.null, (raiseErrorKnownLocation "SyntaxError" (locOf (env.getD i .null)).lineno
        (locOf (env.getD i .null)).colOffset (locOf (env.getD j .null)).endLineno
        (locOf (env.getD j .null)).endColOffset m s).2) := by
  simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper, raiseRange,
    List.drop_succ_cons, List.drop_zero, hm, List.getD_cons_zero, List.getD_cons_succ]
  rfl

theorem evalA_kl (env : Array Ast) (ex : Extra) (i : Nat) (m : String) (s : PS)
    (hm : msgOf [.str (m.toList.map Char.toNat)] = m) :
    evalA env ex (.call .RAISE_SYNTAX_ERROR_KNOWN_LOCATION [.var i, .str m]) s =
      (.null, (raiseErrorKnownLocation "SyntaxError" (locOf (env.getD i .null)).lineno
        (locOf (env.getD i .null)).colOffset (locOf (env.getD i .null)).endLineno
        (locOf (env.getD i .null)).endColOffset m s).2) := by
  simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper, raiseRange,
    List.drop_succ_cons, List.drop_zero, hm, List.getD_cons_zero, List.getD_cons_succ]
  rfl

/-- An action whose value is `NULL` with an exception set, whatever `EXTRA` is: the error
return. -/
theorem altResult_raise {a : Alt} {g : Bool} {env : Array Ast} {st : Int × Int} {s s' : PS}
    {act : AE} (h1 : a.action = some act) (h : ∀ ex, evalA env ex act s = (.null, s'))
    (he : s'.errOccurred = true) :
    altResult a g env st s = (none, { s' with errorIndicator := true }) := by
  cases hx : a.extra
  · rw [altResult_plain h1 hx]
    simp only [h, nonNull, he]
    rfl
  · rw [altResult_extra h1 hx]
    simp only [h, nonNull, he]
    rfl

theorem altResult_pure {a : Alt} {g : Bool} {env : Array Ast} {st : Int × Int} {s : PS}
    {act : AE} {v : Ast} (h1 : a.action = some act) (h : ∀ ex, evalA env ex act s = (v, s)) :
    altResult a g env st s = pureRes v s := by
  cases hx : a.extra
  · rw [altResult_plain h1 hx]
    simp only [h]
    rfl
  · rw [altResult_extra h1 hx]
    simp only [h]
    rfl

theorem altResult_pureX {a : Alt} {g : Bool} {env : Array Ast} {st : Int × Int} {s : PS}
    {act : AE} {v : Loc → Ast} (h1 : a.action = some act) (hx : a.extra = true)
    (h : ∀ (el ec : Int), evalA env ⟨st.1, st.2, el, ec⟩ act s = (v ⟨st.1, st.2, el, ec⟩, s)) :
    altResult a g env st s = pureRes (v (locFrom st s)) s := by
  rw [altResult_extra h1 hx]
  simp only [mkExtra, locFrom, h]
  rfl

theorem altResult_kr {a : Alt} {g : Bool} {env : Array Ast} {st : Int × Int} {s : PS}
    {i j : Nat} {m : String}
    (h1 : a.action = some (.call .RAISE_SYNTAX_ERROR_KNOWN_RANGE [.var i, .var j, .str m]))
    (hm : msgOf [.str (m.toList.map Char.toNat)] = m) :
    altResult a g env st s = oKR i j m env st s := by
  rw [altResult_raise h1 (fun ex => evalA_kr env ex i j m s hm) (errOcc_raiseEKL _ _ _ _ _ _ _)]
  unfold oKR
  rfl

theorem altResult_kl {a : Alt} {g : Bool} {env : Array Ast} {st : Int × Int} {s : PS}
    {i : Nat} {m : String}
    (h1 : a.action = some (.call .RAISE_SYNTAX_ERROR_KNOWN_LOCATION [.var i, .str m]))
    (hm : msgOf [.str (m.toList.map Char.toNat)] = m) :
    altResult a g env st s = oKL i m env st s := by
  rw [altResult_raise h1 (fun ex => evalA_kl env ex i m s hm) (errOcc_raiseEKL _ _ _ _ _ _ _)]
  unfold oKL
  rfl

theorem altResult_from {a : Alt} {g : Bool} {env : Array Ast} {st : Int × Int} {s : PS}
    {i : Nat} {m : String}
    (h1 : a.action = some (.call .RAISE_SYNTAX_ERROR_STARTING_FROM [.var i, .str m]))
    (hm : msgOf [.str (m.toList.map Char.toNat)] = m) :
    altResult a g env st s = oFrom i m env st s := by
  rw [altResult_raise h1 (fun ex => by
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper,
      List.drop_succ_cons, List.drop_zero, hm, List.getD_cons_zero, List.getD_cons_succ]
    rfl) (errOcc_raiseEKL _ _ _ _ _ _ _)]
  unfold oFrom
  rfl

/-- `RAISE_SYNTAX_ERROR`, `RAISE_SYNTAX_ERROR_ON_NEXT_TOKEN`, `RAISE_INDENTATION_ERROR` with a
message whose arguments are the action's other arguments. -/
theorem altResult_msg {a : Alt} {g : Bool} {env : Array Ast} {st : Int × Int} {s : PS}
    {h : Helper} {args : List AE} {cls : String} {um : Bool} {m : Array Ast → String}
    (h1 : a.action = some (.call h args))
    (hh : ∀ ex, evalA env ex (.call h args) s = (.null, (raiseError cls um (m env) s).2)) :
    altResult a g env st s = oMsg cls um m env st s := by
  cases hx : a.extra
  · rw [altResult_plain h1 hx]
    unfold oMsg
    simp only [hh, nonNull, raisedMsg]
    split <;> simp_all
  · rw [altResult_extra h1 hx]
    unfold oMsg
    simp only [hh, nonNull, raisedMsg]
    split <;> simp_all

theorem altResult_syn {a : Alt} {g : Bool} {env : Array Ast} {st : Int × Int} {s : PS} {m : String}
    (h1 : a.action = some (.call .RAISE_SYNTAX_ERROR [.str m]))
    (hm : msgOf [.str (m.toList.map Char.toNat)] = m) :
    altResult a g env st s = oMsg "SyntaxError" false (fun _ => m) env st s :=
  altResult_msg h1 (fun ex => by
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper, hm]
    rfl)

theorem altResult_next {a : Alt} {g : Bool} {env : Array Ast} {st : Int × Int} {s : PS} {m : String}
    (h1 : a.action = some (.call .RAISE_SYNTAX_ERROR_ON_NEXT_TOKEN [.str m]))
    (hm : msgOf [.str (m.toList.map Char.toNat)] = m) :
    altResult a g env st s = oMsg "SyntaxError" true (fun _ => m) env st s :=
  altResult_msg h1 (fun ex => by
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper, hm]
    rfl)

theorem altResult_ind {a : Alt} {g : Bool} {env : Array Ast} {st : Int × Int} {s : PS} {m : String}
    (h1 : a.action = some (.call .RAISE_INDENTATION_ERROR [.str m]))
    (hm : msgOf [.str (m.toList.map Char.toNat)] = m) :
    altResult a g env st s = oMsg "IndentationError" false (fun _ => m) env st s :=
  altResult_msg h1 (fun ex => by
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper, hm]
    rfl)

/-- `formatMsg` on text without `%` followed by `%d` and an int. -/
theorem formatMsg_d (n : Int) : ∀ (cs : List Char), '%' ∉ cs →
    formatMsg (cs ++ ['%', 'd']) [.int n] = String.ofList cs ++ toString n
  | [], _ => by simp [formatMsg]
  | c :: cs, h => by
    have hc : c ≠ '%' := fun e => h (e ▸ List.mem_cons_self ..)
    have ih := formatMsg_d n cs (fun e => h (List.mem_cons_of_mem _ e))
    simp only [List.cons_append]
    have : formatMsg (c :: (cs ++ ['%', 'd'])) [.int n] =
        String.singleton c ++ formatMsg (cs ++ ['%', 'd']) [.int n] := by
      rw [formatMsg.eq_def]
      split
      all_goals simp_all
    rw [this, ih]
    simp [String.ofList_cons, String.append_assoc]

theorem map_ofNat_toNat (l : List Char) : l.map (Char.ofNat ∘ Char.toNat) = l := by
  induction l <;> simp_all [Char.ofNat_toNat]

/-- `RAISE_INDENTATION_ERROR("... on line %d", a->lineno)`: the message is the text and the line
of the value `i`. -/
theorem altResult_indLine {a : Alt} {g : Bool} {env : Array Ast} {st : Int × Int} {s : PS}
    {pre : String} {i : Nat}
    (h1 : a.action = some (.call .RAISE_INDENTATION_ERROR [.str (pre ++ "%d"), .attr (.var i) "lineno"]))
    (hp : '%' ∉ pre.toList) :
    altResult a g env st s =
      oMsg "IndentationError" false (fun env => pre ++ toString (locOf (env.getD i .null)).lineno) env st s :=
  altResult_msg h1 (fun ex => by
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper, msgOf,
      attrOf, beq_self_eq_true, ↓reduceIte]
    have e : (cpsStr ((pre ++ "%d").toList.map Char.toNat)).toList = pre.toList ++ ['%', 'd'] := by
      simp [cpsStr, String.toList_append, map_ofNat_toNat]
    rw [e, formatMsg_d _ _ hp, String.ofList_toList]
    rfl)

/-! ### Messages with `_PyPegen_get_expr_name`, invalid targets, default actions -/

theorem formatMsg_plainc (c : Char) (cs : List Char) (as : List Ast) (hc : c ≠ '%') :
    formatMsg (c :: cs) as = String.singleton c ++ formatMsg cs as := by
  rw [formatMsg.eq_def]
  split
  all_goals simp_all

theorem formatMsg_plain : ∀ (cs : List Char), '%' ∉ cs → ∀ as, formatMsg cs as = String.ofList cs
  | [], _, as => by cases as <;> simp [formatMsg]
  | c :: cs, h, as => by
    have hc : c ≠ '%' := fun e => h (e ▸ List.mem_cons_self ..)
    rw [formatMsg_plainc c cs as hc, formatMsg_plain cs (fun e => h (List.mem_cons_of_mem _ e)) as]
    simp [String.ofList_cons]

/-- The piece `PyUnicode_FromFormatV` writes for one conversion. -/
def fmtPiece (k : Char) (a : Ast) : String :=
  match a with
  | .str cs | .ident cs => if k == 'R' then "'" ++ cpsStr cs ++ "'" else cpsStr cs
  | .int i => if k == 'c' then chStr i.toNat else toString i
  | _ => ""

theorem formatMsg_pct : ∀ (cs : List Char) (k : Char) (rest : List Char) (a : Ast) (as : List Ast),
    '%' ∉ cs → k ≠ '%' →
    formatMsg (cs ++ '%' :: k :: rest) (a :: as) =
      String.ofList cs ++ fmtPiece k a ++ formatMsg rest as
  | [], k, rest, a, as, _, hk => by
    simp only [List.nil_append, String.ofList_nil, String.empty_append]
    rw [formatMsg.eq_def]
    split
    · simp_all
    · simp_all
    · rename_i c r a' as' _ h1 h2
      obtain ⟨rfl, rfl⟩ := h1
      obtain ⟨rfl, rfl⟩ := h2
      rfl
    · rename_i h1 h2
      obtain ⟨rfl, rfl⟩ := h1
      first | simp_all | exact absurd rfl (h2 _ _ _ _ rfl rfl) | exact absurd rfl (h2 _ _ _ _ rfl)
  | c :: cs, k, rest, a, as, h, hk => by
    have hc : c ≠ '%' := fun e => h (e ▸ List.mem_cons_self ..)
    rw [List.cons_append, formatMsg_plainc c _ _ hc,
      formatMsg_pct cs k rest a as (fun e => h (List.mem_cons_of_mem _ e)) hk]
    simp [String.ofList_cons, String.append_assoc]

theorem cpsStr_toList (nm : String) : cpsStr (nm.toList.map Char.toNat) = nm := by
  simp [cpsStr, map_ofNat_toNat]

/-- `_PyPegen_get_expr_name` (`Parser/action_helpers.c:1084-1159`) through `callHelper`: the name
of the node's kind, or `NULL` with a `SystemError` set (only a `Slice`, which no rule passes). -/
theorem callHelper_exprName (e : Ast) (s : PS) :
    callHelper .get_expr_name [e] s = match exprName e with
      | some nm => (.str (nm.toList.map Char.toNat), s)
      | none => (.null, (setErr { cls := "SystemError", msg := "unexpected expression in assignment" } s).2) := by
  simp only [callHelper, List.getD_cons_zero]
  cases exprName e <;> rfl

/-- The state `_PyPegen_get_expr_name` leaves when it fails. -/
def exprNameFail (s : PS) : PS :=
  (setErr { cls := "SystemError", msg := "unexpected expression in assignment" } s).2

theorem msg_pct_s (pre post : String) (hp : '%' ∉ pre.toList) (hq : '%' ∉ post.toList) (x : Ast) :
    msgOf [.str ((pre ++ "%s" ++ post).toList.map Char.toNat), x] = pre ++ fmtPiece 's' x ++ post := by
  simp only [msgOf]
  have e : (cpsStr ((pre ++ "%s" ++ post).toList.map Char.toNat)).toList =
      pre.toList ++ '%' :: 's' :: post.toList := by
    simp [cpsStr, String.toList_append, map_ofNat_toNat]
  rw [e, formatMsg_pct _ _ _ _ _ hp (by decide), formatMsg_plain _ hq, String.ofList_toList,
    String.ofList_toList]

/-- `RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, "pre%spost", _PyPegen_get_expr_name(c))` over the
values `i`, `j`, with the name of value `k`; when the name fails, the message has an empty name
and the raise runs over the `SystemError`. -/
@[irreducible] def oKRName (i j k : Nat) (pre post : String) :
    Array Ast → Int × Int → PS → Option Ast × PS :=
  fun env _ s => match exprName (env.getD k .null) with
    | some nm => (none, raisedAt (env.getD i .null) (env.getD j .null) (pre ++ nm ++ post) s)
    | none => (none, raisedAt (env.getD i .null) (env.getD j .null) (pre ++ post) (exprNameFail s))

theorem altResult_krName {a : Alt} {g : Bool} {env : Array Ast} {st : Int × Int} {s : PS}
    {i j k : Nat} {pre post : String}
    (h1 : a.action = some (.call .RAISE_SYNTAX_ERROR_KNOWN_RANGE
      [.var i, .var j, .str (pre ++ "%s" ++ post), .call .get_expr_name [.var k]]))
    (hp : '%' ∉ pre.toList) (hq : '%' ∉ post.toList) :
    altResult a g env st s = oKRName i j k pre post env st s := by
  unfold oKRName
  cases hn : exprName (env.getD k .null) with
  | some nm =>
    rw [altResult_raise h1 (fun ex => by
      simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper_exprName,
        hn]
      simp only [callHelper, raiseRange, List.drop_succ_cons, List.drop_zero, List.getD_cons_zero,
        List.getD_cons_succ, msg_pct_s pre post hp hq, fmtPiece, cpsStr_toList]
      rfl) (errOcc_raiseEKL _ _ _ _ _ _ _)]
    rfl
  | none =>
    rw [altResult_raise h1 (fun ex => by
      simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper_exprName,
        hn]
      simp only [callHelper, raiseRange, List.drop_succ_cons, List.drop_zero, List.getD_cons_zero,
        List.getD_cons_succ, msg_pct_s pre post hp hq, fmtPiece, String.append_empty]
      rfl) (errOcc_raiseEKL _ _ _ _ _ _ _)]
    rfl

/-- `RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "pre%spost", _PyPegen_get_expr_name(a))`. -/
@[irreducible] def oKLName (i : Nat) (pre post : String) :
    Array Ast → Int × Int → PS → Option Ast × PS :=
  fun env _ s => match exprName (env.getD i .null) with
    | some nm => (none, raisedAt (env.getD i .null) (env.getD i .null) (pre ++ nm ++ post) s)
    | none => (none, raisedAt (env.getD i .null) (env.getD i .null) (pre ++ post) (exprNameFail s))

theorem altResult_klName {a : Alt} {g : Bool} {env : Array Ast} {st : Int × Int} {s : PS}
    {i : Nat} {pre post : String}
    (h1 : a.action = some (.call .RAISE_SYNTAX_ERROR_KNOWN_LOCATION
      [.var i, .str (pre ++ "%s" ++ post), .call .get_expr_name [.var i]]))
    (hp : '%' ∉ pre.toList) (hq : '%' ∉ post.toList) :
    altResult a g env st s = oKLName i pre post env st s := by
  unfold oKLName
  cases hn : exprName (env.getD i .null) with
  | some nm =>
    rw [altResult_raise h1 (fun ex => by
      simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper_exprName,
        hn]
      simp only [callHelper, raiseRange, List.drop_succ_cons, List.drop_zero, List.getD_cons_zero,
        List.getD_cons_succ, msg_pct_s pre post hp hq, fmtPiece, cpsStr_toList]
      rfl) (errOcc_raiseEKL _ _ _ _ _ _ _)]
    rfl
  | none =>
    rw [altResult_raise h1 (fun ex => by
      simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper_exprName,
        hn]
      simp only [callHelper, raiseRange, List.drop_succ_cons, List.drop_zero, List.getD_cons_zero,
        List.getD_cons_succ, msg_pct_s pre post hp hq, fmtPiece, String.append_empty]
      rfl) (errOcc_raiseEKL _ _ _ _ _ _ _)]
    rfl

/-- `RAISE_SYNTAX_ERROR_INVALID_TARGET(type, e)` (`Parser/pegen.h:245-264`) on the value `i`, `k`
the `TARGETS_TYPE` (0 `STAR_TARGETS`, 1 `DEL_TARGETS`, 2 `FOR_TARGETS`): the first invalid
target `t` of `e` (`_PyPegen_get_invalid_target`) gives "cannot assign to <name of t>" (or
"cannot delete" for `DEL_TARGETS`) over `t`; with none, the action's `NULL` without an exception
is the result. -/
def targetMsg (k : Nat) (t : Ast) : String :=
  if k == 0 || k == 2 then s!"cannot assign to {(exprName t).getD ""}"
  else s!"cannot delete {(exprName t).getD ""}"

@[irreducible] def oTarget (k i : Nat) : Array Ast → Int × Int → PS → Option Ast × PS :=
  fun env _ s => match invalidTarget k 100000 (env.getD i .null) with
    | .null => pureRes .null s
    | t => (none, raisedAt t t (targetMsg k t) s)

theorem altResult_target {a : Alt} {g : Bool} {env : Array Ast} {st : Int × Int} {s : PS}
    {k i : Nat} (h1 : a.action = some (.call .RAISE_SYNTAX_ERROR_INVALID_TARGET [.int k, .var i])) :
    altResult a g env st s = oTarget k i env st s := by
  unfold oTarget
  have hk : ((k : Int) == 0 || (k : Int) == 2) = (k == 0 || k == 2) := by
    by_cases h0 : k = 0
    · subst h0; rfl
    · by_cases h2 : k = 2
      · subst h2; rfl
      · rw [show ((k : Int) == 0) = false by simp; omega, show ((k : Int) == 2) = false by simp; omega,
          show (k == 0) = false by simp; omega, show (k == 2) = false by simp; omega]
  generalize ht : invalidTarget k 100000 (env.getD i .null) = t
  by_cases hn : t = .null
  · subst hn
    rw [altResult_pure h1 (fun ex => by
      simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper,
        List.getD_cons_zero, List.getD_cons_succ, Int.toNat_natCast, ht]
      rfl)]
  · rw [altResult_raise (s' := (raiseRange "SyntaxError" t t (targetMsg k t) s).2) h1 (fun ex => by
      simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper,
        List.getD_cons_zero, List.getD_cons_succ, Int.toNat_natCast, hk, ht]
      cases t <;> first | contradiction | rfl) (errOcc_raiseEKL _ _ _ _ _ _ _)]
    cases t <;> first | contradiction | rfl

/-- The default action of an alternative with several items: the dummy `_PyPegen_dummy_name`
result (`(void*)1` in `emit_default_action`). -/
@[irreducible] def oDummy : Array Ast → Int × Int → PS → Option Ast × PS :=
  fun _ _ s => (some (rec_ .PDummy []), s)

theorem altResult_dummy {a : Alt} {env : Array Ast} {st : Int × Int} {s : PS}
    (h1 : a.action = none) (h2 : 1 < a.nvars) : altResult a false env st s = oDummy env st s := by
  unfold oDummy
  simp only [altResult, h1, h2, ↓reduceIte, Bool.false_eq_true]
  rfl

/-- An action that is one of the values: `{ a }`. -/
@[irreducible] def oVar (i : Nat) : Array Ast → Int × Int → PS → Option Ast × PS :=
  fun env _ s => pureRes (env.getD i .null) s

theorem altResult_var {a : Alt} {g : Bool} {env : Array Ast} {st : Int × Int} {s : PS} {i : Nat}
    (h1 : a.action = some (.var i)) : altResult a g env st s = oVar i env st s := by
  unfold oVar
  exact altResult_pure h1 (fun _ => rfl)

theorem altResult_p {a : Alt} {g : Bool} {env : Array Ast} {st : Int × Int} {s : PS}
    {act : AE} {v : Array Ast → Ast} (h1 : a.action = some act) (h : ∀ ex, evalA env ex act s = (v env, s)) :
    altResult a g env st s = oPure v env st s := by
  unfold oPure
  exact altResult_pure h1 h

theorem altResult_x {a : Alt} {g : Bool} {env : Array Ast} {st : Int × Int} {s : PS}
    {act : AE} {v : Array Ast → Loc → Ast} (h1 : a.action = some act) (hx : a.extra = true)
    (h : ∀ (el ec : Int), evalA env ⟨st.1, st.2, el, ec⟩ act s = (v env ⟨st.1, st.2, el, ec⟩, s)) :
    altResult a g env st s = oPureX v env st s := by
  unfold oPureX
  exact altResult_pureX h1 hx h

/-- An action that computes a value and a state: `emit_action`'s check on what it returned. -/
theorem altResult_pure2 {a : Alt} {g : Bool} {env : Array Ast} {st : Int × Int} {s s' : PS}
    {act : AE} {v : Ast} (h1 : a.action = some act) (h : ∀ ex, evalA env ex act s = (v, s')) :
    altResult a g env st s = pureRes v s' := by
  cases hx : a.extra
  · rw [altResult_plain h1 hx]
    simp only [h]
    rfl
  · rw [altResult_extra h1 hx]
    simp only [h]
    rfl

/-- `RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, msg)` over two computed endpoints. -/
theorem altResult_krv {a : Alt} {g : Bool} {env : Array Ast} {st : Int × Int} {s : PS}
    {ea eb : AE} {va vb : Ast} {m : String}
    (h1 : a.action = some (.call .RAISE_SYNTAX_ERROR_KNOWN_RANGE [ea, eb, .str m]))
    (ha : ∀ ex, evalA env ex ea s = (va, s)) (hb : ∀ ex, evalA env ex eb s = (vb, s))
    (hm : msgOf [.str (m.toList.map Char.toNat)] = m) :
    altResult a g env st s = (none, raisedAt va vb m s) := by
  rw [altResult_raise h1 (fun ex => by
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, ha, hb, callHelper,
      raiseRange, List.drop_succ_cons, List.drop_zero, hm, List.getD_cons_zero, List.getD_cons_succ]
    rfl) (errOcc_raiseEKL _ _ _ _ _ _ _)]
  rfl

/-- An action that calls a helper with a state: `emit_action`'s check on its value and state. -/
@[irreducible] def oState (v : Array Ast → PS → Ast × PS) : Array Ast → Int × Int → PS → Option Ast × PS :=
  fun env _ s => pureRes (v env s).1 (v env s).2

theorem altResult_s {a : Alt} {g : Bool} {env : Array Ast} {st : Int × Int} {s : PS}
    {act : AE} {v : Array Ast → PS → Ast × PS} (h1 : a.action = some act)
    (h : ∀ ex, evalA env ex act s = v env s) : altResult a g env st s = oState v env st s := by
  unfold oState
  exact altResult_pure2 h1 (fun ex => (h ex).trans rfl)

/-- The same with `EXTRA`. -/
@[irreducible] def oStateX (v : Array Ast → Loc → PS → Ast × PS) :
    Array Ast → Int × Int → PS → Option Ast × PS :=
  fun env st s => pureRes (v env (locFrom st s) s).1 (v env (locFrom st s) s).2

theorem altResult_sx {a : Alt} {g : Bool} {env : Array Ast} {st : Int × Int} {s : PS}
    {act : AE} {v : Array Ast → Loc → PS → Ast × PS} (h1 : a.action = some act) (hx : a.extra = true)
    (h : ∀ (el ec : Int), evalA env ⟨st.1, st.2, el, ec⟩ act s = v env ⟨st.1, st.2, el, ec⟩ s) :
    altResult a g env st s = oStateX v env st s := by
  unfold oStateX
  rw [altResult_extra h1 hx]
  simp only [mkExtra, locFrom, h]
  rfl

/-- `PyErr_Occurred() ? NULL : RAISE_SYNTAX_ERROR_ON_NEXT_TOKEN(msg)`: with an exception already
set, the action's `NULL` (an error return); otherwise the raise at the token under the mark. -/
@[irreducible] def oNextIf (m : String) : Array Ast → Int × Int → PS → Option Ast × PS :=
  fun _ _ s => if s.errOccurred then pureRes .null s else raisedMsg "SyntaxError" true m s

theorem altResult_nextIf {a : Alt} {g : Bool} {env : Array Ast} {st : Int × Int} {s : PS} {m : String}
    (h1 : a.action = some (.ite (.call .PyErr_Occurred []) .null
      (.call .RAISE_SYNTAX_ERROR_ON_NEXT_TOKEN [.str m])))
    (hm : msgOf [.str (m.toList.map Char.toNat)] = m) :
    altResult a g env st s = oNextIf m env st s := by
  unfold oNextIf
  have hp : ∀ ex, evalA env ex (.call .PyErr_Occurred []) s =
      (.int (if s.errOccurred then 1 else 0), s) := fun _ => rfl
  cases hs : s.errOccurred
  · rw [altResult_pure2 (v := .null) (s' := (raiseError "SyntaxError" true m s).2) h1 (fun ex => by
      rw [evalA_ite, hp, hs]
      simp only [Bool.false_eq_true, ↓reduceIte, truth, evalA, evalA.evalList, bind, StateT.bind, pure,
        StateT.pure, callHelper, hm]
      rfl)]
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold raisedMsg pureRes
    generalize (raiseError "SyntaxError" true m s).2 = r
    cases hr : r.errOccurred <;> simp [nonNull, hr]
  · rw [altResult_pure2 (v := .null) (s' := s) h1 (fun ex => by
      rw [evalA_ite, hp, hs]
      rfl)]
    rfl

theorem altResult_none1' {a : Alt} {g : Bool} {env : Array Ast} {st : Int × Int} {s : PS}
    (h1 : a.action = none) (h2 : a.nvars = 1) : altResult a g env st s = oVar0 env st s := by
  rw [altResult_none1 h1 h2]
  unfold oVar0
  rfl


/-! ### Groups of single tokens -/

/-- A one-token alternative with the default action. -/
def tokAlt0 (k : Nat) : Alt :=
  { items := [.call (.tok k)], action := none, nvars := 1, guardInvalid := false, extra := false }

/-- `_tmp_n: 'a' | 'b' | ...`, a group of single tokens with the default action: the token
under the mark if its type is in `ts` (the mark past it), otherwise `NULL` with the state the
entry read left. -/
def TokGroup (id : Nat) (ts : List Nat) : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  (t.type ∈ ts → callRule (f + ts.length + 5) id p = (.tok t, { q with mark := p.mark + 1 }.leave)) ∧
  (t.type ∉ ts → callRule (f + ts.length + 5) id p = (.null, q.leave))

theorem alts_tokGroup (st : Int × Int) : ∀ (l : List Nat) (f : Nat) (s : PS),
    s.mark < s.fill → s.errorIndicator = false →
    runAlts (f + l.length + 3) (l.map tokAlt0) false s.mark st s =
      if (s.tokenAt s.mark).type ∈ l then (some (.tok (s.tokenAt s.mark)), { s with mark := s.mark + 1 })
      else (some .null, s)
  | [], f, s, _, _ => by
    simp only [List.map_nil, List.length_nil, Nat.add_zero, List.not_mem_nil, ↓reduceIte]
    rw [show f + 3 = (f + 2) + 1 from rfl, alts_nil]
  | k :: rest, f, s, hlt, he => by
    rw [List.map_cons, show f + (k :: rest).length + 3 = (f + rest.length + 3) + 1 by simp; omega]
    by_cases hk : (s.tokenAt s.mark).type = k
    · have e1 : runCall (f + rest.length + 2) (.tok k) s =
          (.tok (s.tokenAt s.mark), { s with mark := s.mark + 1 }) := by
        rw [show f + rest.length + 2 = (f + rest.length + 1) + 1 from rfl, call_tok,
          expectToken_at _ _ hlt, ite_t hk]
      rw [alts_ok (by rfl) he (by
        show runItems (f + rest.length + 3) [.call (.tok k)] #[] false s = _
        rw [show f + rest.length + 3 = (f + rest.length + 2) + 1 from rfl, items_call e1 (by simp),
          items_nil])]
      rw [altResult_none1 rfl rfl]
      simp [hk]
    · have e1 : runCall (f + rest.length + 2) (.tok k) s = (.null, s) := by
        rw [show f + rest.length + 2 = (f + rest.length + 1) + 1 from rfl, call_tok,
          expectToken_at _ _ hlt, ite_f hk]
      rw [alts_fail (by rfl) he (by
        show runItems (f + rest.length + 3) [.call (.tok k)] #[] false s = _
        rw [show f + rest.length + 3 = (f + rest.length + 2) + 1 from rfl, items_call_null e1])]
      have hs : { s with mark := s.mark } = s := rfl
      rw [hs, alts_tokGroup st rest f s hlt he]
      simp [hk]

theorem tokGroup_of {id : Nat} {ts : List Nat}
    (hne : ts ≠ [])
    (hr : ruleOf id = Rule.mk (ruleOf id).name .normal false false false false false (ts.map tokAlt0)) :
    TokGroup id ts := by
  intro f p q h
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  have he' : p.enter.errorIndicator = false := h.ei
  have hq : { q with mark := p.mark } = q := by rw [← hm]
  have hlt' : q.mark < q.fill := hm ▸ hlt
  rw [callRule_plain (by rw [hr]) (by rw [hr]) (by rw [hr]) (by rw [hr]) (by rw [hr]) h.ei h.level, hr]
  dsimp only
  cases ts with
  | nil => exact absurd rfl hne
  | cons k rest =>
    have e1 : runCall (f + rest.length + 2) (.tok k) p.enter = if (q.tokenAt p.mark).type = k then
        (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) else (.null, q) := by
      rw [show f + rest.length + 2 = (f + rest.length + 1) + 1 from rfl, call_tok, expect_entered h]
    rw [List.map_cons, show f + (k :: rest).length + 3 = (f + rest.length + 3) + 1 by simp; omega]
    by_cases hk : (q.tokenAt p.mark).type = k
    · rw [alts_ok (by rfl) he' (by
        show runItems (f + rest.length + 3) [.call (.tok k)] #[] false p.enter = _
        rw [show f + rest.length + 3 = (f + rest.length + 2) + 1 from rfl, items_call (by rw [e1, ite_t hk])
          (by simp), items_nil])]
      rw [altResult_none1 rfl rfl]
      simp [hk]
    · rw [alts_fail (by rfl) he' (by
        show runItems (f + rest.length + 3) [.call (.tok k)] #[] false p.enter = _
        rw [show f + rest.length + 3 = (f + rest.length + 2) + 1 from rfl,
          items_call_null (by rw [e1, ite_f hk])]), hq]
      have := alts_tokGroup (0, 0) rest f q hlt' he
      rw [hm] at this
      rw [this]
      by_cases hr' : (q.tokenAt p.mark).type ∈ rest
      · simp [hr', hm]
      · simp [hr', hk]

theorem altsAre_nil : AltsAre [] [] := trivial

theorem altsAre_cons {a : Alt} {x : SAlt} {as : List Alt} {xs : List SAlt}
    (h1 : a.items = x.items) (h2 : a.guardInvalid = x.inv)
    (h3 : ∀ env st s, altResult a false env st s = x.out env st s) (h : AltsAre as xs) :
    AltsAre (a :: as) (x :: xs) := ⟨⟨h1, h2, h3⟩, h⟩

/-- Close the `AltsAre` goal of a statement alternative by alternative, each action by the
lemma for its form; actions of another form are left as goals. -/
macro "spec_alts" : tactic => `(tactic| (
  repeat' (first | exact altsAre_nil | apply altsAre_cons rfl rfl)
  all_goals first
    | (intro _ _ _; exact altResult_kl rfl (by decide +kernel))
    | (intro _ _ _; exact altResult_kr rfl (by decide +kernel))
    | (intro _ _ _; exact altResult_from rfl (by decide +kernel))
    | (intro _ _ _; exact altResult_syn rfl (by decide +kernel))
    | (intro _ _ _; exact altResult_next rfl (by decide +kernel))
    | (intro _ _ _; exact altResult_ind rfl (by decide +kernel))
    | (intro _ _ _; exact altResult_indLine rfl (by decide +kernel))
    | (intro _ _ _; exact altResult_none1' rfl rfl)
    | (intro _ _ _; exact altResult_krName rfl (by decide +kernel) (by decide +kernel))
    | (intro _ _ _; exact altResult_klName rfl (by decide +kernel) (by decide +kernel))
    | (intro _ _ _; exact altResult_target rfl)
    | (intro _ _ _; exact altResult_dummy rfl (by decide))
    | (intro _ _ _; exact altResult_var rfl)
    | (intro _ _ _; exact altResult_p rfl (fun _ => rfl))
    | (intro _ _ _; exact altResult_x rfl rfl (fun _ _ => rfl))
    | (intro _ _ _; exact altResult_krv rfl (fun _ => rfl) (fun _ => rfl) (by decide +kernel))
    | (intro _ _ _; exact altResult_pure2 rfl (fun _ => rfl))
    | (intro _ _ _; exact altResult_s rfl (fun _ => rfl))
    | (intro _ _ _; exact altResult_sx rfl rfl (fun _ _ => rfl))
    | (intro _ _ _; exact altResult_nextIf rfl (by decide +kernel))
    | skip))

/-! ### Rules without `EXTRA` -/

/-- A rule function without `EXTRA`, not `(memo)`, not left-recursive: from any entry state (no
error, below `MAXSTACK`), its result is that of its alternatives `xs`, run from the state after
`p->level++`, with `p->level--` at the end. -/
def PlainSpec (id : Nat) (xs : List SAlt) : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false →
  p.level ≠ MAXSTACK → callRule (f + 2) id p = finish (specAlts f xs p.mark (0, 0) p.enter)

/-- `RAISE_SYNTAX_ERROR(msg)` with a fixed message. -/
abbrev oSyn (m : String) := oMsg "SyntaxError" false (fun _ => m)

/-- `RAISE_INDENTATION_ERROR("<pre>%d", a->lineno)`, `a` the value `i`. -/
abbrev oIndent (pre : String) (i : Nat) :=
  oMsg "IndentationError" false (fun env => pre ++ toString (locOf (env.getD i .null)).lineno)

/-- Prove a `PlainSpec`: the entry, then each alternative against the data. -/
macro "plain_spec" : tactic => `(tactic| (
  intro f p he hl
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  refine congrArg finish (runAlts_spec f _ _ ?_ _ _ _)
  spec_alts))

/-! ### Rules with `EXTRA` -/

/-- A rule function with `EXTRA`, not `(memo)`, not left-recursive: from an entry state where the
token under the mark is read into `q`, the result of its alternatives `xs` from `q`, with the
start location of that token. -/
def ExtraSpec (id : Nat) (xs : List SAlt) : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  callRule (f + 2) id p =
    finish (specAlts f xs p.mark ((q.tokenAt p.mark).lineno, (q.tokenAt p.mark).colOffset) q)

/-- Prove an `ExtraSpec`. -/
macro "extra_spec" : tactic => `(tactic| (
  intro f p q h
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  refine congrArg finish (runAlts_spec f _ _ ?_ _ _ _)
  spec_alts))

/-- A `_without_invalid` rule function with `EXTRA` (`callRule` turns `call_invalid_rules` off
around it and puts it back): from an entry state with the flag off and the token under the mark
read into `q`, the result of its alternatives, the flag restored. -/
def NoInvExtraSpec (id : Nat) (xs : List SAlt) : Prop := ∀ (f : Nat) (p q : PS),
  Entered { p with callInvalidRules := false } q →
  callRule (f + 2) id p =
    let a := finish (specAlts f xs p.mark ((q.tokenAt p.mark).lineno, (q.tokenAt p.mark).colOffset) q)
    (a.1, { a.2 with callInvalidRules := p.callInvalidRules })

theorem callRule_noinv_extra {f id : Nat} {p q : PS}
    (h1 : (ruleOf id).leftRec = false) (h2 : (ruleOf id).withoutInvalid = true)
    (h3 : (ruleOf id).memo = false) (h4 : (ruleOf id).kind = .normal) (h5 : (ruleOf id).extra = true)
    (h : Entered { p with callInvalidRules := false } q) :
    callRule (f + 2) id p =
      let a := runAlts f (ruleOf id).alts false p.mark
        ((q.tokenAt p.mark).lineno, (q.tokenAt p.mark).colOffset) q
      (a.1.getD .null, { a.2.leave with callInvalidRules := p.callInvalidRules }) := by
  have he' : ({ p with callInvalidRules := false } : PS).enter.errorIndicator = false := h.ei
  have hp : rulePrologue id (ruleOf id) { p with callInvalidRules := false } =
      (.inr (p.mark, ((q.tokenAt p.mark).lineno, (q.tokenAt p.mark).colOffset)), q) := by
    simp only [rulePrologue, addLevel_ok _ h.level, he', h3, Bool.false_eq_true, ↓reduceIte,
      ruleStart, h5, startLocation, h.read, Bool.not_true]
    rfl
  simp only [callRule, h1, h2, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  simp only [ruleBody, hp, h4, retLevel_eq]
  have hg : (RuleKind.normal == RuleKind.gather) = false := rfl
  simp only [hg, h3, Bool.false_eq_true, ↓reduceIte]
  split <;> simp_all [PS.leave]

/-! ### `(memo)` rules without `EXTRA` -/

/-- A `(memo)` rule function without `EXTRA`, at a position with no memo entry for it yet: the
memo lookup reads the token under the mark into `q`; the result of the alternatives from `q` is
memoized (`memoDone`). -/
def MemoSpec (id : Nat) (xs : List SAlt) : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  (q.memo.getD p.mark []).find? (fun m => m.1 == 1000 + id) = none →
  callRule (f + 2) id p = memoDone p.mark id (specAlts f xs p.mark (0, 0) q)

macro "memo_spec" : tactic => `(tactic| (
  intro f p q h hn
  rw [callRule_memo_plain rfl rfl rfl rfl rfl h hn]
  refine congrArg (memoDone p.mark _) (runAlts_spec f _ _ ?_ _ _ _)
  spec_alts))

/-- A `(memo)` rule function with `EXTRA`, at a position with no memo entry for it yet. -/
def MemoExtraSpec (id : Nat) (xs : List SAlt) : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  (q.memo.getD p.mark []).find? (fun m => m.1 == 1000 + id) = none →
  callRule (f + 2) id p = memoDone p.mark id
    (specAlts f xs p.mark ((q.tokenAt p.mark).lineno, (q.tokenAt p.mark).colOffset) q)

macro "memo_extra_spec" : tactic => `(tactic| (
  intro f p q h hn
  rw [callRule_memo_extra rfl rfl rfl rfl rfl h hn]
  refine congrArg (memoDone p.mark _) (runAlts_spec f _ _ ?_ _ _ _)
  spec_alts))

end PyLean.PyGrammar.Peg
