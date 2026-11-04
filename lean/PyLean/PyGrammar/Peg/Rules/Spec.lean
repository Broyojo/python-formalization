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
    | skip))

end PyLean.PyGrammar.Peg
