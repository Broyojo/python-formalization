import PyLean.PyGrammar.Peg.Rules.Base

/-! `augassign` (`Grammar/python.gram:170-183`), a choice among single tokens. -/

namespace PyLean.PyGrammar.Peg

open Lexer

/-- A one-token alternative with a plain action. -/
def tokAlt (k : Nat) (act : AE) : Alt :=
  { items := [.call (.tok k)], action := some act, nvars := 1, guardInvalid := false, extra := false }

/-- Ordered choice among one-token alternatives: the first whose token is under the mark. -/
theorem alts_tokTable (st : Int × Int) : ∀ (l : List (Nat × AE)) (f : Nat) (s : PS),
    l.length + 3 ≤ f → s.mark < s.fill → s.errorIndicator = false →
    runAlts f (l.map fun x => tokAlt x.1 x.2) false s.mark st s =
      match l.find? (fun x => x.1 == (s.tokenAt s.mark).type) with
      | some x => altResult (tokAlt x.1 x.2) false #[.tok (s.tokenAt s.mark)] st
          { s with mark := s.mark + 1 }
      | none => (some .null, s)
  | [], f, s, hf, _, _ => by
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp at hf; omega⟩
    rw [List.map_nil, alts_nil]
    rfl
  | (k, act) :: rest, f, s, hf, hlt, he => by
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 3 := ⟨f - 3, by simp at hf; omega⟩
    rw [List.map_cons]
    by_cases hk : (s.tokenAt s.mark).type = k
    · have e1 : runCall (g + 1) (.tok k) s = (.tok (s.tokenAt s.mark), { s with mark := s.mark + 1 }) := by
        rw [call_tok, expectToken_at _ _ hlt, ite_t hk]
      rw [alts_ok (by rfl) he (by
        show runItems (g + 2) [.call (.tok k)] #[] false s = _
        rw [items_call e1 (by simp), items_nil])]
      simp [List.find?, hk]
    · have e1 : runCall (g + 1) (.tok k) s = (.null, s) := by
        rw [call_tok, expectToken_at _ _ hlt, ite_f hk]
      rw [alts_fail (by rfl) he (by
        show runItems (g + 2) [.call (.tok k)] #[] false s = _
        rw [items_call_null e1])]
      have hs : { s with mark := s.mark } = s := rfl
      rw [hs, alts_tokTable st rest (g + 2) s (by simp at hf ⊢; omega) hlt he]
      have : (k == (s.tokenAt s.mark).type) = false := by simp; omega
      simp [List.find?, this]

/-- The operator of each augmented assignment token (`Grammar/python.gram:170-183`). -/
def augOp : Nat → Option Ctor
  | 36 => some .Add | 37 => some .Sub | 38 => some .Mult | 50 => some .MatMult
  | 39 => some .Div | 40 => some .Mod | 41 => some .BitAnd | 42 => some .BitOr
  | 43 => some .BitXor | 44 => some .LShift | 45 => some .RShift | 46 => some .Pow
  | 48 => some .FloorDiv | _ => none

/-- `augassign`: at an augmented assignment token, `_PyPegen_augoperator(p, Op)` for its operator
and the token taken; `@=` under a `feature_version` below 5 fails `CHECK_VERSION`: `NULL`,
`error_indicator` set, and the exception `_PyPegen_raise_error` sets for "The '@' operator is only
supported in Python 3.5 and greater"; at any other token `NULL`. -/
def AugAssign : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  let s1 := { q with mark := p.mark + 1 }
  (augOp t.type = none → callRule (f + 18) 13 p = (.null, q.leave)) ∧
  (∀ c, augOp t.type = some c → (c = .MatMult → 5 ≤ p.featureVersion) →
    callRule (f + 18) 13 p = (rec_ .PAugOperator [opNode c], s1.leave)) ∧
  (augOp t.type = some .MatMult → p.featureVersion < 5 →
    (callRule (f + 18) 13 p).1 = .null ∧ (callRule (f + 18) 13 p).2.errorIndicator = true ∧
    (callRule (f + 18) 13 p).2.tok = (raiseError0 "SyntaxError"
      "The '@' operator is only supported in Python 3.5 and greater"
      { s1 with errorIndicator := true }).2.tok)

/-- The alternatives of `augassign` in the grammar data's order, as a table. -/
def augTable : List (Nat × AE) :=
  [(36, .call .augoperator [.ctor .Add]), (37, .call .augoperator [.ctor .Sub]),
   (38, .call .augoperator [.ctor .Mult]),
   (50, .checkVersion (.int 5) (.str "The '@' operator is") (.call .augoperator [.ctor .MatMult])),
   (39, .call .augoperator [.ctor .Div]), (40, .call .augoperator [.ctor .Mod]),
   (41, .call .augoperator [.ctor .BitAnd]), (42, .call .augoperator [.ctor .BitOr]),
   (43, .call .augoperator [.ctor .BitXor]), (44, .call .augoperator [.ctor .LShift]),
   (45, .call .augoperator [.ctor .RShift]), (46, .call .augoperator [.ctor .Pow]),
   (48, .call .augoperator [.ctor .FloorDiv])]

theorem r13_alts : r13.alts = augTable.map fun x => tokAlt x.1 x.2 := rfl

theorem aug_plain (k : Nat) (c : Ctor) (t : Token) (s : PS) (he : s.errorIndicator = false) :
    altResult (tokAlt k (.call .augoperator [.ctor c])) false #[.tok t] (0, 0) s =
      (some (rec_ .PAugOperator [opNode c]), s) := by
  rw [altResult_plain rfl rfl]
  simp [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper, nonNull, he, rec_]

theorem augAssign_proven : AugAssign := by
  intro f p q h
  obtain ⟨he, -, -, hfv, hm, hlt, -⟩ := h.facts
  have hlt' : q.mark < q.fill := hm ▸ hlt
  have he' : p.enter.errorIndicator = false := h.ei
  have hq : { q with mark := p.mark } = q := by rw [← hm]
  rw [callRule_plain rfl rfl rfl rfl rfl h.ei h.level]
  simp only [show ruleOf 13 = r13 from rfl, r13_alts]
  have key : runAlts (f + 16) (augTable.map fun x => tokAlt x.1 x.2) false p.mark (0, 0) p.enter =
      match augTable.find? (fun x => x.1 == (q.tokenAt p.mark).type) with
      | some x => altResult (tokAlt x.1 x.2) false #[.tok (q.tokenAt p.mark)] (0, 0)
          { q with mark := p.mark + 1 }
      | none => (some .null, q) := by
    rw [show augTable = (36, .call .augoperator [.ctor .Add]) :: augTable.tail from rfl,
      List.map_cons]
    by_cases hk : (q.tokenAt p.mark).type = 36
    · have e1 : runCall (f + 14) (.tok 36) p.enter =
          (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) := by
        rw [call_tok, expect_entered h, ite_t hk]
      rw [alts_ok (by rfl) he' (by
        show runItems (f + 15) [.call (.tok 36)] #[] false p.enter = _
        rw [items_call e1 (by simp), items_nil])]
      simp [List.find?, hk]
    · have e1 : runCall (f + 14) (.tok 36) p.enter = (.null, q) := by
        rw [call_tok, expect_entered h, ite_f hk]
      rw [alts_fail (by rfl) he' (by
        show runItems (f + 15) [.call (.tok 36)] #[] false p.enter = _
        rw [items_call_null e1]), hq]
      have := alts_tokTable (0, 0) augTable.tail (f + 15) q (by simp [augTable]) hlt' he
      rw [hm] at this
      rw [this]
      have hb : (36 == (q.tokenAt p.mark).type) = false := by simp; omega
      simp [List.find?, hb]
  rw [key]
  generalize hn : (q.tokenAt p.mark).type = n
  refine ⟨fun hc => ?_, fun c hc hv => ?_, fun hc hv => ?_⟩
  · have : augTable.find? (fun x => x.1 == n) = none := by
      rw [List.find?_eq_none]
      intro x hx hxe
      simp only [augTable, List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      · simp only [beq_iff_eq] at hxe
        subst hxe
        simp [augOp] at hc
    rw [this, ← hq]
    rfl
  · have hs1 : ({ q with mark := p.mark + 1 } : PS).errorIndicator = false := he
    unfold augOp at hc
    split at hc <;> (try simp at hc) <;> subst hc <;>
      simp only [augTable, List.find?, beq_self_eq_true, Nat.reduceBEq, Bool.false_eq_true]
    all_goals first
      | rw [aug_plain _ _ _ _ hs1]; rfl
      | skip
    have h5 : ¬ ((({ q with mark := p.mark + 1 } : PS).featureVersion : Int) < 5) := by
      show ¬ ((q.featureVersion : Int) < 5)
      have := hv rfl
      omega
    rw [altResult_plain rfl rfl]
    simp [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper, nonNull, he,
      rec_, get, getThe, MonadStateOf.get, StateT.get, h5]
  · rw [show n = 50 by unfold augOp at hc; split at hc <;> simp_all]
    simp only [augTable, List.find?, Nat.reduceBEq, beq_self_eq_true]
    rw [altResult_plain rfl rfl]
    have h5 : (({ q with mark := p.mark + 1 } : PS).featureVersion : Int) < 5 := by
      show (q.featureVersion : Int) < 5
      omega
    have hE : evalA #[.tok (q.tokenAt p.mark)] {}
        (.checkVersion (.int 5) (.str "The '@' operator is") (.call .augoperator [.ctor .MatMult]))
        { q with mark := p.mark + 1 } =
        (.null, (raiseError0 "SyntaxError"
        "The '@' operator is only supported in Python 3.5 and greater"
          { ({ q with mark := p.mark + 1 } : PS) with errorIndicator := true }).2) := by
      have hmsg : toString (cpsStr ("The '@' operator is".toList.map Char.toNat)) ++
          toString " only supported in Python 3." ++ toString (5 : Int) ++ toString " and greater" =
          "The '@' operator is only supported in Python 3.5 and greater" := by decide +kernel
      simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper, rec_,
        get, getThe, MonadStateOf.get, StateT.get]
      rw [ite_t h5]
      simp only [hmsg]
      rfl
    simp only [tokAlt] at hE
    rw [hE]
    have hei := (frame_raiseError0 "SyntaxError"
        "The '@' operator is only supported in Python 3.5 and greater"
      { ({ q with mark := p.mark + 1 } : PS) with errorIndicator := true }).grows.err rfl
    generalize raiseError0 "SyntaxError"
        "The '@' operator is only supported in Python 3.5 and greater"
      { ({ q with mark := p.mark + 1 } : PS) with errorIndicator := true } = r at hei ⊢
    dsimp only
    split <;> simp [hei, PS.leave]

end PyLean.PyGrammar.Peg
