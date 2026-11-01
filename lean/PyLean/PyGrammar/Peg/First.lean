import PyLean.PyGrammar.Peg.Sound
import PyLean.PyGrammar.Peg.FirstDefs
import PyLean.PyGrammar.Peg.FirstTable

set_option maxRecDepth 100000

/-!
What each grammar rule can start with, as a consequence of `CallRuleSound`. `firstTable` is checked
here, not trusted: `allClosed` asks the kernel whether every rule's entry covers all its
alternatives. Induction on `RuleM` then gives `RuleStarts`: when rule `id` succeeds on a run with
no error, the token under the mark at the start has one of the types listed for `id`, unless the
rule can match nothing and did. `RuleFacts.lean` instantiates this for each rule of
`Grammar/python.gram`, with the token types written out.
-/

namespace PyLean.PyGrammar.Peg

open Lexer

/-- The entry of a rule. An id past the last rule behaves as the last rule in `ruleOf`. -/
def firstOf (id : Nat) : Bool × List Nat := firstTable.getD (min id 444) (false, [])

/-- `firstTable` is closed under the grammar. -/
def AllClosed : Prop :=
  (List.range ruleCount).all (fun id => Closed firstOf (ruleOf id) (firstOf id)) = true

theorem allClosed : AllClosed := by
  unfold AllClosed
  decide +kernel

theorem ruleOf_high (id : Nat) (h : 445 ≤ id) : ruleOf id = ruleOf 444 := by
  have h444 : ruleOf 444 = r444 := rfl
  rw [h444]
  unfold ruleOf
  rw [if_neg (show ¬ id < 222 by omega), if_neg (show ¬ id < 333 by omega),
    if_neg (show ¬ id < 389 by omega), if_neg (show ¬ id < 417 by omega),
    if_neg (show ¬ id < 431 by omega), if_neg (show ¬ id < 438 by omega),
    if_neg (show ¬ id < 441 by omega), if_neg (show ¬ id < 443 by omega),
    if_neg (show ¬ id < 444 by omega)]

theorem closed_all (id : Nat) : Closed firstOf (ruleOf id) (firstOf id) = true := by
  have hall := allClosed
  unfold AllClosed at hall
  rw [List.all_eq_true] at hall
  by_cases h : id < 445
  · exact hall id (List.mem_range.mpr h)
  · have h' : 445 ≤ id := by omega
    have e : firstOf id = firstOf 444 := by
      unfold firstOf
      rw [Nat.min_eq_right (by omega)]
      rfl
    rw [ruleOf_high id h', e]
    exact hall 444 (List.mem_range.mpr (by decide))

/-- A match from `i` to `j` starts as `x` says. -/
def Starts (ts : Nat → Token) (x : Bool × List Nat) (i j : Nat) : Prop :=
  (x.1 = true ∧ j = i) ∨ (ts i).type ∈ x.2

theorem subsetB_mem {xs ys : List Nat} (h : subsetB xs ys = true) {t : Nat} (ht : t ∈ xs) :
    t ∈ ys := by
  have := (List.all_eq_true.mp h) t ht
  simpa using this

theorem starts_covers {ts : Nat → Token} {x f : Bool × List Nat} {i j : Nat}
    (h : covers x f = true) (s : Starts ts x i j) : Starts ts f i j := by
  simp only [covers, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  rcases s with ⟨h1, h2⟩ | h1
  · rcases h.2 with h3 | h3
    · rw [h1] at h3
      cases h3
    · exact Or.inl ⟨h3, h2⟩
  · exact Or.inr (subsetB_mem h.1 h1)

theorem items_call_true {c : Call} {rest : List Item} (hn : (callFirst firstOf c).1 = true) :
    itemsFirst firstOf (.call c :: rest) =
      ((itemsFirst firstOf rest).1, (callFirst firstOf c).2 ++ (itemsFirst firstOf rest).2) := by
  simp only [itemsFirst, hn, ↓reduceIte]

mutual
  theorem call_first {ts : Nat → Token} : ∀ {c : Call} {i k : Nat}, CallM ts c i k →
      Starts ts (callFirst firstOf c) i k
    | _, _, _, .tok h => Or.inr (by simp [callFirst, h])
    | _, _, _, .name h => Or.inr (by simp [callFirst, h])
    | _, _, _, .number h => Or.inr (by simp [callFirst, h])
    | _, _, _, .string h => Or.inr (by simp [callFirst, h])
    | _, _, _, .softKeywordToken h _ => Or.inr (by simp [callFirst, h])
    | _, _, _, .softKw h _ => Or.inr (by simp [callFirst, h])
    | _, _, _, .forcedTok h => Or.inr (by simp [callFirst, h])
    | _, _, _, .forcedRule h => rule_first h
    | _, _, _, .rule h => rule_first h

  theorem items_first {ts : Nat → Token} : ∀ {l : List Item} {i j : Nat}, ItemsM ts l i j →
      Starts ts (itemsFirst firstOf l) i j
    | _, _, _, .nil => Or.inl ⟨rfl, rfl⟩
    | _, _, _, @ItemsM.call _ c rest i k j h r => by
      have s := call_first h
      have ih := items_first r
      cases hn : (callFirst firstOf c).1 with
      | true =>
        rw [items_call_true hn]
        rcases s with ⟨_, h2⟩ | h1
        · subst h2
          rcases ih with ⟨h3, h4⟩ | h3
          · exact Or.inl ⟨h3, h4⟩
          · exact Or.inr (List.mem_append_right _ h3)
        · exact Or.inr (List.mem_append_left _ h1)
      | false =>
        have e : itemsFirst firstOf (.call c :: rest) = (false, (callFirst firstOf c).2) := by
          simp only [itemsFirst, hn, Bool.false_eq_true, ↓reduceIte]
        rw [e]
        rcases s with ⟨h1, _⟩ | h1
        · rw [hn] at h1
          cases h1
        · exact Or.inr h1
    | _, _, _, @ItemsM.opt _ c rest i k j h r => by
      have s := call_first h
      have ih := items_first r
      show Starts ts ((itemsFirst firstOf rest).1,
        (callFirst firstOf c).2 ++ (itemsFirst firstOf rest).2) i j
      rcases s with ⟨_, h2⟩ | h1
      · subst h2
        rcases ih with ⟨h3, h4⟩ | h3
        · exact Or.inl ⟨h3, h4⟩
        · exact Or.inr (List.mem_append_right _ h3)
      · exact Or.inr (List.mem_append_left _ h1)
    | _, _, _, @ItemsM.optSkip _ c rest i j r => by
      have ih := items_first r
      show Starts ts ((itemsFirst firstOf rest).1,
        (callFirst firstOf c).2 ++ (itemsFirst firstOf rest).2) i j
      rcases ih with ⟨h3, h4⟩ | h3
      · exact Or.inl ⟨h3, h4⟩
      · exact Or.inr (List.mem_append_right _ h3)
    | _, _, _, @ItemsM.optSoft _ rest i j h _ => by
      show Starts ts ((itemsFirst firstOf rest).1,
        [TokKind.NAME.num] ++ (itemsFirst firstOf rest).2) i j
      exact Or.inr (List.mem_append_left _ (by simp [h]))
    | _, _, _, .look r => by
      simp only [itemsFirst]
      exact items_first r
    | _, _, _, .cut r => by
      simp only [itemsFirst]
      exact items_first r

  theorem loop_first {ts : Nat → Token} : ∀ {a : Alt} {i j : Nat}, LoopM ts a i j →
      j = i ∨ (ts i).type ∈ (itemsFirst firstOf a.items).2
    | _, _, _, .done => Or.inl rfl
    | _, _, _, .step h r => by
      rcases items_first h with ⟨_, h2⟩ | h1
      · subst h2
        exact loop_first r
      · exact Or.inr h1

  theorem rule_first {ts : Nat → Token} : ∀ {id i j : Nat}, RuleM ts id i j →
      Starts ts (firstOf id) i j
    | id, _, _, @RuleM.alt _ _ a _ _ hk hm h => by
      have hc := closed_all id
      have hall : (ruleOf id).alts.all (fun a => covers (itemsFirst firstOf a.items) (firstOf id))
          = true := by
        unfold Closed at hc
        rcases hk with hk | hk <;> simpa only [hk] using hc
      exact starts_covers (List.all_eq_true.mp hall a hm) (items_first h)
    | id, i, j, .loop0 hk h => by
      have hc := closed_all id
      unfold Closed at hc
      simp only [hk, Bool.and_eq_true] at hc
      rcases loop_first h with h1 | h1
      · exact Or.inl ⟨hc.1, h1⟩
      · exact Or.inr (subsetB_mem hc.2 h1)
    | id, i, j, @RuleM.loop1 _ _ _ k _ hk h r => by
      have hc := closed_all id
      unfold Closed at hc
      simp only [hk] at hc
      rcases items_first h with ⟨h1, h2⟩ | h1
      · subst h2
        rcases loop_first r with h3 | h3
        · exact starts_covers hc (Or.inl ⟨h1, h3⟩)
        · exact starts_covers hc (Or.inr h3)
      · exact starts_covers hc (Or.inr h1)
end

/-- What the parser's success on a rule says about the first token: the type is one of the rule's,
or the rule can match nothing and did. Same hypotheses as `CallRuleSound`. -/
def RuleStarts (id : Nat) (nullable : Bool) (types : List Nat) : Prop :=
  ∀ (fuel : Nat) (p : PS), p.mark ≤ p.fill → (∀ i, p.memo.getD i [] = []) →
    (callRule fuel id p).2.errorIndicator = false → nonNull (callRule fuel id p).1 = true →
    (nullable = true ∧ (callRule fuel id p).2.mark = p.mark) ∨
      ((callRule fuel id p).2.tokenAt p.mark).type ∈ types

theorem ruleStarts (id : Nat) : RuleStarts id (firstOf id).1 (firstOf id).2 := by
  intro fuel p hm he hq hn
  exact rule_first (callRuleSound_proven fuel id p hm he hq hn)

/-- `RuleStarts` for every rule, with `firstOf` as the table: the registry's form of the per-rule
facts. -/
def AllRulesStart : Prop := ∀ id, RuleStarts id (firstOf id).1 (firstOf id).2

theorem allRulesStart_proven : AllRulesStart := ruleStarts

end PyLean.PyGrammar.Peg
