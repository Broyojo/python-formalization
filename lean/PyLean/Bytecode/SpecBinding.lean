import PyLean.Bytecode.Ceval

/-!
Argument binding in `Python/ceval.c` (CPython 3.15.2): the keyword loop of `initialize_locals`
(lines 1803-1899), its unexpected keyword error and `positional_only_passed_as_keyword`
(lines 1674-1735), for every code object, function, keyword list and runtime.
-/

namespace PyLean.Bytecode

/-- **The keyword loop** (`initialize_locals`, lines 1803-1899), one keyword `k = v` at a time,
for every code object, function, `**kwargs` dict, keyword list and runtime: a keyword naming a
parameter (`kwSlot`, the first of `co_varnames[co_posonlyargcount:total_args]` with its text)
that is already set raises `"Q() got multiple values for argument 'K'"` (`kw_found`, lines
1889-1897) and binds nothing more; one that is not set takes `v` and the loop goes on. A keyword
naming no parameter goes into `**kwargs` (`PyDict_SetItem`) when there is one; with no
`**kwargs`, `positional_only_passed_as_keyword` runs first when there are positional-only
parameters, and its error is the one raised; otherwise the unexpected keyword error is. A loop that
skipped the check, bound twice, or reported a different keyword fails one of these. -/
def BindKeywordsRules : Prop :=
  ∀ (co : Code) (func : FuncObj) (kwdict : Val) (kwnames : List String) (k : String) (v : Val)
    (rest : List (String × Val)) (fast : Array Val) (rt : Rt),
    (∀ j y rt', kwSlot co k = some j → fast.getD j .null ≠ .null →
      typeError (α := Unit) s!"{func.qualname}() got multiple values for argument '{k}'" rt = .error y rt' →
      bindKeywords co func kwdict kwnames ((k, v) :: rest) fast rt = .error y rt') ∧
    (∀ j, kwSlot co k = some j → fast.getD j .null = .null →
      bindKeywords co func kwdict kwnames ((k, v) :: rest) fast rt =
        bindKeywords co func kwdict kwnames rest (fast.setIfInBounds j v) rt) ∧
    (∀ y rt', kwSlot co k = none → kwdict = .null → co.posonlyargcount ≠ 0 →
      posonlyPassedAsKeyword co kwnames func.qualname rt = .error y rt' →
      bindKeywords co func kwdict kwnames ((k, v) :: rest) fast rt = .error y rt') ∧
    (∀ rt1 y rt', kwSlot co k = none → kwdict = .null →
      (co.posonlyargcount = 0 ∧ rt1 = rt ∨ posonlyPassedAsKeyword co kwnames func.qualname rt = .ok () rt1) →
      unexpectedKeyword (α := Unit) co func.qualname k rt1 = .error y rt' →
      bindKeywords co func kwdict kwnames ((k, v) :: rest) fast rt = .error y rt') ∧
    (kwSlot co k = none → kwdict ≠ .null →
      bindKeywords co func kwdict kwnames ((k, v) :: rest) fast rt =
        (do dictSetStr kwdict k v; bindKeywords co func kwdict kwnames rest fast) rt)

theorem bindKeywordsRules_proven : BindKeywordsRules := by
  intro co func kwdict kwnames k v rest fast rt
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j y rt' hj hs ht
    have hb : (fast.getD j .null != .null) = true := by simpa using hs
    simp only [bindKeywords, hj, hb, if_true, bind, EStateM.bind, ht]
  · intro j hj hs
    have hb : (fast.getD j .null != .null) = false := by simpa using hs
    simp only [bindKeywords, hj, hb, Bool.false_eq_true, if_false, bind, EStateM.bind, pure, EStateM.pure]
  · intro y rt' hj hk hp hpe
    have hb : (co.posonlyargcount != 0) = true := by simpa using hp
    simp only [bindKeywords, hj, hk, beq_self_eq_true, if_true, hb, bind, EStateM.bind, hpe]
  · intro rt1 y rt' hj hk hp hu
    rcases hp with ⟨hp, hr⟩ | hp
    · subst hr
      have hb : (co.posonlyargcount != 0) = false := by simpa using hp
      simp only [bindKeywords, hj, hk, beq_self_eq_true, if_true, hb, Bool.false_eq_true, if_false, bind,
        EStateM.bind, pure, EStateM.pure, hu]
    · by_cases hz : co.posonlyargcount = 0
      · have hb : (co.posonlyargcount != 0) = false := by simpa using hz
        simp only [posonlyPassedAsKeyword, hz] at hp
        simp at hp
        simp only [pure, EStateM.pure] at hp
        cases hp
        simp only [bindKeywords, hj, hk, beq_self_eq_true, if_true, hb, Bool.false_eq_true, if_false, bind,
          EStateM.bind, pure, EStateM.pure, hu]
      · have hb : (co.posonlyargcount != 0) = true := by simpa using hz
        simp only [bindKeywords, hj, hk, beq_self_eq_true, if_true, hb, bind, EStateM.bind, hp, hu]
  · intro hj hk
    have hb : (kwdict == .null) = false := by simpa using hk
    simp only [bindKeywords, hj, hb, Bool.false_eq_true, if_false]

/-- **`positional_only_passed_as_keyword`** (lines 1674-1735), for every code object, keyword list
and runtime: the keywords equal to a positional-only name, collected positional-only name by
name and, for each, in keyword order (the pointer test, else `PyObject_RichCompareBool`, which on
two exact `str` is equality of the text), are joined with `", "` into
`"Q() got some positional-only arguments passed as keyword arguments: 'A, B'"`; with none it
returns 0 and changes nothing. -/
def PosonlyKeywordRules : Prop :=
  ∀ (co : Code) (kwnames : List String) (q : String) (rt : Rt),
    let conflicts := (List.range co.posonlyargcount).flatMap fun i =>
      kwnames.filter (· == co.localsplusnames.getD i "")
    (conflicts = [] → posonlyPassedAsKeyword co kwnames q rt = .ok () rt) ∧
    (conflicts ≠ [] → posonlyPassedAsKeyword co kwnames q rt =
      typeError s!"{q}() got some positional-only arguments passed as keyword arguments: '{joinStrs ", " conflicts}'" rt)

theorem posonlyKeywordRules_proven : PosonlyKeywordRules := by
  intro co kwnames q rt conflicts
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h' : conflicts.isEmpty = true := by rw [h]; rfl
    simp only [conflicts] at h'
    simp only [posonlyPassedAsKeyword, h', Bool.not_true, Bool.false_eq_true, if_false, pure, EStateM.pure]
  · have h' : conflicts.isEmpty = false := by
      cases hc : conflicts with
      | nil => exact absurd hc h
      | cons _ _ => rfl
    simp only [conflicts] at h'
    simp only [posonlyPassedAsKeyword, h', Bool.not_false, if_true]
    rfl

/-- One step of the candidate loop goes on with the suggestion it had or with this item, which is
not the name. -/
theorem suggestLoop_step (name item : String) (rest : List String) (sug : Option String) (sd : Nat) :
    ∃ X Y, (X = sug ∨ (X = some item ∧ item ≠ name)) ∧
      PyLean.TypeObj.suggestLoop name (item :: rest) sug sd = PyLean.TypeObj.suggestLoop name rest X Y := by
  conv => enter [1, X, 1, Y, 2, 1]; unfold PyLean.TypeObj.suggestLoop
  by_cases hne : item = name
  · simp only [hne, beq_self_eq_true, if_true]
    exact ⟨_, _, Or.inl rfl, rfl⟩
  · have hb : (item == name) = false := by simpa using hne
    simp only [hb, Bool.false_eq_true, if_false]
    repeat' split
    all_goals first | exact ⟨_, _, Or.inl rfl, rfl⟩ | exact ⟨_, _, Or.inr ⟨rfl, hne⟩, rfl⟩

/-- The candidate loop keeps an item of the list, never the name itself. -/
theorem suggestLoop_mem (name : String) :
    ∀ (dir : List String) (sug : Option String) (sd : Nat) (s : String),
      PyLean.TypeObj.suggestLoop name dir sug sd = some s → sug = some s ∨ (s ∈ dir ∧ s ≠ name)
  | [], sug, sd, s, h => by simp [PyLean.TypeObj.suggestLoop] at h; exact Or.inl h
  | item :: rest, sug, sd, s, h => by
    obtain ⟨X, Y, hX, he⟩ := suggestLoop_step name item rest sug sd
    rw [he] at h
    rcases suggestLoop_mem name rest X Y s h with h1 | ⟨h1, h2⟩
    · rcases hX with hX | ⟨hX, hn⟩
      · exact Or.inl (by rw [← hX]; exact h1)
      · rw [hX] at h1; cases h1; exact Or.inr ⟨List.mem_cons_self, hn⟩
    · exact Or.inr ⟨List.mem_cons_of_mem _ h1, h2⟩

/-- **The unexpected keyword error** (lines 1851-1876), for every code object, keyword and
runtime: `"Q() got an unexpected keyword argument 'K'"`, with `". Did you mean 'S'?"` exactly when
`_Py_CalculateSuggestions` finds `S` among the names that may be passed by keyword (only tried
when there are any); a suggestion is always such a name, never a positional-only one and never the
keyword itself. -/
def UnexpectedKeywordRules : Prop :=
  ∀ (co : Code) (q k : String) (rt : Rt),
    (kwSuggestion co k = if co.argcount + co.kwonlyargcount > co.posonlyargcount then
      PyLean.TypeObj.calcSuggestion (possibleKeywords co) k else none) ∧
    (kwSuggestion co k = none → unexpectedKeyword (α := Unit) co q k rt =
      typeError s!"{q}() got an unexpected keyword argument '{k}'" rt) ∧
    (∀ s, kwSuggestion co k = some s → unexpectedKeyword (α := Unit) co q k rt =
      typeError s!"{q}() got an unexpected keyword argument '{k}'. Did you mean '{s}'?" rt) ∧
    (∀ s, kwSuggestion co k = some s → s ≠ k ∧ ∃ j, co.posonlyargcount ≤ j ∧ j < co.argcount + co.kwonlyargcount ∧
      co.localsplusnames.getD j "" = s)

theorem unexpectedKeywordRules_proven : UnexpectedKeywordRules := by
  intro co q k rt
  refine ⟨rfl, fun h => ?_, fun s h => ?_, fun s h => ?_⟩
  · simp only [unexpectedKeyword, h]
  · simp only [unexpectedKeyword, h]
  · simp only [kwSuggestion] at h
    split at h
    · simp only [PyLean.TypeObj.calcSuggestion] at h
      split at h
      · cases h
      · rcases suggestLoop_mem k _ none 0 s h with h1 | ⟨h1, h2⟩
        · cases h1
        · refine ⟨h2, ?_⟩
          simp only [possibleKeywords, List.mem_map, List.mem_range'_1] at h1
          obtain ⟨j, ⟨hj1, hj2⟩, hj⟩ := h1
          exact ⟨j, hj1, by omega, hj⟩
    · cases h

end PyLean.Bytecode
