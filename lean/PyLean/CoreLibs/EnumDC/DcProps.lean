import PyLean.CoreLibs.EnumDC.Dataclass

/-!
Properties of the dataclass mirrors. Each one pins the function down: a statement that a wrong `getField`, `fieldsPut`,
`initCheck` or `andChain` would also satisfy is not stated.
-/

namespace PyLean.CoreLibs.EnumDC

open PyLean

/-- A field with only a default and the `kw_only` of the class. -/
def bareField (name : String) (k : FKind) (kw : Bool) (d : Option Int) (u : Bool) : DField :=
  { name := name, kind := k, dflt := d, unhash := u, kwOnly := if k != .classVar then some kw else none }

/-- A `field()` once it has a name, a kind, and its `kw_only`. -/
def namedField (g : DField) (name : String) (k : FKind) (kw : Bool) : DField :=
  { g with
    name := name
    kind := k
    kwOnly := if k != .classVar && g.kwOnly.isNone then some kw else g.kwOnly }

/-- `_get_field`, every path, and what comes out. A default factory on a `ClassVar` or `InitVar` is a `TypeError`, as is
`kw_only` on a `ClassVar`, and an unhashable default on a real field is the `ValueError` of "use default_factory".
Otherwise the field has the name and the kind it was declared with, the settings of a `field()`, and `kw_only` from the
`field()` or from the default. -/
def GetFieldPaths : Prop :=
  ∀ (g : DField) (name : String) (k : FKind) (kw : Bool) (v : Int) (u : Bool),
    (k ≠ .plain → g.factory.isSome = true → (getField (.field g) name k kw).raises "TypeError") ∧
    (g.factory.isSome = false → g.kwOnly.isSome = true → (getField (.field g) name .classVar kw).raises "TypeError") ∧
    (g.dflt.isSome = true → g.unhash = true → g.factory.isSome = false →
      (getField (.field g) name .plain kw).raises "ValueError") ∧
    (getField (.value v true) name .plain kw).raises "ValueError" ∧
    (g.unhash = false → g.factory.isSome = false ∨ k = .plain → (k ≠ .classVar ∨ g.kwOnly.isNone = true) →
      getField (.field g) name k kw = .ok (namedField g name k kw)) ∧
    (k ≠ .plain ∨ u = false → getField (.value v u) name k kw = .ok (bareField name k kw (some v) u)) ∧
    getField .slot name k kw = .ok (bareField name k kw none false) ∧
    getField .missing name k kw = .ok (bareField name k kw none false)

theorem getFieldPaths_proven : GetFieldPaths := by
  intro g name k kw v u
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hk hf
    refine ⟨.typeError s!"field {name} cannot have a default factory", ?_, rfl⟩
    have : (k != .plain) = true := by simpa using hk
    simp [getField, this, hf]
  · intro hf hk
    refine ⟨.typeError s!"field {name} is a ClassVar but specifies kw_only", ?_, rfl⟩
    simp [getField, hf, hk]
  · intro hd hu hf
    refine ⟨.valueError s!"~mutable default for field {name} is not allowed: use default_factory", ?_, rfl⟩
    cases hk : g.kwOnly <;> simp [getField, hd, hu, hk]
  · refine ⟨.valueError s!"~mutable default for field {name} is not allowed: use default_factory", ?_, rfl⟩
    simp [getField]
  · intro hu hf hc
    cases k with
    | plain =>
      have hu' : g.unhash = false := hu
      by_cases hn : g.kwOnly.isNone = true <;> simp [getField, namedField, hu', hn]
    | classVar =>
      have h1 : g.factory.isSome = false := by simpa using hf
      have h2 : g.kwOnly.isNone = true := by simpa using hc
      have h3 : g.kwOnly = none := by simpa using h2
      simp [getField, namedField, h1, h3]
    | initVar =>
      have h1 : g.factory.isSome = false := by simpa using hf
      by_cases hn : g.kwOnly.isNone = true <;> simp [getField, namedField, h1, hu, hn]
  · intro h
    cases k with
    | plain =>
      have hu' : u = false := by simpa using h
      subst hu'
      simp [getField, bareField]
    | classVar => simp [getField, bareField]
    | initVar => simp [getField, bareField]
  · cases k <;> simp [getField, bareField]
  · cases k <;> simp [getField, bareField]

/-- `fields[f.name] = f`: the names stay without repeats, the field is found under its name, every other name is found
as before, and the list of names only grows at the end. So a derived class overrides a field in the place the base gave
it. Docs: "the base class... fields are... in the order". -/
def FieldsPutSpec : Prop :=
  ∀ (m : List DField) (f : DField), (m.map (·.name)).Nodup →
    ((fieldsPut m f).map (·.name)).Nodup ∧
    (fieldsPut m f).find? (fun x => x.name == f.name) = some f ∧
    (∀ n, n ≠ f.name → (fieldsPut m f).find? (fun x => x.name == n) = m.find? (fun x => x.name == n)) ∧
    (fieldsPut m f).map (·.name) = (if m.any (fun x => x.name == f.name) then m.map (·.name) else m.map (·.name) ++ [f.name])

private theorem put_names (m : List DField) (f : DField) (h : m.any (fun x => x.name == f.name) = true) :
    (m.map (fun x => if x.name == f.name then f else x)).map (·.name) = m.map (·.name) := by
  clear h
  induction m with
  | nil => rfl
  | cons x xs ih =>
    by_cases hx : x.name = f.name
    · simp only [List.map_cons, hx, beq_self_eq_true, ↓reduceIte, ih]
    · have : (x.name == f.name) = false := by simpa using hx
      simp only [List.map_cons, this, Bool.false_eq_true, ↓reduceIte, ih]

private theorem put_find (m : List DField) (f : DField) (hn : (m.map (·.name)).Nodup) (n : String) (hne : n ≠ f.name) :
    (m.map (fun x => if x.name == f.name then f else x)).find? (fun x => x.name == n) = m.find? (fun x => x.name == n) := by
  clear hn
  induction m with
  | nil => rfl
  | cons x xs ih =>
    by_cases hx : x.name = f.name
    · have h1 : (f.name == n) = false := by
        have : f.name ≠ n := fun e => hne e.symm
        simpa using this
      simp only [List.map_cons, hx, beq_self_eq_true, ↓reduceIte, List.find?_cons, h1, ih]
    · have h3 : (x.name == f.name) = false := by simpa using hx
      simp only [List.map_cons, h3, Bool.false_eq_true, ↓reduceIte, List.find?_cons, ih]

private theorem put_find_self (m : List DField) (f : DField) (h : m.any (fun x => x.name == f.name) = true) :
    (m.map (fun x => if x.name == f.name then f else x)).find? (fun x => x.name == f.name) = some f := by
  induction m with
  | nil => simp at h
  | cons x xs ih =>
    by_cases hx : x.name = f.name
    · simp [hx]
    · have h3 : (x.name == f.name) = false := by simpa using hx
      have h' : xs.any (fun x => x.name == f.name) = true := by simpa [h3] using h
      simp only [List.map_cons, h3, Bool.false_eq_true, ↓reduceIte, List.find?_cons, ih h']

theorem fieldsPutSpec_proven : FieldsPutSpec := by
  intro m f hn
  by_cases h : m.any (fun x => x.name == f.name) = true
  · have hp : fieldsPut m f = m.map (fun x => if x.name == f.name then f else x) := by simp [fieldsPut, h]
    rw [hp]
    refine ⟨by rw [put_names m f h]; exact hn, put_find_self m f h, fun n hne => put_find m f hn n hne, ?_⟩
    rw [put_names m f h]
    simp [h]
  · have hb : m.any (fun x => x.name == f.name) = false := Bool.eq_false_iff.2 h
    have hp : fieldsPut m f = m ++ [f] := by simp only [fieldsPut, hb, Bool.false_eq_true, ↓reduceIte]
    rw [hp]
    have hnone : m.find? (fun x => x.name == f.name) = none := by
      apply List.find?_eq_none.2
      intro x hx he
      have : m.any (fun x => x.name == f.name) = true := List.any_eq_true.2 ⟨x, hx, he⟩
      rw [hb] at this
      exact Bool.noConfusion this
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [List.map_append, List.map_cons, List.map_nil]
      refine List.nodup_append.2 ⟨hn, by simp, ?_⟩
      intro a ha b hbm he
      simp only [List.mem_singleton] at hbm
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
      apply h
      exact List.any_eq_true.2 ⟨x, hx, by simp [he, hbm]⟩
    · simp [List.find?_append, hnone]
    · intro n hne
      have : (f.name == n) = false := by
        have : f.name ≠ n := fun e => hne e.symm
        simpa using this
      cases hm : m.find? (fun x => x.name == n) with
      | none => simp [List.find?_append, hm, this]
      | some y => simp [List.find?_append, hm]
    · simp [hb]

/-- `_init_fn`'s check is exact: on the standard fields that go to `__init__`, it passes exactly when no field without a
default comes after one with a default. Neither "always passes" nor "always fails" meets this. -/
def InitCheckExact : Prop :=
  ∀ l : List DField, initCheck none l = .ok () ↔
    (l.filter (·.init)).Pairwise (fun a b => (a.dflt.isSome || a.factory.isSome) = true → (b.dflt.isSome || b.factory.isSome) = true)

private theorem initCheck_seen (s : String) (l : List DField) :
    initCheck (some s) l = .ok () ↔ ∀ f ∈ l.filter (·.init), (f.dflt.isSome || f.factory.isSome) = true := by
  induction l generalizing s with
  | nil => simp [initCheck]
  | cons f r ih =>
    simp only [initCheck]
    by_cases hi : f.init = true
    · simp only [hi, ↓reduceIte, List.filter_cons, List.mem_cons, forall_eq_or_imp]
      by_cases hd : (f.dflt.isSome || f.factory.isSome) = true
      · simp only [hd, ↓reduceIte, true_and]
        exact ih f.name
      · simp [hd]
    · have hi' : f.init = false := Bool.eq_false_iff.2 hi
      simp only [hi', Bool.false_eq_true, ↓reduceIte, List.filter_cons]
      exact ih s

theorem initCheckExact_proven : InitCheckExact := by
  intro l
  induction l with
  | nil => simp [initCheck]
  | cons f r ih =>
    simp only [initCheck]
    by_cases hi : f.init = true
    · simp only [hi, ↓reduceIte, List.filter_cons, List.pairwise_cons]
      by_cases hd : (f.dflt.isSome || f.factory.isSome) = true
      · simp only [hd, ↓reduceIte, true_imp_iff]
        rw [initCheck_seen]
        constructor
        · intro h
          refine ⟨h, ?_⟩
          apply List.Pairwise.imp_of_mem _ (List.pairwise_of_forall (R := fun _ _ => True) (by simp))
          intro a b _ hb _ _
          exact h b hb
        · exact fun h => h.1
      · have hd' : (f.dflt.isSome || f.factory.isSome) = false := Bool.eq_false_iff.2 hd
        simp only [hd', Bool.false_eq_true, ↓reduceIte, false_imp_iff, implies_true, true_and]
        exact ih
    · have hi' : f.init = false := Bool.eq_false_iff.2 hi
      simp only [hi', Bool.false_eq_true, ↓reduceIte, List.filter_cons]
      exact ih

/-- `add_fns_to_class`: a method that the class defines is kept; if it has an `overwrite_error` that is a `TypeError`,
and if none of the methods does, what goes in is exactly the methods that the class does not define, in order. -/
def AddFnsSpec : Prop :=
  ∀ (cls : String) (defined : List String) (l : List (String × Option String)),
    (l.all (fun p => !(defined.contains p.1) || p.2.isNone) = true →
      addFns cls defined l = .ok ((l.map Prod.fst).filter (fun n => !defined.contains n))) ∧
    (∀ pre n e post, l = pre ++ (n, some e) :: post → defined.contains n = true →
      pre.all (fun p => !(defined.contains p.1) || p.2.isNone) = true → (addFns cls defined l).raises "TypeError")

theorem addFnsSpec_proven : AddFnsSpec := by
  intro cls defined l
  refine ⟨?_, ?_⟩
  · induction l with
    | nil => intro _; rfl
    | cons p r ih =>
      intro h
      obtain ⟨n, e⟩ := p
      have h' : (!(defined.contains n) || e.isNone) = true ∧
          r.all (fun p => !(defined.contains p.1) || p.2.isNone) = true := by simpa using h
      have ihr := ih h'.2
      by_cases hd : defined.contains n = true
      · have he : e = none := by
          have := h'.1
          simp only [hd, Bool.not_true, Bool.false_or] at this
          simpa using this
        subst he
        simp only [addFns, hd, ↓reduceIte, ihr, List.map_cons, List.filter_cons, Bool.not_true, Bool.false_eq_true]
      · have hd' : defined.contains n = false := Bool.eq_false_iff.2 hd
        simp only [addFns, hd', Bool.false_eq_true, ↓reduceIte, ihr, List.map_cons, List.filter_cons, Bool.not_false]
  · intro pre
    induction pre generalizing l with
    | nil =>
      intro n e post hl hd _
      subst hl
      exact ⟨.typeError s!"Cannot overwrite attribute {n} in class {cls}{e}", by
        simp only [List.nil_append, addFns, hd, ↓reduceIte], rfl⟩
    | cons p r ih =>
      intro n e post hl hd ha
      subst hl
      obtain ⟨m, x⟩ := p
      have h' : (!(defined.contains m) || x.isNone) = true ∧
          r.all (fun p => !(defined.contains p.1) || p.2.isNone) = true := by simpa using ha
      obtain ⟨err, h1, h2⟩ := ih (r ++ (n, some e) :: post) n e post rfl hd h'.2
      refine ⟨err, ?_, h2⟩
      by_cases hd2 : defined.contains m = true
      · have he : x = none := by
          have := h'.1
          simp only [hd2, Bool.not_true, Bool.false_or] at this
          simpa using this
        subst he
        simp only [List.cons_append, addFns, hd2, ↓reduceIte]
        exact h1
      · have hd' : defined.contains m = false := Bool.eq_false_iff.2 hd2
        simp only [List.cons_append, addFns, hd', Bool.false_eq_true, ↓reduceIte, h1]

/-- What `_process_class` accepts: `order` needs `eq`; with dataclass bases, `frozen` agrees with every one of them, so
that a class cannot mix; the hash action is not the exception; the positional fields are those with `init` and without
`kw_only`, in order, the keyword-only ones the rest, and there are no pseudo-fields of `ClassVar` among them; the methods
that went in are those the class did not define; `__match_args__` is the positional names. -/
def ProcessAccepted : Prop :=
  ∀ (c : DClass) (i : DInfo), processClass c = .ok i → ∃ own,
    scanAnns c.anns c.params.kwOnly false = .ok own ∧ c.stray = none ∧ i.fields = allFields c own ∧
    (c.params.order = true → c.params.eq = true) ∧
    (c.bases ≠ [] → (c.params.frozen = true ↔ anyFrozen c.bases = true) ∧
      (c.params.frozen = true → allFrozen c.bases = true)) ∧
    i.hash = hashAction c.params.unsafeHash c.params.eq c.params.frozen (explicitHash c) ∧ i.hash ≠ .exception ∧
    i.std = (i.fields.filter (fun f => f.kind != .classVar)).filter (fun f => f.init && f.kwOnly != some true) ∧
    i.kw = (i.fields.filter (fun f => f.kind != .classVar)).filter (fun f => f.init && f.kwOnly == some true) ∧
    (c.params.init = true → initCheck none i.std = .ok ()) ∧
    (∀ n ∈ i.generated, c.defined.contains n = false) ∧
    (i.matchArgs = if c.params.matchArgs && !c.defined.contains "__match_args__"
      then some (i.std.map (·.name)) else none) ∧
    (c.params.weakrefSlot = true → c.params.slots = true)

private theorem addFns_new {cls : String} {defined : List String} {l : List (String × Option String)}
    {g : List String} (h : addFns cls defined l = .ok g) : ∀ n ∈ g, defined.contains n = false := by
  induction l generalizing g with
  | nil =>
    simp only [addFns, Except.ok.injEq] at h
    subst h
    simp
  | cons p r ih =>
    obtain ⟨n, e⟩ := p
    simp only [addFns] at h
    split at h
    · rename_i hd
      split at h
      · simp at h
      · exact ih h
    · rename_i hd
      split at h
      · simp at h
      · rename_i l' hl
        simp only [Except.ok.injEq] at h
        subst h
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact Bool.eq_false_iff.2 hd
        · exact ih hl x hx

theorem processAccepted_proven : ProcessAccepted := by
  intro c i h
  unfold processClass at h
  split at h
  · simp at h
  rename_i own hown
  try simp only at h
  split at h
  · simp at h
  rename_i hs
  split at h
  · simp at h
  rename_i h1
  split at h
  · simp at h
  rename_i h2
  split at h
  · simp at h
  rename_i h3
  try simp only at h
  split at h
  · simp at h
  rename_i hc
  split at h
  · simp at h
  rename_i h4
  split at h
  · simp at h
  rename_i gen hg
  split at h
  · simp at h
  rename_i h5
  split at h
  · simp at h
  rename_i h6
  simp only [Except.ok.injEq] at h
  subst h
  have hb : ∀ b : Bool, ¬(b = true) → b = false := fun b hb => Bool.eq_false_iff.2 hb
  refine ⟨own, hown, hs, rfl, ?_, ?_, rfl, ?_, rfl, rfl, ?_, addFns_new hg, rfl, ?_⟩
  · intro ho
    have := h3
    simp only [Bool.and_eq_true, Bool.not_eq_true', not_and, Bool.not_eq_false] at this
    exact this ho
  · intro hne
    have hne' : c.bases.isEmpty = false := by
      cases hh : c.bases with
      | nil => exact absurd hh hne
      | cons _ _ => rfl
    simp only [hne', Bool.not_false, Bool.true_and, Bool.not_eq_true', Bool.and_eq_true, not_and,
      Bool.not_eq_false] at h1 h2
    constructor
    · constructor
      · intro hf
        have hall : allFrozen c.bases = true := by
          by_cases ha : allFrozen c.bases = true
          · exact ha
          · exact absurd hf (h2 (Bool.eq_false_iff.2 ha))
        cases hh : c.bases with
        | nil => exact absurd hh hne
        | cons b r =>
          rw [hh] at hall
          simp only [allFrozen, List.all_cons, Bool.and_eq_true] at hall
          simp [anyFrozen, hall.1]
      · intro ha
        exact h1 ha
    · intro hf
      by_cases ha : allFrozen c.bases = true
      · exact ha
      · exact absurd hf (h2 (Bool.eq_false_iff.2 ha))
  · simpa using h4
  · intro hi
    simp only [hi, ↓reduceIte] at hc
    exact hc
  · intro hw
    have := h5
    simp only [Bool.and_eq_true, Bool.not_eq_true', not_and, Bool.not_eq_false] at this
    exact this hw

/-! ### `__init__` -/

/-- The interpreter's binding of `__init__`, exactly: too many positional arguments, an unknown keyword, a keyword that
repeats a positional, and a parameter left without a value or a default are each a `TypeError`, and anything else binds
the first parameters to `args` in order, and the rest by keyword. -/
def BindExact : Prop :=
  ∀ (std kw : List DField) (args : List Int) (kwargs : List (String × Int)),
    let names := (std ++ kw).map (·.name)
    let given := (std.take args.length).map (·.name)
    let bound := given.zip args ++ kwargs
    (args.length > std.length → (bindArgs std kw args kwargs).raises "TypeError") ∧
    (args.length ≤ std.length → kwargs.any (fun p => !names.contains p.1) = true →
      (bindArgs std kw args kwargs).raises "TypeError") ∧
    (args.length ≤ std.length → kwargs.any (fun p => !names.contains p.1) = false →
      kwargs.any (fun p => given.contains p.1) = true → (bindArgs std kw args kwargs).raises "TypeError") ∧
    (args.length ≤ std.length → kwargs.any (fun p => !names.contains p.1) = false →
      kwargs.any (fun p => given.contains p.1) = false →
      ((std ++ kw).any (fun f => f.dflt.isNone && f.factory.isNone && (bound.lookup f.name).isNone) = true →
        (bindArgs std kw args kwargs).raises "TypeError") ∧
      ((std ++ kw).any (fun f => f.dflt.isNone && f.factory.isNone && (bound.lookup f.name).isNone) = false →
        bindArgs std kw args kwargs = .ok bound))

theorem bindExact_proven : BindExact := by
  intro std kw args kwargs names given bound
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    refine ⟨.typeError "~takes positional arguments but more were given", ?_, rfl⟩
    simp only [bindArgs, h, ↓reduceIte]
  · intro h h1
    have h' : ¬ args.length > std.length := by omega
    refine ⟨.typeError "~got an unexpected keyword argument", ?_, rfl⟩
    simp only [bindArgs, h']
    exact if_pos h1
  · intro h h1 h2
    have h' : ¬ args.length > std.length := by omega
    refine ⟨.typeError "~got multiple values for argument", ?_, rfl⟩
    simp only [bindArgs, h', ↓reduceIte]
    rw [if_neg (by simp only [names] at h1; simp only [h1, Bool.false_eq_true, not_false_eq_true]), if_pos h2]
  · intro h h1 h2
    have h' : ¬ args.length > std.length := by omega
    have e : bindArgs std kw args kwargs =
        (if (std ++ kw).any (fun f => f.dflt.isNone && f.factory.isNone && (bound.lookup f.name).isNone) = true then
          .error (.typeError "~missing required argument") else .ok bound) := by
      simp only [bindArgs, h', ↓reduceIte]
      rw [if_neg (by simp only [names] at h1; simp only [h1, Bool.false_eq_true, not_false_eq_true]),
        if_neg (by simp only [given] at h2; simp only [h2, Bool.false_eq_true, not_false_eq_true])]
    refine ⟨?_, ?_⟩
    · intro h3
      exact ⟨.typeError "~missing required argument", by rw [e, if_pos h3], rfl⟩
    · intro h3
      rw [e, if_neg (by simp only [h3, Bool.false_eq_true, not_false_eq_true])]

/-- What `_field_init` assigns, each branch: an argument wins; otherwise the factory is called, or the default used; a field
outside `__init__` gets the factory, and otherwise nothing, leaving the class attribute, except that with `slots` the
default is assigned. -/
def FieldValuePaths : Prop :=
  ∀ (f : DField) (s : Bool) (b : List (String × Int)) (v n d : Int),
    (f.init = true → b.lookup f.name = some v → fieldValue s b f = some v) ∧
    (f.init = true → b.lookup f.name = none → f.factory = some n → fieldValue s b f = some n) ∧
    (f.init = true → b.lookup f.name = none → f.factory = none → fieldValue s b f = f.dflt) ∧
    (f.init = false → f.factory = some n → fieldValue s b f = some n) ∧
    (f.init = false → f.factory = none → fieldValue s b f = if s then f.dflt else none)

theorem fieldValuePaths_proven : FieldValuePaths := by
  intro f s b v n d
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hi hb
    cases hf : f.factory <;> cases hd : f.dflt <;> simp [fieldValue, hf, hd, hi, hb]
  · intro hi hb hf
    simp [fieldValue, hf, hi, hb]
  · intro hi hb hf
    cases hd : f.dflt <;> simp [fieldValue, hf, hd, hi, hb]
  · intro hi hf
    simp [fieldValue, hf, hi]
  · intro hi hf
    cases s <;> simp [fieldValue, hf, hi]

private theorem lookup_filterMap (val : DField → Option Int) (l : List DField) (hn : (l.map (·.name)).Nodup)
    (f : DField) (hf : f ∈ l) :
    (l.filterMap (fun g => (val g).map (fun v => (g.name, v)))).lookup f.name = val f := by
  induction l with
  | nil => simp at hf
  | cons x xs ih =>
    simp only [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.1 hf with rfl | hf'
    · cases hv : val f with
      | none =>
        have key : ∀ (ys : List DField), f.name ∉ ys.map (·.name) →
            (ys.filterMap (fun g => (val g).map (fun v => (g.name, v)))).lookup f.name = none := by
          intro ys
          induction ys with
          | nil => simp
          | cons y ys ih2 =>
            intro hy
            simp only [List.map_cons, List.mem_cons, not_or] at hy
            have hb : (f.name == y.name) = false := by simpa using hy.1
            cases hw : val y with
            | none => simp [List.filterMap_cons, hw, ih2 hy.2]
            | some w => simp [List.filterMap_cons, hw, List.lookup_cons, hb, ih2 hy.2]
        simpa [List.filterMap_cons, hv] using key xs hn.1
      | some w => simp [List.filterMap_cons, hv]
    · have hne : f.name ≠ x.name := fun e => hn.1 (e ▸ List.mem_map.2 ⟨f, hf', rfl⟩)
      have hb : (f.name == x.name) = false := by simpa using hne
      cases hw : val x with
      | none => simpa [List.filterMap_cons, hw] using ih hn.2 hf'
      | some w => simpa [List.filterMap_cons, hw, List.lookup_cons, hb] using ih hn.2 hf'

/-- `C(**kw)`: for every real field, what the instance holds is what `_field_init` gives for that field and keyword, so
that one field cannot pick up the value of another. Field names do not repeat, by `FieldsPutSpec`. -/
def InitValues : Prop :=
  ∀ (i : DInfo) (post : Bool) (kw : List (String × Int)) (o : DObj), (i.fields.map (·.name)).Nodup →
    callInit i post [] kw = .ok o → ∀ f ∈ i.fields, f.kind = .plain →
      o.attrs.lookup f.name = fieldValue i.params.slots kw f

private theorem bind_nil {std kw' : List DField} {kw b : List (String × Int)} (h : bindArgs std kw' [] kw = .ok b) :
    b = kw := by
  unfold bindArgs at h
  simp only [List.length_nil] at h
  split at h
  · simp at h
  split at h
  · simp at h
  split at h
  · simp at h
  split at h
  · simp at h
  simpa using h.symm

private theorem init_body {i : DInfo} {post : Bool} {args : List Int} {kw : List (String × Int)} {o : DObj}
    (h : callInit i post args kw = .ok o) :
    ∃ b, bindArgs i.std i.kw args kw = .ok b ∧ o = initBody i post b := by
  unfold callInit at h
  split at h
  · simp at h
  rename_i b hb
  refine ⟨b, hb, ?_⟩
  split at h
  · split at h
    · simp at h
    · simpa using h.symm
  · simpa using h.symm

theorem initValues_proven : InitValues := by
  intro i post kw o hn h f hf hk
  obtain ⟨b, hb, rfl⟩ := init_body h
  have e := bind_nil hb
  subst e
  have hsub : (((i.fields.filter (fun f => f.kind != .classVar)).filter (fun f => f.kind == .plain)).map (·.name)).Nodup := by
    have s1 : ((i.fields.filter (fun f => f.kind != .classVar)).filter (fun f => f.kind == .plain)).Sublist i.fields :=
      (List.filter_sublist).trans List.filter_sublist
    exact (s1.map _).nodup hn
  have hmem : f ∈ (i.fields.filter (fun f => f.kind != .classVar)).filter (fun f => f.kind == .plain) := by
    simp [hf, hk]
  exact lookup_filterMap _ _ hsub f hmem

/-- `replace` can fail on the instance it starts from only as the docs say. With a field declared `init=False` in the
changes it is a `TypeError`, and an `InitVar` without a default that is not in the changes is another, wherever the field
stands: the fields before it have only to be passed. -/
def ReplaceErrors : Prop :=
  ∀ (i : DInfo) (o : DObj) (pre post : List DField) (f : DField) (ch ch' : List (String × Int)),
    replaceLoop i o pre ch = .ok ch' → f.kind ≠ .classVar →
    (f.init = false → (ch'.lookup f.name).isSome = true → (replaceLoop i o (pre ++ f :: post) ch).raises "TypeError") ∧
    (f.init = true → f.kind = .initVar → f.dflt = none → ch'.lookup f.name = none →
      (replaceLoop i o (pre ++ f :: post) ch).raises "TypeError")

private theorem replaceLoop_append (i : DInfo) (o : DObj) (pre r : List DField) :
    ∀ ch ch', replaceLoop i o pre ch = .ok ch' → replaceLoop i o (pre ++ r) ch = replaceLoop i o r ch' := by
  induction pre with
  | nil =>
    intro ch ch' h
    simp only [replaceLoop, Except.ok.injEq] at h
    subst h
    rfl
  | cons f t ih =>
    intro ch ch' h
    simp only [List.cons_append, replaceLoop] at h ⊢
    split at h
    · rw [if_pos ‹_›]
      exact ih _ _ h
    · rw [if_neg ‹_›]
      split at h
      · rw [if_pos ‹_›]
        split at h
        · simp at h
        · rw [if_neg ‹_›]
          exact ih _ _ h
      · rw [if_neg ‹_›]
        split at h
        · rw [if_pos ‹_›]
          split at h
          · simp at h
          · rw [if_neg ‹_›]
            split at h
            · simp at h
            · exact ih _ _ h
        · rw [if_neg ‹_›]
          exact ih _ _ h

theorem replaceErrors_proven : ReplaceErrors := by
  intro i o pre post f ch ch' h hk
  have hk' : (f.kind == .classVar) = false := by simpa using hk
  refine ⟨?_, ?_⟩
  · intro hi hs
    refine ⟨.typeError s!"field {f.name} is declared with init=False, it cannot be specified with replace()", ?_, rfl⟩
    rw [replaceLoop_append i o pre _ ch ch' h]
    simp only [replaceLoop, hk', Bool.false_eq_true, ↓reduceIte, hi, Bool.not_false, hs]
  · intro hi hv hd hn
    refine ⟨.typeError s!"InitVar '{f.name}' must be specified with replace()", ?_, rfl⟩
    rw [replaceLoop_append i o pre _ ch ch' h]
    simp [replaceLoop, hk', hi, hn, hv, hd]

private theorem replaceLoop_spec (i : DInfo) (o : DObj) (fs : List DField) :
    ∀ ch ch', replaceLoop i o fs ch = .ok ch' → (∀ f ∈ fs, f.kind = .plain ∧ f.init = true) →
      (∀ n w, ch.lookup n = some w → ch'.lookup n = some w) ∧
      (∀ f ∈ fs, ∃ v, ch'.lookup f.name = some v ∧ (ch.lookup f.name = none → getAttrD i o f.name = .ok v)) := by
  induction fs with
  | nil =>
    intro ch ch' h _
    simp only [replaceLoop, Except.ok.injEq] at h
    subst h
    exact ⟨fun _ _ h => h, by simp⟩
  | cons f r ih =>
    intro ch ch' h hall
    obtain ⟨hp, hi⟩ := hall f (by simp)
    have hall' := fun x hx => hall x (List.mem_cons_of_mem _ hx)
    have hk : (f.kind == .classVar) = false := by simp [hp]
    have hv : (f.kind == .initVar) = false := by simp [hp]
    simp only [replaceLoop, hk, Bool.false_eq_true, ↓reduceIte, hi, Bool.not_true] at h
    by_cases hc : (ch.lookup f.name).isNone = true
    · simp only [hc, ↓reduceIte, hv, Bool.false_and] at h
      cases hg : getAttrD i o f.name with
      | error e =>
        simp [hg] at h
      | ok v =>
      simp only [hg] at h
      obtain ⟨h1, h2⟩ := ih _ _ h hall'
      have hc' : ch.lookup f.name = none := by simpa using hc
      have snoc : ∀ n w, ch.lookup n = some w → (ch ++ [(f.name, v)]).lookup n = some w := by
        intro n w hw
        simp [List.lookup_append, hw]
      have self : (ch ++ [(f.name, v)]).lookup f.name = some v := by
        simp [List.lookup_append, hc']
      refine ⟨fun n w hw => h1 n w (snoc n w hw), ?_⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨v, h1 _ _ self, fun _ => hg⟩
      · by_cases he : x.name = f.name
        · refine ⟨v, by rw [he]; exact h1 _ _ self, fun _ => by rw [he]; exact hg⟩
        · obtain ⟨u, hu, hu2⟩ := h2 x hx
          exact ⟨u, hu, fun hn => hu2 (by simp [List.lookup_append, hn, he])⟩
    · have hc' : (ch.lookup f.name).isNone = false := Bool.eq_false_iff.2 hc
      simp only [hc', Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨h1, h2⟩ := ih _ _ h hall'
      refine ⟨h1, ?_⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · cases hw : ch.lookup x.name with
        | none => simp [hw] at hc
        | some w => exact ⟨w, h1 _ _ hw, by simp⟩
      · exact h2 x hx

/-- `replace`, on a class whose fields are all real and in `__init__`: every field of the result holds its value from the
changes, and any other field its value in the original. "Return a new object replacing specified fields with new
values." The other kinds of field are in `ReplaceErrors`. -/
def ReplaceSpec : Prop :=
  ∀ (i : DInfo) (post : Bool) (o o' : DObj) (ch : List (String × Int)), (i.fields.map (·.name)).Nodup →
    (∀ f ∈ i.fields, f.kind = .plain ∧ f.init = true) → dcReplace i post o ch = .ok o' →
    ∀ f ∈ i.fields, ∃ v, o'.attrs.lookup f.name = some v ∧ (∀ w, ch.lookup f.name = some w → v = w) ∧
      (ch.lookup f.name = none → getAttrD i o f.name = .ok v)

theorem replaceSpec_proven : ReplaceSpec := by
  intro i post o o' ch hn hall h f hf
  unfold dcReplace at h
  split at h
  · simp at h
  rename_i kw hk
  obtain ⟨h1, h2⟩ := replaceLoop_spec i o i.fields ch kw hk hall
  obtain ⟨v, hv, hv2⟩ := h2 f hf
  have hp := hall f hf
  have e := initValues_proven i post kw o' hn h f hf hp.1
  rw [(fieldValuePaths_proven f i.params.slots kw v 0 0).1 hp.2 hv] at e
  refine ⟨v, e, ?_, hv2⟩
  intro w hw
  have := h1 _ _ hw
  rw [hv] at this
  simpa using this

/-- Any instance can be made once its arguments bind: "`__init__` raises only what binding raises". False: an `InitVar`
with `init=False` is not a parameter, and the generated `__post_init__` call names it, so `__init__` raises `NameError`.
The comment at Lib/dataclasses.py:894-898 knows that `init=<anything>` on an `InitVar` makes no sense, and does not
check it. -/
def InitBindsAlways : Prop :=
  ∀ (c : DClass) (i : DInfo) (args : List Int) (kw b : List (String × Int)), processClass c = .ok i →
    bindArgs i.std i.kw args kw = .ok b → ∃ o, callInit i true args kw = .ok o

theorem initBindsAlways_refuted : ¬InitBindsAlways := by
  intro h
  let c : DClass := { anns := [{ name := "x", kind := .field .initVar, attr := .field { init := false } }] }
  let f : DField := { name := "x", kind := .initVar, init := false, kwOnly := some false }
  let i : DInfo := { params := {}, fields := [f], std := [], kw := [], generated := ["__init__", "__repr__", "__eq__"],
                     hash := .setNone, matchArgs := some [] }
  have h1 : processClass c = .ok i := by decide +kernel
  have h2 : bindArgs i.std i.kw [] [] = .ok [] := by decide +kernel
  obtain ⟨o, ho⟩ := h c i [] [] [] h1 h2
  have h3 : callInit i true [] [] = .error (.named "NameError" "name 'x' is not defined") := by decide +kernel
  rw [h3] at ho
  cases ho

/-- The narrowed statement, by the same check: with no such `InitVar`, or with no `__post_init__`, `__init__` raises only
what binding raises. -/
def InitBindsNarrow : Prop :=
  ∀ (i : DInfo) (post : Bool) (args : List Int) (kw b : List (String × Int)),
    (post = false ∨ i.fields.all (fun f => f.kind != .initVar || f.init) = true) →
    bindArgs i.std i.kw args kw = .ok b → callInit i post args kw = .ok (initBody i post b)

theorem initBindsNarrow_proven : InitBindsNarrow := by
  intro i post args kw b h hb
  simp only [callInit, hb]
  cases hf : i.fields.find? (fun f => f.kind == .initVar && !f.init) with
  | none => rfl
  | some f =>
    rcases h with h | h
    · simp [h]
    · have hm := List.mem_of_find?_eq_some hf
      have hp := List.find?_some hf
      have := List.all_eq_true.1 h f hm
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hp
      simp [hp.1, hp.2] at this

/-! ### Hash, equality, order, frozen -/

/-- `_hash_add`: a field is hashed when `hash=True`, or when `hash` is left to `None` and it is compared, so with `hash`
left out everywhere the hash reads exactly the fields of `__eq__`, which is what makes equal objects hash equally. -/
def HashFieldsSpec : Prop :=
  ∀ fs : List DField,
    (∀ f, f ∈ hashFields fs ↔ f ∈ fs ∧ (f.hash = some true ∨ (f.hash = none ∧ f.compare = true))) ∧
    ((∀ f ∈ fs, f.hash = none) → hashFields fs = fs.filter (·.compare))

theorem hashFieldsSpec_proven : HashFieldsSpec := by
  intro fs
  refine ⟨?_, ?_⟩
  · intro f
    simp only [hashFields, List.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      cases hh : f.hash with
      | none => simp only [hh] at h2; exact .inr ⟨rfl, h2⟩
      | some b => simp only [hh] at h2; simp [h2]
    · rintro ⟨h1, h2 | ⟨h2, h3⟩⟩
      · exact ⟨h1, by simp [h2]⟩
      · exact ⟨h1, by simp [h2, h3]⟩
  · intro h
    apply List.filter_congr
    intro f hf
    simp [h f hf]

/-- The `and` chain of `__eq__`: the first falsy result is the answer, whatever comes after it, which is not evaluated
and may raise; an exception before that propagates; if all before the last are true, the last is the answer whatever its
truth, so a non-boolean `==` comes back as it is. No field compared is `True`. -/
def AndChainSpec : Prop :=
  ∀ (α : Type) (yes x : α) (b : Bool) (e : PyExc) (pre : List α) (post : List (Py (α × Bool))),
    andChain yes [] = .ok yes ∧
    andChain yes (pre.map (fun a => .ok (a, true)) ++ .ok (x, false) :: post) = .ok x ∧
    andChain yes (pre.map (fun a => .ok (a, true)) ++ .error e :: post) = .error e ∧
    andChain yes (pre.map (fun a => .ok (a, true)) ++ [.ok (x, b)]) = .ok x

private theorem chain_cons {α : Type} (y a : α) (t : Py (α × Bool)) (r : List (Py (α × Bool))) :
    andChain y (.ok (a, true) :: t :: r) = andChain y (t :: r) := by
  simp [andChain]

theorem andChainSpec_proven : AndChainSpec := by
  intro α yes x b e pre post
  refine ⟨rfl, ?_, ?_, ?_⟩
  · induction pre with
    | nil =>
      cases post with
      | nil => rfl
      | cons u v => simp [andChain]
    | cons a p ih =>
      cases p with
      | nil =>
        simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append] at ih ⊢
        rw [chain_cons]
        exact ih
      | cons c d =>
        simp only [List.map_cons, List.cons_append] at ih ⊢
        rw [chain_cons]
        exact ih
  · induction pre with
    | nil =>
      cases post with
      | nil => rfl
      | cons u v => simp [andChain]
    | cons a p ih =>
      cases p with
      | nil =>
        simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append] at ih ⊢
        rw [chain_cons]
        exact ih
      | cons c d =>
        simp only [List.map_cons, List.cons_append] at ih ⊢
        rw [chain_cons]
        exact ih
  · induction pre with
    | nil => rfl
    | cons a p ih =>
      cases p with
      | nil =>
        simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append] at ih ⊢
        rw [chain_cons]
        exact ih
      | cons c d =>
        simp only [List.map_cons, List.cons_append] at ih ⊢
        rw [chain_cons]
        exact ih

/-- The generated `__eq__`: `self is other` is `True` without looking at a field, and another class is `NotImplemented`. -/
def EqPaths : Prop :=
  ∀ (α : Type) (yes : α) (sc : Bool) (ts : List (Py (α × Bool))),
    dcEq yes true sc ts = some (.ok yes) ∧ dcEq yes false false ts = none ∧
    dcEq yes false true ts = some (andChain yes ts)

theorem eqPaths_proven : EqPaths := by
  intro α yes sc ts
  simp [dcEq]

/-- The ordering methods compare as tuples: the first place that differs decides, and on equal lengths `<`, `==` and `>`
are exclusive and exhaustive, `<=` is not `>`, and `>=` is not `<`. Another class is `NotImplemented`. Docs: "as if it
were a tuple of its fields, in order". -/
def OrderSpec : Prop :=
  ∀ (a b : List Int) (x y : Int),
    (x ≠ y → tupLt (x :: a) (y :: b) = decide (x < y)) ∧ tupLt (x :: a) (x :: b) = tupLt a b ∧
    (a.length = b.length → (a = b ∨ tupLt a b = true ∨ tupLt b a = true) ∧ tupLt a a = false ∧
      ¬(tupLt a b = true ∧ tupLt b a = true) ∧
      dcOrder "le" true a b = some (!tupLt b a) ∧ dcOrder "ge" true a b = some (!tupLt a b)) ∧
    dcOrder "lt" true a b = some (tupLt a b) ∧ dcOrder "gt" true a b = some (tupLt b a) ∧
    dcOrder "lt" false a b = none

private theorem tup_irrefl (a : List Int) : tupLt a a = false := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp [tupLt, ih]

private theorem tup_tri (a b : List Int) (h : a.length = b.length) :
    (a = b ∨ tupLt a b = true ∨ tupLt b a = true) ∧ ¬(tupLt a b = true ∧ tupLt b a = true) := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => simp [tupLt]
    | cons _ _ => simp at h
  | cons x xs ih =>
    cases b with
    | nil => simp at h
    | cons y ys =>
      have hl : xs.length = ys.length := by simpa using h
      by_cases hxy : x = y
      · subst hxy
        have := ih ys hl
        simp only [tupLt, beq_self_eq_true, ↓reduceIte, List.cons.injEq, true_and]
        exact this
      · have h1 : (x == y) = false := by simpa using hxy
        have h2 : (y == x) = false := by
          have : y ≠ x := fun e => hxy e.symm
          simpa using this
        simp only [tupLt, h1, h2, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq]
        constructor
        · right
          omega
        · omega

theorem orderSpec_proven : OrderSpec := by
  intro a b x y
  refine ⟨?_, ?_, ?_, rfl, rfl, rfl⟩
  · intro h
    have : (x == y) = false := by simpa using h
    simp [tupLt, this]
  · simp [tupLt]
  · intro hl
    obtain ⟨h1, h2⟩ := tup_tri a b hl
    refine ⟨h1, tup_irrefl a, h2, ?_, ?_⟩
    · simp only [dcOrder, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.some.injEq]
      show (tupLt a b || a == b) = !tupLt b a
      by_cases he : a = b
      · subst he; simp [tup_irrefl]
      · have hb : (a == b) = false := by simpa using he
        cases h3 : tupLt a b <;> cases h4 : tupLt b a <;> simp_all
    · simp only [dcOrder, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.some.injEq]
      show (tupLt b a || a == b) = !tupLt a b
      by_cases he : a = b
      · subst he; simp [tup_irrefl]
      · have hb : (a == b) = false := by simpa using he
        cases h3 : tupLt a b <;> cases h4 : tupLt b a <;> simp_all

/-- A frozen class: on the class itself any attribute is refused, and on a subclass the fields, and nothing else, so that
a subclass that is not a dataclass can have attributes of its own. -/
def FrozenRule : Prop :=
  ∀ (fields : List String) (n : String),
    (frozenSet true fields n).raises "FrozenInstanceError" ∧ (frozenDel true fields n).raises "FrozenInstanceError" ∧
    (fields.contains n = true → (frozenSet false fields n).raises "FrozenInstanceError" ∧
      (frozenDel false fields n).raises "FrozenInstanceError") ∧
    (fields.contains n = false → frozenSet false fields n = .ok () ∧ frozenDel false fields n = .ok ())

theorem frozenRule_proven : FrozenRule := by
  intro fields n
  refine ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, ?_, ?_⟩
  · intro h
    exact ⟨⟨.named "FrozenInstanceError" s!"cannot assign to field '{n}'", by simp only [frozenSet, Bool.false_or, h, ↓reduceIte], rfl⟩,
      ⟨.named "FrozenInstanceError" s!"cannot delete field '{n}'", by simp only [frozenDel, Bool.false_or, h, ↓reduceIte], rfl⟩⟩
  · intro h
    exact ⟨by simp only [frozenSet, Bool.false_or, h, Bool.false_eq_true, ↓reduceIte],
      by simp only [frozenDel, Bool.false_or, h, Bool.false_eq_true, ↓reduceIte]⟩

/-- The name of an item, when it has one. -/
def itemName : MakeItem → Option String
  | .name s => some s
  | .named s => some s
  | _ => none

/-- `make_dataclass` accepts a list of fields exactly when every item has a name that is an identifier and not a keyword,
and no name repeats, and the fields are those names, in order. -/
def MakeExact : Prop :=
  ∀ (items : List MakeItem) (l : List String),
    makeNames items [] = .ok l ↔
      (items.map itemName = l.map some ∧ l.Nodup ∧ ∀ n ∈ l, isIdent n = true ∧ kwList.contains n = false)

private theorem make_cons {it : MakeItem} {n : String} (h : itemName it = some n) (r : List MakeItem)
    (seen : List String) : makeNames (it :: r) seen =
      if !isIdent n then .error (.typeError s!"Field names must be valid identifiers: '{n}'")
      else if kwList.contains n then .error (.typeError s!"Field names must not be keywords: '{n}'")
      else if seen.contains n then .error (.typeError s!"Field name duplicated: '{n}'")
      else makeNames r (seen ++ [n]) := by
  cases it with
  | name s => simp only [itemName, Option.some.injEq] at h; subst h; rfl
  | named s => simp only [itemName, Option.some.injEq] at h; subst h; rfl
  | notStr => simp [itemName] at h
  | bad => simp [itemName] at h

private theorem make_fwd (items : List MakeItem) :
    ∀ (seen l : List String), seen.Nodup → makeNames items seen = .ok l →
      ∃ ns, l = seen ++ ns ∧ items.map itemName = ns.map some ∧ l.Nodup ∧
        ∀ n ∈ ns, isIdent n = true ∧ kwList.contains n = false := by
  induction items with
  | nil =>
    intro seen l hs h
    simp only [makeNames, Except.ok.injEq] at h
    subst h
    exact ⟨[], by simp, rfl, hs, by simp⟩
  | cons it r ih =>
    intro seen l hs h
    cases hn : itemName it with
    | none =>
      cases it with
      | name s => simp [itemName] at hn
      | named s => simp [itemName] at hn
      | notStr => simp [makeNames] at h
      | bad => simp [makeNames] at h
    | some n =>
      rw [make_cons hn] at h
      split at h
      · simp at h
      rename_i h1
      split at h
      · simp at h
      rename_i h2
      split at h
      · simp at h
      rename_i h3
      have hs' : (seen ++ [n]).Nodup := by
        refine List.nodup_append.2 ⟨hs, by simp, ?_⟩
        intro a ha b hb he
        simp only [List.mem_singleton] at hb
        subst hb
        subst he
        exact h3 (by simpa using ha)
      obtain ⟨ns, h4, h5, h6, h7⟩ := ih _ _ hs' h
      refine ⟨n :: ns, by simp [h4], by simp [hn, h5], h6, ?_⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨by simpa using h1, Bool.eq_false_iff.2 h2⟩
      · exact h7 x hx

private theorem make_back (ns : List String) :
    ∀ (items : List MakeItem) (seen : List String), items.map itemName = ns.map some → (seen ++ ns).Nodup →
      (∀ n ∈ ns, isIdent n = true ∧ kwList.contains n = false) → makeNames items seen = .ok (seen ++ ns) := by
  induction ns with
  | nil =>
    intro items seen h _ _
    have : items = [] := by simpa using h
    subst this
    simp [makeNames]
  | cons n r ih =>
    intro items seen h hn hv
    cases items with
    | nil => simp at h
    | cons it t =>
      simp only [List.map_cons, List.cons.injEq] at h
      rw [make_cons h.1]
      have h0 := hv n (by simp)
      have hc : seen.contains n = false := by
        have hm := List.nodup_append.1 hn
        apply Bool.eq_false_iff.2
        intro hh
        exact hm.2.2 n (by simpa using hh) n (by simp) rfl
      simp only [h0.1, h0.2, hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      have e := ih t (seen ++ [n]) h.2 (by simpa using hn) (fun x hx => hv x (by simp [hx]))
      simpa using e

theorem makeExact_proven : MakeExact := by
  intro items l
  constructor
  · intro h
    obtain ⟨ns, h1, h2, h3, h4⟩ := make_fwd items [] l (by simp) h
    simp only [List.nil_append] at h1
    subst h1
    exact ⟨h2, h3, h4⟩
  · rintro ⟨h1, h2, h3⟩
    simpa using make_back l items [] h1 (by simpa using h2) h3

/-! ### `asdict` and `astuple` -/

mutual
  /-- A value with no dataclass instance in it. -/
  def DV.plain : DV → Bool
    | .inst _ _ => false
    | .list l | .tuple l | .named l | .listSub l | .tupleSub l => DV.plainL l
    | .dict k v | .dictSub k v | .defaultDict k v | .counter k v => DV.plainL k && DV.plainL v
    | _ => true

  def DV.plainL : List DV → Bool
    | [] => true
    | v :: r => v.plain && DV.plainL r
end

mutual
  /-- `asdict` and `astuple` agree below the first dataclass: the twins treat every container alike, whatever the
  factories, since those only act on instances. -/
  theorem twinV (fa : DictFact) (ft : TupFact) : (v : DV) → v.plain = true → asdictV fa v = astupleV ft v
    | .atom _, _ => by simp only [asdictV, astupleV]
    | .str _, _ => by simp only [asdictV, astupleV]
    | .copied _, _ => by simp only [asdictV, astupleV]
    | .unhash _, _ => by simp only [asdictV, astupleV]
    | .inst _ _, h => by simp [DV.plain] at h
    | .list l, h => by
      have e := twinL fa ft l (by simpa [DV.plain] using h)
      simp only [asdictV, astupleV, e]
    | .tuple l, h => by
      have e := twinL fa ft l (by simpa [DV.plain] using h)
      simp only [asdictV, astupleV, e]
    | .named l, h => by
      have e := twinL fa ft l (by simpa [DV.plain] using h)
      simp only [asdictV, astupleV, e]
    | .listSub l, h => by
      have e := twinL fa ft l (by simpa [DV.plain] using h)
      simp only [asdictV, astupleV, e]
    | .tupleSub l, h => by
      have e := twinL fa ft l (by simpa [DV.plain] using h)
      simp only [asdictV, astupleV, e]
    | .dict k v, h => by
      have h' : DV.plainL k = true ∧ DV.plainL v = true := by simpa [DV.plain] using h
      simp only [asdictV, astupleV, twinL fa ft k h'.1, twinL fa ft v h'.2]
    | .dictSub k v, h => by
      have h' : DV.plainL k = true ∧ DV.plainL v = true := by simpa [DV.plain] using h
      simp only [asdictV, astupleV, twinL fa ft k h'.1, twinL fa ft v h'.2]
    | .defaultDict k v, h => by
      have h' : DV.plainL k = true ∧ DV.plainL v = true := by simpa [DV.plain] using h
      simp only [asdictV, astupleV, twinL fa ft k h'.1, twinL fa ft v h'.2]
    | .counter k v, h => by
      have h' : DV.plainL k = true ∧ DV.plainL v = true := by simpa [DV.plain] using h
      simp only [asdictV, astupleV, twinL fa ft k h'.1, twinL fa ft v h'.2]

  theorem twinL (fa : DictFact) (ft : TupFact) : (l : List DV) → DV.plainL l = true → asdictL fa l = astupleL ft l
    | [], _ => by simp only [asdictL, astupleL]
    | v :: r, h => by
      have h' : v.plain = true ∧ DV.plainL r = true := by simpa [DV.plainL] using h
      simp only [asdictL, astupleL, twinV fa ft v h'.1, twinL fa ft r h'.2]
end

mutual
  /-- A value made only of leaves, lists and tuples. -/
  def DV.tree : DV → Bool
    | .atom _ | .str _ | .copied _ | .unhash _ => true
    | .list l | .tuple l | .named l | .listSub l | .tupleSub l => DV.treeL l
    | _ => false

  def DV.treeL : List DV → Bool
    | [] => true
    | v :: r => v.tree && DV.treeL r
end

mutual
  theorem treePlain : (v : DV) → v.tree = true → v.plain = true
    | .atom _, _ => by simp [DV.plain]
    | .str _, _ => by simp [DV.plain]
    | .copied _, _ => by simp [DV.plain]
    | .unhash _, _ => by simp [DV.plain]
    | .list l, h => by simpa [DV.plain] using treePlainL l (by simpa [DV.tree] using h)
    | .tuple l, h => by simpa [DV.plain] using treePlainL l (by simpa [DV.tree] using h)
    | .named l, h => by simpa [DV.plain] using treePlainL l (by simpa [DV.tree] using h)
    | .listSub l, h => by simpa [DV.plain] using treePlainL l (by simpa [DV.tree] using h)
    | .tupleSub l, h => by simpa [DV.plain] using treePlainL l (by simpa [DV.tree] using h)
    | .inst _ _, h => by simp [DV.tree] at h
    | .dict _ _, h => by simp [DV.tree] at h
    | .dictSub _ _, h => by simp [DV.tree] at h
    | .defaultDict _ _, h => by simp [DV.tree] at h
    | .counter _ _, h => by simp [DV.tree] at h

  theorem treePlainL : (l : List DV) → DV.treeL l = true → DV.plainL l = true
    | [], _ => by simp [DV.plainL]
    | v :: r, h => by
      have h' : v.tree = true ∧ DV.treeL r = true := by simpa [DV.treeL] using h
      simp [DV.plainL, treePlain v h'.1, treePlainL r h'.2]
end

mutual
  theorem treeId (fa : DictFact) : (v : DV) → v.tree = true → asdictV fa v = .ok v
    | .atom _, _ => by simp only [asdictV]
    | .str _, _ => by simp only [asdictV]
    | .copied _, _ => by simp only [asdictV]
    | .unhash _, _ => by simp only [asdictV]
    | .list l, h => by simp only [asdictV, treeIdL fa l (by simpa [DV.tree] using h)]
    | .tuple l, h => by simp only [asdictV, treeIdL fa l (by simpa [DV.tree] using h)]
    | .named l, h => by simp only [asdictV, treeIdL fa l (by simpa [DV.tree] using h)]
    | .listSub l, h => by simp only [asdictV, treeIdL fa l (by simpa [DV.tree] using h)]
    | .tupleSub l, h => by simp only [asdictV, treeIdL fa l (by simpa [DV.tree] using h)]
    | .inst _ _, h => by simp [DV.tree] at h
    | .dict _ _, h => by simp [DV.tree] at h
    | .dictSub _ _, h => by simp [DV.tree] at h
    | .defaultDict _ _, h => by simp [DV.tree] at h
    | .counter _ _, h => by simp [DV.tree] at h

  theorem treeIdL (fa : DictFact) : (l : List DV) → DV.treeL l = true → asdictL fa l = .ok l
    | [], _ => by simp only [asdictL]
    | v :: r, h => by
      have h' : v.tree = true ∧ DV.treeL r = true := by simpa [DV.treeL] using h
      simp only [asdictL, treeId fa v h'.1, treeIdL fa r h'.2]
end

/-- `asdict` and `astuple` on an instance of leaves, lists and tuples: `asdict` gives its names against its values,
unchanged, and `astuple` the values; with `dict_factory=list`, the pairs. Containers below the first instance go the same
way in both twins, whatever the factories. The docstrings of the two functions, and of their examples. -/
def AsdictAstuple : Prop :=
  ∀ (names : List String) (vals : List DV), DV.treeL vals = true →
    asdictV .dict (.inst names vals) = .ok (.dict (names.map .str) vals) ∧
    asdictV .dictLike (.inst names vals) = .ok (.dict (names.map .str) vals) ∧
    asdictV .list (.inst names vals) = .ok (.list ((names.map DV.str).zip vals |>.map fun p => .tuple [p.1, p.2])) ∧
    astupleV .tuple (.inst names vals) = .ok (.tuple vals) ∧
    astupleV .list (.inst names vals) = .ok (.list vals)

theorem asdictAstuple_proven : AsdictAstuple := by
  intro names vals h
  have ha : ∀ f, asdictL f vals = .ok vals := fun f => treeIdL f vals h
  have ht : ∀ f g, astupleL f vals = asdictL g vals := fun f g => (twinL g f vals (treePlainL vals h)).symm
  have ht' : ∀ f, astupleL f vals = .ok vals := fun f => (ht f .dict).trans (ha .dict)
  simp only [asdictV, astupleV, ha, ht']
  simp

/-- The twins agree below the first instance: for a value with no dataclass in it, `asdict` and `astuple` give the same
result, or the same failure, whatever their factories, down to the dict subclasses. -/
def TwinsOnPlain : Prop :=
  ∀ (fa : DictFact) (ft : TupFact) (v : DV), v.plain = true → asdictV fa v = astupleV ft v

theorem twinsOnPlain_proven : TwinsOnPlain := fun fa ft v h => twinV fa ft v h

mutual
  /-- `dict_factory=dict` takes a fast path, and `lambda p: dict(p)` the general one: their results are the same. -/
  theorem fastSlowV : (v : DV) → asdictV .dict v = asdictV .dictLike v
    | .atom _ => by simp only [asdictV]
    | .str _ => by simp only [asdictV]
    | .copied _ => by simp only [asdictV]
    | .unhash _ => by simp only [asdictV]
    | .inst n l => by simp only [asdictV, fastSlowL l]
    | .list l => by simp only [asdictV, fastSlowL l]
    | .tuple l => by simp only [asdictV, fastSlowL l]
    | .named l => by simp only [asdictV, fastSlowL l]
    | .listSub l => by simp only [asdictV, fastSlowL l]
    | .tupleSub l => by simp only [asdictV, fastSlowL l]
    | .dict k v => by simp only [asdictV, fastSlowL k, fastSlowL v]
    | .dictSub k v => by simp only [asdictV, fastSlowL k, fastSlowL v]
    | .defaultDict k v => by simp only [asdictV, fastSlowL k, fastSlowL v]
    | .counter k v => by simp only [asdictV, fastSlowL k, fastSlowL v]

  theorem fastSlowL : (l : List DV) → asdictL .dict l = asdictL .dictLike l
    | [] => by simp only [asdictL]
    | v :: r => by simp only [asdictL, fastSlowV v, fastSlowL r]
end

/-- The fast path of `asdict` and the general one agree on every value. -/
def FastSlowAgree : Prop := ∀ v : DV, asdictV .dict v = asdictV .dictLike v

theorem fastSlowAgree_proven : FastSlowAgree := fastSlowV

/-- A dict subclass comes back with its items: Lib/dataclasses.py:1565 calls `obj_type` on pairs. False for `Counter`,
which counts what it is given, so a `Counter` field becomes a `Counter` of `(key, count)` pairs, in `asdict` and in
`astuple`. -/
def CounterSurvives : Prop :=
  ∀ ks vs : List DV, DV.treeL ks = true → DV.treeL vs = true → asdictV .dict (.counter ks vs) = .ok (.counter ks vs)

theorem counterSurvives_refuted : ¬CounterSurvives := by
  intro h
  have := h [.atom 1] [.atom 2] rfl rfl
  have e : asdictV .dict (.counter [.atom 1] [.atom 2]) = .ok (.counter [.tuple [.atom 1, .atom 2]] [.atom 1]) := rfl
  rw [e] at this
  simp at this

/-- `asdict` works where `astuple` does. False: a frozen dataclass as a key of a `dict` field becomes a `dict`, which is
not hashable, while `astuple` makes it a tuple. -/
def AsdictWhereAstuple : Prop :=
  ∀ (v r : DV), astupleV .tuple v = .ok r → ∃ r', asdictV .dict v = .ok r'

theorem asdictWhereAstuple_refuted : ¬AsdictWhereAstuple := by
  intro h
  let v : DV := .inst ["x"] [.dict [.inst ["a"] [.atom 1]] [.atom 2]]
  obtain ⟨r', hr⟩ := h v (.tuple [.dict [.tuple [.atom 1]] [.atom 2]]) rfl
  have e : asdictV .dict v = .error (.typeError "~unhashable type") := rfl
  rw [e] at hr
  cases hr

end PyLean.CoreLibs.EnumDC
