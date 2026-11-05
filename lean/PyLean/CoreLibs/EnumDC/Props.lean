import PyLean.CoreLibs.EnumDC.Model

/-!
Properties of the `Flag` and dataclass mirrors.
-/

namespace PyLean.CoreLibs.EnumDC

open PyLean

/-- `|`, `&` and `^` on two values of a `Flag` class commute under every boundary, for every class:
they build the class from the commuted integer. `Flag` docs, flags as bit sets. -/
def FlagOpsCommute : Prop :=
  ∀ (c : FlagCls) (a b : Nat),
    c.orOp a b = c.orOp b a ∧ c.andOp a b = c.andOp b a ∧ c.xorOp a b = c.xorOp b a

theorem flagOpsCommute_proven : FlagOpsCommute := by
  intro c a b
  simp [FlagCls.orOp, FlagCls.andOp, FlagCls.xorOp, Nat.or_comm, Nat.and_comm, Nat.xor_comm]

/-- `other in self` is bit containment: every bit of `other` is in `self`. Docstring of
`Flag.__contains__`: "Returns True if self has at least the same flags set as other." -/
def FlagContainsBits : Prop :=
  ∀ self other : Nat, flagContains self other = true ↔
    ∀ i, other.testBit i = true → self.testBit i = true

theorem flagContainsBits_proven : FlagContainsBits := by
  intro self other
  simp only [flagContains, beq_iff_eq]
  constructor
  · intro h i hi
    have := congrArg (fun n => n.testBit i) h
    simp only [Nat.testBit_and, hi, Bool.true_and] at this
    simpa [hi] using this
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and]
    cases ho : other.testBit i with
    | false => simp
    | true => simp [h i ho]

/-- A value of a `STRICT` flag class that the class accepts and that is not zero has a name: it is a
combination of members. False: with `A = 1` and `X = 6`, `F(3)` raises "no members with value 2", but
`F(2)` is accepted as a nameless pseudo-member, because the test at Lib/enum.py:1555 returns before the
strict test at :1557. Then `F(2) | F.A` raises `ValueError` on two valid operands. -/
def StrictValuesAreNamed : Prop :=
  ∀ (c : FlagCls) (v : Int) (n : Nat) (name : Option String), c.boundary = .strict →
    c.call v = .ok (.flag n name) → n ≠ 0 → name.isSome = true

theorem strictValuesAreNamed_refuted : ¬StrictValuesAreNamed := by
  intro h
  have := h { name := "F", members := [("A", 1), ("X", 6)], boundary := .strict } 2 2 none rfl (by decide) (by decide)
  simp at this

/-- The bit helpers on concrete shapes used by every `Flag`: zero is not a single bit, the
next `auto()` value after a power of two doubles it, and `Enum`'s next value follows the largest. -/
def AutoValues : Prop :=
  isSingleBit 0 = false ∧
  (∀ (x : Int) (xs : List Int), enumNext 0 (x :: xs) = xs.foldl max x + 1) ∧
  (∀ start, enumNext start [] = start) ∧
  (∀ (start : Option Nat) (l : List Nat), flagNext start 0 l = start.getD 1) ∧
  (∀ (s : Nat), flagNext (some s) 0 [] = s)

theorem autoValues_proven : AutoValues := by
  refine ⟨rfl, fun _ _ => rfl, fun _ => rfl, ?_, ?_⟩
  · intro start l
    simp [flagNext]
  · intro s
    simp [flagNext]

/-- The if-statement version of the table, from bpo-32929 referenced at Lib/dataclasses.py:974. -/
def hashByIf (unsafeHash eq frozen explicit : Bool) : HashAction :=
  if unsafeHash then (if explicit then .exception else .add)
  else if eq then
    if explicit then .none else (if frozen then .add else .setNone)
  else .none

/-- `_hash_action` is the rule: `unsafe_hash` adds or conflicts with an explicit `__hash__`; `eq`
without `frozen` makes the class unhashable, with `frozen` it adds a hash; an explicit `__hash__` is
otherwise kept. Sixteen rows, one rule. Docs of `dataclass`. -/
def HashTableIsRule : Prop :=
  ∀ u e f h : Bool, hashAction u e f h = hashByIf u e f h

theorem hashTableIsRule_proven : HashTableIsRule := by
  intro u e f h
  cases u <;> cases e <;> cases f <;> cases h <;> rfl

/-- `_fields_in_init_order`: a field reaches `__init__` exactly when `init` is true, once, positional
ones first. Docs of `dataclass`, keyword-only fields. -/
def InitOrderPartition : Prop :=
  ∀ (fs : List FieldSpec) (f : FieldSpec),
    (f ∈ (initOrder fs).1 ∨ f ∈ (initOrder fs).2) ↔ (f ∈ fs ∧ f.init = true)

theorem initOrderPartition_proven : InitOrderPartition := by
  intro fs f
  simp only [initOrder, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true']
  cases f.kwOnly <;> simp

/-- `__init__` is rejected exactly when a field without default follows one with a default among the
init fields: an accepted class has no such pair. Docs of `dataclass`. -/
def InitDefaultOrderSound : Prop :=
  ∀ (fs pre post : List FieldSpec) (d f : FieldSpec),
    initDefaultOrder none fs = .ok () → fs = pre ++ d :: post → d.init = true → d.hasDefault = true →
    f ∈ post → f.init = true → f.hasDefault = true

theorem order_seen (s : String) : ∀ fs : List FieldSpec, initDefaultOrder (some s) fs = .ok () →
    ∀ f ∈ fs, f.init = true → f.hasDefault = true
  | [], _, _, h, _ => by cases h
  | g :: gs, hok, f, hf, hi => by
    simp only [initDefaultOrder] at hok
    rcases List.mem_cons.mp hf with rfl | hm
    · simp only [hi, ite_true] at hok
      cases hd : f.hasDefault with
      | true => rfl
      | false => simp [hd] at hok
    · split at hok
      · split at hok
        · exact order_seen _ gs hok f hm hi
        · cases hok
      · exact order_seen s gs hok f hm hi

theorem order_any : ∀ (s : Option String) (pre post : List FieldSpec) (d f : FieldSpec),
    initDefaultOrder s (pre ++ d :: post) = .ok () → d.init = true → d.hasDefault = true →
    f ∈ post → f.init = true → f.hasDefault = true
  | s, [], post, d, f, h, h1, h2, hf, hi => by
    simp only [List.nil_append, initDefaultOrder, h1, h2, ite_true] at h
    exact order_seen _ post h f hf hi
  | s, g :: gs, post, d, f, h, h1, h2, hf, hi => by
    simp only [List.cons_append, initDefaultOrder] at h
    split at h
    · split at h
      · exact order_any _ gs post d f h h1 h2 hf hi
      · split at h
        · cases h
        · exact order_any _ gs post d f h h1 h2 hf hi
    · exact order_any _ gs post d f h h1 h2 hf hi

theorem initDefaultOrderSound_proven : InitDefaultOrderSound := by
  intro fs pre post d f h he h1 h2 hf hi
  subst he
  exact order_any none pre post d f h h1 h2 hf hi

/-- `_tuple_str` gives `()` for no fields and a trailing comma otherwise, so a single field still makes
a tuple; `fields()` lists no pseudo-field; `field` rejects both defaults; `order` needs `eq`. -/
def DataclassHelpers : Prop :=
  tupleStr "self" [] = "()" ∧
  (∀ fs : List FieldSpec, ∀ f ∈ fieldsOf fs, f.kind = 0) ∧
  fieldCheck true true = .error (.valueError "cannot specify both default and default_factory") ∧
  (∀ a b, a = false ∨ b = false → fieldCheck a b = .ok ()) ∧
  decoratorCheck true false false false false = .error (.valueError "eq must be true if order is true")

theorem dataclassHelpers_proven : DataclassHelpers := by
  refine ⟨rfl, ?_, rfl, ?_, rfl⟩
  · intro fs f hf
    have := (List.mem_filter.mp hf).2
    simpa using this
  · intro a b h
    cases a <;> cases b
    · rfl
    · rfl
    · rfl
    · simp at h

/-- `replace` on a class whose fields are all plain `init` fields keeps the caller's changes and adds
every other field from the instance, so `__init__` gets a value for every field. `replace` docs:
"Creates a new object of the same type as obj, replacing fields with values from changes." -/
def ReplaceFillsFields : Prop :=
  ∀ (α : Type) (fs : List FieldSpec) (get : String → α) (changes : List (String × α)),
    (∀ f ∈ fs, f.init = true ∧ f.kind = 0) →
    ∃ r, replaceArgs fs get changes = .ok r ∧ ∀ f ∈ fs, f.name ∈ r.map Prod.fst

theorem lookup_mem_keys {α : Type} : ∀ (l : List (String × α)) (k : String),
    (l.lookup k).isSome = true → k ∈ l.map Prod.fst
  | [], _, h => by simp at h
  | q :: qs, k, h => by
    by_cases e : k = q.1
    · simp [e]
    · have e' : (k == q.1) = false := by simpa using e
      simp only [List.lookup, e'] at h
      exact List.mem_cons_of_mem _ (lookup_mem_keys qs k h)

theorem replace_fold {α : Type} (get : String → α) (changes : List (String × α)) :
    ∀ (fs : List FieldSpec) (acc : List (String × α)), (∀ f ∈ fs, f.init = true ∧ f.kind = 0) →
    ∃ r, fs.foldlM (replaceStep changes get) acc = .ok r ∧
      (∀ n ∈ acc.map Prod.fst, n ∈ r.map Prod.fst) ∧
      ∀ f ∈ fs, (f.name ∈ r.map Prod.fst ∨ (changes.lookup f.name).isSome = true)
  | [], acc, _ => ⟨acc, rfl, fun _ h => h, by simp⟩
  | f :: fs, acc, h => by
    obtain ⟨hi, hk⟩ := h f (by simp)
    have hrest : ∀ g ∈ fs, g.init = true ∧ g.kind = 0 := fun g hg => h g (by simp [hg])
    have hk1 : (f.kind == 1) = false := by simp [hk]
    have hk2 : (f.kind == 2) = false := by simp [hk]
    cases hl : (changes.lookup f.name) with
    | some v =>
      have hs : replaceStep changes get acc f = .ok acc := by
        simp [replaceStep, hk1, hi, hl]
      obtain ⟨r, h1, h2, h3⟩ := replace_fold get changes fs acc hrest
      refine ⟨r, by simpa [List.foldlM_cons, hs, bind, Except.bind] using h1, h2, ?_⟩
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact Or.inr (by simp [hl])
      · exact h3 g hg
    | none =>
      have hs : replaceStep changes get acc f = .ok (acc ++ [(f.name, get f.name)]) := by
        simp [replaceStep, hk1, hk2, hi, hl]
      obtain ⟨r, h1, h2, h3⟩ := replace_fold get changes fs (acc ++ [(f.name, get f.name)]) hrest
      refine ⟨r, by simpa [List.foldlM_cons, hs, bind, Except.bind] using h1, ?_, ?_⟩
      · intro n hn
        exact h2 n (by simp only [List.map_append, List.mem_append]; exact Or.inl hn)
      · intro g hg
        rcases List.mem_cons.mp hg with rfl | hg
        · exact Or.inl (h2 _ (by simp))
        · exact h3 g hg

theorem replaceFillsFields_proven : ReplaceFillsFields := by
  intro α fs get changes h
  obtain ⟨r, h1, h2, h3⟩ := replace_fold get changes fs changes h
  refine ⟨r, h1, ?_⟩
  intro f hf
  rcases h3 f hf with h4 | h4
  · exact h4
  · exact h2 _ (lookup_mem_keys _ _ h4)

end PyLean.CoreLibs.EnumDC
