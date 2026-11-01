import PyLean.CoreLibs.EnumDC.EnumClass

/-!
Properties of `EnumDict`, the functional API, the lookups and the `Flag` operators.
-/

namespace PyLean.CoreLibs.EnumDC

open PyLean

theorem set_private {d : EnumDict} {key : Name} (v : EV) (h : d.privateName key = true) :
    d.set key v = .ok (d.store key v) := by
  simp [EnumDict.set, h]

theorem set_plain {d : EnumDict} {key : Name} (v : EV) (h1 : d.privateName key = false)
    (h2 : isSunder key = false) (h3 : isDunder key = false) (h4 : d.memberNames.contains key = false)
    (h5 : d.ignore.contains key = false) : d.set key v = d.setValue key v := by
  simp only [EnumDict.set, h1, h2, h3, h4, h5, Bool.false_eq_true, ↓reduceIte]

/-- The order of `EnumDict.__setitem__`, for every key and value. A private name of the class is a plain attribute
whatever it holds. A reserved sunder name is a `ValueError`. Past those, a name that is already a member is a
`TypeError`: "If an enum member name is used twice, an error is raised". A name in `_ignore_`, a `nonmember` and a
descriptor add no member, and a plain value on a name already in the body, a descriptor say, is the same `TypeError`.
Docstring of `__setitem__`. -/
def EnumDictBranches : Prop :=
  ∀ (d : EnumDict) (key : Name) (v : EV) (a : Atom) (i : Nat),
    (d.privateName key = true → ∃ d', d.set key v = .ok d' ∧ d'.memberNames = d.memberNames) ∧
    (d.privateName key = false → isSunder key = true → sunderReserved key = true →
      (d.set key v).raises "ValueError") ∧
    (d.privateName key = false → isSunder key = false → isDunder key = false →
      (d.memberNames.contains key = true → (d.set key v).raises "TypeError") ∧
      (d.memberNames.contains key = false →
        (d.ignore.contains key = true → ∃ d', d.set key v = .ok d' ∧ d'.memberNames = d.memberNames) ∧
        (d.ignore.contains key = false →
          (∃ d', d.set key (.nonmember v) = .ok d' ∧ d'.memberNames = d.memberNames) ∧
          (∃ d', d.set key (.descr i) = .ok d' ∧ d'.memberNames = d.memberNames) ∧
          (d.has key = true → (d.set key (.atom a)).raises "TypeError"))))

theorem enumDictBranches_proven : EnumDictBranches := by
  intro d key v a i
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact ⟨_, set_private v h, rfl⟩
  · intro h1 h2 h3
    refine ⟨.valueError "~_sunder_ names are reserved for future Enum use", ?_, rfl⟩
    simp [EnumDict.set, h1, h2, h3]
  · intro h1 h2 h3
    refine ⟨?_, ?_⟩
    · intro h4
      refine ⟨.typeError "~already defined as", ?_, rfl⟩
      simp only [EnumDict.set, h1, h2, h3, h4, Bool.false_eq_true, ↓reduceIte]
    · intro h4
      refine ⟨?_, ?_⟩
      · intro h5
        refine ⟨d.store key v, ?_, rfl⟩
        simp only [EnumDict.set, h1, h2, h3, h4, h5, Bool.false_eq_true, ↓reduceIte]
      · intro h5
        refine ⟨⟨d.store key v, ?_, rfl⟩, ⟨d.store key (.descr i), ?_, rfl⟩, ?_⟩
        · rw [set_plain _ h1 h2 h3 h4 h5]; rfl
        · rw [set_plain _ h1 h2 h3 h4 h5]; rfl
        · intro h6
          refine ⟨.typeError "~already defined as", ?_, rfl⟩
          rw [set_plain _ h1 h2 h3 h4 h5]
          simp [EnumDict.setValue, EnumDict.storeMember, h6]

theorem storeMember_names {d d' : EnumDict} {key : Name} {v : EV} (h : d.storeMember key v = .ok d') :
    d'.memberNames = d.memberNames ++ [key] := by
  unfold EnumDict.storeMember at h
  split at h
  · simp at h
  · simp only at h
    have aux : ∀ (s : Bool) (l : List Atom), d.addAuto key s l = .ok d' →
        d'.memberNames = d.memberNames ++ [key] := by
      intro s l hh
      unfold EnumDict.addAuto at hh
      split at hh
      · simp at hh
      · simp only [Except.ok.injEq] at hh
        subst hh
        rfl
    split at h
    · exact aux _ _ h
    · split at h
      · exact aux _ _ h
      · simp only [Except.ok.injEq] at h
        subst h
        rfl
    · simp only [Except.ok.injEq] at h
      subst h
      rfl

/-- A name is added to `member_names` only when it is new, whatever the key and the value, so `member_names` has no
repeats: the sentence "Track enum member order and ensure member names are not reused" of the `EnumDict` docstring,
checked on every path of `__setitem__`. -/
def MemberNamesNew : Prop :=
  ∀ (d d' : EnumDict) (key : Name) (v : EV), d.set key v = .ok d' →
    d'.memberNames = d.memberNames ∨
      (d.memberNames.contains key = false ∧ d'.memberNames = d.memberNames ++ [key])

theorem memberNamesNew_proven : MemberNamesNew := by
  intro d d' key v h
  unfold EnumDict.set at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    exact .inl rfl
  split at h
  · split at h
    · simp at h
    split at h
    · split at h
      · simp at h
      simp only [Except.ok.injEq] at h
      subst h
      exact .inl rfl
    split at h
    · split at h
      · simp at h
      split at h
      · simp at h
      simp only [Except.ok.injEq] at h
      subst h
      exact .inl rfl
    simp only [Except.ok.injEq] at h
    subst h
    exact .inl rfl
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    exact .inl rfl
  split at h
  · simp at h
  rename_i h4
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    exact .inl rfl
  have hm : d.memberNames.contains key = false := by simpa using h4
  unfold EnumDict.setValue at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    exact .inl rfl
  · simp only [Except.ok.injEq] at h
    subst h
    exact .inl rfl
  · simp only [Except.ok.injEq] at h
    subst h
    exact .inl rfl
  · split at h
    · simp only [Except.ok.injEq] at h
      subst h
      exact .inl rfl
    · exact .inr ⟨hm, storeMember_names h⟩
  · exact .inr ⟨hm, storeMember_names h⟩

/-- A `_ignore_` name cannot be set to a name that is already a member, and an ignored name never becomes one: the
`ValueError` of Lib/enum.py:381-385, and the branch at :392. `__order__` is stored as `_order_`. Everything `_generate_next_value_`
needs: it is a `TypeError` once `auto()` has been used, and otherwise it is what the next `auto()` calls. -/
def EnumDictSunders : Prop :=
  ∀ (d : EnumDict) (l : List Name) (v : EV) (g : Gen), d.privateName "_ignore_".toList = false →
    d.privateName "_generate_next_value_".toList = false →
    (l.any d.memberNames.contains = true → (d.set "_ignore_".toList (.names l)).raises "ValueError") ∧
    (l.any d.memberNames.contains = false →
      ∃ d', d.set "_ignore_".toList (.names l) = .ok d' ∧ d'.ignore = l ∧ d'.memberNames = d.memberNames) ∧
    (d.autoCalled = true → (d.set "_generate_next_value_".toList (.gen g)).raises "TypeError") ∧
    (d.autoCalled = false → ∃ d', d.set "_generate_next_value_".toList (.gen g) = .ok d' ∧ d'.gen = g)

private theorem sunder_ignore : isSunder "_ignore_".toList = true := by decide +kernel
private theorem reserved_ignore : sunderReserved "_ignore_".toList = false := by decide +kernel
private theorem sunder_gnv : isSunder "_generate_next_value_".toList = true := by decide +kernel
private theorem reserved_gnv : sunderReserved "_generate_next_value_".toList = false := by decide +kernel
private theorem ignore_ne_gnv : ("_ignore_".toList == "_generate_next_value_".toList) = false := by decide +kernel

theorem enumDictSunders_proven : EnumDictSunders := by
  intro d l v g hi hg
  have seti : ∀ w, d.set "_ignore_".toList w =
      (match ignoreList w with
       | .error e => .error e
       | .ok l =>
        if l.any d.memberNames.contains then .error (.valueError "~_ignore_ cannot specify already set names")
        else .ok ({ d with ignore := l }.store "_ignore_".toList (.names l))) := by
    intro w
    simp only [EnumDict.set, hi, sunder_ignore, reserved_ignore, ignore_ne_gnv, Bool.false_eq_true, ↓reduceIte,
      beq_self_eq_true]
    rfl
  have setg : ∀ w, d.set "_generate_next_value_".toList w =
      (if d.autoCalled then .error (.typeError "_generate_next_value_ must be defined before members")
       else .ok ({ d with gen := genOf w }.store "_generate_next_value_".toList w)) := by
    intro w
    simp only [EnumDict.set, hg, sunder_gnv, reserved_gnv, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    refine ⟨.valueError "~_ignore_ cannot specify already set names", ?_, rfl⟩
    rw [seti]
    simp only [ignoreList, h, ↓reduceIte]
  · intro h
    refine ⟨{ d with ignore := l }.store "_ignore_".toList (.names l), ?_, rfl, rfl⟩
    rw [seti]
    simp only [ignoreList, h, Bool.false_eq_true, ↓reduceIte]
  · intro h
    refine ⟨.typeError "_generate_next_value_ must be defined before members", ?_, rfl⟩
    rw [setg]
    simp [h]
  · intro h
    refine ⟨{ d with gen := g }.store "_generate_next_value_".toList (.gen g), ?_, rfl⟩
    rw [setg]
    simp only [genOf, h, Bool.false_eq_true, ↓reduceIte]

/-! ### `auto()` and the functional API -/

/-- The values `1 .. k`. -/
def iota (k : Nat) : List EV := (List.range k).map (fun (i : Nat) => .atom (.int ((i : Int) + 1)))

private theorem intsOf_iota (k : Nat) :
    intsOf (iota k) = (List.range k).map (fun i : Nat => (i : Int) + 1) := by
  simp only [intsOf, iota, List.filterMap_map]
  induction k with
  | zero => rfl
  | succ n ih => simp [List.range_succ, List.filterMap_append, ih]

private theorem iota_succ (k : Nat) : iota (k + 1) = iota k ++ [.atom (.int ((k : Int) + 1))] := by
  simp [iota, List.range_succ]

private theorem max_range (k : Nat) :
    ((List.range k).map (fun i : Nat => (i : Int) + 1)).foldl max 0 = (k : Int) := by
  induction k with
  | zero => rfl
  | succ n ih =>
    simp only [List.range_succ, List.map_append, List.foldl_append, ih, List.map_cons, List.map_nil, List.foldl_cons,
      List.foldl_nil]
    omega

theorem sortable_ints (l : List EV) (h : ∀ v ∈ l, ∃ n : Int, v = .atom (.int n)) : sortable l = true := by
  match l, h with
  | [], _ => rfl
  | [_], _ => rfl
  | x :: y :: r, h =>
    obtain ⟨n, rfl⟩ := h x (by simp)
    simp only [sortable, sortRank, Option.isSome_some, Bool.true_and, List.all_eq_true]
    intro z hz
    obtain ⟨m, rfl⟩ := h z (List.mem_cons_of_mem _ hz)
    simp [sortRank]

theorem enumGenerate_iota (k : Nat) : enumGenerate 1 (iota k) = .ok (.int ((k : Int) + 1)) := by
  cases k with
  | zero => rfl
  | succ n =>
    have hne : (iota (n + 1)).isEmpty = false := by simp [iota]
    have hs : sortable (iota (n + 1)) = true := by
      apply sortable_ints
      intro v hv
      simp only [iota, List.mem_map] at hv
      obtain ⟨i, _, rfl⟩ := hv
      exact ⟨_, rfl⟩
    have hi := intsOf_iota (n + 1)
    have hm := max_range (n + 1)
    rw [List.range_succ_eq_map, List.map_cons, List.foldl_cons] at hm
    rw [List.range_succ_eq_map, List.map_cons] at hi
    simp only [enumGenerate, hne, hs, Bool.false_eq_true, ↓reduceIte, Bool.not_true, hi]
    have e : max (0 : Int) (((0 : Nat) : Int) + 1) = ((0 : Nat) : Int) + 1 := by decide
    rw [e] at hm
    rw [hm]

/-- A name that `__setitem__` treats as ordinary in a class called `c`. -/
structure Ordinary (c key : Name) : Prop where
  priv : isPrivate c key = false
  sun : isSunder key = false
  dun : isDunder key = false

def autoBody (names : List Name) : List (Name × EV) := names.map (fun n => (n, .atom (.auto none)))

/-- `class c(Enum)` with a body, as `__prepare__`, the assignments, and `EnumType.__new__`. -/
def classBody (k : EKind) (first : Gen) (cls : Name) (body : List (Name × EV)) : Py EClass :=
  match enumPrepare cls first with
  | .error e => .error e
  | .ok d =>
    match d.setAll body with
    | (_, some e) => .error e
    | (d', none) => enumTypeNew k d'

private theorem any_dictSet (l : List (Name × EV)) (k m : Name) (v : EV) :
    (dictSet l k v).any (fun p => p.1 == m) = (l.any (fun p => p.1 == m) || k == m) := by
  unfold dictSet
  split
  · rename_i h
    induction l with
    | nil => simp at h
    | cons x xs ih =>
      by_cases hx : x.1 = k
      · simp only [List.map_cons, hx, beq_self_eq_true, ↓reduceIte, List.any_cons]
        have : (xs.map (fun p => if (p.1 == k) = true then (k, v) else p)).any (fun p => p.1 == m)
            = (xs.any (fun p => p.1 == m) || (k == m && xs.any (fun p => p.1 == k))) := by
          clear ih h
          induction xs with
          | nil => simp
          | cons y ys ih2 =>
            by_cases hy : y.1 = k
            · simp only [List.map_cons, hy, beq_self_eq_true, ↓reduceIte, List.any_cons, ih2, Bool.true_or,
                Bool.and_true]
              cases k == m <;> simp
            · have : (y.1 == k) = false := by simpa using hy
              simp only [List.map_cons, this, Bool.false_eq_true, ↓reduceIte, List.any_cons, ih2, Bool.false_or]
              cases y.1 == m <;> simp
        rw [this]
        cases k == m <;> simp
      · have hb : (x.1 == k) = false := by simpa using hx
        have h' : xs.any (fun p => p.1 == k) = true := by
          simpa [List.any_cons, hb] using h
        simp only [List.map_cons, hb, Bool.false_eq_true, ↓reduceIte, List.any_cons, ih h', Bool.or_assoc]
  · simp [List.any_append]

private theorem has_store (d : EnumDict) (k m : Name) (v : EV) :
    (d.store k v).has m = (d.has m || k == m) := by
  simp [EnumDict.has, EnumDict.store, any_dictSet]

/-- The two ways of building a class keep the same tables; only `_auto_called` differs. -/
structure Twin (a b : EnumDict) : Prop where
  items : a.items = b.items
  names : a.memberNames = b.memberNames
  last : a.lastValues = b.lastValues
  ignore : a.ignore = b.ignore
  cls : a.clsName = b.clsName
  gen : a.gen = b.gen

private theorem set_auto {d : EnumDict} {c n : Name} {k : Nat} (o : Ordinary c n) (hc : d.clsName = some c)
    (hg : d.gen = .enum) (hi : d.ignore = []) (hl : d.lastValues = iota k) (hm : d.memberNames.contains n = false)
    (hh : d.has n = false) :
    d.set n (.atom (.auto none)) = .ok { d.store n (.atom (.int ((k : Int) + 1))) with
      memberNames := d.memberNames ++ [n], lastValues := iota (k + 1), autoCalled := true } := by
  have hp : d.privateName n = false := by simp [EnumDict.privateName, hc, o.priv]
  rw [set_plain _ hp o.sun o.dun hm (by simp [hi])]
  simp [EnumDict.setValue, EnumDict.storeMember, hh, EnumDict.addAuto, autoLoop, hg, Gen.call, hl, enumGenerate_iota,
    iota_succ]

private theorem set_int {d : EnumDict} {c n : Name} (o : Ordinary c n) (hc : d.clsName = some c) (i : Int)
    (hi : d.ignore = []) (hm : d.memberNames.contains n = false) (hh : d.has n = false) :
    d.set n (.atom (.int i)) = .ok (d.addMember n (.atom (.int i))) := by
  have hp : d.privateName n = false := by simp [EnumDict.privateName, hc, o.priv]
  rw [set_plain _ hp o.sun o.dun hm (by simp [hi])]
  simp [EnumDict.setValue, EnumDict.storeMember, hh]

private theorem setAll_auto (c : Name) (names : List Name) :
    ∀ (a b : EnumDict) (k : Nat), Twin a b → a.gen = .enum → a.clsName = some c → a.ignore = [] →
      a.lastValues = iota k → (∀ n ∈ names, Ordinary c n) → names.Nodup →
      (∀ n ∈ names, a.memberNames.contains n = false ∧ a.has n = false) →
      ∃ ps a' b', createPairs .enum 1 k (iota k) names = .ok ps ∧ a.setAll (autoBody names) = (a', none) ∧
        b.setAll ps = (b', none) ∧ Twin a' b' ∧ a'.memberNames = a.memberNames ++ names ∧
        a'.lastValues = iota (k + names.length) := by
  induction names with
  | nil =>
    intro a b k t _ _ _ hl _ _ _
    exact ⟨[], a, b, rfl, rfl, rfl, t, by simp, by simpa using hl⟩
  | cons n r ih =>
    intro a b k t hg hc hi hl ho hn hf
    have o := ho n (by simp)
    have hf0 := hf n (by simp)
    have ha := set_auto o hc hg hi hl hf0.1 hf0.2
    have hb := set_int o (t.cls ▸ hc) ((k : Int) + 1) (t.ignore ▸ hi) (t.names ▸ hf0.1)
      (by rw [show b.has n = a.has n by simp [EnumDict.has, t.items]]; exact hf0.2)
    have hnr := (List.nodup_cons.1 hn)
    let a1 : EnumDict := { a.store n (.atom (.int ((k : Int) + 1))) with
      memberNames := a.memberNames ++ [n], lastValues := iota (k + 1), autoCalled := true }
    have t1 : Twin a1 (b.addMember n (.atom (.int ((k : Int) + 1)))) := by
      constructor
      · simp [a1, EnumDict.addMember, EnumDict.store, t.items]
      · simp [a1, EnumDict.addMember, t.names]
      · simp [a1, EnumDict.addMember, iota_succ, ← t.last, hl]
      · simp [a1, EnumDict.addMember, EnumDict.store, t.ignore]
      · simp [a1, EnumDict.addMember, EnumDict.store, t.cls]
      · simp [a1, EnumDict.addMember, EnumDict.store, t.gen]
    obtain ⟨ps, a', b', h1, h2, h3, h4, h5, h6⟩ := ih a1 _ (k + 1) t1 (by simpa [a1, EnumDict.store] using hg)
      (by simpa [a1, EnumDict.store] using hc) (by simpa [a1, EnumDict.store] using hi) rfl
      (fun x hx => ho x (by simp [hx])) hnr.2
      (by
        intro x hx
        have hxn : n ≠ x := fun e => hnr.1 (e ▸ hx)
        have hf1 := hf x (by simp [hx])
        constructor
        · simpa [a1, List.contains_append, hxn.symm] using hf1.1
        · have : a1.has x = (a.store n (.atom (.int ((k : Int) + 1)))).has x := rfl
          rw [this, has_store]
          simp [hf1.2, hxn])
    refine ⟨(n, .atom (.int ((k : Int) + 1))) :: ps, a', b', ?_, ?_, ?_, h4, ?_, ?_⟩
    · have : enumGenerate 1 (iota k) = .ok (.int ((k : Int) + 1)) := enumGenerate_iota k
      simp only [createPairs, Gen.call, this]
      rw [← iota_succ, h1]
    · simp only [autoBody, List.map_cons, EnumDict.setAll, ha]
      exact h2
    · simp only [EnumDict.setAll, hb]
      exact h3
    · rw [h5]
      simp [a1]
    · rw [h6]
      congr 1
      simp
      omega

private theorem enumTypeNew_twin {a b : EnumDict} (t : Twin a b) (k : EKind) : enumTypeNew k a = enumTypeNew k b := by
  simp only [enumTypeNew, t.items, t.names, t.ignore]

private theorem no_double_underscore (c rest : List Char) :
    "generate_next_value_".toList ≠ c ++ ['_', '_'] ++ rest := by
  intro h
  have key : ∀ m : Fin 19, "generate_next_value_".toList[m.val]? = some '_' →
      "generate_next_value_".toList[m.val + 1]? ≠ some '_' := by decide +kernel
  have hc : c.length < 19 := by
    have := congrArg List.length h
    simp at this
    have h20 : "generate_next_value_".toList.length = 20 := by decide +kernel
    omega
  have h1 : "generate_next_value_".toList[c.length]? = some '_' := by simp [h]
  have h2 : "generate_next_value_".toList[c.length + 1]? = some '_' := by simp [h]
  exact key ⟨c.length, hc⟩ h1 h2

private theorem gnv_not_private (c : Name) : isPrivate c "_generate_next_value_".toList = false := by
  unfold isPrivate
  simp only [Bool.and_eq_false_iff]
  by_cases h : (['_'] ++ c ++ ['_', '_']).isPrefixOf "_generate_next_value_".toList = true
  · have hp := List.isPrefixOf_iff_prefix.1 h
    obtain ⟨t, ht⟩ := hp
    exact absurd (by simpa using ht.symm) (fun e => no_double_underscore c t (by simpa using e))
  · exact Or.inl (Or.inr (Bool.eq_false_iff.2 h))

/-- The functional API and the class statement agree: `Enum('C', names)` is `class C(Enum)` with `auto()` for every
name, table for table, for every list of different ordinary names and every class name; and the values are `1 .. n`, in
order. Docs: "the first argument of the call to Enum is the name of the enumeration", "the second argument is the source
of enumeration member names", and "assigned values start at 1". The hypotheses are the type invariant of a class body:
names not repeated, and not the special names, which are not members in either form. -/
def FunctionalMatchesClass : Prop :=
  ∀ (c : Name) (names : List Name), (∀ n ∈ names, Ordinary c n) → names.Nodup →
    classBody .plain .enum c (autoBody names) = enumCreate .plain .enum c 1 (.seq names) ∧
    ∃ d d', enumPrepare c .enum = .ok d ∧ d.setAll (autoBody names) = (d', none) ∧ d'.memberNames = names ∧
      d'.lastValues = iota names.length

theorem functionalMatchesClass_proven : FunctionalMatchesClass := by
  intro c names ho hn
  let d0 : EnumDict := { ({ clsName := some c } : EnumDict) with gen := .enum }.store
    "_generate_next_value_".toList (.gen .enum)
  have hp : enumPrepare c .enum = .ok d0 := by
    simp only [enumPrepare, EnumDict.set, EnumDict.privateName, gnv_not_private, sunder_gnv, reserved_gnv,
      Bool.false_eq_true, ↓reduceIte, beq_self_eq_true]
    rfl
  obtain ⟨ps, a', b', h1, h2, h3, h4, h5, h6⟩ := setAll_auto c names d0 d0 0
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl rfl rfl ho hn (by
      intro n hn'
      refine ⟨rfl, ?_⟩
      have hne : "_generate_next_value_".toList ≠ n := by
        intro e
        have := (ho n hn').sun
        rw [← e, sunder_gnv] at this
        exact Bool.noConfusion this
      simpa [d0, EnumDict.has, EnumDict.store, dictSet] using hne)
  refine ⟨?_, d0, a', hp, h2, by simpa [d0, EnumDict.store] using h5, by simpa using h6⟩
  have h1' : createPairs .enum 1 0 [] names = .ok ps := h1
  simp only [classBody, enumCreate, hp, h2, h1', h3]
  exact enumTypeNew_twin h4 _

/-! ### `Enum.__new__` -/

/-- `Enum.__new__`, every path: a member comes back as it is; a value in the table is that member; a value not in the
table goes to `_missing_`, whose member is the answer, whose `None` is the `ValueError`, whose anything else is a
`TypeError`, and whose exception propagates. A class with no members is a `TypeError`. An unhashable value is found by
the long search, and does not raise. Docs of `_missing_`. -/
def EnumLookup : Prop :=
  ∀ (c : EClass) (m : Name) (v : EV) (e : PyExc) (miss : MissingRet) (ip : Bool),
    enumNew c (some m) v ip miss = .ok m ∧
    (v.hashable = true → c.value2member.lookup v = some m → enumNew c none v ip miss = .ok m) ∧
    (v.hashable = true → c.value2member.lookup v = none →
      (c.memberMap.isEmpty = false →
        enumNew c none v ip (.member m) = .ok m ∧
        (enumNew c none v ip .none).raises "ValueError" ∧
        (enumNew c none v ip .other).raises "TypeError" ∧
        enumNew c none v ip (.raises e) = .error e) ∧
      (c.memberMap.isEmpty = true → (enumNew c none v ip miss).raises "TypeError")) ∧
    (v.hashable = false → ∀ l k, c.unhashableMap.find? (fun p => p.2.contains v) = some (m, l) →
      c.memberMap.lookup m = some k → enumNew c none v ip miss = .ok k)

theorem enumLookup_proven : EnumLookup := by
  intro c m v e miss ip
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro h1 h2
    simp [enumNew, EClass.found, h1, h2]
  · intro h1 h2
    refine ⟨?_, ?_⟩
    · intro h3
      refine ⟨?_, ⟨.valueError "~is not a valid enum value", ?_, rfl⟩,
        ⟨.typeError "~error in _missing_: returned instead of None or a valid member", ?_, rfl⟩, ?_⟩
      · simp [enumNew, EClass.found, h1, h2, h3]
      · simp [enumNew, EClass.found, h1, h2, h3]
      · simp [enumNew, EClass.found, h1, h2, h3]
      · simp [enumNew, EClass.found, h1, h2, h3]
    · intro h3
      cases ip with
      | true => exact ⟨.typeError "do not use `super().__new__; call the appropriate __new__ directly", by
          simp [enumNew, EClass.found, h1, h2, h3], rfl⟩
      | false => exact ⟨.typeError "~has no members defined", by simp [enumNew, EClass.found, h1, h2, h3], rfl⟩
  · intro h1 l k h2 h3
    simp only [enumNew, EClass.found, EClass.search, h1, h2, h3, Bool.false_eq_true, ↓reduceIte]

/-- `Color(1, 2)` looks up the tuple `(1, 2)`, so that a tuple value can be written without its parentheses; one
argument is the value itself; a class without members has no lookup, and with `names` goes to the functional API. -/
def EnumCallShape : Prop :=
  ∀ (c : EClass) (self : Option Name) (a b : Atom) (r : List Atom) (miss : MissingRet),
    (c.memberMap.isEmpty = false →
      enumCall c self a (b :: r) miss = some (enumNew c self (.tup (a :: b :: r)) false miss) ∧
      enumCall c self a [] miss = some (enumNew c self (.atom a) false miss)) ∧
    (c.memberMap.isEmpty = true →
      enumCall c self a (b :: r) miss = none ∧ ∃ x, enumCall c self a [] miss = some x ∧ x.raises "TypeError")

theorem enumCallShape_proven : EnumCallShape := by
  intro c self a b r miss
  refine ⟨?_, ?_⟩
  · intro h
    simp [enumCall, h]
  · intro h
    refine ⟨by simp [enumCall, h], _, ?_, ⟨.typeError "~has no members; specify `names=()`", rfl, rfl⟩⟩
    simp [enumCall, h]

/-! ### `_add_member_` and its callers -/

/-- `_add_alias_`: a new name is added and points at the member, the same name again is nothing, and a name bound to
another member is a `NameError`. `_member_names_` does not change, so an alias does not show up in iteration or `len`. -/
def AddAlias : Prop :=
  ∀ (c : EClass) (self name other x : Name),
    (c.memberMap.lookup name = none → ∃ c', c.addAlias self name = .ok c' ∧ c'.memberNames = c.memberNames ∧
      c'.memberMap = c.memberMap ++ [(name, self)] ∧ c'.len = c.len ∧ c'.iter.length ≤ c'.len) ∧
    (c.memberMap.lookup name = some self → c.addAlias self name = .ok c) ∧
    (c.memberMap.lookup name = some other → other ≠ self → (c.addAlias self name).raises "NameError")

theorem addAlias_proven : AddAlias := by
  intro c self name other x
  refine ⟨?_, ?_, ?_⟩
  · intro h
    refine ⟨{ c with memberMap := c.memberMap ++ [(name, self)] }, ?_, rfl, rfl, rfl, ?_⟩
    · simp [EClass.addAlias, EClass.addToMap, h]
    · simp only [EClass.iter, EClass.len]
      exact List.length_filterMap_le _ _
  · intro h
    simp [EClass.addAlias, EClass.addToMap, h]
  · intro h hn
    refine ⟨.named "NameError" "~is already bound", ?_, rfl⟩
    simp [EClass.addAlias, EClass.addToMap, h, hn]

/-- The scan of the bases in `_add_member_`: `enum.property` stops it at once, with type `enum`. Short of one, a redirect
is made exactly when a descriptor is there; a plain attribute does not make one. -/
def ScanBases : Prop :=
  (∀ (pre post : List BaseAttr) (i : Nat) (s : Scan), (∀ a ∈ pre, a = .absent) →
    scanBases i s (pre ++ .prop :: post) =
      { found := true, attrType := some "enum", clsIndex := some (i + pre.length) }) ∧
  (∀ (l : List BaseAttr) (i : Nat) (s : Scan), .prop ∉ l →
    (scanBases i s l).found = (s.found || l.contains .descr))

theorem scanBases_proven : ScanBases := by
  refine ⟨?_, ?_⟩
  · intro pre
    induction pre with
    | nil => intro post i s _; simp [scanBases]
    | cons a r ih =>
      intro post i s h
      have ha : a = .absent := h a (by simp)
      subst ha
      simp only [List.cons_append, scanBases]
      rw [ih post (i + 1) s (fun x hx => h x (by simp [hx]))]
      simp [Nat.add_comm, Nat.add_left_comm]
  · intro l
    induction l with
    | nil => intro i s _; simp [scanBases]
    | cons a r ih =>
      intro i s h
      have hr : .prop ∉ r := fun e => h (by simp [e])
      cases a with
      | absent => simp [scanBases, ih _ _ hr]
      | prop => simp at h
      | descr => simp [scanBases, ih _ _ hr]
      | plain => simp [scanBases, ih _ _ hr]

private theorem lookup_snoc_self (l : List (EV × Name)) (k : EV) (v : Name) (h : l.lookup k = none) :
    (l ++ [(k, v)]).lookup k = some v := by
  induction l with
  | nil => simp [List.lookup]
  | cons x xs ih =>
    obtain ⟨a, b⟩ := x
    by_cases hx : k = a
    · subst hx; simp at h
    · have hb : (k == a) = false := by simpa using hx
      simp only [List.lookup_cons, hb, List.cons_append] at h ⊢
      exact ih h

/-- A hashable value belongs to one member: once `_add_value_alias_` has bound it, the same call on another member is a
`ValueError`, whatever `name` does. The docs of `_add_value_alias_`: "Raises a ValueError if the value is already linked
with a different member." -/
def ValueAliasHashable : Prop :=
  ∀ (c c' : EClass) (f : Name → Name) (m m' : Name) (v : EV), v.hashable = true → m ≠ m' →
    c.addValueAlias f m v = .ok c' → (c'.addValueAlias f m' v).raises "ValueError"

theorem valueAliasHashable_proven : ValueAliasHashable := by
  intro c c' f m m' v hv hne h
  have hl : c'.value2member.lookup v = some m := by
    simp only [EClass.addValueAlias, hv, ↓reduceIte] at h
    split at h
    · rename_i x hx
      split at h
      · simp at h
      · rename_i hb
        simp only [Except.ok.injEq] at h
        subst h
        simp at hb
        rw [hx, hb]
    · rename_i hx
      simp only [Except.ok.injEq] at h
      subst h
      simp [EClass.bindValue, hv, setDefault, hx, lookup_snoc_self _ _ _ hx]
  refine ⟨.valueError "~is already bound", ?_, rfl⟩
  simp [EClass.addValueAlias, hv, hl, hne]

/-- A class with members `A` and `B`. -/
def twoMembers (a b : EV) : EClass :=
  { memberMap := [(['A'], ['A']), (['B'], ['B'])]
    values := [(['A'], a), (['B'], b)] }

/-- The same sentence for every value. False: for an unhashable value the check at Lib/enum.py:1220-1224 reads the
`_value_` of the members only, so a value linked with `_add_value_alias_` is not seen, and the second member gets it
as well. -/
def ValueAliasExclusive : Prop :=
  ∀ (c c' : EClass) (f : Name → Name) (m m' : Name) (v : EV), m ≠ m' →
    c.addValueAlias f m v = .ok c' → (c'.addValueAlias f m' v).raises "ValueError"

theorem valueAliasExclusive_refuted : ¬ValueAliasExclusive := by
  intro h
  let c := twoMembers (.atom (.int 1)) (.atom (.int 2))
  obtain ⟨e, he, _⟩ := h c (c.bindValue id ['A'] (.atom (.list 9))) id ['A'] ['B'] (.atom (.list 9)) (by decide)
    (by decide +kernel)
  have : (c.bindValue id ['A'] (.atom (.list 9))).addValueAlias id ['B'] (.atom (.list 9)) =
      .ok ((c.bindValue id ['A'] (.atom (.list 9))).bindValue id ['B'] (.atom (.list 9))) := by decide +kernel
  rw [this] at he
  cases he

/-- With the value bound as a member's `_value_`, the same sentence fails another way: the `ValueError` is formatted with
`cls._value2member_map_[value]`, at Lib/enum.py:1223, so hashing the unhashable value again raises `TypeError`. -/
def ValueAliasBoundError : Prop :=
  ∀ (c : EClass) (f : Name → Name) (m m' : Name) (v : EV), m ≠ m' → c.findEqual v = some m' →
    (c.addValueAlias f m v).raises "ValueError"

theorem valueAliasBoundError_refuted : ¬ValueAliasBoundError := by
  intro h
  let c := twoMembers (.atom (.list 1)) (.atom (.int 2))
  obtain ⟨e, he, hc⟩ := h c id ['B'] ['A'] (.atom (.list 1)) (by decide) (by decide +kernel)
  have : c.addValueAlias id ['B'] (.atom (.list 1)) = .error (.typeError "~unhashable") := by decide +kernel
  rw [this] at he
  cases he
  exact absurd hc (by decide)

/-- `unique` raises only for a class with aliases: "Class decorator for enumerations ensuring unique member values",
and `verify(UNIQUE)` the same. False: it compares each name with `member.name`, so a class that defines a `name` of
its own, a property returning the lower-case name say, has every member reported as a duplicate of itself. -/
def UniqueOnlyOnAliases : Prop :=
  ∀ (c : EClass) (f : Name → Name), (∀ p ∈ c.memberMap, p.1 = p.2) → c.unique f = .ok () ∧ c.verifyUnique f = .ok ()

theorem uniqueOnlyOnAliases_refuted : ¬UniqueOnlyOnAliases := by
  intro h
  have := (h { memberMap := [(['A'], ['A'])] } (fun _ => ['a']) (by simp)).1
  simp [EClass.unique] at this

/-- The narrowed statement: with `member.name` being `_name_`, `unique` and `verify(UNIQUE)` raise exactly when some
name points at a member of another name. -/
def UniqueNamed : Prop :=
  ∀ c : EClass, (c.unique id = .ok () ↔ ∀ p ∈ c.memberMap, p.1 = p.2) ∧
    (c.verifyUnique id = .ok () ↔ ∀ p ∈ c.memberMap, p.1 = p.2)

theorem uniqueNamed_proven : UniqueNamed := by
  intro c
  constructor <;> (simp only [EClass.unique, EClass.verifyUnique, id]; split)
  all_goals rename_i h
  · simp only [List.any_eq_true, bne_iff_ne] at h
    obtain ⟨p, hp, hn⟩ := h
    simp only [reduceCtorEq, false_iff]
    exact fun hh => hn (hh p hp)
  · simp only [List.any_eq_true, bne_iff_ne, not_exists, not_and, Decidable.not_not] at h
    simpa using h
  · simp only [List.any_eq_true, bne_iff_ne] at h
    obtain ⟨p, hp, hn⟩ := h
    simp only [reduceCtorEq, false_iff]
    exact fun hh => hn (hh p hp)
  · simp only [List.any_eq_true, bne_iff_ne, not_exists, not_and, Decidable.not_not] at h
    simpa using h

/-- `Enum.__new__` finds a value bound by `_add_value_alias_`: "A member can be looked up by its value alias". False for
a class with a `name` of its own: Lib/enum.py:1234 files the value under `self.name` and :1165 does `cls[name]`, which is
a `KeyError` from a lookup that should end in the member. -/
def ValueAliasFound : Prop :=
  ∀ (c c' : EClass) (f : Name → Name) (m : Name) (v : EV), c.memberMap.lookup m = some m →
    c.addValueAlias f m v = .ok c' → enumNew c' none v false .none = .ok m

theorem valueAliasFound_refuted : ¬ValueAliasFound := by
  intro h
  let c : EClass := { memberMap := [(['A'], ['A'])], values := [(['A'], .atom (.int 1))] }
  have := h c (c.bindValue (fun _ => ['a']) ['A'] (.atom (.list 1))) (fun _ => ['a']) ['A'] (.atom (.list 1))
    (by decide) (by decide +kernel)
  revert this
  decide +kernel

/-! ### The body and `EnumDict` used directly -/

/-- `EnumDict` is public, "to allow subclasses of `EnumType`", so `d['A'] = auto()` works on one. False:
`_generate_next_value` is only set by the `__setitem__` of `__prepare__`, so `auto()` is an `AttributeError`. -/
def EnumDictAuto : Prop :=
  ∀ c key : Name, Ordinary c key → ∃ r, ({ clsName := some c } : EnumDict).set key (.atom (.auto none)) = .ok r

theorem enumDictAuto_refuted : ¬EnumDictAuto := by
  intro h
  obtain ⟨r, hr⟩ := h ['C'] ['A'] ⟨by decide, by decide, by decide⟩
  have : ({ clsName := some ['C'] } : EnumDict).set ['A'] (.atom (.auto none)) =
      .error (.named "AttributeError" "'EnumDict' object has no attribute '_generate_next_value'") := by
    decide +kernel
  rw [this] at hr
  cases hr

/-- `update` keeps the key. False, by the same defect: it takes that `AttributeError` as meaning that `members` has no
`keys`, goes round again over the mapping's keys, and unpacks them, so that `{'AB': auto()}` assigns `'B'` to `A`. -/
def EnumDictUpdateKeys : Prop :=
  ∀ (c : Name) (key : Name) (v : EV) (d' : EnumDict),
    ({ clsName := some c } : EnumDict).update (.mapping [(key, v)]) [] = .ok d' → d'.has key = true

theorem enumDictUpdateKeys_refuted : ¬EnumDictUpdateKeys := by
  intro h
  have := h ['C'] ['A', 'B'] (.atom (.auto none)) _ rfl
  revert this
  decide +kernel

/-! ### Rules on values -/

/-- The default `_generate_next_value_`: the first value is `start`; after that one more than the largest value, which
is greater than each value so far; values with no order or no `+ 1` are the `TypeError`s of the source. Docs of `auto`:
"the highest member + 1". -/
def EnumGenerateRules : Prop :=
  ∀ (st i : Int) (r : List Int) (s : String),
    enumGenerate st [] = .ok (.int st) ∧
    (∃ m, enumGenerate 1 ((i :: r).map (fun x => .atom (.int x))) = .ok (.int m) ∧
      (∀ x ∈ i :: r, x < m) ∧ (m - 1) ∈ i :: r) ∧
    (enumGenerate 1 [.atom (.str s)]).raises "TypeError" ∧
    enumGenerate 1 [.atom (.int i), .atom (.str s)] = .error (.typeError "unable to sort non-numeric values")

private theorem intsOf_map (l : List Int) : intsOf (l.map (fun x => .atom (.int x))) = l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simpa [intsOf] using ih

private theorem foldl_max_bound (l : List Int) (a : Int) :
    a ≤ l.foldl max a ∧ (∀ x ∈ l, x ≤ l.foldl max a) ∧ (l.foldl max a = a ∨ l.foldl max a ∈ l) := by
  induction l generalizing a with
  | nil => simp [Int.le_refl]
  | cons y ys ih =>
    simp only [List.foldl_cons]
    obtain ⟨h1, h2, h3⟩ := ih (max a y)
    refine ⟨by omega, ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · omega
      · exact h2 x hx
    · rcases h3 with h3 | h3
      · rw [h3]
        by_cases hay : y ≤ a
        · left; omega
        · right; simp; left; omega
      · right; simp [h3]

theorem enumGenerateRules_proven : EnumGenerateRules := by
  intro st i r s
  refine ⟨rfl, ?_, ⟨.typeError "~unable to increment", ?_, rfl⟩, ?_⟩
  · obtain ⟨h1, h2, h3⟩ := foldl_max_bound r i
    refine ⟨r.foldl max i + 1, ?_, ?_, ?_⟩
    · have hs : sortable ((i :: r).map (fun x => EV.atom (.int x))) = true := by
        apply sortable_ints
        intro v hv
        simp only [List.mem_map] at hv
        obtain ⟨x, _, rfl⟩ := hv
        exact ⟨x, rfl⟩
      simp only [enumGenerate, List.map_cons, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at hs ⊢
      rw [hs]
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      have := intsOf_map (i :: r)
      simp only [List.map_cons] at this
      rw [this]
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · omega
      · have := h2 x hx
        omega
    · simp only [Int.add_sub_cancel]
      rcases h3 with h3 | h3
      · simp [h3]
      · simp [h3]
  · rfl
  · rfl

/-- `StrEnum.__new__`: a member takes one `str`, or nothing at all, and every other argument list raises `TypeError`.
Docstring of the method: "values must already be of type `str`". -/
def StrEnumValues : Prop :=
  ∀ (l : List Atom) (s : String), strEnumNew l = .ok s ↔ (l = [] ∧ s = "") ∨ l = [.str s]

theorem strEnumValues_proven : StrEnumValues := by
  intro l s
  match l with
  | [] => simp [strEnumNew, eq_comm]
  | [a] =>
    cases a <;> simp [strEnumNew]
  | [_, b] =>
    cases b <;> simp [strEnumNew]
  | [_, b, c] =>
    cases b <;> cases c <;> simp [strEnumNew]
  | _ :: _ :: _ :: _ :: r =>
    simp [strEnumNew]

/-- `_order_`: for a class that is not a `Flag`, a non-empty order that names members and nothing that is an alias
passes exactly when it is the definition order. Docs: "`_order_` -- ... used in Python 2/3 code to ensure member order
is consistent". -/
def OrderCheck : Prop :=
  ∀ (c : EClass) (o : List Name), c.kind ≠ .flag → o ≠ [] →
    (∀ x ∈ o, (c.memberMap.lookup x).isSome = true → c.memberNames.contains x = true) →
    (c.checkOrder (some o) = .ok () ↔ o = c.memberNames)

theorem orderCheck_proven : OrderCheck := by
  intro c o hk hne hall
  have hf : o.filter (fun x => !(c.memberMap.lookup x).isSome || c.memberNames.contains x) = o := by
    apply List.filter_eq_self.2
    intro x hx
    by_cases h : (c.memberMap.lookup x).isSome = true
    · simp only [hall x hx h, Bool.or_true]
    · have h' : (c.memberMap.lookup x).isSome = false := Bool.eq_false_iff.2 h
      simp only [h', Bool.not_false, Bool.true_or]
  have he : o.isEmpty = false := by cases o <;> simp_all
  have hk' : (c.kind == EKind.flag) = false := by simpa using hk
  simp only [EClass.checkOrder, hk', Bool.false_eq_true, ↓reduceIte, he, hf]
  by_cases h : o = c.memberNames
  · simp [h]
  · simp [h]

/-- `verify(CONTINUOUS)` on a class that is not a `Flag`: it passes exactly when every integer between the lowest and
the highest value is a value. Docs: "Ensure there are no missing values between the highest-valued member and the
lowest-valued member". -/
def VerifyContinuous : Prop :=
  ∀ (c : EClass) (i : Int) (is : List Int), c.kind ≠ .flag → c.intValues = i :: is →
    (c.verifyContinuous = .ok () ↔
      ∀ k, is.foldl min i < k → k < is.foldl max i → k ∈ i :: is)

private theorem mem_intRange (a b k : Int) : k ∈ intRange a b ↔ a ≤ k ∧ k < b := by
  simp only [intRange, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨n, hn, rfl⟩
    omega
  · intro h
    exact ⟨(k - a).toNat, by omega, by omega⟩

theorem verifyContinuous_proven : VerifyContinuous := by
  intro c i is hk hv
  have hk' : (c.kind == EKind.flag) = false := by simpa using hk
  simp only [EClass.verifyContinuous, hv]
  split
  · rename_i he
    simp only [true_iff]
    intro k h1 h2
    omega
  · simp only [hk', Bool.false_eq_true, ↓reduceIte]
    have hc : ∀ k : Int, (!(i :: is).contains k) = false ↔ k ∈ i :: is := by
      intro k
      have e : (i :: is).contains k = decide (k ∈ i :: is) := by simp
      rw [e]
      simp only [Bool.not_eq_false', decide_eq_true_eq]
    have hg : ((intRange (is.foldl min i + 1) (is.foldl max i)).filter
        (fun k => !(i :: is).contains k)).isEmpty = true ↔
        ∀ k, is.foldl min i < k → k < is.foldl max i → k ∈ i :: is := by
      rw [List.isEmpty_iff, List.filter_eq_nil_iff]
      constructor
      · intro h k h1 h2
        have := h k ((mem_intRange _ _ _).2 ⟨by omega, h2⟩)
        exact (hc k).1 (Bool.eq_false_iff.2 this)
      · intro h k hk
        have hk' := (mem_intRange _ _ _).1 hk
        have := (hc k).2 (h k (by omega) hk'.2)
        intro e
        rw [this] at e
        exact Bool.noConfusion e
    by_cases h : ∀ k, is.foldl min i < k → k < is.foldl max i → k ∈ i :: is
    · simp only [hg.2 h, ↓reduceIte, true_iff]
      exact h
    · have : ((intRange (is.foldl min i + 1) (is.foldl max i)).filter
          (fun k => !(i :: is).contains k)).isEmpty = false := by
        cases he : ((intRange (is.foldl min i + 1) (is.foldl max i)).filter
          (fun k => !(i :: is).contains k)).isEmpty with
        | false => rfl
        | true => exact absurd (hg.1 he) h
      simp only [this, Bool.false_eq_true, ↓reduceIte, reduceCtorEq, false_iff]
      exact h

/-! ### `Flag` operators -/

/-- The operators of `Flag` through `_get_value`, each path. An object of another class is `NotImplemented`, so that
Python tries the other operand; an `int` works on an `IntFlag` only; a `None` value is the `TypeError`; otherwise the
class is called on the bit operation. `in` raises `TypeError` for anything but a member, and for a member is the subset
test. `__bool__` is the value. `__invert__` keeps its result: with a cached value it does not compute. -/
def FlagOperands : Prop :=
  ∀ (c : FlagCls) (op : Nat → Nat → Nat) (m : Bool) (self o : Nat) (v : Int) (r x : FlagVal),
    flagBin c m op (some self) .other = none ∧
    flagBin c false op (some self) (.mixin v) = none ∧
    flagBin c true op (some self) (.mixin v) = some (c.call (twos op self v)) ∧
    flagBin c m op (some self) (.same (some o)) = some (c.call (twos op self o)) ∧
    (∃ e, flagBin c m op none (.same (some o)) = some (.error e) ∧ e.className = "TypeError") ∧
    (∃ e, flagBin c m op (some self) (.same none) = some (.error e) ∧ e.className = "TypeError") ∧
    (flagIn self .other).raises "TypeError" ∧ (flagIn self (.mixin v)).raises "TypeError" ∧
    flagIn self (.same (some o)) = .ok ((o &&& self) == o) ∧
    (flagBool self = false ↔ self = 0) ∧
    flagInvert c (some x) (some self) = .ok (x, some x) ∧
    (flagInvert c none none).raises "TypeError" ∧
    (c.invert self = .ok r → flagInvert c none (some self) = .ok (r, some r))

theorem flagOperands_proven : FlagOperands := by
  intro c op m self o v r x
  refine ⟨?_, rfl, rfl, rfl, ⟨.typeError "~cannot be combined with other flags", rfl, rfl⟩,
    ⟨.typeError "~cannot be combined with other flags", rfl, rfl⟩,
    ⟨.typeError "~unsupported operand type(s) for 'in'", rfl, rfl⟩,
    ⟨.typeError "~unsupported operand type(s) for 'in'", rfl, rfl⟩, rfl, ?_, rfl,
    ⟨.typeError "~cannot be inverted", rfl, rfl⟩, ?_⟩
  · simp [flagBin, getValue]
  · simp [flagBool]
  · intro h; simp [flagInvert, h]

/-- `value in cls`, for a `Flag` class and a value that is not negative, means that the value is the value of a member or
a pseudo-member: the docstring of `EnumType.__contains__`. False under `CONFORM`: `_missing_` discards the unknown bits
before it returns a member, and `__contains__` only looks at the type of that member, so `8 in F` is true for a class of
two bits, for which `F(8)` is `F(0)`. -/
def FlagClassContainsValue : Prop :=
  ∀ (c : FlagCls) (i : Int), 0 ≤ i → c.classContains (some i) = true →
    ∃ n name, c.call i = .ok (.flag n name) ∧ (n : Int) = i

theorem flagClassContainsValue_refuted : ¬FlagClassContainsValue := by
  intro h
  obtain ⟨n, name, h1, h2⟩ := h ⟨"F", [("A", 1), ("B", 2)], .conform⟩ 8 (by decide) (by decide +kernel)
  have : (FlagCls.call ⟨"F", [("A", 1), ("B", 2)], .conform⟩ 8) = .ok (.flag 0 none) := by decide +kernel
  rw [this] at h1
  simp only [Except.ok.injEq, FlagVal.flag.injEq] at h1
  omega

/-! ### Names and bits -/

/-- A name is not both dunder and sunder, and every sunder name is outside the dunder branch, so the branches of
`__setitem__` do not overlap. The private test needs more than one trailing underscore to fail. -/
def NameClasses : Prop :=
  ∀ name : Name, (isDunder name = true → isSunder name = false)

theorem nameClasses_proven : NameClasses := by
  intro name h
  match name with
  | [] => simp [isDunder] at h
  | [_] => simp [isDunder] at h
  | a :: b :: r =>
    simp only [isDunder, Bool.and_eq_true] at h
    have : b = '_' := by
      have h2 := h.1.1.1.2
      simp at h2
      exact h2.2
    subst this
    simp [isSunder]

/-- `_is_single_bit` is what it says: a power of two, and nothing else. -/
def SingleBit : Prop :=
  ∀ n : Nat, isSingleBit n = true ↔ ∃ k, n = 2 ^ k

theorem singleBit_proven : SingleBit := by
  intro n
  constructor
  · intro h
    simp only [isSingleBit] at h
    split at h
    · simp at h
    rename_i hn
    have h0 : n &&& (n - 1) = 0 := by simpa using h
    refine ⟨n.log2, ?_⟩
    have h1 : 2 ^ n.log2 ≤ n := Nat.log2_self_le hn
    have h2 : n < 2 ^ (n.log2 + 1) := Nat.lt_log2_self
    apply Classical.byContradiction
    intro hne
    have hgt : 2 ^ n.log2 ≤ n - 1 := by omega
    have bit : ∀ x, 2 ^ n.log2 ≤ x → x < 2 ^ (n.log2 + 1) → x.testBit n.log2 = true := by
      intro x h3 h4
      have e : x = 2 ^ n.log2 + (x - 2 ^ n.log2) := by omega
      have hlt : x - 2 ^ n.log2 < 2 ^ n.log2 := by
        have : 2 ^ (n.log2 + 1) = 2 * 2 ^ n.log2 := by rw [Nat.pow_succ]; omega
        omega
      rw [e, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt]
      rfl
    have := congrArg (fun m => m.testBit n.log2) h0
    simp only [Nat.testBit_and, bit n h1 h2, bit (n - 1) hgt (by omega), Bool.and_self, Nat.zero_testBit] at this
    exact Bool.noConfusion this
  · rintro ⟨k, rfl⟩
    have hp : 2 ^ k ≠ 0 := by
      have := Nat.two_pow_pos k
      omega
    simp only [isSingleBit, hp, ↓reduceIte, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_self, beq_self_eq_true]

end PyLean.CoreLibs.EnumDC
