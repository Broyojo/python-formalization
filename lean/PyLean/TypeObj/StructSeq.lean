import PyLean.Core

/-!
Struct sequences (`os.stat_result`, `time.struct_time`, ...), Objects/structseq.c, CPython 3.15.2:
the constructor `structseq_new_impl` (:166-270), `__reduce__` (`structseq_reduce`, :342-385) and
`__replace__` (`structseq_replace`, :388-458). `StructSeqC.lean` models the same functions in
memory, with the size attributes read from the type's dict.

A struct sequence type has `nVis` visible fields (the tuple part), `nFields` fields in all, and
`nUnnamed` unnamed visible fields; field `i` (for `i ≥ nUnnamed`) is named
`names[i - nUnnamed]` (`tp_members`). Field values are `Option α`, `none` being `None`.
-/

namespace PyLean.TypeObj.StructSeq

variable {α : Type}

structure SType where
  tpName : String
  nVis : Nat
  nFields : Nat
  nUnnamed : Nat
  names : List String

def SType.nameOf (t : SType) (i : Nat) : String := t.names.getD (i - t.nUnnamed) ""

/-- A dict key: a str, or something else (which `PyDict_GetItemStringRef` never finds). -/
inductive Key where
  | str (s : String)
  | other

inductive DictArg (α : Type) where
  | dict (items : List (Key × Option α))
  | notDict

inductive SeqArg (α : Type) where
  | seq (xs : List (Option α))
  | notSeq

def lookup (items : List (Key × Option α)) (name : String) : Option (Option α) :=
  (items.find? (fun kv => match kv.1 with | .str s => s == name | .other => false)).map (·.2)

/-- The hidden fields read from the dict (:240-254): each found name counts. -/
def fillFromDict (t : SType) (items : List (Key × Option α)) (len : Nat) : List (Option α) × Nat :=
  (List.range (t.nFields - len)).foldl (fun (acc, n) k =>
    match lookup items (t.nameOf (len + k)) with
    | some v => (acc ++ [v], n + 1)
    | none => (acc ++ [none], n)) ([], 0)

/-- `structseq_new_impl(type, arg, dict)`, :166-270. -/
def structseqNew (t : SType) (arg : SeqArg α) (dict : Option (DictArg α)) : Py (List (Option α)) :=
  match arg with
  | .notSeq => .error (.typeError "constructor requires a sequence")
  | .seq xs =>
    match dict with
    | some .notDict => .error (.typeError s!"{t.tpName}() takes a dict as second arg, if any")
    | _ =>
      let len := xs.length
      let lenErr : Option PyExc :=
        if t.nVis ≠ t.nFields then
          if len < t.nVis then some (.typeError s!"~{t.tpName}() takes an at least {t.nVis}-sequence ({len}-sequence given)")
          else if len > t.nFields then some (.typeError s!"~{t.tpName}() takes an at most {t.nFields}-sequence ({len}-sequence given)")
          else none
        else if len ≠ t.nVis then some (.typeError s!"~{t.tpName}() takes a {t.nVis}-sequence ({len}-sequence given)")
        else none
      match lenErr with
      | some e => .error e
      | none =>
        match dict with
        | some (.dict items) =>
          if items ≠ [] then
            let (rest, found) := fillFromDict t items len
            if items.length > found then
              .error (.typeError s!"{t.tpName}() got duplicate or unexpected field name(s)")
            else .ok (xs ++ rest)
          else .ok (xs ++ List.replicate (t.nFields - len) none)
        | _ => .ok (xs ++ List.replicate (t.nFields - len) none)

/-- `structseq_reduce`, :342-385: `(type, (tuple(visible), {name: value for hidden fields}))`. -/
def structseqReduce (t : SType) (s : List (Option α)) : List (Option α) × List (Key × Option α) :=
  (s.take t.nVis, (List.range (t.nFields - t.nVis)).map fun k => (.str (t.nameOf (t.nVis + k)), s.getD (t.nVis + k) none))

/-- The type invariants: hidden fields follow the visible ones, unnamed fields are visible, and
the hidden fields' names are distinct. -/
def SType.WF (t : SType) : Prop :=
  t.nVis ≤ t.nFields ∧ t.nUnnamed ≤ t.nVis ∧
  ((List.range (t.nFields - t.nVis)).map fun k => t.nameOf (t.nVis + k)).Nodup

/-- Pickling round-trips: `type(*s.__reduce__()[1])` rebuilds every field of `s`, hidden ones
included, for every struct sequence type and value. -/
def ReduceRoundTrip : Prop :=
  ∀ (α : Type) (t : SType) (s : List (Option α)), t.WF → s.length = t.nFields →
    structseqNew t (.seq (structseqReduce t s).1) (some (.dict (structseqReduce t s).2)) = .ok s

theorem lookup_at (t : SType) (s : List (Option α)) (m : Nat) (hnd : ((List.range m).map fun k => t.nameOf (t.nVis + k)).Nodup)
    (k : Nat) (hk : k < m) :
    lookup ((List.range m).map fun j => ((Key.str (t.nameOf (t.nVis + j))), s.getD (t.nVis + j) none)) (t.nameOf (t.nVis + k))
      = some (s.getD (t.nVis + k) none) := by
  induction m with
  | zero => omega
  | succ m ih =>
    rw [List.range_succ, List.map_append] at hnd ⊢
    rw [List.nodup_append] at hnd
    obtain ⟨hnd1, _, hdisj⟩ := hnd
    unfold lookup
    rw [List.find?_append]
    by_cases hkm : k < m
    · have := ih hnd1 hkm
      unfold lookup at this
      rw [Option.map_eq_some_iff] at this
      obtain ⟨p, hp, hpv⟩ := this
      rw [hp]; simp [hpv]
    · have hk' : k = m := by omega
      subst hk'
      have hnone : (List.find? (fun kv => match kv.1 with | .str s => s == t.nameOf (t.nVis + k) | .other => false)
          ((List.range k).map fun j => ((Key.str (t.nameOf (t.nVis + j))), s.getD (t.nVis + j) none))) = none := by
        rw [List.find?_eq_none]
        intro p hp
        simp only [List.mem_map, List.mem_range] at hp
        obtain ⟨j, hj, rfl⟩ := hp
        have := hdisj (t.nameOf (t.nVis + j)) (by simp; exact ⟨j, hj, rfl⟩) (t.nameOf (t.nVis + k)) (by simp)
        simp [this]
      rw [hnone]; simp

theorem fill_round (t : SType) (s : List (Option α)) (m : Nat)
    (hnd : ((List.range m).map fun k => t.nameOf (t.nVis + k)).Nodup) (j : Nat) (hj : j ≤ m) :
    (List.range j).foldl (fun (acc, n) k =>
      match lookup ((List.range m).map fun j => ((Key.str (t.nameOf (t.nVis + j))), s.getD (t.nVis + j) none)) (t.nameOf (t.nVis + k)) with
      | some v => (acc ++ [v], n + 1)
      | none => (acc ++ [none], n)) ([], 0)
      = ((List.range j).map fun k => s.getD (t.nVis + k) none, j) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [List.range_succ, List.foldl_append, ih (by omega)]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [lookup_at t s m hnd j (by omega)]
    simp [List.range_succ]

theorem reduceRoundTrip_proven : ReduceRoundTrip := by
  intro α t s ⟨hvf, _, hnd⟩ hlen
  have htake : (s.take t.nVis).length = t.nVis := by simp; omega
  unfold structseqReduce structseqNew
  simp only [htake]
  have hrebuild : s.take t.nVis ++ (List.range (t.nFields - t.nVis)).map (fun k => s.getD (t.nVis + k) none) = s := by
    apply List.ext_getElem?
    intro p
    by_cases hp : p < t.nVis
    · rw [List.getElem?_append_left (by simp; omega), List.getElem?_take_of_lt hp]
    · rw [List.getElem?_append_right (by simp; omega)]
      simp only [List.length_take, Nat.min_eq_left (show t.nVis ≤ s.length by omega), List.getElem?_map]
      by_cases hq : p < t.nFields
      · rw [List.getElem?_range (by omega)]
        simp only [Option.map_some, List.getD_eq_getElem?_getD, show t.nVis + (p - t.nVis) = p by omega]
        rw [List.getElem?_eq_getElem (by omega)]; rfl
      · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]; rfl
  by_cases he : t.nVis = t.nFields
  · have hz : t.nFields - t.nVis = 0 := by omega
    simp [he, hz] at hrebuild ⊢
    simpa [he] using hrebuild
  · simp only [he, ne_eq, not_false_eq_true, if_true, show ¬ t.nVis < t.nVis by omega, if_false,
      show ¬ t.nVis > t.nFields by omega]
    have hne : ((List.range (t.nFields - t.nVis)).map fun k => ((Key.str (t.nameOf (t.nVis + k))), s.getD (t.nVis + k) none)) ≠ [] := by
      simp; omega
    simp only [hne, not_false_eq_true, if_true]
    unfold fillFromDict
    rw [fill_round t s _ hnd _ (Nat.le_refl _)]
    simp only [List.getD_eq_getElem?_getD] at hrebuild
    simpa using hrebuild

/-! ## `__replace__` (`copy.replace`), :388-458 -/

/-- `PyDict_PopString(kwargs, name)`: the value, if present, and the dict without it. -/
def popName (kws : List (String × Option α)) (name : String) : Option (Option α) × List (String × Option α) :=
  match kws.find? (·.1 == name) with
  | some (_, v) => (some v, kws.filter (·.1 != name))
  | none => (none, kws)

/-- The field loop, :423-433: field `i` takes the popped value or keeps its own. -/
def replaceLoop (names : List String) : List (Option α) → List (String × Option α) → List (Option α) × List (String × Option α)
  | [], kws => ([], kws)
  | v :: vs, kws =>
    let (got, kws) := popName kws (names.headD "")
    let (rest, kws) := replaceLoop names.tail vs kws
    (got.getD v :: rest, kws)

/-- `structseq_replace(self, *args, **kwargs)`: positional arguments are refused, types with
unnamed fields refused, then each field is taken from `kwargs` if named there; names left over
raise `TypeError`. -/
def structseqReplace (t : SType) (s : List (Option α)) (nargs : Nat) (kws : List (String × Option α)) :
    Py (List (Option α)) :=
  if nargs ≠ 0 then .error (.typeError "__replace__() takes no positional arguments")
  else if t.nUnnamed > 0 then
    .error (.typeError s!"__replace__() is not supported for {t.tpName} because it has unnamed field(s)")
  else
    let (res, left) := replaceLoop t.names s kws
    if left ≠ [] then .error (.typeError "~Got unexpected field name(s): %R") else .ok res

/-- The value `kws` holds for `n`. -/
def kwLookup (kws : List (String × Option α)) (n : String) : Option (Option α) :=
  (kws.find? (·.1 == n)).map (·.2)

/-- `copy.replace(s, **kws)` on a type without unnamed fields (distinct field names): every field
named in `kws` takes that value and every other field keeps its own; and a keyword that names no
field raises `TypeError`. -/
def ReplaceSpec : Prop :=
  ∀ (α : Type) (t : SType) (s : List (Option α)) (kws : List (String × Option α)),
    t.nUnnamed = 0 → t.names.length = s.length → t.names.Nodup →
    (kws.all (fun kv => t.names.contains kv.1) →
      structseqReplace t s 0 kws = .ok ((t.names.zip s).map fun (n, v) => (kwLookup kws n).getD v)) ∧
    (kws.any (fun kv => !t.names.contains kv.1) → ∃ e, structseqReplace t s 0 kws = .error e ∧ e.className = "TypeError")

theorem popName_eq (kws : List (String × Option α)) (n : String) :
    popName kws n = (kwLookup kws n, kws.filter (·.1 != n)) := by
  unfold popName kwLookup
  cases h : kws.find? (·.1 == n) with
  | some kv => simp
  | none =>
    simp only [Option.map_none, Prod.mk.injEq, true_and]
    symm
    rw [List.filter_eq_self]
    intro kv hkv
    have := List.find?_eq_none.mp h kv hkv
    simpa using this

theorem find?_filter_of_imp {β : Type} (p q : β → Bool) (l : List β) (h : ∀ x, p x = true → q x = true) :
    (l.filter q).find? p = l.find? p := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases hq : q a = true
    · simp only [List.filter_cons, hq, ite_true, List.find?_cons]
      split <;> simp_all
    · have hp : p a = false := by
        cases hpa : p a
        · rfl
        · exact absurd (h a hpa) hq
      simp only [List.filter_cons, hq, List.find?_cons, hp]
      simp [ih]

theorem kwLookup_filter (kws : List (String × Option α)) (m n : String) (h : m ≠ n) :
    kwLookup (kws.filter (·.1 != m)) n = kwLookup kws n := by
  unfold kwLookup
  rw [find?_filter_of_imp]
  intro x hx
  simp only [beq_iff_eq] at hx
  simp only [bne_iff_ne, ne_eq]
  rw [hx]; exact Ne.symm h

theorem replaceLoop_spec (names : List String) (s : List (Option α)) (kws : List (String × Option α))
    (hlen : names.length = s.length) (hnd : names.Nodup) :
    replaceLoop names s kws = ((names.zip s).map (fun (n, v) => (kwLookup kws n).getD v),
      kws.filter (fun kv => !names.contains kv.1)) := by
  induction s generalizing names kws with
  | nil =>
    cases names with
    | nil =>
      simp only [replaceLoop, List.zip_nil_left, List.map_nil, Prod.mk.injEq, true_and]
      exact (List.filter_eq_self.mpr (fun _ _ => by simp)).symm
    | cons _ _ => simp at hlen
  | cons v vs ih =>
    cases names with
    | nil => simp at hlen
    | cons n ns =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      rw [List.nodup_cons] at hnd
      unfold replaceLoop
      simp only [List.headD_cons, List.tail_cons, popName_eq]
      rw [ih ns _ hlen hnd.2]
      simp only [List.zip_cons_cons, List.map_cons, Prod.mk.injEq, List.cons.injEq, true_and]
      refine ⟨List.map_congr_left ?_, ?_⟩
      · intro ⟨m, w⟩ hm
        have hmn : n ≠ m := by
          intro he; subst he; exact hnd.1 (List.of_mem_zip hm).1
        simp only
        rw [kwLookup_filter kws n m hmn]
      · rw [List.filter_filter]
        apply List.filter_congr
        intro kv _
        by_cases h : kv.1 = n <;> simp [h, List.contains_cons]

theorem replaceSpec_proven : ReplaceSpec := by
  intro α t s kws hu hlen hnd
  have hloop := replaceLoop_spec t.names s kws hlen hnd
  constructor
  · intro hall
    have hmem : ∀ a b, (a, b) ∈ kws → a ∈ t.names := fun a b h =>
      List.mem_of_elem_eq_true (List.all_eq_true.mp hall (a, b) h)
    have hleft : kws.filter (fun kv => !t.names.contains kv.1) = [] := by
      rw [List.filter_eq_nil_iff]
      intro kv hkv
      have := List.all_eq_true.mp hall kv hkv
      simp only [Bool.not_eq_true', Bool.not_eq_false', Bool.not_eq_eq_eq_not, Bool.not_true]
      simpa using this
    unfold structseqReplace
    rw [hloop]
    simp only [hleft]
    simp [hu]
  · intro hany
    obtain ⟨kv, hkv, hn⟩ := List.any_eq_true.mp hany
    have hleft : kws.filter (fun kv => !t.names.contains kv.1) ≠ [] := by
      intro h
      have := List.filter_eq_nil_iff.mp h kv hkv
      simp_all
    refine ⟨.typeError "~Got unexpected field name(s): %R", ?_, rfl⟩
    unfold structseqReplace
    rw [hloop]
    simp only [show (0 : Nat) ≠ 0 ↔ False by simp, hu, show ¬ (0 : Nat) > 0 by omega, if_false, ite_false]
    simp only [ne_eq, hleft, not_false_eq_true, if_true, ite_true]

end PyLean.TypeObj.StructSeq
