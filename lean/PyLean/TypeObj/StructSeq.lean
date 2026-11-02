import PyLean.Core

/-!
Struct sequences (`os.stat_result`, `time.struct_time`, ...), Objects/structseq.c, CPython 3.15.2:
the constructor `structseq_new_impl` (:167-272) and `__reduce__` (`structseq_reduce`, :389-428).

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

/-- The hidden fields read from the dict (:240-255): each found name counts. -/
def fillFromDict (t : SType) (items : List (Key × Option α)) (len : Nat) : List (Option α) × Nat :=
  (List.range (t.nFields - len)).foldl (fun (acc, n) k =>
    match lookup items (t.nameOf (len + k)) with
    | some v => (acc ++ [v], n + 1)
    | none => (acc ++ [none], n)) ([], 0)

/-- `structseq_new_impl(type, arg, dict)`, :167-272. -/
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

/-- `structseq_reduce`, :389-428: `(type, (tuple(visible), {name: value for hidden fields}))`. -/
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

end PyLean.TypeObj.StructSeq
