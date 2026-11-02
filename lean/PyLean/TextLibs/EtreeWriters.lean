import PyLean.TextLibs.EtreeProps
import PyLean.Sequences.Insert

/-!
`Element.append`, `extend` and `insert`: the C accelerator (Modules/_elementtree.c) against the
pure-Python twin (Lib/xml/etree/ElementTree.py:222-252), on the model of `EtreeModel.lean`.

Argument Clinic checks `subelement: object(subclass_of=Element_Type)` and converts
`index: Py_ssize_t` before the body runs, in parameter order; the Python twin checks the type
first and leaves the index to `list.insert`.
-/

namespace PyLean.TextLibs.Etree

open PyLean PyLean.Sequences

set_option linter.unusedSectionVars false

variable {α : Type} [Inhabited α]

/-- Argument Clinic's `subclass_of` failure (`_PyArg_BadArgument`): "<fn>() argument [n] must be
xml.etree.ElementTree.Element, not <type>". -/
def clinicTypeErr (T : Ty α) (what : String) (x : α) : PyExc :=
  .typeError s!"{what} must be xml.etree.ElementTree.Element, not {T.tpName x}"

/-- `element_add_subelement`, :538-555, for an Element (the type check there is what
`extend` relies on; `append` has passed Clinic's check already). -/
def addAllC (T : Ty α) : List α → List α → Out α
  | kids, [] => (kids, .ok ())
  | kids, x :: xs => if T.isElem x then addAllC T (kids ++ [x]) xs else (kids, .error (typeErrC T x))

/-- `Element.append`, :716-735. -/
def appendC (T : Ty α) (kids : List α) (x : α) : Out α :=
  if T.isElem x then (kids ++ [x], .ok ()) else (kids, .error (clinicTypeErr T "append() argument 1" x))

/-- `PySequence_Fast(elements, "'elements' must be an iterable")` as in `fastC`. -/
def fastExtend (kids : List α) : Arg α → List α × Py (List α)
  | .seq xs => (kids, .ok xs)
  | .iter xs stop eff => (eff kids, match stop with | none => .ok xs | some e => .error e)
  | .notIter _ => (kids, .error (.typeError "'elements' must be an iterable"))

/-- `Element.extend`, :1246-1282: the whole iterable first, then one `element_add_subelement`
per item, stopping at the first non-Element. -/
def extendC (T : Ty α) (kids : List α) (a : Arg α) : Out α :=
  let (kids, r) := fastExtend kids a
  match r with
  | .error e => (kids, .error e)
  | .ok xs => addAllC T kids xs

/-- The shift loop of `Element.insert`, :1584-1585:
`for (i = length; i > index; i--) children[i] = children[i-1];`. -/
def insShift (mem : List α) (length index : Int) : List α :=
  (List.range (length - index).toNat).foldl
    (fun m (k : Nat) => m.set (length - k).toNat (ix m (length - k - 1))) mem

/-- `Element.insert(index, subelement)`, :1552-1592: Clinic converts `index`, then checks the
type; the body clamps `index` into `[0, length]`, grows the buffer, shifts and stores. -/
def insertC (T : Ty α) (kids : List α) (index : Int) (x : α) : Out α :=
  match asSsize index with
  | .error e => (kids, .error e)
  | .ok index =>
    if !T.isElem x then (kids, .error (clinicTypeErr T "insert() argument 2" x))
    else
      let length : Int := kids.length
      let index := if index < 0 then (if index + length < 0 then 0 else index + length) else index
      let index := if index > length then length else index
      let mem := insShift (kids ++ [default]) length index
      (mem.set index.toNat x, .ok ())

/-- `Element.append`, ElementTree.py:222-230. -/
def appendPy (T : Ty α) (kids : List α) (x : α) : Out α :=
  if !T.isElem x then (kids, .error (typeErrPy T x)) else (listAppend kids x, .ok ())

def addAllPy (T : Ty α) : List α → List α → Out α
  | kids, [] => (kids, .ok ())
  | kids, x :: xs => if !T.isElem x then (kids, .error (typeErrPy T x)) else addAllPy T (listAppend kids x) xs

/-- `Element.extend`, ElementTree.py:233-241: check and append item by item as the iterable
yields them. -/
def extendPy (T : Ty α) (kids : List α) : Arg α → Out α
  | .notIter n => (kids, .error (.typeError s!"'{n}' object is not iterable"))
  | .seq xs => addAllPy T kids xs
  | .iter xs stop eff =>
    match addAllPy T (eff kids) xs with
    | (k, .error e) => (k, .error e)
    | (k, .ok ()) => match stop with
      | some e => (k, .error e)
      | none => (k, .ok ())

/-- `Element.insert`, ElementTree.py:243-246. -/
def insertPy (T : Ty α) (kids : List α) (index : Int) (x : α) : Out α :=
  if !T.isElem x then (kids, .error (typeErrPy T x)) else ofList kids (listInsert kids index x)

/-! ## Properties -/

/-- For Element arguments, `append` and `insert` leave the same children and raise the same
exception in both twins for every int index, and `extend` of a list or tuple leaves the same
children and raises the same exception class. -/
def WritersTwins : Prop :=
  ∀ (α : Type) [Inhabited α] (T : Ty α) (kids : List α),
    (kids.length : Int) < ssizeMax →
    (∀ x, T.isElem x → appendC T kids x = appendPy T kids x) ∧
    (∀ i x, T.isElem x → insertC T kids i x = insertPy T kids i x) ∧
    (∀ xs, (extendC T kids (.seq xs)).1 = (extendPy T kids (.seq xs)).1 ∧
      Agree (extendC T kids (.seq xs)).2 (extendPy T kids (.seq xs)).2)

theorem addAll_twins (T : Ty α) (kids xs : List α) :
    (addAllC T kids xs).1 = (addAllPy T kids xs).1 ∧ Agree (addAllC T kids xs).2 (addAllPy T kids xs).2 := by
  induction xs generalizing kids with
  | nil => exact ⟨rfl, rfl⟩
  | cons x xs ih =>
    unfold addAllC addAllPy
    cases h : T.isElem x
    · simp [Agree, PyExc.className, typeErrC, typeErrPy]
    · simp only [Bool.not_true, if_true, if_false, listAppend, Bool.false_eq_true]
      exact ih _

/-- The insert shift equals `insAt` for an index in `[0, length]`. -/
theorem insert_shift (kids : List α) (x : α) (j : Nat) (hj : j ≤ kids.length) :
    (insShift (kids ++ [default]) kids.length j).set j x = insAt kids j x := by
  have hlen : (kids ++ [(default : α)]).length = kids.length + 1 := by simp
  have hs : insShift (kids ++ [default]) kids.length j =
      (List.range (kids.length - j)).foldl
        (fun m (k : Nat) => m.set (kids.length - 1 - k + 1) (m.getD (kids.length - 1 - k) default))
        (kids ++ [default]) := by
    unfold insShift
    rw [show ((kids.length : Int) - (j : Int)).toNat = kids.length - j by omega]
    apply foldl_range_congr
    intro m k hk
    simp only [ix]
    rw [show ((kids.length : Int) - (k : Int)).toNat = kids.length - 1 - k + 1 by omega,
      show ((kids.length : Int) - (k : Int) - 1).toNat = kids.length - 1 - k by omega]
  apply List.ext_getElem?
  intro p
  rw [hs, set_getElem?, foldl_set_length, hlen, shiftUp_nat _ _ _ _ (by omega) hlen,
    show ([default] : List α) = List.replicate 1 default from rfl, pad_get, pad_get]
  unfold insAt
  by_cases h1 : p < j
  · rw [if_neg (by omega), if_neg (by omega), if_pos (by omega),
      List.getElem?_append_left (by simp; omega), List.getElem?_take_of_lt h1]
  · by_cases h2 : p = j
    · subst h2
      rw [if_pos ⟨rfl, by omega⟩, List.getElem?_append_right (by simp; omega)]
      simp [Nat.min_eq_left hj]
    · rw [if_neg (fun h => h2 h.1), List.getElem?_append_right (by simp; omega)]
      rw [show p - (kids.take j).length = (p - j - 1) + 1 by simp; omega, List.getElem?_cons_succ,
        List.getElem?_drop]
      by_cases h3 : p < kids.length + 1
      · rw [if_pos (by omega), if_pos (by omega)]
        congr 1; omega
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), List.getElem?_eq_none (by omega)]

theorem writersTwins_proven : WritersTwins := by
  intro α _ T kids hn
  refine ⟨fun x hx => ?_, fun i x hx => ?_, fun xs => ?_⟩
  · simp [appendC, appendPy, hx, listAppend]
  · unfold insertC insertPy ofList listInsert
    cases h : asSsize i with
    | error e => simp [hx, h, bind, Except.bind]
    | ok j =>
      simp only [hx, Bool.not_true, if_false, Bool.false_eq_true, h, bind, Except.bind, pure,
        Except.pure, listIns1, ins1Pos]
      have hb := ins1Pos_bounds kids.length j (by omega)
      unfold ins1Pos at hb
      generalize hw : (if (if j < 0 then (if j + kids.length < 0 then 0 else j + kids.length) else j) >
          (kids.length : Int) then (kids.length : Int)
          else (if j < 0 then (if j + kids.length < 0 then 0 else j + kids.length) else j)) = w at hb ⊢
      obtain ⟨w, rfl⟩ := Int.eq_ofNat_of_zero_le hb.1
      rw [show ((w : Int)).toNat = w by omega, insert_shift kids x w (by omega)]
  · exact addAll_twins T kids xs

/-- `extend` leaves the same children in both twins for every iterable. -/
def ExtendTwins : Prop :=
  ∀ (α : Type) [Inhabited α] (T : Ty α) (kids : List α) (a : Arg α),
    (extendC T kids a).1 = (extendPy T kids a).1

/-- An iterator that yields two Elements and then raises: C collects the whole iterable before
appending and leaves the children as they were; the twin has appended both. -/
theorem extendTwins_refuted : ¬ ExtendTwins := by
  intro h
  have := h Nat caseTy [] (.iter [60, 61] (some (.valueError "boom")) id)
  revert this
  decide

/-- A child that is not an Element is refused by both twins with `TypeError` and the children are
left as they were: C through Argument Clinic's `subclass_of` check (for `insert`, after converting
`index`), Python through `_assert_is_element` (ElementTree.py:248-252), for every non-Element value
and every index that fits `Py_ssize_t`. -/
def WritersRefuse : Prop :=
  ∀ (α : Type) [Inhabited α] (T : Ty α) (kids : List α) (x : α) (i : Int),
    T.isElem x = false → -ssizeMax - 1 ≤ i → i ≤ ssizeMax →
    appendC T kids x = (kids, .error (clinicTypeErr T "append() argument 1" x)) ∧
    appendPy T kids x = (kids, .error (typeErrPy T x)) ∧
    insertC T kids i x = (kids, .error (clinicTypeErr T "insert() argument 2" x)) ∧
    insertPy T kids i x = (kids, .error (typeErrPy T x))

theorem writersRefuse_proven : WritersRefuse := by
  intro α _ T kids x i hx h1 h2
  have ha : asSsize i = .ok i := by
    unfold ssizeMax at h1 h2
    unfold asSsize ssizeMin ssizeMax
    rw [if_pos (by omega)]
  refine ⟨by simp [appendC, hx], by simp [appendPy, hx], ?_, by simp [insertPy, hx]⟩
  simp [insertC, ha, hx]

end PyLean.TextLibs.Etree
