import PyLean.CoreLibs.Coll.UserListGProps
import PyLean.ListSort.Modified

/-!
`UserList.__repr__`, `pop` and `sort`, Lib/collections/__init__.py:1299-1300, :1383-1384,
:1404-1405 (CPython 3.15.2), with fallible and recursive item reprs and the fallible `list.sort`
of `PyLean.ListSort` (comparisons and keys that raise and change the list).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace PyLean.CoreLibs.Coll

open PyLean
open PyLean.ListSort (PLt LView listSortImplFx listSortKeyImplFx listSortCntF applyEffs modifiedCheck)

variable {α : Type}

/-! ### `__repr__` -/

/-- An item of a list: an ordinary object, or a `UserList` (by id). -/
inductive LRef (α : Type) where
  | plain (v : α)
  | ul (id : Nat)

/-- `UserList.__repr__`, :1299-1300, `repr(self.data)`: `list_repr` (Objects/listobject.c), `[]` for an
empty list, then `Py_ReprEnter`, so a list whose `repr` is in progress (`running`, by the id of the
`UserList` holding it) prints `[...]`; each item's `repr` may raise. `heap i` is object `i`'s items. -/
def ulReprR (rv : α → Py String) (heap : Nat → Option (List (LRef α))) : Nat → List Nat → Nat → Py String
  | 0, _, _ => .error .modelFuel
  | fuel + 1, running, i =>
    match heap i with
    | none => .error (.named "NameError" "~no such object")
    | some [] => .ok "[]"
    | some items =>
      if i ∈ running then .ok "[...]"
      else do
        let parts ← items.mapM (fun x => match x with
          | .plain v => rv v
          | .ul j => ulReprR rv heap fuel (i :: running) j)
        pure ("[" ++ ", ".intercalate parts ++ "]")

theorem mapM_plainL (rv : α → Py String) (g : LRef α → Py String) (hg : ∀ v, g (.plain v) = rv v) :
    ∀ l : List α, (l.map LRef.plain).mapM g = l.mapM rv
  | [] => rfl
  | v :: t => by
    simp only [List.map_cons, List.mapM_cons, hg]
    rw [mapM_plainL rv g hg t]

/-- **`repr(u)` is `repr(u.data)`, with the list's recursion guard.** For every `repr` of items (free
to raise): a `UserList` of ordinary items prints `[r1, r2, ...]`; an empty one prints `[]`; one that
holds itself after an item prints `[r, [...]]`; an item whose `repr` raises makes it raise.

Source: Lib/collections/__init__.py:1299-1300; Objects/listobject.c `list_repr`. -/
def UserListReprR : Prop :=
  ∀ (α : Type) (rv : α → Py String) (heap : Nat → Option (List (LRef α))) (i fuel : Nat) (v : α)
    (rest : List (LRef α)) (e : PyExc),
    (∀ l : List α, l ≠ [] → heap i = some (l.map .plain) →
      ulReprR rv heap (fuel + 1) [] i = (do let parts ← l.mapM rv; pure ("[" ++ ", ".intercalate parts ++ "]"))) ∧
    (heap i = some [] → ulReprR rv heap (fuel + 1) [] i = .ok "[]") ∧
    (heap i = some [.plain v, .ul i] →
      ulReprR rv heap (fuel + 2) [] i = (do let a ← rv v; pure ("[" ++ ", ".intercalate [a, "[...]"] ++ "]"))) ∧
    (heap i = some (.plain v :: rest) → rv v = .error e → ulReprR rv heap (fuel + 1) [] i = .error e)

theorem userListReprR_proven : UserListReprR := by
  intro α rv heap i fuel v rest e
  refine ⟨fun l hl hh => ?_, fun hh => ?_, fun hh => ?_, fun hh he => ?_⟩
  · cases l with
    | nil => exact absurd rfl hl
    | cons a t =>
      simp only [ulReprR, hh, List.map_cons, List.not_mem_nil, if_false]
      rw [← List.map_cons, mapM_plainL rv _ (fun _ => rfl)]
  · simp only [ulReprR, hh]
  · simp only [ulReprR, hh, List.not_mem_nil, if_false, List.mapM_cons, List.mapM_nil, List.mem_cons, true_or,
      if_true]
    cases rv v <;> rfl
  · simp only [ulReprR, hh, List.not_mem_nil, if_false, List.mapM_cons, he]
    rfl

/-! ### `pop` -/

/-- **`pop` returns what `list.pop` returns and leaves its list.** For every `list` implementation and
index: `u.pop(i)` gives `self.data.pop(i)`'s value and its remaining items, or its exception; on
ints, `u.pop()` of a non-empty list returns the last item and keeps the others.

Source: Lib/collections/__init__.py:1383-1384; Doc/library/stdtypes.rst, `s.pop([i])`. -/
def UserListPop : Prop :=
  ∀ (α : Type) (ops : ListOps α) (u : UL α) (i : Option Int),
    (ulPop ops u i).map (·.1) = (ops.pop u.data i).map (·.1) ∧
    (ulPop ops u i).map (·.2.data) = (ops.pop u.data i).map (·.2) ∧
    (ulPop ops u i).map (·.2.cls) = (ops.pop u.data i).map (fun _ => u.cls)

theorem userListPop_proven : UserListPop := by
  intro α ops u i
  refine ⟨?_, ?_, ?_⟩ <;> (simp only [ulPop]; cases ops.pop u.data i <;> rfl)

theorem userListPopInt (c : String) (l : List Int) (x : Int) :
    ulPop intOps ⟨c, l ++ [x]⟩ none = .ok (x, ⟨c, l⟩) := by
  simp [ulPop, intOps, Sequences.listPop, Sequences.listPopK, Sequences.popArg, Sequences.validIndex,
    Sequences.ix, bind, Except.bind, pure, Except.pure, Except.map]
  have h1 : (-1 + ((l.length : Int) + 1)) = (l.length : Int) := by omega
  rw [h1, if_neg (by omega)]
  simp [List.eraseIdx_append_of_length_le]

/-! ### `sort` -/

/-- The arguments of `u.sort(...)`: the number of positional arguments, and the keywords `key`
(`none`: omitted; `some none`: `key=None`; else a function that may raise and change the list) and
`reverse` (omitted, or an object whose truth test may raise). Other keyword names are out of scope. -/
structure SortArgs (α κ ρ : Type) where
  npos : Nat := 0
  key : Option (Option (α → LView α → Py κ × LView α)) := none
  reverse : Option ρ := none

/-- The number of keyword arguments given. -/
def SortArgs.nkw {α κ ρ : Type} (a : SortArgs α κ ρ) : Nat :=
  (if a.key.isSome then 1 else 0) + (if a.reverse.isSome then 1 else 0)

/-- `UserList.sort(*args, **kwds)`, :1404-1405: `self.data.sort(*args, **kwds)`. Clinic
(Objects/clinic/listobject.c.h:248-270, `_PyArg_UnpackKeywords`, Python/getargs.c:2572-2593) first
refuses more than two arguments in all, then any positional one, then takes `key` and
`reverse = PyObject_IsTrue(reverse)` (`truth`, which may raise); then `list_sort_impl` with the
comparison `ltA` of items or `ltK` of keys, and `eff` what the comparisons do to the list. -/
def ulSortP {κ ρ : Type} (truth : ρ → Py Bool) (ltA : PLt α) (ltK : PLt κ) (eff : Nat → LView α → LView α)
    (u : UL α) (a : SortArgs α κ ρ) : Out (UL α) :=
  if a.npos + a.nkw > 2 then
    (u, some (.typeError s!"sort() takes at most 2 {if a.npos = 0 then "keyword " else ""}arguments ({a.npos + a.nkw} given)"))
  else if a.npos ≠ 0 then (u, some (.typeError "sort() takes no positional arguments"))
  else
    let rev : Py Bool := match a.reverse with
      | none => .ok false
      | some r => truth r
    match rev with
    | .error e => (u, some e)
    | .ok rev =>
      let r := match a.key.getD none with
        | none => listSortImplFx ltA eff u.data rev
        | some k => listSortKeyImplFx ltK k eff u.data rev
      (⟨u.cls, r.1⟩, r.2)

/-- **`u.sort(...)` is `list.sort` on `u.data`, argument checks and outcomes included.** For every
comparison and key (which may raise or change the list) and every `reverse` object: more than two
arguments in all is `sort() takes at most 2 arguments`, otherwise any positional argument is
`sort() takes no positional arguments`, both with `u` unchanged; a `reverse` whose truth test
raises raises that with `u` unchanged; otherwise `u.sort(key=k, reverse=r)` leaves `u.data` and
raises exactly as `self.data.sort(key=k, reverse=r)` does (with or without a key, `key=None` being
none), so a raising `<` or `key` is propagated and a sort whose comparisons touched the list
raises `ValueError('list modified during sort')`.

Source: Lib/collections/__init__.py:1404-1405; Objects/clinic/listobject.c.h:248-270;
Python/getargs.c:2572-2593; Objects/listobject.c:2965-3227. -/
def UserListSortP : Prop :=
  ∀ (α κ ρ : Type) (truth : ρ → Py Bool) (ltA : PLt α) (ltK : PLt κ) (eff : Nat → LView α → LView α)
    (u : UL α) (a : SortArgs α κ ρ) (b : Bool) (e : PyExc),
    (a.npos + a.nkw > 2 → ulSortP truth ltA ltK eff u a =
      (u, some (.typeError
        s!"sort() takes at most 2 {if a.npos = 0 then "keyword " else ""}arguments ({a.npos + a.nkw} given)"))) ∧
    (a.npos ≠ 0 → a.npos + a.nkw ≤ 2 →
      ulSortP truth ltA ltK eff u a = (u, some (.typeError "sort() takes no positional arguments"))) ∧
    (∀ r, a.npos = 0 → a.reverse = some r → truth r = .error e → ulSortP truth ltA ltK eff u a = (u, some e)) ∧
    (a.npos = 0 → (a.reverse.map truth).getD (.ok false) = .ok b → a.key.getD none = none →
      ulSortP truth ltA ltK eff u a = (⟨u.cls, (listSortImplFx ltA eff u.data b).1⟩,
        (listSortImplFx ltA eff u.data b).2)) ∧
    (∀ k, a.npos = 0 → (a.reverse.map truth).getD (.ok false) = .ok b → a.key.getD none = some k →
      ulSortP truth ltA ltK eff u a = (⟨u.cls, (listSortKeyImplFx ltK k eff u.data b).1⟩,
        (listSortKeyImplFx ltK k eff u.data b).2)) ∧
    (∀ r n, a.npos = 0 → (a.reverse.map truth).getD (.ok false) = .ok b → a.key.getD none = none →
      listSortCntF ltA u.data b = (r, n, none) → (applyEffs eff n LView.during).allocated ≠ -1 →
      (ulSortP truth ltA ltK eff u a).2 = some (.valueError "list modified during sort"))

theorem nkw_le {α κ ρ : Type} (a : SortArgs α κ ρ) : a.nkw ≤ 2 := by
  unfold SortArgs.nkw; split <;> split <;> omega

theorem userListSortP_proven : UserListSortP := by
  intro α κ ρ truth ltA ltK eff u a b e
  have hrev : ∀ b, (a.reverse.map truth).getD (.ok false) = .ok b →
      (match a.reverse with | none => (Except.ok false : Py Bool) | some r => truth r) = .ok b := by
    intro b h; cases hr : a.reverse <;> simp_all
  have h2 : ¬ 2 < a.nkw := by have := nkw_le a; omega
  refine ⟨fun h => ?_, fun h h3 => ?_, fun r h hr he => ?_, fun h hb hk => ?_, fun k h hb hk => ?_,
    fun r n h hb hk hs ha => ?_⟩
  · simp only [ulSortP, h, if_true]
  · simp [ulSortP, h, show ¬ (a.npos + a.nkw > 2) by omega]
  · simp [ulSortP, h, h2, hr, he]
  · simp [ulSortP, h, h2, hrev b hb, hk]
  · simp [ulSortP, h, h2, hrev b hb, hk]
  · simp [ulSortP, h, h2, hrev b hb, hk, listSortImplFx, hs, modifiedCheck, ha]

/-- **`[a] < [b, 2]` when `a == b`: past an `==`-true prefix the lengths decide.** For every
element comparison: when `u.data`'s items are pairwise identical or `==` to the first items of `l`,
and `l` is longer, every ordering is the comparison of the lengths.

Source: Objects/listobject.c:3497-3500. -/
def UserListLenAfterPrefix : Prop :=
  ∀ (α β : Type) [DecidableEq α] (E : ElemOps α β) (op : CmpOp) (u : UL α) (l t : List α) (P : List (α × α)),
    (∀ p ∈ P, eqId E p.1 p.2 = .ok true) → u.data = P.map (·.1) → l = P.map (·.2) ++ t → op ≠ .eq →
    ulCmpP E op u (.list l) = .ok (.bool (cmpLen op P.length (P.length + t.length)))

theorem userListLenAfterPrefix_proven : UserListLenAfterPrefix := by
  intro α β _ E op u l t P hP hu hl hop
  have hd : firstDiff E u.data l = .ok none := by
    rw [hu, hl]
    have := firstDiff_eqPrefix E P [] t hP
    rw [List.append_nil] at this
    rw [this]
    cases t <;> rfl
  simp only [ulCmpP, listRichP]
  rw [if_neg (fun h => hop h.2), hd]
  show Except.ok (CRes.bool (cmpLen op u.data.length l.length)) = _
  rw [hu, hl]
  simp

end PyLean.CoreLibs.Coll
