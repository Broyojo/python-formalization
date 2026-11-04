import PyLean.CoreLibs.Coll.UserStringProps
import PyLean.CoreLibs.Coll.UserListG
import PyLean.CoreLibs.Coll.CounterProps2

/-!
`collections.UserString` where its body calls Python code, Lib/collections/__init__.py:1418-1667
(CPython 3.15.2): `str(x)` in `__init__`, `__add__`, `__radd__` and `__rmod__` (the object's
`__str__`, which may raise), comparisons against an object with its reflected method,
`__getnewargs__` as a tuple, and `join` over a fallible iterable. Also the `TypeError` the
non-unwrapping methods raise for a `UserString` argument.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace PyLean.CoreLibs.Coll

open PyLean
open PyLean.StrSearch

/-- An argument whose `str()` is Python code: a `str`, a `UserString`, or another object (its type
name and `str(obj)`, which may raise). -/
inductive SArgP where
  | str (s : Seq)
  | user (s : Seq)
  | other (ty : String) (text : Py Seq)

/-- `str(x)`: a `str` itself, a `UserString`'s `__str__` (`str(self.data)`), else `__str__`. -/
def strOf : SArgP → Py Seq
  | .str s | .user s => .ok s
  | .other _ t => t

/-- `UserString.__init__`, :1420-1426: a `str` as is, a `UserString`'s `data[:]`, else `str(seq)`. -/
def usNewP (cls : String) : SArgP → Py US
  | .str s => .ok ⟨cls, s⟩
  | .user s => .ok ⟨cls, s⟩
  | .other _ t => t.map (fun s => ⟨cls, s⟩)

/-- `UserString.__add__`, :1485-1490: `other.data`, a `str`, else `str(other)`. -/
def usAddP (u : US) : SArgP → Py US
  | .user t | .str t => .ok ⟨u.cls, u.data ++ t⟩
  | .other _ t => t.map (fun s => ⟨u.cls, u.data ++ s⟩)

/-- `UserString.__radd__`, :1492-1495: a `str` as is, else `str(other)`. -/
def usRaddP (u : US) (a : SArgP) : Py US := (strOf a).map (fun s => ⟨u.cls, s ++ u.data⟩)

/-- `UserString.__rmod__`, :1505-1506: `self.__class__(str(template) % self)`. -/
def usRmodP (ops : UniOps) (u : US) (template : SArgP) : Py US := do
  let t ← strOf template
  wrapIn u (ops.modUser t u.data)

/-- `UserString.__getnewargs__`, :1446-1447: the 1-tuple `(self.data[:],)`. -/
def usGetnewargsP (u : US) : List Seq := [u.data]

/-- The operand of a comparison: a `str`, a `UserString`, or another object with its reflected
method for each operator (`none`: `NotImplemented`). -/
inductive SCOpnd (β : Type) where
  | str (s : Seq)
  | user (s : Seq)
  | other (ty : String) (refl : SOp → Option (Py β))

/-- `UserString.__eq__`, ..., `__ge__`, :1449-1472: `self.data op string` after unwrapping a
`UserString`; against another object `str` returns `NotImplemented`, then the operand's reflected
method answers, or `==` is identity (false) and the orderings raise. -/
def usRichP {β : Type} (op : SOp) (u : US) : SCOpnd β → Py (CRes β)
  | .str t | .user t => .ok (.bool (op.test (seqCmp u.data t)))
  | .other ty refl =>
    match refl op with
    | some r => CRes.obj <$> r
    | none =>
      if op = .eq then .ok (.bool false)
      else .error (.typeError s!"'{op.sym}' not supported between instances of 'str' and '{ty}'")

/-- `UserString.join`, :1596-1597, `self.data.join(seq)`: `PySequence_Fast(seq, "can only join an
iterable")` (Objects/unicodeobject.c:10027) reads the whole iterable first, replacing a `TypeError`
from `iter()`; then `strJoin`'s item checks. -/
def usJoinP (u : US) (it : Py (FIt SArg)) : Py Seq :=
  match it with
  | .error (.typeError _) => .error (.typeError "can only join an iterable")
  | .error e => .error e
  | .ok it =>
    match it.stop with
    | some e => .error e
    | none => strJoin u.data it.xs

/-! ### Properties -/

/-- **`str()` is called where the source calls it, and may raise.** For every class and object:
`UserString(x)`, `u + x`, `x + u` and `x % u` use `str(x)` for an object that is neither a `str` nor
a `UserString`, and an `__str__` that raises makes each raise; for a returning `__str__` they are
the models of `UserString.lean`. `u.__getnewargs__()` is the 1-tuple of `u.data`, and `cls(*args)`
rebuilds `u`.

Source: Lib/collections/__init__.py:1420-1426, :1446-1447, :1485-1495, :1505-1506; the copy
protocol requires `__getnewargs__` to return a tuple (Objects/typeobject.c). -/
def UserStringStrCalls : Prop :=
  ∀ (ops : UniOps) (cls ty : String) (u : US) (t : Seq) (e : PyExc),
    usNewP cls (.other ty (.error e)) = .error e ∧
    usAddP u (.other ty (.error e)) = .error e ∧
    usRaddP u (.other ty (.error e)) = .error e ∧
    usRmodP ops u (.other ty (.error e)) = .error e ∧
    usNewP cls (.other ty (.ok t)) = .ok (usNew cls (.other ty t)) ∧
    usAddP u (.other ty (.ok t)) = .ok (usAdd u (.other ty t)) ∧
    usRaddP u (.other ty (.ok t)) = .ok (usRadd u (.other ty t)) ∧
    usRaddP u (.user t) = .ok (usRadd u (.user t)) ∧
    usRmodP ops u (.str t) = usRmod ops u t ∧
    usGetnewargsP u = [u.data] ∧ (usGetnewargsP u).length = 1 ∧
    (∀ s, usGetnewargsP u = [s] → usNewP u.cls (.str s) = .ok u)

theorem userStringStrCalls_proven : UserStringStrCalls := by
  intro ops cls ty u t e
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun s hs => ?_⟩
  simp only [usGetnewargsP, List.cons.injEq, and_true] at hs
  subst hs
  rfl

/-- **Comparisons against other objects go through the reflected method.** For every
`UserString` and comparison: a `UserString` operand compares by its data, like the equal `str`;
against another object whose reflected method returns, its object is the result
(`UserString('a') == mock.ANY` is `True`); when it returns `NotImplemented`, `==` is `False` and
the orderings raise `TypeError`; an operand's raising method raises.

Source: Lib/collections/__init__.py:1449-1472; Doc/reference/datamodel.rst (rich comparisons). -/
def UserStringCompareP : Prop :=
  ∀ (β : Type) (op : SOp) (u : US) (t : Seq) (ty : String) (refl : SOp → Option (Py β)),
    usRichP (β := β) op u (.user t) = usRichP op u (.str t) ∧
    usRichP (β := β) op u (.str t) = (usRich op u (.str t)).map CRes.bool ∧
    (∀ r, refl op = some r → usRichP op u (.other ty refl) = CRes.obj <$> r) ∧
    (refl op = none → usRichP op u (.other ty refl) =
      if op = .eq then .ok (.bool false)
      else .error (.typeError s!"'{op.sym}' not supported between instances of 'str' and '{ty}'"))

theorem userStringCompareP_proven : UserStringCompareP := by
  intro β op u t ty refl
  refine ⟨rfl, rfl, fun r hr => ?_, fun hr => ?_⟩
  · simp [usRichP, hr]
  · simp only [usRichP, hr]

/-- **The methods without the unwrap line refuse a `UserString` argument, and `join` reads its
iterable first.** For every `UserString` `u` and text `s`: `strip`, `lstrip`, `rstrip` with
`chars=UserString(s)`, `rpartition`, `split` and `rsplit` with `sep=UserString(s)`, `center`,
`ljust`, `rjust` with `fillchar=UserString(s)` (and a width that fits), and `join` of a list holding
a `UserString`, each raise the `TypeError` of the `str` method; `u.join(5)` raises
`can only join an iterable`, and an iterator that raises makes `join` raise it before any item is
checked.

Source: Lib/collections/__init__.py:1515-1516, :1596-1652 (no `isinstance(..., UserString)` test, unlike
`count` or `replace`); Objects/unicodeobject.c. -/
def UserStringNoUnwrap : Prop :=
  ∀ (ops : UniOps) (u : US) (s : Seq) (w m : Int) (e : PyExc) (rest : List SArg),
    ssizeMin ≤ w → w ≤ ssizeMax → ssizeMin ≤ m → m ≤ ssizeMax →
    usCall ops (.strip (some (.user s)) .both) u = .error (.typeError "strip arg must be None or str") ∧
    usCall ops (.strip (some (.user s)) .left) u = .error (.typeError "lstrip arg must be None or str") ∧
    usCall ops (.strip (some (.user s)) .right) u = .error (.typeError "rstrip arg must be None or str") ∧
    usCall ops (.rpartition (.user s)) u = .error (.typeError "must be str, not collections.UserString") ∧
    usCall ops (.split (some (.user s)) m) u = .error (.typeError "must be str or None, not UserString") ∧
    usCall ops (.rsplit (some (.user s)) m) u = .error (.typeError "must be str or None, not UserString") ∧
    usCall ops (.center w (some (.user s))) u =
      .error (.typeError "The fill character must be a unicode character, not UserString") ∧
    usCall ops (.ljust w (some (.user s))) u =
      .error (.typeError "The fill character must be a unicode character, not UserString") ∧
    usCall ops (.rjust w (some (.user s))) u =
      .error (.typeError "The fill character must be a unicode character, not UserString") ∧
    usCall ops (.join (.user s :: rest)) u =
      .error (.typeError "sequence item 0: expected str instance, UserString found") ∧
    (∀ msg, usJoinP u (.error (.typeError msg)) = .error (.typeError "can only join an iterable")) ∧
    (∀ xs, usJoinP u (.ok ⟨xs, some e⟩) = .error e) ∧
    (∀ xs, usJoinP u (.ok ⟨xs, none⟩) = usJoin u xs)

theorem userStringNoUnwrap_proven : UserStringNoUnwrap := by
  intro ops u s w m e rest hw1 hw2 hm1 hm2
  have hw : argSsize w = .ok w := by simp [argSsize]; omega
  have hm : argSsize m = .ok m := by simp [argSsize]; omega
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
  · simp only [usCall, usSplit, strSplitA, hm, ok_bind]; rfl
  · simp only [usCall, usRSplit, strRSplitA, hm, ok_bind]; rfl
  · simp only [usCall, usCenter, strCenterA, hw, ok_bind]; rfl
  · simp only [usCall, usLjust, strLjustA, hw, ok_bind]; rfl
  · simp only [usCall, usRjust, strRjustA, hw, ok_bind]; rfl

/-- **Clinic converts the integer argument first.** For every receiver: `center`, `ljust`, `rjust`
with a width outside `Py_ssize_t` raise `OverflowError` whatever the fill character (so
`'a'.center(2**63, 'ab')` is not the fill `TypeError`), and so do `split` and `rsplit` with such a
`maxsplit`, whatever `sep`.

Source: Objects/clinic/unicodeobject.c.h:115-132; Objects/unicodeobject.c:12900-12912. -/
def StrClinicOrder : Prop :=
  ∀ (s : Seq) (w : Int) (fill sep : Option SArg), (w < ssizeMin ∨ w > ssizeMax) →
    let ov : PyExc := .overflowError "Python int too large to convert to C ssize_t"
    strCenterA s w fill = .error ov ∧ strLjustA s w fill = .error ov ∧ strRjustA s w fill = .error ov ∧
    strSplitA s sep w = .error ov ∧ strRSplitA s sep w = .error ov

theorem strClinicOrder_proven : StrClinicOrder := by
  intro s w fill sep hw
  have h : argSsize w = .error (.overflowError "Python int too large to convert to C ssize_t") := by
    simp [argSsize, hw]
  simp only [strCenterA, strLjustA, strRjustA, strSplitA, strRSplitA, h]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end PyLean.CoreLibs.Coll
