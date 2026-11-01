import PyLean.TypeObj.Call

/-!
Properties of `_list_extend`, `Objects/listobject.c:1478`, reached from `list +=` and
`list.__init__`. They quantify over every `Rt`, so over every `__iter__` and `__next__`.
-/

namespace PyLean.TypeObj

/-- **The loop keeps what it has.** For every `__next__`: an item that arrives is in the list
before `__next__` runs again, and a raising `__next__` ends the loop in exactly the world it
raised in. With the two together, `l += it` keeps the items before the exception. -/
def ListExtendLoopStep : Prop :=
  ∀ (rt : Rt) (addr : Addr) (it : Val) (fuel : Nat) (w w1 : World),
    (∀ (x : Val) (w2 : World), rt.iterNext it w = .ok (some x) w1 →
      listAppendAll addr [x] w1 = .ok () w2 →
      listExtendLoop rt addr it (fuel + 1) w = listExtendLoop rt addr it fuel w2) ∧
    (∀ e : PyErr, rt.iterNext it w = .err e w1 →
      listExtendLoop rt addr it (fuel + 1) w = .err e w1) ∧
    (rt.iterNext it w = .ok none w1 →
      listExtendLoop rt addr it (fuel + 1) w = .ok () w1)

theorem listExtendLoopStep_proven : ListExtendLoopStep := by
  intro rt addr it fuel w w1
  refine ⟨?_, ?_, ?_⟩
  · intro x w2 h1 h2
    simp [listExtendLoop, h1, h2]
  · intro e h1
    simp [listExtendLoop, h1]
  · intro h1
    simp [listExtendLoop, h1]

/-- **Extending a list with itself runs no Python code.** For every `Rt`, and so for every
`__iter__` and `__len__` a subclass defines, `l += l` doubles the list directly. -/
def ListExtendSelf : Prop :=
  ∀ (rt : Rt) (a : Addr) (w : World),
    listExtend rt (.obj a) a (.obj a) w =
      listAppendAll a ((listOf w (.obj a)).getD []) w

theorem listExtendSelf_proven : ListExtendSelf := by
  intro rt a w
  simp [listExtend, Val.is]

/-- **A size hint that overflows is ignored.** `m + n` beyond `PY_SSIZE_T_MAX` reserves nothing
and the loop runs (`Objects/listobject.c:1317`); otherwise a total of `2 ^ 48` or more is a
`MemoryError`. The bound `2 ^ 48` is the model's stand-in for allocator failure, a limit of the
platform rather than of the language. -/
def ListReserveRule : Prop :=
  ∀ (m n : Int) (w : World),
    (m > PyLean.ssizeMax - n → listReserve m n w = .ok () w) ∧
    (m ≤ PyLean.ssizeMax - n → m + n ≥ 2 ^ 48 →
      listReserve m n w = (raiseC B.MemoryError "" : M Unit) w)

theorem listReserveRule_proven : ListReserveRule := by
  intro m n w
  constructor
  · intro h
    simp [listReserve, h]
  · intro h1 h2
    have h3 : ¬ m > PyLean.ssizeMax - n := by omega
    have h4 : (281474976710656 : Int) ≤ m + n := by omega
    simp [listReserve, h3, h4]

/-- **The iterator comes first.** `list_extend_iter_lock_held` calls `PyObject_GetIter`, then
the hint, and a failure of `__iter__` ends it before the hint runs. -/
def ListExtendIterFirst : Prop :=
  ∀ (rt : Rt) (addr : Addr) (b : Val) (e : PyErr) (w w1 : World),
    rt.getIter b w = .err e w1 → listExtendIter rt addr b w = .err e w1

theorem listExtendIterFirst_proven : ListExtendIterFirst := by
  intro rt addr b e w w1 h
  simp [listExtendIter, h]

/-- **`list.__init__` clears first.** For every `Rt`, `l.__init__(x)` empties the list and then
extends it, so `l.__init__(l)` leaves it empty and `l.__init__(iter(l))` sees no items. -/
def ListInitClearsFirst : Prop :=
  ∀ (rt : Rt) (a : Addr) (x : Val) (w : World),
    listInit rt (.obj a) [x] [] w =
      (do
        modObj a fun o => { o with body := .list [] }
        listExtend rt (.obj a) a x : M Unit) w

theorem listInitClearsFirst_proven : ListInitClearsFirst := by
  intro rt a x w
  simp [listInit, noKeywords, unpackTuple]

end PyLean.TypeObj
