import PyLean.CoreLibs.Misc.Contextlib.Model

/-!
Facts about the exception heap of `Exc.lean`: raising only rewrites `__context__`, allocation
appends.
-/

namespace PyLean.CoreLibs.Misc.Contextlib

/-- Two exception objects that agree on everything but `__context__`. -/
def SameData (a b : ExcObj) : Prop :=
  a.children = b.children ∧ a.msg = b.msg ∧ a.cause = b.cause ∧ a.tb = b.tb ∧ a.cls = b.cls

theorem SameData.refl (a : ExcObj) : SameData a a := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem SameData.trans {a b c : ExcObj} (h1 : SameData a b) (h2 : SameData b c) : SameData a c :=
  ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.1.trans h2.2.2.1, h1.2.2.2.1.trans h2.2.2.2.1,
    h1.2.2.2.2.trans h2.2.2.2.2⟩

theorem length_set (h : Heap) (a : ExcId) (o : ExcObj) : (h.set a o).length = h.length := by
  simp

theorem length_setContext (h : Heap) (a : ExcId) (c : Option ExcId) :
    (h.setContext a c).length = h.length := by
  simp [Heap.setContext, Heap.modify]

theorem length_breakCycle (value : ExcId) :
    ∀ (fuel : Nat) (h : Heap) (o slow : ExcId) (t : Bool),
      (Heap.breakCycle value fuel h o slow t).length = h.length := by
  intro fuel
  induction fuel with
  | zero => intro h o slow t; rfl
  | succ f ih =>
    intro h o slow t
    simp only [Heap.breakCycle]
    split
    · rfl
    · split
      · exact length_setContext _ _ _
      · split
        · rfl
        · exact ih _ _ _ _

theorem length_raiseCtx (h : Heap) (value : ExcId) (handled : Option ExcId) :
    (h.raiseCtx value handled).length = h.length := by
  unfold Heap.raiseCtx
  split
  · rfl
  · split
    · rfl
    · rw [length_setContext, length_breakCycle]

theorem setContext_same (h : Heap) (a : ExcId) (c : Option ExcId) (r : ExcId) :
    SameData ((h.setContext a c).get r) (h.get r) := by
  simp only [Heap.setContext, Heap.modify, Heap.get]
  by_cases har : a = r
  · subst har
    by_cases hl : a < h.length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_set_self (by omega)]
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · rw [List.set_eq_of_length_le (Nat.le_of_not_lt hl)]
      exact SameData.refl _
  · rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne har, ← List.getD_eq_getElem?_getD]
    exact SameData.refl _

theorem breakCycle_same (value : ExcId) (r : ExcId) :
    ∀ (fuel : Nat) (h : Heap) (o slow : ExcId) (t : Bool),
      SameData ((Heap.breakCycle value fuel h o slow t).get r) (h.get r) := by
  intro fuel
  induction fuel with
  | zero => intro h o slow t; exact SameData.refl _
  | succ f ih =>
    intro h o slow t
    simp only [Heap.breakCycle]
    split
    · exact SameData.refl _
    · split
      · exact setContext_same _ _ _ _
      · split
        · exact SameData.refl _
        · exact ih _ _ _ _

theorem raiseCtx_same (h : Heap) (value : ExcId) (handled : Option ExcId) (r : ExcId) :
    SameData ((h.raiseCtx value handled).get r) (h.get r) := by
  unfold Heap.raiseCtx
  split
  · exact SameData.refl _
  · split
    · exact SameData.refl _
    · exact (setContext_same _ _ _ _).trans (breakCycle_same _ _ _ _ _ _ _)

theorem isInst_of_same {h h' : Heap} {e : ExcId} (hs : SameData (h'.get e) (h.get e)) (n : String) :
    h'.isInst e n = h.isInst e n := by
  simp [Heap.isInst, hs.2.2.2.2]

theorem get_alloc_lt (h : Heap) (o : ExcObj) (r : ExcId) (hr : r < h.length) :
    (h.alloc o).1.get r = h.get r := by
  simp [Heap.alloc, Heap.get, List.getD_eq_getElem?_getD, List.getElem?_append_left hr]

theorem get_alloc_last (h : Heap) (o : ExcObj) : (h.alloc o).1.get (h.alloc o).2 = o := by
  simp [Heap.alloc, Heap.get, List.getD_eq_getElem?_getD]

/-- The object `raiseNew` makes keeps its class, message and cause. -/
theorem raiseNew_obj {σ : Type} (s : St σ) (c : Cls) (msg : String) (hd : Option ExcId) :
    SameData ((s.raiseNew c msg hd).1.h.get (s.raiseNew c msg hd).2) { cls := c, msg := msg } := by
  simp only [St.raiseNew]
  have := raiseCtx_same (s.h.alloc { cls := c, msg := msg }).1 (s.h.alloc { cls := c, msg := msg }).2
    hd (s.h.alloc { cls := c, msg := msg }).2
  rw [get_alloc_last] at this
  exact this

theorem raiseNew_isInst {σ : Type} (s : St σ) (c : Cls) (msg : String) (hd : Option ExcId)
    (n : String) :
    (s.raiseNew c msg hd).1.h.isInst (s.raiseNew c msg hd).2 n = c.contains n := by
  simp [Heap.isInst, (raiseNew_obj s c msg hd).2.2.2.2]

theorem isInst_lt {h : Heap} {e : ExcId} {n : String} (hi : h.isInst e n = true) : e < h.length := by
  rcases Nat.lt_or_ge e h.length with hl | hl
  · exact hl
  · exfalso
    simp [Heap.isInst, Heap.get, List.getD_eq_getElem?_getD, List.getElem?_eq_none hl] at hi
    change n ∈ ([] : List String) at hi
    simp at hi

theorem length_modify (h : Heap) (a : ExcId) (f : ExcObj → ExcObj) : (h.modify a f).length = h.length := by
  simp [Heap.modify]

theorem get_modify_self (h : Heap) (a : ExcId) (f : ExcObj → ExcObj) (ha : a < h.length) :
    (h.modify a f).get a = f (h.get a) := by
  simp [Heap.modify, Heap.get, List.getD_eq_getElem?_getD, List.getElem?_set_self ha]

theorem raiseCtx_context (h : Heap) (v x : ExcId) (hv : v < h.length) (hx : x ≠ v) :
    ((h.raiseCtx v (some x)).get v).context = some x := by
  simp only [Heap.raiseCtx, hx, if_false, Heap.setContext]
  rw [get_modify_self _ _ _ (by rw [length_breakCycle]; exact hv)]

end PyLean.CoreLibs.Misc.Contextlib
