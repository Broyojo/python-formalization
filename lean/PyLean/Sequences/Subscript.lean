import PyLean.Sequences.DequeOps

/-!
Subscripts with an int index: `s[i]`, `s[i] = v`, `del s[i]` agree across
`list` and `collections.deque` (up to the `IndexError` message), for every
Python int `i`.
-/

namespace PyLean.Sequences

open PyLean

set_option linter.unusedSectionVars false

variable {α : Type} [Inhabited α]

/-- Sequence indexing: `Py_ssize_t` conversion (`IndexError` beyond it), add
`len` to a negative index, then `0 <= j < len` or `IndexError(msg)`. -/
def seqGet (msg : String) (l : List α) (i : Int) : Py α := do
  let i ← subIndex i
  let j := if i < 0 then i + l.length else i
  if 0 ≤ j ∧ j < l.length then return ix l j else throw (.indexError msg)

/-- `s[i] = v` (`some v`) or `del s[i]` (`none`). -/
def seqAss (msg : String) (l : List α) (i : Int) (v : Option α) : Py (List α) := do
  let i ← subIndex i
  let j := if i < 0 then i + l.length else i
  if 0 ≤ j ∧ j < l.length then
    return (match v with | some v => l.set j.toNat v | none => l.eraseIdx j.toNat)
  else throw (.indexError msg)

/-- For every element type, list `l`, every int `i` (including far outside
`Py_ssize_t`) and value `v`: `l[i]`, `l[i] = v`, `del l[i]` and `d[i]`, `d[i] = v`,
`del d[i]` (any deque with items `l`, type invariant `WF`) behave as
`seqGet`/`seqAss` with their own message; the deque's block arithmetic (left or
right walk) reads and writes exactly item `i`, and the results keep the invariant
and `maxlen`. -/
def SubscriptAgree : Prop :=
  ∀ (α : Type) [Inhabited α] (l : List α) (i : Int),
    listGetItem l i = seqGet "list index out of range" l i ∧
    (∀ v, listAssItem l i v = seqAss "list assignment index out of range" l i v) ∧
    (∀ d : Deque α, d.WF → d.items = l →
      d.getitem i = seqGet "deque index out of range" l i ∧
      ∀ v, (d.setitem i v).map (·.items) = seqAss "deque index out of range" l i v ∧
        ∀ d', d.setitem i v = .ok d' → d'.WF ∧ d'.maxlen = d.maxlen)

theorem subscriptAgree_proven : SubscriptAgree := by
  intro α _ l i
  by_cases hs : ssizeMin ≤ i ∧ i ≤ ssizeMax
  · have hsub : subIndex i = .ok i := by unfold subIndex asSsizeExc; rw [iteT hs]
    generalize hj : (if i < 0 then i + l.length else i) = j
    refine ⟨?_, fun v => ?_, fun d hd hl => ?_⟩
    · simp only [listGetItem, seqGet, hsub, bind, Except.bind, hj, validIndex]
      by_cases hv : 0 ≤ j ∧ j < l.length
      · simp [hv]
      · simp [hv]; rfl
    · simp only [listAssItem, seqAss, hsub, bind, Except.bind, hj, validIndex]
      by_cases hv : 0 ≤ j ∧ j < l.length
      · simp only [hv, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
        cases v <;> rfl
      · simp [hv]; rfl
    · subst hl
      have hj' : (if i < 0 then i + d.size else i) = j := by rw [Deque.size_eq]; exact hj
      have hiC := Deque.itemC_spec d hd.1 j
      refine ⟨?_, fun v => ?_⟩
      · simp only [Deque.getitem, seqGet, hsub, bind, Except.bind]
        rw [hj', hj, hiC]
        by_cases hv : 0 ≤ j ∧ j < d.size
        · rw [iteT hv, iteT (by rw [Deque.size_eq] at hv; exact hv)]; rfl
        · rw [iteF hv, iteF (by rw [Deque.size_eq] at hv; exact hv)]; rfl
      · have haC := Deque.assItemC_spec d hd j v
        simp only [Deque.setitem, seqAss, hsub, bind, Except.bind]
        rw [hj', hj, haC]
        by_cases hv : 0 ≤ j ∧ j < d.size
        · rw [iteT hv, iteT (by rw [Deque.size_eq] at hv; exact hv)]
          cases v with
          | some v =>
            refine ⟨rfl, fun d' he => ?_⟩
            simp only [pure, Except.pure, Except.ok.injEq] at he
            subst he
            refine ⟨⟨?_, ?_⟩, rfl⟩
            · have := hd.1; rw [Deque.layout_iff] at this ⊢; simp only [List.length_set]; exact this
            · have := hd.2; rw [Deque.maxOk_iff] at this ⊢; simp only [List.length_set]; exact this
          | none =>
            obtain ⟨d', hdel, w', i', m'⟩ := Deque.delItem_spec d j hd hv.1 hv.2
            rw [hdel]
            refine ⟨by simp only [Except.map, i', pure, Except.pure], fun d'' he => ?_⟩
            simp only [Except.ok.injEq] at he; subst he; exact ⟨w', m'⟩
        · rw [iteF hv, iteF (by rw [Deque.size_eq] at hv; exact hv)]
          exact ⟨rfl, fun d' he => nomatch he⟩
  · have hsub : subIndex i = .error (.indexError "cannot fit 'int' into an index-sized integer") := by
      unfold subIndex asSsizeExc; rw [iteF hs]
    refine ⟨?_, fun v => ?_, fun d _ _ => ⟨?_, fun v => ⟨?_, fun d' he => ?_⟩⟩⟩ <;>
      simp only [listGetItem, listAssItem, Deque.getitem, Deque.setitem, seqGet,
        seqAss, hsub, bind, Except.bind, Except.map] at *
    exact nomatch he

end PyLean.Sequences
