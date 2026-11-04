import PyLean.Sequences.DequeIter

/-!
`deque.__reduce__`, `repr(deque)`, `deque.__sizeof__` and `deque_richcompare`, the last with
element comparisons that may raise or run any code on either deque.
-/

namespace PyLean.Sequences

open PyLean

set_option linter.unusedSectionVars false

variable {α : Type} [Inhabited α]

/-! ### `__reduce__` -/

theorem makeEmpty_absent (t : String) :
    Deque.makeEmpty t .absent = .ok ({ Deque.new t with maxlen := -1 } : Deque α) := by
  unfold Deque.makeEmpty Deque.initRe
  rfl

theorem makeEmpty_int (t : String) (m : Int) (h0 : 0 ≤ m) (h1 : m ≤ ssizeMax) :
    Deque.makeEmpty t (.int m) = .ok ({ Deque.new t with maxlen := m } : Deque α) := by
  unfold Deque.makeEmpty Deque.initRe
  simp only [asSsize]
  rw [iteT ⟨by unfold ssizeMin; unfold ssizeMax at h1; omega, h1⟩]
  simp only [iteF (show ¬ m < 0 by omega)]
  rfl

/-- `d.__reduce__()` (`deque___reduce___impl`, _collectionsmodule.c:1604-1628), for every
element type, every deque (type invariants `WF`, `maxlen` a `Py_ssize_t`) and every outcome
of `_PyObject_GetState(d)` (an overridden `__getstate__` may raise): a raising state makes
`__reduce__` raise it, before any iterator is made; otherwise the result is
`(type(d), args, state, it)` with `args` `()` for an unbounded deque and `((), maxlen)` for a
bounded one (the bound `d.maxlen` reports), and `it` yields exactly the deque's items. The
round trip pickle and `copy` perform holds: `type(d)(*args)` followed by `extend` with what
`it` yields gives a deque of the same type, items and `maxlen`. -/
def DequeReduce : Prop :=
  ∀ (α : Type) [Inhabited α] (σ : Type) (d : Deque α), d.WF → d.maxlen ≤ ssizeMax →
    (∀ e, d.reduceRe (σ := σ) (.error e) = .error e) ∧
    ∀ st : σ, ∃ it, d.reduceRe (.ok st) = .ok (d.tname, d.getMaxlen, st, it) ∧
      d.drain Deque.iterNext (d.items.length + 1) it = .ok d.items ∧
      ∃ e : Deque α, Deque.makeEmpty d.tname (match d.getMaxlen with | none => .absent | some m => .int m) = .ok e ∧
        (e.extend d.items).items = d.items ∧ (e.extend d.items).maxlen = d.maxlen ∧
        (e.extend d.items).tname = d.tname

theorem dequeReduce_proven : DequeReduce := by
  intro α _ σ d h hm
  refine ⟨fun e => rfl, fun st => ⟨d.iter, ?_, ?_, ?_⟩⟩
  · simp only [Deque.reduceRe, Deque.getMaxlen]
    by_cases hc : d.maxlen < 0 <;> simp [hc]
  · have := Deque.fwd_drain d h.1 d.items.length d.iter 0 0 (Deque.fwd_init d h.1) (by omega)
    rw [Nat.zero_add] at this; exact this
  · have hk := maxOk_le d h
    rcases Deque.maxlen_cases d h with hl | hl | hl
    · have hg : d.getMaxlen = none := by unfold Deque.getMaxlen; rw [iteT (by omega)]
      rw [hg]
      refine ⟨_, makeEmpty_absent d.tname, ?_⟩
      obtain ⟨_, i, m⟩ := Deque.extend_spec ({ Deque.new d.tname with maxlen := -1 } : Deque α) d.items
        (new_wf d.tname (-1) (Or.inl rfl))
      refine ⟨by rw [i]; rfl, by rw [m, hl], by rw [extend_tname]; rfl⟩
    · have hg : d.getMaxlen = some d.maxlen := by unfold Deque.getMaxlen; rw [iteF (by omega)]
      rw [hg]
      refine ⟨_, makeEmpty_int d.tname d.maxlen (by omega) hm, ?_⟩
      obtain ⟨_, i, m⟩ := Deque.extend_spec ({ Deque.new d.tname with maxlen := d.maxlen } : Deque α) d.items
        (new_wf d.tname d.maxlen (Or.inr (by omega)))
      refine ⟨?_, by rw [m], by rw [extend_tname]; rfl⟩
      rw [i]; show keepLast d.maxlen ([] ++ d.items) = d.items
      rw [List.nil_append, keepLast_of_le _ _ hk]
    · have hg : d.getMaxlen = some d.maxlen := by unfold Deque.getMaxlen; rw [iteF (by omega)]
      rw [hg]
      refine ⟨_, makeEmpty_int d.tname d.maxlen (by omega) hm, ?_⟩
      obtain ⟨_, i, m⟩ := Deque.extend_spec ({ Deque.new d.tname with maxlen := d.maxlen } : Deque α) d.items
        (new_wf d.tname d.maxlen (Or.inr (by omega)))
      refine ⟨?_, by rw [m], by rw [extend_tname]; rfl⟩
      rw [i]; show keepLast d.maxlen ([] ++ d.items) = d.items
      rw [List.nil_append, keepLast_of_le _ _ hk]

/-! ### `repr` -/

/-- The item `repr` calls of `list_repr` over `xs`, from deque `d`, all returning: they
return `ss` in order and leave the deque `d'`. -/
inductive ReprRun (r : Deque α → α → Py String × Deque α) : List α → Deque α → List String → Deque α → Prop
  | nil (d : Deque α) : ReprRun r [] d [] d
  | cons (x : α) (xs : List α) (d d1 d2 : Deque α) (s : String) (ss : List String) :
      r d x = (.ok s, d1) → ReprRun r xs d1 ss d2 → ReprRun r (x :: xs) d (s :: ss) d2

/-- The calls return until one raises `e`, leaving the deque `d'`. -/
inductive ReprFail (r : Deque α → α → Py String × Deque α) : List α → Deque α → PyExc → Deque α → Prop
  | here (x : α) (xs : List α) (d d1 : Deque α) (e : PyExc) :
      r d x = (.error e, d1) → ReprFail r (x :: xs) d e d1
  | later (x : α) (xs : List α) (d d1 d2 : Deque α) (s : String) (e : PyExc) :
      r d x = (.ok s, d1) → ReprFail r xs d1 e d2 → ReprFail r (x :: xs) d e d2

theorem listReprRe_run (r : Deque α → α → Py String × Deque α) {xs : List α} {d : Deque α}
    {ss : List String} {d' : Deque α} (h : ReprRun r xs d ss d') :
    ∀ acc, Deque.listReprRe r xs acc d = (.ok ("[" ++ ", ".intercalate (acc.reverse ++ ss) ++ "]"), d') := by
  induction h with
  | nil d => intro acc; simp only [Deque.listReprRe, List.append_nil]
  | cons x xs d d1 d2 s ss hx _ ih =>
    intro acc
    simp only [Deque.listReprRe, hx]
    rw [ih (s :: acc)]
    simp

theorem listReprRe_fail (r : Deque α → α → Py String × Deque α) {xs : List α} {d : Deque α}
    {e : PyExc} {d' : Deque α} (h : ReprFail r xs d e d') :
    ∀ acc, Deque.listReprRe r xs acc d = (.error e, d') := by
  induction h with
  | here x xs d d1 e hx => intro acc; simp only [Deque.listReprRe, hx]
  | later x xs d d1 d2 s e hx _ ih => intro acc; simp only [Deque.listReprRe, hx]; exact ih _

/-- `repr(d)` (`deque_repr`, _collectionsmodule.c:1633-1661), for every element type, every
deque, every element `repr` (which may raise and may run any code on the deque: clear it,
re-initialise it with another `maxlen`, ...) and every outcome of `Py_ReprEnter(d)`: an
error is returned as is; a deque already being printed gives `'[...]'`; otherwise the item
reprs run on the snapshot `list(d)` from left to right, and when they all return
`s_0, ..., s_{n-1}` the result is `T([s_0, ..., s_{n-1}])` or
`T([s_0, ..., s_{n-1}], maxlen=m)` with the type name `T` and the bound `m` the deque had
before any item repr ran, whatever they did to it; the first item repr that raises makes
`repr(d)` raise its exception. -/
def DequeRepr : Prop :=
  ∀ (α : Type) [Inhabited α] (d : Deque α) (r : Deque α → α → Py String × Deque α),
    (∀ e, d.reprRe r (.error e) = (.error e, d)) ∧
    d.reprRe r (.ok true) = (.ok "[...]", d) ∧
    (∀ (ss : List String) (d' : Deque α), ReprRun r d.items d ss d' →
      d.reprRe r (.ok false) =
        (.ok (if d.maxlen ≥ 0 then s!"{d.tname}({"[" ++ ", ".intercalate ss ++ "]"}, maxlen={d.maxlen})"
          else s!"{d.tname}({"[" ++ ", ".intercalate ss ++ "]"})"), d')) ∧
    (∀ (e : PyExc) (d' : Deque α), ReprFail r d.items d e d' → d.reprRe r (.ok false) = (.error e, d'))

theorem dequeRepr_proven : DequeRepr := by
  intro α _ d r
  refine ⟨fun e => rfl, rfl, fun ss d' hr => ?_, fun e d' hf => ?_⟩
  · have := listReprRe_run r hr []
    simp only [List.reverse_nil, List.nil_append] at this
    unfold Deque.reprRe
    simp only [this]
    split <;> rfl
  · have := listReprRe_fail r hf []
    unfold Deque.reprRe
    simp only [this]

/-! ### `__sizeof__` -/

/-- `d.__sizeof__()` (`deque___sizeof___impl`, _collectionsmodule.c:1790-1800), for every
deque (type invariant `WF`) and every basic size of its type: the size is the basic size
plus 528 bytes (`sizeof(block)` on LP64) per block from `leftblock` to `rightblock`
inclusive, i.e. `rbNum + 1` blocks, at least one; the `assert` at :1795-1796
(`leftindex + len - 1 == (blocks - 1) * BLOCKLEN + rightindex`) holds; every item lies in
one of the counted blocks, and the last item in the last one. -/
def DequeSizeof : Prop :=
  ∀ (α : Type) [Inhabited α] (d : Deque α), d.WF → ∀ basicsize : Int,
    d.sizeof basicsize = basicsize + 528 * (d.rbNum + 1) ∧ 1 ≤ d.blocks ∧
    d.left + d.size - 1 = (d.blocks - 1) * 64 + d.right ∧
    (∀ k : Nat, k < d.items.length → (d.left + k) / 64 < d.blocks) ∧
    (d.items ≠ [] → (d.left + d.size - 1) / 64 = d.blocks - 1)

theorem dequeSizeof_proven : DequeSizeof := by
  intro α _ d h bs
  have h' := h.1
  rw [Deque.layout_iff] at h'
  have hb : d.blocks = d.rbNum + 1 := by
    unfold Deque.blocks Deque.rbNum; rw [Deque.size_eq]
    rcases Nat.eq_zero_or_pos d.items.length with h0 | h0
    · have := h'.2.2.2.2.2 (by omega); omega
    · omega
  refine ⟨?_, ?_, ?_, fun k hk => ?_, fun hne => ?_⟩
  · unfold Deque.sizeof; rw [hb]; omega
  · rw [hb]; unfold Deque.rbNum; rw [Deque.size_eq]
    rcases Nat.eq_zero_or_pos d.items.length with h0 | h0
    · have := h'.2.2.2.2.2 (by omega); omega
    · omega
  · rw [hb]; unfold Deque.rbNum; rw [Deque.size_eq]
    rcases Nat.eq_zero_or_pos d.items.length with h0 | h0
    · have := h'.2.2.2.2.2 (by omega); omega
    · omega
  · rw [hb]; unfold Deque.rbNum; rw [Deque.size_eq]; omega
  · have h0 : 0 < d.items.length := List.length_pos_iff.mpr hne
    rw [hb]; unfold Deque.rbNum; omega

/-! ### Rich comparison -/

namespace Deque

variable {S : Type}

theorem fwd_next_ok (d : Deque α) (h : d.Layout) (it : Iter) (p : Nat) (hf : FwdAt d it p) :
    ∃ x it', iterNext d it = (.ok x, it') := by
  by_cases hp : p < d.items.length
  · obtain ⟨it', e, _⟩ := fwd_step d h it p hf hp
    exact ⟨_, _, e⟩
  · have hpl : p = d.items.length := by have := hf.2.2.1; omega
    exact ⟨_, _, fwd_end d it (by rw [← hpl]; exact hf)⟩

theorem richLoop_skip (gv gw : S → Deque α) (eq rich : RCmp S α) (op : CmpOp) (s : S)
    (hv : (gv s).Layout) (hw : (gw s).Layout) :
    ∀ (k n p : Nat) (it1 it2 : Iter), FwdAt (gv s) it1 p → FwdAt (gw s) it2 p →
    p + k ≤ (gv s).items.length → p + k ≤ (gw s).items.length →
    (∀ q : Nat, p ≤ q → q < p + k → eq s (ix (gv s).items q) (ix (gw s).items q) = (.ok true, s)) →
    ∃ it1' it2', FwdAt (gv s) it1' (p + k) ∧ FwdAt (gw s) it2' (p + k) ∧
      richLoopRe gv gw eq rich op (k + n) it1 it2 s = richLoopRe gv gw eq rich op n it1' it2' s
  | 0, n, p, it1, it2, h1, h2, _, _, _ => ⟨it1, it2, h1, h2, by rw [Nat.zero_add]⟩
  | k + 1, n, p, it1, it2, h1, h2, l1, l2, hq => by
    obtain ⟨a1, b1, c1⟩ := fwd_step (gv s) hv it1 p h1 (by omega)
    obtain ⟨a2, b2, c2⟩ := fwd_step (gw s) hw it2 p h2 (by omega)
    have he := hq p (Nat.le_refl _) (by omega)
    obtain ⟨it1', it2', d1, d2, e⟩ := richLoop_skip gv gw eq rich op s hv hw k n (p + 1) a1 a2 c1 c2
      (by omega) (by omega) (fun q hq1 hq2 => hq q (by omega) (by omega))
    refine ⟨it1', it2', by rw [show p + (k + 1) = p + 1 + k by omega]; exact d1,
      by rw [show p + (k + 1) = p + 1 + k by omega]; exact d2, ?_⟩
    rw [show k + 1 + n = (k + n) + 1 by omega, richLoopRe.eq_2]
    simp only [b1, b2, he]
    exact e

theorem richLoop_at (gv gw : S → Deque α) (eq rich : RCmp S α) (op : CmpOp) (s : S)
    (hv : (gv s).Layout) (hw : (gw s).Layout) (k n : Nat) (it1 it2 : Iter)
    (h1 : FwdAt (gv s) it1 k) (h2 : FwdAt (gw s) it2 k) (l1 : k < (gv s).items.length)
    (l2 : k < (gw s).items.length) :
    ∃ it1' it2', FwdAt (gv s) it1' (k + 1) ∧ FwdAt (gw s) it2' (k + 1) ∧
      richLoopRe gv gw eq rich op (n + 1) it1 it2 s =
        match eq s (ix (gv s).items k) (ix (gw s).items k) with
        | (.error e, s') => (.error e, s')
        | (.ok false, s') => rich s' (ix (gv s).items k) (ix (gw s).items k)
        | (.ok true, s') => richLoopRe gv gw eq rich op n it1' it2' s' := by
  obtain ⟨a1, b1, c1⟩ := fwd_step (gv s) hv it1 k h1 l1
  obtain ⟨a2, b2, c2⟩ := fwd_step (gw s) hw it2 k h2 l2
  refine ⟨a1, a2, c1, c2, ?_⟩
  rw [richLoopRe.eq_2]
  simp only [b1, b2]
  rfl

theorem richLoop_end (gv gw : S → Deque α) (eq rich : RCmp S α) (op : CmpOp) (s : S)
    (hv : (gv s).Layout) (hw : (gw s).Layout) (k n : Nat) (it1 it2 : Iter)
    (h1 : FwdAt (gv s) it1 k) (h2 : FwdAt (gw s) it2 k)
    (hk : k = (gv s).items.length ∨ k = (gw s).items.length) :
    richLoopRe gv gw eq rich op (n + 1) it1 it2 s =
      (.ok (endCmp op (decide (k < (gv s).items.length)) (decide (k < (gw s).items.length))), s) := by
  have k1 := h1.2.2.1
  have k2 := h2.2.2.1
  rw [richLoopRe.eq_2]
  by_cases c1 : k < (gv s).items.length
  · have c2 : ¬ k < (gw s).items.length := by omega
    obtain ⟨a1, b1, _⟩ := fwd_step (gv s) hv it1 k h1 c1
    have b2 := fwd_end (gw s) it2 (by rw [show (gw s).items.length = k by omega]; exact h2)
    simp only [b1, b2, c1, c2, decide_true, decide_false, Option.isSome_some, Option.isSome_none]
  · have e1 := fwd_end (gv s) it1 (by rw [show (gv s).items.length = k by omega]; exact h1)
    by_cases c2 : k < (gw s).items.length
    · obtain ⟨a2, b2, _⟩ := fwd_step (gw s) hw it2 k h2 c2
      simp only [e1, b2, c1, c2, decide_true, decide_false, Option.isSome_some, Option.isSome_none]
    · have e2 := fwd_end (gw s) it2 (by rw [show (gw s).items.length = k by omega]; exact h2)
      simp only [e1, e2, c1, c2, decide_false, Option.isSome_none]

theorem richLoop_mutV (gv gw : S → Deque α) (eq rich : RCmp S α) (op : CmpOp) (n : Nat) (it1 it2 : Iter)
    (s' : S) (hs : (gv s').state ≠ it1.state) :
    richLoopRe gv gw eq rich op (n + 1) it1 it2 s' = (.error mutatedErr, s') := by
  have : iterNext (gv s') it1 = (.error mutatedErr, { it1 with counter := 0 }) := by
    unfold iterNext; rw [iteT hs]
  rw [richLoopRe.eq_2]
  simp only [this]

theorem richLoop_mutW (gv gw : S → Deque α) (eq rich : RCmp S α) (op : CmpOp) (n : Nat) (it1 it2 : Iter)
    (s' : S) (hx : ∃ x it', iterNext (gv s') it1 = (.ok x, it')) (hs : (gw s').state ≠ it2.state) :
    richLoopRe gv gw eq rich op (n + 1) it1 it2 s' = (.error mutatedErr, s') := by
  obtain ⟨x, it', hx⟩ := hx
  have : iterNext (gw s') it2 = (.error mutatedErr, { it2 with counter := 0 }) := by
    unfold iterNext; rw [iteT hs]
  rw [richLoopRe.eq_2]
  simp only [hx, this]

end Deque

/-- `deque_richcompare(v, w, op)` (_collectionsmodule.c:1664-1740) for every element type,
every world `S` holding the two deques `v = gv s`, `w = gw s` (type invariant `WF`; `same`
says `v is w`), every `op` and every element comparison `eq` (`Py_EQ`) and `rich` (`op`):
callbacks that may raise and may run any code on either deque. Scope: the deques' own
iterators (a subclass overriding `__iter__` is out of scope). The shortcuts: `v is w` gives
`True` for `==` and `False` for `!=`, different lengths give `False` / `True`, before any
element is compared. Otherwise, for every position `k` up to both lengths such that the
`==` comparisons before `k` returned true and left both deques alone: when both have an
item `k`, a raising `==` on that pair makes the compare raise it; one returning false makes
the result `rich(v[k], w[k])`'s, whatever it did to the deques; one returning true after
moving `v`'s mutation counter, or after moving `w`'s with `v` untouched, raises
`RuntimeError('deque mutated during iteration')` (the iterators' state check, :1973-1978);
when one deque ends at `k`, the result is the `switch` at :1724-1731 on which one goes on. -/
def DequeCompareRe : Prop :=
  ∀ (α : Type) [Inhabited α] (S : Type) (gv gw : S → Deque α) (eq rich : Deque.RCmp S α) (op : CmpOp)
    (same : Bool) (s : S), (gv s).WF → (gw s).WF →
    (op = .eq → same = true → Deque.richcompareRe gv gw eq rich op same s = (.ok true, s)) ∧
    (op = .eq → same = false → (gv s).size ≠ (gw s).size →
      Deque.richcompareRe gv gw eq rich op same s = (.ok false, s)) ∧
    (op = .ne → same = true → Deque.richcompareRe gv gw eq rich op same s = (.ok false, s)) ∧
    (op = .ne → same = false → (gv s).size ≠ (gw s).size →
      Deque.richcompareRe gv gw eq rich op same s = (.ok true, s)) ∧
    (((op ≠ .eq ∧ op ≠ .ne) ∨ (same = false ∧ (gv s).size = (gw s).size)) →
      ∀ k : Nat, k ≤ (gv s).items.length → k ≤ (gw s).items.length →
      (∀ q : Nat, q < k → eq s (ix (gv s).items q) (ix (gw s).items q) = (.ok true, s)) →
      (k < (gv s).items.length → k < (gw s).items.length →
        (∀ e s', eq s (ix (gv s).items k) (ix (gw s).items k) = (.error e, s') →
          Deque.richcompareRe gv gw eq rich op same s = (.error e, s')) ∧
        (∀ s', eq s (ix (gv s).items k) (ix (gw s).items k) = (.ok false, s') →
          Deque.richcompareRe gv gw eq rich op same s = rich s' (ix (gv s).items k) (ix (gw s).items k)) ∧
        (∀ s', eq s (ix (gv s).items k) (ix (gw s).items k) = (.ok true, s') → (gv s').state ≠ (gv s).state →
          Deque.richcompareRe gv gw eq rich op same s = (.error Deque.mutatedErr, s')) ∧
        (∀ s', eq s (ix (gv s).items k) (ix (gw s).items k) = (.ok true, s') → gv s' = gv s →
          (gw s').state ≠ (gw s).state →
          Deque.richcompareRe gv gw eq rich op same s = (.error Deque.mutatedErr, s'))) ∧
      ((k = (gv s).items.length ∨ k = (gw s).items.length) →
        Deque.richcompareRe gv gw eq rich op same s =
          (.ok (Deque.endCmp op (decide (k < (gv s).items.length)) (decide (k < (gw s).items.length))), s)))

theorem richcompareRe_loop {S : Type} (gv gw : S → Deque α) (eq rich : Deque.RCmp S α) (op : CmpOp)
    (same : Bool) (s : S) (h : ((op ≠ .eq ∧ op ≠ .ne) ∨ (same = false ∧ (gv s).size = (gw s).size))) :
    Deque.richcompareRe gv gw eq rich op same s =
      Deque.richLoopRe gv gw eq rich op ((gv s).items.length + 1) (gv s).iter (gw s).iter s := by
  unfold Deque.richcompareRe
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp only [h1, h2, false_and, ite_false]
  · simp only [h1, h2, Bool.false_eq_true, and_false, ne_eq, not_true_eq_false, ite_false]

theorem dequeCompareRe_proven : DequeCompareRe := by
  intro α _ S gv gw eq rich op same s hv hw
  refine ⟨fun h1 h2 => ?_, fun h1 h2 h3 => ?_, fun h1 h2 => ?_, fun h1 h2 h3 => ?_, fun hloop k k1 k2 hq => ?_⟩
  · subst h1 h2; unfold Deque.richcompareRe; simp
  · subst h1 h2; unfold Deque.richcompareRe; simp [h3]
  · subst h1 h2; unfold Deque.richcompareRe; simp
  · subst h1 h2; unfold Deque.richcompareRe; simp [h3]
  rw [richcompareRe_loop gv gw eq rich op same s hloop]
  obtain ⟨it1, it2, f1, f2, e⟩ := Deque.richLoop_skip gv gw eq rich op s hv.1 hw.1 k
    ((gv s).items.length - k + 1) 0 (gv s).iter (gw s).iter (Deque.fwd_init _ hv.1) (Deque.fwd_init _ hw.1)
    (by omega) (by omega) (fun q _ hq2 => hq q (by omega))
  rw [Nat.zero_add] at f1 f2
  rw [show (gv s).items.length + 1 = k + ((gv s).items.length - k + 1) by omega, e]
  refine ⟨fun l1 l2 => ?_, fun hk => ?_⟩
  · obtain ⟨a1, a2, c1, c2, e2⟩ := Deque.richLoop_at gv gw eq rich op s hv.1 hw.1 k ((gv s).items.length - k)
      it1 it2 f1 f2 l1 l2
    rw [show (gv s).items.length - k + 1 = ((gv s).items.length - k) + 1 by omega, e2]
    refine ⟨fun e' s' he => by rw [he], fun s' he => by rw [he], fun s' he hst => ?_, fun s' he hvs hst => ?_⟩
    · rw [he]
      simp only
      rw [show (gv s).items.length - k = ((gv s).items.length - k - 1) + 1 by omega]
      exact Deque.richLoop_mutV gv gw eq rich op _ a1 a2 s' (by rw [c1.1]; exact hst)
    · rw [he]
      simp only
      rw [show (gv s).items.length - k = ((gv s).items.length - k - 1) + 1 by omega]
      refine Deque.richLoop_mutW gv gw eq rich op _ a1 a2 s' ?_ (by rw [c2.1]; exact hst)
      rw [hvs]; exact Deque.fwd_next_ok _ hv.1 a1 (k + 1) c1
  · exact Deque.richLoop_end gv gw eq rich op s hv.1 hw.1 k _ it1 it2 f1 f2 hk

/-- Lexicographic comparison of two sequences by first difference (Doc/library/stdtypes.rst,
"Comparisons": sequences of the same type compare lexicographically): the first pair whose
`==` is false decides through `op`, a raising `==` raises, and when one sequence runs out the
lengths decide. -/
def seqCmp (eq rich : α → α → Py Bool) (op : CmpOp) : List α → List α → Py Bool
  | [], ys => .ok (Deque.endCmp op false (!ys.isEmpty))
  | _ :: _, [] => .ok (Deque.endCmp op true false)
  | x :: xs, y :: ys =>
    match eq x y with
    | .error e => .error e
    | .ok false => rich x y
    | .ok true => seqCmp eq rich op xs ys

/-- `deque_richcompare` with element comparisons that do not touch the deques, for every
element type, every pair of deques (type invariant `WF`; `v is w` allowed through `same`)
and every `op` the shortcuts do not decide: the result is the lexicographic comparison of
`list(v)` and `list(w)`, so the block walks of both iterators read the items in order. -/
def DequeCompareSeq : Prop :=
  ∀ (α : Type) [Inhabited α] (S : Type) (gv gw : S → Deque α) (eq rich : α → α → Py Bool) (op : CmpOp)
    (same : Bool) (s : S), (gv s).WF → (gw s).WF →
    ((op ≠ .eq ∧ op ≠ .ne) ∨ (same = false ∧ (gv s).size = (gw s).size)) →
    Deque.richcompareRe gv gw (fun s x y => (eq x y, s)) (fun s x y => (rich x y, s)) op same s =
      (seqCmp eq rich op (gv s).items (gw s).items, s)

theorem richLoop_pure {S : Type} (gv gw : S → Deque α) (eq rich : α → α → Py Bool) (op : CmpOp) (s : S)
    (hv : (gv s).Layout) (hw : (gw s).Layout) :
    ∀ (k p n : Nat) (it1 it2 : Deque.Iter), Deque.FwdAt (gv s) it1 p → Deque.FwdAt (gw s) it2 p →
    p + k = min (gv s).items.length (gw s).items.length →
    Deque.richLoopRe gv gw (fun s x y => (eq x y, s)) (fun s x y => (rich x y, s)) op (n + k + 1) it1 it2 s =
      (seqCmp eq rich op ((gv s).items.drop p) ((gw s).items.drop p), s)
  | 0, p, n, it1, it2, h1, h2, hk => by
    rw [Nat.add_zero, Deque.richLoop_end gv gw _ _ op s hv hw p n it1 it2 h1 h2 (by omega)]
    by_cases c1 : p < (gv s).items.length
    · have c2 : ¬ p < (gw s).items.length := by omega
      rw [List.drop_eq_nil_of_le (as := (gw s).items) (by omega), ← ix_drop _ _ c1]
      simp only [seqCmp, c1, c2, decide_true, decide_false]
    · rw [List.drop_eq_nil_of_le (as := (gv s).items) (by omega)]
      by_cases c2 : p < (gw s).items.length
      · rw [← ix_drop _ _ c2]
        simp only [seqCmp, c1, c2, decide_true, decide_false, List.isEmpty_cons, Bool.not_false]
      · rw [List.drop_eq_nil_of_le (as := (gw s).items) (by omega)]
        simp only [seqCmp, c1, c2, decide_false, List.isEmpty_nil, Bool.not_true]
  | k + 1, p, n, it1, it2, h1, h2, hk => by
    obtain ⟨a1, a2, c1, c2, e⟩ := Deque.richLoop_at gv gw (fun s x y => (eq x y, s)) (fun s x y => (rich x y, s))
      op s hv hw p (n + k + 1) it1 it2 h1 h2 (by omega) (by omega)
    rw [show n + (k + 1) + 1 = (n + k + 1) + 1 by omega, e, ← ix_drop _ _ (show p < (gv s).items.length by omega),
      ← ix_drop _ _ (show p < (gw s).items.length by omega)]
    simp only [seqCmp]
    cases hq : eq (ix (gv s).items p) (ix (gw s).items p) with
    | error e => rfl
    | ok b =>
      cases b with
      | false => rfl
      | true => exact richLoop_pure gv gw eq rich op s hv hw k (p + 1) n a1 a2 c1 c2 (by omega)

theorem dequeCompareSeq_proven : DequeCompareSeq := by
  intro α _ S gv gw eq rich op same s hv hw hloop
  rw [richcompareRe_loop gv gw _ _ op same s hloop]
  have := richLoop_pure gv gw eq rich op s hv.1 hw.1 (min (gv s).items.length (gw s).items.length) 0
    ((gv s).items.length - min (gv s).items.length (gw s).items.length) (gv s).iter (gw s).iter
    (Deque.fwd_init _ hv.1) (Deque.fwd_init _ hw.1) (by omega)
  rw [show (gv s).items.length - min (gv s).items.length (gw s).items.length +
    min (gv s).items.length (gw s).items.length + 1 = (gv s).items.length + 1 by omega] at this
  rw [this]
  simp

end PyLean.Sequences
