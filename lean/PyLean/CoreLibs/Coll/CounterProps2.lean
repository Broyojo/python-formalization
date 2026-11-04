import PyLean.CoreLibs.Coll.CounterProps

/-!
Properties of the generic `Counter` model, continued: `most_common`, `__delitem__`, `copy`,
`__reduce__`, the unary operators, `elements` and the rich comparisons.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace PyLean.CoreLibs.Coll

open PyLean
open PyLean.Accel.Heapq (Eff SEnv Sorter HO hEnv nSelect pySortedBy pureKey builtinHier Hier isA SortOk
  kOf sorted_honest NSelectIsSortedPrefix nSelectIsSortedPrefix_proven LenTrue)

variable {κ ν : Type} [DecidableEq κ]

/-! ### Monad and dict helpers -/

@[simp] theorem ok_bind {α β : Type} (a : α) (f : α → Py β) : (Except.ok a >>= f : Py β) = f a := rfl
@[simp] theorem error_bind {α β : Type} (e : PyExc) (f : α → Py β) : (Except.error e >>= f : Py β) = .error e := rfl
@[simp] theorem pure_py {α : Type} (a : α) : (pure a : Py α) = .ok a := rfl
theorem bind_ok_right {α : Type} (x : Py α) : (x >>= fun r => Except.ok r) = x := by cases x <;> rfl

theorem del_of_notMem {d : D κ ν} {x : κ} (h : x ∉ D.keys d) : D.del d x = d := by
  induction d with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    simp only [D.keys_cons, List.mem_cons, not_or] at h
    have : a ≠ x := fun e => h.1 e.symm
    simp [D.del, this, ih h.2]

theorem hash_of_mem {K : KOps κ} {d : D κ ν} (h : HashOk K d) {p : κ × ν} (hp : p ∈ d) : K.hash p.1 = .ok () :=
  h p.1 (D.mem_keys_of_mem hp)

theorem loopInto_congr (K : KOps κ) {f g : κ → ν → Py (Option ν)} :
    ∀ (l r : D κ ν), (∀ p ∈ l, f p.1 p.2 = g p.1 p.2) → loopInto K f r l = loopInto K g r l
  | [], _, _ => rfl
  | (e, c) :: t, r, h => by
    have ih := fun r' => loopInto_congr K t r' (fun p hp => h p (by simp [hp]))
    simp only [loopInto, h (e, c) (by simp), ih]

/-- A loop whose body never raises appends the stored items. -/
theorem loopInto_pure (K : KOps κ) {f : κ → ν → Py (Option ν)} {F : κ → ν → Option ν} :
    ∀ (l r : D κ ν), D.WF l → HashOk K l → (∀ p ∈ l, (F p.1 p.2).isSome → p.1 ∉ D.keys r) →
      (∀ p ∈ l, f p.1 p.2 = .ok (F p.1 p.2)) →
      loopInto K f r l = .ok (r ++ l.filterMap (fun p => (F p.1 p.2).map (fun v => (p.1, v))))
  | [], r, _, _, _, _ => by simp [loopInto]
  | (e, c) :: t, r, hw, hh, hf, hF => by
    have he : K.hash e = .ok () := hh e (by simp [D.keys])
    have hn := D.notMem_of_cons hw
    have hht : HashOk K t := fun k hk => hh k (by simp [D.keys] at hk ⊢; exact Or.inr hk)
    simp only [loopInto, hF (e, c) (by simp), ok_bind]
    cases hFe : F e c with
    | none =>
      simp only [pure_py, ok_bind]
      rw [loopInto_pure K t r (D.WF_of_cons hw) hht (fun p hp => hf p (by simp [hp]))
        (fun p hp => hF p (by simp [hp]))]
      simp [hFe]
    | some v =>
      have hfe : e ∉ D.keys r := hf (e, c) (by simp) (by simp [hFe])
      simp only [dSet_ok r v he, ok_bind]
      rw [D.set_of_notMem v hfe]
      rw [loopInto_pure K t (r ++ [(e, v)]) (D.WF_of_cons hw) hht ?_ (fun p hp => hF p (by simp [hp]))]
      · simp [hFe]
      · intro p hp hs
        simp only [D.keys_append, D.keys_cons, D.keys_nil, List.mem_append, List.mem_singleton, not_or]
        refine ⟨hf p (by simp [hp]) hs, ?_⟩
        intro hpe
        have hm := D.mem_keys_of_mem hp
        rw [hpe] at hm
        exact hn hm

theorem allM_pure {α : Type} {p : α → Py Bool} {P : α → Bool} :
    ∀ (l : List α), (∀ x ∈ l, p x = .ok (P x)) → allM p l = .ok (decide (∀ x ∈ l, P x = true))
  | [], _ => by simp [allM]
  | x :: xs, h => by
    simp only [allM, h x (by simp), ok_bind]
    rw [allM_pure xs (fun y hy => h y (by simp [hy]))]
    cases hx : P x <;> simp [hx]

theorem allM_raises {α : Type} {p : α → Py Bool} :
    ∀ (l : List α), (∀ x ∈ l, p x ≠ .ok false) → (∃ x ∈ l, ∃ y, p x = .error y) → ∃ y, allM p l = .error y
  | [], _, ⟨x, hx, _⟩ => by simp at hx
  | x :: xs, h, ⟨z, hz, y, hy⟩ => by
    simp only [allM]
    cases hpx : p x with
    | error e => exact ⟨e, rfl⟩
    | ok b =>
      cases b
      · exact absurd hpx (h x (by simp))
      · simp only [ok_bind, ite_true]
        rcases List.mem_cons.1 hz with rfl | hz
        · rw [hpx] at hy; cases hy
        · exact allM_raises xs (fun w hw => h w (by simp [hw])) ⟨z, hz, y, hy⟩

/-! ### `most_common` -/

theorem mcEnv_honest [DecidableEq ν] [Inhabited ν] (N : Num ν) (r : ν → ν → Bool)
    (hlt : N.lt = fun x y => .ok (r x y)) (hgt : N.gt = fun x y => .ok (r y x))
    (heq : N.eq = fun x y => .ok (!r x y && !r y x)) (xs : List (MObj κ ν)) :
    mcEnv N xs = hEnv xs (fun a b => r a.2 b.2) (.ok xs.length) := by
  obtain ⟨z, o, ad, sb, ia, is, ab, lt, gt, le, ge, eq, tr, ix⟩ := N
  simp only at hlt hgt heq
  subst hlt hgt heq
  rfl

theorem unObj_itemObjs (d : D κ ν) : unObj (itemObjs d) = d := by
  induction d with
  | nil => rfl
  | cons p t ih => show p :: unObj (itemObjs t) = p :: t; rw [ih]

theorem itemObjs_mergeSort (d : D κ ν) (r : ν → ν → Bool) :
    (itemObjs d).mergeSort (fun a b => !r a.2 b.2) = itemObjs (d.mergeSort (fun a b => !r a.2 b.2)) := by
  unfold itemObjs
  exact (List.map_mergeSort (l := d) (r := fun (a b : κ × ν) => !r a.2 b.2)
    (s := fun (a b : MObj κ ν) => !r a.2 b.2)
    (f := fun (p : κ × ν) => ((some p.1 : Option κ), p.2)) (fun _ _ _ _ => rfl)).symm

/-- **`most_common` is the stable descending sort, cut at `n`.** For every key type, every
count type whose `<` is a strict weak order `r` with `>` its converse and `==` "neither is
`<`" (and the truth tests of their results never raise), and every `list.sort` that is a
correct stable sort: `most_common()` (`n=None`, `sorted(..., reverse=True)`) is the items in
non-increasing order of count with equal counts in insertion order, and `most_common(n)` for
`n >= 0` (`heapq.nlargest`, through its `n == 1`, `n >= len` and heap paths) is its first `n`
items, ties included.

Source: docstring, Lib/collections/__init__.py:629-630, and Doc/library/collections.rst
("Elements with equal counts are ordered in the order first encountered"). The hypotheses are
the language reference's rules for a total order (Doc/reference/expressions.rst); counts that
break them are the `TypeError` case of `__repr__`. -/
def MostCommonSorted : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] [DecidableEq ν] [Inhabited ν] (N : Num ν) (r : ν → ν → Bool)
    (So : Sorter Nat) (d : D κ ν), Accel.StrictWeak r → SortOk So →
    N.lt = (fun x y => .ok (r x y)) → N.gt = (fun x y => .ok (r y x)) →
    N.eq = (fun x y => .ok (!r x y && !r y x)) →
    mostCommon N So d none = .ok (d.mergeSort (fun a b => !r a.2 b.2)) ∧
    ∀ n : Int, 0 ≤ n → mostCommon N So d (some n) = .ok ((d.mergeSort (fun a b => !r a.2 b.2)).take n.toNat)

theorem mostCommonSorted_proven : MostCommonSorted := by
  intro κ ν _ _ _ N r So d hr hSo hlt hgt heq
  have hE := mcEnv_honest N r hlt hgt heq (itemObjs d)
  have hr' := Accel.Heapq.StrictWeak.pullback hr (Prod.snd : MObj κ ν → ν)
  refine ⟨?_, fun n hn => ?_⟩
  · have hs : ((pySortedBy (hEnv (itemObjs d) (fun a b => r a.2 b.2) (.ok (itemObjs d).length)) So
        (some (pureKey getCount)) true .src).run 0).1 =
        .ok ((itemObjs d).mergeSort (fun a b => !r a.2 b.2)) :=
      sorted_honest (itemObjs d) (fun a b => r a.2 b.2) (.ok (itemObjs d).length) hr' So hSo (some getCount) true 0
    show Except.map unObj ((pySortedBy (mcEnv N (itemObjs d)) So (some (pureKey getCount)) true .src).run 0).1 = _
    rw [hE, hs, itemObjs_mergeSort]
    exact congrArg Except.ok (unObj_itemObjs _)
  · have hs : ((nSelect (hEnv (itemObjs d) (fun a b => r a.2 b.2) (.ok (itemObjs d).length)) So true true
        (d.length + 1) n .src (some (pureKey getCount))).run 0).1 =
        .ok (((itemObjs d).mergeSort (fun a b => !r a.2 b.2)).take n.toNat) :=
      nSelectIsSortedPrefix_proven _ (itemObjs d) _ (some getCount) n true true So _ _ 0 hr' hSo hn
        (by simp [itemObjs]) (Or.inl rfl)
    show Except.map unObj ((nSelect (mcEnv N (itemObjs d)) So true true (d.length + 1) n .src
      (some (pureKey getCount))).run 0).1 = _
    rw [hE, hs, itemObjs_mergeSort]
    show Except.ok (unObj ((List.map _ _).take n.toNat)) = _
    rw [← List.map_take]
    exact congrArg Except.ok (unObj_itemObjs _)

/-! ### `__delitem__` -/

/-- **`del c[e]` is `dict.__delitem__` behind an `in` test.** For a hashable `e`, it removes
`e`, and on an absent `e` it leaves the counter as it is where `dict.__delitem__` raises
`KeyError(e)`; for an unhashable `e` it raises exactly the exception the dict operation
raises (from `elem in self`, :747).

Source: docstring, Lib/collections/__init__.py:746 ("Like dict.__delitem__() but does not
raise KeyError for missing values"). -/
def DelitemGuard : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] (K : KOps κ) (rk : κ → String) (d : D κ ν) (e : κ),
    (K.hash e = .ok () →
      delitem K rk d e = .ok (D.del d e) ∧
      (e ∉ D.keys d → delitem K rk d e = .ok d ∧ dictDelitem K rk d e = .error (.keyError (rk e)))) ∧
    (∀ x, K.hash e = .error x →
      ∃ y, dHash K e = .error y ∧ delitem K rk d e = .error y ∧ dictDelitem K rk d e = .error y)

theorem delitemGuard_proven : DelitemGuard := by
  intro κ ν _ K rk d e
  refine ⟨fun hk => ⟨?_, fun hn => ⟨?_, ?_⟩⟩, fun x hx => ?_⟩
  · unfold delitem
    rw [dMem_ok d hk, ok_bind]
    cases hm : D.mem d e
    · rw [del_of_notMem (D.mem_false_iff.1 hm)]; rfl
    · simp only [ite_true]
      unfold dictDelitem
      rw [dHash_ok hk, ok_bind, hm]; rfl
  · unfold delitem
    rw [dMem_ok d hk, ok_bind, D.mem_false_iff.2 hn]; rfl
  · unfold dictDelitem
    rw [dHash_ok hk, ok_bind, D.mem_false_iff.2 hn]; rfl
  · have : ∃ y, dHash K e = .error y := by
      unfold dHash; rw [hx]; cases x <;> simp
    obtain ⟨y, hy⟩ := this
    refine ⟨y, hy, ?_, ?_⟩
    · unfold delitem dMem; rw [hy]; rfl
    · unfold dictDelitem; rw [hy]; rfl

/-! ### `copy`, `__reduce__` -/

/-- **`copy` and `__reduce__` build new objects of `self`'s class with `self`'s items.** For
every counter with any counts (non-positive ones included): `c.copy()` is the new object
`self.__class__(self)` allocates, of `c`'s class, with `c`'s items in `c`'s order (a `copy`
returning `self` has `c`'s id); `c.__reduce__()` is `(c.__class__, (d,))` for a new plain
`dict` `d` with those items, and calling the class on `d` rebuilds them (the pickle round trip).

Source: docstring 'Return a shallow copy.', Lib/collections/__init__.py:739, and the pickle
protocol for `__reduce__` (Doc/library/pickle.rst). -/
def CopyReduce : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] [DecidableEq ν] (K : KOps κ) (N : Num ν) (fresh fresh' : Nat)
    (c : CObj κ ν), D.WF c.data →
    counterCopy K N fresh c = .ok ⟨fresh, c.cls, c.data⟩ ∧
    counterReduce fresh' c = (c.cls, ⟨fresh', "dict", c.data⟩) ∧
    counterNew K N (.mapping (dictSrc (counterReduce fresh' c).2.data)) [] = .ok c.data

theorem copyReduce_proven : CopyReduce := by
  intro κ ν _ _ K N fresh fresh' c hw
  have hu := update_nil_WF hw
  refine ⟨?_, ?_, ?_⟩
  · simp [counterCopy, counterNew, update, updateSrc, updateMapping, dictMerge, ctrSrc, dictSrc,
      Out.andThen, Out.toPy, hu]
  · simp [counterReduce, hu]
  · simp [counterReduce, counterNew, update, updateSrc, updateMapping, dictMerge, dictSrc,
      Out.andThen, Out.toPy, hu]

/-! ### Unary operators -/

/-- **Unary `+` and `-` are the binary operators with an empty counter.** For every key type
and every count type, whatever its `<` and `-` do (raise, return non-bools, NaN-like values):
`-c` is `Counter() - c`, result and exception alike; and `+c` is `c + Counter()` when
`x + 0` is `x`.

Source: docstrings, Lib/collections/__init__.py:938 ('Adds an empty counter') and :946-947
('Subtracts from an empty counter'). -/
def UnaryAsBinary : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] (K : KOps κ) (N : Num ν) (a : D κ ν), HashOk K a →
    negC K N a = subC K N [] a ∧
    ((∀ x, N.add x N.zero = .ok x) → posC K N a = addC K N a [])

theorem unaryAsBinary_proven : UnaryAsBinary := by
  intro κ ν _ K N a hh
  refine ⟨?_, fun hadd => ?_⟩
  · unfold negC subC
    simp only [loopInto, ok_bind]
    apply loopInto_congr
    intro p hp
    rw [dMem_ok [] (hash_of_mem hh hp), ok_bind]
    rfl
  · unfold posC addC
    have h2 : ∀ r, loopInto K (onlyRightPos K N a) r [] = .ok r := fun _ => rfl
    simp only [h2, bind_ok_right]
    apply loopInto_congr
    intro p hp
    rw [dGet_ok [] N.zero (hash_of_mem hh hp), ok_bind]
    simp [D.get?, hadd]

/-! ### `elements` -/

/-- **`elements()` is lazy and stops at the first bad count.** For every count type and every
`idx` that `__index__` gives: on items whose counts convert to `Py_ssize_t`, `c.elements()`
yields each key `max(0, n)` times in insertion order; at the first count whose `__index__`
raises (a float, say), it yields the elements before it and then raises that exception, and at
the first count out of `Py_ssize_t` range it raises `OverflowError`, later items unread.

Source: docstring, Lib/collections/__init__.py:643-658 ('repeating each as many times as its
count ... elements() will ignore it'), and the lazy `chain.from_iterable` of :661. -/
def ElementsLazy : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] (N : Num ν) (idx : ν → Int) (pre : D κ ν),
    (∀ p ∈ pre, N.index p.2 = .ok (idx p.2) ∧ ssizeMin ≤ idx p.2 ∧ idx p.2 ≤ ssizeMax) →
    elements N pre = FIt.ofList (pre.flatMap (fun p => List.replicate (idx p.2).toNat p.1)) ∧
    (∀ (e : κ) (v : ν) (post : D κ ν) (ex : PyExc), N.index v = .error ex →
      elements N (pre ++ (e, v) :: post) =
        ⟨pre.flatMap (fun p => List.replicate (idx p.2).toNat p.1), some ex⟩) ∧
    (∀ (e : κ) (v : ν) (post : D κ ν) (n : Int), N.index v = .ok n → (n < ssizeMin ∨ n > ssizeMax) →
      elements N (pre ++ (e, v) :: post) =
        ⟨pre.flatMap (fun p => List.replicate (idx p.2).toNat p.1),
          some (.overflowError "Python int too large to convert to C ssize_t")⟩)

theorem elementsLazy_proven : ElementsLazy := by
  intro κ ν _ N idx pre
  induction pre with
  | nil =>
    intro _
    refine ⟨rfl, fun e v post ex hv => ?_, fun e v post n hv hr => ?_⟩
    · simp [elements, repeatTimes, hv]
    · simp [elements, repeatTimes, hv, hr]
  | cons p t ih =>
    intro h
    obtain ⟨k, v0⟩ := p
    obtain ⟨hp1, hp2, hp3⟩ := h (k, v0) (by simp)
    simp only at hp1 hp2 hp3
    have ⟨h1, h2, h3⟩ := ih (fun q hq => h q (by simp [hq]))
    have hrep : repeatTimes N v0 = .ok (idx v0).toNat := by
      simp only [repeatTimes, hp1, ok_bind]
      rw [if_neg (by omega)]; rfl
    refine ⟨?_, fun e v post ex hv => ?_, fun e v post n hv hr => ?_⟩
    · simp only [elements, hrep, h1, FIt.ofList, List.flatMap_cons]
    · simp only [List.cons_append, elements, hrep, h2 e v post ex hv, List.flatMap_cons]
    · simp only [List.cons_append, elements, hrep, h3 e v post n hv hr, List.flatMap_cons]

/-! ### Rich comparison -/

/-- `self[e]` on a counter with every key hashable. -/
def at0 (N : Num ν) (d : D κ ν) (e : κ) : ν := (D.get? d e).getD N.zero

/-- **The comparisons are pointwise over both key sets, missing counts as zero.** For every key
type and every count type whose `==`, `<=` and `>=` (with their truth tests) are pure
predicates `E`, `L`, `G` (any predicates: partial orders, NaN-like values): `a == b` is true
exactly when `E(a[e], b[e])` holds for every key `e` of `a` and of `b`, with `0` for a key
missing on one side, and likewise `<=` with `L` and `>=` with `G`; `!=` is the negation of `==`,
`<` is `<=` and `!=`, `>` is `>=` and `!=`. Against an operand that is not a `Counter`, every
one returns `NotImplemented`; against a `Counter`, none does.

Source: docstrings, Lib/collections/__init__.py:800-830 ('Missing counts are treated as
zero'). -/
def ComparePointwise : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] (K : KOps κ) (N : Num ν) (E L G : ν → ν → Bool) (a b : D κ ν),
    HashOk K a → HashOk K b →
    N.eq = (fun x y => .ok (E x y)) → N.le = (fun x y => .ok (L x y)) → N.ge = (fun x y => .ok (G x y)) →
    let all := fun (R : ν → ν → Bool) => decide (∀ e ∈ D.keys a ++ D.keys b, R (at0 N a e) (at0 N b e) = true)
    eqC K N a b = .ok (all E) ∧ neC K N a b = .ok (!all E) ∧ leC K N a b = .ok (all L) ∧
    ltC K N a b = .ok (all L && !all E) ∧ geC K N a b = .ok (all G) ∧ gtC K N a b = .ok (all G && !all E) ∧
    (∀ f ∈ [eqC K N a, neC K N a, leC K N a, ltC K N a, geC K N a, gtC K N a],
      guarded f .other = none ∧ guarded f (.ctr b) = some (f b))

theorem cmpAll_pure (K : KOps κ) (N : Num ν) (R : ν → ν → Bool) (a b : D κ ν) (ha : HashOk K a) (hb : HashOk K b)
    (r : ν → ν → Py Bool) (hr : r = fun x y => .ok (R x y)) :
    cmpAll K N r a b = .ok (decide (∀ e ∈ D.keys a ++ D.keys b, R (at0 N a e) (at0 N b e) = true)) := by
  subst hr
  unfold cmpAll
  apply allM_pure
  intro e he
  have hea : K.hash e = .ok () := by
    rcases List.mem_append.1 he with h | h
    · exact ha e h
    · exact hb e h
  rw [dGet_ok a N.zero hea, ok_bind, dGet_ok b N.zero hea, ok_bind]
  rfl

theorem comparePointwise_proven : ComparePointwise := by
  intro κ ν _ K N E L G a b ha hb hE hL hG
  have he := cmpAll_pure K N E a b ha hb N.eq hE
  have hl := cmpAll_pure K N L a b ha hb N.le hL
  have hg := cmpAll_pure K N G a b ha hb N.ge hG
  refine ⟨he, ?_, hl, ?_, hg, ?_, ?_⟩
  · simp only [neC, eqC, he, ok_bind, pure_py]
  · simp only [ltC, leC, hl, ok_bind, neC, eqC, he, pure_py]
    cases decide (∀ e ∈ D.keys a ++ D.keys b, L (at0 N a e) (at0 N b e) = true) <;> rfl
  · simp only [gtC, geC, hg, ok_bind, neC, eqC, he, pure_py]
    cases decide (∀ e ∈ D.keys a ++ D.keys b, G (at0 N a e) (at0 N b e) = true) <;> rfl
  · intro f _; exact ⟨rfl, rfl⟩

/-- **A raising comparison is not swallowed.** For every count type and every pair of
counters: if comparing the counts of some key raises and no key before it compared false,
then `==`, `<=` and `>=` raise.

Source: invariant (an exception in user code propagates). -/
def CompareRaises : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] (K : KOps κ) (N : Num ν) (a b : D κ ν), HashOk K a → HashOk K b →
    ∀ r ∈ [N.eq, N.le, N.ge],
      (∀ e ∈ D.keys a ++ D.keys b, r (at0 N a e) (at0 N b e) ≠ .ok false) →
      (∃ e ∈ D.keys a ++ D.keys b, ∃ x, r (at0 N a e) (at0 N b e) = .error x) →
      ∃ x, cmpAll K N r a b = .error x

theorem compareRaises_proven : CompareRaises := by
  intro κ ν _ K N a b ha hb r _ hn hx
  unfold cmpAll
  have hh : ∀ e ∈ D.keys a ++ D.keys b, K.hash e = .ok () := by
    intro e he
    rcases List.mem_append.1 he with h | h
    · exact ha e h
    · exact hb e h
  have hp : ∀ e ∈ D.keys a ++ D.keys b,
      (do let x ← dGet K a e N.zero; let y ← dGet K b e N.zero; r x y) = r (at0 N a e) (at0 N b e) := by
    intro e he
    rw [dGet_ok a N.zero (hh e he), ok_bind, dGet_ok b N.zero (hh e he), ok_bind]; rfl
  apply allM_raises
  · intro e he; rw [hp e he]; exact hn e he
  · obtain ⟨e, he, x, hx⟩ := hx
    exact ⟨e, he, x, by rw [hp e he]; exact hx⟩

end PyLean.CoreLibs.Coll
