import PyLean.CoreLibs.Functools.Partial

/-!
Properties of `partial`, `partialmethod` and `Placeholder`.
-/

namespace PyLean.CoreLibs.Functools

open PyLean

/-- A `partial` object is well formed: `phcount` counts the stored placeholders, and the last
stored argument is not a placeholder. Type invariant: `partial_new` and `__setstate__` enforce both. -/
def PWf {α : Type} (args : List (PArg α)) (ph : Nat) : Prop :=
  ph = phCount args ∧ trailingPh args = false

theorem phCount_fill {α : Type} : ∀ (p n : List (PArg α)),
    phCount (fill p n) = phCount p - min (phCount p) n.length + phCount n
  | [], n => by simp [fill, phCount]
  | .ph :: rest, [] => by
    have ih := phCount_fill rest ([] : List (PArg α))
    simp only [phCount, fill, List.filter_cons, isPh, ite_true, List.length_cons, List.length_nil,
      List.filter_nil] at ih ⊢
    omega
  | .ph :: rest, m :: n => by
    have ih := phCount_fill rest n
    cases m <;> simp only [phCount, fill, List.filter_cons, isPh, Bool.false_eq_true, ite_true,
      ite_false, List.length_cons] at ih ⊢ <;> omega
  | .val a :: rest, n => by
    have ih := phCount_fill rest n
    cases n <;> simpa only [phCount, fill, List.filter_cons, isPh, Bool.false_eq_true, ite_false]
      using ih

theorem fill_no_ph {α : Type} : ∀ (p n : List (PArg α)), phCount p = 0 → fill p n = p ++ n
  | [], _, _ => rfl
  | .ph :: _, _, h => by simp [phCount, List.filter_cons, isPh] at h
  | .val a :: rest, n, h => by
    have h' : phCount rest = 0 := by simpa [phCount, List.filter_cons, isPh] using h
    cases n <;> simp [fill, fill_no_ph rest _ h']

theorem phCount_append {α : Type} (a b : List (PArg α)) :
    phCount (a ++ b) = phCount a + phCount b := by
  simp [phCount]

theorem fillCall_no_ph {α : Type} : ∀ (p : List (PArg α)) (n : List α), phCount p = 0 →
    fillCall p n = valsOf p ++ n
  | [], _, _ => rfl
  | .ph :: _, _, h => by simp [phCount, List.filter_cons, isPh] at h
  | .val a :: rest, n, h => by
    have h' : phCount rest = 0 := by simpa [phCount, List.filter_cons, isPh] using h
    simp [fillCall, valsOf, fillCall_no_ph rest n h']

/-- A keyword dictionary has distinct keys: type invariant. -/
def KwOk {α : Type} (kw : List (String × α)) : Prop := (kw.map Prod.fst).Nodup

theorem mergeKw_nil_aux {α : Type} : ∀ (acc rest : List (String × α)),
    ((acc ++ rest).map Prod.fst).Nodup → mergeKw acc rest = acc ++ rest
  | acc, [], _ => by simp [mergeKw]
  | acc, p :: rest, h => by
    have hn : p.1 ∉ acc.map Prod.fst := by
      intro hm
      rw [List.map_append, List.map_cons, List.nodup_append] at h
      exact (h.2.2 _ hm _ (by simp)) rfl
    have hany : acc.any (fun q => q.1 == p.1) = false := by
      rw [List.any_eq_false]
      intro q hq e
      exact hn (List.mem_map.mpr ⟨q, hq, by simpa using e⟩)
    have ih := mergeKw_nil_aux (acc ++ [p]) rest (by simpa using h)
    simp only [mergeKw, List.foldl_cons, hany, Bool.false_eq_true, ite_false] at ih ⊢
    simpa using ih

theorem mergeKw_nil {α : Type} (kw : List (String × α)) (h : KwOk kw) : mergeKw [] kw = kw := by
  simpa using mergeKw_nil_aux [] kw (by simpa [KwOk] using h)

theorem fill_nil {α : Type} : ∀ p : List (PArg α), fill p [] = p
  | [] => rfl
  | .ph :: rest => by simp [fill, fill_nil rest]
  | .val a :: rest => by simp [fill, fill_nil rest]

theorem fillCall_fill {α : Type} : ∀ (p n : List (PArg α)) (more : List α),
    phCount n ≤ more.length → fillCall (fill p n) more = fillCall p (fillCall n more)
  | p, [], more, _ => by simp [fill_nil, fillCall]
  | [], m :: n, more, _ => by simp [fill, fillCall]
  | .val a :: rest, m :: n, more, h => by
    simp only [fill, fillCall]
    rw [fillCall_fill rest (m :: n) more h]
  | .ph :: rest, .val a :: n, more, h => by
    have h' : phCount n ≤ more.length := by
      simpa [phCount, List.filter_cons, isPh] using h
    simp only [fill, fillCall]
    rw [fillCall_fill rest n more h']
  | .ph :: rest, .ph :: n, [], h => by
    simp [phCount, List.filter_cons, isPh] at h
  | .ph :: rest, .ph :: n, x :: ms, h => by
    have h' : phCount n ≤ ms.length := by
      simpa [phCount, List.filter_cons, isPh] using h
    simp only [fill, fillCall]
    rw [fillCall_fill rest n ms h']

theorem length_fillCall {α : Type} : ∀ (a : List (PArg α)) (m : List α), phCount a ≤ m.length →
    (fillCall a m).length + phCount a = a.length + m.length
  | [], m, _ => by simp [fillCall, phCount]
  | .val v :: rest, m, h => by
    have ih := length_fillCall rest m (by simpa [phCount, List.filter_cons, isPh] using h)
    simp only [fillCall, List.length_cons, phCount, List.filter_cons, isPh, Bool.false_eq_true,
      ite_false] at ih ⊢
    omega
  | .ph :: rest, [], h => by
    simp [phCount, List.filter_cons, isPh] at h
  | .ph :: rest, x :: ms, h => by
    have ih := length_fillCall rest ms (by simpa [phCount, List.filter_cons, isPh] using h)
    simp only [fillCall, List.length_cons, phCount, List.filter_cons, isPh, ite_true] at ih ⊢
    omega

theorem phCount_le {α : Type} (a : List (PArg α)) : phCount a ≤ a.length :=
  List.length_filter_le _ _

/-! ### The merger -/

theorem orderLoop_j {α : Type} : ∀ (l : List (PArg α)) (i j : Nat),
    (orderLoop l i j).2 = j + phCount l
  | [], _, j => by simp [orderLoop, phCount]
  | .ph :: rest, i, j => by
    have ih := orderLoop_j rest (i + 1) (j + 1)
    simp only [orderLoop, ih, phCount, List.filter_cons, isPh, ite_true, List.length_cons]
    omega
  | .val _ :: rest, i, j => by
    have ih := orderLoop_j rest (i + 1) j
    simpa only [orderLoop, phCount, List.filter_cons, isPh, Bool.false_eq_true, ite_false] using ih

/-- `_partial_prepare_merger` counts what the object stores as `_phcount`. -/
theorem prepareMerger_count {α : Type} (args : List (PArg α)) :
    (prepareMerger args).1 = phCount args := by
  simp only [prepareMerger, prepareMergerOf]
  by_cases h : args.length = 0
  · have : args = [] := List.length_eq_zero_iff.mp h
    subst this
    simp [phCount]
  · simp only [h, ite_false, orderLoop_j]
    omega

theorem prepareMerger_some {α : Type} (args : List (PArg α)) (h : phCount args ≠ 0) :
    (prepareMerger args).2 = some (orderLoop args 0 args.length).1 := by
  have hl : args.length ≠ 0 := by
    intro e
    have : args = [] := List.length_eq_zero_iff.mp e
    subst this
    simp [phCount] at h
  simp only [prepareMerger, prepareMergerOf, hl, ite_false, orderLoop_j]
  simp [h]

/-- What the merger gives when every slot has a value: the stored arguments with `new` in the slots. -/
def takeFill {α : Type} : List (PArg α) → List (PArg α) → List (PArg α)
  | [], _ => []
  | .ph :: rest, n :: new => n :: takeFill rest new
  | .ph :: _, [] => []
  | .val a :: rest, new => .val a :: takeFill rest new

theorem itemget_cons {β : Type} (i : Nat) (order : List Nat) (t : List β) (x : β) (h : t[i]? = some x) :
    itemget (i :: order) t = (itemget order t).map (fun r => x :: r) := by
  simp only [itemget, mapPy, h, bind, Except.bind, pure, Except.pure]
  cases mapPy _ order <;> rfl

theorem itemget_order {α : Type} (t : List (PArg α)) : ∀ (l : List (PArg α)) (i j : Nat)
    (new : List (PArg α)), (∀ k (x : PArg α), l[k]? = some x → t[i + k]? = some x) →
    (∀ k, t[j + k]? = new[k]?) →
    itemget (orderLoop l i j).1 t =
      if phCount l ≤ new.length then .ok (takeFill l new)
      else .error (.indexError "tuple index out of range")
  | [], _, _, _, _, _ => by simp [orderLoop, itemget, mapPy, phCount, takeFill, pure, Except.pure]
  | .ph :: rest, i, j, new, hl, hn => by
    have hpc : phCount (PArg.ph :: rest : List (PArg α)) = phCount rest + 1 := by
      simp [phCount, List.filter_cons, isPh]
    cases new with
    | nil =>
      have h0 : t[j]? = none := by simpa using hn 0
      simp only [orderLoop, itemget, mapPy, h0, hpc, List.length_nil, bind, Except.bind]
      simp
    | cons x new =>
      have h0 : t[j]? = some x := by simpa using hn 0
      have ih := itemget_order t rest (i + 1) (j + 1) new
        (fun k y h => by
          have := hl (k + 1) y (by simpa using h)
          rwa [show i + (k + 1) = i + 1 + k by omega] at this)
        (fun k => by
          have := hn (k + 1)
          rw [show j + (k + 1) = j + 1 + k by omega] at this
          simpa using this)
      simp only [orderLoop, itemget_cons _ _ _ _ h0, ih, hpc, List.length_cons, takeFill,
        Nat.add_le_add_iff_right]
      split <;> rfl
  | .val a :: rest, i, j, new, hl, hn => by
    have hpc : phCount (PArg.val a :: rest : List (PArg α)) = phCount rest := by
      simp [phCount, List.filter_cons, isPh]
    have h0 : t[i]? = some (.val a) := by simpa using hl 0 (.val a) (by simp)
    have ih := itemget_order t rest (i + 1) j new
      (fun k y h => by
        have := hl (k + 1) y (by simpa using h)
        rwa [show i + (k + 1) = i + 1 + k by omega] at this) hn
    simp only [orderLoop, itemget_cons _ _ _ _ h0, ih, hpc, takeFill]
    split <;> rfl

/-- The merger run on `pargs ++ new`, as `__call__` and `_partial_new` run it. -/
theorem itemget_merger {α : Type} (pargs new : List (PArg α)) :
    itemget (orderLoop pargs 0 pargs.length).1 (pargs ++ new) =
      if phCount pargs ≤ new.length then .ok (takeFill pargs new)
      else .error (.indexError "tuple index out of range") := by
  apply itemget_order
  · intro k x h
    have hk : k < pargs.length := (List.getElem?_eq_some_iff.mp h).1
    rw [Nat.zero_add, List.getElem?_append_left hk, h]
  · intro k
    rw [List.getElem?_append_right (by omega)]
    simp

theorem fill_eq_takeFill {α : Type} : ∀ (p n : List (PArg α)),
    fill p n = takeFill p (n ++ List.replicate (phCount p - n.length) .ph) ++ n.drop (phCount p)
  | [], n => by simp [fill, takeFill, phCount]
  | .ph :: rest, [] => by
    have ih := fill_eq_takeFill rest []
    have hpc : phCount (PArg.ph :: rest : List (PArg α)) = phCount rest + 1 := by
      simp [phCount, List.filter_cons, isPh]
    simp only [List.nil_append, List.length_nil, Nat.sub_zero, List.drop_nil, List.append_nil] at ih
    simp only [fill, hpc, List.length_nil, Nat.sub_zero, List.nil_append, List.replicate_succ,
      takeFill, List.drop_nil, List.append_nil, ih]
  | .ph :: rest, x :: n => by
    have ih := fill_eq_takeFill rest n
    have hpc : phCount (PArg.ph :: rest : List (PArg α)) = phCount rest + 1 := by
      simp [phCount, List.filter_cons, isPh]
    simp only [fill, hpc, List.length_cons, Nat.add_sub_add_right, List.cons_append, takeFill,
      List.drop_succ_cons]
    rw [ih]
  | .val a :: rest, n => by
    have ih := fill_eq_takeFill rest n
    have hpc : phCount (PArg.val a :: rest : List (PArg α)) = phCount rest := by
      simp [phCount, List.filter_cons, isPh]
    have hf : fill (PArg.val a :: rest) n = .val a :: fill rest n := by
      cases n <;> rfl
    rw [hf, hpc, ih]
    rfl

theorem fillCall_eq_takeFill {α : Type} : ∀ (p : List (PArg α)) (n : List α), phCount p ≤ n.length →
    fillCall p n = valsOf (takeFill p (n.map .val)) ++ n.drop (phCount p)
  | [], n, _ => by simp [fillCall, takeFill, valsOf, phCount]
  | .ph :: _, [], h => by simp [phCount, List.filter_cons, isPh] at h
  | .ph :: rest, x :: n, h => by
    have hpc : phCount (PArg.ph :: rest : List (PArg α)) = phCount rest + 1 := by
      simp [phCount, List.filter_cons, isPh]
    have ih := fillCall_eq_takeFill rest n (by simp [hpc] at h; omega)
    simp only [fillCall, hpc, List.map_cons, takeFill, List.drop_succ_cons, ih]
    simp [valsOf]
  | .val a :: rest, n, h => by
    have hpc : phCount (PArg.val a :: rest : List (PArg α)) = phCount rest := by
      simp [phCount, List.filter_cons, isPh]
    have ih := fillCall_eq_takeFill rest n (by omega)
    simp only [fillCall, hpc, takeFill, ih]
    simp [valsOf]

/-- `__call__` in Python as a length test: the merger's `IndexError` is exactly "too few arguments". -/
theorem partialCallPy_spec {α : Type} (func : Fn α) (pargs : List (PArg α)) (pkw kw : List (String × α))
    (ph : Nat) (args : List α) (hph : ph = phCount pargs) :
    partialCallPy func pargs pkw ph args kw =
      if ph ≠ 0 ∧ args.length < ph then .error (.typeError (missingMsg ph args.length))
      else callFn func (fillCall pargs args) (mergeKw pkw kw) := by
  subst hph
  simp only [partialCallPy]
  by_cases h0 : phCount pargs = 0
  · simp only [h0, ne_eq, not_true_eq_false, ite_false, false_and]
    rw [fillCall_no_ph pargs args h0]
  · have hm := itemget_merger pargs (args.map PArg.val)
    simp only [h0, ne_eq, not_false_eq_true, ite_true, true_and, prepareMerger_some pargs h0, hm,
      List.length_map]
    by_cases hl : args.length < phCount pargs
    · have h1 : ¬ phCount pargs ≤ args.length := by omega
      simp [hl, h1]
    · have h1 : phCount pargs ≤ args.length := by omega
      simp only [h1, hl, ite_true, ite_false]
      rw [fillCall_eq_takeFill pargs args h1]

theorem cMergeLoop_ok {α : Type} (args : List α) : ∀ (p : List (PArg α)) (j : Nat),
    j + phCount p ≤ args.length →
    ∃ h, cMergeLoop args p j = some (h, j + phCount p) ∧
      fillCall p (args.drop j) = h ++ args.drop (j + phCount p)
  | [], j, _ => ⟨[], by simp [cMergeLoop, phCount], by simp [fillCall, phCount]⟩
  | .ph :: rest, j, hj => by
    have hpc : phCount (PArg.ph :: rest : List (PArg α)) = phCount rest + 1 := by
      simp [phCount, List.filter_cons, isPh]
    have hlt : j < args.length := by omega
    obtain ⟨h, h1, h2⟩ := cMergeLoop_ok args rest (j + 1) (by omega)
    have hx : args[j]? = some args[j] := List.getElem?_eq_getElem hlt
    refine ⟨args[j] :: h, ?_, ?_⟩
    · simp only [cMergeLoop, hx, h1, Option.map_some, hpc]
      congr 2
      omega
    · rw [List.drop_eq_getElem_cons hlt, hpc]
      simp only [fillCall, h2, List.cons_append]
      congr 3
      omega
  | .val a :: rest, j, hj => by
    have hpc : phCount (PArg.val a :: rest : List (PArg α)) = phCount rest := by
      simp [phCount, List.filter_cons, isPh]
    obtain ⟨h, h1, h2⟩ := cMergeLoop_ok args rest j (by omega)
    refine ⟨a :: h, ?_, ?_⟩
    · simp only [cMergeLoop, h1, Option.map_some, hpc]
    · simp only [fillCall, h2, hpc, List.cons_append]

/-- With `phcount` right, C's two merge loops stay in bounds and give the merged arguments. -/
theorem cMerge_ok {α : Type} (pargs : List (PArg α)) (args : List α) (h : phCount pargs ≤ args.length) :
    cMerge pargs (phCount pargs) args = some (fillCall pargs args) := by
  obtain ⟨t, h1, h2⟩ := cMergeLoop_ok args pargs 0 (by omega)
  simp only [Nat.zero_add, List.drop_zero] at h1 h2
  have hc : phCount pargs + (args.length - phCount pargs) ≤ args.length := by omega
  have ht : (args.drop (phCount pargs)).take (args.length - phCount pargs) = args.drop (phCount pargs) :=
    List.take_of_length_le (by simp)
  simp only [cMerge, h1, hc, ite_true, ht, h2]

theorem vecMerge_ok {α : Type} (pargs : List (PArg α)) (args : List α) (h : phCount pargs ≤ args.length) :
    vecMerge pargs (phCount pargs) args = .ok (fillCall pargs args) := by
  obtain ⟨t, h1, _⟩ := cMergeLoop_ok args pargs 0 (by omega)
  simp only [Nat.zero_add] at h1
  simp only [vecMerge, h1, cMerge_ok pargs args h, ne_eq, not_true_eq_false, and_false, ite_false]

theorem partialCallC_spec {α : Type} (func : Fn α) (pargs : List (PArg α)) (pkw kw : List (String × α))
    (ph : Nat) (args : List α) (hph : ph = phCount pargs) :
    partialCallC func pargs pkw ph args kw =
      if args.length < ph then .error (.typeError (missingMsg ph args.length))
      else callFn func (fillCall pargs args) (if pkw.isEmpty then kw else mergeKw pkw kw) := by
  subst hph
  simp only [partialCallC]
  by_cases hl : args.length < phCount pargs
  · simp [hl]
  · have h1 : phCount pargs ≤ args.length := by omega
    simp only [hl, ite_false]
    by_cases h0 : phCount pargs = 0
    · simp only [h0, ne_eq, not_true_eq_false, ite_false]
      rw [fillCall_no_ph pargs args h0]
    · simp only [h0, ne_eq, not_false_eq_true, ite_true]
      have := cMerge_ok pargs args h1
      rw [this]

theorem map_replace_absent {α : Type} (p : String × α) :
    ∀ t : List (String × α), (∀ q ∈ t, q.1 ≠ p.1) → t.map (fun q => if q.1 == p.1 then p else q) = t
  | [], _ => rfl
  | q :: t, h => by
    have h1 : (q.1 == p.1) = false := by simpa using h q (by simp)
    simp only [List.map_cons, h1, Bool.false_eq_true, ite_false]
    rw [map_replace_absent p t (fun r hr => h r (by simp [hr]))]

theorem any_of_keys {α : Type} (A B : List (String × α)) (k : String) (h : A.map Prod.fst = B.map Prod.fst) :
    A.any (fun q => q.1 == k) = B.any (fun q => q.1 == k) := by
  have e : ∀ C : List (String × α), C.any (fun q => q.1 == k) = (C.map Prod.fst).any (· == k) := by
    intro C
    simp [List.any_map, Function.comp_def]
  rw [e A, e B, h]

theorem replace_keys {α : Type} (p : String × α) (A : List (String × α)) :
    (A.map (fun q => if q.1 == p.1 then p else q)).map Prod.fst = A.map Prod.fst := by
  induction A with
  | nil => rfl
  | cons q A ih =>
    simp only [List.map_cons, ih, List.cons.injEq, and_true]
    split
    · next h => exact (beq_iff_eq.1 h).symm
    · rfl

/-- The loop of `partial_vectorcall`, with no Python code in its lookups, keeps the keys of the stored dict and leaves
what `{**stored, **call}` gives. -/
theorem vecKwLoop_plain {α : Type} (pkw : List (String × α)) : ∀ (kw : List (String × α))
    (m : Option (List (String × α))) (t : List (String × α)),
    (m.getD pkw).map Prod.fst = pkw.map Prod.fst →
    (∀ p ∈ kw, ∀ q ∈ t, q.1 ≠ p.1) → (kw.map Prod.fst).Nodup →
    ∃ m' t', vecKwLoop pkw m t (plainKw kw) = .ok (pkw, m', t') ∧
      (m'.getD pkw).map Prod.fst = pkw.map Prod.fst ∧
      (m'.getD pkw) ++ t' = kw.foldl mergeStep (m.getD pkw ++ t) := by
  intro kw
  induction kw with
  | nil =>
    intro m t hA _ _
    exact ⟨m, t, rfl, hA, rfl⟩
  | cons p kw ih =>
    intro m t hA hd hn
    obtain ⟨k, v⟩ := p
    simp only [List.map_cons, List.nodup_cons] at hn
    have hk : ∀ r ∈ kw, r.1 ≠ k := by
      intro r hr e
      exact hn.1 (by subst e; exact List.mem_map.2 ⟨r, hr, rfl⟩)
    have ht : ∀ q ∈ t, q.1 ≠ k := fun q hq => hd (k, v) (by simp) q hq
    have ha : (t.any (fun q => q.1 == k)) = false := by
      rw [List.any_eq_false]
      intro q hq
      simpa using ht q hq
    have hAny := any_of_keys (m.getD pkw) pkw k hA
    by_cases hc : pkw.any (fun q => q.1 == k) = true
    · have hk2 := replace_keys (k, v) (m.getD pkw)
      obtain ⟨m', t', h1, h2, h3⟩ := ih (some ((m.getD pkw).map (fun q => if q.1 == k then (k, v) else q))) t
        (by simpa [Option.getD] using hk2.trans hA) (fun r hr q hq => hd r (by simp [hr]) q hq) hn.2
      refine ⟨m', t', ?_, h2, ?_⟩
      · simpa [vecKwLoop, plainKw, hc] using h1
      · have hs : mergeStep (m.getD pkw ++ t) (k, v) =
            (m.getD pkw).map (fun q => if q.1 == k then (k, v) else q) ++ t := by
          have hz := map_replace_absent (k, v) t ht
          simp only [mergeStep, List.any_append, hAny, hc, ha, Bool.true_or, ite_true, List.map_append, hz]
        simpa [List.foldl_cons, hs] using h3
    · have hc' : pkw.any (fun q => q.1 == k) = false := by simpa only [Bool.not_eq_true] using hc
      obtain ⟨m', t', h1, h2, h3⟩ := ih m (t ++ [(k, v)]) hA
        (by
          intro r hr q hq
          rcases List.mem_append.1 hq with hq | hq
          · exact hd r (by simp [hr]) q hq
          · simp only [List.mem_singleton] at hq
            subst hq
            exact (hk r hr).symm) hn.2
      refine ⟨m', t', ?_, h2, ?_⟩
      · simpa [vecKwLoop, plainKw, hc'] using h1
      · have hs : mergeStep (m.getD pkw ++ t) (k, v) = m.getD pkw ++ t ++ [(k, v)] := by
          simp [mergeStep, List.any_append, hAny, hc', ha]
        have e : m.getD pkw ++ t ++ [(k, v)] = m.getD pkw ++ (t ++ [(k, v)]) := by simp
        simpa [List.foldl_cons, hs, e] using h3

theorem vecKeywords_plain {α : Type} (pkw kw : List (String × α)) (hk : KwOk kw) :
    vecKeywords pkw (plainKw kw) = .ok (if pkw.isEmpty then kw else mergeKw pkw kw) := by
  cases hp : pkw with
  | nil =>
    simp [vecKeywords, plainKw, Function.comp_def]
  | cons b bs =>
    obtain ⟨m', t', h1, h2, h3⟩ := vecKwLoop_plain (b :: bs) kw none [] rfl (by simp) hk
    have hl : (m'.getD (b :: bs)).length = (b :: bs).length := by
      simpa using congrArg List.length h2
    simp only [Option.getD_none, List.append_nil] at h3
    have hf : List.foldl mergeStep (b :: bs) kw = mergeKw (b :: bs) kw := rfl
    simp only [vecKeywords, List.isEmpty_cons, Bool.false_eq_true, ite_false, h1, vecKwFinish, hl]
    simp [h3, hf]

/-- With no Python code in the lookups, the keywords of `partial_vectorcall` are `{**stored, **call}`, stored first, and
with none stored the ones of the call. Distinct keywords in a call are a type invariant. A key whose lookup raises stops
the call with that exception, before anything is built. -/
def VecKeywordsMerge : Prop :=
  ∀ (α : Type) (pkw kw : List (String × α)) (a : String × α) (k : VecKw α) (rest : List (VecKw α)) (e : PyExc), KwOk kw →
    vecKeywords pkw (plainKw kw) = .ok (if pkw.isEmpty then kw else mergeKw pkw kw) ∧
    (k.onLookup (a :: pkw) = .error e → vecKeywords (a :: pkw) (k :: rest) = .error e)

theorem vecKeywordsMerge_proven : VecKeywordsMerge := by
  intro α pkw kw a k rest e hk
  refine ⟨vecKeywords_plain pkw kw hk, ?_⟩
  intro h
  simp [vecKeywords, vecKwLoop, h]

theorem partialVectorcall_spec {α : Type} (func : Fn α) (pargs : List (PArg α)) (pkw kw : List (String × α))
    (ph : Nat) (args : List α) (hph : ph = phCount pargs) (hk : KwOk kw) :
    partialVectorcall func pargs pkw ph args kw = partialCallC func pargs pkw ph args kw := by
  rw [partialCallC_spec func pargs pkw kw ph args hph]
  subst hph
  simp only [partialVectorcall, partialVectorcallKws, vecKeywords_plain pkw kw hk]
  by_cases hl : args.length < phCount pargs
  · simp [hl]
  · have h1 : phCount pargs ≤ args.length := by omega
    simp only [hl, ite_false]
    by_cases h0 : phCount pargs = 0
    · simp only [h0, ne_eq, not_true_eq_false, ite_false]
      rw [fillCall_no_ph pargs args h0]
    · simp only [h0, ne_eq, not_false_eq_true, ite_true, vecMerge_ok pargs args h1]

/-- `_partial_prepare_merger`: `phcount` is the number of placeholders, there is a merger exactly when that is
not zero, and running the merger on `args + new` puts `new` in the slots, or raises `IndexError` when `new` is
too short, which `__call__` turns into the `TypeError`. -/
def PartialMergerIsFill : Prop :=
  ∀ (α : Type) (pargs new : List (PArg α)),
    (prepareMerger pargs).1 = phCount pargs ∧
    (phCount pargs = 0 → (prepareMerger pargs).2 = none) ∧
    (phCount pargs ≠ 0 → ∃ order, (prepareMerger pargs).2 = some order ∧
      ((phCount pargs ≤ new.length → itemget order (pargs ++ new) = .ok (takeFill pargs new)) ∧
       (new.length < phCount pargs → (itemget order (pargs ++ new)).raises "IndexError")))

theorem partialMergerIsFill_proven : PartialMergerIsFill := by
  intro α pargs new
  refine ⟨prepareMerger_count pargs, ?_, ?_⟩
  · intro h
    simp only [prepareMerger, prepareMergerOf]
    by_cases hl : pargs.length = 0
    · simp [hl]
    · simp [hl, orderLoop_j, h]
  · intro h
    refine ⟨_, prepareMerger_some pargs h, ?_, ?_⟩
    · intro hle
      rw [itemget_merger]
      simp [hle]
    · intro hlt
      rw [itemget_merger]
      have : ¬ phCount pargs ≤ new.length := by omega
      simp only [this, ite_false]
      exact ⟨_, rfl, rfl⟩

/-! ### `_partial_new` -/

/-- The flattening as a formula. -/
def flattenSpec {α : Type} (outer : Option Nat) (func : Fn α) (args : List (PArg α))
    (kw' : List (String × α)) : Fn α :=
  match func with
  | .pobj _ _ inner pargs pkw pph =>
    if args.isEmpty then .pobj outer none inner pargs (mergeKw pkw kw') pph
    else
      let tot := if pph = 0 then pargs ++ args else fill pargs args
      .pobj outer none inner tot (mergeKw pkw kw') (phCount tot)
  | _ => .pobj outer none func args kw' (phCount args)

/-- The merge branch of `_partial_new` is `fill`. -/
theorem newCore_inner {α : Type} (args pargs : List (PArg α)) (kw : List (String × PArg α))
    (kw' pkw : List (String × α)) (pph : Nat) (hph : pph = phCount pargs)
    (ht : trailingPh args = false) (hk : kwVals kw = some kw') :
    newCore args kw (some (pargs, pkw, pph)) =
      .ok (if args.isEmpty then (pargs, mergeKw pkw kw', pph) else
        let tot := if pph = 0 then pargs ++ args else fill pargs args
        (tot, mergeKw pkw kw', phCount tot)) := by
  subst hph
  simp only [newCore, ht, Bool.false_eq_true, ite_false, hk]
  by_cases he : args.isEmpty = true
  · simp [he]
  · simp only [he, Bool.false_eq_true, ite_false]
    by_cases h0 : phCount pargs = 0
    · simp only [h0, ne_eq, not_true_eq_false, ite_false, ite_true, prepareMerger_count]
    · simp only [h0, ne_eq, not_false_eq_true, ite_true, ite_false, prepareMerger_some pargs h0]
      have htot : (if args.length < phCount pargs then
          pargs ++ args ++ List.replicate (phCount pargs - args.length) PArg.ph else pargs ++ args) =
          pargs ++ (args ++ List.replicate (phCount pargs - args.length) .ph) := by
        by_cases hl : args.length < phCount pargs
        · simp [hl]
        · have : phCount pargs - args.length = 0 := by omega
          simp [hl, this]
      rw [htot, itemget_merger]
      have hle : phCount pargs ≤ (args ++ List.replicate (phCount pargs - args.length) (.ph : PArg α)).length := by
        simp only [List.length_append, List.length_replicate]
        omega
      simp only [hle, ite_true]
      have hdrop : (if args.length > phCount pargs then
          takeFill pargs (args ++ List.replicate (phCount pargs - args.length) .ph) ++
            args.drop (phCount pargs)
          else takeFill pargs (args ++ List.replicate (phCount pargs - args.length) .ph)) =
          fill pargs args := by
        rw [fill_eq_takeFill pargs args]
        by_cases hl : args.length > phCount pargs
        · simp [hl]
        · have : args.drop (phCount pargs) = [] := List.drop_eq_nil_of_le (by omega)
          simp [hl, this]
      rw [hdrop, prepareMerger_count]

/-- The `partial` head of `_partial_new`, as validation followed by the formula. `PWf` is the type invariant
of the wrapped `partial`. -/
theorem partialNewPy_spec {α : Type} (outer : Option Nat) (func : Fn α) (args : List (PArg α))
    (kw : List (String × PArg α))
    (hwf : ∀ o d g pargs pkw ph, func = .pobj o d g pargs pkw ph → PWf pargs ph) :
    partialNewPy outer func args kw =
      (validateNew func args kw).map (flattenSpec outer func args) := by
  unfold partialNewPy validateNew
  by_cases hc : func.isCallable = true
  · simp only [hc, Bool.not_true, Bool.false_eq_true, ite_false]
    by_cases ht : trailingPh args = true
    · cases func <;> simp [newCore, ht, Except.map]
    · have ht' : trailingPh args = false := by simpa using ht
      cases hk : kwVals kw with
      | none =>
        cases func <;> simp [newCore, ht', hk, Except.map]
      | some kw' =>
        simp only [ht', Bool.false_eq_true, ite_false, hk, Except.map]
        cases func with
        | pobj o d g pargs pkw ph =>
          simp only
          rw [newCore_inner args pargs kw kw' pkw ph (hwf _ _ _ _ _ _ rfl).1 ht' hk]
          simp only [flattenSpec]
          split <;> rfl
        | base id => simp [newCore, ht', hk, flattenSpec, prepareMerger_count]
        | notCallable => simp [Fn.isCallable] at hc
        | fails e => simp [newCore, ht', hk, flattenSpec, prepareMerger_count]
        | bound f s => simp [newCore, ht', hk, flattenSpec, prepareMerger_count]
  · have : func.isCallable = false := by simpa using hc
    simp [this, Except.map]

/-- `partial(func, *args, **kw)` builds the same object in C and in Python whenever `func` is not a
`partial` with a `__dict__`: same function, same arguments, same keywords, same placeholder count,
for nested partials, for placeholders on both sides, and the same exception for each rejected
call. Well-formedness of the wrapped `partial` is a type invariant. -/
def PartialNewTwins : Prop :=
  ∀ (α : Type) (outer : Option Nat) (func : Fn α) (args : List (PArg α))
    (kw : List (String × PArg α)),
    (∀ o d g pargs pkw ph, func = .pobj o (some d) g pargs pkw ph → False) →
    (∀ o d g pargs pkw ph, func = .pobj o d g pargs pkw ph → PWf pargs ph) →
    partialNewC outer func args kw = partialNewPy outer func args kw

theorem flattenTwins {α : Type} (outer : Option Nat) (o : Option Nat) (g : Fn α)
    (pargs args : List (PArg α)) (pkw kw : List (String × α)) (ph : Nat) (h : ph = phCount pargs) :
    flattenC outer (.pobj o none g pargs pkw ph) args kw =
      flattenSpec outer (.pobj o none g pargs pkw ph) args kw := by
  subst h
  cases hn : args with
  | nil =>
    simp [flattenC, flattenSpec, phCount]
  | cons a rest =>
    by_cases h0 : phCount pargs = 0
    · simp [flattenC, flattenSpec, h0, phCount_append]
    · have hp : phCount pargs > 0 := by omega
      simp only [flattenC, flattenSpec, hp, h0, List.isEmpty_cons, Bool.false_eq_true, ite_false,
        Bool.not_false, and_self, ite_true, phCount_fill]

theorem partialNewTwins_proven : PartialNewTwins := by
  intro α outer func args kw hd hwf
  rw [partialNewPy_spec outer func args kw hwf]
  simp only [partialNewC, bind, Except.bind, pure, Except.pure, Except.map]
  cases validateNew func args kw with
  | error e => rfl
  | ok kw' =>
    simp only
    cases func with
    | base id => rfl
    | notCallable => rfl
    | fails e => rfl
    | bound f s => rfl
    | pobj o d g pargs pkw ph =>
      cases d with
      | some x => exact (hd _ _ _ _ _ _ rfl).elim
      | none =>
        rw [flattenTwins outer o g pargs args pkw kw' ph (hwf _ _ _ _ _ _ rfl).1]

/-- `partial(p, *args)` is the same object in both twins for every wrapped object. False: when the
wrapped `partial` has an instance `__dict__`, C keeps it as `func` and Python flattens it. -/
def PartialNewTwinsAlways : Prop :=
  ∀ (func : Fn Nat) (args : List (PArg Nat)),
    partialNewC none func args [] = partialNewPy none func args []

theorem partialNewTwinsAlways_refuted : ¬PartialNewTwinsAlways := by
  intro h
  have := h (.pobj none (some []) (.base 0) [] [] 0) []
  revert this
  decide

/-! ### Calls -/

/-- The three ways of calling a `partial`, Python's `__call__`, C's `partial_call` and C's
`partial_vectorcall`, give the same call of the wrapped function, or the same `TypeError` with the
same message, for every wrapped function and every placeholder pattern. Type invariants: well-formed
`partial`, and distinct keywords in the call. -/
def PartialCallTwins : Prop :=
  ∀ (α : Type) (func : Fn α) (pargs : List (PArg α)) (pkw kw : List (String × α)) (ph : Nat)
    (args : List α), PWf pargs ph → KwOk kw →
    partialCallPy func pargs pkw ph args kw = partialCallC func pargs pkw ph args kw ∧
    partialVectorcall func pargs pkw ph args kw = partialCallC func pargs pkw ph args kw

theorem partialCallTwins_proven : PartialCallTwins := by
  intro α func pargs pkw kw ph args ⟨hph, _⟩ hk
  have hmerge : (if pkw.isEmpty then kw else mergeKw pkw kw) = mergeKw pkw kw := by
    cases pkw with
    | nil => simp [mergeKw_nil kw hk]
    | cons _ _ => simp
  refine ⟨?_, partialVectorcall_spec func pargs pkw kw ph args hph hk⟩
  rw [partialCallPy_spec func pargs pkw kw ph args hph,
    partialCallC_spec func pargs pkw kw ph args hph, hmerge]
  by_cases h0 : ph = 0
  · subst h0
    simp
  · by_cases hl : args.length < ph <;> simp [h0, hl]

/-- The result of `partial(func, *args)(*more)`, where `func` is any callable: it is `func(*args, *more)`.
False: both twins flatten a `partial` subclass, so its `__call__` override is never called. -/
def PartialCallsWrappedObject : Prop :=
  ∀ (func : Fn Nat) (args : List Nat) (more : List Nat),
    func.isCallable = true →
    (do callFn (← partialNewC none func (args.map PArg.val) []) more []) =
      callFn func (args ++ more) []

theorem partialCallsWrappedObject_refuted : ¬PartialCallsWrappedObject := by
  intro h
  have := h (.pobj (some 77) none (.base 0) [] [] 0) [] [] rfl
  revert this
  decide

/-- Both sides give the same call, or both raise `TypeError`. -/
def sameOrTypeError {α : Type} (a b : Py α) : Prop :=
  a = b ∨ (a.raises "TypeError" ∧ b.raises "TypeError")

/-- A `partial` of a plain `partial` behaves like the inner one called with the outer arguments in
the slots they fill: `partial(p, *args)(*more)` is `p(*filled)`, for every placeholder pattern on
both levels, where `more` covers the outer placeholders. The positional core of the docs' "roughly
equivalent" code, with no keywords at either level; a `partial` subclass overriding `__call__` is
excluded here and refuted separately. `PWf` is a type invariant. -/
def PartialNestedPositional : Prop :=
  ∀ (α : Type) (g : Fn α) (d : Option (List (String × α))) (pargs args : List (PArg α)) (ph : Nat)
    (more : List α), PWf pargs ph → trailingPh args = false → phCount args ≤ more.length →
    ∃ p, partialNewPy none (.pobj none d g pargs [] ph) args [] = .ok p ∧
      sameOrTypeError (callFn p more []) (callFn (.pobj none d g pargs [] ph) (fillCall args more) [])

theorem nested_spec {α : Type} (g : Fn α) (d : Option (List (String × α))) (pargs args : List (PArg α))
    (ph : Nat) (more : List α) (hw : PWf pargs ph) (hm : phCount args ≤ more.length) :
    sameOrTypeError (callFn (flattenSpec none (.pobj none d g pargs [] ph) args []) more [])
      (callFn (.pobj none d g pargs [] ph) (fillCall args more) []) := by
  obtain ⟨hph, _⟩ := hw
  have hlen := length_fillCall args more hm
  have hle := phCount_le args
  have hmk : mergeKw ([] : List (String × α)) [] = [] := rfl
  by_cases he : args.isEmpty = true
  · have hn : args = [] := by simpa using he
    subst hn
    left
    simp [flattenSpec, fillCall, hmk, callFn]
  · have hne : args.isEmpty = false := by simpa using he
    by_cases h0 : ph = 0
    · left
      have hp : phCount pargs = 0 := by omega
      have htot : fillCall (pargs ++ args) more = fillCall pargs (fillCall args more) := by
        rw [← fillCall_fill pargs args more hm, fill_no_ph pargs args hp]
      simp only [flattenSpec, hne, Bool.false_eq_true, ite_false, h0, ite_true, callFn, hmk]
      rw [phCount_append, hp, Nat.zero_add]
      have h1 : ¬ more.length < phCount args := by omega
      have h2 : ¬ (fillCall args more).length < 0 := by omega
      simp only [h1, h2, ite_false, htot, hmk]
    · have hfc := phCount_fill pargs args
      have htot := fillCall_fill pargs args more hm
      simp only [flattenSpec, hne, Bool.false_eq_true, ite_false, h0, callFn, hmk]
      rw [hfc, ← hph, htot]
      by_cases hl : more.length < ph - min ph args.length + phCount args
      · have h2 : (fillCall args more).length < ph := by omega
        right
        simp only [hl, ite_true, h2]
        exact ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩⟩
      · have h2 : ¬ (fillCall args more).length < ph := by omega
        left
        simp only [hl, ite_false, h2]

theorem partialNestedPositional_proven : PartialNestedPositional := by
  intro α g d pargs args ph more hw ht hm
  refine ⟨flattenSpec none (.pobj none d g pargs [] ph) args [], ?_, nested_spec g d pargs args ph more hw hm⟩
  have hs := partialNewPy_spec none (.pobj none d g pargs [] ph) args []
    (fun o' d' g' a' k' p' h => by cases h; exact hw)
  have hv : validateNew (.pobj none d g pargs [] ph) args ([] : List (String × PArg α)) = .ok [] := by
    simp [validateNew, Fn.isCallable, ht, kwVals]
  rw [hs, hv]
  rfl

/-- `partial.__get__` and `partial_descr_get`: on the class it gives the object itself, on an instance a
`MethodType`, and calling that puts the instance first and then runs the `partial`, for every wrapped
function and every argument list. -/
def PartialGetBinds : Prop :=
  ∀ (α : Type) (self : Fn α) (o : α) (args : List α) (kw : List (String × α)),
    descrGet self none = self ∧ callFn (descrGet self (some o)) args kw = callFn self (o :: args) kw

theorem partialGetBinds_proven : PartialGetBinds := fun _ _ _ _ _ => ⟨rfl, by simp [descrGet, callFn]⟩

/-! ### State -/

/-- No tuple subclass in the state, and no empty dict subclass whose conversion raises: documented
preconditions of the narrowed twin property. The first is refuted by `PartialStateKeepsPhcountAlways`; the
second is the `PyDict_Copy` shortcut, where C skips an overridden `keys` that Python calls. -/
def NoTupleSub {α : Type} : PState α → Prop
  | .four _ (.sub _) _ _ => False
  | .four _ _ (.sub [] (some _)) _ => False
  | _ => True

/-- A state of the kind `tuple(args)` at Lib/functools.py:419 is there for: a tuple subclass counts when it overrides none
of what `__setstate__` reads. A subclass that does is on record in `PartialStateKeepsPhcountAlways`, and in
`PartialStateViews` for what the Python twin reads. The empty dict subclass is on record in `PartialStateEmptyDictSub`. -/
def HonestState {α : Type} : PState α → Prop
  | .four _ (.sub t) _ _ => t = TupSub.honest t.raw
  | _ => True

theorem pyHead_honest {α : Type} (raw : List (PArg α)) :
    pyHead (TupSub.honest raw) = if trailingPh raw then .error (.typeError trailingMsg) else .ok (raw, phCount raw) := by
  have hp : (prepareMergerOf raw.length raw).1 = phCount raw := prepareMerger_count raw
  cases hl : raw.getLast? with
  | none =>
    have he : raw = [] := List.getLast?_eq_none_iff.1 hl
    subst he
    simp [pyHead, lastIsPh, TupSub.honest, trailingPh]
    rfl
  | some a =>
    have hne : raw.isEmpty = false := by
      cases raw with
      | nil => simp at hl
      | cons _ _ => rfl
    cases a with
    | ph => simp [pyHead, lastIsPh, TupSub.honest, trailingPh, hl, hne, isPh]
    | val x =>
      simp [pyHead, lastIsPh, TupSub.honest, trailingPh, hl, hne, isPh]
      simpa using hp

/-- The dict field of a Python object is always there; C leaves it `NULL`. -/
def withDict {α : Type} : Fn α → Fn α
  | .pobj o d f a k p => .pobj o (some (d.getD [])) f a k p
  | f => f

theorem prepareMergerOf_length {α : Type} (l : List (PArg α)) :
    (prepareMergerOf l.length l).1 = phCount l := prepareMerger_count l

/-- `__setstate__` in C and in Python accept the same exact-tuple states and build the same object, up to
the `__dict__` Python creates; each failure has the same exception class in both, and `dict(kwds)`
failing on a dict subclass propagates from both, leaving the object as it was because no assignment
has run. They differ in two messages: Python says "must be a tuple" and "expected 4 items", C says "invalid
partial state". The result keeps the invariant `PWf`. A tuple subclass is excluded by a documented
precondition and handled by the next two properties. -/
def StateAgrees {α : Type} (o : Option Nat) (st : PState α) : Prop :=
  (∀ r, setstateC o st = .ok r → setstatePy o st = .ok (withDict r)) ∧
  (∀ r, setstatePy o st = .ok r → ∃ c, setstateC o st = .ok c ∧ withDict c = r) ∧
  (∀ e, setstateC o st = .error e → ∃ e', setstatePy o st = .error e' ∧ e'.className = e.className) ∧
  (∀ d f a k ph, setstateC o st = .ok (.pobj o d f a k ph) → PWf a ph)

/-- `PartialStateTwins`, on states with an exact tuple. -/
theorem stateAgrees_tuple {α : Type} (o : Option Nat) (st : PState α) (hs : NoTupleSub st) : StateAgrees o st := by
  unfold StateAgrees
  cases st with
  | notTuple =>
    exact ⟨by simp [setstateC], by simp [setstatePy],
      fun e h => by cases h; exact ⟨_, rfl, rfl⟩, by simp [setstateC]⟩
  | size n =>
    exact ⟨by simp [setstateC], by simp [setstatePy],
      fun e h => by cases h; exact ⟨_, rfl, rfl⟩, by simp [setstateC]⟩
  | four func args kw ns =>
    cases args with
    | sub t => exact hs.elim
    | other =>
      have hbad : stateShapeOk func StArgs.other kw ns = false := by simp [stateShapeOk, StArgs.raw]
      simp only [setstateC, setstatePy, hbad, Bool.not_false, ite_true]
      exact ⟨by simp, by simp, fun e h => by cases h; exact ⟨_, rfl, rfl⟩, by simp⟩
    | tuple items =>
      simp only [setstateC, setstatePy]
      by_cases hsh : stateShapeOk func (.tuple items) kw ns = true
      · simp only [hsh, Bool.not_true, Bool.false_eq_true, ite_false, StArgs.raw, pyHead_honest]
        by_cases ht : trailingPh items = true
        · simp only [ht, ite_true]
          exact ⟨by simp, by simp, fun e h => by cases h; exact ⟨_, rfl, rfl⟩, by simp⟩
        · have ht' : trailingPh items = false := by simpa using ht
          simp only [ht', Bool.false_eq_true, ite_false, prepareMergerOf_length]
          cases kw with
          | other => simp [stateShapeOk] at hsh
          | none =>
            cases ns with
            | other => simp [stateShapeOk] at hsh
            | none =>
              simp only
              exact ⟨fun r h => (by cases h; rfl), fun r h => (by cases h; exact ⟨_, rfl, rfl⟩),
                fun e h => (by cases h), fun d f a k ph h => (by cases h; exact ⟨rfl, ht'⟩)⟩
            | dict x =>
              simp only
              exact ⟨fun r h => (by cases h; rfl), fun r h => (by cases h; exact ⟨_, rfl, rfl⟩),
                fun e h => (by cases h), fun d f a k ph h => (by cases h; exact ⟨rfl, ht'⟩)⟩
          | exact d =>
            cases ns with
            | other => simp [stateShapeOk] at hsh
            | none =>
              simp only
              exact ⟨fun r h => (by cases h; rfl), fun r h => (by cases h; exact ⟨_, rfl, rfl⟩),
                fun e h => (by cases h), fun d f a k ph h => (by cases h; exact ⟨rfl, ht'⟩)⟩
            | dict x =>
              simp only
              exact ⟨fun r h => (by cases h; rfl), fun r h => (by cases h; exact ⟨_, rfl, rfl⟩),
                fun e h => (by cases h), fun d f a k ph h => (by cases h; exact ⟨rfl, ht'⟩)⟩
          | sub d fl =>
            cases fl with
            | some e =>
              cases d with
              | nil => exact hs.elim
              | cons q qs =>
                simp only
                exact ⟨by simp, by simp, fun e' h => (by cases h; exact ⟨_, rfl, rfl⟩), by simp⟩
            | none =>
              cases ns with
              | other => simp [stateShapeOk] at hsh
              | none =>
                cases d <;>
                  exact ⟨fun r h => (by cases h; rfl), fun r h => (by cases h; exact ⟨_, rfl, rfl⟩),
                    fun e h => (by cases h), fun d f a k ph h => (by cases h; exact ⟨rfl, ht'⟩)⟩
              | dict x =>
                cases d <;>
                  exact ⟨fun r h => (by cases h; rfl), fun r h => (by cases h; exact ⟨_, rfl, rfl⟩),
                    fun e h => (by cases h), fun d f a k ph h => (by cases h; exact ⟨rfl, ht'⟩)⟩
      · simp only [Bool.not_eq_true] at hsh
        simp only [hsh, Bool.not_false, ite_true]
        exact ⟨by simp, by simp, fun e h => by cases h; exact ⟨_, rfl, rfl⟩, by simp⟩

/-- `__setstate__` in C and in Python agree on an exact tuple and on a tuple subclass that overrides nothing they read, the
case `tuple(args)` exists for; see `StateAgrees` for what they agree on. They differ in two messages: Python says "must be
a tuple" and "expected 4 items", C says "invalid partial state". -/
def PartialStateTwins : Prop :=
  ∀ (α : Type) (o : Option Nat) (st : PState α), HonestState st →
    (match st with
     | .four _ _ (.sub [] (some _)) _ => False
     | _ => True) → StateAgrees o st

theorem partialStateTwins_proven : PartialStateTwins := by
  intro α o st hs hk
  cases st with
  | notTuple => exact stateAgrees_tuple o _ trivial
  | size n => exact stateAgrees_tuple o _ trivial
  | four func args kw ns =>
    have hnt : ∀ A : StArgs α, (∀ t, A ≠ .sub t) → NoTupleSub (PState.four func A kw ns) := by
      intro A hA
      cases A with
      | sub t => exact absurd rfl (hA t)
      | tuple r =>
        cases kw with
        | sub d fl =>
          cases d with
          | nil =>
            cases fl with
            | some e => exact hk.elim
            | none => trivial
          | cons _ _ => trivial
        | _ => trivial
      | other =>
        cases kw with
        | sub d fl =>
          cases d with
          | nil =>
            cases fl with
            | some e => exact hk.elim
            | none => trivial
          | cons _ _ => trivial
        | _ => trivial
    cases args with
    | tuple r => exact stateAgrees_tuple o _ (hnt _ (by simp))
    | other => exact stateAgrees_tuple o _ (hnt _ (by simp))
    | sub t =>
      have he : t = TupSub.honest t.raw := hs
      have main := stateAgrees_tuple o (.four func (.tuple t.raw) kw ns) (hnt _ (by simp))
      have eC : setstateC o (.four func (.sub t) kw ns) = setstateC o (.four func (.tuple t.raw) kw ns) := by
        rw [he]
        rfl
      have eP : setstatePy o (.four func (.sub t) kw ns) = setstatePy o (.four func (.tuple t.raw) kw ns) := by
        rw [he]
        rfl
      unfold StateAgrees at main ⊢
      rw [eC, eP]
      exact main

/-- The reads of a tuple subclass in the Python twin, in order, each from the source: an overridden `__bool__` that says no
leaves `args[-1]`, `__len__` and the first iteration unread, so a trailing placeholder gets through, with a count of nought;
`__bool__`, `__getitem__`, `__len__` and each `__iter__` raising propagates; and what is kept is the second iteration, and
what is counted the first. -/
def PartialStateViews : Prop :=
  ∀ (α : Type) (t : TupSub α) (e : PyExc) (l1 l2 : List (PArg α)) (n : Nat) (a : α),
    (t.truth = .error e → pyHead t = .error e) ∧
    (t.truth = .ok true → t.last = .error e → pyHead t = .error e) ∧
    (t.truth = .ok true → t.last = .ok .ph → pyHead t = .error (.typeError trailingMsg)) ∧
    (t.truth = .ok false → t.iter1 = .ok l1 → pyHead t = .ok (l1, 0)) ∧
    (t.truth = .ok false → t.iter1 = .error e → pyHead t = .error e) ∧
    (t.truth = .ok true → t.last = .ok (.val a) →
      (t.len = .ok n → t.iter1 = .ok l1 → t.iter2 = .ok l2 → pyHead t = .ok (l2, (prepareMergerOf n l1).1)) ∧
      (t.len = .error e → pyHead t = .error e) ∧
      (t.len = .ok n → t.iter1 = .error e → pyHead t = .error e) ∧
      (t.len = .ok n → t.iter1 = .ok l1 → t.iter2 = .error e → pyHead t = .error e))

theorem partialStateViews_proven : PartialStateViews := by
  intro α t e l1 l2 n a
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; simp [pyHead, lastIsPh, h]
  · intro h1 h2; simp [pyHead, lastIsPh, h1, h2]
  · intro h1 h2; simp [pyHead, lastIsPh, h1, h2, isPh]
  · intro h1 h2; simp [pyHead, lastIsPh, h1, h2]
  · intro h1 h2; simp [pyHead, lastIsPh, h1, h2]
  · intro h1 h2
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h3 h4 h5; simp [pyHead, lastIsPh, h1, h2, h3, h4, h5, isPh]
    · intro h3; simp [pyHead, lastIsPh, h1, h2, h3, isPh]
    · intro h3 h4; simp [pyHead, lastIsPh, h1, h2, h3, h4, isPh]
    · intro h3 h4 h5; simp [pyHead, lastIsPh, h1, h2, h3, h4, h5, isPh]

/-- The Python twin too keeps the count of what it kept. False: it counts the first iteration, and keeps the second. -/
def PartialStatePyPhcount : Prop :=
  ∀ (st : PState Nat) (d : Option (List (String × Nat))) (f : Fn Nat) (a : List (PArg Nat))
    (k : List (String × Nat)) (ph : Nat),
    setstatePy none st = .ok (.pobj none d f a k ph) → ph = phCount a

theorem partialStatePyPhcount_refuted : ¬PartialStatePyPhcount := by
  intro h
  have := h (.four (.base 0) (.sub ⟨[.val 1], .ok true, .ok (.val 1), .ok 1, .ok [.val 1], .ok [.ph, .val 1]⟩) .none .none)
    (some []) (.base 0) [.ph, .val 1] [] 0 (by decide)
  revert this
  decide

/-- An empty dict subclass in a state behaves alike in the twins. False: `dict(kwds)` in Python runs an overridden `keys`,
which may raise, and `PyDict_Copy` in C skips the items of an empty dict and calls nothing. -/
def PartialStateEmptyDictSub : Prop :=
  ∀ (α : Type) (o : Option Nat) (st : PState α) (e : PyExc), setstatePy o st = .error e →
    ∃ e', setstateC o st = .error e'

theorem partialStateEmptyDictSub_refuted : ¬PartialStateEmptyDictSub := by
  intro h
  obtain ⟨e', he⟩ := h Nat none (.four (.base 0) (.tuple []) (.sub [] (some (.valueError "conv"))) .none)
    (.valueError "conv") rfl
  cases he

/-- After a successful `__setstate__`, `_phcount` counts the placeholders of `args`, whatever the state. False
for a tuple subclass whose `__iter__` differs from its storage: C counts the storage and keeps the iteration. -/
def PartialStateKeepsPhcountAlways : Prop :=
  ∀ (st : PState Nat) (d : Option (List (String × Nat))) (f : Fn Nat) (a : List (PArg Nat))
    (k : List (String × Nat)) (ph : Nat),
    setstateC none st = .ok (.pobj none d f a k ph) → ph = phCount a

theorem partialStateKeepsPhcountAlways_refuted : ¬PartialStateKeepsPhcountAlways := by
  intro h
  have := h (.four (.base 0) (.sub (.iterates [.ph, .val 1] (.ok [.val 1, .val 2]))) .none .none) none (.base 0)
    [.val 1, .val 2] [] 1 (by decide)
  revert this
  decide

/-- Calling a `partial` never reads outside the arguments of the call, whatever `__setstate__` was given.
False for the same state, and this is memory-unsafe in C: `partial_call` and `partial_vectorcall` trust
`phcount` and index the argument array past its end. -/
def PartialCallInBoundsAlways : Prop :=
  ∀ (st : PState Nat) (d : Option (List (String × Nat))) (f : Fn Nat) (a : List (PArg Nat))
    (k : List (String × Nat)) (ph : Nat) (args : List Nat),
    setstateC none st = .ok (.pobj none d f a k ph) →
    partialCallC f a k ph args [] ≠ .error oobRead ∧ partialVectorcall f a k ph args [] ≠ .error oobRead

theorem partialCallInBoundsAlways_refuted : ¬PartialCallInBoundsAlways := by
  intro h
  have := (h (.four (.base 0) (.sub (.iterates [.ph, .val 1] (.ok [.ph, .ph, .val 1]))) .none .none) none (.base 0)
    [.ph, .ph, .val 1] [] 1 [10] (by decide)).1
  revert this
  decide

/-- A vectorcall of a `partial` writes only inside its stack array, whatever `__setstate__` was given. False
when `args` has fewer placeholders than `phcount`, with more call arguments than `phcount`: the `memcpy` starts
at `j`, not at `phcount`, and overruns the array by the difference. With a tuple of four items and three call
arguments that is `small_stack`, and glibc reports stack smashing. -/
def PartialVectorcallWritesInBounds : Prop :=
  ∀ (st : PState Nat) (d : Option (List (String × Nat))) (f : Fn Nat) (a : List (PArg Nat))
    (k : List (String × Nat)) (ph : Nat) (args : List Nat),
    setstateC none st = .ok (.pobj none d f a k ph) → partialVectorcall f a k ph args [] ≠ .error oobWrite

theorem partialVectorcallWritesInBounds_refuted : ¬PartialVectorcallWritesInBounds := by
  intro h
  have := h (.four (.base 0) (.sub (.iterates [.ph, .ph, .val 1] (.ok [.val 1, .val 2, .val 3, .val 4]))) .none .none)
    none (.base 0) [.val 1, .val 2, .val 3, .val 4] [] 2 [10, 11, 12] (by decide)
  revert this
  decide

/-- A call of a well-formed `partial` writes only inside the tuple of keyword names and the stack it allocated. False:
the sizes come from `PyDict_GET_SIZE(partial_keywords)` at Modules/_functoolsmodule.c:392, the lookup at :467 can run the
`__eq__` of a `str` subclass, which can add to `p.keywords`, and the `PyDict_Next` loop at :508-513 then writes one item
per key. -/
def PartialVectorcallKwWritesInBounds : Prop :=
  ∀ (func : Fn Nat) (pargs : List (PArg Nat)) (pkw : List (String × Nat)) (ph : Nat) (args : List Nat)
    (kws : List (VecKw Nat)), ph = phCount pargs → partialVectorcallKws func pargs pkw ph args kws ≠ .error oobWrite

theorem partialVectorcallKwWritesInBounds_refuted : ¬PartialVectorcallKwWritesInBounds := by
  intro h
  exact h (.base 0) [] [("a", 1)] 0 [] [⟨"b", 2, fun d => .ok (d ++ [("x", 0), ("y", 0)])⟩] rfl (by decide)

/-- A call of a well-formed `partial` hands the callee a tuple of keyword names with every item set. False: a smaller dict
at :508-513 leaves `NULL` in it. -/
def PartialVectorcallKwNamesSet : Prop :=
  ∀ (func : Fn Nat) (pargs : List (PArg Nat)) (pkw : List (String × Nat)) (ph : Nat) (args : List Nat)
    (kws : List (VecKw Nat)), ph = phCount pargs → partialVectorcallKws func pargs pkw ph args kws ≠ .error nullKwName

theorem partialVectorcallKwNamesSet_refuted : ¬PartialVectorcallKwNamesSet := by
  intro h
  exact h (.base 0) [] [("a", 1)] 0 [] [⟨"b", 2, fun _ => .ok []⟩] rfl (by decide)

/-- Every keyword of a call reaches the wrapped function. False: when `__eq__` adds to `p.keywords` no more than the tuple
has room for, the loop at :508-513 overwrites the tail, and the call goes ahead without the keyword. -/
def PartialVectorcallKeepsCallKeywords : Prop :=
  ∀ (pkw : List (String × Nat)) (kws : List (VecKw Nat)) (c : Called Nat),
    partialVectorcallKws (.base 0) [] pkw 0 [] kws = .ok c → ∀ k ∈ kws, (k.key, k.val) ∈ c.kw

theorem partialVectorcallKeepsCallKeywords_refuted : ¬PartialVectorcallKeepsCallKeywords := by
  intro h
  let k : VecKw Nat := ⟨"b", 2, fun d => .ok (d ++ [("z", 1)])⟩
  have := h [("a", 1)] [k] ⟨0, [], [("a", 1), ("z", 1)]⟩ rfl k (by simp)
  revert this
  decide

/-- The narrowed statement: without a tuple subclass in the state, a call of the result stays in bounds in
both C paths. -/
def PartialCallInBounds : Prop :=
  ∀ (α : Type) (st : PState α), HonestState st → (match st with
    | .four _ _ (.sub [] (some _)) _ => False
    | _ => True) → ∀ (d : Option (List (String × α))) (f : Fn α)
    (a : List (PArg α)) (k : List (String × α)) (ph : Nat) (args : List α),
    callFn f (fillCall a args) (if k.isEmpty then [] else mergeKw k []) ≠ .error oobRead →
    setstateC none st = .ok (.pobj none d f a k ph) →
    partialCallC f a k ph args [] ≠ .error oobRead ∧ partialVectorcall f a k ph args [] ≠ .error oobRead

theorem partialCallInBounds_proven : PartialCallInBounds := by
  intro α st hs hk d f a k ph args hf h
  have hw := (partialStateTwins_proven α none st hs hk).2.2.2 d f a k ph h
  have hv := partialVectorcall_spec f a k [] ph args hw.1 (by simp [KwOk])
  rw [hv]
  have : partialCallC f a k ph args [] ≠ .error oobRead := by
    rw [partialCallC_spec f a k [] ph args hw.1]
    by_cases hl : args.length < ph
    · simp [hl, oobRead]
    · simpa only [hl, ite_false] using hf
  exact ⟨this, this⟩

/-- `type(self)(self.func)` followed by the state from `__reduce__` gives the object back: every field in C,
including whether `__dict__` was ever created, and every field in Python, whose `__dict__` always exists.
So a `partial` round-trips through pickle with its function, arguments, keywords, placeholder count and
instance dictionary. `func` being callable and `PWf` are the type invariants of a `partial`. -/
def PartialReduceRoundTrip : Prop :=
  ∀ (α : Type) (o : Option Nat) (d : Option (List (String × α))) (f : Fn α) (a : List (PArg α))
    (k : List (String × α)) (ph : Nat), f.isCallable = true → PWf a ph →
    unpickleWith partialNewC setstateC pReduceC (.pobj o d f a k ph) = .ok (.pobj o d f a k ph) ∧
    unpickleWith partialNewPy setstatePy pReducePy (.pobj o d f a k ph) =
      .ok (.pobj o (some (d.getD [])) f a k ph)

theorem partialReduceRoundTrip_proven : PartialReduceRoundTrip := by
  intro α o d f a k ph hc ⟨h1, h2⟩
  subst h1
  have hnC : ∃ r, partialNewC o f [] [] = .ok r := by
    exact ⟨_, by simp [partialNewC, validateNew, hc, trailingPh, kwVals, bind, Except.bind, pure, Except.pure]; rfl⟩
  have hnP : ∃ r, partialNewPy o f [] [] = .ok r := by
    cases f with
    | notCallable => simp [Fn.isCallable] at hc
    | base id => exact ⟨_, by simp [partialNewPy, Fn.isCallable, newCore, trailingPh, kwVals]; rfl⟩
    | fails e => exact ⟨_, by simp [partialNewPy, Fn.isCallable, newCore, trailingPh, kwVals]; rfl⟩
    | bound g s => exact ⟨_, by simp [partialNewPy, Fn.isCallable, newCore, trailingPh, kwVals]; rfl⟩
    | pobj o' d' g a' k' p' =>
      exact ⟨_, by simp [partialNewPy, Fn.isCallable, newCore, trailingPh, kwVals]; rfl⟩
  obtain ⟨r1, hr1⟩ := hnC
  obtain ⟨r2, hr2⟩ := hnP
  have hsh : ∀ (kw : StKw α) (ns : StNs α), kw ≠ .other → ns ≠ .other →
      stateShapeOk f (.tuple a) kw ns = true := by
    intro kw ns h3 h4
    cases kw <;> cases ns <;> simp_all [stateShapeOk, StArgs.raw]
  constructor
  · simp only [unpickleWith, hr1, pReduceC]
    cases d with
    | none =>
      simp only [setstateC, hsh (.exact k) .none (by simp) (by simp), Bool.not_true,
        Bool.false_eq_true, ite_false, StArgs.raw, h2]
    | some x =>
      simp only [setstateC, hsh (.exact k) (.dict x) (by simp) (by simp), Bool.not_true,
        Bool.false_eq_true, ite_false, StArgs.raw, h2]
  · simp only [unpickleWith, hr2, pReducePy]
    have hkw : ∀ (ns : StNs α), ns ≠ .other →
        (setstatePy o (.four f (.tuple a) (if k.isEmpty then .none else .exact k) ns)) =
        .ok (.pobj o (some (match ns with
          | .dict x => x
          | _ => [])) f a k (phCount a)) := by
      intro ns hns
      cases k with
      | nil =>
        have hs := hsh .none ns (by simp) hns
        simp only [List.isEmpty_nil, ite_true, setstatePy, hs, Bool.not_true,
          Bool.false_eq_true, ite_false, StArgs.raw, h2, pyHead_honest]
        rfl
      | cons p ps =>
        have hs := hsh (.exact (p :: ps)) ns (by simp) hns
        simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false, setstatePy,
          hs, Bool.not_true, StArgs.raw, h2, pyHead_honest]
        rfl
    cases d with
    | none => simpa using hkw .none (by simp)
    | some x =>
      cases x with
      | nil => simpa using hkw .none (by simp)
      | cons p ps => simpa using hkw (.dict (p :: ps)) (by simp)

/-! ### `repr` -/

theorem reprFold_ok {β : Type} (f : β → Py String) (r : β → String) (h : ∀ x, f x = .ok (r x)) :
    ∀ (l : List β) (acc : String), reprFold f acc l = .ok ((l.map r).foldl (fun a x => a ++ ", " ++ x) acc)
  | [], _ => rfl
  | x :: xs, acc => by
    simp only [reprFold, h, List.map_cons, List.foldl_cons]
    exact reprFold_ok f r h xs _

theorem mapPy_ok {β : Type} (f : β → Py String) (r : β → String) (h : ∀ x, f x = .ok (r x)) :
    ∀ l : List β, mapPy f l = .ok (l.map r)
  | [] => rfl
  | x :: xs => by
    simp only [mapPy, h, bind, Except.bind, mapPy_ok f r h xs, pure, Except.pure, List.map_cons]

theorem fold_append (l : List String) : ∀ s t : String,
    l.foldl (fun a x => a ++ ", " ++ x) (s ++ t) = s ++ l.foldl (fun a x => a ++ ", " ++ x) t := by
  induction l with
  | nil => intro s t; rfl
  | cons x xs ih =>
    intro s t
    simp only [List.foldl_cons]
    rw [← ih, String.append_assoc, String.append_assoc, String.append_assoc]

/-- `repr(partial)` is the same string in both twins, for all stored arguments and keywords, when no `repr`
raises: the class, then the function, the arguments and the keywords in order. Twin property of
`_partial_repr` and `partial_repr`. -/
def PartialReprTwins : Prop :=
  ∀ (α : Type) (r : α → String) (cls f : String) (args : List (PArg α)) (kw : List (String × α)),
    let E : ReprEnv α := ⟨fun a => .ok (r a)⟩
    partialReprPy E cls (.ok f) args kw = partialReprC E cls (.ok f) args kw

theorem partialReprTwins_proven : PartialReprTwins := by
  intro α r cls f args kw E
  let ra : PArg α → String := fun a => match a with
    | .ph => "Placeholder"
    | .val v => r v
  have h1 : ∀ a, argRepr E a = .ok (ra a) := by
    intro a
    cases a <;> rfl
  let rk : String × α → String := fun p => p.1 ++ "=" ++ r p.2
  have h2 : ∀ p : String × α, kwRepr E p = .ok (rk p) := fun _ => rfl
  simp only [partialReprPy, partialReprC, bind, Except.bind, mapPy_ok _ ra h1, mapPy_ok _ rk h2,
    reprFold_ok _ ra h1, reprFold_ok _ rk h2, pure, Except.pure, joinComma, List.cons_append]
  rw [List.foldl_append]
  have e1 := fold_append (args.map ra) f ""
  rw [String.append_empty] at e1
  rw [e1, fold_append]
  simp only [String.append_assoc]

/-- Both `repr`s raise the same exception. False: Python evaluates `repr(self.func)` first and C last, so with
two raising `repr`s the twins report different ones. -/
def PartialReprOrderAlways : Prop :=
  ∀ (E : ReprEnv Nat) (func : Py String) (args : List (PArg Nat)),
    partialReprPy E "functools.partial" func args [] = partialReprC E "functools.partial" func args []

theorem partialReprOrderAlways_refuted : ¬PartialReprOrderAlways := by
  intro h
  have := h ⟨fun _ => .error (.valueError "arg")⟩ (.error (.valueError "func")) [.val 1]
  revert this
  decide

/-- A `partial` holding itself prints `...` at that place in both twins, instead of recursing: the element's
`repr` re-enters the guard with the object already running. -/
def PartialReprSelfReference : Prop :=
  ∀ (body : Py String) (s : Nat) (cls f : String),
    let E : ReprEnv Nat := ⟨fun _ => reprGuard true body⟩
    partialReprPy E cls (.ok f) [.val s] [] = .ok (cls ++ "(" ++ f ++ ", ..." ++ ")") ∧
    partialReprC E cls (.ok f) [.val s] [] = .ok (cls ++ "(" ++ f ++ ", ..." ++ ")")

theorem partialReprSelfReference_proven : PartialReprSelfReference := by
  intro body s cls f
  constructor
  · simp [partialReprPy, mapPy, argRepr, reprGuard, bind, Except.bind, pure, Except.pure, joinComma,
      String.append_assoc]
  · simp [partialReprC, reprFold, argRepr, reprGuard, bind, Except.bind, pure, Except.pure,
      String.append_assoc]

/-! ### `Placeholder` -/

/-- `Placeholder()` is one object: from any state a second construction returns the identity of the first,
allocates nothing, and the C and Python `__new__` agree on it. C refuses arguments. Subclassing raises
`TypeError` in both, naming the new class in Python and the base in C. Object identity is modelled by the heap
counter, so a `__new__` allocating each time would fail this. -/
def PlaceholderSingleton : Prop :=
  ∀ (s : PhState) (n : Nat) (name : String),
    (placeholderNewPy (placeholderNewPy s).2).1 = (placeholderNewPy s).1 ∧
    (placeholderNewPy (placeholderNewPy s).2).2 = (placeholderNewPy s).2 ∧
    placeholderNewC 0 s = .ok (placeholderNewPy s) ∧
    (n ≠ 0 → (placeholderNewC n s).raises "TypeError") ∧
    placeholderSubclassPy name = .typeError ("type '" ++ name ++ "' is not an acceptable base type") ∧
    placeholderSubclassC = .typeError "type 'functools._PlaceholderType' is not an acceptable base type" ∧
    placeholderSubclassPy "Sub" ≠ placeholderSubclassC

theorem placeholderSingleton_proven : PlaceholderSingleton := by
  intro s n name
  refine ⟨?_, ?_, ?_, ?_, ?_, rfl, by decide⟩
  · cases h : s.inst <;> simp [placeholderNewPy, h]
  · cases h : s.inst <;> simp [placeholderNewPy, h]
  · cases h : s.inst <;> simp [placeholderNewC, placeholderNewPy, h]
  · intro hn
    exact ⟨_, by simp [placeholderNewC, hn]; rfl, rfl⟩
  · simp [placeholderSubclassPy, String.append_assoc]
    rfl

/-! ### `_unwrap_partial` and `_unwrap_partialmethod` -/

/-- `_unwrap_partial` removes every `partial` layer, whatever the nesting. -/
def UnwrapRemovesPartials : Prop :=
  ∀ (α : Type) (f : Fn α), ∀ o d g a k p, unwrapPartial f ≠ .pobj o d g a k p

theorem unwrapRemovesPartials_proven : UnwrapRemovesPartials := by
  intro α f
  induction f with
  | base id => intro _ _ _ _ _ _; simp [unwrapPartial]
  | notCallable => intro _ _ _ _ _ _; simp [unwrapPartial]
  | fails e => intro _ _ _ _ _ _; simp [unwrapPartial]
  | bound g s ih => intro _ _ _ _ _ _; simp [unwrapPartial]
  | pobj o d g a k p ih => simpa [unwrapPartial] using ih

/-- Neither a `partial`, nor a `partialmethod`, nor an object with a `__partialmethod__` that is one. -/
def Unwrapped : UObj → Prop
  | .part _ | .pm _ => False
  | .method a => a.isPm = false
  | _ => True

theorem stripParts_false : ∀ (n : Nat) (f r : UObj), 0 < n → stripParts n f = (r, false) →
    r = f ∧ (∀ g, f ≠ .part g)
  | 0, _, _, h, _ => by omega
  | n + 1, f, r, _, h => by
    cases f with
    | part g => simp [stripParts] at h
    | leaf i => simp only [stripParts, Prod.mk.injEq] at h; exact ⟨h.1.symm, by simp⟩
    | pm g => simp only [stripParts, Prod.mk.injEq] at h; exact ⟨h.1.symm, by simp⟩
    | method g => simp only [stripParts, Prod.mk.injEq] at h; exact ⟨h.1.symm, by simp⟩
    | bad m => simp only [stripParts, Prod.mk.injEq] at h; exact ⟨h.1.symm, by simp⟩

theorem stripPms_false : ∀ (n : Nat) (f r : UObj), 0 < n → stripPms n f = (r, false) →
    r = f ∧ (∀ g, f ≠ .pm g)
  | 0, _, _, h, _ => by omega
  | n + 1, f, r, _, h => by
    cases f with
    | pm g => simp [stripPms] at h
    | leaf i => simp only [stripPms, Prod.mk.injEq] at h; exact ⟨h.1.symm, by simp⟩
    | part g => simp only [stripPms, Prod.mk.injEq] at h; exact ⟨h.1.symm, by simp⟩
    | method g => simp only [stripPms, Prod.mk.injEq] at h; exact ⟨h.1.symm, by simp⟩
    | bad m => simp only [stripPms, Prod.mk.injEq] at h; exact ⟨h.1.symm, by simp⟩

theorem stripMethods_false : ∀ (n : Nat) (f r : UObj), stripMethods n f = .ok (r, false) →
    r = f ∧ (∀ a, f = .method a → a.isPm = false)
  | 0, _, _, h => by simp [stripMethods] at h
  | n + 1, f, r, h => by
    cases f with
    | leaf i =>
      simp only [stripMethods, Except.ok.injEq, Prod.mk.injEq] at h
      exact ⟨h.1.symm, by simp⟩
    | part g =>
      simp only [stripMethods, Except.ok.injEq, Prod.mk.injEq] at h
      exact ⟨h.1.symm, by simp⟩
    | pm g =>
      simp only [stripMethods, Except.ok.injEq, Prod.mk.injEq] at h
      exact ⟨h.1.symm, by simp⟩
    | bad e => simp [stripMethods] at h
    | method a =>
      simp only [stripMethods] at h
      split at h
      · split at h
        · cases h
        · cases h
      · next hp =>
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        exact ⟨h.1.symm, fun b hb => by cases hb; simpa using hp⟩

/-- `_unwrap_partialmethod` returns only an object that has nothing left to unwrap, however the three kinds of
layer alternate; a failing `__partialmethod__` read is an exception of the call. -/
def UnwrapPartialmethodDone : Prop :=
  ∀ (fuel : Nat) (f r : UObj), unwrapPartialmethod fuel f = .ok r → Unwrapped r

theorem unwrapPartialmethodDone_proven : UnwrapPartialmethodDone := by
  intro fuel
  induction fuel with
  | zero => intro f r h; simp [unwrapPartialmethod] at h
  | succ n ih =>
    intro f r h
    simp only [unwrapPartialmethod] at h
    split at h
    · cases h
    · next f1 m1 h1 =>
      generalize hs2 : stripPms (f1.size + 1) f1 = s2 at h
      obtain ⟨f2, m2⟩ := s2
      generalize hs3 : stripParts (f2.size + 1) f2 = s3 at h
      obtain ⟨f3, m3⟩ := s3
      simp only at h
      split at h
      · exact ih _ _ h
      · next hm =>
        have hm' : m1 = false ∧ m2 = false ∧ m3 = false := by
          simpa [Bool.or_eq_true, and_assoc] using hm
        obtain ⟨rfl, rfl, rfl⟩ := hm'
        simp only [Except.ok.injEq] at h
        subst h
        obtain ⟨e3, p3⟩ := stripParts_false _ _ _ (by omega) hs3
        obtain ⟨e2, p2⟩ := stripPms_false _ _ _ (by omega) hs2
        obtain ⟨e1, p1⟩ := stripMethods_false _ _ _ h1
        subst e1
        subst e2
        subst e3
        cases f3 with
        | leaf i => trivial
        | bad e => trivial
        | part g => exact p3 g rfl
        | pm g => exact p2 g rfl
        | method a => exact p1 a rfl

theorem stripMethods_size : ∀ (n : Nat) (f r : UObj), stripMethods n f = .ok (r, true) → r.size < f.size
  | 0, _, _, h => by simp [stripMethods] at h
  | n + 1, f, r, h => by
    cases f with
    | leaf i => simp [stripMethods] at h
    | part g => simp [stripMethods] at h
    | pm g => simp [stripMethods] at h
    | bad e => simp [stripMethods] at h
    | method a =>
      simp only [stripMethods] at h
      split at h
      · split at h
        · cases h
        · next q hq =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          obtain ⟨r1, b⟩ := q
          cases b with
          | true =>
            have := stripMethods_size n a r1 hq
            simp only [UObj.size]
            omega
          | false =>
            have := (stripMethods_false n a r1 hq).1
            subst this
            simp only [UObj.size]
            omega
      · simp at h

theorem stripPms_size : ∀ (n : Nat) (f : UObj), (stripPms n f).1.size ≤ f.size ∧
    ((stripPms n f).2 = true → (stripPms n f).1.size < f.size)
  | 0, f => by simp [stripPms]
  | n + 1, f => by
    cases f with
    | pm g =>
      have := (stripPms_size n g).1
      simp only [stripPms, UObj.size]
      exact ⟨by omega, fun _ => by omega⟩
    | _ => simp [stripPms]

theorem stripParts_size : ∀ (n : Nat) (f : UObj), (stripParts n f).1.size ≤ f.size ∧
    ((stripParts n f).2 = true → (stripParts n f).1.size < f.size)
  | 0, f => by simp [stripParts]
  | n + 1, f => by
    cases f with
    | part g =>
      have := (stripParts_size n g).1
      simp only [stripParts, UObj.size]
      exact ⟨by omega, fun _ => by omega⟩
    | _ => simp [stripParts]

/-- The loop ends: with fuel the size of the object, `_unwrap_partialmethod` never runs out, because each pass
that moves makes the object smaller. A self-referencing `partial` would loop, but it cannot be written as a `UObj`. -/
def UnwrapPartialmethodEnds : Prop :=
  ∀ (fuel : Nat) (f : UObj), f.size + 1 ≤ fuel → unwrapPartialmethod fuel f ≠ .error .modelFuel

theorem stripMethods_fuel : ∀ (n : Nat) (f : UObj), f.size < n → stripMethods n f ≠ .error .modelFuel
  | 0, _, h => by omega
  | n + 1, f, h => by
    cases f with
    | leaf i => simp [stripMethods]
    | part g => simp [stripMethods]
    | pm g => simp [stripMethods]
    | bad e => simp [stripMethods]
    | method a =>
      simp only [stripMethods]
      split
      · have := stripMethods_fuel n a (by simp only [UObj.size] at h; omega)
        split
        · next e he =>
          intro hc
          simp only [Except.error.injEq] at hc
          subst hc
          exact this he
        · simp
      · simp

theorem unwrapPartialmethodEnds_proven : UnwrapPartialmethodEnds := by
  intro fuel
  induction fuel with
  | zero => intro f h; omega
  | succ n ih =>
    intro f h
    simp only [unwrapPartialmethod]
    have hsm := stripMethods_fuel (f.size + 1) f (by omega)
    split
    · next e he =>
      intro hc
      simp only [Except.error.injEq] at hc
      subst hc
      exact hsm he
    · next f1 m1 h1 =>
      have h1s : f1.size ≤ f.size ∧ (m1 = true → f1.size < f.size) := by
        cases m1 with
        | true =>
          have := stripMethods_size _ _ _ h1
          exact ⟨by omega, fun _ => this⟩
        | false =>
          have := (stripMethods_false _ _ _ h1).1
          subst this
          exact ⟨by omega, by simp⟩
      have h2s := stripPms_size (f1.size + 1) f1
      generalize hs2 : stripPms (f1.size + 1) f1 = s2 at h2s
      obtain ⟨f2, m2⟩ := s2
      have h3s := stripParts_size (f2.size + 1) f2
      generalize hs3 : stripParts (f2.size + 1) f2 = s3 at h3s
      obtain ⟨f3, m3⟩ := s3
      simp only at h2s h3s ⊢
      split
      · next hm =>
        apply ih
        have hany : m1 = true ∨ m2 = true ∨ m3 = true := by simpa [Bool.or_eq_true, or_assoc] using hm
        have : f3.size < f.size := by
          rcases hany with hm | hm | hm
          · have := h1s.2 hm; omega
          · have := h2s.2 hm; omega
          · have := h3s.2 hm; omega
        omega
      · simp

/-! ### `partialmethod` -/

theorem methodCall_spec {α : Type} (u : UMethod α) (first : α) (args : List α) (kw : List (String × α))
    (hph : u.self.phcount = phCount u.self.args) :
    methodCall u first args kw =
      if u.self.phcount ≠ 0 ∧ args.length < u.self.phcount then
        .error (.typeError (missingMethodMsg u.self.phcount args.length))
      else callKind u.self.func.kind (first :: fillCall u.self.args args) (mergeKw u.self.keywords kw) := by
  simp only [methodCall, hph]
  by_cases h0 : phCount u.self.args = 0
  · simp only [h0, ne_eq, not_true_eq_false, ite_false, false_and, List.cons_append]
    rw [fillCall_no_ph _ _ h0]
  · have hm := itemget_merger u.self.args (args.map PArg.val)
    simp only [h0, ne_eq, not_false_eq_true, ite_true, true_and, prepareMerger_some _ h0, hm,
      List.length_map]
    by_cases hl : args.length < phCount u.self.args
    · have h1 : ¬ phCount u.self.args ≤ args.length := by omega
      simp [hl, h1]
    · have h1 : phCount u.self.args ≤ args.length := by omega
      simp only [h1, hl, ite_true, ite_false, List.cons_append]
      rw [fillCall_eq_takeFill _ _ h1]

/-- A `partialmethod` that is well formed: type invariant. -/
def PmWf {α : Type} (p : PMeth α) : Prop := PWf p.args p.phcount

theorem kwVals_map {α : Type} (l : List (String × α)) :
    kwVals (l.map (fun q => (q.1, PArg.val q.2))) = some l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [kwVals, List.map_cons, List.mapM_cons] at ih ⊢
    simp [ih]

theorem newBound_call {α : Type} (p : PMeth α) (nf : Fn α) (hw : PmWf p) (args : List α)
    (kw : List (String × α)) (hn : ∀ o d g a k ph, nf ≠ .pobj o d g a k ph) (hc : nf.isCallable = true) :
    ∀ (new : PartialNew α), (new = partialNewC ∨ new = partialNewPy) → ∃ r,
      new none nf p.args (p.keywords.map (fun q => (q.1, .val q.2))) = .ok r ∧
      callFn r args kw =
        if args.length < p.phcount then .error (.typeError (missingMsg p.phcount args.length))
        else callFn nf (fillCall p.args args) (mergeKw p.keywords kw) := by
  intro new hnew
  obtain ⟨h1, h2⟩ := hw
  have hflat : ∀ (x : Nat), x = phCount p.args → callFn (.pobj none none nf p.args p.keywords x) args kw =
      if args.length < p.phcount then .error (.typeError (missingMsg p.phcount args.length))
      else callFn nf (fillCall p.args args) (mergeKw p.keywords kw) := by
    intro x hx
    simp [callFn, hx, h1]
  rcases hnew with rfl | rfl
  · refine ⟨.pobj none none nf p.args p.keywords (phCount p.args), ?_, hflat _ rfl⟩
    have hf : flattenC none nf p.args p.keywords = .pobj none none nf p.args p.keywords (phCount p.args) := by
      cases nf with
      | pobj o d g a k ph => exact (hn _ _ _ _ _ _ rfl).elim
      | _ => rfl
    simp [partialNewC, validateNew, hc, h2, kwVals_map, bind, Except.bind, pure, Except.pure, hf]
  · refine ⟨.pobj none none nf p.args p.keywords (phCount p.args), ?_, hflat _ rfl⟩
    cases nf with
    | pobj o d g a k ph => exact (hn _ _ _ _ _ _ rfl).elim
    | notCallable => simp [Fn.isCallable] at hc
    | base id => simp [partialNewPy, Fn.isCallable, newCore, h2, kwVals_map, prepareMerger_count]
    | fails e => simp [partialNewPy, Fn.isCallable, newCore, h2, kwVals_map, prepareMerger_count]
    | bound g s => simp [partialNewPy, Fn.isCallable, newCore, h2, kwVals_map, prepareMerger_count]

/-- `pmBound` then a call. -/
theorem pmBound_call {α : Type} (p : PMeth α) (nf : Fn α) (self : Option α) (hw : PmWf p) (args : List α)
    (kw : List (String × α)) (hn : ∀ o d g a k ph, nf ≠ .pobj o d g a k ph) (hc : nf.isCallable = true)
    (new : PartialNew α) (hnew : new = partialNewC ∨ new = partialNewPy) :
    (do callGot (← pmBound new p nf (.ok self)) args kw) =
      if args.length < p.phcount then .error (.typeError (missingMsg p.phcount args.length))
      else callFn nf (fillCall p.args args) (mergeKw p.keywords kw) := by
  obtain ⟨r, h1, h2⟩ := newBound_call p nf hw args kw hn hc new hnew
  have hset : ∀ (r : Fn α) (v : α), callFn (setSelf r v) args kw = callFn r args kw := by
    intro r v
    cases r with
    | pobj o d g a k p => cases o <;> rfl
    | _ => rfl
  simp only [pmBound, h1]
  cases self with
  | none => simpa [bind, Except.bind, callGot] using h2
  | some v => simpa [bind, Except.bind, callGot, hset] using h2

/-- `obj.m(*args)` and `Cls.m(...)` through `partialmethod.__get__`, by what `self.func` is, for every
placeholder pattern with enough arguments, and with either `partial`:
a plain function binds the instance, and through the class takes its first argument from the call; a
`classmethod` binds the owner from both; a `staticmethod` binds nothing. The first two go through
`partial(new_func, ...)` on an instance and through `_method` on the class. The docs' "will be
called with ... as a method". `PmWf` is a type invariant. -/
def PartialmethodKinds : Prop :=
  ∀ (α : Type) (new : PartialNew α), (new = partialNewC ∨ new = partialNewPy) →
  ∀ (a : Option α) (id : Nat) (pargs : List (PArg α)) (pkw kw : List (String × α)) (ph : Nat)
    (o c x : α) (args : List α), PWf pargs ph → ph ≤ args.length →
    let call := Except.ok (ε := PyExc) (Called.mk id (fillCall pargs args) (mergeKw pkw kw))
    let first (v : α) : Py (Called α) := .ok ⟨id, v :: fillCall pargs args, mergeKw pkw kw⟩
    (do callGot (← pmGet new ⟨⟨.fn id, .ok a, none, none⟩, pargs, pkw, ph⟩ (some o) c) args kw) = first o ∧
    (do callGot (← pmGet new ⟨⟨.fn id, .ok a, none, none⟩, pargs, pkw, ph⟩ none c) (x :: args) kw) = first x ∧
    (do callGot (← pmGet new ⟨⟨.classm id, .ok a, none, none⟩, pargs, pkw, ph⟩ (some o) c) args kw) = first c ∧
    (do callGot (← pmGet new ⟨⟨.classm id, .ok a, none, none⟩, pargs, pkw, ph⟩ none c) args kw) = first c ∧
    (do callGot (← pmGet new ⟨⟨.staticm id, .ok a, none, none⟩, pargs, pkw, ph⟩ (some o) c) args kw) = call ∧
    (do callGot (← pmGet new ⟨⟨.staticm id, .ok a, none, none⟩, pargs, pkw, ph⟩ none c) args kw) = call

theorem partialmethodKinds_proven : PartialmethodKinds := by
  intro α new hnew a id pargs pkw kw ph o c x args hw hl call first
  have hnl : ¬ args.length < ph := by omega
  have hb : ∀ (kind : MKind α) (nf : Fn α) (self : Option α),
      (∀ o d g a k ph, nf ≠ .pobj o d g a k ph) → nf.isCallable = true →
      (do callGot (← pmBound new ⟨{ kind := kind, abstract := .ok a }, pargs, pkw, ph⟩ nf (.ok self)) args kw) =
        callFn nf (fillCall pargs args) (mergeKw pkw kw) := by
    intro kind nf self h1 h2
    have := pmBound_call ⟨{ kind := kind, abstract := .ok a }, pargs, pkw, ph⟩ nf self hw args kw h1 h2 new hnew
    simpa [hnl] using this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [pmGet, callFn, first] using hb (.fn id) (.bound (.base id) o) (some o) (by simp) rfl
  · have hm := methodCall_spec ⟨⟨⟨.fn id, .ok a, none, none⟩, pargs, pkw, ph⟩, a⟩ x args kw hw.1
    dsimp only at hm
    simp [pmGet, pmUnbound, makeUnbound, bind, Except.bind, callGot, hm, hnl, callKind, first]
  · simpa [pmGet, callFn, first] using hb (.classm id) (.bound (.base id) c) (some c) (by simp) rfl
  · simpa [pmGet, callFn, first] using hb (.classm id) (.bound (.base id) c) (some c) (by simp) rfl
  · simpa [pmGet, callFn, call] using hb (.staticm id) (.base id) none (by simp) rfl
  · simpa [pmGet, callFn, call] using hb (.staticm id) (.base id) none (by simp) rfl

/-- `Cls.m` reads `__isabstractmethod__` through `_make_unbound_method`, so an exception from that read
propagates; `obj.m` for a plain function does not read it. A `__get__` that raises propagates from either. -/
def PartialmethodAbstractRead : Prop :=
  ∀ (α : Type) (new : PartialNew α) (e : PyExc) (id : Nat) (pargs : List (PArg α)) (pkw : List (String × α))
    (ph : Nat) (c : α),
    pmGet new ⟨⟨.fn id, .error e, none, none⟩, pargs, pkw, ph⟩ none c = .error e ∧
    (∀ (s : Py (Option α)) (call : Fn α) (ab : Py (Option α)) (obj : Option α),
      pmGet new ⟨⟨.custom (fun _ => .error e) s call, ab, none, none⟩, pargs, pkw, ph⟩ obj c = .error e) ∧
    (∀ (u : UMethod α) (p : PMeth α) (a : Option α), makeUnbound p = .ok u →
      p.func.abstract = .ok a → u.self = p ∧ u.isAbstract = a)

theorem partialmethodAbstractRead_proven : PartialmethodAbstractRead := by
  intro α new e id pargs pkw ph c
  refine ⟨rfl, fun _ _ _ _ => rfl, ?_⟩
  intro u p a h1 h2
  simp only [makeUnbound, h2, Except.ok.injEq] at h1
  subst h1
  exact ⟨rfl, rfl⟩

theorem nested_args {α : Type} (pargs args : List (PArg α)) (ph : Nat) (more : List α)
    (hph : ph = phCount pargs) (hm : phCount args ≤ more.length) :
    let tot := if ph = 0 then pargs ++ args else fill pargs args
    fillCall tot more = fillCall pargs (fillCall args more) ∧
      (more.length < phCount tot ↔ (fillCall args more).length < ph) := by
  have hlen := length_fillCall args more hm
  have hle := phCount_le args
  by_cases h0 : ph = 0
  · have hp : phCount pargs = 0 := by omega
    simp only [h0, ite_true, phCount_append, hp, Nat.zero_add]
    rw [← fillCall_fill pargs args more hm, fill_no_ph pargs args hp]
    exact ⟨rfl, by omega⟩
  · simp only [h0, ite_false]
    refine ⟨fillCall_fill pargs args more hm, ?_⟩
    rw [phCount_fill, ← hph]
    omega

/-- `partialmethod(pm, *args)` flattens as `partial` does, through the same body: the new object called with
`more` is `pm` called with `more` in the slots of `args`, for every placeholder pattern on both levels, or
both raise `TypeError`. No keywords at either level, as in `PartialNestedPositional`. -/
def PartialmethodNested : Prop :=
  ∀ (α : Type) (t : MTarget α) (pargs args : List (PArg α)) (ph : Nat) (first : α) (more : List α),
    PWf pargs ph → trailingPh args = false → phCount args ≤ more.length → ∃ q,
      partialmethodNew (.pm ⟨t, pargs, [], ph⟩) args [] = .ok q ∧ ∀ a : Option α,
        sameOrTypeError (methodCall ⟨q, a⟩ first more [])
          (methodCall ⟨⟨t, pargs, [], ph⟩, a⟩ first (fillCall args more) [])

theorem partialmethodNested_proven : PartialmethodNested := by
  intro α t pargs args ph first more hw ht hm
  have hk : kwVals ([] : List (String × PArg α)) = some [] := rfl
  have hn := newCore_inner args pargs [] [] [] ph hw.1 ht hk
  simp only [partialmethodNew, hn]
  by_cases he : args.isEmpty = true
  · have hnil : args = [] := by simpa using he
    subst hnil
    exact ⟨⟨t, pargs, mergeKw [] [], ph⟩, rfl, fun a => Or.inl rfl⟩
  · simp only [he, Bool.false_eq_true, ite_false]
    obtain ⟨h1, h2⟩ := nested_args pargs args ph more hw.1 hm
    generalize htot : (if ph = 0 then pargs ++ args else fill pargs args) = tot at h1 h2
    refine ⟨⟨t, tot, mergeKw [] [], phCount tot⟩, rfl, fun a => ?_⟩
    rw [methodCall_spec ⟨⟨t, tot, _, _⟩, a⟩ first more [] rfl,
      methodCall_spec ⟨⟨t, pargs, [], ph⟩, a⟩ first _ [] hw.1]
    simp only [mergeKw, List.foldl_nil]
    by_cases hl : more.length < phCount tot
    · have h3 := h2.mp hl
      have c1 : phCount tot ≠ 0 := by omega
      have c2 : ph ≠ 0 := by omega
      right
      exact ⟨⟨_, by simp [hl, c1]; rfl, rfl⟩, ⟨_, by simp [h3, c2]; rfl, rfl⟩⟩
    · have h3 : ¬ (fillCall args more).length < ph := fun x => hl (h2.mpr x)
      left
      simp [hl, h3, h1]

/-- `partialmethod(obj)` raises `TypeError` for an object neither callable nor a descriptor, before anything else; but an
exception from `hasattr(func, "__get__")`, and one from the `repr` in the message, comes out in place of it. -/
def PartialmethodRejects : Prop :=
  ∀ (α : Type) (t : MTarget α) (args : List (PArg α)) (kw : List (String × PArg α)) (e : PyExc),
    t.kind.isCallable = false →
    (t.getFail = some e → partialmethodNew (.target t) args kw = .error e) ∧
    (t.getFail = none → t.kind.hasGet = false →
      (t.reprFail = none → (partialmethodNew (.target t) args kw).raises "TypeError") ∧
      (t.reprFail = some e → partialmethodNew (.target t) args kw = .error e))

theorem partialmethodRejects_proven : PartialmethodRejects := by
  intro α t args kw e h1
  refine ⟨?_, ?_⟩
  · intro h
    simp [partialmethodNew, h1, h]
  · intro h h2
    refine ⟨?_, ?_⟩
    · intro h3
      exact ⟨.typeError "~the first argument must be a callable or a descriptor", by
        simp [partialmethodNew, h1, h, h2, h3], rfl⟩
    · intro h3
      simp [partialmethodNew, h1, h, h2, h3]

/-- The twins of `partial` take the same objects apart. False: `isinstance` in Python goes through `__class__`, so an object
that claims to be a `partial` is flattened, where `PyObject_TypeCheck` in C leaves it as the function. -/
def PartialNewDuck : Prop :=
  ∀ (fake : Nat) (inner : Fn Nat) (pargs : List (PArg Nat)) (pkw : List (String × Nat)) (pph : Nat) (args : List (PArg Nat)),
    duckNewPy none inner pargs pkw pph args [] = partialNewC none (.base fake) args []

theorem partialNewDuck_refuted : ¬PartialNewDuck := by
  intro h
  have := h 9 (.base 1) [] [] 0 []
  revert this
  decide

/-- The full `repr` of a `partial`, in Python: the two reads from the class come first, and an exception from either stops
it before any `repr`; then `repr(self.func)`, the arguments and the keywords. -/
def PartialReprFull : Prop :=
  ∀ (α : Type) (E : ReprEnv α) (grows : α → Bool) (mod qual f : Py String) (args : List (PArg α)) (kw : List (String × α))
    (e : PyExc) (m q : String),
    (mod = .error e → partialReprFullPy E grows mod qual f args kw = .error e) ∧
    (mod = .ok m → qual = .error e → partialReprFullPy E grows mod qual f args kw = .error e) ∧
    (mod = .ok m → qual = .ok q → f = .error e → partialReprFullPy E grows mod qual f args kw = .error e) ∧
    ((∀ p ∈ kw, grows p.2 = false) → mod = .ok m → qual = .ok q →
      partialReprFullPy E grows mod qual f args kw = partialReprPy E (m ++ "." ++ q) f args kw)

private theorem kwLoop_noMut {α : Type} (E : ReprEnv α) (grows : α → Bool) :
    ∀ kw : List (String × α), (∀ p ∈ kw, grows p.2 = false) → kwLoopPy E grows kw = mapPy (kwRepr E) kw
  | [], _ => rfl
  | p :: r, h => by
    have h1 := h p (by simp)
    simp only [kwLoopPy, mapPy, bind, Except.bind]
    cases hk : kwRepr E p with
    | error e => rfl
    | ok s =>
      simp only [h1, Bool.false_eq_true, ↓reduceIte, kwLoop_noMut E grows r (fun q hq => h q (by simp [hq]))]
      cases mapPy (kwRepr E) r <;> rfl

theorem partialReprFull_proven : PartialReprFull := by
  intro α E grows mod qual f args kw e m q
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h; subst h; rfl
  · intro h1 h2; subst h1 h2; rfl
  · intro h1 h2 h3; subst h1 h2 h3; rfl
  · intro h1 h2 h3
    subst h2 h3
    simp only [partialReprFullPy, partialReprPy, kwLoop_noMut E grows kw h1, bind, Except.bind, pure, Except.pure]

/-- The twins of `repr` agree on keywords whose `repr` is harmless. False when one adds to `self.keywords`: the generator in
Python raises `RuntimeError` at its next step, where the `PyDict_Next` loop of C goes on. -/
def PartialReprMutation : Prop :=
  ∀ (E : ReprEnv Nat) (grows : Nat → Bool) (extra : String × Nat) (kw : List (String × Nat)) (x : String),
    (partialReprFullPy E grows (.ok "m") (.ok "p") (.ok x) [] kw).toOption.isSome = true ↔
      (partialReprFullC E grows extra "m.p" (.ok x) [] kw).toOption.isSome = true

theorem partialReprMutation_refuted : ¬PartialReprMutation := by
  intro h
  have := (h ⟨fun _ => .ok "v"⟩ (fun _ => true) ("z", 1) [("a", 1)] "f").2 (by decide)
  revert this
  decide

/-- A `partial` holding itself prints `...` at each such place in both twins, wherever it is among the arguments and whatever
the other arguments print: `none` stands for the partial, whose `repr` meets the guard already set. -/
def selfEnv {α : Type} (s : α → String) : ReprEnv (Option α) :=
  ⟨fun v => match v with
    | none => reprGuard true (.error .modelFuel)
    | some a => .ok (s a)⟩

def selfShown {α : Type} (s : α → String) : PArg (Option α) → String
  | .ph => "Placeholder"
  | .val none => "..."
  | .val (some a) => s a

def PartialReprSelfAnywhere : Prop :=
  ∀ (α : Type) (s : α → String) (cls f : String) (args : List (PArg (Option α))),
    partialReprPy (selfEnv s) cls (.ok f) args [] = .ok (cls ++ "(" ++ joinComma (f :: args.map (selfShown s)) ++ ")") ∧
    partialReprC (selfEnv s) cls (.ok f) args [] =
      .ok (cls ++ "(" ++ f ++ (args.map (selfShown s)).foldl (fun a x => a ++ ", " ++ x) "" ++ ")")

private theorem self_args {α : Type} (s : α → String) : ∀ args : List (PArg (Option α)),
    mapPy (argRepr (selfEnv s)) args = .ok (args.map (selfShown s))
  | [] => rfl
  | a :: r => by
    have ih := self_args s r
    have ha : argRepr (selfEnv s) a = .ok (selfShown s a) := by
      cases a with
      | ph => rfl
      | val v =>
        cases v <;> rfl
    simp [mapPy, ha, ih, bind, Except.bind, pure, Except.pure]

private theorem self_fold {α : Type} (s : α → String) : ∀ (args : List (PArg (Option α))) (acc : String),
    reprFold (argRepr (selfEnv s)) acc args = .ok ((args.map (selfShown s)).foldl (fun a x => a ++ ", " ++ x) acc)
  | [], _ => rfl
  | a :: r, acc => by
    have ha : argRepr (selfEnv s) a = .ok (selfShown s a) := by
      cases a with
      | ph => rfl
      | val v =>
        cases v <;> rfl
    simp only [reprFold, ha, List.map_cons, List.foldl_cons]
    exact self_fold s r _

theorem partialReprSelfAnywhere_proven : PartialReprSelfAnywhere := by
  intro α s cls f args
  constructor
  · simp [partialReprPy, self_args, mapPy, bind, Except.bind, pure, Except.pure]
  · simp only [partialReprC, self_fold, reprFold, bind, Except.bind, pure, Except.pure]

end PyLean.CoreLibs.Functools
