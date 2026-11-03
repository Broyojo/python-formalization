import PyLean.ListSort.FallibleBridge2

/-!
# `list.sort` with a comparison or key function that raises

The main loop and `list_sort_impl` with a comparison that never raises are the model's
(`SortFallibleAgree`), so the stability and count theorems about `listSortCnt` describe the success
path; a raising comparison or key function ends the sort as `goto fail` and `keyfunc_fail` do
(`SortFails`); and every outcome is a permutation (`SortPermOnError`).
-/

namespace PyLean.ListSort

open PyLean

variable {α : Type}

/-! ## The merge policy commutes with the embedding of the model's state -/

theorem mergeWhile_sim {σ τ : Type} (F : Nat → Nat → Nat → σ → σ) (G : Nat → Nat → Nat → τ → τ)
    (emb : σ → τ) (h : ∀ b na nb s, G b na nb (emb s) = emb (F b na nb s)) (p : Nat) :
    ∀ (n : Nat) (stk : List Slice) (s : σ), stk.length ≤ n →
      mergeWhile G p stk (emb s) = ((mergeWhile F p stk s).1, emb (mergeWhile F p stk s).2) := by
  intro n
  induction n with
  | zero => intro stk s hl; match stk with | [] => simp [mergeWhile]
  | succ n ih =>
    intro stk s hl
    match stk with
    | t :: u :: rest =>
      rw [mergeWhile, mergeWhile]
      by_cases hp : u.power > p
      · simp only [hp, ↓reduceIte]
        rw [h]
        exact ih _ _ (by simp at hl ⊢; omega)
      · simp only [hp, ↓reduceIte]
    | [t] => simp [mergeWhile]
    | [] => simp [mergeWhile]

theorem foundNewRun_sim {σ τ : Type} (F : Nat → Nat → Nat → σ → σ) (G : Nat → Nat → Nat → τ → τ)
    (emb : σ → τ) (h : ∀ b na nb s, G b na nb (emb s) = emb (F b na nb s)) (N n2 : Nat) (stk : List Slice)
    (s : σ) : foundNewRun G N n2 stk (emb s) = ((foundNewRun F N n2 stk s).1, emb (foundNewRun F N n2 stk s).2) := by
  unfold foundNewRun
  match stk with
  | [] => rfl
  | top :: rest =>
    simp only
    rw [mergeWhile_sim F G emb h _ _ (top :: rest) s (Nat.le_refl _)]
    generalize mergeWhile F (powerloop top.base top.len n2 N) (top :: rest) s = R
    obtain ⟨stk', s'⟩ := R
    cases stk' <;> rfl

theorem forceCollapse_sim {σ τ : Type} (F : Nat → Nat → Nat → σ → σ) (G : Nat → Nat → Nat → τ → τ)
    (emb : σ → τ) (h : ∀ b na nb s, G b na nb (emb s) = emb (F b na nb s)) :
    ∀ (n : Nat) (stk : List Slice) (s : σ), stk.length ≤ n →
      forceCollapse G stk (emb s) = ((forceCollapse F stk s).1, emb (forceCollapse F stk s).2) := by
  intro n
  induction n with
  | zero => intro stk s hl; match stk with | [] => simp [forceCollapse]
  | succ n ih =>
    intro stk s hl
    match stk with
    | t :: u :: v :: rest =>
      rw [forceCollapse, forceCollapse]
      by_cases hv : v.len < t.len
      · simp only [hv, ↓reduceIte]; rw [h]; exact ih _ _ (by simp at hl ⊢; omega)
      · simp only [hv, ↓reduceIte]; rw [h]; exact ih _ _ (by simp at hl ⊢; omega)
    | [t, u] => rw [forceCollapse, forceCollapse, h]; exact ih _ _ (by simp at hl ⊢; omega)
    | [t] => simp [forceCollapse]
    | [] => simp [forceCollapse]

/-- The model's merge state as a fallible one with no exception. -/
def embF (s : List α × MS) : FRes α := (s.1, s.2, none)

theorem mergeAtArrF_emb (f : α → α → Bool) (b na nb : Nat) (s : List α × MS) :
    mergeAtArrF (pureLt f) b na nb (embF s) = embF (mergeAtArr f b na nb s) := by
  obtain ⟨arr, ms⟩ := s
  exact mergeAtArrF_pure f b na nb arr ms

/-! ## The main loop -/

theorem sortStepF_pure (f : α → α → Bool) (N pos : Nat) (st : Sorter α) :
    sortStepF (pureLt f) N pos st = ((sortStep f N pos st).1, (sortStep f N pos st).2, none) := by
  simp only [sortStepF, sortStep, countRunF_pure]
  generalize countRun f (st.arr.drop pos) st.ms = CR
  obtain ⟨n0, rest0, ms0⟩ := CR
  simp only
  generalize minrunNext st.mr = MR
  obtain ⟨minrun, mr⟩ := MR
  simp only
  by_cases hn : n0 < minrun
  · simp only [hn, ↓reduceIte, binarysortF_pure]
    have := foundNewRun_sim (mergeAtArr f) (mergeAtArrF (pureLt f)) embF (mergeAtArrF_emb f) N
      (if N - pos ≤ minrun then N - pos else minrun) st.stk
      (st.arr.take pos ++ (binarysort f rest0 (if N - pos ≤ minrun then N - pos else minrun) n0 ms0).1,
        (binarysort f rest0 (if N - pos ≤ minrun then N - pos else minrun) n0 ms0).2)
    simp only [embF] at this
    rw [this]
  · simp only [hn, ↓reduceIte]
    have := foundNewRun_sim (mergeAtArr f) (mergeAtArrF (pureLt f)) embF (mergeAtArrF_emb f) N n0 st.stk
      (st.arr.take pos ++ rest0, ms0)
    simp only [embF] at this
    rw [this]

theorem sortLoopF_pure (f : α → α → Bool) (N : Nat) :
    ∀ (fuel pos : Nat) (st : Sorter α), sortLoopF (pureLt f) N fuel pos st = (sortLoop f N fuel pos st, none)
  | 0, _, _ => rfl
  | fuel + 1, pos, st => by
    simp only [sortLoopF, sortLoop, sortStepF_pure]
    generalize sortStep f N pos st = S
    obtain ⟨st', n⟩ := S
    simp only
    split
    · exact sortLoopF_pure f N fuel _ _
    · rfl

theorem sortCoreF_pure (f : α → α → Bool) (xs : List α) : sortCoreF (pureLt f) xs = (sortCore f xs, none) := by
  unfold sortCoreF sortCore
  dsimp only
  split
  · rfl
  · rw [sortLoopF_pure]
    simp only
    generalize sortLoop f xs.length xs.length 0 _ = st
    have := forceCollapse_sim (mergeAtArr f) (mergeAtArrF (pureLt f)) embF (mergeAtArrF_emb f) _
      st.stk (st.arr, st.ms) (Nat.le_refl _)
    simp only [embF] at this
    rw [this]

theorem listSortCntF_pure (f : α → α → Bool) (xs : List α) (reverse : Bool) :
    listSortCntF (pureLt f) xs reverse = ((listSortCnt f xs reverse).1, (listSortCnt f xs reverse).2, none) := by
  unfold listSortCntF listSortCnt
  split
  · rfl
  · simp only [sortCoreF_pure]

/-! ## The statements -/

/-- With a comparison that never raises, the fallible `binarysort`, `count_run`, `gallop_left`,
`gallop_right`, `merge_lo`, `merge_hi`, `merge_at` and the whole sort (`list_sort_impl` without a key)
compute exactly what the model computes, comparison count included, and report no exception; so the
stability, permutation, count and stack theorems about the model are theorems about this one. With a
key function that never raises and leaves the list alone, `list.sort(key=...)` is `listSortKey`. -/
def SortFallibleAgree : Prop :=
  ∀ (α κ : Type) (f : α → α → Bool) (xs A B : List α) (a : α) (get : Nat → α) (n m hint : Nat) (ms : MS)
    (reverse : Bool) (kf : α → κ) (g : κ → κ → Bool),
    binarysortF (pureLt f) xs n m ms = ((binarysort f xs n m ms).1, (binarysort f xs n m ms).2, none) ∧
    countRunF (pureLt f) xs ms = ((countRun f xs ms).1, (countRun f xs ms).2.1, (countRun f xs ms).2.2, none) ∧
    gallopLeftF (pureLt f) a get n hint ms = (.ok (gallopLeft f a get n hint ms).1, (gallopLeft f a get n hint ms).2) ∧
    gallopRightF (pureLt f) a get n hint ms = (.ok (gallopRight f a get n hint ms).1, (gallopRight f a get n hint ms).2) ∧
    mergeLoF (pureLt f) A B ms = ((mergeLo f A B ms).1, (mergeLo f A B ms).2, none) ∧
    mergeHiF (pureLt f) A B ms = ((mergeHi f A B ms).1, (mergeHi f A B ms).2, none) ∧
    mergeAtF (pureLt f) A B ms = ((mergeAt f A B ms).1, (mergeAt f A B ms).2, none) ∧
    listSortCntF (pureLt f) xs reverse = ((listSortCnt f xs reverse).1, (listSortCnt f xs reverse).2, none) ∧
    listSortImplF (pureLt f) xs reverse = (listSort f xs reverse, none) ∧
    listSortKeyImplF (pureLt g) (fun x u => (.ok (kf x), u)) xs reverse = (listSortKey kf g xs reverse, none)

theorem keysLoop_pure {κ β : Type} (kf : α → κ) :
    ∀ (xs : List α) (u : β) (acc : List κ),
      keysLoop (fun x u => (.ok (kf x), u)) xs u acc = (.ok (acc.reverse ++ xs.map kf), u)
  | [], u, acc => by simp [keysLoop]
  | x :: xs, u, acc => by
    simp only [keysLoop]
    rw [keysLoop_pure kf xs u (kf x :: acc)]
    simp

theorem zip_map_self {κ : Type} (kf : α → κ) (xs : List α) : (xs.map kf).zip xs = xs.map fun x => (kf x, x) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem sortFallibleAgree_proven : SortFallibleAgree := by
  intro α κ f xs A B a get n m hint ms reverse kf g
  refine ⟨binarysortF_pure f xs n m ms, countRunF_pure f xs ms, gallopLeftF_pure f a get n hint ms,
    gallopRightF_pure f a get n hint ms, mergeLoF_pure f A B ms, mergeHiF_pure f A B ms, mergeAtF_pure f A B ms,
    listSortCntF_pure f xs reverse, ?_, ?_⟩
  · simp only [listSortImplF, listSortCntF_pure, listSort]
  · simp only [listSortKeyImplF, keysLoop_pure, List.reverse_nil, List.nil_append, zip_map_self]
    have hp : (fun p q : κ × α => pureLt g p.1 q.1) = pureLt (fun p q : κ × α => g p.1 q.1) := rfl
    rw [hp, listSortCntF_pure]
    simp only [LView.during, ne_eq, Int.reduceNeg, not_true_eq_false, ↓reduceIte]
    rfl

/-- What a raising comparison or key function does to `list.sort`, for every list:

* a comparison that always raises is called once, by `count_run`'s first `IFLT` (:2004-2006); the sort
  stops and the list is unchanged, for `reverse=True` too (the reversal is undone on the way out,
  :3200-3201);
* a key function that raises on an item stops the key loop there (:3015-3021, `keyfunc_fail`): the
  list is unchanged and that exception propagates;
* a key function that changes the list it sees, which `list_sort_impl` emptied with `allocated = -1`
  (:2989-2994), makes a sort that otherwise succeeds raise `ValueError("list modified during sort")`
  (:3193-3199), and the list still holds the sorted items;
* `PyList_Sort` (:3231-3245) refuses a non-list with `SystemError`, and returns `-1` with the sort's
  exception when `list_sort_impl` fails. -/
def SortFails : Prop :=
  ∀ (α κ : Type) (e : PyExc) (xs : List α) (reverse : Bool) (g : κ → κ → Bool) (kf : α → κ)
    (key : α → LView α → Py κ × LView α),
    2 ≤ xs.length →
    listSortCntF (fun _ _ => (.error e : Py Bool)) xs reverse = (xs, 1, some e) ∧
    (∀ (pre : List α) (x : α) (post : List α) (u : LView α), xs = pre ++ x :: post →
      keysLoop key pre LView.during [] = (.ok (pre.map kf), u) → (key x u).1 = .error e →
      listSortKeyImplF (pureLt g) key xs reverse = (xs, some e)) ∧
    ((∀ x u, (key x u).1 = .ok (kf x)) → (∀ x u, ((key x u).2).allocated ≠ -1) →
      listSortKeyImplF (pureLt g) key xs reverse =
        (listSortKey kf g xs reverse, some (.valueError "list modified during sort"))) ∧
    pyListSortF (fun _ _ => (.error e : Py Bool)) (some xs) = (.error e, xs) ∧
    pyListSortF (fun _ _ => (.error e : Py Bool)) (none : Option (List α)) = (.error sortSystemError, [])

theorem sortCoreF_raise (e : PyExc) (ys : List α) (h : 2 ≤ ys.length) :
    (sortCoreF (fun _ _ => (.error e : Py Bool)) ys).1.arr = ys ∧
    (sortCoreF (fun _ _ => (.error e : Py Bool)) ys).1.ms.ncmp = 1 ∧
    (sortCoreF (fun _ _ => (.error e : Py Bool)) ys).2 = some e := by
  match ys, h with
  | y0 :: y1 :: rest, _ =>
    have hN : (y0 :: y1 :: rest).length = (rest.length + 1) + 1 := rfl
    unfold sortCoreF
    simp only [hN]
    rw [if_neg (by omega)]
    simp only [sortLoopF, sortStepF, List.drop_zero, countRunF, ascTakeF, isltF, List.take_zero,
      List.nil_append]
    refine ⟨?_, ?_, ?_⟩ <;> first | trivial | rfl

theorem keysLoop_append {κ β : Type} (key : α → β → Py κ × β) :
    ∀ (pre rest : List α) (u : β) (acc : List κ),
      keysLoop key (pre ++ rest) u acc =
        match keysLoop key pre u acc with
        | (.ok ks, u') => keysLoop key rest u' ks.reverse
        | (.error e, u') => (.error e, u')
  | [], rest, u, acc => by simp [keysLoop]
  | x :: pre, rest, u, acc => by
    simp only [List.cons_append, keysLoop]
    rcases hk : key x u with ⟨r, u'⟩
    rcases r with e | k
    · rfl
    · exact keysLoop_append key pre rest u' (k :: acc)

theorem keysLoop_mut {κ : Type} (key : α → LView α → Py κ × LView α) (kf : α → κ)
    (hk : ∀ x u, (key x u).1 = .ok (kf x)) (hm : ∀ x u, ((key x u).2).allocated ≠ -1) :
    ∀ (xs : List α) (u : LView α) (acc : List κ), xs ≠ [] →
      (keysLoop key xs u acc).1 = .ok (acc.reverse ++ xs.map kf) ∧ ((keysLoop key xs u acc).2).allocated ≠ -1
  | [], _, _, h => absurd rfl h
  | [x], u, acc, _ => by
    have h1 := hk x u
    have h2 := hm x u
    rcases hq : key x u with ⟨r, u'⟩
    rw [hq] at h1 h2
    simp only at h1 h2
    subst h1
    simp only [keysLoop, hq]
    exact ⟨by simp, h2⟩
  | x :: y :: xs, u, acc, _ => by
    have h1 := hk x u
    rcases hq : key x u with ⟨r, u'⟩
    rw [hq] at h1
    simp only at h1
    subst h1
    have := keysLoop_mut key kf hk hm (y :: xs) u' (kf x :: acc) (by simp)
    rw [keysLoop]
    simp only [hq]
    refine ⟨by rw [this.1]; simp, this.2⟩

theorem sortFails_proven : SortFails := by
  intro α κ e xs reverse g kf key hlen
  have hraise : ∀ rv, listSortCntF (fun _ _ => (.error e : Py Bool)) xs rv = (xs, 1, some e) := by
    intro rv
    unfold listSortCntF
    rw [if_neg (by omega)]
    simp only
    cases rv
    · obtain ⟨h1, h2, h3⟩ := sortCoreF_raise e xs hlen
      simp only [Bool.false_eq_true, ↓reduceIte]
      generalize sortCoreF _ xs = R at h1 h2 h3
      obtain ⟨st, er⟩ := R
      simp only at h1 h2 h3 ⊢
      rw [h1, h2, h3]
    · obtain ⟨h1, h2, h3⟩ := sortCoreF_raise e xs.reverse (by simpa using hlen)
      simp only [↓reduceIte]
      generalize sortCoreF _ xs.reverse = R at h1 h2 h3
      obtain ⟨st, er⟩ := R
      simp only at h1 h2 h3 ⊢
      rw [h1, h2, h3, List.reverse_reverse]
  refine ⟨hraise reverse, fun pre x post u hxs hpre hx => ?_, fun hk hm => ?_, ?_, rfl⟩
  · unfold listSortKeyImplF
    rw [hxs, keysLoop_append, hpre]
    simp only [keysLoop]
    have hp : key x u = (.error e, (key x u).2) := by rw [← hx]
    rw [hp]
  · unfold listSortKeyImplF
    have hne : xs ≠ [] := by intro h; rw [h] at hlen; simp at hlen
    obtain ⟨h1, h2⟩ := keysLoop_mut key kf hk hm xs LView.during [] hne
    generalize keysLoop key xs LView.during [] = K at h1 h2
    obtain ⟨ks, during⟩ := K
    simp only at h1 h2
    subst h1
    simp only [List.reverse_nil, List.nil_append, zip_map_self]
    have hp : (fun p q : κ × α => pureLt g p.1 q.1) = pureLt (fun p q : κ × α => g p.1 q.1) := rfl
    rw [hp, listSortCntF_pure]
    simp only [h2, ne_eq, not_false_eq_true, ↓reduceIte]
    rfl
  · simp only [pyListSortF, listSortImplF, hraise]

end PyLean.ListSort
