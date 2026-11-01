import PyLean.ListSort.Stable

/-!
# Binary search, galloping and binary insertion

For a predicate `P` on indices `[0, n)` that is true exactly below some `k`,
the shared binary-search loop and both galloping searches return `k`, for every
`hint < n` (`gallopCore_spec`). On a sorted vector this gives the documented
results of `gallop_left` (`a[k-1] < key <= a[k]`, `listobject.c:2077-2079`) and
`gallop_right` (`a[k-1] <= key < a[k]`, `:2166-2168`).
-/

namespace PyLean.ListSort

variable {α : Type}

theorem binLoop_spec (test : Nat → MS → Bool × MS) (P : Nat → Bool) (k : Nat) :
    ∀ (fuel lo hi : Nat) (ms : MS), (∀ m ms, lo ≤ m → m < hi → (test m ms).1 = P m) →
      (∀ m, lo ≤ m → m < hi → (P m = true ↔ m < k)) → lo ≤ k → k ≤ hi → hi - lo ≤ fuel →
      (binLoop test fuel lo hi ms).1 = k
  | 0, lo, hi, ms, _, _, h1, h2, h3 => by simp [binLoop]; omega
  | fuel + 1, lo, hi, ms, ht, hP, h1, h2, h3 => by
    simp only [binLoop]
    split
    · have hm1 : lo ≤ lo + (hi - lo) / 2 := by omega
      have hm2 : lo + (hi - lo) / 2 < hi := by omega
      rw [ht _ _ hm1 hm2]
      split
      · rename_i hc
        have := (hP _ hm1 hm2).1 hc
        exact binLoop_spec test P k fuel _ hi _ (fun m ms h1 h2 => ht m ms (by omega) h2)
          (fun m h1 h2 => hP m (by omega) h2) (by omega) h2 (by omega)
      · rename_i hc
        have : ¬ (lo + (hi - lo) / 2 < k) := fun h => hc ((hP _ hm1 hm2).2 h)
        exact binLoop_spec test P k fuel lo _ _ (fun m ms h1 h2 => ht m ms h1 (by omega))
          (fun m h1 h2 => hP m h1 (by omega)) h1 (by omega) (by omega)
    · simp; omega

theorem gallopUp_spec (test : Nat → MS → Bool × MS) (P : Nat → Bool) (k n hint : Nat)
    (ht : ∀ m ms, m < n → (test m ms).1 = P m) (hP : ∀ i, i < n → (P i = true ↔ i < k))
    (hk : k ≤ n) (hh : hint < n) :
    ∀ (fuel lastofs ofs : Nat) (ms : MS), hint + lastofs < k → lastofs < ofs → lastofs < n - hint →
      n - hint + 1 ≤ fuel + ofs →
      let r := gallopUp test hint (n - hint) fuel lastofs ofs ms
      hint + r.1 < k ∧ r.1 < r.2.1 ∧ r.1 < n - hint ∧ (n - hint ≤ r.2.1 ∨ k ≤ hint + r.2.1)
  | 0, lastofs, ofs, ms, h1, h2, h3, h4 => by simp [gallopUp]; omega
  | fuel + 1, lastofs, ofs, ms, h1, h2, h3, h4 => by
    simp only [gallopUp]
    split
    · rw [ht _ _ (by omega)]
      split
      · rename_i _ hc
        have := (hP _ (by omega)).1 hc
        exact gallopUp_spec test P k n hint ht hP hk hh fuel ofs (2 * ofs + 1) _ (by omega) (by omega)
          (by omega) (by omega)
      · rename_i _ hc
        have : ¬ (hint + ofs < k) := fun h => hc ((hP _ (by omega)).2 h)
        simp only; omega
    · simp only; omega

theorem gallopDown_spec (test : Nat → MS → Bool × MS) (P : Nat → Bool) (k n hint : Nat)
    (ht : ∀ m ms, m < n → (test m ms).1 = P m) (hP : ∀ i, i < n → (P i = true ↔ i < k))
    (hh : hint < n) :
    ∀ (fuel lastofs ofs : Nat) (ms : MS), k ≤ hint - lastofs → lastofs ≤ hint → lastofs < ofs →
      hint + 2 ≤ fuel + ofs →
      let r := gallopDown test hint (hint + 1) fuel lastofs ofs ms
      k ≤ hint - r.1 ∧ r.1 ≤ hint ∧ r.1 < r.2.1 ∧ (hint + 1 ≤ r.2.1 ∨ hint - r.2.1 < k)
  | 0, lastofs, ofs, ms, h1, h2, h3, h4 => by simp [gallopDown]; omega
  | fuel + 1, lastofs, ofs, ms, h1, h2, h3, h4 => by
    simp only [gallopDown]
    split
    · rw [ht _ _ (by omega)]
      split
      · rename_i _ hc
        have := (hP _ (by omega)).1 hc
        simp only; omega
      · rename_i _ hc
        have : ¬ (hint - ofs < k) := fun h => hc ((hP _ (by omega)).2 h)
        exact gallopDown_spec test P k n hint ht hP hh fuel ofs (2 * ofs + 1) _ (by omega) (by omega)
          (by omega) (by omega)
    · simp only; omega

/-- Both gallops and the final binary search find the boundary `k`. -/
theorem gallopCore_spec (test : Nat → MS → Bool × MS) (P : Nat → Bool) (k n hint : Nat) (ms : MS)
    (ht : ∀ m ms, m < n → (test m ms).1 = P m) (hP : ∀ i, i < n → (P i = true ↔ i < k))
    (hk : k ≤ n) (hh : hint < n) : (gallopCore test n hint ms).1 = k := by
  simp only [gallopCore]
  rw [ht _ _ hh]
  split
  · rename_i hc
    have hk' := (hP _ hh).1 hc
    have := gallopUp_spec test P k n hint ht hP hk hh (n + 1) 0 1 (test hint ms).2 (by omega) (by omega)
      (by omega) (by omega)
    generalize gallopUp test hint (n - hint) (n + 1) 0 1 (test hint ms).2 = G at this
    obtain ⟨lastofs, ofs, ms1⟩ := G
    simp only at this ⊢
    apply binLoop_spec test P k
    · intro m ms h1 h2; exact ht m ms (by split at h2 <;> omega)
    · intro m h1 h2; exact hP m (by split at h2 <;> omega)
    · omega
    · split <;> omega
    · split <;> omega
  · rename_i hc
    have hk' : k ≤ hint := by
      rcases Nat.lt_or_ge hint k with h | h
      · exact absurd ((hP _ hh).2 h) hc
      · exact h
    have := gallopDown_spec test P k n hint ht hP hh (n + 1) 0 1 (test hint ms).2 (by omega) (by omega)
      (by omega) (by omega)
    generalize gallopDown test hint (hint + 1) (n + 1) 0 1 (test hint ms).2 = G at this
    obtain ⟨lastofs, ofs, ms1⟩ := G
    simp only at this ⊢
    apply binLoop_spec test P k
    · intro m ms h1 h2; exact ht m ms (by omega)
    · intro m h1 h2; exact hP m (by omega)
    · split <;> omega
    · omega
    · split <;> omega

/-! ## On sorted lists -/

/-- On a list where `p` holds on a prefix (closed downwards), the indices
satisfying `p` are those below `(takeWhile p).length`. -/
theorem takeWhile_iff (p : α → Bool) :
    ∀ (A : List α), A.Pairwise (fun x y => p y = true → p x = true) →
      ∀ i (hi : i < A.length), (p A[i] = true ↔ i < (A.takeWhile p).length)
  | [], _, i, hi => by simp at hi
  | a :: A, h, i, hi => by
    obtain ⟨h1, h2⟩ := List.pairwise_cons.1 h
    cases hpa : p a with
    | false =>
      simp only [List.takeWhile_cons, hpa, Bool.false_eq_true, ↓reduceIte, List.length_nil]
      constructor
      · intro hpi
        cases i with
        | zero => simp [hpa] at hpi
        | succ i =>
          have := h1 _ (List.getElem_mem (by simpa using hi))
          simp at hpi; rw [this hpi] at hpa; cases hpa
      · intro h; omega
    | true =>
      simp only [List.takeWhile_cons, hpa, ↓reduceIte, List.length_cons]
      cases i with
      | zero => simp [hpa]
      | succ i =>
        simp only [List.getElem_cons_succ]
        rw [takeWhile_iff p A h2 i (by simpa using hi)]
        omega

theorem sorted_pairwise_lt (kf : α → Int) (key : α) {A : List α} (h : Sorted kf A) :
    A.Pairwise (fun x y => decide (kf y < kf key) = true → decide (kf x < kf key) = true) :=
  h.imp (fun hxy => by simp; omega)

theorem sorted_pairwise_le (kf : α → Int) (key : α) {A : List α} (h : Sorted kf A) :
    A.Pairwise (fun x y => decide (kf y ≤ kf key) = true → decide (kf x ≤ kf key) = true) :=
  h.imp (fun hxy => by simp; omega)

/-- `gallop_left` on a sorted vector: the number of items `< key`. -/
theorem gallopLeft_spec (kf : α → Int) (key : α) (A : List α) (get : Nat → α) (hint : Nat) (ms : MS)
    (hs : Sorted kf A) (hget : ∀ i (hi : i < A.length), get i = A[i]) (hh : hint < A.length) :
    (gallopLeft (ltOf kf) key get A.length hint ms).1 =
      (A.takeWhile (fun x => decide (kf x < kf key))).length := by
  apply gallopCore_spec _ (fun i => decide (kf (get i) < kf key))
  · intro m ms hm; rfl
  · intro i hi
    rw [hget i hi]
    exact takeWhile_iff _ A (sorted_pairwise_lt kf key hs) i hi
  · exact (List.takeWhile_prefix _).length_le
  · exact hh

/-- `gallop_right` on a sorted vector: the number of items `<= key`. -/
theorem gallopRight_spec (kf : α → Int) (key : α) (A : List α) (get : Nat → α) (hint : Nat) (ms : MS)
    (hs : Sorted kf A) (hget : ∀ i (hi : i < A.length), get i = A[i]) (hh : hint < A.length) :
    (gallopRight (ltOf kf) key get A.length hint ms).1 =
      (A.takeWhile (fun x => decide (kf x ≤ kf key))).length := by
  apply gallopCore_spec _ (fun i => decide (kf (get i) ≤ kf key))
  · intro m ms hm
    show (!decide (kf key < kf (get m))) = decide (kf (get m) ≤ kf key)
    by_cases h : kf key < kf (get m) <;> simp [h] <;> omega
  · intro i hi
    rw [hget i hi]
    exact takeWhile_iff _ A (sorted_pairwise_le kf key hs) i hi
  · exact (List.takeWhile_prefix _).length_le
  · exact hh

/-! ## binarysort -/

theorem takeWhile_all (p : α → Bool) (S : List α) : ∀ x ∈ S.takeWhile p, p x = true := by
  have := List.all_takeWhile (p := p) (l := S)
  rw [List.all_eq_true] at this
  exact this

theorem dropWhile_all_not (p : α → Bool) :
    ∀ (S : List α), S.Pairwise (fun x y => p y = true → p x = true) → ∀ x ∈ S.dropWhile p, p x = false
  | [], _, x, hx => by simp at hx
  | a :: S, h, x, hx => by
    obtain ⟨h1, h2⟩ := List.pairwise_cons.1 h
    cases hpa : p a with
    | true =>
      simp only [List.dropWhile_cons, hpa, ↓reduceIte] at hx
      exact dropWhile_all_not p S h2 x hx
    | false =>
      simp only [List.dropWhile_cons, hpa, Bool.false_eq_true, ↓reduceIte] at hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hpa
      · cases hpx : p x with
        | false => rfl
        | true => rw [h1 x hx hpx] at hpa; cases hpa

theorem take_drop_of_takeWhile (p : α → Bool) (S : List α) :
    S.take (S.takeWhile p).length = S.takeWhile p ∧ S.drop (S.takeWhile p).length = S.dropWhile p := by
  have h := List.takeWhile_append_dropWhile (p := p) (l := S)
  generalize S.takeWhile p = T at h ⊢
  generalize S.dropWhile p = D at h ⊢
  subst h
  simp

/-- The stable insertion of `e` into the sorted `S`. -/
theorem ss_insert (kf : α → Int) {P S : List α} (e : α) (h : SS kf P S) :
    SS kf (P ++ [e]) (S.takeWhile (fun x => decide (kf x ≤ kf e)) ++ e ::
      S.dropWhile (fun x => decide (kf x ≤ kf e))) := by
  have hS := h.1
  have hT := takeWhile_all (fun x => decide (kf x ≤ kf e)) S
  have hD := dropWhile_all_not (fun x => decide (kf x ≤ kf e)) S (sorted_pairwise_le kf e hS)
  have hsplit := List.takeWhile_append_dropWhile (p := fun x => decide (kf x ≤ kf e)) (l := S)
  generalize S.takeWhile (fun x => decide (kf x ≤ kf e)) = T at hsplit hT
  generalize S.dropWhile (fun x => decide (kf x ≤ kf e)) = D at hsplit hD
  subst hsplit
  obtain ⟨hTs, hDs, hTD⟩ := sorted_append.1 hS
  apply SS.of_parts h (Sorted.ss (by simp [Sorted] : Sorted kf [e]))
  rw [List.append_assoc]
  apply ss_prefix hTs
  · intro x hx y hy
    rcases List.mem_append.1 hy with hy | hy
    · exact hTD x hx y hy
    · simp at hy; subst hy; simpa using hT x hx
  · have := ss_swap (Sorted.ss hDs) (Sorted.ss (by simp [Sorted] : Sorted kf [e]))
      (fun x hx y hy => by simp at hx; subst hx; have := hD y hy; simp at this; omega)
    simpa using this

theorem bsInsert_spec (kf : α → Int) (sorted : List α) (p : α) (ms : MS) (hs : Sorted kf sorted) :
    (bsInsert (ltOf kf) sorted p ms).1 = sorted.takeWhile (fun x => decide (kf x ≤ kf p)) ++ p ::
      sorted.dropWhile (fun x => decide (kf x ≤ kf p)) := by
  simp only [bsInsert]
  have hl := binLoop_spec (fun m ms => let r := islt (ltOf kf) ms p (sorted.getD m p); (!r.1, r.2))
    (fun i => decide (kf (sorted.getD i p) ≤ kf p)) (sorted.takeWhile (fun x => decide (kf x ≤ kf p))).length
    (sorted.length + 1) 0 sorted.length ms
    (fun m ms _ _ => by
      simp only [islt, ltOf]
      generalize kf (sorted.getD m p) = u
      by_cases h : kf p < u
      · simp only [h, decide_true, Bool.not_true]; symm; simp; omega
      · simp only [h, decide_false, Bool.not_false]; symm; simp; omega)
    (fun m _ hm => by
      have := takeWhile_iff _ sorted (sorted_pairwise_le kf p hs) m hm
      simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm] using this)
    (by omega) ((List.takeWhile_prefix _).length_le) (by omega)
  generalize binLoop _ _ _ _ _ = R at hl
  obtain ⟨l, ms'⟩ := R
  simp only at hl ⊢
  subst hl
  rw [(take_drop_of_takeWhile _ sorted).1, (take_drop_of_takeWhile _ sorted).2]

theorem bsLoop_spec (kf : α → Int) :
    ∀ (sorted ps : List α) (ms : MS) (P : List α), SS kf P sorted →
      SS kf (P ++ ps) (bsLoop (ltOf kf) sorted ps ms).1
  | sorted, [], ms, P, h => by simpa [bsLoop] using h
  | sorted, p :: ps, ms, P, h => by
    simp only [bsLoop]
    have h1 := ss_insert kf p h
    rw [← bsInsert_spec kf sorted p ms h.1] at h1
    have := bsLoop_spec kf _ ps (bsInsert (ltOf kf) sorted p ms).2 _ h1
    simpa using this

/-- `binarysort(ss, n, ok)` with `a[:max(ok,1)]` sorted and `ok <= n <= len(a)`
leaves the stable sort of `a[:n]` followed by `a[n:]`. -/
theorem binarysort_spec (kf : α → Int) (a : List α) (n ok : Nat) (ms : MS)
    (hok : (if ok = 0 then 1 else ok) ≤ n)
    (hs : Sorted kf (a.take (if ok = 0 then 1 else ok))) :
    ∃ R, (binarysort (ltOf kf) a n ok ms).1 = R ++ a.drop n ∧ SS kf (a.take n) R := by
  simp only [binarysort]
  generalize (if ok = 0 then 1 else ok) = k at hok hs
  have := bsLoop_spec kf (a.take k) ((a.take n).drop k) ms (a.take k) (Sorted.ss hs)
  have e : a.take k ++ (a.take n).drop k = a.take n := by
    conv => rhs; rw [← List.take_append_drop k (a.take n)]
    rw [List.take_take, Nat.min_eq_left hok]
  rw [e] at this
  exact ⟨_, rfl, this⟩

end PyLean.ListSort
