import PyLean.ListSort.MergeHi
import PyLean.ListSort.Bound

/-!
# The whole sort is the stable sort

`Runs` (top first) says every pending run's slice of the array is the stable
sort of the same slice of the input, and the runs tile `[0, pos)`.
`merge_at`, `found_new_run`, the run detection and `merge_force_collapse`
preserve it; at the end one run covers the array (`sortCore_eq`).
-/

namespace PyLean.ListSort

variable {α : Type}

def seg (l : List α) (b n : Nat) : List α := (l.drop b).take n

def Runs (kf : α → Int) (xs arr : List α) : List Slice → Nat → Prop
  | [], p => p = 0
  | e :: rest, p => e.base + e.len = p ∧ 0 < e.len ∧
      SS kf (seg xs e.base e.len) (seg arr e.base e.len) ∧ Runs kf xs arr rest e.base

theorem seg_take (l : List α) (b n p : Nat) (h : b + n ≤ p) : seg (l.take p) b n = seg l b n := by
  unfold seg
  rw [List.drop_take, List.take_take, Nat.min_eq_left (by omega)]

theorem runs_congr (kf : α → Int) (xs : List α) :
    ∀ (stk : List Slice) (p : Nat) (arr arr' : List α), arr'.take p = arr.take p →
      Runs kf xs arr stk p → Runs kf xs arr' stk p
  | [], _, _, _, _, h => h
  | e :: rest, p, arr, arr', ht, ⟨h1, h2, h3, h4⟩ => by
    refine ⟨h1, h2, ?_, runs_congr kf xs rest e.base arr arr' ?_ h4⟩
    · rw [← seg_take arr' _ _ p (by omega), ht, seg_take arr _ _ p (by omega)]; exact h3
    · have := congrArg (List.take e.base) ht
      rwa [List.take_take, List.take_take, Nat.min_eq_left (by omega)] at this

theorem seg_split (l : List α) (b n1 n2 : Nat) : seg l b (n1 + n2) = seg l b n1 ++ seg l (b + n1) n2 := by
  unfold seg
  rw [List.take_add, List.drop_drop]

theorem seg_length (l : List α) (b n : Nat) (h : b + n ≤ l.length) : (seg l b n).length = n := by
  unfold seg; simp; omega

theorem mergeAtArr_data (kf : α → Int) (xs : List α) (b n1 n2 : Nat) (arr : List α) (ms : MS)
    (hlen : b + n1 + n2 ≤ arr.length) (h1 : 0 < n1) (h2 : 0 < n2)
    (hu : SS kf (seg xs b n1) (seg arr b n1)) (ht : SS kf (seg xs (b + n1) n2) (seg arr (b + n1) n2)) :
    (mergeAtArr (ltOf kf) b n1 n2 (arr, ms)).1.length = arr.length ∧
      (mergeAtArr (ltOf kf) b n1 n2 (arr, ms)).1.take b = arr.take b ∧
      (mergeAtArr (ltOf kf) b n1 n2 (arr, ms)).1.drop (b + n1 + n2) = arr.drop (b + n1 + n2) ∧
      SS kf (seg xs b (n1 + n2)) (seg (mergeAtArr (ltOf kf) b n1 n2 (arr, ms)).1 b (n1 + n2)) := by
  have hA := seg_length arr b n1 (by omega)
  have hB := seg_length arr (b + n1) n2 (by omega)
  have hm := mergeAt_spec kf (seg arr b n1) (seg arr (b + n1) n2) ms hu.1 ht.1
    (fun h => by rw [h] at hA; simp at hA; omega) (fun h => by rw [h] at hB; simp at hB; omega)
  simp only [mergeAtArr]
  unfold seg at hm hA hB
  generalize mergeAt (ltOf kf) ((arr.drop b).take n1) ((arr.drop (b + n1)).take n2) ms = M at hm
  obtain ⟨m, ms'⟩ := M
  simp only at hm ⊢
  have hml : m.length = n1 + n2 := by rw [hm.length]; simp [hA, hB]
  have htb : (arr.take b).length = b := by simp; omega
  refine ⟨by simp; omega, ?_, ?_, ?_⟩
  · rw [List.append_assoc, List.take_left' htb]
  · rw [List.drop_left' (by simp; omega)]
  · have : seg (arr.take b ++ m ++ arr.drop (b + n1 + n2)) b (n1 + n2) = m := by
      unfold seg
      rw [List.append_assoc, List.drop_left' htb, List.take_left' hml]
    rw [this, seg_split]
    exact SS.of_parts hu ht hm

theorem runs_drop (kf : α → Int) (xs : List α) {arr : List α} {e : Slice} {rest : List Slice} {p : Nat}
    (h : Runs kf xs arr (e :: rest) p) : e.base + e.len = p := h.1

/-- Merging the two topmost runs keeps `Runs`. -/
theorem runs_merge_top (kf : α → Int) (xs : List α) (N p : Nat) (t u : Slice) (rest : List Slice)
    (arr : List α) (ms : MS) (h : Runs kf xs arr (t :: u :: rest) p) (hN : arr.length = N) (hp : p ≤ N)
    (q : Nat) :
    Runs kf xs (mergeAtArr (ltOf kf) u.base u.len t.len (arr, ms)).1 (⟨u.base, u.len + t.len, q⟩ :: rest) p ∧
      (mergeAtArr (ltOf kf) u.base u.len t.len (arr, ms)).1.length = N ∧
      (mergeAtArr (ltOf kf) u.base u.len t.len (arr, ms)).1.drop p = arr.drop p := by
  obtain ⟨ht1, ht2, ht3, hu1, hu2, hu3, hr⟩ := h
  have hd := mergeAtArr_data kf xs u.base u.len t.len arr ms (by omega) hu2 ht2 hu3 (by rw [hu1]; exact ht3)
  obtain ⟨hd1, hd2, hd3, hd4⟩ := hd
  have hp' : u.base + u.len + t.len = p := by omega
  refine ⟨⟨by simp; omega, by simp; omega, hd4, runs_congr kf xs rest u.base arr _ hd2 hr⟩, by rw [hd1, hN], ?_⟩
  rw [← hp', hd3]

theorem mergeWhile_data (kf : α → Int) (xs : List α) (N p power : Nat) :
    ∀ (n : Nat) (stk : List Slice) (arr : List α) (ms : MS), stk.length ≤ n →
      Runs kf xs arr stk p → arr.length = N → p ≤ N →
      Runs kf xs (mergeWhile (mergeAtArr (ltOf kf)) power stk (arr, ms)).2.1
          (mergeWhile (mergeAtArr (ltOf kf)) power stk (arr, ms)).1 p ∧
        (mergeWhile (mergeAtArr (ltOf kf)) power stk (arr, ms)).2.1.length = N ∧
        (mergeWhile (mergeAtArr (ltOf kf)) power stk (arr, ms)).2.1.drop p = arr.drop p := by
  intro n
  induction n with
  | zero =>
    intro stk arr ms h hr hN hp
    match stk with
    | [] => simp [mergeWhile]; exact ⟨hr, hN⟩
  | succ n ih =>
    intro stk arr ms h hr hN hp
    match stk with
    | t :: u :: rest =>
      rw [mergeWhile]
      split
      · have hm := runs_merge_top kf xs N p t u rest arr ms hr hN hp u.power
        generalize mergeAtArr (ltOf kf) u.base u.len t.len (arr, ms) = S at hm
        obtain ⟨arr', ms'⟩ := S
        have := ih _ arr' ms' (by simp at h ⊢; omega) hm.1 hm.2.1 hp
        exact ⟨this.1, this.2.1, this.2.2.trans hm.2.2⟩
      · exact ⟨hr, hN, rfl⟩
    | [t] => simp [mergeWhile]; exact ⟨hr, hN⟩
    | [] => simp [mergeWhile]; exact ⟨hr, hN⟩

theorem foundNewRun_data (kf : α → Int) (xs : List α) (N p n2 : Nat) (stk : List Slice) (arr : List α)
    (ms : MS) (hr : Runs kf xs arr stk p) (hN : arr.length = N) (hp : p ≤ N) :
    Runs kf xs (foundNewRun (mergeAtArr (ltOf kf)) N n2 stk (arr, ms)).2.1
        (foundNewRun (mergeAtArr (ltOf kf)) N n2 stk (arr, ms)).1 p ∧
      (foundNewRun (mergeAtArr (ltOf kf)) N n2 stk (arr, ms)).2.1.length = N ∧
      (foundNewRun (mergeAtArr (ltOf kf)) N n2 stk (arr, ms)).2.1.drop p = arr.drop p := by
  unfold foundNewRun
  split
  · exact ⟨hr, hN, rfl⟩
  · rename_i top rest
    have := mergeWhile_data kf xs N p (powerloop top.base top.len n2 N) _ (top :: rest) arr ms
      (Nat.le_refl _) hr hN hp
    dsimp only
    generalize mergeWhile (mergeAtArr (ltOf kf)) (powerloop top.base top.len n2 N) (top :: rest) (arr, ms) = R
      at this ⊢
    obtain ⟨stk', arr', ms'⟩ := R
    match stk', this with
    | [], this => exact this
    | t :: rest', this => exact this

theorem forceCollapse_data (kf : α → Int) (xs : List α) (N p : Nat) :
    ∀ (n : Nat) (stk : List Slice) (arr : List α) (ms : MS), stk.length ≤ n →
      Runs kf xs arr stk p → arr.length = N → p ≤ N →
      Runs kf xs (forceCollapse (mergeAtArr (ltOf kf)) stk (arr, ms)).2.1
          (forceCollapse (mergeAtArr (ltOf kf)) stk (arr, ms)).1 p ∧
        (forceCollapse (mergeAtArr (ltOf kf)) stk (arr, ms)).2.1.length = N := by
  intro n
  induction n with
  | zero =>
    intro stk arr ms h hr hN hp
    match stk with
    | [] => simp [forceCollapse]; exact ⟨hr, hN⟩
  | succ n ih =>
    intro stk arr ms h hr hN hp
    match stk with
    | t :: u :: v :: rest =>
      rw [forceCollapse]
      split
      · -- merge v and u, the top stays
        obtain ⟨ht1, ht2, ht3, hu1, hu2, hu3, hv1, hv2, hv3, hr'⟩ := hr
        have hd := mergeAtArr_data kf xs v.base v.len u.len arr ms (by omega) hv2 hu2 hv3
          (by rw [hv1]; exact hu3)
        obtain ⟨hd1, hd2, hd3, hd4⟩ := hd
        generalize mergeAtArr (ltOf kf) v.base v.len u.len (arr, ms) = S at hd1 hd2 hd3 hd4
        obtain ⟨arr', ms'⟩ := S
        simp only at hd1 hd2 hd3 hd4
        have hseg : seg arr' t.base t.len = seg arr t.base t.len := by
          unfold seg
          rw [show t.base = v.base + v.len + u.len by omega, hd3]
        have hruns : Runs kf xs arr' (t :: ⟨v.base, v.len + u.len, v.power⟩ :: rest) p :=
          ⟨ht1, ht2, by rw [hseg]; exact ht3, by simp; omega, by simp; omega, hd4,
            runs_congr kf xs rest v.base arr arr' hd2 hr'⟩
        exact ih _ arr' ms' (by simp at h ⊢; omega) hruns (by rw [hd1, hN]) hp
      · have hm := runs_merge_top kf xs N p t u (v :: rest) arr ms hr hN hp u.power
        generalize mergeAtArr (ltOf kf) u.base u.len t.len (arr, ms) = S at hm
        obtain ⟨arr', ms'⟩ := S
        exact ih _ arr' ms' (by simp at h ⊢; omega) hm.1 hm.2.1 hp
    | [t, u] =>
      rw [forceCollapse]
      have hm := runs_merge_top kf xs N p t u [] arr ms hr hN hp u.power
      generalize mergeAtArr (ltOf kf) u.base u.len t.len (arr, ms) = S at hm
      obtain ⟨arr', ms'⟩ := S
      exact ih _ arr' ms' (by simp at h ⊢; omega) hm.1 hm.2.1 hp
    | [t] => simp [forceCollapse]; exact ⟨hr, hN⟩
    | [] => simp [forceCollapse]; exact ⟨hr, hN⟩

theorem SS.of_feq {kf : α → Int} {P Q A B M : List α} (hA : FEq kf P A) (hB : FEq kf Q B)
    (hM : SS kf (A ++ B) M) : SS kf (P ++ Q) M :=
  ⟨hM.1, (FEq.append hA hB).trans hM.2⟩

/-- Data invariant of the main loop at position `pos`. -/
def DataOK (kf : α → Int) (xs : List α) (pos : Nat) (st : Sorter α) : Prop :=
  Runs kf xs st.arr st.stk pos ∧ st.arr.length = xs.length ∧ st.arr.drop pos = xs.drop pos

theorem sortStep_data (kf : α → Int) (xs : List α) (pos : Nat) (st : Sorter α)
    (h : DataOK kf xs pos st) (hpos : pos < xs.length) :
    DataOK kf xs (pos + (sortStep (ltOf kf) xs.length pos st).2)
      (sortStep (ltOf kf) xs.length pos st).1 ∧
    1 ≤ (sortStep (ltOf kf) xs.length pos st).2 ∧
      pos + (sortStep (ltOf kf) xs.length pos st).2 ≤ xs.length := by
  obtain ⟨hruns, hlen, hdrop⟩ := h
  have hX : (xs.drop pos) ≠ [] := by
    intro h; have := congrArg List.length h; simp at this; omega
  have hcr := countRun_spec kf (xs.drop pos) st.ms hX
  have hcp := countRun_perm (ltOf kf) (xs.drop pos) st.ms
  simp only [sortStep]
  rw [hdrop]
  generalize countRun (ltOf kf) (xs.drop pos) st.ms = CR at hcr hcp
  obtain ⟨n0, ys, ms0⟩ := CR
  simp only at hcr hcp
  obtain ⟨R, hys, hR⟩ := hcr
  obtain ⟨_, hn0, hn0'⟩ := hcp
  have hn0 := hn0 hX
  simp only [List.length_drop] at hn0'
  have hRl : R.length = n0 := by rw [hR.length]; simp; omega
  -- the run is sorted for every minrun
  generalize minrunNext st.mr = MR
  obtain ⟨minrun, mr⟩ := MR
  simp only
  -- after the optional binary insertion
  have hrun : ∃ n rest ms, (if n0 < minrun then
      ((if xs.length - pos ≤ minrun then xs.length - pos else minrun),
        (binarysort (ltOf kf) ys (if xs.length - pos ≤ minrun then xs.length - pos else minrun) n0 ms0).1,
        (binarysort (ltOf kf) ys (if xs.length - pos ≤ minrun then xs.length - pos else minrun) n0 ms0).2)
      else (n0, ys, ms0)) = (n, rest, ms) ∧ 1 ≤ n ∧ n ≤ xs.length - pos ∧
      ∃ R', rest = R' ++ (xs.drop pos).drop n ∧ SS kf ((xs.drop pos).take n) R' := by
    split
    · rename_i hlt
      have hf1 : n0 ≤ (if xs.length - pos ≤ minrun then xs.length - pos else minrun) := by split <;> omega
      have hf2 : (if xs.length - pos ≤ minrun then xs.length - pos else minrun) ≤ xs.length - pos := by
        split <;> omega
      refine ⟨_, _, _, rfl, by omega, hf2, ?_⟩
      generalize (if xs.length - pos ≤ minrun then xs.length - pos else minrun) = force at hf1 hf2
      have hok : (if n0 = 0 then 1 else n0) = n0 := by simp only [show n0 ≠ 0 by omega, ↓reduceIte]
      have hyt : ys.take n0 = R := by rw [hys, List.take_left' hRl]
      obtain ⟨R', hb1, hb2⟩ := binarysort_spec kf ys force n0 ms0 (by rw [hok]; exact hf1)
        (by rw [hok, hyt]; exact hR.1)
      refine ⟨R', ?_, ?_⟩
      · rw [hb1, hys, List.drop_append, List.drop_eq_nil_of_le (by rw [hRl]; omega), List.nil_append, hRl,
          List.drop_drop, show n0 + (force - n0) = force by omega]
      · have e1 : ys.take force = R ++ ((xs.drop pos).drop n0).take (force - n0) := by
          rw [hys, List.take_append, hRl, List.take_of_length_le (by omega)]
        have e2 : (xs.drop pos).take force =
            (xs.drop pos).take n0 ++ ((xs.drop pos).drop n0).take (force - n0) := by
          rw [show force = n0 + (force - n0) by omega, List.take_add]; simp
        rw [e2]
        rw [e1] at hb2
        exact SS.of_feq hR.2 (FEq.refl _ _) hb2
    · exact ⟨_, _, _, rfl, hn0, hn0', R, hys, hR⟩
  obtain ⟨n, rest, ms, hEq2, hn1, hn2, R', hrest, hR'⟩ := hrun
  have hlet : (if n0 < minrun then
      (let force := if xs.length - pos ≤ minrun then xs.length - pos else minrun
       let (rest, ms) := binarysort (ltOf kf) ys force n0 ms0
       (force, rest, ms))
      else (n0, ys, ms0)) = (n, rest, ms) := by
    rw [← hEq2]
  rw [hlet]
  simp only
  have hR'l : R'.length = n := by rw [hR'.length]; simp; omega
  have hrl : rest.length = xs.length - pos := by rw [hrest]; simp; omega
  have harr1 : (st.arr.take pos ++ rest).take pos = st.arr.take pos := List.take_left' (by simp; omega)
  have hruns1 := runs_congr kf xs st.stk pos st.arr _ harr1 hruns
  have hlen1 : (st.arr.take pos ++ rest).length = xs.length := by simp; omega
  have hd := foundNewRun_data kf xs xs.length pos n st.stk (st.arr.take pos ++ rest) ms hruns1 hlen1 (by omega)
  generalize foundNewRun (mergeAtArr (ltOf kf)) xs.length n st.stk (st.arr.take pos ++ rest, ms) = F at hd
  obtain ⟨stk', arr', ms'⟩ := F
  simp only at hd ⊢
  obtain ⟨hd1, hd2, hd3⟩ := hd
  rw [List.drop_left' (by simp; omega)] at hd3
  refine ⟨⟨⟨by simp, hn1, ?_, hd1⟩, hd2, ?_⟩, hn1, by omega⟩
  · have e1 : seg xs pos n = (xs.drop pos).take n := rfl
    have e2 : seg arr' pos n = R' := by
      unfold seg; rw [hd3, hrest, List.take_left' hR'l]
    rw [e1, e2]; exact hR'
  · rw [← List.drop_drop, hd3, hrest, List.drop_left' hR'l, List.drop_drop]

theorem sortLoop_data (kf : α → Int) (xs : List α) :
    ∀ (fuel pos : Nat) (st : Sorter α), DataOK kf xs pos st → pos < xs.length → xs.length ≤ pos + fuel →
      DataOK kf xs xs.length (sortLoop (ltOf kf) xs.length fuel pos st)
  | 0, pos, st, _, hpos, hf => by omega
  | fuel + 1, pos, st, h, hpos, hf => by
    have hs := sortStep_data kf xs pos st h hpos
    simp only [sortLoop]
    generalize sortStep (ltOf kf) xs.length pos st = S at hs
    obtain ⟨st', n⟩ := S
    simp only at hs ⊢
    split
    · exact sortLoop_data kf xs fuel (pos + n) st' hs.1 (by omega) (by omega)
    · have : pos + n = xs.length := by omega
      rw [this] at hs
      exact hs.1

/-- The model of `list.sort` sorts stably: for a consistent comparison by an
integer key, the array after the sort is the stable sort of the input. -/
theorem sortCore_eq (kf : α → Int) (xs : List α) : (sortCore (ltOf kf) xs).arr = stableSort kf xs := by
  unfold sortCore
  dsimp only
  split
  · rename_i h
    apply ss_eq_stableSort
    apply Sorted.ss
    match xs, h with
    | [], _ => simp [Sorted]
    | [x], _ => simp [Sorted]
  · rename_i h
    have h0 : DataOK kf xs 0
        { arr := xs, ms := {}, stk := [], pushOk := true, mr := mergeInitMr xs.length } :=
      ⟨rfl, rfl, rfl⟩
    have hl := sortLoop_data kf xs xs.length 0 _ h0 (by omega) (by omega)
    generalize sortLoop (ltOf kf) xs.length xs.length 0 _ = st at hl
    obtain ⟨hruns, hlen, _⟩ := hl
    have hfc := forceCollapse_data kf xs xs.length xs.length _ st.stk st.arr st.ms (Nat.le_refl _) hruns hlen
      (Nat.le_refl _)
    have hfl := forceCollapse_len (mergeAtArr (ltOf kf)) _ st.stk (st.arr, st.ms) (Nat.le_refl _)
    have hne : 1 ≤ st.stk.length := by
      cases hs : st.stk with
      | nil => rw [hs] at hruns; simp only [Runs] at hruns; omega
      | cons _ _ => simp
    rw [Nat.min_eq_right hne] at hfl
    generalize forceCollapse (mergeAtArr (ltOf kf)) st.stk (st.arr, st.ms) = F at hfc hfl
    obtain ⟨stk', arr', ms'⟩ := F
    simp only at hfc hfl ⊢
    obtain ⟨hr, hl'⟩ := hfc
    match stk', hr with
    | [], hr => simp only [Runs] at hr; omega
    | [e], ⟨h1, h2, h3, h4⟩ =>
      simp only [Runs] at h4
      have hel : e.len = xs.length := by omega
      have hx : seg xs e.base e.len = xs := by unfold seg; rw [h4, hel]; simp
      have ha : seg arr' e.base e.len = arr' := by unfold seg; rw [h4, hel, ← hl']; simp
      rw [hx, ha] at h3
      exact ss_eq_stableSort h3
    | _ :: _ :: _, _ => simp at hfl

end PyLean.ListSort
