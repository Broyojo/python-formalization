import PyLean.ListSort.Power

/-!
# The pending-run stack invariant

A stack entry is paired with its ghost: the original runs (as found by the main
loop) that were merged into it. `TopInv N pos xs` (top first) says:

* the top entry is a single original run ending at `pos`;
* every other entry `e` (`Below`) stores the power of the boundary between its
  last original run and the first original run of the entry above, every
  boundary inside `e` has a strictly larger power, and the stored powers
  strictly increase towards the top (all `>= 1`);
* the entries are adjacent and the bottom one starts at 0.

`foundNewRun_inv` shows `found_new_run` + push preserves it for any merge
function, and `topInv_bound` turns it into `2^(entries below the top) < 2N`.
-/

namespace PyLean.ListSort

def Below (N : Nat) : Run → Option Nat → List (Slice × List Run) → Prop
  | f, _, [] => f.1 = 0
  | f, ap, (e, g) :: rest =>
    ∃ fst lst, g.head? = some fst ∧ g.getLast? = some lst ∧ Blk N g ∧
      e.base = fst.1 ∧ e.base + e.len = f.1 ∧ Adj lst f ∧
      e.power = bp N lst f ∧ Chn (fun r r' => e.power < bp N r r') g ∧ 1 ≤ e.power ∧
      (∀ q, ap = some q → e.power < q) ∧ Below N fst (some e.power) rest

def TopInv (N pos : Nat) : List (Slice × List Run) → Prop
  | [] => pos = 0
  | (e, g) :: rest =>
    g = [(e.base, e.len)] ∧ 0 < e.len ∧ e.base + e.len = pos ∧ pos ≤ N ∧
      Below N (e.base, e.len) none rest

/-- The stack invariant: some ghost assignment satisfies `TopInv`. -/
def StackInv (N pos : Nat) (stk : List Slice) : Prop :=
  ∃ xs : List (Slice × List Run), xs.map Prod.fst = stk ∧ TopInv N pos xs

theorem below_none {N : Nat} {f : Run} {q : Nat} :
    ∀ {xs : List (Slice × List Run)}, Below N f (some q) xs → Below N f none xs
  | [], h => h
  | (_, _) :: _, ⟨fst, lst, h1, h2, h3, h4, h5, h6, h7, h8, h9, _, h11⟩ =>
    ⟨fst, lst, h1, h2, h3, h4, h5, h6, h7, h8, h9, (fun _ h => by cases h), h11⟩

theorem below_some {N : Nat} {f : Run} {q : Nat} :
    ∀ {xs : List (Slice × List Run)}, Below N f none xs →
      (∀ e g rest, xs = (e, g) :: rest → e.power < q) → Below N f (some q) xs
  | [], h, _ => h
  | (e, g) :: rest, ⟨fst, lst, h1, h2, h3, h4, h5, h6, h7, h8, h9, _, h11⟩, hq =>
    ⟨fst, lst, h1, h2, h3, h4, h5, h6, h7, h8, h9,
      (fun q' hq' => by cases hq'; exact hq e g rest rfl), h11⟩

/-- The state of the `while` loop of `found_new_run`: the top block `T` (ghost
`gT`) ends with the previous original run `prev`, next to the new run `new`,
all its inner boundaries have power `> p = bp prev new`, and the rest of the
stack is as in `Below` (with no constraint against `T`'s stale power). -/
def LoopInv (N p : Nat) (prev new : Run) : List (Slice × List Run) → Prop
  | [] => False
  | (T, gT) :: rest =>
    ∃ fst, gT.head? = some fst ∧ gT.getLast? = some prev ∧ Blk N gT ∧ Adj prev new ∧
      0 < new.2 ∧ new.1 + new.2 ≤ N ∧
      p = bp N prev new ∧ T.base = fst.1 ∧ T.base + T.len = new.1 ∧
      Chn (fun r r' => p < bp N r r') gT ∧ Below N fst none rest

theorem getLast?_append_of_ne {β : Type} (l1 l2 : List β) (x : β) (h : l2.getLast? = some x) :
    (l1 ++ l2).getLast? = some x := by
  rw [List.getLast?_append, h]; rfl

theorem head?_append_of_ne {β : Type} (l1 l2 : List β) (x : β) (h : l1.head? = some x) :
    (l1 ++ l2).head? = some x := by
  cases l1 with
  | nil => simp at h
  | cons a l => simpa using h

theorem mergeWhile_inv {σ : Type} (mf : Nat → Nat → Nat → σ → σ) (N p : Nat) (prev new : Run) :
    ∀ (n : Nat) (xs : List (Slice × List Run)) (s : σ), xs.length = n → LoopInv N p prev new xs →
      ∃ ys, (mergeWhile mf p (xs.map Prod.fst) s).1 = ys.map Prod.fst ∧ LoopInv N p prev new ys ∧
        ∀ T gT e g rest, ys = (T, gT) :: (e, g) :: rest → e.power ≤ p := by
  intro n
  induction n with
  | zero => intro xs s hn hinv; match xs, hinv with | [], h => exact h.elim
  | succ n ih =>
    intro xs s hn hinv
    match xs, hinv with
    | [(T, gT)], hinv =>
      refine ⟨[(T, gT)], by simp [mergeWhile], hinv, fun _ _ e g rest h => by simp at h⟩
    | (T, gT) :: (u, gu) :: rest, hinv =>
      obtain ⟨fst, hfst, hlast, hblk, hadj, hnew, hnewN, hp, hTb, hTe, hchn, hbelow⟩ := hinv
      obtain ⟨ufst, ulst, hu1, hu2, hu3, hu4, hu5, hu6, hu7, hu8, hu9, _, hu11⟩ := hbelow
      simp only [List.map_cons]
      rw [mergeWhile]
      by_cases hgt : u.power > p
      · simp only [hgt, ↓reduceIte]
        have hinv' : LoopInv N p prev new ((⟨u.base, u.len + T.len, u.power⟩, gu ++ gT) :: rest) := by
          refine ⟨ufst, head?_append_of_ne _ _ _ hu1, getLast?_append_of_ne _ _ _ hlast, ?_, hadj, hnew,
            hnewN, hp, hu4, by simp; omega, ?_, below_none hu11⟩
          · refine ⟨chn_append gu gT ulst fst hu2 hfst hu3.1 hblk.1 hu6, fun r hr => ?_⟩
            rcases List.mem_append.1 hr with hr | hr
            · exact hu3.2 r hr
            · exact hblk.2 r hr
          · refine chn_append gu gT ulst fst hu2 hfst ?_ ?_ ?_
            · exact chn_imp (fun a b h => by omega) gu hu8
            · exact hchn
            · rw [← hu7]; exact hgt
        have := ih _ (mf u.base u.len T.len s) (by simp at hn ⊢; omega) hinv'
        simpa using this
      · simp only [hgt, ↓reduceIte]
        refine ⟨(T, gT) :: (u, gu) :: rest, by simp,
          ⟨fst, hfst, hlast, hblk, hadj, hnew, hnewN, hp, hTb, hTe, hchn,
            ⟨ufst, ulst, hu1, hu2, hu3, hu4, hu5, hu6, hu7, hu8, hu9, (fun _ h => by cases h), hu11⟩⟩, ?_⟩
        intro _ _ e g rest' h
        simp at h
        obtain ⟨_, ⟨rfl, rfl⟩, rfl⟩ := h
        omega

/-- `found_new_run` followed by the push of the new run `(pos, n2)` preserves
the stack invariant, for every merge function. -/
theorem foundNewRun_inv {σ : Type} (mf : Nat → Nat → Nat → σ → σ) (N pos n2 : Nat)
    (stk : List Slice) (s : σ) (hinv : StackInv N pos stk) (hn2 : 0 < n2) (hN : pos + n2 ≤ N) :
    StackInv N (pos + n2) (⟨pos, n2, 0⟩ :: (foundNewRun mf N n2 stk s).1) := by
  obtain ⟨xs, rfl, htop⟩ := hinv
  match xs, htop with
  | [], htop =>
    simp only [TopInv] at htop
    subst htop
    refine ⟨[(⟨0, n2, 0⟩, [(0, n2)])], by simp [foundNewRun], ?_⟩
    simp [TopInv, Below]; omega
  | (T, gT) :: rest, htop =>
    obtain ⟨hg, hlen, hend, hpos, hbelow⟩ := htop
    subst hg
    have hinv0 : LoopInv N (bp N (T.base, T.len) (pos, n2)) (T.base, T.len) (pos, n2)
        ((T, [(T.base, T.len)]) :: rest) := by
      refine ⟨(T.base, T.len), rfl, rfl, ⟨trivial, ?_⟩, ?_, hn2, hN, rfl, rfl, ?_, trivial, hbelow⟩
      · intro r hr; simp at hr; subst hr; exact ⟨hlen, by omega⟩
      · simp [Adj]; omega
      · simp; omega
    obtain ⟨ys, hys, hloop, hexit⟩ := mergeWhile_inv mf N _ _ _ _ _ s rfl hinv0
    simp only [List.map_cons] at hys
    simp only [List.map_cons, foundNewRun]
    have hp : powerloop T.base T.len n2 N = bp N (T.base, T.len) (pos, n2) := rfl
    rw [hp]
    generalize mergeWhile mf (bp N (T.base, T.len) (pos, n2)) (T :: List.map Prod.fst rest) s = res at hys ⊢
    obtain ⟨stk', s'⟩ := res
    simp only at hys
    subst hys
    match ys, hloop, hexit with
    | (T', gT') :: rest', hloop, hexit =>
      obtain ⟨fst, hfst, hlast, hblk, hadj, _, _, hpp, hTb, hTe, hchn, hbel⟩ := hloop
      refine ⟨(⟨pos, n2, 0⟩, [(pos, n2)]) :: ({ T' with power := bp N (T.base, T.len) (pos, n2) }, gT')
        :: rest', by simp, rfl, hn2, rfl, hN, ?_⟩
      have hspec := bp_spec N (T.base, T.len) (pos, n2) hadj (by simpa using hlen) hn2 hN
      refine ⟨fst, (T.base, T.len), hfst, hlast, hblk, hTb, hTe, hadj, rfl, hchn, hspec.1,
        (fun q hq => by cases hq), ?_⟩
      apply below_some hbel
      intro e g rest'' hxs
      subst hxs
      have hle := hexit _ _ e g rest'' rfl
      rcases Nat.lt_or_ge e.power (bp N (T.base, T.len) (pos, n2)) with h | h
      · exact h
      · exfalso
        obtain ⟨efst, elst, he1, he2, he3, he4, he5, he6, he7, he8, he9, _, _⟩ := hbel
        have heq : e.power = bp N (T.base, T.len) (pos, n2) := by omega
        -- boundaries (elst | fst) and (prev | new) both have power L; inner ones are larger
        have hfstN : 0 < fst.2 ∧ fst.1 + fst.2 ≤ N := hblk.2 fst (List.mem_of_mem_head? hfst)
        have hs1 := bp_spec N elst fst he6 (he3.2 elst (List.mem_of_mem_getLast? he2)).1 hfstN.1 hfstN.2
        have hmid := chn_gq N (bp N (T.base, T.len) (pos, n2)) gT' fst (T.base, T.len) hblk
          (by simpa [← hpp] using hchn) hfst hlast
        rw [← he7] at hs1
        rw [heq] at hs1
        exact no_equal_powers N _ elst fst (T.base, T.len) (pos, n2) hspec.1 hs1.2.1 hs1.2.2.1
          hspec.2.1 hspec.2.2.1 hmid

/-- Every `Below` chain is no longer than its top stored power, and that power
`L` has `2^L < 2N`. -/
theorem below_bound {N : Nat} :
    ∀ {f : Run} {ap : Option Nat} (xs : List (Slice × List Run)), 0 < f.2 → f.1 + f.2 ≤ N →
      Below N f ap xs →
      xs = [] ∨ ∃ e g rest, xs = (e, g) :: rest ∧ xs.length ≤ e.power ∧ 2 ^ e.power < 2 * N
  | _, _, [], _, _, _ => .inl rfl
  | f, _, (e, g) :: rest, hf1, hf2, h => by
    obtain ⟨fst, lst, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
    refine .inr ⟨e, g, rest, rfl, ?_, ?_⟩
    have hfst := h3.2 fst (List.mem_of_mem_head? h1)
    · rcases below_bound rest hfst.1 hfst.2 h11 with h | ⟨e', g', rest', rfl, hl, _⟩
      · subst h; simpa using h9
      · have := h10
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hlt, _⟩ := h11
        have := hlt e.power rfl
        simp at hl ⊢; omega
    · have hl := h3.2 lst (List.mem_of_mem_getLast? h2)
      rw [h7]
      exact (bp_spec N lst f h6 hl.1 hf1 hf2).2.2.2

end PyLean.ListSort
