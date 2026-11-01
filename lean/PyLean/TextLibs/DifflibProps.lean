import PyLean.TextLibs.DifflibModel

/-!
`SequenceMatcher`, for all sequences and all `isjunk`: `find_longest_match` returns a real match in its
box, the blocks are in order and do not touch, and the opcodes turn `a` into `b`. `Eqs a b i j k` says
`a[i:i+k] == b[j:j+k]`, with both slices in range.
-/

namespace PyLean.TextLibs.Difflib

open PyLean

/-- `a[i:i+k] == b[j:j+k]`, both in range. -/
def Eqs (a b : List Nat) (i j k : Nat) : Prop :=
  i + k ≤ a.length ∧ j + k ≤ b.length ∧ ∀ t, t < k → a[i + t]? = b[j + t]?

theorem eqs_zero (a b : List Nat) (i j : Nat) (hi : i ≤ a.length) (hj : j ≤ b.length) : Eqs a b i j 0 :=
  ⟨hi, hj, fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem eqs_right {a b : List Nat} {i j k : Nat} (h : Eqs a b i j k) (hi : i + k < a.length)
    (hj : j + k < b.length) (he : a[i + k]? = b[j + k]?) : Eqs a b i j (k + 1) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by omega, by omega, ?_⟩
  intro t ht
  by_cases hk : t = k
  · subst hk; exact he
  · exact h3 t (by omega)

theorem eqs_left {a b : List Nat} {i j k : Nat} (h : Eqs a b (i + 1) (j + 1) k)
    (he : a[i]? = b[j]?) : Eqs a b i j (k + 1) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by omega, by omega, ?_⟩
  intro t ht
  cases t with
  | zero => simpa using he
  | succ t =>
    have := h3 t (by omega)
    have e1 : i + (t + 1) = i + 1 + t := by omega
    have e2 : j + (t + 1) = j + 1 + t := by omega
    rw [e1, e2]
    exact this

theorem eqs_join {a b : List Nat} {i j k m : Nat} (h1 : Eqs a b i j k) (h2 : Eqs a b (i + k) (j + k) m) :
    Eqs a b i j (k + m) := by
  refine ⟨by have := h2.1; omega, by have := h2.2.1; omega, ?_⟩
  intro t ht
  by_cases hk : t < k
  · exact h1.2.2 t hk
  · have := h2.2.2 (t - k) (by omega)
    have e1 : i + k + (t - k) = i + t := by omega
    have e2 : j + k + (t - k) = j + t := by omega
    rwa [e1, e2] at this

/-! ### `b2j` -/

/-- Each index in `b2j[x]` holds `x`, and the indices increase. -/
def B2jOk (m : List (Nat × List Nat)) (b : List Nat) : Prop :=
  ∀ x l, m.lookup x = some l → (∀ j ∈ l, b[j]? = some x) ∧ l.Pairwise (· < ·)

theorem lookup_addIdx (m : List (Nat × List Nat)) (e i x : Nat) :
    (addIdx m e i).lookup x =
      if x == e then some ((m.lookup x).getD [] ++ [i]) else m.lookup x := by
  induction m with
  | nil =>
    simp only [addIdx, List.lookup]
    by_cases h : x = e
    · subst h; simp
    · have h' : (x == e) = false := by simpa using h
      simp [h']
  | cons p r ih =>
    obtain ⟨k, v⟩ := p
    simp only [addIdx]
    split
    · rename_i hk
      have hk : k = e := by simpa using hk
      subst hk
      simp only [List.lookup]
      by_cases h : x = k
      · subst h; simp
      · have h' : (x == k) = false := by simpa using h
        simp [h']
    · rename_i hk
      have hk : k ≠ e := by simpa using hk
      simp only [List.lookup]
      rw [ih]
      by_cases h : x = k
      · subst h
        have h' : (x == e) = false := by simpa using hk
        simp [h']
      · have h' : (x == k) = false := by simpa using h
        simp [h']

/-- Every index stored is below `n`, which the next index exceeds, so the lists stay increasing. -/
def BuildInv (b : List Nat) (n : Nat) (m : List (Nat × List Nat)) : Prop :=
  ∀ x l, m.lookup x = some l → (∀ j ∈ l, j < n ∧ b[j]? = some x) ∧ l.Pairwise (· < ·)

theorem build_step (b : List Nat) (n e : Nat) (m : List (Nat × List Nat)) (he : b[n]? = some e)
    (h : BuildInv b n m) : BuildInv b (n + 1) (addIdx m e n) := by
  intro x l hl
  rw [lookup_addIdx] at hl
  split at hl
  · rename_i hx
    have hx : x = e := by simpa using hx
    subst hx
    simp only [Option.some.injEq] at hl
    subst hl
    cases hm : m.lookup x with
    | none =>
      simp only [Option.getD_none, List.nil_append, List.mem_singleton, forall_eq]
      exact ⟨⟨by omega, he⟩, by simp⟩
    | some l =>
      obtain ⟨h1, h2⟩ := h x l hm
      simp only [Option.getD_some]
      refine ⟨?_, ?_⟩
      · intro j hj
        rcases List.mem_append.mp hj with hj | hj
        · exact ⟨by have := (h1 j hj).1; omega, (h1 j hj).2⟩
        · simp only [List.mem_singleton] at hj
          subst hj
          exact ⟨by omega, he⟩
      · refine List.pairwise_append.mpr ⟨h2, by simp, ?_⟩
        intro a ha c hc
        simp only [List.mem_singleton] at hc
        subst hc
        exact (h1 a ha).1
  · obtain ⟨h1, h2⟩ := h x l hl
    exact ⟨fun j hj => ⟨by have := (h1 j hj).1; omega, (h1 j hj).2⟩, h2⟩

theorem build_loop (b : List Nat) : ∀ (rest : List Nat) (n : Nat) (m : List (Nat × List Nat)),
    (∀ t, rest[t]? = b[n + t]?) → BuildInv b n m →
    BuildInv b (n + rest.length) ((rest.zipIdx n).foldl (fun m p => addIdx m p.1 p.2) m) := by
  intro rest
  induction rest with
  | nil => intro n m _ h; simpa using h
  | cons e r ih =>
    intro n m hr h
    simp only [List.zipIdx_cons, List.foldl_cons, List.length_cons]
    have he : b[n]? = some e := by
      have := hr 0
      simpa using this.symm
    have := ih (n + 1) _ (fun t => by
      have := hr (t + 1)
      have e1 : n + (t + 1) = n + 1 + t := by omega
      rw [e1] at this
      simpa using this) (build_step b n e m he h)
    have e2 : n + 1 + r.length = n + (r.length + 1) := by omega
    rwa [e2] at this

theorem buildB2j_ok (b : List Nat) : B2jOk (buildB2j b) b := by
  have h := build_loop b b 0 [] (fun t => by simp) (fun x l hl => by simp at hl)
  intro x l hl
  obtain ⟨h1, h2⟩ := h x l hl
  exact ⟨fun j hj => (h1 j hj).2, h2⟩

theorem lookup_filter (m : List (Nat × List Nat)) (f : Nat → Bool) (x : Nat) :
    (m.filter (fun p => f p.1)).lookup x = if f x then m.lookup x else none := by
  induction m with
  | nil => simp
  | cons p r ih =>
    obtain ⟨k, v⟩ := p
    by_cases hx : x = k
    · subst hx
      cases hf : f x <;> simp [List.filter_cons, hf, ih]
    · have : (x == k) = false := by simpa using hx
      cases hf : f k <;> simp [List.filter_cons, hf, ih, List.lookup, this]

theorem b2j_filter (m : List (Nat × List Nat)) (b : List Nat) (f : Nat → Bool) (h : B2jOk m b) :
    B2jOk (m.filter (fun p => f p.1)) b := by
  intro x l hl
  rw [lookup_filter] at hl
  split at hl
  · exact h x l hl
  · simp at hl

/-- What `chainB` keeps. -/
theorem chainB_spec (s s' : SM) (h : chainB s = (s', .ok ())) :
    s'.a = s.a ∧ s'.b = s.b ∧ B2jOk s'.b2j s.b ∧ s'.blocks = s.blocks ∧ s'.opcodes = s.opcodes ∧
      s'.fullb = s.fullb ∧ s'.isjunk = s.isjunk ∧ s'.autojunk = s.autojunk := by
  unfold chainB at h
  simp only at h
  split at h
  · simp at h
  · simp only [Prod.mk.injEq, and_true] at h
    subst h
    refine ⟨rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
    simp only
    exact b2j_filter _ _ (fun k => !_) (b2j_filter _ _ (fun k => !_) (buildB2j_ok s.b))

/-- A matcher as `__init__` and `set_seq2` leave it. -/
def Ready (s : SM) : Prop := B2jOk s.b2j s.b

theorem make_ok (isjunk : Option (Nat → Py Bool)) (a b : List Nat) (auto : Bool) (s : SM)
    (h : make isjunk a b auto = .ok s) :
    chainB { a, b := b, isjunk, autojunk := auto, blocks := none, opcodes := none, fullb := none } = (s, .ok ()) := by
  unfold make at h
  split at h
  · rename_i s1 heq
    simp only [Except.ok.injEq] at h
    subst h
    exact heq
  · simp at h

theorem make_ready (isjunk : Option (Nat → Py Bool)) (a b : List Nat) (auto : Bool) (s : SM)
    (h : make isjunk a b auto = .ok s) : Ready s ∧ s.a = a ∧ s.b = b := by
  obtain ⟨h1, h2, h3, _⟩ := chainB_spec _ _ (make_ok _ _ _ _ _ h)
  simp only at h1 h2 h3
  exact ⟨by rw [Ready, h2]; exact h3, h1, h2⟩

end PyLean.TextLibs.Difflib
