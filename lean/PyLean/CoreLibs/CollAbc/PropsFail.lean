import PyLean.CoreLibs.CollAbc.Props
import PyLean.CoreLibs.CollAbc.PropsMap

/-!
The failure paths of the `Mapping`, `Sequence` and `throw` mixins, over any subclass's primitives. `PropsMap` and
`PropsSeq` compare the mixins with `dict` and `list`, whose primitives raise only `KeyError` and `IndexError`, so a
mixin that swallowed every exception would pass them. These statements take primitives that can raise anything.
-/

namespace PyLean.CoreLibs.CollAbc

open PyLean

/-! ### `throw` -/

/-- `Generator.throw` and the two others, every path of Lib/_collections_abc.py:374-380: the outcome for each kind of
`typ` and `val`, with and without a traceback, and not only the case where the raise succeeds. -/
def ThrowPaths : Prop :=
  ∀ (n m : String),
    throwBody (.cls n) none false = .ok ⟨n, false⟩ ∧ throwBody (.inst n) none false = .ok ⟨n, false⟩ ∧
    throwBody .other none false = .error "TypeError" ∧
    throwBody (.cls n) none true = .ok ⟨n, true⟩ ∧ throwBody (.inst n) none true = .error "TypeError" ∧
    throwBody .other none true = .error "TypeError" ∧
    throwBody (.cls n) (some (.inst m)) true = .ok ⟨m, true⟩ ∧
    throwBody (.cls n) (some (.cls m)) true = .error "TypeError" ∧
    throwBody (.cls n) (some .other) true = .error "AttributeError" ∧
    throwBody (.cls n) (some (.inst m)) false = .ok ⟨m, false⟩ ∧
    throwBody (.cls n) (some (.cls m)) false = .ok ⟨m, false⟩ ∧
    throwBody (.cls n) (some .other) false = .error "TypeError"

theorem throwPaths_proven : ThrowPaths := by
  intro n m
  simp [throwBody, raiseArg]

/-! ### `Mapping` -/

/-- `get`, `__contains__` and `ItemsView.__contains__` catch `KeyError` and nothing else, for any `__getitem__`; the
unpack in `ItemsView.__contains__` is outside the `try`. -/
def MappingPaths : Prop :=
  ∀ (K V : Type) (m : MapV K V) (E : EqOps V) (key : K) (default v value : V) (e : PyExc) (t : Bool) (n : Nat),
    (m.getitem key = .ok v →
      m.get key default = .ok v ∧ m.contains key = .ok true ∧
      m.itemsContain E (.pair key value t) = E.same v value) ∧
    (isKeyError e = true → m.getitem key = .error e →
      m.get key default = .ok default ∧ m.contains key = .ok false ∧
      m.itemsContain E (.pair key value t) = .ok false) ∧
    (isKeyError e = false → m.getitem key = .error e →
      m.get key default = .error e ∧ m.contains key = .error e ∧
      m.itemsContain E (.pair key value t) = .error e) ∧
    (m.itemsContain E (.notIterable : ItemArg K V)).raises "TypeError" ∧
    (n < 2 → m.itemsContain E (.wrongLen n t : ItemArg K V) =
      .error (.valueError s!"not enough values to unpack (expected 2, got {n})")) ∧
    (2 ≤ n → m.itemsContain E (.wrongLen n t : ItemArg K V) =
      .error (.valueError s!"too many values to unpack (expected 2, got {n})")) ∧
    (E.is_ v value = true → E.same v value = .ok true) ∧
    (E.is_ v value = false → E.same v value = E.eq v value)

theorem mappingPaths_proven : MappingPaths := by
  intro K V m E key default v value e t n
  refine ⟨?_, ?_, ?_, ⟨_, rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
  · intro h; simp [MapV.get, MapV.contains, MapV.itemsContain, h]
  · intro h1 h; simp [MapV.get, MapV.contains, MapV.itemsContain, h, h1]
  · intro h1 h; simp [MapV.get, MapV.contains, MapV.itemsContain, h, h1]
  · intro h; simp [MapV.itemsContain, h]
  · intro h
    have : ¬ n < 2 := by omega
    simp [MapV.itemsContain, this]
  · intro h; simp [EqOps.same, h, pure, Except.pure]
  · intro h; simp [EqOps.same, h]

/-! ### `MutableMapping` -/

/-- `pop`, `popitem`, `setdefault` and `update`, every path, for any primitives: which exception is swallowed, that a
failing `__delitem__` or `__setitem__` is the outcome, and the order of the steps. -/
def MMapPaths : Prop :=
  ∀ (σ K V : Type) (M : MMap σ K V) (s s' : σ) (key : K) (d v : V) (e : PyExc) (rest : List K) (kw : List (K × V))
    (o : MapV K V) (xs : List (K × V)),
    ((M.view s).getitem key = .ok v →
      M.pop s key (some d) = (do let t ← M.delitem s key; pure (v, t)) ∧
      M.setdefault s key d = .ok (v, s)) ∧
    (isKeyError e = true → (M.view s).getitem key = .error e →
      M.pop s key none = .error e ∧ M.pop s key (some d) = .ok (d, s) ∧
      M.setdefault s key d = (do let t ← M.setitem s key d; pure (d, t))) ∧
    (isKeyError e = false → (M.view s).getitem key = .error e →
      M.pop s key none = .error e ∧ M.pop s key (some d) = .error e ∧ M.setdefault s key d = .error e) ∧
    ((M.view s).iter = .error e → M.popitem s = .error e) ∧
    ((M.view s).iter = .ok [] → (M.view s).tail = none → M.popitem s = .error bareKeyError) ∧
    ((M.view s).iter = .ok [] → (M.view s).tail = some e → M.popitem s = .error e) ∧
    ((M.view s).iter = .ok (key :: rest) → (M.view s).getitem key = .error e → M.popitem s = .error e) ∧
    ((M.view s).iter = .ok (key :: rest) → (M.view s).getitem key = .ok v → M.delitem s key = .error e →
      M.popitem s = .error e) ∧
    ((M.view s).iter = .ok (key :: rest) → (M.view s).getitem key = .ok v → M.delitem s key = .ok s' →
      M.popitem s = .ok ((key, v), s')) ∧
    (o.iter = .error e → M.update s (.mapping o) kw = .error e) ∧
    (o.iter = .ok (key :: rest) → o.getitem key = .error e → M.update s (.mapping o) kw = .error e) ∧
    (M.setAll s xs = .error e → M.update s (.pairs xs) kw = .error e) ∧
    (M.setAll s xs = .ok s' → M.update s (.pairs xs) kw = M.setAll s' kw)

theorem mMapPaths_proven : MMapPaths := by
  intro σ K V M s s' key d v e rest kw o xs
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; simp [MMap.pop, MMap.setdefault, h]
  · intro h1 h; simp [MMap.pop, MMap.setdefault, h, h1]
  · intro h1 h; simp [MMap.pop, MMap.setdefault, h, h1]
  · intro h; simp [MMap.popitem, h, bind, Except.bind]
  · intro h h2; simp [MMap.popitem, h, h2, bind, Except.bind, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw]
  · intro h h2; simp [MMap.popitem, h, h2, bind, Except.bind, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw]
  · intro h h2; simp [MMap.popitem, h, h2, bind, Except.bind]
  · intro h h2 h3; simp [MMap.popitem, h, h2, h3, bind, Except.bind]
  · intro h h2 h3; simp [MMap.popitem, h, h2, h3, bind, Except.bind, pure, Except.pure]
  · intro h; simp [MMap.update, h, bind, Except.bind]
  · intro h h2; simp [MMap.update, MMap.updateKeys, h, h2, bind, Except.bind]
  · intro h; simp [MMap.update, h, bind, Except.bind]
  · intro h; simp [MMap.update, h, bind, Except.bind]

/-- `clear` is `popitem` until `KeyError`: that ends it, in the state it reached, and anything else propagates. -/
def MMapClear : Prop :=
  ∀ (σ K V : Type) (M : MMap σ K V) (fuel : Nat) (s s' : σ) (p : K × V) (e : PyExc),
    (isKeyError e = true → M.popitem s = .error e → M.clear (fuel + 1) s = .ok s) ∧
    (isKeyError e = false → M.popitem s = .error e → M.clear (fuel + 1) s = .error e) ∧
    (M.popitem s = .ok (p, s') → M.clear (fuel + 1) s = M.clear fuel s')

theorem mMapClear_proven : MMapClear := by
  intro σ K V M fuel s s' p e
  refine ⟨?_, ?_, ?_⟩
  · intro h1 h; simp [MMap.clear, h, h1]
  · intro h1 h; simp [MMap.clear, h, h1]
  · intro h; simp [MMap.clear, h]

/-! ### `Sequence` -/

/-- `xs` are the items from index `n` on. -/
def Holds {α : Type} (s : Seq α) (n : Int) (xs : List α) : Prop :=
  ∀ (j : Nat) (h : j < xs.length), s.getitem (n + j) = .ok xs[j]

section Seqs
variable {α : Type} (s : Seq α) (E : EqOps α) (value : α)

theorem Holds.tail {n : Int} {x : α} {xs : List α} (h : Holds s n (x :: xs)) : Holds s (n + 1) xs := by
  intro j hj
  have := h (j + 1) (by simpa using hj)
  have e : n + 1 + (j : Int) = n + ((j + 1 : Nat) : Int) := by omega
  rw [e]
  simpa using this

theorem Holds.head {n : Int} {x : α} {xs : List α} (h : Holds s n (x :: xs)) : s.getitem n = .ok x := by
  have := h 0 (by simp)
  simpa using this

theorem iterFrom_end (e : PyExc) (fuel : Nat) : ∀ (xs : List α) (n : Int), Holds s n xs →
    s.getitem (n + xs.length) = .error e → xs.length < fuel →
    s.iterFrom fuel n = if isIndexError e then .ok xs else .error e
  | [], n, _, h2, h3 => by
    cases fuel with
    | zero => simp at h3
    | succ f =>
      have : s.getitem n = .error e := by simpa using h2
      simp only [Seq.iterFrom, this]
  | x :: xs, n, h1, h2, h3 => by
    cases fuel with
    | zero => simp at h3
    | succ f =>
      have ih := iterFrom_end e f xs (n + 1) (h1.tail s)
        (by
          have e2 : n + 1 + (xs.length : Int) = n + ((x :: xs).length : Int) := by simp; omega
          rw [e2]; exact h2)
        (by simpa using h3)
      simp only [Seq.iterFrom, h1.head s, ih]
      split <;> simp [bind, Except.bind, pure, Except.pure]

theorem containsFrom_end (e : PyExc) (fuel : Nat) : ∀ (xs : List α) (n : Int), Holds s n xs →
    (∀ x ∈ xs, E.same x value = .ok false) → s.getitem (n + xs.length) = .error e → xs.length < fuel →
    s.containsFrom E value fuel n = if isIndexError e then .ok false else .error e
  | [], n, _, _, h2, h3 => by
    cases fuel with
    | zero => simp at h3
    | succ f =>
      have : s.getitem n = .error e := by simpa using h2
      simp only [Seq.containsFrom, this]
  | x :: xs, n, h1, hf, h2, h3 => by
    cases fuel with
    | zero => simp at h3
    | succ f =>
      have ih := containsFrom_end e f xs (n + 1) (h1.tail s) (fun y hy => hf y (by simp [hy]))
        (by
          have e2 : n + 1 + (xs.length : Int) = n + ((x :: xs).length : Int) := by simp; omega
          rw [e2]; exact h2)
        (by simpa using h3)
      have hx := hf x (by simp)
      simp [Seq.containsFrom, h1.head s, hx, bind, Except.bind, ih]

theorem containsFrom_hit (fuel : Nat) (v : α) (hv : E.same v value = .ok true) : ∀ (xs : List α) (n : Int),
    Holds s n xs → (∀ x ∈ xs, E.same x value = .ok false) → s.getitem (n + xs.length) = .ok v → xs.length < fuel →
    s.containsFrom E value fuel n = .ok true
  | [], n, _, _, h2, h3 => by
    cases fuel with
    | zero => simp at h3
    | succ f =>
      have : s.getitem n = .ok v := by simpa using h2
      simp [Seq.containsFrom, this, hv, bind, Except.bind, pure, Except.pure]
  | x :: xs, n, h1, hf, h2, h3 => by
    cases fuel with
    | zero => simp at h3
    | succ f =>
      have ih := containsFrom_hit f v hv xs (n + 1) (h1.tail s) (fun y hy => hf y (by simp [hy]))
        (by
          have e2 : n + 1 + (xs.length : Int) = n + ((x :: xs).length : Int) := by simp; omega
          rw [e2]; exact h2)
        (by simpa using h3)
      have hx := hf x (by simp)
      simp [Seq.containsFrom, h1.head s, hx, bind, Except.bind, ih]

theorem indexLoop_end (e : PyExc) (fuel : Nat) : ∀ (xs : List α) (n : Int), Holds s n xs →
    (∀ x ∈ xs, E.same x value = .ok false) → s.getitem (n + xs.length) = .error e → xs.length < fuel →
    s.indexLoop E value none fuel n = if isIndexError e then .error (.valueError "") else .error e
  | [], n, _, _, h2, h3 => by
    cases fuel with
    | zero => simp at h3
    | succ f =>
      have : s.getitem n = .error e := by simpa using h2
      simp only [Seq.indexLoop, Option.isNone_none, true_or, ↓reduceIte, this]
  | x :: xs, n, h1, hf, h2, h3 => by
    cases fuel with
    | zero => simp at h3
    | succ f =>
      have ih := indexLoop_end e f xs (n + 1) (h1.tail s) (fun y hy => hf y (by simp [hy]))
        (by
          have e2 : n + 1 + (xs.length : Int) = n + ((x :: xs).length : Int) := by simp; omega
          rw [e2]; exact h2)
        (by simpa using h3)
      have hx := hf x (by simp)
      simp [Seq.indexLoop, h1.head s, hx, bind, Except.bind, ih]

theorem indexLoop_hit (fuel : Nat) (v : α) (hv : E.same v value = .ok true) : ∀ (xs : List α) (n : Int),
    Holds s n xs → (∀ x ∈ xs, E.same x value = .ok false) → s.getitem (n + xs.length) = .ok v → xs.length < fuel →
    s.indexLoop E value none fuel n = .ok (n + xs.length)
  | [], n, _, _, h2, h3 => by
    cases fuel with
    | zero => simp at h3
    | succ f =>
      have : s.getitem n = .ok v := by simpa using h2
      simp [Seq.indexLoop, this, hv, bind, Except.bind, pure, Except.pure]
  | x :: xs, n, h1, hf, h2, h3 => by
    cases fuel with
    | zero => simp at h3
    | succ f =>
      have e2 : n + 1 + (xs.length : Int) = n + ((x :: xs).length : Int) := by simp; omega
      have ih := indexLoop_hit f v hv xs (n + 1) (h1.tail s) (fun y hy => hf y (by simp [hy]))
        (by rw [e2]; exact h2) (by simpa using h3)
      have hx := hf x (by simp)
      simp only [Seq.indexLoop, Option.isNone_none, true_or, ↓reduceIte, h1.head s]
      simp [hx, bind, Except.bind, ih, e2]

end Seqs

/-- The `Sequence` mixins over any `__getitem__`, with the items before index `n` as `xs`: `__iter__`, `__contains__` and
`index` treat `IndexError` as the end, and only that; another exception from `self[n]` reaches the caller, where catching
everything would give `xs`, `False` or `ValueError`. The first comparison that says yes ends the search, whatever
comes after it. -/
def SeqPaths : Prop :=
  ∀ (α : Type) (s : Seq α) (E : EqOps α) (value v : α) (xs : List α) (e : PyExc) (fuel : Nat),
    Holds s 0 xs → xs.length < fuel →
    (s.getitem xs.length = .error e →
      s.iterFrom fuel 0 = (if isIndexError e then .ok xs else .error e) ∧
      ((∀ x ∈ xs, E.same x value = .ok false) →
        s.containsFrom E value fuel 0 = (if isIndexError e then .ok false else .error e) ∧
        s.indexLoop E value none fuel 0 = (if isIndexError e then .error (.valueError "") else .error e))) ∧
    (s.getitem xs.length = .ok v → E.same v value = .ok true → (∀ x ∈ xs, E.same x value = .ok false) →
      s.containsFrom E value fuel 0 = .ok true ∧ s.indexLoop E value none fuel 0 = .ok xs.length)

theorem seqPaths_proven : SeqPaths := by
  intro α s E value v xs e fuel h hl
  constructor
  · intro h2
    have h2' : s.getitem (0 + xs.length) = .error e := by simpa using h2
    refine ⟨iterFrom_end s e fuel xs 0 h h2' hl, ?_⟩
    intro hf
    exact ⟨containsFrom_end s E value e fuel xs 0 h hf h2' hl, indexLoop_end s E value e fuel xs 0 h hf h2' hl⟩
  · intro h2 hv hf
    have h2' : s.getitem (0 + xs.length) = .ok v := by simpa using h2
    have i := indexLoop_hit s E value fuel v hv xs 0 h hf h2' hl
    exact ⟨containsFrom_hit s E value fuel v hv xs 0 h hf h2' hl, by simpa using i⟩

/-- `MutableSequence.clear`, `extend` and `remove`: `clear` is `pop` until `IndexError`, in the state it reached, and
anything else propagates; `extend(self)` reads the items first, so that it terminates; a failing `append` stops `extend`
in the middle, and a failing `index` means nothing is deleted. -/
def MSeqPaths : Prop :=
  ∀ (σ α : Type) (M : MSeq σ α) (E : EqOps α) (fuel : Nat) (s s' : σ) (v : α) (p : α × σ) (vs : List α) (e : PyExc)
    (i : Int),
    (isIndexError e = true → M.pop s = .error e → M.clear (fuel + 1) s = .ok s) ∧
    (isIndexError e = false → M.pop s = .error e → M.clear (fuel + 1) s = .error e) ∧
    (M.pop s = .ok p → M.clear (fuel + 1) s = M.clear fuel p.2) ∧
    (M.append s v = .error e → M.extend s (some (v :: vs)) fuel = .error e) ∧
    (M.append s v = .ok s' → M.extend s (some (v :: vs)) fuel = M.extendList s' vs) ∧
    ((M.view s).iterFrom fuel 0 = .error e → M.extend s none fuel = .error e) ∧
    ((M.view s).iterFrom fuel 0 = .ok vs → M.extend s none fuel = M.extendList s vs) ∧
    ((M.view s).index E v 0 none fuel = .error e → M.remove E s v fuel = .error e) ∧
    ((M.view s).index E v 0 none fuel = .ok i → M.remove E s v fuel = M.delitem s i)

theorem mSeqPaths_proven : MSeqPaths := by
  intro σ α M E fuel s s' v p vs e i
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h1 h; simp [MSeq.clear, h, h1]
  · intro h1 h; simp [MSeq.clear, h, h1]
  · intro h; obtain ⟨a, b⟩ := p; simp [MSeq.clear, h]
  · intro h; simp [MSeq.extend, MSeq.extendList, h, bind, Except.bind]
  · intro h; simp [MSeq.extend, MSeq.extendList, h, bind, Except.bind]
  · intro h; simp [MSeq.extend, h, bind, Except.bind]
  · intro h; simp [MSeq.extend, h, bind, Except.bind]
  · intro h; simp [MSeq.remove, h, bind, Except.bind]
  · intro h; simp [MSeq.remove, h, bind, Except.bind]

/-! ### `Set`, with iterators that fail after their items -/

section Sets
variable {α : Type}

theorem allInT_all (c : α → Py Bool) (t : Option PyExc) : ∀ xs : List α, (∀ x ∈ xs, c x = .ok true) →
    allInT c t xs = raiseTail t true
  | [], _ => rfl
  | x :: xs, h => by
    have hx := h x (by simp)
    simp [allInT, hx, bind, Except.bind, allInT_all c t xs (fun y hy => h y (by simp [hy]))]

theorem allInT_no (c : α → Py Bool) (t : Option PyExc) (z : α) (post : List α) (hz : c z = .ok false) :
    ∀ pre : List α, (∀ x ∈ pre, c x = .ok true) → allInT c t (pre ++ z :: post) = .ok false
  | [], _ => by simp [allInT, hz, bind, Except.bind, pure, Except.pure]
  | x :: xs, h => by
    have hx := h x (by simp)
    simp [allInT, hx, bind, Except.bind, allInT_no c t z post hz xs (fun y hy => h y (by simp [hy]))]

theorem allInT_err (c : α → Py Bool) (t : Option PyExc) (z : α) (post : List α) (e : PyExc) (hz : c z = .error e) :
    ∀ pre : List α, (∀ x ∈ pre, c x = .ok true) → allInT c t (pre ++ z :: post) = .error e
  | [], _ => by simp [allInT, hz, bind, Except.bind]
  | x :: xs, h => by
    have hx := h x (by simp)
    simp [allInT, hx, bind, Except.bind, allInT_err c t z post e hz xs (fun y hy => h y (by simp [hy]))]

theorem filterT_all (c : α → Py Bool) (p : α → Bool) (t : Option PyExc) : ∀ xs : List α,
    (∀ x ∈ xs, c x = .ok (p x)) → filterT c t xs = raiseTail t (xs.filter p) ∨ (∃ e, t = some e ∧ filterT c t xs = .error e)
  | [], _ => Or.inl rfl
  | x :: xs, h => by
    have hx := h x (by simp)
    rcases filterT_all c p t xs (fun y hy => h y (by simp [hy])) with h1 | ⟨e, h1, h2⟩
    · cases t with
      | none =>
        left
        simp only [raiseTail] at h1
        simp only [filterT, hx, h1, bind, Except.bind, pure, Except.pure, raiseTail, List.filter_cons]
      | some e =>
        right
        refine ⟨e, rfl, ?_⟩
        simp only [raiseTail] at h1
        simp [filterT, hx, h1, bind, Except.bind]
    · right
      exact ⟨e, h1, by simp [filterT, hx, h2, bind, Except.bind]⟩

theorem filterT_err (c : α → Py Bool) (t : Option PyExc) (z : α) (post : List α) (e : PyExc) (hz : c z = .error e) :
    ∀ pre : List α, (∀ x ∈ pre, ∃ b, c x = .ok b) → filterT c t (pre ++ z :: post) = .error e
  | [], _ => by simp [filterT, hz, bind, Except.bind]
  | x :: xs, h => by
    obtain ⟨b, hx⟩ := h x (by simp)
    simp [filterT, hx, bind, Except.bind, filterT_err c t z post e hz xs (fun y hy => h y (by simp [hy]))]

end Sets

/-- The comparisons of `Set`, for any primitives. The lengths decide first, so a failing `__iter__` is not reached when
they already answer. A failing `__len__` is the outcome. In the loop, an element that is missing returns `False` at once,
even if the iterator would have raised afterwards, and a raising `__contains__` or iterator is the outcome. -/
def SetCmpPaths : Prop :=
  ∀ (α : Type) (self o : SetV α) (n m : Nat) (xs pre post : List α) (z : α) (e : PyExc),
    self.len = .ok n → o.len = .ok m →
    (n > m → self.le (.set o) = .ok (.val false) ∧ self.lt (.set o) = .ok (.val false) ∧
      self.eq (.set o) = .ok (.val false)) ∧
    (n < m → self.ge (.set o) = .ok (.val false) ∧ self.gt (.set o) = .ok (.val false) ∧
      self.eq (.set o) = .ok (.val false)) ∧
    (n ≤ m →
      (self.iter = .error e → self.le (.set o) = .error e) ∧
      (self.iter = .ok (pre ++ z :: post) → (∀ x ∈ pre, o.contains x = .ok true) → o.contains z = .ok false →
        self.le (.set o) = .ok (.val false)) ∧
      (self.iter = .ok (pre ++ z :: post) → (∀ x ∈ pre, o.contains x = .ok true) → o.contains z = .error e →
        self.le (.set o) = .error e) ∧
      (self.iter = .ok xs → (∀ x ∈ xs, o.contains x = .ok true) →
        self.le (.set o) = (match self.tail with
          | none => .ok (.val true)
          | some e => .error e))) ∧
    (m ≤ n →
      (o.iter = .error e → self.ge (.set o) = .error e) ∧
      (o.iter = .ok (pre ++ z :: post) → (∀ x ∈ pre, self.contains x = .ok true) → self.contains z = .ok false →
        self.ge (.set o) = .ok (.val false))) ∧
    (n < m → self.lt (.set o) = self.le (.set o)) ∧ (m < n → self.gt (.set o) = self.ge (.set o)) ∧
    (n = m → self.eq (.set o) = self.le (.set o)) ∧
    (n = m → self.lt (.set o) = .ok (.val false) ∧ self.gt (.set o) = .ok (.val false)) ∧
    (∀ t ys, self.le (.iterable ys t) = .ok .notImplemented) ∧ self.le .other = .ok .notImplemented

theorem setCmpPaths_proven : SetCmpPaths := by
  intro α self o n m xs pre post z e h1 h2
  have hle : ∀ h : n ≤ m, ¬ n > m := fun h => by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun _ _ => rfl, rfl⟩
  · intro h
    have h3 : ¬ n < m := by omega
    have h4 : n ≠ m := by omega
    simp [SetV.le, SetV.lt, SetV.eq, h1, h2, h, h3, h4, bind, Except.bind, pure, Except.pure]
  · intro h
    have h3 : ¬ n > m := by omega
    have h4 : n ≠ m := by omega
    simp [SetV.ge, SetV.gt, SetV.eq, h1, h2, h, h3, h4, bind, Except.bind, pure, Except.pure]
  · intro h
    have h3 := hle h
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h4; simp [SetV.le, h1, h2, h3, h4, bind, Except.bind]
    · intro h4 h5 h6
      have := allInT_no o.contains self.tail z post h6 pre h5
      simp [SetV.le, h1, h2, h3, h4, this, bind, Except.bind, pure, Except.pure]
    · intro h4 h5 h6
      have := allInT_err o.contains self.tail z post e h6 pre h5
      simp [SetV.le, h1, h2, h3, h4, this, bind, Except.bind]
    · intro h4 h5
      have := allInT_all o.contains self.tail xs h5
      simp only [SetV.le, h1, h2, bind, Except.bind, pure, Except.pure, h3, if_false, h4, this]
      cases self.tail <;> rfl
  · intro h
    have h3 : ¬ n < m := by omega
    refine ⟨?_, ?_⟩
    · intro h4; simp [SetV.ge, h1, h2, h3, h4, bind, Except.bind]
    · intro h4 h5 h6
      have := allInT_no self.contains o.tail z post h6 pre h5
      simp [SetV.ge, h1, h2, h3, h4, this, bind, Except.bind, pure, Except.pure]
  · intro h; simp [SetV.lt, h1, h2, h, bind, Except.bind]
  · intro h
    have h3 : n > m := by omega
    simp [SetV.gt, h1, h2, h3, bind, Except.bind]
  · intro h; simp [SetV.eq, h1, h2, h, bind, Except.bind]
  · intro h
    subst h
    simp [SetV.lt, SetV.gt, h1, h2, bind, Except.bind, pure, Except.pure]

/-- The algebra of `Set`, for any primitives: `&` keeps what `__contains__` accepts, in the order of `other`; a raising
`__contains__` is the outcome, ahead of an iterator failure further on; an iterator that raises after its items is the
outcome; and `isdisjoint` answers `False` at the first common element, before that failure. -/
def SetAlgPaths : Prop :=
  ∀ (α β : Type) (self : SetV α) (f : List α → β) (ys pre post : List α) (z : α) (e : PyExc) (p : α → Bool)
    (t : Option PyExc),
    self.and f (.iterable (.error e) t) = .error e ∧
    ((∀ x ∈ ys, self.contains x = .ok (p x)) → self.and f (.iterable (.ok ys)) = .ok (.val (f (ys.filter p)))) ∧
    ((∀ x ∈ pre, ∃ b, self.contains x = .ok b) → self.contains z = .error e →
      self.and f (.iterable (.ok (pre ++ z :: post)) t) = .error e) ∧
    ((∀ x ∈ ys, self.contains x = .ok (p x)) → self.and f (.iterable (.ok ys) (some e)) = .error e) ∧
    self.and f .other = .ok .notImplemented ∧
    ((∀ x ∈ pre, self.contains x = .ok false) → self.contains z = .ok true →
      self.isdisjoint (.iterable (.ok (pre ++ z :: post)) t) = .ok false) ∧
    ((∀ x ∈ ys, self.contains x = .ok false) → self.isdisjoint (.iterable (.ok ys) (some e)) = .error e) ∧
    (self.iter = .error e → self.or f (.iterable (.ok ys) t) = .error e) ∧
    (self.iter = .ok pre → self.tail = some e → self.or f (.iterable (.ok ys) t) = .error e) ∧
    (self.iter = .ok pre → self.tail = none → self.or f (.iterable (.ok ys)) = .ok (.val (f (pre ++ ys)))) ∧
    (self.iter = .ok pre → self.tail = none → self.or f (.iterable (.ok ys) (some e)) = .error e) ∧
    (self.isdisjoint .other).raises "TypeError"

theorem isdisjoint_hit {α : Type} (self : SetV α) (o : Operand α) (z : α) (post : List α)
    (hz : self.contains z = .ok true) : ∀ pre : List α, (∀ x ∈ pre, self.contains x = .ok false) →
    SetV.isdisjoint.go self o (pre ++ z :: post) = .ok false
  | [], _ => by simp [SetV.isdisjoint.go, hz, bind, Except.bind, pure, Except.pure]
  | x :: xs, h => by
    have hx := h x (by simp)
    simp [SetV.isdisjoint.go, hx, bind, Except.bind, isdisjoint_hit self o z post hz xs (fun y hy => h y (by simp [hy]))]

theorem isdisjoint_tail {α : Type} (self : SetV α) (o : Operand α) (e : PyExc) (ht : o.tail = some e) :
    ∀ ys : List α, (∀ x ∈ ys, self.contains x = .ok false) → SetV.isdisjoint.go self o ys = .error e
  | [], _ => by simp [SetV.isdisjoint.go, ht, raiseTail]
  | x :: xs, h => by
    have hx := h x (by simp)
    simp [SetV.isdisjoint.go, hx, bind, Except.bind, isdisjoint_tail self o e ht xs (fun y hy => h y (by simp [hy]))]

theorem setAlgPaths_proven : SetAlgPaths := by
  intro α β self f ys pre post z e p t
  refine ⟨rfl, ?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ⟨_, rfl, rfl⟩⟩
  · intro h
    rcases filterT_all self.contains p none ys h with h1 | ⟨_, h2, _⟩
    · simp [SetV.and, Operand.items?, Operand.tail, bind, Except.bind, pure, Except.pure] at h1 ⊢
      rw [h1]
      rfl
    · cases h2
  · intro h1 h2
    have := filterT_err self.contains t z post e h2 pre h1
    simp [SetV.and, Operand.items?, Operand.tail, this, bind, Except.bind]
  · intro h
    rcases filterT_all self.contains p (some e) ys h with h1 | ⟨e', h2, h3⟩
    · simp only [raiseTail] at h1
      simp [SetV.and, Operand.items?, Operand.tail, h1, bind, Except.bind]
    · cases h2
      simp [SetV.and, Operand.items?, Operand.tail, h3, bind, Except.bind]
  · intro h1 h2
    have := isdisjoint_hit self (.iterable (.ok (pre ++ z :: post)) t) z post h2 pre h1
    simp only [SetV.isdisjoint, Operand.items?, bind, Except.bind]
    exact this
  · intro h
    have := isdisjoint_tail self (.iterable (.ok ys) (some e)) e rfl ys h
    simp only [SetV.isdisjoint, Operand.items?, bind, Except.bind]
    exact this
  · intro h; simp [SetV.or, Operand.items?, h, bind, Except.bind]
  · intro h h2; simp [SetV.or, Operand.items?, h, h2, raiseTail, bind, Except.bind]
  · intro h h2; simp [SetV.or, Operand.items?, Operand.tail, h, h2, raiseTail, bind, Except.bind, pure, Except.pure]
  · intro h h2; simp [SetV.or, Operand.items?, Operand.tail, h, h2, raiseTail, bind, Except.bind]

/-- `-`, the reflected `-` and `^`, for any primitives: a plain iterable goes through `_from_iterable` first, whole, so
its failure comes before anything else; then the elements of the left side are tested against the right one. -/
def SetSubPaths : Prop :=
  ∀ (α : Type) (self o : SetV α) (f : List α → SetV α) (ys xs : List α) (e : PyExc) (t : Option PyExc)
    (p : α → Bool),
    self.sub f (.iterable (.error e) t) = .error e ∧ self.rsub f (.iterable (.error e) t) = .error e ∧
    self.xor f (.iterable (.error e) t) = .error e ∧
    self.sub f (.iterable (.ok ys) (some e)) = .error e ∧ self.rsub f (.iterable (.ok ys) (some e)) = .error e ∧
    self.xor f (.iterable (.ok ys) (some e)) = .error e ∧
    self.sub f .other = .ok .notImplemented ∧ self.rsub f .other = .ok .notImplemented ∧
    self.xor f .other = .ok .notImplemented ∧
    (self.iter = .error e → self.sub f (.set o) = .error e) ∧
    (o.iter = .error e → self.rsub f (.set o) = .error e) ∧
    (self.iter = .ok xs → self.tail = none → (∀ x ∈ xs, o.contains x = .ok (p x)) →
      self.sub f (.set o) = .ok (.val (f (xs.filter (fun x => !p x)))))

theorem notInT_all {α : Type} (s : SetV α) (p : α → Bool) : ∀ xs : List α, (∀ x ∈ xs, s.contains x = .ok (p x)) →
    notInT s none xs = .ok (xs.filter (fun x => !p x))
  | [], _ => rfl
  | x :: xs, h => by
    have hx := h x (by simp)
    have ih := notInT_all s p xs (fun y hy => h y (by simp [hy]))
    simp only [notInT_none] at ih ⊢
    simp only [notIn, filterPy, hx, bind, Except.bind, pure, Except.pure, List.filter_cons] at ih ⊢
    rw [ih]

theorem setSubPaths_proven : SetSubPaths := by
  intro α self o f ys xs e t p
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [SetV.sub, Operand.asSet?, bind, Except.bind]
  · simp [SetV.rsub, Operand.asSet?, bind, Except.bind]
  · simp [SetV.xor, Operand.asSet?, bind, Except.bind]
  · simp [SetV.sub, Operand.asSet?, raiseTail, bind, Except.bind]
  · simp [SetV.rsub, Operand.asSet?, raiseTail, bind, Except.bind]
  · simp [SetV.xor, Operand.asSet?, raiseTail, bind, Except.bind]
  · intro h; simp [SetV.sub, Operand.asSet?, h, bind, Except.bind]
  · intro h; simp [SetV.rsub, Operand.asSet?, h, bind, Except.bind]
  · intro h1 h2 h3
    have := notInT_all o p xs h3
    simp [SetV.sub, Operand.asSet?, h1, h2, this, bind, Except.bind, pure, Except.pure]

/-- `MutableSet`, every path, for any primitives: `remove` raises `KeyError` only when the element is absent; `pop` turns
the end of the iterator into `KeyError`, and passes any other exception through; `clear` stops at `KeyError` only;
`|=` and `-=` stop at the first failing `add` or `discard`, and an iterator that raises after its items is the outcome. -/
def MSetPaths : Prop :=
  ∀ (σ α : Type) (M : MSet σ α) (fuel : Nat) (s s' : σ) (v : α) (vs : List α) (e : PyExc) (p : α × σ),
    ((M.view s).contains v = .error e → M.remove s v = .error e) ∧
    ((M.view s).contains v = .ok false → M.remove s v = .error (.keyError "~value")) ∧
    ((M.view s).contains v = .ok true → M.remove s v = M.discard s v) ∧
    ((M.view s).iter = .error e → M.pop s = .error e) ∧
    ((M.view s).iter = .ok [] → (M.view s).tail = none → M.pop s = .error bareKeyError) ∧
    ((M.view s).iter = .ok [] → (M.view s).tail = some e → M.pop s = .error e) ∧
    ((M.view s).iter = .ok (v :: vs) → M.discard s v = .error e → M.pop s = .error e) ∧
    ((M.view s).iter = .ok (v :: vs) → M.discard s v = .ok s' → M.pop s = .ok (v, s')) ∧
    (isKeyError e = true → M.pop s = .error e → M.clear (fuel + 1) s = .ok s) ∧
    (isKeyError e = false → M.pop s = .error e → M.clear (fuel + 1) s = .error e) ∧
    (M.pop s = .ok p → M.clear (fuel + 1) s = M.clear fuel p.2) ∧
    M.ior s .other = .error (.typeError "~object is not iterable") ∧
    M.ior s (.iterable (.error e)) = .error e ∧
    (M.add s v = .error e → M.ior s (.iterable (.ok (v :: vs))) = .error e) ∧
    (M.add s v = .ok s' → M.ior s (.iterable (.ok (v :: vs))) = forAdd M.add s' vs) ∧
    M.ior s (.iterable (.ok []) (some e)) = .error e ∧
    (M.discard s v = .error e → M.isub s (some (.iterable (.ok (v :: vs)))) fuel = .error e) ∧
    M.isub s (some (.iterable (.ok []) (some e))) fuel = .error e ∧
    M.isub s none fuel = M.clear fuel s ∧ M.ixor s none fuel = M.clear fuel s

theorem mSetPaths_proven : MSetPaths := by
  intro σ α M fuel s s' v vs e p
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩
  · intro h; simp [MSet.remove, h, bind, Except.bind]
  · intro h; simp [MSet.remove, h, bind, Except.bind, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw]
  · intro h; simp [MSet.remove, h, bind, Except.bind]
  · intro h; simp [MSet.pop, h, bind, Except.bind]
  · intro h h2; simp [MSet.pop, h, h2, bind, Except.bind, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw]
  · intro h h2; simp [MSet.pop, h, h2, bind, Except.bind, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw]
  · intro h h2; simp [MSet.pop, h, h2, bind, Except.bind]
  · intro h h2; simp [MSet.pop, h, h2, bind, Except.bind, pure, Except.pure]
  · intro h1 h; simp [MSet.clear, h, h1]
  · intro h1 h; simp [MSet.clear, h, h1]
  · intro h; obtain ⟨a, b⟩ := p; simp [MSet.clear, h]
  · simp [MSet.ior, Operand.items?, bind, Except.bind]
  · intro h; simp [MSet.ior, Operand.items?, Operand.tail, forAddT, h, bind, Except.bind]
  · intro h; simp [MSet.ior, Operand.items?, Operand.tail, forAddT, h, bind, Except.bind]
  · simp [MSet.ior, Operand.items?, Operand.tail, forAddT, raiseTail, bind, Except.bind]
  · intro h; simp [MSet.isub, Operand.items?, Operand.tail, forAddT, h, bind, Except.bind]
  · simp [MSet.isub, Operand.items?, Operand.tail, forAddT, raiseTail, bind, Except.bind]

/-- `ValuesView.__contains__` stops at the first match, so a mapping whose iterator raises afterwards still answers; `for`
over the mapping raises it only if the search reaches the end. -/
def ValuesTail : Prop :=
  ∀ (K V : Type) (m : MapV K V) (E : EqOps V) (value v : V) (k : K) (rest : List K) (e : PyExc),
    m.iter = .ok (k :: rest) → m.getitem k = .ok v → E.same v value = .ok true → m.valuesContain E value = .ok true

theorem valuesTail_proven : ValuesTail := by
  intro K V m E value v k rest e h1 h2 h3
  simp [MapV.valuesContain, MapV.valuesContain.go, h1, h2, h3, bind, Except.bind, pure, Except.pure]

end PyLean.CoreLibs.CollAbc
