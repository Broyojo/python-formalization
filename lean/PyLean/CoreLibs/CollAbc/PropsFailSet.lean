import PyLean.CoreLibs.CollAbc.PropsFail

/-!
The failure paths of the `Set` and `MutableSet` mixins over any subclass's primitives: a failing `__len__`, `__iter__`
or `__contains__`, an iterator that raises after its items, and a `_from_iterable` that consumes its argument as the
generator produces it and can raise at any element.
-/

namespace PyLean.CoreLibs.CollAbc

open PyLean

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

theorem feedIf_pure {ρ β : Type} (B : FromIter ρ α β) (keep : α → Py Bool) (p : α → Bool) (t : Option PyExc) :
    ∀ (xs : List α) (r : ρ), (∀ x ∈ xs, keep x = .ok (p x)) → feedIf B keep t r xs = feedAll B t r (xs.filter p)
  | [], _, _ => rfl
  | x :: xs, r, h => by
    have hx := h x (by simp)
    have ih := fun r => feedIf_pure B keep p t xs r (fun y hy => h y (by simp [hy]))
    cases hp : p x with
    | true =>
      simp only [feedIf, hx, hp, bind, Except.bind, ite_true, List.filter_cons, feedAll]
      cases B.push r x <;> simp [ih]
    | false =>
      simp only [feedIf, hx, hp, bind, Except.bind, List.filter_cons, Bool.false_eq_true, ite_false]
      exact ih r

theorem feedIf_skip_err {ρ β : Type} (B : FromIter ρ α β) (keep : α → Py Bool) (t : Option PyExc) (z : α)
    (post : List α) (e : PyExc) (hz : keep z = .error e) :
    ∀ (pre : List α) (r : ρ), (∀ x ∈ pre, keep x = .ok false) → feedIf B keep t r (pre ++ z :: post) = .error e
  | [], r, _ => by simp [feedIf, hz, bind, Except.bind]
  | x :: xs, r, h => by
    have hx := h x (by simp)
    simp only [List.cons_append, feedIf, hx, bind, Except.bind, Bool.false_eq_true, ite_false]
    exact feedIf_skip_err B keep t z post e hz xs r (fun y hy => h y (by simp [hy]))

theorem disjoint_hit (c : α → Py Bool) (t : Option PyExc) (z : α) (post : List α) (hz : c z = .ok true) :
    ∀ pre : List α, (∀ x ∈ pre, c x = .ok false) → disjointLoop c t (pre ++ z :: post) = .ok false
  | [], _ => by simp [disjointLoop, hz, bind, Except.bind, pure, Except.pure]
  | x :: xs, h => by
    have hx := h x (by simp)
    simp [disjointLoop, hx, bind, Except.bind, disjoint_hit c t z post hz xs (fun y hy => h y (by simp [hy]))]

theorem disjoint_err (c : α → Py Bool) (t : Option PyExc) (z : α) (post : List α) (e : PyExc) (hz : c z = .error e) :
    ∀ pre : List α, (∀ x ∈ pre, c x = .ok false) → disjointLoop c t (pre ++ z :: post) = .error e
  | [], _ => by simp [disjointLoop, hz, bind, Except.bind]
  | x :: xs, h => by
    have hx := h x (by simp)
    simp [disjointLoop, hx, bind, Except.bind, disjoint_err c t z post e hz xs (fun y hy => h y (by simp [hy]))]

theorem disjoint_all (c : α → Py Bool) (t : Option PyExc) : ∀ xs : List α, (∀ x ∈ xs, c x = .ok false) →
    disjointLoop c t xs = raiseTail t true
  | [], _ => rfl
  | x :: xs, h => by
    have hx := h x (by simp)
    simp [disjointLoop, hx, bind, Except.bind, disjoint_all c t xs (fun y hy => h y (by simp [hy]))]

end Sets

/-- The comparisons of `Set`, for any primitives. A failing `len(self)`, then a failing `len(other)`, is the outcome of
all five. The lengths decide next, so a failing `__iter__` is not reached when they already answer. In the loops of
`__le__` and `__ge__`, an element that is missing returns `False` at once, even if the iterator would have raised
afterwards; a raising `__contains__` is the outcome; when every element is contained, the iterator's end is: `True`,
or its exception. A non-`Set` is `NotImplemented`. Lib/_collections_abc.py:562-595. -/
def SetCmpPaths : Prop :=
  ∀ (α : Type) (self o : SetV α) (n m : Nat) (xs pre post : List α) (z : α) (e : PyExc) (abc : Bool)
    (it : Py (List α)) (t : Option PyExc),
    (self.len = .error e → self.le (.set o) = .error e ∧ self.lt (.set o) = .error e ∧
      self.ge (.set o) = .error e ∧ self.gt (.set o) = .error e ∧ self.eq (.set o) = .error e) ∧
    (self.len = .ok n → o.len = .error e → self.le (.set o) = .error e ∧ self.lt (.set o) = .error e ∧
      self.ge (.set o) = .error e ∧ self.gt (.set o) = .error e ∧ self.eq (.set o) = .error e) ∧
    (self.len = .ok n → o.len = .ok m →
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
          self.le (.set o) = Ret.val <$> raiseTail self.tail true)) ∧
      (m ≤ n →
        (o.iter = .error e → self.ge (.set o) = .error e) ∧
        (o.iter = .ok (pre ++ z :: post) → (∀ x ∈ pre, self.contains x = .ok true) → self.contains z = .ok false →
          self.ge (.set o) = .ok (.val false)) ∧
        (o.iter = .ok (pre ++ z :: post) → (∀ x ∈ pre, self.contains x = .ok true) → self.contains z = .error e →
          self.ge (.set o) = .error e) ∧
        (o.iter = .ok xs → (∀ x ∈ xs, self.contains x = .ok true) →
          self.ge (.set o) = Ret.val <$> raiseTail o.tail true)) ∧
      (n < m → self.lt (.set o) = self.le (.set o)) ∧ (m < n → self.gt (.set o) = self.ge (.set o)) ∧
      (n = m → self.eq (.set o) = self.le (.set o)) ∧
      (n = m → self.lt (.set o) = .ok (.val false) ∧ self.gt (.set o) = .ok (.val false))) ∧
    self.le (.iterable abc it t) = .ok .notImplemented ∧ self.lt (.iterable abc it t) = .ok .notImplemented ∧
    self.ge (.iterable abc it t) = .ok .notImplemented ∧ self.gt (.iterable abc it t) = .ok .notImplemented ∧
    self.eq (.iterable abc it t) = .ok .notImplemented

theorem setCmpPaths_proven : SetCmpPaths := by
  intro α self o n m xs pre post z e abc it t
  refine ⟨?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · intro h
    simp [SetV.le, SetV.lt, SetV.ge, SetV.gt, SetV.eq, h, bind, Except.bind]
  · intro h1 h2
    simp [SetV.le, SetV.lt, SetV.ge, SetV.gt, SetV.eq, h1, h2, bind, Except.bind]
  intro h1 h2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have h3 : ¬ n < m := by omega
    have h4 : n ≠ m := by omega
    simp [SetV.le, SetV.lt, SetV.eq, h1, h2, h, h3, h4, bind, Except.bind, pure, Except.pure]
  · intro h
    have h3 : ¬ n > m := by omega
    have h4 : n ≠ m := by omega
    simp [SetV.ge, SetV.gt, SetV.eq, h1, h2, h, h3, h4, bind, Except.bind, pure, Except.pure]
  · intro h
    have h3 : ¬ n > m := by omega
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
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h4; simp [SetV.ge, h1, h2, h3, h4, bind, Except.bind]
    · intro h4 h5 h6
      have := allInT_no self.contains o.tail z post h6 pre h5
      simp [SetV.ge, h1, h2, h3, h4, this, bind, Except.bind, pure, Except.pure]
    · intro h4 h5 h6
      have := allInT_err self.contains o.tail z post e h6 pre h5
      simp [SetV.ge, h1, h2, h3, h4, this, bind, Except.bind]
    · intro h4 h5
      have := allInT_all self.contains o.tail xs h5
      simp only [SetV.ge, h1, h2, bind, Except.bind, pure, Except.pure, h3, if_false, h4, this]
      cases o.tail <;> rfl
  · intro h; simp [SetV.lt, h1, h2, h, bind, Except.bind]
  · intro h
    have h3 : n > m := by omega
    simp [SetV.gt, h1, h2, h3, bind, Except.bind]
  · intro h; simp [SetV.eq, h1, h2, h, bind, Except.bind]
  · intro h
    subst h
    simp [SetV.lt, SetV.gt, h1, h2, bind, Except.bind, pure, Except.pure]

/-- `&`, `|` and `isdisjoint` for any primitives and any constructor. `&` and `|` refuse a non-`Iterable` (an object
with only `__getitem__` too) with `NotImplemented`. `&` calls `iter(other)` before the constructor starts, then the
generator and the constructor interleave: each element is tested and, when kept, pushed before the next is tested, so
a constructor that fails on a kept element (as `set()` on an unhashable one) is the outcome before a later raising
`__contains__`, and with total tests the result is the constructor run on the kept elements. `|` starts the
constructor, then iterates `self`, then `other`. `isdisjoint` iterates anything `iter()` accepts, with no
`isinstance` test. Lib/_collections_abc.py:606-626. -/
def SetAlgPaths : Prop :=
  ∀ (ρ α β : Type) (self : SetV α) (B : FromIter ρ α β) (o : Operand α) (xs pre post ys : List α) (x z : α)
    (r0 r1 r2 : ρ) (e : PyExc) (p : α → Bool) (t : Option PyExc) (it : Py (List α)) (abc : Bool),
    self.and B (.iterable false it t) = .ok .notImplemented ∧
    self.or B (.iterable false it t) = .ok .notImplemented ∧
    (o.isIterable = true → o.items = .error e → self.and B o = .error e) ∧
    (o.isIterable = true → o.items = .ok xs → B.start = .error e → self.and B o = .error e) ∧
    (o.isIterable = true → o.items = .ok xs → B.start = .ok r0 → (∀ y ∈ xs, self.contains y = .ok (p y)) →
      self.and B o = (do let r ← feedAll B o.tail r0 (xs.filter p); let b ← B.done r; pure (.val b))) ∧
    (o.isIterable = true → o.items = .ok (x :: post) → B.start = .ok r0 → self.contains x = .ok true →
      B.push r0 x = .error e → self.and B o = .error e) ∧
    (o.isIterable = true → o.items = .ok (pre ++ z :: post) → B.start = .ok r0 →
      (∀ y ∈ pre, self.contains y = .ok false) → self.contains z = .error e → self.and B o = .error e) ∧
    (o.isIterable = true → B.start = .error e → self.or B o = .error e) ∧
    (o.isIterable = true → B.start = .ok r0 → self.iter = .error e → self.or B o = .error e) ∧
    (o.isIterable = true → B.start = .ok r0 → self.iter = .ok (x :: post) → B.push r0 x = .error e →
      self.or B o = .error e) ∧
    (o.isIterable = true → B.start = .ok r0 → self.iter = .ok ys → feedAll B self.tail r0 ys = .ok r1 →
      o.items = .error e → self.or B o = .error e) ∧
    (o.isIterable = true → B.start = .ok r0 → self.iter = .ok ys → feedAll B self.tail r0 ys = .ok r1 →
      o.items = .ok xs → feedAll B o.tail r1 xs = .ok r2 → self.or B o = Ret.val <$> B.done r2) ∧
    self.isdisjoint (.iterable abc (.error e) t) = .error e ∧
    ((∀ y ∈ pre, self.contains y = .ok false) → self.contains z = .ok true →
      self.isdisjoint (.iterable abc (.ok (pre ++ z :: post)) t) = .ok false) ∧
    ((∀ y ∈ pre, self.contains y = .ok false) → self.contains z = .error e →
      self.isdisjoint (.iterable abc (.ok (pre ++ z :: post)) t) = .error e) ∧
    ((∀ y ∈ xs, self.contains y = .ok false) → self.isdisjoint (.iterable abc (.ok xs) t) = raiseTail t true)

theorem setAlgPaths_proven : SetAlgPaths := by
  intro ρ α β self B o xs pre post ys x z r0 r1 r2 e p t it abc
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_⟩
  · intro h1 h2; simp [SetV.and, h1, h2, bind, Except.bind]
  · intro h1 h2 h3; simp [SetV.and, h1, h2, h3, bind, Except.bind]
  · intro h1 h2 h3 h4
    simp only [SetV.and, h1, h2, h3, Bool.not_true, Bool.false_eq_true, ite_false, bind, Except.bind]
    rw [feedIf_pure B self.contains p o.tail xs r0 h4]
  · intro h1 h2 h3 h4 h5
    simp [SetV.and, feedIf, h1, h2, h3, h4, h5, bind, Except.bind]
  · intro h1 h2 h3 h4 h5
    simp [SetV.and, h1, h2, h3, feedIf_skip_err B self.contains o.tail z post e h5 pre r0 h4, bind, Except.bind]
  · intro h1 h2; simp [SetV.or, h1, h2, bind, Except.bind]
  · intro h1 h2 h3; simp [SetV.or, h1, h2, h3, bind, Except.bind]
  · intro h1 h2 h3 h4; simp [SetV.or, feedAll, h1, h2, h3, h4, bind, Except.bind]
  · intro h1 h2 h3 h4 h5; simp [SetV.or, h1, h2, h3, h4, h5, bind, Except.bind]
  · intro h1 h2 h3 h4 h5 h6
    simp only [SetV.or, h1, h2, h3, h4, h5, h6, Bool.not_true, Bool.false_eq_true, ite_false, bind, Except.bind]
    cases B.done r2 <;> rfl
  · intro h1 h2
    simp only [SetV.isdisjoint, Operand.items, Operand.tail, bind, Except.bind]
    exact disjoint_hit self.contains t z post h2 pre h1
  · intro h1 h2
    simp only [SetV.isdisjoint, Operand.items, Operand.tail, bind, Except.bind]
    exact disjoint_err self.contains t z post e h2 pre h1
  · intro h1
    simp only [SetV.isdisjoint, Operand.items, Operand.tail, bind, Except.bind]
    exact disjoint_all self.contains t xs h1

/-- `-`, the reflected `-` and `^`, for any primitives and any constructor. A non-`Iterable` gives `NotImplemented`; a
non-`Set` `Iterable` goes through `_from_iterable` whole first (the constructor starts, calls `iter(other)` and takes
each element, any of which may fail), so its failure comes before anything else, and its result stands for `other`.
Then `-` iterates `self` (the reflected one `other`), starts the constructor and pushes each element the other side
does not contain. `^` is `(self - other) | (other - self)`: the left subtraction first, its failure before the right
one runs, then `|` of the two. Lib/_collections_abc.py:628-651. -/
def SetSubPaths : Prop :=
  ∀ (ρ α δ γ : Type) (self o : SetV α) (B : FromIter ρ α (SetV α)) (minus : SetV α → SetV α → Py δ)
    (bor : δ → δ → Py γ) (xs ys : List α) (x : α) (r0 : ρ) (e : PyExc) (t : Option PyExc) (p : α → Bool)
    (it : Py (List α)) (a b : δ),
    self.sub B (.iterable false it t) = .ok .notImplemented ∧
    self.rsub B (.iterable false it t) = .ok .notImplemented ∧
    self.xor B minus bor (.iterable false it t) = .ok .notImplemented ∧
    (build B it t = .error e → self.sub B (.iterable true it t) = .error e ∧
      self.rsub B (.iterable true it t) = .error e ∧ self.xor B minus bor (.iterable true it t) = .error e) ∧
    (build B it t = .ok o → self.sub B (.iterable true it t) = self.sub B (.set o) ∧
      self.rsub B (.iterable true it t) = self.rsub B (.set o) ∧
      self.xor B minus bor (.iterable true it t) = self.xor B minus bor (.set o)) ∧
    (B.start = .error e → build B it t = .error e) ∧
    (B.start = .ok r0 → it = .error e → build B it t = .error e) ∧
    (B.start = .ok r0 → B.push r0 x = .error e → build B (.ok (x :: xs)) t = .error e) ∧
    (B.start = .ok r0 → build B (.ok xs) t = (feedAll B t r0 xs >>= B.done)) ∧
    (self.iter = .error e → self.sub B (.set o) = .error e) ∧
    (self.iter = .ok xs → B.start = .error e → self.sub B (.set o) = .error e) ∧
    (self.iter = .ok xs → B.start = .ok r0 → (∀ y ∈ xs, o.contains y = .ok (p y)) →
      self.sub B (.set o) =
        (do let r ← feedAll B self.tail r0 (xs.filter (fun y => !p y)); let v ← B.done r; pure (.val v))) ∧
    (o.iter = .error e → self.rsub B (.set o) = .error e) ∧
    (o.iter = .ok ys → B.start = .ok r0 → (∀ y ∈ ys, self.contains y = .ok (p y)) →
      self.rsub B (.set o) =
        (do let r ← feedAll B o.tail r0 (ys.filter (fun y => !p y)); let v ← B.done r; pure (.val v))) ∧
    (minus self o = .error e → self.xor B minus bor (.set o) = .error e) ∧
    (minus self o = .ok a → minus o self = .error e → self.xor B minus bor (.set o) = .error e) ∧
    (minus self o = .ok a → minus o self = .ok b → self.xor B minus bor (.set o) = Ret.val <$> bor a b)

theorem setSubPaths_proven : SetSubPaths := by
  intro ρ α δ γ self o B minus bor xs ys x r0 e t p it a b
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    simp [SetV.sub, SetV.rsub, SetV.xor, Operand.asSet?, h, bind, Except.bind]
  · intro h
    simp [SetV.sub, SetV.rsub, SetV.xor, Operand.asSet?, h, bind, Except.bind]
  · intro h; simp [build, h, bind, Except.bind]
  · intro h1 h2; simp [build, h1, h2, bind, Except.bind]
  · intro h1 h2; simp [build, feedAll, h1, h2, bind, Except.bind]
  · intro h1; simp [build, h1, bind, Except.bind]
  · intro h; simp [SetV.sub, Operand.asSet?, h, bind, Except.bind]
  · intro h1 h2; simp [SetV.sub, Operand.asSet?, h1, h2, bind, Except.bind]
  · intro h1 h2 h3
    have hk : ∀ y ∈ xs, notIn o y = .ok (!p y) := by
      intro y hy; simp [notIn, h3 y hy, bind, Except.bind, pure, Except.pure]
    simp only [SetV.sub, Operand.asSet?, h1, h2, bind, Except.bind]
    rw [feedIf_pure B (notIn o) (fun y => !p y) self.tail xs r0 hk]
  · intro h; simp [SetV.rsub, Operand.asSet?, h, bind, Except.bind]
  · intro h1 h2 h3
    have hk : ∀ y ∈ ys, notIn self y = .ok (!p y) := by
      intro y hy; simp [notIn, h3 y hy, bind, Except.bind, pure, Except.pure]
    simp only [SetV.rsub, Operand.asSet?, h1, h2, bind, Except.bind]
    rw [feedIf_pure B (notIn self) (fun y => !p y) o.tail ys r0 hk]
  · intro h; simp [SetV.xor, Operand.asSet?, h, bind, Except.bind]
  · intro h1 h2; simp [SetV.xor, Operand.asSet?, h1, h2, bind, Except.bind]
  · intro h1 h2
    simp only [SetV.xor, Operand.asSet?, h1, h2, bind, Except.bind]
    cases bor a b <;> rfl

/-- `MutableSet`, every path, for any primitives: `remove` raises `KeyError` only when the element is absent; `pop` turns
the end of the iterator into `KeyError`, and passes any other exception through; `clear` stops at `KeyError` only.
`|=` and `-=` iterate anything `iter()` accepts, with no `isinstance` test, and stop at the first failing `add` or
`discard`; an iterator that raises after its items is the outcome. `&=` iterates `self - it`, the operator:
`Set.__sub__`, then `it.__rsub__(self)` when that is `NotImplemented` (first when `it`'s class is a subclass with its
own), and `TypeError` when neither answers. `^=` sends a non-`Set` through `_from_iterable` with no `isinstance` test
and loops over the set that made, its iterator's end included. Lib/_collections_abc.py:714-767. -/
def MSetPaths : Prop :=
  ∀ (σ ρ α : Type) (M : MSet σ ρ α) (fuel : Nat) (s s' : σ) (v : α) (vs : List α) (e : PyExc) (p : α × σ)
    (abc rfirst : Bool) (t : Option PyExc) (it : Py (List α)) (d o : SetV α) (op : Operand α),
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
    M.ior s (.iterable abc (.error e) t) = .error e ∧
    (M.add s v = .error e → M.ior s (.iterable abc (.ok (v :: vs)) t) = .error e) ∧
    (M.add s v = .ok s' → M.ior s (.iterable abc (.ok (v :: vs)) t) = M.ior s' (.iterable abc (.ok vs) t)) ∧
    M.ior s (.iterable abc (.ok []) (some e)) = .error e ∧
    M.ior s .other = .error (.typeError "~object is not iterable") ∧
    M.isub s (some (.iterable abc (.error e) t)) fuel = .error e ∧
    (M.discard s v = .error e → M.isub s (some (.iterable abc (.ok (v :: vs)) t)) fuel = .error e) ∧
    (M.discard s v = .ok s' →
      M.isub s (some (.iterable abc (.ok (v :: vs)) t)) fuel = M.isub s' (some (.iterable abc (.ok vs) t)) fuel) ∧
    M.isub s (some (.iterable abc (.ok []) (some e))) fuel = .error e ∧
    M.isub s none fuel = M.clear fuel s ∧ M.ixor s none fuel = M.clear fuel s ∧
    Py.raises (M.iand s (.iterable false it t) none rfirst) "TypeError" ∧
    (M.iand s (.iterable false it t) (some (.ok (.val d))) false = (d.iter >>= forAddT M.discard d.tail s)) ∧
    (M.iand s op (some (.ok (.val d))) true = (d.iter >>= forAddT M.discard d.tail s)) ∧
    ((M.view s).sub M.fromIter op = .ok (.val d) →
      ∀ rs, M.iand s op rs false = (d.iter >>= forAddT M.discard d.tail s)) ∧
    ((M.view s).sub M.fromIter op = .error e → M.iand s op none rfirst = .error e) ∧
    (build M.fromIter it t = .error e → M.ixor s (some (.iterable abc it t)) fuel = .error e) ∧
    (build M.fromIter it t = .ok o → M.ixor s (some (.iterable abc it t)) fuel = M.ixor s (some (.set o)) fuel) ∧
    (o.iter = .error e → M.ixor s (some (.set o)) fuel = .error e) ∧
    (o.iter = .ok (v :: vs) → (M.view s).contains v = .ok true → M.discard s v = .ok s' →
      M.ixor s (some (.set o)) fuel = forAddT M.toggle o.tail s' vs) ∧
    (o.iter = .ok (v :: vs) → (M.view s).contains v = .ok false → M.add s v = .ok s' →
      M.ixor s (some (.set o)) fuel = forAddT M.toggle o.tail s' vs) ∧
    (o.iter = .ok [] → o.tail = some e → M.ixor s (some (.set o)) fuel = .error e)

theorem mSetPaths_proven : MSetPaths := by
  intro σ ρ α M fuel s s' v vs e p abc rfirst t it d o op
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_, rfl, rfl, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · simp [MSet.ior, Operand.items, bind, Except.bind]
  · intro h; simp [MSet.ior, Operand.items, Operand.tail, forAddT, h, bind, Except.bind]
  · intro h; simp [MSet.ior, Operand.items, Operand.tail, forAddT, h, bind, Except.bind]
  · simp [MSet.ior, Operand.items, Operand.tail, forAddT, raiseTail, bind, Except.bind]
  · simp [MSet.isub, Operand.items, bind, Except.bind]
  · intro h; simp [MSet.isub, Operand.items, Operand.tail, forAddT, h, bind, Except.bind]
  · intro h; simp [MSet.isub, Operand.items, Operand.tail, forAddT, h, bind, Except.bind]
  · simp [MSet.isub, Operand.items, Operand.tail, forAddT, raiseTail, bind, Except.bind]
  · refine ⟨.typeError "~unsupported operand type(s) for -", ?_, rfl⟩
    cases rfirst <;> simp [MSet.iand, binaryOp, retOr, SetV.sub, Operand.asSet?, bind, Except.bind]
  · simp [MSet.iand, binaryOp, retOr, SetV.sub, Operand.asSet?, bind, Except.bind, pure, Except.pure]
  · simp [MSet.iand, binaryOp, retOr, bind, Except.bind, pure, Except.pure]
  · intro h rs
    cases rs <;> simp [MSet.iand, binaryOp, retOr, h, bind, Except.bind, pure, Except.pure]
  · intro h
    cases rfirst <;> simp [MSet.iand, binaryOp, retOr, h, bind, Except.bind]
  · intro h; simp [MSet.ixor, h, bind, Except.bind]
  · intro h; simp [MSet.ixor, h, bind, Except.bind]
  · intro h; simp [MSet.ixor, h, bind, Except.bind]
  · intro h1 h2 h3; simp [MSet.ixor, forAddT, MSet.toggle, h1, h2, h3, bind, Except.bind]
  · intro h1 h2 h3; simp [MSet.ixor, forAddT, MSet.toggle, h1, h2, h3, bind, Except.bind]
  · intro h1 h2; simp [MSet.ixor, forAddT, raiseTail, h1, h2, bind, Except.bind]

end PyLean.CoreLibs.CollAbc
