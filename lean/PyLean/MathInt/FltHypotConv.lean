import PyLean.MathInt.FltHypot

/-!
# Properties: the arguments of `hypot` and `dist`, and exact values

`math_hypot_impl` (Modules/mathmodule.c:2065-2105) converts each argument with `ASSIGN_DOUBLE`
(:205-220) before looking at any value, and `math_dist_impl` (:1965-2044) converts `p[i]` then
`q[i]` for each `i` in turn (:2009-2020). `ASSIGN_DOUBLE`'s fast paths for exact floats and ints
agree with `PyFloat_AsDouble`, so `hypot(*args)` is `hypot` of the converted floats, and the first
argument that fails to convert decides the exception. Exact cases pin the value `vector_norm`
computes on both of its branches (scaled normal numbers, and the subnormal rescaling of
:1914-1920).
-/

namespace PyLean.MathInt

open PyLean PyLean.Binary64 PyLean.Binary64.F64

/-- `ASSIGN_DOUBLE` of `p[i]`, then of `q[i]` (mathmodule.c:2012-2013). -/
def convPair (pq : Arg × Arg) : Py (F64 × F64) := do
  let a ← asDouble pq.1
  let b ← asDouble pq.2
  pure (a, b)

/-- `hypot` and `dist` on arbitrary argument objects.

* `hypot(*args)` raises the conversion error of the first argument that has one, and otherwise
  equals `hypot` of the converted floats (`PyFloat_AsDouble`, floatobject.c:247-303);
* `dist(p, q)` with points of equal dimension converts `p[0]`, `q[0]`, `p[1]`, `q[1]`, ... in this
  order, raises the first conversion error, and otherwise equals `dist` of the converted floats;
* exact cases: `hypot(3.0, 4.0) == 5.0` (Doc/library/math.rst gives `sqrt(x*x + y*y)`), and the
  same scaled by `2**1000` and by `2**-1074` (all three numbers subnormal), `hypot(5.0, 12.0) ==
  13.0`, and `hypot(3, 4) == 5.0` for ints. -/
def HypotConv : Prop :=
  (∀ args : List Arg, math_hypot args =
    (do let xs ← args.mapM asDouble; math_hypot (xs.map .float))) ∧
  (∀ p q : It, p.err = none → q.err = none → p.items.length = q.items.length →
    math_dist p q = (do
      let xy ← (p.items.zip q.items).mapM convPair
      math_dist ⟨xy.map (fun v => .float v.1), none⟩ ⟨xy.map (fun v => .float v.2), none⟩)) ∧
  math_hypot [.float (ofInt 3), .float (ofInt 4)] = .ok (ofInt 5) ∧
  math_hypot [.float (ofRat (3 * pw 1000)), .float (ofRat (4 * pw 1000))] = .ok (ofRat (5 * pw 1000)) ∧
  math_hypot [.float (ofRat (3 * pw (-1074))), .float (ofRat (4 * pw (-1074)))] =
    .ok (ofRat (5 * pw (-1074))) ∧
  math_hypot [.float (ofInt 5), .float (ofInt 12)] = .ok (ofInt 13) ∧
  math_hypot [.int 3, .int 4] = .ok (ofInt 5)

theorem assignDouble_eq (o : Arg) : assignDouble o = asDouble o := by cases o <;> rfl

theorem hypot_fold_conv : ∀ (args : List Arg) (s : List F64 × F64 × Bool),
    args.foldlM hypotStep s =
      (do let xs ← args.mapM asDouble; (xs.map Arg.float).foldlM hypotStep s) := by
  intro args
  induction args with
  | nil => intro s; rfl
  | cons a as ih =>
    intro s
    simp only [List.foldlM_cons, List.mapM_cons]
    cases h : asDouble a with
    | error e => simp [hypotStep, assignDouble_eq, h, bind, Except.bind]
    | ok x =>
      simp only [hypotStep, assignDouble_eq, h, bind, Except.bind, pure, Except.pure]
      rw [ih]
      simp only [bind, Except.bind, pure, Except.pure]
      cases as.mapM asDouble <;> rfl

theorem dist_fold_conv : ∀ (pq : List (Arg × Arg)) (s : List F64 × F64 × Bool),
    pq.foldlM distStep s =
      (do
        let xy ← pq.mapM convPair
        (xy.map (fun v => (Arg.float v.1, Arg.float v.2))).foldlM distStep s) := by
  intro pq
  induction pq with
  | nil => intro s; rfl
  | cons a as ih =>
    intro s
    simp only [List.foldlM_cons, List.mapM_cons]
    cases h1 : asDouble a.1 with
    | error e => simp [distStep, convPair, assignDouble_eq, h1, bind, Except.bind]
    | ok x =>
      cases h2 : asDouble a.2 with
      | error e => simp [distStep, convPair, assignDouble_eq, h1, h2, bind, Except.bind]
      | ok y =>
        simp only [distStep, convPair, assignDouble_eq, h1, h2, bind, Except.bind, pure, Except.pure]
        rw [ih]
        simp only [bind, Except.bind, pure, Except.pure]
        cases as.mapM convPair <;> rfl

theorem zip_map_pairs (xy : List (F64 × F64)) :
    (xy.map (fun v => Arg.float v.1)).zip (xy.map (fun v => Arg.float v.2)) =
      xy.map (fun v => (Arg.float v.1, Arg.float v.2)) := by
  induction xy with
  | nil => rfl
  | cons v vs ih => simp [ih]

theorem hypotConv_proven : HypotConv := by
  refine ⟨fun args => ?_, fun p q hp hq hl => ?_, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel⟩
  · unfold math_hypot
    rw [hypot_fold_conv]
    simp only [bind, Except.bind]
    cases args.mapM asDouble <;> rfl
  · obtain ⟨pi, pe⟩ := p; obtain ⟨qi, qe⟩ := q
    simp only at hp hq hl; subst hp; subst hq
    have hlen : ∀ xy : List (F64 × F64),
        (xy.map (fun v => Arg.float v.1)).length = (xy.map (fun v => Arg.float v.2)).length := by
      intro xy; simp
    simp only [math_dist, It.finish, bind, Except.bind, hl, bne_self_eq_false, Bool.false_eq_true,
      ↓reduceIte]
    rw [dist_fold_conv]
    cases (pi.zip qi).mapM convPair with
    | error e => rfl
    | ok xy =>
      simp only [bind, Except.bind, math_dist, It.finish, hlen, bne_self_eq_false, Bool.false_eq_true,
        ↓reduceIte, zip_map_pairs]

end PyLean.MathInt
