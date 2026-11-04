import PyLean.CoreLibs.Operator.ProtoProps
import PyLean.CoreLibs.Operator.GettersProps

/-!
What each operator function computes, pinned to concrete results and failure paths. The twin statements of
`ProtoProps` and `GettersProps` say that two mirrors agree, which two equally wrong mirrors would also do; the
statements here say what the agreed result is, so that `fun _ => .error _` and "always the first branch" fail.
-/

namespace PyLean.CoreLibs.Operator

open PyLean

/-! ### `+`, `*`, `**` and the in-place forms -/

/-- What `binary_op1` answers wins over the sequence slots: `PyNumber_Add`, `PyNumber_Multiply`, `PyNumber_Power`
return its value and raise its exception. `SequenceFallback` and `PowerDispatch` take the `NotImplemented` case. -/
def FirstStepWins : Prop :=
  ∀ (α : Type) (A : BinArgs α) (Q : SeqArgs α) (v w x : α) (e : PyExc),
    (binaryOp1 A v w = .ok (.val x) →
      numberAdd A Q v w = .ok x ∧ numberMul A Q v w = .ok x ∧ numberPow A v w = .ok x) ∧
    (binaryOp1 A v w = .error e →
      numberAdd A Q v w = .error e ∧ numberMul A Q v w = .error e ∧ numberPow A v w = .error e)

theorem firstStepWins_proven : FirstStepWins := by
  intro α A Q v w x e
  constructor
  · intro h; simp [numberAdd, numberMul, numberPow, ternaryOp, binaryOp, h]
  · intro h; simp [numberAdd, numberMul, numberPow, ternaryOp, binaryOp, h]

/-- The in-place forms, every outcome. A raising in-place slot is final; `NotImplemented` from it is the same as
having no slot; `binary_op1` comes next; and only then the sequence slots. `a *= b` with a left operand that has
`tp_as_sequence` but no repeat slot raises, even when `b` could repeat: `PyNumber_InPlaceMultiply` differs from
`PyNumber_Multiply` there, and the refuted `ImulIsMul` is that case. -/
def InplaceExact : Prop :=
  ∀ (α : Type) (A : BinArgs α) (Q : SeqArgs α) (sym : String) (v w x : α) (f : α → α → Py (Ret α)) (e : PyExc)
    (g : α → Int → Py α),
    (f v w = .error e →
      inplaceOp (some f) A sym v w = .error e ∧ inplaceAdd (some f) A Q v w = .error e ∧
      inplaceMul (some f) A Q v w = .error e ∧ inplacePow (some f) A v w = .error e) ∧
    (f v w = .ok (.val x) → inplaceMul (some f) A Q v w = .ok x) ∧
    (f v w = .ok .notImplemented →
      inplaceAdd (some f) A Q v w = inplaceAdd none A Q v w ∧
      inplaceMul (some f) A Q v w = inplaceMul none A Q v w ∧
      inplacePow (some f) A v w = inplacePow none A v w) ∧
    (binaryOp1 A v w = .ok (.val x) →
      inplaceAdd none A Q v w = .ok x ∧ inplaceMul none A Q v w = .ok x ∧ inplacePow none A v w = .ok x) ∧
    (binaryOp1 A v w = .error e →
      inplaceAdd none A Q v w = .error e ∧ inplaceMul none A Q v w = .error e ∧
      inplacePow none A v w = .error e) ∧
    (binaryOp1 A v w = .ok .notImplemented →
      inplaceOp none A sym v w = .error (binopError sym A.lt A.rt) ∧
      (Q.hasV = false → inplaceAdd none A Q v w = .error (binopError "+=" A.lt A.rt)) ∧
      (Q.hasV = true → Q.iconcat = none → Q.concat = none →
        inplaceAdd none A Q v w = .error (binopError "+=" A.lt A.rt)) ∧
      (Q.hasV = true → Q.irepeatV = none → Q.repeatV = none →
        inplaceMul none A Q v w = .error (binopError "*=" A.lt A.rt)) ∧
      (Q.hasV = false → Q.hasW = false → inplaceMul none A Q v w = .error (binopError "*=" A.lt A.rt)) ∧
      (Q.hasV = false → Q.hasW = true → Q.repeatW = some g → inplaceMul none A Q v w = sequenceRepeat Q g w v) ∧
      (Q.hasV = false → Q.hasW = true → Q.repeatW = none →
        inplaceMul none A Q v w = .error (binopError "*=" A.lt A.rt))) ∧
    (f v w = .ok (.val x) → inplaceAdd (some f) A Q v w = .ok x ∧ inplacePow (some f) A v w = .ok x) ∧
    (binaryOp1 A v w = .ok .notImplemented →
      (inplacePow none A v w = .error (binopError "**=" A.lt A.rt)) ∧
      (∀ c : α → α → Py α, Q.hasV = true → Q.iconcat = some c → inplaceAdd none A Q v w = c v w) ∧
      (∀ c : α → α → Py α, Q.hasV = true → Q.iconcat = none → Q.concat = some c → inplaceAdd none A Q v w = c v w) ∧
      (∀ n : Int, Q.index w = some (.ok n) → ssizeMin ≤ n → n ≤ ssizeMax →
        (Q.hasV = true → Q.irepeatV = some g → inplaceMul none A Q v w = g v n) ∧
        (Q.hasV = true → Q.irepeatV = none → Q.repeatV = some g → inplaceMul none A Q v w = g v n)) ∧
      (Q.hasV = true → Q.irepeatV = some g → Q.index w = some (.error e) → inplaceMul none A Q v w = .error e) ∧
      (Q.hasV = true → Q.irepeatV = some g → Q.index w = none → (inplaceMul none A Q v w).raises "TypeError") ∧
      (∀ n : Int, (n > ssizeMax ∨ n < ssizeMin) →
        let over : Py α := .error (.overflowError s!"cannot fit '{Q.tn w}' into an index-sized integer")
        (Q.hasV = true → Q.irepeatV = some g → Q.index w = some (.ok n) → inplaceMul none A Q v w = over) ∧
        (Q.hasV = true → Q.irepeatV = none → Q.repeatV = some g → Q.index w = some (.ok n) →
          inplaceMul none A Q v w = over) ∧
        (Q.hasV = false → Q.hasW = true → Q.repeatW = some g → Q.index v = some (.ok n) →
          inplaceMul none A Q v w =
            .error (.overflowError s!"cannot fit '{Q.tn v}' into an index-sized integer"))))

theorem inplaceExact_proven : InplaceExact := by
  intro α A Q sym v w x f e g
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; simp [inplaceOp, inplaceAdd, inplaceMul, inplacePow, binaryIop1, h]
  · intro h; simp [inplaceMul, binaryIop1, h]
  · intro h; simp [inplaceAdd, inplaceMul, inplacePow, binaryIop1, h]
  · intro h; simp [inplaceAdd, inplaceMul, inplacePow, ternaryOp, binaryOp, binaryIop1, h]
  · intro h; simp [inplaceAdd, inplaceMul, inplacePow, ternaryOp, binaryOp, binaryIop1, h]
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [inplaceOp, binaryIop1, h]
    · intro h1; simp [inplaceAdd, binaryIop1, h, h1]
    · intro h1 h2 h3; simp [inplaceAdd, binaryIop1, h, h1, h2, h3]
    · intro h1 h2 h3; simp [inplaceMul, binaryIop1, h, h1, h2, h3]
    · intro h1 h2; simp [inplaceMul, binaryIop1, h, h1, h2]
    · intro h1 h2 h3; simp [inplaceMul, binaryIop1, h, h1, h2, h3]
    · intro h1 h2 h3; simp [inplaceMul, binaryIop1, h, h1, h2, h3]
  · intro h; exact ⟨by simp [inplaceAdd, binaryIop1, h], by simp [inplacePow, h]⟩
  · intro h
    refine ⟨by simp [inplacePow, ternaryOp, binaryOp, h], ?_, ?_, ?_, ?_, ?_, ?_⟩
    rotate_left 5
    · intro n hn
      refine ⟨?_, ?_, ?_⟩
      · intro h1 h2 h3; simp [inplaceMul, binaryIop1, h, h1, h2, sequenceRepeat, h3, fitSsize, hn]
      · intro h1 h2 h3 h4; simp [inplaceMul, binaryIop1, h, h1, h2, h3, sequenceRepeat, h4, fitSsize, hn]
      · intro h1 h2 h3 h4; simp [inplaceMul, binaryIop1, h, h1, h2, h3, sequenceRepeat, h4, fitSsize, hn]
    · intro c h1 h2; simp [inplaceAdd, binaryIop1, h, h1, h2]
    · intro c h1 h2 h3; simp [inplaceAdd, binaryIop1, h, h1, h2, h3]
    · intro n h1 h2 h3
      have hf : ¬ (n > ssizeMax ∨ n < ssizeMin) := by omega
      refine ⟨?_, ?_⟩
      · intro h4 h5; simp [inplaceMul, binaryIop1, h, h4, h5, sequenceRepeat, h1, fitSsize, hf]
      · intro h4 h5 h6; simp [inplaceMul, binaryIop1, h, h4, h5, h6, sequenceRepeat, h1, fitSsize, hf]
    · intro h1 h2 h3; simp [inplaceMul, binaryIop1, h, h1, h2, sequenceRepeat, h3]
    · intro h1 h2 h3
      exact ⟨_, by simp [inplaceMul, binaryIop1, h, h1, h2, sequenceRepeat, h3]; rfl, rfl⟩

/-- The rest of `do_richcompare`: an ordering nobody answers raises with the source's message for every ordering;
with operands of one type the left method runs, then the right one with the swapped operator; and the reflected
method of a subclass that raises is final. -/
def RichCompareExact : Prop :=
  ∀ (α : Type) (A : CmpArgs α) (op : RichOp) (v w x : α) (l r : RichOp → α → α → Py (Ret α)) (e : PyExc),
    A.rv = some l → A.rw = some r →
    (A.sameType = true → l op v w = .ok (.val x) → richCompare A op v w = .ok x) ∧
    (A.sameType = true → l op v w = .ok .notImplemented → r op.swapped w v = .ok (.val x) →
      richCompare A op v w = .ok x) ∧
    (A.sameType = false → A.subtype = true → r op.swapped w v = .error e → richCompare A op v w = .error e) ∧
    ((A.sameType = true ∨ A.subtype = false) → l op v w = .ok .notImplemented →
      r op.swapped w v = .ok .notImplemented → op ≠ .eq → op ≠ .ne →
      richCompare A op v w = .error (.typeError
        s!"'{op.sym}' not supported between instances of '{A.lt}' and '{A.rt}'"))

theorem richCompareExact_proven : RichCompareExact := by
  intro α A op v w x l r e h1 h2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hs hl; simp [richCompare, h1, h2, hs, hl]
  · intro hs hl hr; simp [richCompare, h1, h2, hs, hl, hr]
  · intro hs hu hr; simp [richCompare, h2, hs, hu, hr]
  · intro hs hl hr h3 h4
    have hf : (!A.sameType && A.subtype && A.rw.isSome) = false := by
      rcases hs with hs | hs <;> simp [hs]
    cases op <;> first | exact absurd rfl h3 | exact absurd rfl h4 | simp [richCompare, h1, h2, hf, hl, hr]

/-! ### `index` -/

/-- Each twin of `operator.index`, every path. C answers an `int` first, then reads the slot and checks what it
returns; Python returns what `a.__index__()` returns, reading the instance dict and then the class, whatever the
object is. `IndexTwinsAlways` is refuted on those differences. -/
def IndexExact : Prop :=
  ∀ (o : IndexObj) (n : Int) (tn : String) (e : PyExc) (r : Py IndexRet),
    (o.isInt = some n → indexC o = .ok (.exact n)) ∧
    (o.isInt = none → o.slot = none →
      indexC o = .error (.typeError s!"'{o.tn}' object cannot be interpreted as an integer")) ∧
    (o.isInt = none → o.slot = some (.error e) → indexC o = .error e) ∧
    (o.isInt = none → o.slot = some (.ok (.exact n)) → indexC o = .ok (.exact n)) ∧
    (o.isInt = none → o.slot = some (.ok (.other tn)) →
      indexC o = .error (.typeError s!"{o.tn}.__index__() must return an int, not {tn}")) ∧
    (o.isInt = none → o.slot = some (.ok (.sub n)) → o.warn = none → indexC o = .ok (.exact n)) ∧
    (o.isInt = none → o.slot = some (.ok (.sub n)) → o.warn = some e → indexC o = .error e) ∧
    (o.inst = some r → indexPy o = r) ∧
    (o.inst = none → o.slot = some r → indexPy o = r) ∧
    (o.inst = none → o.isInt = some n → o.slot = some (.ok (.exact n)) → indexPy o = .ok (.exact n)) ∧
    (o.inst = none → o.slot = none →
      indexPy o = .error (.named "AttributeError" s!"'{o.tn}' object has no attribute '__index__'"))

theorem indexExact_proven : IndexExact := by
  intro o n tn e r
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; simp [indexC, h]
  · intro h h2; simp [indexC, h, h2]
  · intro h h2; simp [indexC, h, h2]
  · intro h h2; simp [indexC, h, h2]
  · intro h h2; simp [indexC, h, h2]
  · intro h h2 h3; simp [indexC, h, h2, h3]
  · intro h h2 h3; simp [indexC, h, h2, h3]
  · intro h; simp [indexPy, h]
  · intro h h2; simp [indexPy, h, h2]
  · intro h h2 h3; simp [indexPy, h, h3]
  · intro h h2; simp [indexPy, h, h2]

/-! ### `concat`, `iconcat` -/

/-- Each twin of `concat` and `iconcat`, every path. C tries the sequence slot first and `nb_add` only for two
sequences; Python checks `__getitem__` and then does `+`, which tries `nb_add` first. -/
def ConcatExact : Prop :=
  ∀ (α : Type) (A : ConcatArgs α) (lt rt : String) (a b x : α) (f g : α → α → Py α) (e : PyExc),
    (A.sqConcat = some f → concatC A lt a b = f a b) ∧
    (A.sqConcat = none → (A.seqA && A.seqB) = false → concatC A lt a b = .error (noConcat lt)) ∧
    (A.sqConcat = none → A.seqA = true → A.seqB = true →
      (A.nbAdd a b = .ok (.val x) → concatC A lt a b = .ok x) ∧
      (A.nbAdd a b = .ok .notImplemented → concatC A lt a b = .error (noConcat lt)) ∧
      (A.nbAdd a b = .error e → concatC A lt a b = .error e)) ∧
    (A.sqInplace = some g → iconcatC A lt a b = g a b) ∧
    (A.sqInplace = none → A.sqConcat = some f → iconcatC A lt a b = f a b) ∧
    (A.sqInplace = none → A.sqConcat = none → (A.seqA && A.seqB) = false →
      iconcatC A lt a b = .error (noConcat lt)) ∧
    (A.sqInplace = none → A.sqConcat = none → A.seqA = true → A.seqB = true →
      (A.nbIAdd a b = .ok (.val x) → iconcatC A lt a b = .ok x) ∧
      (A.nbIAdd a b = .ok .notImplemented → iconcatC A lt a b = .error (noConcat lt)) ∧
      (A.nbIAdd a b = .error e → iconcatC A lt a b = .error e)) ∧
    (A.hasGetitem = .ok false →
      concatPy A lt rt a b = .error (noConcat lt) ∧ iconcatPy A lt rt a b = .error (noConcat lt)) ∧
    (A.hasGetitem = .error e → concatPy A lt rt a b = .error e ∧ iconcatPy A lt rt a b = .error e) ∧
    (A.hasGetitem = .ok true →
      (A.nbAdd a b = .ok (.val x) → concatPy A lt rt a b = .ok x) ∧
      (A.nbAdd a b = .error e → concatPy A lt rt a b = .error e) ∧
      (A.nbAdd a b = .ok .notImplemented → A.sqConcat = some f → concatPy A lt rt a b = f a b) ∧
      (A.nbAdd a b = .ok .notImplemented → A.sqConcat = none →
        concatPy A lt rt a b = .error (binopError "+" lt rt)) ∧
      (A.nbIAdd a b = .ok (.val x) → iconcatPy A lt rt a b = .ok x) ∧
      (A.nbIAdd a b = .error e → iconcatPy A lt rt a b = .error e) ∧
      (A.nbIAdd a b = .ok .notImplemented → A.sqInplace = some g → iconcatPy A lt rt a b = g a b) ∧
      (A.nbIAdd a b = .ok .notImplemented → A.sqInplace = none → A.sqConcat = some f →
        iconcatPy A lt rt a b = f a b) ∧
      (A.nbIAdd a b = .ok .notImplemented → A.sqInplace = none → A.sqConcat = none →
        iconcatPy A lt rt a b = .error (binopError "+=" lt rt)))

theorem concatExact_proven : ConcatExact := by
  intro α A lt rt a b x f g e
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_left 8
  · intro h; simp [concatPy, iconcatPy, h]
  rotate_left 1
  · intro h; simp [concatC, h]
  · intro h h2; simp [concatC, h, h2]
  · intro h h2 h3
    refine ⟨?_, ?_, ?_⟩ <;> intro h4 <;> simp [concatC, h, h2, h3, h4, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw]
  · intro h; simp [iconcatC, h]
  · intro h h2; simp [iconcatC, h, h2]
  · intro h h2 h3; simp [iconcatC, h, h2, h3]
  · intro h h2 h3 h4
    refine ⟨?_, ?_, ?_⟩ <;> intro h5 <;> simp [iconcatC, h, h2, h3, h4, h5, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw]
  · intro h; simp [concatPy, iconcatPy, h]
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;>
      simp_all [concatPy, iconcatPy, plus, plusEq, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw]

/-! ### `countOf`, `indexOf`, `contains` -/

section Search

variable {α : Type} (same : Same α) (b : α)

theorem countLoop_all (p : α → Bool) : ∀ (xs : List α) (n : Nat), (∀ x ∈ xs, same x b = .ok (p x)) →
    countLoop same b n xs none = .ok (n + xs.countP p)
  | [], n, _ => by simp [countLoop]
  | x :: xs, n, h => by
    have hx := h x (by simp)
    have ih := countLoop_all p xs (if p x then n + 1 else n) (fun y hy => h y (by simp [hy]))
    simp only [countLoop, hx, ih, List.countP_cons]
    cases p x <;> simp <;> omega

theorem countLoop_stop (v : α) (post : List α) (t : Option PyExc) (e : PyExc) (hv : same v b = .error e) :
    ∀ (pre : List α) (n : Nat), (∀ x ∈ pre, ∃ h, same x b = .ok h) →
      countLoop same b n (pre ++ v :: post) t = .error e
  | [], n, _ => by simp [countLoop, hv]
  | x :: xs, n, h => by
    obtain ⟨c, hc⟩ := h x (by simp)
    simpa [countLoop, hc] using countLoop_stop v post t e hv xs _ (fun y hy => h y (by simp [hy]))

theorem countLoop_tail (e : PyExc) : ∀ (pre : List α) (n : Nat), (∀ x ∈ pre, ∃ h, same x b = .ok h) →
      countLoop same b n pre (some e) = .error e
  | [], n, _ => by simp [countLoop]
  | x :: xs, n, h => by
    obtain ⟨c, hc⟩ := h x (by simp)
    simpa [countLoop, hc] using countLoop_tail e xs _ (fun y hy => h y (by simp [hy]))

theorem indexLoop_miss (t : Option PyExc) (r : PyExc) (hr : r = t.getD (.valueError indexMsg)) :
    ∀ (pre : List α) (i : Nat), (∀ x ∈ pre, same x b = .ok false) → indexLoop same b i pre t = .error r
  | [], i, _ => by cases t <;> simp_all [indexLoop]
  | x :: xs, i, h => by
    have hc := h x (by simp)
    simpa [indexLoop, hc] using indexLoop_miss t r hr xs _ (fun y hy => h y (by simp [hy]))

theorem indexLoop_hit (v : α) (post : List α) (t : Option PyExc) (hv : same v b = .ok true) :
    ∀ (pre : List α) (i : Nat), (∀ x ∈ pre, same x b = .ok false) →
      indexLoop same b i (pre ++ v :: post) t = .ok (i + pre.length)
  | [], i, _ => by simp [indexLoop, hv]
  | x :: xs, i, h => by
    have hc := h x (by simp)
    have ih := indexLoop_hit v post t hv xs (i + 1) (fun y hy => h y (by simp [hy]))
    simp only [List.cons_append, indexLoop, hc, ih, List.length_cons]
    congr 1
    omega

theorem indexLoop_stop (v : α) (post : List α) (t : Option PyExc) (e : PyExc) (hv : same v b = .error e) :
    ∀ (pre : List α) (i : Nat), (∀ x ∈ pre, same x b = .ok false) →
      indexLoop same b i (pre ++ v :: post) t = .error e
  | [], i, _ => by simp [indexLoop, hv]
  | x :: xs, i, h => by
    have hc := h x (by simp)
    simpa [indexLoop, hc] using indexLoop_stop v post t e hv xs _ (fun y hy => h y (by simp [hy]))

theorem containsLoop_all (p : α → Bool) : ∀ (xs : List α), (∀ x ∈ xs, same x b = .ok (p x)) →
    containsLoop same b xs none = .ok (xs.any p)
  | [], _ => by simp [containsLoop]
  | x :: xs, h => by
    have hx := h x (by simp)
    have ih := containsLoop_all p xs (fun y hy => h y (by simp [hy]))
    simp only [containsLoop, hx, List.any_cons]
    cases hp : p x <;> simp [ih]

theorem containsLoop_tail (e : PyExc) : ∀ (pre : List α), (∀ x ∈ pre, same x b = .ok false) →
    containsLoop same b pre (some e) = .error e
  | [], _ => by simp [containsLoop]
  | x :: xs, h => by
    have hc := h x (by simp)
    simpa [containsLoop, hc] using containsLoop_tail e xs (fun y hy => h y (by simp [hy]))

theorem containsLoop_hit (v : α) (post : List α) (t : Option PyExc) (hv : same v b = .ok true) :
    ∀ (pre : List α), (∀ x ∈ pre, same x b = .ok false) → containsLoop same b (pre ++ v :: post) t = .ok true
  | [], _ => by simp [containsLoop, hv]
  | x :: xs, h => by
    have hc := h x (by simp)
    simpa [containsLoop, hc] using containsLoop_hit v post t hv xs (fun y hy => h y (by simp [hy]))

theorem containsLoop_stop (v : α) (post : List α) (t : Option PyExc) (e : PyExc) (hv : same v b = .error e) :
    ∀ (pre : List α), (∀ x ∈ pre, same x b = .ok false) → containsLoop same b (pre ++ v :: post) t = .error e
  | [], _ => by simp [containsLoop, hv]
  | x :: xs, h => by
    have hc := h x (by simp)
    simpa [containsLoop, hc] using containsLoop_stop v post t e hv xs (fun y hy => h y (by simp [hy]))

end Search

/-- The three searches, with comparisons that are any function `p` and may raise, in both twins. `count` is the
number of hits. `indexOf` and `contains` stop at the first hit, so what follows it is never read, even an iterator
that would raise. A raising comparison stops all three there, and so does a raising iterator, which is reached only
when no earlier item ended the search. -/
def SearchExact : Prop :=
  ∀ (α : Type) (same : Same α) (tn : String) (b : α) (p : α → Bool) (xs pre post : List α) (v : α) (e : PyExc)
    (t : Option PyExc),
    ((∀ x ∈ xs, same x b = .ok (p x)) →
      countOfPy same b (.items xs none) = .ok (xs.countP p) ∧
      countOfC same tn b (.items xs none) = .ok (xs.countP p) ∧
      containsOp none same tn b (.items xs none) = .ok (xs.any p)) ∧
    ((∀ x ∈ pre, same x b = .ok false) →
      indexOfPy same b (.items pre none) = .error (.valueError indexMsg) ∧
      indexOfC same tn b (.items pre none) = .error (.valueError indexMsg) ∧
      indexOfPy same b (.items pre (some e)) = .error e ∧
      indexOfC same tn b (.items pre (some e)) = .error e ∧
      containsOp none same tn b (.items pre (some e)) = .error e ∧
      (same v b = .ok true →
        indexOfPy same b (.items (pre ++ v :: post) t) = .ok pre.length ∧
        indexOfC same tn b (.items (pre ++ v :: post) t) = .ok pre.length ∧
        containsOp none same tn b (.items (pre ++ v :: post) t) = .ok true) ∧
      (same v b = .error e →
        indexOfPy same b (.items (pre ++ v :: post) t) = .error e ∧
        indexOfC same tn b (.items (pre ++ v :: post) t) = .error e ∧
        containsOp none same tn b (.items (pre ++ v :: post) t) = .error e)) ∧
    ((∀ x ∈ pre, ∃ h, same x b = .ok h) →
      countOfPy same b (.items pre (some e)) = .error e ∧
      countOfC same tn b (.items pre (some e)) = .error e ∧
      (same v b = .error e →
        countOfPy same b (.items (pre ++ v :: post) t) = .error e ∧
        countOfC same tn b (.items (pre ++ v :: post) t) = .error e)) ∧
    countOfPy same b (.fail e) = .error e ∧ indexOfPy same b (.fail e) = .error e ∧
    (isTypeError e = false →
      countOfC same tn b (.fail e) = .error e ∧ indexOfC same tn b (.fail e) = .error e ∧
      containsOp none same tn b (.fail e) = .error e)

theorem searchExact_proven : SearchExact := by
  intro α same tn b p xs pre post v e t
  refine ⟨?_, ?_, ?_, rfl, rfl, ?_⟩
  · intro h
    have hc := countLoop_all same b p xs 0 h
    have ha := containsLoop_all same b p xs h
    simp only [Nat.zero_add] at hc
    exact ⟨by simp [countOfPy, hc], by simp [countOfC, hc], by simp [containsOp, ha]⟩
  · intro h
    have m0 := indexLoop_miss same b none (.valueError indexMsg) rfl pre 0 h
    have m1 := indexLoop_miss same b (some e) e rfl pre 0 h
    have c1 := containsLoop_tail same b e pre h
    refine ⟨by simp [indexOfPy, m0], by simp [indexOfC, m0], by simp [indexOfPy, m1], by simp [indexOfC, m1],
      by simp [containsOp, c1], ?_, ?_⟩
    · intro hv
      have i1 := indexLoop_hit same b v post t hv pre 0 h
      have c2 := containsLoop_hit same b v post t hv pre h
      simp only [Nat.zero_add] at i1
      exact ⟨by simp [indexOfPy, i1], by simp [indexOfC, i1], by simp [containsOp, c2]⟩
    · intro hv
      have i1 := indexLoop_stop same b v post t e hv pre 0 h
      have c2 := containsLoop_stop same b v post t e hv pre h
      exact ⟨by simp [indexOfPy, i1], by simp [indexOfC, i1], by simp [containsOp, c2]⟩
  · intro h
    have c1 := countLoop_tail same b e pre 0 h
    refine ⟨by simp [countOfPy, c1], by simp [countOfC, c1], ?_⟩
    intro hv
    have c2 := countLoop_stop same b v post t e hv pre 0 h
    exact ⟨by simp [countOfPy, c2], by simp [countOfC, c2]⟩
  · intro h
    have he : iterError tn false e = e := by cases e <;> simp_all [iterError, isTypeError]
    have he2 : iterError tn true e = e := by cases e <;> simp_all [iterError, isTypeError]
    exact ⟨by simp [countOfC, he], by simp [indexOfC, he], by simp [containsOp, he2]⟩

/-! ### `length_hint` -/

/-- `length_hint` in Python, every path. `default` is checked first, a working `len` wins, a `TypeError` from `len`
or from the hint falls through, any other exception propagates, and a negative hint raises. The lookup
`type(obj).__length_hint__` finds the class's attribute, else the metaclass's; an `AttributeError` from it is the
default, any other exception propagates. The default and the hint come back as the objects given, an `int` subclass
included. -/
def LengthHintPyExact : Prop :=
  ∀ (o : HintObj) (d v : Int) (n : Nat) (m m' tn : String) (e : PyExc),
    (o.len = .ok n → lengthHintPy o (.int d) = .ok (.exact n)) ∧
    (isTypeError e = false → o.len = .error e → lengthHintPy o (.int d) = .error e) ∧
    (o.len = .error (.typeError m) →
      (o.hint = none → o.metaHint = none → lengthHintPy o (.int d) = .ok (.exact d)) ∧
      (o.hint = some (.func (.ok .notImplemented)) → lengthHintPy o (.int d) = .ok (.exact d)) ∧
      (o.hint = some (.func (.error (.typeError m'))) → lengthHintPy o (.int d) = .ok (.exact d)) ∧
      (isTypeError e = false → o.hint = some (.func (.error e)) → lengthHintPy o (.int d) = .error e) ∧
      (o.hint = some (.func (.ok (.other tn))) →
        lengthHintPy o (.int d) = .error (.typeError s!"__length_hint__ must be integer, not {tn}")) ∧
      (o.hint = some (.func (.ok (.int v))) → 0 ≤ v → lengthHintPy o (.int d) = .ok (.exact v)) ∧
      (o.hint = some (.func (.ok (.int v))) → v < 0 →
        lengthHintPy o (.int d) = .error (.valueError negativeHint)) ∧
      (∀ g, o.hint = some (.prop g) → lengthHintPy o (.int d) = .ok (.exact d)) ∧
      (∀ r, o.hint = some (.static r (.error (.typeError m'))) → lengthHintPy o (.int d) = .ok (.exact d)) ∧
      (∀ r, o.hint = some (.static r (.ok (.int v))) → 0 ≤ v → lengthHintPy o (.int d) = .ok (.exact v)) ∧
      (o.hint = none → o.metaHint = some (.ok (.int v)) → 0 ≤ v → lengthHintPy o (.int d) = .ok (.exact v)) ∧
      (∀ c, isAttrError e = false → o.hint = some (.desc c (.error e)) → lengthHintPy o (.int d) = .error e) ∧
      (∀ c, o.hint = some (.desc c (.error (.named "AttributeError" m'))) →
        lengthHintPy o (.int d) = .ok (.exact d)) ∧
      (o.hint = none → o.metaHint = none → lengthHintPy o (.intSub d tn) = .ok (.sub d tn)) ∧
      (o.hint = some (.func (.ok (.intSub v tn))) → 0 ≤ v → lengthHintPy o (.int d) = .ok (.sub v tn))) ∧
    lengthHintPy o (.other tn) = .error (.typeError s!"'{tn}' object cannot be interpreted as an integer")

theorem lengthHintPyExact_proven : LengthHintPyExact := by
  intro o d v n m m' tn e
  refine ⟨?_, ?_, ?_, rfl⟩
  · intro h; simp [lengthHintPy, h, bind, Except.bind, pure, Except.pure]
  · intro h1 h; simp [lengthHintPy, h, h1, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw]
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;>
      simp_all [lengthHintPy, hintLookupPy, isTypeError, isAttrError, bind, Except.bind, pure, Except.pure,
        throw, throwThe, MonadExcept.throw, MonadExceptOf.throw]

/-- `length_hint` in C, every path. The checks of the Python twin, with `Py_ssize_t` around them: `default` must
fit, and so must the hint, whose overflow is reported before its sign. An object with `__index__` is a `default`
here and a `TypeError` in Python. -/
def LengthHintCExact : Prop :=
  ∀ (o : HintObj) (d v : Int) (n : Nat) (m m' tn : String) (e : PyExc),
    ((d > ssizeMax ∨ d < ssizeMin) →
      lengthHintC o (.int d) = .error (.overflowError "Python int too large to convert to C ssize_t") ∧
      lengthHintC o (.indexable d) = .error (.overflowError "Python int too large to convert to C ssize_t")) ∧
    lengthHintC o (.other tn) = .error (.typeError s!"'{tn}' object cannot be interpreted as an integer") ∧
    (ssizeMin ≤ d → d ≤ ssizeMax →
      (o.len = .ok n → lengthHintC o (.int d) = .ok n ∧ lengthHintC o (.indexable d) = .ok n) ∧
      (isTypeError e = false → o.len = .error e → lengthHintC o (.int d) = .error e) ∧
      (o.len = .error (.typeError m) →
        (o.hint = none → lengthHintC o (.int d) = .ok d) ∧
        (o.hint = some (.func (.ok .notImplemented)) → lengthHintC o (.int d) = .ok d) ∧
        (o.hint = some (.func (.error (.typeError m'))) → lengthHintC o (.int d) = .ok d) ∧
        (isTypeError e = false → o.hint = some (.func (.error e)) → lengthHintC o (.int d) = .error e) ∧
        (o.hint = some (.func (.ok (.other tn))) →
          lengthHintC o (.int d) = .error (.typeError s!"{o.tn}.__length_hint__() must return an int, not {tn}")) ∧
        (o.hint = some (.func (.ok (.int v))) → 0 ≤ v → v ≤ ssizeMax → lengthHintC o (.int d) = .ok v) ∧
        (o.hint = some (.func (.ok (.int v))) → v < 0 → ssizeMin ≤ v →
          lengthHintC o (.int d) = .error (.valueError (negativeHintC o))) ∧
        (o.hint = some (.func (.ok (.int v))) → (v > ssizeMax ∨ v < ssizeMin) →
          lengthHintC o (.int d) = .error (.overflowError "Python int too large to convert to C ssize_t")) ∧
        (o.hint = some (.prop (.error e)) → lengthHintC o (.int d) = .error e) ∧
        ((o.hint = some (.prop (.ok (.ok (.int v)))) → 0 ≤ v → v ≤ ssizeMax → lengthHintC o (.int d) = .ok v) ∧
          (o.hint = some (.prop (.ok (.error (.typeError m')))) → lengthHintC o (.int d) = .ok d)) ∧
        (∀ r, o.hint = some (.static (.ok (.int v)) r) → 0 ≤ v → v ≤ ssizeMax → lengthHintC o (.int d) = .ok v) ∧
        (∀ p, o.hint = some (.desc (.error e) p) → lengthHintC o (.int d) = .error e) ∧
        (o.hint = some (.func (.ok (.intSub v tn))) → 0 ≤ v → v ≤ ssizeMax → lengthHintC o (.int d) = .ok v) ∧
        (o.hint = none → lengthHintC o (.intSub d tn) = .ok d)))

theorem toSsize_ok (n : Int) (h1 : ssizeMin ≤ n) (h2 : n ≤ ssizeMax) : toSsize n = .ok n := by
  have : ¬(n > ssizeMax ∨ n < ssizeMin) := by omega
  simp [toSsize, this]

theorem toSsize_bad (n : Int) (h : n > ssizeMax ∨ n < ssizeMin) :
    toSsize n = .error (.overflowError "Python int too large to convert to C ssize_t") := by
  simp [toSsize, h]

theorem lengthHintCExact_proven : LengthHintCExact := by
  intro o d v n m m' tn e
  refine ⟨?_, rfl, ?_⟩
  · intro h
    have := toSsize_bad d h
    simp [lengthHintC, this, bind, Except.bind]
  · intro h1 h2
    have hd := toSsize_ok d h1 h2
    refine ⟨?_, ?_, ?_⟩
    · intro h; simp [lengthHintC, hd, h, bind, Except.bind, pure, Except.pure]
    · intro h3 h; simp [lengthHintC, hd, h, h3, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw]
    · intro h
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      rotate_left 11
      · intro p h4
        simp [lengthHintC, hd, h, h4, hintLookupC, isTypeError, bind, Except.bind, pure, Except.pure, throw, throwThe,
          MonadExcept.throw, MonadExceptOf.throw]
      · intro h4 h5 h6
        have hv := toSsize_ok v (by simp only [ssizeMin] at *; omega) h6
        have h7 : ¬ v < 0 := by omega
        simp [lengthHintC, hd, h, h4, hv, h7, hintLookupC, isTypeError, bind, Except.bind, pure, Except.pure]
      · intro h4
        simp [lengthHintC, hd, h, h4, isTypeError, bind, Except.bind, pure, Except.pure]
      rotate_left 8
      · intro h4
        simp [lengthHintC, hd, h, h4, hintLookupC, isTypeError, bind, Except.bind, pure, Except.pure, throw, throwThe,
          MonadExcept.throw, MonadExceptOf.throw]
      · refine ⟨?_, ?_⟩
        · intro h4 h5 h6
          have hv := toSsize_ok v (by simp only [ssizeMin] at *; omega) h6
          have h7 : ¬ v < 0 := by omega
          simp [lengthHintC, hd, h, h4, hv, h7, hintLookupC, isTypeError, bind, Except.bind, pure, Except.pure]
        · intro h4
          simp [lengthHintC, hd, h, h4, hintLookupC, isTypeError, bind, Except.bind, pure, Except.pure]
      · intro r h4 h5 h6
        have hv := toSsize_ok v (by simp only [ssizeMin] at *; omega) h6
        have h7 : ¬ v < 0 := by omega
        simp [lengthHintC, hd, h, h4, hv, h7, hintLookupC, isTypeError, bind, Except.bind, pure, Except.pure]
      · intro h4; simp [lengthHintC, hintLookupC, hd, h, h4, isTypeError, bind, Except.bind, pure, Except.pure]
      · intro h4; simp [lengthHintC, hintLookupC, hd, h, h4, isTypeError, bind, Except.bind, pure, Except.pure]
      · intro h4; simp [lengthHintC, hintLookupC, hd, h, h4, isTypeError, bind, Except.bind, pure, Except.pure]
      · intro h3 h4
        have ht : isTypeError (.typeError m) = true := rfl
        simp [lengthHintC, hintLookupC, hd, h, h3, h4, ht, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw]
      · intro h4; simp [lengthHintC, hintLookupC, hd, h, h4, isTypeError, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw]
      · intro h4 h5 h6
        have hv := toSsize_ok v (by simp only [ssizeMin] at *; omega) h6
        have h7 : ¬ v < 0 := by omega
        simp [lengthHintC, hintLookupC, hd, h, h4, hv, h7, isTypeError, bind, Except.bind, pure, Except.pure]
      · intro h4 h5 h6
        have hv := toSsize_ok v h6 (by simp only [ssizeMax] at *; omega)
        simp [lengthHintC, hintLookupC, hd, h, h4, hv, h5, isTypeError, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw]
      · intro h4 h5
        have hv := toSsize_bad v h5
        simp [lengthHintC, hintLookupC, hd, h, h4, hv, isTypeError, bind, Except.bind, pure, Except.pure]

/-! ### `_compare_digest` -/

/-- `compare_digest` is equality on ASCII strings and on buffers, whatever the lengths, and refuses everything else
with the source's message. -/
def DigestExact : Prop :=
  ∀ (a b : List Nat) (x y : Bool) (ta tb sa sb : String),
    compareDigest (.str true a sa) (.str true b sb) = .ok (decide (a = b)) ∧
    compareDigest (.buffer a) (.buffer b) = .ok (decide (a = b)) ∧
    compareDigest (.str false a sa) (.str y b sb) =
      .error (.typeError "comparing strings with non-ASCII characters is not supported") ∧
    compareDigest (.str x a sa) (.str false b sb) =
      .error (.typeError "comparing strings with non-ASCII characters is not supported") ∧
    compareDigest (.str x a sa) (.buffer b) = .error (.typeError "~a bytes-like object is required") ∧
    compareDigest (.buffer a) (.str y b sb) = .error (.typeError "~a bytes-like object is required") ∧
    compareDigest (.other ta) (.other tb) = .error (.typeError
      s!"unsupported operand types(s) or combination of types: '{ta}' and '{tb}'") ∧
    compareDigest (.str x a sa) (.other tb) = .error (.typeError
      s!"unsupported operand types(s) or combination of types: '{sa}' and '{tb}'") ∧
    compareDigest (.other ta) (.str y b sb) = .error (.typeError
      s!"unsupported operand types(s) or combination of types: '{ta}' and '{sb}'") ∧
    (∀ (e : PyExc) (d : DigestArg),
      compareDigest (.bufferErr e) d = .error e ∧
      compareDigest .bufferNd d = .error (.named "BufferError" ndimMsg) ∧
      compareDigest (.buffer a) (.bufferErr e) = .error e ∧
      compareDigest (.buffer a) .bufferNd = .error (.named "BufferError" ndimMsg) ∧
      compareDigest (.str x a sa) (.bufferErr e) = .error (.typeError "~a bytes-like object is required") ∧
      compareDigest (.other ta) .bufferNd = .error (.typeError "~a bytes-like object is required"))

theorem digestExact_proven : DigestExact := by
  intro a b x y ta tb sa sb
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  rotate_left 4
  · simp [compareDigest, DigestArg.hasBuffer, DigestArg.tn]
  · simp [compareDigest, DigestArg.hasBuffer, DigestArg.tn]
  · simp [compareDigest, DigestArg.hasBuffer, DigestArg.tn]
  rotate_left 1
  · simp [compareDigest, (compareDigestCorrect_proven a b).1]
  · simp [compareDigest, digestBuffer, DigestArg.hasBuffer, (compareDigestCorrect_proven a b).1]
  · simp [compareDigest]
  · simp [compareDigest]
  · intro e d
    refine ⟨?_, ?_, rfl, rfl, rfl, rfl⟩
    · cases d <;> rfl
    · cases d <;> rfl

/-! ### The getters -/

theorem mapPy_mem {β γ : Type} (f : β → Py γ) (r : β → γ) :
    ∀ l : List β, (∀ x ∈ l, f x = .ok (r x)) → mapPy f l = .ok (l.map r)
  | [], _ => rfl
  | x :: xs, h => by
    have hx := h x (by simp)
    have ih := mapPy_mem f r xs (fun y hy => h y (by simp [hy]))
    simp [mapPy, hx, ih]

theorem mapPy_stop {β γ : Type} (f : β → Py γ) (z : β) (post : List β) (e : PyExc) (hz : f z = .error e) :
    ∀ pre : List β, (∀ x ∈ pre, ∃ y, f x = .ok y) → mapPy f (pre ++ z :: post) = .error e
  | [], _ => by simp [mapPy, hz]
  | x :: xs, h => by
    obtain ⟨y, hy⟩ := h x (by simp)
    simp [mapPy, hy, mapPy_stop f z post e hz xs (fun u hu => h u (by simp [hu]))]

theorem mapPy_length {β γ : Type} (f : β → Py γ) : ∀ (l : List β) (r : List γ), mapPy f l = .ok r →
    r.length = l.length
  | [], r, h => by simp [mapPy] at h; subst h; rfl
  | x :: xs, r, h => by
    simp only [mapPy] at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i y _ ys hys
        cases h
        simp [mapPy_length f xs ys hys]

/-- The argument checks, as exact conditions, and not only "the twins agree when they fail". The C check of the
getters tests keywords first and that of `methodcaller` the count first, so `f(1, 2, k=3)` names different faults. -/
def GetterArityExact : Prop :=
  ∀ (name : String) (nargs nkw : Nat),
    (oneArgPy nargs nkw = none ↔ nargs = 1 ∧ nkw = 0) ∧
    (oneArgC name nargs nkw = none ↔ nargs = 1 ∧ nkw = 0) ∧
    (oneArgVectorC name nargs nkw = none ↔ nargs = 1 ∧ nkw = 0) ∧
    (newArgPy nargs nkw = none ↔ nargs ≠ 0 ∧ nkw = 0) ∧
    (newArgC name nargs nkw = none ↔ nargs ≠ 0 ∧ nkw = 0) ∧
    (nkw ≠ 0 → oneArgC name nargs nkw = some (.typeError s!"{name}() takes no keyword arguments")) ∧
    (nargs ≠ 1 → oneArgVectorC name nargs nkw = some (.typeError s!"{name} expected 1 argument, got {nargs}"))

theorem getterArityExact_proven : GetterArityExact := by
  intro name nargs nkw
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [oneArgPy]; split <;> simp_all <;> omega
  · simp only [oneArgC]; split
    · simp_all
    · split <;> simp_all
  · simp only [oneArgVectorC]; split
    · simp_all
    · split <;> simp_all
  · simp only [newArgPy]; split <;> simp_all <;> omega
  · simp only [newArgC]; split
    · simp_all
    · split <;> simp_all
  · intro h; simp [oneArgC, h]
  · intro h; simp [oneArgVectorC, h]

/-- `itemgetter` called, every path: one item gives the value and more give the tuple in key order, in both twins;
the first failing item stops the tuple. C's shortcut answers only for an exact tuple, an index it holds and one in
range; otherwise `obj[item]` runs, and its failure is the outcome. -/
def ItemgetterExact : Prop :=
  ∀ (α κ : Type) (o : ItemObj α κ) (k a b : ItemKey κ) (rest pre post : List (ItemKey κ)) (v : α) (e : PyExc)
    (xs : List α) (i : Nat) (r : ItemKey κ → α),
    (o.get k.key = .ok v →
      itemCallPy [k] o = .ok (.one v) ∧ (fastIndex k = none → itemCallC [k] o = .ok (.one v)) ∧
      (o.exactTuple = none → itemCallC [k] o = .ok (.one v))) ∧
    (o.get k.key = .error e →
      itemCallPy [k] o = .error e ∧ (fastIndex k = none → itemCallC [k] o = .error e) ∧
      (o.exactTuple = none → itemCallC [k] o = .error e) ∧
      (fastIndex k = some i → o.exactTuple = some xs → xs[i]? = none → itemCallC [k] o = .error e)) ∧
    (fastIndex k = some i → o.exactTuple = some xs → xs[i]? = some v → itemCallC [k] o = .ok (.one v)) ∧
    ((∀ x ∈ a :: b :: rest, o.get x.key = .ok (r x)) →
      itemCallPy (a :: b :: rest) o = .ok (.many ((a :: b :: rest).map r)) ∧
      itemCallC (a :: b :: rest) o = .ok (.many ((a :: b :: rest).map r))) ∧
    ((∀ x ∈ pre, ∃ y, o.get x.key = .ok y) → o.get k.key = .error e → (pre ++ k :: post).length ≠ 1 →
      itemCallPy (pre ++ k :: post) o = .error e ∧ itemCallC (pre ++ k :: post) o = .error e)

theorem itemgetterExact_proven : ItemgetterExact := by
  intro α κ o k a b rest pre post v e xs i r
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h
    refine ⟨by simp [itemCallPy, h], ?_, ?_⟩
    · intro h2; simp [itemCallC, h, h2]
    · intro h2; simp [itemCallC, h, h2]
  · intro h
    refine ⟨by simp [itemCallPy, h], ?_, ?_, ?_⟩
    · intro h2; simp [itemCallC, h, h2]
    · intro h2; simp [itemCallC, h, h2]
    · intro h2 h3 h4; simp [itemCallC, h, h2, h3, h4]
  · intro h1 h2 h3; simp [itemCallC, h1, h2, h3]
  · intro h
    have hm := mapPy_mem (fun x : ItemKey κ => o.get x.key) r _ h
    exact ⟨by simp only [itemCallPy]; rw [hm], by simp only [itemCallC]; rw [hm]⟩
  · intro h1 h2 h3
    have hm := mapPy_stop (fun x : ItemKey κ => o.get x.key) k post e h2 pre h1
    have hp : itemCallPy (pre ++ k :: post) o = match mapPy (fun x : ItemKey κ => o.get x.key) (pre ++ k :: post) with
        | .error e => .error e
        | .ok vs => .ok (.many vs) := by
      cases hl : pre ++ k :: post with
      | nil => simp at hl
      | cons p q =>
        cases q with
        | nil => simp [hl] at h3
        | cons _ _ => rfl
    have hc : itemCallC (pre ++ k :: post) o = match mapPy (fun x : ItemKey κ => o.get x.key) (pre ++ k :: post) with
        | .error e => .error e
        | .ok vs => .ok (.many vs) := by
      cases hl : pre ++ k :: post with
      | nil => simp at hl
      | cons p q =>
        cases q with
        | nil => simp [hl] at h3
        | cons _ _ => rfl
    rw [hp, hc, hm]
    exact ⟨rfl, rfl⟩

/-- `joinArgs` is `", ".join`. -/
theorem joinArgs_eq : ∀ l : List String, joinArgs l = String.intercalate ", " l
  | [] => rfl
  | [_] => rfl
  | x :: y :: ys => by rw [join_cons, String.intercalate_cons_cons, joinArgs_eq (y :: ys)]

/-- The `repr` of `itemgetter` and `attrgetter`: the class name and the items, joined by `", "`. A failing `repr` of
an item stops at the first such item. C has a second shape in its source, which comes to the same text, and a
recursion guard that the Python twin lacks. -/
def GetterReprExact : Prop :=
  ∀ (κ : Type) (rep : κ → Py String) (r : κ → String) (cls : String) (items pre post : List κ) (z : κ) (e : PyExc),
    ((∀ k ∈ items, rep k = .ok (r k)) →
      reprPy rep cls items = .ok (cls ++ "(" ++ ", ".intercalate (items.map r) ++ ")") ∧
      reprC rep false cls items = .ok (cls ++ "(" ++ ", ".intercalate (items.map r) ++ ")")) ∧
    ((∀ k ∈ pre, ∃ s, rep k = .ok s) → rep z = .error e →
      reprPy rep cls (pre ++ z :: post) = .error e ∧ reprC rep false cls (pre ++ z :: post) = .error e) ∧
    reprC rep true cls items = .ok (cls ++ "(...)")

theorem getterReprExact_proven : GetterReprExact := by
  intro κ rep r cls items pre post z e
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hm := mapPy_mem rep r items h
    have hp : reprPy rep cls items = .ok (cls ++ "(" ++ ", ".intercalate (items.map r) ++ ")") := by
      simp [reprPy, hm, joinArgs_eq]
    exact ⟨hp, by rw [getterReprTwins_proven]; exact hp⟩
  · intro h1 h2
    have hm := mapPy_stop rep z post e h2 pre h1
    have hp : reprPy rep cls (pre ++ z :: post) = .error e := by simp [reprPy, hm]
    exact ⟨hp, by rw [getterReprTwins_proven]; exact hp⟩
  · simp [reprC]

/-- `attrgetter` names: `split('.')` gives parts with no dot that join back, so it is the split and no other; Python
calls the name's `split`; C keeps an undotted name as the object it was given, a `str` subclass included, and a
dotted one as its exact parts; anything else is refused by both. -/
def AttrNameExact : Prop :=
  ∀ (s : List Char) (c : Chain),
    joinChars (splitChars s) = s ∧ splitChars s ≠ [] ∧ (∀ p ∈ splitChars s, '.' ∉ p) ∧
    namePy (.str s) = .ok (splitChars s) ∧ nameC (.str s) = .ok (splitChars s) ∧
    namePy (.strSub s c) = .ok c ∧
    nameCObj (.str s) = .ok (if '.' ∈ s then .chain (splitChars s) else .single (.str s)) ∧
    nameCObj (.strSub s c) = .ok (if '.' ∈ s then .chain (splitChars s) else .single (.strSub s c)) ∧
    dotjoinObj (.chain (splitChars s)) = .str s ∧
    namePy .other = .error (.typeError attrNameMsg) ∧ nameC .other = .error (.typeError attrNameMsg) ∧
    nameCObj .other = .error (.typeError attrNameMsg)

theorem split_no_dot : ∀ (s : List Char), ∀ p ∈ splitChars s, '.' ∉ p
  | [] => by simp [splitChars]
  | c :: cs => by
    have ih := split_no_dot cs
    simp only [splitChars]
    cases hs : splitChars cs with
    | nil => simp
    | cons r rs =>
      rw [hs] at ih
      by_cases hc : c = '.'
      · simp only [hc, ↓reduceIte]
        intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · simp
        · exact ih p (by simpa using hp)
      · simp only [hc, ↓reduceIte]
        intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · have := ih r (by simp)
          simp only [List.mem_cons, not_or]
          exact ⟨fun h => hc h.symm, this⟩
        · exact ih p (List.mem_cons_of_mem _ hp)

theorem attrNameExact_proven : AttrNameExact := by
  intro s c
  have h := split_join s
  refine ⟨h.1, h.2, split_no_dot s, rfl, rfl, rfl, ?_, ?_, by simp [dotjoinObj, h.1], rfl, rfl, rfl⟩
  · by_cases hd : '.' ∈ s <;> simp [nameCObj, hd]
  · by_cases hd : '.' ∈ s <;> simp [nameCObj, hd]

/-- `attrgetter` built and called, every path. Every `str` is accepted, in both twins, and a dotted name walks left
to right: the first failing lookup is the outcome, and the walk never reads past it. One name gives the value, more
give the tuple. -/
def AttrCallExact : Prop :=
  ∀ (α : Type) (ga : GetAttr α) (obj v : α) (n : List Char) (ns c : Chain) (e : PyExc) (a b : Chain)
    (rest pre post : List Chain) (r : Chain → α) (args : List AttrArg),
    dotted ga obj [] = .ok obj ∧
    (ga obj n = .error e → dotted ga obj (n :: ns) = .error e) ∧
    (ga obj n = .ok v → dotted ga obj (n :: ns) = dotted ga v ns) ∧
    (dotted ga obj c = .ok v → attrCall ga [c] obj = .ok (.one v)) ∧
    (dotted ga obj c = .error e → attrCall ga [c] obj = .error e) ∧
    ((∀ x ∈ a :: b :: rest, dotted ga obj x = .ok (r x)) →
      attrCall ga (a :: b :: rest) obj = .ok (.many ((a :: b :: rest).map r))) ∧
    ((∀ x ∈ pre, ∃ y, dotted ga obj x = .ok y) → dotted ga obj c = .error e → (pre ++ c :: post).length ≠ 1 →
      attrCall ga (pre ++ c :: post) obj = .error e) ∧
    ((∀ x ∈ args, x ≠ .other) → ∃ g l, attrgetterNewPy args = .ok g ∧ attrgetterNewC args = .ok l ∧ g.attrs = args)

theorem attrCallExact_proven : AttrCallExact := by
  intro α ga obj v n ns c e a b rest pre post r args
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; simp [dotted, h]
  · intro h; simp [dotted, h]
  · intro h; simp [attrCall, h]
  · intro h; simp [attrCall, h]
  · intro h
    have hm := mapPy_mem (dotted ga obj) r _ h
    simp only [attrCall]; rw [hm]
  · intro h1 h2 h3
    have hm := mapPy_stop (dotted ga obj) c post e h2 pre h1
    have hp : attrCall ga (pre ++ c :: post) obj = match mapPy (dotted ga obj) (pre ++ c :: post) with
        | .error e => .error e
        | .ok vs => .ok (.many vs) := by
      cases hl : pre ++ c :: post with
      | nil => simp at hl
      | cons p q =>
        cases q with
        | nil => simp [hl] at h3
        | cons _ _ => rfl
    rw [hp, hm]
  · intro h
    have hs : ∀ l : List AttrArg, (∀ x ∈ l, x ≠ .other) →
        (∃ ys, mapPy namePy l = .ok ys) ∧ (∃ ys, mapPy nameC l = .ok ys) := by
      intro l
      induction l with
      | nil => intro _; exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
      | cons x xs ih =>
        intro hl
        obtain ⟨⟨ys, hy⟩, ⟨zs, hz⟩⟩ := ih (fun y hy => hl y (by simp [hy]))
        have hx := hl x (by simp)
        cases x with
        | other => exact absurd rfl hx
        | str s => exact ⟨⟨_, by simp [mapPy, namePy, hy]; rfl⟩, ⟨_, by simp [mapPy, nameC, hz]; rfl⟩⟩
        | strSub s c => exact ⟨⟨_, by simp [mapPy, namePy, hy]; rfl⟩, ⟨_, by simp [mapPy, nameC, hz]; rfl⟩⟩
    obtain ⟨⟨ys, hy⟩, ⟨zs, hz⟩⟩ := hs args h
    exact ⟨⟨args, ys⟩, zs, by simp [attrgetterNewPy, hy], by simp [attrgetterNewC, hz], rfl⟩

/-- `methodcaller` built and called, every path. Any `str` is stored with the arguments as given, in both twins, and
anything else is refused. A call looks the method up on the object and then calls it with the stored arguments: a
failing lookup is the outcome, and nothing is called. -/
def MethodcallerExact : Prop :=
  ∀ (α β : Type) (m : Meth α β) (c : Mc α) (obj : α) (f : List α → List (String × α) → Py β) (e : PyExc)
    (s : List Char) (sub : Chain) (args : List α) (kw : List (String × α)) (nargs nkw : Nat),
    (m obj c.name = .error e → mcCall m c obj = .error e ∧ mcCallC m c obj = .error e) ∧
    (m obj c.name = .ok f → mcCall m c obj = f c.args c.kw ∧ mcCallC m c obj = f c.args c.kw) ∧
    (usesVectorcall nargs nkw = true ↔ nargs + nkw < 7) ∧
    mcNewPy (some (.str s)) args kw = .ok ⟨s, args, kw⟩ ∧ mcNewC (some (.str s)) args kw = .ok ⟨s, args, kw⟩ ∧
    mcNewPy (some (.strSub s sub)) args kw = .ok ⟨s, args, kw⟩ ∧
    mcNewC (some (.strSub s sub)) args kw = .ok ⟨s, args, kw⟩ ∧
    mcNewPy (some .other) args kw = .error (.typeError "method name must be a string") ∧
    mcNewC (some .other) args kw = .error (.typeError "method name must be a string") ∧
    mcNewC none args kw = .error (.typeError "methodcaller needs at least one argument, the method name") ∧
    (∀ nm : String, nargs ≠ 1 → oneArgVectorC nm nargs nkw =
      some (.typeError s!"{nm} expected 1 argument, got {nargs}")) ∧
    (∀ nm : String, nkw ≠ 0 → oneArgVectorC nm 1 nkw = some (.typeError s!"{nm}() takes no keyword arguments")) ∧
    (∀ nm : String, oneArgVectorC nm 1 0 = none) ∧
    (∀ nm : String, nkw ≠ 0 → oneArgC nm nargs nkw = some (.typeError s!"{nm}() takes no keyword arguments")) ∧
    (∀ nm : String, nargs ≠ 1 → oneArgC nm nargs 0 =
      some (.typeError s!"{nm} expected 1 argument, got {nargs}"))

theorem methodcallerExact_proven : MethodcallerExact := by
  intro α β m c obj f e s sub args kw nargs nkw
  have ht := fun o => (methodcallerTwins_proven α β m c o).2.1
  refine ⟨?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, fun _ => rfl, ?_, ?_⟩
  rotate_left 3
  · intro nm h; simp [oneArgVectorC, h]
  · intro nm h; simp [oneArgVectorC, h]
  · intro nm h; simp [oneArgC, h]
  · intro nm h; simp [oneArgC, h]
  · intro h
    have : mcCall m c obj = .error e := by simp [mcCall, h]
    exact ⟨this, by rw [ht, this]⟩
  · intro h
    have : mcCall m c obj = f c.args c.kw := by simp [mcCall, h]
    exact ⟨this, by rw [ht, this]⟩
  · simp [usesVectorcall]; omega

/-- The `repr` of `methodcaller`, for a name and arguments whose `repr` may raise: the two twins agree on every
outcome. False: Python evaluates `repr(self._name)` first (Lib/operator.py:330), C formats `%R` of `mc->name` last
(Modules/_operator.c:1865), after the arguments. For `methodcaller(S('f'), X())` where both `S.__repr__` and
`X.__repr__` raise, Python raises the name's exception and C the argument's
(bugs/corelibs-operator-twin-str-subclass.yaml). -/
def McReprExact : Prop :=
  ∀ (α : Type) (rep : α → Py String) (cls : String) (nameRep : Py String) (c : Mc α),
    mcReprC rep false cls nameRep c = mcReprPy rep cls nameRep c

theorem mcReprExact_refuted : ¬McReprExact := by
  intro h
  have := h Nat (fun _ => .error (.valueError "arg")) "c" (.error (.valueError "name")) ⟨['f'], [0], []⟩
  revert this
  decide

/-- The `repr` of `methodcaller`, each twin on its own, every outcome. With every `repr` succeeding the twins give
one text, the class name with the name, the arguments and the keywords joined by `", "`. Python's first step is the
name: its exception is the outcome whatever the arguments do. C's last step is the name, except with no arguments
at all, where it is the only one: the first failing argument or keyword `repr` is C's outcome whatever the name
does, and the name's exception comes out only when every argument printed. The recursion guard is C's alone. -/
def McReprOrder : Prop :=
  ∀ (α : Type) (rep : α → Py String) (r : α → String) (cls nameRepr : String) (c : Mc α) (pre post : List α)
    (z : α) (e e' : PyExc) (kpre kpost : List (String × α)) (key : String),
    ((∀ a, rep a = .ok (r a)) →
      mcReprPy rep cls (.ok nameRepr) c = .ok (cls ++ "(" ++
        ", ".intercalate (nameRepr :: c.args.map r ++ c.kw.map (fun p => p.1 ++ "=" ++ r p.2)) ++ ")") ∧
      mcReprC rep false cls (.ok nameRepr) c = mcReprPy rep cls (.ok nameRepr) c) ∧
    mcReprPy rep cls (.error e) c = .error e ∧
    ((∀ a, rep a = .ok (r a)) → mcReprC rep false cls (.error e) c = .error e) ∧
    (c.args = pre ++ z :: post → (∀ a ∈ pre, ∃ s, rep a = .ok s) → rep z = .error e' →
      ∀ nameRep, mcReprC rep false cls nameRep c = .error e' ∧ mcReprPy rep cls (.ok nameRepr) c = .error e') ∧
    ((∀ a ∈ c.args, rep a = .ok (r a)) → c.kw = kpre ++ (key, z) :: kpost → (∀ p ∈ kpre, ∃ s, rep p.2 = .ok s) →
      rep z = .error e' →
      ∀ nameRep, mcReprC rep false cls nameRep c = .error e' ∧ mcReprPy rep cls (.ok nameRepr) c = .error e') ∧
    (∀ nameRep, mcReprC rep true cls nameRep c = .ok (cls ++ "(...)"))

theorem mcReprOrder_proven : McReprOrder := by
  intro α rep r cls nameRepr c pre post z e e' kpre kpost key
  have hagree : ∀ nameRepr : String, mcReprC rep false cls (.ok nameRepr) c = mcReprPy rep cls (.ok nameRepr) c := by
    intro nameRepr
    by_cases he : (c.args.isEmpty && c.kw.isEmpty) = true
    · have e1 : c.args = [] := by simpa using (Bool.and_eq_true_iff.mp he).1
      have e2 : c.kw = [] := by simpa using (Bool.and_eq_true_iff.mp he).2
      simp [mcReprC, mcReprPy, e1, e2, mapPy, joinArgs, Except.map]
    · simp only [mcReprC, mcReprPy, Bool.false_eq_true, ↓reduceIte, he]
      cases hm : mapPy rep c.args with
      | error e => rfl
      | ok a =>
        simp only
        cases hk : mapPy (fun p : String × α => (rep p.2).map (fun x => p.1 ++ "=" ++ x)) c.kw with
        | error e => rfl
        | ok k =>
          simp only
          have hla := mapPy_length _ _ _ hm
          have hlk := mapPy_length _ _ _ hk
          cases hl : a ++ k with
          | nil =>
            have h3 := List.append_eq_nil_iff.mp hl
            have e1 : c.args = [] := by
              apply List.length_eq_zero_iff.1
              rw [← hla, h3.1]; rfl
            have e2 : c.kw = [] := by
              apply List.length_eq_zero_iff.1
              rw [← hlk, h3.2]; rfl
            simp [e1, e2] at he
          | cons x xs =>
            simp only [List.cons_append, hl]
            rw [join_cons]
            simp [String.append_assoc]
  refine ⟨?_, rfl, ?_, ?_, ?_, fun _ => by simp [mcReprC]⟩
  · intro h
    have h1 : mapPy rep c.args = .ok (c.args.map r) := mapPy_mem rep r _ (fun a _ => h a)
    let rk : String × α → String := fun p => p.1 ++ "=" ++ r p.2
    have h2 : mapPy (fun p : String × α => (rep p.2).map (fun x => p.1 ++ "=" ++ x)) c.kw =
        .ok (c.kw.map rk) := mapPy_mem _ rk _ (fun p _ => by simp [h, Except.map, rk])
    refine ⟨?_, hagree nameRepr⟩
    simp only [mcReprPy, h1, h2, joinArgs_eq]
    rfl
  · intro h
    have h1 : mapPy rep c.args = .ok (c.args.map r) := mapPy_mem rep r _ (fun a _ => h a)
    let rk : String × α → String := fun p => p.1 ++ "=" ++ r p.2
    have h2 : mapPy (fun p : String × α => (rep p.2).map (fun x => p.1 ++ "=" ++ x)) c.kw =
        .ok (c.kw.map rk) := mapPy_mem _ rk _ (fun p _ => by simp [h, Except.map, rk])
    by_cases he : (c.args.isEmpty && c.kw.isEmpty) = true
    · simp [mcReprC, he, Except.map]
    · simp only [mcReprC, Bool.false_eq_true, ↓reduceIte, he, h1, h2]
  · intro h1 h2 h3 nameRep
    have hm := mapPy_stop rep z post e' h3 pre h2
    have hne : (c.args.isEmpty && c.kw.isEmpty) = false := by simp [h1]
    refine ⟨?_, ?_⟩
    · simp [mcReprC, hne, h1, hm]
    · simp [mcReprPy, h1, hm]
  · intro h1 h2 h3 h4 nameRep
    have ha : mapPy rep c.args = .ok (c.args.map r) := mapPy_mem rep r _ h1
    have hm := mapPy_stop (fun p : String × α => (rep p.2).map (fun x => p.1 ++ "=" ++ x)) (key, z) kpost e'
      (by simp [h4, Except.map]) kpre (fun p hp => by
        obtain ⟨s, hs⟩ := h3 p hp
        exact ⟨p.1 ++ "=" ++ s, by simp [hs, Except.map]⟩)
    have hne : (c.args.isEmpty && c.kw.isEmpty) = false := by simp [h2]
    refine ⟨?_, ?_⟩
    · simp only [mcReprC, Bool.false_eq_true, ↓reduceIte, hne]
      rw [ha]
      simp only [h2, hm]
    · simp only [mcReprPy]
      rw [ha]
      simp only [h2, hm]

end PyLean.CoreLibs.Operator
