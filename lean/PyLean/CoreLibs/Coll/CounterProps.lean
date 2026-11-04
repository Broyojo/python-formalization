import PyLean.CoreLibs.Coll.Counter

/-!
Properties of the generic `Counter` model of `Counter.lean` (Lib/collections/__init__.py:540-1033,
Modules/_collectionsmodule.c:2544-2655, CPython 3.15.2).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace PyLean.CoreLibs.Coll

open PyLean
open PyLean.Accel.Heapq (Eff SEnv Sorter HO hEnv nSelect pySortedBy pureKey builtinHier Hier isA SortOk
  kOf sorted_honest NSelectIsSortedPrefix nSelectIsSortedPrefix_proven LenTrue)

variable {κ ν : Type} [DecidableEq κ]

/-! ### Helpers -/

theorem dHash_ok {K : KOps κ} {k : κ} (h : K.hash k = .ok ()) : dHash K k = .ok () := by
  simp [dHash, h]

theorem dGet_ok {K : KOps κ} {k : κ} (d : D κ ν) (z : ν) (h : K.hash k = .ok ()) :
    dGet K d k z = .ok ((D.get? d k).getD z) := by
  unfold dGet; rw [dHash_ok h]; rfl

theorem dSet_ok {K : KOps κ} {k : κ} (d : D κ ν) (v : ν) (h : K.hash k = .ok ()) :
    dSet K d k v = .ok (D.set d k v) := by
  unfold dSet; rw [dHash_ok h]; rfl

theorem dMem_ok {K : KOps κ} {k : κ} (d : D κ ν) (h : K.hash k = .ok ()) :
    dMem K d k = .ok (D.mem d k) := by
  unfold dMem; rw [dHash_ok h]; rfl

theorem loopS_pure {σ α : Type} {f : σ → α → Py σ} {g : σ → α → σ} :
    ∀ (xs : List α) (s : σ), (∀ s, ∀ x ∈ xs, f s x = .ok (g s x)) → loopS f s xs = (xs.foldl g s, none)
  | [], _, _ => rfl
  | x :: xs, s, h => by
    simp only [loopS, h s x (by simp), List.foldl_cons]
    exact loopS_pure xs _ (fun s y hy => h s y (by simp [hy]))

theorem forIt_congr {σ α : Type} {f g : σ → α → Py σ} (h : ∀ s x, f s x = g s x) (s : σ) (it : FIt α) :
    forIt f s it = forIt g s it := by
  have : f = g := funext fun s => funext fun x => h s x
  subst this; rfl

theorem update_nil_WF {d : D κ ν} (h : D.WF d) : D.update [] d = d := by
  rw [D.update_fresh h (by simp)]; rfl

/-! ### `_count_elements`: C and Python twins -/

/-- **`_count_elements` twins agree.** For every key and count type, every target mapping and
every iterable, the C function (fast or slow path) and the Python one leave the same dict and
raise the same exception, as long as `0 + 1` is the object `1` (true of ints).

Source: invariant, C and Python twins (Lib/collections/__init__.py:546-549 replaces the Python
function by the C one). False twice: an instance attribute `get` is seen by `mapping.get` (:542)
but not by the C fast-path test, which looks at the type (Modules/_collectionsmodule.c:2566-2573);
and an unhashable element is reported by the C fast path with the bare hash error
(:2591-2594) where `dict.get` in the Python twin wraps it (`dict_unhashable_type`). -/
def CountElementsTwins : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] [DecidableEq ν] (K : KOps κ) (N : Num ν) (T : CTarget κ ν) (d : D κ ν)
    (it : Py (FIt κ)), N.add N.zero N.one = .ok N.one → countPy K N T d it = countC K N T d it

/-- A key type whose every key hashes. -/
def hashAll : KOps Nat := ⟨fun _ => .ok (), fun _ => "int"⟩

/-- `c = Counter(); c.get = lambda k, d=0: 10; _count_elements(c, [0])`: the Python twin
stores `11`, the C fast path `1`. -/
theorem countElementsTwins_refuted : ¬ CountElementsTwins := by
  intro h
  have := h Nat Int hashAll intNum { instGet := some (fun _ _ _ => .ok 10) } [] (.ok (FIt.ofList [0])) rfl
  exact absurd this (by decide)

/-- The same with no instance attribute, for an unhashable element. -/
def CountElementsTwinsHashable : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] [DecidableEq ν] (K : KOps κ) (N : Num ν) (T : CTarget κ ν) (d : D κ ν)
    (it : Py (FIt κ)), T.instGet = none → N.add N.zero N.one = .ok N.one →
      countPy K N T d it = countC K N T d it

/-- A key whose `__hash__` raises `TypeError('unhashable type: 'list'')`. -/
def hashNone : KOps Nat := ⟨fun _ => .error (.typeError "unhashable type: 'list'"), fun _ => "list"⟩

/-- `_count_elements(Counter(), [[1]])`: C raises `unhashable type: 'list'`, Python
`cannot use 'list' as a dict key (unhashable type: 'list')`. -/
theorem countElementsTwinsHashable_refuted : ¬ CountElementsTwinsHashable := by
  intro h
  have := h Nat Int hashNone intNum {} [] (.ok (FIt.ofList [0])) rfl rfl
  exact absurd this (by decide)

/-- **The twins agree once both differences are excluded.** With no instance attribute `get`
and an element type whose `__hash__` never raises a bare `TypeError` (it may raise anything
else), the Python `_count_elements` and the C one, on either path (`type(mapping).get` and
`__setitem__` overridden or not, each free to raise), leave the same dict and raise the same
exception, for every iterable (`iter()` and `next()` may raise), every count type whose `0 + 1`
is `1`, and every partial update made before an exception.

Source: narrowing of `coll-count-elements-twins`. -/
def CountElementsTwinsNarrow : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] [DecidableEq ν] (K : KOps κ) (N : Num ν) (T : CTarget κ ν) (d : D κ ν)
    (it : Py (FIt κ)), T.instGet = none → (∀ k m, K.hash k ≠ .error (.typeError m)) →
      N.add N.zero N.one = .ok N.one → countPy K N T d it = countC K N T d it

theorem countElementsTwinsNarrow_proven : CountElementsTwinsNarrow := by
  intro κ ν _ _ K N T d it hinst hhash hone
  cases it with
  | error e => rfl
  | ok it =>
    obtain ⟨tg, ts, ig⟩ := T
    simp only at hinst
    subst hinst
    cases tg <;> cases ts
    · show forIt _ d it = countCFast K N d it
      unfold countCFast
      apply forIt_congr
      intro s key
      simp only [boundGet, setItem, dGet, dSet, dHash]
      cases hk : K.hash key with
      | error e =>
        cases e <;> first | exact absurd hk (hhash _ _) | rfl
      | ok u =>
        cases u
        cases hg : D.get? s key with
        | none => simp [hone]; rfl
        | some old => cases N.add old N.one <;> rfl
    all_goals
      show forIt _ d it = countCSlow K N _ d it
      unfold countCSlow
      apply forIt_congr
      intro s key
      cases hb : boundGet K _ s key N.zero with
      | error e => simp only [hb]; rfl
      | ok old =>
        simp only [hb]
        by_cases h0 : old = N.zero
        · subst h0; simp [bind, Except.bind, hone] <;> rfl
        · simp [bind, Except.bind, h0] <;> rfl

end PyLean.CoreLibs.Coll
