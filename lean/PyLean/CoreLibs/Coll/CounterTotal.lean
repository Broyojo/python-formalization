import PyLean.CoreLibs.Coll.CounterProps5

/-!
`Counter.total`, Lib/collections/__init__.py:624-626, `sum(self.values())`, with a model of builtin
`sum` (`builtin_sum_impl`, Python/bltinmodule.c:2878-3090, CPython 3.15.2) for `start=0`: the
`PyLong_CheckExact` fast path in a C `Py_ssize_t` (:2922-2972), then `PyNumber_Add` from the first
item that is not an int or would overflow. The float and complex fast paths (:2974-3076, compensated
summation) are entered when the running result becomes an exact float or complex; they are the
parameter `fcTail`, not modelled here.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace PyLean.CoreLibs.Coll

open PyLean

variable {ν : Type}

/-- What `sum` tests of an object: an exact `int` (or `bool`) and its value, an exact `float` or
`complex`, or anything else. -/
inductive SKind where
  | int (n : Int)
  | floatOrComplex
  | other

/-- The generic loop, :2963-2971 and the end of the function: `result = result + item`. -/
def sumGeneric (N : Num ν) : ν → List ν → Option PyExc → Py ν
  | r, [], stop => match stop with
    | none => .ok r
    | some e => .error e
  | r, x :: xs, stop => do
    let r ← N.add r x
    sumGeneric N r xs stop

/-- From the first item that is not an exact int or would overflow `Py_ssize_t`:
`PyLong_FromSsize_t(i_result) + item` (:2957-2966), then the remaining items by `fcTail` if that result
is an exact float or complex (:2974), else by the generic loop. -/
def sumBreak (N : Num ν) (kindOf : ν → SKind) (ofInt : Int → ν)
    (fcTail : ν → List ν → Option PyExc → Py ν) (acc : Int) (x : ν) (xs : List ν) (stop : Option PyExc) :
    Py ν := do
  let r ← N.add (ofInt acc) x
  match kindOf r with
  | .floatOrComplex => fcTail r xs stop
  | _ => sumGeneric N r xs stop

/-- `sum(items)` with `start` omitted: the int fast path on `i_result` (:2929-2955). -/
def sumP (N : Num ν) (kindOf : ν → SKind) (ofInt : Int → ν)
    (fcTail : ν → List ν → Option PyExc → Py ν) (acc : Int) : List ν → Option PyExc → Py ν
  | [], stop => match stop with
    | none => .ok (ofInt acc)
    | some e => .error e
  | x :: xs, stop =>
    match kindOf x with
    | .int b =>
      if (if acc ≥ 0 then b ≤ ssizeMax - acc else b ≥ ssizeMin - acc) then
        sumP N kindOf ofInt fcTail (acc + b) xs stop
      else sumBreak N kindOf ofInt fcTail acc x xs stop
    | _ => sumBreak N kindOf ofInt fcTail acc x xs stop

/-- `Counter.total`, :624-626: `sum(self.values())`. -/
def counterTotal {κ : Type} (N : Num ν) (kindOf : ν → SKind) (ofInt : Int → ν)
    (fcTail : ν → List ν → Option PyExc → Py ν) (d : D κ ν) : Py ν :=
  sumP N kindOf ofInt fcTail 0 (D.values d) none

/-- **`total()` is the sum of the counts.** For every key type: with int counts (`int` objects
added exactly by `+`, whether or not the fast path's `Py_ssize_t` overflows), `c.total()` is the
sum of the counts; with counts that are not ints, floats or complexes and whose sums are not
either (`Fraction`, `Decimal`, user types), it is `((0 + c1) + c2) + ...` in insertion order, `+`
free to raise, the first exception propagating.

Source: docstring 'Sum of the counts', Lib/collections/__init__.py:625; Python/bltinmodule.c:2878-2972. -/
def CounterTotalSum : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] (fcInt : Int → List Int → Option PyExc → Py Int)
    (fc : ν → List ν → Option PyExc → Py ν) (N : Num ν) (kindOf : ν → SKind) (ofInt : Int → ν)
    (d : D κ Int) (e : D κ ν),
    counterTotal intNum SKind.int id fcInt d = .ok (D.values d).sum ∧
    ((∀ v, kindOf v = .other) →
      counterTotal N kindOf ofInt fc e = sumGeneric N (ofInt 0) (D.values e) none)

theorem sumGeneric_int (r : Int) : ∀ (xs : List Int), sumGeneric intNum r xs none = .ok (r + xs.sum)
  | [] => by simp [sumGeneric]
  | x :: xs => by
    show (Except.ok (r + x) >>= fun r => sumGeneric intNum r xs none) = _
    rw [ok_bind, sumGeneric_int (r + x) xs]
    simp [Int.add_assoc]

theorem sumP_int (fc : Int → List Int → Option PyExc → Py Int) :
    ∀ (xs : List Int) (acc : Int), sumP intNum SKind.int id fc acc xs none = .ok (acc + xs.sum)
  | [] => by intro acc; simp [sumP]
  | x :: xs => by
    intro acc
    have hb : sumBreak intNum SKind.int id fc acc x xs none = .ok (acc + (x :: xs).sum) := by
      show (Except.ok (acc + x) >>= fun r => match SKind.int r with
        | .floatOrComplex => fc r xs none
        | _ => sumGeneric intNum r xs none) = _
      rw [ok_bind]
      show sumGeneric intNum (acc + x) xs none = _
      rw [sumGeneric_int]
      simp [Int.add_assoc]
    show (if (if acc ≥ 0 then x ≤ ssizeMax - acc else x ≥ ssizeMin - acc) then
        sumP intNum SKind.int id fc (acc + x) xs none
      else sumBreak intNum SKind.int id fc acc x xs none) = _
    by_cases hc : (if acc ≥ 0 then x ≤ ssizeMax - acc else x ≥ ssizeMin - acc)
    · rw [if_pos hc, sumP_int fc xs (acc + x)]; simp [Int.add_assoc]
    · rw [if_neg hc]; exact hb

theorem sumP_other (N : Num ν) (kindOf : ν → SKind) (ofInt : Int → ν) (fc : ν → List ν → Option PyExc → Py ν)
    (h : ∀ v, kindOf v = .other) : ∀ (xs : List ν),
      sumP N kindOf ofInt fc 0 xs none = sumGeneric N (ofInt 0) xs none
  | [] => rfl
  | x :: xs => by
    simp only [sumP, h x, sumBreak, sumGeneric]
    cases N.add (ofInt 0) x with
    | error e => rfl
    | ok r => simp [h r]

theorem counterTotalSum_proven : CounterTotalSum := by
  intro κ ν _ fcInt fc N kindOf ofInt d e
  refine ⟨?_, fun h => ?_⟩
  · unfold counterTotal; rw [sumP_int]; simp
  · unfold counterTotal; exact sumP_other N kindOf ofInt fc h _

end PyLean.CoreLibs.Coll
