import PyLean.Itertools.Simple
import PyLean.Itertools.CombProps

/-!
`batched`: the C object against the doc equivalent (which uses the C `islice`).
-/

namespace PyLean.Itertools

open PyLean

local notation "D" => docIsliceLoop

theorem D_take (B : Int) : ∀ (xs : List Int) (i : Int),
    D (some B) 1 i i xs = (xs.take (B - i).toNat, min xs.length (B - i).toNat)
  | [], i => by simp [docIsliceLoop]
  | x :: xs, i => by
    by_cases h : B ≤ i
    · rw [D_stop B 1 i i _ h]
      simp [show (B - i).toNat = 0 by omega]
    · rw [D_yield (some B) 1 i x xs (by simp [BoundAbove]; omega), D_take B xs (i + 1)]
      obtain ⟨k, hk⟩ : ∃ k : Nat, (B - i).toNat = k + 1 := ⟨(B - i).toNat - 1, by omega⟩
      rw [hk, show (B - (i + 1)).toNat = k by omega]
      simp <;> omega

/-- `islice(it, n)` for `1 <= n <= sys.maxsize` takes `min(n, len)` items. -/
theorem cIslice_stop (it : List Int) (n : Int) (h1 : 1 ≤ n) (h2 : n ≤ ssizeMax)
    (hl : (it.length : Int) ≤ ssizeMax) :
    cIslice it [some n] = ((it.take n.toNat, none), min (it.length : Int) n) := by
  have hok : IsliceArgsOk [some n] := by simp [IsliceArgsOk]
  have hs : IsliceArgsSsize [some n] := by
    simp [IsliceArgsSsize, InSsize]; rw [ssizeMin_eq] at *; rw [ssizeMax_eq] at *; omega
  have hag := isliceDocAgreeNoWrap_proven it [some n] hok hl hs (by simp [isliceRef])
  have hd : docIslice it [some n] = (Run.ok (it.take n.toNat), min (it.length : Int) n) := by
    have := doc_args_ok [some n] hok (by simp [IsliceRefOk, isliceRef, StopOk]; omega)
    simp only [docIslice, this, isliceRef, Option.map, show max 0 n = n by omega]
    rw [D_take n it 0]
    simp [Run.ok]; omega
  simp only [isliceAgree] at hag
  rw [hd] at hag
  obtain ⟨h1', h2', h3'⟩ := hag
  simp only [Run.ok, Option.isSome_none, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at h1' h2' h3'
  ext1
  · ext1 <;> simp [h1', h3']
  · exact h2'

theorem batchedLoop_eq (n : Int) (strict : Bool) (h1 : 1 ≤ n) (h2 : n ≤ ssizeMax)
    (ht : tupleNewOk n = true) : ∀ (fuel : Nat) (it : List Int), (it.length : Int) ≤ ssizeMax →
    drain cBatchedNext fuel { it := it, batchSize := n, strict := strict } = docBatchedLoop n strict fuel it
  | 0, _, _ => rfl
  | fuel + 1, it, hl => by
    rw [drain_succ]
    simp only [cBatchedNext, docBatchedLoop, show ¬ n < 0 by omega, ↓reduceIte, ht, Bool.not_true,
      Bool.false_eq_true, cIslice_stop it n h1 h2 hl]
    have hd : it.drop (min (it.length : Int) n).toNat = it.drop n.toNat := by
      by_cases hc : (it.length : Int) ≤ n
      · rw [List.drop_of_length_le (by omega), List.drop_of_length_le (by omega)]
      · congr 1; omega
    by_cases hfull : ((it.take n.toNat).length : Int) = n
    · have hne : it.take n.toNat ≠ [] := by intro h; rw [h] at hfull; simp at hfull; omega
      simp only [hfull, ↓reduceIte, hne, bne_self_eq_false, Bool.and_false, Bool.false_eq_true, hd,
        Run.cons]
      rw [batchedLoop_eq n strict h1 h2 ht fuel _ (by simp; omega)]
    · simp only [hfull, ↓reduceIte]
      by_cases hz : (it.take n.toNat).length = 0
      · have : it.take n.toNat = [] := List.eq_nil_of_length_eq_zero hz
        simp [hz, this, Run.ok]
      · have hne : it.take n.toNat ≠ [] := by intro h; rw [h] at hz; simp at hz
        simp only [hz, ↓reduceIte, hne]
        cases strict with
        | true =>
          simp only [List.length_take] at hfull
          simp [hfull, Run.err]
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_and, hd, Run.cons]
          rw [batchedLoop_eq n false h1 h2 ht fuel _ (by simp; omega)]

/-- Broad: for every int `n`, C `batched` yields the doc equivalent's batches
and raises in the same cases. -/
def BatchedDocAgree : Prop :=
  ∀ (l : List Int) (n : Int) (strict : Bool), (l.length : Int) ≤ ssizeMax →
    runAgree (cBatched l n strict) (docBatched l n strict)

theorem batchedDocAgree_refuted : ¬BatchedDocAgree := by
  intro h
  have := (h [1, 2, 3] (2 ^ 63 - 1) false (by decide)).1
  revert this
  decide

/-- Narrowed to `n` for which a result tuple of `n` items can be allocated. -/
def BatchedDocAgreeAlloc : Prop :=
  ∀ (l : List Int) (n : Int) (strict : Bool), (l.length : Int) ≤ ssizeMax → tupleNewOk n = true →
    runAgree (cBatched l n strict) (docBatched l n strict)

theorem batchedDocAgreeAlloc_proven : BatchedDocAgreeAlloc := by
  intro l n strict hl ht
  by_cases h1 : n < 1
  · have hc : ∃ e, cBatched l n strict = Run.err e := by
      simp only [cBatched, cBatchedNew]
      cases ha : asSsize n with
      | error e => exact ⟨e, by simp [bind, Except.bind]⟩
      | ok v =>
        have hv : v = n := by simp only [asSsize] at ha; split at ha <;> simp_all
        subst hv
        exact ⟨.valueError "n must be at least one",
          by simp [bind, Except.bind, h1, throw, throwThe, MonadExceptOf.throw]⟩
    obtain ⟨e, he⟩ := hc
    simp [runAgree, he, docBatched, h1, Run.err]
  · have h2 : n ≤ ssizeMax := by
      simp only [tupleNewOk, ssizeMax_eq, mallocLimit_eq, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true,
        decide_eq_true_eq] at ht ⊢
      omega
    apply runAgree_of_eq
    simp only [cBatched, cBatchedNew, asSsize_ok (by rw [ssizeMin_eq]; omega) h2, docBatched, h1,
      ↓reduceIte, bind, Except.bind, pure, Except.pure]
    exact batchedLoop_eq n strict (by omega) h2 ht _ l hl

end PyLean.Itertools
