import PyLean.UnicodeObj.FormatPercent
import PyLean.UnicodeObj.FormatProps

/-!
Properties of `%`-formatting.
-/

namespace PyLean.UnicodeObj

open PyLean

theorem percentIntFastSlow_proven : PercentIntFastSlow := by
  intro v alt t base hb
  obtain ⟨hd, hm⟩ := digitsOf_spec base v.natAbs
  have hneg : ∀ n : Nat, ¬ ((-1 : Int) > n) := by intro n; omega
  have hbase : (if t == 111 then 8 else if t == 120 || t == 88 then 16 else 10) = base := by
    rcases hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  simp only [formatLongStr, hbase, longFormat, bind, Except.bind]
  generalize digitsOf base v.natAbs = ds at *
  obtain ⟨d, r, rfl⟩ : ∃ d r, ds = d :: r := by
    cases ds with
    | nil => exact absurd rfl hd
    | cons d r => exact ⟨d, r, rfl⟩
  have hd45 : (d == 45) = false := by simpa using hm d List.mem_cons_self
  by_cases hlim : 4300 < r.length + 1 <;>
    rcases hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    by_cases hv : v < 0 <;> cases alt <;> simp [hv, hd45, hneg, hlim]

theorem formatLoop_plain (fmtlen fuel : Nat) (s : Str) (ctx : FCtx) (out : Str)
    (hs : ∀ c ∈ s, c ≠ 37) (hf : s.length < fuel) :
    formatLoop fmtlen fuel s ctx out = .ok (out ++ s, ctx) := by
  induction fuel generalizing s out with
  | zero => omega
  | succ fuel ih =>
    cases s with
    | nil => simp [formatLoop]
    | cons c t =>
      have hc : (c != 37) = true := by simpa using hs c List.mem_cons_self
      simp only [List.length_cons] at hf
      simp only [formatLoop, hc, if_true]
      rw [ih t _ (fun x hx => hs x (List.mem_cons_of_mem _ hx)) (by omega)]
      simp

/-- A format with no `%` gives itself for an empty tuple, and raises `TypeError` for a
non-empty one. For every such format and every tuple. -/
def PercentNoDirective : Prop :=
  ∀ (fmt : Str) (items : List FObj), (∀ c ∈ fmt, c ≠ 37) →
    pyUnicodeFormat fmt (.tuple items) =
      if items = [] then .ok fmt
      else .error (.typeError "not all arguments converted during string formatting")

theorem percentNoDirective_proven : PercentNoDirective := by
  intro fmt items h
  simp only [pyUnicodeFormat, bind, Except.bind]
  rw [formatLoop_plain _ _ fmt _ [] h (by omega)]
  cases items with
  | nil => simp
  | cons x xs =>
    have : (0 : Int) < ((x :: xs).length : Int) := by simp
    simp [this]

end PyLean.UnicodeObj
