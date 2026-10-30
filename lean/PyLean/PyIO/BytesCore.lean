import PyLean.PyIO.Lines
import PyLean.PyIO.BytesTwins

/-!
The proven core of the BytesIO twin agreement: with arguments in C range,
no exported views, no allocation failure and no `readline(0)` on a closed
stream, `io.BytesIO` and `_pyio.BytesIO` agree on every value and exception
class. The proof is a simulation: both twins keep the same buffer, position
and closed flag after every operation.
-/

namespace PyLean.PyIO

open PyLean

/-! ## `readlines` -/

/-- `readlines` from `pos` with `size` bytes already returned: the final
position and the lines (`maxsize > 0` is the hint). -/
def rlSpec (buf : List Nat) (maxsize : Int) : Nat → Nat → Nat → Nat × List Atom
  | 0, pos, _ => (pos, [])
  | f + 1, pos, size =>
    let k := lineLen (buf.drop pos)
    if k = 0 then (pos, []) else
    if maxsize > 0 ∧ ((size + k : Nat) : Int) ≥ maxsize then (pos + k, [.bytes (slice buf pos k)])
    else
      let r := rlSpec buf maxsize f (pos + k) (size + k)
      (r.1, .bytes (slice buf pos k) :: r.2)

theorem rlSpec_fuel (buf : List Nat) (m : Int) : ∀ f₁ f₂ pos size,
    buf.length - pos < f₁ → buf.length - pos < f₂ → rlSpec buf m f₁ pos size = rlSpec buf m f₂ pos size := by
  intro f₁
  induction f₁ with
  | zero => intros; omega
  | succ f ih =>
    intro f₂ pos size h₁ h₂
    cases f₂ with
    | zero => omega
    | succ g =>
      simp only [rlSpec]
      split
      · rfl
      · next hk =>
        split
        · rfl
        · have hpos : pos < buf.length := by
            refine Nat.lt_of_not_le (fun hc => hk ?_)
            rw [List.drop_eq_nil_of_le hc]; rfl
          have hk1 : 0 < lineLen (buf.drop pos) := by omega
          have hk2 : lineLen (buf.drop pos) ≤ buf.length - pos := by
            have := lineLen_le (buf.drop pos); simp at this; omega
          rw [ih g (pos + lineLen (buf.drop pos)) (size + lineLen (buf.drop pos)) (by omega) (by omega)]

theorem scanEol_all (s : BState) : C.scanEol s (-1) = lineLen (s.buf.drop s.pos) := by
  rw [scanEol_eq]
  simp only [show (-1 : Int) < 0 by decide, ite_true]
  rw [List.take_of_length_le (by simp)]

theorem C_readlinesLoop (maxsize : Int) : ∀ fuel (s : BState) (size : Nat) (acc : List Atom),
    C.readlinesLoop maxsize s size acc fuel =
      ({ s with pos := (rlSpec s.buf maxsize fuel s.pos size).1 },
       .ok (.list (acc.reverse ++ (rlSpec s.buf maxsize fuel s.pos size).2))) := by
  intro fuel
  induction fuel with
  | zero => intro s size acc; simp [C.readlinesLoop, rlSpec]
  | succ f ih =>
    intro s size acc
    simp only [C.readlinesLoop, rlSpec, scanEol_all]
    split
    · simp
    · split
      · simp
      · rw [ih]; simp

theorem P_readlinesLoop (hint : Option Int) (maxsize : Int)
    (hm : (hint = none ∧ maxsize ≤ 0) ∨ (hint = some maxsize ∧ maxsize > 0)) :
    ∀ fuel (s : BState) (n : Nat) (acc : List Atom), s.closed = false → s.buf.length - s.pos < fuel →
    P.readlinesLoop hint s n acc fuel =
      ({ s with pos := (rlSpec s.buf maxsize fuel s.pos n).1 },
       .ok (.list (acc.reverse ++ (rlSpec s.buf maxsize fuel s.pos n).2))) := by
  intro fuel
  induction fuel with
  | zero => intros; omega
  | succ f ih =>
    intro s n acc hc hf
    simp only [P.readlinesLoop, rlSpec]
    rw [readlineRaw_eq s none hc]
    simp only [Option.getD_none, scanEol_all]
    have hle := lineLen_le (s.buf.drop s.pos)
    have hsl : slice s.buf s.pos (lineLen (s.buf.drop s.pos)) = [] ↔ lineLen (s.buf.drop s.pos) = 0 :=
      slice_eq_nil _ _ _ hle
    by_cases hk : lineLen (s.buf.drop s.pos) = 0
    · have : slice s.buf s.pos (lineLen (s.buf.drop s.pos)) = [] := hsl.mpr hk
      simp [hk, slice]
    · have : slice s.buf s.pos (lineLen (s.buf.drop s.pos)) ≠ [] := fun h => hk (hsl.mp h)
      simp only [this, ite_false, hk]
      have hlen : (slice s.buf s.pos (lineLen (s.buf.drop s.pos))).length = lineLen (s.buf.drop s.pos) :=
        slice_length _ _ _ hle
      have hpos : s.pos < s.buf.length := by
        refine Nat.lt_of_not_le (fun hc' => hk ?_)
        rw [List.drop_eq_nil_of_le hc']; rfl
      have hk1 : lineLen (s.buf.drop s.pos) ≤ s.buf.length - s.pos := by simp at hle; omega
      rcases hm with ⟨rfl, hm⟩ | ⟨rfl, hm⟩
      · have : ¬ (maxsize > 0 ∧ (((n + lineLen (s.buf.drop s.pos)) : Nat) : Int) ≥ maxsize) := by omega
        simp only [this, ite_false]
        rw [hlen, ← Int.natCast_add,
          ih { s with pos := s.pos + lineLen (s.buf.drop s.pos) } _ _ hc
            (by show s.buf.length - (s.pos + lineLen (s.buf.drop s.pos)) < f; omega)]
        simp
      · rw [hlen]
        by_cases hb : (((n + lineLen (s.buf.drop s.pos)) : Nat) : Int) ≥ maxsize
        · have h1 : maxsize > 0 ∧ (((n + lineLen (s.buf.drop s.pos)) : Nat) : Int) ≥ maxsize := ⟨hm, hb⟩
          have h2 : ((n : Int) + (lineLen (s.buf.drop s.pos) : Nat)) ≥ maxsize := by omega
          simp only [h1, h2, and_self, ite_true]
          simp
        · have h1 : ¬ (maxsize > 0 ∧ (((n + lineLen (s.buf.drop s.pos)) : Nat) : Int) ≥ maxsize) := by omega
          have h2 : ¬ ((n : Int) + (lineLen (s.buf.drop s.pos) : Nat)) ≥ maxsize := by omega
          simp only [h1, h2, ite_false]
          rw [← Int.natCast_add, ih { s with pos := s.pos + lineLen (s.buf.drop s.pos) } _ _ hc
            (by show s.buf.length - (s.pos + lineLen (s.buf.drop s.pos)) < f; omega)]
          simp

end PyLean.PyIO
