import PyLean.Pickle.DecC

/-!
`load_counted_long` (`Modules/_pickle.c:5703-5734`, `cLoadCountedLong`) at any position of an
unframed stream: the count read, the negative count, the empty payload and the truncated payload.
-/

namespace PyLean.Pickle

open PyLean

theorem cbind_ok {α β : Type} {m : CM α} {k : α → CM β} {s s' : CSt} {a : α} (h : m s = .ok (a, s')) :
    (m >>= k) s = k a s' := by
  show StateT.bind m k s = _
  simp only [StateT.bind, bind, Except.bind, h]

theorem cbind_err {α β : Type} {m : CM α} {k : α → CM β} {s : CSt} {e : PyExc} (h : m s = .error e) :
    (m >>= k) s = .error e := by
  show StateT.bind m k s = _
  simp only [StateT.bind, bind, Except.bind, h]

theorem cRead_ok {s : CSt} {n : Nat} (h : s.idx + n ≤ s.inputLen) :
    cRead n s = .ok ((s.inp.drop s.idx).take n, { s with idx := s.idx + n }) := by
  unfold cRead
  show (ite (s.idx + n ≤ s.inputLen) (_ : CM Bytes) _) s = _
  rw [if_pos h]
  rfl

theorem cRead_err {s : CSt} {n : Nat} (h : ¬ s.idx + n ≤ s.inputLen) (hf : s.frameEnd = none) :
    ∃ e, cRead n s = .error e := by
  unfold cRead
  show ∃ e, (ite (s.idx + n ≤ s.inputLen) (_ : CM Bytes) _) s = _
  rw [if_neg h]
  by_cases ho : s.idx > ssizeMaxN - n
  · exact ⟨_, by rw [if_pos ho]; rfl⟩
  · refine ⟨truncated, ?_⟩
    rw [if_neg ho]
    show (match s.frameEnd with
      | some fe => _
      | none => cThrow truncated) s = _
    rw [hf]
    rfl

/-- The count field at the reader's position. -/
def lcnt (nb : Nat) (s : CSt) : Int := calcBinint ((s.inp.drop s.idx).take nb)

/-- The reader moved on by `k` with `v` pushed. -/
def advPush (s : CSt) (k : Nat) (v : DV) : CSt := { s with idx := s.idx + k, stack := v :: s.stack }

/-- The reader moved on by `k` and then `m`, with `v` pushed. -/
def advPush2 (s : CSt) (k m : Nat) (v : DV) : CSt := { s with idx := s.idx + k + m, stack := v :: s.stack }

/-- At any position of an unframed stream, `LONG1` (`nb = 1`) and `LONG4` (`nb = 4`): too few
bytes for the count is an error; a negative count is "LONG pickle has negative byte count"; a
zero count pushes 0 after the count; too few bytes for the payload is an error; otherwise the
payload, read as a little-endian two's-complement int, is pushed and the reader is right after
it. The payload `save_long` writes is `encode_long(x)`, which this reads back as `x`
(`pickle-decode-encode-long`). -/
def CountedLongRead : Prop :=
  ∀ (nb : Nat) (s : CSt), s.frameEnd = none →
    (¬ s.idx + nb ≤ s.inputLen → ∃ e, cLoadCountedLong nb s = .error e) ∧
    (s.idx + nb ≤ s.inputLen → lcnt nb s < 0 →
      cLoadCountedLong nb s = .error (unpicklingError "LONG pickle has negative byte count")) ∧
    (s.idx + nb ≤ s.inputLen → lcnt nb s = 0 →
      cLoadCountedLong nb s = .ok ((), advPush s nb (.int 0))) ∧
    (s.idx + nb ≤ s.inputLen → 0 < lcnt nb s → ¬ s.idx + nb + (lcnt nb s).toNat ≤ s.inputLen →
      ∃ e, cLoadCountedLong nb s = .error e) ∧
    (s.idx + nb ≤ s.inputLen → 0 < lcnt nb s → s.idx + nb + (lcnt nb s).toNat ≤ s.inputLen →
      cLoadCountedLong nb s = .ok ((), advPush2 s nb (lcnt nb s).toNat
        (.int (decodeLong ((s.inp.drop (s.idx + nb)).take (lcnt nb s).toNat)))))

theorem countedLongRead_proven : CountedLongRead := by
  intro nb s hf
  unfold lcnt advPush advPush2
  have hk : cLoadCountedLong nb s = (cRead nb >>= fun b =>
        if calcBinint b < 0 then cThrow (unpicklingError "LONG pickle has negative byte count")
        else if calcBinint b = 0 then cPush (.int 0)
        else cRead (calcBinint b).toNat >>= fun b => cPush (.int (decodeLong b))) s := rfl
  refine ⟨fun h => ?_, fun h hn => ?_, fun h hz => ?_, fun h hp ht => ?_, fun h hp ht => ?_⟩
  · obtain ⟨e, he⟩ := cRead_err h hf
    exact ⟨e, hk.trans (cbind_err he)⟩
  · rw [hk, cbind_ok (cRead_ok h)]
    rw [if_pos hn]
    rfl
  · rw [hk, cbind_ok (cRead_ok h)]
    rw [if_neg (by omega), if_pos hz]
    rfl
  · rw [hk, cbind_ok (cRead_ok h)]
    rw [if_neg (by omega), if_neg (by omega)]
    obtain ⟨e, he⟩ := cRead_err (s := { s with idx := s.idx + nb })  ht hf
    exact ⟨e, cbind_err he⟩
  · rw [hk, cbind_ok (cRead_ok h)]
    rw [if_neg (by omega), if_neg (by omega)]
    rw [cbind_ok (cRead_ok (s := { s with idx := s.idx + nb })  ht)]
    rfl

end PyLean.Pickle
