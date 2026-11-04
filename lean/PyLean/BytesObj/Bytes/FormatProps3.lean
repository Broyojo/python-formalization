import PyLean.BytesObj.Bytes.FormatProps2
import PyLean.BytesObj.Bytes.Specs4

/-!
What `_PyBytes_FormatEx` writes on success: the conversions run through `bytes % args` end to
end, `getnextarg`'s tuple branch, the `*` width and precision, and the mapping key.
-/

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

/-! ## The writer below the memory limit -/

/-- The writer `PyBytesWriter_Grow` leaves, or the old one on failure. -/
def growTo (w : Writer) (g : Int) : Writer :=
  match writerGrow w g with
  | .ok w' => w'
  | .error _ => w

theorem writerResizeRaw_ba (w w' : Writer) (size : Int) (b : Bool)
    (h : writerResizeRaw w size b = .ok w') : w'.useBytearray = w.useBytearray := by
  unfold writerResizeRaw at h
  split at h
  · cases h; rfl
  · simp only at h
    split at h
    · cases h; rfl
    · cases h

theorem writerGrow_fields (w w' : Writer) (g : Int) (h : writerGrow w g = .ok w') :
    w'.size = w.size + g ∧ w'.useBytearray = w.useBytearray := by
  unfold writerGrow at h
  split at h
  · rename_i hg0
    cases h
    exact ⟨by omega, rfl⟩
  · split at h
    · cases h
    · split at h
      · cases h
      · simp only at h
        split at h
        · rename_i w1 hr
          cases h
          exact ⟨rfl, writerResizeRaw_ba w w1 _ _ hr⟩
        · cases h

theorem writerGrow_eq (w : Writer) (g : Int) (h0 : 0 ≤ w.size) (hg : 0 ≤ g) (hs : w.size + g < 2 ^ 46) :
    writerGrow w g = .ok (growTo w g) ∧ (growTo w g).size = w.size + g ∧
      (growTo w g).useBytearray = w.useBytearray := by
  obtain ⟨w', h⟩ := writerGrowth_proven.1 w g h0 hg hs
  have hf := writerGrow_fields _ _ _ h
  have e : growTo w g = w' := by simp [growTo, h]
  rw [e]
  exact ⟨h, hf⟩

theorem writerFinish_ok (w : Writer) (out : Seq) (hb : w.useBytearray = false)
    (h1 : (out.length : Int) ≤ w.size) (h2 : w.size < 2 ^ 46) : writerFinish w out = .ok out := by
  have hc : ∀ m : Int, 0 ≤ m → m < 2 ^ 46 → bytesSizeCheck m = .ok () :=
    fun m a b => bytesSizeCheck_ok m a (by omega)
  have hk : ¬ ((out.length : Int) < 0) := by omega
  have hg : ¬ ((out.length : Int) > w.size) := by omega
  have hcs := hc (out.length : Int) (by omega) (by omega)
  unfold writerFinish writerFinishSize
  rw [if_neg hk, if_neg hg]
  by_cases hz : (out.length : Int) = 0
  · simp [hz, hb]
  · have hz' : out ≠ [] := by intro e; simp [e] at hz
    rw [if_neg (by simp [hz'])]
    rcases hobj : w.obj with _ | ⟨n, a⟩
    · simp [hcs]
    · simp only [hb, Bool.false_eq_true, if_false]
      by_cases hn : (out.length : Int) = n
      · simp [hn]
      · rw [if_pos hn]
        unfold bytesResizeCheck
        rw [if_neg hk]
        simp only [hcs, ite_self]

/-- `writeField` below the memory limit: the field is written and the writer grows by
`alloc - 2`. -/
theorem writeField_eq (dict : Bool) (st : FS) (fl : Fl) (c : Int) (fill : Nat) (isNum : Bool)
    (width len : Int) (pbuf : Seq) (sign : Nat) (pbuf' : Seq) (len' : Int)
    (hss : signStep isNum fl pbuf len = (sign, pbuf', len'))
    (hd : ¬ (dict = true ∧ st.argidx < st.arglen)) (h0 : 0 ≤ st.w.size)
    (hs : st.w.size + fieldAlloc sign (if width < len' then len' else width) len' < 2 ^ 46) :
    writeField dict st fl c fill isNum width len pbuf =
      .ok { st with
        w := if fieldAlloc sign (if width < len' then len' else width) len' > 2 then
            growTo st.w (fieldAlloc sign (if width < len' then len' else width) len' - 2) else st.w,
        out := st.out ++ fieldWrites fl c fill sign (if width < len' then len' else width) len' pbuf' } := by
  unfold writeField
  simp only [hss]
  generalize hA : fieldAlloc sign (if width < len' then len' else width) len' = A at hs ⊢
  have hd' : ¬ (dict = true ∧ st.argidx < st.arglen) := hd
  simp only [bind, Except.bind, pure, Except.pure]
  by_cases hgt : A > 2
  · rw [if_pos hgt, (writerGrow_eq st.w _ h0 (by omega) (by omega)).1, if_pos hgt]
    try simp only
    rw [if_neg hd']
  · rw [if_neg hgt, if_neg hgt]
    try simp only
    rw [if_neg hd']

/-- The writer after the `alloc - 2` growth of a field. -/
def growIf (w : Writer) (A : Int) : Writer := if A > 2 then growTo w (A - 2) else w

theorem growTo_ba (w : Writer) (g : Int) : (growTo w g).useBytearray = w.useBytearray := by
  unfold growTo
  split
  · rename_i w' h
    exact (writerGrow_fields _ _ _ h).2
  · rfl

@[simp] theorem growIf_ba (w : Writer) (A : Int) : (growIf w A).useBytearray = w.useBytearray := by
  unfold growIf
  split
  · exact growTo_ba _ _
  · rfl

theorem growIf_size (w : Writer) (A : Int) (h0 : 0 ≤ w.size) (hs : w.size + A < 2 ^ 46) :
    (growIf w A).size = w.size + (if A > 2 then A - 2 else 0) := by
  unfold growIf
  by_cases h : A > 2
  · rw [if_pos h, if_pos h]
    exact (writerGrow_eq w (A - 2) h0 (by omega) (by omega)).2.1
  · rw [if_neg h, if_neg h]
    omega

/-- `writeField_eq` with the sign step left as it is, for rewriting. -/
theorem writeField_eq' (dict : Bool) (st : FS) (fl : Fl) (c : Int) (fill : Nat) (isNum : Bool)
    (width len : Int) (pbuf : Seq)
    (hd : ¬ (dict = true ∧ st.argidx < st.arglen)) (h0 : 0 ≤ st.w.size)
    (hs : st.w.size + fieldAlloc (signStep isNum fl pbuf len).1
      (if width < (signStep isNum fl pbuf len).2.2 then (signStep isNum fl pbuf len).2.2 else width)
      (signStep isNum fl pbuf len).2.2 < 2 ^ 46) :
    writeField dict st fl c fill isNum width len pbuf =
      let sg := signStep isNum fl pbuf len
      let width' := if width < sg.2.2 then sg.2.2 else width
      .ok { st with
        w := growIf st.w (fieldAlloc sg.1 width' sg.2.2),
        out := st.out ++ fieldWrites fl c fill sg.1 width' sg.2.2 sg.2.1 } :=
  writeField_eq dict st fl c fill isNum width len pbuf _ _ _ rfl hd h0 hs

theorem growIf_fields (w : Writer) (A : Int) (h0 : 0 ≤ w.size) (hs : w.size + A < 2 ^ 46) :
    (if A > 2 then growTo w (A - 2) else w).size = w.size + (if A > 2 then A - 2 else 0) ∧
    (if A > 2 then growTo w (A - 2) else w).useBytearray = w.useBytearray := by
  by_cases h : A > 2
  · have := writerGrow_eq w (A - 2) h0 (by omega) (by omega)
    simp only [if_pos h]
    exact ⟨this.2.1, this.2.2⟩
  · simp only [if_neg h]
    exact ⟨by omega, trivial⟩

/-- The plain field: no flag, the width at most the length. -/
theorem fieldWrites_self (c : Int) (t : Seq) (hc : hasPrefix {} c = false) :
    fieldWrites {} c 32 0 t.length t.length t = t := by
  simp [fieldWrites, hc]

/-! ## The arguments `%b` and `%s` take -/

/-- What `%b` and `%s` accept, as the documentation lists it: bytes, bytearray, an object
whose `__bytes__` returns bytes, and a buffer. -/
def bytesLikeArg : Obj → Option Seq
  | .bytes s | .bytearray s | .memview s _ => some s
  | .dunder (.bytes s) => some s
  | _ => none

theorem formatObj_of_bytesLike (x : Obj) (s : Seq) (h : bytesLikeArg x = some s) :
    ∀ st, formatObj st x = .ok s := by
  intro st
  cases x <;> simp [bytesLikeArg] at h
  all_goals first
    | (subst h; simp [formatObj, Obj.buffer?])
    | skip
  rename_i r
  cases r <;> simp at h
  subst h
  simp [formatObj]

theorem intRepr_len (v : Int) (t : Seq) (h : intRepr v = .ok t) : t.length ≤ 4301 := by
  unfold intRepr Fractions.strInt at h
  by_cases hd : Fractions.numDigits v.natAbs > Fractions.maxStrDigits
  · simp [hd, bind, Except.bind] at h
  · simp only [hd, if_false, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp only [Fractions.numDigits, Fractions.maxStrDigits] at hd
    by_cases hv : v < 0 <;> simp [hv] <;> omega


theorem writerFinish_growIf (w : Writer) (A : Int) (out : Seq) (hb : w.useBytearray = false)
    (h0 : 0 ≤ w.size) (hA : 0 ≤ A) (hs : w.size + A < 2 ^ 46)
    (hl : (out.length : Int) ≤ w.size + (if A > 2 then A - 2 else 0)) :
    writerFinish (growIf w A) out = .ok out := by
  have g := growIf_size w A h0 hs
  refine writerFinish_ok _ _ (by simp [hb]) (by rw [g]; exact hl) ?_
  rw [g]
  split <;> omega

end PyLean.BytesObj.Bytes
