import PyLean.TextLibs.TomlModel

/-!
`TOMLDecodeError.__init__`, _parser.py:89-136: the line and column it reports.
-/

namespace PyLean.TextLibs.Toml

theorem firstIdx_eq_count (m : Str) :
    firstIdx (· == 10) m = if m.count 10 = 0 then none else some (m.takeWhile (· != 10)).length := by
  induction m with
  | nil => simp [firstIdx]
  | cons c r ih =>
    by_cases h : c = 10
    · subst h; simp [firstIdx]
    · have h' : (c == 10) = false := by simp [h]
      simp only [firstIdx, h', ih, List.count_cons, List.takeWhile_cons, bne_iff_ne, ne_eq,
        Bool.false_eq_true, ite_false]
      simp [h]
      split <;> simp

theorem takeWhile_length_le (p : Nat → Bool) (m : Str) : (m.takeWhile p).length ≤ m.length := by
  induction m with
  | nil => simp
  | cons c r ih =>
    simp only [List.takeWhile_cons]
    split <;> simp <;> omega

theorem takeWhile_lt_of_count (m : Str) (h : m.count 10 ≠ 0) :
    (m.takeWhile (· != 10)).length < m.length := by
  induction m with
  | nil => simp at h
  | cons c r ih =>
    by_cases hc : c = 10
    · subst hc; simp
    · have : r.count 10 ≠ 0 := by simpa [List.count_cons, hc] using h
      simp [hc]
      exact ih this

theorem takeWhile_all_of_count (m : Str) (h : m.count 10 = 0) :
    (m.takeWhile (· != 10)).length = m.length := by
  induction m with
  | nil => simp
  | cons c r ih =>
    by_cases hc : c = 10
    · subst hc; simp at h
    · have : r.count 10 = 0 := by simpa [List.count_cons, hc] using h
      simp [hc, ih this]

/-- The column `colno` should be: one more than the number of characters since the last
newline before `pos`. -/
def colSpec (doc : Str) (pos : Nat) : Nat := ((doc.take pos).reverse.takeWhile (· != 10)).length + 1

/-- The line `lineno` should be: one more than the number of newlines before `pos`. -/
def lineSpec (doc : Str) (pos : Nat) : Nat := (doc.take pos).count 10 + 1

def coordSpec (doc : Str) (pos : Nat) : Str :=
  if pos = doc.length then S "end of document"
  else S s!"line {lineSpec doc pos}, column {(colSpec doc pos : Int)}"

/-- The non-default arguments among `msg`, `doc`, `pos`, in order. -/
def nonDefault : List EArg → List EArg
  | [] => []
  | .dflt :: r => nonDefault r
  | a :: r => a :: nonDefault r

/-- The attributes `TdeCoords` promises. -/
def tdeSpec (msg doc : Str) (pos : Nat) : TdeFull :=
  { errmsg := msg ++ S " (at " ++ coordSpec doc pos ++ S ")", msg, doc, pos,
    lineno := lineSpec doc pos, colno := colSpec doc pos }

/-- `TOMLDecodeError(msg, doc, pos)` with `str` msg and doc and an `int` pos: (1) for every
`0 ≤ pos ≤ len(doc)` it sets `lineno` and `colno` to the line and column of `pos` (1-based,
counted from the last newline before `pos`), and the message is `msg (at line L, column C)`, or
`msg (at end of document)` when `pos == len(doc)`; (2) for every `int` pos, also outside the
document, it does not raise; (3) any other call (extra positional arguments, or a `msg`, `doc`
or `pos` of another type, or missing) warns, and then calls `ValueError.__init__` with the given
arguments in order, or raises the `DeprecationWarning` when warnings are errors. -/
def TdeCoords : Prop :=
  (∀ (warnErr : Bool) (msg doc : Str) (pos : Nat), pos ≤ doc.length →
    tdeInit warnErr (.str msg) (.str doc) (.int pos) [] = .ok (.full (tdeSpec msg doc pos))) ∧
  (∀ (warnErr : Bool) (msg doc : Str) (pos : Int),
    ∃ r, tdeInit warnErr (.str msg) (.str doc) (.int pos) [] = .ok (.full r)) ∧
  (∀ (warnErr : Bool) (msg doc pos : EArg) (args : List EArg),
    ¬ (args = [] ∧ msg.isStr ∧ doc.isStr ∧ pos.isInt) →
    tdeInit warnErr msg doc pos args =
      if warnErr then .error (.named "DeprecationWarning" warnMsg)
      else .ok (.legacy (nonDefault [msg, doc, pos] ++ args)))

theorem sliceEnd_nat (p len : Nat) (h : p ≤ len) : sliceEnd (p : Int) len = p := by
  unfold sliceEnd
  simp only [show ¬ ((p : Int) < 0) by omega, ite_false]
  simp; omega

theorem tdeFull_nat (msg doc : Str) (pos : Nat) (hpos : pos ≤ doc.length) :
    tdeFull msg doc pos = .ok (tdeSpec msg doc pos) := by
  have hlen : (doc.take pos).length = pos := by simp; omega
  unfold tdeFull
  rw [sliceEnd_nat _ _ hpos]
  by_cases hc : (doc.take pos).count 10 = 0
  · have ht := takeWhile_all_of_count (doc.take pos).reverse (by simpa using hc)
    simp only [List.length_reverse, hlen] at ht
    have hcs : colSpec doc pos = pos + 1 := by simp [colSpec, ht]
    have hls : lineSpec doc pos = 1 := by simp [lineSpec, hc]
    by_cases he : pos = doc.length
    · have hle : doc.length ≤ pos := by omega
      simp only [tdeSpec, coordSpec, if_pos he]
      simp [hc, hcs, hls, hle, bind, Except.bind, pure, Except.pure]
    · have hle : ¬ doc.length ≤ pos := by omega
      simp only [tdeSpec, coordSpec, if_neg he]
      simp [hc, hcs, hls, hle, bind, Except.bind, pure, Except.pure]
  · have hcr : (doc.take pos).reverse.count 10 ≠ 0 := by simpa using hc
    have hlt := takeWhile_lt_of_count _ hcr
    simp only [List.length_reverse, hlen] at hlt
    generalize ht : ((doc.take pos).reverse.takeWhile (· != 10)).length = t at hlt
    have hl : lastIdx 10 (doc.take pos) = some (pos - 1 - t) := by
      simp only [lastIdx, firstIdx_eq_count, List.count_reverse, if_neg hc, List.length_reverse, hlen,
        ht, Option.map]
    have hcs : colSpec doc pos = t + 1 := by simp [colSpec, ht]
    have hcol : ((pos : Int) - ((pos - 1 - t : Nat) : Int)) = ((t + 1 : Nat) : Int) := by omega
    have h1 : ((doc.take pos).count 10 + 1 == 1) = false := by simp; omega
    simp only [hl, h1, Bool.false_eq_true, ite_false, bind, Except.bind, pure, Except.pure]
    rw [hcol]
    by_cases he : pos = doc.length
    · have hle : doc.length ≤ pos := by omega
      simp only [tdeSpec, coordSpec, if_pos he]
      simp [hcs, hle, lineSpec]
    · have hle : ¬ doc.length ≤ pos := by omega
      simp only [tdeSpec, coordSpec, if_neg he]
      simp [hcs, hle, lineSpec]

@[simp] theorem bne_dflt_str (s : Str) : (EArg.str s != EArg.dflt) = true := rfl
@[simp] theorem bne_dflt_int (i : Int) : (EArg.int i != EArg.dflt) = true := rfl
@[simp] theorem bne_dflt_obj (s : Str) : (EArg.obj s != EArg.dflt) = true := rfl
@[simp] theorem bne_dflt_dflt : (EArg.dflt != EArg.dflt) = false := rfl

theorem tdeCoords_proven : TdeCoords := by
  refine ⟨?_, ?_, ?_⟩
  · intro warnErr msg doc pos hpos
    simp [tdeInit, tdeFull_nat msg doc pos hpos, Except.map]
  · intro warnErr msg doc pos
    unfold tdeInit tdeFull
    simp only [bind, Except.bind]
    generalize hl : doc.take (sliceEnd pos doc.length) = l
    by_cases h1 : (l.count 10 + 1 == 1) = true
    · simp only [h1, ite_true]; exact ⟨_, rfl⟩
    · have : l.reverse.count 10 ≠ 0 := by simp at h1 ⊢; omega
      have hi : lastIdx 10 l = some (l.length - 1 - (l.reverse.takeWhile (· != 10)).length) := by
        simp only [lastIdx, firstIdx_eq_count, if_neg this, List.length_reverse]; rfl
      simp only [h1, Bool.false_eq_true, ite_false, hi]; exact ⟨_, rfl⟩
  · intro warnErr msg doc pos args h
    unfold tdeInit
    split
    · simp_all [EArg.isStr, EArg.isInt]
    · cases warnErr
      · cases msg <;> cases doc <;> cases pos <;> simp [nonDefault]
      · rfl

end PyLean.TextLibs.Toml
