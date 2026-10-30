import PyLean.PyIO.Spec

/-!
`readlines(hint)`: "hint can be specified to control the number of lines
read: no more lines will be read if the total size (in bytes/characters) of
all lines so far exceeds hint" (`IOBase.readlines`, Doc/library/io.rst).
The C `_io._IOBase.readlines` (used by `io.StringIO`) follows this; the C
`BytesIO.readlines` and the `_pyio` `IOBase.readlines` stop one line early,
as soon as the total *reaches* `hint`.
-/

namespace PyLean.PyIO

open PyLean

def atomLen : Atom → Nat
  | .str l => l.length
  | .bytes b => b.length
  | _ => 0

/-- The documented selection: whole lines until the running total (starting
at `acc`) exceeds `h`. -/
def docPrefix (h : Int) : List Atom → Int → List Atom
  | [], _ => []
  | l :: ls, acc => if acc + atomLen l > h then [l] else l :: docPrefix h ls (acc + atomLen l)

/-- `readlines(hint)` for `hint > 0` returns the documented prefix of
`readlines()`, for every open BytesIO (both twins). -/
def BytesIOReadlinesHintDoc : Prop :=
  ∀ (init : List Nat) (h : Int) (L : List Atom), 0 < h → InSsize h →
    (C.readlines (bInit init) none).2 = .ok (.list L) →
    (C.readlines (bInit init) (some h)).2 = .ok (.list (docPrefix h L 0)) ∧
    (P.readlines (bInit init) (some h)).2 = .ok (.list (docPrefix h L 0))

/-- `BytesIO(b'a\nb\nc').readlines(2)` returns `[b'a\n']` in both twins; the
documented result (the total 2 does not exceed 2) is `[b'a\n', b'b\n']`,
which is what `io.StringIO('a\nb\nc').readlines(2)` returns. -/
theorem bytesIOReadlinesHintDoc_refuted : ¬BytesIOReadlinesHintDoc := by
  intro hp
  have := (hp [97, 10, 98, 10, 99] 2 [.bytes [97, 10], .bytes [98, 10], .bytes [99]] (by decide) (by decide)
    (by decide)).1
  revert this
  decide

/-- Every line `next()` returns, without accumulators: the reference list
`readlines()` returns. -/
def scLines : SCState → Nat → Py (List Atom)
  | _, 0 => .error .modelFuel
  | s, f + 1 =>
    match SC.next s with
    | (_, .error .stopIteration) => .ok []
    | (_, .error e) => .error e
    | (s', .ok v) =>
      let line := v.strOf
      (scLines s' f).map (Atom.str line :: ·)

theorem readlinesLoop_none (len : Int) : ∀ (f : Nat) (s : SCState) (acc : List Atom),
    (SC.readlinesLoop (-1) s len acc f).2 = (scLines s f).map (fun L => .list (acc.reverse ++ L)) := by
  intro f
  induction f generalizing len with
  | zero => intro s acc; simp [SC.readlinesLoop, scLines, Except.map]
  | succ f ih =>
    intro s acc
    simp only [SC.readlinesLoop, scLines]
    rcases hn : SC.next s with ⟨s', r⟩
    cases r with
    | error e =>
      cases e <;> simp [Except.map]
    | ok v =>
      simp only [show ¬ ((-1 : Int) > 0) by decide, false_and, ite_false]
      rw [ih]
      cases hL : scLines s' f <;> simp [Except.map]

theorem readlinesLoop_hint (h : Int) (hh : 0 < h) : ∀ (f : Nat) (s : SCState) (len : Int) (acc L : List Atom),
    scLines s f = .ok L →
    (SC.readlinesLoop h s len acc f).2 = .ok (.list (acc.reverse ++ docPrefix h L len)) := by
  intro f
  induction f with
  | zero => intro s len acc L hL; simp [scLines] at hL
  | succ f ih =>
    intro s len acc L hL
    simp only [scLines] at hL
    simp only [SC.readlinesLoop]
    rcases hn : SC.next s with ⟨s', r⟩
    rw [hn] at hL
    cases r with
    | error e =>
      cases e <;> simp at hL
      subst hL; simp [docPrefix]
    | ok v =>
      simp only at hL ⊢
      cases hL' : scLines s' f with
      | error e => rw [hL'] at hL; simp [Except.map] at hL
      | ok L' =>
        rw [hL'] at hL
        simp [Except.map] at hL
        subst hL
        generalize v.strOf = line
        simp only [docPrefix, atomLen]
        by_cases hb : (line.length : Int) > h - len
        · have : len + (line.length : Int) > h := by omega
          simp [hh, hb, this]
        · have : ¬ (len + (line.length : Int) > h) := by omega
          have hb' : ¬ (h > 0 ∧ (line.length : Int) > h - len) := fun h' => hb h'.2
          rw [if_neg hb', ih s' (len + line.length) _ L' hL']
          simp [this]

/-- For every open C `StringIO` and every `hint > 0`, `readlines(hint)`
returns the documented prefix of what `readlines()` returns. -/
def CStringIOReadlinesHintDoc : Prop :=
  ∀ (s : SCState) (h : Int) (L : List Atom), s.closed = false → 0 < h → InSsize h →
    (SC.readlines s none).2 = .ok (.list L) →
    (SC.readlines s (some h)).2 = .ok (.list (docPrefix h L 0))

theorem cStringIOReadlinesHintDoc_proven : CStringIOReadlinesHintDoc := by
  intro s h L hc hh hr hL
  simp only [SC.readlines, optSsize, Option.getD_none, hc, Bool.false_eq_true, ite_false] at hL ⊢
  simp only [hr, ite_true]
  rw [readlinesLoop_none] at hL
  cases hs : scLines s (s.buf.length - s.pos + 2) with
  | error e => rw [hs] at hL; simp [Except.map] at hL
  | ok L' =>
    rw [hs] at hL
    simp [Except.map] at hL
    subst hL
    rw [readlinesLoop_hint h hh _ s 0 [] L' hs]
    simp

end PyLean.PyIO
