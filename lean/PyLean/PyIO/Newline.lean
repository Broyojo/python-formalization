import PyLean.PyIO.Text

/-!
`IncrementalNewlineDecoder` as a Python-visible class: the C implementation
(`_PyIncrementalNewlineDecoder_decode`, `Modules/_io/textio.c:248-663`) and the
Python twin (`Lib/_pyio.py:1948-2031`). The wrapped decoder is `None` (the input
is text) or the UTF-8 decoder with buffer `ubuf` (the input is bytes).
-/

namespace PyLean.PyIO

open PyLean

structure NDec where
  /-- `none`: `decoder is None`; `some b`: incremental UTF-8 with buffer `b`. -/
  inner : Option (List Nat)
  translate : Bool
  pendingcr : Bool
  seennl : NlKinds
  deriving Repr, DecidableEq, Inhabited

def NDec.fresh (inner : Option (List Nat)) (translate : Bool) : NDec :=
  ⟨inner, translate, false, ⟨false, false, false⟩⟩

/-- The wrapped decoder's step, shared by both twins (`check_decoded`,
textio.c:301-313, cannot fail for these two decoders). -/
def NDec.inputStep (d : NDec) (input : List Nat) (final : Bool) : Py (NDec × List Nat) :=
  match d.inner with
  | none => .ok (d, input)
  | some b =>
    match utf8Dec final (b ++ input) with
    | .error e => .error e
    | .ok (out, rest) => .ok ({ d with inner := some rest }, out)

/-- `self.pendingcr and (output or final)`, then keeping a final `\r` back:
textio.c:350-384, _pyio.py:1968-1977. -/
def NDec.pendStep (d : NDec) (out : List Nat) (final : Bool) : NDec × List Nat :=
  let (d, out) := if d.pendingcr && (final || !out.isEmpty) then
      ({ d with pendingcr := false }, 13 :: out) else (d, out)
  if !final && out.getLast? == some 13 then ({ d with pendingcr := true }, out.dropLast)
  else (d, out)

namespace NC

def allSeen : NlKinds := ⟨true, true, true⟩

/-- The scan for `translate == 0`, textio.c:433-460 (stops once all three kinds
are seen). -/
def scan : List Nat → NlKinds → NlKinds
  | [], s => s
  | 10 :: r, s =>
    let s := s.union ⟨false, true, false⟩
    if s = allSeen then s else scan r s
  | 13 :: 10 :: r, s =>
    let s := s.union ⟨false, false, true⟩
    if s = allSeen then s else scan r s
  | 13 :: r, s =>
    let s := s.union ⟨true, false, false⟩
    if s = allSeen then s else scan r s
  | _ :: r, s => if s = allSeen then s else scan r s

/-- The translating loop, textio.c:470-508. -/
def transl : List Nat → NlKinds → List Nat × NlKinds
  | [], s => ([], s)
  | 10 :: r, s =>
    let (o, s') := transl r (s.union ⟨false, true, false⟩)
    (10 :: o, s')
  | 13 :: 10 :: r, s =>
    let (o, s') := transl r (s.union ⟨false, false, true⟩)
    (10 :: o, s')
  | 13 :: r, s =>
    let (o, s') := transl r (s.union ⟨true, false, false⟩)
    (10 :: o, s')
  | c :: r, s =>
    let (o, s') := transl r s
    (c :: o, s')

/-- The bookkeeping of `_PyIncrementalNewlineDecoder_decode`, textio.c:386-513. -/
def record (d : NDec) (out : List Nat) : NDec × List Nat :=
  if out = [] then (d, out) else
  let seennl := d.seennl
  let lfOnly : NlKinds := ⟨false, true, false⟩
  let noneSeen : NlKinds := ⟨false, false, false⟩
  let onlyLf := (seennl = lfOnly ∨ seennl = noneSeen) ∧ !out.contains 13
  if onlyLf then
    if seennl = noneSeen ∧ out.contains 10 then ({ d with seennl := seennl.union lfOnly }, out) else (d, out)
  else if !d.translate then
    if seennl = allSeen then (d, out) else ({ d with seennl := scan out seennl }, out)
  else
    let (o, s) := transl out seennl
    ({ d with seennl := s }, o)

/-- `_PyIncrementalNewlineDecoder_decode`, textio.c:328-519. -/
def decode (d : NDec) (input : List Nat) (final : Bool) : Py (NDec × List Nat) :=
  match d.inputStep input final with
  | .error e => .error e
  | .ok (d, out) =>
    let (d, out) := d.pendStep out final
    .ok (record d out)

end NC

namespace NP

/-- `IncrementalNewlineDecoder.decode`, _pyio.py:1962-1991: `count`, then
`replace`, which `nlKinds` and `translateNl` compute. -/
def decode (d : NDec) (input : List Nat) (final : Bool) : Py (NDec × List Nat) :=
  match d.inputStep input final with
  | .error e => .error e
  | .ok (d, out) =>
    let (d, out) := d.pendStep out final
    let d := { d with seennl := d.seennl.union (nlKinds out) }
    .ok (d, if d.translate then translateNl out else out)

end NP

/-- `getstate()`: textio.c:542-578, _pyio.py:1993-2002. -/
def NDec.getstate (d : NDec) : List Nat × Nat :=
  (d.inner.getD [], if d.pendingcr then 1 else 0)

/-- `setstate((buf, flag))`: textio.c:588-617, _pyio.py:2004-2008 (the low bit is
`pendingcr`; `flag >> 1` goes to the wrapped decoder, which ignores it). -/
def NDec.setstate (d : NDec) (buf : List Nat) (flag : Int) : NDec :=
  { d with pendingcr := flag % 2 = 1, inner := d.inner.map (fun _ => buf) }

/-- `reset()`: textio.c:625-636, _pyio.py:2010-2014. -/
def NDec.reset (d : NDec) : NDec :=
  { d with pendingcr := false, seennl := ⟨false, false, false⟩, inner := d.inner.map (fun _ => []) }

end PyLean.PyIO
