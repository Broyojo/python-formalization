import PyLean.PyIO.TextOps

/-!
`io.TextIOWrapper.tell()` after `next()` and `flush()` (`Modules/_io/textio.c`, CPython
3.15.2). `next()` clears `telling` (textio.c:3283-3320), so `read_chunk` stops updating
the snapshot (:1957, :2036), and `flush()` sets `telling` again; `tell()` then
reconstructs the position from the old snapshot and the new `b2cratio`
(:2949), with `skip_bytes` bounded only by an `assert` (:2951).
-/

namespace PyLean.PyIO

open PyLean

/-- `io.TextIOWrapper(io.BytesIO(data), encoding='utf-8')` with the default newline. -/
def tiowUtf8 (data : List Nat) : Py TC :=
  TCm.init data .utf8 ("utf-8".toList.map Char.toNat) ("strict".toList.map Char.toNat) false none false false 8192

/-- `f.seek(f.tell()); next(f); f.flush(); f.tell()` returns a position no greater than
the length of the stream (or raises): a position is an offset into the stream. -/
def tellAfterNextInRange (data : List Nat) : Bool :=
  match tiowUtf8 data with
  | .error _ => true
  | .ok t =>
    match (runOps TCm.stepOp t [.seekTell, .next, .flush, .tell]).2.getLast? with
    | some (.ok (.int v)) => decide (v ≤ data.length)
    | _ => true

def TextCTellAfterNextInRange : Prop := ∀ data : List Nat, tellAfterNextInRange data = true

/-- `b'\nb\xe2\x82\xac'` (5 bytes): `seek(tell())` leaves the snapshot `(0, b'')`; `next()`
reads the whole chunk without updating it and returns `'\n'`; `flush()` re-enables
`tell()`, which computes `skip_bytes = int(5/3 * 1) = 1` bytes of the empty snapshot,
decodes the `bytes` object's terminating NUL as one character, and returns 6. -/
theorem textCTellAfterNextInRange_refuted : ¬TextCTellAfterNextInRange := by
  intro h
  have := h [10, 98, 226, 130, 172]
  revert this
  decide +kernel

end PyLean.PyIO
