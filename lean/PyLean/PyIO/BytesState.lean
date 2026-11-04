import PyLean.PyIO.BytesExtra

/-!
`io.BytesIO`'s pickling with Python objects as the state (`Modules/_io/bytesio.c`,
CPython 3.15.2): `bytesio_getstate_lock_held` (:909-935) returns
`(getvalue(), pos, copy of self->dict or None)`, and `bytesio_setstate_lock_held`
(:948-1023) checks the state's shape, resets the stream, writes `state[0]`, then checks
and sets the position, then checks and merges the dict, so a bad later item leaves the
earlier ones applied.

The instance dict `self->dict` is `NULL` until an attribute is set or `__dict__` is read
(`PyObject_GenericGetDict` creates it); here its values are ints. `self->dict = dict`
(:1018) stores the caller's dict object itself; the model keeps its contents (the harness
does not keep that dict). Scope: an exact `io.BytesIO` (`Py_TYPE(self)->tp_name` is
`_io.BytesIO` in the first message). `_pyio.BytesIO`'s state is its instance dict, with no
checks (`PyIO/BytesExtra.lean`).
-/

namespace PyLean.PyIO

open PyLean

/-- An item of a `__setstate__` state. -/
inductive SItem where
  | bytes (d : List Nat)
  | bytearray (d : List Nat)
  | int (v : Int)
  | bool (b : Bool)
  | none
  | dict (kv : List (String × Int))
  /-- Any other object, by type name (`str`, `float`, `list`). -/
  | other (typeName : String)
  deriving Repr, DecidableEq, Inhabited

def SItem.typeName : SItem → String
  | .bytes _ => "bytes" | .bytearray _ => "bytearray" | .int _ => "int" | .bool _ => "bool"
  | .none => "NoneType" | .dict _ => "dict" | .other t => t

/-- The argument of `__setstate__`: a tuple, or an object of another type. -/
inductive SArg where
  | tuple (items : List SItem)
  | other (typeName : String)
  deriving Repr, DecidableEq, Inhabited

/-- A C `BytesIO` and its instance dict (`none` while `self->dict` is `NULL`). -/
structure DState where
  s : BState
  dict : Option (List (String × Int))
  deriving Repr, DecidableEq, Inhabited

/-- `d[k] = v` on an insertion-ordered dict. -/
def dictSet (d : List (String × Int)) (k : String) (v : Int) : List (String × Int) :=
  if d.any (·.1 == k) then d.map (fun p => if p.1 = k then (k, v) else p) else d ++ [(k, v)]

/-- `PyDict_Update(old, new)`. -/
def dictUpdate (old new : List (String × Int)) : List (String × Int) :=
  new.foldl (fun acc p => dictSet acc p.1 p.2) old

/-- A dict slot as the harness reports it: `[None]` for `None`, else `True` and the items. -/
def encDict : Option (List (String × Int)) → List Atom
  | none => [.none]
  | some kv => .bool true :: kv.flatMap (fun p => [.str (p.1.toList.map Char.toNat), .int p.2])

inductive DOp where
  | base (o : BOp)
  /-- `f.k = v`. -/
  | setattr (k : String) (v : Int)
  /-- `f.__dict__`, which creates the dict. -/
  | getdict
  | getstate
  | setstate (a : SArg)
  deriving Repr, DecidableEq, Inhabited

namespace C

def setstateShape (t : String) : PyExc :=
  .typeError s!"_io.BytesIO.__setstate__ argument should be 3-tuple, got {t}"

/-- `_io_BytesIO_write_impl(self, state[0])` (bytesio.c:977-980): a `bytes` or `bytearray` is
written, anything else refused by `PyObject_GetBuffer` (:242). -/
def writeSItem (s : BState) : SItem → BState × Py Val
  | .bytes b | .bytearray b => write s b
  | x => (s, .error (.typeError s!"a bytes-like object is required, not '{x.typeName}'"))

/-- The position item (bytesio.c:985-1000): `PyLong_Check` (:986-991), `PyLong_AsSsize_t`
(:992-994), the sign (:995-999). A `bool` is an int. -/
def statePos : SItem → Py Int
  | .int v => argSsize v
  | .bool b => .ok (if b then 1 else 0)
  | x => .error (.typeError s!"second item of state must be an integer, not {x.typeName}")

/-- `bytesio_setstate_lock_held` after `state[0]` was written into `s` (bytesio.c:985-1022):
the position, then the dict, `None` skipped, a non-dict refused, a dict merged into an
existing `self->dict` (:1011-1016) or installed (:1018). -/
def setstateRest (d : DState) (s : BState) (i1 i2 : SItem) : DState × Py Val :=
  match statePos i1 with
  | .error e => ({ d with s := s }, .error e)
  | .ok p =>
    if p < 0 then ({ d with s := s }, .error (.valueError "position value cannot be negative")) else
    match i2 with
    | .none => ({ d with s := { s with pos := p.toNat } }, .ok .none)
    | .dict kv =>
      (DState.mk { s with pos := p.toNat } (some (match d.dict with | some old => dictUpdate old kv | none => kv)),
       .ok .none)
    | x => ({ d with s := { s with pos := p.toNat } },
        .error (.typeError s!"third item of state should be a dict, got a {x.typeName}"))

/-- `bytesio_setstate_lock_held`, bytesio.c:948-1023: the shape check (:963-968), exports
(:969), the reset (:972-973), the write of `state[0]` (:977-980), then the rest. Every
failure returns at once, keeping what was done before it. -/
def setstateObj (d : DState) : SArg → DState × Py Val
  | .other t => (d, .error (setstateShape t))
  | .tuple (i0 :: i1 :: i2 :: _) =>
    if d.s.exports > 0 then (d, .error bufferError) else
    match writeSItem { d.s with buf := [], pos := 0 } i0 with
    | (s, .error e) => ({ d with s := s }, .error e)
    | (s, .ok _) => setstateRest d s i1 i2
  | .tuple _ => (d, .error (setstateShape "tuple"))

/-- `bytesio_getstate_lock_held`, bytesio.c:909-935: `getvalue()` (which refuses a closed
stream), `None` for a `NULL` dict or `PyDict_Copy(self->dict)`, and the position. -/
def getstateObj (d : DState) : DState × Py Val :=
  if d.s.closed then (d, .error closedErr)
  else (d, .ok (.list ([.bytes d.s.buf, .int d.s.pos] ++ encDict d.dict)))

def dstep (d : DState) : DOp → DState × Py Val
  | .base o => let (s, r) := step d.s o; ({ d with s := s }, r)
  | .setattr k v => ({ d with dict := some (dictSet (d.dict.getD []) k v) }, .ok .none)
  | .getdict => ({ d with dict := some (d.dict.getD []) }, .ok (.list (encDict (some (d.dict.getD [])))))
  | .getstate => getstateObj d
  | .setstate a => setstateObj d a

end C

/-- The state `__getstate__` returns, as a `__setstate__` argument. -/
def getstateArg (d : DState) : SArg :=
  .tuple [.bytes d.s.buf, .int d.s.pos, match d.dict with | none => .none | some kv => .dict kv]

theorem C_write_reset (s : BState) (b : List Nat) (hc : s.closed = false) (he : s.exports = 0)
    (hm : b.length < memLimit) :
    C.write { s with buf := [], pos := 0 } b =
      (if b = [] then { s with buf := [], pos := 0 } else { s with buf := b, pos := b.length, shared := false },
       .ok (.int b.length)) := by
  have hmax : memLimit ≤ ssizeMax := by decide
  obtain ⟨tb, tp, tc, te, ts⟩ := s
  simp only at hc he; subst hc he
  by_cases hb : b = []
  · simp [C.write, hb]
  · have hl : b.length ≠ 0 := fun e => hb (List.eq_nil_of_length_eq_zero e)
    have c1 : ¬ ((0 + b.length : Nat) > 0 ∧ (((0 + b.length : Nat)) : Int) > ssizeMax) := by omega
    have c2 : ¬ ((0 + b.length : Nat) > 0 ∧ (((0 + b.length : Nat)) : Int) = ssizeMax) := by omega
    have c3 : ¬ ((0 + b.length : Nat) > 0 ∧ (0 + b.length : Nat) ≥ memLimit) := by omega
    simp only [C.write, Bool.false_eq_true, ite_false, Nat.lt_irrefl, gt_iff_lt, hl, List.length_nil]
    simp only [gt_iff_lt] at c1 c2 c3
    simp only [c1, c2, c3, ite_false, hb]
    simp [writeAt]

/-- `__setstate__(state)` on an exact `io.BytesIO`, for every stream and every state object:
a non-tuple or a tuple of fewer than 3 items raises
`TypeError('_io.BytesIO.__setstate__ argument should be 3-tuple, got T')` and changes
nothing, as does `BufferError` with a live view. On an open stream with no view the stream
is emptied first, so a first item that is not bytes-like raises its `TypeError` and leaves
it empty at 0; a bytes-like first item `b` (below the allocation bound) becomes the
contents whatever follows. Then a second item that is not an int raises
`TypeError('second item of state must be an integer, not T')`, one outside `Py_ssize_t`
`OverflowError`, a negative one `ValueError('position value cannot be negative')`, each with
the position left at `len(b)` by the write; a `bool` is an int. Otherwise the position is
set, and the third item: `None` keeps the dict, a dict is merged into the instance dict or
becomes it, anything else raises `TypeError('third item of state should be a dict, got a T')`
with contents and position already set. -/
def BytesIOSetstateChecks : Prop := ∀ (d : DState),
  (∀ t, C.setstateObj d (.other t) = (d, .error (C.setstateShape t))) ∧
  (∀ items : List SItem, items.length < 3 → C.setstateObj d (.tuple items) = (d, .error (C.setstateShape "tuple"))) ∧
  (d.s.exports > 0 → ∀ i0 i1 i2 rest, C.setstateObj d (.tuple (i0 :: i1 :: i2 :: rest)) = (d, .error bufferError)) ∧
  (d.s.closed = false → d.s.exports = 0 → ∀ i0 i1 i2 rest,
    ((∀ b, i0 ≠ .bytes b ∧ i0 ≠ .bytearray b) →
      C.setstateObj d (.tuple (i0 :: i1 :: i2 :: rest)) = ({ d with s := { d.s with buf := [], pos := 0 } },
        .error (.typeError s!"a bytes-like object is required, not '{i0.typeName}'"))) ∧
    (∀ b, (i0 = .bytes b ∨ i0 = .bytearray b) → b.length < memLimit →
      (C.setstateObj d (.tuple (i0 :: i1 :: i2 :: rest))).1.s.buf = b ∧
      (C.setstateObj d (.tuple (i0 :: i1 :: i2 :: rest))).1.s.closed = false ∧
      ((∀ v, i1 ≠ .int v) → (∀ bb, i1 ≠ .bool bb) →
        (C.setstateObj d (.tuple (i0 :: i1 :: i2 :: rest))).2 =
          .error (.typeError s!"second item of state must be an integer, not {i1.typeName}") ∧
        (C.setstateObj d (.tuple (i0 :: i1 :: i2 :: rest))).1.s.pos = b.length ∧
        (C.setstateObj d (.tuple (i0 :: i1 :: i2 :: rest))).1.dict = d.dict) ∧
      (∀ v, i1 = .int v → ¬ InSsize v →
        (C.setstateObj d (.tuple (i0 :: i1 :: i2 :: rest))).2 =
          .error (.overflowError "Python int too large to convert to C ssize_t") ∧
        (C.setstateObj d (.tuple (i0 :: i1 :: i2 :: rest))).1.s.pos = b.length) ∧
      (∀ v, i1 = .int v → InSsize v → v < 0 →
        (C.setstateObj d (.tuple (i0 :: i1 :: i2 :: rest))).2 =
          .error (.valueError "position value cannot be negative") ∧
        (C.setstateObj d (.tuple (i0 :: i1 :: i2 :: rest))).1.s.pos = b.length) ∧
      (∀ v, (i1 = .int v ∨ (∃ bb, i1 = .bool bb ∧ v = if bb then 1 else 0)) → InSsize v → 0 ≤ v →
        (C.setstateObj d (.tuple (i0 :: i1 :: i2 :: rest))).1.s.pos = v.toNat ∧
        (i2 = .none → (C.setstateObj d (.tuple (i0 :: i1 :: i2 :: rest))).2 = .ok .none ∧
          (C.setstateObj d (.tuple (i0 :: i1 :: i2 :: rest))).1.dict = d.dict) ∧
        (∀ kv, i2 = .dict kv → (C.setstateObj d (.tuple (i0 :: i1 :: i2 :: rest))).2 = .ok .none ∧
          (C.setstateObj d (.tuple (i0 :: i1 :: i2 :: rest))).1.dict =
            some (match d.dict with | some old => dictUpdate old kv | none => kv)) ∧
        (i2 ≠ .none → (∀ kv, i2 ≠ .dict kv) →
          (C.setstateObj d (.tuple (i0 :: i1 :: i2 :: rest))).2 =
            .error (.typeError s!"third item of state should be a dict, got a {i2.typeName}") ∧
          (C.setstateObj d (.tuple (i0 :: i1 :: i2 :: rest))).1.dict = d.dict))))

theorem setstate_written (d : DState) (i0 : SItem) (b : List Nat) (hc : d.s.closed = false) (he : d.s.exports = 0)
    (hb : i0 = .bytes b ∨ i0 = .bytearray b) (hm : b.length < memLimit) :
    C.writeSItem { d.s with buf := [], pos := 0 } i0 =
      (if b = [] then { d.s with buf := [], pos := 0 } else { d.s with buf := b, pos := b.length, shared := false },
       .ok (.int b.length)) := by
  rcases hb with rfl | rfl <;> exact C_write_reset d.s b hc he hm

theorem bytesIOSetstateChecks_proven : BytesIOSetstateChecks := by
  intro d
  refine ⟨fun t => rfl, fun items h => ?_, fun he i0 i1 i2 rest => ?_, fun hc he i0 i1 i2 rest => ⟨fun hn => ?_, fun b hb hm => ?_⟩⟩
  · match items, h with
    | [], _ => rfl
    | [_], _ => rfl
    | [_, _], _ => rfl
  · simp [C.setstateObj, he]
  · have hne : ¬ d.s.exports > 0 := by omega
    have : C.writeSItem { d.s with buf := [], pos := 0 } i0 = ({ d.s with buf := [], pos := 0 },
        .error (.typeError s!"a bytes-like object is required, not '{i0.typeName}'")) := by
      cases i0 with
      | bytes b => exact absurd rfl (hn b).1
      | bytearray b => exact absurd rfl (hn b).2
      | _ => rfl
    simp only [C.setstateObj, hne, ite_false, this]
  · have hne : ¬ d.s.exports > 0 := by omega
    have hw := setstate_written d i0 b hc he hb hm
    generalize hsw : (if b = [] then { d.s with buf := [], pos := 0 }
      else { d.s with buf := b, pos := b.length, shared := false }) = sw at hw
    have hsw' : sw.buf = b ∧ sw.pos = b.length ∧ sw.closed = false := by
      rw [← hsw]; by_cases h : b = [] <;> simp [h, hc]
    have hS : C.setstateObj d (.tuple (i0 :: i1 :: i2 :: rest)) = C.setstateRest d sw i1 i2 := by
      simp only [C.setstateObj, hne, ite_false, hw]
    rw [hS]
    refine ⟨?_, ?_, fun h1 h2 => ?_, fun v hv hr => ?_, fun v hv hr hn => ?_, fun v hv hr hp => ?_⟩
    · unfold C.setstateRest
      split
      · exact hsw'.1
      · split
        · exact hsw'.1
        · split <;> exact hsw'.1
    · unfold C.setstateRest
      split
      · exact hsw'.2.2
      · split
        · exact hsw'.2.2
        · split <;> exact hsw'.2.2
    · have : C.statePos i1 = .error (.typeError s!"second item of state must be an integer, not {i1.typeName}") := by
        cases i1 with
        | int v => exact absurd rfl (h1 v)
        | bool bb => exact absurd rfl (h2 bb)
        | _ => rfl
      simp only [C.setstateRest, this]
      simp [hsw']
    · subst hv
      have : C.statePos (.int v) = .error (.overflowError "Python int too large to convert to C ssize_t") := by
        simp [C.statePos, argSsize, hr]
      simp only [C.setstateRest, this]
      simp [hsw']
    · subst hv
      have : C.statePos (.int v) = .ok v := by simp [C.statePos, argSsize, hr]
      simp only [C.setstateRest, this, hn, ite_true]
      simp [hsw']
    · have : C.statePos i1 = .ok v := by
        rcases hv with rfl | ⟨bb, rfl, rfl⟩
        · simp [C.statePos, argSsize, hr]
        · rfl
      have hpn : ¬ v < 0 := by omega
      simp only [C.setstateRest, this, hpn, ite_false]
      refine ⟨?_, fun h => ?_, fun kv h => ?_, fun h1 h2 => ?_⟩
      · cases i2 <;> rfl
      · subst h; exact ⟨rfl, rfl⟩
      · subst h; exact ⟨rfl, rfl⟩
      · cases i2 with
        | none => exact absurd rfl h1
        | dict kv => exact absurd rfl (h2 kv)
        | _ => exact ⟨rfl, rfl⟩

/-- Pickling round trip with the instance dict: `__getstate__` of an open `io.BytesIO`
returns its contents, its position and a copy of its instance dict, or `None` while it has
none (bytesio.c:921-930), without changing it; `__setstate__` of that state on any open
`io.BytesIO` with no view restores contents and position and merges the dict into the
target's, so into a fresh object it brings the dict over exactly. Hypotheses: the position
fits `Py_ssize_t` and the contents are below the allocation bound (type invariants). -/
def BytesIOPickleDict : Prop := ∀ (d t : DState), d.s.closed = false → t.s.closed = false → t.s.exports = 0 →
  (d.s.pos : Int) ≤ ssizeMax → d.s.buf.length < memLimit →
  C.getstateObj d = (d, .ok (.list ([.bytes d.s.buf, .int d.s.pos] ++ encDict d.dict))) ∧
  (C.setstateObj t (getstateArg d)).2 = .ok .none ∧
  (C.setstateObj t (getstateArg d)).1.s.buf = d.s.buf ∧ (C.setstateObj t (getstateArg d)).1.s.pos = d.s.pos ∧
  (C.setstateObj t (getstateArg d)).1.dict =
    (match d.dict with
     | none => t.dict
     | some kv => some (match t.dict with | some old => dictUpdate old kv | none => kv)) ∧
  (t.dict = none → (C.setstateObj t (getstateArg d)).1.dict = d.dict)

theorem bytesIOPickleDict_proven : BytesIOPickleDict := by
  intro d t hd ht he hp hm
  have hz : ssizeMin ≤ 0 := by decide
  have hsz : InSsize (d.s.pos : Int) := ⟨by omega, hp⟩
  obtain ⟨_, _, _, h⟩ := bytesIOSetstateChecks_proven t
  refine ⟨by simp [C.getstateObj, hd], ?_⟩
  cases hdd : d.dict with
  | none =>
    obtain ⟨_, hok⟩ := h ht he (.bytes d.s.buf) (.int d.s.pos) .none []
    obtain ⟨hbuf, _, _, _, _, hpos⟩ := hok d.s.buf (.inl rfl) hm
    obtain ⟨hpv, hnone, _, _⟩ := hpos d.s.pos (.inl rfl) hsz (by omega)
    simp only [getstateArg, hdd]
    exact ⟨(hnone rfl).1, hbuf, by rw [hpv]; simp, (hnone rfl).2, fun htn => by simp [(hnone rfl).2, htn]⟩
  | some kv =>
    obtain ⟨_, hok⟩ := h ht he (.bytes d.s.buf) (.int d.s.pos) (.dict kv) []
    obtain ⟨hbuf, _, _, _, _, hpos⟩ := hok d.s.buf (.inl rfl) hm
    obtain ⟨hpv, _, hdict, _⟩ := hpos d.s.pos (.inl rfl) hsz (by omega)
    simp only [getstateArg, hdd]
    exact ⟨(hdict kv rfl).1, hbuf, by rw [hpv]; simp, (hdict kv rfl).2, fun htn => by simp [(hdict kv rfl).2, htn]⟩

end PyLean.PyIO
