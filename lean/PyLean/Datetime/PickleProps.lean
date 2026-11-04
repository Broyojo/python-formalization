import PyLean.Datetime.ArgCheckProps

/-!
Pickling `time` and `datetime` end to end (review 50b4b958): `_getstate` with its tzinfo
element, `__reduce_ex__`/`__reduce__`, and unpickling through the pickle branch of
`__new__` (the header test, the latin-1 encoding, `__setstate` and its
`bad tzinfo state arg`). C mirrored separately: `time_getstate`/`datetime_getstate` set the
fold bit with `|=`, `time_from_pickle`/`datetime_from_pickle` decode. 3.15.2.
-/

namespace PyLean.Datetime
open PyLean

/-! ### Models -/

/-- The state tuple `_getstate` returns: `(basestate,)` for a naive object, `(basestate, tzinfo)`
otherwise. -/
inductive StateTuple where
  | one (b : List Nat)
  | two (b : List Nat) (tz : Tz)
  deriving DecidableEq, Repr

/-- `cls(*state)`, what unpickling calls. -/
def StateTuple.args : StateTuple → List Arg
  | .one b => [.bytes b]
  | .two b z => [.bytes b, .tz z]

/-- `time._getstate(protocol)`, Py:1753-1764: the six bytes (fold added to the hour above
protocol 3), then the tuple with the tzinfo when there is one. -/
def tmGetstateTuplePy (t : TM) (protocol : Int) : StateTuple :=
  match t.tz with
  | none => .one (tmGetstate t protocol)
  | some z => .two (tmGetstate t protocol) z

/-- `time_getstate`, :5269-5287: the packed data with `|= (1 << 7)` on the first byte for
`proto > 3` and fold (:5277-5279), then `PyTuple_Pack(1, ...)` or the pair (:5280-5283). -/
def tmGetstateTupleC (t : TM) (proto : Int) : StateTuple :=
  let b := match timeData t with
    | h :: rest => (if proto > 3 ∧ t.fold ≠ 0 then h ||| 128 else h) :: rest
    | [] => []
  match t.tz with
  | none => .one b
  | some z => .two b z

/-- `time.__reduce_ex__(protocol)`, Py:1779-1780: `(self.__class__, self._getstate(protocol))`;
the class is the receiver's (classes by identity), so the state is what varies. -/
def tmReduceExPy (t : TM) (protocol : Int) : StateTuple := tmGetstateTuplePy t protocol

/-- `time.__reduce__()`, Py:1782-1783: `self.__reduce_ex__(2)`. -/
def tmReducePy (t : TM) : StateTuple := tmReduceExPy t 2

/-- `datetime_time___reduce_ex___impl`, :5297-5300. -/
def tmReduceExC (t : TM) (proto : Int) : StateTuple := tmGetstateTupleC t proto

/-- `datetime_time___reduce___impl`, :5308-5311: `time_getstate(self, 2)`. -/
def tmReduceC (t : TM) : StateTuple := tmGetstateTupleC t 2

/-- `datetime._getstate(protocol)`, Py:2402-2415. -/
def dtGetstateTuplePy (dt : DT) (protocol : Int) : StateTuple :=
  match dt.tz with
  | none => .one (dtGetstate dt protocol)
  | some z => .two (dtGetstate dt protocol) z

/-- `datetime_getstate`, :7201-7219: the month byte `|= (1 << 7)` for `proto > 3` and fold. -/
def dtGetstateTupleC (dt : DT) (proto : Int) : StateTuple :=
  let b := match dtData dt with
    | yhi :: ylo :: m :: rest => yhi :: ylo :: (if proto > 3 ∧ dt.fold ≠ 0 then m ||| 128 else m) :: rest
    | l => l
  match dt.tz with
  | none => .one b
  | some z => .two b z

/-- `datetime.__reduce_ex__(protocol)`, Py:2432-2433. -/
def dtReduceExPy (dt : DT) (protocol : Int) : StateTuple := dtGetstateTuplePy dt protocol

/-- `datetime.__reduce__()`, Py:2435-2436: `self.__reduce_ex__(2)`. -/
def dtReducePy (dt : DT) : StateTuple := dtReduceExPy dt 2

/-- `datetime_datetime___reduce_ex___impl`, :7229-7233. -/
def dtReduceExC (dt : DT) (proto : Int) : StateTuple := dtGetstateTupleC dt proto

/-- `datetime_datetime___reduce___impl`, :7241-7245: `datetime_getstate(self, 2)`. -/
def dtReduceC (dt : DT) : StateTuple := dtGetstateTupleC dt 2

/-! ### Lemmas -/

theorem or128 : ∀ n : Nat, n < 128 → n ||| 128 = n + 128 := by decide

theorem tmGetstate_twin (t : TM) (p : Int) (h : t.Valid) : tmGetstateTupleC t p = tmGetstateTuplePy t p := by
  obtain ⟨h1, h2, _⟩ := h
  have : t.h.toNat ||| 128 = t.h.toNat + 128 := or128 _ (by omega)
  have e : (match timeData t with
      | h :: rest => (if p > 3 ∧ t.fold ≠ 0 then h ||| 128 else h) :: rest
      | [] => []) = tmGetstate t p := by
    simp only [timeData, tmGetstate, this]
    by_cases hc : p > 3 ∧ t.fold ≠ 0
    · simp [hc]
    · have hc' : ¬ (t.fold ≠ 0 ∧ p > 3) := fun x => hc ⟨x.2, x.1⟩
      simp only [hc, hc', ↓reduceIte]
  unfold tmGetstateTupleC tmGetstateTuplePy
  simp only [e]

theorem dtGetstate_twin (dt : DT) (p : Int) (h : dt.Valid) : dtGetstateTupleC dt p = dtGetstateTuplePy dt p := by
  obtain ⟨hd, _⟩ := h
  have hm : 1 ≤ dt.m ∧ dt.m ≤ 12 := by unfold ValidDate at hd; omega
  have : dt.m.toNat ||| 128 = dt.m.toNat + 128 := or128 _ (by omega)
  have e : (match dtData dt with
      | yhi :: ylo :: m :: rest => yhi :: ylo :: (if p > 3 ∧ dt.fold ≠ 0 then m ||| 128 else m) :: rest
      | l => l) = dtGetstate dt p := by
    simp only [dtData, dateData, dtGetstate, List.cons_append, this]
    by_cases hc : p > 3 ∧ dt.fold ≠ 0
    · simp [hc]
    · have hc' : ¬ (dt.fold ≠ 0 ∧ p > 3) := fun x => hc ⟨x.2, x.1⟩
      simp only [hc, hc', ↓reduceIte]
  unfold dtGetstateTupleC dtGetstateTuplePy
  simp only [e]

/-- The six state bytes of a valid time: the header test of the pickle branch passes. -/
theorem tmGetstate_header (t : TM) (p : Int) (h : t.Valid) :
    (tmGetstate t p).length = 6 ∧ (tmGetstate t p).getD 0 0 % 128 < 24 := by
  obtain ⟨h1, h2, _⟩ := h
  simp only [tmGetstate, timeData]
  split <;> simp only [List.length_cons, List.length_nil, List.getD_cons_zero, true_and] <;> omega

theorem tmGetstate_form (t : TM) (p : Int) (h : t.Valid) :
    ∃ b0 b1 b2 b3 b4 b5 : Nat, tmGetstate t p = [b0, b1, b2, b3, b4, b5] ∧ b0 % 128 < 24 := by
  obtain ⟨h1, h2, _⟩ := h
  simp only [tmGetstate, timeData]
  split
  · exact ⟨_, _, _, _, _, _, rfl, by omega⟩
  · exact ⟨_, _, _, _, _, _, rfl, by omega⟩

theorem dtGetstate_form (dt : DT) (p : Int) (h : dt.Valid) :
    ∃ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Nat, dtGetstate dt p = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9] ∧
      1 ≤ b2 % 128 ∧ b2 % 128 ≤ 12 := by
  obtain ⟨hd, _⟩ := h
  have hm : 1 ≤ dt.m ∧ dt.m ≤ 12 := by unfold ValidDate at hd; omega
  simp only [dtGetstate, dtData, dateData, List.cons_append, List.nil_append]
  split
  · exact ⟨_, _, _, _, _, _, _, _, _, _, rfl, by omega, by omega⟩
  · exact ⟨_, _, _, _, _, _, _, _, _, _, rfl, by omega, by omega⟩

theorem dtGetstate_header (dt : DT) (p : Int) (h : dt.Valid) :
    (dtGetstate dt p).length = 10 ∧ 1 ≤ (dtGetstate dt p).getD 2 0 % 128 ∧ (dtGetstate dt p).getD 2 0 % 128 ≤ 12 := by
  obtain ⟨hd, _⟩ := h
  have hm : 1 ≤ dt.m ∧ dt.m ≤ 12 := by unfold ValidDate at hd; omega
  simp only [dtGetstate, dtData, dateData, List.cons_append, List.nil_append]
  split <;> simp only [List.length_cons, List.length_nil, List.getD_cons_succ, List.getD_cons_zero, true_and] <;> omega

/-! ### Pickle round trips -/

/-- Pickling a `time` with `__reduce_ex__(p)` (what `pickle.dumps` calls with its protocol) or
`__reduce__()`, for every valid time and every protocol: the twins produce the same state
tuple; `__reduce__` is `__reduce_ex__(2)`; and unpickling it, `time(*state)` (the pickle branch of
the constructor), gives back the time with its tzinfo, and its fold above protocol 3 and fold 0
otherwise, in both twins. A `_getstate` that dropped the tzinfo, or a `__reduce__` that kept
the fold, does not satisfy it. -/
def TimeReduceRoundtrip : Prop :=
  ∀ (t : TM) (p : Int), t.Valid →
    tmReduceExPy t p = tmReduceExC t p ∧ tmReducePy t = tmReduceC t ∧
    timeCallPy (tmReduceExPy t p).args (.int 0) = .ok { t with fold := if p > 3 then t.fold else 0 } ∧
    timeNewC (tmReduceExC t p).args (.int 0) = .ok { t with fold := if p > 3 then t.fold else 0 } ∧
    timeCallPy (tmReducePy t).args (.int 0) = .ok { t with fold := 0 } ∧
    timeNewC (tmReduceC t).args (.int 0) = .ok { t with fold := 0 }

theorem tm_unpickle_py (t : TM) (p : Int) (h : t.Valid) :
    timeCallPy (tmGetstateTuplePy t p).args (.int 0) = .ok { t with fold := if p > 3 then t.fold else 0 } := by
  obtain ⟨b0, b1, b2, b3, b4, b5, hb, hb0⟩ := tmGetstate_form t p h
  have hp := timePickle_proven t p h
  have hs : tmSetstate t.tz (tmGetstate t p) = some { t with fold := if p > 3 then t.fold else 0 } := by
    by_cases h3 : p > 3
    · rw [hp.1 h3]; simp [h3]
    · rw [hp.2 (by omega)]; simp [h3]
  rw [hb] at hs
  unfold tmGetstateTuplePy
  rw [hb]
  cases htz : t.tz with
  | none =>
    rw [htz] at hs
    simp [StateTuple.args, timeCallPy, timeNewPy, stateOf, hb0, Arg.falsy, stateTz, hs, bind, Except.bind,
      pure, Except.pure]
  | some z =>
    rw [htz] at hs
    simp [StateTuple.args, timeCallPy, timeNewPy, stateOf, hb0, Arg.falsy, stateTz, hs, bind, Except.bind,
      pure, Except.pure]

theorem tm_unpickle_c (t : TM) (p : Int) (h : t.Valid) :
    timeNewC (tmGetstateTuplePy t p).args (.int 0) = .ok { t with fold := if p > 3 then t.fold else 0 } := by
  obtain ⟨b0, b1, b2, b3, b4, b5, hb, hb0⟩ := tmGetstate_form t p h
  have hp := timePickle_proven t p h
  have hs : tmSetstate t.tz (tmGetstate t p) = some { t with fold := if p > 3 then t.fold else 0 } := by
    by_cases h3 : p > 3
    · rw [hp.1 h3]; simp [h3]
    · rw [hp.2 (by omega)]; simp [h3]
  rw [hb] at hs
  unfold tmGetstateTuplePy
  rw [hb]
  cases htz : t.tz with
  | none =>
    rw [htz] at hs
    simp [StateTuple.args, timeNewC, stateOf, hb0, stateTz, hs, bind, Except.bind, pure, Except.pure]
  | some z =>
    rw [htz] at hs
    simp [StateTuple.args, timeNewC, stateOf, hb0, stateTz, hs, bind, Except.bind, pure, Except.pure]

theorem timeReduceRoundtrip_proven : TimeReduceRoundtrip := by
  intro t p h
  have e1 := tmGetstate_twin t p h
  have e2 := tmGetstate_twin t 2 h
  refine ⟨e1.symm, e2.symm, tm_unpickle_py t p h, ?_, ?_, ?_⟩
  · unfold tmReduceExC; rw [e1]; exact tm_unpickle_c t p h
  · unfold tmReducePy tmReduceExPy; have := tm_unpickle_py t 2 h; simpa using this
  · unfold tmReduceC; rw [e2]; have := tm_unpickle_c t 2 h; simpa using this

/-- The same for `datetime`: the twins produce the same state tuple, `__reduce__` is
`__reduce_ex__(2)`, and `datetime(*state)` gives back the datetime with its tzinfo, its fold
above protocol 3 and fold 0 otherwise, in both twins. -/
def DatetimeReduceRoundtrip : Prop :=
  ∀ (dt : DT) (p : Int), dt.Valid →
    dtReduceExPy dt p = dtReduceExC dt p ∧ dtReducePy dt = dtReduceC dt ∧
    datetimeCallPy (dtReduceExPy dt p).args (.int 0) = .ok { dt with fold := if p > 3 then dt.fold else 0 } ∧
    datetimeNewC (dtReduceExC dt p).args (.int 0) = .ok { dt with fold := if p > 3 then dt.fold else 0 } ∧
    datetimeCallPy (dtReducePy dt).args (.int 0) = .ok { dt with fold := 0 } ∧
    datetimeNewC (dtReduceC dt).args (.int 0) = .ok { dt with fold := 0 }

theorem dt_unpickle_py (dt : DT) (p : Int) (h : dt.Valid) :
    datetimeCallPy (dtGetstateTuplePy dt p).args (.int 0) = .ok { dt with fold := if p > 3 then dt.fold else 0 } := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, hb, hb1, hb2⟩ := dtGetstate_form dt p h
  have hp := datetimePickle_proven dt p h
  have hs : dtSetstate dt.tz (dtGetstate dt p) = some { dt with fold := if p > 3 then dt.fold else 0 } := by
    by_cases h3 : p > 3
    · rw [hp.1 h3]; simp [h3]
    · rw [hp.2 (by omega)]; simp [h3]
  rw [hb] at hs
  unfold dtGetstateTuplePy
  rw [hb]
  cases htz : dt.tz with
  | none =>
    rw [htz] at hs
    simp [StateTuple.args, datetimeCallPy, datetimeNewPy, stateOf, hb1, hb2, stateTz, hs, bind, Except.bind,
      pure, Except.pure]
  | some z =>
    rw [htz] at hs
    simp [StateTuple.args, datetimeCallPy, datetimeNewPy, stateOf, hb1, hb2, stateTz, hs, bind, Except.bind,
      pure, Except.pure]

theorem dt_unpickle_c (dt : DT) (p : Int) (h : dt.Valid) :
    datetimeNewC (dtGetstateTuplePy dt p).args (.int 0) = .ok { dt with fold := if p > 3 then dt.fold else 0 } := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, hb, hb1, hb2⟩ := dtGetstate_form dt p h
  have hp := datetimePickle_proven dt p h
  have hs : dtSetstate dt.tz (dtGetstate dt p) = some { dt with fold := if p > 3 then dt.fold else 0 } := by
    by_cases h3 : p > 3
    · rw [hp.1 h3]; simp [h3]
    · rw [hp.2 (by omega)]; simp [h3]
  rw [hb] at hs
  unfold dtGetstateTuplePy
  rw [hb]
  cases htz : dt.tz with
  | none =>
    rw [htz] at hs
    simp [StateTuple.args, datetimeNewC, stateOf, hb1, hb2, stateTz, hs, bind, Except.bind, pure, Except.pure]
  | some z =>
    rw [htz] at hs
    simp [StateTuple.args, datetimeNewC, stateOf, hb1, hb2, stateTz, hs, bind, Except.bind, pure, Except.pure]

theorem datetimeReduceRoundtrip_proven : DatetimeReduceRoundtrip := by
  intro dt p h
  have e1 := dtGetstate_twin dt p h
  have e2 := dtGetstate_twin dt 2 h
  refine ⟨e1.symm, e2.symm, dt_unpickle_py dt p h, ?_, ?_, ?_⟩
  · unfold dtReduceExC; rw [e1]; exact dt_unpickle_c dt p h
  · unfold dtReducePy dtReduceExPy; have := dt_unpickle_py dt 2 h; simpa using this
  · unfold dtReduceC; rw [e2]; have := dt_unpickle_c dt 2 h; simpa using this

/-! ### The pickle branch of `time(...)` and `datetime(...)` on any state -/

/-- `time(state, tzinfo)` for every byte string and tzinfo argument (unpickling, or a direct
call): the header test (:1446-1447: six bytes and `ord(state[0]) & 0x7F < 24`) selects the
pickle branch, where `__setstate` (:1766-1777) decodes hour (the low seven bits of the first
byte), fold (its top bit), minute, second and the 24-bit microsecond, unchecked, and keeps the
tzinfo, in both twins, for a `None`/omitted or `tzinfo` second argument; a second argument
that is neither (and not falsy, `datetime-time-pickle-falsy-tzinfo`) is
`TypeError('bad tzinfo state arg')` in both (:1767-1768, `time_from_pickle` :4682-4685); a `str`
state with a character above U+00FF is the latin-1 `ValueError` in both; and bytes failing the
header take the field path, a `TypeError` in both. -/
def TimeNewPickle : Prop :=
  ∀ (b : List Nat) (z : Option Tz) (cs : List Nat),
    (b.length = 6 → b.getD 0 0 % 128 < 24 → (∀ x ∈ b, x < 256) →
      let v : TM := ⟨(b.getD 0 0 % 128 : Nat), (b.getD 1 0 : Nat), (b.getD 2 0 : Nat),
        ((b.getD 3 0 * 256 + b.getD 4 0) * 256 + b.getD 5 0 : Nat), if b.getD 0 0 ≥ 128 then 1 else 0, z⟩
      timeCallPy [.bytes b, tzArg z] (.int 0) = .ok v ∧ timeNewC [.bytes b, tzArg z] (.int 0) = .ok v ∧
      (timeCallPy [.bytes b, .other] (.int 0)).raises "TypeError" ∧
      (timeNewC [.bytes b, .other] (.int 0)).raises "TypeError") ∧
    (cs.length = 6 → cs.getD 0 0 % 128 < 24 → (∃ c ∈ cs, c > 255) →
      (timeCallPy [.str cs] (.int 0)).raises "ValueError" ∧ (timeNewC [.str cs] (.int 0)).raises "ValueError") ∧
    (¬ (b.length = 6 ∧ b.getD 0 0 % 128 < 24) →
      (timeCallPy [.bytes b, tzArg z] (.int 0)).raises "TypeError" ∧
      (timeNewC [.bytes b, tzArg z] (.int 0)).raises "TypeError")

theorem tmSetstate_decode (b : List Nat) (z : Option Tz) (hl : b.length = 6) (hb : ∀ x ∈ b, x < 256) :
    tmSetstate z b = some ⟨(b.getD 0 0 % 128 : Nat), (b.getD 1 0 : Nat), (b.getD 2 0 : Nat),
      ((b.getD 3 0 * 256 + b.getD 4 0) * 256 + b.getD 5 0 : Nat), if b.getD 0 0 ≥ 128 then 1 else 0, z⟩ := by
  match b, hl with
  | [h, mi, s, u1, u2, u3], _ =>
    have := hb h (by simp)
    simp only [tmSetstate, List.getD_cons_zero, List.getD_cons_succ]
    by_cases hh : h > 127
    · have hh' : h ≥ 128 := by omega
      simp only [hh, hh', ↓reduceIte, Option.some.injEq, TM.mk.injEq, and_true]
      omega
    · have hh' : ¬ h ≥ 128 := by omega
      simp only [hh, hh', ↓reduceIte, Option.some.injEq, TM.mk.injEq, and_true]
      omega

theorem timeNewPy_nohdr (b : List Nat) (mi s us tz fold : Arg) (hn : ¬(b.length = 6 ∧ b.getD 0 0 % 128 < 24)) :
    (timeNewPy (.bytes b) mi s us tz fold).raises "TypeError" := by
  unfold timeNewPy
  simp only [stateOf]
  rw [if_neg hn]
  exact ⟨_, rfl, rfl⟩

theorem timeNewC_nohdr (b : List Nat) (a : Arg) (hn : ¬(b.length = 6 ∧ b.getD 0 0 % 128 < 24)) :
    (timeNewC [.bytes b, a] (.int 0)).raises "TypeError" := by
  unfold timeNewC
  simp only [stateOf, List.length_cons, List.length_nil, List.headD]
  rw [if_neg hn]
  exact ⟨_, rfl, rfl⟩

theorem datetimeNewPy_nohdr (b : List Nat) (m d h mi s us tz fold : Arg)
    (hn : ¬(b.length = 10 ∧ 1 ≤ b.getD 2 0 % 128 ∧ b.getD 2 0 % 128 ≤ 12)) :
    (datetimeNewPy (.bytes b) m d h mi s us tz fold).raises "TypeError" := by
  unfold datetimeNewPy
  simp only [stateOf]
  rw [if_neg hn]
  exact ⟨_, rfl, rfl⟩

theorem datetimeNewC_nohdr (b : List Nat) (a : Arg)
    (hn : ¬(b.length = 10 ∧ 1 ≤ b.getD 2 0 % 128 ∧ b.getD 2 0 % 128 ≤ 12)) :
    (datetimeNewC [.bytes b, a] (.int 0)).raises "TypeError" := by
  unfold datetimeNewC
  simp only [stateOf, List.length_cons, List.length_nil, List.headD]
  rw [if_neg hn]
  exact ⟨_, rfl, rfl⟩

theorem timeNewPickle_proven : TimeNewPickle := by
  intro b z cs
  refine ⟨fun hl hh hb => ?_, fun hl hh hc => ?_, fun hn => ?_⟩
  · match b, hl with
    | [b0, b1, b2, b3, b4, b5], _ =>
      have hd := tmSetstate_decode [b0, b1, b2, b3, b4, b5] z rfl hb
      simp only [List.getD_cons_zero, List.getD_cons_succ] at hh hd ⊢
      refine ⟨?_, ?_, ?_, ?_⟩
      · cases z <;> simp [timeCallPy, timeNewPy, stateOf, hh, tzArg, Arg.falsy, stateTz, hd, bind,
          Except.bind, pure, Except.pure]
      · cases z <;> simp [timeNewC, stateOf, hh, tzArg, stateTz, hd, bind, Except.bind, pure, Except.pure]
      · simp [timeCallPy, timeNewPy, stateOf, hh, Arg.falsy, stateTz, bind, Except.bind, Py.raises,
          PyExc.className]
      · simp [timeNewC, stateOf, hh, stateTz, bind, Except.bind, Py.raises, PyExc.className]
  · have hany : cs.any (· > 255) = true := by
      obtain ⟨c, hm, hc⟩ := hc; exact List.any_eq_true.mpr ⟨c, hm, by simpa using hc⟩
    match cs, hl with
    | [c0, c1, c2, c3, c4, c5], _ =>
      simp only [List.getD_cons_zero] at hh
      refine ⟨?_, ?_⟩
      · simp [timeCallPy, timeNewPy, stateOf, hh, latin1State, hany, bind, Except.bind, Py.raises,
          PyExc.className]
      · simp [timeNewC, stateOf, hh, latin1State, hany, bind, Except.bind, Py.raises, PyExc.className]
  · exact ⟨timeNewPy_nohdr b _ _ _ _ _ hn, timeNewC_nohdr b _ hn⟩

/-- `datetime(state, tzinfo)` for every byte string: the header test (:1802-1803: ten bytes
and `1 <= ord(state[2]) & 0x7F <= 12`) selects the pickle branch, where `__setstate`
(:2417-2430) decodes year, month (low seven bits), fold (top bit), day, hour, minute, second
and microsecond, unchecked, and keeps the tzinfo, in both twins, for a `None`/omitted or
`tzinfo` second argument; any other second argument is `TypeError('bad tzinfo state arg')` in
both (no falsy conversion here); a `str` state above U+00FF is the latin-1 `ValueError` in
both; bytes failing the header take the field path, a `TypeError` in both. -/
def DatetimeNewPickle : Prop :=
  ∀ (b : List Nat) (z : Option Tz) (cs : List Nat),
    (b.length = 10 → 1 ≤ b.getD 2 0 % 128 → b.getD 2 0 % 128 ≤ 12 → (∀ x ∈ b, x < 256) →
      ∃ v : DT, dtSetstate z b = some v ∧
      v.y = (b.getD 0 0 * 256 + b.getD 1 0 : Nat) ∧ v.m = (b.getD 2 0 % 128 : Nat) ∧
      v.fold = (if b.getD 2 0 ≥ 128 then 1 else 0) ∧ v.d = b.getD 3 0 ∧ v.h = b.getD 4 0 ∧
      v.mi = b.getD 5 0 ∧ v.s = b.getD 6 0 ∧ v.us = ((b.getD 7 0 * 256 + b.getD 8 0) * 256 + b.getD 9 0 : Nat) ∧
      v.tz = z ∧
      datetimeCallPy [.bytes b, tzArg z] (.int 0) = .ok v ∧ datetimeNewC [.bytes b, tzArg z] (.int 0) = .ok v ∧
      (∀ a : Arg, (∀ t, a ≠ .tz t) → a ≠ .none_ →
        (datetimeCallPy [.bytes b, a] (.int 0)).raises "TypeError" ∧
        (datetimeNewC [.bytes b, a] (.int 0)).raises "TypeError")) ∧
    (cs.length = 10 → 1 ≤ cs.getD 2 0 % 128 → cs.getD 2 0 % 128 ≤ 12 → (∃ c ∈ cs, c > 255) →
      (datetimeCallPy [.str cs] (.int 0)).raises "ValueError" ∧ (datetimeNewC [.str cs] (.int 0)).raises "ValueError") ∧
    (¬ (b.length = 10 ∧ 1 ≤ b.getD 2 0 % 128 ∧ b.getD 2 0 % 128 ≤ 12) →
      (datetimeCallPy [.bytes b, tzArg z] (.int 0)).raises "TypeError" ∧
      (datetimeNewC [.bytes b, tzArg z] (.int 0)).raises "TypeError")

theorem datetimeNewPickle_proven : DatetimeNewPickle := by
  intro b z cs
  refine ⟨fun hl hh1 hh2 hb => ?_, fun hl hh1 hh2 hc => ?_, fun hn => ?_⟩
  · match b, hl with
    | [y1, y2, m, d, h, mi, s, u1, u2, u3], _ =>
      have hm := hb m (by simp)
      simp only [List.getD_cons_zero, List.getD_cons_succ] at hh1 hh2 ⊢
      have hdec : dtSetstate z [y1, y2, m, d, h, mi, s, u1, u2, u3] =
          some ⟨(y1 * 256 + y2 : Nat), (m % 128 : Nat), d, h, mi, s, ((u1 * 256 + u2) * 256 + u3 : Nat),
            if m ≥ 128 then 1 else 0, z⟩ := by
        simp only [dtSetstate]
        by_cases hmm : m > 127
        · have hm' : m ≥ 128 := by omega
          simp only [hmm, hm', ↓reduceIte, Option.some.injEq, DT.mk.injEq, and_true, true_and]
          omega
        · have hm' : ¬ m ≥ 128 := by omega
          simp only [hmm, hm', ↓reduceIte, Option.some.injEq, DT.mk.injEq, and_true, true_and]
          omega
      refine ⟨_, hdec, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, fun a ha hn => ⟨?_, ?_⟩⟩
      · cases z <;> simp [datetimeCallPy, datetimeNewPy, stateOf, hh1, hh2, tzArg, stateTz, hdec, bind,
          Except.bind, pure, Except.pure]
      · cases z <;> simp [datetimeNewC, stateOf, hh1, hh2, tzArg, stateTz, hdec, bind, Except.bind, pure,
          Except.pure]
      · have hst : (stateTz a).raises "TypeError" := by
          cases a with
          | none_ => exact absurd rfl hn
          | tz t => exact absurd rfl (ha t)
          | _ => exact ⟨_, rfl, rfl⟩
        obtain ⟨e, he, hc⟩ := hst
        refine ⟨e, ?_, hc⟩
        simp [datetimeCallPy, datetimeNewPy, stateOf, hh1, hh2, he, bind, Except.bind]
      · have hst : (stateTz a).raises "TypeError" := by
          cases a with
          | none_ => exact absurd rfl hn
          | tz t => exact absurd rfl (ha t)
          | _ => exact ⟨_, rfl, rfl⟩
        obtain ⟨e, he, hc⟩ := hst
        refine ⟨e, ?_, hc⟩
        simp [datetimeNewC, stateOf, hh1, hh2, he, bind, Except.bind]
  · have hany : cs.any (· > 255) = true := by
      obtain ⟨c, hm, hc⟩ := hc; exact List.any_eq_true.mpr ⟨c, hm, by simpa using hc⟩
    match cs, hl with
    | [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9], _ =>
      simp only [List.getD_cons_zero, List.getD_cons_succ] at hh1 hh2
      refine ⟨?_, ?_⟩
      · simp [datetimeCallPy, datetimeNewPy, stateOf, hh1, hh2, latin1State, hany, bind, Except.bind,
          Py.raises, PyExc.className]
      · simp [datetimeNewC, stateOf, hh1, hh2, latin1State, hany, bind, Except.bind, Py.raises,
          PyExc.className]
  · exact ⟨datetimeNewPy_nohdr b _ _ _ _ _ _ _ _ hn, datetimeNewC_nohdr b _ hn⟩

end PyLean.Datetime
