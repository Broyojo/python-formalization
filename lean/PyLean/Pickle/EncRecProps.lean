import PyLean.Pickle.EncRecExact
import PyLean.Pickle.EncFrame
import PyLean.Binary64.Props2

/-!
`pickle.dumps` (C, `c` levels of stack room) vs `pickle._dumps` (Python, `b` frames left where it
is called), on the mirrors of `EncRec.lean`.

* `DumpsTwinsRec`: for every room and frame budget the twins agree. Refuted: a list in a list
  with 5 frames left; at the default limit of 1000, lists about 330 deep (probe).
Scope: the Python mirror has no codec registry; it is the interpreter whose raw-unicode-escape
codec is already cached. On a fresh interpreter the first protocol 0 `str` costs about 9 more
frames (`encodings.search_function`, importlib) until the codec is cached, so the frame bounds
below are false there (probe: `bytearray(b'z')` at protocol 0 needs 25 frames).

* `DumpsTwinsNarrow`: with `4 * dep x + 4` levels of room and `10 * dep x + 18` frames, the
  twins agree on every plain value whose ints pass C's LONG4 size check, for `protocol` None or an
  int within C long, with or without `buffer_callback`.
* `DumpsTwinsNoRec`: the same for every room and budget under which neither raises its
  `RecursionError`.
* `DumpsTwinsProtocol`: also for float protocols. Refuted: `protocol=2.5` is a TypeError in C,
  protocol 2 in Python.
-/

namespace PyLean.Pickle

open PyLean PyLean.Binary64

/-! ## Bridges to `Enc.lean` -/

theorem encRun_lift {α : Type} (f : List Event → Bytes) (a : Py α) (k : α → EncM Unit) :
    encRun f (liftPyA a >>= k) = (match a with | .ok v => encRun f (k v) | .error e => .error e) := by
  cases a <;> rfl

theorem approx_run {r : PyExc} {m m' : EncM Unit} (f : List Event → Bytes) (h : Approx r m m') :
    encRun f m = encRun f m' ∨ encRun f m = .error r := by
  rcases h {} with h | h
  · left; unfold encRun; simp only [StateT.run, h]
  · right; unfold encRun; simp only [StateT.run, h]; rfl

/-- The frames-free `pickle.dumps` with the argument checks. -/
def cDumpsU (x : PV) (a : DumpsArgs) : Py Bytes :=
  encRun cFrame (do let p ← liftPyA (cProtocolA a.protocol); liftPyA (cBufCheck a.bufcb p); cBody p x)

def pyDumpsU (x : PV) (a : DumpsArgs) : Py Bytes :=
  encRun pyFrame (liftPyA (pyProtocolA a) >>= fun p => pyBody p x)

theorem cDumpsA_approx (c : Nat) (x : PV) (a : DumpsArgs) :
    cDumpsA c x a = cDumpsU x a ∨ cDumpsA c x a = .error recC :=
  approx_run cFrame (approx_bind (approx_refl _) fun _ => approx_bind (approx_refl _) fun _ => ac_body _ _ _)

/-- `_Pickler.__init__` with its `_Framer.__init__` frame. -/
theorem init_approx (a : DumpsArgs) (b2 : Nat) :
    Approx recPy (do let p ← liftPyA (pyProtocolA a); pyCall b2 (fun _ => pure ()); pure p)
      (liftPyA (pyProtocolA a)) := by
  intro s
  cases pyProtocolA a with
  | error e => exact .inl rfl
  | ok v =>
    unfold pyCall
    by_cases hb : b2 = 0
    · right; simp only [hb, if_true]; rfl
    · left; simp only [hb, if_false]; rfl

theorem init_exact (a : DumpsArgs) {b2 : Nat} (hb : 1 ≤ b2) :
    (do let p ← liftPyA (pyProtocolA a); pyCall b2 (fun _ => pure ()); pure p) = liftPyA (pyProtocolA a) := by
  cases pyProtocolA a with
  | error e => rfl
  | ok v =>
    unfold pyCall
    simp only [show ¬ b2 = 0 from by omega, if_false]
    rfl

theorem pyDumpsA_approx (b : Nat) (x : PV) (a : DumpsArgs) :
    pyDumpsA b x a = pyDumpsU x a ∨ pyDumpsA b x a = .error recPy :=
  approx_run pyFrame (approx_pyCall fun _ => approx_bind (approx_pyCall fun _ => init_approx a _) fun _ =>
    approx_pyCall fun _ => ap_body _ _ _)

theorem cDumpsA_exact {c : Nat} (x : PV) (a : DumpsArgs) (hc : 4 * x.dep + 4 ≤ c) :
    cDumpsA c x a = cDumpsU x a := by
  unfold cDumpsA cDumpsM cDumpsU
  simp only [xc_body _ x hc]

theorem pyDumpsA_exact {b : Nat} (x : PV) (a : DumpsArgs) (hb : 10 * x.dep + 18 ≤ b) :
    pyDumpsA b x a = pyDumpsU x a := by
  unfold pyDumpsA pyDumpsM pyDumpsU
  congr 1
  exact eq_pyCall (by omega) (eq_bind (eq_pyCall (by omega) (init_exact a (by omega))) fun p =>
    eq_pyCall (by omega) (ex_body p x (by omega)))

theorem cDumps_eq (x : PV) (i : Int) :
    cDumps x i = (match cProtocol i with | .ok p => encRun cFrame (cBody p x) | .error e => .error e) := by
  unfold cDumps; cases cProtocol i <;> rfl

theorem pyDumps_eq (x : PV) (i : Int) :
    pyDumps x i = (match pyProtocol i with | .ok p => encRun pyFrame (pyBody p x) | .error e => .error e) := by
  unfold pyDumps; cases pyProtocol i <;> rfl

/-- `protocol` is `None` or an int within C `long`. -/
def ProtoOk : ProtoArg → Prop
  | .none => True
  | .int i => longMin ≤ i ∧ i ≤ longMax
  | _ => False

/-- The frames-free twins with argument checks agree on the protocols of `ProtoOk`. -/
theorem dumpsU_same (x : PV) (a : DumpsArgs) (hp : ProtoOk a.protocol) (hi : IntsOk x) :
    SameOutcome (cDumpsU x a) (pyDumpsU x a) := by
  obtain ⟨pa, bufcb⟩ := a
  unfold cDumpsU pyDumpsU
  rw [encRun_lift, encRun_lift]
  cases pa with
  | none =>
    simp only [cProtocolA, pyProtocolA]
    have h5 := dumpsTwinsFree_proven x 5 (by decide) (by decide) hi
    rw [cDumps_eq, pyDumps_eq] at h5
    have e1 : cProtocol 5 = .ok 5 := by decide
    have e2 : pyProtocol 5 = .ok 5 := by decide
    rw [e1, e2] at h5
    simp only [show ¬ (bufcb = true ∧ 5 < 5) from by omega, if_false, cBufCheck]
    rw [encRun_lift]
    exact h5
  | int i =>
    simp only [ProtoOk] at hp
    have h5 := dumpsTwinsFree_proven x i hp.1 hp.2 hi
    rw [cDumps_eq, pyDumps_eq] at h5
    simp only [cProtocolA, pyProtocolA]
    unfold cProtocol at h5 ⊢
    unfold pyProtocol at h5
    rw [if_neg (show ¬ (i < longMin ∨ i > longMax) by have := hp.1; have := hp.2; simp only [longMin, longMax] at *; omega)] at h5 ⊢
    by_cases hn : i < 0
    · rw [if_pos hn, if_pos hn] at h5
      rw [if_pos hn, if_pos hn, if_neg (show ¬ (bufcb = true ∧ 5 < 5) by omega)]
      dsimp only
      rw [encRun_lift]
      unfold cBufCheck
      rw [if_neg (show ¬ (bufcb = true ∧ 5 < 5) by omega)]
      exact h5
    rw [if_neg hn, if_neg hn] at h5
    rw [if_neg hn, if_neg hn]
    by_cases h6 : i > 5
    · rw [if_pos h6, if_pos (show ¬ (0 ≤ i ∧ i ≤ 5) by omega)]; trivial
    rw [if_neg h6] at h5
    rw [if_pos (show i ≤ 5 by omega)] at h5
    rw [if_neg h6, if_neg (show ¬¬ (0 ≤ i ∧ i ≤ 5) by omega)]
    dsimp only
    rw [encRun_lift]
    unfold cBufCheck
    by_cases hb : bufcb = true ∧ i < 5
    · rw [if_pos (show bufcb = true ∧ i.toNat < 5 from ⟨hb.1, by omega⟩), if_pos hb]
      trivial
    · rw [if_neg (show ¬ (bufcb = true ∧ i.toNat < 5) from fun h => hb ⟨h.1, by omega⟩), if_neg hb]
      exact h5
  | float f => exact hp.elim
  | other t => exact hp.elim

/-! ## The recursion limits -/

/-- For every stack room and frame budget, `pickle.dumps` and `pickle._dumps` both raise or
return the same bytes, on the values and protocols of `DumpsTwinsNarrow`. -/
def DumpsTwinsRec : Prop :=
  ∀ (x : PV) (a : DumpsArgs) (c b : Nat), ProtoOk a.protocol → IntsOk x →
    SameOutcome (cDumpsA c x a) (pyDumpsA b x a)

/-- `[[]]`. -/
def wNest : PV := .list (.u 0) [.list (.u 1) []]

/-- `[[]]` with 100 levels of room and 5 frames: C pickles it; Python runs out in `memoize`
(`_dumps`, `dump`, `save`, `save_list`, `memoize`, `put`). At the default recursion limit,
`pickle._dumps` of lists about 330 deep raises `RecursionError` while `pickle.dumps` pickles
lists 100000 deep (probe). -/
theorem dumpsTwinsRec_refuted : ¬ DumpsTwinsRec := by
  intro h
  have h1 := h wNest {} 100 5 trivial (by simp [wNest, IntsOk, IntsOkList])
  have hp : pyDumpsA 5 wNest {} = .error recPy := by decide +kernel
  have hc : (cDumpsA 100 wNest {}).isOk = true := by decide +kernel
  rw [hp] at h1
  revert hc h1
  cases cDumpsA 100 wNest {} <;> simp [SameOutcome, Except.isOk, Except.toBool]

/-- With `4 * dep x + 4` levels of C stack room and `10 * dep x + 18` Python frames left where
`pickle._dumps` is called, for every plain value whose ints pass C's LONG4 size check, `protocol`
None or an int within C long, and either `buffer_callback`: `pickle.dumps` and `pickle._dumps`
both raise, or both return the same bytes. Each hypothesis is one refutation:
`pickle-dumps-twins-rec`, `pickle-save-long-twins`, `pickle-dumps-twins` and
`pickle-dumps-protocol-float`. -/
def DumpsTwinsNarrow : Prop :=
  ∀ (x : PV) (a : DumpsArgs) (c b : Nat), ProtoOk a.protocol → IntsOk x →
    4 * x.dep + 4 ≤ c → 10 * x.dep + 18 ≤ b →
    SameOutcome (cDumpsA c x a) (pyDumpsA b x a)

theorem dumpsTwinsNarrow_proven : DumpsTwinsNarrow := by
  intro x a c b hp hi hc hb
  rw [cDumpsA_exact x a hc, pyDumpsA_exact x a hb]
  exact dumpsU_same x a hp hi

/-- The same for every room and frame budget under which neither twin raises its
`RecursionError`. -/
def DumpsTwinsNoRec : Prop :=
  ∀ (x : PV) (a : DumpsArgs) (c b : Nat), ProtoOk a.protocol → IntsOk x →
    cDumpsA c x a ≠ .error recC → pyDumpsA b x a ≠ .error recPy →
    SameOutcome (cDumpsA c x a) (pyDumpsA b x a)

theorem dumpsTwinsNoRec_proven : DumpsTwinsNoRec := by
  intro x a c b hp hi hc hb
  rcases cDumpsA_approx c x a with h1 | h1
  · rcases pyDumpsA_approx b x a with h2 | h2
    · rw [h1, h2]; exact dumpsU_same x a hp hi
    · exact absurd h2 hb
  · exact absurd h1 hc

/-! ## The protocol argument -/

/-- `DumpsTwinsNarrow` for every `protocol` object of `ProtoArg`. -/
def DumpsTwinsProtocol : Prop :=
  ∀ (x : PV) (a : DumpsArgs) (c b : Nat), IntsOk x →
    4 * x.dep + 4 ≤ c → 10 * x.dep + 18 ≤ b →
    SameOutcome (cDumpsA c x a) (pyDumpsA b x a)

/-- `2.5`. -/
def f25 : F64 := F64.ofBits 0x4004000000000000

theorem f25_fin : f25.isFinite = true := by decide
theorem f25_rat : f25.toRat = 5 / 2 := by decide +kernel

/-- `_Pickler.__init__` with `protocol=2.5`: `2.5 < 0` and `0 <= 2.5 <= 5` compare exactly,
`int(2.5)` is 2. -/
theorem pyProtocolA_f25 : pyProtocolA { protocol := .float f25 } = .ok 2 := by
  obtain ⟨h0f, h0r⟩ := ofInt_small (n := 0) (by decide)
  obtain ⟨h5f, h5r⟩ := ofInt_small (n := 5) (by decide)
  have hlt0 : F64.lt f25 (F64.ofInt 0) = false := by
    rw [lt_of_finite f25_fin h0f, f25_rat, h0r]; decide +kernel
  have hle0 : F64.le (F64.ofInt 0) f25 = true := by
    unfold F64.le; rw [lt_of_finite h0f f25_fin, f25_rat, h0r]; decide +kernel
  have hle5 : F64.le f25 (F64.ofInt 5) = true := by
    unfold F64.le; rw [lt_of_finite f25_fin h5f, f25_rat, h5r]; decide +kernel
  have htr : f25.truncInt = 2 := by
    unfold F64.truncInt F64.floorInt F64.ceilInt
    rw [f25_rat]
    have hs : f25.sign = false := by decide
    rw [hs]; decide +kernel
  unfold pyProtocolA
  simp only [hlt0, hle0, hle5, htr, Bool.false_eq_true, if_false, and_self, not_true_eq_false, false_and]
  rfl

/-- `pickle.dumps(None, 2.5)`: `PyLong_AsLong` raises TypeError; `_Pickler.__init__` compares
2.5 with 0 and 5, then takes `int(2.5)`, and `pickle._dumps` returns `b'\x80\x02N.'`. -/
def a25 : DumpsArgs := { protocol := .float f25 }

set_option maxRecDepth 20000 in
theorem dumpsTwinsProtocol_refuted : ¬ DumpsTwinsProtocol := by
  intro h
  have hi : IntsOk PV.none := True.intro
  have hc4 : 4 * PV.none.dep + 4 ≤ 4 := by decide
  have hb18 : 10 * PV.none.dep + 18 ≤ 18 := by decide
  have h1 := h PV.none a25 4 18 hi hc4 hb18
  rw [cDumpsA_exact _ _ hc4, pyDumpsA_exact _ _ hb18] at h1
  have hp : pyDumpsU .none a25 = encRun pyFrame (pyBody 2 .none) := by
    unfold pyDumpsU a25; rw [encRun_lift, pyProtocolA_f25]
  have hc : cDumpsU .none a25 = .error (.typeError "'float' object cannot be interpreted as an integer") := rfl
  have hb : encRun pyFrame (pyBody 2 .none) = .ok [oPROTO, 2, oNONE, oSTOP] := by decide +kernel
  rw [hp, hb, hc] at h1
  exact h1

/-! ## The earlier twin statements on the bounded mirrors -/

/-- For every value, int `protocol`, stack room and frame budget, the twins return the same
bytes or raise the same exception. -/
def DumpsTwinsAgreeR : Prop :=
  ∀ (x : PV) (protocol : Int) (c b : Nat),
    cDumpsA c x { protocol := .int protocol } = pyDumpsA b x { protocol := .int protocol }

theorem dumpsU_int (x : PV) (i : Int) (hl : longMin ≤ i ∧ i ≤ longMax) :
    cDumpsU x { protocol := .int i } = cDumps x i := by
  unfold cDumpsU
  rw [encRun_lift, cDumps_eq]
  simp only [cProtocolA]
  cases cProtocol i with
  | error e => rfl
  | ok p => simp only [cBufCheck, Bool.false_eq_true, false_and, if_false]; rfl

theorem pyDumpsU_int (x : PV) (i : Int) : pyDumpsU x { protocol := .int i } = pyDumps x i := by
  unfold pyDumpsU
  rw [encRun_lift, pyDumps_eq]
  simp only [pyProtocolA, pyProtocol, Bool.false_eq_true, false_and]
  by_cases hn : i < 0
  · rw [if_pos hn, if_pos hn, if_neg (fun h => h)]
  · rw [if_neg hn, if_neg hn]
    by_cases h5 : i ≤ 5
    · rw [if_pos h5, if_neg (show ¬¬ (0 ≤ i ∧ i ≤ 5) by omega), if_neg (fun h => h)]
    · rw [if_neg h5, if_pos (show ¬ (0 ≤ i ∧ i ≤ 5) by omega)]

/-- `protocol=-2**63-1`, as `dumpsTwinsAgree_refuted`: OverflowError in C, the highest protocol
in Python. -/
theorem dumpsTwinsAgreeR_refuted : ¬ DumpsTwinsAgreeR := by
  intro h
  have h1 := h .none (-(2 ^ 63) - 1) 4 18
  have hc : cDumpsA 4 .none { protocol := .int (-(2 ^ 63) - 1) } =
      .error (.overflowError "Python int too large to convert to C long") := by decide +kernel
  have hp : pyDumpsA 18 .none { protocol := .int (-(2 ^ 63) - 1) } = .ok [oPROTO, 5, oNONE, oSTOP] := by
    decide +kernel
  rw [hc, hp] at h1
  cases h1

/-- `DumpsTwinsAgreeR` for protocols within C long. -/
def DumpsTwinsAgreeLongR : Prop :=
  ∀ (x : PV) (protocol : Int) (c b : Nat), longMin ≤ protocol → protocol ≤ longMax →
    cDumpsA c x { protocol := .int protocol } = pyDumpsA b x { protocol := .int protocol }

/-- `bytes(2**32)` at protocol 3, as `dumpsTwinsAgreeLong_refuted`: OverflowError in C,
struct.error in Python. -/
theorem dumpsTwinsAgreeLongR_refuted : ¬ DumpsTwinsAgreeLongR := by
  intro h
  obtain ⟨d, hd⟩ : ∃ d : Bytes, d.length = 2 ^ 32 := ⟨List.replicate _ 0, List.length_replicate⟩
  have h1 := h (.bytes (.u 0) d) 3 4 18 (by decide) (by decide)
  rw [cDumpsA_exact _ _ (by simp [PV.dep]), pyDumpsA_exact _ _ (by simp [PV.dep]),
    dumpsU_int _ _ (by decide), pyDumpsU_int, cDumps_big_bytes d hd, pyDumps_big_bytes d hd] at h1
  simp [structError] at h1

end PyLean.Pickle
