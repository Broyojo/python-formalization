import PyLean.Pickle.Enc

/-!
`pickle.dumps` (C) vs `pickle._dumps` (Python): layered byte-equality claims.
Each layer excludes exactly the inputs of the refutation before it. Since
gh-144162 the C batch loops write what Python's `batched` loops write, so no
batch size needs excluding; `EncSim` proves that for every size.
-/

namespace PyLean.Pickle

open PyLean

theorem bind_run {m : EncM Unit} {k : Unit → EncM Unit} {s s' : EncSt} (h : m s = .ok ((), s')) :
    (m >>= k) s = k () s' := by
  show (StateT.bind m k) s = _
  simp only [StateT.bind, bind, Except.bind, h]

/-- For every plain value and every `protocol` argument, the C and Python
picklers produce the same bytes (or raise the same exception). Source: twin
agreement (`pickle.py` falls back to `_Pickler` when `_pickle` is missing). -/
def DumpsTwinsAgree : Prop := ∀ (x : PV) (protocol : Int), cDumps x protocol = pyDumps x protocol

/-- `protocol=-2**63-1`: `_Pickler_SetProtocol` calls `PyLong_AsLong` and
raises `OverflowError`; `_Pickler.__init__` maps every negative protocol to the
highest one. -/
theorem dumpsTwinsAgree_refuted : ¬ DumpsTwinsAgree := by
  intro h
  have := h .none (-(2 ^ 63) - 1)
  revert this
  decide +kernel

/-- The protocol a `protocol` argument selects: negative means the highest. -/
def effProto (protocol : Int) : Nat := if protocol < 0 then 5 else protocol.toNat

/-- `DumpsTwinsAgree` for `protocol` within C `long`. -/
def DumpsTwinsAgreeLong : Prop :=
  ∀ (x : PV) (protocol : Int), longMin ≤ protocol → protocol ≤ longMax →
    cDumps x protocol = pyDumps x protocol

theorem cSaveBytesData_big (b : Bytes) (hb : b.length = 2 ^ 32) :
    cSaveBytesData 3 b = throw (.overflowError
      "serializing a bytes object larger than 4 GiB requires pickle protocol 4 or higher") := by
  unfold cSaveBytesData
  simp only [hb]
  rfl

theorem pySaveBytesData_big (b : Bytes) (hb : b.length = 2 ^ 32) :
    pySaveBytesData 3 b = throw (structError "'I' format requires 0 <= number <= 4294967295") := by
  unfold pySaveBytesData
  simp only [hb]
  rfl

theorem cDumps_big_bytes (b : Bytes) (hb : b.length = 2 ^ 32) :
    cDumps (.bytes (.u 0) b) 3 = .error (.overflowError
      "serializing a bytes object larger than 4 GiB requires pickle protocol 4 or higher") := by
  have hp : cProtocol 3 = .ok 3 := rfl
  have hbody : cBody 3 (.bytes (.u 0) b) {} = .error (.overflowError
      "serializing a bytes object larger than 4 GiB requires pickle protocol 4 or higher") := by
    simp only [cBody, cSave, cSaveBytesObj, cSaveBytesData_big b hb]
    rfl
  unfold cDumps
  simp only [hp, bind, Except.bind, StateT.run, hbody]

theorem pyDumps_big_bytes (b : Bytes) (hb : b.length = 2 ^ 32) :
    pyDumps (.bytes (.u 0) b) 3 = .error (structError "'I' format requires 0 <= number <= 4294967295") := by
  have hp : pyProtocol 3 = .ok 3 := rfl
  have hbody : pyBody 3 (.bytes (.u 0) b) {} =
      .error (structError "'I' format requires 0 <= number <= 4294967295") := by
    simp only [pyBody, pySave, pySaveBytesObj, pySaveBytesData_big b hb]
    rfl
  unfold pyDumps
  simp only [hp, bind, Except.bind, StateT.run, hbody]

/-- `pickle.dumps(bytes(2**32), 3)`: C raises `OverflowError` with an
explanation; `pickle._dumps` raises `struct.error` from `pack("<I", n)`. -/
theorem dumpsTwinsAgreeLong_refuted : ¬ DumpsTwinsAgreeLong := by
  intro h
  obtain ⟨b, hb⟩ : ∃ b : Bytes, b.length = 2 ^ 32 := ⟨List.replicate _ 0, List.length_replicate⟩
  have := h (.bytes (.u 0) b) 3 (by decide) (by decide)
  rw [cDumps_big_bytes b hb, pyDumps_big_bytes b hb] at this
  simp [structError] at this

end PyLean.Pickle
