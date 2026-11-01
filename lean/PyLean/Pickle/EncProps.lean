import PyLean.Pickle.BatchProps

/-!
`pickle.dumps` (C) vs `pickle._dumps` (Python): layered byte-equality claims.
Each layer excludes exactly the inputs of the refutation before it.
-/

namespace PyLean.Pickle

open PyLean

/-- For every plain value and every `protocol` argument, the C and Python
picklers produce the same bytes (or raise the same exception). Source: twin
agreement (`pickle.py` falls back to `_Pickler` when `_pickle` is missing). -/
def DumpsTwinsAgree : Prop := ∀ (x : PV) (protocol : Int), cDumps x protocol = pyDumps x protocol

/-- A list of 1001 items: the C pickler writes the last batch of one item as
`MARK item APPENDS`, the Python pickler as `item APPEND`
(python/cpython#135573, fixed on main). -/
theorem dumpsTwinsAgree_refuted : ¬ DumpsTwinsAgree := by
  intro h
  have := h (noneList 1001) 2
  rw [cDumps_witness, pyDumps_witness] at this
  have h2 := List.append_cancel_left (Except.ok.inj this)
  revert h2
  decide

mutual
/-- The batch shapes where the twins differ (see the refutation and
`cAppends`/`cSetitems`/`cAdditems`): a list (including the list that
protocols < 4 build for a set or frozenset) of `n > 1` items with
`n % 1000 = 1`; a dict of `n > 1` items with `n % 1000 ∈ {0, 1}`; a protocol
4+ set of `n > 0` items with `n % 1000 = 0`. `BatchOk proto x` holds when no
such container occurs in `x`. -/
def BatchOk (proto : Nat) : PV → Prop
  | .tuple _ xs => BatchOkList proto xs
  | .list _ xs => ¬ (proto ≥ 1 ∧ xs.length > 1 ∧ xs.length % 1000 = 1) ∧ BatchOkList proto xs
  | .dict _ kvs => ¬ (proto ≥ 1 ∧ kvs.length > 1 ∧ (kvs.length % 1000 = 1 ∨ kvs.length % 1000 = 0)) ∧
      BatchOkPairs proto kvs
  | .set _ xs =>
      (if proto ≥ 4 then ¬ (xs.length > 0 ∧ xs.length % 1000 = 0)
       else ¬ (proto ≥ 1 ∧ xs.length > 1 ∧ xs.length % 1000 = 1)) ∧ BatchOkList proto xs
  | .frozenset _ xs =>
      (proto < 4 → ¬ (proto ≥ 1 ∧ xs.length > 1 ∧ xs.length % 1000 = 1)) ∧ BatchOkList proto xs
  | _ => True
def BatchOkList (proto : Nat) : List PV → Prop
  | [] => True
  | x :: xs => BatchOk proto x ∧ BatchOkList proto xs
def BatchOkPairs (proto : Nat) : List (PV × PV) → Prop
  | [] => True
  | (k, v) :: kvs => BatchOk proto k ∧ BatchOk proto v ∧ BatchOkPairs proto kvs
end

/-- `DumpsTwinsAgree` for values without those batch shapes. -/
def DumpsTwinsAgreeBatchOk : Prop :=
  ∀ (x : PV) (protocol : Int), (∀ p : Nat, (p : Int) = protocol → BatchOk p x) →
    cDumps x protocol = pyDumps x protocol

/-- `protocol=-2**63-1`: `_Pickler_SetProtocol` calls `PyLong_AsLong` and
raises `OverflowError`; `_Pickler.__init__` maps every negative protocol to the
highest one. -/
theorem dumpsTwinsAgreeBatchOk_refuted : ¬ DumpsTwinsAgreeBatchOk := by
  intro h
  have := h .none (-(2 ^ 63) - 1) (by intro p hp; omega)
  revert this
  decide +kernel

/-- `DumpsTwinsAgreeBatchOk` for `protocol` within C `long`. -/
def DumpsTwinsAgreeBatchOkLong : Prop :=
  ∀ (x : PV) (protocol : Int), longMin ≤ protocol → protocol ≤ longMax →
    (∀ p : Nat, (p : Int) = protocol → BatchOk p x) → cDumps x protocol = pyDumps x protocol

theorem cSaveBytesData_big (o : Oid) (b : Bytes) (hb : b.length = 2 ^ 32) :
    cSaveBytesData 3 o b = throw (.overflowError
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
  have hp : cProtocol 3 = .ok 3 := by decide
  unfold cDumps
  rw [hp]
  simp only [bind, Except.bind]
  simp only [cSave, cSaveBytesObj, cSaveBytesData_big _ b hb]
  rfl

theorem pyDumps_big_bytes (b : Bytes) (hb : b.length = 2 ^ 32) :
    pyDumps (.bytes (.u 0) b) 3 = .error (structError "'I' format requires 0 <= number <= 4294967295") := by
  have hp : pyProtocol 3 = .ok 3 := by decide
  unfold pyDumps
  rw [hp]
  simp only [bind, Except.bind]
  simp only [pySave, pySaveBytesObj, pySaveBytesData_big b hb]
  rfl

/-- `pickle.dumps(bytes(2**32), 3)`: C raises `OverflowError` with an
explanation; `pickle._dumps` raises `struct.error` from `pack("<I", n)`. -/
theorem dumpsTwinsAgreeBatchOkLong_refuted : ¬ DumpsTwinsAgreeBatchOkLong := by
  intro h
  obtain ⟨b, hb⟩ : ∃ b : Bytes, b.length = 2 ^ 32 := ⟨List.replicate _ 0, List.length_replicate⟩
  have := h (.bytes (.u 0) b) 3 (by decide) (by decide) (by intro p _; simp [BatchOk])
  rw [cDumps_big_bytes b hb, pyDumps_big_bytes b hb] at this
  simp [structError] at this

end PyLean.Pickle
