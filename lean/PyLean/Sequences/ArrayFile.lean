import PyLean.Sequences.ArrayBytes

/-!
`array.fromfile` and `array.tofile` (`Modules/arraymodule.c:1745-1840`, CPython 3.15.2), with
the file's `read` and `write` as callbacks that may raise and change the array.
-/

namespace PyLean.Sequences

open PyLean

/-- An exception that is the model's report of C undefined behaviour, not a Python outcome. -/
def isCUB (e : PyExc) : Bool := e.className == "CUndefinedBehaviour"

/-! ### `frombytes` on any bytes -/

theorem length_chunks (k : Nat) (hk : 0 < k) :
    ∀ (fuel q : Nat) (bs : List Nat), bs.length ≤ fuel → bs.length = q * k →
      (chunks k bs fuel).length = q
  | 0, q, bs, h, hq => by
    have : bs.length = 0 := by omega
    have : q = 0 := by
      rcases Nat.eq_zero_or_pos q with h0 | h0
      · exact h0
      · have := Nat.mul_le_mul_right k h0; omega
    simp [chunks, *]
  | fuel + 1, q, bs, h, hq => by
    unfold chunks
    by_cases he : bs.isEmpty
    · have h0 : bs = [] := List.isEmpty_iff.mp he
      subst h0
      have : q = 0 := by
        rcases Nat.eq_zero_or_pos q with h0 | h0
        · exact h0
        · have := Nat.mul_le_mul_right k h0; simp at hq; omega
      simp [this]
    · simp only [he, Bool.false_eq_true, if_false, List.length_cons]
      have hl : bs.length ≠ 0 := by simpa [List.isEmpty_iff, List.length_eq_zero_iff] using he
      have hq1 : 1 ≤ q := by
        rcases Nat.eq_zero_or_pos q with h0 | h0
        · rw [h0] at hq; omega
        · exact h0
      have hd : (bs.drop k).length = (q - 1) * k := by
        simp only [List.length_drop, hq, Nat.sub_one_mul]
      have hsub : (q - 1) * k = q * k - k := Nat.sub_one_mul q k
      have hkq : k ≤ q * k := by have := Nat.mul_le_mul_right k hq1; omega
      rw [length_chunks k hk fuel (q - 1) (bs.drop k) (by rw [hd, hsub]; omega) hd]
      omega

/-- `a.frombytes(bs)` of any bytes: `ValueError` for a length that is not a multiple of the item
size, otherwise the decoded items appended (no buffer exported, the result fits). -/
theorem arrFromBytes_ok (a : Arr) (bs : List Nat) (hx : a.exports = 0)
    (hm : (bs.length : Int) % a.tc.itemsize = 0)
    (hf : a.Fits (a.items.length + (bs.length : Int) / a.tc.itemsize)) :
    ∃ a', arrFromBytes a bs 1 = .ok a' ∧
      a'.items = a.items ++ (chunks a.tc.itemsize.toNat bs bs.length).map (itemOfBytes a.tc) ∧
      a'.tc = a.tc ∧ a'.exports = 0 := by
  have hsz := itemsize_cases a.tc
  have hpos : 0 < a.tc.itemsize.toNat := by rcases hsz with h | h | h | h | h <;> rw [h] <;> decide
  have hcast : ((a.tc.itemsize.toNat : Nat) : Int) = a.tc.itemsize := by
    rcases hsz with h | h | h | h | h <;> rw [h] <;> rfl
  have hmN : bs.length % a.tc.itemsize.toNat = 0 := by
    have : ((bs.length % a.tc.itemsize.toNat : Nat) : Int) = 0 := by
      rw [Int.natCast_emod, hcast]; exact hm
    omega
  have hlenc := length_chunks a.tc.itemsize.toNat hpos bs.length (bs.length / a.tc.itemsize.toNat) bs
    (Nat.le_refl _) (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmN)).symm
  have hq : (bs.length : Int) / a.tc.itemsize = ((bs.length / a.tc.itemsize.toNat : Nat) : Int) := by
    rw [Int.natCast_ediv, hcast]
  by_cases h0 : bs.length = 0
  · have : bs = [] := List.eq_nil_of_length_eq_zero h0
    subst this
    refine ⟨a, ?_, by simp [chunks], rfl, hx⟩
    simp [arrFromBytes, bind, Except.bind, pure, Except.pure]
  · have hdv := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmN)
    have hk : bs.length / a.tc.itemsize.toNat > 0 := by
      rcases Nat.eq_zero_or_pos (bs.length / a.tc.itemsize.toNat) with h1 | h1
      · rw [h1] at hdv; omega
      · exact h1
    obtain ⟨a1, hr, hi, ht, hx1⟩ := arrResize_ok a (a.items.length + (bs.length / a.tc.itemsize.toNat : Nat))
      hx (by omega) (by rw [← hq]; exact hf)
    have hres : a1.items = a.items ++ List.replicate (bs.length / a.tc.itemsize.toNat) 0 := by
      rw [hi]; exact resized_grow _ _ hk
    let src := (chunks a.tc.itemsize.toNat bs bs.length).map (itemOfBytes a.tc)
    refine ⟨{ a1 with items := memcpy a1.items a.items.length src }, ?_, ?_, ht, hx1.1⟩
    · unfold arrFromBytes
      simp only [bind, Except.bind, pure, Except.pure, throwE, show ¬ ((1 : Int) ≠ 1) by decide, ite_false]
      rw [iteF (show ¬ ((bs.length : Int) % a.tc.itemsize ≠ 0) by rw [hm]; decide), hq, iteT (by omega)]
      have hsm : ¬ (((bs.length / a.tc.itemsize.toNat : Nat) : Int) > ssizeMax - a.items.length ∨
          (a.items.length : Int) + ((bs.length / a.tc.itemsize.toNat : Nat) : Int) > ssizeMax / a.tc.itemsize) := by
        unfold Arr.Fits at hf
        rw [hq] at hf
        have : ssizeMax / a.tc.itemsize ≤ ssizeMax := Int.ediv_le_self _ (by unfold ssizeMax; omega)
        omega
      rw [iteF hsm, hr]
    · show memcpy a1.items _ _ = _
      rw [hres]
      have := memcpy_end a.items ((chunks a.tc.itemsize.toNat bs bs.length).map (itemOfBytes a.tc))
      rw [List.length_map, hlenc] at this
      exact this

/-! ### `fromfile` -/

/-- A file whose `read(n)` returns its next `n` bytes, or fewer at the end, and does nothing
else (an `io.BytesIO` holding `bs`). -/
def fileRead (bs : List Nat) : ReadFn := fun n a => (.bytes (bs.take n.toNat), a)

def eofErr : PyExc := .named "EOFError" "read() didn't return enough bytes"

/-- The items `frombytes` decodes from `bs`. -/
def decodedItems (tc : TC) (bs : List Nat) : List Int := (chunks tc.itemsize.toNat bs bs.length).map (itemOfBytes tc)

/-- Doc/library/array.rst:208-213: "Read *n* items (as machine values) from the file object *f*
and append them to the end of the array. If less than *n* items are available, `EOFError` is
raised, but the items that were available are still inserted into the array." For a plain file
holding `bs`, of which `k` whole items are available.

Refuted: when the file ends inside an item, `read` returns a length that is not a multiple of
the item size, `frombytes` raises `ValueError` (arraymodule.c:1778, 1924-1929), and none of the
available items is inserted; the bytes are consumed from the file all the same. -/
def ArrayFromFileDoc : Prop :=
  ∀ (a : Arr) (bs : List Nat) (n : Nat), a.exports = 0 → a.Fits (a.items.length + n) →
    let isz := a.tc.itemsize.toNat
    let k := bs.length / isz
    let r := arrFromFile a (fileRead bs) (.int n)
    (n ≤ k → r.1 = .ok () ∧ r.2.1.items = a.items ++ decodedItems a.tc (bs.take (n * isz))) ∧
    (k < n → r.1 = .error eofErr ∧ r.2.1.items = a.items ++ decodedItems a.tc (bs.take (k * isz)))

theorem arrayFromFileDoc_refuted : ¬ ArrayFromFileDoc := by
  intro h
  have := (h ⟨.i, [], 0, false, 0, "array"⟩ [1, 0, 0, 0, 2, 0] 2 rfl (by unfold Arr.Fits; decide)).2 (by decide)
  revert this
  decide +kernel

/-- `a.fromfile(f, n)` exactly, for every file object, its `read` a callback that may raise,
return any object, or change the array:
* `n` goes through `_PyNumber_Index` and `PyLong_AsSsize_t` and must not be negative; a refused
  `n` raises before `read` is called, and so does an `n` whose byte count passes
  `PY_SSIZE_T_MAX` (`MemoryError`, :1754-1757);
* `read(n * itemsize)` is called once; its exception propagates, a result that is not `bytes`
  (or a subclass) raises `TypeError`;
* exact `bytes` whose length is not a multiple of the item size raise `ValueError` and append
  nothing; otherwise every item they hold is appended, to the array as `read` left it, and
  `EOFError` is raised afterwards unless exactly `n` items came, also when `read` returned more
  bytes than asked for (the check is `!=`, :1776);
* when `read` left a buffer of the array exported, a non-empty result raises `BufferError`
  after the bytes were read;
* for an instance of a `bytes` subclass (`ArrayFromFileSub`) the two reads of `b` differ: the
  `EOFError` test uses its length (`PyBytes_GET_SIZE`), the items come from its buffer
  (`PyObject_GetBuffer`, through a `__buffer__` the class may define): a `__buffer__` that raises
  propagates, a buffer of item size other than 1 raises `TypeError`, and otherwise the buffer's
  items are appended, whatever the length says; the buffer is then released, which runs a
  `__release_buffer__` the class defines and may change the array before `fromfile` returns. -/
def ArrayFromFileBytes : Prop :=
  (∀ n : Int, 0 ≤ n → n ≤ ssizeMax → fromFileCount (.int n) = .ok n) ∧
  (∀ n : Int, n < 0 → ssizeMin ≤ n → fromFileCount (.int n) = .error (.valueError "n cannot be negative")) ∧
  (∀ n : Int, (ssizeMax < n ∨ n < ssizeMin) →
    fromFileCount (.int n) = .error (.overflowError "Python int too large to convert to C ssize_t")) ∧
  (∀ v e, toIndex v = .error e → fromFileCount v = .error e) ∧
  (∀ a read v e, fromFileCount v = .error e → arrFromFile a read v = (.error e, a, [])) ∧
  (∀ a read v n, fromFileCount v = .ok n → arrFromFile a read v = arrFromFileC a read n) ∧
  (∀ a read n, n > ssizeMax / a.tc.itemsize → arrFromFileC a read n = (.error memoryError, a, [])) ∧
  (∀ a read n e a1, n ≤ ssizeMax / a.tc.itemsize → read (n * a.tc.itemsize) a = (.raises e, a1) →
    arrFromFileC a read n = (.error e, a1, [n * a.tc.itemsize])) ∧
  (∀ a read n a1, n ≤ ssizeMax / a.tc.itemsize → read (n * a.tc.itemsize) a = (.notBytes, a1) →
    arrFromFileC a read n = (.error (.typeError "read() didn't return bytes"), a1, [n * a.tc.itemsize])) ∧
  (∀ a read n bs a1, n ≤ ssizeMax / a.tc.itemsize → read (n * a.tc.itemsize) a = (.bytes bs, a1) →
    a1.tc = a.tc → (bs.length : Int) % a.tc.itemsize ≠ 0 →
    arrFromFileC a read n = (.error (.valueError "bytes length not a multiple of item size"), a1, [n * a.tc.itemsize])) ∧
  (∀ a read n bs a1, n ≤ ssizeMax / a.tc.itemsize → read (n * a.tc.itemsize) a = (.bytes bs, a1) →
    a1.exports = 0 → a1.tc = a.tc → (bs.length : Int) % a.tc.itemsize = 0 →
    a1.Fits (a1.items.length + (bs.length : Int) / a.tc.itemsize) →
    ∃ a2, arrFromFileC a read n =
      ((if (bs.length : Int) = n * a.tc.itemsize then .ok () else .error eofErr), a2, [n * a.tc.itemsize]) ∧
      a2.items = a1.items ++ decodedItems a.tc bs) ∧
  (∀ a read n bs a1, n ≤ ssizeMax / a.tc.itemsize → read (n * a.tc.itemsize) a = (.bytes bs, a1) →
    a1.exports > 0 → a1.tc = a.tc → bs ≠ [] → (bs.length : Int) % a.tc.itemsize = 0 →
    a1.Fits (a1.items.length + (bs.length : Int) / a.tc.itemsize) →
    (arrFromFileC a read n).1 = .error bufferErr)

theorem arrayFromFileBytes_proven : ArrayFromFileBytes := by
  have hsz : ∀ tc : TC, 0 < tc.itemsize := fun tc => by
    rcases itemsize_cases tc with h | h | h | h | h <;> rw [h] <;> decide
  refine ⟨fun n h0 h1 => ?_, fun n h0 h1 => ?_, fun n h => ?_, fun v e he => ?_,
    fun a read v e he => ?_, fun a read v n hn => ?_, fun a read n hn => ?_,
    fun a read n e a1 hn hr => ?_, fun a read n a1 hn hr => ?_, fun a read n bs a1 hn hr ht hm => ?_,
    fun a read n bs a1 hn hr hx ht hm hf => ?_, fun a read n bs a1 hn hr hx ht hne hm hf => ?_⟩
  · have hr : ssizeMin ≤ n ∧ n ≤ ssizeMax := ⟨by unfold ssizeMin ssizeMax at *; omega, h1⟩
    have hn : ¬ n < 0 := by omega
    simp only [fromFileCount, toIndex, asSsize, bind, Except.bind, pure, Except.pure, throwE, hr,
      and_self, if_true, hn, if_false]
  · have hr : ssizeMin ≤ n ∧ n ≤ ssizeMax := ⟨h1, by unfold ssizeMax; omega⟩
    simp only [fromFileCount, toIndex, asSsize, bind, Except.bind, pure, Except.pure, throwE, hr,
      and_self, if_true, h0]
  · have hr : ¬ (ssizeMin ≤ n ∧ n ≤ ssizeMax) := by omega
    simp only [fromFileCount, toIndex, asSsize, bind, Except.bind, pure, Except.pure, throwE, hr,
      if_false]
  · simp only [fromFileCount, he, bind, Except.bind]
  · simp only [arrFromFile, he]
  · simp only [arrFromFile, hn]
  · simp only [arrFromFileC]; rw [iteT hn]
  · simp only [arrFromFileC]; rw [iteF (by omega), hr]
  · simp only [arrFromFileC]; rw [iteF (by omega), hr]
  · simp only [arrFromFileC]; rw [iteF (by omega), hr]
    simp only
    have : arrFromBytes a1 bs 1 = .error (.valueError "bytes length not a multiple of item size") := by
      unfold arrFromBytes
      simp only [bind, Except.bind, pure, Except.pure, throwE, show ¬ ((1 : Int) ≠ 1) by decide, ite_false]
      rw [ht, iteT hm]
    rw [this]
  · obtain ⟨a2, h1, h2, _, _⟩ := arrFromBytes_ok a1 bs hx (by rw [ht]; exact hm) (by rw [ht]; exact hf)
    refine ⟨a2, ?_, by rw [h2, ht]; rfl⟩
    simp only [arrFromFileC]; rw [iteF (by omega), hr]
    simp only [h1]
    by_cases hl : (bs.length : Int) = n * a.tc.itemsize
    · rw [iteF (by omega), iteT hl]
    · rw [iteT hl, iteF hl]; rfl
  · simp only [arrFromFileC]; rw [iteF (by omega), hr]
    simp only
    have hk : (bs.length : Int) / a1.tc.itemsize > 0 := by
      have hl : bs.length ≠ 0 := fun h => hne (List.eq_nil_of_length_eq_zero h)
      rw [ht]
      rcases itemsize_cases a.tc with h | h | h | h | h <;> rw [h] at hm ⊢ <;> omega
    have : arrFromBytes a1 bs 1 = .error bufferErr := by
      unfold arrFromBytes
      simp only [bind, Except.bind, pure, Except.pure, throwE, show ¬ ((1 : Int) ≠ 1) by decide, ite_false]
      rw [ht, iteF (show ¬ ((bs.length : Int) % a.tc.itemsize ≠ 0) by rw [hm]; decide), ← ht, iteT hk]
      have hsm : ¬ ((bs.length : Int) / a1.tc.itemsize > ssizeMax - a1.items.length ∨
          (a1.items.length : Int) + (bs.length : Int) / a1.tc.itemsize > ssizeMax / a1.tc.itemsize) := by
        unfold Arr.Fits at hf
        rw [← ht] at hf
        have : ssizeMax / a1.tc.itemsize ≤ ssizeMax := Int.ediv_le_self _ (by unfold ssizeMax; omega)
        omega
      rw [iteF hsm, arrResize_exported a1 _ hx (by omega)]
    rw [this]

/-- `a.frombytes(arg)` for every argument whose buffer methods are Python code
(`__buffer__`, `__release_buffer__`), which may raise and change the array:
* a `__buffer__` that raises propagates, and nothing is released;
* otherwise the buffer is released last, on every path, after the bytes were copied, on the
  array as `frombytes` leaves it, and the release cannot change the outcome: a view whose item
  size is not 1 raises `TypeError`, a length that is not a multiple of the item size
  `ValueError`, each with the array as `__buffer__` left it; otherwise the view's items are
  appended (no buffer exported, the result fits).
With `plainBuf bs` (a `bytes` object) this is `ArrayBytesRoundTrip`'s `frombytes`. -/
def ArrayFromBytesCall : Prop :=
  (∀ a (b : BufArg) e a1, b.getbuf a = (.error e, a1) → arrFromBytesCall a b = (.error e, a1)) ∧
  (∀ a (b : BufArg) bs isz a1, isz ≠ 1 → b.getbuf a = (.ok (bs, isz), a1) →
    arrFromBytesCall a b = (.error (.typeError "a bytes-like object is required"), b.release a1)) ∧
  (∀ a (b : BufArg) bs a1, b.getbuf a = (.ok (bs, 1), a1) → (bs.length : Int) % a1.tc.itemsize ≠ 0 →
    arrFromBytesCall a b = (.error (.valueError "bytes length not a multiple of item size"), b.release a1)) ∧
  (∀ a (b : BufArg) bs a1, b.getbuf a = (.ok (bs, 1), a1) → a1.exports = 0 →
    (bs.length : Int) % a1.tc.itemsize = 0 → a1.Fits (a1.items.length + (bs.length : Int) / a1.tc.itemsize) →
    ∃ a2, arrFromBytesCall a b = (.ok (), b.release a2) ∧ a2.items = a1.items ++ decodedItems a1.tc bs ∧
      a2.tc = a1.tc)

theorem arrayFromBytesCall_proven : ArrayFromBytesCall := by
  refine ⟨fun a b e a1 hg => ?_, fun a b bs isz a1 hi hg => ?_, fun a b bs a1 hg hm => ?_,
    fun a b bs a1 hg hx hm hf => ?_⟩
  · simp only [arrFromBytesCall, hg]
  · have : arrFromBytes a1 bs isz = .error (.typeError "a bytes-like object is required") := by
      unfold arrFromBytes
      simp only [bind, Except.bind, pure, Except.pure, throwE]
      rw [iteT hi]
    simp only [arrFromBytesCall, hg, this]
  · have : arrFromBytes a1 bs 1 = .error (.valueError "bytes length not a multiple of item size") := by
      unfold arrFromBytes
      simp only [bind, Except.bind, pure, Except.pure, throwE, show ¬ ((1 : Int) ≠ 1) by decide, ite_false]
      rw [iteT hm]
    simp only [arrFromBytesCall, hg, this]
  · obtain ⟨a2, h1, h2, h3, _⟩ := arrFromBytes_ok a1 bs hx hm hf
    exact ⟨a2, by simp only [arrFromBytesCall, hg, h1], h2, h3⟩

/-- `fromfile` when `read` returns an instance of a `bytes` subclass of length `size` with the
buffer methods `buf`: the items come from the buffer and the `EOFError` test from `size`, which
comes after the buffer was released (`__release_buffer__` may have changed the array); the
outcome otherwise is that of `ArrayFromBytesCall`. -/
def ArrayFromFileSub : Prop :=
  (∀ a read n (size : Nat) (buf : BufArg) e a1 a2, n ≤ ssizeMax / a.tc.itemsize →
    read (n * a.tc.itemsize) a = (.bytesSub size buf, a1) → buf.getbuf a1 = (.error e, a2) →
    arrFromFileC a read n = (.error e, a2, [n * a.tc.itemsize])) ∧
  (∀ a read n (size : Nat) (buf : BufArg) bs isz a1 a2, n ≤ ssizeMax / a.tc.itemsize → isz ≠ 1 →
    read (n * a.tc.itemsize) a = (.bytesSub size buf, a1) → buf.getbuf a1 = (.ok (bs, isz), a2) →
    arrFromFileC a read n =
      (.error (.typeError "a bytes-like object is required"), buf.release a2, [n * a.tc.itemsize])) ∧
  (∀ a read n (size : Nat) (buf : BufArg) bs a1 a2, n ≤ ssizeMax / a.tc.itemsize →
    read (n * a.tc.itemsize) a = (.bytesSub size buf, a1) → buf.getbuf a1 = (.ok (bs, 1), a2) →
    (bs.length : Int) % a2.tc.itemsize ≠ 0 →
    arrFromFileC a read n =
      (.error (.valueError "bytes length not a multiple of item size"), buf.release a2, [n * a.tc.itemsize])) ∧
  (∀ a read n (size : Nat) (buf : BufArg) bs a1 a2, n ≤ ssizeMax / a.tc.itemsize →
    read (n * a.tc.itemsize) a = (.bytesSub size buf, a1) → buf.getbuf a1 = (.ok (bs, 1), a2) →
    a2.exports = 0 → (bs.length : Int) % a2.tc.itemsize = 0 →
    a2.Fits (a2.items.length + (bs.length : Int) / a2.tc.itemsize) →
    ∃ a3, arrFromFileC a read n =
      ((if (size : Int) = n * a.tc.itemsize then .ok () else .error eofErr), buf.release a3,
        [n * a.tc.itemsize]) ∧
      a3.items = a2.items ++ decodedItems a2.tc bs)

theorem arrayFromFileSub_proven : ArrayFromFileSub := by
  obtain ⟨c1, c2, c3, c4⟩ := arrayFromBytesCall_proven
  refine ⟨fun a read n size buf e a1 a2 hn hr hg => ?_, fun a read n size buf bs isz a1 a2 hn hi hr hg => ?_,
    fun a read n size buf bs a1 a2 hn hr hg hm => ?_, fun a read n size buf bs a1 a2 hn hr hg hx hm hf => ?_⟩
  · simp only [arrFromFileC]; rw [iteF (by omega), hr]
    simp only [c1 a1 buf e a2 hg]
  · simp only [arrFromFileC]; rw [iteF (by omega), hr]
    simp only [c2 a1 buf bs isz a2 hi hg]
  · simp only [arrFromFileC]; rw [iteF (by omega), hr]
    simp only [c3 a1 buf bs a2 hg hm]
  · obtain ⟨a3, h1, h2, _⟩ := c4 a1 buf bs a2 hg hx hm hf
    refine ⟨a3, ?_, h2⟩
    simp only [arrFromFileC]; rw [iteF (by omega), hr]
    simp only [h1]
    by_cases hl : (size : Int) = n * a.tc.itemsize
    · rw [iteF (by omega), iteT hl]
    · rw [iteT hl, iteF hl]; rfl

/-- `ArrayFromFileBytes` and `ArrayFromFileSub`. -/
def ArrayFromFile : Prop := ArrayFromFileBytes ∧ ArrayFromFileSub

theorem arrayFromFile_proven : ArrayFromFile := ⟨arrayFromFileBytes_proven, arrayFromFileSub_proven⟩

/-! ### `tofile` -/

/-- A `write` that does not touch the array; `fail i` is the exception call `i` raises, if any. -/
def pureWrite (fail : Nat → Option PyExc) : WriteFn := fun i _ a =>
  ((match fail i with | some e => .error e | none => .ok ()), a)

/-- The 64 KiB blocks of `bs`, the last one shorter. -/
def blocksOf (bs : List Nat) : List (List Nat) :=
  (List.range ((bs.length + 65535) / 65536)).map (fun i => (bs.drop (i * 65536)).take 65536)

/-- Writing blocks in order, from call number `i`, stopping at the first call that raises. -/
def writeAll (fail : Nat → Option PyExc) : Nat → List (List Nat) → Py Unit × List (List Nat)
  | _, [] => (.ok (), [])
  | i, b :: bs =>
    match fail i with
    | some e => (.error e, [b])
    | none => ((writeAll fail (i + 1) bs).1, b :: (writeAll fail (i + 1) bs).2)

theorem blocks_flatten (bs : List Nat) :
    ∀ (k s : Nat), ((List.range' s k).map (fun i => (bs.drop (i * 65536)).take 65536)).flatten =
      (bs.drop (s * 65536)).take (k * 65536)
  | 0, s => by simp
  | k + 1, s => by
    rw [List.range'_succ, List.map_cons, List.flatten_cons, blocks_flatten bs k (s + 1),
      show (k + 1) * 65536 = 65536 + k * 65536 by omega, List.take_add, List.drop_drop,
      show s * 65536 + 65536 = (s + 1) * 65536 by omega]

/-- `a.tofile(f)` for every `write` that leaves the array alone and may raise at any call:
it writes the 64 KiB blocks of `a.tobytes()` in order, one call each, and stops after the
first call that raises, with its exception; an empty array writes nothing. The blocks put
together are `a.tobytes()`, as Doc/library/array.rst:270-284 says (`tobytes` gives "the same
sequence of bytes that would be written to a file by the `tofile` method"). -/
def ArrayToFile : Prop :=
  (∀ (a : Arr) (fail : Nat → Option PyExc),
    arrToFile a (pureWrite fail) =
      ((writeAll fail 0 (blocksOf (arrToBytes a))).1, a, (writeAll fail 0 (blocksOf (arrToBytes a))).2)) ∧
  (∀ bs : List Nat, (blocksOf bs).flatten = bs)

set_option maxRecDepth 100000 in
theorem toFileLoop_pure (a : Arr) (fail : Nat → Option PyExc) (bytes : List Nat) (hb : arrToBytes a = bytes)
    (NB : Nat) (hNB : NB = (bytes.length + 65535) / 65536) :
    ∀ (m i : Nat) (out : List (List Nat)), out.length = i → i + m = NB →
      toFileLoop (pureWrite fail) bytes.length NB m i a out =
        ((writeAll fail i ((List.range' i m).map (fun j => (bytes.drop (j * 65536)).take 65536))).1, a,
          out ++ (writeAll fail i ((List.range' i m).map (fun j => (bytes.drop (j * 65536)).take 65536))).2)
  | 0, i, out, _, _ => by simp [toFileLoop, writeAll]
  | m + 1, i, out, hl, hm => by
    have hi : i * 65536 < bytes.length := by
      have : i < (bytes.length + 65535) / 65536 := by omega
      have := (Nat.lt_div_iff_mul_lt (by decide)).mp this
      omega
    have hsize : (if (i : Int) * blocksize + blocksize > (bytes.length : Int) then (bytes.length : Int) - i * blocksize
        else blocksize) = ((min 65536 (bytes.length - i * 65536) : Nat) : Int) := by
      unfold blocksize; split <;> omega
    have hblk : blockOf a ((i : Int) * blocksize) ((min 65536 (bytes.length - i * 65536) : Nat) : Int) =
        .ok ((bytes.drop (i * 65536)).take 65536) := by
      unfold blockOf
      rw [hb, if_pos (by unfold blocksize; omega)]
      simp only [Except.ok.injEq]
      rw [show ((i : Int) * blocksize).toNat = i * 65536 by unfold blocksize; omega,
        show ((min 65536 (bytes.length - i * 65536) : Nat) : Int).toNat = min 65536 (bytes.length - i * 65536) by omega]
      by_cases hc : 65536 ≤ bytes.length - i * 65536
      · rw [Nat.min_eq_left hc]
      · rw [Nat.min_eq_right (by omega), List.take_of_length_le (l := bytes.drop (i * 65536)) (by simp),
          List.take_of_length_le (l := bytes.drop (i * 65536)) (by simp; omega)]
    unfold toFileLoop
    rw [if_pos (by omega)]
    simp only []
    rw [hsize, hblk]
    simp only [List.range'_succ, List.map_cons, writeAll]
    simp only [pureWrite, hl]
    cases hf : fail i with
    | some e => simp
    | none =>
      simp only []
      rw [show (i : Int) + 1 = ((i + 1 : Nat) : Int) by omega,
        toFileLoop_pure a fail bytes hb NB hNB m (i + 1) (out ++ [(bytes.drop (i * 65536)).take 65536])
          (by simp [hl]) (by omega)]
      simp

theorem arrayToFile_proven : ArrayToFile := by
  refine ⟨fun a fail => ?_, fun bs => ?_⟩
  · unfold arrToFile
    have hlen := length_arrToBytes a
    by_cases h0 : a.items.length = 0
    · rw [if_pos (by omega)]
      have : arrToBytes a = [] := by
        rw [← List.length_eq_zero_iff, hlen, h0]; simp
      rw [this]
      simp [blocksOf, writeAll]
    · rw [if_neg (by omega)]
      have hsz := itemsize_cases a.tc
      have hcast : ((a.items.length : Int) * a.tc.itemsize) = ((arrToBytes a).length : Int) := by
        rw [hlen]; rcases hsz with h | h | h | h | h <;> rw [h] <;> simp
      rw [hcast]
      have hnb : ((((arrToBytes a).length : Int) + blocksize - 1) / blocksize) =
          (((arrToBytes a).length + 65535) / 65536 : Nat) := by unfold blocksize; omega
      rw [hnb, show ((((arrToBytes a).length + 65535) / 65536 : Nat) : Int).toNat =
        ((arrToBytes a).length + 65535) / 65536 by omega]
      have := toFileLoop_pure a fail (arrToBytes a) rfl _ rfl (((arrToBytes a).length + 65535) / 65536) 0 []
        rfl (by omega)
      rw [show ((0 : Nat) : Int) = 0 from rfl] at this
      rw [this]
      simp [blocksOf, List.range_eq_range']
  · unfold blocksOf
    rw [List.range_eq_range', blocks_flatten bs _ 0]
    simp only [Nat.zero_mul, List.drop_zero]
    exact List.take_of_length_le (by omega)

/-- `a.tofile(f)` reads only inside the array, for every `write` callback: the outcome is a Python
exception or success, never the model's report of C undefined behaviour.

Refuted: `nbytes` and `nblocks` are computed once (arraymodule.c:1807-1811) and `ob_item` is
read again for each block (:1822-1828), so a `write` that empties the array makes the next
block a read of `size` bytes at `NULL + 65536`, a segmentation fault. Duplicate of
python/cpython#142884 (open). -/
def ArrayToFileSafe : Prop :=
  ∀ (a : Arr) (write : WriteFn) (e : PyExc), a.WF → a.exports = 0 → (arrToFile a write).1 = .error e →
    isCUB e = false

/-- A `write` that clears the array (`a.clear()` or `del a[:]`). -/
def clearingWrite : WriteFn := fun _ _ a =>
  match arrClear a with
  | .ok a' => (.ok (), a')
  | .error e => (.error e, a)

set_option maxRecDepth 100000 in
theorem arrayToFileSafe_refuted : ¬ ArrayToFileSafe := by
  intro h
  let a : Arr := ⟨.Zd, List.replicate 4097 0, 4097, true, 0, "array"⟩
  have hw : a.WF := by
    intro x hx
    have := List.eq_of_mem_replicate hx
    subst this; decide
  have hr : (arrToFile a clearingWrite).1 = .error (cUB "tofile reads past the items of the array") := by
    decide +kernel
  have := h a clearingWrite _ hw rfl hr
  exact absurd this (by decide)

end PyLean.Sequences
