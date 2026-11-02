import PyLean.BytesObj.Bytes.ByteArrayProps3

/-!
`bytearray`: items, concatenation, the constructor, the iterator, `__reduce__` and the
read-only wrappers.
-/

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

/-! ## Items -/

/-- `b[i] = c` sets one position for every in-range Python index; a value outside
`range(256)` raises `ValueError` even for a bad index, since the value is converted first
(GH-91153: the conversion can run `__index__`, which may resize); `del b[i]` is the list's
`del l[i]`. `bytearray_setitem` (`sq_ass_item`) and the subscript path agree. -/
def ItemSpec : Prop :=
  (∀ (b : BA) (i : Int) (c : Nat), c < 256 → 0 ≤ i → i < b.size → i ≤ ssizeMax →
    baAssIndex b i (some (.int c)) = .ok { b with data := b.data.set i.toNat (c : Int) }) ∧
  (∀ (b : BA) (i v : Int), v < 0 ∨ v ≥ 256 → ssizeMin ≤ i → i ≤ ssizeMax →
    baAssIndex b i (some (.int v)) = .error (.valueError "byte must be in range(0, 256)")) ∧
  (∀ (b : BA) (i : Int) (c : Nat), c < 256 → ssizeMin ≤ i → i ≤ ssizeMax →
    baSetItemRaw b i (some (.int c)) = baAssIndex b i (some (.int c))) ∧
  (∀ (b r : BA) (i : Int), baAssIndex b i none = .ok r →
    Sequences.listAssItem b.data i none = .ok r.data)

theorem subIndex_ok (i : Int) (h1 : ssizeMin ≤ i) (h2 : i ≤ ssizeMax) : Sequences.subIndex i = .ok i := by
  simp [Sequences.subIndex, Sequences.asSsizeExc, h1, h2]

theorem itemSpec_proven : ItemSpec := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro b i c hc h0 h1 h2
    have h3 : ssizeMin ≤ i := by rw [show ssizeMin = -9223372036854775808 by decide]; omega
    have h4 : ¬ (i < 0) := by omega
    have h5 : ¬ (i < 0 ∨ i ≥ b.size) := by omega
    simp only [baAssIndex, subIndex_ok i h3 h2, bind, Except.bind, getByte_ok c hc, pure, Except.pure]
    simp only [Functor.map, Except.map]
    rw [if_neg h4, if_neg h5]
  · intro b i v h h1 h2
    simp only [baAssIndex, subIndex_ok i h1 h2, bind, Except.bind, getByte_bad v h, pure, Except.pure]
    simp only [Functor.map, Except.map]
  · intro b i c hc h1 h2
    simp only [baAssIndex, baSetItemRaw, subIndex_ok i h1 h2, bind, Except.bind, getByte_ok c hc,
      Functor.map, Except.map]
  · intro b r i h
    unfold baAssIndex at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    cases hi : Sequences.subIndex i with
    | error e => rw [hi] at h; simp at h
    | ok k =>
      rw [hi] at h
      simp only at h
      by_cases hb : (if k < 0 then k + b.size else k) < 0 ∨ (if k < 0 then k + b.size else k) ≥ b.size
      · rw [if_pos hb] at h
        simp at h
      rw [if_neg hb] at h
      generalize hj : (if k < 0 then k + b.size else k) = j at h hb
      have hsz : b.size = (b.data.length : Int) := rfl
      obtain ⟨n, rfl⟩ : ∃ n : Nat, j = n := ⟨j.toNat, by omega⟩
      have e := plain_agrees b r n ((n : Int) + 1) [] (by omega) (by omega) (by omega) h
      have hv : Sequences.validIndex (n : Int) b.data.length = true := by
        simp only [Sequences.validIndex, decide_eq_true_eq]
        omega
      simp only [Sequences.listAssItem, hi, bind, Except.bind, pure, Except.pure]
      have hk : (if k < 0 then k + (b.data.length : Int) else k) = n := by
        rw [← hsz]; exact hj
      rw [hk]
      simp only [hv, Bool.not_true, Bool.false_eq_true, if_false, e]
      have hl : n < b.data.length := by omega
      simp only [Sequences.listAssSlice]
      have c1 : ¬ ((n : Int) < 0) := by omega
      have c2 : ¬ ((n : Int) > b.data.length) := by omega
      have c3 : ¬ ((n : Int) + 1 < n) := by omega
      have c4 : ¬ ((n : Int) + 1 > b.data.length) := by omega
      simp only [c1, c2, c3, c4, if_false, List.append_nil]
      have e1 : ((n : Int) + 1).toNat = n + 1 := by omega
      simp only [Int.toNat_natCast, e1]
      congr 1
      rw [List.eraseIdx_eq_take_drop_succ]

/-! ## Concatenation, repetition, extend, copy -/

/-- `bytearray + x`, `+=`, `*=`, `extend` and `copy`: the contents are what the sequence
operations say, for buffers and iterables; `*=` refuses with exports when the size changes
and accepts `n = 1`; a value that is no buffer is a `TypeError`. -/
def ConcatSpec2 : Prop :=
  (∀ (a b : Seq), (a.length : Int) + b.length + 33 < 2 ^ 47 → a ++ b ≠ [] →
    ∃ r, baConcat (.bytearray a) (.bytes b) = .ok r ∧ r.data = seqData (a ++ b)) ∧
  (∀ (b r : BA) (o : Obj) (v : Seq), o.buffer? = some v → baIConcat b o = .ok r →
    r.data = b.data ++ seqData v) ∧
  (∀ (b : BA) (o : Obj), o.buffer? = none → ∃ m, baIConcat b o = .error (.typeError m)) ∧
  (∀ b : BA, baIRepeat b 1 = .ok b) ∧
  (∀ (b : BA) (n : Int), 1 < n → b.size ≠ 0 → b.size ≤ Int.tdiv baSizeMax n → b.exports > 0 →
    baIRepeat b n = .error (bufferError "Existing exports of data: object cannot be re-sized")) ∧
  (∀ (b r : BA) (v : Seq), b.seq = v → (v.length : Int) + 33 < 2 ^ 47 → v ≠ [] → baCopy b = .ok r →
    r.data = seqData v)

theorem concatSpec2_proven : ConcatSpec2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b h hne
    have h1 : ¬ ((a.length : Int) > baSizeMax - b.length) := by
      unfold baSizeMax
      rw [ssizeMax_val, objsize_val]
      omega
    have hne2 : ¬ ((a.length : Int) + b.length = 0) := by
      intro e
      apply hne
      have ha : a.length = 0 := by omega
      have hb : b.length = 0 := by omega
      simp [List.length_eq_zero_iff.mp ha, List.length_eq_zero_iff.mp hb]
    have h3 : ¬ ((a.length : Int) + b.length < 0) := by omega
    have h4 := bytesSizeCheck_ok ((a.length : Int) + b.length) (by omega) h
    refine ⟨{ data := seqData ((a ++ b).take ((a.length : Int) + b.length).toNat),
              alloc := (a.length : Int) + b.length }, ?_, ?_⟩
    · simp only [baConcat, Obj.buffer?, h1, if_false, baFromStringAndSize, h3, h4, hne2]
    · simp only
      have e : ((a.length : Int) + b.length).toNat = (a ++ b).length := by simp; omega
      rw [e, List.take_length]
  · intro b r o v hv h
    unfold baIConcat at h
    simp only [hv, bind, Except.bind, pure, Except.pure] at h
    split at h
    · simp at h
    split at h
    · simp at h
    simp only [Except.ok.injEq] at h
    rename_i r' hr
    subst h
    obtain ⟨h0, hc⟩ := baResize_cases _ _ _ hr
    have hsz : b.size = (b.data.length : Int) := rfl
    have hlen : b.size.toNat = b.data.length := by omega
    show r'.data.take b.size.toNat ++ seqData v = b.data ++ seqData v
    rw [hlen]
    rcases hc with ⟨e1, _⟩ | ⟨_, _, hd, _, _⟩
    · rw [e1, List.take_length]
    · rw [hd]
      simp only [resizedData]
      have e : (b.size + (v.length : Int)).toNat = b.data.length + v.length := by omega
      have e2 : b.data.take (b.data.length + v.length) = b.data := List.take_of_length_le (by omega)
      rw [e, e2, List.take_left' rfl]
  · intro b o h
    exact ⟨_, by simp [baIConcat, h, bind, Except.bind]; rfl⟩
  · intro b
    simp [baIRepeat, pure, Except.pure]
  · intro b n h1 h2 h3 h4
    have hp : 0 < b.size := by simp only [BA.size] at h2 ⊢; omega
    have h5 : ¬ (n < 0) := by omega
    have h6 : ¬ (n = 1) := by omega
    have h7 : ¬ (n > 0 ∧ b.size > Int.tdiv baSizeMax n) := by omega
    have hmul : b.size * n ≠ b.size := by
      intro e
      have : b.size * n > b.size * 1 := Int.mul_lt_mul_of_pos_left (by omega) hp
      omega
    have hnn : 0 ≤ b.size * n := Int.mul_nonneg (by omega) (by omega)
    have hr := exportRule_proven.2.1 b (b.size * n) hnn hmul h4
    simp only [baIRepeat, h5, if_false, h6, h7, bind, Except.bind, hr, pure, Except.pure]
  · intro b r v hv hl hne h
    subst hv
    unfold baCopy at h
    have hsz : b.size = (b.data.length : Int) := rfl
    have hl2 : b.seq.length = b.data.length := by simp [BA.seq]
    have h0 : ¬ (b.size = 0) := by
      intro e
      apply hne
      have : b.data.length = 0 := by omega
      simp [BA.seq, List.length_eq_zero_iff.mp this]
    have h3 : ¬ (b.size < 0) := by omega
    have h4 := bytesSizeCheck_ok b.size (by omega) (by omega)
    simp only [baFromStringAndSize, h3, h4, h0, if_false, Except.ok.injEq] at h
    subst h
    simp only
    have e : b.size.toNat = b.seq.length := by omega
    rw [e, List.take_length]

/-! ## The constructor -/

/-- `bytearray(x)` for a fresh object: a buffer gives its contents, an int `n ≥ 0` gives `n`
zeros and a negative one `ValueError`, no argument gives the empty object, `str` without an
encoding and a stray `encoding` are the errors of `bytes()`; every successful construction
has a valid layout. `__init__` on a non-empty object with exports raises `BufferError`. -/
def InitSpec : Prop :=
  (∀ s : Seq, (s.length : Int) + 1 < 2 ^ 46 → ∃ r, baNew (some (.bytes s)) none none = .ok r ∧
    r.data = seqData s) ∧
  (∀ n : Nat, n ≠ 0 → (n : Int) + 1 < 2 ^ 46 → ∃ r, baNew (some (.int n)) none none = .ok r ∧
    r.data = List.replicate n 0) ∧
  (∀ v : Int, v < 0 → ssizeMin ≤ v →
    baNew (some (.int v)) none none = .error (.valueError "negative count")) ∧
  baNew none none none = .ok {} ∧
  (∀ cs : Seq, baNew (some (.str cs)) none none = bytesNewError cs) ∧
  (∀ (b : BA) (arg : Option Obj), b.exports > 0 →
    (baInit b arg none none).2 = some (bufferError "Existing exports of data: object cannot be re-sized"))
where
  /-- The `TypeError` `bytes()` gives for a `str` without an encoding. -/
  bytesNewError (_ : Seq) : Py BA := .error (.typeError "string argument without an encoding")

theorem resize_empty (n : Nat) (h0 : n ≠ 0) (hs : (n : Int) + 1 < 2 ^ 46) :
    ∃ r, baResize {} (n : Int) = .ok r := by
  have := exportRule_proven.2.2.2 {} (n : Int) (by omega) rfl (by omega)
  obtain ⟨r, hr, _⟩ := this
  exact ⟨r, hr⟩

theorem baNewObject_eq : baNewObject = {} := rfl

theorem init_fresh : (do canResize ({} : BA); baResize {} 0 : Py BA) = .ok {} := rfl

theorem initSpec_proven : InitSpec := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s h
    cases hs : s with
    | nil =>
      refine ⟨{}, ?_, rfl⟩
      rfl
    | cons c cs =>
      rw [← hs]
      have hne : s.length ≠ 0 := by simp [hs]
      obtain ⟨r, hr⟩ := resize_empty s.length hne (by omega)
      refine ⟨{ r with data := seqData s }, ?_, rfl⟩
      have hz : ({} : BA).size = 0 := rfl
      simp [baNew, baNewObject_eq, baInit, init_fresh, hz, Obj.index?, Obj.buffer?, hr]
  · intro n h0 h
    obtain ⟨r, hr⟩ := resize_empty n h0 (by omega)
    have h1 : ssizeMin ≤ (n : Int) ∧ (n : Int) ≤ ssizeMax := by
      rw [ssizeMax_val, show ssizeMin = -9223372036854775808 by decide]; omega
    have h2 : ¬ ((n : Int) < 0) := by omega
    have h3 : (n : Int) > 0 := by omega
    refine ⟨{ r with data := List.replicate n 0 }, ?_, ?_⟩
    · have hz : ({} : BA).size = 0 := rfl
      have h3' : 0 < n := by omega
      simp [baNew, baNewObject_eq, baInit, init_fresh, hz, Obj.index?, countOf, h1, h2, h3', hr]
    · rfl
  · intro v h1 h2
    have h3 : ssizeMin ≤ v ∧ v ≤ ssizeMax := by rw [ssizeMax_val]; omega
    have hz : ({} : BA).size = 0 := rfl
    simp [baNew, baNewObject_eq, baInit, init_fresh, hz, Obj.index?, countOf, h3, h1]
  · rfl
  · intro cs
    rfl
  · intro b arg h2
    simp [baInit, canResize, h2, bind, Except.bind]

/-! ## The iterator -/

/-- The iterator reads the current contents at its index, however the object has changed;
past the end it stops, and from then on stays stopped whatever happens to the object. The
hint is never negative. `__setstate__` clamps above, and a negative state means exhausted
(as for the list iterator, unlike the bytes iterator's clamp to 0). -/
def BaIterSpec : Prop :=
  (∀ (seq : BA) (i : Nat), i < seq.data.length →
    baIterNext seq { index := i } = (some (seq.data.getD i 0), { index := (i : Int) + 1 })) ∧
  (∀ (seq : BA) (i : Nat), seq.data.length ≤ i →
    baIterNext seq { index := i } = (none, { index := -1 })) ∧
  (∀ seq : BA, baIterNext seq { index := -1 } = (none, { index := -1 })) ∧
  (∀ (seq : BA) (it : BAIter), 0 ≤ baIterLen seq it) ∧
  (∀ (seq : BA) (n : Int), ssizeMin ≤ n → n ≤ ssizeMax → seq.size < n →
    baIterSetstate seq {} n = .ok { index := seq.size }) ∧
  (∀ (seq : BA) (n : Int), ssizeMin ≤ n → n ≤ ssizeMax → n < 0 →
    (baIterNext seq (match baIterSetstate seq {} n with | .ok it => it | .error _ => {})).1 = none)

theorem baIterSpec_proven : BaIterSpec := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro seq i h
    have h1 : ¬ ((i : Int) < 0) := by omega
    have h2 : (i : Int) < seq.size := by simp only [BA.size]; omega
    simp [baIterNext, h1, h2]
  · intro seq i h
    have h1 : ¬ ((i : Int) < 0) := by omega
    have h2 : ¬ ((i : Int) < seq.size) := by simp only [BA.size]; omega
    simp [baIterNext, h1, h2]
  · intro seq
    simp [baIterNext]
  · intro seq it
    simp only [baIterLen]
    repeat' split
    all_goals omega
  · intro seq n h1 h2 h3
    have hp : 0 ≤ seq.size := by simp only [BA.size]; omega
    have h4 : ¬ (n < -1) := by omega
    simp [baIterSetstate, Sequences.asSsize, h1, h2, h3, h4, bind, Except.bind, pure, Except.pure]
  · intro seq n h1 h2 h3
    have hp : 0 ≤ seq.size := by simp only [BA.size]; omega
    by_cases h4 : n < -1
    · simp [baIterSetstate, Sequences.asSsize, h1, h2, h4, bind, Except.bind, pure, Except.pure, baIterNext]
    · have h5 : n = -1 := by omega
      subst h5
      have h6 : ¬ ((-1 : Int) > seq.size) := by omega
      simp [baIterSetstate, Sequences.asSsize, h1, h2, h6, bind, Except.bind, pure, Except.pure, baIterNext]

/-! ## `__reduce__` -/

/-- `bytearray.__reduce_ex__(proto)` gives constructor arguments that rebuild the contents:
none for an empty object, `(text, 'latin-1')` below protocol 3 and `(bytes,)` from 3 on, for
every byte string. -/
def ReduceSpec : Prop :=
  ∀ (s : Seq) (proto : Int), (∀ c ∈ s, c < 256) → (s.length : Int) + 1 < 2 ^ 46 →
    match baReduce s proto with
    | .empty => s = []
    | .text cs => proto < 3 ∧ ∃ r, baNew (some (.str cs)) (some "latin-1") none = .ok r ∧ r.data = seqData s
    | .bin b => 3 ≤ proto ∧ ∃ r, baNew (some (.bytes b)) none none = .ok r ∧ r.data = seqData s

theorem reduceSpec_proven : ReduceSpec := by
  intro s proto hs hl
  unfold baReduce
  cases hn : s.isEmpty with
  | true =>
    simpa using hn
  | false =>
    have hne : s ≠ [] := by
      intro e; simp [e] at hn
    have hlen : s.length ≠ 0 := by
      intro e; exact hne (List.length_eq_zero_iff.mp e)
    by_cases hp : proto < 3
    · simp only [Bool.false_eq_true, if_false, hp, if_true]
      refine ⟨trivial, ?_⟩
      obtain ⟨r, hr⟩ := resize_empty s.length hlen (by omega)
      have hf := findIdx_none_lt s 256 hs
      have e1 : encodeStr s "latin-1" = .ok s := by simp [encodeStr, hf]
      have hz : ({} : BA).size = 0 := rfl
      have h5 : ¬ ((0 : Int) > baSizeMax - s.length) := by
        unfold baSizeMax
        rw [ssizeMax_val, objsize_val]
        omega
      refine ⟨{ r with data := r.data.take (0 : Int).toNat ++ seqData s }, ?_, by simp⟩
      have hc0 : canResize ({} : BA) = .ok () := rfl
      have hr0 : baResize {} 0 = .ok {} := rfl
      have h6 : ¬ (baSizeMax - (s.length : Int) < 0) := by omega
      simp [baNew, baNewObject_eq, baInit, hc0, hr0, hz, e1, baIConcat, Obj.buffer?, h6, hr, bind, Except.bind, pure, Except.pure]
    · simp only [Bool.false_eq_true, if_false, hp]
      obtain ⟨r, h1, h2⟩ := initSpec_proven.1 s (by omega)
      exact ⟨by omega, r, h1, h2⟩

/-! ## Read-only wrappers, buffers -/

/-- The read-only methods run the `bytes` code on the contents and leave `ob_exports` as
it was, and while they run a resize raises `BufferError`, so no callback can pull the buffer
from under them. -/
def ReadWrappers : Prop :=
  ∀ {α : Type} (b : BA) (op : Seq → Py α),
    baRead b op = (op b.seq, b) ∧
    ∀ n : Int, 0 ≤ n → n ≠ b.size →
      baResize (baGetBuffer b) n = .error (bufferError "Existing exports of data: object cannot be re-sized")

theorem readWrappers_proven : ReadWrappers := by
  intro α b op
  constructor
  · simp [baRead, withBuffer, baGetBuffer, baReleaseBuffer, BA.seq]
  · intro n h0 h1
    have := exportRule_proven.2.1 (baGetBuffer b) n h0 h1 (by simp [baGetBuffer])
    exact this

/-- A view of `bytes` is read-only and shows the contents; a view of `bytearray` is writable
and holds an export until released, which is what stops a resize; `bytes(b)` and
`__getnewargs__` are the contents. -/
def BufferSpec : Prop :=
  (∀ s : Seq, bytesBufferInfo s = (s, true) ∧ bytesBytes s = s) ∧
  (∀ b : BA, (baBufferInfo b).1 = (b.seq, false) ∧ (baBufferInfo b).2.exports = b.exports + 1 ∧
    baReleaseBuffer (baBufferInfo b).2 = b)

theorem bufferSpec_proven : BufferSpec := by
  refine ⟨fun s => ⟨rfl, rfl⟩, ?_⟩
  intro b
  simp [baBufferInfo, baGetBuffer, baReleaseBuffer]

/-! ## Escape warnings -/

/-- `PyBytes_DecodeEscape`: clean input gives no warning, and an invalid escape keeps the
backslash and gives one. -/
def EscapeWarning : Prop :=
  (∀ s : Seq, (∀ c ∈ s, c < 256) → bytesDecodeEscape (reprBody 39 s) none = .ok (s, none)) ∧
  (∃ m, bytesDecodeEscape [92, 113] none = .ok ([92, 113], some m))

theorem escapeWarning_proven : EscapeWarning := by
  constructor
  · intro s hs
    have := reprDecodeRoundTrip_proven 39 s (Or.inl rfl) hs
    simp [bytesDecodeEscape, this, bind, Except.bind, escapeWarning, pure, Except.pure]
  · exact ⟨_, rfl⟩

end PyLean.BytesObj.Bytes
