import PyLean.TextLibs.StructUse

/-!
Second re-review of `Modules/_struct.c`: code offsets and padding of `prepare_s`, the remaining
branches of `same_format` and `s_init`, what `Struct.unpack` returns, and the failure exits of the
module cache.
-/

namespace PyLean.TextLibs.Struct

open PyLean PyLean.TextLibs

set_option linter.unusedSimpArgs false

/-! ### `prepare_s`: offsets and padding of two items -/

/-- `n` rounded up to a multiple of `a` (`a = 0`: no alignment). -/
def roundUp (n a : Nat) : Nat := if a = 0 then n else (n + a - 1) / a * a

def pairOk (p : List Char) (a b : FormatDef) : Bool :=
  match prepareS ((p ++ a.format ++ b.format).map Char.toNat) with
  | .ok s =>
    s.sSize == roundUp a.size b.alignment + b.size &&
      s.codes.map (·.offset) ==
        (if a.code = 'x' then [] else [0]) ++ (if b.code = 'x' then [] else [roundUp a.size b.alignment])
  | .error _ => false

/-- For every prefix and every two codes `a`, `b` of the table it selects, `Struct(prefix + a + b)`
puts `a` at offset 0 and `b` at the first multiple of `b`'s alignment after `a` (native padding,
1757-1764 with `align`), and its size is that offset plus `b`'s size: `calcsize('bi') == 8`,
`Struct('bh')` has `h` at 2. `x` makes no code (1771-1772). A second pass that stored offset 0 for
every code, or skipped the padding, fails this. -/
def PairOffsets : Prop :=
  ∀ p ∈ [[], ['<'], ['>'], ['!'], ['='], ['@']], ∀ a ∈ (whichtable p).1.table, ∀ b ∈ (whichtable p).1.table,
    ∃ s, prepareS ((p ++ a.format ++ b.format).map Char.toNat) = .ok s ∧
      s.sSize = roundUp a.size b.alignment + b.size ∧
      s.codes.map (·.offset) =
        (if a.code = 'x' then [] else [0]) ++ (if b.code = 'x' then [] else [roundUp a.size b.alignment])

theorem pair_check : ∀ p ∈ [[], ['<'], ['>'], ['!'], ['='], ['@']], ∀ a ∈ (whichtable p).1.table,
    ∀ b ∈ (whichtable p).1.table, pairOk p a b = true := by
  decide +kernel

theorem pairOffsets_proven : PairOffsets := by
  intro p hp a ha b hb
  have h := pair_check p hp a ha b hb
  unfold pairOk at h
  split at h
  · rename_i s hs
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨s, hs, h.1, h.2⟩
  · cases h

/-! ### `same_format` on other bytes, `s_init` on a subclass -/

/-- The branches the first statement left: `__init__` with `bytes` other than the format warns and
installs the new format (`same_format`, 1946-1948); on a subclass with its own `__init__`, an object
`__new__` made but `__init__` has not run on is initialised explicitly (`tp_init == s_init` is false,
1994), so another format warns "Different format ..." and is installed, while on `Struct` itself the
same call is the implicit one and changes nothing. -/
def LifeBranches2 : Prop :=
  (∀ (s s' : SObj) (b : Bool) (bs : List Nat), bs ≠ s.format → setFormat (.bytes bs) = .ok s' →
    structInitImpl ⟨some s, b⟩ (.bytes bs) =
      (.ok ⟨some s', true⟩, [("FutureWarning", if b then reinitMsg else diffMsg)])) ∧
  (∀ (s s' : SObj) (cps : List Nat), cps ≠ s.format → setFormat (.str cps) = .ok s' →
    sInitL { initIsS := false } ⟨some s, false⟩ ⟨[.str cps], []⟩ =
      (.ok ⟨some s', true⟩, [("FutureWarning", diffMsg)])) ∧
  (∀ (s : SObj) (a : CallArgs), sInitL {} ⟨some s, false⟩ a = (.ok ⟨some s, true⟩, []))

theorem lifeBranches2_proven : LifeBranches2 := by
  refine ⟨fun s s' b bs hne h => ?_, fun s s' cps hne h => ?_, fun s a => rfl⟩
  · have : sameFormat s (.bytes bs) = false := by simp [sameFormat, hne]
    cases b <;> simp [structInitImpl, this, h, reinitMsg, diffMsg]
  · have : sameFormat s (.str cps) = false := by simp [sameFormat, hne]
    simp [sInitL, parseFormat, structInitImpl, this, h, diffMsg]

/-! ### What `unpack` returns -/

/-- The items of a struct, each code `repeat` times, at `offset + j * size`. -/
def reps (c : Code) : Nat → Nat → List (Code × Nat)
  | 0, _ => []
  | j + 1, off => (c, off) :: reps c j (off + c.size)

def itemPos (s : SObj) : List (Code × Nat) := s.codes.flatMap (fun c => reps c c.repeat_ c.offset)

theorem unpackRepeat_eq (c : Code) (buf : List Nat) : ∀ (j off : Nat),
    unpackRepeat c buf j off = (reps c j off).mapM (fun p => unpackOne p.1 (buf.drop p.2)) := by
  intro j
  induction j with
  | zero => intro off; rfl
  | succ j ih =>
    intro off
    simp only [unpackRepeat, reps, List.mapM_cons, ih]

/-- One step of the code loop of `s_unpack_internal`. -/
def stepU (buf : List Nat) (acc : List SV) (code : Code) : Py (List SV) := do
  return acc ++ (← unpackRepeat code buf code.repeat_ code.offset)

theorem sUnpack_stepU (s : SObj) (buf : List Nat) :
    sUnpackInternal s buf = s.codes.foldlM (stepU buf) [] := rfl

theorem foldl_eq (buf : List Nat) : ∀ (codes : List Code) (acc : List SV),
    codes.foldlM (stepU buf) acc =
      (match (codes.flatMap (fun c => reps c c.repeat_ c.offset)).mapM
            (fun p => unpackOne p.1 (buf.drop p.2)) with
       | .ok l => .ok (acc ++ l)
       | .error e => .error e : Py (List SV)) := by
  intro codes
  induction codes with
  | nil => intro acc; simp [List.mapM_nil, pure, Except.pure]
  | cons c cs ih =>
    intro acc
    rw [List.foldlM_cons, List.flatMap_cons, List.mapM_append]
    have hstep : stepU buf acc c = (match (reps c c.repeat_ c.offset).mapM
        (fun p => unpackOne p.1 (buf.drop p.2)) with
        | .ok l => .ok (acc ++ l) | .error e => .error e) := by
      unfold stepU
      rw [unpackRepeat_eq]
      cases (reps c c.repeat_ c.offset).mapM (fun p => unpackOne p.1 (buf.drop p.2)) <;> rfl
    rw [hstep]
    cases (reps c c.repeat_ c.offset).mapM (fun p => unpackOne p.1 (buf.drop p.2)) with
    | error e => rfl
    | ok l =>
      show cs.foldlM (stepU buf) (acc ++ l) = _
      rw [ih]
      cases (cs.flatMap (fun c => reps c c.repeat_ c.offset)).mapM (fun p => unpackOne p.1 (buf.drop p.2)) with
      | error e => rfl
      | ok l2 => simp [bind, Except.bind, pure, Except.pure, List.append_assoc]

/-- `Struct.unpack` of a buffer of the right size is `s_unpack_internal` of that buffer from its first
byte, with the `Struct` the buffer conversion left, and `s_unpack_internal` gives, in order, each item
read at its code's offset plus `j * size` (2047-2072). An impl that started at `buf + 1`, or returned
`s_len` zeros, fails this. -/
def UnpackValues : Prop :=
  (∀ (s : SObj) (b : BufArg) (buf : List Nat), readBuf b = .ok buf → buf.length = (bufStruct s b).sSize →
    structUnpackA s b = sUnpackInternal (bufStruct s b) buf) ∧
  (∀ (t : SObj) (buf : List Nat),
    sUnpackInternal t buf = (itemPos t).mapM (fun p => unpackOne p.1 (buf.drop p.2)))

theorem unpackValues_proven : UnpackValues := by
  refine ⟨fun s b buf h hl => ?_, fun t buf => ?_⟩
  · simp [structUnpackA, h, structUnpack, hl, bind, Except.bind]
  · rw [sUnpack_stepU, foldl_eq]
    unfold itemPos
    cases (t.codes.flatMap (fun c => reps c c.repeat_ c.offset)).mapM (fun p => unpackOne p.1 (buf.drop p.2)) <;> rfl

/-! ### The failure exits of the cache -/

/-- A format argument as `cache_struct_converter` sees it. -/
inductive CArg where
  /-- A `str` or a `str` subclass. -/
  | key (k : CKey)
  | bytes (b : List Nat)
  /-- A hashable object that is not `str` or `bytes` (compared by identity). -/
  | other (ty : String)
  | unhashable (ty : String)
  | hashRaises (ty : String) (e : PyExc)
  /-- A `str` subclass whose second `__hash__`, the one `PyDict_SetItem` makes, raises. -/
  | setRaises (k : CKey)

/-- `cache_struct_converter`, `Modules/_struct.c:2617-2664`: `bytes` are decoded to a `str` key
(2629-2635); the lookup fails for an unhashable key, or with what `__hash__` raises, a `TypeError`
reworded as the dictionary does (2640-2643); a non-`str` object misses and `Struct(key)` refuses it;
a failing `PyDict_SetItem` is swallowed and the struct is returned uncached (2655-2656). -/
def cacheConvert (c : Cache) : CArg → Py SObj × Cache
  | .key k => cacheStructC c k
  | .bytes b => cacheStructC c (.str (decodeSurrogate b))
  | .other t => (setFormat (.other t true), c)
  | .unhashable t => (.error (.typeError s!"cannot use '{t}' as a dict key (unhashable type: '{t}')"), c)
  | .hashRaises t e =>
    (match e with
     | .typeError m => .error (.typeError s!"cannot use '{t}' as a dict key ({m})")
     | e => .error e, c)
  | .setRaises k =>
    match cacheFind c k with
    | some s => (.ok s, c)
    | none =>
      match structInit (.str k.value) with
      | .ok s => (.ok s, if c.length ≥ MAXCACHE then [] else c)
      | .error e => (.error e, c)

/-- The exits of the converter by outcome, on a coherent cache: an unhashable format is the
dictionary's `TypeError`, not `Struct()`'s; a `__hash__` that raises `TypeError` is reworded and any
other exception passes; a hashable non-format is `Struct()`'s `TypeError`; `bytes` give the struct
of their `surrogateescape` decoding, the same as the equal `str` when ASCII, and share its cache
entry; and a failing `SetItem` still returns the struct, leaving the cache without it. -/
def CacheEdges : Prop :=
  ∀ (c : Cache), Coherent c → c.length ≤ MAXCACHE →
    (∀ t, (cacheConvert c (.unhashable t)).1 =
      .error (.typeError s!"cannot use '{t}' as a dict key (unhashable type: '{t}')")) ∧
    (∀ t m, (cacheConvert c (.hashRaises t (.typeError m))).1 =
      .error (.typeError s!"cannot use '{t}' as a dict key ({m})")) ∧
    (∀ t e, (∀ m, e ≠ .typeError m) → (cacheConvert c (.hashRaises t e)).1 = .error e) ∧
    (∀ t, (cacheConvert c (.other t)).1 =
      .error (.typeError s!"Struct() argument 1 must be a str or bytes object, not {t}")) ∧
    (∀ b, (cacheConvert c (.bytes b)).1 = structInit (.bytes b)) ∧
    (∀ b, (∀ x ∈ b, x < 128) → cacheConvert c (.bytes b) = cacheConvert c (.key (.str b))) ∧
    (∀ v s, cacheFind c (.str v) = none → structInit (.str v) = .ok s →
      (cacheConvert c (.setRaises (.str v))).1 = .ok s ∧
      ∀ p ∈ (cacheConvert c (.setRaises (.str v))).2, p ∈ c)

theorem cacheEdges_proven : CacheEdges := by
  intro c h hl
  refine ⟨fun t => rfl, fun t m => rfl, fun t e he => ?_, fun t => rfl, fun b => ?_, fun b hb => ?_,
    fun v s hf hs => ?_⟩
  · cases e with
    | typeError m => exact absurd rfl (he m)
    | _ => rfl
  · simp only [cacheConvert]
    rw [(cacheCoherent_proven.1 c _ h hl).1]
    rfl
  · simp only [cacheConvert, decodeSurrogate_ascii b hb]
  · simp only [cacheConvert, hf, CKey.value, hs]
    refine ⟨trivial, fun p hp => ?_⟩
    split at hp
    · simp at hp
    · exact hp

end PyLean.TextLibs.Struct
