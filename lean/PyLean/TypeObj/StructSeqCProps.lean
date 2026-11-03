import PyLean.TypeObj.StructSeqRepr

/-!
# Struct sequences in memory: properties (Objects/structseq.c, CPython 3.15.2)

* `NewTypeLayout` (proven): what `PyStructSequence_NewType` builds from a desc.
* `NewTypeInBounds` (refuted): it never reads past the desc's field array.
* `ReprLabelsMatchAttrs` (refuted): `repr` labels each item with the attribute that reads it.
* `NewIndexContract` (proven): `PyStructSequence_New` on a type whose size attributes are its own,
  and the index contract of `PyStructSequence_SetItem`/`GetItem`.
* `NewSetsException` (refuted): `PyStructSequence_New` returns `NULL` only with an exception set.
* `ReplaceInBounds`, `ReduceInBounds`, `NewImplInBounds` (refuted): `__replace__`, `__reduce__`
  and the constructor stay inside the memory they use, whatever Python code does to the size
  attributes.
-/

namespace PyLean.TypeObj.StructSeq

open PyLean PyLean.UnicodeObj

/-! ## Type creation -/

/-- The named fields of a field array, each with its own index in the array. -/
def namedFields (fs : List FName) : List Member :=
  (fs.zip (List.range fs.length)).filterMap fun (f, i) =>
    match f with
    | .named b => some { name := b, slot := i }
    | .unnamed => none

/-- The names of the named fields among `fs`. -/
def namesOf (fs : List FName) : List Bytes :=
  fs.filterMap fun f => match f with | .named b => some b | .unnamed => none

/-- For every desc and every outcome of the rest of `PyType_FromSpecWithBases`, a type that
`PyStructSequence_NewType` builds has: as `tp_members`, the named fields in order, each reading
the slot of its own index (the docs: "The index in the `PyStructSequence_Field` array determines
which field of the struct sequence is described"); `0 ≤ n_in_sequence ≤ n_fields`; the three
size attributes `(n_in_sequence, #fields, #unnamed)`; as `__match_args__` the decoded names of
the named visible fields; and `tp_basicsize = 32 + 8 * hidden` when `hidden`, the number of
fields past `n_in_sequence`, is below `2^28 - 4` (above it the `(int)` cast at :775 wraps). -/
def NewTypeLayout : Prop :=
  ∀ (d : Desc) (malloc : Nat → Bool) (rest : Py Unit) (b : Built), newType d malloc rest = .ok b →
    b.type.name = d.name ∧
    b.type.members = namedFields d.fields ∧
    0 ≤ d.nInSeq ∧ d.nInSeq ≤ d.fields.length ∧
    b.type.dict = honestDict d.nInSeq d.fields.length (d.fields.count .unnamed) ∧
    (namesOf (d.fields.take d.nInSeq.toNat)).mapM (fun n => utf8Decode n .strict) = .ok b.matchArgs ∧
    ((d.fields.length : Int) - d.nInSeq < 2 ^ 28 - 4 →
      (b.type.basicsize : Int) = 32 + 8 * ((d.fields.length : Int) - d.nInSeq))

theorem countMembers_eq (fs : List FName) : countMembers fs = (fs.length, fs.count .unnamed) := by
  unfold countMembers
  suffices h : ∀ (a b : Nat), fs.foldl (fun (p : Nat × Nat) f => (p.1 + 1, if f = .unnamed then p.2 + 1 else p.2)) (a, b)
      = (a + fs.length, b + fs.count .unnamed) by
    have := h 0 0
    simp only [Nat.zero_add] at this
    exact this
  induction fs with
  | nil => intro a b; simp
  | cons f fs ih =>
    intro a b
    simp only [List.foldl_cons]
    rw [ih]
    by_cases hf : f = .unnamed
    · subst hf; simp [List.count_cons]; omega
    · simp [hf, List.count_cons]; omega

theorem initMembersLoop_eq (fs : List FName) (i : Nat) (acc : List Member) :
    initMembersLoop fs i acc = acc ++ (fs.zip (List.range' i fs.length)).filterMap (fun (f, j) =>
      match f with
      | .named b => some { name := b, slot := j }
      | .unnamed => none) := by
  induction fs generalizing i acc with
  | nil => simp [initMembersLoop]
  | cons f fs ih =>
    cases f with
    | unnamed => simp [initMembersLoop, ih, List.range'_succ]
    | named b => simp [initMembersLoop, ih, List.range'_succ]

theorem matchArgsLoop_ok (fs : List FName) :
    ∀ (k i : Nat) (ma : List Str), matchArgsLoop fs k i = .ok ma →
      (k = 0 ∨ i + k ≤ fs.length) ∧
        (namesOf ((fs.drop i).take k)).mapM (fun n => utf8Decode n .strict) = .ok ma := by
  intro k
  induction k with
  | zero =>
    intro i ma h
    simp only [matchArgsLoop] at h
    cases h
    simp [namesOf]
    rfl
  | succ k ih =>
    intro i ma h
    simp only [matchArgsLoop] at h
    by_cases hi : i < fs.length
    · rw [dif_pos hi] at h
      have hdrop : (fs.drop i).take (k + 1) = fs[i] :: (fs.drop (i + 1)).take k := by
        rw [List.drop_eq_getElem_cons hi]; rfl
      cases hf : fs[i] with
      | unnamed =>
        rw [hf] at h
        simp only [CRes.pure_eq, CRes.bind_ok] at h
        cases hr : matchArgsLoop fs k (i + 1) with
        | ok rest =>
          rw [hr] at h
          simp only [CRes.bind_ok] at h
          cases h
          obtain ⟨h1, h2⟩ := ih (i + 1) _ hr
          refine ⟨Or.inr (by omega), ?_⟩
          rw [hdrop, hf]
          simpa [namesOf] using h2
        | exc e => rw [hr] at h; cases h
        | nullNoExc => rw [hr] at h; cases h
        | ub x => rw [hr] at h; cases h
      | named b =>
        rw [hf] at h
        cases hd : utf8Decode b .strict with
        | error e => simp [hd, CRes.ofPy] at h
        | ok sb =>
          simp only [hd, CRes.ofPy, CRes.bind_ok, CRes.pure_eq] at h
          cases hr : matchArgsLoop fs k (i + 1) with
          | ok rest =>
            rw [hr] at h
            simp only [CRes.bind_ok] at h
            cases h
            obtain ⟨h1, h2⟩ := ih (i + 1) _ hr
            refine ⟨Or.inr (by omega), ?_⟩
            rw [hdrop, hf]
            simp only [namesOf, List.filterMap_cons] at h2 ⊢
            rw [List.mapM_cons, hd, h2]
            rfl
          | exc e => rw [hr] at h; cases h
          | nullNoExc => rw [hr] at h; cases h
          | ub x => rw [hr] at h; cases h
    · rw [dif_neg hi] at h
      cases h

theorem toCInt_small (x : Int) (h0 : 0 ≤ x) (h1 : x < 2 ^ 31) : toCInt x = x := by
  unfold toCInt
  have : x % 2 ^ 32 = x := Int.emod_eq_of_lt h0 (by omega)
  rw [this, if_neg (by omega)]

theorem newTypeLayout_proven : NewTypeLayout := by
  intro d malloc rest b h
  unfold newType at h
  rw [countMembers_eq] at h
  simp only at h
  unfold initializeMembers at h
  by_cases hm : malloc ((d.fields.length - d.fields.count FName.unnamed + 1) * 40) = true
  · simp only [hm, Bool.not_true, Bool.false_eq_true, if_false, CRes.bind_ok, List.take_length] at h
    unfold fromSpecBasicsize at h
    cases hrest : rest with
    | error e => rw [hrest] at h; cases h
    | ok u =>
      cases u
      rw [hrest] at h
      simp only at h
      generalize hbs : toCInt (40 + ((d.fields.length : Int) - d.nInSeq - 1) * 8) = bsz at h
      by_cases hneg : bsz < 0
      · rw [if_pos hneg] at h; cases h
      · rw [if_neg hneg] at h
        by_cases hsmall : (if bsz = 0 then 32 else bsz.toNat) < 32
        · rw [if_pos hsmall] at h; cases h
        · rw [if_neg hsmall] at h
          simp only [CRes.bind_ok] at h
          unfold initDict at h
          by_cases hn : d.nInSeq < 0
          · rw [if_pos hn] at h; cases h
          · rw [if_neg hn] at h
            cases hma : matchArgsLoop d.fields d.nInSeq.toNat 0 with
            | ok ma =>
              rw [hma] at h
              simp only [CRes.bind_ok] at h
              cases h
              obtain ⟨hlen, hmap⟩ := matchArgsLoop_ok d.fields _ 0 ma hma
              simp only [List.drop_zero] at hmap
              refine ⟨rfl, ?_, by omega, ?_, rfl, hmap, ?_⟩
              · rw [initMembersLoop_eq]
                simp [namedFields, List.range_eq_range']
              · rcases hlen with h0 | h0 <;> omega
              · intro hh
                have hle : d.nInSeq ≤ d.fields.length := by rcases hlen with h0 | h0 <;> omega
                have : bsz = 32 + 8 * ((d.fields.length : Int) - d.nInSeq) := by
                  rw [← hbs, toCInt_small _ (by omega) (by omega)]; omega
                subst this
                simp only
                rw [if_neg (by omega)]
                omega
            | exc e => rw [hma] at h; cases h
            | nullNoExc => rw [hma] at h; cases h
            | ub x => rw [hma] at h; cases h
  · simp only [Bool.not_eq_true] at hm
    simp [hm] at h

/-- `PyStructSequence_NewType` never reads past the `NULL` terminator of the desc's field array,
whatever `n_in_sequence` says. -/
def NewTypeInBounds : Prop :=
  ∀ (d : Desc) (malloc : Nat → Bool) (rest : Py Unit), (newType d malloc rest).isUB = false

/-- One named field and `n_in_sequence = 5`: `hidden = -4`, so `spec.basicsize` is `0`, which
`PyType_FromSpecWithBases` takes as "inherit tuple's" (Objects/typeobject.c:5645-5648), and the
`__match_args__` loop then reads fields 1-4 of a one-field array. -/
def descPlus4 : Desc := { name := lit "m.T", fields := [.named (lit "a")], nInSeq := 5 }

theorem newTypeInBounds_refuted : ¬ NewTypeInBounds := by
  intro h
  have := h descPlus4 (fun _ => true) (.ok ())
  revert this
  decide

/-! ## `repr` labels -/

variable {α : Type}

/-- `name=getattr(s, name)` for visible field `i`: the label of `repr`, and the item that
attribute reads (`tp_members[i].slot`). -/
def attrFieldText (t : CType) (o : CObj α) (rep : α → Py Str) (i : Nat) : CRes Str :=
  if h : i < t.members.length then do
    let nm ← CRes.ofPy (utf8Decode t.members[i].name .strict)
    let s ← pssGetItem o t.members[i].slot
    let r ← itemText rep s
    .ok (nm ++ [chEq] ++ r)
  else .exc (systemError s!"~In structseq_repr(), member {i} name is NULL for type {t.nameStr}")

/-- What `repr` would print if each label were followed by the value of that attribute, as in
`namedtuple`, whose `__repr__` prints `name=value` for each field name and its own value. -/
def attrReprSpec (t : CType) (o : CObj α) (rep : α → Py Str) : CRes Str :=
  match utf8Decode t.name .strict with
  | .error e => .exc e
  | .ok nm =>
    (catAll ((List.range o.size).map fun i => (attrFieldText t o rep i).map (sepOf i ++ ·))).map
      (fun body => nm ++ [chLParen] ++ body ++ [chRParen])

/-- For every type `PyStructSequence_NewType` builds and every object of its visible size, when
`repr` succeeds, every `name=value` pair it prints has `value == getattr(s, name)`. -/
def ReprLabelsMatchAttrs : Prop :=
  ∀ (α : Type) (d : Desc) (malloc : Nat → Bool) (rest : Py Unit) (b : Built) (o : CObj α)
    (rep : α → Py Str) (walloc : Int → Bool) (s : Str),
    newType d malloc rest = .ok b → (o.size : Int) = d.nInSeq →
    structseqRepr walloc b.type o rep = .ok s → attrReprSpec b.type o rep = .ok s

/-- Fields `a`, unnamed, `b`, with `n_in_sequence = 2`: `b` is hidden. Like `os.stat_result`,
whose visible slots 7-9 are unnamed and are followed by the hidden `st_atime`, ... -/
def descMid : Desc :=
  { name := lit "m.T", fields := [.named (lit "a"), .unnamed, .named (lit "b")], nInSeq := 2 }

def builtMid : Built :=
  { type := { name := lit "m.T", members := [⟨lit "a", 0⟩, ⟨lit "b", 2⟩], basicsize := 40,
              dict := honestDict 2 3 1 },
    matchArgs := [lit "a"] }

/-- `T((0, 1), {'b': 2})`: two visible items, the hidden `b`, and the block's spare slot. -/
def objMid : CObj Nat := { size := 2, slots := [.val 0, .val 1, .val 2, .junk] }

def repDigit (n : Nat) : Py Str := .ok [48 + n]

theorem reprLabelsMatchAttrs_refuted : ¬ ReprLabelsMatchAttrs := by
  intro h
  have hb : newType descMid (fun _ => true) (.ok ()) = .ok builtMid := rfl
  have hr : structseqRepr (fun _ => true) builtMid.type objMid repDigit = .ok (lit "m.T(a=0, b=1)") := rfl
  have := h Nat descMid _ _ builtMid objMid repDigit _ _ hb rfl hr
  have ha : attrReprSpec builtMid.type objMid repDigit = .ok (lit "m.T(a=0, b=2)") := rfl
  rw [ha] at this
  injection this with h'
  revert h'
  decide

/-! ## `PyStructSequence_New` and the index contract -/

/-- A type whose dict holds its own sizes: `v` visible fields, `n` fields, `u` unnamed, and
`tp_basicsize` holding the `n - v` hidden slots, as `NewTypeLayout` builds it. -/
def Honest (t : CType) (v n u : Nat) : Prop :=
  t.dict = honestDict v n u ∧ t.basicsize = 32 + 8 * (n - v) ∧ v ≤ n

theorem honest_nfields (v n u : Nat) : honestDict v n u "n_fields" = .ok (some (.int n)) := by
  simp [honestDict]

theorem honest_nseq (v n u : Nat) : honestDict v n u "n_sequence_fields" = .ok (some (.int v)) := by
  simp [honestDict]

theorem honest_nunnamed (v n u : Nat) : honestDict v n u "n_unnamed_fields" = .ok (some (.int u)) := by
  simp [honestDict]

theorem sizeOf_small (tp key : String) (d : TDict) (n : Nat) (h : d key = .ok (some (.int n)))
    (hn : n < 2 ^ 63) : sizeOrNull (getTypeAttrAsSize tp d key) = .ok n := by
  unfold getTypeAttrAsSize asSsize sizeOrNull
  rw [h]
  simp only
  rw [if_pos (by unfold ssizeMin ssizeMax; omega)]
  simp

/-- For every type whose size attributes are its own, with fewer than `2^57` fields (the desc's
16-byte fields and the 40-byte members both fit in the address space), `PyStructSequence_New` fails only with
`MemoryError` from the allocator, and otherwise returns an object with `Py_SIZE = v`,
`get_real_size = n`, its `n` field slots `NULL` and `n - v` spare slots after them. On it,
`PyStructSequence_SetItem`/`GetItem` at every index `0 ≤ i < n` (the documented range) write and
read slot `i` alone; in a release build nothing is checked, so an index outside the block,
`i < 0` or `i ≥ 2n - v`, is undefined behaviour. -/
def NewIndexContract : Prop :=
  ∀ (α : Type) (t : CType) (v n u : Nat) (malloc : Nat → Bool), Honest t v n u → n < 2 ^ 57 →
    (malloc (preSize + (32 + 8 * (n - v) + 8 * n)) = false ∧ pssNew (α := α) t malloc = .exc memoryError) ∨
    (malloc (preSize + (32 + 8 * (n - v) + 8 * n)) = true ∧
     ∃ o : CObj α, pssNew t malloc = .ok o ∧ o.size = v ∧ realSize t o.size = n ∧
      o.slots = List.replicate n .null ++ List.replicate (n - v) .junk ∧
      ∀ (i : Int) (x : α),
        (0 ≤ i → i < n → ∃ o', pssSetItem o i x = .ok o' ∧ o'.size = o.size ∧
          pssGetItem o' i = .ok (.val x) ∧ ∀ j : Int, j ≠ i → pssGetItem o' j = pssGetItem o j) ∧
        ((i < 0 ∨ (2 * n - v : Nat) ≤ i) → (pssSetItem o i x).isUB = true ∧ (pssGetItem o i).isUB = true))

theorem newIndexContract_proven : NewIndexContract := by
  intro α t v n u malloc ⟨hd, hb, hv⟩ hn
  have h1 : sizeOrNull (getTypeAttrAsSize t.nameStr t.dict "n_fields") = .ok n :=
    sizeOf_small _ _ _ n (by rw [hd]; exact honest_nfields v n u) (by omega)
  have h2 : sizeOrNull (getTypeAttrAsSize t.nameStr t.dict "n_sequence_fields") = .ok v :=
    sizeOf_small _ _ _ v (by rw [hd]; exact honest_nseq v n u) (by omega)
  have hraw : (t.basicsize + n * 8) % 2 ^ 64 = 32 + 8 * (n - v) + 8 * n := by
    rw [hb, Nat.mod_eq_of_lt (show 32 + 8 * (n - v) + n * 8 < 2 ^ 64 by omega)]; omega
  have hX8 : (32 + 8 * (n - v) + 8 * n + 7) / 8 * 8 = 32 + 8 * (n - v) + 8 * n := by omega
  have hround : ((32 + 8 * (n - v) + 8 * n + 7) / 8 * 8) % 2 ^ 64 = 32 + 8 * (n - v) + 8 * n := by
    rw [hX8]; exact Nat.mod_eq_of_lt (by omega)
  have hcap : ¬ (32 + 8 * (n - v) + 8 * n > ssizeMax.toNat - preSize) := by
    unfold ssizeMax preSize; omega
  unfold pssNew
  rw [h1]
  simp only [CRes.bind_ok]
  rw [h2]
  simp only [CRes.bind_ok]
  unfold gcNewVar
  simp only [hraw, hround]
  rw [if_neg hcap]
  cases hm : malloc (preSize + (32 + 8 * (n - v) + 8 * n)) with
  | false => left; exact ⟨rfl, rfl⟩
  | true =>
    right
    refine ⟨rfl, ?_⟩
    simp only [Bool.not_true, Bool.false_eq_true, if_false, CRes.bind_ok]
    rw [if_neg (show ¬ (32 + 8 * (n - v) + 8 * n < obItemOff) by unfold obItemOff; omega)]
    have hc : (32 + 8 * (n - v) + 8 * n - obItemOff) / 8 = n + (n - v) := by unfold obItemOff; omega
    rw [hc, if_neg (show ¬ (n > n + (n - v)) by omega)]
    refine ⟨_, rfl, rfl, ?_, ?_, ?_⟩
    · simp only [realSize, hb, obItemOff]; omega
    · rw [show n + (n - v) - n = n - v by omega]
    · intro i x
      generalize hL : (List.replicate n (Slot.null : Slot α) ++ List.replicate (n + (n - v) - n) (Slot.junk : Slot α)) = L
      have hlen : L.length = 2 * n - v := by rw [← hL]; simp; omega
      constructor
      · intro hi0 hin
        unfold pssSetItem writeSlot
        rw [if_neg (show ¬ (i < 0) by omega), if_pos (show i.toNat < L.length by rw [hlen]; omega)]
        simp only [CRes.bind_ok]
        refine ⟨_, rfl, rfl, ?_, ?_⟩
        · unfold pssGetItem readSlot
          rw [if_neg (show ¬ (i < 0) by omega)]
          simp only [List.length_set]
          rw [dif_pos (show i.toNat < L.length by rw [hlen]; omega)]
          simp
        · intro j hj
          unfold pssGetItem readSlot
          by_cases hj0 : j < 0
          · rw [if_pos hj0, if_pos hj0]
          · rw [if_neg hj0, if_neg hj0]
            simp only [List.length_set]
            by_cases hjl : j.toNat < L.length
            · rw [dif_pos hjl, dif_pos hjl]
              rw [List.getElem_set_ne (show i.toNat ≠ j.toNat by omega)]
            · rw [dif_neg hjl, dif_neg hjl]
      · intro hout
        unfold pssSetItem pssGetItem writeSlot readSlot
        rcases hout with hneg | hbig
        · rw [if_pos hneg, if_pos hneg]; exact ⟨rfl, rfl⟩
        · rw [if_neg (show ¬ (i < 0) by omega), if_neg (show ¬ (i < 0) by omega),
            if_neg (show ¬ (i.toNat < L.length) by rw [hlen]; omega),
            dif_neg (show ¬ (i.toNat < L.length) by rw [hlen]; omega)]
          exact ⟨rfl, rfl⟩

/-- `PyStructSequence_New` "Return[s] `NULL` with an exception set on failure"
(Doc/c-api/tuple.rst:235): for every type it never returns `NULL` with nothing set. -/
def NewSetsException : Prop :=
  ∀ (α : Type) (t : CType) (malloc : Nat → Bool), pssNew (α := α) t malloc ≠ .nullNoExc

/-- `os.terminal_size`: fields `columns`, `lines`, no hidden ones. -/
def termSize (d : TDict) : CType :=
  { name := lit "os.terminal_size", members := [⟨lit "columns", 0⟩, ⟨lit "lines", 1⟩],
    basicsize := 32, dict := d }

theorem newSetsException_refuted : ¬ NewSetsException := by
  intro h
  exact h Nat (termSize (honestDict 2 (-1) 0)) (fun _ => true) rfl

/-! ## Memory safety when the size attributes are rebound -/

/-- An object as the constructor leaves it: each of its `get_real_size` slots holds an object. -/
def WellFormed (t : CType) (o : CObj α) : Prop :=
  ∀ i, i < realSize t o.size → ∃ a, o.slots[i]? = some (.val a)

/-- `copy.replace(s, **kws)` never accesses memory outside what it allocated or read, for every
well-formed `s` and every state of the type's size attributes. -/
def ReplaceInBounds : Prop :=
  ∀ (α : Type) (t : CType) (o : CObj α) (kws : Option (KwArg α)) (malloc : Nat → Bool),
    WellFormed t o → (replaceC t o 0 kws malloc).isUB = false

/-- `os.terminal_size((1, 2))`, after `os.terminal_size.n_fields = n_sequence_fields = 0`. -/
theorem replaceInBounds_refuted : ¬ ReplaceInBounds := by
  intro h
  have := h Nat (termSize (honestDict 0 0 0)) { size := 2, slots := [.val 1, .val 2] } none (fun _ => true)
    (by
      intro i hi
      have : i < 2 := by simpa [realSize, termSize, obItemOff] using hi
      rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩)
  revert this
  decide

/-- `s.__reduce__()` never accesses memory out of bounds, for every well-formed `s` and every
state of the type's size attributes. -/
def ReduceInBounds : Prop :=
  ∀ (α : Type) (t : CType) (o : CObj α), WellFormed t o → (reduceC t o).isUB = false

/-- One visible field `a`, one hidden `b`; `n_unnamed_fields = 5` makes the hidden field's member
index `1 - 5`. -/
def oneHidden (d : TDict) : CType :=
  { name := lit "m.T", members := [⟨lit "a", 0⟩, ⟨lit "b", 1⟩], basicsize := 40, dict := d }

theorem reduceInBounds_refuted : ¬ ReduceInBounds := by
  intro h
  have := h Nat (oneHidden (honestDict 1 2 5)) { size := 1, slots := [.val 7, .val 8, .junk] }
    (by
      intro i hi
      have : i < 2 := by simpa [realSize, oneHidden, obItemOff] using hi
      rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
      · exact ⟨7, rfl⟩
      · exact ⟨8, rfl⟩)
  revert this
  decide

/-- The constructor never accesses memory out of bounds when the type's size attributes are its
own on entry, whatever Python code converting the argument does. -/
def NewImplInBounds : Prop :=
  ∀ (α : Type) (t : CType) (v n u : Nat) (arg : FastArg α) (dict : Option (CDictArg α)) (none_ : α)
    (malloc : Nat → Bool), Honest t v n u → (newImplC t arg dict none_ malloc).isUB = false

/-- `os.terminal_size(it)` where iterating `it` sets `n_fields = n_sequence_fields = 0` and yields
two items. -/
theorem newImplInBounds_refuted : ¬ NewImplInBounds := by
  intro h
  have := h Nat (termSize (honestDict 2 2 0)) 2 2 0 { res := .ok [1, 2], dictAfter := honestDict 0 0 0 }
    none 0 (fun _ => true) ⟨rfl, rfl, by omega⟩
  revert this
  decide

end PyLean.TypeObj.StructSeq
