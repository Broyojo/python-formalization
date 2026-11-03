import PyLean.TypeObj.StructSeqHonest

/-!
# Exact outcomes of `__reduce__`, `__replace__` and the constructor on the C model

See `StructSeqHonest.lean` for the setting (`HonestLayout`).
-/

namespace PyLean.TypeObj.StructSeq

open PyLean PyLean.UnicodeObj

variable {α : Type}

/-! ## `__reduce__` -/

/-- The hidden fields' `(name, value)` pairs from field `i` on: the name is
`tp_members[i - u].name`, decoded, or its decoding error. -/
def redFill (t : CType) (u : Nat) : Nat → List α → CRes (List (Str × α))
  | _, [] => .ok []
  | i, x :: xs => do
    let key ← CRes.ofPy (utf8Decode (t.members.getD (i - u) ⟨[], 0⟩).name .strict)
    let rest ← redFill t u (i + 1) xs
    .ok ((key, x) :: rest)

theorem fromArray_vals (vals : List α) (rest : List (Slot α)) :
    ∀ k, k ≤ vals.length → fromArray (vals.map Slot.val ++ rest) k = .ok (vals.take k) := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    simp only [fromArray]
    rw [ih (by omega)]
    simp only [CRes.bind_ok]
    rw [read_vals vals rest k (by omega)]
    simp only [CRes.bind_ok, deref]
    rw [List.take_succ_eq_append_getElem (by omega)]

theorem reduceLoop_vals (t : CType) (vals : List α) (rest : List (Slot α)) (sz u : Nat) :
    ∀ fuel i, u ≤ i → i + fuel ≤ vals.length → i + fuel ≤ u + t.members.length →
      reduceLoop t ⟨sz, vals.map Slot.val ++ rest⟩ u fuel i = redFill t u i ((vals.drop i).take fuel) := by
  intro fuel
  induction fuel with
  | zero => intro i _ _ _; simp [reduceLoop, redFill]
  | succ fuel ih =>
    intro i hu h1 h2
    rw [drop_take_succ vals i fuel (by omega)]
    simp only [reduceLoop, redFill]
    rw [memberName_getD _ i u hu (by omega)]
    simp only [CRes.bind_ok, fromCString]
    cases CRes.ofPy (utf8Decode (t.members.getD (i - u) ⟨[], 0⟩).name .strict) with
    | ok key =>
      simp only [CRes.bind_ok]
      rw [read_vals vals rest i (by omega)]
      simp only [CRes.bind_ok, deref]
      rw [ih (i + 1) (by omega) (by omega) (by omega)]
    | exc e => rfl
    | nullNoExc => rfl
    | ub w => rfl

/-- `s.__reduce__()`: when reading `n_unnamed_fields` fails, that failure, for every type and
object; and, while the sizes are honest, for every object whose `n` fields hold `vals`, exactly
`(vals[:v], [(name_i, vals[i]) for the hidden fields i])` with `name_i = tp_members[i - u].name`,
or the first name that is not UTF-8. -/
def ReduceSpecC : Prop :=
  (∀ (α : Type) (t : CType) (o : CObj α) (r : CRes Nat),
    sizeOrNull (getTypeAttrAsSize t.nameStr t.dict "n_unnamed_fields") = r → (∀ c, r ≠ .ok c) →
    reduceC t o = r.bind fun _ => .nullNoExc) ∧
  ∀ (α : Type) (t : CType) (v n u : Nat) (vals : List α) (rest : List (Slot α)),
    HonestLayout t v n u → n < 2 ^ 57 → vals.length = n →
    reduceC t ⟨v, vals.map Slot.val ++ rest⟩ =
      (redFill t u v (vals.drop v)).map (fun d => (vals.take v, d))

theorem reduceSpecC_proven : ReduceSpecC := by
  constructor
  · intro α t o r hr hne
    unfold reduceC
    rw [hr]
    cases r with
    | ok c => exact absurd rfl (hne c)
    | exc e => rfl
    | nullNoExc => rfl
    | ub w => rfl
  · intro α t v n u vals rest h hn hl
    obtain ⟨_, _, hu⟩ := honest_reads h hn
    have hrs := realSize_honest h.1
    obtain ⟨⟨_, _, hv⟩, hm, huv⟩ := h
    unfold reduceC
    simp only
    rw [hu, hrs]
    simp only [CRes.bind_ok]
    rw [fromArray_vals vals rest v (by omega)]
    simp only [CRes.bind_ok]
    rw [reduceLoop_vals t vals rest v u (n - v) v huv (by omega) (by omega)]
    rw [show (vals.drop v).take (n - v) = vals.drop v by
      rw [List.take_of_length_le]; simp; omega]
    cases redFill t u v (vals.drop v) <;> rfl

/-! ## `__replace__` -/

/-- The new values from field `i` on: the keyword popped for field `i`'s name, or the old
value; the first decoding error or pop error wins. -/
def kwFill (t : CType) (pop : Nat → Str → Py (Option α)) : Nat → List α → CRes (List α)
  | _, [] => .ok []
  | i, x :: xs => do
    let key ← CRes.ofPy (utf8Decode (t.members.getD i ⟨[], 0⟩).name .strict)
    let got ← CRes.ofPy (pop i key)
    let rest ← kwFill t pop (i + 1) xs
    .ok (got.getD x :: rest)

theorem copyLoop_vals (vals : List α) (rest J : List (Slot α)) (sz : Nat) :
    ∀ fuel (pre : List α) m i, i = pre.length → fuel ≤ m → i + fuel ≤ vals.length →
      replaceCopyLoop ⟨sz, vals.map Slot.val ++ rest⟩ fuel i (shape pre m J) =
        .ok (shape (pre ++ (vals.drop i).take fuel) (m - fuel) J) := by
  intro fuel
  induction fuel with
  | zero => intro pre m i _ _ _; simp [replaceCopyLoop]
  | succ fuel ih =>
    intro pre m i hi hm hv
    subst hi
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [replaceCopyLoop]
    rw [read_vals vals rest pre.length (by omega)]
    simp only [CRes.bind_ok, deref]
    rw [write_shape]
    simp only [CRes.bind_ok]
    rw [ih (pre ++ [vals[pre.length]]) m' (pre.length + 1) (by simp) (by omega) (by omega),
      drop_take_succ vals pre.length fuel (by omega)]
    simp [show m' + 1 - (fuel + 1) = m' - fuel by omega]

theorem kwLoop_vals (t : CType) (pop : Nat → Str → Py (Option α)) (vals : List α)
    (rest J : List (Slot α)) (sz : Nat) :
    ∀ fuel (pre : List α) m i, i = pre.length → fuel ≤ m → i + fuel ≤ vals.length →
      i + fuel ≤ t.members.length →
      replaceKwLoop t ⟨sz, vals.map Slot.val ++ rest⟩ pop fuel i (shape pre m J) =
        (kwFill t pop i ((vals.drop i).take fuel)).map (fun ys => shape (pre ++ ys) (m - fuel) J) := by
  intro fuel
  induction fuel with
  | zero => intro pre m i _ _ _ _; simp [replaceKwLoop, kwFill, CRes.map]
  | succ fuel ih =>
    intro pre m i hi hm hv hmem
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [drop_take_succ vals i fuel (by omega)]
    simp only [replaceKwLoop, kwFill]
    rw [memberName_nat _ i (by omega)]
    simp only [CRes.bind_ok, fromCString]
    cases CRes.ofPy (utf8Decode (t.members.getD i ⟨[], 0⟩).name .strict) with
    | ok key =>
      simp only [CRes.bind_ok]
      cases CRes.ofPy (pop i key) with
      | ok got =>
        simp only [CRes.bind_ok]
        have hk : ∀ x : α, (do
              let res ← writeSlot (shape pre (m' + 1) J) i (Slot.val x) "structseq_replace: write past the new block"
              replaceKwLoop t ⟨sz, vals.map Slot.val ++ rest⟩ pop fuel (i + 1) res) =
            CRes.map (fun ys => shape (pre ++ ys) (m' + 1 - (fuel + 1)) J) (do
              let rest ← kwFill t pop (i + 1) (List.take fuel (List.drop (i + 1) vals))
              CRes.ok (x :: rest)) := by
          intro x
          rw [hi, write_shape]
          simp only [CRes.bind_ok]
          rw [ih (pre ++ [x]) m' (pre.length + 1) (by simp) (by omega) (by omega) (by omega)]
          cases kwFill t pop (pre.length + 1) ((vals.drop (pre.length + 1)).take fuel) with
          | ok ys => simp [CRes.map, show m' + 1 - (fuel + 1) = m' - fuel by omega]
          | exc e => rfl
          | nullNoExc => rfl
          | ub w => rfl
        cases got with
        | some x =>
          simp only [CRes.pure_eq, CRes.bind_ok, Option.getD_some]
          exact hk x
        | none =>
          rw [read_vals vals rest i (by omega)]
          simp only [CRes.bind_ok, deref, Option.getD_none]
          exact hk vals[i]
      | exc e => rfl
      | nullNoExc => rfl
      | ub w => rfl
    | exc e => rfl
    | nullNoExc => rfl
    | ub w => rfl

/-- `copy.replace(s, **kws)` while the sizes are honest (fewer than `2^57` fields), for every
object whose `n` fields hold `vals`, every keyword dict (each pop an arbitrary outcome, as a
str-subclass key's `__eq__` can make it), every allocator outcome: positional arguments are
refused, then a type with unnamed fields, then the allocator's `MemoryError`; with no keywords
the copy has `vals`; otherwise field `i` takes the value popped under its name or keeps
`vals[i]`, the first decoding or pop error wins, and keywords left over raise `TypeError`. The
spare `n - v` slots after the fields are junk. -/
def ReplaceSpecC : Prop :=
  ∀ (α : Type) (t : CType) (v n u : Nat) (vals : List α) (rest : List (Slot α)) (nargs : Nat)
    (kws : Option (KwArg α)) (malloc : Nat → Bool),
    HonestLayout t v n u → n < 2 ^ 57 → vals.length = n →
    replaceC t ⟨v, vals.map Slot.val ++ rest⟩ nargs kws malloc =
      if nargs ≠ 0 then .exc (.typeError "__replace__() takes no positional arguments")
      else if u > 0 then
        .exc (.typeError s!"~__replace__() is not supported for {t.nameStr} because it has unnamed field(s)")
      else if malloc (preSize + (32 + 8 * (n - v) + 8 * n)) = false then .exc memoryError
      else match kws with
        | none => .ok ⟨v, vals.map Slot.val ++ List.replicate (n - v) .junk⟩
        | some kw => (kwFill t kw.pop 0 vals).bind fun ys =>
            if kw.sizeAfter > 0 then .exc (.typeError "~Got unexpected field name(s): %R")
            else .ok ⟨v, ys.map Slot.val ++ List.replicate (n - v) .junk⟩

theorem replaceSpecC_proven : ReplaceSpecC := by
  intro α t v n u vals rest nargs kws malloc h hn hl
  obtain ⟨_, _, hu⟩ := honest_reads h hn
  have hrs := realSize_honest h.1
  have hnew := newIndexContract_proven α t v n u malloc h.1 hn
  obtain ⟨⟨_, _, hv⟩, hm, huv⟩ := h
  unfold replaceC
  by_cases ha : nargs ≠ 0
  · rw [if_pos ha, if_pos ha]
  · rw [if_neg ha, if_neg ha]
    simp only
    rw [hrs, hu]
    simp only [CRes.bind_ok]
    by_cases hu0 : u > 0
    · rw [if_pos hu0, if_pos hu0]
    · rw [if_neg hu0, if_neg hu0]
      have hu0' : u = 0 := by omega
      subst hu0'
      rcases hnew with ⟨hmf, hme⟩ | ⟨hmt, o, ho, hsz, _, hslots, _⟩
      · rw [hme, if_pos hmf]; rfl
      · rw [ho, if_neg (by rw [hmt]; simp)]
        simp only [CRes.bind_ok]
        have hsh : o.slots = shape ([] : List α) n (List.replicate (n - v) .junk) := by
          rw [hslots]; simp [shape]
        cases kws with
        | none =>
          simp only
          rw [hsh, copyLoop_vals vals rest _ v n [] n 0 rfl (by omega) (by omega)]
          simp only [CRes.bind_ok, List.drop_zero, List.nil_append, Nat.sub_self]
          rw [List.take_of_length_le (by omega)]
          simp [shape, hsz]
        | some kw =>
          simp only
          rw [hsh, kwLoop_vals t kw.pop vals rest _ v n [] n 0 rfl (by omega) (by omega) (by omega)]
          simp only [List.drop_zero, List.nil_append, Nat.sub_self]
          rw [List.take_of_length_le (by omega)]
          cases kwFill t kw.pop 0 vals with
          | ok ys =>
            simp only [CRes.map, CRes.bind_ok]
            split <;> simp [shape, hsz, CRes.bind, *]
          | exc e => rfl
          | nullNoExc => rfl
          | ub w => rfl

/-! ## The constructor -/

theorem newCopyLoop_shape (J : List (Slot α)) :
    ∀ (xs pre : List α) m i, i = pre.length → xs.length ≤ m →
      newCopyLoop xs i (shape pre m J) = .ok (shape (pre ++ xs) (m - xs.length) J) := by
  intro xs
  induction xs with
  | nil => intro pre m i _ _; simp [newCopyLoop]
  | cons x xs ih =>
    intro pre m i hi hm
    subst hi
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by simp at hm; omega⟩
    simp only [newCopyLoop]
    rw [write_shape]
    simp only [CRes.bind_ok]
    rw [ih (pre ++ [x]) m' (pre.length + 1) (by simp) (by simp at hm; omega)]
    simp [show m' + 1 - (xs.length + 1) = m' - xs.length by omega]

theorem newNoneLoop_shape (J : List (Slot α)) (none_ : α) :
    ∀ fuel (pre : List α) m i, i = pre.length → fuel ≤ m →
      newNoneLoop none_ fuel i (shape pre m J) = .ok (shape (pre ++ List.replicate fuel none_) (m - fuel) J) := by
  intro fuel
  induction fuel with
  | zero => intro pre m i _ _; simp [newNoneLoop]
  | succ fuel ih =>
    intro pre m i hi hm
    subst hi
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [newNoneLoop]
    rw [write_shape]
    simp only [CRes.bind_ok]
    rw [ih (pre ++ [none_]) m' (pre.length + 1) (by simp) (by omega)]
    simp [List.replicate_succ, show m' + 1 - (fuel + 1) = m' - fuel by omega]

/-- The `dict` loop from field `i` on: the value looked up under `tp_members[i - u].name`, or
`None`, and how many were found; the first decoding or lookup error wins. -/
def dictFill (t : CType) (none_ : α) (look : Nat → Str → Py (Option α)) (u : Nat) :
    Nat → Nat → CRes (List α × Nat)
  | 0, _ => .ok ([], 0)
  | fuel + 1, i => do
    let key ← CRes.ofPy (utf8Decode (t.members.getD (i - u) ⟨[], 0⟩).name .strict)
    let got ← CRes.ofPy (look i key)
    let r ← dictFill t none_ look u fuel (i + 1)
    .ok (match got with
      | some x => (x :: r.1, r.2 + 1)
      | none => (none_ :: r.1, r.2))

theorem newDictLoop_shape (t : CType) (none_ : α) (look : Nat → Str → Py (Option α)) (u : Nat)
    (J : List (Slot α)) :
    ∀ fuel (pre : List α) m i found, i = pre.length → fuel ≤ m → u ≤ i →
      i + fuel ≤ u + t.members.length →
      newDictLoop t none_ look u fuel i (shape pre m J) found =
        (dictFill t none_ look u fuel i).map (fun r => (shape (pre ++ r.1) (m - fuel) J, found + r.2)) := by
  intro fuel
  induction fuel with
  | zero => intro pre m i found _ _ _ _; simp [newDictLoop, dictFill, CRes.map]
  | succ fuel ih =>
    intro pre m i found hi hm hu hmem
    subst hi
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [newDictLoop, dictFill]
    rw [memberName_getD _ pre.length u hu (by omega)]
    simp only [CRes.bind_ok, fromCString]
    cases CRes.ofPy (utf8Decode (t.members.getD (pre.length - u) ⟨[], 0⟩).name .strict) with
    | ok key =>
      simp only [CRes.bind_ok]
      cases CRes.ofPy (look pre.length key) with
      | ok got =>
        simp only [CRes.bind_ok]
        cases got with
        | some x =>
          simp only
          rw [write_shape]
          simp only [CRes.bind_ok]
          rw [ih (pre ++ [x]) m' (pre.length + 1) (found + 1) (by simp) (by omega) (by omega) (by omega)]
          cases dictFill t none_ look u fuel (pre.length + 1) with
          | ok r => simp [CRes.map, show m' + 1 - (fuel + 1) = m' - fuel by omega]; omega
          | exc e => rfl
          | nullNoExc => rfl
          | ub w => rfl
        | none =>
          simp only
          rw [write_shape]
          simp only [CRes.bind_ok]
          rw [ih (pre ++ [none_]) m' (pre.length + 1) found (by simp) (by omega) (by omega) (by omega)]
          cases dictFill t none_ look u fuel (pre.length + 1) with
          | ok r => simp [CRes.map, show m' + 1 - (fuel + 1) = m' - fuel by omega]
          | exc e => rfl
          | nullNoExc => rfl
          | ub w => rfl
      | exc e => rfl
      | nullNoExc => rfl
      | ub w => rfl
    | exc e => rfl
    | nullNoExc => rfl
    | ub w => rfl

/-- The three length checks of :200-226. -/
def lenCheck (name : String) (v n len : Nat) : Option PyExc :=
  if v ≠ n then
    if len < v then some (.typeError s!"~{name}() takes an at least {v}-sequence ({len}-sequence given)")
    else if len > n then some (.typeError s!"~{name}() takes an at most {n}-sequence ({len}-sequence given)")
    else none
  else if len ≠ v then some (.typeError s!"~{name}() takes a {v}-sequence ({len}-sequence given)")
  else none

/-- `T(arg, dict)` while the sizes are honest and stay so (fewer than `2^57` fields): the
argument's conversion error; `TypeError` for a `dict` that is not a dict; the length checks
(`v ≤ len ≤ n`, or `len = v` when there are no hidden fields); the allocator's `MemoryError`;
then the `len` items followed, for each hidden field, by the value the `dict` argument holds
under its name (each lookup an arbitrary outcome: a key's `__eq__` can raise or change the dict)
or `None`, with `TypeError` when the dict's size after the lookups exceeds the number found. An
empty dict (size zero at :238) is no dict. -/
def NewImplSpecC : Prop :=
  ∀ (α : Type) (t : CType) (v n u : Nat) (arg : FastArg α) (dict : Option (CDictArg α)) (none_ : α)
    (malloc : Nat → Bool), HonestLayout t v n u → n < 2 ^ 57 → arg.dictAfter = t.dict →
    newImplC t arg dict none_ malloc =
      match arg.res with
      | .error e => .exc e
      | .ok xs =>
        match dict with
        | some .notDict => .exc (.typeError s!"~{t.nameStr}() takes a dict as second arg, if any")
        | _ =>
          match lenCheck t.nameStr v n xs.length with
          | some e => .exc e
          | none =>
            if malloc (preSize + (32 + 8 * (n - v) + 8 * n)) = false then .exc memoryError
            else
              let J := List.replicate (n - v) (Slot.junk : Slot α)
              let plain : CRes (CObj α) :=
                .ok ⟨v, (xs ++ List.replicate (n - xs.length) none_).map Slot.val ++ J⟩
              match dict with
              | some (.dict look size0 size1) =>
                if size0 > 0 then
                  (dictFill t none_ look u (n - xs.length) xs.length).bind fun r =>
                    if size1 > r.2 then
                      .exc (.typeError s!"~{t.nameStr}() got duplicate or unexpected field name(s)")
                    else .ok ⟨v, (xs ++ r.1).map Slot.val ++ J⟩
                else plain
              | _ => plain

theorem lenCheck_none {name : String} {v n len : Nat} (hv : v ≤ n) (h : lenCheck name v n len = none) :
    v ≤ len ∧ len ≤ n := by
  unfold lenCheck at h
  split at h
  · split at h
    · cases h
    · split at h
      · cases h
      · omega
  · split at h
    · cases h
    · omega

theorem newImplSpecC_proven : NewImplSpecC := by
  intro α t v n u arg dict none_ malloc h hn hda
  obtain ⟨hnf, hns, hnu⟩ := honest_reads h hn
  have hnew := newIndexContract_proven α t v n u malloc h.1 hn
  obtain ⟨⟨_, _, hv⟩, hm, huv⟩ := h
  have ht : ({ t with dict := arg.dictAfter } : CType) = t := by rw [hda]
  unfold newImplC
  rw [hns, hnf, hnu]
  simp only [CRes.bind_ok]
  rw [ht]
  cases hres : arg.res with
  | error e => rfl
  | ok xs =>
    simp only [CRes.ofPy, CRes.bind_ok]
    have hlen : (if v ≠ n then
          if xs.length < v then some (PyExc.typeError s!"~{t.nameStr}() takes an at least {v}-sequence ({xs.length}-sequence given)")
          else if xs.length > n then some (PyExc.typeError s!"~{t.nameStr}() takes an at most {n}-sequence ({xs.length}-sequence given)")
          else none
        else if xs.length ≠ v then some (PyExc.typeError s!"~{t.nameStr}() takes a {v}-sequence ({xs.length}-sequence given)")
        else none) = lenCheck t.nameStr v n xs.length := rfl
    cases dict with
    | some d =>
      cases d with
      | notDict => rfl
      | dict look size0 size1 =>
        simp only
        rw [hlen]
        cases hl : lenCheck t.nameStr v n xs.length with
        | some e => rfl
        | none =>
          obtain ⟨hl1, hl2⟩ := lenCheck_none hv hl
          simp only
          rcases hnew with ⟨hmf, hme⟩ | ⟨hmt, o, ho, hsz, _, hslots, _⟩
          · rw [hme, if_pos hmf]; rfl
          · rw [ho, if_neg (by rw [hmt]; simp)]
            simp only [CRes.bind_ok]
            have hsh : o.slots = shape ([] : List α) n (List.replicate (n - v) .junk) := by
              rw [hslots]; simp [shape]
            rw [hsh, newCopyLoop_shape _ xs [] n 0 rfl hl2]
            simp only [CRes.bind_ok, List.nil_append]
            by_cases hs0 : size0 > 0
            · rw [if_pos hs0, if_pos hs0]
              rw [newDictLoop_shape t none_ look u _ (n - xs.length) xs (n - xs.length) xs.length 0 rfl
                (Nat.le_refl _) (by omega) (by omega)]
              cases dictFill t none_ look u (n - xs.length) xs.length with
              | ok r =>
                simp only [CRes.map, CRes.bind_ok, Nat.zero_add]
                split <;> simp [shape, hsz, CRes.bind, *]
              | exc e => rfl
              | nullNoExc => rfl
              | ub w => rfl
            · rw [if_neg hs0, if_neg hs0]
              rw [newNoneLoop_shape _ none_ (n - xs.length) xs (n - xs.length) xs.length rfl (Nat.le_refl _)]
              simp [shape, hsz]
    | none =>
      simp only
      rw [hlen]
      cases hl : lenCheck t.nameStr v n xs.length with
      | some e => rfl
      | none =>
        obtain ⟨hl1, hl2⟩ := lenCheck_none hv hl
        simp only
        rcases hnew with ⟨hmf, hme⟩ | ⟨hmt, o, ho, hsz, _, hslots, _⟩
        · rw [hme, if_pos hmf]; rfl
        · rw [ho, if_neg (by rw [hmt]; simp)]
          simp only [CRes.bind_ok]
          have hsh : o.slots = shape ([] : List α) n (List.replicate (n - v) .junk) := by
            rw [hslots]; simp [shape]
          rw [hsh, newCopyLoop_shape _ xs [] n 0 rfl hl2]
          simp only [CRes.bind_ok, List.nil_append]
          rw [newNoneLoop_shape _ none_ (n - xs.length) xs (n - xs.length) xs.length rfl (Nat.le_refl _)]
          simp [shape, hsz]

end PyLean.TypeObj.StructSeq
