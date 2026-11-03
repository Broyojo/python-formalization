import PyLean.TypeObj.StructSeqSpec

/-!
# `PyStructSequence_NewType`: when it accepts a desc, and what it refuses

`NewTypeOutcomes` (proven): `MemoryError` when `tp_members` cannot be allocated; the failure of
the rest of `PyType_FromSpecWithBases`; for a valid desc (`0 ≤ n_in_sequence ≤ #fields`,
fewer than `2^28 - 4` hidden fields) the type of `NewTypeLayout`, unless a visible name is not
UTF-8; `TypeError` for `n_in_sequence = #fields + 1 .. #fields + 3`; `SystemError` for
`#fields + 5` and above and for a negative one (while `hidden` stays inside a C `int`).

Two refutations show what `PyStructSequence_NewType` does not check:
`NewTypeBasicsizeExact` (the `(int)` cast at :775 wraps for `2^29` hidden fields, giving a
`tp_basicsize` that counts none of them) and `ReduceInBoundsBuilt` (a desc with unnamed hidden
fields, which structseq.c:23-24 forbids and nothing enforces, makes `__reduce__` read
`tp_members[-1]`).
-/

namespace PyLean.TypeObj.StructSeq

open PyLean PyLean.UnicodeObj

theorem toCInt_id (x : Int) (h0 : -2 ^ 31 ≤ x) (h1 : x < 2 ^ 31) : toCInt x = x := by
  unfold toCInt
  by_cases hx : 0 ≤ x
  · have : x % 2 ^ 32 = x := Int.emod_eq_of_lt hx (by omega)
    rw [this, if_neg (by omega)]
  · have : x % 2 ^ 32 = x + 2 ^ 32 := by omega
    rw [this, if_pos (by omega)]
    omega

theorem matchArgsLoop_eq (fs : List FName) :
    ∀ (k i : Nat), i + k ≤ fs.length →
      matchArgsLoop fs k i = CRes.ofPy ((namesOf ((fs.drop i).take k)).mapM (fun n => utf8Decode n .strict)) := by
  intro k
  induction k with
  | zero => intro i _; simp [matchArgsLoop, namesOf]; rfl
  | succ k ih =>
    intro i hle
    have hi : i < fs.length := by omega
    simp only [matchArgsLoop]
    rw [dif_pos hi]
    have hdrop : (fs.drop i).take (k + 1) = fs[i] :: (fs.drop (i + 1)).take k := by
      rw [List.drop_eq_getElem_cons hi]; rfl
    rw [hdrop, ih (i + 1) (by omega)]
    cases hf : fs[i] with
    | unnamed =>
      simp only [CRes.pure_eq, CRes.bind_ok, namesOf, List.filterMap_cons]
      cases (List.filterMap (fun f => match f with | .named b => some b | .unnamed => none)
          ((fs.drop (i + 1)).take k)).mapM (fun n => utf8Decode n .strict) <;> rfl
    | named b =>
      simp only [namesOf, List.filterMap_cons, List.mapM_cons]
      cases hd : utf8Decode b .strict with
      | error e => rfl
      | ok sb =>
        simp only [CRes.ofPy, CRes.bind_ok, CRes.pure_eq]
        cases (List.filterMap (fun f => match f with | .named b => some b | .unnamed => none)
            ((fs.drop (i + 1)).take k)).mapM (fun n => utf8Decode n .strict) <;> rfl

/-- What `PyStructSequence_NewType` does with every desc, every allocator and every outcome of
the rest of `PyType_FromSpecWithBases`. A named field called `__weaklistoffset__`,
`__dictoffset__` or `__vectorcalloffset__` is refused with `SystemError` (`specialCheck`); the
other cases are stated for descs without such a field. -/
def NewTypeOutcomes : Prop :=
  ∀ (d : Desc) (malloc : Nat → Bool) (rest : Py Unit),
    (malloc ((d.fields.length - d.fields.count .unnamed + 1) * 40) = false →
      newType d malloc rest = .exc memoryError) ∧
    (malloc ((d.fields.length - d.fields.count .unnamed + 1) * 40) = true →
      (∀ e, rest = .error e → newType d malloc rest = .exc e) ∧
      (rest = .ok () → specialCheck (namedFields d.fields) = none → 0 ≤ d.nInSeq →
        d.nInSeq ≤ d.fields.length → (d.fields.length : Int) - d.nInSeq < 2 ^ 28 - 4 →
        newType d malloc rest =
          (CRes.ofPy ((namesOf (d.fields.take d.nInSeq.toNat)).mapM (fun b => utf8Decode b .strict))).map
            fun ma =>
              { type := { name := d.name, members := namedFields d.fields,
                          basicsize := (32 + 8 * ((d.fields.length : Int) - d.nInSeq)).toNat,
                          dict := honestDict d.nInSeq d.fields.length (d.fields.count .unnamed) },
                matchArgs := ma }) ∧
      (rest = .ok () → specialCheck (namedFields d.fields) = none →
        (d.fields.length : Int) + 1 ≤ d.nInSeq → d.nInSeq ≤ d.fields.length + 3 →
        ∃ m, newType d malloc rest = .exc (.typeError m)) ∧
      (rest = .ok () → (d.fields.length : Int) + 5 ≤ d.nInSeq → d.nInSeq - d.fields.length < 2 ^ 28 →
        newType d malloc rest =
          .exc (systemError "Cannot extend variable-size class without Py_TPFLAGS_ITEMS_AT_END.")) ∧
      (rest = .ok () → specialCheck (namedFields d.fields) = none → d.nInSeq < 0 →
        (d.fields.length : Int) - d.nInSeq < 2 ^ 28 - 4 →
        newType d malloc rest =
          .exc (systemError "~Objects/tupleobject.c:40: bad argument to internal function")) ∧
      (∀ e, rest = .ok () → specialCheck (namedFields d.fields) = some e →
        d.nInSeq ≤ d.fields.length + 4 → (d.fields.length : Int) - d.nInSeq < 2 ^ 28 - 4 →
        newType d malloc rest = .exc e))

theorem initMembers_named (fs : List FName) : initMembersLoop fs 0 [] = namedFields fs := by
  rw [initMembersLoop_eq]
  simp [namedFields, List.range_eq_range']

theorem newTypeOutcomes_proven : NewTypeOutcomes := by
  intro d malloc rest
  have hbase : ∀ (hm : malloc ((d.fields.length - d.fields.count .unnamed + 1) * 40) = true),
      newType d malloc rest =
        (fromSpecBasicsize d.name (namedFields d.fields)
            (toCInt (40 + ((d.fields.length : Int) - d.nInSeq - 1) * 8)) rest).bind
          fun bs => (initDict d d.fields.length (d.fields.count .unnamed)).bind fun r =>
            .ok { type := { name := d.name, members := namedFields d.fields, basicsize := bs,
                            dict := r.1 }, matchArgs := r.2 } := by
    intro hm
    unfold newType
    rw [countMembers_eq]
    simp only
    unfold initializeMembers
    simp only [hm, Bool.not_true, Bool.false_eq_true, if_false, CRes.bind_ok, List.take_length,
      initMembers_named]
    rfl
  refine ⟨fun hm => ?_, fun hm => ⟨fun e he => ?_, fun hr hs h0 h1 h2 => ?_, fun hr hs h1 h2 => ?_,
    fun hr h1 h2 => ?_, fun hr hs h1 h2 => ?_, fun e hr hs h1 h2 => ?_⟩⟩
  · unfold newType
    rw [countMembers_eq]
    simp only
    unfold initializeMembers
    simp [hm]
  · rw [hbase hm, he]; rfl
  · rw [hbase hm, hr]
    simp only [fromSpecBasicsize]
    rw [toCInt_id _ (by omega) (by omega), if_neg (by omega)]
    rw [if_neg (show ¬ (40 + ((d.fields.length : Int) - d.nInSeq - 1) * 8 = 0) by omega)]
    simp only [hs]
    rw [if_neg (show ¬ ((40 + ((d.fields.length : Int) - d.nInSeq - 1) * 8).toNat < 32) by omega)]
    simp only [CRes.bind_ok, initDict]
    rw [if_neg (by omega), matchArgsLoop_eq d.fields _ 0 (by omega)]
    simp only [List.drop_zero, List.nil_append]
    cases (namesOf (d.fields.take d.nInSeq.toNat)).mapM (fun b => utf8Decode b .strict) with
    | error e => rfl
    | ok ma =>
      simp only [CRes.ofPy, CRes.bind_ok, CRes.map, CRes.bind]
      congr 3
      congr 1; omega
  · rw [hbase hm, hr]
    simp only [fromSpecBasicsize]
    rw [toCInt_id _ (by omega) (by omega), if_neg (by omega)]
    rw [if_neg (show ¬ (40 + ((d.fields.length : Int) - d.nInSeq - 1) * 8 = 0) by omega)]
    simp only [hs]
    rw [if_pos (show (40 + ((d.fields.length : Int) - d.nInSeq - 1) * 8).toNat < 32 by omega)]
    exact ⟨_, rfl⟩
  · rw [hbase hm, hr]
    simp only [fromSpecBasicsize]
    rw [toCInt_id _ (by omega) (by omega), if_pos (by omega)]
    rfl
  · rw [hbase hm, hr]
    simp only [fromSpecBasicsize]
    rw [toCInt_id _ (by omega) (by omega), if_neg (by omega)]
    rw [if_neg (show ¬ (40 + ((d.fields.length : Int) - d.nInSeq - 1) * 8 = 0) by omega)]
    simp only [hs]
    rw [if_neg (show ¬ ((40 + ((d.fields.length : Int) - d.nInSeq - 1) * 8).toNat < 32) by omega)]
    simp only [CRes.bind_ok, initDict]
    rw [if_pos h1]
    rfl
  · rw [hbase hm, hr]
    simp only [fromSpecBasicsize]
    rw [toCInt_id _ (by omega) (by omega), if_neg (by omega)]
    simp only [hs]
    rfl

/-! ## The `(int)` cast of the basicsize -/

/-- Every type `PyStructSequence_NewType` builds has `tp_basicsize = 32 + 8 * hidden`, so that
`get_real_size` counts its hidden fields. -/
def NewTypeBasicsizeExact : Prop :=
  ∀ (d : Desc) (malloc : Nat → Bool) (rest : Py Unit) (b : Built), newType d malloc rest = .ok b →
    (b.type.basicsize : Int) = 32 + 8 * ((d.fields.length : Int) - d.nInSeq)

theorem initMembersLoop_unnamed (k i : Nat) (acc : List Member) :
    initMembersLoop (List.replicate k .unnamed) i acc = acc := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih => simp only [List.replicate_succ, initMembersLoop]; exact ih (i + 1)

theorem newType_unnamed (nm : Bytes) (k : Nat) :
    newType { name := nm, fields := List.replicate k .unnamed, nInSeq := 0 } (fun _ => true) (.ok ()) =
      (fromSpecBasicsize nm [] (toCInt (40 + ((k : Int) - 0 - 1) * 8)) (.ok ())).bind fun bs =>
        .ok { type := { name := nm, members := [], basicsize := bs, dict := honestDict 0 k k },
              matchArgs := [] } := by
  unfold newType
  rw [countMembers_eq]
  simp only [List.length_replicate, List.count_replicate_self]
  unfold initializeMembers
  simp only [Bool.not_true, Bool.false_eq_true, if_false, CRes.bind_ok]
  rw [List.take_of_length_le (by simp), initMembersLoop_unnamed]
  cases fromSpecBasicsize nm [] (toCInt (40 + ((k : Int) - 0 - 1) * 8)) (.ok ()) with
  | ok bs => rfl
  | exc e => rfl
  | nullNoExc => rfl
  | ub w => rfl

theorem toCInt_wide : toCInt (40 + (((2 ^ 29 : Nat) : Int) - 0 - 1) * 8) = 32 := by
  unfold toCInt
  decide

/-- `2^29` unnamed fields, none visible. -/
def descWide : Desc := { name := lit "m.Wide", fields := List.replicate (2 ^ 29) .unnamed, nInSeq := 0 }

theorem newTypeBasicsizeExact_refuted : ¬ NewTypeBasicsizeExact := by
  intro h
  have hw := newType_unnamed (lit "m.Wide") (2 ^ 29)
  rw [toCInt_wide] at hw
  have hf : fromSpecBasicsize (lit "m.Wide") [] 32 (.ok ()) = .ok 32 := rfl
  rw [hf] at hw
  have := h descWide (fun _ => true) (.ok ()) _ hw
  rw [show descWide.fields = List.replicate (2 ^ 29) .unnamed from rfl, List.length_replicate] at this
  rw [show descWide.nInSeq = 0 from rfl] at this
  dsimp only at this
  omega

/-! ## Unnamed hidden fields -/

/-- `__reduce__` stays in bounds on every object of every type `PyStructSequence_NewType`
builds, while the size attributes are the ones it stored. -/
def ReduceInBoundsBuilt : Prop :=
  ∀ (α : Type) (d : Desc) (malloc : Nat → Bool) (rest : Py Unit) (b : Built) (vals : List α)
    (more : List (Slot α)), newType d malloc rest = .ok b → vals.length = d.fields.length →
    (reduceC b.type ⟨d.nInSeq.toNat, vals.map Slot.val ++ more⟩).isUB = false

/-- Fields `x`, unnamed, unnamed, with `n_in_sequence = 1`: the unnamed fields are hidden. -/
def descHiddenUnnamed : Desc :=
  { name := lit "m.T", fields := [.named (lit "x"), .unnamed, .unnamed], nInSeq := 1 }

theorem reduceInBoundsBuilt_refuted : ¬ ReduceInBoundsBuilt := by
  intro h
  have hb : newType descHiddenUnnamed (fun _ => true) (.ok ()) =
      .ok { type := { name := lit "m.T", members := [⟨lit "x", 0⟩], basicsize := 48,
                      dict := honestDict 1 3 2 }, matchArgs := [lit "x"] } := rfl
  have := h Nat descHiddenUnnamed _ _ _ [1, 2, 3] [.junk, .junk] hb rfl
  revert this
  decide

end PyLean.TypeObj.StructSeq
