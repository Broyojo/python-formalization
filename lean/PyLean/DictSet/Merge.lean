import PyLean.DictSet.Props3

/-!
`dict.update` with callbacks that fight back.

`dict_dict_merge` reads the source with `_PyDict_Next` while `__eq__` of the source's keys runs
against the receiver, and that `__eq__` can change either dict. Its only defence is the count test
at `dictobject.c:3981`. These statements hold for every key protocol, with no `Honest`.
-/

namespace PyLean.DictSet

open PyLean

variable {K V : Type} [DecidableEq K]

section Loop
variable (P : Proto K (PyDict K V)) (ov orig fuel : Nat) (pos pos' : Int) (mp s : PyDict K V)
  (src src' : PeerDict K V) (key : K) (value : V) (hash : Int)

/-- A failure in the loop body comes first: the test at :3978 precedes the one at :3981. -/
theorem mergeLive_error (e : PyExc) (h1 : mp.peer = some src)
    (h2 : dictNext src.toDict pos = some (pos', key, value, hash))
    (h3 : mergeStep P ov key hash value mp = (.error e, s)) :
    mergeLive P ov orig (fuel + 1) pos mp = (.error e, s) := by
  simp only [mergeLive, h1, h2, h3]

/-- The test at :3981 fires on a changed count, in the state the callback left. -/
theorem mergeLive_guard (h1 : mp.peer = some src)
    (h2 : dictNext src.toDict pos = some (pos', key, value, hash))
    (h3 : mergeStep P ov key hash value mp = (.ok (), s)) (h4 : s.peer = some src')
    (hne : orig ≠ src'.used) :
    mergeLive P ov orig (fuel + 1) pos mp = (.error mergeMutated, s) := by
  have : (orig != src'.used) = true := by simpa using hne
  simp only [mergeLive, h1, h2, h3, h4, this, if_true]

/-- With the count unchanged the loop goes on, from the source as it stands: `s`, not `mp`. -/
theorem mergeLive_next (h1 : mp.peer = some src)
    (h2 : dictNext src.toDict pos = some (pos', key, value, hash))
    (h3 : mergeStep P ov key hash value mp = (.ok (), s)) (h4 : s.peer = some src')
    (heq : orig = src'.used) :
    mergeLive P ov orig (fuel + 1) pos mp = mergeLive P ov orig fuel pos' s := by
  have : (orig != src'.used) = false := by simpa using heq
  simp only [mergeLive, h1, h2, h3, h4, this, Bool.false_eq_true, if_false]

/-- The end of the source ends the loop. -/
theorem mergeLive_end (h1 : mp.peer = some src) (h2 : dictNext src.toDict pos = none) :
    mergeLive P ov orig (fuel + 1) pos mp = (.ok (), mp) := by
  simp only [mergeLive, h1, h2]

end Loop

/-- The order of the three outcomes of one turn of the loop. -/
def MergeGuard : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (ov orig fuel : Nat) (pos pos' : Int)
    (mp s : PyDict K V) (src : PeerDict K V) (key : K) (value : V) (hash : Int),
    mp.peer = some src → dictNext src.toDict pos = some (pos', key, value, hash) →
    (∀ e, mergeStep P ov key hash value mp = (.error e, s) →
      mergeLive P ov orig (fuel + 1) pos mp = (.error e, s)) ∧
    (∀ src', mergeStep P ov key hash value mp = (.ok (), s) → s.peer = some src' →
      (orig ≠ src'.used → mergeLive P ov orig (fuel + 1) pos mp = (.error mergeMutated, s)) ∧
      (orig = src'.used →
        mergeLive P ov orig (fuel + 1) pos mp = mergeLive P ov orig fuel pos' s))
theorem mergeGuard_proven : MergeGuard := by
  intro K V _ P ov orig fuel pos pos' mp s src key value hash h1 h2
  refine ⟨fun e h3 => mergeLive_error P ov orig fuel pos pos' mp s src key value hash e h1 h2 h3, ?_⟩
  intro src' h3 h4
  exact ⟨mergeLive_guard P ov orig fuel pos pos' mp s src src' key value hash h1 h2 h3 h4,
    mergeLive_next P ov orig fuel pos pos' mp s src src' key value hash h1 h2 h3 h4⟩

/-- A source no callback touches is merged as it was at the start. The hypothesis is the point of
the statement, and it is the only one on `__eq__`: it may lie, raise, or change the receiver. -/
def MergeQuiet : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)), (∀ a b s, (P.eq a b s).2.peer = s.peer) →
    ∀ (ov : Nat) (other : PyDict K V) (ok : Keys K V), other.body = .combined ok →
      ∀ d : PyDict K V,
        mergeLive P ov other.used (mergeFuel other) 0 { d with peer := some other.toPeer } =
          mergeLoop P ov (dictItems other) { d with peer := some other.toPeer }
theorem mergeQuiet_proven : MergeQuiet := fun _ _ _ _ hp ov other ok hob d =>
  mergeLive_items hp ov other ok hob d

/-- `override` is forced to 1 on an empty receiver (:3905). -/
def MergeEmptyTarget : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (other mp : PyDict K V) (ov : Nat),
    mp.used = 0 → dictDictMerge P other ov mp = dictDictMerge P other 1 mp
theorem mergeEmptyTarget_proven : MergeEmptyTarget := by
  intro K V _ P other mp ov h
  simp only [dictDictMerge, h, beq_self_eq_true, if_true]

/-- `dict_dict_merge` as a whole, for every key protocol and override: the self and empty tests; on an
empty receiver the clone when the source is clean, and otherwise the rest with `override` forced to
1; and otherwise the rest. -/
def DictDictMergeBody : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (other mp : PyDict K V) (ov : Nat),
    ((other.ident = mp.ident ∨ other.used = 0) → dictDictMerge P other ov mp = (.ok (), mp)) ∧
    (other.ident ≠ mp.ident → other.used ≠ 0 →
      (mp.used ≠ 0 → dictDictMerge P other ov mp = mergeRest P other ov mp) ∧
      (mp.used = 0 → ∀ k okeys, mp.body = .combined k → other.body = .combined okeys →
        ((other.used == okeys.nentries && (okeys.log2Size == PyDict_LOG_MINSIZE ||
            decide (usableFraction (okeys.size / 2) < other.used))) = true →
          dictDictMerge P other ov mp = (.ok (), { mp with
            nextId := mp.nextId + 1
            used := other.used
            body := .combined (cloneCombinedDictKeys mp.nextId okeys) })) ∧
        ((other.used == okeys.nentries && (okeys.log2Size == PyDict_LOG_MINSIZE ||
            decide (usableFraction (okeys.size / 2) < other.used))) = false →
          dictDictMerge P other ov mp = mergeRest P other 1 mp)) ∧
      (mp.used = 0 → mp.body.isSplit = true → dictDictMerge P other ov mp = mergeRest P other 1 mp) ∧
      (mp.used = 0 → other.body.isSplit = true → dictDictMerge P other ov mp = mergeRest P other 1 mp))
theorem dictDictMergeBody_proven : DictDictMergeBody := by
  intro K V _ P other mp ov
  refine ⟨?_, ?_⟩
  · rintro (h | h) <;> simp [dictDictMerge, h]
  · intro h1 h2
    have e1 : (other.ident == mp.ident) = false := by simpa using h1
    have e2 : (other.used == 0) = false := by simpa using h2
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h3
      have e3 : (mp.used == 0) = false := by simpa using h3
      simp [dictDictMerge, e1, e2, e3]
    · intro h3 k okeys hb ho
      have e3 : (mp.used == 0) = true := by simpa using h3
      constructor
      · intro hc
        simp only [dictDictMerge, e1, e2, e3, Bool.false_or, Bool.false_eq_true, if_false, if_true,
          hb, ho]
        rw [if_pos hc]
      · intro hc
        simp only [dictDictMerge, e1, e2, e3, Bool.false_or, Bool.false_eq_true, if_false, if_true,
          hb, ho]
        rw [if_neg (by simp [hc])]
    · intro h3 hs
      have e3 : (mp.used == 0) = true := by simpa using h3
      cases hb : mp.body with
      | combined k => simp [hb, Body.isSplit] at hs
      | split k v =>
        simp only [dictDictMerge, e1, e2, e3, Bool.false_or, Bool.false_eq_true, if_false, if_true, hb]
    · intro h3 hs
      have e3 : (mp.used == 0) = true := by simpa using h3
      cases ho : other.body with
      | combined k => simp [ho, Body.isSplit] at hs
      | split k v =>
        simp only [dictDictMerge, e1, e2, e3, Bool.false_or, Bool.false_eq_true, if_false, if_true, ho]
        cases mp.body <;> rfl

/-- The one big resize at the top of the rest of `dict_dict_merge` (:3933-3946): it runs only when the
source does not fit, a failure ends the merge, and the loop starts from what it left, with the source
in hand and its count as `orig_size`. -/
def MergeRestBody : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (other mp s : PyDict K V) (ov : Nat)
    (e : PyExc),
    (usableFraction (2 ^ mp.body.log2Size) < other.used →
      (dictResize (estimateLog2Keysize (mp.used + other.used)) other.body.isUnicode mp = (.error e, s) →
        mergeRest P other ov mp = (.error e, s)) ∧
      (dictResize (estimateLog2Keysize (mp.used + other.used)) other.body.isUnicode mp = (.ok (), s) →
        mergeRest P other ov mp =
          mergeLive P ov other.used (mergeFuel other) 0 { s with peer := some other.toPeer })) ∧
    (¬ usableFraction (2 ^ mp.body.log2Size) < other.used →
      mergeRest P other ov mp =
        mergeLive P ov other.used (mergeFuel other) 0 { mp with peer := some other.toPeer })
theorem mergeRestBody_proven : MergeRestBody := by
  intro K V _ P other mp s ov e
  refine ⟨fun h => ⟨fun h2 => ?_, fun h2 => ?_⟩, fun h => ?_⟩
  · simp only [mergeRest]
    rw [if_pos h, h2]
  · simp only [mergeRest]
    rw [if_pos h, h2]
  · simp only [mergeRest]
    rw [if_neg h]

/-- The branches of the loop body of `dict_dict_merge` on `override` (:3956-3975). -/
def MergeStepBody : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (key : K) (hash : Int) (value : V)
    (ov : Nat) (d s : PyDict K V) (e : PyExc),
    mergeStep P 1 key hash value d = insertDict P key hash value d ∧
    (ov ≠ 1 →
      (dictContainsKnownHash P key hash d = (.error e, s) →
        mergeStep P ov key hash value d = (.error e, s)) ∧
      (dictContainsKnownHash P key hash d = (.ok false, s) →
        mergeStep P ov key hash value d = insertDict P key hash value s) ∧
      (dictContainsKnownHash P key hash d = (.ok true, s) →
        (ov = 0 → mergeStep P ov key hash value d = (.ok (), s)) ∧
        (ov ≠ 0 → mergeStep P ov key hash value d = (.error (keyErr P key), s))))
theorem mergeStepBody_proven : MergeStepBody := by
  intro K V _ P key hash value ov d s e
  refine ⟨by simp [mergeStep], fun hov => ?_⟩
  have e1 : (ov == 1) = false := by simpa using hov
  refine ⟨fun h => ?_, fun h => ?_, fun h => ⟨fun h0 => ?_, fun h0 => ?_⟩⟩
  · simp [mergeStep, e1, M.bind_run, h]
  · simp [mergeStep, e1, M.bind_run, h]
  · subst h0
    simp [mergeStep, M.bind_run, h]
  · have e2 : (ov != 0) = true := by simpa using h0
    simp [mergeStep, e1, e2, M.bind_run, h]

section Witness

/-- Integer keys, all hashing to 0 up to `2`, so `1` and `2` are compared with each other. -/
def intOps : KeyOps Nat :=
  { hash := fun k => .ok (if k ≤ 2 then 0 else (k : Int))
    isStr := fun _ => false
    isStrLike := fun _ => false
    strEq := fun a b => a == b
    reprStr := toString
    repr := fun k => .ok (toString k)
    typeName := fun _ => "int" }

def intPlain : Proto Nat (PyDict Nat Nat) := { intOps with eq := fun a b s => (.ok (a == b), s) }

/-- `__eq__` clears the source. -/
def intClears : Proto Nat (PyDict Nat Nat) :=
  { intOps with
    eq := fun a b s =>
      (.ok (a == b), { s with peer := s.peer.map fun p => (dictClear p.toDict).toPeer }) }

/-- `__eq__` replaces the last item of the source by one under key 99, as long as key 99 is not
there yet. -/
def intSwaps : Proto Nat (PyDict Nat Nat) :=
  { intOps with
    eq := fun a b s =>
      (.ok (a == b),
       { s with
         peer := s.peer.map fun p =>
           let d := p.toDict
           if (dictItems d).any (fun e => e.1 == 99) then p
           else
             match dictPopitem d with
             | (.ok (_, v), d') => (dictSetItem intPlain 99 v d').2.toPeer
             | (.error _, _) => p }) }

def wReceiver : PyDict Nat Nat := (dictSetItem intPlain 1 10 { ident := 1 }).2
def wSource : PyDict Nat Nat :=
  (dictSetItem intPlain 3 30 (dictSetItem intPlain 2 20 { ident := 2 }).2).2

def isMutated : Py Unit → Bool
  | .error e => e.className == mergeMutated.className && e.message == mergeMutated.message
  | .ok _ => false

end Witness

/-- The test at :3981 is reachable through `dictMerge` itself. -/
def MergeGuardReachable : Prop :=
  ∃ (P : Proto Nat (PyDict Nat Nat)) (mp other : PyDict Nat Nat),
    isMutated (dictMerge P (.dict other) 1 mp).1 = true
theorem mergeGuardReachable_proven : MergeGuardReachable :=
  ⟨intClears, wReceiver, wSource, by decide +kernel⟩

/-- The test does not see a change that keeps the count: the merge succeeds, and a key the source
held at the start is not in the receiver, while one added later is. -/
def MergeSameSizeUnseen : Prop :=
  ∃ (P : Proto Nat (PyDict Nat Nat)) (mp other : PyDict Nat Nat),
    (match dictMerge P (.dict other) 1 mp with
     | (.ok _, d') =>
       (dictItems other).any (fun e => e.1 == 3) &&
         !(dictItems d').any (fun e => e.1 == 3) &&
         (dictItems d').any (fun e => e.1 == 99)
     | (.error _, _) => false) = true
theorem mergeSameSizeUnseen_proven : MergeSameSizeUnseen :=
  ⟨intSwaps, wReceiver, wSource, by decide +kernel⟩

section Generic
variable (P : Proto K (PyDict K V)) (g : K → DM K V V) (key : K) (rest : List K)
  (d s : PyDict K V)

theorem generic_present_skip (h : pyDictContains P key d = (.ok true, s)) :
    mergeGenericLoop P g 0 (key :: rest) d = mergeGenericLoop P g 0 rest s := by
  simp [mergeGenericLoop, M.bind_run, h]

theorem generic_present_raise (h : pyDictContains P key d = (.ok true, s)) :
    mergeGenericLoop P g 2 (key :: rest) d = (.error (keyErr P key), s) := by
  simp [mergeGenericLoop, M.bind_run, h]

theorem generic_contains_raises (ov : Nat) (hov : ov ≠ 1) (e : PyExc)
    (h : pyDictContains P key d = (.error e, s)) :
    mergeGenericLoop P g ov (key :: rest) d = (.error e, s) := by
  have : (ov != 1) = true := by simpa using hov
  simp [mergeGenericLoop, M.bind_run, h, this]

theorem generic_absent (ov : Nat) (hov : ov ≠ 1) (h : pyDictContains P key d = (.ok false, s)) :
    mergeGenericLoop P g ov (key :: rest) d =
      (g key >>= fun v => dictSetItem P key v >>= fun _ => mergeGenericLoop P g ov rest) s := by
  have : (ov != 1) = true := by simpa using hov
  simp [mergeGenericLoop, M.bind_run, h, this]

/-- `override == 1` never tests membership. -/
theorem generic_override1 :
    mergeGenericLoop P g 1 (key :: rest) d =
      (g key >>= fun v => dictSetItem P key v >>= fun _ => mergeGenericLoop P g 1 rest) d := by
  simp [mergeGenericLoop, M.bind_run]

end Generic

/-- The slow path of `dict_merge`, for any protocol and any `keys()` and `__getitem__`, which may
raise and may change the receiver. -/
def MergeGeneric : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (g : K → DM K V V) (keys : DM K V (List K))
    (key : K) (rest : List K) (ov : Nat) (d s : PyDict K V) (b : Option (MergeObj K V)),
    dictMergeChecked P false b ov d = (.error badInternalCall, d) ∧
    dictMergeChecked P true none ov d = (.error badInternalCall, d) ∧
    (∀ o : MergeObj K V, (o.isDict && o.iterIsDict) = true →
      dictMergeChecked P true (some o) ov d = dictDictMerge P o.asDict ov d) ∧
    (∀ o : MergeObj K V, (o.isDict && o.iterIsDict) = false →
      dictMergeChecked P true (some o) ov d = dictMerge P (.mapping o.keys o.getitem) ov d) ∧
    (∀ e, keys d = (.error e, s) → dictMerge P (.mapping keys g) ov d = (.error e, s)) ∧
    (∀ ks, keys d = (.ok ks, s) → dictMerge P (.mapping keys g) ov d = mergeGenericLoop P g ov ks s) ∧
    (pyDictContains P key d = (.ok true, s) →
      mergeGenericLoop P g 0 (key :: rest) d = mergeGenericLoop P g 0 rest s ∧
      mergeGenericLoop P g 2 (key :: rest) d = (.error (keyErr P key), s)) ∧
    (ov ≠ 1 → ∀ e, pyDictContains P key d = (.error e, s) →
      mergeGenericLoop P g ov (key :: rest) d = (.error e, s)) ∧
    (ov ≠ 1 → pyDictContains P key d = (.ok false, s) →
      mergeGenericLoop P g ov (key :: rest) d =
        (g key >>= fun v => dictSetItem P key v >>= fun _ => mergeGenericLoop P g ov rest) s) ∧
    mergeGenericLoop P g 1 (key :: rest) d =
      (g key >>= fun v => dictSetItem P key v >>= fun _ => mergeGenericLoop P g 1 rest) d
theorem mergeGeneric_proven : MergeGeneric := by
  intro K V _ P g keys key rest ov d s b
  refine ⟨?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, generic_override1 P g key rest d⟩
  · cases b <;> rfl
  · intro o h
    simp [dictMergeChecked, MergeObj.route, h, dictMerge]
  · intro o h
    simp [dictMergeChecked, MergeObj.route, h]
  · intro e h
    simp [dictMerge, M.bind_run, h]
  · intro ks h
    simp [dictMerge, M.bind_run, h]
  · intro h
    exact ⟨generic_present_skip P g key rest d s h, generic_present_raise P g key rest d s h⟩
  · intro hov e h
    exact generic_contains_raises P g key rest d s ov hov e h
  · intro hov h
    exact generic_absent P g key rest d s ov hov h

/-- `merge_from_seq2_lock_held`, for an iterator that may raise or change the receiver at any step:
`PyObject_GetIter` first, then each outcome of a step and what follows it, on both branches of
`override`. The state after a failure is the one the step left, so what earlier elements did stays,
and a `TypeError` from `PySequence_Fast` carries a note, as no other exception does. -/
def Seq2Order : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (ov : Bool) (i : Nat)
    (step : DM K V (Option (Seq2Item K V))) (rest : List (DM K V (Option (Seq2Item K V))))
    (d s : PyDict K V),
    (∀ (it : ReIter (PyDict K V) (Seq2Item K V)) (e : PyExc), it.getIter d = (.error e, s) →
      mergeFromSeq2 P it ov d = (.error e, s)) ∧
    (∀ (it : ReIter (PyDict K V) (Seq2Item K V)) (u : Unit), it.getIter d = (.ok u, s) →
      mergeFromSeq2 P it ov d = seq2Loop P ov 0 it.steps s) ∧
    (seq2Loop P ov i [] d = (.ok (), d)) ∧
    (∀ e, step d = (.error e, s) → seq2Loop P ov i (step :: rest) d = (.error e, s)) ∧
    (step d = (.ok none, s) → seq2Loop P ov i (step :: rest) d = (.ok (), s)) ∧
    (∀ m, step d = (.ok (some (.notSeq (.typeError m))), s) →
      seq2Loop P ov i (step :: rest) d =
        (.error (.typeError m), { s with note := some (seq2Note i) })) ∧
    (∀ e, (∀ m, e ≠ .typeError m) → step d = (.ok (some (.notSeq e)), s) →
      seq2Loop P ov i (step :: rest) d = (.error e, s)) ∧
    (∀ n, step d = (.ok (some (.wrongLen n)), s) → seq2Loop P ov i (step :: rest) d =
      (.error (.valueError s!"dictionary update sequence element #{i} has length {n}; 2 is required"), s)) ∧
    (∀ k v, step d = (.ok (some (.pair k v)), s) →
      seq2Loop P true i (step :: rest) d =
        (dictSetItem P k v >>= fun _ => seq2Loop P true (i + 1) rest) s) ∧
    (∀ k v, step d = (.ok (some (.pair k v)), s) →
      seq2Loop P false i (step :: rest) d =
        (dictSetdefaultRef P k v false false >>= fun _ => seq2Loop P false (i + 1) rest) s)
theorem seq2Order_proven : Seq2Order := by
  intro K V _ P ov i step rest d s
  refine ⟨?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro it e h
    simp [mergeFromSeq2, M.bind_run, h]
  · intro it u h
    simp [mergeFromSeq2, M.bind_run, h]
  · intro e h
    simp [seq2Loop, M.bind_run, h]
  · intro h
    simp [seq2Loop, M.bind_run, h]
  · intro m h
    simp [seq2Loop, M.bind_run, h, M.modify_run]
  · intro e he h
    cases e with
    | typeError m => exact absurd rfl (he m)
    | _ => simp [seq2Loop, M.bind_run, h]
  · intro n h
    simp [seq2Loop, M.bind_run, h]
  · intro k v h
    simp [seq2Loop, M.bind_run, h]
  · intro k v h
    simp [seq2Loop, M.bind_run, h]

end PyLean.DictSet
