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
    (key : K) (rest : List K) (ov : Nat) (d s : PyDict K V) (b : Option (MergeArg K V)),
    dictMergeChecked P false b ov d = (.error badInternalCall, d) ∧
    dictMergeChecked P true none ov d = (.error badInternalCall, d) ∧
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
  refine ⟨?_, rfl, ?_, ?_, ?_, ?_, ?_, generic_override1 P g key rest d⟩
  · cases b <;> rfl
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
each outcome of a step, and what follows it. The state after a failure is the one the step left, so
what earlier elements did stays. -/
def Seq2Order : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (ov : Bool) (i : Nat)
    (step : DM K V (Option (Seq2Item K V))) (rest : List (DM K V (Option (Seq2Item K V))))
    (d s : PyDict K V),
    (∀ e, step d = (.error e, s) → seq2Loop P ov i (step :: rest) d = (.error e, s)) ∧
    (step d = (.ok none, s) → seq2Loop P ov i (step :: rest) d = (.ok (), s)) ∧
    (∀ e, step d = (.ok (some (.notSeq e)), s) → seq2Loop P ov i (step :: rest) d = (.error e, s)) ∧
    (∀ n, step d = (.ok (some (.wrongLen n)), s) → seq2Loop P ov i (step :: rest) d =
      (.error (.valueError s!"dictionary update sequence element #{i} has length {n}; 2 is required"), s)) ∧
    (∀ k v, step d = (.ok (some (.pair k v)), s) →
      seq2Loop P true i (step :: rest) d =
        (dictSetItem P k v >>= fun _ => seq2Loop P true (i + 1) rest) s)
theorem seq2Order_proven : Seq2Order := by
  intro K V _ P ov i step rest d s
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> simp_all [seq2Loop, M.bind_run]

end PyLean.DictSet
