import PyLean.DictSet.Props315

/-!
`dict.update` and the C API merges (CPython 3.15.2, `Objects/dictobject.c:3990-4167, 4356-4396`).
-/

namespace PyLean.DictSet

open PyLean

variable {K V : Type} [DecidableEq K]

/-- `dict.update` (`dict_update`, `dict_update_common`), for every key protocol and every argument:
more than one positional argument is the `TypeError` of `PyArg_UnpackTuple`, with the dict untouched;
one argument goes through `dict_update_arg`, whose failure is the result and stops the keywords;
then keywords that are not all strings are `TypeError("keywords must be strings")`, in the state the
argument left, and string keywords are merged with override 1. -/
def UpdateBody : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (args : List (UpdateArg K V))
    (kwds : Option (PyDict K V)) (d : PyDict K V),
    (2 ≤ args.length → dictUpdate P args kwds d =
      (.error (.typeError s!"update expected at most 1 argument, got {args.length}"), d)) ∧
    (∀ a e s, args = [a] → dictUpdateArg P a d = (.error e, s) → dictUpdate P args kwds d = (.error e, s)) ∧
    (∀ s, (args = [] ∧ s = d ∨ ∃ a, args = [a] ∧ dictUpdateArg P a d = (.ok (), s)) →
      (kwds = none → dictUpdate P args kwds d = (.ok (), s)) ∧
      (∀ kw, kwds = some kw → dictHasOnlyStringKeys P.toKeyOps kw = false →
        dictUpdate P args kwds d = (.error (.typeError "keywords must be strings"), s)) ∧
      (∀ kw, kwds = some kw → dictHasOnlyStringKeys P.toKeyOps kw = true →
        dictUpdate P args kwds d = dictMerge P (.dict kw) 1 s))

theorem updateBody_proven : UpdateBody := by
  intro K V _ P args kwds d
  have hpre : ∀ (s : PyDict K V), (args = [] ∧ s = d ∨ ∃ a, args = [a] ∧ dictUpdateArg P a d = (.ok (), s)) →
      dictUpdate P args kwds d = (match kwds with
        | none => pure ()
        | some kw =>
          if dictHasOnlyStringKeys P.toKeyOps kw then dictMerge P (.dict kw) 1
          else M.throw (.typeError "keywords must be strings")) s := by
    intro s hs
    rcases hs with ⟨rfl, rfl⟩ | ⟨a, rfl, ha⟩
    · rfl
    · (simp only [dictUpdate, dictUpdateCommon, M.bind_run, ha]) <;> rfl
  refine ⟨fun h => ?_, fun a e s ha he => ?_, fun s hs => ⟨fun hk => ?_, fun kw hk hn => ?_, fun kw hk hn => ?_⟩⟩
  · match args, h with
    | _ :: _ :: _, _ => (simp [dictUpdate, dictUpdateCommon, M.bind_run]) <;> decide
  · subst ha
    simp only [dictUpdate, dictUpdateCommon, M.bind_run, he]
  · rw [hpre s hs, hk]
    rfl
  · rw [hpre s hs, hk]
    simp [hn]
  · rw [hpre s hs, hk]
    simp [hn]

/-- `PyDict_Update`, `PyDict_Merge`, `_PyDict_MergeUniq` and `PyDict_MergeFromSeq2`, for every key
protocol. `PyDict_Merge` passes `override != 0`, so any non-zero override, 2 included, is
`PyDict_Update`, and only `_PyDict_MergeUniq` reaches override 2. With override 2 a key already in the
receiver stops the merge with that key as `dupkey`, override 0 skips it, and override 1 stores over it.
`PyDict_MergeFromSeq2` refuses what is not a dict, with the `TypeError` of a frozendict for one, and
otherwise runs `merge_from_seq2_lock_held`, as `dict_merge_from_seq2` does. -/
def MergeApiBody : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (b : Option (MergeObj K V)) (o : Int)
    (d : PyDict K V) (seq2 : ReIter (PyDict K V) (Seq2Item K V)) (ov : Bool)
    (key : K) (hash : Int) (value : V) (s : PyDict K V),
    (o ≠ 0 → pyDictMerge P true b o d = pyDictUpdate P true b d) ∧
    (o = 0 → pyDictMerge P true b o d = dictMergeChecked P true b 0 d) ∧
    (∀ ov', (if o != 0 then 1 else 0) = ov' → ov' ≠ 2) ∧
    pyDictMergeUniq P true b d = dictMergeChecked P true b 2 d ∧
    (dictContainsKnownHash P key hash d = (.ok true, s) →
      mergeStep P 2 key hash value d = (.error mergeDupExc, { s with dupkey := some key }) ∧
      mergeStep P 0 key hash value d = (.ok (), s) ∧
      mergeStep P 1 key hash value d = insertDict P key hash value d) ∧
    pyDictMergeFromSeq2C P false seq2 ov d = (.error badInternalCall, d) ∧
    (d.frozen = true → pyDictMergeFromSeq2C P true seq2 ov d =
      (.error (frozendictNoSupport "assignment"), d)) ∧
    (d.frozen = false → pyDictMergeFromSeq2C P true seq2 ov d = dictMergeFromSeq2Locked P seq2 ov d) ∧
    (∀ e s', seq2.getIter d = (.error e, s') → dictMergeFromSeq2Locked P seq2 ov d = (.error e, s')) ∧
    (∀ s', seq2.getIter d = (.ok (), s') →
      dictMergeFromSeq2Locked P seq2 ov d = seq2Loop P ov 0 seq2.steps s')

theorem mergeApiBody_proven : MergeApiBody := by
  intro K V _ P b o d seq2 ov key hash value s
  refine ⟨fun h => ?_, fun h => ?_, fun ov' h => ?_, rfl, fun hc => ⟨?_, ?_, rfl⟩, ?_, fun h => ?_,
    fun h => ?_, fun e s' h => ?_, fun s' h => ?_⟩
  · have : (o != 0) = true := by simpa using h
    simp [pyDictMerge, pyDictUpdate, this]
  · subst h
    rfl
  · subst h
    split <;> decide
  · simp [mergeStep, M.bind_run, hc, mergeDup]
  · simp [mergeStep, M.bind_run, hc]
  · simp [pyDictMergeFromSeq2C]
  · simp [pyDictMergeFromSeq2C, h]
  · simp [pyDictMergeFromSeq2C, h]
  · simp [dictMergeFromSeq2Locked, mergeFromSeq2, M.bind_run, h]
  · simp [dictMergeFromSeq2Locked, mergeFromSeq2, M.bind_run, h]

end PyLean.DictSet
