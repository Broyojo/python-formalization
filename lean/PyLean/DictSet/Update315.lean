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

/-! ## `PyDict_Update` and `_PyDict_MergeUniq` run to their outcomes -/

section Wrappers
variable {P : Proto K (PyDict K V)} {hf : K → Int} {eqv : K → K → Bool}

theorem contains_present (H : Honest P hf eqv) (d : PyDict K V) (hd : DictInv hf eqv P.isStr d)
    (key : K) (w : V) (hw : assocGet eqv (dictAssoc d) key = some w) :
    dictContainsKnownHash P key (hf key) d = (.ok true, d) := by
  obtain ⟨ix, hl, _, hs⟩ := lookup_assoc H d hd key
  have hix := hs w hw
  have hne : ix ≠ DKIX_EMPTY := by simp only [DKIX_EMPTY]; omega
  simp [dictContainsKnownHash, M.bind_run, hl, hw, hne]

/-- `_PyDict_MergeUniq(a, b)` from a well-formed dict `b` whose first pair's key `a` already holds,
for an honest protocol: the merge stops at that pair with `-2` and the key in `*dupkey`, the
`TypeError` of `f(**a, **b)`; or `MemoryError` from the one big resize before the loop. -/
theorem mergeUniq_dup (H : Honest P hf eqv) (d o : PyDict K V) (hd : DictInv hf eqv P.isStr d)
    (ho : DictInv hf eqv P.isStr o) (hne : o.ident ≠ d.ident) (hfz : d.frozen = false)
    (hd0 : d.used ≠ 0) (key : K) (v : V) (h : Int) (rest : List (K × V × Int))
    (hit : dictItems o = (key, v, h) :: rest) (w : V) (hw : assocGet eqv (dictAssoc d) key = some w)
    (obj : MergeObj K V) (hobj : (obj.isDict && obj.iterIsDict) = true) (has : obj.asDict = o) :
    (∃ s, pyDictMergeUniq P true (some obj) d = (.error memoryError, s)) ∨
    ∃ s, pyDictMergeUniq P true (some obj) d = (.error mergeDupExc, s) ∧ s.dupkey = some key := by
  obtain ⟨ko, hob, wo, huo⟩ := ho.wf
  obtain ⟨k, hb, wk, hu⟩ := hd.wf
  have hh : h = hf key := by
    have hm : (key, v, h) ∈ dictItems o := by rw [hit]; simp
    rw [dictItems_spec o ko hob] at hm
    obtain ⟨x, hx, hxe⟩ := List.mem_map.mp hm
    obtain ⟨t, ht⟩ := (mem_live ko x).mp hx
    have := wo.hashes t x ht
    simp only [Prod.mk.injEq] at hxe
    rw [← hxe.2.2, ← hxe.1]
    exact this
  subst hh
  have ho0 : o.used ≠ 0 := by
    intro h0
    have hnil : liveEntries ko = [] := List.length_eq_zero_iff.mp (by omega)
    rw [dictItems_spec o ko hob, hnil] at hit
    simp at hit
  have e1 : (o.ident == d.ident) = false := by simpa using hne
  have e2 : (o.used == 0) = false := by simpa using ho0
  have e3 : (d.used == 0) = false := by simpa using hd0
  have hroute : pyDictMergeUniq P true (some obj) d = mergeRest P o 2 d := by
    simp [pyDictMergeUniq, dictMergeChecked, hfz, MergeObj.route, hobj, has, dictMerge, dictDictMerge,
      e1, e2, e3]
  rw [hroute]
  have tail : ∀ d1 : PyDict K V, DictInv hf eqv P.isStr d1 → dictAssoc d1 = dictAssoc d →
      ∃ s, mergeLive P 2 o.used (mergeFuel o) 0 { d1 with peer := some o.toPeer } =
        (.error mergeDupExc, s) ∧ s.dupkey = some key := by
    intro d1 hd1 ha
    rw [mergeLive_items (fun a b s => by rw [H.eq_ok]) 2 o ko hob d1, hit]
    have hw1 : assocGet eqv (dictAssoc ({ d1 with peer := some o.toPeer } : PyDict K V)) key = some w := by
      show assocGet eqv (dictAssoc d1) key = some w
      rw [ha]; exact hw
    have hc := contains_present H _ (dictInv_peer d1 hd1 _) key w hw1
    refine ⟨{ { d1 with peer := some o.toPeer } with dupkey := some key }, ?_, rfl⟩
    simp [mergeLoop, mergeStep, M.bind_run, hc, mergeDup]
  simp only [mergeRest]
  by_cases hr : usableFraction (2 ^ d.body.log2Size) < o.used
  · rw [if_pos hr]
    by_cases hlt : estimateLog2Keysize (d.used + o.used) < 64
    · have hroom : d.used ≤ usableFraction (2 ^ estimateLog2Keysize (d.used + o.used)) := by
        have := estimateRoom_proven (d.used + o.used)
        omega
      obtain ⟨k', h1, h2, h3, _, _, _, _⟩ := dictResize_spec H d k hb wk hu _ hlt hroom o.body.isUnicode
      rw [h1]
      let d1 : PyDict K V := { d with nextId := d.nextId + 1, body := .combined k' }
      have hd1 : DictInv hf eqv P.isStr d1 := ⟨⟨k', rfl, h2, by simp [d1, hu, h3]⟩⟩
      have ha : dictAssoc d1 = dictAssoc d := by simp [dictAssoc, d1, hb, Keys.items, h3]
      exact Or.inr (tail d1 hd1 ha)
    · left
      refine ⟨d, ?_⟩
      simp only [dictResize]
      rw [if_pos (by omega)]
  · rw [if_neg hr]
    exact Or.inr (tail d hd rfl)

end Wrappers

/-- `PyDict_Update` and `_PyDict_MergeUniq` on a dict and a well-formed dict `b` that takes the fast
route, for an honest protocol. `PyDict_Update` refuses a frozendict and what is not a dict, and
otherwise stores every pair of `b` over the receiver's, in order: the fold of `d[k] = v`, with
`MemoryError` the one failure. `_PyDict_MergeUniq` stops at the first pair of `b` whose key the
receiver holds, with `-2` and that key in `*dupkey` (here when it is `b`'s first pair), or
`MemoryError`. -/
def UpdateUniqRun : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (hf : K → Int) (eqv : K → K → Bool),
    Honest P hf eqv → ∀ (d o : PyDict K V) (obj : MergeObj K V),
      DictInv hf eqv P.isStr d → DictInv hf eqv P.isStr o → o.ident ≠ d.ident →
      (obj.isDict && obj.iterIsDict) = true → obj.asDict = o →
      pyDictUpdate P false (some obj) d = (.error badInternalCall, d) ∧
      (d.frozen = true → pyDictUpdate P true (some obj) d =
        (.error (frozendictNoSupport "assignment"), d)) ∧
      (d.frozen = false →
        (∃ s, pyDictUpdate P true (some obj) d = (.error memoryError, s) ∧
          (TooBig s.used ∨ 64 ≤ estimateLog2Keysize (d.used + o.used))) ∨
        ∃ d', pyDictUpdate P true (some obj) d = (.ok (), d') ∧ DictInv hf eqv P.isStr d' ∧
          dictAssoc d' = assocUpdateFrom eqv (dictAssoc d) (dictItems o)) ∧
      (d.frozen = false → d.used ≠ 0 → ∀ key v h rest w, dictItems o = (key, v, h) :: rest →
        assocGet eqv (dictAssoc d) key = some w →
        (∃ s, pyDictMergeUniq P true (some obj) d = (.error memoryError, s)) ∨
        ∃ s, pyDictMergeUniq P true (some obj) d = (.error mergeDupExc, s) ∧ s.dupkey = some key)

theorem updateUniqRun_proven : UpdateUniqRun := by
  intro K V _ P hf eqv H d o obj hd ho hne hobj has
  refine ⟨by simp [pyDictUpdate, dictMergeChecked], fun h => by simp [pyDictUpdate, dictMergeChecked, h],
    fun hfz => ?_, fun hfz hd0 key v h rest w hit hw =>
      mergeUniq_dup H d o hd ho hne hfz hd0 key v h rest hit w hw obj hobj has⟩
  have hroute : pyDictUpdate P true (some obj) d = dictDictMerge P o 1 d := by
    simp [pyDictUpdate, dictMergeChecked, hfz, MergeObj.route, hobj, has, dictMerge]
  rw [hroute]
  exact dictDictMerge_spec H d o hd ho hne

end PyLean.DictSet
