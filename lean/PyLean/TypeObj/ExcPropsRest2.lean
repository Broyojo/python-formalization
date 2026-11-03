import PyLean.TypeObj.ExcPropsRest

/-!
More properties of `ImportError` (`Objects/exceptions.c:1803-1925`) and `OSError`
(`:2183-2462`): the keywords of `ImportError.__init__`, `__getstate__` and `__reduce__`, the slot
test of `oserror_use_init`, the effects of `OSError.__init__`, and the deletion and range checks of
`characters_written`.
-/

namespace PyLean.TypeObj

/-- The member names of an exception, each once: a type invariant, since `memSet` is the only
way to change them and it keeps the names distinct (`memSet_nodup`). -/
def MemNodup (d : ExcData) : Prop := (d.members.map Prod.fst).Nodup

theorem set_keys (d : NameDict) (n : Name) (v : Val) :
    (NameDict.set d n v).map Prod.fst =
      if n ∈ d.map Prod.fst then d.map Prod.fst else d.map Prod.fst ++ [n] := by
  induction d with
  | nil => simp [NameDict.set]
  | cons p ps ih =>
    obtain ⟨k, x⟩ := p
    by_cases hk : k = n
    · subst hk; simp [NameDict.set]
    · have hk' : (k == n) = false := by simpa using hk
      simp only [NameDict.set, hk', Bool.false_eq_true, if_false, List.map_cons, ih]
      by_cases hn : n ∈ ps.map Prod.fst
      · simp [hn]
      · have : ¬ (n = k ∨ n ∈ ps.map Prod.fst) := by
          intro h; rcases h with h | h
          · exact hk h.symm
          · exact hn h
        simp [hn, Ne.symm hk]

theorem erase_sublist (d : NameDict) (n : Name) :
    ((NameDict.erase d n).map Prod.fst).Sublist (d.map Prod.fst) := by
  induction d with
  | nil => simp [NameDict.erase]
  | cons p ps ih =>
    obtain ⟨k, x⟩ := p
    by_cases hk : (k == n) = true
    · simp only [NameDict.erase, hk, if_true, List.map_cons]
      exact List.sublist_cons_self _ _
    · have hk' : (k == n) = false := by simpa using hk
      simp only [NameDict.erase, hk', Bool.false_eq_true, if_false, List.map_cons]
      exact ih.cons_cons _

theorem memSet_nodup {d : ExcData} (h : MemNodup d) (n : Name) (v : Option Val) :
    MemNodup (memSet n v d) := by
  unfold MemNodup memSet at *
  cases v with
  | some x =>
    simp only [set_keys]
    split
    · exact h
    · rename_i hn
      refine List.nodup_append.mpr ⟨h, by simp, ?_⟩
      intro x hx y hy
      simp only [List.mem_singleton] at hy
      subst hy
      intro he
      subst he
      exact hn hx
  | none => exact h.sublist (erase_sublist _ _)

theorem get?_none_of_not_mem (ps : NameDict) (n : Name) (h : n ∉ ps.map Prod.fst) :
    NameDict.get? ps n = none := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨k, x⟩ := p
    simp only [List.map_cons, List.mem_cons, not_or] at h
    have hk' : (k == n) = false := by simpa using Ne.symm h.1
    simp [NameDict.get?, hk', ih h.2]

theorem memGet_memSet_self {d : ExcData} (hd : MemNodup d) (n : Name) (v : Option Val) :
    memGet (memSet n v d) n = v := by
  cases v with
  | some x => exact memGet_memSet_same _ _ _
  | none =>
    unfold MemNodup at hd
    show NameDict.get? (NameDict.erase d.members n) n = none
    generalize d.members = ms at hd
    induction ms with
    | nil => simp [NameDict.erase, NameDict.get?]
    | cons p ps ih =>
      obtain ⟨k, x⟩ := p
      simp only [List.map_cons, List.nodup_cons] at hd
      by_cases hk : k = n
      · subst hk; simp [NameDict.erase, get?_none_of_not_mem ps k hd.1]
      · have hk' : (k == n) = false := by simpa using hk
        simp [NameDict.erase, NameDict.get?, hk', ih hd.2]

theorem memGet_withArgs (d : ExcData) (xs : List Val) (n : Name) :
    memGet { d with args := xs } n = memGet d n := rfl

theorem memGet_withWritten (d : ExcData) (k : Int) (n : Name) :
    memGet { d with written := k } n = memGet d n := rfl

/-- Name the world of a successful run by the `IsExc` fact about it. -/
theorem ex_of_isExc {P : World → Prop} {f : M Unit} {w W : World} {a : Addr} {d : ExcData}
    (h : IsExc W a d) (heq : f w = .ok () W) (hp : IsExc W a d → P W) :
    ∃ w', f w = .ok () w' ∧ P w' := ⟨W, heq, hp h⟩

/-! ## `ImportError` -/

/-- The keyword names of `ImportError_init`, `:1806`. -/
def importKw : List Name := ["name", "path", "name_from"]

/-- **`ImportError.__init__` stores its keywords and resets what it is not given.** With
keywords among `name`, `path` and `name_from` (at most three, the parse's own bound), `args` is
the positional arguments, each of the three members is its keyword or NULL (`Py_XSETREF` with
NULL, `:1827-1829`), and `msg` is the argument when there is exactly one and NULL otherwise
(`:1831-1834`), on a first or a later call. An unexpected keyword is the `TypeError` of the
parse, `ImportError() got an unexpected keyword argument 'k'` followed by
`. Did you mean 'n'?` when `_Py_CalculateSuggestions` finds a close parameter name
(`Python/getargs.c:1979-1995`, `unexpectedKwMsg`), raised after `BaseException_init` has already
replaced `args` (`:1813`). An `__init__`
that ignored its keywords, or kept an old `msg`, fails. `MemNodup` is the type invariant that each
member name is stored once. -/
def ImportErrorInitKw : Prop :=
  (∀ (a : Addr) (d : ExcData) (args : List Val) (kw : Kw) (w : World), IsExc w a d → MemNodup d →
    kw.length ≤ 3 → kw.all (fun p => importKw.contains p.1) = true →
    ∃ w', importErrorInit (.obj a) args kw w = .ok () w' ∧
      excArgs w' (.obj a) = args ∧
      memGet (excDataOf w' (.obj a)) "name" = NameDict.get? kw "name" ∧
      memGet (excDataOf w' (.obj a)) "path" = NameDict.get? kw "path" ∧
      memGet (excDataOf w' (.obj a)) "name_from" = NameDict.get? kw "name_from" ∧
      memGet (excDataOf w' (.obj a)) "msg" = importMsg args) ∧
  (∀ (a : Addr) (args : List Val) (kw : Kw) (k : Name) (x : Val) (w : World),
    kw.length ≤ 3 → kw.find? (fun p => !importKw.contains p.1) = some (k, x) →
    importErrorInit (.obj a) args kw w =
      .err (.exc B.TypeError (unexpectedKwMsg "ImportError" importKw k) none)
        (excUpdW w a fun d => { d with args := args }))

theorem importErrorInitKw_proven : ImportErrorInitKw := by
  refine ⟨?_, ?_⟩
  · intro a d args kw w hx hnd hl hall
    have hany : kw.any (fun p => !importKw.contains p.1) = false := by
      rw [List.all_eq_true] at hall
      rw [List.any_eq_false]
      intro p hp
      have := hall p hp
      simp only [Bool.not_eq_true', Bool.not_eq_false', this, not_true_eq_false, not_false_eq_true]
      decide
    have hgt : ¬ 3 < kw.length := by omega
    simp only [importKw] at hany
    have h1 := hx.update (fun d => { d with args := args })
    have h2 := isExc_memSet h1 "name" (NameDict.get? kw "name")
    have h3 := isExc_memSet h2 "path" (NameDict.get? kw "path")
    have h4 := isExc_memSet h3 "name_from" (NameDict.get? kw "name_from")
    have h5 := isExc_memSet h4 "msg" (importMsg args)
    refine ex_of_isExc h5 ?_ ?_
    · simp only [importErrorInit, baseExceptionInit, argNoKeywords, argKeywordOnly, M.bind_app,
        getW_app, excUpdate_app]
      simp only [List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, if_false, gt_iff_lt, hgt, hany]
      simp [excUpdate_app, hgt]
      try rfl
    · intro h5
      simp only [excArgs]
      rw [h5.data]
      have n0 : MemNodup { d with args := args } := hnd
      have n1 := memSet_nodup n0 "name" (NameDict.get? kw "name")
      have n2 := memSet_nodup n1 "path" (NameDict.get? kw "path")
      have n3 := memSet_nodup n2 "name_from" (NameDict.get? kw "name_from")
      refine ⟨rfl, ?_, ?_, ?_, ?_⟩
      · rw [memGet_memSet_ne _ "msg" "name" _ (by decide),
          memGet_memSet_ne _ "name_from" "name" _ (by decide),
          memGet_memSet_ne _ "path" "name" _ (by decide), memGet_memSet_self n0]
      · rw [memGet_memSet_ne _ "msg" "path" _ (by decide),
          memGet_memSet_ne _ "name_from" "path" _ (by decide), memGet_memSet_self n1]
      · rw [memGet_memSet_ne _ "msg" "name_from" _ (by decide), memGet_memSet_self n2]
      · exact memGet_memSet_self n3 _ _
  · intro a args kw k x w hl hf
    have h2 := List.find?_some hf
    have hany : kw.any (fun p => !importKw.contains p.1) = true :=
      List.any_eq_true.mpr ⟨(k, x), List.mem_of_find?_eq_some hf, h2⟩
    have hgt : ¬ 3 < kw.length := by omega
    simp only [importKw] at hf hany
    simp only [importErrorInit, baseExceptionInit, argNoKeywords, argKeywordOnly,
      argUnexpectedKeyword, M.bind_app, getW_app, excUpdate_app, List.isEmpty_nil, Bool.not_true,
      Bool.false_eq_true, if_false, List.length_cons, List.length_nil, gt_iff_lt, hgt, hany,
      if_true, hf, M.pure_app, typeErr, raiseC]
    try rfl

/-- **The suggestion is `_Py_CalculateSuggestions`'s.** The keyword names of `ImportError`,
`NameError` and `AttributeError` against the keywords tried on CPython 3.15.2, with the messages
it printed: a close name is suggested (`nam`, `Name`, `nme`, `named` give `name`; `pat`, `path_`
give `path`; `name_fro`, `nameFrom` give `name_from`; `ob`, `obj_` give `obj`), a far one is not
(`zzq`, `x`, `naem`, `é`, `o`, `zz`, and `obj` for `NameError`). -/
def KwSuggestionsMatch : Prop :=
  unexpectedKwMsg "ImportError" importKw "nam" =
    "ImportError() got an unexpected keyword argument 'nam'. Did you mean 'name'?" ∧
  calcSuggestion importKw "Name" = some "name" ∧
  calcSuggestion importKw "nme" = some "name" ∧
  calcSuggestion importKw "named" = some "name" ∧
  calcSuggestion importKw "pat" = some "path" ∧
  calcSuggestion importKw "path_" = some "path" ∧
  calcSuggestion importKw "name_fro" = some "name_from" ∧
  calcSuggestion importKw "nameFrom" = some "name_from" ∧
  calcSuggestion importKw "zzq" = none ∧
  calcSuggestion importKw "x" = none ∧
  calcSuggestion importKw "naem" = none ∧
  calcSuggestion importKw "é" = none ∧
  unexpectedKwMsg "ImportError" importKw "zzq" = "ImportError() got an unexpected keyword argument 'zzq'" ∧
  calcSuggestion ["name"] "obj" = none ∧
  calcSuggestion ["name"] "zz" = none ∧
  calcSuggestion ["name", "obj"] "ob" = some "obj" ∧
  calcSuggestion ["name", "obj"] "obj_" = some "obj" ∧
  calcSuggestion ["name", "obj"] "nme" = some "name" ∧
  calcSuggestion ["name", "obj"] "o" = none

theorem kwSuggestionsMatch_proven : KwSuggestionsMatch := by
  unfold KwSuggestionsMatch
  decide +kernel

/-- **`NameError` and `AttributeError` refuse an unknown keyword with the same message**, after
`BaseException_init` has replaced `args` (`Objects/exceptions.c:2580-2605`, `:2663-2690`). -/
def NameAttrInitUnexpected : Prop :=
  (∀ (a : Addr) (args : List Val) (kw : Kw) (k : Name) (x : Val) (w : World),
    kw.length ≤ 1 → kw.find? (fun p => !["name"].contains p.1) = some (k, x) →
    nameErrorInit (.obj a) args kw w =
      .err (.exc B.TypeError (unexpectedKwMsg "NameError" ["name"] k) none)
        (excUpdW w a fun d => { d with args := args })) ∧
  (∀ (a : Addr) (args : List Val) (kw : Kw) (k : Name) (x : Val) (w : World),
    kw.length ≤ 2 → kw.find? (fun p => !["name", "obj"].contains p.1) = some (k, x) →
    attributeErrorInit (.obj a) args kw w =
      .err (.exc B.TypeError (unexpectedKwMsg "AttributeError" ["name", "obj"] k) none)
        (excUpdW w a fun d => { d with args := args }))

theorem nameAttrInitUnexpected_proven : NameAttrInitUnexpected := by
  refine ⟨?_, ?_⟩
  · intro a args kw k x w hl hf
    have h2 := List.find?_some hf
    have hany : kw.any (fun p => !["name"].contains p.1) = true :=
      List.any_eq_true.mpr ⟨(k, x), List.mem_of_find?_eq_some hf, h2⟩
    have hgt : ¬ 1 < kw.length := by omega
    simp only [nameErrorInit, baseExceptionInit, argNoKeywords, argKeywordOnly,
      argUnexpectedKeyword, M.bind_app, getW_app, excUpdate_app, List.isEmpty_nil, Bool.not_true,
      Bool.false_eq_true, if_false, List.length_cons, List.length_nil, gt_iff_lt, hgt, hany,
      if_true, hf, M.pure_app, typeErr, raiseC]
    try rfl
  · intro a args kw k x w hl hf
    have h2 := List.find?_some hf
    have hany : kw.any (fun p => !["name", "obj"].contains p.1) = true :=
      List.any_eq_true.mpr ⟨(k, x), List.mem_of_find?_eq_some hf, h2⟩
    have hgt : ¬ 2 < kw.length := by omega
    simp only [attributeErrorInit, baseExceptionInit, argNoKeywords, argKeywordOnly,
      argUnexpectedKeyword, M.bind_app, getW_app, excUpdate_app, List.isEmpty_nil, Bool.not_true,
      Bool.false_eq_true, if_false, List.length_cons, List.length_nil, gt_iff_lt, hgt, hany,
      if_true, hf, M.pure_app, typeErr, raiseC]
    try rfl

theorem lookup_optSet_same (es : List (Val × Val)) (k : Name) (x : Option Val) :
    dictLookup (optSetEntry es k x) (.str k) = x.or (dictLookup es (.str k)) := by
  cases x <;> simp [optSetEntry, dictLookup_setEntry_same]

theorem lookup_optSet_ne (es : List (Val × Val)) (k m : Name) (x : Option Val) (h : k ≠ m) :
    dictLookup (optSetEntry es k x) (.str m) = dictLookup es (.str m) := by
  cases x <;> simp [optSetEntry, dictLookup_setEntry_ne _ _ _ _ h]

/-- **`ImportError.__getstate__` and `__reduce__`.** When `name`, `path` or `name_from` is set,
the state is a new dict: a copy of the instance dict (or an empty one) with each set member
under its name, over any entry of the instance dict with that key (`:1884-1900`); every other key
is the instance dict's. With none set, the state is the instance dict itself, or `None` when there
is none (`:1902-1907`). `__reduce__` is `(type, args)` for a `None` state and
`(type, args, state)` otherwise (`:1919-1922`). A `getstate` returning `{'name': n}` alone fails
the copy part; one that always copies fails the identity part. -/
def ImportErrorGetstateReduce : Prop :=
  (∀ (v : Val) (w : World),
    let d := excDataOf w v
    (memGet d "name").isSome || (memGet d "path").isSome || (memGet d "name_from").isSome →
    ∃ w', importErrorGetstate v w = .ok (.obj w.heap.size) w' ∧
      ∃ es, dictOf w' (.obj w.heap.size) = some es ∧
        (∀ k ∈ importKw, dictLookup es (.str k) = (memGet d k).or (dictLookup (instDictEntries w v) (.str k))) ∧
        (∀ k, k ∉ importKw → dictLookup es (.str k) = dictLookup (instDictEntries w v) (.str k))) ∧
  (∀ (v : Val) (a : Addr) (w : World),
    let d := excDataOf w v
    memGet d "name" = none → memGet d "path" = none → memGet d "name_from" = none →
    instDictAddr w v = some a → importErrorGetstate v w = .ok (.obj a) w) ∧
  (∀ (v : Val) (w : World),
    let d := excDataOf w v
    memGet d "name" = none → memGet d "path" = none → memGet d "name_from" = none →
    instDictAddr w v = none → importErrorGetstate v w = .ok .none w) ∧
  (∀ (v st : Val) (w w1 : World), importErrorGetstate v w = .ok st w1 →
    importErrorReduce v w =
      .ok (if st.is .none then .tuple [.obj (typeOf w1 v), .tuple (excArgs w1 v)]
           else .tuple [.obj (typeOf w1 v), .tuple (excArgs w1 v), st]) w1)

theorem importErrorGetstateReduce_proven : ImportErrorGetstateReduce := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v w d h
    simp only [importErrorGetstate, M.bind_app, getW_app]
    simp only [d] at h
    simp only [h, if_true, alloc_app]
    refine ⟨_, rfl, _, dictOf_alloc _ _ _, ?_, ?_⟩
    · intro k hk
      simp only [importKw, List.mem_cons, List.mem_nil_iff, or_false] at hk
      rcases hk with rfl | rfl | rfl
      · rw [lookup_optSet_ne _ _ _ _ (by decide), lookup_optSet_ne _ _ _ _ (by decide),
          lookup_optSet_same]
      · rw [lookup_optSet_ne _ _ _ _ (by decide), lookup_optSet_same,
          lookup_optSet_ne _ _ _ _ (by decide)]
      · rw [lookup_optSet_same, lookup_optSet_ne _ _ _ _ (by decide),
          lookup_optSet_ne _ _ _ _ (by decide)]
    · intro k hk
      simp only [importKw, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hk
      rw [lookup_optSet_ne _ _ _ _ (Ne.symm hk.2.2), lookup_optSet_ne _ _ _ _ (Ne.symm hk.2.1),
        lookup_optSet_ne _ _ _ _ (Ne.symm hk.1)]
  · intro v a w d h1 h2 h3 h4
    simp only [d] at h1 h2 h3
    simp [importErrorGetstate, h1, h2, h3, h4]
  · intro v w d h1 h2 h3 h4
    simp only [d] at h1 h2 h3
    simp [importErrorGetstate, h1, h2, h3, h4]
  · intro v st w w1 h
    simp only [importErrorReduce, M.bind_app, h, getW_app]
    cases st.is .none <;> rfl

/-! ## `OSError` -/

/-- **`oserror_use_init` is the slot test of `:2196`**: true exactly when the class's `tp_init`
is not `OSError_init` and its `tp_new` is `OSError_new`, i.e. a subclass that defines `__init__`
but not `__new__`. -/
def OsErrorUseInitSlots : Prop :=
  (∀ (w : World) (t : Addr), slotOf w t .tp_init = some (.c .osError) → oserrorUseInit w t = false) ∧
  (∀ (w : World) (t : Addr), slotOf w t .tp_new ≠ some (.c .osError) → oserrorUseInit w t = false) ∧
  (∀ (w : World) (t : Addr), slotOf w t .tp_init ≠ some (.c .osError) →
    slotOf w t .tp_new = some (.c .osError) → oserrorUseInit w t = true)

theorem osErrorUseInitSlots_proven : OsErrorUseInitSlots := by
  refine ⟨?_, ?_, ?_⟩
  · intro w t h
    simp [oserrorUseInit, h]
  · intro w t h
    simp [oserrorUseInit, h]
  · intro w t h1 h2
    simp [oserrorUseInit, h1, h2]

/-- **`OSError.__init__` when `oserror_use_init` holds** refuses keywords with `%.200s` of the
class name (`:2285-2286`) and otherwise is `oserror_init` on the parsed arguments (`:2288-2301`). -/
def OsErrorInitUseInit : Prop :=
  (∀ (rt : Rt) (self : Val) (args : List Val) (kw : Kw) (w : World),
    oserrorUseInit w (typeOf w self) = true → kw ≠ [] →
    osErrorInit rt self args kw w = .err (.exc B.TypeError (noKwMsg (typeName w self)) none) w) ∧
  (∀ (rt : Rt) (self : Val) (args : List Val) (w : World),
    oserrorUseInit w (typeOf w self) = true →
    osErrorInit rt self args [] w = oserrorInit rt self args (oserrorParseArgs args) w)

theorem osErrorInitUseInit_proven : OsErrorInitUseInit := by
  refine ⟨?_, ?_⟩
  · intro rt self args kw w h hk
    have : kw.isEmpty = false := by cases kw <;> simp_all
    simp [osErrorInit, h, argNoKeywords, this, typeErr, raiseC]
  · intro rt self args w h
    simp [osErrorInit, h, argNoKeywords]

/-- **What `oserror_init` stores** (`:2123-2176`). With 3 to 5 arguments and a filename other than
`None` (and not the `BlockingIOError` count), `errno`, `strerror` and `filename` are positions
0-2, `filename2` is position 4 when it is not `None` (otherwise unchanged), and `args` is cut to
the first two (`:2146-2163`). With fewer than 2 or more than 5 arguments nothing is parsed:
`errno` and `strerror` become NULL and `args` is kept whole. On an exact `BlockingIOError` an
`int` third argument in `Py_ssize_t` is `characters_written`, and `args` stays whole
(`:2137-2145`). `excNumberCheck w (.int n)` is the fact that `int` has `nb_index`; `MemNodup` is
the type invariant that each member name is stored once. -/
def OsErrorInitEffects : Prop :=
  (∀ (rt : Rt) (a : Addr) (d : ExcData) (e s f : Val) (rest : List Val) (w : World),
    IsExc w a d → MemNodup d → typeOf w (.obj a) ≠ B.BlockingIOError → rest.length ≤ 2 → f ≠ .none →
    ∃ w', oserrorInit rt (.obj a) (e :: s :: f :: rest) (oserrorParseArgs (e :: s :: f :: rest)) w = .ok () w' ∧
      memGet (excDataOf w' (.obj a)) "errno" = some e ∧
      memGet (excDataOf w' (.obj a)) "strerror" = some s ∧
      memGet (excDataOf w' (.obj a)) "filename" = some f ∧
      memGet (excDataOf w' (.obj a)) "filename2" =
        (if nonNone rest[1]? then rest[1]? else memGet d "filename2") ∧
      excArgs w' (.obj a) = [e, s]) ∧
  (∀ (rt : Rt) (a : Addr) (d : ExcData) (args : List Val) (w : World),
    IsExc w a d → MemNodup d → ¬ (2 ≤ args.length ∧ args.length ≤ 5) →
    ∃ w', oserrorInit rt (.obj a) args (oserrorParseArgs args) w = .ok () w' ∧
      memGet (excDataOf w' (.obj a)) "errno" = none ∧
      memGet (excDataOf w' (.obj a)) "strerror" = none ∧
      memGet (excDataOf w' (.obj a)) "filename" = memGet d "filename" ∧
      excArgs w' (.obj a) = args) ∧
  (∀ (rt : Rt) (a : Addr) (d : ExcData) (e s : Val) (n : Int) (rest : List Val) (w : World),
    IsExc w a d → typeOf w (.obj a) = B.BlockingIOError → excNumberCheck w (.int n) = true →
    inSsize n = true → rest.length ≤ 2 →
    ∃ w', oserrorInit rt (.obj a) (e :: s :: .int n :: rest) (oserrorParseArgs (e :: s :: .int n :: rest)) w = .ok () w' ∧
      (excDataOf w' (.obj a)).written = n ∧
      memGet (excDataOf w' (.obj a)) "filename" = memGet d "filename" ∧
      memGet (excDataOf w' (.obj a)) "errno" = some e ∧
      excArgs w' (.obj a) = e :: s :: .int n :: rest)

theorem osErrorInitEffects_proven : OsErrorInitEffects := by
  refine ⟨?_, ?_, ?_⟩
  · intro rt a d e s f rest w hx hnd ht hr hf
    have hp : oserrorParseArgs (e :: s :: f :: rest) =
        { myerrno := some e, strerror := some s, filename := some f, filename2 := rest[1]? } := by
      have h2 : 2 ≤ (e :: s :: f :: rest).length ∧ (e :: s :: f :: rest).length ≤ 5 := by
        simp; omega
      simp [oserrorParseArgs]; omega
    have hfn : f.is .none = false := by cases f <;> simp_all [Val.is]
    have hbt : (typeOf w (.obj a) == B.BlockingIOError) = false := by simpa using ht
    have hlen : 2 ≤ rest.length + 1 + 1 + 1 ∧ rest.length + 1 + 1 + 1 ≤ 5 := by omega
    have h1 := isExc_memSet hx "filename" (some f)
    have n1 := memSet_nodup hnd "filename" (some f)
    by_cases h2 : nonNone rest[1]? = true
    · have h3 := isExc_memSet h1 "filename2" rest[1]?
      have h4 := isExc_memSet h3 "errno" (some e)
      have h5 := isExc_memSet h4 "strerror" (some s)
      have h6 := h5.update (fun d => { d with args := [e, s] })
      refine ex_of_isExc h6 ?_ ?_
      · simp only [oserrorInit, hp, M.bind_app, getW_app]
        simp [hfn, hbt, excUpdate_app, h2, hlen]
        try rfl
      · intro h6
        simp only [excArgs]
        rw [h6.data]
        simp only [memGet_withArgs]
        simp only [h2, if_true]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · rw [memGet_memSet_ne _ "strerror" "errno" _ (by decide), memGet_memSet_same]
        · rw [memGet_memSet_same]
        · rw [memGet_memSet_ne _ "strerror" "filename" _ (by decide),
            memGet_memSet_ne _ "errno" "filename" _ (by decide),
            memGet_memSet_ne _ "filename2" "filename" _ (by decide), memGet_memSet_same]
        · rw [memGet_memSet_ne _ "strerror" "filename2" _ (by decide),
            memGet_memSet_ne _ "errno" "filename2" _ (by decide), memGet_memSet_self n1]
        · first | rfl | trivial
    · have h2' : nonNone rest[1]? = false := by simpa using h2
      have h4 := isExc_memSet h1 "errno" (some e)
      have h5 := isExc_memSet h4 "strerror" (some s)
      have h6 := h5.update (fun d => { d with args := [e, s] })
      refine ex_of_isExc h6 ?_ ?_
      · simp only [oserrorInit, hp, M.bind_app, getW_app]
        simp [hfn, hbt, excUpdate_app, h2', hlen]
        try rfl
      · intro h6
        simp only [excArgs]
        rw [h6.data]
        simp only [memGet_withArgs]
        simp only [h2', Bool.false_eq_true, if_false]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · rw [memGet_memSet_ne _ "strerror" "errno" _ (by decide), memGet_memSet_same]
        · rw [memGet_memSet_same]
        · rw [memGet_memSet_ne _ "strerror" "filename" _ (by decide),
            memGet_memSet_ne _ "errno" "filename" _ (by decide), memGet_memSet_same]
        · rw [memGet_memSet_ne _ "strerror" "filename2" _ (by decide),
            memGet_memSet_ne _ "errno" "filename2" _ (by decide),
            memGet_memSet_ne _ "filename" "filename2" _ (by decide)]
        · first | rfl | trivial
  · intro rt a d args w hx hnd hl
    have hp : oserrorParseArgs args = {} := by simp [oserrorParseArgs, hl]
    have h4 := isExc_memSet hx "errno" none
    have h5 := isExc_memSet h4 "strerror" none
    have h6 := h5.update (fun d => { d with args := args })
    refine ex_of_isExc h6 ?_ ?_
    · simp only [oserrorInit, hp, M.bind_app, getW_app]
      simp [excUpdate_app]
      try rfl
    · intro h6
      simp only [excArgs]
      rw [h6.data]
      simp only [memGet_withArgs]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [memGet_memSet_ne _ "strerror" "errno" _ (by decide), memGet_memSet_self hnd]
      · exact memGet_memSet_self (memSet_nodup hnd "errno" none) _ _
      · rw [memGet_memSet_ne _ "strerror" "filename" _ (by decide),
          memGet_memSet_ne _ "errno" "filename" _ (by decide)]
      · first | rfl | trivial
  · intro rt a d e s n rest w hx ht hn hs hr
    have hp : oserrorParseArgs (e :: s :: .int n :: rest) =
        { myerrno := some e, strerror := some s, filename := some (.int n), filename2 := rest[1]? } := by
      simp [oserrorParseArgs]; omega
    have h1 := hx.update (fun d => { d with written := n })
    have h4 := isExc_memSet h1 "errno" (some e)
    have h5 := isExc_memSet h4 "strerror" (some s)
    have h6 := h5.update (fun d => { d with args := e :: s :: .int n :: rest })
    refine ex_of_isExc h6 ?_ ?_
    · simp only [oserrorInit, hp, M.bind_app, getW_app]
      simp [Val.is, ht, hn, excAsSsizeValueError, excNumberIndex, intOf, hs, excUpdate_app]
      try rfl
    · intro h6
      simp only [excArgs]
      rw [h6.data]
      simp only [memGet_withArgs]
      refine ⟨by first | rfl | trivial, ?_, ?_, by first | rfl | trivial⟩
      · rw [memGet_memSet_ne _ "strerror" "filename" _ (by decide),
          memGet_memSet_ne _ "errno" "filename" _ (by decide), memGet_withWritten]
      · rw [memGet_memSet_ne _ "strerror" "errno" _ (by decide), memGet_memSet_same]

/-- **Deleting `characters_written` and its range.** `del e.characters_written` is
`AttributeError: characters_written` when it is unset (`-1`), and otherwise resets it to unset,
after which reading it is the same `AttributeError` (`:2448-2455`). An `int` outside `Py_ssize_t`
is the `ValueError` of `PyNumber_AsSsize_t(arg, PyExc_ValueError)` (`:2457-2459`), with nothing
stored. -/
def OsErrorWrittenSetBranches : Prop :=
  (∀ (rt : Rt) (a : Addr) (d : ExcData) (w : World), IsExc w a d → d.written = -1 →
    osErrorWrittenSet rt (.obj a) none w = .err (.exc B.AttributeError "characters_written" none) w) ∧
  (∀ (rt : Rt) (a : Addr) (d : ExcData) (w : World), IsExc w a d → d.written ≠ -1 →
    osErrorWrittenSet rt (.obj a) none w = .ok () (excUpdW w a fun d => { d with written := -1 }) ∧
    osErrorWrittenGet (.obj a) (excUpdW w a fun d => { d with written := -1 }) =
      .err (.exc B.AttributeError "characters_written" none) (excUpdW w a fun d => { d with written := -1 })) ∧
  (∀ (rt : Rt) (self : Val) (n : Int) (w : World), inSsize n = false →
    osErrorWrittenSet rt self (some (.int n)) w =
      .err (.exc B.ValueError s!"cannot fit '{trunc 200 (typeName w (.int n))}' into an index-sized integer" none) w)

theorem osErrorWrittenSetBranches_proven : OsErrorWrittenSetBranches := by
  refine ⟨?_, ?_, ?_⟩
  · intro rt a d w hx h
    simp [osErrorWrittenSet, hx.data, h, attrErr, raiseC]
  · intro rt a d w hx h
    have hne : (d.written == -1) = false := by simpa using h
    refine ⟨?_, ?_⟩
    · simp [osErrorWrittenSet, hx.data, h, excUpdate_app]
    · simp [osErrorWrittenGet, excUpdW_data hx, attrErr, raiseC]
  · intro rt self n w h
    simp [osErrorWrittenSet, excAsSsizeValueError, excNumberIndex, intOf, h, valueErr, raiseC]

/-- **`oserror_init` with two arguments, and with a `None` filename** (`:2136`, `:2165-2172`):
`OSError(errno, strerror)` stores both and keeps `args` whole; with 3 to 5 arguments and a `None`
third one, the filename block is skipped (no `filename`, no `filename2`, no cut), and `errno` and
`strerror` are stored. -/
def OsErrorInitTwoOrNone : Prop :=
  (∀ (rt : Rt) (a : Addr) (d : ExcData) (e s : Val) (w : World), IsExc w a d →
    ∃ w', oserrorInit rt (.obj a) [e, s] (oserrorParseArgs [e, s]) w = .ok () w' ∧
      memGet (excDataOf w' (.obj a)) "errno" = some e ∧
      memGet (excDataOf w' (.obj a)) "strerror" = some s ∧
      memGet (excDataOf w' (.obj a)) "filename" = memGet d "filename" ∧
      excArgs w' (.obj a) = [e, s]) ∧
  (∀ (rt : Rt) (a : Addr) (d : ExcData) (e s : Val) (rest : List Val) (w : World), IsExc w a d →
    rest.length ≤ 2 →
    ∃ w', oserrorInit rt (.obj a) (e :: s :: .none :: rest)
        (oserrorParseArgs (e :: s :: .none :: rest)) w = .ok () w' ∧
      memGet (excDataOf w' (.obj a)) "errno" = some e ∧
      memGet (excDataOf w' (.obj a)) "strerror" = some s ∧
      memGet (excDataOf w' (.obj a)) "filename" = memGet d "filename" ∧
      memGet (excDataOf w' (.obj a)) "filename2" = memGet d "filename2" ∧
      excArgs w' (.obj a) = e :: s :: .none :: rest)

theorem osErrorInitTwoOrNone_proven : OsErrorInitTwoOrNone := by
  refine ⟨?_, ?_⟩
  · intro rt a d e s w hx
    have hp : oserrorParseArgs [e, s] = { myerrno := some e, strerror := some s } := by
      simp [oserrorParseArgs]
    have h4 := isExc_memSet hx "errno" (some e)
    have h5 := isExc_memSet h4 "strerror" (some s)
    have h6 := h5.update (fun d => { d with args := [e, s] })
    refine ex_of_isExc h6 ?_ ?_
    · simp only [oserrorInit, hp, M.bind_app, getW_app]
      simp [excUpdate_app]
      try rfl
    · intro h6
      simp only [excArgs]
      rw [h6.data]
      simp only [memGet_withArgs]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [memGet_memSet_ne _ "strerror" "errno" _ (by decide), memGet_memSet_same]
      · rw [memGet_memSet_same]
      · rw [memGet_memSet_ne _ "strerror" "filename" _ (by decide),
          memGet_memSet_ne _ "errno" "filename" _ (by decide)]
      · first | rfl | trivial
  · intro rt a d e s rest w hx hr
    have hp : oserrorParseArgs (e :: s :: .none :: rest) =
        { myerrno := some e, strerror := some s, filename := some .none, filename2 := rest[1]? } := by
      simp [oserrorParseArgs]; omega
    have h4 := isExc_memSet hx "errno" (some e)
    have h5 := isExc_memSet h4 "strerror" (some s)
    have h6 := h5.update (fun d => { d with args := e :: s :: .none :: rest })
    refine ex_of_isExc h6 ?_ ?_
    · simp only [oserrorInit, hp, M.bind_app, getW_app]
      simp [Val.is, excUpdate_app]
      try rfl
    · intro h6
      simp only [excArgs]
      rw [h6.data]
      simp only [memGet_withArgs]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [memGet_memSet_ne _ "strerror" "errno" _ (by decide), memGet_memSet_same]
      · rw [memGet_memSet_same]
      · rw [memGet_memSet_ne _ "strerror" "filename" _ (by decide),
          memGet_memSet_ne _ "errno" "filename" _ (by decide)]
      · rw [memGet_memSet_ne _ "strerror" "filename2" _ (by decide),
          memGet_memSet_ne _ "errno" "filename2" _ (by decide)]
      · first | rfl | trivial

/-- **`NameError.__init__` and `AttributeError.__init__` store their keywords and reset the
others** (`:2580-2605`, `:2663-2690`): with keywords among the names (at most the parse's bound),
`args` is the positional arguments and each member is its keyword or NULL (`Py_XSETREF` with
NULL, `:2602`, `:2686-2687`), on a first or a later call. An init that keeps an old `name` or
`obj` fails. `MemNodup` is the type invariant that each member name is stored once. -/
def NameAttrInitStores : Prop :=
  (∀ (a : Addr) (d : ExcData) (args : List Val) (kw : Kw) (w : World), IsExc w a d → MemNodup d →
    kw.length ≤ 1 → kw.all (fun p => ["name"].contains p.1) = true →
    ∃ w', nameErrorInit (.obj a) args kw w = .ok () w' ∧
      excArgs w' (.obj a) = args ∧
      memGet (excDataOf w' (.obj a)) "name" = NameDict.get? kw "name") ∧
  (∀ (a : Addr) (d : ExcData) (args : List Val) (kw : Kw) (w : World), IsExc w a d → MemNodup d →
    kw.length ≤ 2 → kw.all (fun p => ["name", "obj"].contains p.1) = true →
    ∃ w', attributeErrorInit (.obj a) args kw w = .ok () w' ∧
      excArgs w' (.obj a) = args ∧
      memGet (excDataOf w' (.obj a)) "name" = NameDict.get? kw "name" ∧
      memGet (excDataOf w' (.obj a)) "obj" = NameDict.get? kw "obj")

theorem nameAttrInitStores_proven : NameAttrInitStores := by
  refine ⟨?_, ?_⟩
  · intro a d args kw w hx hnd hl hall
    have hany : kw.any (fun p => !["name"].contains p.1) = false := by
      rw [List.all_eq_true] at hall
      rw [List.any_eq_false]
      intro p hp
      have := hall p hp
      simp only [Bool.not_eq_true', Bool.not_eq_false', this, not_true_eq_false, not_false_eq_true]
      decide
    have hgt : ¬ 1 < kw.length := by omega
    have h1 := hx.update (fun d => { d with args := args })
    have h2 := isExc_memSet h1 "name" (NameDict.get? kw "name")
    refine ex_of_isExc h2 ?_ ?_
    · simp only [nameErrorInit, baseExceptionInit, argNoKeywords, argKeywordOnly, M.bind_app,
        getW_app, excUpdate_app]
      simp only [List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, if_false, gt_iff_lt, hgt, hany]
      simp [excUpdate_app, hgt]
      try rfl
    · intro h2
      simp only [excArgs]
      rw [h2.data]
      have n0 : MemNodup { d with args := args } := hnd
      exact ⟨rfl, memGet_memSet_self n0 _ _⟩
  · intro a d args kw w hx hnd hl hall
    have hany : kw.any (fun p => !["name", "obj"].contains p.1) = false := by
      rw [List.all_eq_true] at hall
      rw [List.any_eq_false]
      intro p hp
      have := hall p hp
      simp only [Bool.not_eq_true', Bool.not_eq_false', this, not_true_eq_false, not_false_eq_true]
      decide
    have hgt : ¬ 2 < kw.length := by omega
    have h1 := hx.update (fun d => { d with args := args })
    have h2 := isExc_memSet h1 "name" (NameDict.get? kw "name")
    have h3 := isExc_memSet h2 "obj" (NameDict.get? kw "obj")
    refine ex_of_isExc h3 ?_ ?_
    · simp only [attributeErrorInit, baseExceptionInit, argNoKeywords, argKeywordOnly, M.bind_app,
        getW_app, excUpdate_app]
      simp only [List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, if_false, gt_iff_lt, hgt, hany]
      simp [excUpdate_app, hgt]
      try rfl
    · intro h3
      simp only [excArgs]
      rw [h3.data]
      have n0 : MemNodup { d with args := args } := hnd
      have n1 := memSet_nodup n0 "name" (NameDict.get? kw "name")
      refine ⟨rfl, ?_, memGet_memSet_self n1 _ _⟩
      rw [memGet_memSet_ne _ "obj" "name" _ (by decide), memGet_memSet_self n0]

/-! ## `SyntaxError` -/

theorem memGet_memSet_eq {d : ExcData} (hd : MemNodup d) (n : Name) (v : Option Val) (m : Name) :
    memGet (memSet n v d) m = if n = m then v else memGet d m := by
  by_cases h : n = m
  · subst h; simp [memGet_memSet_self hd]
  · simp [h, memGet_memSet_ne _ _ _ _ h]

/-- **`SyntaxError.__init__` stores `msg` and the location** (`:2790-2837`): with at least one
argument `msg` is the first (`:2800-2802`), and with exactly two the second is parsed: it is
`syntaxErrorParseInfo` in the world after `args` and `msg` were stored. The parse converts it with
`tuple()`, and 4, 6 or 7 items are stored as `filename`, `lineno`, `offset`, `text` and the
optional `end_lineno`, `end_offset`, `_metadata` (NULL when absent, `:2822-2828`). Five items are
the `end_offset` refusal (`SyntaxErrorInitChecks`). `MemNodup` is the type invariant that each
member name is stored once. -/
def SyntaxErrorInitStores : Prop :=
  (∀ (rt : Rt) (a : Addr) (d : ExcData) (items : List Val) (w : World),
    IsExc w a d → MemNodup d → 4 ≤ items.length → items.length ≤ 7 → items.length ≠ 5 →
    ∃ w', syntaxErrorParseInfo rt (.obj a) (.tuple items) w = .ok () w' ∧
      memGet (excDataOf w' (.obj a)) "filename" = items[0]? ∧
      memGet (excDataOf w' (.obj a)) "lineno" = items[1]? ∧
      memGet (excDataOf w' (.obj a)) "offset" = items[2]? ∧
      memGet (excDataOf w' (.obj a)) "text" = items[3]? ∧
      memGet (excDataOf w' (.obj a)) "end_lineno" = items[4]? ∧
      memGet (excDataOf w' (.obj a)) "end_offset" = items[5]? ∧
      memGet (excDataOf w' (.obj a)) "_metadata" = items[6]?) ∧
  (∀ (rt : Rt) (a : Addr) (m info : Val) (w : World),
    syntaxErrorInit rt (.obj a) [m, info] [] w =
      syntaxErrorParseInfo rt (.obj a) info
        (excUpdW (excUpdW w a fun d => { d with args := [m, info] }) a (memSet "msg" (some m)))) ∧
  (∀ (rt : Rt) (a : Addr) (d : ExcData) (m : Val) (rest : List Val) (w : World),
    IsExc w a d → rest.length ≠ 1 →
    ∃ w', syntaxErrorInit rt (.obj a) (m :: rest) [] w = .ok () w' ∧
      excArgs w' (.obj a) = m :: rest ∧ memGet (excDataOf w' (.obj a)) "msg" = some m ∧
      memGet (excDataOf w' (.obj a)) "filename" = memGet d "filename") ∧
  (∀ (rt : Rt) (a : Addr) (d : ExcData) (w : World), IsExc w a d →
    ∃ w', syntaxErrorInit rt (.obj a) [] [] w = .ok () w' ∧ excArgs w' (.obj a) = [] ∧
      memGet (excDataOf w' (.obj a)) "msg" = memGet d "msg")

theorem argCount_in (n : Nat) (h1 : 4 ≤ n) (h2 : n ≤ 7) (W : World) :
    argCount none 4 7 n W = .ok () W := by
  have hb : (decide (n < 4) || decide (7 < n)) = false := by
    rw [Bool.or_eq_false_iff]; constructor <;> simp <;> omega
  unfold argCount
  simp only [hb]
  rfl

theorem syntaxErrorParseInfo_ok (rt : Rt) (a : Addr) (items : List Val) (w : World)
    (hc : ∀ W, argCount none 4 7 items.length W = .ok () W)
    (hend : (items[4]?.isSome && items[5]?.isNone) = false) :
    syntaxErrorParseInfo rt (.obj a) (.tuple items) w = syntaxErrorStoreInfo (.obj a) items w := by
  simp only [syntaxErrorParseInfo, M.bind_app, excSeqTuple, M.pure_app, hc, hend]
  cases syntaxErrorStoreInfo (.obj a) items w <;> rfl

theorem storeInfo_reads (d : ExcData) (hnd : MemNodup d) (items : List Val) :
    memGet (memSet "_metadata" items[6]? (memSet "end_offset" items[5]? (memSet "end_lineno" items[4]?
      (memSet "text" items[3]? (memSet "offset" items[2]? (memSet "lineno" items[1]?
        (memSet "filename" items[0]? d))))))) "filename" = items[0]? ∧
    memGet (memSet "_metadata" items[6]? (memSet "end_offset" items[5]? (memSet "end_lineno" items[4]?
      (memSet "text" items[3]? (memSet "offset" items[2]? (memSet "lineno" items[1]?
        (memSet "filename" items[0]? d))))))) "lineno" = items[1]? ∧
    memGet (memSet "_metadata" items[6]? (memSet "end_offset" items[5]? (memSet "end_lineno" items[4]?
      (memSet "text" items[3]? (memSet "offset" items[2]? (memSet "lineno" items[1]?
        (memSet "filename" items[0]? d))))))) "offset" = items[2]? ∧
    memGet (memSet "_metadata" items[6]? (memSet "end_offset" items[5]? (memSet "end_lineno" items[4]?
      (memSet "text" items[3]? (memSet "offset" items[2]? (memSet "lineno" items[1]?
        (memSet "filename" items[0]? d))))))) "text" = items[3]? ∧
    memGet (memSet "_metadata" items[6]? (memSet "end_offset" items[5]? (memSet "end_lineno" items[4]?
      (memSet "text" items[3]? (memSet "offset" items[2]? (memSet "lineno" items[1]?
        (memSet "filename" items[0]? d))))))) "end_lineno" = items[4]? ∧
    memGet (memSet "_metadata" items[6]? (memSet "end_offset" items[5]? (memSet "end_lineno" items[4]?
      (memSet "text" items[3]? (memSet "offset" items[2]? (memSet "lineno" items[1]?
        (memSet "filename" items[0]? d))))))) "end_offset" = items[5]? ∧
    memGet (memSet "_metadata" items[6]? (memSet "end_offset" items[5]? (memSet "end_lineno" items[4]?
      (memSet "text" items[3]? (memSet "offset" items[2]? (memSet "lineno" items[1]?
        (memSet "filename" items[0]? d))))))) "_metadata" = items[6]? := by
  have n4 := memSet_nodup hnd "filename" items[0]?
  have n5 := memSet_nodup n4 "lineno" items[1]?
  have n6 := memSet_nodup n5 "offset" items[2]?
  have n7 := memSet_nodup n6 "text" items[3]?
  have n8 := memSet_nodup n7 "end_lineno" items[4]?
  have n9 := memSet_nodup n8 "end_offset" items[5]?
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [memGet_memSet_ne _ "_metadata" "filename" _ (by decide), memGet_memSet_ne _ "end_offset" "filename" _ (by decide), memGet_memSet_ne _ "end_lineno" "filename" _ (by decide), memGet_memSet_ne _ "text" "filename" _ (by decide), memGet_memSet_ne _ "offset" "filename" _ (by decide), memGet_memSet_ne _ "lineno" "filename" _ (by decide), memGet_memSet_self hnd]
  · rw [memGet_memSet_ne _ "_metadata" "lineno" _ (by decide), memGet_memSet_ne _ "end_offset" "lineno" _ (by decide), memGet_memSet_ne _ "end_lineno" "lineno" _ (by decide), memGet_memSet_ne _ "text" "lineno" _ (by decide), memGet_memSet_ne _ "offset" "lineno" _ (by decide), memGet_memSet_self n4]
  · rw [memGet_memSet_ne _ "_metadata" "offset" _ (by decide), memGet_memSet_ne _ "end_offset" "offset" _ (by decide), memGet_memSet_ne _ "end_lineno" "offset" _ (by decide), memGet_memSet_ne _ "text" "offset" _ (by decide), memGet_memSet_self n5]
  · rw [memGet_memSet_ne _ "_metadata" "text" _ (by decide), memGet_memSet_ne _ "end_offset" "text" _ (by decide), memGet_memSet_ne _ "end_lineno" "text" _ (by decide), memGet_memSet_self n6]
  · rw [memGet_memSet_ne _ "_metadata" "end_lineno" _ (by decide), memGet_memSet_ne _ "end_offset" "end_lineno" _ (by decide), memGet_memSet_self n7]
  · rw [memGet_memSet_ne _ "_metadata" "end_offset" _ (by decide), memGet_memSet_self n8]
  · rw [memGet_memSet_self n9]

theorem excUpdate_isExc {w w' : World} {a : Addr} {d : ExcData} (hx : IsExc w a d)
    (f : ExcData → ExcData) (h : excUpdate (.obj a) f w = .ok () w') : IsExc w' a (f d) := by
  rw [excUpdate_app] at h
  cases h
  exact hx.update f

theorem excUpdate_total2 (a : Addr) (f : ExcData → ExcData) (w : World) :
    ∃ w', excUpdate (.obj a) f w = .ok () w' := ⟨_, excUpdate_app w a f⟩

theorem storeInfo_spec {w : World} {a : Addr} {d : ExcData} (hx : IsExc w a d) (items : List Val) :
    ∃ w', syntaxErrorStoreInfo (.obj a) items w = .ok () w' ∧
      IsExc w' a (memSet "_metadata" items[6]? (memSet "end_offset" items[5]? (memSet "end_lineno" items[4]?
        (memSet "text" items[3]? (memSet "offset" items[2]? (memSet "lineno" items[1]?
          (memSet "filename" items[0]? d))))))) := by
  obtain ⟨w1, h1⟩ := excUpdate_total2 a (memSet "filename" items[0]?) w
  have y1 := excUpdate_isExc hx _ h1
  obtain ⟨w2, h2⟩ := excUpdate_total2 a (memSet "lineno" items[1]?) w1
  have y2 := excUpdate_isExc y1 _ h2
  obtain ⟨w3, h3⟩ := excUpdate_total2 a (memSet "offset" items[2]?) w2
  have y3 := excUpdate_isExc y2 _ h3
  obtain ⟨w4, h4⟩ := excUpdate_total2 a (memSet "text" items[3]?) w3
  have y4 := excUpdate_isExc y3 _ h4
  obtain ⟨w5, h5⟩ := excUpdate_total2 a (memSet "end_lineno" items[4]?) w4
  have y5 := excUpdate_isExc y4 _ h5
  obtain ⟨w6, h6⟩ := excUpdate_total2 a (memSet "end_offset" items[5]?) w5
  have y6 := excUpdate_isExc y5 _ h6
  obtain ⟨w7, h7⟩ := excUpdate_total2 a (memSet "_metadata" items[6]?) w6
  have y7 := excUpdate_isExc y6 _ h7
  exact ⟨w7, by simp only [syntaxErrorStoreInfo, M.bind_app, h1, h2, h3, h4, h5, h6, h7], y7⟩

theorem syntaxErrorInitStores_proven : SyntaxErrorInitStores := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro rt a d items w hx hnd h4 h7 h5
    have hend : (items[4]?.isSome && items[5]?.isNone) = false := by
      rcases Nat.lt_or_ge items.length 5 with h | h
      · rw [List.getElem?_eq_none (show items.length ≤ 4 by omega)]; rfl
      · rw [List.getElem?_eq_getElem (show 5 < items.length by omega)]
        simp
    obtain ⟨w', hs, hx'⟩ := storeInfo_spec hx items
    refine ⟨w', ?_, ?_⟩
    · rw [syntaxErrorParseInfo_ok rt a items w (argCount_in _ h4 h7) hend, hs]
    · rw [hx'.data]
      exact storeInfo_reads d hnd items
  · intro rt a m info w
    simp only [syntaxErrorInit, baseExceptionInit, argNoKeywords, M.bind_app, getW_app,
      List.isEmpty_nil, excUpdate_app]
    rfl
  · intro rt a d m rest w hx hr
    have x1 := hx.update (fun d => { d with args := m :: rest })
    have x2 := isExc_memSet x1 "msg" (some m)
    refine ex_of_isExc x2 ?_ ?_
    · simp only [syntaxErrorInit, baseExceptionInit, argNoKeywords, M.bind_app, getW_app,
        List.isEmpty_nil, excUpdate_app]
      match rest, hr with
      | [], _ => simp [excUpdate_app]
      | _ :: _ :: _, _ => simp [excUpdate_app]
    · intro x2
      simp only [excArgs]
      rw [x2.data]
      refine ⟨rfl, memGet_memSet_same _ _ _, ?_⟩
      rw [memGet_memSet_ne _ "msg" "filename" _ (by decide)]
      rfl
  · intro rt a d w hx
    have x1 := hx.update (fun d => { d with args := [] })
    refine ex_of_isExc x1 ?_ ?_
    · simp [syntaxErrorInit, baseExceptionInit, argNoKeywords, excUpdate_app]
    · intro x1
      simp only [excArgs]
      rw [x1.data]
      exact ⟨rfl, rfl⟩

theorem basenameOffset_nosep (i off : Nat) (cs : List Char) (h : sepChar ∉ cs) :
    basenameOffset i off cs = off := by
  induction cs generalizing i off with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.mem_cons, not_or] at h
    have hc : (c == sepChar) = false := by simpa using Ne.symm h.1
    simp [basenameOffset, hc, ih _ _ h.2]

theorem basenameOffset_last (post : List Char) (hp : sepChar ∉ post) :
    ∀ (pre : List Char) (i off : Nat),
      basenameOffset i off (pre ++ sepChar :: post) = i + pre.length + 1 := by
  intro pre
  induction pre with
  | nil => intro i off; simp [basenameOffset, basenameOffset_nosep _ _ _ hp]
  | cons c pre ih =>
    intro i off
    simp only [List.cons_append, basenameOffset, ih, List.length_cons]
    omega

/-- **`my_basename` drops exactly up to the last separator** (`:2882-2904`): with a `/` in the
name, the result is what follows the last one; with none, the name itself. `fun _ => ""` fails
both. -/
def MyBasenameExact : Prop :=
  (∀ (pre post : List Char), sepChar ∉ post →
    myBasename (String.ofList (pre ++ sepChar :: post)) = String.ofList post) ∧
  (∀ (s : String), sepChar ∉ s.toList → myBasename s = s)

theorem myBasenameExact_proven : MyBasenameExact := by
  refine ⟨?_, ?_⟩
  · intro pre post hp
    have ho := basenameOffset_last post hp pre 0 0
    simp only [myBasename, String.toList_ofList, ho]
    simp
  · intro s h
    simp [myBasename, basenameOffset_nosep _ _ _ h]

/-- **`SyntaxError.__str__`** (`:2907-2949`): `str(msg)` (`None` when unset) is followed by
` (file, line N)`, ` (file)` or ` (line N)`, where `file` is `my_basename` of a `str` filename
(subclasses included, printed by their content) and `N` the value of an exact `int` lineno, `-1`
when it does not fit in `long`; with neither, just `str(msg)`. The filename and lineno are read
before `str(msg)` runs. -/
def SyntaxErrorStrFormats : Prop :=
  ∀ (rt : Rt) (self : Val) (m : String) (w w1 : World),
    rt.str (orNone (memGet (excDataOf w self) "msg")) w = .ok m w1 →
    (∀ (f : Val) (fs : String) (l : Int), memGet (excDataOf w self) "filename" = some f →
      strOf w f = some fs → memGet (excDataOf w self) "lineno" = some (.int l) →
      syntaxErrorStr rt self w = .ok (.str s!"{m} ({myBasename fs}, line {longOrMinusOne l})") w1) ∧
    (∀ (f : Val) (fs : String), memGet (excDataOf w self) "filename" = some f →
      strOf w f = some fs → (∀ l, memGet (excDataOf w self) "lineno" ≠ some (.int l)) →
      syntaxErrorStr rt self w = .ok (.str s!"{m} ({myBasename fs})") w1) ∧
    (∀ (l : Int), (∀ f fs, memGet (excDataOf w self) "filename" = some f → strOf w f ≠ some fs) →
      memGet (excDataOf w self) "lineno" = some (.int l) →
      syntaxErrorStr rt self w = .ok (.str s!"{m} (line {longOrMinusOne l})") w1)

theorem syntaxErrorStrFormats_proven : SyntaxErrorStrFormats := by
  intro rt self m w w1 hm
  refine ⟨?_, ?_, ?_⟩
  · intro f fs l h1 h2 h3
    simp only [syntaxErrorStr, M.bind_app, getW_app, h1, Option.map, h2, h3]
    simp [hm]
  · intro f fs h1 h2 h3
    have hl : (match memGet (excDataOf w self) "lineno" with
        | some (.int i) => some i
        | _ => (none : Option Int)) = none := by
      cases hq : memGet (excDataOf w self) "lineno" with
      | none => rfl
      | some v => cases v <;> first | rfl | exact absurd hq (h3 _)
    simp only [syntaxErrorStr, M.bind_app, getW_app, h1, Option.map, h2, hl]
    simp [hm]
  · intro l h1 h3
    cases hq : memGet (excDataOf w self) "filename" with
    | none => simp [syntaxErrorStr, hq, h3, hm]
    | some f =>
      cases hs : strOf w f with
      | none => simp [syntaxErrorStr, hq, hs, h3, hm]
      | some fs => exact absurd hs (h1 f fs hq)

/-! ## `AttributeError` pickling -/

/-- **`AttributeError.__getstate__` and `__reduce__`** (`:2719-2760`): the state is a new dict, a
copy of the instance dict with `name` over it when the member is set and `args` always (`args`
is never NULL on an initialised object); `obj` is left out on purpose (`:2733-2735`), so the state
holds `obj` only when the instance dict does; every other key is the instance dict's.
`__reduce__` is `(type, args, state)` with `type` and `args` read after `__getstate__` ran
(`:2757`). The instance dict's keys are compared by the model's identity test (exact `str`
attribute names); a key with a colliding hash and a Python `__eq__` is outside the model, see bug
`typeobj-exc-getstate-borrowed-dict`. -/
def AttributeErrorGetstateReduce : Prop :=
  (∀ (v : Val) (w : World),
    ∃ w', attributeErrorGetstate v w = .ok (.obj w.heap.size) w' ∧
      ∃ es, dictOf w' (.obj w.heap.size) = some es ∧
        dictLookup es (.str "args") = some (.tuple (excArgs w v)) ∧
        dictLookup es (.str "name") =
          (memGet (excDataOf w v) "name").or (dictLookup (instDictEntries w v) (.str "name")) ∧
        dictLookup es (.str "obj") = dictLookup (instDictEntries w v) (.str "obj") ∧
        (∀ k, k ≠ "args" → k ≠ "name" →
          dictLookup es (.str k) = dictLookup (instDictEntries w v) (.str k))) ∧
  (∀ (v st : Val) (w w1 : World), attributeErrorGetstate v w = .ok st w1 →
    attributeErrorReduce v w = .ok (.tuple [.obj (typeOf w1 v), .tuple (excArgs w1 v), st]) w1)

theorem attributeErrorGetstateReduce_proven : AttributeErrorGetstateReduce := by
  refine ⟨?_, ?_⟩
  · intro v w
    simp only [attributeErrorGetstate, M.bind_app, getW_app, alloc_app]
    refine ⟨_, rfl, _, dictOf_alloc _ _ _, ?_, ?_, ?_, ?_⟩
    · rw [dictLookup_setEntry_same]; rfl
    · rw [dictLookup_setEntry_ne _ _ _ _ (by decide), lookup_optSet_same]
    · rw [dictLookup_setEntry_ne _ _ _ _ (by decide), lookup_optSet_ne _ _ _ _ (by decide)]
    · intro k h1 h2
      rw [dictLookup_setEntry_ne _ _ _ _ (Ne.symm h1), lookup_optSet_ne _ _ _ _ (Ne.symm h2)]
  · intro v st w w1 h
    simp only [attributeErrorReduce, M.bind_app, h, getW_app]
    rfl

/-! ## `MemoryError` and its freelist -/

/-- **`MemoryError.__new__` with the freelist explicit** (`:4111-4151`): a subclass gets a fresh
object with its arguments and leaves the freelist alone; `MemoryError` itself takes the most
recently freed entry with `args` `()` when one is free, and a fresh object with the given
arguments when none is. -/
def MemoryErrorNewBranches : Prop :=
  (∀ (args : List Val) (s : MemFreelist),
    memoryErrorNewC false args s = (.fresh { args := args }, s)) ∧
  (∀ (args : List Val) (d : ExcData) (s : MemFreelist),
    memoryErrorNewC true args (d :: s) = (.reused { d with args := [] }, s)) ∧
  (∀ (args : List Val), memoryErrorNewC true args [] = (.fresh { args := args }, []))

theorem memoryErrorNewBranches_proven : MemoryErrorNewBranches := by
  refine ⟨?_, ?_, ?_⟩
  · intro args s; rfl
  · intro args d s; rfl
  · intro args; rfl

/-- **`MemoryError(*args)` keeps its arguments**, as a subclass and `BaseException.__new__` do.
FALSE whenever a freelist entry is free, which is the case from startup (16 preallocated):
the entry comes back with `args` `()` (`:4124`). Holds once the freelist is empty. -/
def MemoryErrorNewCKeepsArgs : Prop :=
  ∀ (args : List Val) (s : MemFreelist) (d : ExcData) (s' : MemFreelist),
    memoryErrorNewC true args s = (.reused d, s') → d.args = args

theorem memoryErrorNewCKeepsArgs_refuted : ¬MemoryErrorNewCKeepsArgs := by
  intro h
  have := h [.int 1] [{}] { args := [] } [] rfl
  simp at this

/-- **`_PyErr_NoMemory` takes a freelist entry, or the shared last-resort error** (`:4154-4167`,
`get_memory_error(0, NULL, NULL)`): with an entry free it is that entry, `args` `()`, and the list
shrinks by one; with none it is the last-resort singleton, never a fresh allocation. -/
def PyErrNoMemoryBranches : Prop :=
  (∀ (d : ExcData) (s : MemFreelist), pyErrNoMemory (d :: s) = (.reused { d with args := [] }, s)) ∧
  pyErrNoMemory [] = (.lastResort, [])

theorem pyErrNoMemoryBranches_proven : PyErrNoMemoryBranches := ⟨fun _ _ => rfl, rfl⟩

/-- **`preallocate_memerrors` fills the freelist with sixteen cleared objects** (`:4198-4217`):
each is a `MemoryError` made with no arguments and passed through `BaseException_clear`, so it has
`args` `()` and no traceback, cause, context or notes. -/
def PreallocateContents : Prop :=
  preallocateMemerrors.length = memerrorsSave ∧
  ∀ d ∈ preallocateMemerrors, d = baseExceptionClear { args := [] }

theorem preallocateContents_proven : PreallocateContents := by
  refine ⟨rfl, ?_⟩
  intro d hd
  simp [preallocateMemerrors, memoryErrorDealloc, memerrorsSave, List.range, List.range.loop,
    List.foldl] at hd
  first
    | exact hd
    | (rcases hd with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> exact h)

end PyLean.TypeObj
