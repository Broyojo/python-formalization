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
parse, raised after `BaseException_init` has already replaced `args` (`:1813`). An `__init__`
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
      .err (.exc B.TypeError s!"ImportError() got an unexpected keyword argument '{k}'" none)
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

end PyLean.TypeObj
