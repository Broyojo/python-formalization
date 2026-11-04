import PyLean.CoreLibs.Misc.Contextlib.HeapLemmas

/-!
`@wraps(func)` on the `helper` of `contextmanager` and `asynccontextmanager`, Lib/contextlib.py:365,
:398: what the decoration copies onto `helper`, in which order it reads `func`, and how it fails.
-/

namespace PyLean.CoreLibs.Misc.Contextlib

open PyLean

variable {σ Val D : Type}

/-- What the setter of `a` on a function object accepts (Objects/funcobject.c:716-733, :743-761,
:934-956, :1035-1047); the setters of `__module__` and `__doc__` take anything. -/
def Accepts (k : ValOps Val) (a : String) (v : Val) : Prop :=
  (a = "__name__" → k.isStr v = true) ∧ (a = "__qualname__" → k.isStr v = true) ∧
  (a = "__annotate__" → k.isNone v = true ∨ k.callable v = true) ∧
  (a = "__type_params__" → k.isTuple v = true)

/-- The setter of `a` refuses `v` with `TypeError(msg)`. -/
def Refuses (k : ValOps Val) (a : String) (v : Val) (msg : String) : Prop :=
  (a = "__name__" ∧ k.isStr v = false ∧ msg = "__name__ must be set to a string object") ∨
  (a = "__qualname__" ∧ k.isStr v = false ∧ msg = "__qualname__ must be set to a string object") ∨
  (a = "__annotate__" ∧ k.isNone v = false ∧ k.callable v = false ∧
    msg = "__annotate__ must be callable or None") ∨
  (a = "__type_params__" ∧ k.isTuple v = false ∧ msg = "__type_params__ must be set to a tuple")

/-- A read of `func` that the loop gets past: a value the setter accepts, or an `AttributeError`. -/
def Copyable (k : ValOps Val) (h : Heap) (a : String) (r : Res Val) : Prop :=
  (∃ v, r = .ok v ∧ Accepts k a v) ∨ (∃ e, r = .error e ∧ h.isInst e "AttributeError" = true)

/-- The value read, or `d` when the read raised. -/
def pick (r : Res Val) (d : Val) : Val :=
  match r with
  | .ok v => v
  | .error _ => d

/-- The world after reading `names` in order, each read changing it by `upd`. -/
def afterReads (upd : String → σ → σ) (names : List String) (s : St σ) : St σ :=
  { s with g := names.foldl (fun g a => upd a g) s.g }

/-- The six attributes of `w` are those read from `func` where the read gave a value, and `helper`'s
own where it raised `AttributeError`. -/
def CopiedMeta (r : String → Res Val) (h0 w : FnAttrs Val) : Prop :=
  w.module = pick (r "__module__") h0.module ∧ w.name = pick (r "__name__") h0.name ∧
  w.qualname = pick (r "__qualname__") h0.qualname ∧ w.doc = pick (r "__doc__") h0.doc ∧
  w.annotate = pick (r "__annotate__") h0.annotate ∧
  w.typeParams = pick (r "__type_params__") h0.typeParams

/-- `@wraps(func)` on `helper`, for every `func` whose attribute reads give `r` and change only the
world, by `upd`, so that their order shows. `func = Placeholder` is refused by `partial` before
anything is read. Otherwise the reads go in the order of `WRAPPER_ASSIGNMENTS`, and:
- when each read gives a value its setter accepts or `AttributeError`, `helper` gets those values,
  keeps its own name, qualified name, module and empty docstring, annotations and type parameters
  where `AttributeError` was raised, gets the items of `func.__dict__` (none when that raises
  `AttributeError`), the last of a key winning, and `__wrapped__` is `func` whatever that dict held;
  the six attributes are not taken from the dict; a failure of `func.__dict__` or of iterating it
  propagates;
- the first read that is refused by its setter (a non-`str` `__name__` or `__qualname__`, an
  `__annotate__` that is neither callable nor `None`, a non-tuple `__type_params__`) stops it with
  that `TypeError`, chained to the exception being handled, and nothing after it is read; the first
  read that raises anything but `AttributeError` stops it with that exception. -/
def ContextmanagerWraps : Prop :=
  ∀ (σ Val D : Type) (k : ValOps Val) (fn : FuncView σ Val D) (self : Val) (isAsync : Bool)
    (handled : Option ExcId) (s : St σ) (upd : String → σ → σ) (r : String → Res Val),
    let run := contextmanagerDeco k fn self isAsync handled s
    let h0 := freshHelper k isAsync
    (k.isPlaceholder self = true →
      run = ((s.raiseNew clsType "Placeholder cannot be passed as a keyword argument" handled).1,
        .error (s.raiseNew clsType "Placeholder cannot be passed as a keyword argument" handled).2)) ∧
    (k.isPlaceholder self = false → (∀ a s', fn.read a s' = ({ s' with g := upd a s'.g }, r a)) →
      ((∀ a ∈ wrapperAssignments, Copyable k s.h a (r a)) →
        let s1 := afterReads upd wrapperAssignments s
        (∀ s2 d ps s3, fn.getDict s1 = (s2, .ok d) → fn.items d s2 = (s3, .ok ps) →
          ∃ w, run = (s3, .ok w) ∧ CopiedMeta r h0 w ∧
            ∀ key, w.dict.lookup key = if key = "__wrapped__" then some self else ps.reverse.lookup key) ∧
        (∀ s2 e, fn.getDict s1 = (s2, .error e) → s2.h.isInst e "AttributeError" = true →
          ∃ w, run = (s2, .ok w) ∧ CopiedMeta r h0 w ∧ w.dict = [("__wrapped__", self)]) ∧
        (∀ s2 e, fn.getDict s1 = (s2, .error e) → s2.h.isInst e "AttributeError" = false →
          run = (s2, .error e)) ∧
        (∀ s2 d s3 e, fn.getDict s1 = (s2, .ok d) → fn.items d s2 = (s3, .error e) →
          run = (s3, .error e))) ∧
      (∀ pre a post, wrapperAssignments = pre ++ a :: post → (∀ b ∈ pre, Copyable k s.h b (r b)) →
        let sa := afterReads upd (pre ++ [a]) s
        (∀ v msg, r a = .ok v → Refuses k a v msg →
          run = ((sa.raiseNew clsType msg handled).1, .error (sa.raiseNew clsType msg handled).2) ∧
          ∀ y, handled = some y → y < s.h.length →
            ((sa.raiseNew clsType msg handled).1.h.get (sa.raiseNew clsType msg handled).2).context =
              some y) ∧
        (∀ e, r a = .error e → s.h.isInst e "AttributeError" = false → run = (sa, .error e))))

/-! ### Proof -/

/-- The setters without their checks. -/
def FnAttrs.put (f : FnAttrs Val) (a : String) (v : Val) : FnAttrs Val :=
  if a = "__module__" then { f with module := v }
  else if a = "__name__" then { f with name := v }
  else if a = "__qualname__" then { f with qualname := v }
  else if a = "__doc__" then { f with doc := v }
  else if a = "__annotate__" then { f with annotate := v }
  else if a = "__type_params__" then { f with typeParams := v }
  else { f with dict := dictSet f.dict a v }

def FnAttrs.putR (f : FnAttrs Val) (a : String) (x : Res Val) : FnAttrs Val :=
  match x with
  | .ok v => f.put a v
  | .error _ => f

def copyAll (r : String → Res Val) : List String → FnAttrs Val → FnAttrs Val
  | [], f => f
  | a :: l, f => copyAll r l (f.putR a (r a))

theorem set_of_accepts (k : ValOps Val) (f : FnAttrs Val) (a : String) (v : Val)
    (h : Accepts k a v) : f.set k a v = .ok (f.put a v) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold FnAttrs.set FnAttrs.put
  by_cases e1 : a = "__module__"
  · simp [e1]
  by_cases e2 : a = "__name__"
  · subst e2; simp [h1 rfl]
  by_cases e3 : a = "__qualname__"
  · subst e3; simp [h2 rfl]
  by_cases e4 : a = "__doc__"
  · subst e4; simp
  by_cases e5 : a = "__annotate__"
  · subst e5
    rcases h3 rfl with h | h <;> simp [h]
  by_cases e6 : a = "__type_params__"
  · subst e6; simp [h4 rfl]
  simp [e1, e2, e3, e4, e5, e6]

theorem set_of_refuses (k : ValOps Val) (f : FnAttrs Val) (a : String) (v : Val) (msg : String)
    (h : Refuses k a v msg) : f.set k a v = .error msg := by
  rcases h with ⟨rfl, h1, rfl⟩ | ⟨rfl, h1, rfl⟩ | ⟨rfl, h1, h2, rfl⟩ | ⟨rfl, h1, rfl⟩ <;>
    simp [FnAttrs.set, *]

theorem assignAll_copy (k : ValOps Val) (fn : FuncView σ Val D) (handled : Option ExcId)
    (upd : String → σ → σ) (r : String → Res Val)
    (hread : ∀ a s', fn.read a s' = ({ s' with g := upd a s'.g }, r a)) :
    ∀ (pre rest : List String) (f : FnAttrs Val) (s : St σ), (∀ b ∈ pre, Copyable k s.h b (r b)) →
      assignAll k fn handled (pre ++ rest) f s =
        assignAll k fn handled rest (copyAll r pre f) (afterReads upd pre s) := by
  intro pre
  induction pre with
  | nil => intro rest f s _; rfl
  | cons b pre ih =>
    intro rest f s hc
    have hb := hc b (by simp)
    have hrest : ∀ b' ∈ pre, Copyable k ({ s with g := upd b s.g } : St σ).h b' (r b') :=
      fun b' hb' => hc b' (by simp [hb'])
    rcases hb with ⟨v, hv, hacc⟩ | ⟨e, he, hattr⟩
    · simp only [List.cons_append, assignAll, hread, hv, set_of_accepts k f b v hacc]
      rw [ih rest _ { s with g := upd b s.g } hrest]
      simp [copyAll, FnAttrs.putR, hv, afterReads]
    · simp only [List.cons_append, assignAll, hread, he, hattr, if_true]
      rw [ih rest _ { s with g := upd b s.g } hrest]
      simp [copyAll, FnAttrs.putR, he, afterReads]

theorem assignAll_nil (k : ValOps Val) (fn : FuncView σ Val D) (handled : Option ExcId)
    (f : FnAttrs Val) (s : St σ) : assignAll k fn handled [] f s = (s, .ok f) := rfl

theorem copyAll_meta (r : String → Res Val) (h0 : FnAttrs Val) :
    CopiedMeta r h0 (copyAll r wrapperAssignments h0) ∧
      (copyAll r wrapperAssignments h0).dict = h0.dict := by
  unfold CopiedMeta
  simp only [wrapperAssignments, copyAll, FnAttrs.putR]
  cases r "__module__" <;> cases r "__name__" <;> cases r "__qualname__" <;> cases r "__doc__" <;>
    cases r "__annotate__" <;> cases r "__type_params__" <;> simp [FnAttrs.put, pick]

theorem lookup_cons' (key pk : String) (pv : Val) (l : List (String × Val)) :
    ((pk, pv) :: l).lookup key = if key = pk then some pv else l.lookup key := by
  by_cases h : key = pk
  · subst h; simp [List.lookup]
  · have hb : (key == pk) = false := by simpa using h
    simp [List.lookup, hb, h]

theorem lookup_append_or (l1 l2 : List (String × Val)) (key : String) :
    (l1 ++ l2).lookup key = (l1.lookup key).or (l2.lookup key) := by
  induction l1 with
  | nil => simp [List.lookup]
  | cons p l ih =>
    obtain ⟨pk, pv⟩ := p
    rw [List.cons_append, lookup_cons', lookup_cons', ih]
    by_cases h : key = pk <;> simp [h]

theorem lookup_map_set (d : List (String × Val)) (k key : String) (v : Val) :
    (d.map (fun p => if p.1 == k then (k, v) else p)).lookup key =
      if key = k then (if d.any (fun p => p.1 == k) then some v else none) else d.lookup key := by
  induction d with
  | nil => simp [List.lookup]
  | cons p l ih =>
    obtain ⟨pk, pv⟩ := p
    have hm : (if ((pk, pv).1 == k) = true then (k, v) else (pk, pv)) =
        if pk = k then (k, v) else (pk, pv) := by simp
    rw [List.map_cons, hm, List.any_cons]
    by_cases hp : pk = k
    · subst hp
      rw [if_pos rfl, lookup_cons', lookup_cons', ih]
      by_cases hk : key = pk <;> simp [hk]
    · have hb : (pk == k) = false := by simpa using hp
      rw [if_neg hp, lookup_cons', lookup_cons', ih, hb, Bool.false_or]
      by_cases hk : key = pk
      · subst hk; simp [hp]
      · simp [hk]

theorem lookup_none_of_any (d : List (String × Val)) (k : String)
    (h : ¬ (d.any (fun p => p.1 == k)) = true) : d.lookup k = none := by
  induction d with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨pk, pv⟩ := p
    simp only [List.any_cons, Bool.or_eq_true, beq_iff_eq, not_or] at h
    have hne : ¬ k = pk := fun e => h.1 e.symm
    rw [lookup_cons', if_neg hne, ih h.2]

theorem lookup_dictSet (d : List (String × Val)) (k key : String) (v : Val) :
    (dictSet d k v).lookup key = if key = k then some v else d.lookup key := by
  unfold dictSet
  split
  · rename_i hany
    rw [lookup_map_set]
    simp [hany]
  · rename_i hany
    rw [lookup_append_or, lookup_cons']
    by_cases hk : key = k
    · subst hk
      simp [List.lookup, lookup_none_of_any d key hany]
    · simp [List.lookup, hk]

theorem lookup_foldl (ps d : List (String × Val)) (key : String) :
    (ps.foldl (fun d (p : String × Val) => dictSet d p.1 p.2) d).lookup key =
      (ps.reverse.lookup key).or (d.lookup key) := by
  induction ps generalizing d with
  | nil => simp
  | cons p ps ih =>
    rw [List.foldl_cons, ih, lookup_dictSet, List.reverse_cons, lookup_append_or]
    obtain ⟨pk, pv⟩ := p
    rw [lookup_cons']
    by_cases h : key = pk
    · cases ps.reverse.lookup key <;> simp [List.lookup, h]
    · cases ps.reverse.lookup key <;> simp [List.lookup, h]

/-- An exception raised while `y`, an existing exception, is handled has `y` as `__context__`. -/
theorem raiseNew_context (s : St σ) (c : Cls) (msg : String) (y : ExcId) (hy : y < s.h.length) :
    ((s.raiseNew c msg (some y)).1.h.get (s.raiseNew c msg (some y)).2).context = some y := by
  simp only [St.raiseNew]
  apply raiseCtx_context
  · simp [Heap.alloc]
  · simp only [Heap.alloc]; exact Nat.ne_of_lt hy

theorem afterReads_snoc (upd : String → σ → σ) (pre : List String) (a : String) (s : St σ) :
    afterReads upd (pre ++ [a]) s =
      { afterReads upd pre s with g := upd a (afterReads upd pre s).g } := by
  simp [afterReads, List.foldl_append]

theorem contextmanagerWraps_proven : ContextmanagerWraps := by
  intro σ Val D k fn self isAsync handled s upd r run h0
  refine ⟨?_, ?_⟩
  · intro hp
    simp [run, contextmanagerDeco, hp]
  intro hp hread
  have hrun : run = updateWrapper k fn self handled h0 s := by
    simp [run, h0, contextmanagerDeco, hp]
  rw [hrun]
  obtain ⟨hmeta, hdict⟩ := copyAll_meta r h0
  have hd0 : h0.dict = [] := rfl
  refine ⟨?_, ?_⟩
  · intro hall
    have ha := assignAll_copy k fn handled upd r hread wrapperAssignments [] h0 s hall
    rw [List.append_nil, assignAll_nil] at ha
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro s2 d ps s3 hg hi
      refine ⟨{ copyAll r wrapperAssignments h0 with
        dict := dictSet (ps.foldl (fun d (p : String × Val) => dictSet d p.1 p.2) (copyAll r wrapperAssignments h0).dict)
          "__wrapped__" self }, ?_, hmeta, ?_⟩
      · simp only [updateWrapper, ha, hg, hi]
      · intro key
        rw [lookup_dictSet, lookup_foldl, hdict, hd0]
        by_cases hk : key = "__wrapped__"
        · simp [hk]
        · cases ps.reverse.lookup key <;> simp [hk, List.lookup]
    · intro s2 e hg he
      refine ⟨{ copyAll r wrapperAssignments h0 with dict := [("__wrapped__", self)] }, ?_, hmeta, rfl⟩
      simp only [updateWrapper, ha, hg, he, if_true, List.foldl_nil, hdict, hd0]
      rfl
    · intro s2 e hg he
      simp only [updateWrapper, ha, hg, he, Bool.false_eq_true, if_false]
    · intro s2 d s3 e hg hi
      simp only [updateWrapper, ha, hg, hi]
  · intro pre a post hsplit hpre
    have ha := assignAll_copy k fn handled upd r hread pre (a :: post) h0 s hpre
    have hsa := afterReads_snoc upd pre a s
    have hh : (afterReads upd pre s).h = s.h := rfl
    refine ⟨?_, ?_⟩
    · intro v msg hv hm
      have hset := set_of_refuses k (copyAll r pre h0) a v msg hm
      refine ⟨?_, ?_⟩
      · simp only [updateWrapper]
        rw [hsplit, ha]
        simp only [assignAll, hread, hv, hset, hsa]
      · intro y hy hyl
        subst hy
        exact raiseNew_context _ clsType msg y hyl
    · intro e he hattr
      simp only [updateWrapper]
      rw [hsplit, ha]
      simp only [assignAll, hread, he, hsa, hh, hattr, Bool.false_eq_true, if_false]

end PyLean.CoreLibs.Misc.Contextlib
