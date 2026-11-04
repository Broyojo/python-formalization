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

/-- Reading the attributes `names` of `func` in order from `s`, each read in the world the read
before it left, gets past every one and ends in `s'`: each result is `Copyable`, judged in the heap
that read returned, so an `AttributeError` the read itself allocated (the ordinary missing
attribute) counts. -/
def PassesReads (k : ValOps Val) (fn : FuncView σ Val D) : List String → St σ → St σ → Prop
  | [], s, s' => s' = s
  | a :: l, s, s' =>
    Copyable k (fn.read a s).1.h a (fn.read a s).2 ∧ PassesReads k fn l (fn.read a s).1 s'

/-- The six attributes of `w` are those read from `func` (`r1`, ..., `r6` for `__module__`, ...,
`__type_params__`) where the read gave a value, and `helper`'s own where it raised
`AttributeError`. -/
def CopiedMeta (r1 r2 r3 r4 r5 r6 : Res Val) (h0 w : FnAttrs Val) : Prop :=
  w.module = pick r1 h0.module ∧ w.name = pick r2 h0.name ∧ w.qualname = pick r3 h0.qualname ∧
  w.doc = pick r4 h0.doc ∧ w.annotate = pick r5 h0.annotate ∧ w.typeParams = pick r6 h0.typeParams

/-- `@wraps(func)` on `helper`, for every `func` and every behaviour of its attribute reads: each
`getattr(func, attr)` may run any code, change the world, allocate (a missing attribute raises a new
`AttributeError`) and raise. `func = Placeholder` is refused by `partial` before anything is read.
Otherwise the reads go in the order of `WRAPPER_ASSIGNMENTS`, each in the world the one before left
(`s1`, ..., `s6`), and:
- when each read gives a value its setter accepts or an `AttributeError` (judged in the heap that
  read returned), `helper` gets those values, keeps its own name, qualified name, module and empty
  docstring, annotations and type parameters where `AttributeError` was raised, gets the items of
  `func.__dict__` (none when that raises `AttributeError`), the last of a key winning, and
  `__wrapped__` is `func` whatever that dict held; the six attributes are not taken from the dict;
  a failure of `func.__dict__` or of iterating it propagates;
- the first read that is refused by its setter (a non-`str` `__name__` or `__qualname__`, an
  `__annotate__` that is neither callable nor `None`, a non-tuple `__type_params__`) stops it with
  that `TypeError`, raised in the world that read left and chained to the exception being handled
  (which exists in that heap: type invariant), and nothing after it is read; the first read that
  raises anything but `AttributeError` stops it with that exception, in the world it left. -/
def ContextmanagerWraps : Prop :=
  ∀ (σ Val D : Type) (k : ValOps Val) (fn : FuncView σ Val D) (self : Val) (isAsync : Bool)
    (handled : Option ExcId) (s : St σ),
    let run := contextmanagerDeco k fn self isAsync handled s
    let h0 := freshHelper k isAsync
    (k.isPlaceholder self = true →
      run = ((s.raiseNew clsType "Placeholder cannot be passed as a keyword argument" handled).1,
        .error (s.raiseNew clsType "Placeholder cannot be passed as a keyword argument" handled).2)) ∧
    (k.isPlaceholder self = false →
      (∀ (s1 s2 s3 s4 s5 s6 : St σ) (r1 r2 r3 r4 r5 r6 : Res Val),
        fn.read "__module__" s = (s1, r1) → fn.read "__name__" s1 = (s2, r2) →
        fn.read "__qualname__" s2 = (s3, r3) → fn.read "__doc__" s3 = (s4, r4) →
        fn.read "__annotate__" s4 = (s5, r5) → fn.read "__type_params__" s5 = (s6, r6) →
        Copyable k s1.h "__module__" r1 → Copyable k s2.h "__name__" r2 →
        Copyable k s3.h "__qualname__" r3 → Copyable k s4.h "__doc__" r4 →
        Copyable k s5.h "__annotate__" r5 → Copyable k s6.h "__type_params__" r6 →
        (∀ s7 d ps s8, fn.getDict s6 = (s7, .ok d) → fn.items d s7 = (s8, .ok ps) →
          ∃ w, run = (s8, .ok w) ∧ CopiedMeta r1 r2 r3 r4 r5 r6 h0 w ∧
            ∀ key, w.dict.lookup key = if key = "__wrapped__" then some self else ps.reverse.lookup key) ∧
        (∀ s7 e, fn.getDict s6 = (s7, .error e) → s7.h.isInst e "AttributeError" = true →
          ∃ w, run = (s7, .ok w) ∧ CopiedMeta r1 r2 r3 r4 r5 r6 h0 w ∧ w.dict = [("__wrapped__", self)]) ∧
        (∀ s7 e, fn.getDict s6 = (s7, .error e) → s7.h.isInst e "AttributeError" = false →
          run = (s7, .error e)) ∧
        (∀ s7 d s8 e, fn.getDict s6 = (s7, .ok d) → fn.items d s7 = (s8, .error e) →
          run = (s8, .error e))) ∧
      (∀ pre a post s0, wrapperAssignments = pre ++ a :: post → PassesReads k fn pre s s0 →
        (∀ sa v msg, fn.read a s0 = (sa, .ok v) → Refuses k a v msg →
          run = ((sa.raiseNew clsType msg handled).1, .error (sa.raiseNew clsType msg handled).2) ∧
          ∀ y, handled = some y → y < sa.h.length →
            ((sa.raiseNew clsType msg handled).1.h.get (sa.raiseNew clsType msg handled).2).context =
              some y) ∧
        (∀ sa e, fn.read a s0 = (sa, .error e) → sa.h.isInst e "AttributeError" = false →
          run = (sa, .error e))))

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

theorem assignAll_step (k : ValOps Val) (fn : FuncView σ Val D) (handled : Option ExcId)
    (a : String) (rest : List String) (f : FnAttrs Val) (s s1 : St σ) (x : Res Val)
    (hr : fn.read a s = (s1, x)) (hc : Copyable k s1.h a x) :
    assignAll k fn handled (a :: rest) f s = assignAll k fn handled rest (f.putR a x) s1 := by
  rcases hc with ⟨v, rfl, hacc⟩ | ⟨e, rfl, hattr⟩
  · simp only [assignAll, hr, set_of_accepts k f a v hacc, FnAttrs.putR]
  · simp only [assignAll, hr, hattr, if_true, FnAttrs.putR]

theorem assignAll_passes (k : ValOps Val) (fn : FuncView σ Val D) (handled : Option ExcId) :
    ∀ (pre rest : List String) (f : FnAttrs Val) (s s' : St σ), PassesReads k fn pre s s' →
      ∃ f', assignAll k fn handled (pre ++ rest) f s = assignAll k fn handled rest f' s' := by
  intro pre
  induction pre with
  | nil =>
    intro rest f s s' hp
    simp only [PassesReads] at hp
    subst hp
    exact ⟨f, rfl⟩
  | cons b pre ih =>
    intro rest f s s' hp
    simp only [PassesReads] at hp
    obtain ⟨hc, hp⟩ := hp
    rw [List.cons_append, assignAll_step k fn handled b (pre ++ rest) f s _ _ rfl hc]
    exact ih rest _ _ s' hp

theorem putR6_meta (h0 : FnAttrs Val) (r1 r2 r3 r4 r5 r6 : Res Val) :
    CopiedMeta r1 r2 r3 r4 r5 r6 h0 ((((((h0.putR "__module__" r1).putR "__name__" r2).putR
      "__qualname__" r3).putR "__doc__" r4).putR "__annotate__" r5).putR "__type_params__" r6) ∧
    ((((((h0.putR "__module__" r1).putR "__name__" r2).putR "__qualname__" r3).putR "__doc__" r4).putR
      "__annotate__" r5).putR "__type_params__" r6).dict = h0.dict := by
  unfold CopiedMeta
  cases r1 <;> cases r2 <;> cases r3 <;> cases r4 <;> cases r5 <;> cases r6 <;>
    simp [FnAttrs.putR, FnAttrs.put, pick]

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

theorem contextmanagerWraps_proven : ContextmanagerWraps := by
  intro σ Val D k fn self isAsync handled s run h0
  refine ⟨?_, ?_⟩
  · intro hp
    simp [run, contextmanagerDeco, hp]
  intro hp
  have hrun : run = updateWrapper k fn self handled h0 s := by
    simp [run, h0, contextmanagerDeco, hp]
  rw [hrun]
  have hd0 : h0.dict = [] := rfl
  refine ⟨?_, ?_⟩
  · intro s1 s2 s3 s4 s5 s6 r1 r2 r3 r4 r5 r6 e1 e2 e3 e4 e5 e6 c1 c2 c3 c4 c5 c6
    obtain ⟨hmeta, hdict⟩ := putR6_meta h0 r1 r2 r3 r4 r5 r6
    have ha : assignAll k fn handled wrapperAssignments h0 s = (s6, .ok ((((((h0.putR "__module__" r1).putR
        "__name__" r2).putR "__qualname__" r3).putR "__doc__" r4).putR "__annotate__" r5).putR
        "__type_params__" r6)) := by
      simp only [wrapperAssignments]
      rw [assignAll_step k fn handled _ _ _ _ _ _ e1 c1, assignAll_step k fn handled _ _ _ _ _ _ e2 c2,
        assignAll_step k fn handled _ _ _ _ _ _ e3 c3, assignAll_step k fn handled _ _ _ _ _ _ e4 c4,
        assignAll_step k fn handled _ _ _ _ _ _ e5 c5, assignAll_step k fn handled _ _ _ _ _ _ e6 c6]
      rfl
    generalize ((((((h0.putR "__module__" r1).putR "__name__" r2).putR "__qualname__" r3).putR
      "__doc__" r4).putR "__annotate__" r5).putR "__type_params__" r6) = w0 at ha hmeta hdict
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro s7 d ps s8 hg hi
      refine ⟨{ w0 with
        dict := dictSet (ps.foldl (fun d (p : String × Val) => dictSet d p.1 p.2) w0.dict)
          "__wrapped__" self }, ?_, hmeta, ?_⟩
      · simp only [updateWrapper, ha, hg, hi]
      · intro key
        rw [lookup_dictSet, lookup_foldl, hdict, hd0]
        by_cases hk : key = "__wrapped__"
        · simp [hk]
        · cases ps.reverse.lookup key <;> simp [hk, List.lookup]
    · intro s7 e hg he
      refine ⟨{ w0 with dict := [("__wrapped__", self)] }, ?_, hmeta, rfl⟩
      simp only [updateWrapper, ha, hg, he, if_true, List.foldl_nil, hdict, hd0]
      rfl
    · intro s7 e hg he
      simp only [updateWrapper, ha, hg, he, Bool.false_eq_true, if_false]
    · intro s7 d s8 e hg hi
      simp only [updateWrapper, ha, hg, hi]
  · intro pre a post s0 hsplit hpre
    obtain ⟨f', ha⟩ := assignAll_passes k fn handled pre (a :: post) h0 s s0 hpre
    refine ⟨?_, ?_⟩
    · intro sa v msg hv hm
      have hset := set_of_refuses k f' a v msg hm
      refine ⟨?_, ?_⟩
      · simp only [updateWrapper]
        rw [hsplit, ha]
        simp only [assignAll, hv, hset]
      · intro y hy hyl
        subst hy
        exact raiseNew_context _ clsType msg y hyl
    · intro sa e he hattr
      simp only [updateWrapper]
      rw [hsplit, ha]
      simp only [assignAll, he, hattr, Bool.false_eq_true, if_false]

end PyLean.CoreLibs.Misc.Contextlib
