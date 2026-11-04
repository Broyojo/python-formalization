import PyLean.CoreLibs.Misc.Weakref.PropsDict

/-! Properties of `WeakMethod` (Lib/weakref.py:38-89) and `finalize` (:442-576). -/

namespace PyLean.CoreLibs.Misc.Weakref

open PyLean

/-! ### `WeakMethod` -/

/-- `WeakMethod(meth)`: an `AttributeError` from `meth.__self__` or `meth.__func__` becomes the
`TypeError` naming `type(meth)`, any other exception passes through, and an object or function that
cannot be weakly referenced raises `ref()`'s `TypeError` (the object first). Otherwise both are
held. `__call__` rebuilds the bound method while both referents live and gives `None` otherwise. -/
def WeakMethodNew : Prop :=
  ∀ (i : Nat) (meth : Meth) (cb : Bool) (w : World) (m : WM) (n : Int) (e : PyExc) (ob f : Nat),
    (meth.self = .error e → WM.new i meth cb = .error
      (if isAttrErr e then .typeError s!"argument should be a bound method, not {meth.tp}" else e)) ∧
    (meth.self = .ok (.obj ob) → meth.func = .error e → WM.new i meth cb = .error
      (if isAttrErr e then .typeError s!"argument should be a bound method, not {meth.tp}" else e)) ∧
    (meth.self = .ok (.int n) → (∃ x, meth.func = .ok x) →
      WM.new i meth cb = .error (.typeError "cannot create weak reference to 'int' object")) ∧
    (meth.self = .ok (.obj ob) → meth.func = .ok (.int n) →
      WM.new i meth cb = .error (.typeError "cannot create weak reference to 'int' object")) ∧
    (meth.self = .ok (.obj ob) → meth.func = .ok (.obj f) →
      WM.new i meth cb = .ok { id := i, obj := ob, func := f, alive := true, callback := cb }) ∧
    (alive w m.obj = true → alive w m.func = true → m.call w = some (m.obj, m.func)) ∧
    (alive w m.obj = false → m.call w = none) ∧
    (alive w m.func = false → m.call w = none)

theorem weakMethodNew_proven : WeakMethodNew := by
  intro i meth cb w m n e ob f
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; simp [WM.new, h]
  · intro h1 h2; simp [WM.new, h1, h2, refOf]
  · intro h1 h2
    obtain ⟨x, hx⟩ := h2
    simp [WM.new, h1, hx, refOf]
  · intro h1 h2; simp [WM.new, h1, h2, refOf]
  · intro h1 h2; simp [WM.new, h1, h2, refOf]
  · intro h1 h2; simp [WM.call, h1, h2]
  · intro h; simp [WM.call, h]
  · intro h; simp [WM.call, h]

/-- The callback of a `WeakMethod` runs at most once: the first death of the object or the function
clears `_alive` and fires it if there is one, and later deaths do nothing. The death of anything else
changes nothing. -/
def WeakMethodCallbackOnce : Prop :=
  ∀ (m : WM) (o o' : Nat),
    (m.alive = true → (m.obj = o ∨ m.func = o) →
      m.onDeath o = ({ m with alive := false }, m.callback)) ∧
    (m.alive = false → m.onDeath o = (m, false)) ∧
    (m.obj ≠ o → m.func ≠ o → m.onDeath o = (m, false)) ∧
    ((m.onDeath o).1.alive = false → ((m.onDeath o).1.onDeath o').2 = false)

theorem weakMethodCallbackOnce_proven : WeakMethodCallbackOnce := by
  intro m o o'
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h1 h2
    have : (m.obj == o || m.func == o) = true := by
      rcases h2 with h | h <;> simp [h]
    simp [WM.onDeath, h1, this]
  · intro h; simp [WM.onDeath, h]
  · intro h1 h2
    simp [WM.onDeath, h1, h2]
  · intro h
    have key : ∀ m' : WM, m'.alive = false → (m'.onDeath o').2 = false := by
      intro m' h'
      simp [WM.onDeath, h']
    exact key _ h

/-- `x.__eq__` and `x.__ne__` on two live weak methods return the referents' own results, not a
`bool`: a false result of comparing the objects is returned as it is, and an exception from the
comparison or from its truth test passes through; a true one hands over to the functions. Against a
dead one, either method answers by identity, and against anything but a `WeakMethod` it is
`NotImplemented`. `__ne__` calls the objects' `__ne__`: a true result of it is the answer whatever
`__eq__` says. When the referents' `__ne__` is the default one (the negated truth of `__eq__`),
`__ne__` is the negated truth of `__eq__`. -/
def WeakMethodCompare : Prop :=
  ∀ (R : Type) (c : RCmp R) (w : World) (m o : WM),
    m.eq c w none = none ∧ m.ne c w none = none ∧
    (m.alive = false → m.eq c w (some o) = some (.ok (c.ofBool (m.id == o.id))) ∧
      m.ne c w (some o) = some (.ok (c.ofBool (m.id != o.id)))) ∧
    (m.alive = true → o.alive = true → alive w m.obj = true → alive w o.obj = true →
      (∀ e, c.eq m.obj o.obj = .error e → m.eq c w (some o) = some (.error e)) ∧
      (∀ x e, c.eq m.obj o.obj = .ok x → c.truth x = .error e → m.eq c w (some o) = some (.error e)) ∧
      (∀ x, c.eq m.obj o.obj = .ok x → c.truth x = .ok false → m.eq c w (some o) = some (.ok x)) ∧
      (∀ x, c.eq m.obj o.obj = .ok x → c.truth x = .ok true →
        alive w m.func = true → alive w o.func = true → m.eq c w (some o) = some (c.eq m.func o.func)) ∧
      (∀ x, c.ne m.obj o.obj = .ok x → c.truth x = .ok true → m.ne c w (some o) = some (.ok x))) ∧
    ((∀ a b, c.ne a b = match c.eq a b with
        | .error e => .error e
        | .ok x =>
          match c.truth x with
          | .error e => .error e
          | .ok t => .ok (c.ofBool (!t))) →
      (∀ t, c.truth (c.ofBool t) = .ok t) →
      m.ne c w (some o) = (m.eq c w (some o)).map (fun r =>
        match r with
        | .error e => .error e
        | .ok x =>
          match c.truth x with
          | .error e => .error e
          | .ok t => .ok (c.ofBool (!t))))

theorem weakMethodCompare_proven : WeakMethodCompare := by
  intro R c w m o
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · intro h
    simp [WM.eq, WM.ne, h]
  · intro h1 h2 h3 h4
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro e he; simp [WM.eq, h1, h2, refCmp, h3, h4, he]
    · intro x e hx ht; simp [WM.eq, h1, h2, refCmp, h3, h4, hx, ht]
    · intro x hx ht; simp [WM.eq, h1, h2, refCmp, h3, h4, hx, ht]
    · intro x hx ht h5 h6; simp [WM.eq, h1, h2, refCmp, h3, h4, hx, ht, h5, h6]
    · intro x hx ht; simp [WM.ne, h1, h2, refCmp, h3, h4, hx, ht]
  · intro hne ht
    have hcmp : ∀ x a y b, refCmp c c.ne true w x a y b =
        match refCmp c c.eq false w x a y b with
        | .error e => .error e
        | .ok r =>
          match c.truth r with
          | .error e => .error e
          | .ok t => .ok (c.ofBool (!t)) := by
      intro x a y b
      simp only [refCmp]
      split
      · exact hne a b
      · simp [ht, bne]
    simp only [WM.eq, WM.ne]
    split
    · simp [ht, bne]
    · simp only [Option.map_some, hcmp m.id m.obj o.id o.obj]
      cases hrc : refCmp c c.eq false w m.id m.obj o.id o.obj with
      | error e => rfl
      | ok x =>
        cases htx : c.truth x with
        | error e => simp [htx]
        | ok t =>
          cases t with
          | false => simp [htx, ht]
          | true => simp [htx, ht, hcmp m.id m.func o.id o.func]

/-! ### `finalize` -/

namespace Fin

variable {F σ : Type}

/-- `finalize`: "The first time the finalizer is called it evaluates func ... After this the finalizer
is dead, and calling it just returns None." `detach` kills it and returns the object and function
while the object lives; `peek` returns them and leaves it alive. Once `_shutdown` is set, a call pops
the entry without running it. -/
def FinalizeOnce : Prop :=
  ∀ (F : Type) (st : Fin F) (w : World) (self : Nat) (info : Info F),
    (st.registry.map (·.1)).Nodup →
    dGet st.registry self = some info →
    (st.shutdown = false → (st.call self).2 = some info.func) ∧
    (st.shutdown = true → (st.call self).2 = none) ∧
    ((st.call self).1.call self).2 = none ∧
    (st.call self).1.isAlive self = false ∧
    st.isAlive self = true ∧
    (alive w info.obj = true →
      st.peek w self = some (.obj info.obj, info.func) ∧
      (st.detach w self).2 = some (.obj info.obj, info.func) ∧
      (st.detach w self).1.isAlive self = false) ∧
    (alive w info.obj = false → st.peek w self = none ∧ st.detach w self = (st, none))

theorem finalizeOnce_proven : FinalizeOnce := by
  intro F st w self info hk hg
  have hdel : dGet (dDel st.registry self) self = none := by
    have := dGet_dDel (K := Nat) (β := Info F) hk self self
    simpa using this
  have hc : (st.call self).1 = { st with registry := dDel st.registry self } := by
    simp only [call, hg]
    cases st.shutdown <;> rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; simp [call, hg, h]
  · intro h; simp [call, hg, h]
  · rw [hc]; simp [call, hdel]
  · rw [hc]; simp [isAlive, hdel]
  · simp [isAlive, hg]
  · intro h
    have hd : deref w info.obj = some (.obj info.obj) := by simp [deref, h]
    refine ⟨by simp [peek, hg, hd], by simp [detach, hg, hd], ?_⟩
    simp [detach, hg, hd, isAlive, hdel]
  · intro h
    have hd : deref w info.obj = none := by simp [deref, h]
    exact ⟨by simp [peek, hg, hd], by simp [detach, hg, hd]⟩

/-- The `atexit` property. The getter is `False` for a dead finalizer and the flag otherwise. The
setter evaluates `bool(value)` only for a live finalizer: there an exception from `__bool__` passes
through and changes nothing, and a result sets the flag of this finalizer alone; for a dead one
nothing is evaluated and nothing changes. -/
def FinalizeAtexit : Prop :=
  ∀ (F : Type) (st : Fin F) (self g : Nat) (info : Info F) (e : PyExc) (b : Bool),
    (st.registry.map (·.1)).Nodup →
    (dGet st.registry self = none → st.atexit self = false ∧ st.setAtexit self (.error e) = .ok st) ∧
    (dGet st.registry self = some info →
      st.atexit self = info.atexit ∧
      st.setAtexit self (.error e) = .error e ∧
      ∃ st', st.setAtexit self (.ok b) = .ok st' ∧ st'.atexit self = b ∧
        (g ≠ self → dGet st'.registry g = dGet st.registry g))

theorem finalizeAtexit_proven : FinalizeAtexit := by
  intro F st self g info e b _
  constructor
  · intro h
    exact ⟨by simp [atexit, h], by simp [setAtexit, h]⟩
  · intro h
    refine ⟨by simp [atexit, h], by simp [setAtexit, h], ?_⟩
    refine ⟨{ st with registry := dSet st.registry self { info with atexit := b } },
      by simp [setAtexit, h], by simp [atexit, dGet_dSet], ?_⟩
    intro hg
    simp [dGet_dSet, Ne.symm hg]

/-- `finalize.__init__` registers the `_Info` of the object and function, with `atexit` true ("By
default atexit is true") and the next index, leaves the other finalizers, and marks the registry
dirty. A target that cannot be weakly referenced raises `TypeError` and registers nothing, but the
`atexit` hook is registered already. `__repr__` names the class of the finalizer (a subclass its
own), and the object's type name as `%r` quotes it while the object lives; it says `dead` for an
unregistered finalizer and for a registered one whose object died. -/
def FinalizeInit : Prop :=
  ∀ (F : Type) (st : Fin F) (w : World) (self o g : Nat) (n : Int) (f : F) (info : Info F)
    (cls a b t : String),
    (st.init self (.obj o) f).2 = .ok () ∧
    dGet (st.init self (.obj o) f).1.registry self =
      some { obj := o, func := f, atexit := true, index := st.indexIter } ∧
    (g ≠ self → dGet (st.init self (.obj o) f).1.registry g = dGet st.registry g) ∧
    (st.init self (.obj o) f).1.dirty = true ∧
    (st.init self (.obj o) f).1.indexIter = st.indexIter + 1 ∧
    (st.init self (.int n) f).2 = .error (.typeError "cannot create weak reference to 'int' object") ∧
    (st.init self (.int n) f).1.registry = st.registry ∧
    (st.init self (.int n) f).1.registeredWithAtexit = true ∧
    (dGet st.registry self = none → st.repr w self cls a b t = s!"<{cls} object at {a}; dead>") ∧
    (dGet st.registry self = some info → alive w info.obj = false →
      st.repr w self cls a b t = s!"<{cls} object at {a}; dead>") ∧
    (dGet st.registry self = some info → alive w info.obj = true →
      st.repr w self cls a b t = s!"<{cls} object at {a}; for {strRepr t} at {b}>")

theorem finalizeInit_proven : FinalizeInit := by
  intro F st w self o g n f info cls a b t
  refine ⟨rfl, ?_, ?_, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [init, refOf, dGet_dSet]
  · intro hg
    simp [init, refOf, dGet_dSet, Ne.symm hg]
  · intro h; simp [repr, h]
  · intro h1 h2; simp [repr, h1, deref, h2]
  · intro h1 h2; simp [repr, h1, deref, h2]

theorem sorted_insert (kv : Nat × Info F) :
    ∀ l : List (Nat × Info F), l.Pairwise (fun a b => a.2.index ≤ b.2.index) →
      (insertByIndex kv l).Pairwise (fun a b => a.2.index ≤ b.2.index) := by
  intro l
  induction l with
  | nil => intro _; simp [insertByIndex]
  | cons x rest ih =>
    intro h
    obtain ⟨h1, h2⟩ := List.pairwise_cons.1 h
    simp only [insertByIndex]
    split
    · rename_i hlt
      refine List.pairwise_cons.2 ⟨?_, h⟩
      intro b hb
      rcases List.mem_cons.1 hb with rfl | hb
      · omega
      · have := h1 b hb
        omega
    · rename_i hge
      refine List.pairwise_cons.2 ⟨?_, ih h2⟩
      have hmem : ∀ b ∈ insertByIndex kv rest, b = kv ∨ b ∈ rest := by
        clear ih h h1 h2
        induction rest with
        | nil => simp [insertByIndex]
        | cons y r ihr =>
          intro b hb
          simp only [insertByIndex] at hb
          split at hb
          · rcases List.mem_cons.1 hb with e | hb
            · exact .inl e
            · exact .inr hb
          · rcases List.mem_cons.1 hb with e | hb
            · exact .inr (by simp [e])
            · rcases ihr b hb with e | e
              · exact .inl e
              · exact .inr (by simp [e])
      intro b hb
      rcases hmem b hb with rfl | e
      · omega
      · exact h1 b e

theorem insert_perm (kv : Nat × Info F) (l : List (Nat × Info F)) :
    (insertByIndex kv l).Perm (kv :: l) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons x rest ih =>
    simp only [insertByIndex]
    split
    · exact List.Perm.refl _
    · exact (ih.cons x).trans (List.Perm.swap _ _ _)

/-- `_select_for_exit` lists the live finalizers marked for exit, "oldest first": a permutation of
those whose `atexit` is true, by ascending creation index. -/
def SelectForExit : Prop :=
  ∀ (F : Type) (st : Fin F),
    let l := (st.registry.filter (fun kv => kv.2.atexit)).foldr insertByIndex []
    selectForExit st = l.map (·.1) ∧ l.Perm (st.registry.filter (fun kv => kv.2.atexit)) ∧
    l.Pairwise (fun a b => a.2.index ≤ b.2.index)

theorem selectForExit_proven : SelectForExit := by
  intro F st
  refine ⟨rfl, ?_, ?_⟩
  · generalize st.registry.filter (fun kv => kv.2.atexit) = r
    induction r with
    | nil => exact List.Perm.refl _
    | cons x rest ih =>
      simp only [List.foldr_cons]
      exact (insert_perm x _).trans (ih.cons x)
  · generalize st.registry.filter (fun kv => kv.2.atexit) = r
    induction r with
    | nil => simp
    | cons x rest ih =>
      simp only [List.foldr_cons]
      exact sorted_insert x _ ih

/-- A `run` that records the function and the `gc` flag it sees, and neither touches the class
state nor fails. -/
structure PlainRun (run : RunF σ F) (log : σ → List (F × Bool)) : Prop where
  same : ∀ f st s, (run f st s).1 = st
  ok : ∀ f st s, (run f st s).2.2 = none
  logs : ∀ f st s, log (run f st s).2.1 = log s ++ [(f, st.gc)]

/-- `_exitfunc`: "any remaining finalizers for which the atexit attribute is true will be run in
reverse order of creation". With functions that do not fail or create finalizers, it runs each one
selected exactly once, newest first, with `gc` disabled, and then sets `_shutdown` and leaves `gc`
as it found it. The registry may be dirty, as `__init__` always leaves it. -/
def ExitfuncOrder : Prop :=
  ∀ (F σ : Type) (run : RunF σ F) (hook : σ → PyExc → σ × Option PyExc) (log : σ → List (F × Bool))
    (st : Fin F) (s : σ),
    PlainRun run log → st.shutdown = false → st.registry ≠ [] → (st.registry.map (·.1)).Nodup →
    let sel := selectForExit st
    let r := exitfunc run hook (sel.length + 1) st s
    r.2.2 = none ∧
    log r.2.1 = log s ++ (sel.reverse.filterMap (fun f => (dGet st.registry f).map (·.func, false))) ∧
    r.1.shutdown = true ∧ r.1.gc = st.gc

theorem dDel_nodup (l : List (Nat × Info F)) (f : Nat) (h : (l.map (·.1)).Nodup) :
    ((dDel l f).map (·.1)).Nodup := Keys_dDel h f

theorem exit_loop_order (run : RunF σ F) (hook : σ → PyExc → σ × Option PyExc)
    (log : σ → List (F × Bool)) (hr : PlainRun run log) :
    ∀ (n : Nat) (pending : List Nat) (st : Fin F) (s : σ), pending.length = n →
      st.dirty = false → st.shutdown = false → pending.Nodup →
      (st.registry.map (·.1)).Nodup →
      (exitLoop run hook (n + 1) st s (some pending)).2.2 = none ∧
      (exitLoop run hook (n + 1) st s (some pending)).1.gc = st.gc ∧
      log (exitLoop run hook (n + 1) st s (some pending)).2.1 = log s ++
        (pending.reverse.filterMap (fun f => (dGet st.registry f).map (·.func, st.gc))) := by
  intro n
  induction n with
  | zero =>
    intro pending st s hn hd _ _ _
    have : pending = [] := List.length_eq_zero_iff.1 hn
    subst this
    simp [exitLoop, hd]
  | succ n ih =>
    intro pending st s hn hd hsh hnd hk
    have hne : pending ≠ [] := by
      intro e
      simp [e] at hn
    obtain ⟨init, f, hp⟩ : ∃ init f, pending = init ++ [f] :=
      ⟨pending.dropLast, pending.getLast hne, (List.dropLast_concat_getLast hne).symm⟩
    subst hp
    have hl : init.length = n := by
      simp at hn
      omega
    have hnd' : init.Nodup := (List.nodup_append.1 hnd).1
    have hnf : f ∉ init := by
      intro hm
      exact (List.nodup_append.1 hnd).2.2 f hm f (by simp) rfl
    have hgl : (init ++ [f]).getLast? = some f := by simp
    have hdl : (init ++ [f]).dropLast = init := by simp
    have hdelf : ∀ st' : Fin F, (st'.registry.map (·.1)).Nodup →
        isAlive { st' with registry := dDel st'.registry f } f = false := by
      intro st' hk'
      have := dGet_dDel (K := Nat) (β := Info F) hk' f f
      simp [isAlive, this]
    rw [exitLoop]
    simp only [Option.isNone_some, hd, Bool.or_false, Bool.false_eq_true, if_false,
      Option.getD_some, hgl, hdl]
    cases hg : dGet st.registry f with
    | none =>
      have hc : st.call f = (st, none) := by simp [call, hg]
      have hal : isAlive st f = false := by simp [isAlive, hg]
      simp only [hc, hal, Bool.false_eq_true, if_false]
      obtain ⟨a, b, c⟩ := ih init st s hl hd hsh hnd' hk
      refine ⟨a, b, ?_⟩
      rw [c]
      simp [hg]
    | some info =>
      let st' : Fin F := { st with registry := dDel st.registry f }
      have hc : st.call f = (st', some info.func) := by
        simp [call, hg, hsh, st']
      simp only [hc]
      generalize hrun : run info.func st' s = rr
      obtain ⟨st2, s2, x⟩ := rr
      have h1 : st2 = st' := by
        have := hr.same info.func st' s
        rw [hrun] at this
        exact this
      have h2 : x = none := by
        have := hr.ok info.func st' s
        rw [hrun] at this
        exact this
      have h3 : log s2 = log s ++ [(info.func, st.gc)] := by
        have := hr.logs info.func st' s
        rw [hrun] at this
        exact this
      subst h1 h2
      have hk' : (st'.registry.map (·.1)).Nodup := dDel_nodup _ _ hk
      have hal : isAlive st' f = false := hdelf st hk
      simp only [hal, Bool.false_eq_true, if_false]
      obtain ⟨a, b, c⟩ := ih init st' s2 hl hd hsh hnd' hk'
      refine ⟨a, b, ?_⟩
      rw [c, h3]
      simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.singleton_append, List.filterMap_cons, hg, Option.map_some, List.append_assoc,
        List.cons_append]
      have hrest : (init.reverse.filterMap (fun f' => (dGet st'.registry f').map (·.func, st'.gc))) =
          (init.reverse.filterMap (fun f' => (dGet st.registry f').map (·.func, st.gc))) := by
        have hcongr : ∀ l : List Nat, f ∉ l →
            l.filterMap (fun f' => (dGet st'.registry f').map (·.func, st'.gc)) =
            l.filterMap (fun f' => (dGet st.registry f').map (·.func, st.gc)) := by
          intro l
          induction l with
          | nil => intro _; rfl
          | cons x r ihl =>
            intro hl
            have hxf : f ≠ x := fun e => hl (by simp [e])
            have e1 : dGet st'.registry x = dGet st.registry x := by
              simp only [st', dGet_dDel hk, hxf, if_false]
            simp only [List.filterMap_cons, e1, ihl (fun h => hl (by simp [h]))]
            rfl
        exact hcongr _ (fun h => hnf (List.mem_reverse.1 h))
      rw [hrest]

theorem selectForExit_nodup (st : Fin F) (hk : (st.registry.map (·.1)).Nodup) :
    (selectForExit st).Nodup := by
  obtain ⟨h1, h2, _⟩ := selectForExit_proven F st
  rw [h1]
  have hf : ((st.registry.filter (fun kv => kv.2.atexit)).map (·.1)).Nodup :=
    (List.Sublist.map _ List.filter_sublist).nodup hk
  exact ((h2.map _).nodup_iff).2 hf

theorem exit_start (run : RunF σ F) (hook : σ → PyExc → σ × Option PyExc)
    (log : σ → List (F × Bool)) (hr : PlainRun run log) (s : σ) (st0 : Fin F)
    (hsh : st0.shutdown = false) (hk : (st0.registry.map (·.1)).Nodup) :
    (exitLoop run hook ((selectForExit st0).length + 1) st0 s none).2.2 = none ∧
    (exitLoop run hook ((selectForExit st0).length + 1) st0 s none).1.gc = st0.gc ∧
    log (exitLoop run hook ((selectForExit st0).length + 1) st0 s none).2.1 = log s ++
      ((selectForExit st0).reverse.filterMap (fun f => (dGet st0.registry f).map (·.func, st0.gc))) := by
  have hsel : selectForExit ({ st0 with dirty := false } : Fin F) = selectForExit st0 := rfl
  have hstart : exitLoop run hook ((selectForExit st0).length + 1) st0 s none =
      exitLoop run hook ((selectForExit st0).length + 1) { st0 with dirty := false } s
        (some (selectForExit st0)) := by
    rw [exitLoop, exitLoop]
    simp only [Option.isNone_none, Option.isNone_some, Bool.true_or, Bool.false_or, if_true,
      Bool.false_eq_true, if_false, Option.getD_some, hsel]
  rw [hstart]
  exact exit_loop_order run hook log hr _ _ { st0 with dirty := false } s rfl rfl hsh
    (selectForExit_nodup st0 hk) hk

theorem exitfuncOrder_proven : ExitfuncOrder := by
  intro F σ run hook log st s hr hsh hne hk sel r
  have hempty : st.registry.isEmpty = false := by
    cases hreg : st.registry with
    | nil => exact absurd hreg hne
    | cons _ _ => rfl
  cases hgc : st.gc with
  | true =>
    obtain ⟨a, b, c⟩ := exit_start run hook log hr s ({ st with gc := false }) hsh hk
    have hr0 : r = ({ { (exitLoop run hook (sel.length + 1) { st with gc := false } s none).1 with
        shutdown := true } with gc := true },
        (exitLoop run hook (sel.length + 1) { st with gc := false } s none).2.1,
        (exitLoop run hook (sel.length + 1) { st with gc := false } s none).2.2) := by
      simp [r, exitfunc, hempty, hgc]
    rw [hr0]
    exact ⟨a, c, rfl, rfl⟩
  | false =>
    obtain ⟨a, b, c⟩ := exit_start run hook log hr s st hsh hk
    have hr0 : r = ({ (exitLoop run hook (sel.length + 1) st s none).1 with shutdown := true },
        (exitLoop run hook (sel.length + 1) st s none).2.1,
        (exitLoop run hook (sel.length + 1) st s none).2.2) := by
      simp [r, exitfunc, hempty, hgc]
    rw [hr0]
    rw [hgc] at b c
    exact ⟨a, c, rfl, b⟩

/-- The paths of the exit loop that `ExitfuncOrder` leaves out. An `Exception` from a finalizer goes
to `sys.excepthook` and the loop goes on; an exception from the hook itself, or a `BaseException`
from the finalizer, ends the loop with it; a finalizer whose function registers it again fails the
`assert`. A dirty registry (a finalizer created by the last function) makes the loop select again,
dropping what was pending. Whatever the loop gives, `_exitfunc` sets `_shutdown` and re-enables `gc`
if it disabled it, and an empty registry runs nothing. -/
def ExitfuncPaths : Prop :=
  ∀ (F σ : Type) (run : RunF σ F) (hook : σ → PyExc → σ × Option PyExc) (n fuel : Nat) (st st1 st2 : Fin F)
    (s s2 s3 : σ) (pre : List Nat) (f : Nat) (fn : F) (e e' : PyExc) (p : Option (List Nat)),
    (st.dirty = false → st.call f = (st1, some fn) →
      (run fn st1 s = (st2, s2, some (e, true)) → hook s2 e = (s3, none) → isAlive st2 f = false →
        exitLoop run hook (n + 1) st s (some (pre ++ [f])) = exitLoop run hook n st2 s3 (some pre)) ∧
      (run fn st1 s = (st2, s2, some (e, true)) → hook s2 e = (s3, some e') →
        exitLoop run hook (n + 1) st s (some (pre ++ [f])) = (st2, s3, some e')) ∧
      (run fn st1 s = (st2, s2, some (e, false)) →
        exitLoop run hook (n + 1) st s (some (pre ++ [f])) = (st2, s2, some e)) ∧
      (run fn st1 s = (st2, s2, none) → isAlive st2 f = true →
        exitLoop run hook (n + 1) st s (some (pre ++ [f])) = (st2, s2, some (.assertionError "")))) ∧
    (st.dirty = true → exitLoop run hook (n + 1) st s p = exitLoop run hook (n + 1) st s none) ∧
    (exitfunc run hook fuel st s).1.shutdown = true ∧
    (st.registry ≠ [] → st.gc = true → (exitfunc run hook fuel st s).1.gc = true) ∧
    (st.registry = [] → exitfunc run hook fuel st s = ({ st with shutdown := true }, s, none))

theorem exitfuncPaths_proven : ExitfuncPaths := by
  intro F σ run hook n fuel st st1 st2 s s2 s3 pre f fn e e' p
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hd hc
    have hgl : (pre ++ [f]).getLast? = some f := by simp
    have hdl : (pre ++ [f]).dropLast = pre := by simp
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hrun hh ha
      rw [exitLoop]
      simp [hd, hgl, hdl, hc, hrun, hh, ha]
    · intro hrun hh
      rw [exitLoop]
      simp [hd, hgl, hdl, hc, hrun, hh]
    · intro hrun
      rw [exitLoop]
      simp [hd, hgl, hdl, hc, hrun]
    · intro hrun ha
      rw [exitLoop]
      simp [hd, hgl, hdl, hc, hrun, ha]
  · intro hd
    rw [exitLoop, exitLoop]
    simp [hd]
  · simp only [exitfunc]
    split <;> rfl
  · intro hne hg
    have : st.registry.isEmpty = false := by
      cases hreg : st.registry with
      | nil => exact absurd hreg hne
      | cons _ _ => rfl
    simp [exitfunc, this, hg]
  · intro h
    simp [exitfunc, h]

end Fin

end PyLean.CoreLibs.Misc.Weakref
