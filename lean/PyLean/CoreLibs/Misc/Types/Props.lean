import PyLean.CoreLibs.Misc.Types.Model

/-! Properties of the class-creation helpers of `Lib/types.py`, over any `Ops`. -/

namespace PyLean.CoreLibs.Misc.Types

open PyLean

variable {O NS R : Type}

/-- The shape of a `resolveLoop` result, as `resolveBases` reads it. -/
def viewResolve : Py (List O × Bool) → Py (Option (List O))
  | .error e => .error e
  | .ok (_, false) => .ok none
  | .ok (new, true) => .ok (some new)

theorem splice_mid (acc rest nb : List O) (b : O) (i : Nat) (hi : i = acc.length) :
    splice (acc ++ b :: rest) i nb = acc ++ nb ++ rest := by
  subst hi
  simp [splice, List.take_append, List.drop_append]

theorem resolve_update (ops : Ops O NS R) (bases : List O) :
    ∀ (rest : List O) (i : Nat) (acc before : List O) (upd : Bool) (shift : Int),
      ((acc.length : Int) = i + shift) → (upd = false → acc = before) →
      viewResolve (resolveLoop ops bases i rest (acc ++ rest) upd shift) =
        updateLoop ops bases rest before (if upd then some acc else none) := by
  intro rest
  induction rest with
  | nil =>
    intro i acc before upd shift _ _
    cases upd <;> simp [resolveLoop, updateLoop, viewResolve]
  | cons b rest ih =>
    intro i acc before upd shift hlen hupd
    have keepIH : viewResolve (resolveLoop ops bases (i + 1) rest (acc ++ b :: rest) upd shift) =
        updateLoop ops bases rest (before ++ [b])
          ((if upd then some acc else none).map (· ++ [b])) := by
      have := ih (i + 1) (acc ++ [b]) (before ++ [b]) upd shift
        (by simp [hlen]; omega) (fun h => by rw [hupd h])
      cases upd <;> simpa using this
    simp only [resolveLoop, updateLoop]
    split
    · exact keepIH
    · split
      · exact keepIH
      · rename_i f hf
        cases hc : f bases with
        | error e => rfl
        | ok r =>
          cases r with
          | none => rfl
          | some nb =>
            simp only
            have hi : (i + shift).toNat = acc.length := by omega
            rw [hi, splice_mid acc rest nb b _ rfl]
            have := ih (i + 1) (acc ++ nb) (before ++ [b]) true (shift + nb.length - 1)
              (by simp; omega) (by simp)
            have e : (if upd = true then some acc else none).getD before = acc := by
              cases upd with
              | true => simp
              | false => simp [hupd rfl]
            rw [e]
            simpa using this

/-- `resolve_bases` and the C function behind the class statement implement the same PEP 560 step:
for every object model and every base tuple, `types.resolve_bases(bases)` and `update_bases` give
the same result, the same exception, and the same answer to "is it the original tuple". -/
def ResolveBasesTwin : Prop :=
  ∀ (O NS R : Type) (ops : Ops O NS R) (bases : List O),
    resolveBases ops bases = updateBases ops bases

theorem resolveBasesTwin_proven : ResolveBasesTwin := by
  intro O NS R ops bases
  have := resolve_update ops bases bases 0 [] [] false 0 (by simp) (by simp)
  simp only [List.nil_append, Bool.false_eq_true, if_false] at this
  unfold resolveBases updateBases
  rw [← this]
  cases resolveLoop ops bases 0 bases bases false 0 with
  | error e => rfl
  | ok r =>
    obtain ⟨n, u⟩ := r
    cases u <;> rfl

/-- The bases with their `__mro_entries__` replaced. Every entry that is no class and has the
method contributes the tuple it returns. -/
def flatBases (ops : Ops O NS R) (bases : List O) : List O → List O
  | [] => []
  | b :: rest =>
    (if ops.isType b then [b] else
      match ops.mroEntries b with
      | none => [b]
      | some f =>
        match f bases with
        | .ok (some nb) => nb
        | _ => []) ++ flatBases ops bases rest

theorem updateLoop_flat (ops : Ops O NS R) (bases : List O)
    (hok : ∀ b ∈ bases, ∀ f, ops.isType b = false → ops.mroEntries b = some f →
      ∃ nb, f bases = .ok (some nb)) :
    ∀ (rest before : List O) (new : Option (List O)), (∀ b ∈ rest, b ∈ bases) →
      ∃ r, updateLoop ops bases rest before new = .ok r ∧
        (r.getD (before ++ rest)) ++ [] = (new.getD before) ++ flatBases ops bases rest ∧
        (r.isSome = (new.isSome || rest.any (fun b => !ops.isType b && (ops.mroEntries b).isSome))) := by
  intro rest
  induction rest with
  | nil =>
    intro before new _
    refine ⟨new, rfl, ?_, ?_⟩
    · cases new <;> simp [flatBases]
    · simp
  | cons b rest ih =>
    intro before new hmem
    have hb := hmem b (by simp)
    have hrest : ∀ x ∈ rest, x ∈ bases := fun x hx => hmem x (by simp [hx])
    simp only [updateLoop, flatBases]
    by_cases ht : ops.isType b = true
    · obtain ⟨r, h1, h2, h3⟩ := ih (before ++ [b]) (new.map (· ++ [b])) hrest
      refine ⟨r, by simp only [ht, if_true]; exact h1, ?_, ?_⟩
      · simp only [ht, if_true]
        cases new with
        | none => simpa using h2
        | some l => simpa using h2
      · rw [h3]
        cases new <;> simp [ht]
    · have ht' : ops.isType b = false := by simpa using ht
      cases hm : ops.mroEntries b with
      | none =>
        obtain ⟨r, h1, h2, h3⟩ := ih (before ++ [b]) (new.map (· ++ [b])) hrest
        refine ⟨r, by simp only [ht', hm]; simpa using h1, ?_, ?_⟩
        · simp only [ht', hm]
          cases new with
          | none => simpa using h2
          | some l => simpa using h2
        · rw [h3]
          cases new <;> simp [ht', hm]
      | some f =>
        obtain ⟨nb, hnb⟩ := hok b hb f ht' hm
        obtain ⟨r, h1, h2, h3⟩ := ih (before ++ [b]) (some (new.getD before ++ nb)) hrest
        refine ⟨r, by simp only [ht', hm, hnb]; simpa using h1, ?_, ?_⟩
        · simp only [ht', hm, hnb]
          simpa using h2
        · rw [h3]
          simp [ht', hm]

/-- `resolve_bases` with `shift`: for every base tuple whose `__mro_entries__` methods all return a
tuple, the result replaces each such base, in place, by the tuple it returned, keeps the others in
order, and is the original object exactly when no base has the method. -/
def ResolveBasesFlat : Prop :=
  ∀ (O NS R : Type) (ops : Ops O NS R) (bases : List O),
    (∀ b ∈ bases, ∀ f, ops.isType b = false → ops.mroEntries b = some f →
      ∃ nb, f bases = .ok (some nb)) →
    ∃ r, resolveBases ops bases = .ok r ∧
      r.getD bases = flatBases ops bases bases ∧
      (r.isNone = !bases.any (fun b => !ops.isType b && (ops.mroEntries b).isSome))

theorem resolveBasesFlat_proven : ResolveBasesFlat := by
  intro O NS R ops bases hok
  rw [resolveBasesTwin_proven O NS R ops bases]
  obtain ⟨r, h1, h2, h3⟩ := updateLoop_flat ops bases hok bases [] none (fun _ h => h)
  refine ⟨r, h1, ?_, ?_⟩
  · simpa using h2
  · cases r with
    | none =>
      simp only [Option.isSome_none, Option.isNone_none] at h3 ⊢
      simpa using h3.symm
    | some l =>
      simp only [Option.isSome_some, Option.isNone_some] at h3 ⊢
      simpa using h3.symm

/-- What `_calculate_meta` assumes of `issubclass`: it does not raise, and it is a preorder. -/
structure SubOrder (ops : Ops O NS R) (sub : O → O → Bool) : Prop where
  ok : ∀ a b, ops.issubclass a b = .ok (sub a b)
  refl : ∀ a, sub a a = true
  trans : ∀ a b c, sub a b = true → sub b c = true → sub a c = true

/-- `_calculate_meta` returns the most derived metaclass: when `issubclass` is a preorder, a result
`w` is a subclass of the candidate and of `type(b)` for every base `b`, which is what `type.__new__`
checks afterwards. It is either the candidate or the type of a base. Otherwise the result is the
"metaclass conflict" `TypeError`. -/
def CalculateMetaWinner : Prop :=
  ∀ (O NS R : Type) (ops : Ops O NS R) (sub : O → O → Bool), SubOrder ops sub →
    ∀ (m0 : O) (bases : List O),
      (∃ w, calculateMeta ops m0 bases = .ok w ∧ sub w m0 = true ∧
        (∀ b ∈ bases, sub w (ops.typeOf b) = true) ∧
        (w = m0 ∨ ∃ b ∈ bases, w = ops.typeOf b)) ∨
      (∃ m, calculateMeta ops m0 bases = .error (.typeError m))

theorem calcLoop_spec (ops : Ops O NS R) (sub : O → O → Bool) (hs : SubOrder ops sub) :
    ∀ (bases : List O) (winner : O),
      (∃ w, calcLoop ops winner bases = .ok w ∧ sub w winner = true ∧
        (∀ b ∈ bases, sub w (ops.typeOf b) = true) ∧
        (w = winner ∨ ∃ b ∈ bases, w = ops.typeOf b)) ∨
      (∃ m, calcLoop ops winner bases = .error (.typeError m)) := by
  intro bases
  induction bases with
  | nil => intro winner; exact .inl ⟨winner, rfl, hs.refl _, by simp, .inl rfl⟩
  | cons b rest ih =>
    intro winner
    simp only [calcLoop, hs.ok]
    cases h1 : sub winner (ops.typeOf b) with
    | true =>
      rcases ih winner with ⟨w, h, hw, hall, hor⟩ | hE
      · refine .inl ⟨w, h, hw, ?_, ?_⟩
        · intro x hx
          rcases List.mem_cons.1 hx with rfl | hx
          · exact hs.trans _ _ _ hw h1
          · exact hall x hx
        · rcases hor with rfl | ⟨c, hc, e⟩
          · exact .inl rfl
          · exact .inr ⟨c, by simp [hc], e⟩
      · exact .inr hE
    | false =>
      cases h2 : sub (ops.typeOf b) winner with
      | true =>
        rcases ih (ops.typeOf b) with ⟨w, h, hw, hall, hor⟩ | hE
        · refine .inl ⟨w, h, hs.trans _ _ _ hw h2, ?_, ?_⟩
          · intro x hx
            rcases List.mem_cons.1 hx with rfl | hx
            · exact hw
            · exact hall x hx
          · rcases hor with e | ⟨c, hc, e⟩
            · exact .inr ⟨b, by simp, e⟩
            · exact .inr ⟨c, by simp [hc], e⟩
        · exact .inr hE
      | false => exact .inr ⟨_, rfl⟩

theorem calculateMetaWinner_proven : CalculateMetaWinner := by
  intro O NS R ops sub hs m0 bases
  exact calcLoop_spec ops sub hs bases m0

/-- `prepare_class` and `metaclass`: a `metaclass` entry of `kwds` never reaches `__prepare__` or
the returned `kwds`, and the other keywords stay, in order. Without it and without bases the
candidate is `type`; without it and with bases it is `type(bases[0])`. `kwds` is a dict, so its
keys are distinct. -/
def PrepareClassMeta : Prop :=
  ∀ (O : Type) (kwds : List (String × O)),
    (kwds.map (·.1)).Nodup →
    (popMeta kwds).2 = kwds.filter (fun kv => kv.1 ≠ "metaclass") ∧
    (popMeta kwds).1 = kwds.lookup "metaclass"

theorem popMeta_spec {O : Type} : ∀ kwds : List (String × O),
    (kwds.map (·.1)).Nodup →
    (popMeta kwds).2 = kwds.filter (fun kv => kv.1 ≠ "metaclass") ∧
    (popMeta kwds).1 = kwds.lookup "metaclass" := by
  intro kwds
  induction kwds with
  | nil => intro _; simp [popMeta]
  | cons kv rest ih =>
    intro h
    obtain ⟨k, v⟩ := kv
    simp only [List.map_cons, List.nodup_cons] at h
    obtain ⟨hk, hn⟩ := h
    obtain ⟨i1, i2⟩ := ih hn
    by_cases hm : k = "metaclass"
    · subst hm
      constructor
      · simp only [popMeta, if_true, List.filter_cons, ne_eq, decide_not, not_true_eq_false,
          decide_true, Bool.not_true, Bool.false_eq_true, if_false]
        symm
        apply List.filter_eq_self.2
        intro a ha
        have : a.1 ≠ "metaclass" := by
          intro e
          exact hk (by rw [← e]; exact List.mem_map_of_mem ha)
        simpa using this
      · simp [popMeta, List.lookup]
    · have hm' : ("metaclass" == k) = false := by
        simp only [beq_eq_false_iff_ne]; exact fun e => hm e.symm
      constructor
      · simp [popMeta, hm, i1, List.filter_cons]
      · simp [popMeta, hm, i2, List.lookup, hm']

theorem prepareClassMeta_proven : PrepareClassMeta := fun _ kwds h => popMeta_spec kwds h

/-- The default candidate of `prepare_class`: without `metaclass`, an empty `bases` gives `type`,
which then cannot lose, and otherwise the winner comes from `_calculate_meta` started at
`type(bases[0])`. A candidate that is no class skips `_calculate_meta`. `__prepare__` is called when
it exists, with the remaining keywords, and `{}` is used otherwise. -/
def PrepareClassDefault : Prop :=
  ∀ (O NS R : Type) (ops : Ops O NS R) (name : String),
    (ops.isType ops.typeObj = true → ops.prepare ops.typeObj = none →
      prepareClass ops name [] none = .ok (ops.typeObj, ops.emptyNs, [])) ∧
    (∀ (m : O) (p : String → List O → List (String × O) → Py NS) (bases : List O)
       (kw kw' : List (String × O)),
      ops.isType m = false → ops.prepare m = some p → popMeta kw = (some m, kw') →
      prepareClass ops name bases (some kw) =
        (match p name bases kw' with
         | .error e => .error e
         | .ok ns => .ok (m, ns, kw')))

theorem prepareClassDefault_proven : PrepareClassDefault := by
  intro O NS R ops name
  constructor
  · intro h1 h2
    simp [prepareClass, popMeta, h1, h2, calculateMeta, calcLoop]
  · intro m p bases kw kw' h1 h2 h3
    simp only [prepareClass, Option.getD_some, h3, h1, h2, Bool.false_eq_true, if_false]
    cases p name bases kw' <;> rfl

/-- `new_class` and `__orig_bases__`: when no base has `__mro_entries__`, the metaclass gets the
original `bases` and `__orig_bases__` is not written. When one has, the metaclass gets the resolved
tuple, `prepare_class` sees it too, `exec_body` runs first and `__orig_bases__` is the tuple the
caller passed. -/
def NewClassOrigBases : Prop :=
  ∀ (O NS R : Type) (ops : Ops O NS R) (name : String) (bases : List O)
    (m : O) (ns ns1 ns2 : NS) (kw : List (String × O)) (body : NS → Py NS) (resolved : List O)
    (kwds : Option (List (String × O))),
    (resolveBases ops bases = .ok none →
      prepareClass ops name bases kwds = .ok (m, ns, kw) →
      body ns = .ok ns1 →
      newClass ops name bases kwds (some body) = ops.callMeta m name bases ns1 kw) ∧
    (resolveBases ops bases = .ok (some resolved) →
      prepareClass ops name resolved kwds = .ok (m, ns, kw) →
      body ns = .ok ns1 →
      ops.setOrig ns1 bases = .ok ns2 →
      newClass ops name bases kwds (some body) = ops.callMeta m name resolved ns2 kw)

theorem newClassOrigBases_proven : NewClassOrigBases := by
  intro O NS R ops name bases m ns ns1 ns2 kw body resolved kwds
  constructor
  · intro h1 h2 h3
    simp [newClass, h1, h2, h3]
  · intro h1 h2 h3 h4
    simp [newClass, h1, h2, h3, h4]

/-- `get_original_bases`: on a class it returns `__orig_bases__` when the class's own `__dict__`
has it, and `__bases__` otherwise. On an object without `__bases__`, or without `__dict__`, it raises
the documented `TypeError`, never `AttributeError`. -/
def GetOriginalBases : Prop :=
  ∀ (V : Type) (c : ClsLike V),
    (∀ b o, c.hasDict = true → c.bases = some b → c.origBases = some o →
      getOriginalBases c = .ok o) ∧
    (∀ b, c.hasDict = true → c.bases = some b → c.origBases = none →
      getOriginalBases c = .ok b) ∧
    ((c.hasDict = false ∨ c.bases = none) →
      getOriginalBases c = .error (.typeError s!"Expected an instance of type, not '{c.typeName}'"))

theorem getOriginalBases_proven : GetOriginalBases := by
  intro V c
  refine ⟨?_, ?_, ?_⟩
  · intro b o h1 h2 h3; simp [getOriginalBases, h1, h2, h3]
  · intro b h1 h2 h3; simp [getOriginalBases, h1, h2, h3]
  · intro h
    rcases h with h | h
    · simp [getOriginalBases, h]
    · cases hd : c.hasDict <;> simp [getOriginalBases, h, hd]

/-! ### `DynamicClassAttribute` -/

variable {F : Type}

/-- `getter`, `setter` and `deleter` each replace one function and keep the other two, keep
`overwrite_doc`, and `__isabstractmethod__` comes from the `fget` of the result. -/
def DcaAccessors : Prop :=
  ∀ (F : Type) (o : FnOps F) (d : DCA F) (f : F),
    (let g := d.getter o f
     g.fget = some f ∧ g.fset = d.fset ∧ g.fdel = d.fdel ∧ g.overwriteDoc = d.overwriteDoc ∧
       g.isAbstract = o.abstractOf f) ∧
    (let g := d.setter o f
     g.fget = d.fget ∧ g.fset = some f ∧ g.fdel = d.fdel ∧ g.overwriteDoc = d.overwriteDoc) ∧
    (let g := d.deleter o f
     g.fget = d.fget ∧ g.fset = d.fset ∧ g.fdel = some f ∧ g.overwriteDoc = d.overwriteDoc)

theorem dcaAccessors_proven : DcaAccessors := by
  intro F o d f
  simp [DCA.getter, DCA.setter, DCA.deleter, DCA.init]

/-- The doc rule "the next two lines make DynamicClassAttribute act the same as property": with an
explicit truthy `doc` that text stays and later accessors do not change it. Without one the
attribute takes `fget.__doc__`, and `getter` replaces it by the new `fget`'s doc when that has one.
-/
def DcaDoc : Prop :=
  ∀ (F : Type) (o : FnOps F) (f g : F) (s : String),
    s ≠ "" →
    (DCA.init o (some f) none none (some s)).doc = some s ∧
    (DCA.init o (some f) none none (some s)).overwriteDoc = false ∧
    ((DCA.init o (some f) none none (some s)).getter o g).doc = some s ∧
    (DCA.init o (some f) none none none).doc = o.docOf f ∧
    (DCA.init o (some f) none none none).overwriteDoc = true ∧
    (o.docOf g = some s → ((DCA.init o (some f) none none none).getter o g).doc = some s)

theorem dcaDoc_proven : DcaDoc := by
  intro F o f g s hs
  simp [DCA.init, DCA.getter, docOr, fgetDoc, hs]
  intro h
  simp [h, hs]

/-- The descriptor protocol of `DynamicClassAttribute`: class access raises `AttributeError` so that
`__getattr__` of the metaclass runs, except for an abstract `fget`, where the descriptor returns
itself so that `abc` can see it. Instance access calls `fget`. A missing function raises
`AttributeError` with the message of the source, on read, write and delete. -/
def DcaDescriptor : Prop :=
  ∀ (F I V : Type) (d : DCA F) (get : F → I → Py V) (set : F → I → V → Py Unit)
    (del : F → I → Py Unit) (i : I) (v : V) (f : F),
    (d.isAbstract = false → (d.get get none).toOption.isNone = true) ∧
    (d.isAbstract = true → ∃ r, d.get get none = .ok r ∧ (match r with
      | .self => True
      | .value _ => False)) ∧
    (d.fget = none → d.get get (some i) = .error (attrErr "unreadable attribute")) ∧
    (d.fget = some f → ∀ x, get f i = .ok x → ∃ r, d.get get (some i) = .ok r ∧ (match r with
      | .self => False
      | .value y => y = x)) ∧
    (d.fset = none → d.set set i v = .error (attrErr "can't set attribute")) ∧
    (d.fdel = none → d.delete del i = .error (attrErr "can't delete attribute"))

theorem dcaDescriptor_proven : DcaDescriptor := by
  intro F I V d get set del i v f
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; simp [DCA.get, h, Except.toOption]
  · intro h; exact ⟨.self, by simp [DCA.get, h], trivial⟩
  · intro h; simp [DCA.get, h]
  · intro h x hx; exact ⟨.value x, by simp [DCA.get, h, hx], rfl⟩
  · intro h; simp [DCA.set, h]
  · intro h; simp [DCA.delete, h]

/-! ### `_GeneratorWrapper` -/

variable {G V : Type}

/-- An operation on the wrapped generator. -/
inductive GenOp (V : Type) where
  | send (v : V)
  | throw (tp : V) (rest : List V)
  | close
  | next
  | giCode
  | giFrame
  | giRunning
  | giYieldfrom
  | giSuspended

/-- The operation on the generator itself. -/
def GenOp.direct (o : GenObj G V) (g : G) : GenOp V → G × Py V
  | .send v => o.send g v
  | .throw t r => o.throw g t r
  | .close => o.close g
  | .next => o.next g
  | .giCode => (g, o.giCode g)
  | .giFrame => (g, o.giFrame g)
  | .giRunning => (g, o.giRunning g)
  | .giYieldfrom => (g, o.giYieldfrom g)
  | .giSuspended => (g, o.giSuspended g)

/-- The operation through the wrapper. -/
def GenOp.wrapped (o : GenObj G V) (w : Wrapper G) : GenOp V → Wrapper G × Py V
  | .send v => w.send o v
  | .throw t r => w.throw o t r
  | .close => w.close o
  | .next => w.next o
  | .giCode => (w, w.giCode o)
  | .giFrame => (w, w.giFrame o)
  | .giRunning => (w, w.giRunning o)
  | .giYieldfrom => (w, w.giYieldfrom o)
  | .giSuspended => (w, w.giSuspended o)

def runDirect (o : GenObj G V) : G → List (GenOp V) → List (Py V)
  | _, [] => []
  | g, op :: rest =>
    let (g, r) := op.direct o g
    r :: runDirect o g rest

def runWrapped (o : GenObj G V) : Wrapper G → List (GenOp V) → List (Py V)
  | _, [] => []
  | w, op :: rest =>
    let (w, r) := op.wrapped o w
    r :: runWrapped o w rest

/-- `_GeneratorWrapper` is transparent: for every wrapped object and every sequence of `send`,
`throw`, `close`, `__next__` and `gi_*` reads, results and exceptions are those of the object
itself. `__iter__` and `__await__` return the generator itself exactly when the object is a native
generator. -/
def WrapperTransparent : Prop :=
  ∀ (G V : Type) (o : GenObj G V) (g : G) (isgen : Bool) (n q : Option String)
    (ops : List (GenOp V)),
    runWrapped o (Wrapper.init g isgen n q) ops = runDirect o g ops ∧
    (Wrapper.init g isgen n q).iter =
      (if isgen then .inl g else .inr (Wrapper.init g isgen n q))

theorem wrapper_sim (o : GenObj G V) (ops : List (GenOp V)) :
    ∀ (w : Wrapper G), runWrapped o w ops = runDirect o w.wrapped ops := by
  induction ops with
  | nil => intro w; rfl
  | cons op rest ih =>
    intro w
    cases op <;> simp only [runWrapped, runDirect, GenOp.wrapped, GenOp.direct, Wrapper.send,
      Wrapper.throw, Wrapper.close, Wrapper.next, Wrapper.giCode, Wrapper.giFrame,
      Wrapper.giRunning, Wrapper.giYieldfrom, Wrapper.giSuspended, ih]

theorem wrapperTransparent_proven : WrapperTransparent := by
  intro G V o g isgen n q ops
  exact ⟨wrapper_sim o ops _, rfl⟩

/-- The two state reads of `_GeneratorWrapper`, new in 3.15: `gi_state` is the state of the wrapped object and `cr_state` the
same one in the names of a coroutine, for every state a generator has; a read that raises raises through both. -/
def WrapperStates : Prop :=
  ∀ (G V : Type) (o : GenObj G V) (g : G) (isgen : Bool) (n q : Option String) (e : PyExc) (s c : String),
    (Wrapper.init g isgen n q).giState o = o.giState g ∧
    (o.giState g = .ok s → (s, c) ∈ [("GEN_CREATED", "CORO_CREATED"), ("GEN_RUNNING", "CORO_RUNNING"),
      ("GEN_SUSPENDED", "CORO_SUSPENDED"), ("GEN_CLOSED", "CORO_CLOSED")] →
      (Wrapper.init g isgen n q).crState o = .ok c) ∧
    (o.giState g = .error e → (Wrapper.init g isgen n q).crState o = .error e)

theorem wrapperStates_proven : WrapperStates := by
  intro G V o g isgen n q e s c
  refine ⟨rfl, ?_, ?_⟩
  · intro h hm
    simp only [Wrapper.crState, Wrapper.init, h]
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  · intro h
    simp [Wrapper.crState, Wrapper.init, h]

/-! ### `coroutine` -/

/-- `coroutine` on its input: a non-callable is the `TypeError`; a plain function that already is a
coroutine function comes back untouched; a generator function comes back with `CO_ITERABLE_COROUTINE`
added to its flags and no other flag changed; anything else gets the wrapper. -/
def CoroutineCases : Prop :=
  ∀ f : CoFunc,
    (f.callable = false → coroutine f = .error (.typeError "types.coroutine() expects a callable")) ∧
    (f.callable = true → f.function = true → f.flags &&& 0x180 ≠ 0 → coroutine f = .ok .same) ∧
    (f.callable = true → f.function = true → f.flags &&& 0x180 = 0 → f.flags &&& 0x20 ≠ 0 →
      coroutine f = .ok (.flagged (f.flags ||| 0x100))) ∧
    (f.callable = true → f.function = false → coroutine f = .ok .wrapped)

theorem coroutineCases_proven : CoroutineCases := by
  intro f
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h; simp [coroutine, h]
  · intro h1 h2 h3; simp [coroutine, h1, h2, h3]
  · intro h1 h2 h3 h4; simp [coroutine, h1, h2, h3, h4]
  · intro h1 h2; simp [coroutine, h1, h2]

/-- `wrapped` wraps exactly the objects that are generators in the `collections.abc` sense and not
coroutines, and are neither native coroutines nor iterable coroutines: a value that can already be
awaited is returned as it is. -/
def WrappedDecision : Prop :=
  ∀ c : CoValue,
    wrappedWraps c = true ↔
      (c.isCoroutineType = false ∧ (c.isGeneratorType = false ∨ c.flags &&& 0x100 = 0) ∧
        c.isGenerator = true ∧ c.isCoroutine = false)

theorem wrappedDecision_proven : WrappedDecision := by
  intro c
  unfold wrappedWraps
  cases h1 : c.isCoroutineType <;> cases h2 : c.isGeneratorType <;>
    cases h3 : c.isGenerator <;> cases h4 : c.isCoroutine <;> simp

end PyLean.CoreLibs.Misc.Types
