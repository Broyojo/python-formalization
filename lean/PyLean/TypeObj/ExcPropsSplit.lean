import PyLean.TypeObj.ExcPropsBase

/-!
`BaseExceptionGroup.split` and `subgroup`: what `exceptiongroup_split_recursive` computes.

The recursion is compared with `specSplit`, a pure function on the group tree of the initial
world. The comparison needs three things from the world, gathered in `SplitHyp`:

* the matcher is a function `p` of the exception (`check`);
* `derive` honours its contract: it returns a group whose `exceptions` are the given
  ones. `BaseExceptionGroup.derive` does, and a user override must for the result to be a
  split of the original group at all (`derive`);
* running user code does not change which objects are groups or what they contain (`Ext`).
  That is a type invariant: `.exceptions` is a read-only member holding a tuple, and
  `__class__` assignment cannot cross the layout of `BaseExceptionGroup`.

`Valid w f v` says that the group tree below `v` consists of heap objects of finished classes
and is less than `f` levels deep, the model's stand-in for the recursion limit.
-/

namespace PyLean.TypeObj

/-- `eg->excs`. -/
def egKids (w : World) (v : Val) : List Val := (excDataOf w v).egExceptions

/-- The nesting structure of an exception group. -/
inductive Shape where
  | leaf (v : Val)
  | node (kids : List Shape)

/-- The shape of `v` in world `w`. -/
def shapeW (w : World) : Nat → Val → Shape
  | 0, v => .leaf v
  | f + 1, v => if egCheck w v then .node ((egKids w v).map (shapeW w f)) else .leaf v

/-- A group of `xs`, or NULL when there are none: `exceptiongroup_subset` on shapes. -/
def mkNode : List Shape → Option Shape
  | [] => none
  | xs => some (.node xs)

/-- What `split` should return for a matcher `p`: a matching exception is kept whole, a
non-matching leaf goes to the rest, and a non-matching group is split child by child. -/
def specSplit (w : World) (p : Val → Bool) : Nat → Val → Option Shape × Option Shape
  | 0, _ => (none, none)
  | f + 1, v =>
    if p v then (some (shapeW w (f + 1) v), none)
    else if !egCheck w v then (none, some (.leaf v))
    else
      let rs := (egKids w v).map (specSplit w p f)
      (mkNode (rs.flatMap (·.1.toList)), mkNode (rs.flatMap (·.2.toList)))

/-! ## Stability of the world -/

/-- What user code may not change about an existing object: whether its class is a group
class, and what the group contains. -/
def groupView (w : World) (a : Addr) : Option Bool × List Val :=
  ((tdata w (typeOf w (.obj a))).mro.map (·.contains B.BaseExceptionGroup), egKids w (.obj a))

/-- `w'` extends `w`. -/
structure Ext (w w' : World) : Prop where
  size : w.heap.size ≤ w'.heap.size
  view : ∀ a, a < w.heap.size → groupView w' a = groupView w a

theorem Ext.refl (w : World) : Ext w w := ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem Ext.trans {w1 w2 w3 : World} (h1 : Ext w1 w2) (h2 : Ext w2 w3) : Ext w1 w3 :=
  ⟨Nat.le_trans h1.size h2.size, fun a ha => by
    rw [h2.view a (Nat.lt_of_lt_of_le ha h1.size), h1.view a ha]⟩

/-- A heap object of a finished class. -/
def NodeOK (w : World) : Val → Prop
  | .obj a => a < w.heap.size ∧ ((tdata w (typeOf w (.obj a))).mro).isSome = true
  | _ => False

/-- The tree below `v` consists of `NodeOK` objects and fits in `f` levels. -/
def Valid (w : World) : Nat → Val → Prop
  | 0, _ => False
  | f + 1, v => NodeOK w v ∧ (egCheck w v = true → ∀ k ∈ egKids w v, Valid w f k)

theorem egCheck_eq_contains {w : World} {a : Addr} {m : List Addr}
    (h : (tdata w (typeOf w (.obj a))).mro = some m) :
    egCheck w (.obj a) = m.contains B.BaseExceptionGroup := by
  simp [egCheck, isSubtype, h]

theorem NodeOK.mono {w w' : World} (h : Ext w w') {v : Val} (hn : NodeOK w v) : NodeOK w' v := by
  cases v with
  | obj a =>
    obtain ⟨h1, h2⟩ := hn
    refine ⟨Nat.lt_of_lt_of_le h1 h.size, ?_⟩
    have hv := congrArg Prod.fst (h.view a h1)
    simp only [groupView] at hv
    cases hm : (tdata w (typeOf w (.obj a))).mro with
    | none => simp [hm] at h2
    | some m =>
      rw [hm] at hv
      cases hm' : (tdata w' (typeOf w' (.obj a))).mro with
      | none => simp [hm'] at hv
      | some m' => simp
  | _ => exact hn.elim

theorem egCheck_stable {w w' : World} (h : Ext w w') {v : Val} (hn : NodeOK w v) :
    egCheck w' v = egCheck w v := by
  cases v with
  | obj a =>
    obtain ⟨h1, h2⟩ := hn
    have hv := congrArg Prod.fst (h.view a h1)
    simp only [groupView] at hv
    cases hm : (tdata w (typeOf w (.obj a))).mro with
    | none => simp [hm] at h2
    | some m =>
      cases hm' : (tdata w' (typeOf w' (.obj a))).mro with
      | none => simp [hm, hm'] at hv
      | some m' =>
        simp [hm, hm'] at hv
        rw [egCheck_eq_contains hm, egCheck_eq_contains hm', Bool.eq_iff_iff]
        simpa using hv
  | _ => exact hn.elim

theorem egKids_stable {w w' : World} (h : Ext w w') {v : Val} (hn : NodeOK w v) :
    egKids w' v = egKids w v := by
  cases v with
  | obj a => exact congrArg Prod.snd (h.view a hn.1)
  | _ => exact hn.elim

theorem Valid.nodeOK {w : World} {f : Nat} {v : Val} (h : Valid w f v) : NodeOK w v := by
  cases f with
  | zero => exact h.elim
  | succ f => exact h.1

theorem Valid.mono {w w' : World} (h : Ext w w') :
    ∀ (f : Nat) (v : Val), Valid w f v → Valid w' f v := by
  intro f
  induction f with
  | zero => intro v hv; exact hv.elim
  | succ f ih =>
    intro v hv
    refine ⟨hv.1.mono h, ?_⟩
    intro hg k hk
    rw [egCheck_stable h hv.1] at hg
    rw [egKids_stable h hv.1] at hk
    exact ih k (hv.2 hg k hk)

theorem shapeW_stable {w w' : World} (h : Ext w w') :
    ∀ (f : Nat) (v : Val), Valid w f v → shapeW w' f v = shapeW w f v := by
  intro f
  induction f with
  | zero => intro v _; rfl
  | succ f ih =>
    intro v hv
    simp only [shapeW, egCheck_stable h hv.1, egKids_stable h hv.1]
    split
    · rename_i hg
      congr 1
      apply List.map_congr_left
      intro k hk
      exact ih k (hv.2 hg k hk)
    · rfl

theorem specSplit_stable {w w' : World} (p : Val → Bool) (h : Ext w w') :
    ∀ (f : Nat) (v : Val), Valid w f v → specSplit w' p f v = specSplit w p f v := by
  intro f
  induction f with
  | zero => intro v _; rfl
  | succ f ih =>
    intro v hv
    simp only [specSplit, egCheck_stable h hv.1, egKids_stable h hv.1]
    by_cases hp : p v = true
    · simp only [hp, if_true, shapeW_stable h (f + 1) v hv]
    · simp only [hp, if_false, Bool.false_eq_true]
      by_cases hg : egCheck w v = true
      · have hm : (egKids w v).map (specSplit w' p f) = (egKids w v).map (specSplit w p f) := by
          apply List.map_congr_left
          intro k hk
          exact ih k (hv.2 hg k hk)
        simp only [hg, Bool.not_true, Bool.false_eq_true, if_false, hm]
      · simp only [Bool.not_eq_true] at hg
        simp [hg]

/-! ## The heap steps of `exceptiongroup_subset` -/

theorem ext_push (w : World) (o : Obj) :
    Ext w { w with heap := w.heap.push (.val o) } := by
  refine ⟨by simp, ?_⟩
  intro a ha
  have hg : World.get { w with heap := w.heap.push (.val o) } a = w.get a := get_push_lt w _ ha
  have ht : ∀ t, tdata { w with heap := w.heap.push (.val o) } t = tdata w t := by
    intro t
    by_cases h2 : t = w.heap.size
    · subst h2
      simp only [tdata]
      rw [get_push_size]
      have hd : w.get w.heap.size = default := by
        simp only [World.get]
        rw [Array.getD_eq_getD_getElem?]
        simp
      rw [hd]
      rfl
    · simp only [tdata, World.get]
      rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?]
      simp [Array.getElem?_push, h2]
  have htp : typeOf { w with heap := w.heap.push (.val o) } (.obj a) = typeOf w (.obj a) := by
    simp only [typeOf, hg]
  simp only [groupView, htp, ht, egKids, excDataOf, payloadOf, hg]

/-- The update of one object. -/
def updObj (f : ExcData → ExcData) (o : Obj) : Obj :=
  match o.body with
  | .exc d => { o with body := .exc (f d) }
  | _ => o

theorem excUpdW_val {w : World} {a : Addr} {o : Obj} (f : ExcData → ExcData)
    (hc : w.get a = .val o) : excUpdW w a f = w.setCell a (.val (updObj f o)) := by
  simp [excUpdW, hc, updObj]
  rfl

theorem get_excUpdW_ne (w : World) (a b : Addr) (f : ExcData → ExcData) (h : a ≠ b) :
    (excUpdW w a f).get b = w.get b := by
  cases hc : w.get a with
  | ty c t => simp [excUpdW, hc]
  | val o => rw [excUpdW_val f hc, get_setCell_ne _ _ _ _ h]

theorem tdata_excUpdW (w : World) (a t : Addr) (f : ExcData → ExcData) (ha : a < w.heap.size) :
    tdata (excUpdW w a f) t = tdata w t := by
  by_cases hab : a = t
  · subst hab
    cases hc : w.get a with
    | ty c d => simp [excUpdW, hc]
    | val o =>
      rw [excUpdW_val f hc]
      simp [tdata, get_setCell_same _ _ _ ha, hc]
  · simp [tdata, get_excUpdW_ne _ _ _ _ hab]

theorem typeOf_excUpdW (w : World) (a b : Addr) (f : ExcData → ExcData) (ha : a < w.heap.size) :
    typeOf (excUpdW w a f) (.obj b) = typeOf w (.obj b) := by
  by_cases hab : a = b
  · subst hab
    cases hc : w.get a with
    | ty c d => simp [excUpdW, hc]
    | val o =>
      rw [excUpdW_val f hc]
      simp only [typeOf, get_setCell_same _ _ _ ha, hc]
      unfold updObj
      split <;> rfl
  · simp [typeOf, get_excUpdW_ne _ _ _ _ hab]

theorem size_excUpdW (w : World) (a : Addr) (f : ExcData → ExcData) :
    (excUpdW w a f).heap.size = w.heap.size := by
  unfold excUpdW
  cases w.get a with
  | ty c t => rfl
  | val o => exact size_setCell _ _ _

theorem egKids_excUpdW (w : World) (a b : Addr) (f : ExcData → ExcData) (ha : a < w.heap.size)
    (hf : ∀ d, (f d).egExceptions = d.egExceptions) :
    egKids (excUpdW w a f) (.obj b) = egKids w (.obj b) := by
  by_cases hab : a = b
  · subst hab
    cases hc : w.get a with
    | ty c d => simp [excUpdW, hc]
    | val o =>
      rw [excUpdW_val f hc]
      simp only [egKids, excDataOf, payloadOf, get_setCell_same _ _ _ ha, hc]
      cases hb : o.body with
      | exc d => simp [updObj, hb, hf]
      | _ => simp [updObj, hb]
  · simp [egKids, excDataOf, payloadOf, get_excUpdW_ne _ _ _ _ hab]

theorem ext_excUpdW (w : World) (a : Addr) (f : ExcData → ExcData) (ha : a < w.heap.size)
    (hf : ∀ d, (f d).egExceptions = d.egExceptions) : Ext w (excUpdW w a f) := by
  refine ⟨by rw [size_excUpdW]; exact Nat.le_refl _, ?_⟩
  intro b _
  have ht : ∀ t, tdata (excUpdW w a f) t = tdata w t := fun t => tdata_excUpdW w a t f ha
  simp only [groupView, typeOf_excUpdW w a b f ha, ht, egKids_excUpdW w a b f ha hf]

/-! ## The hypotheses -/

/-- See the head of this file. -/
structure SplitHyp (rt : Rt) (mt : MatcherType) (mv : Val) (p : Val → Bool) : Prop where
  /-- The matcher is the function `p` and keeps groups intact. -/
  check : ∀ exc w b w', splitCheckMatch rt exc mt mv w = .ok b w' → b = p exc ∧ Ext w w'
  /-- `derive` returns a group of the given exceptions. -/
  derive : ∀ orig xs lst w g w', listOf w lst = some xs →
    callMethodO rt orig "derive" lst w = .ok g w' →
    Ext w w' ∧ NodeOK w' g ∧ (egCheck w' g = true → egKids w' g = xs)
  /-- The attribute reads and writes on `__notes__` keep groups intact. -/
  notesGet : ∀ orig w r w', rt.getOptionalAttr orig "__notes__" w = .ok r w' → Ext w w'
  notesList : ∀ n w c w', excSeqList rt n w = .ok c w' → Ext w w'
  notesSet : ∀ eg c w w', rt.setAttr eg "__notes__" c w = .ok () w' → Ext w w'

theorem tracebackSet_ext (a : Addr) (v : Option Val) (w w' : World) (ha : a < w.heap.size)
    (h : baseExceptionTracebackSet (.obj a) v w = .ok () w') : Ext w w' := by
  simp only [baseExceptionTracebackSet, M.bind_app, getW_app] at h
  cases v with
  | none => simp [typeErr, raiseC] at h
  | some t =>
    by_cases h1 : tracebackCheck w t = true
    · simp [h1, excUpdate_app] at h
      subst h
      exact ext_excUpdW _ _ _ ha (fun _ => rfl)
    · have h1' : tracebackCheck w t = false := by simpa using h1
      by_cases h2 : t.is .none = true
      · simp [h1', h2, excUpdate_app] at h
        subst h
        exact ext_excUpdW _ _ _ ha (fun _ => rfl)
      · have h2' : t.is .none = false := by simpa using h2
        simp [h1', h2', typeErr, raiseC] at h

theorem subsetCopyMeta_ext (orig : Val) (a : Addr) (w w' : World) (ha : a < w.heap.size)
    (h : subsetCopyMeta orig (.obj a) w = .ok () w') : Ext w w' := by
  have tail : ∀ w1 c c' w'', a < w1.heap.size →
      excUpdW (excUpdW w1 a (fun d => { d with context := c }))
        a (fun d => { d with suppressContext := true, cause := c' }) = w'' → Ext w1 w'' := by
    intro w1 c c' w'' h1 he
    subst he
    refine (ext_excUpdW _ a (fun d => { d with context := c }) h1 (fun _ => rfl)).trans
      (ext_excUpdW _ a (fun d => { d with suppressContext := true, cause := c' }) ?_ (fun _ => rfl))
    rw [size_excUpdW]
    exact h1
  simp only [subsetCopyMeta, M.bind_app, getW_app] at h
  cases hg : pyExceptionGetTraceback w orig with
  | none =>
    simp [hg, pyExceptionSetContext, pyExceptionSetCause, excUpdate_app] at h
    exact tail _ _ _ _ ha h
  | some tb =>
    simp only [hg] at h
    cases ht : baseExceptionTracebackSet (.obj a) (some tb) w with
    | err e w1 => simp [ht] at h
    | ok u w1 =>
      have hext := tracebackSet_ext a _ w w1 ha ht
      simp [ht, pyExceptionSetContext, pyExceptionSetCause, excUpdate_app] at h
      exact hext.trans (tail _ _ _ _ (Nat.lt_of_lt_of_le ha hext.size) h)

theorem listOf_alloc (w : World) (xs : List Val) :
    listOf { w with heap := w.heap.push (.val { cls := B.list, body := .list xs }) }
      (.obj w.heap.size) = some xs := by
  simp [listOf, payloadOf, get_push_size]

theorem subset_spec {rt : Rt} {mt : MatcherType} {mv : Val} {p : Val → Bool}
    (H : SplitHyp rt mt mv p) (orig : Val) (xs : List Val) (res : Option Val) (w w' : World)
    (hs : exceptiongroupSubset rt orig xs w = .ok res w') :
    Ext w w' ∧ (xs = [] → res = none) ∧
      (xs ≠ [] → ∃ g, res = some g ∧ NodeOK w' g ∧ egCheck w' g = true ∧ egKids w' g = xs) := by
  cases xs with
  | nil =>
    simp [exceptiongroupSubset] at hs
    obtain ⟨h1, h2⟩ := hs
    subst h1 h2
    exact ⟨Ext.refl _, by simp, by simp⟩
  | cons x xs' =>
    let xs := x :: xs'
    have hEmpty : xs.isEmpty = false := rfl
    let c : Obj := { cls := B.list, body := .list xs }
    let w1 : World := { w with heap := w.heap.push (.val c) }
    have hext1 : Ext w w1 := ext_push w c
    have hl1 : listOf w1 (.obj w.heap.size) = some xs := listOf_alloc w xs
    have hE : (x :: xs').isEmpty = false := rfl
    simp only [exceptiongroupSubset, hE, M.bind_app] at hs
    try simp only [Bool.false_eq_true, if_false, M.bind_app] at hs
    rw [alloc_app] at hs
    dsimp only at hs
    cases hd : callMethodO rt orig "derive" (.obj w.heap.size) w1 with
    | err e w2 =>
      simp only [w1, c, xs] at hd
      rw [hd] at hs
      cases hs
    | ok g w2 =>
      obtain ⟨hext2, hn, hk⟩ := H.derive _ _ _ _ _ _ hl1 hd
      simp only [w1, c, xs] at hd
      rw [hd] at hs
      dsimp only at hs
      simp only [getW_app] at hs
      by_cases hgrp : egCheck w2 g = true
      · have hkids := hk hgrp
        cases g with
        | obj a =>
          rw [if_pos hgrp] at hs
          simp only [M.bind_app] at hs
          cases hm : subsetCopyMeta orig (.obj a) w2 with
          | err e w3 => simp [hm] at hs
          | ok u w3 =>
            have hext3 := subsetCopyMeta_ext orig a w2 w3 hn.1 hm
            simp only [hm] at hs
            have fin : ∀ w4, Ext w3 w4 → Ext w w4 ∧ NodeOK w4 (.obj a) ∧
                egCheck w4 (.obj a) = true ∧ egKids w4 (.obj a) = xs := by
              intro w4 h4
              have h24 := hext3.trans h4
              refine ⟨hext1.trans (hext2.trans h24), hn.mono h24, ?_, ?_⟩
              · rw [egCheck_stable h24 hn]; exact hgrp
              · rw [egKids_stable h24 hn]; exact hkids
            cases ho : rt.getOptionalAttr orig "__notes__" w3 with
            | err e w4 => simp [ho] at hs
            | ok n w4 =>
              have hext4 := H.notesGet _ _ _ _ ho
              simp only [ho] at hs
              cases n with
              | none =>
                simp at hs
                obtain ⟨h1, h2⟩ := hs
                subst h1 h2
                obtain ⟨f1, f2, f3, f4⟩ := fin _ hext4
                exact ⟨f1, by simp [xs], fun _ => ⟨_, rfl, f2, f3, f4⟩⟩
              | some ns =>
                simp only [M.bind_app, getW_app] at hs
                by_cases hq : excSeqCheck w4 ns = true
                · simp only [hq, if_true, M.bind_app] at hs
                  cases hl : excSeqList rt ns w4 with
                  | err e w5 => simp [hl] at hs
                  | ok cs w5 =>
                    have hext5 := H.notesList _ _ _ _ hl
                    simp only [hl, alloc_app] at hs
                    cases hset : rt.setAttr (.obj a) "__notes__"
                        (some (.obj w5.heap.size))
                        { w5 with heap := w5.heap.push (.val { cls := B.list, body := .list cs }) } with
                    | err e w6 => simp [hset] at hs
                    | ok u6 w6 =>
                      have hext7 := H.notesSet _ _ _ _ hset
                      have hext6 : Ext w5 { w5 with heap := w5.heap.push (.val { cls := B.list, body := .list cs }) } :=
                        ext_push w5 _
                      simp [hset] at hs
                      obtain ⟨h1, h2⟩ := hs
                      subst h1 h2
                      obtain ⟨f1, f2, f3, f4⟩ := fin _ (hext4.trans (hext5.trans (hext6.trans hext7)))
                      exact ⟨f1, by simp [xs], fun _ => ⟨_, rfl, f2, f3, f4⟩⟩
                · have hq' : excSeqCheck w4 ns = false := by simpa using hq
                  simp [hq'] at hs
                  obtain ⟨h1, h2⟩ := hs
                  subst h1 h2
                  obtain ⟨f1, f2, f3, f4⟩ := fin _ hext4
                  exact ⟨f1, by simp [xs], fun _ => ⟨_, rfl, f2, f3, f4⟩⟩
        | _ => exact hn.elim
      · rw [if_neg hgrp] at hs
        simp [typeErr, raiseC] at hs

/-! ## The recursion -/

/-- A result pointer against the shape it should have. -/
def RO (w : World) (f : Nat) : Option Val → Option Shape → Prop
  | none, none => True
  | some v, some s => Valid w f v ∧ shapeW w f v = s
  | _, _ => False

theorem RO.mono {w w' : World} (h : Ext w w') {f : Nat} {x : Option Val} {s : Option Shape}
    (hr : RO w f x s) : RO w' f x s := by
  cases x <;> cases s
  · exact hr
  · exact hr
  · exact hr
  · exact ⟨Valid.mono h _ _ hr.1, (shapeW_stable h _ _ hr.1).trans hr.2⟩

theorem RO.toList {w : World} {f : Nat} {x : Option Val} {s : Option Shape} (hr : RO w f x s) :
    (∀ y ∈ x.toList, Valid w f y) ∧ x.toList.map (shapeW w f) = s.toList := by
  cases x <;> cases s
  · simp
  · exact hr.elim
  · exact hr.elim
  · obtain ⟨h1, h2⟩ := hr
    simp [h1, h2]

theorem flatMap_congr' {α β : Type} {f g : α → List β} :
    ∀ l : List α, (∀ a ∈ l, f a = g a) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | a :: as, h => by
    simp only [List.flatMap_cons]
    rw [h a (List.mem_cons_self), flatMap_congr' as (fun b hb => h b (List.mem_cons_of_mem _ hb))]

theorem kids_spec {p : Val → Bool} (cr : Bool) (f : Nat)
    (rec : Val → M (Option Val × Option Val))
    (IH : ∀ exc w m r w', Valid w f exc → rec exc w = .ok (m, r) w' →
      Ext w w' ∧ RO w' f m (specSplit w p f exc).1 ∧
        RO w' f r (if cr then (specSplit w p f exc).2 else none)) :
    ∀ (es ml rl : List Val) (w : World) (ml' rl' : List Val) (w' : World),
      (∀ e ∈ es, Valid w f e) → (∀ x ∈ ml, Valid w f x) → (∀ x ∈ rl, Valid w f x) →
      splitKids rec es ml rl w = .ok (ml', rl') w' →
      Ext w w' ∧ (∀ x ∈ ml', Valid w' f x) ∧ (∀ x ∈ rl', Valid w' f x) ∧
      ml'.map (shapeW w' f) = ml.map (shapeW w f) ++
        es.flatMap (fun e => (specSplit w p f e).1.toList) ∧
      rl'.map (shapeW w' f) = rl.map (shapeW w f) ++
        es.flatMap (fun e => (if cr then (specSplit w p f e).2 else none).toList) := by
  intro es
  induction es with
  | nil =>
    intro ml rl w ml' rl' w' _ hm hr h
    simp [splitKids] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    subst h1 h2 h3
    exact ⟨Ext.refl _, hm, hr, by simp, by simp⟩
  | cons e es ih =>
    intro ml rl w ml' rl' w' he hm hr h
    simp only [splitKids, M.bind_app] at h
    have hve : Valid w f e := he e List.mem_cons_self
    cases hrec : rec e w with
    | err ee w1 => simp [hrec] at h
    | ok res w1 =>
      obtain ⟨m, r⟩ := res
      simp only [hrec] at h
      obtain ⟨hext, hrm, hrr⟩ := IH e w m r w1 hve hrec
      obtain ⟨hm1, hms⟩ := hrm.toList
      obtain ⟨hr1, hrs⟩ := hrr.toList
      have hmv : ∀ x ∈ ml ++ m.toList, Valid w1 f x := by
        intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact Valid.mono hext _ _ (hm x hx)
        · exact hm1 x hx
      have hrv : ∀ x ∈ rl ++ r.toList, Valid w1 f x := by
        intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact Valid.mono hext _ _ (hr x hx)
        · exact hr1 x hx
      have hes : ∀ x ∈ es, Valid w1 f x := fun x hx =>
        Valid.mono hext _ _ (he x (List.mem_cons_of_mem _ hx))
      obtain ⟨hext2, hv1, hv2, hs1, hs2⟩ := ih _ _ w1 ml' rl' w' hes hmv hrv h
      refine ⟨hext.trans hext2, hv1, hv2, ?_, ?_⟩
      · rw [hs1, List.map_append, hms]
        have h1 : ml.map (shapeW w1 f) = ml.map (shapeW w f) :=
          List.map_congr_left (fun x hx => shapeW_stable hext f x (hm x hx))
        have h2 : es.flatMap (fun e => (specSplit w1 p f e).1.toList) =
            es.flatMap (fun e => (specSplit w p f e).1.toList) :=
          flatMap_congr' _ (fun x hx => by
            rw [specSplit_stable p hext f x (he x (List.mem_cons_of_mem _ hx))])
        rw [h1, h2]
        simp [List.flatMap_cons, List.append_assoc]
      · rw [hs2, List.map_append, hrs]
        have h1 : rl.map (shapeW w1 f) = rl.map (shapeW w f) :=
          List.map_congr_left (fun x hx => shapeW_stable hext f x (hr x hx))
        have h2 : es.flatMap (fun e => (if cr then (specSplit w1 p f e).2 else none).toList) =
            es.flatMap (fun e => (if cr then (specSplit w p f e).2 else none).toList) :=
          flatMap_congr' _ (fun x hx => by
            rw [specSplit_stable p hext f x (he x (List.mem_cons_of_mem _ hx))])
        rw [h1, h2]
        simp [List.flatMap_cons, List.append_assoc]

/-- `exceptiongroup_subset` builds the group `mkNode` describes. -/
theorem subset_RO {rt : Rt} {mt : MatcherType} {mv : Val} {p : Val → Bool}
    (H : SplitHyp rt mt mv p) (orig : Val) (xs : List Val) (L : List Shape) (res : Option Val)
    (f : Nat) (w w' : World) (hv : ∀ x ∈ xs, Valid w f x) (hL : xs.map (shapeW w f) = L)
    (hs : exceptiongroupSubset rt orig xs w = .ok res w') :
    Ext w w' ∧ RO w' (f + 1) res (mkNode L) := by
  obtain ⟨hext, h0, h1⟩ := subset_spec H orig xs res w w' hs
  refine ⟨hext, ?_⟩
  cases xs with
  | nil =>
    have := h0 rfl
    subst this
    simp at hL
    subst hL
    simp [mkNode, RO]
  | cons x xs' =>
    obtain ⟨g, hg, hn, hc, hk⟩ := h1 (by simp)
    subst hg
    have hv' : ∀ y ∈ x :: xs', Valid w' f y := fun y hy => Valid.mono hext _ _ (hv y hy)
    have hsh : (x :: xs').map (shapeW w' f) = L := by
      rw [← hL]
      exact List.map_congr_left (fun y hy => shapeW_stable hext f y (hv y hy))
    subst hsh
    constructor
    · refine ⟨hn, fun _ k hk' => ?_⟩
      rw [hk] at hk'
      exact hv' k hk'
    · simp [shapeW, hc, hk, mkNode]

/-- The recursion computes `specSplit`. -/
theorem split_spec {rt : Rt} {mt : MatcherType} {mv : Val} {p : Val → Bool}
    (H : SplitHyp rt mt mv p) (cr : Bool) :
    ∀ (f : Nat) (exc : Val) (w : World) (m r : Option Val) (w' : World),
      Valid w f exc → splitRecursive rt mt mv cr f exc w = .ok (m, r) w' →
      Ext w w' ∧ RO w' f m (specSplit w p f exc).1 ∧
        RO w' f r (if cr then (specSplit w p f exc).2 else none) := by
  intro f
  induction f with
  | zero =>
    intro exc w m r w' hv _
    exact hv.elim
  | succ f ih =>
    intro exc w m r w' hv h
    simp only [splitRecursive, M.bind_app] at h
    cases hc : splitCheckMatch rt exc mt mv w with
    | err e w1 => simp [hc] at h
    | ok b w1 =>
      obtain ⟨hb, hext⟩ := H.check _ _ _ _ hc
      simp only [hc] at h
      have hv1 := Valid.mono hext _ _ hv
      by_cases hp : p exc = true
      · have hbt : b = true := by rw [hb, hp]
        subst hbt
        simp at h
        obtain ⟨⟨h1, h2⟩, h3⟩ := h
        subst h1 h2 h3
        refine ⟨hext, ?_, ?_⟩
        · simp only [specSplit, hp, if_true]
          exact ⟨hv1, shapeW_stable hext _ _ hv⟩
        · simp only [specSplit, hp, if_true]
          cases cr <;> simp [RO]
      · have hp' : p exc = false := by simpa using hp
        have hbf : b = false := by rw [hb, hp']
        subst hbf
        have hgrp := egCheck_stable hext hv.1
        simp only [Bool.false_eq_true, if_false, M.bind_app, getW_app] at h
        by_cases hg : egCheck w exc = true
        · have hg1 : egCheck w1 exc = true := by rw [hgrp]; exact hg
          simp only [hg1, Bool.not_true, Bool.false_eq_true, if_false, M.bind_app] at h
          have hkw : (excDataOf w1 exc).egExceptions = egKids w exc := egKids_stable hext hv.1
          rw [hkw] at h
          have hkv : ∀ e ∈ egKids w exc, Valid w1 f e := fun e he =>
            Valid.mono hext _ _ (hv.2 hg e he)
          cases hk : splitKids (splitRecursive rt mt mv cr f) (egKids w exc) [] [] w1 with
          | err e w2 => simp [hk] at h
          | ok res w2 =>
            obtain ⟨ml, rl⟩ := res
            simp only [hk] at h
            obtain ⟨hext2, hvm, hvr, hs1, hs2⟩ :=
              kids_spec cr f _ ih (egKids w exc) [] [] w1 ml rl w2 hkv (by simp) (by simp) hk
            simp only [List.map_nil, List.nil_append] at hs1 hs2
            have hstab : ∀ e ∈ egKids w exc, specSplit w1 p f e = specSplit w p f e :=
              fun e he => specSplit_stable p hext f e (hv.2 hg e he)
            have hs1' : ml.map (shapeW w2 f) =
                ((egKids w exc).map (specSplit w p f)).flatMap (·.1.toList) := by
              rw [hs1, List.flatMap_map]
              exact flatMap_congr' _ (fun e he => by rw [hstab e he])
            have hspec : specSplit w p (f + 1) exc =
                (mkNode (((egKids w exc).map (specSplit w p f)).flatMap (·.1.toList)),
                 mkNode (((egKids w exc).map (specSplit w p f)).flatMap (·.2.toList))) := by
              simp [specSplit, hp', hg]
            cases hs : exceptiongroupSubset rt exc ml w2 with
            | err e w3 => simp [hs] at h
            | ok mres w3 =>
              obtain ⟨hext3, hro⟩ := subset_RO H exc ml _ mres f w2 w3 hvm hs1' hs
              simp only [hs] at h
              cases cr with
              | false =>
                simp at h
                obtain ⟨⟨h1, h2⟩, h3⟩ := h
                subst h1 h2 h3
                refine ⟨hext.trans (hext2.trans hext3), ?_, ?_⟩
                · rw [hspec]; exact hro
                · simp [RO]
              | true =>
                simp only [if_true, M.bind_app] at h
                have hs2' : rl.map (shapeW w2 f) =
                    ((egKids w exc).map (specSplit w p f)).flatMap (·.2.toList) := by
                  rw [hs2, List.flatMap_map]
                  exact flatMap_congr' _ (fun e he => by simp [hstab e he])
                have hvr3 : ∀ x ∈ rl, Valid w3 f x := fun x hx => Valid.mono hext3 _ _ (hvr x hx)
                have hs2'' : rl.map (shapeW w3 f) =
                    ((egKids w exc).map (specSplit w p f)).flatMap (·.2.toList) := by
                  rw [← hs2']
                  exact List.map_congr_left (fun x hx => shapeW_stable hext3 f x (hvr x hx))
                cases hr : exceptiongroupSubset rt exc rl w3 with
                | err e w4 => simp [hr] at h
                | ok rres w4 =>
                  obtain ⟨hext4, hro2⟩ := subset_RO H exc rl _ rres f w3 w4 hvr3 hs2'' hr
                  simp [hr] at h
                  obtain ⟨⟨h1, h2⟩, h3⟩ := h
                  subst h1 h2 h3
                  refine ⟨hext.trans (hext2.trans (hext3.trans hext4)), ?_, ?_⟩
                  · rw [hspec]; exact hro.mono hext4
                  · rw [hspec]; simpa using hro2
        · have hg' : egCheck w exc = false := by simpa using hg
          have hg1 : egCheck w1 exc = false := by rw [hgrp]; exact hg'
          simp [hg1] at h
          obtain ⟨⟨h1, h2⟩, h3⟩ := h
          subst h1 h2 h3
          refine ⟨hext, ?_, ?_⟩
          · simp [specSplit, hp', hg', RO]
          · have hsp : specSplit w p (f + 1) exc = (none, some (.leaf exc)) := by
              simp [specSplit, hp', hg']
            rw [hsp]
            cases cr with
            | false => simp [RO]
            | true =>
              refine ⟨hv1, ?_⟩
              simp [shapeW, hg1]

/-! ## The properties -/

mutual
  /-- The leaves of a shape, left to right. -/
  def Shape.leaves : Shape → List Val
    | .leaf v => [v]
    | .node ks => Shape.leavesL ks
  def Shape.leavesL : List Shape → List Val
    | [] => []
    | s :: ss => s.leaves ++ Shape.leavesL ss
end

/-- The leaves of an optional shape. -/
def sLeaves : Option Shape → List Val
  | none => []
  | some s => s.leaves

/-- The leaves of an optional result in a world. -/
def optLeaves (w : World) (f : Nat) (x : Option Val) : List Val :=
  sLeaves (x.map (shapeW w f))

theorem leavesL_append (a b : List Shape) :
    Shape.leavesL (a ++ b) = Shape.leavesL a ++ Shape.leavesL b := by
  induction a with
  | nil => simp [Shape.leavesL]
  | cons x xs ih => simp [Shape.leavesL, ih, List.append_assoc]

theorem leavesL_toList (x : Option Shape) : Shape.leavesL x.toList = sLeaves x := by
  cases x <;> simp [Shape.leavesL, sLeaves]

theorem sLeaves_mkNode (L : List Shape) : sLeaves (mkNode L) = Shape.leavesL L := by
  cases L with
  | nil => simp [mkNode, sLeaves, Shape.leavesL]
  | cons x xs => simp [mkNode, sLeaves, Shape.leaves]

theorem kids_perm (w : World) (p : Val → Bool) (f : Nat)
    (IH : ∀ v, Valid w f v →
      (sLeaves (specSplit w p f v).1 ++ sLeaves (specSplit w p f v).2).Perm (shapeW w f v).leaves) :
    ∀ es : List Val, (∀ e ∈ es, Valid w f e) →
      (Shape.leavesL (es.flatMap (fun e => (specSplit w p f e).1.toList)) ++
        Shape.leavesL (es.flatMap (fun e => (specSplit w p f e).2.toList))).Perm
      (Shape.leavesL (es.map (shapeW w f)))
  | [], _ => by simp [Shape.leavesL]
  | e :: es, h => by
    have h1 := IH e (h e List.mem_cons_self)
    have h2 := kids_perm w p f IH es (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.flatMap_cons, leavesL_append, leavesL_toList, List.map_cons, Shape.leavesL]
    generalize sLeaves (specSplit w p f e).1 = A at *
    generalize sLeaves (specSplit w p f e).2 = B at *
    generalize Shape.leavesL (es.flatMap (fun e => (specSplit w p f e).1.toList)) = C at *
    generalize Shape.leavesL (es.flatMap (fun e => (specSplit w p f e).2.toList)) = D at *
    have h3 : ((A ++ C) ++ (B ++ D)).Perm ((A ++ B) ++ (C ++ D)) := by
      simp only [List.append_assoc]
      refine List.Perm.append_left A ?_
      rw [← List.append_assoc, ← List.append_assoc]
      exact List.Perm.append_right D List.perm_append_comm
    exact h3.trans (h1.append h2)

theorem spec_perm (w : World) (p : Val → Bool) :
    ∀ (f : Nat) (v : Val), Valid w f v →
      (sLeaves (specSplit w p f v).1 ++ sLeaves (specSplit w p f v).2).Perm (shapeW w f v).leaves := by
  intro f
  induction f with
  | zero => intro v hv; exact hv.elim
  | succ f ih =>
    intro v hv
    by_cases hp : p v = true
    · simp [specSplit, hp, sLeaves]
    · have hp' : p v = false := by simpa using hp
      by_cases hg : egCheck w v = true
      · have h := kids_perm w p f ih (egKids w v) (hv.2 hg)
        simp [specSplit, hp', hg, sLeaves_mkNode, shapeW, Shape.leaves, List.flatMap_map]
        exact h
      · have hg' : egCheck w v = false := by simpa using hg
        simp [specSplit, hp', hg', sLeaves, shapeW, Shape.leaves]

/-- **`split` partitions the leaves.** Under `SplitHyp`, the leaves of the match part and the
leaves of the rest part together are exactly the leaves of the group, each once. -/
def SplitPartitionsLeaves : Prop :=
  ∀ (rt : Rt) (mt : MatcherType) (mv : Val) (p : Val → Bool), SplitHyp rt mt mv p →
    ∀ (f : Nat) (exc : Val) (w : World) (m r : Option Val) (w' : World),
      Valid w f exc → splitRecursive rt mt mv true f exc w = .ok (m, r) w' →
      (optLeaves w' f m ++ optLeaves w' f r).Perm (shapeW w f exc).leaves

theorem RO.leaves {w : World} {f : Nat} {x : Option Val} {s : Option Shape} (hr : RO w f x s) :
    optLeaves w f x = sLeaves s := by
  cases x <;> cases s
  · rfl
  · exact hr.elim
  · exact hr.elim
  · simp [optLeaves, hr.2]

theorem splitPartitionsLeaves_proven : SplitPartitionsLeaves := by
  intro rt mt mv p H f exc w m r w' hv h
  obtain ⟨_, h1, h2⟩ := split_spec H true f exc w m r w' hv h
  simp only [if_true] at h2
  rw [h1.leaves, h2.leaves]
  exact spec_perm w p f exc hv

/-- **`split` preserves structure.** Under `SplitHyp`, each part has the shape `specSplit`
gives: matching exceptions stay whole, and a group that matches only in part is rebuilt around
the matching children, with empty groups dropped. -/
def SplitPreservesStructure : Prop :=
  ∀ (rt : Rt) (mt : MatcherType) (mv : Val) (p : Val → Bool), SplitHyp rt mt mv p →
    ∀ (f : Nat) (exc : Val) (w : World) (m r : Option Val) (w' : World),
      Valid w f exc → splitRecursive rt mt mv true f exc w = .ok (m, r) w' →
      m.map (shapeW w' f) = (specSplit w p f exc).1 ∧ r.map (shapeW w' f) = (specSplit w p f exc).2

theorem RO.shape {w : World} {f : Nat} {x : Option Val} {s : Option Shape} (hr : RO w f x s) :
    x.map (shapeW w f) = s := by
  cases x <;> cases s
  · rfl
  · exact hr.elim
  · exact hr.elim
  · simp [hr.2]

theorem splitPreservesStructure_proven : SplitPreservesStructure := by
  intro rt mt mv p H f exc w m r w' hv h
  obtain ⟨_, h1, h2⟩ := split_spec H true f exc w m r w' hv h
  simp only [if_true] at h2
  exact ⟨h1.shape, h2.shape⟩

/-- **`subgroup(c)` is `split(c)[0]`.** Under `SplitHyp`, the recursion with
`construct_rest = false` builds a group of the same shape as the match part of the recursion
with `construct_rest = true`, and no rest. -/
def SubgroupEqualsSplitMatch : Prop :=
  ∀ (rt : Rt) (mt : MatcherType) (mv : Val) (p : Val → Bool), SplitHyp rt mt mv p →
    ∀ (f : Nat) (exc : Val) (w : World) (m1 r1 m2 r2 : Option Val) (w1 w2 : World),
      Valid w f exc →
      splitRecursive rt mt mv true f exc w = .ok (m1, r1) w1 →
      splitRecursive rt mt mv false f exc w = .ok (m2, r2) w2 →
      m1.map (shapeW w1 f) = m2.map (shapeW w2 f) ∧ r2 = none

theorem subgroupEqualsSplitMatch_proven : SubgroupEqualsSplitMatch := by
  intro rt mt mv p H f exc w m1 r1 m2 r2 w1 w2 hv h1 h2
  obtain ⟨_, a1, _⟩ := split_spec H true f exc w m1 r1 w1 hv h1
  obtain ⟨_, a2, a3⟩ := split_spec H false f exc w m2 r2 w2 hv h2
  refine ⟨by rw [a1.shape, a2.shape], ?_⟩
  simp only [Bool.false_eq_true, if_false] at a3
  cases r2 with
  | none => rfl
  | some x => exact a3.elim

theorem splitRec_full (rt : Rt) (mt : MatcherType) (mv : Val) (cr : Bool) (f : Nat) (exc : Val)
    (w w1 : World) (h : splitCheckMatch rt exc mt mv w = .ok true w1) :
    splitRecursive rt mt mv cr (f + 1) exc w = .ok (some exc, none) w1 := by
  simp [splitRecursive, h]

/-- **A condition that accepts the group returns the group itself.** When the matcher accepts
`exc`, for every kind of matcher and every `rt`, the recursion stops there: the match part is
`exc`, by identity, and there is no rest. `split` and `subgroup` then return `self`. -/
def SplitFullMatchIdentity : Prop :=
  (∀ (rt : Rt) (mt : MatcherType) (mv : Val) (cr : Bool) (f : Nat) (exc : Val) (w w1 : World),
    splitCheckMatch rt exc mt mv w = .ok true w1 →
    splitRecursive rt mt mv cr (f + 1) exc w = .ok (some exc, none) w1) ∧
  (∀ (rt : Rt) (self mv : Val) (mt : MatcherType) (w w1 w2 : World),
    getMatcherType mv w = .ok mt w1 →
    splitCheckMatch rt self mt mv w1 = .ok true w2 →
    baseExceptionGroupSplit rt self mv w = .ok (.tuple [self, .none]) w2 ∧
    baseExceptionGroupSubgroup rt self mv w = .ok self w2)

theorem splitFullMatchIdentity_proven : SplitFullMatchIdentity := by
  refine ⟨?_, ?_⟩
  · intro rt mt mv cr f exc w w1 h
    exact splitRec_full rt mt mv cr f exc w w1 h
  · intro rt self mv mt w w1 w2 h1 h2
    have key : ∀ cr, splitRecursive rt mt mv cr excRecFuel self w1 = .ok (some self, none) w2 :=
      fun cr => splitRec_full rt mt mv cr 1999 self w1 w2 h2
    constructor
    · simp only [baseExceptionGroupSplit, M.bind_app, h1, key]
      simp
    · simp only [baseExceptionGroupSubgroup, M.bind_app, h1, key]
      simp

/-- **A leaf that does not match goes to the rest**, and to nothing when `subgroup` asks for
no rest. -/
def SplitLeafNoMatch : Prop :=
  ∀ (rt : Rt) (mt : MatcherType) (mv : Val) (cr : Bool) (f : Nat) (exc : Val) (w w1 : World),
    splitCheckMatch rt exc mt mv w = .ok false w1 → egCheck w1 exc = false →
    splitRecursive rt mt mv cr (f + 1) exc w = .ok (none, if cr then some exc else none) w1

theorem splitLeafNoMatch_proven : SplitLeafNoMatch := by
  intro rt mt mv cr f exc w w1 h hg
  simp [splitRecursive, h, hg]

end PyLean.TypeObj
