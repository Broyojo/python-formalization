import PyLean.CoreLibs.Coll.ChainMapProps
import PyLean.CoreLibs.Coll.UserDict

/-!
Properties of `UserDict`: method-by-method comparison with `dict`. Without
`__missing__` every method matches except `popitem`, and with `__missing__` the inherited
`pop`, `setdefault` and `items()` part from `dict` subclasses.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace PyLean.CoreLibs.Coll

open PyLean D

variable {κ ν : Type} [DecidableEq κ]

theorem udNew_some {cls : String} {s : D κ ν} (h : WF s) : udNew cls (some s) [] = ⟨cls, s⟩ := by
  simp [udNew, udUpdate, D.update]
  exact update_nil_WF h

theorem mem_of_get? {d : D κ ν} {k : κ} {v : ν} (h : D.get? d k = some v) : D.mem d k = true := by
  simp [D.mem, h]

theorem mem_of_get?_none {d : D κ ν} {k : κ} (h : D.get? d k = none) : D.mem d k = false := by
  simp [D.mem, h]

theorem udGetitem_some {rk : κ → String} {miss : Option (κ → ν)} {u : UD κ ν} {k : κ} {v : ν}
    (h : D.get? u.data k = some v) : udGetitem rk miss u k = .ok v := by
  simp [udGetitem, mem_of_get? h, h]

theorem udGetitem_none {rk : κ → String} {miss : Option (κ → ν)} {u : UD κ ν} {k : κ}
    (h : D.get? u.data k = none) :
    udGetitem rk miss u k = match miss with
      | some f => .ok (f k)
      | none => .error (.keyError (rk k)) := by
  unfold udGetitem
  rw [mem_of_get?_none h]
  rfl

/-- Without `__missing__`, a `UserDict` behaves like the `dict` it wraps, method by
method, on every dict: subscript, `get`, `in`, `len`, `iter`, `pop` with and without a
default, `setdefault`, `del` (same `KeyError`), and `(k, v) in .items()`. Doc: "the class
... simulates a dictionary". -/
def UserDictMatchesDict : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] [DecidableEq ν] (rk : κ → String) (u : UD κ ν) (k : κ) (d : Option ν)
    (v w : ν),
    udGetitem rk none u k = dictGetitem rk none u.data k ∧
    udGet rk none u k d = .ok ((D.get? u.data k).or d) ∧
    udContains u k = D.mem u.data k ∧
    udLen u = (udIter u).length ∧
    udPop rk none u k d = (dictPop rk u.data k d).map (fun r => (r.1, { u with data := r.2 })) ∧
    (udSetdefault rk none u k v).1 = (dictSetdefault u.data k v).1 ∧
    (udSetdefault rk none u k v).2.data = (dictSetdefault u.data k v).2 ∧
    udItemsContains rk none u k w = dictItemsContains u.data k w

theorem userDictMatchesDict_proven : UserDictMatchesDict := by
  intro κ ν _ _ rk u k d v w
  have hlen : udLen u = (udIter u).length := by simp [udLen, udIter, D.keys]
  cases hg : D.get? u.data k with
  | some x =>
    have hm := mem_of_get? hg
    have h1 := udGetitem_some (rk := rk) (miss := none) hg
    refine ⟨?_, ?_, rfl, hlen, ?_, ?_, ?_, ?_⟩
    · simp [h1, dictGetitem, hg]
    · simp [udGet, udContains, hm, h1, Except.map, hg]
    · simp [udPop, h1, udDelitem, hm, dictPop, hg, bind, Except.bind, pure, Except.pure, Except.map]
    · simp [udSetdefault, h1, dictSetdefault, hg]
    · simp [udSetdefault, h1, dictSetdefault, hg]
    · simp [udItemsContains, h1, dictItemsContains, hg]
  | none =>
    have hm := mem_of_get?_none hg
    have h1 := udGetitem_none (rk := rk) (miss := none) hg
    simp only at h1
    refine ⟨?_, ?_, rfl, hlen, ?_, ?_, ?_, ?_⟩
    · simp [h1, dictGetitem, hg]
    · simp [udGet, udContains, hm, hg]
    · cases d <;> simp [udPop, h1, dictPop, hg, Except.map]
    · simp [udSetdefault, h1, dictSetdefault, hg]
    · simp [udSetdefault, h1, dictSetdefault, hg, udSetitem]
    · simp [udItemsContains, h1, dictItemsContains, hg]

/-- `dict.popitem` removes the most recently inserted item ("LIFO order", guaranteed since
3.7). `UserDict.popitem` should simulate that. False on 3.14: it inherits
`MutableMapping.popitem`, which takes the first key. -/
def UserDictPopitemMatchesDict : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] (rk : κ → String) (u : UD κ ν), u.data ≠ [] →
    udPopitem rk none u = (dictPopitem u.data).map (fun r => (r.1, { u with data := r.2 }))

theorem userDictPopitemMatchesDict_refuted : ¬ UserDictPopitemMatchesDict := by
  intro h
  have := h Nat Nat (fun _ => "") ⟨"UserDict", [(1, 1), (2, 2)]⟩ (by simp)
  simp [udPopitem, udIter, udGetitem, udDelitem, D.mem, D.get?, D.keys, D.del, dictPopitem, D.popitem?,
    Except.map, bind, Except.bind, pure, Except.pure] at this

/-- `reversed(d)` works on a `dict` since 3.8 and `UserDict` "simulates a dictionary". False:
`Mapping.__reversed__ = None` makes `reversed(UserDict(...))` a `TypeError`. -/
def UserDictReversible : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] (u : UD κ ν), udReversed u = dictReversed u.data

theorem userDictReversible_refuted : ¬ UserDictReversible := by
  intro h
  have := h Nat Nat ⟨"UserDict", []⟩
  simp [udReversed, dictReversed] at this

/-- `d[k] = v` then `d[k]` gives `v`, and leaves a valid dict; `del d[k]` on a present key removes
that key and no other; on an absent key it raises `KeyError(k)`, as `dict` does. -/
def UserDictSetDel : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] (rk : κ → String) (u : UD κ ν) (k x : κ) (v : ν), WF u.data →
    udGetitem rk none (udSetitem u k v) k = .ok v ∧ WF (udSetitem u k v).data ∧
    (D.mem u.data k = false → udDelitem rk u k = .error (.keyError (rk k))) ∧
    (∀ u', udDelitem rk u k = .ok u' →
      D.get? u'.data k = none ∧ (x ≠ k → D.get? u'.data x = D.get? u.data x))

theorem userDictSetDel_proven : UserDictSetDel := by
  intro κ ν _ rk u k x v hw
  refine ⟨?_, WF_set hw k v, ?_, ?_⟩
  · apply udGetitem_some
    simp [udSetitem, get?_set]
  · intro h
    simp [udDelitem, h]
  · intro u' h
    unfold udDelitem at h
    split at h
    · simp only [Except.ok.injEq] at h
      subst h
      constructor
      · simp [get?_del hw]
      · intro hx
        have : ¬ k = x := fun e => hx e.symm
        simp [get?_del hw, this]
    · simp at h

/-- Both orders remove an existing item; they differ only in which one is picked. A
one-item `UserDict` agrees with `dict`. -/
def UserDictPopitemNarrow : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] (rk : κ → String) (cls : String) (k : κ) (v : ν),
    udPopitem rk none ⟨cls, [(k, v)]⟩ =
      (dictPopitem [(k, v)]).map (fun r => (r.1, ⟨cls, r.2⟩))

theorem userDictPopitemNarrow_proven : UserDictPopitemNarrow := by
  intro κ ν _ rk cls k v
  simp [udPopitem, udIter, udGetitem, udDelitem, D.mem, D.get?, D.keys, D.del, dictPopitem, D.popitem?,
    Except.map, bind, Except.bind, pure, Except.pure]

/-- The comment at :1162-1163 says "Modify __contains__ and get() to work like dict does
when __missing__ is present": a `UserDict` subclass with `__missing__` should
act as a `dict` subclass with `__missing__`, where only `d[k]` consults it. For
`pop(k, default)`, `setdefault` and `(k, v) in .items()` this is false: the inherited
`MutableMapping` versions go through `self[key]`, and `__missing__` answers
instead of a `KeyError`. -/
def UserDictMissingLikeDict : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] [DecidableEq ν] (rk : κ → String) (f : κ → ν) (u : UD κ ν) (k : κ)
    (x v : ν),
    udPop rk (some f) u k (some x) =
      (dictPop rk u.data k (some x)).map (fun r => (r.1, { u with data := r.2 })) ∧
    (udSetdefault rk (some f) u k x).1 = (dictSetdefault u.data k x).1 ∧
    (udSetdefault rk (some f) u k x).2.data = (dictSetdefault u.data k x).2 ∧
    udItemsContains rk (some f) u k v = dictItemsContains u.data k v

theorem userDictMissingLikeDict_refuted : ¬ UserDictMissingLikeDict := by
  intro h
  have := (h Nat Nat (fun _ => "") (fun _ => 0) ⟨"D", []⟩ 1 5 0).1
  simp [udPop, udGetitem, udDelitem, D.mem, D.get?, dictPop, Except.map, bind, Except.bind, pure,
    Except.pure, Functor.map] at this

/-- The narrowed statement, which is all that holds: on a key that is present the
`__missing__` hook plays no part, and `get`/`in` never call it (the fix of gh-83445). -/
def UserDictMissingNarrow : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] [DecidableEq ν] (rk : κ → String) (f : κ → ν) (u : UD κ ν) (k : κ)
    (d : Option ν) (x v : ν),
    udGet rk (some f) u k d = .ok ((D.get? u.data k).or d) ∧
    udContains u k = D.mem u.data k ∧
    (D.mem u.data k = true →
      udPop rk (some f) u k d = (dictPop rk u.data k d).map (fun r => (r.1, { u with data := r.2 })) ∧
      (udSetdefault rk (some f) u k x).1 = (dictSetdefault u.data k x).1 ∧
      udItemsContains rk (some f) u k v = dictItemsContains u.data k v)

theorem userDictMissingNarrow_proven : UserDictMissingNarrow := by
  intro κ ν _ _ rk f u k d x v
  refine ⟨?_, rfl, ?_⟩
  · cases hg : D.get? u.data k with
    | some y =>
      simp [udGet, udContains, mem_of_get? hg, udGetitem_some (rk := rk) (miss := some f) hg, Except.map]
    | none => simp [udGet, udContains, mem_of_get?_none hg, hg]
  · intro hm
    have hs : (D.get? u.data k).isSome = true := hm
    obtain ⟨y, hg⟩ := Option.isSome_iff_exists.mp hs
    have h1 := udGetitem_some (rk := rk) (miss := some f) hg
    refine ⟨?_, ?_, ?_⟩
    · simp [udPop, h1, udDelitem, hm, dictPop, hg, bind, Except.bind, pure, Except.pure, Except.map]
    · simp [udSetdefault, h1, dictSetdefault, hg]
    · simp [udItemsContains, h1, dictItemsContains, hg]

/-- `|`, `|=` agree with `dict`'s, keep the class, and treat `UserDict` and `dict`
operands alike; anything else is `NotImplemented`. `fromkeys` matches `dict.fromkeys`
and `UserDict(src, **kw)` matches `dict(src, **kw)`. `copy()` and `copy.copy` keep
the items, in order, and the class, on `UserDict` and on subclasses alike. -/
def UserDictConstructorsUnion : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] (u : UD κ ν) (o : D κ ν) (src : Option (D κ ν)) (kw : D κ ν)
    (cls : String) (it : List κ) (v : ν), WF u.data → WF o →
    udOr u (.dict o) = some ⟨u.cls, D.or_ u.data o⟩ ∧
    udOr u (.user o) = some ⟨u.cls, D.or_ u.data o⟩ ∧
    udRor u (.dict o) = some ⟨u.cls, D.or_ o u.data⟩ ∧
    udRor u (.user o) = some ⟨u.cls, D.or_ o u.data⟩ ∧
    udOr u .other = none ∧ udRor u .other = none ∧
    udIor u o = ⟨u.cls, D.or_ u.data o⟩ ∧
    (udFromkeys cls it v).data = D.fromkeys it v ∧
    (udNew cls src kw).data = D.update (D.update [] (src.getD [])) kw ∧
    udCopy u = u ∧ udCopyDunder u = u

theorem data_fromkeys (cls : String) (v : ν) (it : List κ) (d : D κ ν) :
    (it.foldl (fun d k => udSetitem d k v) (⟨cls, d⟩ : UD κ ν)) =
      ⟨cls, it.foldl (fun d x => D.set d x v) d⟩ := by
  induction it generalizing d with
  | nil => rfl
  | cons a t ih => exact ih _

theorem userDictConstructorsUnion_proven : UserDictConstructorsUnion := by
  intro κ ν _ u o src kw cls it v hu ho
  have hor1 : WF (D.or_ u.data o) := WF_update hu o
  have hor2 : WF (D.or_ o u.data) := WF_update ho u.data
  have hd : udCopyDunder u = u := by
    cases u with
    | mk c d => simp only [udCopyDunder]; congr 1; exact update_nil_WF hu
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl, ?_, ?_, ?_, hd⟩
  · simp [udOr, udNew_some hor1]
  · simp [udOr, udNew_some hor1]
  · simp [udRor, udNew_some hor2]
  · simp [udRor, udNew_some hor2]
  · simp [udFromkeys, data_fromkeys, D.fromkeys]
  · cases src <;> cases kw <;> simp [udNew, udUpdate, D.update]
  · unfold udCopy
    split
    · next h =>
      cases u with
      | mk c d =>
        simp only at h
        subst h
        exact udNew_some hu
    · cases u with
      | mk c d =>
        simp only [udUpdate, udCopyDunder]
        simp only at hu
        simp [D.update]
        exact update_nil_WF hu

/-- `MutableMapping.clear` on a `UserDict`: looping `popitem` empties it, on every
`UserDict` and for any `__missing__`. `repr(UserDict(d)) == repr(d)`. -/
def UserDictClearRepr : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] (rk : κ → String) (rv : ν → String) (miss : Option (κ → ν))
    (u : UD κ ν) (s : D κ ν), WF u.data → WF s →
    (udClear rk miss u).data = [] ∧ (udClear rk miss u).cls = u.cls ∧
    udRepr rk rv (udNew u.cls (some s) []) = reprD rk rv s

theorem clearLoop_nil (rk : κ → String) (miss : Option (κ → ν)) :
    ∀ (n : Nat) (u : UD κ ν), WF u.data → u.data.length < n →
      (udClearLoop rk miss n u).data = [] ∧ (udClearLoop rk miss n u).cls = u.cls := by
  intro n
  induction n with
  | zero => intro u _ h; simp at h
  | succ n ih =>
    intro u hw hl
    cases u with
    | mk c d =>
      cases d with
      | nil => simp [udClearLoop, udPopitem, udIter]
      | cons p t =>
        obtain ⟨a, b⟩ := p
        have hw' : WF ((a, b) :: t) := hw
        have hpi : udPopitem rk miss ⟨c, (a, b) :: t⟩ = .ok ((a, b), ⟨c, t⟩) := by
          simp [udPopitem, udIter, udGetitem, udDelitem, D.mem, D.get?, D.keys, D.del,
            bind, Except.bind, pure, Except.pure]
        simp only [udClearLoop, hpi]
        have hlt : t.length < n := by simpa using hl
        exact ih ⟨c, t⟩ (WF_of_cons hw') hlt

theorem userDictClearRepr_proven : UserDictClearRepr := by
  intro κ ν _ rk rv miss u s hu hs
  have := clearLoop_nil rk miss (u.data.length + 1) u hu (by omega)
  refine ⟨this.1, this.2, ?_⟩
  simp [udRepr, udNew_some hs]

end PyLean.CoreLibs.Coll
