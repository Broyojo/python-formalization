import PyLean.DictSet.Props315

/-!
`dict.fromkeys` and `frozendict.fromkeys` (CPython 3.15.2, `Objects/dictobject.c:3362-3600`).
-/

namespace PyLean.DictSet

open PyLean

variable {K V : Type} [DecidableEq K]

/-- `dict_dict_fromkeys`, for every key protocol: a failed resize is the result; otherwise the loop
starts at position 0, with the iterable in hand (or the dict itself, when `cls()` returned the
iterable). Each turn takes the next item of the iterable as it is now, which a key's `__eq__` may have
changed; a failed `insertdict` is the result in the state it left, and the end of the iterable ends
it. No turn compares the iterable's size with what it was. -/
def DictDictFromkeysBody : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (src mp : PyDict K V) (value : V),
    let alias := src.ident == mp.ident
    let newSize := max (estimateLog2Keysize src.used) mp.body.log2Size
    (∀ e s, dictResize newSize src.body.isUnicode mp = (.error e, s) →
      dictDictFromkeys P src value mp = (.error e, s)) ∧
    (∀ s, dictResize newSize src.body.isUnicode mp = (.ok (), s) →
      dictDictFromkeys P src value mp =
        fromkeysLive P value alias (fromkeysFuel src) 0
          (if alias then s else { s with peer := some src.toPeer })) ∧
    (∀ (fuel : Nat) (pos : Int) (st srcNow : PyDict K V), eqLeft alias st = some srcNow →
      (dictNext srcNow pos = none → fromkeysLive P value alias (fuel + 1) pos st = (.ok (), st)) ∧
      (∀ pos' key v h, dictNext srcNow pos = some (pos', key, v, h) →
        (∀ e s, insertDict P key h value st = (.error e, s) →
          fromkeysLive P value alias (fuel + 1) pos st = (.error e, s)) ∧
        (∀ s, insertDict P key h value st = (.ok (), s) →
          fromkeysLive P value alias (fuel + 1) pos st = fromkeysLive P value alias fuel pos' s)))

theorem dictDictFromkeysBody_proven : DictDictFromkeysBody := by
  intro K V _ P src mp value alias newSize
  refine ⟨fun e s h => ?_, fun s h => ?_, fun fuel pos st srcNow hs => ⟨fun hn => ?_, fun pos' key v hh hn => ⟨fun e s he => ?_, fun s he => ?_⟩⟩⟩
  · simp only [dictDictFromkeys]
    rw [h]
  · simp only [dictDictFromkeys]
    rw [h]
  · simp [fromkeysLive, hs, hn]
  · simp [fromkeysLive, hs, hn, he]
  · simp [fromkeysLive, hs, hn, he]

/-! ### A source that shrinks while `fromkeys` reads it -/

/-- Ints, all hashing to 0 up to 2; `1 == 2` pops the last item of the source and answers no. -/
def popsSrcProto : Proto Nat (PyDict Nat Nat) :=
  { hash := fun k => .ok (if k ≤ 2 then 0 else (k : Int))
    isStr := fun _ => false, isStrLike := fun _ => false, strEq := fun a b => a == b
    reprStr := fun _ => "", repr := fun _ => .ok "", typeName := fun _ => ""
    eq := fun a b s =>
      if a = 1 ∧ b = 2 then
        (.ok false, { s with peer := s.peer.map fun p => (dictPopitem p.toDict).2.toPeer })
      else (.ok (a == b), s) }

def popsSrc : PyDict Nat Nat :=
  (dictSetItem popsSrcProto 3 0 (dictSetItem popsSrcProto 2 0
    (dictSetItem popsSrcProto 1 0 ({ ident := 1 } : PyDict Nat Nat)).2).2).2

/-- `dict.fromkeys(src)` while a key's `__eq__` pops an item of `src`: the call succeeds, and the key
the source held at the start under 3 is not in the result. `dict_dict_merge` has a count test for
this (:4249); `dict_dict_fromkeys` has none. On record, not a bug report: on CPython 3.15.2 the same
program gives a dict of two keys, while `dict.fromkeys(iter(src))` raises `RuntimeError`. -/
def FromkeysShrinkUnseen : Prop :=
  dictKeysList popsSrc = [1, 2, 3] ∧
  (dictDictFromkeys popsSrcProto popsSrc 0 ({ ident := 2 } : PyDict Nat Nat)).1 = .ok () ∧
  dictKeysList (dictDictFromkeys popsSrcProto popsSrc 0 ({ ident := 2 } : PyDict Nat Nat)).2 = [1, 2]

theorem fromkeysShrinkUnseen_proven : FromkeysShrinkUnseen := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-! ### A frozendict that Python code holds is filled again -/

/-- Whether `r`, if it is the object `x` itself, still holds what `x` held. -/
def fkSame [DecidableEq V] (x : FkObj K V) (r : Py (FkObj K V)) : Bool :=
  match r with
  | .ok y => !(y.d.ident == x.d.ident) || decide (dictItems y.d = dictItems x.d)
  | .error _ => true

/-- A frozendict never changes once Python code holds it: if one call of `fromkeys` hands a
frozendict to Python code, and `cls()` of a later call returns that frozendict, the later call does
not change it. Python code holds what `cls()` returns, so this is the immutability of frozendict
(PEP 814). -/
def FromKeysFrozenStable : Prop :=
  ∀ (K V : Type) [DecidableEq K] [DecidableEq V] (P : Proto K (PyDict K V)) (hf : K → Int)
    (eqv : K → K → Bool), Honest P hf eqv →
    ∀ (cls1 : FkCls K V) (it1 : FkIter K V) (v1 : V) (id1 : Nat) (x : FkObj K V),
      x ∈ (dictFromkeysImpl P cls1 it1 v1 id1).2 → x.d.frozen = true →
      ∀ (cls2 : FkCls K V) (it2 : FkIter K V) (v2 : V) (id2 : Nat),
        cls2.isFrozendictType = false → cls2.call = .ok x →
        fkSame x (dictFromkeysImpl P cls2 it2 v2 id2).1 = true

/-- `class F(frozendict)`, whose `__init__` keeps its argument: `F()` is a tracked instance. -/
def fkLeakCls : FkCls Nat Nat :=
  { isFrozendictType := false
    call := .ok { d := { ident := 5, frozen := true }, exact := false }
    callWith := fun _ => .ok { d := { ident := 6, frozen := true }, exact := false }
    setItem := fun _ _ => pure ()
    instMap := .dict {} }

/-- A list of keys, as an iterator that never raises. -/
def fkList (ks : List Nat) : FkIter Nat Nat :=
  { fast := none, iter := { steps := ks.map fun k => pure (some k) } }

/-- The frozendict `F.fromkeys([1, 2])` hands to `F(d)`. -/
def fkLeaked : FkObj Nat Nat := (dictFromkeysImpl intProto fkLeakCls (fkList [1, 2]) 0 10).2.head!

/-- `class G(frozendict)` whose `__new__` returns that frozendict. -/
def fkReuseCls : FkCls Nat Nat := { fkLeakCls with call := .ok fkLeaked }

theorem head!_mem {α : Type} [Inhabited α] (l : List α) (h : l.isEmpty = false) : l.head! ∈ l := by
  cases l with
  | nil => simp at h
  | cons a t => simp [List.head!]

theorem fromKeysFrozenStable_refuted : ¬FromKeysFrozenStable := by
  intro h
  have hne : (dictFromkeysImpl intProto fkLeakCls (fkList [1, 2]) 0 10).2.isEmpty = false := by
    decide +kernel
  have hfz : fkLeaked.d.frozen = true := by decide +kernel
  have := h Nat Nat intProto _ _ intProto_honest fkLeakCls (fkList [1, 2]) 0 10 fkLeaked
    (head!_mem _ hne) hfz fkReuseCls (fkList [3]) 0 20 rfl rfl
  revert this
  decide +kernel

end PyLean.DictSet
