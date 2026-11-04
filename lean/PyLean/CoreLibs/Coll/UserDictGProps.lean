import PyLean.CoreLibs.Coll.UserDictG
import PyLean.CoreLibs.Coll.CounterProps3

/-!
Properties of `UserDictG.lean`: the constructor, `__getitem__` and `__contains__`, key order,
`__repr__`, `__ior__`, `__copy__` and `copy`, `fromkeys`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace PyLean.CoreLibs.Coll

open PyLean

variable {κ ν : Type} [DecidableEq κ]

/-! ### Helpers -/

theorem loopS_append {σ α : Type} (f : σ → α → Py σ) (s : σ) (l1 l2 : List α) :
    loopS f s (l1 ++ l2) = (match loopS f s l1 with
      | (s', none) => loopS f s' l2
      | r => r) := by
  induction l1 generalizing s with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, loopS]
    cases f s x with
    | ok s' => exact ih s'
    | error e => rfl

theorem loop_keys_update (K : KOps κ) (g : κ → Py ν) :
    ∀ (l s : D κ ν), HashOk K l → (∀ q ∈ l, g q.1 = .ok q.2) →
      loopS (fun s k => do let v ← g k; dSet K s k v) s (D.keys l) = (D.update s l, none)
  | [], s, _, _ => rfl
  | p :: l, s, hh, hg => by
    show loopS _ s (p.1 :: D.keys l) = _
    simp only [loopS, hg p (by simp), ok_bind, dSet_ok s p.2 (hh p.1 (by simp [D.keys]))]
    exact loop_keys_update K g l _ (fun k hk => hh k (by simp [D.keys] at hk ⊢; exact Or.inr hk))
      (fun q hq => hg q (by simp [hq]))

theorem loop_pairs_update (K : KOps κ) :
    ∀ (l s : D κ ν), HashOk K l →
      loopS (fun s (p : Py (κ × ν)) => do let (k, v) ← p; dSet K s k v) s (l.map .ok) = (D.update s l, none)
  | [], s, _ => rfl
  | p :: l, s, hh => by
    simp only [List.map_cons, loopS, ok_bind, dSet_ok s p.2 (hh p.1 (by simp [D.keys]))]
    exact loop_pairs_update K l _ (fun k hk => hh k (by simp [D.keys] at hk ⊢; exact Or.inr hk))

theorem dictUSrc_update (K : KOps κ) (d s : D κ ν) (hw : D.WF d) (hh : HashOk K d) :
    udUpdateP K s (dictUSrc d) = (D.update s d, none) := by
  show forIt _ s (FIt.ofList (D.keys d)) = _
  simp only [forIt, FIt.ofList]
  rw [loop_keys_update K _ d s hh (fun q hq => by simp [D.get?_of_mem_pair hw hq])]

/-! ### `__init__` -/

/-- **`UserDict(src, **kwargs)` is `dict(src, **kwargs)`, and its argument may fail.** For every
key and value type with hashable keys: a `dict` argument and an iterable of the same pairs give
the items of `dict(src, **kwargs)`; no argument gives the keywords' dict; an argument whose
`iter()` raises, an iterable whose item fails to unpack (or whose `next()` raises) after valid
pairs, and a `Mapping` whose `[]` raises, each make the constructor raise that exception.

Source: Doc/library/collections.rst, UserDict ('initialized with the contents of the optional
initialdata'); Lib/collections/__init__.py:1177-1182 and Lib/_collections_abc.py:965-984. -/
def UserDictInitP : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] (K : KOps κ) (d kw : D κ ν) (e : PyExc),
    D.WF d → D.WF kw → HashOk K d → HashOk K kw →
    udNewP K (some (dictUSrc d)) kw = .ok (D.update (D.update [] d) kw) ∧
    udNewP K (some (.pairs (.ok (FIt.ofList (d.map .ok))))) kw = .ok (D.update (D.update [] d) kw) ∧
    udNewP K none kw = .ok (D.update [] kw) ∧
    udNewP K (some (.pairs (.error e))) kw = .error e ∧
    udNewP K (some (.pairs (.ok ⟨d.map .ok ++ [.error e], none⟩))) kw = .error e ∧
    udNewP K (some (.pairs (.ok ⟨d.map .ok, some e⟩))) kw = .error e ∧
    (d ≠ [] → udNewP K (some (.mapping (.ok (FIt.ofList (D.keys d))) (fun _ => .error e))) kw = .error e)

theorem kw_step (K : KOps κ) (kw : D κ ν) (hw : D.WF kw) (hh : HashOk K kw) (s : D κ ν) :
    (if kw.isEmpty then (s, none) else udUpdateP K s (dictUSrc kw)) = (D.update s kw, none) := by
  cases kw with
  | nil => rfl
  | cons p t => simp only [List.isEmpty_cons, Bool.false_eq_true, if_false]; exact dictUSrc_update K _ s hw hh

theorem userDictInitP_proven : UserDictInitP := by
  intro κ ν _ K d kw e hd hkw hhd hhkw
  have hk := kw_step K kw hkw hhkw
  refine ⟨?_, ?_, ?_, rfl, ?_, ?_, fun hne => ?_⟩
  · simp only [udNewP, dictUSrc_update K d [] hd hhd, Out.andThen, hk, Out.toPy]
  · have h1 : udUpdateP K [] (.pairs (.ok (FIt.ofList (d.map .ok)))) = (D.update [] d, none) := by
      simp only [udUpdateP, forPy, forIt, FIt.ofList, loop_pairs_update K d [] hhd]
    simp only [udNewP, h1, Out.andThen, hk, Out.toPy]
  · simp only [udNewP, Out.andThen, hk, Out.toPy]
  · simp only [udNewP, udUpdateP, forPy, forIt, loopS_append, loop_pairs_update K d [] hhd]
    rfl
  · simp only [udNewP, udUpdateP, forPy, forIt, loop_pairs_update K d [] hhd]
    rfl
  · cases d with
    | nil => exact absurd rfl hne
    | cons p t => rfl

/-! ### `__getitem__`, `__contains__` -/

/-- **`__getitem__` with a `__missing__` that is Python code; `in` never calls it.** For every
key: a present key gives its value, whatever `__missing__` is; an absent key gives
`KeyError(key)` without `__missing__`, and otherwise exactly what `__missing__` returns or
raises (a raised exception, `KeyError` or not, propagates); with a returning `__missing__` this
is the pure model of `UserDict.lean`. `key in u` is `key in u.data`: false for an absent key
even when `u[key]` succeeds through `__missing__`. An unhashable key raises the dict's
exception from both.

Source: Lib/collections/__init__.py:1188-1193, :1204-1207 (comment 'Modify __contains__ and
get() to work like dict does when __missing__ is present'). -/
def UserDictGetitemP : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] (K : KOps κ) (rk : κ → String) (u : UD κ ν) (k : κ),
    (K.hash k = .ok () →
      (∀ miss v, D.get? u.data k = some v → udGetitemP K rk miss u k = .ok v) ∧
      (k ∉ D.keys u.data → udGetitemP K rk none u k = .error (.keyError (rk k))) ∧
      (∀ f : κ → Py ν, k ∉ D.keys u.data → udGetitemP K rk (some f) u k = f k ∧
        udContainsP K u k = .ok false) ∧
      (∀ m : Option (κ → ν), udGetitemP K rk (m.map (fun f k => .ok (f k))) u k = udGetitem rk m u k) ∧
      udContainsP K u k = .ok (udContains u k)) ∧
    (∀ x, K.hash k = .error x → ∀ miss, ∃ y, udGetitemP K rk miss u k = .error y ∧ udContainsP K u k = .error y)

theorem userDictGetitemP_proven : UserDictGetitemP := by
  intro κ ν _ K rk u k
  refine ⟨fun hk => ⟨fun miss v hv => ?_, fun hn => ?_, fun f hn => ⟨?_, ?_⟩, fun m => ?_, ?_⟩, fun x hx miss => ?_⟩
  · have hm : D.mem u.data k = true := by simp [D.mem, hv]
    simp [udGetitemP, dMem_ok u.data hk, hm, hv]
  · simp [udGetitemP, dMem_ok u.data hk, D.mem_false_iff.2 hn]
  · simp [udGetitemP, dMem_ok u.data hk, D.mem_false_iff.2 hn]
  · simp [udContainsP, dMem_ok u.data hk, D.mem_false_iff.2 hn]
  · cases m <;> simp [udGetitemP, udGetitem, dMem_ok u.data hk] <;> split <;> rfl
  · simp [udContainsP, udContains, dMem_ok u.data hk]
  · have : ∃ y, dHash K k = .error y := by
      unfold dHash; rw [hx]; cases x <;> simp
    obtain ⟨y, hy⟩ := this
    exact ⟨y, by simp [udGetitemP, dMem, hy], by simp [udContainsP, dMem, hy]⟩

/-! ### Key order -/

theorem keys_del (d : D κ ν) (k : κ) : D.keys (D.del d k) = (D.keys d).erase k := by
  induction d with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    by_cases h : a = k
    · subst h; simp [D.del, D.keys]
    · simp only [D.del, h, if_false, D.keys_cons, List.erase_cons]
      simp [h, ih]

/-- **`iter(u)` yields the keys in insertion order.** For every `UserDict`: `u[k] = v` keeps a
present key in its place and appends a new one at the end, and `del u[k]` removes `k` from the
order, the others keeping theirs.

Source: Doc/library/stdtypes.rst, dict ('Dictionaries preserve insertion order'), and
Lib/collections/__init__.py:1201-1202. -/
def UserDictIterOrder : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] (rk : κ → String) (u : UD κ ν) (k : κ) (v : ν),
    udIter (udSetitem u k v) = (if k ∈ udIter u then udIter u else udIter u ++ [k]) ∧
    (∀ u', udDelitem rk u k = .ok u' → udIter u' = (udIter u).erase k)

theorem userDictIterOrder_proven : UserDictIterOrder := by
  intro κ ν _ rk u k v
  refine ⟨D.keys_set u.data k v, fun u' h => ?_⟩
  unfold udDelitem at h
  split at h
  · cases h; exact keys_del u.data k
  · cases h

/-! ### `__repr__` -/

theorem mapM_plain (rk : κ → Py String) (rv : ν → Py String) (g : κ × VRef ν → Py String)
    (hg : ∀ p : κ × ν, g (p.1, .plain p.2) = (do let a ← rk p.1; let b ← rv p.2; pure (a ++ ": " ++ b))) :
    ∀ d : D κ ν, (d.map (fun p => (p.1, VRef.plain p.2))).mapM g =
      d.mapM (fun p => do let a ← rk p.1; let b ← rv p.2; pure (a ++ ": " ++ b))
  | [] => rfl
  | p :: t => by
    simp only [List.map_cons, List.mapM_cons, hg p]
    rw [mapM_plain rk rv g hg t]

/-- **`repr(u)` is `repr(u.data)`, with the dict's recursion guard.** For every `repr` of keys
and values (free to raise): a `UserDict` whose values are no `UserDict` prints as its dict
(`reprDict`, which for returning reprs is the `reprD` of `UserDict.lean`); one that holds itself
as a value prints `{...}` there; and a key whose `repr` raises makes the `repr` raise.

Source: Lib/collections/__init__.py:1216-1217; Objects/dictobject.c:3647-3650. -/
def UserDictReprR : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] (rk : κ → Py String) (rv : ν → Py String)
    (heap : Nat → Option (D κ (VRef ν))) (i fuel : Nat),
    (∀ d : D κ ν, heap i = some (d.map (fun p => (p.1, .plain p.2))) →
      udReprR rk rv heap (fuel + 1) [] i = reprDict rk rv d) ∧
    (∀ k : κ, heap i = some [(k, .ud i)] →
      udReprR rk rv heap (fuel + 2) [] i = (do let a ← rk k; pure ("{" ++ ", ".intercalate [a ++ ": " ++ "{...}"] ++ "}"))) ∧
    (∀ (k : κ) (w : VRef ν) (rest : D κ (VRef ν)) (e : PyExc), heap i = some ((k, w) :: rest) → rk k = .error e →
      udReprR rk rv heap (fuel + 1) [] i = .error e) ∧
    (∀ (rk' : κ → String) (rv' : ν → String) (d : D κ ν),
      reprDict (fun k => .ok (rk' k)) (fun v => .ok (rv' v)) d = .ok (reprD rk' rv' d))

theorem userDictReprR_proven : UserDictReprR := by
  intro κ ν _ rk rv heap i fuel
  refine ⟨fun d hh => ?_, fun k hh => ?_, fun k w rest e hh he => ?_, fun rk' rv' d => ?_⟩
  · simp only [udReprR, List.not_mem_nil, if_false, hh]
    rw [mapM_plain rk rv _ (fun p => rfl) d]
    rfl
  · simp only [udReprR, List.not_mem_nil, if_false, hh, List.mapM_cons, List.mapM_nil, List.mem_cons,
      true_or, if_true]
    cases rk k <;> rfl
  · simp only [udReprR, List.not_mem_nil, if_false, hh, List.mapM_cons, he]
    rfl
  · have : ∀ l : D κ ν, l.mapM (fun p => (do
        let a ← (Except.ok (rk' p.1) : Py String)
        let b ← (Except.ok (rv' p.2) : Py String)
        pure (a ++ ": " ++ b))) = .ok (l.map (fun p => rk' p.1 ++ ": " ++ rv' p.2)) := by
      intro l
      induction l with
      | nil => rfl
      | cons a t ih => rw [List.mapM_cons, ih]; rfl
    unfold reprDict
    rw [this]
    rfl

/-! ### `__ior__` -/

/-- **`u |= other` merges `other`'s items into `u.data`, from either branch.** For every
`UserDict` and hashable items: a `UserDict` operand (`other.data`) and any other operand yielding
the same items give the same result, `u.data | items` in `u`'s class; an operand `dict |=`
rejects (a non-iterable's `TypeError`) raises with `u` unchanged; one that fails after some pairs
raises with those pairs already merged.

Source: PEP 584; Lib/collections/__init__.py:1233-1238. -/
def UserDictIorP : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] (K : KOps κ) (u : UD κ ν) (d : D κ ν) (e : PyExc), HashOk K d →
    udIorP K u (.user d) = (⟨u.cls, D.update u.data d⟩, none) ∧
    udIorP K u (.other (.ok (FIt.ofList d))) = (⟨u.cls, D.update u.data d⟩, none) ∧
    udIorP K u (.other (.error e)) = (u, some e) ∧
    udIorP K u (.other (.ok ⟨d, some e⟩)) = (⟨u.cls, D.update u.data d⟩, some e)

theorem userDictIorP_proven : UserDictIorP := by
  intro κ ν _ K u d e hh
  have hl := loopS_pure (g := fun s (p : κ × ν) => D.set s p.1 p.2) (f := fun s p => dSet K s p.1 p.2) d u.data
    (fun s p hp => dSet_ok s p.2 (hash_of_mem hh hp))
  refine ⟨rfl, ?_, rfl, ?_⟩
  · simp only [udIorP, forPy, forIt, FIt.ofList, hl]; rfl
  · simp only [udIorP, forPy, forIt, hl]; rfl

/-! ### `__copy__`, `copy` -/

/-- **`copy.copy(u)` and `u.copy()` make new objects of `u`'s class, and `copy` restores
`u.data` when copying fails.** For every `UserDict` object with a dict as `data`: `__copy__`
gives the new object `fresh` of `u`'s class with `u`'s other attributes and a new dict of `u`'s
items; `copy()` on `UserDict` itself gives the new `UserDict` `fresh` with `u`'s items; on a
subclass whose `__copy__` is `UserDict`'s, a new object of `u`'s class with `u`'s attributes and
items; on a subclass whose `copy.copy` raises, that exception, with `u` left as it was (the
`try`/`finally` of :1251-1255 puts `data` back).

Source: docstring of `copy` ('Return a shallow copy', Doc/library/collections.rst) and
Lib/collections/__init__.py:1240-1257. -/
def UserDictCopyO : Prop :=
  ∀ (κ ν α : Type) [DecidableEq κ] (K : KOps κ) (copyFn : UDO κ ν α → Py (UDO κ ν α)) (fresh : Nat)
    (u : UDO κ ν α) (e : PyExc), D.WF u.data → HashOk K u.data →
    udCopyDunderO fresh u = ⟨fresh, u.cls, u.data, u.attrs⟩ ∧
    (u.cls = "UserDict" → udCopyO K copyFn fresh u = (u, .ok ⟨fresh, "UserDict", u.data, []⟩)) ∧
    (u.cls ≠ "UserDict" →
      udCopyO K (fun t => .ok (udCopyDunderO fresh t)) fresh u = (u, .ok ⟨fresh, u.cls, u.data, u.attrs⟩)) ∧
    (u.cls ≠ "UserDict" → udCopyO K (fun _ => .error e) fresh u = (u, .error e))

theorem userDictCopyO_proven : UserDictCopyO := by
  intro κ ν α _ K copyFn fresh u e hw hh
  have hu := update_nil_WF hw
  refine ⟨by simp [udCopyDunderO, hu], fun hc => ?_, fun hc => ?_, fun hc => ?_⟩
  · simp [udCopyO, hc, hu]
  · simp only [udCopyO, hc, if_false, udCopyDunderO]
    rw [dictUSrc_update K u.data _ hw hh]
    have h0 : D.update ([] : D κ ν) [] = [] := rfl
    simp only [Out.toPy, h0, hu]
    rfl
  · simp [udCopyO, hc]

/-! ### `fromkeys` -/

/-- **`fromkeys` builds an object of `cls` from a fallible iterable.** For every key type with
hashable keys: `cls.fromkeys(xs, v)` on an iterator yielding `xs` is the `cls` instance with
`dict.fromkeys(xs, v)`'s items; an exception from `iter()` or `next()` propagates.

Source: Lib/collections/__init__.py:1272-1277. -/
def UserDictFromkeysP : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] (K : KOps κ) (cls : String) (xs : List κ) (v : ν) (e : PyExc),
    (∀ k ∈ xs, K.hash k = .ok ()) →
    udFromkeysP K cls (.ok ⟨xs, none⟩) v = .ok ⟨cls, D.fromkeys xs v⟩ ∧
    udFromkeysP K cls (.ok ⟨xs, some e⟩) v = .error e ∧
    udFromkeysP K cls (.error e) v = (.error e : Py (UD κ ν))

theorem userDictFromkeysP_proven : UserDictFromkeysP := by
  intro κ ν _ K cls xs v e hh
  have hl := loopS_pure (g := fun d k => D.set d k v) (f := fun d k => dSet K d k v) xs [] (by
    intro s x hx; exact dSet_ok s v (hh x hx))
  refine ⟨?_, ?_, rfl⟩
  · simp only [udFromkeysP, forPy, forIt, hl]; rfl
  · simp only [udFromkeysP, forPy, forIt, hl]; rfl

end PyLean.CoreLibs.Coll
