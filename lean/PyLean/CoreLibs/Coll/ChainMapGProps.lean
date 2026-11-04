import PyLean.CoreLibs.Coll.ChainMapG
import PyLean.CoreLibs.Coll.ChainMapProps
import PyLean.CoreLibs.Coll.CounterProps2

/-!
Properties of `ChainMapG.lean`: `__init__`, `__getitem__` over any mappings, the `__repr__`
guard, `fromkeys`, and the object-level `copy`, `__or__`, `__ior__`, `clear`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace PyLean.CoreLibs.Coll

open PyLean
open PyLean.Accel.Heapq (Hier isA builtinHier)

variable {κ ν : Type} [DecidableEq κ]

/-- **`ChainMap()` holds exactly one empty dict; otherwise `maps` is the arguments.**

Source: docstring, Lib/collections/__init__.py:1055-1057 ('If no mappings are provided, a
single empty dictionary is used'). -/
def ChainMapInit : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] (l : List (D κ ν)),
    (cmNew ([] : List (D κ ν))).maps = [[]] ∧ (l ≠ [] → (cmNew l).maps = l)

theorem chainMapInit_proven : ChainMapInit := by
  intro κ ν _ l
  refine ⟨rfl, fun h => ?_⟩
  cases l with
  | nil => exact absurd rfl h
  | cons a t => rfl

/-- **`__getitem__` asks each mapping's `[]`, and only a `KeyError` moves on.** For every key
and value type and every exception-class relation: on plain dicts it is the flat lookup of
`ChainMapFlatView`; a map whose `m[key]` returns answers (a `defaultdict` answers for a key it
does not hold, while `key in cm` is false and a later map holds the key); a `KeyError` or a
subclass moves on to the next map; any other exception propagates without consulting later
maps.

Source: Doc/library/collections.rst, ChainMap ('Lookups search the underlying mappings
successively'), and the comment at Lib/collections/__init__.py:1067 ("can't use 'key in
mapping' with defaultdict"). -/
def ChainMapGetitemAny : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] (H : Hier) (rk : κ → String) (miss : κ → Py ν) (k : κ),
    (∀ maps : List (D κ ν), cmGetitemG builtinHier miss (maps.map (dictG rk)) k = cmGetitem miss ⟨maps⟩ k) ∧
    (∀ (m : GMap κ ν) (t : List (GMap κ ν)),
      (∀ v, m.getitem k = .ok v → cmGetitemG H miss (m :: t) k = .ok v) ∧
      (∀ e, m.getitem k = .error e → isA H e "KeyError" = true →
        cmGetitemG H miss (m :: t) k = cmGetitemG H miss t k) ∧
      (∀ e, m.getitem k = .error e → isA H e "KeyError" = false →
        cmGetitemG H miss (m :: t) k = .error e)) ∧
    (∀ (d : D κ ν) (v w : ν) (rest : List (D κ ν)), k ∉ D.keys d → (∀ m ∈ rest, k ∉ D.keys m) →
      cmGetitemG H miss (defaultG d (.ok v) :: dictG rk [(k, w)] :: rest.map (dictG rk)) k = .ok v ∧
      cmContainsG (defaultG d (.ok v) :: rest.map (dictG rk)) k = .ok false)

theorem cmGetitemG_dict (rk : κ → String) (miss : κ → Py ν) (k : κ) :
    ∀ maps : List (D κ ν), cmGetitemG builtinHier miss (maps.map (dictG rk)) k = cmGetitem miss ⟨maps⟩ k
  | [] => rfl
  | m :: t => by
    have ih := cmGetitemG_dict rk miss k t
    simp only [List.map_cons, cmGetitemG, dictG]
    cases hm : D.get? m k with
    | some v => simp [cmGetitem, cmLookup, hm]
    | none =>
      have hk : isA builtinHier (.keyError (rk k)) "KeyError" = true := rfl
      simp only [hk, if_true, ih]
      simp [cmGetitem, cmLookup, hm]

theorem cmContainsG_absent (rk : κ → String) (k : κ) :
    ∀ rest : List (D κ ν), (∀ m ∈ rest, k ∉ D.keys m) → cmContainsG (rest.map (dictG rk)) k = .ok false
  | [], _ => rfl
  | m :: t, h => by
    simp only [List.map_cons, cmContainsG, dictG]
    rw [D.mem_false_iff.2 (h m (by simp))]
    exact cmContainsG_absent rk k t (fun m' hm' => h m' (by simp [hm']))

theorem chainMapGetitemAny_proven : ChainMapGetitemAny := by
  intro κ ν _ H rk miss k
  refine ⟨cmGetitemG_dict rk miss k, fun m t => ⟨?_, ?_, ?_⟩, fun d v w rest hd hr => ⟨?_, ?_⟩⟩
  · intro v hv; simp [cmGetitemG, hv]
  · intro e he hk; simp [cmGetitemG, he, hk]
  · intro e he hk; simp [cmGetitemG, he, hk]
  · simp [cmGetitemG, defaultG, (D.get?_eq_none_iff).2 hd]
  · simp only [cmContainsG, defaultG, D.mem_false_iff.2 hd]
    exact cmContainsG_absent rk k rest hr

/-- **The `recursive_repr` guard.** For every `repr` of dicts (free to raise): a `ChainMap` whose
`maps` holds only dicts prints `Cls(r1, r2, ...)` with the dicts' reprs, which on `reprD` is the
`cmRepr` of `ChainMapRepr`; one whose `maps` holds itself after a dict prints `Cls(r, ...)`; and
a dict whose `repr` raises makes the whole `repr` raise.

Source: Lib/collections/__init__.py:1093 (`@_recursive_repr()`) and Lib/reprlib.py:9-24. -/
def ChainMapReprGuard : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] (rd : D κ ν → Py String) (heap : Nat → Option (String × List (MRef κ ν)))
    (cls : String) (i fuel : Nat),
    (∀ maps : List (D κ ν), heap i = some (cls, maps.map .dict) →
      cmReprR rd heap (fuel + 1) [] i = (do
        let parts ← maps.mapM rd
        pure (cls ++ "(" ++ ", ".intercalate parts ++ ")"))) ∧
    (∀ (rk : κ → String) (rv : ν → String) (maps : List (D κ ν)), heap i = some (cls, maps.map .dict) →
      rd = (fun d => .ok (reprD rk rv d)) → cmReprR rd heap (fuel + 1) [] i = .ok (cmRepr cls rk rv ⟨maps⟩)) ∧
    (∀ d : D κ ν, heap i = some (cls, [.dict d, .chain i]) →
      cmReprR rd heap (fuel + 2) [] i = (do let s ← rd d; pure (cls ++ "(" ++ ", ".intercalate [s, "..."] ++ ")"))) ∧
    (∀ (d : D κ ν) (rest : List (MRef κ ν)) (e : PyExc), heap i = some (cls, .dict d :: rest) →
      rd d = .error e → cmReprR rd heap (fuel + 1) [] i = .error e)

theorem mapM_dict (rd : D κ ν → Py String) (g : MRef κ ν → Py String) (hg : ∀ d, g (.dict d) = rd d) :
    ∀ maps : List (D κ ν), (maps.map MRef.dict).mapM g = maps.mapM rd
  | [] => rfl
  | d :: t => by
    simp only [List.map_cons, List.mapM_cons, hg]
    rw [mapM_dict rd g hg t]

theorem chainMapReprGuard_proven : ChainMapReprGuard := by
  intro κ ν _ rd heap cls i fuel
  have h1 : ∀ maps : List (D κ ν), heap i = some (cls, maps.map .dict) →
      cmReprR rd heap (fuel + 1) [] i = (do
        let parts ← maps.mapM rd
        pure (cls ++ "(" ++ ", ".intercalate parts ++ ")")) := by
    intro maps hh
    simp only [cmReprR, List.not_mem_nil, if_false, hh]
    rw [mapM_dict rd _ (fun _ => rfl) maps]
  refine ⟨h1, fun rk rv maps hh hrd => ?_, fun d hh => ?_, fun d rest e hh he => ?_⟩
  · rw [h1 maps hh, hrd]
    have : ∀ l : List (D κ ν), l.mapM (fun d => (Except.ok (reprD rk rv d) : Py String)) = .ok (l.map (reprD rk rv)) := by
      intro l
      induction l with
      | nil => rfl
      | cons a t ih => simp [List.mapM_cons, ih]
    rw [this]
    rfl
  · simp only [cmReprR, List.not_mem_nil, if_false, hh, List.mapM_cons, List.mem_cons, true_or, if_true,
      List.mapM_nil]
    cases rd d <;> rfl
  · simp only [cmReprR, List.not_mem_nil, if_false, hh, List.mapM_cons, he]
    rfl

/-- **`fromkeys` builds exactly one map.** For every key type with hashable keys and every
value: on an iterator yielding `xs` and stopping, `ChainMap.fromkeys(xs, v)` has the single map
`dict.fromkeys(xs, v)`; an exception from `iter()` or `next()` propagates and no `ChainMap` is
made.

Source: docstring, Lib/collections/__init__.py:1099 ('Create a new ChainMap with keys from
iterable'). -/
def ChainMapFromkeys : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] (K : KOps κ) (xs : List κ) (v : ν) (e : PyExc), (∀ k ∈ xs, K.hash k = .ok ()) →
    cmFromkeysP K (.ok ⟨xs, none⟩) v = .ok ⟨[D.fromkeys xs v]⟩ ∧
    cmFromkeysP K (.ok ⟨xs, some e⟩) v = .error e ∧
    cmFromkeysP K (.error e) v = (.error e : Py (CMap κ ν))

theorem chainMapFromkeys_proven : ChainMapFromkeys := by
  intro κ ν _ K xs v e hh
  have hl := loopS_pure (g := fun d k => D.set d k v) (f := fun d k => dSet K d k v) xs [] (by
    intro s x hx; exact dSet_ok s v (hh x hx))
  refine ⟨?_, ?_, rfl⟩
  · simp only [cmFromkeysP, forPy, forIt, hl]
    rfl
  · simp only [cmFromkeysP, forPy, forIt, hl]
    rfl

/-- **`copy`, `|`, `|=` and `clear` on objects.** For every `ChainMap` with a first map `m`
(a dict, so with distinct keys) of id `i` and later maps `t`:
`copy()` is the new object `fresh` whose first map is the new dict `fresh0` with `m`'s items and
whose later maps are `t`'s very objects; `cm | o` (a `Mapping`) is such a copy with `m | o` in
the new dict, so `self.maps[0]` is not the dict written, and a non-`Mapping` gets
`NotImplemented`; `cm |= o` returns `self` (same id) with the same dict object `i` updated in
place and `maps[1:]` untouched, and an `other` that `dict.update` rejects raises its exception;
`clear()` empties `maps[0]` in place, after which every key reads from the later maps; an empty
`maps` raises `IndexError` in all four.

Source: docstrings, Lib/collections/__init__.py:1103 ('New ChainMap or subclass with a new copy
of maps[0] and refs to maps[1:]') and :1148 ('Clear maps[0], leaving maps[1:] intact'); PEP 584. -/
def ChainMapObjects : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] (K : KOps κ) (id i fresh fresh0 : Nat) (m : D κ ν) (t : List (Nat × D κ ν))
    (o : D κ ν) (e : PyExc), D.WF m → HashOk K o →
    let c : CMapO κ ν := ⟨id, (i, m) :: t⟩
    cmCopyO fresh fresh0 c = .ok ⟨fresh, (fresh0, m) :: t⟩ ∧
    cmOrO K fresh fresh0 c (some (.ok (FIt.ofList o))) = some (.ok ⟨fresh, (fresh0, D.update m o) :: t⟩) ∧
    cmOrO K fresh fresh0 c (some (.ok ⟨o, some e⟩)) = some (.error e) ∧
    cmOrO K fresh fresh0 c none = none ∧
    cmIorO K c (.ok (FIt.ofList o)) = (⟨id, (i, D.update m o) :: t⟩, none) ∧
    cmIorO K c (.error e) = (c, some e) ∧
    cmIorO K c (.ok ⟨o, some e⟩) = (⟨id, (i, D.update m o) :: t⟩, some e) ∧
    (∃ r, cmClearO c = .ok r ∧ r.id = id ∧ r.maps = (i, []) :: t ∧
      ∀ k, cmLookup r.view k = cmLookup (t.map (·.2)) k) ∧
    (∀ (c' : CMapO κ ν), c'.maps = [] →
      cmCopyO fresh fresh0 c' = .error noMap ∧ cmIorO K c' (.ok (FIt.ofList o)) = (c', some noMap) ∧
      cmClearO c' = .error noMap)

theorem chainMapObjects_proven : ChainMapObjects := by
  intro κ ν _ K id i fresh fresh0 m t o e hw hh
  simp only
  have hu := update_nil_WF hw
  have hl : ∀ d : D κ ν, loopS (fun d (p : κ × ν) => dSet K d p.1 p.2) d o = (D.update d o, none) :=
    fun d => loopS_pure o d (fun s p hp => dSet_ok s p.2 (hash_of_mem hh hp))
  refine ⟨by simp [cmCopyO, hu], ?_, ?_, rfl, ?_, rfl, ?_,
    ⟨⟨id, (i, []) :: t⟩, rfl, rfl, rfl, fun k => ?_⟩, fun c' hc => ?_⟩
  · simp [cmOrO, cmCopyO, cmIorO, hu, forPy, forIt, FIt.ofList, hl, Out.toPy]
  · simp [cmOrO, cmCopyO, cmIorO, hu, forPy, forIt, hl, Out.toPy]
  · simp [cmIorO, forPy, forIt, FIt.ofList, hl]
  · simp [cmIorO, forPy, forIt, hl]
  · simp [CMapO.view, cmLookup, D.get?]
  · obtain ⟨id', maps'⟩ := c'
    simp only at hc
    subst hc
    exact ⟨rfl, rfl, rfl⟩

/-- **`other | cm` builds `dict(other)` first, and its exception propagates.** For every
`ChainMap`: a `Mapping` `other` whose `dict(other)` gives `o` yields the one-map `ChainMap` of
`ChainMapUnionFlat` (`o` updated from the last map to the first); a `dict(other)` that raises
raises that exception; a non-`Mapping` gets `NotImplemented`.

Source: PEP 584; Lib/collections/__init__.py:1162-1168. -/
def ChainMapRorP : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] (c : CMap κ ν) (o : D κ ν) (e : PyExc),
    cmRorP c (some (.ok o)) = (cmRor c (some o)).map .ok ∧
    cmRorP c (some (.error e)) = some (.error e) ∧
    cmRorP c none = none

theorem chainMapRorP_proven : ChainMapRorP := fun _ _ _ _ _ _ => ⟨rfl, rfl, rfl⟩

end PyLean.CoreLibs.Coll
