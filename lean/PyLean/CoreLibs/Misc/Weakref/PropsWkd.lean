import PyLean.CoreLibs.Misc.Weakref.PropsDict

/-! Properties of `WeakKeyDictionary` (Lib/weakref.py:298-439). -/

namespace PyLean.CoreLibs.Misc.Weakref

open PyLean

/-- The `TypeError` that `dict_unhashable_type` builds from an exact `TypeError`; anything else
passes through. -/
def renameTE (tn : String) : PyExc → PyExc
  | .typeError m => .typeError s!"cannot use '{tn}' as a dict key ({m})"
  | e => e

theorem unhashable_error (tn : String) (e : PyExc) :
    unhashable tn (.error e) = .error (renameTE tn e) := by
  cases e <;> rfl

namespace WKD

variable {V : Type}

/-- The rule for hashable objects (Doc/reference/datamodel.rst, `object.__hash__`: objects which
compare equal have the same hash value), with an `__eq__` that does not raise and is an
equivalence. -/
structure Hashable (q : ROps) : Prop where
  hash : ∀ a, ∃ h, q.hash a = .ok h
  eq : ∀ a b, ∃ t, q.eq a b = .ok t
  refl : ∀ a, q.eq a a = .ok true
  symm : ∀ a b, q.eq a b = q.eq b a
  trans : ∀ a b c, q.eq a b = .ok true → q.eq b c = .ok true → q.eq a c = .ok true
  hashEq : ∀ a b, q.eq a b = .ok true → q.hash a = q.hash b

/-- Each stored `ref` holds its referent's hash: the type invariant of `data`, since a `ref` is
hashed when it is stored and caches the result. -/
def HashOk (q : ROps) (d : WKD V) : Prop := ∀ kv ∈ d.data, q.hash kv.1.ob = .ok kv.1.hash

/-- `__eq__` as a `Bool`, for an `__eq__` that does not raise. -/
def qb (q : ROps) (a b : Nat) : Bool :=
  match q.eq a b with
  | .ok t => t
  | .error _ => false

theorem qb_of {q : ROps} {a b : Nat} {t : Bool} (h : q.eq a b = .ok t) : qb q a b = t := by
  simp [qb, h]

/-- An entry that a lookup of `a` matches. -/
def pr (q : ROps) (w : World) (a : Nat) (kv : WRef × V) : Bool := alive w kv.1.ob && qb q kv.1.ob a

/-- The value stored for `a`. -/
def valOf (q : ROps) (w : World) (d : WKD V) (a : Nat) : Option V :=
  (d.data.find? (pr q w a)).map (·.2)

theorem find_hashable (q : ROps) (hq : Hashable q) (w : World) (k : Nat) (h : Int)
    (hk : q.hash k = .ok h) : ∀ data : List (WRef × V),
    (∀ kv ∈ data, q.hash kv.1.ob = .ok kv.1.hash) → find q w k h data = .ok (data.find? (pr q w k)) := by
  intro data
  induction data with
  | nil => intro _; rfl
  | cons p rest ih =>
    intro hd
    obtain ⟨r, v⟩ := p
    have ih' := ih (fun kv h' => hd kv (by simp [h']))
    simp only [find, List.find?_cons]
    obtain ⟨t, ht⟩ := hq.eq r.ob k
    by_cases hc : (r.hash == h && alive w r.ob) = true
    · simp only [hc, if_true, ht]
      have hal : alive w r.ob = true := by simp at hc; exact hc.2
      cases t with
      | true => simp [pr, hal, qb_of ht]
      | false => simp [pr, hal, qb_of ht, ih']
    · simp only [hc, Bool.false_eq_true, if_false, ih']
      have : pr q w k (r, v) = false := by
        simp only [pr]
        cases hal : alive w r.ob with
        | false => rfl
        | true =>
          cases t with
          | false => simp [qb_of ht]
          | true =>
            exfalso
            have h1 := hq.hashEq _ _ ht
            rw [hd (r, v) (by simp), hk] at h1
            simp only [Except.ok.injEq] at h1
            simp [h1, hal] at hc
      simp [this]

theorem lookup_hashable (q : ROps) (hq : Hashable q) (w : World) (d : WKD V) (k : Nat)
    (hd : HashOk q d) : ∃ h, q.hash k = .ok h ∧
      lookup q w d (.obj k) = .ok (k, h, d.data.find? (pr q w k)) := by
  obtain ⟨h, hh⟩ := hq.hash k
  refine ⟨h, hh, ?_⟩
  simp [lookup, refOf, hh, unhashable, find_hashable q hq w k h hh d.data hd]

/-- Reads through `ref(key)`. A key that `ref()` refuses: `in` says `False` (the only `TypeError`
`__contains__` catches) and the rest raise. A referent whose `__hash__` raises, such as an
instance of a class with `__eq__` and no `__hash__`: every read raises, `in` included, an exact
`TypeError` renamed by the dict; only `pop` on an empty dict answers without hashing. An `__eq__`
that raises ends the lookup with its exception. For hashable keys the reads report the entry whose
referent compares equal. -/
def WkdLookup : Prop :=
  ∀ (V : Type) (q : ROps) (w : World) (d : WKD V) (k : Nat) (n : Int) (dflt : V) (args : List V),
    (let e : PyExc := .typeError "cannot create weak reference to 'int' object"
     d.contains q w (.int n) = .ok false ∧ d.getitem q w (.int n) = .error e ∧
     d.get q w (.int n) dflt = .error e ∧ d.setitem q w (.int n) dflt = .error e ∧
     d.delitem q w (.int n) = .error e ∧ (d.pop q w (.int n) args).2 = .error e ∧
     (d.setdefault q w (.int n) dflt).2 = .error e) ∧
    (∀ e, q.hash k = .error e →
      let e' := renameTE refTn e
      d.contains q w (.obj k) = .error e' ∧ d.getitem q w (.obj k) = .error e' ∧
      d.get q w (.obj k) dflt = .error e' ∧ d.setitem q w (.obj k) dflt = .error e' ∧
      d.delitem q w (.obj k) = .error e' ∧ (d.setdefault q w (.obj k) dflt).2 = .error e' ∧
      (d.data ≠ [] → args.length ≤ 1 → (d.pop q w (.obj k) args).2 = .error e') ∧
      (d.data = [] → (d.pop q w (.obj k) [dflt]).2 = .ok dflt)) ∧
    (∀ r v rest h e, d.data = (r, v) :: rest → q.hash k = .ok h → r.hash = h → alive w r.ob = true →
      q.eq r.ob k = .error e →
      d.contains q w (.obj k) = .error e ∧ d.getitem q w (.obj k) = .error e ∧
      d.get q w (.obj k) dflt = .error e) ∧
    (Hashable q → HashOk q d →
      (valOf q w d k = none →
        d.getitem q w (.obj k) = .error keyErr ∧ d.contains q w (.obj k) = .ok false ∧
        d.get q w (.obj k) dflt = .ok dflt) ∧
      (∀ v, valOf q w d k = some v →
        d.getitem q w (.obj k) = .ok v ∧ d.contains q w (.obj k) = .ok true ∧
        d.get q w (.obj k) dflt = .ok v))

theorem wkdLookup_proven : WkdLookup := by
  intro V q w d k n dflt args
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro e he
    have hl : lookup q w d (.obj k) = .error (renameTE refTn e) := by
      simp [lookup, refOf, he, unhashable_error]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [contains, refOf, hl]
    · simp [getitem, hl]
    · simp [get, hl]
    · simp [setitem, hl]
    · simp [delitem, hl]
    · simp [setdefault, hl]
    · intro hne ha
      have : ¬ (1 < args.length) := by omega
      have hne' : d.data.isEmpty = false := by
        cases hdd : d.data with
        | nil => exact absurd hdd hne
        | cons _ _ => rfl
      simp [pop, refOf, this, hne', hl]
    · intro he0
      simp [pop, refOf, he0]
  · intro r v rest h e hd hh hr ha he
    have hl : lookup q w d (.obj k) = .error e := by
      simp [lookup, refOf, hh, unhashable, hd, find, hr, ha, he]
    exact ⟨by simp [contains, refOf, hl], by simp [getitem, hl], by simp [get, hl]⟩
  · intro hq hd
    obtain ⟨h, _, hl⟩ := lookup_hashable q hq w d k hd
    constructor
    · intro hv
      have hf : d.data.find? (pr q w k) = none := by simpa [valOf] using hv
      simp [getitem, contains, get, refOf, hl, hf]
    · intro v hv
      simp only [valOf] at hv
      cases hf : d.data.find? (pr q w k) with
      | none => simp [hf] at hv
      | some p =>
        obtain ⟨r, v'⟩ := p
        simp only [hf, Option.map_some, Option.some.injEq] at hv
        subst hv
        simp [getitem, contains, get, refOf, hl, hf]

/-! ### Stores -/

theorem find_map_value {q : ROps} {w : World} (r : WRef) (v0 value : V) (key : Nat) :
    ∀ l : List (WRef × V), l.find? (pr q w key) = some (r, v0) →
      (l.map (fun kv => if kv.1 = r then (r, value) else kv)).find? (pr q w key) = some (r, value) := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons p rest ih =>
    intro h
    obtain ⟨x, y⟩ := p
    simp only [List.find?_cons, List.map_cons] at h ⊢
    by_cases hm : pr q w key (x, y) = true
    · simp only [hm] at h
      have e : x = r := by simpa using (congrArg (fun o => o.map Prod.fst) h)
      subst e
      simp [pr] at hm ⊢
      simp [hm]
    · have hm' : pr q w key (x, y) = false := by simpa using hm
      simp only [hm'] at h
      by_cases e : x = r
      · subst e
        have : pr q w key (x, value) = false := by simpa [pr] using hm'
        simp [this, ih h]
      · simp [e, hm', ih h]

theorem find_append_none {q : ROps} {w : World} (r : WRef) (v : V) (key : Nat) :
    ∀ l : List (WRef × V), l.find? (pr q w key) = none → pr q w key (r, v) = true →
      (l ++ [(r, v)]).find? (pr q w key) = some (r, v) := by
  intro l hl h2
  rw [List.find?_append, hl]
  simp [h2]

/-- For a hashable key, `d[k] = v` stores `storeAt` with the lookup's result. -/
theorem setitem_hashable (q : ROps) (hq : Hashable q) (w : World) (d : WKD V) (k : Nat) (v : V)
    (hd : HashOk q d) : ∃ h, q.hash k = .ok h ∧
      d.setitem q w (.obj k) v = .ok (storeAt d k h (d.data.find? (pr q w k)) v) := by
  obtain ⟨h, hh, hl⟩ := lookup_hashable q hq w d k hd
  exact ⟨h, hh, by simp [setitem, hl]⟩

theorem storeAt_hashOk (q : ROps) (d : WKD V) (k : Nat) (h : Int) (hk : q.hash k = .ok h) (v : V)
    (hd : HashOk q d) : ∀ f, (∀ r x, f = some (r, x) → (r, x) ∈ d.data) → HashOk q (storeAt d k h f v) := by
  intro f hf kv hkv
  cases f with
  | none =>
    simp only [storeAt, List.mem_append, List.mem_singleton] at hkv
    rcases hkv with hkv | rfl
    · exact hd kv hkv
    · exact hk
  | some p =>
    obtain ⟨r, x⟩ := p
    simp only [storeAt, List.mem_map] at hkv
    obtain ⟨a, ha, e⟩ := hkv
    split at e
    · subst e
      rename_i har
      have := hd a ha
      rw [har] at this
      exact this
    · subst e; exact hd a ha

theorem valOf_storeAt_same (q : ROps) (hq : Hashable q) (w : World) (d : WKD V) (k : Nat) (h : Int)
    (v : V) (hk : alive w k = true) :
    valOf q w (storeAt d k h (d.data.find? (pr q w k)) v) k = some v := by
  unfold valOf
  cases hf : d.data.find? (pr q w k) with
  | none =>
    simp only [storeAt]
    rw [find_append_none _ v k _ hf (by simp [pr, hk, qb_of (hq.refl k)])]
    rfl
  | some p =>
    obtain ⟨r, v0⟩ := p
    simp only [storeAt]
    rw [find_map_value r v0 v k _ hf]
    rfl

theorem pr_other {q : ROps} (hq : Hashable q) {w : World} {k a : Nat} (hka : q.eq k a = .ok false)
    (kv : WRef × V) (hr : pr q w k kv = true) : pr q w a kv = false := by
  simp only [pr, Bool.and_eq_true] at hr
  simp only [pr]
  obtain ⟨t, ht⟩ := hq.eq kv.1.ob a
  cases t with
  | false => simp [qb_of ht]
  | true =>
    exfalso
    obtain ⟨t2, ht2⟩ := hq.eq kv.1.ob k
    rw [qb_of ht2] at hr
    have h3 : q.eq kv.1.ob k = .ok true := by rw [ht2, hr.2]
    have h4 : q.eq k kv.1.ob = .ok true := by rw [hq.symm]; exact h3
    have := hq.trans _ _ _ h4 ht
    rw [hka] at this
    simp at this

theorem valOf_storeAt_other (q : ROps) (hq : Hashable q) (w : World) (d : WKD V) (k a : Nat) (h : Int)
    (v : V) (hka : q.eq k a = .ok false) :
    valOf q w (storeAt d k h (d.data.find? (pr q w k)) v) a = valOf q w d a := by
  unfold valOf
  cases hf : d.data.find? (pr q w k) with
  | none =>
    simp only [storeAt]
    rw [List.find?_append]
    have : pr q w a ((⟨d.nextRid, k, h, d.eager⟩ : WRef), v) = false := by
      simp [pr, qb_of hka]
    cases hx : d.data.find? (pr q w a) <;> simp [this]
  | some p =>
    obtain ⟨r, v0⟩ := p
    have hm : pr q w k (r, v0) = true := List.find?_some hf
    have hra := pr_other hq hka (r, v0) hm
    simp only [storeAt]
    congr 1
    clear hf hm
    induction d.data with
    | nil => rfl
    | cons p rest ih =>
      obtain ⟨x, y⟩ := p
      simp only [List.map_cons, List.find?_cons]
      by_cases e : x = r
      · subst e
        have h1 : pr q w a (x, v) = false := by simpa [pr] using hra
        have h2 : pr q w a (x, y) = false := by simpa [pr] using hra
        simp [h1, h2, ih]
      · simp only [e, if_false]
        cases pr q w a (x, y) <;> simp [ih]

/-- Writes through an object key. With a hashable key, `d[k] = v` makes `d[k]` give `v`, keeps the
invariant, and leaves every key that does not compare equal to `k`. With an `__eq__` that is never
true, even for the key itself, the identity of the key does not help (the comparison is between the
referents, behind two distinct refs): `d[k] = v` adds a new entry each time and `d[k]` raises
`KeyError`. -/
def WkdWrites : Prop :=
  ∀ (V : Type) (q : ROps) (w : World) (d : WKD V) (k a : Nat) (v : V),
    (Hashable q → HashOk q d → alive w k = true →
      ∃ d', d.setitem q w (.obj k) v = .ok d' ∧ d'.getitem q w (.obj k) = .ok v ∧ HashOk q d' ∧
        (q.eq k a = .ok false → valOf q w d' a = valOf q w d a)) ∧
    (∀ h, q.hash k = .ok h → (∀ b, q.eq b k = .ok false) →
      ∃ d', d.setitem q w (.obj k) v = .ok d' ∧ d'.data.length = d.data.length + 1 ∧
        d'.getitem q w (.obj k) = .error keyErr)

theorem find_never (q : ROps) (w : World) (k : Nat) (h : Int) (hk : ∀ b, q.eq b k = .ok false) :
    ∀ l : List (WRef × V), find q w k h l = .ok none := by
  intro l
  induction l with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨r, v⟩ := p
    simp only [find]
    split
    · simp [hk, ih]
    · exact ih

theorem wkdWrites_proven : WkdWrites := by
  intro V q w d k a v
  constructor
  · intro hq hd hk
    obtain ⟨h, hh, hs⟩ := setitem_hashable q hq w d k v hd
    have hd' := storeAt_hashOk q d k h hh v hd (d.data.find? (pr q w k)) (fun r x e => List.mem_of_find?_eq_some e)
    refine ⟨_, hs, ?_, hd', fun hka => valOf_storeAt_other q hq w d k a h v hka⟩
    have := valOf_storeAt_same q hq w d k h v hk
    obtain ⟨_, _, hl⟩ := lookup_hashable q hq w _ k hd'
    unfold valOf at this
    cases hf : (storeAt d k h (d.data.find? (pr q w k)) v).data.find? (pr q w k) with
    | none => rw [hf] at this; simp at this
    | some p =>
      rw [hf] at this
      obtain ⟨r, x⟩ := p
      simp only [Option.map_some, Option.some.injEq] at this
      subst this
      simp [getitem, hl, hf]
  · intro h hh hk
    have hl : ∀ d0 : WKD V, lookup q w d0 (.obj k) = .ok (k, h, none) := by
      intro d0
      simp [lookup, refOf, hh, unhashable, find_never q w k h hk]
    refine ⟨storeAt d k h none v, by simp [setitem, hl], by simp [storeAt], by simp [getitem, hl]⟩

/-! ### `del`, `pop`, `setdefault` -/

theorem find_delRef_none (q : ROps) (hq : Hashable q) (w : World) (k : Nat) (r : WRef) :
    ∀ l : List (WRef × V), (∀ kv ∈ l, pr q w k kv = true → kv.1 = r) →
      (delRef l r).find? (pr q w k) = none := by
  intro l h
  apply List.find?_eq_none.2
  intro kv hkv hp
  simp only [delRef, List.mem_filter] at hkv
  exact absurd (h kv hkv.1 hp) (by simpa using hkv.2)

/-- `del d[k]` removes the entry whose referent compares equal to `k`, after which `d[k]` raises
`KeyError` (with keys pairwise unequal, a dict's invariant for hashable keys); a missing key raises
`KeyError`. `pop` takes at most one default, as `dict.pop` does: two or more raise `TypeError` before
the lookup, whatever the key; on an empty dict it answers without hashing; a found entry is returned
and removed, a missing one gives the default or `KeyError`. `setdefault` keeps an existing value and
stores the default otherwise. -/
def WkdPopSetdefault : Prop :=
  ∀ (V : Type) (q : ROps) (w : World) (d : WKD V) (k : Nat) (v dflt : V) (x y : V) (rest : List V),
    (d.pop q w (.obj k) (x :: y :: rest)) = (d, .error (popArity (rest.length + 2))) ∧
    (d.data = [] → d.pop q w (.obj k) [] = (d, .error keyErr) ∧ d.pop q w (.obj k) [dflt] = (d, .ok dflt)) ∧
    (Hashable q → HashOk q d → alive w k = true →
      (valOf q w d k = none →
        d.delitem q w (.obj k) = .error keyErr ∧
        (d.pop q w (.obj k) []) = (d, .error keyErr) ∧ (d.pop q w (.obj k) [dflt]) = (d, .ok dflt) ∧
        (d.setdefault q w (.obj k) dflt).2 = .ok dflt ∧
        valOf q w (d.setdefault q w (.obj k) dflt).1 k = some dflt) ∧
      (valOf q w d k = some v →
        (d.setdefault q w (.obj k) dflt) = (d, .ok v) ∧
        (∀ args : List V, args.length ≤ 1 → (d.pop q w (.obj k) args).2 = .ok v) ∧
        ((d.data.map (·.1)).Nodup → (d.data.filter (pr q w k)).length = 1 →
          (∃ d', d.delitem q w (.obj k) = .ok d' ∧ d'.getitem q w (.obj k) = .error keyErr ∧
            d'.data.length + 1 = d.data.length) ∧
          ((d.pop q w (.obj k) []).1).getitem q w (.obj k) = .error keyErr)))

theorem filter_one_eq (q : ROps) (w : World) (k : Nat) (l : List (WRef × V)) (r : WRef) (x : V)
    (hn : (l.map (·.1)).Nodup) (h1 : (l.filter (pr q w k)).length = 1)
    (hf : l.find? (pr q w k) = some (r, x)) : ∀ kv ∈ l, pr q w k kv = true → kv.1 = r := by
  intro kv hkv hp
  have hr : (r, x) ∈ l.filter (pr q w k) :=
    List.mem_filter.2 ⟨List.mem_of_find?_eq_some hf, List.find?_some hf⟩
  have hk : kv ∈ l.filter (pr q w k) := List.mem_filter.2 ⟨hkv, hp⟩
  obtain ⟨a, ha⟩ : ∃ a, l.filter (pr q w k) = [a] := List.length_eq_one_iff.1 h1
  rw [ha] at hr hk
  simp only [List.mem_singleton] at hr hk
  rw [hk, ← hr]

theorem delRef_length (l : List (WRef × V)) (r : WRef) (x : V) (hn : (l.map (·.1)).Nodup)
    (hm : (r, x) ∈ l) : (delRef l r).length + 1 = l.length := by
  induction l with
  | nil => simp at hm
  | cons p rest ih =>
    simp only [List.map_cons, List.nodup_cons] at hn
    by_cases e : p.1 = r
    · have hnot : r ∉ rest.map (·.1) := by rw [← e]; exact hn.1
      have hf : delRef rest r = rest := by
        simp only [delRef]
        rw [List.filter_eq_self]
        intro a ha
        have : a.1 ≠ r := fun h => hnot (List.mem_map.2 ⟨a, ha, h⟩)
        simpa using this
      have h2 : delRef (p :: rest) r = delRef rest r := by simp [delRef, e]
      rw [h2, hf]
      simp
    · have hm' : (r, x) ∈ rest := by
        rcases List.mem_cons.1 hm with h | h
        · rw [← h] at e; exact absurd rfl e
        · exact h
      have h2 : delRef (p :: rest) r = p :: delRef rest r := by simp [delRef, e]
      rw [h2]
      have := ih hn.2 hm'
      simp only [List.length_cons]
      omega

theorem wkdPopSetdefault_proven : WkdPopSetdefault := by
  intro V q w d k v dflt x y rest
  refine ⟨?_, ?_, ?_⟩
  · simp [pop, refOf]
  · intro h
    simp [pop, refOf, h]
  · intro hq hd hk
    obtain ⟨h, hh, hl⟩ := lookup_hashable q hq w d k hd
    have pop_ne : ∀ args : List V, args.length ≤ 1 → d.data ≠ [] →
        d.pop q w (.obj k) args = match d.data.find? (pr q w k) with
          | some (r, v) => ({ d with data := delRef d.data r }, .ok v)
          | none => (d, match args with | a :: _ => .ok a | [] => .error keyErr) := by
      intro args ha hne
      have : ¬ (1 < args.length) := by omega
      have hne' : d.data.isEmpty = false := by
        cases hdd : d.data with
        | nil => exact absurd hdd hne
        | cons _ _ => rfl
      simp only [pop, refOf, this, if_false, hne', Bool.false_eq_true, hl]
      cases d.data.find? (pr q w k) <;> rfl
    constructor
    · intro hv
      have hf : d.data.find? (pr q w k) = none := by simpa [valOf] using hv
      have hpop : ∀ args : List V, args.length ≤ 1 →
          d.pop q w (.obj k) args = (d, match args with | a :: _ => .ok a | [] => .error keyErr) := by
        intro args ha
        by_cases hne : d.data = []
        · match args, ha with
          | [], _ => simp [pop, refOf, hne]
          | [a], _ => simp [pop, refOf, hne]
          | _ :: _ :: _, ha => simp at ha
        · rw [pop_ne args ha hne, hf]
      refine ⟨by simp [delitem, hl, hf], hpop [] (by simp), hpop [dflt] (by simp), ?_, ?_⟩
      · simp [setdefault, hl, hf]
      · simp only [setdefault, hl, hf]
        have := valOf_storeAt_same q hq w d k h dflt hk
        rw [hf] at this
        exact this
    · intro hv
      simp only [valOf] at hv
      cases hf : d.data.find? (pr q w k) with
      | none => simp [hf] at hv
      | some p =>
        obtain ⟨r, v'⟩ := p
        simp only [hf, Option.map_some, Option.some.injEq] at hv
        subst hv
        have hne : d.data ≠ [] := by intro e; simp [e] at hf
        refine ⟨by simp [setdefault, hl, hf], ?_, ?_⟩
        · intro args ha
          rw [pop_ne args ha hne, hf]
        · intro hn h1
          have hone := filter_one_eq q w k d.data r v' hn h1 hf
          have hd' : HashOk q { d with data := delRef d.data r } := by
            intro kv hkv
            exact hd kv (List.mem_filter.1 hkv).1
          obtain ⟨_, _, hl'⟩ := lookup_hashable q hq w { d with data := delRef d.data r } k hd'
          have hnone : (delRef d.data r).find? (pr q w k) = none :=
            find_delRef_none q hq w k r d.data hone
          refine ⟨⟨{ d with data := delRef d.data r }, by simp [delitem, hl, hf],
            by simp [getitem, hl', hnone], ?_⟩, ?_⟩
          · exact delRef_length d.data r v' hn (List.mem_of_find?_eq_some hf)
          · rw [pop_ne [] (by simp) hne, hf]
            simp [getitem, hl', hnone]

/-! ### Death, `popitem` -/

/-- The function behind `liveItems`. -/
def liveF (w : World) (kv : WRef × V) : Option (PV × V) := (deref w kv.1.ob).map (fun x => (x, kv.2))

theorem liveItems_def (w : World) (d : WKD V) : liveItems w d = d.data.filterMap (liveF w) := rfl

/-- A death removes the key at once: live items lose that object, whatever the keys' `__hash__`
and `__eq__` do (the callback finds the dead `ref` by identity), and every entry whose `ref` was made
with the removing callback leaves `data`. -/
def WkdDeath : Prop :=
  ∀ (V : Type) (w : World) (d : WKD V) (o : Nat),
    liveItems (o :: w) (d.onDeath o) = (liveItems w d).filter (fun kv => kv.1 ≠ .obj o) ∧
    (∀ kv ∈ (d.onDeath o).data, kv.1.ob = o → kv.1.cb = false) ∧
    (∀ kv ∈ d.data, kv.1.ob ≠ o → kv ∈ (d.onDeath o).data)

theorem wkdDeath_proven : WkdDeath := by
  intro V w d o
  have key : ∀ l : List (WRef × V),
      l.filterMap (liveF (o :: w)) = (l.filterMap (liveF w)).filter (fun kv => kv.1 ≠ .obj o) := by
    intro l
    induction l with
    | nil => rfl
    | cons p rest ih =>
      obtain ⟨r, x0⟩ := p
      by_cases h1 : r.ob = o
      · have e1 : liveF (o :: w) (r, x0) = none := by
          simp only [liveF]
          rw [deref_cons, if_pos h1]
          rfl
        rw [List.filterMap_cons_none e1]
        cases hd : deref w r.ob with
        | none =>
          have e2 : liveF w (r, x0) = none := by simp only [liveF]; rw [hd]; rfl
          rw [List.filterMap_cons_none e2]
          exact ih
        | some v =>
          have hv := deref_some hd
          have e2 : liveF w (r, x0) = some (v, x0) := by simp only [liveF]; rw [hd]; rfl
          rw [List.filterMap_cons_some e2, List.filter_cons_of_neg (by simp [hv, h1])]
          exact ih
      · cases hd : deref w r.ob with
        | none =>
          have e1 : liveF (o :: w) (r, x0) = none := by
            simp only [liveF]
            rw [deref_cons, if_neg h1, hd]
            rfl
          have e2 : liveF w (r, x0) = none := by simp only [liveF]; rw [hd]; rfl
          rw [List.filterMap_cons_none e1, List.filterMap_cons_none e2]
          exact ih
        | some v =>
          have hv := deref_some hd
          have e1 : liveF (o :: w) (r, x0) = some (v, x0) := by
            simp only [liveF]
            rw [deref_cons, if_neg h1, hd]
            rfl
          have e2 : liveF w (r, x0) = some (v, x0) := by simp only [liveF]; rw [hd]; rfl
          rw [List.filterMap_cons_some e1, List.filterMap_cons_some e2,
            List.filter_cons_of_pos (by simp [hv, h1]), ih]
  refine ⟨?_, ?_, ?_⟩
  · have hf : ∀ l : List (WRef × V),
        (l.filter (fun kv => !(kv.1.ob == o && kv.1.cb))).filterMap (liveF (o :: w)) =
          l.filterMap (liveF (o :: w)) := by
      intro l
      induction l with
      | nil => rfl
      | cons p rest ih =>
        obtain ⟨r, x⟩ := p
        by_cases h1 : r.ob = o
        · have e1 : liveF (o :: w) (r, x) = none := by
            simp only [liveF]
            rw [deref_cons, if_pos h1]
            rfl
          rw [List.filterMap_cons_none e1]
          rw [List.filter_cons]
          split
          · rw [List.filterMap_cons_none e1]; exact ih
          · exact ih
        · rw [List.filter_cons_of_pos (by simp [h1]), List.filterMap_cons, List.filterMap_cons, ih]
    simp only [onDeath, liveItems_def]
    rw [hf, key]
  · intro kv hkv hob
    simp only [onDeath, List.mem_filter] at hkv
    simpa [hob] using hkv.2
  · intro kv hkv hne
    simp only [onDeath, List.mem_filter]
    exact ⟨hkv, by simp [hne]⟩

/-- `popitem` returns the last entry with a live key, dropping what is behind it, and raises the
`KeyError` of the empty dict when none is left. -/
def WkdPopitem : Prop :=
  ∀ (V : Type) (w : World) (d : WKD V),
    (liveItems w d = [] → (d.popitem w).2 = .error popEmpty ∧ (d.popitem w).1.data = []) ∧
    (∀ pre k v, liveItems w d = pre ++ [(k, v)] → (d.popitem w).2 = .ok (k, v) ∧
      liveItems w (d.popitem w).1 = pre)

theorem popitem_loop (w : World) :
    ∀ (n : Nat) (d : WKD V), d.data.length = n →
      (liveItems w d = [] → (popitemLoop w (n + 1) d).2 = .error popEmpty ∧
        (popitemLoop w (n + 1) d).1.data = []) ∧
      (∀ pre k v, liveItems w d = pre ++ [(k, v)] → (popitemLoop w (n + 1) d).2 = .ok (k, v) ∧
        liveItems w (popitemLoop w (n + 1) d).1 = pre) := by
  intro n
  induction n with
  | zero =>
    intro d hn
    have hq : d.data = [] := List.length_eq_zero_iff.1 hn
    have hp : popitemLoop w 1 d = (d, .error popEmpty) := by
      simp [popitemLoop, dPopLast, hq]
    constructor
    · intro _; simp [hp, hq]
    · intro pre k v h
      simp [liveItems, hq] at h
  | succ n ih =>
    intro d hn
    have hne : d.data ≠ [] := by
      intro e
      simp [e] at hn
    obtain ⟨init, p, hd⟩ : ∃ init p, d.data = init ++ [p] :=
      ⟨d.data.dropLast, d.data.getLast hne, (List.dropLast_concat_getLast hne).symm⟩
    obtain ⟨r0, v0⟩ := p
    let d' : WKD V := { d with data := init }
    have hlen : d'.data.length = n := by
      simp [d', hd] at hn ⊢
      omega
    have hpop : dPopLast d.data = some ((r0, v0), init) := by simp [dPopLast, hd]
    have hlive : liveItems w d = liveItems w d' ++
        match deref w r0.ob with
        | some o => [(o, v0)]
        | none => [] := by
      simp only [liveItems, hd, d', List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
      cases deref w r0.ob <;> simp
    obtain ⟨i1, i2⟩ := ih d' hlen
    cases hr : deref w r0.ob with
    | none =>
      have hstep : popitemLoop w (n + 1 + 1) d = popitemLoop w (n + 1) d' := by
        rw [popitemLoop]
        simp only [hpop, hr]
        rfl
      rw [hstep]
      rw [hr] at hlive
      simp only [List.append_nil] at hlive
      rw [hlive]
      exact ⟨i1, i2⟩
    | some o =>
      have hstep : popitemLoop w (n + 1 + 1) d = (d', .ok (o, v0)) := by
        rw [popitemLoop]
        simp only [hpop, hr]
        rfl
      rw [hstep]
      rw [hr] at hlive
      simp only at hlive
      rw [hlive]
      constructor
      · intro h; simp at h
      · intro pre k v h
        have h2 := List.append_inj' h rfl
        simp only [List.cons.injEq, Prod.mk.injEq, and_true] at h2
        obtain ⟨h3, h4, h5⟩ := h2
        subst h3 h4 h5
        exact ⟨rfl, rfl⟩

theorem wkdPopitem_proven : WkdPopitem := by
  intro V w d
  exact popitem_loop w d.data.length d rfl

end WKD

end PyLean.CoreLibs.Misc.Weakref
