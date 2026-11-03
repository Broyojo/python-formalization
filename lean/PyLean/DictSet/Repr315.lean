import PyLean.DictSet.Props315

/-!
`repr` of a dict and a frozendict (CPython 3.15.2, `Objects/dictobject.c:3641-3741, 8341-8359`),
with reprs that may raise and may change the dict.
-/

namespace PyLean.DictSet

open PyLean

variable {K V : Type}

/-- `anydict_repr_impl`, `dict_repr_lock_held`, `dict_repr` and `frozendict_repr`, for any `repr` of
keys and values, which may raise and may change the dict. A failed `Py_ReprEnter` is the result; a
dict already being printed is `{...}`; an empty one is `{}`. Otherwise each turn takes the next item
by `_PyDict_Next` on the dict as the last `repr` left it, writes `", "` unless it is the first, then
`repr(key)`, `": "`, `repr(value)`; a failed `repr` ends it with its exception in the state it left,
and the end of the table closes the brace. There is no test that the dict changed size. A frozendict
is `tp_name()` when empty and `tp_name(...)` around the same text otherwise. -/
def ReprBody : Prop :=
  ∀ (K V : Type) (krepr : K → DM K V String) (vrepr : V → DM K V String) (fuel : Nat)
    (mp : PyDict K V) (tp : String),
    (∀ e, anydictRepr (.error e) krepr vrepr fuel mp = (.error e, mp)) ∧
    anydictRepr (.ok true) krepr vrepr fuel mp = (.ok "{...}", mp) ∧
    (mp.used = 0 → anydictRepr (.ok false) krepr vrepr fuel mp = (.ok "{}", mp)) ∧
    (mp.used ≠ 0 → anydictRepr (.ok false) krepr vrepr fuel mp =
      anydictReprLoop krepr vrepr fuel 0 true "{" mp) ∧
    (∀ (i : Int) (first : Bool) (acc : String) (s : PyDict K V), dictNext s i = none →
      anydictReprLoop krepr vrepr (fuel + 1) i first acc s = (.ok (acc ++ "}"), s)) ∧
    (∀ (i i' : Int) (first : Bool) (acc : String) (s : PyDict K V) (key : K) (value : V) (h : Int),
      dictNext s i = some (i', key, value, h) →
      (∀ e s1, krepr key s = (.error e, s1) →
        anydictReprLoop krepr vrepr (fuel + 1) i first acc s = (.error e, s1)) ∧
      (∀ ks s1, krepr key s = (.ok ks, s1) →
        (∀ e s2, vrepr value s1 = (.error e, s2) →
          anydictReprLoop krepr vrepr (fuel + 1) i first acc s = (.error e, s2)) ∧
        (∀ vs s2, vrepr value s1 = (.ok vs, s2) →
          anydictReprLoop krepr vrepr (fuel + 1) i first acc s =
            anydictReprLoop krepr vrepr fuel i' false
              ((if first then acc else acc ++ ", ") ++ ks ++ ": " ++ vs) s2))) ∧
    (∀ re, mp.used = 0 → frozendictRepr315 tp re krepr vrepr fuel mp = (.ok s!"{tp}()", mp)) ∧
    (∀ re, mp.used ≠ 0 → frozendictRepr315 tp re krepr vrepr fuel mp =
      match anydictRepr re krepr vrepr fuel mp with
      | (.ok r, s) => (.ok s!"{tp}({r})", s)
      | (.error e, s) => (.error e, s))

theorem reprBody_proven : ReprBody := by
  intro K V krepr vrepr fuel mp tp
  refine ⟨fun e => rfl, rfl, fun h => by simp [anydictRepr, h], fun h => by simp [anydictRepr, h],
    fun i first acc s hn => by simp [anydictReprLoop, hn], ?_, fun re h => by simp [frozendictRepr315, h],
    fun re h => ?_⟩
  · intro i i' first acc s key value h hn
    refine ⟨fun e s1 hk => by simp [anydictReprLoop, hn, hk], fun ks s1 hk => ⟨fun e s2 hv => ?_,
      fun vs s2 hv => ?_⟩⟩
    · simp [anydictReprLoop, hn, hk, hv]
    · simp [anydictReprLoop, hn, hk, hv]
  · have : (mp.used == 0) = false := by simpa using h
    simp only [frozendictRepr315, this, Bool.false_eq_true, if_false]
    rcases anydictRepr re krepr vrepr fuel mp with ⟨r, s⟩
    cases r <;> rfl

/-- The loop on a combined table whose reprs do not touch the dict: the items in table order. -/
theorem reprLoop_quiet (kr : K → String) (vr : V → String) (mp : PyDict K V) (k : Keys K V)
    (hb : mp.body = .combined k) :
    ∀ (fuel i : Nat) (first : Bool) (acc : String), i ≤ k.nentries → k.nentries < i + fuel →
      anydictReprLoop (fun x s => (.ok (kr x), s)) (fun x s => (.ok (vr x), s)) fuel (i : Int) first acc mp =
        (.ok (acc ++ reprTail kr vr first (dictNextAll mp fuel (i : Int)) ++ "}"), mp) := by
  intro fuel
  induction fuel with
  | zero => intro i first acc h1 h2; omega
  | succ fuel ih =>
    intro i first acc h1 h2
    simp only [anydictReprLoop, dictNextAll]
    cases hn : dictNext mp (i : Int) with
    | none => simp [reprTail]
    | some t =>
      obtain ⟨pos', key, value, h⟩ := t
      obtain ⟨j, rfl, h4, h5⟩ := dictNext_step mp k hb i pos' key value h hn
      simp only []
      rw [ih (j + 1) false _ (by omega) (by omega)]
      cases first <;> simp [reprTail, String.append_assoc]

/-- `repr(d)` of a dict with a combined table, when the reprs of its keys and values do not change
it: `{k1: v1, k2: v2, ...}` in iteration order, and the dict is unchanged. The fuel is any amount
above the number of entries, so it is no assumption about the dict. -/
def ReprQuiet : Prop :=
  ∀ (K V : Type) (kr : K → String) (vr : V → String) (mp : PyDict K V) (k : Keys K V),
    mp.body = .combined k → ∀ fuel, k.nentries < fuel →
      anydictRepr (.ok false) (fun x s => (.ok (kr x), s)) (fun x s => (.ok (vr x), s)) fuel mp =
        (.ok (if mp.used = 0 then "{}" else reprRender kr vr (dictItems mp)), mp)

theorem reprQuiet_proven : ReprQuiet := by
  intro K V kr vr mp k hb fuel hf
  by_cases h0 : mp.used = 0
  · simp [anydictRepr, h0]
  · have h0' : (mp.used == 0) = false := by simpa using h0
    simp only [anydictRepr, h0', Bool.false_eq_true, if_false, h0]
    have hn : mp.body.nentries = k.nentries := by simp [Body.nentries, hb]
    have hfuel := dictNextAll_fuel mp k hb fuel (mp.body.nentries + mp.used + 1) 0
      (Nat.zero_le _) (by omega) (by omega)
    refine (reprLoop_quiet kr vr mp k hb fuel 0 true "{" (Nat.zero_le _) (by omega)).trans ?_
    rw [hfuel]
    rfl

end PyLean.DictSet
