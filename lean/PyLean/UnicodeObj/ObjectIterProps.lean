import PyLean.UnicodeObj.ObjectIter

/-!
Properties of the `str` iterators.
-/

namespace PyLean.UnicodeObj

open PyLean

/-- What an item of the iterator is: a one-character string of the canonical kind. -/
def iterItem (c : Nat) : Str × Kind := ([c], kindOfMax c)

/-- `next(it)` until it stops, with `fuel` steps at most. -/
def drain : Nat → UIter → List (Str × Kind)
  | 0, _ => []
  | f + 1, it =>
    match it.next with
    | (i, some x) => x :: drain f i
    | (_, none) => []

/-- The characters still to come. -/
def UIter.rest (it : UIter) : Str :=
  match it.seq with
  | some s => s.drop it.index.toNat
  | none => []

/-- The type invariant of an iterator over `src`: the index stays in range once `__setstate__` has
clamped it, the ASCII type goes with ASCII text, and a `str` fits `Py_ssize_t`. -/
def IInv (src : Str) (it : UIter) : Prop :=
  0 ≤ it.index ∧ (it.seq = none ∨ (it.seq = some src ∧ it.index ≤ src.length)) ∧
    (it.asciiType = true → ∀ c ∈ src, c < 128) ∧ (src.length : Int) ≤ ssizeMax

theorem unicodeChar_item (c : Nat) : unicodeChar c = iterItem c := by
  unfold unicodeChar iterItem kindOfMax
  by_cases h1 : c < 128
  · simp [h1, show c < 256 by omega]
  · by_cases h2 : c < 256
    · simp [h1, h2]
    · simp [h1, h2]

theorem iter_inv (s : Str) (e : Bool) (hs : (s.length : Int) ≤ ssizeMax) :
    IInv s (unicodeIter s e) := by
  refine ⟨by simp [unicodeIter], .inr ⟨rfl, by simp [unicodeIter]⟩, ?_, hs⟩
  intro h c hc
  simp only [unicodeIter, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h.2 c hc

theorem next_none {it : UIter} (hs : it.seq = none) : it.next = (it, none) := by
  unfold UIter.next unicodeAsciiIterNext unicodeiterNext
  rw [hs]
  split <;> rfl

theorem getD_get {s : Str} {i : Nat} (h : i < s.length) : s.getD i 0 = s[i] := by
  simp [List.getD, h]

theorem drop_getD {s : Str} {i : Nat} (h : i < s.length) :
    s.drop i = s.getD i 0 :: s.drop (i + 1) := by
  rw [List.drop_eq_getElem_cons h, getD_get h]

theorem getD_mem {s : Str} {i : Nat} (h : i < s.length) : s.getD i 0 ∈ s := by
  rw [getD_get h]
  exact List.getElem_mem h

theorem next_some {src : Str} {it : UIter} (hI : IInv src it) (hs : it.seq = some src)
    (hi : it.index < src.length) :
    it.next = ({ it with index := it.index + 1 }, some (iterItem (src.getD it.index.toNat 0))) := by
  obtain ⟨h0, _, ha, _⟩ := hI
  have hl : it.index.toNat < src.length := by omega
  unfold UIter.next
  split
  · next h =>
    have hc := ha h _ (getD_mem hl)
    unfold unicodeAsciiIterNext
    rw [hs]
    simp only [if_pos hi]
    have e : src.getD it.index.toNat 0 % 256 = src.getD it.index.toNat 0 := Nat.mod_eq_of_lt (by omega)
    rw [e]
    have ek : kindOfMax (src.getD it.index.toNat 0) = .ascii := by
      unfold kindOfMax
      rw [if_pos hc]
    simp only [iterItem, ek]
  · unfold unicodeiterNext
    rw [hs]
    simp only [if_pos hi, unicodeChar_item]

theorem next_end {src : Str} {it : UIter} (hs : it.seq = some src) (hi : ¬it.index < src.length) :
    it.next = ({ it with seq := none }, none) := by
  unfold UIter.next unicodeAsciiIterNext unicodeiterNext
  rw [hs]
  simp only [if_neg hi]
  split <;> rfl

theorem IInv.next {src : Str} {it : UIter} (hI : IInv src it) : IInv src it.next.1 := by
  obtain ⟨h0, h1, ha, hm⟩ := id hI
  rcases h1 with hs | ⟨hs, hle⟩
  · rw [next_none hs]
    exact hI
  · by_cases hi : it.index < src.length
    · rw [next_some hI hs hi]
      exact ⟨by simp only; omega, .inr ⟨hs, by simp only; omega⟩, ha, hm⟩
    · rw [next_end hs hi]
      exact ⟨h0, .inl rfl, ha, hm⟩

theorem rest_le {src : Str} {it : UIter} (hI : IInv src it) : it.rest.length ≤ src.length := by
  unfold UIter.rest
  rcases hI.2.1 with hs | ⟨hs, _⟩
  · rw [hs]
    simp
  · rw [hs]
    simp only [List.length_drop]
    omega

theorem drain_rest : ∀ (fuel : Nat) (src : Str) (it : UIter), IInv src it → it.rest.length < fuel →
    drain fuel it = it.rest.map iterItem := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ h; omega
  | succ f ih =>
    intro src it hI hf
    obtain ⟨h0, h1, _, _⟩ := id hI
    rcases h1 with hs | ⟨hs, hle⟩
    · simp only [drain, next_none hs]
      simp [UIter.rest, hs]
    · by_cases hi : it.index < src.length
      · have hl : it.index.toNat < src.length := by omega
        have hr : it.rest = src.getD it.index.toNat 0 :: src.drop (it.index.toNat + 1) := by
          simp only [UIter.rest, hs]
          exact drop_getD hl
        have hI2 := hI.next
        rw [next_some hI hs hi] at hI2
        simp only [drain, next_some hI hs hi]
        have hr2 : ({ it with index := it.index + 1 } : UIter).rest = src.drop (it.index.toNat + 1) := by
          simp only [UIter.rest, hs]
          congr 1
          omega
        rw [ih src _ hI2 (by
          rw [hr2]
          rw [hr] at hf
          simp only [List.length_cons] at hf
          omega), hr2, hr]
        rfl
      · have hd : it.rest = [] := by
          simp only [UIter.rest, hs]
          apply List.drop_of_length_le
          omega
        simp only [drain, next_end hs hi, hd, List.map_nil]

/-- `list(iter(s))` is the characters of `s`, each a one-character string of the canonical kind,
for both iterator types and for an instance of a subclass, and the iterator ends. The strings that
fit in a `Py_ssize_t` are all the strings. -/
def IterDrains : Prop :=
  ∀ (s : Str) (exact : Bool) (fuel : Nat), (s.length : Int) ≤ ssizeMax → s.length < fuel →
    drain fuel (unicodeIter s exact) = s.map iterItem

theorem iterDrains_proven : IterDrains := by
  intro s e fuel hs hf
  rw [drain_rest fuel s _ (iter_inv s e hs) (by
    have := rest_le (iter_inv s e hs)
    omega)]
  simp [UIter.rest, unicodeIter]

/-- The two `tp_iternext` of `str` do the same thing on the ASCII strings the second is for: same
item, same kind, same state, at every state an iterator can be in. -/
def AsciiIterTwin : Prop :=
  ∀ (src : Str) (it : UIter), IInv src it → (∀ c ∈ src, c < 128) →
    unicodeAsciiIterNext it = unicodeiterNext it

theorem asciiIterTwin_proven : AsciiIterTwin := by
  intro src it hI ha
  obtain ⟨h0, h1, _, _⟩ := id hI
  unfold unicodeAsciiIterNext unicodeiterNext
  rcases h1 with hs | ⟨hs, hle⟩
  · rw [hs]
  · rw [hs]
    simp only
    split
    · next hi =>
      have hl : it.index.toNat < src.length := by omega
      have hc := ha _ (getD_mem hl)
      have e : src.getD it.index.toNat 0 % 256 = src.getD it.index.toNat 0 :=
        Nat.mod_eq_of_lt (by omega)
      rw [e, unicodeChar_item]
      have ek : kindOfMax (src.getD it.index.toNat 0) = .ascii := by
        unfold kindOfMax
        rw [if_pos hc]
      simp only [iterItem, ek]
    · rfl

theorem IInv.setstate {src : Str} {it it' : UIter} {o : GObj} (hI : IInv src it)
    (h : unicodeiterSetstate it o = .ok it') : IInv src it' := by
  obtain ⟨h0, h1, ha, hm⟩ := id hI
  simp only [unicodeiterSetstate, bind, Except.bind] at h
  cases hl : longAsSsize o with
  | error e => simp [hl] at h
  | ok v =>
    rw [hl] at h
    simp only at h
    rcases h1 with hs | ⟨hs, hle⟩
    · rw [hs] at h
      simp only [Except.ok.injEq] at h
      subst h
      exact hI
    · rw [hs] at h
      simp only [Except.ok.injEq] at h
      subst h
      refine ⟨?_, .inr ⟨rfl, ?_⟩, ha, hm⟩
      · simp only
        split
        · omega
        · split <;> omega
      · simp only
        split
        · omega
        · split <;> omega

theorem run_inv {src : Str} {it : UIter} (hI : IInv src it) (op : ISimple) :
    IInv src (ISimple.run it op) := by
  cases op with
  | next => exact hI.next
  | setstate o =>
    simp only [ISimple.run]
    cases h : unicodeiterSetstate it o with
    | ok i => exact hI.setstate h
    | error e => exact hI

theorem fold_inv {src : Str} (ops : List ISimple) {it : UIter} (hI : IInv src it) :
    IInv src (ops.foldl ISimple.run it) := by
  induction ops generalizing it with
  | nil => exact hI
  | cons op t ih => exact ih (run_inv hI op)

theorem len_rest {src : Str} {it : UIter} (hI : IInv src it) :
    unicodeiterLen it = (it.rest.length : Int) := by
  obtain ⟨h0, h1, _, _⟩ := hI
  unfold unicodeiterLen UIter.rest
  rcases h1 with hs | ⟨hs, hle⟩
  · rw [hs]
    simp
  · rw [hs]
    simp only [List.length_drop]
    omega

/-- `__length_hint__` is exact: after any script of `next` and `__setstate__`, including past the
end, it is the number of items still to come. -/
def IterHintExact : Prop :=
  ∀ (s : Str) (exact : Bool) (ops : List ISimple) (fuel : Nat), (s.length : Int) ≤ ssizeMax →
    s.length < fuel →
    let it := ops.foldl ISimple.run (unicodeIter s exact)
    unicodeiterLen it = ((drain fuel it).length : Int)

theorem iterHintExact_proven : IterHintExact := by
  intro s e ops fuel hs hf
  have hI := fold_inv ops (iter_inv s e hs)
  dsimp only
  rw [len_rest hI, drain_rest fuel s _ hI (by
    have := rest_le hI
    omega)]
  simp

/-- `__setstate__`, for every value: an index in `Py_ssize_t` goes where the slice `s[v:]` would
start, a negative one at the start and a large one at the end; an exhausted iterator stays
exhausted; an int out of range raises `OverflowError` and anything else that is not an `int`
raises `TypeError`, for an exhausted iterator too. `__index__` is not consulted. -/
def IterSetstateSpec : Prop :=
  ∀ (src : Str) (it : UIter), IInv src it →
    (∀ v : Int, ssizeMin ≤ v → v ≤ ssizeMax → ∃ it',
      unicodeiterSetstate it (.int v) = .ok it' ∧
      (it.seq = none → it' = it) ∧ (it.seq = some src → it'.rest = src.drop v.toNat)) ∧
    (∀ v : Int, (v > ssizeMax ∨ v < ssizeMin) → unicodeiterSetstate it (.int v) =
      .error (.overflowError "Python int too large to convert to C ssize_t")) ∧
    (∀ o : GObj, (∀ v, o ≠ .int v) → (∀ b, o ≠ .bool b) →
      unicodeiterSetstate it o = .error (.typeError "an integer is required"))

theorem iterSetstateSpec_proven : IterSetstateSpec := by
  intro src it hI
  refine ⟨?_, ?_, ?_⟩
  · intro v h1 h2
    have hl : longAsSsize (.int v) = .ok v := by
      simp only [longAsSsize]
      rw [if_neg (by omega)]
    rcases hs0 : it.seq with _ | s
    · refine ⟨it, ?_, fun _ => rfl, fun h => by simp at h⟩
      simp [unicodeiterSetstate, hl, hs0, bind, Except.bind]
    · refine ⟨{ it with index := if v < 0 then 0
          else if v > (s.length : Int) then (s.length : Int) else v }, ?_, fun h => by simp at h, ?_⟩
      · simp [unicodeiterSetstate, hl, hs0, bind, Except.bind]
      · intro h
        simp only [Option.some.injEq] at h
        subst h
        simp only [UIter.rest, hs0]
        split
        · next hn =>
          rw [show ((0 : Int)).toNat = 0 from rfl, show v.toNat = 0 by omega]
        · split
          · next hg =>
            rw [List.drop_of_length_le (by omega), List.drop_of_length_le (by omega)]
          · rfl
  · intro v h
    have hl : longAsSsize (.int v) = .error (.overflowError "Python int too large to convert to C ssize_t") := by
      simp only [longAsSsize]
      rw [if_pos h]
    simp only [unicodeiterSetstate, hl, bind, Except.bind]
  · intro o h1 h2
    have hl : longAsSsize o = .error (.typeError "an integer is required") := by
      cases o with
      | int v => exact absurd rfl (h1 v)
      | bool b => exact absurd rfl (h2 b)
      | _ => rfl
    simp only [unicodeiterSetstate, hl, bind, Except.bind]

/-- What pickle does with the result of `__reduce__`: call `iter` on the string, then
`__setstate__` with the index if there is one. -/
def rebuildIter (exact : Bool) : IterReduced → Py UIter
  | (_, s, some i) => unicodeiterSetstate (unicodeIter s exact) (.int i)
  | (_, s, none) => .ok (unicodeIter s exact)

/-- `__reduce__` round-trips, whatever the lookup of `iter` does: rebuilding from its result gives
an iterator with the items the original has left after the lookup, including when the lookup
advanced or exhausted it. So the iterator is read after the lookup, which is the point of
issue #101765. A lookup that fails raises what it raises, or `AttributeError`, for every state.
A lookup can only reach this iterator through its methods, which is the hypothesis on `lookup`. -/
def IterReduceRoundTrip : Prop :=
  ∀ (src : Str) (exact : Bool) (lookup : UIter → UIter × BuiltinIter) (it : UIter) (fuel : Nat),
    (∀ i, IInv src i → IInv src (lookup i).1) → IInv src it → src.length < fuel →
    (∀ f, (lookup it).2 = .found f → ∃ r it2,
      (unicodeiterReduce lookup it).2 = .ok r ∧ r.1 = f ∧ rebuildIter exact r = .ok it2 ∧
      drain fuel it2 = drain fuel (lookup it).1) ∧
    ((lookup it).2 = .missing →
      (unicodeiterReduce lookup it).2 = .error (.named "AttributeError" "iter")) ∧
    (∀ e, (lookup it).2 = .raises e → (unicodeiterReduce lookup it).2 = .error e)

theorem iterReduceRoundTrip_proven : IterReduceRoundTrip := by
  intro src e lookup it fuel hl hI hf
  have hI2 := hl it hI
  generalize hq : lookup it = q at *
  obtain ⟨it', r⟩ := q
  simp only at hI2
  refine ⟨?_, ?_, ?_⟩
  · intro f hr
    subst hr
    obtain ⟨h0, h1, ha, hm⟩ := id hI2
    rcases h1 with hs | ⟨hs, hle⟩
    · refine ⟨(f, [], none), unicodeIter [] e, ?_, rfl, rfl, ?_⟩
      · simp [unicodeiterReduce, hq, hs]
      · have h3 := drain_rest fuel [] (unicodeIter [] e) (iter_inv [] e (by simp [ssizeMax])) (by
          simp [UIter.rest, unicodeIter]
          omega)
        have h4 := drain_rest fuel src it' hI2 (by
          have := rest_le hI2
          omega)
        rw [h3, h4]
        simp [UIter.rest, unicodeIter, hs]
    · have hv : longAsSsize (.int it'.index) = .ok it'.index := by
        simp only [longAsSsize]
        rw [if_neg (by simp only [ssizeMin] at *; omega)]
      have hclamp : (if it'.index < 0 then (0 : Int)
          else if it'.index > (src.length : Int) then (src.length : Int) else it'.index) = it'.index := by
        rw [if_neg (by omega), if_neg (by omega)]
      refine ⟨(f, src, some it'.index), { (unicodeIter src e) with index := it'.index }, ?_, rfl, ?_, ?_⟩
      · simp [unicodeiterReduce, hq, hs]
      · simp only [rebuildIter, unicodeiterSetstate, hv, bind, Except.bind, unicodeIter, hclamp]
      · have hJ : IInv src { (unicodeIter src e) with index := it'.index } := by
          obtain ⟨_, _, a3, a4⟩ := iter_inv src e hm
          exact ⟨h0, .inr ⟨rfl, hle⟩, a3, a4⟩
        rw [drain_rest fuel src _ hJ (by
          have := rest_le hJ
          omega), drain_rest fuel src it' hI2 (by
          have := rest_le hI2
          omega)]
        simp [UIter.rest, unicodeIter, hs]
  · intro hr
    subst hr
    simp [unicodeiterReduce, hq]
  · intro x hr
    subst hr
    simp [unicodeiterReduce, hq]

/-- `unicode_char` gives the character in the canonical kind for every code point, the iterators'
characters included, and `SystemError` for everything above U+10FFFF, for every `Py_UCS4`. -/
def UnicodeCharSpec : Prop :=
  ∀ ch : Nat,
    (ch ≤ maxUnicode → unicodeCharChecked ch = .ok ([ch], canonicalKind [ch])) ∧
    (ch > maxUnicode → unicodeCharChecked ch =
      .error (.named "SystemError" "invalid maximum character passed to PyUnicode_New"))

theorem unicodeCharSpec_proven : UnicodeCharSpec := by
  intro ch
  have hm : maxUnicode = 0x10FFFF := rfl
  have e : maxCharOf [ch] = ch := by simp [maxCharOf]
  constructor
  · intro h
    have nb : ¬ch > maxUnicode := by omega
    simp only [unicodeCharChecked, if_neg nb, canonicalKind, e, unicodeChar, ite_self]
    by_cases h1 : ch < 256
    · by_cases h2 : ch < 128
      · simp [h1, h2, kindOfMax]
      · have h3 : ¬ch < 128 := h2
        simp [h1, h2, kindOfMax]
    · simp [h1]
  · intro h
    have nl : ¬ch < 256 := by omega
    simp only [unicodeCharChecked, if_neg nl, if_pos h]

end PyLean.UnicodeObj
