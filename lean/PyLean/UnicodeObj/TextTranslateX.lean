import PyLean.UnicodeObj.TextProps2
import PyLean.UnicodeObj.CodecCallback

/-!
`str.translate` with a table that is a Python object.

`Mapping` in `TextTranslate.lean` is a function of the character alone, so it cannot say what a
`__getitem__` with state does. Here the table is a function of the whole history of lookups, the
last one being the current character. That also covers re-entry: a `__getitem__` that calls back
into `str.translate` touches none of the C state, since `str` is immutable and `ascii_table` is
local, so all it can do is answer differently.

The lookup, output and fast lookup bodies are the ones in `TextTranslate.lean`, applied to the
answer for this call. Only the loops are repeated here, to carry the history.
-/

namespace PyLean.UnicodeObj

open PyLean

abbrev MapH := List Nat → MapItem

/-- The table as it answers this one call. -/
def atCall (m : MapH) (hist : List Nat) (c : Nat) : Mapping := fun _ => m (hist ++ [c])

/-- A table with no state. -/
def pureH (m : Mapping) : MapH := fun hist => m (hist.getLastD 0)

/-- `unicode_fast_translate`'s loop, with the history of lookups. -/
def fastTranslateLoopX (m : MapH) (ignore : Bool) :
    List Nat → AsciiTable → Str → Nat → List Nat → Py (Bool × Str × Nat × List Nat)
  | [], _, out, pos, hist => .ok (true, out, pos, hist)
  | ch :: cs, t, out, pos, hist => do
    let ch2 := t ch
    let step (t' : AsciiTable) (ch2 : Nat) (hist' : List Nat) :
        Py (Bool × Str × Nat × List Nat) :=
      if ch2 = 0xfe then
        if ignore then fastTranslateLoopX m ignore cs t' out (pos + 1) hist'
        else .ok (false, out, pos, hist')
      else fastTranslateLoopX m ignore cs t' (out ++ [ch2]) (pos + 1) hist'
    if ch2 = 0xff then
      let (translate, t') ← fastTranslateLookup (atCall m hist ch) ch t
      if !translate then .ok (false, out, pos, hist ++ [ch])
      else step t' (t' ch) (hist ++ [ch])
    else step t ch2 hist

/-- The inner `while (collend < size)` of `_PyUnicode_TranslateCharmap`, unicodeobject.c:9464-9474.
Every lookup here is thrown away, the last one included: the main loop asks again. -/
def collectUndefinedX (m : MapH) : List Nat → List Nat → Py (List Nat × List Nat)
  | [], hist => .ok ([], hist)
  | c :: cs, hist => do
    match ← charmaptranslateLookup (atCall m hist c) c with
    | .pyNone => collectUndefinedX m cs (hist ++ [c])
    | _ => .ok (c :: cs, hist ++ [c])

/-- What a translate handler sees. -/
structure TransView where
  object : Str
  start : Nat
  stop : Nat
  reason : String
  deriving Repr, DecidableEq

/-- What a translate handler did. -/
inductive TransResp where
  | raises (e : PyExc)
  /-- Not a tuple, a tuple of the wrong size, or a replacement that is not `str`. -/
  | bad
  | ret (rep : Str) (newpos : Int)
  deriving Repr, DecidableEq

abbrev TransCB := List TransView → TransResp

/-- The `errors` of `_PyUnicode_TranslateCharmap`. -/
inductive TH where
  | ignore
  | strict
  | custom (cb : TransCB)

/-- `unicode_translate_call_errorhandler`, unicodeobject.c:9125-9175, with
`make_translate_exception`, :9098-9119. -/
def translateCallback (cb : TransCB) (hist : List TransView) (input : Str) (start stop : Nat) :
    Py (List TransView × Str × Nat) := do
  let hist' := hist ++ [{ object := input, start, stop, reason := "character maps to <undefined>" }]
  match cb hist' with
  | .raises e => .error e
  | .bad => .error (.typeError "translating error handler must return (str, int) tuple")
  | .ret rep newpos0 =>
    let newpos0 ← ssizeOfIndex newpos0
    let len : Int := input.length
    let newpos := if newpos0 < 0 then len + newpos0 else newpos0
    if newpos < 0 ∨ newpos > len then
      .error (.indexError s!"position {newpos} from error handler out of bounds")
    else .ok (hist', rep, newpos.toNat)

/-- The outer `while (i<size)` of `_PyUnicode_TranslateCharmap`, unicodeobject.c:9438-9492. -/
def translateLoopX (m : MapH) (H : TH) (input : Str) :
    Nat → Nat → List Nat → Str → List Nat → List TransView → Py Str
  | 0, _, _, _, _, _ => .error .modelFuel
  | _ + 1, _, [], out, _, _ => .ok out
  | fuel + 1, i, ch :: cs, out, hist, th => do
    match ← charmaptranslateOutput (atCall m hist ch) ch with
    | some w => translateLoopX m H input fuel (i + 1) cs (out ++ w) (hist ++ [ch]) th
    | none =>
      let (rest, hist') ← collectUndefinedX m cs (hist ++ [ch])
      let collend := input.length - rest.length
      match H with
      | .ignore => translateLoopX m H input fuel collend rest out hist' th
      | .strict => .error (translateError input i collend)
      | .custom cb =>
        let (th', rep, newpos) ← translateCallback cb th input i collend
        translateLoopX m H input fuel newpos (input.drop newpos) (out ++ rep) hist' th'

/-- `ignore = (errors != NULL && strcmp(errors, "ignore") == 0)`, unicodeobject.c:9421. -/
def TH.isIgnore : TH → Bool
  | .ignore => true
  | _ => false

/-- `_PyUnicode_TranslateCharmap`, unicodeobject.c:9388-9502. -/
def translateCharmapX (m : MapH) (H : TH) (input : Str) (fuel : Nat) : Py Str :=
  if input.length = 0 then .ok input
  else
    if isAscii input then do
      let (res, out, i, hist) ← fastTranslateLoopX m H.isIgnore input (fun _ => 0xff) [] 0 []
      if res then .ok out
      else translateLoopX m H input fuel i (input.drop i) out hist []
    else translateLoopX m H input fuel 0 input [] [] []

/-- The general loop alone: what `_PyUnicode_TranslateCharmap` runs on a string that is not ASCII. -/
def translateSlowX (m : MapH) (H : TH) (input : Str) (fuel : Nat) : Py Str :=
  if input.length = 0 then .ok input else translateLoopX m H input fuel 0 input [] [] []

/-! ## A table with no state -/

theorem atCall_pure (m : Mapping) (hist : List Nat) (c : Nat) :
    atCall (pureH m) hist c = fun _ => m c := by
  funext x
  simp [atCall, pureH]

theorem lookup_at (m : Mapping) (c : Nat) :
    charmaptranslateLookup (fun _ => m c) c = charmaptranslateLookup m c := rfl

theorem output_at (m : Mapping) (c : Nat) :
    charmaptranslateOutput (fun _ => m c) c = charmaptranslateOutput m c := rfl

theorem fastLookup_at (m : Mapping) (c : Nat) (t : AsciiTable) :
    fastTranslateLookup (fun _ => m c) c t = fastTranslateLookup m c t := rfl

theorem collectUndefinedX_pure (m : Mapping) : ∀ (cs hist : List Nat),
    (collectUndefinedX (pureH m) cs hist).map (·.1) = collectUndefined m cs := by
  intro cs
  induction cs with
  | nil => intro hist; rfl
  | cons c t ih =>
    intro hist
    simp only [collectUndefinedX, collectUndefined, atCall_pure, lookup_at, bind, Except.bind]
    cases charmaptranslateLookup m c with
    | error e => rfl
    | ok l =>
      cases l
      all_goals first
        | rfl
        | exact ih _

theorem translateLoopX_pure (m : Mapping) (input : Str) : ∀ (fuel i : Nat) (rest out hist : List Nat)
    (th : List TransView),
    translateLoopX (pureH m) .ignore input fuel i rest out hist th =
      translateLoop m true input fuel i rest out := by
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ fuel ih =>
    intro i rest out hist th
    cases rest with
    | nil => rfl
    | cons ch cs =>
      simp only [translateLoopX, translateLoop, atCall_pure, output_at, bind, Except.bind]
      cases charmaptranslateOutput m ch with
      | error e => rfl
      | ok w =>
        cases w with
        | some w => exact ih ..
        | none =>
          have hc := collectUndefinedX_pure m cs (hist ++ [ch])
          cases hx : collectUndefinedX (pureH m) cs (hist ++ [ch]) with
          | error e =>
            rw [hx] at hc
            simp only [Except.map] at hc
            simp only [← hc]
          | ok p =>
            obtain ⟨rest, hist'⟩ := p
            rw [hx] at hc
            simp only [Except.map] at hc
            simp only [← hc]
            exact ih ..

theorem fastLoopX_pure (m : Mapping) (ignore : Bool) : ∀ (s : List Nat) (t : AsciiTable) (out : Str)
    (pos : Nat) (hist : List Nat),
    (fastTranslateLoopX (pureH m) ignore s t out pos hist).map (fun r => (r.1, r.2.1, r.2.2.1)) =
      fastTranslateLoop m ignore s t out pos := by
  intro s
  induction s with
  | nil => intros; rfl
  | cons ch cs ih =>
    intro t out pos hist
    simp only [fastTranslateLoopX, fastTranslateLoop, atCall_pure, fastLookup_at, bind, Except.bind]
    by_cases h : t ch = 0xff
    · simp only [h, if_true]
      cases fastTranslateLookup m ch t with
      | error e => rfl
      | ok p =>
        obtain ⟨tr, t'⟩ := p
        cases tr
        · rfl
        · simp only [Bool.not_true, Bool.false_eq_true, if_false]
          by_cases h2 : t' ch = 0xfe
          · simp only [h2, if_true]
            cases ignore
            · rfl
            · exact ih ..
          · simp only [h2, if_false]
            exact ih ..
    · simp only [h, if_false]
      by_cases h2 : t ch = 0xfe
      · simp only [h2, if_true]
        cases ignore
        · rfl
        · exact ih ..
      · simp only [h2, if_false]
        exact ih ..

theorem translateCharmapX_pure (m : Mapping) (s : Str) :
    translateCharmapX (pureH m) .ignore s (s.length + 1) = unicodeTranslate s m := by
  simp only [translateCharmapX, unicodeTranslate, translateCharmap, TH.isIgnore]
  split
  · rfl
  · split
    · have h := fastLoopX_pure m true s (fun _ => 0xff) [] 0 []
      cases hx : fastTranslateLoopX (pureH m) true s (fun _ => 0xff) [] 0 [] with
      | error e =>
        rw [hx] at h
        simp only [Except.map] at h
        simp only [bind, Except.bind, ← h]
      | ok p =>
        obtain ⟨res, out, i, hist⟩ := p
        rw [hx] at h
        simp only [Except.map] at h
        simp only [bind, Except.bind, ← h]
        split
        · rfl
        · exact translateLoopX_pure ..
    · exact translateLoopX_pure ..

/-- With a table that has no state, the ASCII fast path changes nothing: the fast and general paths
give the same result, success or failure, for every string. This is the narrow form of
`TranslateStatefulFastSlow`, which is false. -/
def TranslatePureFastSlow : Prop :=
  ∀ (m : Mapping) (s : Str),
    translateCharmapX (pureH m) .ignore s (s.length + 1) =
      translateSlowX (pureH m) .ignore s (s.length + 1)

theorem translatePureFastSlow_proven : TranslatePureFastSlow := by
  intro m s
  rw [translateCharmapX_pure, translateFastSlow_proven]
  simp only [translateSlowX]
  split
  · rename_i h
    have : s = [] := List.eq_nil_of_length_eq_zero h
    subst this
    rfl
  · rw [translateLoopX_pure, translateLoop_spec m s _ 0 s [] (by omega), withPrefix_nil]

/-! ## A table with state -/

/-- With any table, an ASCII string and a string that is not take the same path in spirit: the
fast path is an optimisation. Stated as: `translate` gives what the general loop alone gives. -/
def TranslateStatefulFastSlow : Prop :=
  ∀ (m : MapH) (s : Str),
    translateCharmapX m .ignore s (s.length + 1) = translateSlowX m .ignore s (s.length + 1)

/-- A table that answers 120 the first time and 121 after that. -/
def flipTable : MapH := fun hist => if hist.length = 1 then .int 120 else .int 121

/-- `'aa'.translate(flipTable)`: the fast path asks once and caches, so it gives `xx`; the general
loop asks twice and gives `xy`. -/
theorem translateStatefulFastSlow_refuted : ¬ TranslateStatefulFastSlow := by
  intro h
  have e := h flipTable [97, 97]
  revert e
  decide +kernel

/-- The fast path's cache works: if it finishes, it asked about each distinct character of the
string exactly once, in order of first appearance. For every table, with state or not. -/
def FastPathOneLookupPerChar : Prop :=
  ∀ (m : MapH) (ignore : Bool) (s : Str) (out : Str) (pos : Nat) (hist : List Nat),
    (∀ c ∈ s, c < 128) →
    fastTranslateLoopX m ignore s (fun _ => 0xff) [] 0 [] = .ok (true, out, pos, hist) →
    hist.Nodup ∧ ∀ c, c ∈ hist ↔ c ∈ s

/-- `ascii_table[c]` is set exactly for the characters asked about, and no value it holds looks
unset. -/
def TableSeen (t : AsciiTable) (hist : List Nat) : Prop :=
  ∀ c, c < 128 → (t c = 0xff ↔ c ∉ hist)

theorem fastLookup_table {m : Mapping} {ch : Nat} {t t' : AsciiTable} {tr : Bool}
    (h : fastTranslateLookup m ch t = .ok (tr, t')) (hch : ch < 128) (ht : tr = true) :
    t' ch ≠ 0xff ∧ ∀ c, c ≠ ch → t' c = t c := by
  subst ht
  have hset : ∀ v, v ≠ 0xff → (tableSet t ch v) ch ≠ 0xff ∧ ∀ c, c ≠ ch → (tableSet t ch v) c = t c := by
    intro v hv
    refine ⟨by simpa [tableSet] using hv, ?_⟩
    intro c hc
    simp [tableSet, hc]
  unfold fastTranslateLookup at h
  simp only [bind, Except.bind] at h
  cases hl : charmaptranslateLookup m ch with
  | error e =>
    rw [hl] at h
    cases h
  | ok l =>
    rw [hl] at h
    cases l with
    | pyNone =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.2]
      exact hset _ (by decide)
    | null =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.2]
      exact hset _ (by omega)
    | long r =>
      dsimp only at h
      split at h
      · simp at h
      · rename_i hr
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.2]
        exact hset _ (by omega)
    | str s =>
      dsimp only at h
      split at h
      · rename_i r
        split at h
        · simp at h
        · rename_i hr
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          rw [← h.2]
          exact hset _ (by omega)
      · simp at h

theorem nodup_snoc {l : List Nat} {c : Nat} (h : l.Nodup) (hc : c ∉ l) : (l ++ [c]).Nodup := by
  unfold List.Nodup at *
  rw [List.pairwise_append]
  refine ⟨h, by simp, ?_⟩
  intro a ha b hb
  simp only [List.mem_singleton] at hb
  subst hb
  exact fun e => hc (e ▸ ha)

theorem fastLoop_seen (m : MapH) (ignore : Bool) : ∀ (s : List Nat) (t : AsciiTable) (out : Str)
    (pos : Nat) (hist : List Nat) (out' : Str) (pos' : Nat) (hist' : List Nat),
    (∀ c ∈ s, c < 128) → TableSeen t hist → hist.Nodup →
    fastTranslateLoopX m ignore s t out pos hist = .ok (true, out', pos', hist') →
    hist'.Nodup ∧ ∀ c, c ∈ hist' ↔ c ∈ hist ∨ c ∈ s := by
  intro s
  induction s with
  | nil =>
    intro t out pos hist out' pos' hist' _ _ hn h
    simp only [fastTranslateLoopX, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, -, -, rfl⟩ := h
    simpa using hn
  | cons ch cs ih =>
    intro t out pos hist out' pos' hist' hs hseen hn h
    have hch : ch < 128 := hs ch List.mem_cons_self
    have hcs : ∀ c ∈ cs, c < 128 := fun c hc => hs c (List.mem_cons_of_mem _ hc)
    simp only [fastTranslateLoopX, bind, Except.bind] at h
    by_cases h1 : t ch = 0xff
    · rw [if_pos h1] at h
      have hnot : ch ∉ hist := (hseen ch hch).1 h1
      cases hl : fastTranslateLookup (atCall m hist ch) ch t with
      | error e =>
        rw [hl] at h
        cases h
      | ok p =>
        obtain ⟨tr, t'⟩ := p
        rw [hl] at h
        cases tr with
        | false => simp at h
        | true =>
          obtain ⟨g1, g2⟩ := fastLookup_table hl hch rfl
          have hseen' : TableSeen t' (hist ++ [ch]) := by
            intro c hc
            by_cases e : c = ch
            · subst e
              simp [g1]
            · rw [g2 c e, hseen c hc]
              simp [e]
          have hn' := nodup_snoc hn hnot
          have finish : ∀ (out2 : Str) (pos2 : Nat),
              fastTranslateLoopX m ignore cs t' out2 pos2 (hist ++ [ch]) = .ok (true, out', pos', hist') →
              hist'.Nodup ∧ ∀ c, c ∈ hist' ↔ c ∈ hist ∨ c ∈ ch :: cs := by
            intro out2 pos2 h2
            obtain ⟨r1, r2⟩ := ih _ _ _ _ _ _ _ hcs hseen' hn' h2
            refine ⟨r1, fun c => ?_⟩
            rw [r2 c]
            simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
            exact or_assoc
          simp only [Bool.not_true, Bool.false_eq_true, if_false] at h
          by_cases h2 : t' ch = 0xfe
          · rw [if_pos h2] at h
            cases ignore
            · simp at h
            · simp only [if_true] at h
              exact finish _ _ h
          · rw [if_neg h2] at h
            exact finish _ _ h
    · rw [if_neg h1] at h
      have hin : ch ∈ hist := Classical.byContradiction fun hc => h1 ((hseen ch hch).2 hc)
      have finish : ∀ (out2 : Str) (pos2 : Nat),
          fastTranslateLoopX m ignore cs t out2 pos2 hist = .ok (true, out', pos', hist') →
          hist'.Nodup ∧ ∀ c, c ∈ hist' ↔ c ∈ hist ∨ c ∈ ch :: cs := by
        intro out2 pos2 h2
        obtain ⟨r1, r2⟩ := ih _ _ _ _ _ _ _ hcs hseen hn h2
        refine ⟨r1, fun c => ?_⟩
        rw [r2 c]
        simp only [List.mem_cons]
        constructor
        · rintro (h | h)
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
        · rintro (h | h | h)
          · exact Or.inl h
          · exact Or.inl (h ▸ hin)
          · exact Or.inr h
      by_cases h2 : t ch = 0xfe
      · rw [if_pos h2] at h
        cases ignore
        · simp at h
        · simp only [if_true] at h
          exact finish _ _ h
      · rw [if_neg h2] at h
        exact finish _ _ h

theorem fastPathOneLookupPerChar_proven : FastPathOneLookupPerChar := by
  intro m ignore s out pos hist hs h
  have hseen : TableSeen (fun _ => 0xff) [] := by
    intro c _
    simp
  obtain ⟨r1, r2⟩ := fastLoop_seen m ignore s _ _ _ _ _ _ _ hs hseen (by simp [List.Nodup]) h
  exact ⟨r1, fun c => by simpa using r2 c⟩

/-! ## The documented reading -/

/-- What the `str.translate` docstring says a lookup means: a `LookupError` leaves the character
alone, `None` deletes it, an ordinal or a string replaces it. -/
def docImage (m : Mapping) (c : Nat) : Str :=
  match m c with
  | .missing => [c]
  | .pyNone => []
  | .int v => [v.toNat]
  | .str s => s
  | _ => []

/-- A lookup result the docstring allows. -/
def ItemOk : MapItem → Prop
  | .missing | .pyNone | .str _ => True
  | .int v => 0 ≤ v ∧ v ≤ maxUnicode
  | .wrong | .raises _ => False

/-- `str.translate` does what its docstring says, one character at a time, for every table with no
state whose answers are allowed, on the fast path and the general path alike. Unlike
`TranslatePureFastSlow`, this is against a reading written out by hand, so it depends on what the
lookup does. -/
def TranslateDocReading : Prop :=
  ∀ (m : Mapping) (s : Str), (∀ c ∈ s, ItemOk (m c)) →
    translateCharmapX (pureH m) .ignore s (s.length + 1) = .ok (s.flatMap (docImage m))

theorem translateSpec_doc (m : Mapping) : ∀ s : List Nat, (∀ c ∈ s, ItemOk (m c)) →
    translateSpec m s = .ok (s.flatMap (docImage m)) := by
  intro s
  induction s with
  | nil => intro _; rfl
  | cons c cs ih =>
    intro h
    have hc := h c List.mem_cons_self
    have hr := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [translateSpec, charmaptranslateOutput, charmaptranslateLookup, bind, Except.bind, hr,
      List.flatMap_cons, docImage]
    cases hm : m c with
    | missing => rfl
    | pyNone => rfl
    | str w => rfl
    | int v =>
      rw [hm] at hc
      obtain ⟨h1, h2⟩ := hc
      simp only
      rw [if_neg (by omega)]
      rfl
    | wrong =>
      rw [hm] at hc
      exact hc.elim
    | raises e =>
      rw [hm] at hc
      exact hc.elim

theorem translateDocReading_proven : TranslateDocReading := by
  intro m s h
  rw [translateCharmapX_pure, translateFastSlow_proven, translateSpec_doc m s h]

/-- The exception an answer raises, if it is one the docstring does not allow. -/
def badItem : MapItem → Option PyExc
  | .int v =>
    if v < 0 ∨ v > maxUnicode then some (.valueError "character mapping must be in range(0x110000)")
    else none
  | .wrong => some (.typeError "character mapping must return integer, None or str")
  | .raises e => some e
  | _ => none

/-- The first answer that is not allowed decides the result, whatever follows it. An ordinal out of
range and an object of the wrong type have their own errors, and any other exception from
`__getitem__` comes through. -/
def TranslateBadItem : Prop :=
  ∀ (m : Mapping) (pre : Str) (c : Nat) (post : Str) (e : PyExc), (∀ x ∈ pre, ItemOk (m x)) →
    badItem (m c) = some e →
    translateCharmapX (pureH m) .ignore (pre ++ c :: post) ((pre ++ c :: post).length + 1) = .error e

theorem translateSpec_bad (m : Mapping) (c : Nat) (post : Str) (e : PyExc) (hb : badItem (m c) = some e) :
    ∀ pre : Str, (∀ x ∈ pre, ItemOk (m x)) → translateSpec m (pre ++ c :: post) = .error e := by
  intro pre
  induction pre with
  | nil =>
    intro _
    simp only [List.nil_append, translateSpec, charmaptranslateOutput, charmaptranslateLookup, bind,
      Except.bind]
    cases hm : m c with
    | missing => simp [hm, badItem] at hb
    | pyNone => simp [hm, badItem] at hb
    | str w => simp [hm, badItem] at hb
    | wrong =>
      simp only [hm, badItem, Option.some.injEq] at hb
      subst hb
      rfl
    | raises x =>
      simp only [hm, badItem, Option.some.injEq] at hb
      subst hb
      rfl
    | int v =>
      simp only [hm, badItem] at hb
      split at hb
      · rename_i hr
        simp only [Option.some.injEq] at hb
        subst hb
        simp only
        rw [if_pos hr]
      · cases hb
  | cons a t ih =>
    intro h
    have ha := h a List.mem_cons_self
    have hr := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.cons_append, translateSpec, charmaptranslateOutput, charmaptranslateLookup, bind,
      Except.bind, hr]
    cases hm : m a with
    | missing => rfl
    | pyNone => rfl
    | str w => rfl
    | int v =>
      rw [hm] at ha
      obtain ⟨h1, h2⟩ := ha
      simp only
      rw [if_neg (by omega)]
    | wrong =>
      rw [hm] at ha
      exact ha.elim
    | raises x =>
      rw [hm] at ha
      exact ha.elim

theorem translateBadItem_proven : TranslateBadItem := by
  intro m pre c post e hp hb
  rw [translateCharmapX_pure, translateFastSlow_proven, translateSpec_bad m c post e hb pre hp]

/-- A translate handler's position lands inside the string. -/
def TranslateCallbackPosition : Prop :=
  ∀ (cb : TransCB) (hist : List TransView) (input : Str) (start stop : Nat)
    (hist' : List TransView) (rep : Str) (newpos : Nat),
    translateCallback cb hist input start stop = .ok (hist', rep, newpos) →
    newpos ≤ input.length ∧
    ∃ p, cb hist' = .ret rep p ∧ (newpos : Int) = if p < 0 then (input.length : Int) + p else p

theorem translateCallbackPosition_proven : TranslateCallbackPosition := by
  intro cb hist input start stop hist' rep newpos h
  simp only [translateCallback, bind, Except.bind] at h
  split at h
  · cases h
  · cases h
  · rename_i rep0 p0 hcb
    split at h
    · cases h
    · rename_i p hp
      have hsame : p0 = p := by
        unfold ssizeOfIndex at hp
        split at hp
        · cases hp
        · simpa using hp
      subst hsame
      by_cases hneg : p0 < 0
      · simp only [if_pos hneg] at h ⊢
        split at h
        · cases h
        · rename_i hin
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact ⟨by omega, p0, hcb, by simp only [if_pos hneg]; omega⟩
      · simp only [if_neg hneg] at h ⊢
        split at h
        · cases h
        · rename_i hin
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact ⟨by omega, p0, hcb, by simp only [if_neg hneg]; omega⟩

end PyLean.UnicodeObj
