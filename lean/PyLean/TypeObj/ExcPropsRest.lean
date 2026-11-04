import PyLean.TypeObj.ExcPropsBase

/-!
Properties of the subclasses: `ImportError`, `AttributeError`, `NameError`, `OSError`,
`SyntaxError`, the Unicode errors, `MemoryError`. Hypotheses are explained in `ExcPropsBase`.
-/

namespace PyLean.TypeObj

/-! ## Dict and member lemmas -/

theorem memGet_memSet_ne (d : ExcData) (n m : Name) (v : Option Val) (h : n ≠ m) :
    memGet (memSet n v d) m = memGet d m := by
  simp only [memGet, memSet]
  have hb : ∀ k : Name, k = n → (k == m) = false := by
    intro k hk
    subst hk
    simpa using h
  cases v with
  | none =>
    simp only
    induction d.members with
    | nil => simp [NameDict.erase]
    | cons p ps ih =>
      obtain ⟨k, x⟩ := p
      by_cases hk : k = n
      · simp [NameDict.erase, NameDict.get?, hk, hb n rfl]
      · have hk' : (k == n) = false := by simpa using hk
        simp [NameDict.erase, NameDict.get?, hk']
        split <;> simp_all
  | some x =>
    simp only
    induction d.members with
    | nil => simp [NameDict.set, NameDict.get?, hb n rfl]
    | cons p ps ih =>
      obtain ⟨k, y⟩ := p
      by_cases hk : k = n
      · simp [NameDict.set, NameDict.get?, hk, hb n rfl]
      · have hk' : (k == n) = false := by simpa using hk
        simp [NameDict.set, NameDict.get?, hk']
        split <;> simp_all

theorem isExc_memSet {w : World} {a : Addr} {d : ExcData} (h : IsExc w a d) (n : Name)
    (v : Option Val) : IsExc (excUpdW w a (memSet n v)) a (memSet n v d) := h.update _

theorem dictLookup_setEntry_same (es : List (Val × Val)) (k : String) (v : Val) :
    dictLookup (dictSetEntry es (.str k) v) (.str k) = some v := by
  induction es with
  | nil => simp [dictSetEntry, dictLookup, Val.is]
  | cons p ps ih =>
    obtain ⟨a, x⟩ := p
    by_cases h : a.is (.str k) = true
    · simp [dictSetEntry, dictLookup, h]
    · have h' : a.is (.str k) = false := by simpa using h
      simp [dictSetEntry, dictLookup, h', ih]

theorem dictLookup_setEntry_ne (es : List (Val × Val)) (k m : String) (v : Val) (h : k ≠ m) :
    dictLookup (dictSetEntry es (.str k) v) (.str m) = dictLookup es (.str m) := by
  have hkm : (Val.is (.str k) (.str m)) = false := by simpa [Val.is] using h
  induction es with
  | nil => simp [dictSetEntry, dictLookup, hkm]
  | cons p ps ih =>
    obtain ⟨a, x⟩ := p
    by_cases hak : a.is (.str k) = true
    · have ha : a = .str k := by
        cases a <;> simp_all [Val.is]
      subst ha
      simp [dictSetEntry, dictLookup, hkm, Val.is_refl]
    · have h' : a.is (.str k) = false := by simpa using hak
      simp [dictSetEntry, dictLookup, h']
      split <;> simp_all

/-! ## `ImportError`, `AttributeError`, `NameError` -/

/-- **`ImportError.msg` and `str`.** After `__init__`, `msg` holds the argument when there is
exactly one, and `str` of an exact-`str` `msg` is that `msg` whatever `args` says; otherwise
`str` is `BaseException_str`. Holds for every `name`/`path`/`name_from`. -/
def ImportErrorMsgStr : Prop :=
  (∀ (a : Addr) (d : ExcData) (m : Val) (w w' : World), IsExc w a d →
    importErrorInit (.obj a) [m] [] w = .ok () w' →
    memGet (excDataOf w' (.obj a)) "msg" = some m) ∧
  (∀ (rt : Rt) (v : Val) (s : String) (w : World), memGet (excDataOf w v) "msg" = some (.str s) →
    importErrorStr rt v w = .ok (.str s) w) ∧
  (∀ (rt : Rt) (v : Val) (w : World), (∀ s, memGet (excDataOf w v) "msg" ≠ some (.str s)) →
    importErrorStr rt v w = baseExceptionStr rt v w)

theorem importErrorMsgStr_proven : ImportErrorMsgStr := by
  refine ⟨?_, ?_, ?_⟩
  · intro a d m w w' hx h
    simp [importErrorInit, baseExceptionInit, argNoKeywords, argKeywordOnly, excUpdate_app,
      NameDict.get?, importMsg] at h
    subst h
    have h1 := hx.update (fun d => { d with args := [m] })
    have h2 := isExc_memSet h1 "name" none
    have h3 := isExc_memSet h2 "path" none
    have h4 := isExc_memSet h3 "name_from" none
    rw [(isExc_memSet h4 "msg" (some m)).data]
    exact memGet_memSet_same _ _ _
  · intro rt v s w h
    simp [importErrorStr, h]
  · intro rt v w h
    show (match memGet (excDataOf w v) "msg" with
      | some (.str s) => (pure (Val.str s) : M Val)
      | _ => baseExceptionStr rt v) w = baseExceptionStr rt v w
    cases hm : memGet (excDataOf w v) "msg" with
    | none => rfl
    | some x =>
      cases x with
      | str s => exact absurd hm (h s)
      | _ => rfl

/-- **`ImportError` and `AttributeError` pickle their `name`.** When the `name` member is set,
the state dict of `__reduce__` holds it. `AttributeError` puts `args` there too, and never
puts `obj` there. -/
def ReduceKeepsNameImportAttr : Prop :=
  (∀ (v n : Val) (w : World), memGet (excDataOf w v) "name" = some n →
    ∃ a w', importErrorGetstate v w = .ok (.obj a) w' ∧
      dictLookup ((dictOf w' (.obj a)).getD []) (.str "name") = some n) ∧
  (∀ (v n : Val) (w : World), memGet (excDataOf w v) "name" = some n →
    ∃ a w', attributeErrorGetstate v w = .ok (.obj a) w' ∧
      dictLookup ((dictOf w' (.obj a)).getD []) (.str "name") = some n ∧
      dictLookup ((dictOf w' (.obj a)).getD []) (.str "args") = some (.tuple (excArgs w v)))

theorem dictOf_alloc (w : World) (t : Addr) (es : List (Val × Val)) :
    dictOf { w with heap := w.heap.push (.val { cls := t, body := .dict es }) }
      (.obj w.heap.size) = some es := by
  simp [dictOf, payloadOf, get_push_size]

theorem reduceKeepsNameImportAttr_proven : ReduceKeepsNameImportAttr := by
  refine ⟨?_, ?_⟩
  · intro v n w h
    simp only [importErrorGetstate, M.bind_app, getW_app, h]
    simp only [Option.isSome_some, Bool.true_or, if_true, alloc_app]
    refine ⟨_, _, rfl, ?_⟩
    rw [dictOf_alloc]
    simp only [Option.getD_some]
    cases hp : memGet (excDataOf w v) "path" <;> cases hq : memGet (excDataOf w v) "name_from" <;>
      simp [optSetEntry, dictLookup_setEntry_ne, dictLookup_setEntry_same]
  · intro v n w h
    simp only [attributeErrorGetstate, M.bind_app, getW_app, h, alloc_app]
    refine ⟨_, _, rfl, ?_, ?_⟩
    · rw [dictOf_alloc]
      simp [optSetEntry, dictLookup_setEntry_ne, dictLookup_setEntry_same]
    · rw [dictOf_alloc]
      simp [dictLookup_setEntry_same, excArgs]

/-- **`NameError` pickles its `name`**, as `ImportError` and `AttributeError` do. FALSE:
`NameError` has no `__reduce__` of its own, so `BaseException.__reduce__` carries `args` and
the instance dict only, and `name` is not in either. -/
def NameErrorReduceKeepsName : Prop :=
  ∀ (v n : Val) (w : World), memGet (excDataOf w v) "name" = some n →
    ∃ (t a : Val) (st : Addr) (w' : World),
      baseExceptionReduce v w = .ok (.tuple [t, a, .obj st]) w' ∧
      dictLookup ((dictOf w' (.obj st)).getD []) (.str "name") = some n

theorem nameErrorReduceKeepsName_refuted : ¬NameErrorReduceKeepsName := by
  intro h
  let d : ExcData := { args := [.str "x"], members := [("name", .str "y")] }
  let w : World := { heap := #[.val { cls := B.NameError, body := .exc d }] }
  have hm : memGet (excDataOf w (.obj 0)) "name" = some (.str "y") := by
    simp [memGet, excDataOf, payloadOf, World.get, w, d, NameDict.get?]
  obtain ⟨t, a, st, w', hr, _⟩ := h (.obj 0) (.str "y") w hm
  simp [baseExceptionReduce, instDictAddr, World.get, w] at hr

/-- **`NameError_init` stores the keyword and only the keyword.** -/
def NameErrorInitKeyword : Prop :=
  ∀ (a : Addr) (d : ExcData) (args : List Val) (n : Val) (w w' : World), IsExc w a d →
    nameErrorInit (.obj a) args [("name", n)] w = .ok () w' →
    excArgs w' (.obj a) = args ∧ memGet (excDataOf w' (.obj a)) "name" = some n

theorem nameErrorInitKeyword_proven : NameErrorInitKeyword := by
  intro a d args n w w' hx h
  simp only [nameErrorInit, baseExceptionInit, argNoKeywords, argKeywordOnly, M.bind_app,
    getW_app] at h
  simp [excUpdate_app, NameDict.get?] at h
  subst h
  have h1 := hx.update (fun d => { d with args := args })
  constructor
  · simp [excArgs, excUpdW_data h1, memSet]
  · simp only [excUpdW_data h1]
    exact memGet_memSet_same _ _ _

/-! ## `OSError` -/

/-- **`__new__` or `__init__`, never both.** When `oserror_use_init` holds, `OSError_new`
parses nothing, not even keywords, and when it does not hold, `OSError_init` does nothing. So
arguments are processed exactly once. -/
def OsErrorParsedOnce : Prop :=
  (∀ (rt : Rt) (t : Addr) (args : List Val) (kw : Kw) (w : World), oserrorUseInit w t = true →
    osErrorNewClass rt t args kw w = .ok (t, {}) w) ∧
  (∀ (rt : Rt) (self : Val) (args : List Val) (kw : Kw) (w : World),
    oserrorUseInit w (typeOf w self) = false → osErrorInit rt self args kw w = .ok () w)

theorem osErrorParsedOnce_proven : OsErrorParsedOnce := by
  refine ⟨?_, ?_⟩
  · intro rt t args kw w h
    simp [osErrorNewClass, h]
  · intro rt self args kw w h
    simp [osErrorInit, h]

/-- **Only `OSError` itself is remapped.** `OSError(errno, ...)` may return a subclass from
`errnomap`; a call on any other class keeps that class, for every `errno` argument and every
`__hash__` it may have. -/
def OsErrorRemapOnlyExact : Prop :=
  ∀ (rt : Rt) (t c : Addr) (args : List Val) (kw : Kw) (p : OsParsed) (w w' : World),
    t ≠ B.OSError → osErrorNewClass rt t args kw w = .ok (c, p) w' → c = t

theorem osErrorRemapOnlyExact_proven : OsErrorRemapOnlyExact := by
  intro rt t c args kw p w w' ht h
  have ht' : (t == B.OSError) = false := by simpa using ht
  simp only [osErrorNewClass, M.bind_app, getW_app] at h
  split at h
  · simp at h
    exact h.1.1.symm
  · simp only [argNoKeywords] at h
    cases hk : kw.isEmpty with
    | false => simp [hk, typeErr, raiseC] at h
    | true =>
      simp [hk] at h
      cases hm : (oserrorParseArgs args).myerrno with
      | none =>
        simp [hm] at h
        exact h.1.1.symm
      | some e =>
        simp [hm, ht] at h
        exact h.1.1.symm

/-- **`errnomap` targets `OSError` subclasses and has one entry per key.** Every target's
row in the type table has `OSError` in its base chain. -/
def ErrnoMapWellFormed : Prop :=
  (errnoMap.map (·.1)).Nodup ∧
  ∀ p ∈ errnoMap, B.OSError ≠ p.2

theorem errnoMapWellFormed_proven : ErrnoMapWellFormed := by
  constructor
  · decide
  · decide

/-- **Argument positions.** With 2 to 5 arguments, `errno`, `strerror`, `filename`, `filename2`
are positions 0, 1, 2 and 4. Outside that range nothing is parsed. -/
def OsErrorParsePositions : Prop :=
  ∀ args : List Val,
    (2 ≤ args.length ∧ args.length ≤ 5 →
      let p := oserrorParseArgs args
      p.myerrno = args[0]? ∧ p.strerror = args[1]? ∧ p.filename = args[2]? ∧ p.filename2 = args[4]?) ∧
    (¬(2 ≤ args.length ∧ args.length ≤ 5) →
      let p := oserrorParseArgs args
      p.myerrno = none ∧ p.strerror = none ∧ p.filename = none ∧ p.filename2 = none)

theorem osErrorParsePositions_proven : OsErrorParsePositions := by
  intro args
  constructor
  · intro h
    simp [oserrorParseArgs, h]
  · intro h
    simp [oserrorParseArgs, h]

/-- **`__reduce__` round-trips the filenames.** When `args` has the two parsed items and a
filename is set, parsing the reduced arguments recovers `errno`, `strerror`, `filename` and
`filename2`. -/
def OsErrorReduceRoundTrip : Prop :=
  ∀ (d : ExcData) (a b fn : Val), d.args = [a, b] → memGet d "filename" = some fn →
    let p := oserrorParseArgs (osReduceArgs d)
    p.myerrno = some a ∧ p.strerror = some b ∧ p.filename = some fn ∧
      p.filename2 = memGet d "filename2"

theorem osErrorReduceRoundTrip_proven : OsErrorReduceRoundTrip := by
  intro d a b fn h1 h2
  cases h3 : memGet d "filename2" <;> simp [osReduceArgs, oserrorParseArgs, h1, h2, h3]

/-- **`OSError.__str__` falls back to `BaseException_str`** when there is no filename and
`errno` or `strerror` is unset. -/
def OsErrorStrFallback : Prop :=
  ∀ (rt : Rt) (v : Val) (w : World), memGet (excDataOf w v) "filename" = none →
    (memGet (excDataOf w v) "errno" = none ∨ memGet (excDataOf w v) "strerror" = none) →
    osErrorStr rt v w = baseExceptionStr rt v w

theorem osErrorStrFallback_proven : OsErrorStrFallback := by
  intro rt v w h1 h2
  simp only [osErrorStr, M.bind_app, getW_app, h1]
  rcases h2 with h | h <;> simp [h]

/-- **`characters_written` reads what was written**, except that `-1` is the "unset" value:
a `Py_ssize_t` other than `-1` comes back, `-1` reads as `AttributeError`. -/
def OsErrorWrittenRoundTrip : Prop :=
  ∀ (rt : Rt) (a : Addr) (d : ExcData) (n : Int) (w w' : World), IsExc w a d →
    osErrorWrittenSet rt (.obj a) (some (.int n)) w = .ok () w' →
    (n ≠ -1 → osErrorWrittenGet (.obj a) w' = .ok (.int n) w') ∧
    (n = -1 → osErrorWrittenGet (.obj a) w' =
      .err (.exc B.AttributeError "characters_written" none) w')

theorem osErrorWrittenRoundTrip_proven : OsErrorWrittenRoundTrip := by
  intro rt a d n w w' hx h
  have hw : w' = excUpdW w a (fun d => { d with written := n }) := by
    simp only [osErrorWrittenSet, excAsSsizeValueError, excNumberIndex, intOf, M.bind_app,
      getW_app] at h
    by_cases hs : inSsize n = true
    · simp [hs, excUpdate_app] at h
      exact h.symm
    · simp [hs, valueErr, raiseC] at h
  subst hw
  have hd := excUpdW_data hx (fun d => { d with written := n })
  constructor
  · intro hn
    simp [osErrorWrittenGet, hd, hn]
  · intro hn
    subst hn
    simp only [osErrorWrittenGet, M.bind_app, getW_app, hd]
    simp [attrErr, raiseC]

/-! ## `SyntaxError` -/

/-- The offset loop only moves past a separator it has seen. -/
theorem basenameOffset_spec (cs : List Char) (i off : Nat) :
    (basenameOffset i off cs = off ∧ sepChar ∉ cs) ∨
    (i < basenameOffset i off cs ∧ basenameOffset i off cs ≤ i + cs.length ∧
      sepChar ∉ cs.drop (basenameOffset i off cs - i)) := by
  induction cs generalizing i off with
  | nil => simp [basenameOffset]
  | cons c cs ih =>
    simp only [basenameOffset]
    by_cases hc : (c == sepChar) = true
    · have hc' : c = sepChar := by simpa using hc
      simp only [hc, if_true]
      rcases ih (i + 1) (i + 1) with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
      · right
        rw [h1]
        refine ⟨by omega, by simp only [List.length_cons]; omega, ?_⟩
        have : i + 1 - i = 1 := by omega
        rw [this]
        simpa using h2
      · right
        refine ⟨by omega, by simp only [List.length_cons]; omega, ?_⟩
        have hk : basenameOffset (i + 1) (i + 1) cs - i = (basenameOffset (i + 1) (i + 1) cs - (i + 1)) + 1 := by
          omega
        rw [hk, List.drop_succ_cons]
        exact h3
    · have hf : (c == sepChar) = false := by simpa using hc
      simp only [hf, if_false, Bool.false_eq_true]
      rcases ih (i + 1) off with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
      · left
        refine ⟨h1, ?_⟩
        have hne : sepChar ≠ c := by
          intro he
          subst he
          simp at hf
        simp [hne, h2]
      · right
        refine ⟨by omega, by simp only [List.length_cons]; omega, ?_⟩
        have hk : basenameOffset (i + 1) off cs - i = (basenameOffset (i + 1) off cs - (i + 1)) + 1 := by
          omega
        rw [hk, List.drop_succ_cons]
        exact h3

/-- **`my_basename` returns the part after the last separator**: a suffix of the name with
no separator in it. -/
def MyBasenameSuffix : Prop :=
  ∀ name : String,
    (∃ pre, name.toList = pre ++ (myBasename name).toList) ∧ sepChar ∉ (myBasename name).toList

theorem myBasenameSuffix_proven : MyBasenameSuffix := by
  intro name
  rcases basenameOffset_spec name.toList 0 0 with ⟨h1, h2⟩ | ⟨h1, _, h3⟩
  · simp only [myBasename, h1]
    exact ⟨⟨[], by simp⟩, by simpa using h2⟩
  · have hne : basenameOffset 0 0 name.toList ≠ 0 := by omega
    simp only [myBasename, bne_iff_ne, ne_eq, hne, not_false_eq_true, if_true]
    simp only [Nat.sub_zero] at h3
    refine ⟨⟨name.toList.take (basenameOffset 0 0 name.toList), ?_⟩, ?_⟩
    · simp [List.take_append_drop]
    · simpa using h3

/-- **`__str__` cannot overflow.** `%ld` of `lineno` prints a value in the range of `long`,
`-1` for anything outside it, so `SyntaxError_str` never raises `OverflowError`. -/
def SyntaxErrorLinenoInRange : Prop :=
  ∀ i : Int, inSsize (longOrMinusOne i) = true ∧ (inSsize i = true → longOrMinusOne i = i)

theorem syntaxErrorLinenoInRange_proven : SyntaxErrorLinenoInRange := by
  intro i
  constructor
  · unfold longOrMinusOne
    split
    · assumption
    · simp [inSsize, PyLean.ssizeMin, PyLean.ssizeMax]
  · intro h
    simp [longOrMinusOne, h]

/-! ## The Unicode errors -/

/-- **`unicode_error_adjust_start`, `_end`, `_len` satisfy their asserts** for every value of
`start` and `end` and every length. These are the statements of
`assert_adjusted_unicode_error_start`, `_end` and `_len`, compiled out of release builds. -/
def UnicodeAdjustInRange : Prop :=
  ∀ start e n : Int, 0 ≤ n →
    let s := unicodeErrorAdjustStart start n
    let t := unicodeErrorAdjustEnd e n
    adjustedStartOk s n ∧ adjustedEndOk t n ∧ adjustedLenOk (unicodeErrorAdjustLen s t) n

theorem unicodeAdjustInRange_proven : UnicodeAdjustInRange := by
  intro start e n hn
  simp only [unicodeErrorAdjustStart, unicodeErrorAdjustEnd, unicodeErrorAdjustLen,
    adjustedStartOk, adjustedEndOk, adjustedLenOk]
  by_cases h0 : n = 0
  · subst h0
    simp
    split <;> split <;> omega
  · have h1 : 1 ≤ n := by omega
    refine ⟨?_, ?_, ?_⟩ <;> (repeat' split) <;> simp_all <;> omega

/-- **`_PyUnicodeError_GetParams` returns clipped values**, for every `object`, `start` and
`end`: on success `0 <= start`, `end <= len`, and `slen` lies in `[0, len]`. -/
def UnicodeGetParamsInRange : Prop :=
  ∀ (self : Val) (asBytes : Bool) (p : UParams) (w w' : World),
    unicodeErrorGetParams self asBytes w = .ok p w' →
    0 ≤ p.objlen ∧ adjustedStartOk p.start p.objlen ∧ adjustedEndOk p.«end» p.objlen ∧
    adjustedLenOk p.slen p.objlen

theorem unicodeObjectLen_nonneg (w : World) (v : Val) (b : Bool) : 0 ≤ unicodeObjectLen w v b := by
  unfold unicodeObjectLen
  split <;> omega

theorem unicodeGetParamsInRange_proven : UnicodeGetParamsInRange := by
  intro self asBytes p w w' h
  simp only [unicodeErrorGetParams, M.bind_app, getW_app] at h
  cases hr : asUnicodeErrorAttribute (memGet (excDataOf w self) "object") "object" asBytes w with
  | err e w1 => simp [hr] at h
  | ok r w1 =>
    simp only [hr] at h
    simp at h
    obtain ⟨hp, _⟩ := h
    subst hp
    have hn := unicodeObjectLen_nonneg w1 r asBytes
    have := unicodeAdjustInRange_proven (ssizeMember (excDataOf w self) "start")
      (ssizeMember (excDataOf w self) "end") _ hn
    exact ⟨hn, this⟩

/-- **`__str__` reads the object only in bounds.** The guard of all three `__str__`s implies
`0 <= start < len`, so the read of one character or byte is valid, for every `start`, `end`
and `len`, including values a user assigned. -/
def UnicodeStrReadInBounds : Prop :=
  ∀ start e len : Int, unicodeStrSingle start e len = true →
    0 ≤ start ∧ start < len ∧ start.toNat < len.toNat ∧ e = start + 1

theorem unicodeStrReadInBounds_proven : UnicodeStrReadInBounds := by
  intro start e len h
  simp only [unicodeStrSingle, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, _⟩, _⟩, h3⟩ := h
  refine ⟨h1, h2, by omega, h3⟩

/-- **The `object` check comes first.** `check_unicode_error_attribute` raises `TypeError`
when the attribute is NULL or of the wrong type, and succeeds without changing anything
otherwise. -/
def UnicodeAttributeCheck : Prop :=
  (∀ (name : String) (b : Bool) (w : World), checkUnicodeErrorAttribute none name b w =
    .err (.exc B.TypeError s!"UnicodeError '{name}' attribute is not set" none) w) ∧
  (∀ (a : Val) (name : String) (w : World), (strOf w a).isSome = true →
    checkUnicodeErrorAttribute (some a) name false w = .ok () w) ∧
  (∀ (a : Val) (name : String) (w : World), (bytesOf w a).isSome = true →
    checkUnicodeErrorAttribute (some a) name true w = .ok () w) ∧
  (∀ (a : Val) (name : String) (w : World), (strOf w a).isSome = false →
    checkUnicodeErrorAttribute (some a) name false w =
      .err (.exc B.TypeError s!"UnicodeError '{name}' attribute must be a {"string"}" none) w)

theorem unicodeAttributeCheck_proven : UnicodeAttributeCheck := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro name b w
    simp [checkUnicodeErrorAttribute, typeErr, raiseC]
  · intro a name w h
    simp [checkUnicodeErrorAttribute, h]
  · intro a name w h
    simp [checkUnicodeErrorAttribute, h]
  · intro a name w h
    simp [checkUnicodeErrorAttribute, h, typeErr, raiseC]

theorem checkUnicodeErrorType_world (self : Val) (n : String) (u : Unit) (w w' : World)
    (h : checkUnicodeErrorType self n w = .ok u w') : w' = w := by
  simp only [checkUnicodeErrorType, M.bind_app, getW_app] at h
  by_cases hc : isSubtype w (typeOf w self) B.UnicodeError = true
  · simp [hc] at h
    exact h.symm
  · simp [hc, typeErr, raiseC] at h

theorem ssizeMember_memSet (d : ExcData) (n : Name) (i : Int) :
    ssizeMember (memSet n (some (.int i)) d) n = i := by
  simp [ssizeMember, memGet_memSet_same]

/-- **The C API stores what it is given and clips what it reads.** `PyUnicode*Error_SetStart`
stores the raw value, and `_PyUnicodeError_GetParams` returns it through
`unicode_error_adjust_start`; `SetEnd` and `unicode_error_adjust_end` likewise, for every kind
of error and every `Py_ssize_t`. A non-`UnicodeError` is a `TypeError`. -/
def UnicodeCapiStartEnd : Prop :=
  (∀ (k : UKind) (a : Addr) (d : ExcData) (s : Int) (p : UParams) (w w' w2 : World),
    IsExc w a d →
    pyUnicodeErrorSetStart k (.obj a) s w = .ok () w' →
    unicodeErrorGetParams (.obj a) k.asBytes w' = .ok p w2 →
    p.start = unicodeErrorAdjustStart s p.objlen) ∧
  (∀ (k : UKind) (a : Addr) (d : ExcData) (e : Int) (p : UParams) (w w' w2 : World),
    IsExc w a d →
    pyUnicodeErrorSetEnd k (.obj a) e w = .ok () w' →
    unicodeErrorGetParams (.obj a) k.asBytes w' = .ok p w2 →
    p.«end» = unicodeErrorAdjustEnd e p.objlen) ∧
  (∀ (k : UKind) (self : Val) (w : World), isSubtype w (typeOf w self) B.UnicodeError = false →
    pyUnicodeErrorGetStart k self w =
      .err (.exc B.TypeError s!"expecting a {k.name} object, got {typeFQN w (typeOf w self)}" none) w)

theorem unicodeCapiStartEnd_proven : UnicodeCapiStartEnd := by
  refine ⟨?_, ?_, ?_⟩
  · intro k a d s p w w' w2 hx h hp
    simp only [pyUnicodeErrorSetStart, M.bind_app] at h
    cases hc : checkUnicodeErrorType (.obj a) k.name w with
    | err e w1 => simp [hc] at h
    | ok u w1 =>
      have hw := checkUnicodeErrorType_world _ _ _ _ _ hc
      subst hw
      simp only [hc, unicodeErrorSetStartImpl, excUpdate_app] at h
      simp at h
      subst h
      simp only [unicodeErrorGetParams, M.bind_app, getW_app] at hp
      simp only [excUpdW_data hx] at hp
      cases hr : asUnicodeErrorAttribute (memGet (memSet "start" (some (.int s)) d) "object")
          "object" k.asBytes (excUpdW w1 a (memSet "start" (some (.int s)))) with
      | err e w3 => simp [hr] at hp
      | ok r w3 =>
        simp only [hr] at hp
        simp at hp
        obtain ⟨hp1, _⟩ := hp
        subst hp1
        simp [ssizeMember_memSet]
  · intro k a d e p w w' w2 hx h hp
    simp only [pyUnicodeErrorSetEnd, M.bind_app] at h
    cases hc : checkUnicodeErrorType (.obj a) k.name w with
    | err e' w1 => simp [hc] at h
    | ok u w1 =>
      have hw := checkUnicodeErrorType_world _ _ _ _ _ hc
      subst hw
      simp only [hc, unicodeErrorSetEndImpl, excUpdate_app] at h
      simp at h
      subst h
      simp only [unicodeErrorGetParams, M.bind_app, getW_app] at hp
      simp only [excUpdW_data hx] at hp
      cases hr : asUnicodeErrorAttribute (memGet (memSet "end" (some (.int e)) d) "object")
          "object" k.asBytes (excUpdW w1 a (memSet "end" (some (.int e)))) with
      | err e' w3 => simp [hr] at hp
      | ok r w3 =>
        simp only [hr] at hp
        simp at hp
        obtain ⟨hp1, _⟩ := hp
        subst hp1
        simp [ssizeMember_memSet]
  · intro k self w h
    simp [pyUnicodeErrorGetStart, checkUnicodeErrorType, h, typeErr, raiseC]

/-- **Every `__init__` keeps `args` when it fails.** `BaseException_init` runs before the
format is parsed, so an arity error leaves the new `args` in place. -/
def UnicodeInitArgsFirst : Prop :=
  ∀ (rt : Rt) (a : Addr) (d : ExcData) (args : List Val) (w : World), IsExc w a d →
    args.length ≠ 5 →
    ∃ w' e, unicodeEncodeErrorInit rt (.obj a) args [] w = .err e w' ∧
      excArgs w' (.obj a) = args

theorem argCount_err (f : Option String) (min max n : Nat) (w : World)
    (h : n < min ∨ max < n) : ∃ m, argCount f min max n w = .err (.exc B.TypeError m none) w := by
  have hc : (decide (n < min) || decide (max < n)) = true := by simpa using h
  simp [argCount, hc, typeErr, raiseC]

theorem unicodeInitArgsFirst_proven : UnicodeInitArgsFirst := by
  intro rt a d args w hx hn
  obtain ⟨m, hm⟩ := argCount_err none 5 5 args.length
    (excUpdW w a (fun d => { d with args := args })) (by omega)
  have h0 : baseExceptionInit (.obj a) args [] w =
      .ok () (excUpdW w a (fun d => { d with args := args })) := by
    simp [baseExceptionInit, argNoKeywords, excUpdate_app]
  refine ⟨excUpdW w a (fun d => { d with args := args }), .exc B.TypeError m none, ?_, ?_⟩
  · simp only [unicodeEncodeErrorInit, M.bind_app, h0, hm]
  · simp [excArgs, excUpdW_data hx]

/-! ## `MemoryError` and its freelist -/

/-- **A `MemoryError` from the freelist looks fresh.** FALSE: `BaseException_clear` does not
reset `suppress_context`, and neither does `get_memory_error`, so the flag of a dead
`MemoryError` shows up on the next one. -/
def MemoryErrorFreelistFresh : Prop :=
  ∀ (d : ExcData) (s : MemFreelist) (r : ExcData) (s' : MemFreelist),
    s.length < memerrorsSave →
    getMemoryError true [] (memoryErrorDealloc true d s) = (.reused r, s') →
    r.suppressContext = false

theorem memoryErrorFreelistFresh_refuted : ¬MemoryErrorFreelistFresh := by
  intro h
  have := h { suppressContext := true } [] _ [] (by decide) rfl
  simp [baseExceptionClear] at this

/-- **`MemoryError.__new__` keeps its arguments**, as `BaseException.__new__` and subclasses
of `MemoryError` do. FALSE: the freelist path of `get_memory_error` sets `args` to the empty
tuple. -/
def MemoryErrorNewKeepsArgs : Prop :=
  ∀ (args : List Val) (v : Val) (w w' : World),
    memoryErrorNew B.MemoryError args w = .ok v w' → excArgs w' v = args

theorem memoryErrorNewKeepsArgs_refuted : ¬MemoryErrorNewKeepsArgs := by
  intro h
  let w : World := {}
  have hr : memoryErrorNew B.MemoryError [.int 1] w =
      .ok (.obj w.heap.size) { w with heap := w.heap.push (.val { cls := B.MemoryError, body := .exc { args := [] } }) } := by
    simp [memoryErrorNew, baseExceptionNew, alloc_app]
  have := h _ _ _ _ hr
  rw [excArgs, (isExc_alloc w _ _).data] at this
  simp at this

/-- **The freelist has a bound and survives startup.** `MemoryError_dealloc` never takes the
list past `MEMERRORS_SAVE`, ignores subclasses, and `preallocate_memerrors` fills it. An empty
list with allocation forbidden gives the shared last-resort error, and teardown empties it. -/
def MemoryErrorFreelistBound : Prop :=
  (∀ (exact : Bool) (d : ExcData) (s : MemFreelist), s.length ≤ memerrorsSave →
    (memoryErrorDealloc exact d s).length ≤ memerrorsSave) ∧
  (∀ (d : ExcData) (s : MemFreelist), memoryErrorDealloc false d s = s) ∧
  preallocateMemerrors.length = memerrorsSave ∧
  (pyErrNoMemory []).1 matches .lastResort ∧
  (∀ s, freePreallocatedMemerrors s = [])

theorem memoryErrorFreelistBound_proven : MemoryErrorFreelistBound := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro exact d s h
    unfold memoryErrorDealloc
    cases exact with
    | false => simpa
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, if_false]
      split
      · simp
        omega
      · exact h
  · intro d s
    simp [memoryErrorDealloc]
  · rfl
  · rfl
  · intro s
    induction s with
    | nil => rfl
    | cons _ _ ih => exact ih

end PyLean.TypeObj
