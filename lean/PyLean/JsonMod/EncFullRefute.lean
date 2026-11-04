import PyLean.JsonMod.EncFullProps

/-!
The hypotheses of `DumpsTwinsX` are needed: each statement below drops one and is refuted on
CPython 3.15.2 (bugs/json-twins-recursion-limit.yaml, bugs/json-encoder-notes-twins.yaml,
bugs/json-separator-str-subclass.yaml, bugs/json-container-subclass-twins.yaml).
-/

namespace PyLean.JsonMod

open PyLean

theorem okx_default : XCfg.Okx {} :=
  ⟨rfl, rfl, rfl, fun n t v' h => by simp [defaultErr] at h⟩

/-- Every string a Python `str` and ASCII `float.__repr__`; containers of every kind (`sub`) and
keys of every type (`anyKey`) when asked. -/
def XKey.vld (anyKey : Bool) : XKey → Bool
  | .str s => strOk s
  | .flt _ r => fltOk r
  | .obj t _ => anyKey || decide (truncName 100 t.tpName = t.name)
  | _ => true

mutual
def XVal.vld (sub anyKey : Bool) : XVal → Bool
  | .str s => strOk s
  | .flt _ r => fltOk r
  | .seq _ xs => XVal.vldList sub anyKey xs
  | .map _ kvs => XVal.vldItems sub anyKey kvs
  | .seqSub _ _ ys _ => sub && XVal.vldList sub anyKey ys
  | .mapSub _ _ _ _ its _ => sub && XVal.vldTrip sub anyKey its
  | _ => true
def XVal.vldList (sub anyKey : Bool) : List XVal → Bool
  | [] => true
  | x :: xs => x.vld sub anyKey && XVal.vldList sub anyKey xs
def XVal.vldItems (sub anyKey : Bool) : List (XKey × XVal) → Bool
  | [] => true
  | (k, x) :: xs => k.vld anyKey && x.vld sub anyKey && XVal.vldItems sub anyKey xs
def XVal.vldTrip (sub anyKey : Bool) : List (ItemShape × XKey × XVal) → Bool
  | [] => true
  | (_, k, x) :: xs => k.vld anyKey && x.vld sub anyKey && XVal.vldTrip sub anyKey xs
end

/-! ### Recursion -/

/-- `json.dumps` with and without `_json`: the same text or the same exception (class and message,
notes aside), for every stack room and frame budget, on the values of `DumpsTwinsX`. -/
def DumpsTwinsRec : Prop :=
  ∀ (cfg : XCfg) (c p : Nat) (v : XVal), cfg.Okx → v.okx = true → SameExc (dumpsCX cfg c v) (dumpsPyX cfg p v)

/-- `[[]]` with two levels of stack room and three frames: C encodes it, Python needs four frames.
At the default recursion limit, `json.dumps` of lists 1000 deep. -/
theorem dumpsTwinsRec_refuted : ¬ DumpsTwinsRec := by
  intro h
  have h1 := h {} 2 3 (nestL 1) okx_default (nestL_okx 1)
  obtain ⟨t, ht⟩ := (dumpsCX_nest {} 2 1).1 (by decide)
  obtain ⟨ns, hns⟩ := (dumpsPyX_nest {} 3 1).2 (by omega)
  rw [ht, hns] at h1
  rcases h1 with ⟨_, h2, h3⟩ | ⟨_, _, _, h2, _⟩ <;> cases h2 <;> cases h3

/-! ### Notes -/

def tSet : PyType := { name := "set" }

/-- `{1: set()}`. -/
def wNotes : XVal := .map tDict [(.int 1, .other 0 tSet)]

theorem wNotes_C : dumpsCX {} 10 wNotes = .error (defaultErr "set", [.key tDict (.orig (.int 1))]) := by
  simp [wNotes, dumpsCX, cObjX, cEnterX, cContX, cMapPart, cExactItems, cMapItemsX, cKeyX, intRepr,
    decDigits, decDigitsF, maxStrDigits, cWriteStringX, cFastEncode, writeStrObj, SObj.ofStr, xe, addNote, cNoteKey,
    XCfg.toE, writeEscapedAscii, asciiEscapeSize, Except.map, tSet]

theorem wNotes_Py : dumpsPyX {} 10 wNotes = .error (defaultErr "set", [.key tDict (.conv (cs "1"))]) := by
  simp [wNotes, dumpsPyX, iterJoinPyX, pyCallX, pyIterX, pyContX, pyDictPart.eq_def, pyExactItems, Except.map,
    tSet, cExactItems, pyDictItemsX, pyKeyX, intRepr, decDigits, decDigitsF, maxStrDigits, pyEncStrX,
    needsReplace, xe, addNote, pyItemX, liftE, SObj.ofStr]
  decide

/-- On exact containers (keys of every type), when neither twin raises its `RecursionError`:
the same text, or the same exception with the same notes as printed (`%T` and `%R` of the original
key in C, `__name__` and the converted key in Python). -/
def DumpsTwinsNotes : Prop :=
  ∀ (cfg : XCfg) (c p : Nat) (v : XVal), cfg.Okx → v.vld false true = true →
    ¬ IsRecCX (dumpsCX cfg c v) → ¬ IsRecPyX (dumpsPyX cfg p v) → SameShown (dumpsCX cfg c v) (dumpsPyX cfg p v)

/-- `json.dumps({1: set()})`: C's note is `when serializing dict item 1`, Python's `when serializing
dict item '1'`. (So is a class outside `__main__`, `%T` printing `mymod.Foo` where Python prints
`Foo`, and the message for a `datetime.date` key: `not datetime.date` in C, `not date` in Python.) -/
theorem dumpsTwinsNotes_refuted : ¬ DumpsTwinsNotes := by
  intro h
  have h1 := h {} 10 10 wNotes okx_default (by decide)
    (by rw [wNotes_C]; rintro ⟨ns, h⟩; cases h)
    (by rw [wNotes_Py]; rintro ⟨ns, h⟩; cases h)
  rw [wNotes_C, wNotes_Py] at h1
  rcases h1 with ⟨_, h2, _⟩ | ⟨e, nsC, nsP, h2, h3, h4⟩
  · cases h2
  · cases h2; cases h3
    simp only [List.map_cons, List.map_nil, showC, showPy, NoteKey.shown, KeyShown.ofKey,
      List.cons.injEq, NoteShown.key.injEq, and_true] at h4
    cases h4.2

/-! ### Separators -/

/-- `str` subclasses whose `__str__` returns `'X'`, as both separators. -/
def cfgSepX : XCfg := { itemSep := ⟨cs ",", false, .ok (cs "X")⟩, keySep := ⟨cs ":", false, .ok (cs "X")⟩ }

/-- `{'a': [1, 2]}`. -/
def wSep : XVal := .map tDict [(.str (cs "a"), .seq tList [.int 1, .int 2])]

theorem wSep_C : dumpsCX cfgSepX 10 wSep = .ok (cs "{\"a\"X[1X2]}") := by
  simp [wSep, cfgSepX, dumpsCX, cObjX, cEnterX, cContX, cMapPart, cExactItems, cMapItemsX, cKeyX, cSeqPart,
    cSeqItemsX, writeStrObj, liftE, intRepr, decDigits, decDigitsF, maxStrDigits, cWriteStringX, cFastEncode,
    XCfg.toE, writeEscapedAscii, asciiEscapeSize, Except.map]
  decide

theorem wSep_Py : dumpsPyX cfgSepX 10 wSep = .ok (cs "{\"a\":[1,2]}") := by
  simp [wSep, cfgSepX, dumpsPyX, iterJoinPyX, pyCallX, pyIterX, pyContX, pyDictPart.eq_def, pyExactItems,
    cExactItems, pyDictItemsX, pyKeyX, pyEncStrX, needsReplace, pyListPart, pyListItemsX, pyItemX, liftE,
    intRepr, decDigits, decDigitsF, maxStrDigits, Except.map]
  decide

/-- With separators that may be `str` subclasses (everything else as in `DumpsTwinsX`), when neither
twin raises its `RecursionError`: the same text or the same exception. -/
def DumpsTwinsSep : Prop :=
  ∀ (cfg : XCfg) (c p : Nat) (v : XVal), cfg.customEnc = none →
    (∀ n t v', cfg.dflt n t = .ok v' → v'.okx = true) → v.okx = true →
    ¬ IsRecCX (dumpsCX cfg c v) → ¬ IsRecPyX (dumpsPyX cfg p v) → SameExc (dumpsCX cfg c v) (dumpsPyX cfg p v)

/-- `json.dumps({'a': [1, 2]}, separators=(S(','), S(':')))` with `S.__str__` returning `'X'`:
`{"a"X[1X2]}` in C (`PyUnicodeWriter_WriteStr` calls `str()`), `{"a":[1,2]}` in Python. -/
theorem dumpsTwinsSep_refuted : ¬ DumpsTwinsSep := by
  intro h
  have h1 := h cfgSepX 10 10 wSep rfl (fun n t v' h => by simp [cfgSepX, defaultErr] at h) (by decide)
    (by rw [wSep_C]; rintro ⟨ns, h⟩; cases h) (by rw [wSep_Py]; rintro ⟨ns, h⟩; cases h)
  rw [wSep_C, wSep_Py] at h1
  rcases h1 with ⟨t, h2, h3⟩ | ⟨_, _, _, h2, _⟩
  · exact absurd (Except.ok.inj (h2.trans h3.symm)) (by decide)
  · cases h2

/-- With a custom `encoder` (`c_make_encoder` only), `encoder_write_string` writes the text of the
`str` the encoder returns, as `_make_iterencode` does. -/
def EncoderStringRaw : Prop :=
  ∀ (cfg : XCfg) (s : PStr) (g : PStr → Except PyExc XOut) (o : SObj),
    cfg.customEnc = some g → g s = .ok (.str o) → cWriteStringX cfg s = .ok o.raw

/-- An encoder returning `S(s)` with `S.__str__` returning `'X'`: C writes `X`
(`_steal_accumulate`'s `PyUnicodeWriter_WriteStr`, Objects/unicode_writer.c:313-331). -/
theorem encoderStringRaw_refuted : ¬ EncoderStringRaw := by
  intro h
  have h1 := h { customEnc := some (fun s => .ok (.str ⟨s, false, .ok (cs "X")⟩)) } (cs "ab") _ ⟨cs "ab", false, .ok (cs "X")⟩ rfl rfl
  simp [cWriteStringX, writeStrObj] at h1
  exact absurd h1 (by decide)

/-- `encoder_write_string` (:1537-1557) and `_steal_accumulate` (:1560-1566), for every string and
every encoder: with `fast_encode` the C escape (`write_escaped_*`, the text of a subclass without
`str()`); with a custom encoder, its exception, `TypeError` for a non-`str` result naming its type
(`%.80s`), and for a `str` result `PyUnicodeWriter_WriteStr`: its text if it is exactly a `str`,
`str()` of it otherwise. -/
def EncoderStringX : Prop :=
  ∀ (cfg : XCfg) (s : PStr),
    (cfg.customEnc = none → cWriteStringX cfg s = .ok (cStrEnc cfg.toE s)) ∧
    (∀ g, cfg.customEnc = some g →
      (∀ e, g s = .error e → cWriteStringX cfg s = .error e) ∧
      (∀ t, g s = .ok (.nonstr t) →
        cWriteStringX cfg s = .error (.typeError s!"encoder() must return a string, not {truncName 80 t}")) ∧
      (∀ o, g s = .ok (.str o) → cWriteStringX cfg s = (if o.exact then .ok o.raw else o.strOf)))

theorem encoderStringX_proven : EncoderStringX := by
  intro cfg s
  refine ⟨fun h => cWriteStringX_std h s, fun g hg => ⟨fun e h => ?_, fun t h => ?_, fun o h => ?_⟩⟩ <;>
    simp [cWriteStringX, hg, h, writeStrObj]

/-! ### Container subclasses -/

def tLsub : PyType := { name := "L", module := "__main__", heap := true }

/-- A `list` subclass with items whose `__iter__` yields nothing. -/
def wSub : XVal := .seqSub tLsub true [] none

theorem wSub_C : dumpsCX {} 10 wSub = .ok (cs "[]") := by
  simp [wSub, dumpsCX, cObjX, cEnterX, cContX, cSeqPart]

theorem wSub_Py : dumpsPyX {} 10 wSub = .ok (cs "]") := by
  simp [wSub, dumpsPyX, iterJoinPyX, pyCallX, pyIterX, pyContX, pyListPart, pyListItemsX]
  decide

/-- With subclasses of `list`, `tuple`, `dict` and `frozendict` (exact separators, no custom
encoder), when neither twin raises its `RecursionError`: the same text or the same exception. -/
def DumpsTwinsSub : Prop :=
  ∀ (cfg : XCfg) (c p : Nat) (v : XVal), cfg.Okx → v.vld true false = true →
    ¬ IsRecCX (dumpsCX cfg c v) → ¬ IsRecPyX (dumpsPyX cfg p v) → SameExc (dumpsCX cfg c v) (dumpsPyX cfg p v)

/-- A `list` subclass that is not empty and iterates as empty: `[]` in C (`PySequence_Fast`, then
the size), `]` in Python (`not lst` is false, and `'['` is written with the first item only). Known:
gh-71800; the dict counterparts are cpython#158731 and #158732. -/
theorem dumpsTwinsSub_refuted : ¬ DumpsTwinsSub := by
  intro h
  have h1 := h {} 10 10 wSub okx_default (by decide)
    (by rw [wSub_C]; rintro ⟨ns, h⟩; cases h) (by rw [wSub_Py]; rintro ⟨ns, h⟩; cases h)
  rw [wSub_C, wSub_Py] at h1
  rcases h1 with ⟨t, h2, h3⟩ | ⟨_, _, _, h2, _⟩
  · cases h2; cases h3
  · cases h2

/-- A `dict` subclass of type `DF` defined in `__main__`. -/
def tDF : PyType := { name := "DF", module := "__main__", heap := true }

/-- `DF(z=1)` where `DF.__len__` returns 0: one stored entry, `bool()` false, `items()` that of
`dict`. -/
def wDictSub : XVal := .mapSub tDF 1 false .ok [(.tup, .str (cs "z"), .int 1)] none

theorem wDictSub_C : dumpsCX {} 10 wDictSub = .ok (cs "{\"z\": 1}") := by
  simp only [wDictSub, dumpsCX, cObjX, cEnterX, cContX]
  unfold cMapPart
  simp [cSubItems, cMapItemsX, cKeyX, cWriteStringX, cFastEncode, writeStrObj, SObj.ofStr, intRepr,
    decDigits, decDigitsF, maxStrDigits, XCfg.toE, writeEscapedAscii, asciiEscapeSize, Except.map, cObjX, liftE]
  decide

theorem wDictSub_Py : dumpsPyX {} 10 wDictSub = .ok (cs "{}") := by
  simp only [wDictSub, dumpsPyX, iterJoinPyX, pyCallX, pyIterX, pyContX]
  unfold pyDictPart
  simp

/-- With a `dict` subclass that overrides only `__len__` (or `__bool__`): its stored size is the
number of its pairs and `items()` is `dict.items`, the pairs of exact-container values of
`DumpsTwinsX`; exact separators, no custom encoder. When neither twin raises its
`RecursionError`, the same text or the same exception. -/
def dictSubOf (t : PyType) (tr : Bool) (kvs : List (XKey × XVal)) : XVal :=
  .mapSub t kvs.length tr .ok (kvs.map fun (k, x) => (.tup, k, x)) none

def DumpsTwinsDictSub : Prop :=
  ∀ (cfg : XCfg) (c p : Nat) (t : PyType) (tr : Bool) (kvs : List (XKey × XVal)), cfg.Okx →
    XVal.okxItems kvs = true →
    ¬ IsRecCX (dumpsCX cfg c (dictSubOf t tr kvs)) → ¬ IsRecPyX (dumpsPyX cfg p (dictSubOf t tr kvs)) →
    SameExc (dumpsCX cfg c (dictSubOf t tr kvs)) (dumpsPyX cfg p (dictSubOf t tr kvs))

/-- `DF(z=1)` with `__len__` returning 0: `{"z": 1}` in C, which tests the stored size
(`PyDict_GET_SIZE`, :1806) and then iterates `PyMapping_Items` (:1839-1840) through
`_encoder_iterate_mapping_lock_held`; `{}` in Python, where `if not dct` calls `__len__`
(encoder.py:329-331). Related: gh-123183, cpython#158731/158732. -/
theorem dumpsTwinsDictSub_refuted : ¬ DumpsTwinsDictSub := by
  intro h
  have h1 := h {} 10 10 tDF false [(.str (cs "z"), .int 1)] okx_default (by decide)
    (by rw [show dictSubOf tDF false [(.str (cs "z"), .int 1)] = wDictSub from rfl, wDictSub_C]; rintro ⟨ns, h⟩; cases h)
    (by rw [show dictSubOf tDF false [(.str (cs "z"), .int 1)] = wDictSub from rfl, wDictSub_Py]; rintro ⟨ns, h⟩; cases h)
  rw [show dictSubOf tDF false [(.str (cs "z"), .int 1)] = wDictSub from rfl, wDictSub_C, wDictSub_Py] at h1
  rcases h1 with ⟨t, h2, h3⟩ | ⟨_, _, _, h2, _⟩
  · cases h2; cases h3
  · cases h2

/-! ### `encoder_call` at a level whose indent cannot be built -/

/-- `c_make_encoder(...)(o, level)` gives the 1-tuple of the text of `_make_iterencode(...)(o,
level)`, or the same exception, for every level `0 <= level <= sys.maxsize`, every value and option
of `DumpsTwinsX`, when neither raises its `RecursionError` (`EncoderCallX` 4 without the cache). -/
def EncoderCallTwins : Prop :=
  ∀ (alloc : Alloc) (cfg : XCfg) (c p : Nat) (v : XVal) (level : Int), cfg.Okx → v.okx = true → 0 ≤ level →
    ¬ outOfSsize level → ¬ IsRecCX (encoderCallX alloc cfg c v level) →
    ¬ IsRecPyX (iterencodePyX cfg p v level.toNat) →
    (∃ t, encoderCallX alloc cfg c v level = .ok [t] ∧ iterencodePyX cfg p v level.toNat = .ok t) ∨
    (∃ e nsC nsP, encoderCallX alloc cfg c v level = .error (e, nsC) ∧ iterencodePyX cfg p v level.toNat = .error (e, nsP))

def cfgIndent2 : XCfg := { indent := some (cs "  ") }

theorem okx_indent2 : cfgIndent2.Okx :=
  ⟨rfl, rfl, rfl, fun n t v' h => by simp [cfgIndent2, defaultErr] at h⟩

theorem wLevel_C (alloc : Alloc) : encoderCallX alloc cfgIndent2 10 (.int 1) (2 ^ 62) =
    .error (xe (.overflowError "repeated string is too long")) :=
  encoderCallX_cacheErr (ind := cs "  ") rfl (by decide)
    (createIndentCache_ovf alloc _ (by decide) (by simp [ssizeMax]; decide))

theorem wLevel_Py : iterencodePyX cfgIndent2 10 (.int 1) (2 ^ 62 : Int).toNat = .ok (cs "1") := by
  simp [iterencodePyX, pyCallX, pyIterX, liftE, intRepr, decDigits, decDigitsF, maxStrDigits]
  decide

/-- With `indent='  '`, `c_make_encoder(...)(1, 2**62)` raises `OverflowError('repeated string is
too long')` from `create_indent_cache` (:1378, `unicode_repeat`, Objects/unicodeobject.c:12573-12576)
before writing anything, while `_make_iterencode(...)(1, 2**62)` returns `'1'`: it repeats the
indent only inside a container (encoder.py:281, :340). Levels whose string `malloc` refuses give
`MemoryError` the same way (bugs/json-encoder-call-indent-level.yaml). -/
theorem encoderCallTwins_refuted : ¬ EncoderCallTwins := by
  intro h
  have h1 := h (fun _ => true) cfgIndent2 10 10 (.int 1) (2 ^ 62) okx_indent2 rfl (by decide) (by decide)
    (by rw [wLevel_C]; rintro ⟨ns, h⟩; cases h) (by rw [wLevel_Py]; rintro ⟨ns, h⟩; cases h)
  rw [wLevel_C, wLevel_Py] at h1
  rcases h1 with ⟨t, h2, _⟩ | ⟨_, _, _, _, h3⟩
  · cases h2
  · cases h3

end PyLean.JsonMod
