import PyLean.JsonMod.ApiProps

/-!
Hooks, `JSONDecoder.__init__`, custom encoders, and the properties that stay
open until the binary64 model exists.
-/

namespace PyLean.JsonMod

open PyLean

/-! ### `object_pairs_hook` takes priority -/

/-- Two decoder configurations that the scanners cannot tell apart. -/
structure Same (a b : DCfg) : Prop where
  strict : a.strict = b.strict
  flt : a.parseFloat = b.parseFloat
  int : a.parseIntFn = b.parseIntFn
  con : a.parseConstant = b.parseConstant
  pairs : a.pairsHook = b.pairsHook
  obj : a.pairsHook.isNone → a.objectHook = b.objectHook
  arr : ∀ xs, mkArr a xs = mkArr b xs

theorem Same.parseInt {a b : DCfg} (h : Same a b) (t : PStr) : parseInt a t = parseInt b t := by
  simp only [PyLean.JsonMod.parseInt, h.int]

theorem Same.fin {a b : DCfg} (h : Same a b) (acc : List (PStr × JVal)) : cFinish a acc = cFinish b acc := by
  unfold cFinish
  rw [← h.pairs]
  cases hp : a.pairsHook with
  | some g => rfl
  | none => simp only; rw [h.obj (by simp [hp])]

theorem Same.mkObj {a b : DCfg} (h : Same a b) (acc : List (PStr × JVal)) : pyMkObj a acc = pyMkObj b acc := by
  unfold pyMkObj
  rw [← h.pairs]
  cases hp : a.pairsHook with
  | some g => rfl
  | none => simp only; rw [h.obj (by simp [hp])]

theorem Same.add {a b : DCfg} (h : Same a b) (acc : List (PStr × JVal)) (k : PStr) (v : JVal) :
    cAddPair a acc k v = cAddPair b acc k v := by
  simp only [cAddPair, h.pairs]

theorem Same.matchNumber {a b : DCfg} (h : Same a b) (s : PStr) (i : Nat) :
    cMatchNumber a s i = cMatchNumber b s i := by
  simp only [cMatchNumber, h.flt, h.parseInt]

theorem same_c {a b : DCfg} (h : Same a b) (s : PStr) : ∀ n : Nat,
    (∀ i, cScanOnce a s n i = cScanOnce b s n i) ∧
    (∀ i acc, cArrLoop a s n i acc = cArrLoop b s n i acc) ∧
    (∀ i acc, cObjBody a s n i acc = cObjBody b s n i acc) := by
  intro n
  induction n with
  | zero => exact ⟨fun _ => by simp [cScanOnce], fun _ _ => by simp [cArrLoop], fun _ _ => by simp [cObjBody]⟩
  | succ n ih =>
    obtain ⟨hs, ha, ho⟩ := ih
    refine ⟨fun i => ?_, fun i acc => ?_, fun i acc => ?_⟩
    · simp only [cScanOnce, h.strict, h.fin, cConst, h.con, h.matchNumber, ho, ha, h.arr]
    · simp only [cArrLoop, hs, ha, h.arr]
    · simp only [cObjBody, h.strict, hs, h.add, h.fin, ho]

theorem same_py {a b : DCfg} (h : Same a b) (s : PStr) : ∀ n : Nat,
    (∀ i, pyScanOnce a s n i = pyScanOnce b s n i) ∧
    (∀ i acc, pyArrLoop a s n i acc = pyArrLoop b s n i acc) ∧
    (∀ i acc, pyObjLoop a s n i acc = pyObjLoop b s n i acc) := by
  intro n
  induction n with
  | zero => exact ⟨fun _ => by simp [pyScanOnce], fun _ _ => by simp [pyArrLoop], fun _ _ => by simp [pyObjLoop]⟩
  | succ n ih =>
    obtain ⟨hs, ha, ho⟩ := ih
    refine ⟨fun i => ?_, fun i acc => ?_, fun i acc => ?_⟩
    · simp only [pyScanOnce, pyScanNumber, h.strict, h.mkObj, h.flt, h.con, h.parseInt, ho, ha, h.arr]
    · simp only [pyArrLoop, hs, ha, h.arr]
    · simp only [pyObjLoop, h.strict, hs, h.mkObj, ho]

/-- `object_pairs_hook` takes priority (`JSONDecoder.__init__` docstring,
decoder.py:304-309): when it is given, `object_hook` is never called, for every
document, in both twins. -/
def PairsHookPriority : Prop :=
  ∀ (cfg : DCfg) (g : List (PStr × JVal) → DR JVal) (s : PStr), cfg.pairsHook.isSome = true →
    loadsC { cfg with objectHook := some g } s = loadsC cfg s ∧
    loadsPy { cfg with objectHook := some g } s = loadsPy cfg s

theorem pairsHookPriority_proven : PairsHookPriority := by
  intro cfg g s hp
  have h : Same { cfg with objectHook := some g } cfg :=
    { strict := rfl, flt := rfl, int := rfl, con := rfl, pairs := rfl, arr := fun _ => rfl
      obj := fun hn => by
        exfalso
        cases hq : cfg.pairsHook with
        | none => simp [hq] at hp
        | some _ => simp [hq] at hn }
  constructor
  · have hr : ∀ idx, rawDecodeC { cfg with objectHook := some g } s idx = rawDecodeC cfg s idx := by
      intro idx
      simp only [rawDecodeC, (same_c h s (docFuel s)).1]
    simp only [loadsC, decodeWith, hr]
  · have hr : ∀ idx, rawDecodePy { cfg with objectHook := some g } s idx = rawDecodePy cfg s idx := by
      intro idx
      simp only [rawDecodePy, (same_py h s (docFuel s)).1]
    simp only [loadsPy, decodeWith, hr]

/-! ### `array_hook` -/

/-- `array_hook` replaces the list (`JSONDecoder.__init__` docstring,
decoder.py:311-317): an `array_hook` that gives its list back changes nothing, for
every document and every other option, in both twins; and on `[]` the result is
what the hook does, value or exception, `StopIteration` turned into the
`JSONDecodeError` of `raw_decode`. -/
def ArrayHook : Prop :=
  (∀ (cfg : DCfg) (s : PStr),
    loadsC { cfg with arrayHook := some fun xs => .ok (.arr xs) } s = loadsC { cfg with arrayHook := none } s ∧
    loadsPy { cfg with arrayHook := some fun xs => .ok (.arr xs) } s = loadsPy { cfg with arrayHook := none } s) ∧
  (∀ (cfg : DCfg) (h : List JVal → DR JVal), cfg.arrayHook = some h →
    loadsC cfg [91, 93] = stopToJde (h []) ∧ loadsPy cfg [91, 93] = stopToJde (h []))

theorem arrayHook_proven : ArrayHook := by
  refine ⟨fun cfg s => ?_, fun cfg h hh => ?_⟩
  · have h : Same { cfg with arrayHook := some fun xs => .ok (.arr xs) } { cfg with arrayHook := none } :=
      { strict := rfl, flt := rfl, int := rfl, con := rfl, pairs := rfl, obj := fun _ => rfl
        arr := fun _ => rfl }
    constructor
    · have hr : ∀ idx, rawDecodeC { cfg with arrayHook := some fun xs => .ok (.arr xs) } s idx =
          rawDecodeC { cfg with arrayHook := none } s idx := by
        intro idx
        simp only [rawDecodeC, (same_c h s (docFuel s)).1]
      simp only [loadsC, decodeWith, hr]
    · have hr : ∀ idx, rawDecodePy { cfg with arrayHook := some fun xs => .ok (.arr xs) } s idx =
          rawDecodePy { cfg with arrayHook := none } s idx := by
        intro idx
        simp only [rawDecodePy, (same_py h s (docFuel s)).1]
      simp only [loadsPy, decodeWith, hr]
  · have hm : mkArr cfg [] = h [] := by simp [mkArr, hh]
    constructor
    · have hraw : rawDecodeC cfg [91, 93] ((wsEnd [91, 93] 0 : Nat) : Int) =
          (match stopToJde ((mkArr cfg []).map (·, (2 : Nat))) with
           | .ok (v, e) => .ok (v, (e : Int))
           | .error err => .error err) := rfl
      unfold loadsC decodeWith
      rw [hraw, hm]
      generalize h [] = r
      cases r with
      | ok v => rfl
      | error e => cases e <;> rfl
    · have hraw : rawDecodePy cfg [91, 93] ((wsEnd [91, 93] 0 : Nat) : Int) =
          stopToJde ((mkArr cfg []).map (·, (2 : Int))) := rfl
      unfold loadsPy decodeWith
      rw [hraw, hm]
      generalize h [] = r
      cases r with
      | ok v => rfl
      | error e => cases e <;> rfl

/-! ### `JSONDecoder.__init__` -/

/-- `JSONDecoder.__init__`: `parse_float or float` and its siblings: a false
callable is the same as no callable; the defaults give the default decoder; the
three object and array hooks are kept as given; an unknown keyword is rejected. -/
def DecoderInit : Prop :=
  (decoderInit { strict := some true } = .ok {}) ∧
  (∀ (a : DecArgs), a.kw = [] → ∃ c, decoderInit a = .ok c ∧ c.objectHook = a.objectHook ∧
    c.pairsHook = a.objectPairsHook ∧ c.arrayHook = a.arrayHook) ∧
  (∀ (a : DecArgs) (h : PStr → DR JVal),
    decoderInit { a with parseFloat := some (false, h) } = decoderInit { a with parseFloat := none } ∧
    decoderInit { a with parseInt := some (false, h) } = decoderInit { a with parseInt := none } ∧
    decoderInit { a with parseConstant := some (false, h) } = decoderInit { a with parseConstant := none }) ∧
  (∀ (a : DecArgs) (k : String) (ks : List String),
    decoderInit { a with kw := k :: ks } =
      .error (.typeError s!"JSONDecoder.__init__() got an unexpected keyword argument '{k}'"))

theorem decoderInit_proven : DecoderInit := by
  refine ⟨rfl, fun a ha => ?_, fun a h => ⟨?_, ?_, ?_⟩, fun _ _ _ => rfl⟩
  · simp only [decoderInit, ha]
    exact ⟨_, rfl, rfl, rfl, rfl⟩
  all_goals rfl

/-! ### `_decode_uXXXX` -/

/-- `_decode_uXXXX(s, pos)` reads back every `\uXXXX` the encoders write, and
reports the `u` position when the four digits are not there. -/
def DecodeUXXXX : Prop :=
  (∀ (s : PStr) (p n : Nat) (r : PStr), n < 0x10000 → s.drop p = uEsc n ++ r → decodeUXXXX s (p + 1) = .ok n) ∧
  (∀ (s : PStr) (p : Nat), hex4 s (p + 1) = none → decodeUXXXX s p = .error (.jde "Invalid \\uXXXX escape" (p : Int)))

theorem decodeUXXXX_proven : DecodeUXXXX := by
  refine ⟨fun s p n r hn hs => ?_, fun s p h => ?_⟩
  · have := hex4_uEsc s p n r hs hn
    simp only [decodeUXXXX, show p + 1 + 1 = p + 2 from rfl, this]
  · simp only [decodeUXXXX, h]

/-! ### `encoder_write_string` -/

/-- `encoder_write_string`: with `fast_encode` the C function; with any other
`encoder` its result, which must be a `str`. -/
def EncoderString : Prop :=
  ∀ (cfg : ECfg) (s : PStr),
    (cfg.customEnc = none → cEncStr cfg s = .ok (cStrEnc cfg s)) ∧
    (∀ g, cfg.customEnc = some g →
      (∀ r, g s = .ok (.str r) → cEncStr cfg s = .ok r) ∧
      (∀ t, g s = .ok (.nonstr t) →
        cEncStr cfg s = .error (.typeError s!"encoder() must return a string, not {String.ofList (t.toList.take 80)}")) ∧
      (∀ e, g s = .error e → cEncStr cfg s = .error e))

theorem encoderString_proven : EncoderString := by
  intro cfg s
  refine ⟨fun hc => cEncStr_std hc s, fun g hg => ⟨fun r h => ?_, fun t h => ?_, fun e h => ?_⟩⟩ <;>
    simp [cEncStr, hg, h]

/-! ### The API twins for `dumps` -/

/-- `json.dumps` with either encoder, for every keyword argument: the same text
or the same exception (type invariants of `ECfg.Ok`, `EVal.ok`). -/
def DumpsApiTwins : Prop :=
  ∀ (a : EncArgs) (cfg : ECfg) (v : EVal), encoderOf a = .ok cfg → cfg.Ok → v.ok = true →
    jsonDumps dumpsPy a v = jsonDumps dumpsC a v

theorem dumpsApiTwins_proven : DumpsApiTwins := by
  intro a cfg v h hO hv
  simp only [jsonDumps, h]
  exact dumpsTwins_proven cfg v hO hv

/-! ### The size of the indent cache -/

theorem rep_length (t : PStr) (n : Nat) : (rep t n).length = n * t.length := by
  induction n with
  | zero => simp [rep]
  | succ n ih => simp only [rep, List.length_append, ih]; rw [Nat.succ_mul]; omega

/-- Entry `2*k` of the indent cache is `1 + (k + i) * len(indent)` characters
long, for every level the cache has reached; entry `2*k-1` is longer by
`len(item_separator)`. The cache therefore holds about `n^2 * len(indent)`
characters at depth `n`, on top of the text written. -/
def IndentCacheSize : Prop :=
  ∀ (cfg : ECfg) (ind : PStr) (i n : Nat) (c : IndentCache), Cached cfg ind i c n → ∀ k, k ≤ n →
    (writeNewlineIndent k c).length = 1 + (k + i) * ind.length ∧
    (1 ≤ k → (c.getD (2 * k - 1) []).length = cfg.itemSep.length + 1 + (k + i) * ind.length)

theorem indentCacheSize_proven : IndentCacheSize := by
  intro cfg ind i n c h k hk
  constructor
  · have e : k * 2 = 2 * k := by omega
    simp only [writeNewlineIndent, e, List.getD_eq_getElem?_getD, h.nl k hk, Option.getD_some, cNewlineIndent,
      List.length_append, rep_length, List.length_cons, List.length_nil]
  · intro h1
    simp only [List.getD_eq_getElem?_getD, h.sep k h1 hk, Option.getD_some, cSepIndent, cNewlineIndent,
      List.length_append, rep_length, List.length_cons, List.length_nil]
    omega

/-! ### Open properties -/

/-- The text of a float that `NUMBER_RE` takes as a float: what `float.__repr__`
writes for a finite float. -/
def isFloatText (r : PStr) : Bool :=
  match numberRe r with
  | some (i, fr, ex) => (i ++ fr ++ ex == r) && (fr != [] || ex != [])
  | none => false

/-- Open. A finite float comes back through `parse_float`, whose argument is
exactly its `repr`: with the default `float`, `loads(dumps(x)) == x` once
`float(repr(x)) == x` is known from the binary64 model. -/
def RoundTripFloat : Prop :=
  ∀ (cfg : ECfg) (dcfg : DCfg) (b : Nat) (r d : PStr) (j : JVal), Layout cfg → dcfg.Rec →
    fltIsFinite b = true → isFloatText r = true → dcfg.parseFloat r = .ok j →
    dumpsC cfg (.flt b r) = .ok d → loadsPy dcfg d = .ok j ∧ loadsC dcfg d = .ok j

mutual
/-- Every `repr` in a value is float text. -/
def EVal.fltText : EVal → Bool
  | .flt _ r => isFloatText r
  | .list xs => EVal.fltTextList xs
  | .dict kvs => EVal.fltTextItems kvs
  | _ => true
def EVal.fltTextList : List EVal → Bool
  | [] => true
  | x :: xs => EVal.fltText x && EVal.fltTextList xs
def EVal.fltTextItems : List (EKey × EVal) → Bool
  | [] => true
  | (_, x) :: xs => EVal.fltText x && EVal.fltTextItems xs
end

/-- Open. `json-dumps-accepted` for values with floats: any text `dumps` writes,
`NaN` and `Infinity` included, is accepted by `loads`. -/
def DumpsAcceptedFloat : Prop :=
  ∀ (cfg : ECfg) (dcfg : DCfg) (v : EVal) (d : PStr), Layout cfg → dcfg.Rec →
    (∀ t, ∃ j, dcfg.parseFloat t = .ok j) → (∀ t, ∃ j, dcfg.parseConstant t = .ok j) →
    v.ok = true → v.fltText = true → dumpsC cfg v = .ok d →
    ∃ j, loadsPy dcfg d = .ok j ∧ loadsC dcfg d = .ok j

/-- Open. `json.loads` on `bytes`: a `str` whose first two characters are ASCII
and not NUL, encoded with `surrogatepass` in any of the five encodings, decodes to
the result of `json.loads` on the `str`. In UTF-16 a high surrogate followed by a
low surrogate becomes one character (`noSurrPair`, as in `json-roundtrip`). -/
def LoadsBytes : Prop :=
  ∀ (decode : DCfg → PStr → DR JVal) (a : DecArgs) (e : TextEnc) (c0 c1 : Nat) (t : PStr),
    0 < c0 → c0 < 128 → 0 < c1 → c1 < 128 → strOk t = true →
    (∀ le, e = .utf16 le → noSurrPair t = true) →
    jsonLoads decode a (.bytes (e.encode (c0 :: c1 :: t))) = jsonLoads decode a (.str (c0 :: c1 :: t))

end PyLean.JsonMod
