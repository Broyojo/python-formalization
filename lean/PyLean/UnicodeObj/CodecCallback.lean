import PyLean.UnicodeObj.CodecProps
import PyLean.UnicodeObj.CodecCharmap
import PyLean.UnicodeObj.CodecUtf7
import PyLean.UnicodeObj.CodecEscape

/-!
A Python error handler: `codecs.register_error(name, fn)`.

`fn` can do anything, so the model takes it as a function from the history of calls to what the
call did. That covers a handler with state, one that raises, one that returns junk, one that
returns a position behind the error, and one that replaces `exc.object`. The history has every
view so far, the last one being the current call.

`ErrHandler` in `CodecHandlers.lean` is the standard handlers. For UTF-16 and most other decoders
C reaches them through the same callback path as a custom one; `.std` is a shortcut around it.
The `*_mimics` theorems below show that the shortcut gives what the callback path gives, so the
theorems proved over `ErrHandler` keep their meaning. The loops here repeat the shape of the loops
over `ErrHandler`, and `*_std` proves each one equal to its original on `.std`.

Abstraction: an encoder never reads `exc.object` back, so a handler that edits it changes only how
a later exception prints. That is not modelled.
-/

namespace PyLean.UnicodeObj

open PyLean

/-- What the exception looks like to the handler. `make_decode_exception` sets `start`, `end` and
`reason` afresh on every call; `object` stays as the last handler left it. -/
structure DecView where
  object : Bytes
  encoding : String
  start : Nat
  stop : Nat
  reason : String
  deriving Repr, DecidableEq

/-- What the handler did to `exc.object`. -/
inductive ObjEdit where
  | keep
  | set (b : Bytes)
  /-- Assigned something that is not `bytes`. -/
  | wrongType
  /-- `del exc.object`. -/
  | deleted
  deriving Repr, DecidableEq

/-- What a decode handler did. -/
inductive DecResp where
  /-- It raised, or `__index__` of the position raised, or the position has no `__index__`. -/
  | raises (e : PyExc)
  /-- Not a tuple, a tuple of the wrong size, or a replacement that is not `str`. -/
  | bad
  | ret (rep : Str) (newpos : Int) (obj : ObjEdit)
  deriving Repr, DecidableEq

abbrev DecCB := List DecView → DecResp

/-- The `errors` of a decoder. -/
inductive DH where
  | std (h : ErrHandler)
  | custom (cb : DecCB)
  /-- No handler of that name: `PyCodec_LookupError` fails at the first error. -/
  | missing (name : String)

/-- `PyCodec_LookupError`, Python/codecs.c, when nothing is registered. -/
def lookupError (name : String) : PyExc :=
  .named "LookupError" s!"unknown error handler name '{name}'"

/-- The `n` conversion of `PyArg_ParseTuple`. It keeps its own error instead of the format's. -/
def ssizeOfIndex (n : Int) : Py Int :=
  if n > ssizeMax ∨ n < ssizeMin then
    .error (.overflowError "Python int too large to convert to C ssize_t")
  else .ok n

/-- `PyUnicodeDecodeError_GetObject`. -/
def decObject (input : Bytes) : ObjEdit → Py Bytes
  | .keep => .ok input
  | .set b => .ok b
  | .wrongType => .error (.typeError "UnicodeError 'object' attribute must be a bytes")
  | .deleted => .error (.typeError "UnicodeError 'object' attribute is not set")

/-- `unicode_decode_call_errorhandler_writer`, unicodeobject.c:4537-4635, with
`make_decode_exception`, :4386-4408. Returns the history, the object, the replacement and the new
position. The position is checked against the object as the handler left it. -/
def decodeCallback (cb : DecCB) (hist : List DecView) (enc reason : String) (input : Bytes)
    (start stop : Nat) : Py (List DecView × Bytes × Str × Nat) := do
  let hist' := hist ++ [{ object := input, encoding := enc, start, stop, reason }]
  match cb hist' with
  | .raises e => .error e
  | .bad => .error (.typeError "decoding error handler must return (str, int) tuple")
  | .ret rep newpos0 obj =>
    let newpos0 ← ssizeOfIndex newpos0
    let input' ← decObject input obj
    let insize : Int := input'.length
    let newpos := if newpos0 < 0 then insize + newpos0 else newpos0
    if newpos < 0 ∨ newpos > insize then
      .error (.indexError s!"position {newpos} from error handler out of bounds")
    else .ok (hist', input', rep, newpos.toNat)

/-- One call of whichever handler `errors` names. -/
def handlerStep (H : DH) (enc : String) (code : EncCode) (reason : String) (input : Bytes)
    (hist : List DecView) (start stop : Nat) : Py (List DecView × Bytes × Str × Nat) :=
  match H with
  | .std h =>
    match decodeHandlerCall h enc code input start stop reason with
    | .error e => .error e
    | .ok (rep, newpos) => .ok (hist, input, rep, newpos)
  | .custom cb => decodeCallback cb hist enc reason input start stop
  | .missing name => .error (lookupError name)

/-- The second result of a decoder. UTF-16 and UTF-32 write `*consumed` at the end, so it is the
position. `unicode_escape` and `raw_unicode_escape` write it only when the input stops short, so at
a normal end it stays what the caller set, the original size (`atEnd`), even if a handler replaced
the object. -/
def stopPos (atEnd : Option Nat) (rest : List Nat) (pos : Nat) : Nat :=
  match atEnd with
  | none => pos
  | some n => if rest.isEmpty then n else pos

/-- `decodeDriver` with any handler. -/
def decodeDriverX (step : List Nat → DStep) (H : DH) (enc : String) (code : EncCode)
    (atEnd : Option Nat) :
    Nat → Bytes → List DecView → Nat → List Nat → Str → Py (Str × Nat)
  | 0, _, _, _, _, _ => .error .modelFuel
  | fuel + 1, input, hist, pos, rest, out =>
    match step rest with
    | .char c n => decodeDriverX step H enc code atEnd fuel input hist (pos + n) (rest.drop n) (out ++ [c])
    | .multi w n => decodeDriverX step H enc code atEnd fuel input hist (pos + n) (rest.drop n) (out ++ w)
    | .stop => .ok (out, stopPos atEnd rest pos)
    | .raise e => .error e
    | .fail reason s e =>
      match handlerStep H enc code reason input hist (pos + s) (pos + e) with
      | .error x => .error x
      | .ok (hist', input', rep, newpos) =>
        decodeDriverX step H enc code atEnd fuel input' hist' newpos (input'.drop newpos) (out ++ rep)

theorem decodeDriverX_std (step : List Nat → DStep) (h : ErrHandler) (enc : String) (code : EncCode)
    (input : Bytes) : ∀ (fuel : Nat) (hist : List DecView) (pos : Nat) (rest : List Nat) (out : Str),
      decodeDriverX step (.std h) enc code none fuel input hist pos rest out =
        decodeDriver step h enc code input fuel pos rest out := by
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ fuel ih =>
    intro hist pos rest out
    simp only [decodeDriverX, decodeDriver]
    cases step rest with
    | char c n => exact ih ..
    | multi w n => exact ih ..
    | stop => rfl
    | raise e => rfl
    | fail r s e =>
      simp only [handlerStep]
      cases decodeHandlerCall h enc code input (pos + s) (pos + e) r with
      | error x => rfl
      | ok p =>
        obtain ⟨w, newpos⟩ := p
        exact ih ..

/-- `unicode_decode_utf8` with any handler. The three names C handles inline are matched first,
the way `error_handler` is switched on at unicodeobject.c:5365-5398. -/
def utf8DecodeLoopX (H : DH) (consumed : Bool) :
    Nat → Bytes → List DecView → Nat → List Nat → Str → Py (Str × Nat)
  | 0, _, _, _, _, _ => .error .modelFuel
  | _ + 1, _, _, pos, [], out => .ok (out, pos)
  | fuel + 1, input, hist, pos, rest@(b0 :: tl), out =>
    let onError (reason : String) (stopAt : Nat) : Py (Str × Nat) :=
      let n := stopAt - pos
      let bad := rest.take n
      let go (w : Str) := utf8DecodeLoopX H consumed fuel input hist stopAt (rest.drop n) (out ++ w)
      let viaCallback : Py (Str × Nat) :=
        match handlerStep H "utf-8" .utf8 reason input hist pos stopAt with
        | .error e => .error e
        | .ok (hist', input', rep, newpos) =>
          utf8DecodeLoopX H consumed fuel input' hist' newpos (input'.drop newpos) (out ++ rep)
      match H with
      | .std .ignore => go []
      | .std .replace => go [0xfffd]
      | .std .surrogateescape => go (bad.map (· + 0xdc00))
      | _ => viaCallback
    match utf8Step rest with
    | .char c n =>
      utf8DecodeLoopX H consumed fuel input hist (pos + n) (rest.drop n) (out ++ [c])
    | .stop =>
      if consumed then .ok (out, pos)
      else onError "unexpected end of data" input.length
    | .err 1 => onError "invalid start byte" (pos + 1)
    | .err code =>
      if code == 2 && consumed && b0 == 0xED && rest.length == 2 &&
          decide (0xA0 ≤ tl.headD 0) && decide (tl.headD 0 ≤ 0xBF) then .ok (out, pos)
      else onError "invalid continuation byte" (pos + code - 1)

theorem utf8DecodeLoopX_std (input : Bytes) (h : ErrHandler) (consumed : Bool) :
    ∀ (fuel : Nat) (hist : List DecView) (pos : Nat) (rest : List Nat) (out : Str),
      utf8DecodeLoopX (.std h) consumed fuel input hist pos rest out =
        utf8DecodeLoop input h consumed fuel pos rest out := by
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ fuel ih =>
    intro hist pos rest out
    cases rest with
    | nil => rfl
    | cons b0 tl =>
      cases hr : utf8Step (b0 :: tl) with
      | char c n =>
        simp only [utf8DecodeLoopX, utf8DecodeLoop, hr]
        exact ih ..
      | stop =>
        simp only [utf8DecodeLoopX, utf8DecodeLoop, hr]
        cases consumed
        · simp only [Bool.false_eq_true, if_false]
          cases h
          all_goals first
            | exact ih ..
            | (simp only [handlerStep]
               generalize decodeHandlerCall _ _ _ _ _ _ _ = d
               cases d with
               | error x => rfl
               | ok p =>
                 obtain ⟨w, np⟩ := p
                 exact ih ..)
        · rfl
      | err k =>
        by_cases hk : k = 1
        · subst hk
          simp only [utf8DecodeLoopX, utf8DecodeLoop, hr]
          cases h
          all_goals first
            | exact ih ..
            | (simp only [handlerStep]
               generalize decodeHandlerCall _ _ _ _ _ _ _ = d
               cases d with
               | error x => rfl
               | ok p =>
                 obtain ⟨w, np⟩ := p
                 exact ih ..)
        · rcases k with _ | _ | j
          · simp only [utf8DecodeLoopX, utf8DecodeLoop, hr]
            split
            · rfl
            · cases h
              all_goals first
                | exact ih ..
                | (simp only [handlerStep]
                   generalize decodeHandlerCall _ _ _ _ _ _ _ = d
                   cases d with
                   | error x => rfl
                   | ok p =>
                     obtain ⟨w, np⟩ := p
                     exact ih ..)
          · exact absurd rfl hk
          · simp only [utf8DecodeLoopX, utf8DecodeLoop, hr]
            split
            · rfl
            · cases h
              all_goals first
                | exact ih ..
                | (simp only [handlerStep]
                   generalize decodeHandlerCall _ _ _ _ _ _ _ = d
                   cases d with
                   | error x => rfl
                   | ok p =>
                     obtain ⟨w, np⟩ := p
                     exact ih ..)

/-- `utf7Error` with any handler. -/
def u7HandlerX (H : DH) (hist : List DecView) (input : Bytes) (start stop : Nat) (reason : String) :
    Py (List DecView × Bytes × Str × Nat) :=
  handlerStep H "utf7" .unknown reason input hist start stop

/-- `utf7Loop` with any handler. -/
def utf7LoopX (H : DH) (consumed : Bool) :
    Nat → Bytes → List DecView → Nat → List Nat → U7 → Str → Py (Str × U7 × Nat)
  | 0, _, _, _, _, _, _ => .error .modelFuel
  | fuel + 1, input, hist, pos, [], st, out =>
    if st.inShift && !consumed then
      let st := { st with inShift := false }
      if st.surrogate != 0 || decide (st.base64bits ≥ 6) ||
          (decide (st.base64bits > 0) && st.base64buffer != 0) then
        match u7HandlerX H hist input st.startinpos input.length "unterminated shift sequence" with
        | .error e => .error e
        | .ok (hist', input', rep, newpos) =>
          utf7LoopX H consumed fuel input' hist' newpos (input'.drop newpos) st (out ++ rep)
      else .ok (out, st, pos)
    else .ok (out, st, pos)
  | fuel + 1, input, hist, pos, ch :: t, st, out =>
    match u7Step st pos out.length ch t.head? with
    | .go w n st' => utf7LoopX H consumed fuel input hist (pos + n) ((ch :: t).drop n) st' (out ++ w)
    | .fail reason n st' =>
      match u7HandlerX H hist input st'.startinpos (pos + n) reason with
      | .error e => .error e
      | .ok (hist', input', rep, newpos) =>
        utf7LoopX H consumed fuel input' hist' newpos (input'.drop newpos) st' (out ++ rep)

theorem utf7LoopX_std (input : Bytes) (h : ErrHandler) (consumed : Bool) :
    ∀ (fuel : Nat) (hist : List DecView) (pos : Nat) (rest : List Nat) (st : U7) (out : Str),
      utf7LoopX (.std h) consumed fuel input hist pos rest st out =
        utf7Loop input h consumed fuel pos rest st out := by
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ fuel ih =>
    intro hist pos rest st out
    cases rest with
    | nil =>
      simp only [utf7LoopX, utf7Loop, u7HandlerX, u7Handler, handlerStep]
      by_cases h1 : (st.inShift && !consumed) = true
      · simp only [h1, if_true]
        by_cases h2 : (st.surrogate != 0 || decide (st.base64bits ≥ 6) ||
            (decide (st.base64bits > 0) && st.base64buffer != 0)) = true
        · simp only [h2, if_true]
          cases decodeHandlerCall h "utf7" .unknown input st.startinpos input.length
            "unterminated shift sequence" with
          | error x => rfl
          | ok p =>
            obtain ⟨w, newpos⟩ := p
            exact ih ..
        · simp only [h2, Bool.false_eq_true, if_false]
      · simp only [h1, Bool.false_eq_true, if_false]
    | cons ch t =>
      simp only [utf7LoopX, utf7Loop, u7HandlerX, u7Handler, handlerStep]
      cases u7Step st pos out.length ch t.head? with
      | go w n st' => exact ih ..
      | fail r n st' =>
        dsimp only
        cases decodeHandlerCall h "utf7" .unknown input st'.startinpos (pos + n) r with
        | error x => rfl
        | ok p =>
          obtain ⟨w, newpos⟩ := p
          exact ih ..

/-! ## The entry points -/

/-- `PyUnicode_DecodeUTF16Stateful`, unicodeobject.c:6285-6437, with any handler. `fuel` has to
outlast a handler that moves the position back. -/
def utf16DecodeX (input : Bytes) (bo : Int) (H : DH) (final : Bool) (fuel : Nat) : Py (Str × Nat) :=
  let (bo, q) := bom16 bo input
  let rest := input.drop q
  if rest.isEmpty then .ok ([], input.length)
  else
    let le := decide (bo ≤ 0)
    decodeDriverX (step16 le !final) H (if le then "utf-16-le" else "utf-16-be")
      (if le then .utf16le else .utf16be) none fuel input [] q rest []

/-- `PyUnicode_DecodeUTF32Stateful`, unicodeobject.c:5978-6120, with any handler. -/
def utf32DecodeX (input : Bytes) (bo : Int) (H : DH) (final : Bool) (fuel : Nat) : Py (Str × Nat) :=
  let (bo, q) := bom32 bo input
  let rest := input.drop q
  if rest.isEmpty then .ok ([], input.length)
  else
    let le := decide (bo ≤ 0)
    decodeDriverX (step32 le !final) H (if le then "utf-32-le" else "utf-32-be")
      (if le then .utf32le else .utf32be) none fuel input [] q rest []

/-- `PyUnicode_DecodeASCII`, unicodeobject.c:7579-7675, with any handler. -/
def asciiDecodeX (input : Bytes) (H : DH) (fuel : Nat) : Py Str := do
  let (s, _) ← decodeDriverX stepAscii H "ascii" .unknown none fuel input [] 0 input []
  .ok s

/-- `_PyUnicode_DecodeUnicodeEscapeInternal2`, unicodeobject.c:6629-6876, with any handler. -/
def unicodeEscapeDecodeX (input : Bytes) (H : DH) (nameToCode : List Nat → Option Nat)
    (final : Bool) (fuel : Nat) : Py (Str × Nat) :=
  if input.isEmpty then .ok ([], 0)
  else
    decodeDriverX (stepUnicodeEscape nameToCode !final) H "unicodeescape" .unknown (some input.length)
      fuel input [] 0 input []

/-- `_PyUnicode_DecodeRawUnicodeEscapeStateful`, unicodeobject.c:7045-7178, with any handler. -/
def rawEscapeDecodeX (input : Bytes) (H : DH) (final : Bool) (fuel : Nat) : Py (Str × Nat) :=
  if input.isEmpty then .ok ([], 0)
  else
    decodeDriverX (stepRawEscape !final) H "rawunicodeescape" .unknown (some input.length) fuel input
      [] 0 input []

/-- `PyUnicode_DecodeCharmap`, unicodeobject.c:8620-8651, with any handler. -/
def charmapDecodeX (input : Bytes) (mapping : DecMap) (H : DH) (fuel : Nat) : Py Str := do
  if input.isEmpty then .ok []
  else
    let step := match mapping with
      | .str t => stepCharmapString t
      | .map m => stepCharmapMapping m
    let (s, _) ← decodeDriverX step H "charmap" .unknown none fuel input [] 0 input []
    .ok s

/-- `PyUnicode_DecodeUTF7Stateful`, unicodeobject.c:4734-4928, with any handler. -/
def utf7DecodeX (input : Bytes) (H : DH) (final : Bool) (fuel : Nat) : Py (Str × Nat) :=
  if input.isEmpty then .ok ([], 0)
  else
    match utf7LoopX H (!final) fuel input [] 0 input {} [] with
    | .error e => .error e
    | .ok (out, st, pos) =>
      if !final && st.inShift then .ok (out.take st.shiftOutStart, st.startinpos)
      else .ok (out, pos)

/-- `bytes.decode('utf-8', errors)`, with any handler. -/
def utf8DecodeX (input : Bytes) (H : DH) (consumed : Bool) (fuel : Nat) : Py (Str × Nat) :=
  utf8DecodeLoopX H consumed fuel input [] 0 input []

/-! ## Encoders -/

/-- What the exception looks like to an encode handler. -/
structure EncView where
  object : Str
  encoding : String
  start : Nat
  stop : Nat
  reason : String
  deriving Repr, DecidableEq

/-- What an encode handler did. -/
inductive EncResp where
  | raises (e : PyExc)
  /-- Not a tuple, or a tuple of the wrong size. -/
  | bad
  /-- A tuple whose position converts but whose replacement is neither `str` nor `bytes`: `O`
accepts anything, so the check comes after the position's. -/
  | badRep (newpos : Int)
  | ret (rep : EncRep) (newpos : Int)
  deriving Repr, DecidableEq

abbrev EncCB := List EncView → EncResp

/-- The `errors` of an encoder. -/
inductive EH where
  | std (h : ErrHandler)
  | custom (cb : EncCB)
  | missing (name : String)

/-- `unicode_encode_call_errorhandler`, unicodeobject.c:7320-7374, with `make_encode_exception`,
:7278-7300. -/
def encodeCallback (cb : EncCB) (hist : List EncView) (enc reason : String) (input : Str)
    (start stop : Nat) : Py (List EncView × EncRep × Nat) := do
  let hist' := hist ++ [{ object := input, encoding := enc, start, stop, reason }]
  let msg : PyExc := .typeError "encoding error handler must return (str/bytes, int) tuple"
  match cb hist' with
  | .raises e => .error e
  | .bad => .error msg
  | .badRep newpos =>
    let _ ← ssizeOfIndex newpos
    .error msg
  | .ret rep newpos0 =>
    let newpos0 ← ssizeOfIndex newpos0
    let len : Int := input.length
    let newpos := if newpos0 < 0 then len + newpos0 else newpos0
    if newpos < 0 ∨ newpos > len then
      .error (.indexError s!"position {newpos} from error handler out of bounds")
    else .ok (hist', rep, newpos.toNat)

/-- One call of whichever handler `errors` names. -/
def encHandlerStep (H : EH) (nameOf : Nat → Option Str) (enc : String) (code : EncCode)
    (reason : String) (input : Str) (hist : List EncView) (start stop : Nat) :
    Py (List EncView × EncRep × Nat) :=
  match H with
  | .std h =>
    match encodeHandlerCall h nameOf enc code input start stop reason with
    | .error e => .error e
    | .ok (rep, newpos) => .ok (hist, rep, newpos)
  | .custom cb => encodeCallback cb hist enc reason input start stop
  | .missing name => .error (lookupError name)

/-- `unicode_encode_ucs1`'s loop with any handler. -/
def ucs1EncodeLoopX (input : Str) (limit : Nat) (H : EH) (nameOf : Nat → Option Str) :
    Nat → List EncView → Nat → List Nat → Bytes → Py Bytes
  | 0, _, _, _, _ => .error .modelFuel
  | _ + 1, _, _, [], out => .ok out
  | fuel + 1, hist, pos, c :: cs, out =>
    if c < limit then ucs1EncodeLoopX input limit H nameOf fuel hist (pos + 1) cs (out ++ [c])
    else
      let enc := if limit == 256 then "latin-1" else "ascii"
      let reason := if limit == 256 then "ordinal not in range(256)"
        else "ordinal not in range(128)"
      let run := unencodableRun limit (c :: cs)
      let collend := pos + run.length
      let go (w : Bytes) :=
        ucs1EncodeLoopX input limit H nameOf fuel hist collend ((c :: cs).drop run.length) (out ++ w)
      let viaHandler (collstart : Nat) (out : Bytes) : Py Bytes :=
        match encHandlerStep H nameOf enc .unknown reason input hist collstart collend with
        | .error e => .error e
        | .ok (hist', rep, newpos) =>
          let next (w : Bytes) :=
            ucs1EncodeLoopX input limit H nameOf fuel hist' newpos (input.drop newpos) (out ++ w)
          match rep with
          | .bytes b => next b
          | .str r =>
            if r.all (· < limit) then next r
            else .error (encodeError enc input collstart collend reason)
      match H with
      | .std .strict => .error (encodeError enc input pos collend reason)
      | .std .replace => go (List.replicate run.length 63)
      | .std .ignore => go []
      | .std .backslashreplace => go (run.flatMap escapeEncodeChar)
      | .std .xmlcharrefreplace => go (run.flatMap xmlRef)
      | .std .surrogateescape =>
        let pre := escapedPrefix run
        if pre.length = run.length then go (pre.map (· - 0xdc00))
        else viaHandler (pos + pre.length) (out ++ pre.map (· - 0xdc00))
      | _ => viaHandler pos out

/-- `encodeWideLoop` with any handler. -/
def encodeWideLoopX (charBytes : Nat → List Nat) (unitSize : Nat) (H : EH)
    (nameOf : Nat → Option Str) (enc : String) (code : EncCode) (input : Str) :
    Nat → List EncView → Nat → List Nat → Bytes → Py Bytes
  | 0, _, _, _, _ => .error .modelFuel
  | _ + 1, _, _, [], out => .ok out
  | fuel + 1, hist, pos, c :: cs, out =>
    if !isSurrogate c then
      encodeWideLoopX charBytes unitSize H nameOf enc code input fuel hist (pos + 1) cs
        (out ++ charBytes c)
    else
      let reason := "surrogates not allowed"
      match encHandlerStep H nameOf enc code reason input hist pos (pos + 1) with
      | .error e => .error e
      | .ok (hist', rep, newpos) =>
        let bad := encodeError enc input pos (pos + 1) reason
        let next := fun (w : Bytes) =>
          encodeWideLoopX charBytes unitSize H nameOf enc code input fuel hist' newpos
            (input.drop newpos) (out ++ w)
        match rep with
        | .bytes b => if b.length % unitSize != 0 then .error bad else next b
        | .str r =>
          if !(r.all (· < 128)) then .error bad else next (r.flatMap charBytes)

/-- `STRINGLIB(utf8_encoder)`, codecs.h:260-470, with any handler: the inline cases, then the
`default:` branch. -/
def utf8EncodeLoopX (input : Str) (H : EH) (nameOf : Nat → Option Str) :
    Nat → List EncView → Nat → List Nat → List Nat → Py (List Nat)
  | 0, _, _, _, _ => .error .modelFuel
  | _ + 1, _, _, [], out => .ok out
  | fuel + 1, hist, pos, c :: cs, out =>
    if !isSurrogate c then
      utf8EncodeLoopX input H nameOf fuel hist (pos + 1) cs (out ++ utf8EncodeChar c)
    else
      let (run, after) := surrogateRun (c :: cs)
      let stopAt := pos + run.length
      let reason := "surrogates not allowed"
      let go (w : List Nat) := utf8EncodeLoopX input H nameOf fuel hist stopAt after (out ++ w)
      let fail (start : Nat) : Py (List Nat) := .error (encodeError "utf-8" input start stopAt reason)
      let viaHandler : Py (List Nat) :=
        match encHandlerStep H nameOf "utf-8" .utf8 reason input hist pos stopAt with
        | .error e => .error e
        | .ok (hist', rep, newpos) =>
          let next (w : List Nat) :=
            utf8EncodeLoopX input H nameOf fuel hist' newpos (input.drop newpos) (out ++ w)
          match rep with
          | .bytes b => next b
          | .str r => if r.all (· < 128) then next r else fail pos
      match H with
      | .std .replace => go (List.replicate run.length 63)
      | .std .ignore => go []
      | .std .surrogatepass => go (run.flatMap utf8EncodeChar)
      | .std .backslashreplace | .std .namereplace => go (run.flatMap escapeEncodeChar)
      | .std .xmlcharrefreplace => go (run.flatMap xmlRef)
      | .std .surrogateescape =>
        match run.findIdx? (fun x => !(decide (0xDC80 ≤ x) && decide (x ≤ 0xDCFF))) with
        | none => go (run.map (· - 0xdc00))
        | some k => fail (pos + k)
      | .std .strict => fail pos
      | _ => viaHandler

/-- `charmap_encoding_error`, unicodeobject.c:8975-9112, with any handler. -/
def charmapEncodingErrorX (input : Str) (mapping : EncMap) (H : EH) (nameOf : Nat → Option Str)
    (hist : List EncView) (inpos : Nat) : Py (List EncView × Bytes × Nat) := do
  let n ← charmapCollect mapping (input.drop (inpos + 1))
  let collend := inpos + 1 + n
  let reason := "character maps to <undefined>"
  let bad := encodeError "charmap" input inpos collend reason
  let run := (input.drop inpos).take (collend - inpos)
  match H with
  | .std .strict => .error bad
  | .std .replace => .ok (hist, ← charmapWriteAll mapping bad (List.replicate run.length 63), collend)
  | .std .ignore => .ok (hist, [], collend)
  | .std .xmlcharrefreplace => .ok (hist, ← charmapWriteAll mapping bad (run.flatMap xmlRef), collend)
  | _ =>
    let (hist', rep, newpos) ← encHandlerStep H nameOf "charmap" .unknown reason input hist inpos collend
    match rep with
    | .bytes b => .ok (hist', b, newpos)
    | .str r => .ok (hist', ← charmapWriteAll mapping bad r, newpos)

/-- `_PyUnicode_EncodeCharmap`'s loop with any handler. -/
def charmapEncodeLoopX (input : Str) (mapping : EncMap) (H : EH) (nameOf : Nat → Option Str) :
    Nat → List EncView → Nat → List Nat → Bytes → Py Bytes
  | 0, _, _, _, _ => .error .modelFuel
  | _ + 1, _, _, [], out => .ok out
  | fuel + 1, hist, pos, c :: cs, out =>
    match charmapencodeOutput mapping c with
    | .error e => .error e
    | .ok (some w) => charmapEncodeLoopX input mapping H nameOf fuel hist (pos + 1) cs (out ++ w)
    | .ok none =>
      match charmapEncodingErrorX input mapping H nameOf hist pos with
      | .error e => .error e
      | .ok (hist', w, newpos) =>
        charmapEncodeLoopX input mapping H nameOf fuel hist' newpos (input.drop newpos) (out ++ w)

/-- `_PyUnicode_EncodeUTF16` with any handler. -/
def utf16EncodeX (s : Str) (byteorder : Int) (H : EH) (nameOf : Nat → Option Str) (fuel : Nat) :
    Py Bytes :=
  let le := decide (byteorder ≤ 0)
  let enc := if byteorder < 0 then "utf-16-le" else if byteorder > 0 then "utf-16-be" else "utf-16"
  let bom := if byteorder = 0 then unitBytes le 0xFEFF else []
  encodeWideLoopX (utf16Char le) 2 H nameOf enc (if le then .utf16le else .utf16be) s fuel [] 0 s bom

/-- `_PyUnicode_EncodeUTF32` with any handler. -/
def utf32EncodeX (s : Str) (byteorder : Int) (H : EH) (nameOf : Nat → Option Str) (fuel : Nat) :
    Py Bytes :=
  let le := decide (byteorder ≤ 0)
  let enc := if byteorder = -1 then "utf-32-le" else if byteorder = 1 then "utf-32-be" else "utf-32"
  let bom := if byteorder = 0 then utf32Char le 0xFEFF else []
  encodeWideLoopX (utf32Char le) 4 H nameOf enc (if le then .utf32le else .utf32be) s fuel [] 0 s bom

end PyLean.UnicodeObj
