import PyLean.UnicodeObj.CodecAscii
import PyLean.UnicodeObj.TextTranslate

/-!
The charmap codec: `charmap_decode_string` (unicodeobject.c:8400-8513),
`charmap_decode_mapping` (:8516-8617), `PyUnicode_BuildEncodingMap` (:8696-8809),
`encoding_map_lookup` (:8812-8840), and the encoder `charmapencode_lookup`,
`charmapencode_output`, `charmap_encoding_error` and `_PyUnicode_EncodeCharmap`
(:8848-9182).

The mapping is an abstract pure function, as for `translate`. The fast paths of
`charmap_decode_string` for tables of at least 256 entries write what the general path
writes; the difftest checks them.
-/

namespace PyLean.UnicodeObj

open PyLean

/-- One round of the general path of `charmap_decode_string`, unicodeobject.c:8473-8498. -/
def stepCharmapString (table : Str) : List Nat → DStep
  | [] => .stop
  | ch :: _ =>
    let x := if ch < table.length then table.getD ch 0 else 0xfffe
    if x == 0xfffe then .fail "character maps to <undefined>" 0 1 else .char x 1

/-- One round of `charmap_decode_mapping`, unicodeobject.c:8530-8600. -/
def stepCharmapMapping (m : Mapping) : List Nat → DStep
  | [] => .stop
  | ch :: _ =>
    let undefined : DStep := .fail "character maps to <undefined>" 0 1
    match m ch with
    | .missing | .pyNone => undefined
    | .raises e => .raise e
    | .int v =>
      if v = 0xFFFE then undefined
      else if v < 0 ∨ v > maxUnicode then
        .raise (.typeError "character mapping must be in range(0x110000)")
      else .char v.toNat 1
    | .str s =>
      match s with
      | [v] => if v == 0xFFFE then undefined else .char v 1
      | _ => .multi s 1
    | .wrong => .raise (.typeError "character mapping must return integer, None or str")

/-- `mapping` of `PyUnicode_DecodeCharmap`: exactly a `str`, or anything else. -/
inductive DecMap where
  | str (table : Str)
  | map (m : Mapping)

/-- `PyUnicode_DecodeCharmap`, unicodeobject.c:8620-8651. -/
def charmapDecode (input : Bytes) (mapping : DecMap) (h : ErrHandler) : Py Str := do
  if input.isEmpty then .ok []
  else
    let step := match mapping with
      | .str t => stepCharmapString t
      | .map m => stepCharmapMapping m
    let (s, _) ← decodeDriver step h "charmap" .unknown input (input.length + 1) 0 input []
    .ok s

/-! ## The encoding map -/

/-- `struct encoding_map`, with the levels as functions. -/
structure Trie where
  level1 : Nat → Nat
  level2 : Nat → Nat
  level3 : Nat → Nat
  count2 : Nat
  count3 : Nat

/-- `PyUnicode_BuildEncodingMap` returns a dict or a trie. -/
inductive EMap where
  | dict (items : List (Nat × Nat))
  | trie (t : Trie)

/-- A `memset`-to-`d` array updated at some indices. -/
def fnSet (f : Nat → Nat) (i v : Nat) : Nat → Nat := fun j => if j = i then v else f j

/-- The first loop of `PyUnicode_BuildEncodingMap`, unicodeobject.c:8725-8740:
`(level1, level2, count2, count3, need_dict)`. -/
def buildScan : List Nat → (Nat → Nat) → (Nat → Nat) → Nat → Nat → (Nat → Nat) × (Nat → Nat) × Nat × Nat × Bool
  | [], l1, l2, c2, c3 => (l1, l2, c2, c3, false)
  | ch :: t, l1, l2, c2, c3 =>
    if ch == 0 || ch > 0xFFFF then (l1, l2, c2, c3, true)
    else if ch == 0xFFFE then buildScan t l1 l2 c2 c3
    else
      let k1 := ch / 2048
      let k2 := ch / 128
      let (l1, c2) := if l1 k1 == 0xFF then (fnSet l1 k1 c2, c2 + 1) else (l1, c2)
      let (l2, c3) := if l2 k2 == 0xFF then (fnSet l2 k2 c3, c3 + 1) else (l2, c3)
      buildScan t l1 l2 c2 c3

/-- The trie filling loop, unicodeobject.c:8783-8798: `(mlevel2, mlevel3, count3)`. -/
def trieFill (mlevel1 : Nat → Nat) : Nat → List Nat → (Nat → Nat) → (Nat → Nat) → Nat →
    (Nat → Nat) × (Nat → Nat) × Nat
  | _, [], m2, m3, c3 => (m2, m3, c3)
  | i, ch :: t, m2, m3, c3 =>
    if ch == 0xFFFE then trieFill mlevel1 (i + 1) t m2 m3 c3
    else
      let i2 := 16 * mlevel1 (ch / 2048) + ch / 128 % 16
      let (m2, c3) := if m2 i2 == 0xFF then (fnSet m2 i2 c3, c3 + 1) else (m2, c3)
      let i3 := 128 * m2 i2 + ch % 128
      trieFill mlevel1 (i + 1) t m2 (fnSet m3 i3 i) c3

/-- `dict[c] = i` in order: later positions win, in the first position of the key. -/
def dictAssign (items : List (Nat × Nat)) (k v : Nat) : List (Nat × Nat) :=
  if items.any (·.1 == k) then items.map fun e => if e.1 == k then (k, v) else e
  else items ++ [(k, v)]

/-- `PyUnicode_BuildEncodingMap`, unicodeobject.c:8696-8809. `string` is not empty. -/
def buildEncodingMap (string : Str) : EMap :=
  let table := string.take 256
  let (l1, l2, c2, c3, need0) := buildScan table.tail (fun _ => 0xFF) (fun _ => 0xFF) 0 0
  let needDict := need0 || table.headD 0 != 0 || c2 ≥ 0xFF || c3 ≥ 0xFF
  if needDict then
    .dict ((List.range table.length).foldl (fun d i => dictAssign d (table.getD i 0) i) [])
  else
    let (m2, m3, c3') := trieFill l1 1 table.tail (fun _ => 0xFF) (fun _ => 0) 0
    let _ := l2
    .trie { level1 := l1, level2 := m2, level3 := m3, count2 := c2, count3 := c3' }

/-- `encoding_map_lookup`, unicodeobject.c:8812-8840: the byte, or `none` for -1. -/
def encodingMapLookup (c : Nat) (t : Trie) : Option Nat :=
  if c > 0xFFFF then none
  else if c = 0 then some 0
  else
    let i := t.level1 (c / 2048)
    if i == 0xFF then none
    else
      let i := t.level2 (16 * i + c / 128 % 16)
      if i == 0xFF then none
      else
        let i := t.level3 (128 * i + c % 128)
        if i == 0 then none else some i

/-- `EncodingMap_size_impl`, unicodeobject.c:8674-8679, on a 64-bit build:
`sizeof(struct encoding_map) - 1` is 63. -/
def encodingMapSize (t : Trie) : Nat := 63 + 16 * t.count2 + 128 * t.count3

/-- What a mapping's `__getitem__` gives the encoder. -/
inductive EncItem where
  | missing | pyNone
  | int (v : Int)
  | bytes (b : Bytes)
  | wrong (typeName : String)
  | raises (e : PyExc)
  deriving Repr, DecidableEq

/-- `mapping` of the encoder. -/
inductive EncMap where
  | trie (t : Trie)
  | map (m : Nat → EncItem)

/-- `charmapencode_lookup`, unicodeobject.c:8848-8892: `none` stands for `Py_None`. -/
def charmapencodeLookup (m : Nat → EncItem) (c : Nat) : Py (Option Bytes) :=
  match m c with
  | .missing | .pyNone => .ok none
  | .raises e => .error e
  | .int v =>
    if v < 0 ∨ v > 255 then .error (.typeError "character mapping must be in range(256)")
    else .ok (some [v.toNat])
  | .bytes b => .ok (some b)
  | .wrong t =>
    .error (.typeError s!"character mapping must return integer, bytes or None, not {t}")

/-- `charmapencode_output`, unicodeobject.c:8916-8970: the bytes, or `none` for
`enc_FAILED`. -/
def charmapencodeOutput (mapping : EncMap) (c : Nat) : Py (Option Bytes) :=
  match mapping with
  | .trie t => .ok ((encodingMapLookup c t).map ([·]))
  | .map m => charmapencodeLookup m c

/-- The `while (collendpos < size)` of `charmap_encoding_error`, unicodeobject.c:8999-9022:
how many characters from the head are unencodable. -/
def charmapCollect (mapping : EncMap) : List Nat → Py Nat
  | [] => .ok 0
  | c :: cs =>
    match charmapencodeOutput mapping c with
    | .error e => .error e
    | .ok (some _) => .ok 0
    | .ok none =>
      match charmapCollect mapping cs with
      | .error e => .error e
      | .ok n => .ok (n + 1)

/-- Output each character through the mapping, failing as the handler paths do. -/
def charmapWriteAll (mapping : EncMap) (bad : PyExc) : List Nat → Py Bytes
  | [] => .ok []
  | c :: cs =>
    match charmapencodeOutput mapping c with
    | .error e => .error e
    | .ok none => .error bad
    | .ok (some w) =>
      match charmapWriteAll mapping bad cs with
      | .error e => .error e
      | .ok r => .ok (w ++ r)

/-- `charmap_encoding_error`, unicodeobject.c:8975-9113: what to write and the new `inpos`. -/
def charmapEncodingError (input : Str) (mapping : EncMap) (h : ErrHandler)
    (nameOf : Nat → Option Str) (inpos : Nat) : Py (Bytes × Nat) := do
  let n ← charmapCollect mapping (input.drop (inpos + 1))
  let collend := inpos + 1 + n
  let reason := "character maps to <undefined>"
  let bad := encodeError "charmap" input inpos collend reason
  let run := (input.drop inpos).take (collend - inpos)
  match h with
  | .strict => .error bad
  | .replace => .ok (← charmapWriteAll mapping bad (List.replicate run.length 63), collend)
  | .ignore => .ok ([], collend)
  | .xmlcharrefreplace => .ok (← charmapWriteAll mapping bad (run.flatMap xmlRef), collend)
  | _ =>
    let (rep, newpos) ← encodeHandlerCall h nameOf "charmap" .unknown input inpos collend reason
    match rep with
    | .bytes b => .ok (b, newpos)
    | .str r => .ok (← charmapWriteAll mapping bad r, newpos)

/-- The `while (inpos<size)` of `_PyUnicode_EncodeCharmap`, unicodeobject.c:9150-9166. -/
def charmapEncodeLoop (input : Str) (mapping : EncMap) (h : ErrHandler)
    (nameOf : Nat → Option Str) : Nat → Nat → List Nat → Bytes → Py Bytes
  | 0, _, _, _ => .error .modelFuel
  | _ + 1, _, [], out => .ok out
  | fuel + 1, pos, c :: cs, out =>
    match charmapencodeOutput mapping c with
    | .error e => .error e
    | .ok (some w) => charmapEncodeLoop input mapping h nameOf fuel (pos + 1) cs (out ++ w)
    | .ok none =>
      match charmapEncodingError input mapping h nameOf pos with
      | .error e => .error e
      | .ok (w, newpos) =>
        charmapEncodeLoop input mapping h nameOf fuel newpos (input.drop newpos) (out ++ w)

/-- `_PyUnicode_EncodeCharmap`, unicodeobject.c:9116-9182. -/
def charmapEncode (s : Str) (mapping : EncMap) (h : ErrHandler) (nameOf : Nat → Option Str) :
    Py Bytes :=
  charmapEncodeLoop s mapping h nameOf (s.length + 1) 0 s []

end PyLean.UnicodeObj
