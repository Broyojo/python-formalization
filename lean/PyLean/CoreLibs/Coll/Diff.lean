import PyLean.DiffCore
import PyLean.CoreLibs.Coll.UserDict
import PyLean.CoreLibs.Coll.UserList
import PyLean.CoreLibs.Coll.UserString
import PyLean.CoreLibs.Coll.Namedtuple

/-! Differential-testing handler for `corelibs` cases with `"fn": "coll.<name>"`.
The dispatcher in `CoreLibs/Diff.lean` strips the `coll.` prefix.

Keys in the cases are strings, counts are ints; a dict or a `Counter` is a list of
`[key, value]` pairs in insertion order. -/

namespace PyLean.CoreLibs.Coll

open Lean PyLean PyLean.Diff
open PyLean.StrSearch (Seq)

/-- `repr` of the short strings the generator uses as keys. -/
def rkStr (s : String) : String := "'" ++ s ++ "'"

def jArr (j : Json) : Except String (List Json) := do
  match j with
  | .arr a => return a.toList
  | _ => throw "expected array"

def decPair (j : Json) : Except String (String × Int) := do
  match ← jArr j with
  | [k, v] => return (← k.getStr?, ← v.getInt?)
  | _ => throw "expected pair"

def getItems (j : Json) (key : String) : Except String (Ctr String) := do
  (← jArr (← field j key)).mapM decPair

def getStrs (j : Json) (key : String) : Except String (List String) := do
  (← jArr (← field j key)).mapM Json.getStr?

def encItems (c : Ctr String) : Json :=
  Json.arr (c.map (fun p => Json.arr #[toJson p.1, toJson p.2])).toArray

def encStrs (l : List String) : Json := Json.arr (l.map toJson).toArray

def okJ (j : Json) : Json := Json.mkObj [("ok", j)]
def okE (c : Ctr String) : Json := okJ (encItems c)
def okI (i : Int) : Json := okJ (toJson i)
def okS (s : String) : Json := okJ (toJson s)

/-- `{"src": "none"|"mapping"|"iter", "items"|"xs": ...}`. -/
def getSrc (j : Json) : Except String (Src String) := do
  match ← getStr j "src" with
  | "none" => return .none
  | "mapping" => return .mapping (← getItems j "items")
  | "iter" => return .iter (← getStrs j "xs")
  | s => throw s!"bad src {s}"

/-- The `b` operand of an in-place operator. -/
def getIOpnd (j : Json) : Except String (IOpnd String) := do
  match ← getStr j "bty" with
  | "Counter" => return .ctr (← getItems j "b")
  | "dict" => return .dict (← getItems j "b")
  | ty => return .nonmapping ty

/-- A binary dunder: a `Counter` right operand, or `b` absent. -/
def binop (j : Json) (opname : String) (f : Ctr String → Ctr String → Ctr String) : Except String Json := do
  let a ← getItems j "a"
  match j.getObjVal? "b" with
  | .ok .null | .error _ =>
    return encPy encItems (.error (.typeError
      s!"unsupported operand type(s) for {opname}: 'Counter' and 'int'"))
  | .ok _ => return encPy encItems (.ok (f a (← getItems j "b")))

/-- A rich comparison. `__eq__`/`__ne__` on a non-`Counter` fall back to identity,
ordering raises. -/
def cmpop (j : Json) (opname : String) (f : Ctr String → Ctr String → Bool) : Except String Json := do
  let a ← getItems j "a"
  match j.getObjVal? "b" with
  | .ok .null | .error _ =>
    if opname == "==" then return encPy toJson (.ok false)
    else if opname == "!=" then return encPy toJson (.ok true)
    else return encPy (fun (b : Bool) => toJson b) (.error (.typeError
      s!"'{opname}' not supported between instances of 'Counter' and 'int'"))
  | .ok _ => return encPy (fun (b : Bool) => toJson b) (.ok (f a (← getItems j "b")))

def runCtr (j : Json) : Except String Json := do
  let op ← getStr j "op"
  match op with
  | "new" => return okE (counterNew (← getSrc j) (← getItems j "kw"))
  | "update" => return okE (update (← getItems j "a") (← getSrc j) (← getItems j "kw"))
  | "subtract" => return okE (subtract (← getItems j "a") (← getSrc j) (← getItems j "kw"))
  | "count_py" => return okE (countElementsPy (← getItems j "a") (← getStrs j "xs"))
  | "count_c" => return okE (countElements (← getItems j "a") (← getStrs j "xs"))
  | "count_slow" => return okE (countElementsCSlow (← getItems j "a") (← getStrs j "xs"))
  | "total" => return okI (total (← getItems j "a"))
  | "most_common" => return encPy encItems (mostCommon (← getItems j "a") (← getOptInt j "n"))
  | "elements" => return encPy encStrs (elements (← getItems j "a"))
  | "copy" => return okE (counterCopy (← getItems j "a"))
  | "reduce" => return okE (counterReduce (← getItems j "a"))
  | "delitem" => return okE (delitem (← getItems j "a") (← getStr j "e"))
  | "getitem" => return okI (cGet (← getItems j "a") (← getStr j "e"))
  | "repr" => return okS (counterRepr "Counter" rkStr (← getItems j "a"))
  | "fromkeys" => return encPy encItems (counterFromkeys (← getStrs j "xs") none)
  | "keep_positive" => return okE (keepPositive (← getItems j "a"))
  | "pos" => return okE (posC (← getItems j "a"))
  | "neg" => return okE (negC (← getItems j "a"))
  | "add" => binop j "+" addC
  | "sub" => binop j "-" subC
  | "or" => binop j "|" orC
  | "and" => binop j "&" andC
  | "eq" => cmpop j "==" eqC
  | "ne" => cmpop j "!=" neC
  | "le" => cmpop j "<=" leC
  | "lt" => cmpop j "<" ltC
  | "ge" => cmpop j ">=" geC
  | "gt" => cmpop j ">" gtC
  | "iadd" => return encPy encItems (dunderIadd (← getItems j "a") (← getIOpnd j))
  | "isub" => return encPy encItems (dunderIsub (← getItems j "a") (← getIOpnd j))
  | "ior" => return encPy encItems (dunderIor (← getItems j "a") (← getIOpnd j))
  | "iand" => return encPy encItems (dunderIand rkStr (← getItems j "a") (← getIOpnd j))
  | _ => throw s!"unknown ctr op {op}"

/-! ### `ChainMap` -/

abbrev CM := CMap String Int

def getMaps (j : Json) : Except String CM := do
  let ms ← jArr (← field j "maps")
  return ⟨← ms.mapM (fun m => do (← jArr m).mapM decPair)⟩

def encCM (c : CM) : Json := Json.arr (c.maps.map encItems).toArray

def encPair (p : String × Int) : Json := Json.arr #[toJson p.1, toJson p.2]

def rvInt (v : Int) : String := toString v

/-- `coll_CMMiss.__missing__` returns -1; plain `ChainMap` raises. -/
def cmMiss (j : Json) : String → Py Int :=
  match j.getObjVal? "sub" with
  | .ok (.num 1) => fun _ => .ok (-1)
  | _ => cmMissing rkStr

def optOther (j : Json) : Except String (Option (Ctr String)) :=
  match j.getObjVal? "o" with
  | .ok .null | .error _ => .ok none
  | .ok _ => some <$> getItems j "o"

def runCM (j : Json) : Except String Json := do
  let op ← getStr j "op"
  let c ← getMaps j
  let miss := cmMiss j
  let k := (j.getObjVal? "k" >>= Json.getStr?).toOption.getD ""
  let dflt ← getOptInt j "d"
  match op with
  | "new" => return okJ (encCM (cmNew c.maps))
  | "getitem" => return encPy toJson (cmGetitem miss c k)
  | "get" => return encPy (fun (o : Option Int) => toJson o) (cmGet miss c k dflt)
  | "len" => return okI (cmLen c)
  | "iter" => return okJ (encStrs (cmIter c))
  | "contains" => return okJ (toJson (cmContains c k))
  | "bool" => return okJ (toJson (cmBool c))
  | "repr" => return okS (cmRepr "ChainMap" rkStr rvInt c)
  | "fromkeys" => return okJ (encCM (cmFromkeys (← getStrs j "xs") (dflt.getD 0)))
  | "copy" => return encPy encCM (cmCopy c)
  | "new_child" =>
    let m ← optOther j
    return okJ (encCM (cmNewChild c m (← getItems j "kw")))
  | "parents" => return okJ (encCM (cmParents c))
  | "setitem" => return encPy encCM (cmSetitem c k (dflt.getD 0))
  | "delitem" => return encPy encCM (cmDelitem rkStr c k)
  | "popitem" => return encPy (fun r => Json.arr #[encPair r.1, encCM r.2]) (cmPopitem c)
  | "pop" => return encPy (fun r => Json.arr #[toJson r.1, encCM r.2]) (cmPop rkStr c k dflt)
  | "clear" => return encPy encCM (cmClear c)
  | "ior" => return encPy encCM (cmIor c (← getItems j "o"))
  | "or" =>
    match cmOr c (← optOther j) with
    | some r => return encPy encCM r
    | none => return encPy encCM (.error (.typeError
        "unsupported operand type(s) for |: 'ChainMap' and 'int'"))
  | "ror" =>
    match cmRor c (← optOther j) with
    | some r => return okJ (encCM r)
    | none => return encPy encCM (.error (.typeError
        "unsupported operand type(s) for |: 'int' and 'ChainMap'"))
  | _ => throw s!"unknown cm op {op}"

/-! ### `UserDict` -/

abbrev U := UD String Int

def udClass (j : Json) : Except String (String × Option (String → Int)) := do
  match ← getNat j "sub" with
  | 0 => return ("UserDict", none)
  | 1 => return ("coll_UDPlain", none)
  | _ => return ("coll_UDMiss", some (fun _ => -1))

def encUD (u : U) : Json := Json.arr #[toJson u.cls, encItems u.data]

def getUOpnd (j : Json) : Except String (UOpnd String Int) := do
  match ← getStr j "oty" with
  | "user" => return .user (← getItems j "o")
  | "dict" => return .dict (← getItems j "o")
  | _ => return .other

def runUD (j : Json) : Except String Json := do
  let op ← getStr j "op"
  let (cls, miss) ← udClass j
  let u : U := ⟨cls, ← getItems j "a"⟩
  let k := (j.getObjVal? "k" >>= Json.getStr?).toOption.getD ""
  let dflt ← getOptInt j "d"
  let nop : String → Except String Json := fun sym =>
    return encPy encUD (.error (.typeError s!"unsupported operand type(s) for |: {sym}"))
  match op with
  | "new" =>
    let src ← optOther j
    return okJ (encUD (udNew cls src (← getItems j "kw")))
  | "len" => return okI (udLen u)
  | "getitem" => return encPy toJson (udGetitem rkStr miss u k)
  | "setitem" => return okJ (encUD (udSetitem u k (dflt.getD 0)))
  | "delitem" => return encPy encUD (udDelitem rkStr u k)
  | "iter" => return okJ (encStrs (udIter u))
  | "contains" => return okJ (toJson (udContains u k))
  | "get" => return encPy (fun (o : Option Int) => toJson o) (udGet rkStr miss u k dflt)
  | "repr" => return okS (udRepr rkStr rvInt u)
  | "or" =>
    match udOr u (← getUOpnd j) with
    | some r => return okJ (encUD r)
    | none => nop s!"'{cls}' and 'int'"
  | "ror" =>
    match udRor u (← getUOpnd j) with
    | some r => return okJ (encUD r)
    | none => nop s!"'int' and '{cls}'"
  | "ior" => return okJ (encUD (udIor u (← getItems j "o")))
  | "copy" => return okJ (encUD (udCopy u))
  | "copy_dunder" => return okJ (encUD (udCopyDunder u))
  | "fromkeys" => return okJ (encUD (udFromkeys cls (← getStrs j "xs") (dflt.getD 0)))
  | "pop" => return encPy (fun r => Json.arr #[toJson r.1, encUD r.2]) (udPop rkStr miss u k dflt)
  | "popitem" => return encPy (fun r => Json.arr #[encPair r.1, encUD r.2]) (udPopitem rkStr miss u)
  | "setdefault" =>
    let r := udSetdefault rkStr miss u k (dflt.getD 0)
    return okJ (Json.arr #[toJson r.1, encUD r.2])
  | "clear" => return okJ (encUD (udClear rkStr miss u))
  | "items_contains" => return okJ (toJson (udItemsContains rkStr miss u k (dflt.getD 0)))
  | "reversed" => return encPy encStrs (udReversed u)
  | "dict_reversed" => return encPy encStrs (dictReversed u.data)
  | "dict_getitem" => return encPy toJson (dictGetitem rkStr miss u.data k)
  | "dict_pop" => return encPy (fun r => Json.arr #[toJson r.1, encItems r.2]) (dictPop rkStr u.data k dflt)
  | "dict_popitem" => return encPy (fun r => Json.arr #[encPair r.1, encItems r.2]) (dictPopitem u.data)
  | "dict_setdefault" =>
    let r := dictSetdefault u.data k (dflt.getD 0)
    return okJ (Json.arr #[toJson r.1, encItems r.2])
  | "dict_items_contains" => return okJ (toJson (dictItemsContains u.data k (dflt.getD 0)))
  | _ => throw s!"unknown ud op {op}"

/-! ### `UserList` -/

def getInts (j : Json) (key : String) : Except String (List Int) := do
  (← jArr (← field j key)).mapM Json.getInt?

def encInts (l : List Int) : Json := Json.arr (l.map toJson).toArray

def getLOpnd (j : Json) : Except String (LOpnd Int) := do
  match ← getStr j "oty" with
  | "user" => return .user (← getInts j "o")
  | "list" => return .list (← getInts j "o")
  | "tuple" => return .iter "tuple" (← getInts j "o")
  | ty => return .noniter ty

def getSlice (j : Json) : Except String RangeSlice.Slice := do
  return ⟨← getOptInt j "st", ← getOptInt j "sp", ← getOptInt j "se"⟩

def encUL (u : UL Int) : Json := Json.arr #[toJson u.cls, encInts u.data]

def cmpOf : String → Option CmpOp
  | "lt" => some .lt
  | "le" => some .le
  | "eq" => some .eq
  | "gt" => some .gt
  | "ge" => some .ge
  | _ => none

def runUL (j : Json) : Except String Json := do
  let op ← getStr j "op"
  let cls := if (← getNat j "sub") = 0 then "UserList" else "coll_ULPlain"
  let u : UL Int := ⟨cls, ← getInts j "a"⟩
  let x := (← getOptInt j "x").getD 0
  let i := (← getOptInt j "i").getD 0
  let enc := encPy encUL
  if let some c := cmpOf op then
    return encPy (fun (b : Bool) => toJson b) (ulCmp intOps c u (← getLOpnd j))
  match op with
  | "new" =>
    match j.getObjVal? "oty" with
    | .ok _ => return enc (ulNew cls (some (← getLOpnd j)))
    | .error _ => return enc (ulNew cls none)
  | "repr" => return okS (ulRepr intOps u)
  | "contains" => return okJ (toJson (ulContains intOps u x))
  | "len" => return okI (ulLen u)
  | "getitem" => return encPy toJson (ulGetitem intOps u i)
  | "getslice" => return enc (ulGetslice intOps u (← getSlice j))
  | "setitem" => return enc (ulSetitem intOps u i x)
  | "setslice" => return enc (ulSetslice intOps u (← getSlice j) (← getInts j "o"))
  | "delitem" => return enc (ulDelitem intOps u i)
  | "delslice" => return enc (ulDelslice intOps u (← getSlice j))
  | "add" => return enc (ulAdd u (← getLOpnd j))
  | "radd" => return enc (ulRadd u (← getLOpnd j))
  | "iadd" => return enc (ulIadd u (← getLOpnd j))
  | "mul" => return enc (ulMul intOps u i)
  | "imul" => return enc (ulImul intOps u i)
  | "copy" => return enc (ulCopy u)
  | "copy_dunder" => return okJ (encUL (ulCopyDunder u))
  | "append" => return okJ (encUL (ulAppend u x))
  | "insert" => return enc (ulInsert intOps u i x)
  | "pop" => return encPy (fun r => Json.arr #[toJson r.1, encUL r.2]) (ulPop intOps u (← getOptInt j "i"))
  | "remove" => return enc (ulRemove intOps u x)
  | "clear" => return okJ (encUL (ulClear u))
  | "count" => return okI (ulCount intOps u x)
  | "index" => return encPy toJson (ulIndex intOps u x (← getOptInt j "st") (← getOptInt j "sp"))
  | "reverse" => return okJ (encUL (ulReverse intOps u))
  | "sort" => return okJ (encUL (ulSort intOps u (← getBool j "r")))
  | "extend" => return enc (ulExtend u (← getLOpnd j))
  | _ => throw s!"unknown ul op {op}"

/-! ### `UserString` -/

def isUp (c : Nat) : Bool := 65 ≤ c && c ≤ 90
def isLo (c : Nat) : Bool := 97 ≤ c && c ≤ 122
def isDig (c : Nat) : Bool := 48 ≤ c && c ≤ 57
def isAl (c : Nat) : Bool := isUp c || isLo c
def toLo (c : Nat) : Nat := if isUp c then c + 32 else c
def toUp (c : Nat) : Nat := if isLo c then c - 32 else c
def asciiWs (c : Nat) : Bool := (9 ≤ c && c ≤ 13) || (28 ≤ c && c ≤ 32)

def asciiTitle (prevCased : Bool) : Seq → Seq
  | [] => []
  | c :: t =>
    (if prevCased then toLo c else toUp c) :: asciiTitle (isAl c) t

def asciiCase : CaseFn → Seq → Seq
  | .lower, s | .casefold, s => s.map toLo
  | .upper, s => s.map toUp
  | .swapcase, s => s.map (fun c => if isUp c then toLo c else toUp c)
  | .capitalize, [] => []
  | .capitalize, c :: t => toUp c :: t.map toLo
  | .title, s => asciiTitle false s

/-- `str.istitle` on ASCII. -/
def asciiIsTitle (s : Seq) : Bool :=
  let rec go (prevCased cased : Bool) : Seq → Bool
    | [] => cased
    | c :: t =>
      if isUp c then !prevCased && go true true t
      else if isLo c then prevCased && go true true t
      else go false cased t
  go false false s

def asciiPred : PredFn → Seq → Bool
  | .isalpha, s => !s.isEmpty && s.all isAl
  | .isalnum, s => !s.isEmpty && s.all (fun c => isAl c || isDig c)
  | .isascii, _ => true
  | .isdecimal, s | .isdigit, s | .isnumeric, s => !s.isEmpty && s.all isDig
  | .isidentifier, [] => false
  | .isidentifier, c :: t =>
    (isAl c || c == 95) && t.all (fun c => isAl c || isDig c || c == 95)
  | .islower, s => s.any isLo && !s.any isUp
  | .isupper, s => s.any isUp && !s.any isLo
  | .isprintable, s => s.all (fun c => 32 ≤ c && c ≤ 126)
  | .isspace, s => !s.isEmpty && s.all asciiWs
  | .istitle, s => asciiIsTitle s

def strOfSeq (s : Seq) : String := String.ofList (s.map Char.ofNat)

/-- `repr(str)` on ASCII. -/
def asciiRepr (s : Seq) : String :=
  let q := if s.contains 39 && !s.contains 34 then "\"" else "'"
  let esc (c : Nat) : String :=
    if c == 92 then "\\\\"
    else if c == 10 then "\\n"
    else if c == 13 then "\\r"
    else if c == 9 then "\\t"
    else if c == 39 && q == "'" then "\\'"
    else if c < 32 || c == 127 then
      "\\x" ++ String.ofList (Nat.toDigits 16 (c + 256)).tail
    else String.singleton (Char.ofNat c)
  q ++ String.join (s.map esc) ++ q

/-- `int(s)` on ASCII, base 10, the digit strings the generator uses. -/
def asciiInt (s : Seq) : Option Int :=
  let t := (s.dropWhile asciiWs).reverse.dropWhile asciiWs |>.reverse
  let (neg, t) := match t with
    | 45 :: r => (true, r)
    | 43 :: r => (false, r)
    | r => (false, r)
  let rec digits (acc : Nat) (prevDigit : Bool) : Seq → Option Nat
    | [] => if prevDigit then some acc else none
    | 95 :: r => if prevDigit then digits acc false r else none
    | c :: r => if isDig c then digits (acc * 10 + (c - 48)) true r else none
  (digits 0 false t).map (fun n => if neg then -(n : Int) else n)

/-- `str.format` for the templates `x`, `{}`, `{}{}`, `{0}`, `{1}`. -/
def asciiFormat (s : Seq) (args : List Int) : Py Seq :=
  let at_ (i : Nat) : Py Seq :=
    match args[i]? with
    | some v => .ok ((toString v).toList.map Char.toNat)
    | none => .error (.indexError
        s!"Replacement index {i} out of range for positional args tuple")
  let rec go (auto : Nat) : Seq → Py Seq
    | [] => .ok []
    | 123 :: 125 :: r => do
      let v ← at_ auto
      let t ← go (auto + 1) r
      return v ++ t
    | 123 :: d :: 125 :: r => do
      let v ← at_ (d - 48)
      let t ← go auto r
      return v ++ t
    | c :: r => do
      let t ← go auto r
      return c :: t
  go 0 s

/-- `str.format_map` for the templates `x`, `{a}`. -/
def asciiFormatMap (s : Seq) (m : List (String × Int)) : Py Seq :=
  let rec go : Seq → Py Seq
    | [] => .ok []
    | 123 :: k :: 125 :: r => do
      let key := String.singleton (Char.ofNat k)
      match D.get? m key with
      | some v =>
        let t ← go r
        return (toString v).toList.map Char.toNat ++ t
      | none => .error (.keyError (rkStr key))
    | c :: r => do
      let t ← go r
      return c :: t
  go s

/-- `s % args` for a tuple of ints, `%d`, `%s`, `%%`. -/
def asciiMod (s : Seq) (args : List Int) : Py Seq :=
  let got := args.length
  let rec go (args : List Int) : Seq → Py Seq
    | [] => if args.isEmpty then .ok []
      else .error (.typeError
        s!"not all arguments converted during string formatting (required {got - args.length}, got {got})")
    | 37 :: 37 :: r => do
      let t ← go args r
      return 37 :: t
    | 37 :: _ :: r =>
      match args with
      | [] => .error (.typeError s!"not enough arguments for format string (got {got})")
      | a :: rest => do
        let t ← go rest r
        return (toString a).toList.map Char.toNat ++ t
    | c :: r => do
      let t ← go args r
      return c :: t
  go args s

/-- `template % u` for a `UserString` `u`: one object, which also passes for a mapping, so
leftover arguments are not an error. -/
def asciiModUser (s self : Seq) : Py Seq :=
  let rec go (used : Bool) : Seq → Py Seq
    | [] => .ok []
    | 37 :: 115 :: r =>
      if used then .error (.typeError "not enough arguments for format string (got 1)")
      else do
        let t ← go true r
        return self ++ t
    | c :: r => do
      let t ← go used r
      return c :: t
  go false s

def asciiTranslate (s : Seq) (t : List (Nat × Option Nat)) : Py Seq :=
  .ok (s.filterMap (fun c =>
    match D.get? t c with
    | some r => r
    | none => some c))

def asciiEncode (s : Seq) (enc err : String) : Py (List Nat) :=
  if enc == "utf-8" || enc == "ascii" then
    if err == "strict" || err == "ignore" then .ok s
    else .ok s
  else .error (.named "LookupError" s!"unknown encoding: {enc}")

def asciiOps : UniOps where
  case := asciiCase
  pred := asciiPred
  encode := asciiEncode
  format := asciiFormat
  formatMap := asciiFormatMap
  mod := asciiMod
  modUser := asciiModUser
  translate := asciiTranslate
  hash _ := 0
  repr := asciiRepr
  toInt s :=
    match asciiInt s with
    | some n => .ok n
    | none => .error (.valueError "~invalid literal")
  toFloat s :=
    match asciiInt s with
    | some n => .ok (toString n ++ ".0")
    | none => .error (.valueError "~could not convert")
  toComplex s :=
    match asciiInt s with
    | some n => .ok ("(" ++ toString n ++ "+0j)")
    | none => .error (.valueError "~malformed")

def decArg (j : Json) : Except String SArg := do
  match ← getStr j "k" with
  | "str" => return .str (← getSeqJ j)
  | "user" => return .user (← getSeqJ j)
  | ty => return .other ty (← getSeqJ j)
where
  getSeqJ (j : Json) : Except String Seq := do
    (← jArr (← field j "s")).mapM Json.getNat?

def getArg (j : Json) (key : String) : Except String SArg := do decArg (← field j key)

def getOptArg (j : Json) (key : String) : Except String (Option SArg) :=
  match j.getObjVal? key with
  | .ok .null | .error _ => .ok none
  | .ok v => some <$> decArg v

def getAffixArg (j : Json) : Except String AffixArg := do
  match j.getObjVal? "tup" with
  | .ok v =>
    let ps ← (← jArr v).mapM (fun p => do (← jArr p).mapM Json.getNat?)
    return .tuple ps
  | .error _ => return .one (← getArg j "a")

def encSeq (s : Seq) : Json := toJson s

def encURes : URes → Json
  | .us u => Json.mkObj [("us", Json.arr #[toJson u.cls, encSeq u.data])]
  | .str s => Json.mkObj [("str", encSeq s)]
  | .bool b => toJson b
  | .int i => toJson i
  | .strs l => Json.mkObj [("strs", Json.arr (l.map encSeq).toArray)]
  | .tup t => Json.mkObj [("tup", Json.arr #[encSeq t.1, encSeq t.2.1, encSeq t.2.2])]
  | .bytes b => Json.mkObj [("bytes", toJson b)]
  | .text s => Json.mkObj [("text", toJson s)]

def caseOf : String → Option CaseFn
  | "capitalize" => some .capitalize
  | "casefold" => some .casefold
  | "lower" => some .lower
  | "upper" => some .upper
  | "swapcase" => some .swapcase
  | "title" => some .title
  | _ => none

def predOf : String → Option PredFn
  | "isalpha" => some .isalpha
  | "isalnum" => some .isalnum
  | "isascii" => some .isascii
  | "isdecimal" => some .isdecimal
  | "isdigit" => some .isdigit
  | "isidentifier" => some .isidentifier
  | "islower" => some .islower
  | "isnumeric" => some .isnumeric
  | "isprintable" => some .isprintable
  | "isspace" => some .isspace
  | "istitle" => some .istitle
  | "isupper" => some .isupper
  | _ => none

def sopOf : String → Option SOp
  | "eq" => some .eq
  | "lt" => some .lt
  | "le" => some .le
  | "gt" => some .gt
  | "ge" => some .ge
  | _ => none

def getCall (op : String) (j : Json) : Except String SCall := do
  if let some f := caseOf op then return .case f
  if let some f := predOf op then return .pred f
  if let some f := sopOf op then return .rich f (← getArg j "a")
  let st ← getOptInt j "st"
  let en ← getOptInt j "en"
  let w := (← getOptInt j "w").getD 0
  match op with
  | "center" => return .center w (← getOptArg j "fill")
  | "ljust" => return .ljust w (← getOptArg j "fill")
  | "rjust" => return .rjust w (← getOptArg j "fill")
  | "zfill" => return .zfill w
  | "expandtabs" => return .expandtabs w
  | "count" => return .count (← getArg j "a") st en
  | "find" => return .find (← getArg j "a") st en true
  | "rfind" => return .find (← getArg j "a") st en false
  | "index" => return .index (← getArg j "a") st en true
  | "rindex" => return .index (← getArg j "a") st en false
  | "startswith" => return .startswith (← getAffixArg j) st en
  | "endswith" => return .endswith (← getAffixArg j) st en
  | "removeprefix" => return .removeprefix (← getArg j "a")
  | "removesuffix" => return .removesuffix (← getArg j "a")
  | "partition" => return .partition (← getArg j "a")
  | "rpartition" => return .rpartition (← getArg j "a")
  | "replace" => return .replace (← getArg j "a") (← getArg j "b") ((← getOptInt j "w").getD (-1))
  | "split" => return .split (← getOptArg j "a") ((← getOptInt j "w").getD (-1))
  | "rsplit" => return .rsplit (← getOptArg j "a") ((← getOptInt j "w").getD (-1))
  | "splitlines" => return .splitlines (← getBool j "keep")
  | "strip" => return .strip (← getOptArg j "a") .both
  | "lstrip" => return .strip (← getOptArg j "a") .left
  | "rstrip" => return .strip (← getOptArg j "a") .right
  | "join" => return .join (← (← jArr (← field j "items")).mapM decArg)
  | "contains" => return .contains (← getArg j "a")
  | "mul" => return .mul w
  | "getitem" => return .getitem w
  | "getslice" => return .getslice ⟨st, en, ← getOptInt j "se"⟩
  | "format" => return .format (← getInts j "args")
  | "format_map" => return .formatMap (← getItems j "m")
  | "mod" => return .mod (← getInts j "args")
  | "translate" =>
    let t ← (← jArr (← field j "t")).mapM (fun p => do
      match ← jArr p with
      | [k, v] => return ((← k.getNat?), (v.getNat?).toOption)
      | _ => throw "bad table")
    return .translate t
  | "encode" => return .encode (← getStr j "enc") (← getStr j "err")
  | "len" => return .len
  | "hash" => return .hash
  | "repr" => return .repr
  | "toInt" => return .toInt
  | "toFloat" => return .toFloat
  | "toComplex" => return .toComplex
  | _ => throw s!"unknown us op {op}"

def runUS (j : Json) : Except String Json := do
  let op ← getStr j "op"
  let cls := if (← getNat j "sub") = 0 then "UserString" else "coll_USPlain"
  let d ← (← jArr (← field j "s")).mapM Json.getNat?
  let u : US := ⟨cls, d⟩
  match op with
  | "new" => return okJ (encURes (.us (usNew cls (← getArg j "a"))))
  | "str" => return okJ (encURes (.str (usStr u)))
  | "getnewargs" => return okJ (encURes (.str (usGetnewargs u)))
  | "add" => return okJ (encURes (.us (usAdd u (← getArg j "a"))))
  | "radd" => return okJ (encURes (.us (usRadd u (← getArg j "a"))))
  | "rmod" =>
    let t ← (← jArr (← field j "t")).mapM Json.getNat?
    return encPy (fun v => encURes (.us v)) (usRmod asciiOps u t)
  | "replace_kw" =>
    let kw ← getStr j "kw"
    let w := (← getOptInt j "w").getD 0
    return encPy (fun v => encURes (.us v)) (usReplaceKw u (← getArg j "a") (← getArg j "b") kw w)
  | "str_replace_kw" =>
    let kw ← getStr j "kw"
    let w := (← getOptInt j "w").getD 0
    return encPy (fun v => encURes (.str v)) (strReplaceKw u.data (← getArg j "a") (← getArg j "b") kw w)
  | "dformat" => return encPy (fun v => encURes (.str v)) (usDunderFormat u (← getStr j "spec"))
  | "encode_none" => return encPy (fun v => encURes (.bytes v)) (usEncode asciiOps u none none)
  | _ =>
    let c ← getCall op j
    if (← getBool j "plain") then return encPy encURes (strCall asciiOps c u.data)
    else return encPy encURes (usCall asciiOps c u)

/-! ### `namedtuple` -/

/-- The NFKC of the characters the generator uses. -/
def nfkcChar (c : Char) : String :=
  let n := c.toNat
  if n == 0xfb01 then "fi"
  else if n == 0xff3f then "_"
  else if 0x1d400 ≤ n && n ≤ 0x1d419 then String.singleton (Char.ofNat (n - 0x1d400 + 65))
  else if 0x1d41a ≤ n && n ≤ 0x1d433 then String.singleton (Char.ofNat (n - 0x1d41a + 97))
  else String.singleton c

def idStart (c : Char) : Bool :=
  let n := c.toNat
  isAl n || n == 95 || n == 0xfb01 || (0x1d400 ≤ n && n ≤ 0x1d433)

def idCont (c : Char) : Bool := idStart c || isDig c.toNat || c.toNat == 0xff3f

/-- `str.isidentifier` and NFKC on the generator's alphabet. -/
def genU : UniId where
  isidentifier s :=
    match s.toList with
    | [] => false
    | c :: t => idStart c && t.all idCont
  nfkc s := String.join (s.toList.map nfkcChar)

def encNT (T : NT Int) : Json :=
  Json.mkObj [("typename", toJson T.typename), ("fields", encStrs T.fields), ("args", encStrs T.args),
    ("defaults", encInts T.defaults), ("fd", encItems T.fieldDefaults), ("doc", toJson T.doc),
    ("newdoc", toJson T.newDoc)]

def runNT (j : Json) : Except String Json := do
  let op ← getStr j "op"
  let typename ← getStr j "typename"
  let fn : FieldNames ← match j.getObjVal? "fstr" with
    | .ok v => pure (.str (← v.getStr?))
    | .error _ => pure (.list (← getStrs j "fields"))
  let rename ← getBool j "rename"
  let defaults : Option (List Int) ← match j.getObjVal? "defaults" with
    | .ok .null | .error _ => pure none
    | .ok _ => pure (some (← getInts j "defaults"))
  let T? : Py (NT Int) := namedtuple genU typename fn rename defaults
  if op == "create" then return encPy encNT T?
  match T? with
  | .error e => return encPy encNT (.error e)
  | .ok T =>
    let vals ← getInts j "vals"
    match op with
    | "call" => return encPy encInts (ntCall T vals (← getItems j "kw"))
    | "make" => return encPy encInts (ntMake T vals)
    | "replace" => return encPy encInts (ntReplace T vals (← getItems j "kw"))
    | "repr" => return okS (ntRepr rvInt T vals)
    | "asdict" => return okJ (encItems (ntAsdict T vals))
    | "getnewargs" => return okJ (encInts vals)
    | "getattr" =>
      match ntGetattr T vals (← getStr j "name") with
      | some v => return okI v
      | none => return encPy toJson (.error (.named "AttributeError" "~no attribute") : Py Int)
    | "roundtrip" => return encPy encInts (ntCall T [] (ntAsdict T vals))
    | _ => throw s!"unknown nt op {op}"

def run (fn : String) (j : Json) : Except String Json :=
  match fn with
  | "ctr" => runCtr j
  | "cm" => runCM j
  | "ud" => runUD j
  | "ul" => runUL j
  | "us" => runUS j
  | "nt" => runNT j
  | _ => throw s!"unknown fn coll.{fn}"

def handler : Handler := fun fn j => some (run fn j)

end PyLean.CoreLibs.Coll
