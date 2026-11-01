import PyLean.DiffCore
import PyLean.CoreLibs.Rand.System
import PyLean.CoreLibs.Rand.FloatInst

/-! Differential-testing handler for `corelibs` cases with `"fn": "rand.<name>"`.
The dispatcher in `CoreLibs/Diff.lean` strips the `rand.` prefix.

Every result is `{"ok": {"r": <value or exception>, "fp": <fingerprint>}}`, so the
generator state after the call is compared too, also after an exception. Floats
cross as their IEEE bits. -/

namespace PyLean.CoreLibs.Rand

open Lean PyLean PyLean.Diff PyLean.CoreLibs.Rand.FloatInst

/-- `PyMem_Malloc`: on the pod's 64-bit Linux an allocation beyond the 47-bit
address space fails. The difftest stays away from sizes between 2**34 and that. -/
def podMalloc (n : Nat) : Bool := n < 2 ^ 47

def G : Gen State Float := mtGen podMalloc

def bigFuel : Nat := 2000000

/-- No entropy is ever read by a difftest case. -/
def noEntropy : Entropy :=
  { urandom := none, now := .ok 0, pid := 0, monotonic := .ok 0 }

def mkState (seed : Int) (burn : Nat) : State :=
  match randomSeed genericNew (.exactInt seed) noEntropy with
  | .ok s => advance burn s
  | .error _ => genericNew

/-! ### JSON -/

def encF (x : Float) : Json := toJson x.toBits.toNat
def decF (j : Json) : Except String Float := do
  let n ← j.getNat?
  return Float.ofBits n.toUInt64

def getF (j : Json) (key : String) : Except String Float := do decF (← field j key)
def getArr (j : Json) (key : String) : Except String (List Json) := do
  return (← (← field j key).getArr?).toList

def getOptF (j : Json) (key : String) : Except String (Option Float) :=
  match j.getObjVal? key with
  | .ok .null | .error _ => .ok none
  | .ok v => some <$> decF v

def fingerprint (s : State) : Json :=
  let (w, _) := genrand s
  toJson [(s.index : Nat), (rd s.mt 0).toNat, (rd s.mt 311).toNat, (rd s.mt 623).toNat, w.toNat]

/-- `{"r": value-or-exception, "fp": fingerprint}`. -/
def enc {α : Type} (e : α → Json) (r : Py α) (s : State) : Except String Json :=
  .ok (Json.mkObj [("ok", Json.mkObj [("r", encPy e r), ("fp", fingerprint s)])])

def encRM {α : Type} (e : α → Json) (x : RM State α) (s : State) : Except String Json :=
  let (r, s') := x s
  enc e r s'

/-- `hex(n)`. -/
def hexStr (n : Int) : String :=
  (if n < 0 then "-" else "") ++ "0x" ++ String.ofList (Nat.toDigits 16 n.natAbs)

/-- JSON cannot carry ints past the 4300-digit limit of the Python reader. -/
def encInt (n : Int) : Json :=
  if n.natAbs < 10 ^ 4000 then toJson n else Json.mkObj [("x", toJson (hexStr n))]

def encIntList (l : List Int) : Json := toJson l

/-- An int as `encInt` writes it. -/
def decInt (j : Json) : Except String Int :=
  match j.getObjVal? "x" with
  | .ok v => do
    let s ← v.getStr?
    let cs := s.toList
    let (neg, cs) := match cs with
      | '-' :: rest => (true, rest)
      | _ => (false, cs)
    let n : Nat := (cs.drop 2).foldl (fun (acc : Nat) (c : Char) =>
      acc * 16 + (if c.isDigit then c.toNat - 48 else c.toNat - 87)) 0
    return if neg then -(n : Int) else n
  | .error _ => j.getInt?
def encNat (n : Nat) : Json := encInt n

/-- `{"i": n}`, `{"b": bool}` or `{"o": typename}`. -/
def getIntArgJ (j : Json) : Except String IntArg :=
  match j.getObjVal? "i", j.getObjVal? "b", j.getObjVal? "o" with
  | .ok v, _, _ => do return .int (← decInt v)
  | _, .ok v, _ => do return .bool (← v.getBool?)
  | _, _, .ok v => do return .other (← v.getStr?)
  | _, _, _ => .error "bad IntArg"

def getIntArg (j : Json) (key : String) : Except String IntArg := do getIntArgJ (← field j key)

def getOptIntArg (j : Json) (key : String) : Except String (Option IntArg) :=
  match j.getObjVal? key with
  | .ok .null | .error _ => .ok none
  | .ok v => some <$> getIntArgJ v

/-- `stop`: an explicit `None` is the same as leaving it out. -/
def getStopArg (j : Json) (key : String) : Except String (Option IntArg) := do
  match ← getOptIntArg j key with
  | some (.other "NoneType") => return none
  | x => return x

def getIntList (j : Json) (key : String) : Except String (List Int) := do
  (← getArr j key).mapM (·.getInt?)

def getElem' (j : Json) : Except String Elem :=
  match j.getStr? with
  | .ok ty => .ok (.other ty)
  | .error _ => do return .int (← j.getInt?)

def getElems (j : Json) (key : String) : Except String (List Elem) := do
  (← getArr j key).mapM getElem'

/-- A population of ints; `seqkind`: `"list"`, `"set"` (not a `Sequence`). -/
def getPop (j : Json) : Except String (SeqObj Int) := do
  let l ← getIntList j "pop"
  let kind ← getStr j "seqkind"
  return { listSeq l with isSequence := kind != "set" }

def getNumJ (j : Json) : Except String (Num Float) :=
  match j.getObjVal? "f" with
  | .ok v => do return .flt (← decF v)
  | .error _ => do return .int (← decInt (← field j "i"))

def getNums (j : Json) (key : String) : Except String (List (Num Float)) := do
  (← getArr j key).mapM getNumJ

def seedArg (j : Json) : Except String SeedArg := do
  let kind ← getStr j "kind"
  match kind with
  | "none" => return .none
  | "int" => return .int (← decInt (← field j "n"))
  | "intsub" => return .intSub (← decInt (← field j "n"))
  | "float" => return .float (← getInt j "h")
  | "str" =>
    let cps ← getIntList j "b"
    return .str (cps.map Int.toNat) (← getInt j "h")
  | "bytes" =>
    let b ← getIntList j "b"
    return .bytes (b.map Int.toNat) (← getInt j "h")
  | "bytearray" =>
    let b ← getIntList j "b"
    return .bytearray (b.map Int.toNat)
  | "other" => return .other
  | k => .error s!"bad seed kind {k}"

def cArg (j : Json) : Except String CArg := do
  let kind ← getStr j "kind"
  match kind with
  | "int" => return .exactInt (← decInt (← field j "n"))
  | "intsub" => return .intSubclass (← decInt (← field j "n"))
  | "hash" => return .hashable (← getInt j "h")
  | "unhashable" => return .unhashable (← getStr j "ty")
  | k => .error s!"bad c arg {k}"

def getInternal (j : Json) : Except String InternalArg := do
  let kind ← getStr j "ikind"
  match kind with
  | "tuple" => return .tuple (← getElems j "xs")
  | "list" => return .list (← getElems j "xs")
  | "other" => return .notIterable (← getStr j "ity")
  | k => .error s!"bad internal {k}"

def getVersionV (j : Json) : Except String VersionV := do
  let text ← getStr j "vtext"
  let value ← getOptInt j "vval"
  return { value, text }

/-- Which `_randbelow`: `"sub": true` is a subclass that overrides `random()` only. -/
def getBelow (j : Json) : Nat → RM State Nat :=
  match j.getObjVal? "sub" with
  | .ok (.bool true) => fun n => randbelowWithout G bigFuel n
  | _ => randbelowWith G bigFuel

def encObj (o : Obj Float) : Json :=
  Json.mkObj [("gauss", match o.gaussNext with
    | some x => encF x
    | none => Json.null)]

/-! ### The deterministic `os.urandom` of the difftest -/

/-- The stub both sides use for `os.urandom`: `n` bytes of the Mersenne Twister
stream. It stands in for the operating system. -/
def stubRaw : Nat → RM State (List Nat) := fun n s =>
  let rec go : Nat → State → List Nat × State
    | 0, s => ([], s)
    | k + 1, s =>
      let (w, s) := genrand s
      let (rest, s) := go k s
      (((w >>> 24).toNat) :: rest, s)
  let (b, s) := go n s
  (.ok b, s)

def S : Gen State Float := sysGen stubRaw

/-! ### Dispatch -/

def getWeights (j : Json) : Except String (Option (WeightsArg Float)) := do
  let v ← field j "weights"
  if v.isNull then pure none
  else
    match v.getObjVal? "wint", v.getObjVal? "wother" with
    | .ok a, _ => pure (some (.intArg (← getIntArgJ a)))
    | _, .ok a => pure (some (.notIterable (← a.getStr?)))
    | _, _ => pure (some (.seq (← (← v.getArr?).toList.mapM getNumJ)))

def getCum (j : Json) : Except String (Option (List (Num Float))) := do
  let v ← field j "cum"
  if v.isNull then pure none
  else pure (some (← (← v.getArr?).toList.mapM getNumJ))

def getStrListOpt (j : Json) (key : String) : Except String (Option (List String)) :=
  match j.getObjVal? key with
  | .ok .null | .error _ => pure none
  | .ok v => do pure (some (← (← v.getArr?).toList.mapM (·.getStr?)))

def stateSum (l : List Int) : Int :=
  (l.zipIdx.foldl (fun acc p => (acc + p.1 * ((p.2 : Int) + 1)) % (2 ^ 61 - 1)) 0)

def timePid (j : Json) : Except String Json := do
  let now ← getInt j "now"
  let mono ← getInt j "mono"
  let pid ← getInt j "pid"
  let (k0, k1) := timeWords now
  let (k3, k4) := timeWords mono
  let ent : Entropy := { urandom := none, now := .ok now, pid := pid.toNat.toUInt32, monotonic := .ok mono }
  let s ← match randomSeed genericNew .none ent with
    | .ok s => pure s
    | .error _ => throw "seed failed"
  enc (fun (l : List Nat) => toJson l)
    (.ok [k0.toNat, k1.toNat, pid.toNat.toUInt32.toNat, k3.toNat, k4.toNat]) s

def run (fn : String) (j : Json) : Except String Json := do
  let seed := ((field j "seed") >>= decInt).toOption.getD 0
  let burn := (getNat j "burn").toOption.getD 0
  let s := mkState seed burn
  let below := getBelow j
  match fn with
  | "words" =>
    let n ← getNat j "n"
    enc (fun (l : List Nat) => toJson l) (.ok ((stream n s).map (·.toNat))) (advance n s)
  | "random" =>
    let n ← getNat j "n"
    let rec go : Nat → State → List Nat → List Nat × State
      | 0, s, acc => (acc.reverse, s)
      | k + 1, s, acc =>
        let (x, s) := G.random s
        go k s (x.toBits.toNat :: acc)
    let (l, s') := go n s []
    let (l2, _) := (List.range n).foldl (fun (acc : List Nat × State) _ =>
      let (m, st) := randomNum acc.2
      (acc.1 ++ [m], st)) (([] : List Nat), s)
    enc (fun (l : List Nat × List Nat) => Json.mkObj [("bits", toJson l.1), ("nums", toJson l.2)])
      (.ok (l, l2)) s'
  | "getrandbits" =>
    encRM encNat (G.getrandbits (← getIntArg j "k")) s
  | "cseed" =>
    let a ← cArg j
    match cSeedMethod s a noEntropy with
    | .ok s' => enc (fun (_ : Unit) => Json.null) (.ok ()) s'
    | .error e => enc (fun (_ : Unit) => Json.null) (.error e) s
  | "cinit" =>
    let a ← cArg j
    match cInit a noEntropy with
    | .ok s' => enc (fun (_ : Unit) => Json.null) (.ok ()) s'
    | .error e => enc (fun (_ : Unit) => Json.null) (.error e) s
  | "getstate" =>
    enc encInt (.ok (stateSum (cGetstate s))) s
  | "csetstate" =>
    let st : CStateArg ← match (← getStr j "ikind") with
      | "tuple" => pure (.tuple (← getElems j "xs"))
      | _ => pure .notTuple
    match cSetstate st with
    | .ok s' => enc (fun (_ : Unit) => Json.null) (.ok ()) s'
    | .error e => enc (fun (_ : Unit) => Json.null) (.error e) s
  | "pysetstate" =>
    let gn ← getOptF j "gauss0"
    let o : Obj Float := { core := s, gaussNext := gn }
    let arg : SetArg Float ← match (← getStr j "skind") with
      | "notsub" => pure (.notSubscriptable (← getStr j "sty"))
      | "emptytuple" => pure (.empty false)
      | "emptylist" => pure (.empty true)
      | _ =>
        pure (.seq (← getNat j "len") (← getVersionV j) (← getInternal j) (← getOptF j "gauss"))
    let (r, o') := pySetstate arg o
    enc (fun (_ : Unit) => Json.null) (match r with
      | .ok () => .ok ()
      | .error e => .error e) o'.core
      |>.map fun out => Json.mkObj [("ok", Json.mkObj [("v", out), ("o", encObj o')])]
  | "pyseed" =>
    let a ← seedArg j
    let v ← getInt j "version"
    let o : Obj Float := { core := s, gaussNext := some 1.5 }
    let (r, o') := pySeed noEntropy a v o
    enc (fun (_ : Unit) => Json.null) r o'.core
      |>.map fun out => Json.mkObj [("ok", Json.mkObj [("v", out), ("o", encObj o')])]
  | "pickle" =>
    let gn ← getOptF j "gauss0"
    let o : Obj Float := { core := s, gaussNext := gn }
    match pyUnpickle { noEntropy with urandom := some #[1, 2, 3] } (pyReduce o) with
    | .ok o' =>
      enc (fun (_ : Unit) => Json.null) (.ok ()) o'.core
        |>.map fun out => Json.mkObj [("ok", Json.mkObj [("v", out), ("o", encObj o')])]
    | .error e => enc (fun (_ : Unit) => Json.null) (.error e) s
  | "new" =>
    let n ← getNat j "n"
    let st := advance (← getNat j "skip") genericNew
    enc (fun (l : List Nat) => toJson l) (.ok ((stream n st).map (·.toNat))) (advance n st)
  | "time_pid" => timePid j
  | "randbelow_with" =>
    encRM encNat (randbelowWith G bigFuel (← getNat j "n")) s
  | "randbelow_without" =>
    encRM encNat (randbelowWithout G bigFuel (← getNat j "n")) s
  | "randbytes" =>
    encRM (fun (l : List Nat) => toJson l) (randbytes G (← getIntArg j "n")) s
  | "randrange" =>
    encRM encInt (randrange below (← getIntArg j "start") (← getStopArg j "stop") (← getOptIntArg j "step")) s
  | "randint" =>
    encRM encInt (randint below (← getIntArg j "a") (← getIntArg j "b")) s
  | "choice" =>
    encRM encInt (choice below (listSeq (← getIntList j "pop"))) s
  | "choice_obj" =>
    -- A dict is not a sequence, but `choice` only needs `len` and `[]`.
    let keys ← getIntList j "keys"
    let vals ← getIntList j "vals"
    let seq : SeqObj Int :=
      { len := .ok keys.length
        getItem := fun i =>
          match (keys.zip vals).lookup (i : Int) with
          | some v => .ok v
          | none => .error (.keyError (toString i))
        toList := fun _ => keys }
    encRM encInt (choice below seq) s
  | "shuffle" =>
    let imm : Option String := match j.getObjVal? "imm" with
      | .ok v => v.getStr?.toOption
      | .error _ => none
    encRM encIntList (shuffle below (← getIntList j "x") imm) s
  | "sample" =>
    let pop ← getPop j
    let counts : Option CountsArg ← match j.getObjVal? "counts" with
      | .ok .null | .error _ => pure none
      | .ok v =>
        match v.getStr? with
        | .ok ty => pure (some (.notIterable ty))
        | .error _ => do
          let xs ← (← v.getArr?).toList.mapM fun (c : Json) =>
            (if c.isNull then pure none else some <$> c.getInt? : Except String CountV)
          pure (some (.seq xs))
    encRM encIntList (sample below bigFuel pop (← getInt j "k") counts) s
  | "sample_range" =>
    let n ← getNat j "n"
    encRM encIntList (sample below bigFuel
      ({ len := (rangeSeq n).len
         getItem := fun i => .ok (i : Int)
         toList := fun _ => (List.range n).map (fun (i : Nat) => (i : Int)) } :
        SeqObj Int) (← getInt j "k")) s
  | "setsize" =>
    enc encNat (.ok (setsize (← getNat j "k"))) s
  | "choices" =>
    let pop ← getPop j
    encRM encIntList (choices G pop (← getWeights j) (← getCum j) (← getInt j "k")) s
  | "uniform" => encRM encF (uniform G (← getF j "a") (← getF j "b")) s
  | "triangular" =>
    encRM encF (triangular G (← getF j "a") (← getF j "b") (← getOptF j "c")) s
  | "normalvariate" => encRM encF (normalvariate G bigFuel (← getF j "a") (← getF j "b")) s
  | "gauss" =>
    let gn ← getOptF j "gauss0"
    encRM (fun (p : Float × Option Float) => Json.mkObj
        [("v", encF p.1), ("next", match p.2 with
          | some x => encF x
          | none => Json.null)])
      (gauss G (← getF j "a") (← getF j "b") gn) s
  | "lognormvariate" => encRM encF (lognormvariate G bigFuel (← getF j "a") (← getF j "b")) s
  | "expovariate" => encRM encF (expovariate G (← getF j "a")) s
  | "vonmisesvariate" => encRM encF (vonmisesvariate G bigFuel (← getF j "a") (← getF j "b")) s
  | "gammavariate" => encRM encF (gammavariate G bigFuel (← getF j "a") (← getF j "b")) s
  | "betavariate" => encRM encF (betavariate G bigFuel (← getF j "a") (← getF j "b")) s
  | "paretovariate" => encRM encF (paretovariate G (← getF j "a")) s
  | "weibullvariate" => encRM encF (weibullvariate G (← getF j "a") (← getF j "b")) s
  | "binomialvariate" =>
    encRM encInt (binomialvariate G bigFuel 4 (← getInt j "n") (← getF j "p")) s
  | "sys_random" =>
    encRM encF (sysRandom stubRaw) s
  | "sys_getrandbits" =>
    encRM encNat (sysGetrandbits stubRaw (← getIntArg j "k")) s
  | "sys_randbytes" =>
    encRM (fun (l : List Nat) => toJson l) (sysRandbytes stubRaw (← getIntArg j "n")) s
  | "sys_randrange" =>
    encRM encInt (randrange (randbelowWith S bigFuel) (← getIntArg j "start") (← getStopArg j "stop") none) s
  | "sys_seed" =>
    encRM (fun (_ : Unit) => Json.null) (sysSeed ()) s
  | "sys_state" =>
    encRM (fun (_ : Unit) => Json.null) (sysNotImplemented ()) s
  | "init_subclass" =>
    let cs ← getArr j "classes"
    -- classes[i]: {"own": [has _randbelow in body, getrandbits, random], "mro": [indices]}
    let rec build : List Json → List ClsDict → Except String (List ClsDict × List (Option String))
      | [], done => .ok (done, [])
      | c :: rest, done => do
        let own ← getStr c "rb" |>.toOption |> (fun o => pure o : Option String → Except String (Option String))
        let g ← getBool c "gb"
        let r ← getBool c "rnd"
        let isRandom ← getBool c "random"
        let mro ← (← getArr c "mro").mapM (·.getNat?)
        let base : ClsDict := { randbelow := own, hasGetrandbits := g, hasRandom := r }
        let chain := mro.map (fun i => if i = done.length then base else done.getD i default)
        -- The tail of every MRO is `Random`, then `_random.Random` and `object`.
        let rootFn : ClsDict := { randbelow := some "_randbelow_with_getrandbits", hasGetrandbits := false, hasRandom := false }
        -- `__init_subclass__` only runs for subclasses of `Random`.
        -- Otherwise the attribute is plain inheritance along the MRO.
        let res := if isRandom then initSubclass (chain ++ [rootFn])
                   else chain.findSome? (·.randbelow)
        let (out, tail) ← build rest (done ++ [{ base with randbelow := res }])
        return (out, res :: tail)
    let (_, res) ← build cs []
    enc (fun (l : List (Option String)) => toJson l) (.ok res) s
  | "main" =>
    let getInput (c : Json) : Except String (CliInput Float) := do
      let asInt ← getOptInt c "asint"
      let asFloat ← getOptF c "asfloat"
      let words ← (← getArr c "words").mapM (·.getStr?)
      return { asInt, asFloat, words }
    let args : CliArgs Float :=
      { choice := ← getStrListOpt j "choice"
        integer := ← getOptInt j "integer"
        float := ← getOptF j "float"
        test := ← getOptInt j "test"
        input := ← (← getArr j "input").mapM getInput
        inputStrs := ← (← getArr j "inputstrs").mapM (·.getStr?) }
    encRM (fun (o : CliOut Float) => match o with
        | .str x => Json.mkObj [("s", toJson x)]
        | .int n => Json.mkObj [("i", toJson n)]
        | .flt x => Json.mkObj [("f", encF x)])
      (cliMain below G args "HELP") s
  | _ => throw s!"unknown fn rand.{fn}"

def handler : Handler := fun fn j => some (run fn j)

end PyLean.CoreLibs.Rand
