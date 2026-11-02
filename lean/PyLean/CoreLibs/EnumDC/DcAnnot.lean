import PyLean.CoreLibs.EnumDC.DcProps

/-!
Three pieces of `Lib/dataclasses.py` that are new in 3.15: `_get_type_from_annotation`, which replaced `_is_type`,
`_AutoDocstring.__get__`, which builds the class docstring on demand, and the `frozendict` branch of `_asdict_inner` and
`_astuple_inner`. `getattr`, `inspect.signature` and `setattr` are parameters; `\w` and `\s` of the regular expression are
modelled on ASCII.
-/

namespace PyLean.CoreLibs.EnumDC

open PyLean

def isWordChar (c : Char) : Bool := c.isAlphanum || c == '_'
def isSpaceC (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0b' || c == '\x0c'

/-- The next `\w+`, and what follows it. -/
def wordAt (s : List Char) : Option (String × List Char) :=
  match s.takeWhile isWordChar with
  | [] => none
  | w => some (String.ofList w, s.dropWhile isWordChar)

/-- `(?:\s*\.\s*\w+)*`, which gives back what it took for a dot with no word after it. `n` is the fuel, the length of `s`. -/
def dottedRest : Nat → List Char → List String
  | 0, _ => []
  | n + 1, s =>
    match s.dropWhile isSpaceC with
    | '.' :: r =>
      match wordAt (r.dropWhile isSpaceC) with
      | some (w, rest) => w :: dottedRest n rest
      | none => []
    | _ => []

/-- `re.compile(r'^\s*(\w+(?:\s*\.\s*\w+)*)').prefixmatch(annotation)`, Lib/dataclasses.py:797-801, with the names that
`match[1].split(".")` and `path_item.strip()` get from the group, Lib/dataclasses.py:805-809. -/
def annotationPath (s : List Char) : Option (List String) :=
  match wordAt (s.dropWhile isSpaceC) with
  | none => none
  | some (w, rest) => some (w :: dottedRest rest.length rest)

/-- The loop of `_get_type_from_annotation`, Lib/dataclasses.py:807-815: `get` is `getattr(root, name, None)` with `none` for
`None`, and `isExc` says that an exception is an `Exception`, which is ignored. -/
def annotationWalk {O : Type} (get : O → String → Py (Option O)) (isExc : PyExc → Bool) : O → List String → Py (Option O)
  | root, [] => .ok (some root)
  | root, p :: rest =>
    match get root p with
    | .error e => if isExc e then .ok none else .error e
    | .ok none => .ok none
    | .ok (some o) => annotationWalk get isExc o rest

/-- `_get_type_from_annotation(annotation, cls)`, Lib/dataclasses.py:759-817: `root` is `sys.modules.get(cls.__module__)`. -/
def typeFromAnnotation {O : Type} (get : O → String → Py (Option O)) (isExc : PyExc → Bool) (root : O) (s : List Char) :
    Py (Option O) :=
  match annotationPath s with
  | none => .ok none
  | some path => annotationWalk get isExc root path

/-- `s.replace(' -> None', '')`. -/
def dropArrowNone : List Char → List Char
  | ' ' :: '-' :: '>' :: ' ' :: 'N' :: 'o' :: 'n' :: 'e' :: r => dropArrowNone r
  | c :: r => c :: dropArrowNone r
  | [] => []

/-- `_AutoDocstring.__get__`, Lib/dataclasses.py:983-997: `sig` is `str(inspect.signature(cls, ...))`, `name` is `cls.__name__`
and `set` what `setattr(cls, '__doc__', doc)` raises. The result is the text that is stored on the class, so the
descriptor is gone after the first read. -/
def autoDocGet (name : String) (sig : Py String) (set : Option PyExc) : Py String :=
  let doc : Py String :=
    match sig with
    | .ok s => .ok (name ++ String.ofList (dropArrowNone s.toList))
    | .error (.typeError _) | .error (.valueError _) => .ok name
    | .error e => .error e
  match doc with
  | .error e => .error e
  | .ok d =>
    match set with
    | some e => .error e
    | none => .ok d

/-- `_get_type_from_annotation`: an annotation that does not start with a dotted name gives nothing; the path stops at the
first character that is not part of one, so a subscript plays no part; each name is read from the one before; `None`
ends the walk; an `Exception` from the read gives nothing, and any other exception goes out. -/
def AnnotationWalks : Prop :=
  ∀ (O : Type) (get : O → String → Py (Option O)) (isExc : PyExc → Bool) (root o : O) (p : String) (rest : List String)
    (e : PyExc),
    typeFromAnnotation get isExc root [] = .ok none ∧
    typeFromAnnotation get isExc root ('[' :: 'a' :: []) = .ok none ∧
    annotationPath " typing . ClassVar [int]".toList = some ["typing", "ClassVar"] ∧
    annotationPath "ClassVar[int]".toList = some ["ClassVar"] ∧
    annotationPath "a.".toList = some ["a"] ∧
    annotationPath "a.b.c".toList = some ["a", "b", "c"] ∧
    annotationWalk get isExc root [] = .ok (some root) ∧
    (get root p = .ok none → annotationWalk get isExc root (p :: rest) = .ok none) ∧
    (get root p = .ok (some o) → annotationWalk get isExc root (p :: rest) = annotationWalk get isExc o rest) ∧
    (get root p = .error e → isExc e = true → annotationWalk get isExc root (p :: rest) = .ok none) ∧
    (get root p = .error e → isExc e = false → annotationWalk get isExc root (p :: rest) = .error e)

theorem annotationWalks_proven : AnnotationWalks := by
  intro O get isExc root o p rest e
  refine ⟨rfl, rfl, by decide, by decide, by decide, by decide, rfl, ?_, ?_, ?_, ?_⟩
  · intro h; simp [annotationWalk, h]
  · intro h; simp [annotationWalk, h]
  · intro h1 h2; simp [annotationWalk, h1, h2]
  · intro h1 h2; simp [annotationWalk, h1, h2]

/-- `_AutoDocstring.__get__`: the name of the class and its signature without ` -> None`; a signature that cannot be had,
`TypeError` or `ValueError`, leaves the name alone, and any other exception goes out; so does one from `setattr`. -/
def AutoDocExact : Prop :=
  ∀ (name s m : String) (e : PyExc),
    autoDocGet name (.ok s) none = .ok (name ++ String.ofList (dropArrowNone s.toList)) ∧
    dropArrowNone "(x: int) -> None".toList = "(x: int)".toList ∧
    dropArrowNone "(x: int)".toList = "(x: int)".toList ∧
    autoDocGet name (.error (.typeError m)) none = .ok name ∧
    autoDocGet name (.error (.valueError m)) none = .ok name ∧
    autoDocGet name (.error (.named "KeyError" m)) none = .error (.named "KeyError" m) ∧
    autoDocGet name (.ok s) (some e) = .error e

theorem autoDocExact_proven : AutoDocExact := by
  intro name s m e
  exact ⟨rfl, by decide, by decide, rfl, rfl, rfl, rfl⟩

/-- A `frozendict` in a field: `_asdict_inner` and `_astuple_inner` rebuild it from the converted keys and values, in order,
as a `frozendict`, an unhashable converted key is the `TypeError` of building it, and a failure below it comes out. -/
def AsdictFrozendict : Prop :=
  ∀ (fa : DictFact) (ft : TupFact) (k v k' v' : List DV) (e : PyExc),
    (asdictL fa k = .ok k' → asdictL fa v = .ok v' → asdictV fa (.frozenDict k v) = wrapDict .frozenDict (dvPairs k' v')) ∧
    (astupleL ft k = .ok k' → astupleL ft v = .ok v' → astupleV ft (.frozenDict k v) = wrapDict .frozenDict (dvPairs k' v')) ∧
    (asdictL fa k = .error e → asdictV fa (.frozenDict k v) = .error e) ∧
    (asdictL fa k = .ok k' → asdictL fa v = .error e → asdictV fa (.frozenDict k v) = .error e)

theorem asdictFrozendict_proven : AsdictFrozendict := by
  intro fa ft k v k' v' e
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h1 h2
    simp [asdictV, h1, h2]
  · intro h1 h2
    simp [astupleV, h1, h2]
  · intro h
    simp [asdictV, h]
  · intro h1 h2
    simp [asdictV, h1, h2]

end PyLean.CoreLibs.EnumDC
