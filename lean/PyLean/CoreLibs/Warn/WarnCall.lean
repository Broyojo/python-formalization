import PyLean.CoreLibs.Warn.Model

/-!
`warnings.warn`, both twins, CPython 3.15.2. C, Python/_warnings.c: the clinic wrapper and
`warnings_warn_impl` (:1193-1211), `get_category` (:1119-1144), `do_warn` (:1147-1170),
`setup_context` (:1015-1116), `next_external_frame` (:998-1009), `is_internal_frame` (:983-995),
`is_filename_to_skip` (:958-980), `is_internal_filename` (:934-955), `get_frame_filename`
(:925-931). Python, Lib/_py_warnings.py: `warn` (:465-520), `_next_external_frame` (:454-461),
`_is_internal_frame` (:449-451), `_is_filename_to_skip` (:445-446), `_is_internal_filename`
(:441-442). Both end in their own `warn_explicit` (`Model.lean`).

Scope:
* The stack is a list of frames from the caller of `warn` outwards; the Python twin's `warn` has a
  frame of its own (`self`), which `sys._getframe(0)` returns. A frame is its code's
  `co_filename` (always a str), its line (a C `int`, `PyFrame_GetLineNumber`) and its globals.
* A globals dict is what `warn` reads from it: `__name__` (missing, a str, `None`, or another
  object) and `__warningregistry__` (missing, a dict, `None`, or another object). Both twins store
  a new dict when it is missing; the twins pass the same registry.
* `skip_file_prefixes` is a tuple (of strs, tuples of strs, or other objects) or another object.
* `category` is `None`, a class (id, `__name__`, the `%N` name C prints, whether it is a Warning
  subclass) or another object (`type(x).__name__` and the `%T` name). `message` is a str (or str
  subclass) or a Warning instance (its class and `str(message)`), with its `__class__` as Python
  reads it (`ClsV`); `category(message)` is a callback of the category that can raise.
-/

namespace PyLean.CoreLibs.Warn

open PyLean

structure Frame where
  filename : String
  lineno : Int
  globals : Nat

inductive NameV where
  | missing
  | str (s : String)
  | none
  | obj

inductive RegV where
  | missing
  | dict (r : Reg)
  | none
  | obj

structure Globals where
  name : NameV
  reg : RegV

inductive PElem where
  | str (s : String)
  | tup (ss : List String)
  | obj (tp : String)

inductive SkipA where
  | tuple (ps : List PElem)
  | other (tp : String)

inductive CatA where
  | none
  | cls (id : Nat) (name fq : String) (isWarn : Bool)
  | obj (tp fq : String)

inductive MsgA where
  | str (s : String) (dc : ClsV)
  | warn (cls : Nat) (text : String) (dc : ClsV)

structure WEnv where
  frames : List Frame
  self : Frame
  globals : Nat → Globals
  /-- the globals of the `<sys>` case, `sys.__dict__` (`interp->sysdict` in C) -/
  sysG : Nat
  userWarning : Nat
  /-- `category(message)` for a str message -/
  mkMsg : Nat → Py Unit
  /-- `linecache.getlines(filename, globals)` for the globals `g` (Python passes the frame's
  globals as `module_globals`) -/
  lines : Nat → Py Unit

/-- Where the walk ends: `warn`'s own frame (Python only), frame `i`, or past the outermost frame
(`<sys>`). -/
inductive Pos where
  | self
  | idx (i : Nat)
  | sys
  deriving DecidableEq

/-! ## Filenames -/

def isInfixL (p : List Char) : List Char → Bool
  | [] => p.isEmpty
  | c :: cs => p.isPrefixOf (c :: cs) || isInfixL p cs

/-- `'importlib' in filename and '_bootstrap' in filename`, :441-442 and _warnings.c:934-955
(`co_filename` is a str, so C's `PyUnicode_Check` holds). -/
def internalFn (f : String) : Bool :=
  isInfixL "importlib".toList f.toList && isInfixL "_bootstrap".toList f.toList

/-- C `is_filename_to_skip`, :958-980: every prefix is a str by then. -/
def cSkipFn (ps : List String) (f : String) : Bool := ps.any (fun p => p.toList.isPrefixOf f.toList)

/-- `filename.startswith(prefix)`. -/
def pyStartsWith (f : String) : PElem → Py Bool
  | .str s => .ok (s.toList.isPrefixOf f.toList)
  | .tup ss => .ok (ss.any (fun s => s.toList.isPrefixOf f.toList))
  | .obj tp => .error (.typeError s!"startswith first arg must be str or a tuple of str, not {tp}")

/-- `_is_filename_to_skip`, :445-446: `any(...)` stops at the first true. -/
def pySkipFn (ps : List PElem) (f : String) : Py Bool :=
  match ps with
  | [] => .ok false
  | p :: rest => do
    if ← pyStartsWith f p then return true
    pySkipFn rest f

/-! ## Walking the stack -/

/-- `next_external_frame` / `_next_external_frame` past frame `i`: the next outer frame whose
filename is neither internal nor skipped, `none` past the outermost. `rest` are the frames after
`i`, the first of them at index `j`. -/
def nextExt (skip : String → Py Bool) : List Frame → Nat → Py (Option Nat)
  | [], _ => .ok none
  | f :: fs, j => do
    if internalFn f.filename then nextExt skip fs (j + 1)
    else if ← skip f.filename then nextExt skip fs (j + 1)
    else .ok (some j)

def after (fr : List Frame) (i : Nat) : List Frame := fr.drop (i + 1)

/-- `while (--stack_level > 0 && f != NULL) f = <step>(f)`, `n` rounds. -/
def cLoop (step : Nat → Option Nat) : Nat → Option Nat → Option Nat
  | 0, f => f
  | _ + 1, none => none
  | n + 1, some i => cLoop step n (step i)

/-- `PyFrame_GetBack`: the next outer frame, `none` past the outermost. -/
def cBack (fr : List Frame) (i : Nat) : Option Nat := if i + 1 < fr.length then some (i + 1) else none

/-- `next_external_frame(f, skip_file_prefixes)`, :998-1009 (it cannot fail). -/
def cStep (fr : List Frame) (ps : List String) (i : Nat) : Option Nat :=
  match nextExt (fun f => .ok (cSkipFn ps f)) (after fr i) (i + 1) with
  | .ok r => r
  | .error _ => none

/-- `is_internal_frame(f)` for the caller's frame, :983-995 (`NULL` is not internal). -/
def internal0 : List Frame → Bool
  | f :: _ => internalFn f.filename
  | [] => false

/-- `setup_context`'s walk, :1043-1056: `none` is `NULL`. -/
def cWalk (fr : List Frame) (ps : List String) (s : Int) : Option Nat :=
  let f0 : Option Nat := if fr.isEmpty then none else some 0
  if s ≤ 0 || internal0 fr then cLoop (cBack fr) (s - 1).toNat f0
  else cLoop (cStep fr ps) (s - 1).toNat f0

/-- `for x in range(n): frame = _next_external_frame(frame, ...); if frame is None: raise
ValueError`, :494-497: `none` is the `ValueError`. -/
def pyLoop (fr : List Frame) (ps : List PElem) : Nat → Nat → Py (Option Nat)
  | 0, i => .ok (some i)
  | n + 1, i => do
    match ← nextExt (pySkipFn ps) (after fr i) (i + 1) with
    | none => .ok none
    | some j => pyLoop fr ps n j

/-- `sys._getframe(depth)` from inside `warn`: a C `int`; 0 or less is `warn`'s own frame;
`none` is the `ValueError` of a stack not deep enough. -/
def getframe (fr : List Frame) (d : Int) : Py (Option Pos) :=
  if d > intMax ∨ d < -intMax - 1 then .error (.overflowError "Python int too large to convert to C int")
  else if d ≤ 0 then .ok (some .self)
  else if (d - 1).toNat < fr.length then .ok (some (.idx (d - 1).toNat)) else .ok none

/-- `frame = sys._getframe(stacklevel)`, :490, its `ValueError` caught at :498 (`.sys`). -/
def pyPlain (fr : List Frame) (s : Int) : Py Pos :=
  (getframe fr s).map (fun o => o.getD .sys)

/-- The loop of :492-497 from `sys._getframe(1)`, its `ValueError` caught at :498. -/
def pyExt (fr : List Frame) (ps : List PElem) (s : Int) : Py Pos :=
  (pyLoop fr ps (s - 1).toNat 0).map (fun o => match o with
    | some i => .idx i
    | none => .sys)

/-- The walk of `warn`, :486-498: where it ends (`.sys` for the `ValueError`).
`stacklevel <= 1 or _is_internal_frame(sys._getframe(1))`; `sys._getframe(1)` raises
`ValueError` when the caller is the outermost frame. -/
def pyWalk (fr : List Frame) (ps : List PElem) (s : Int) : Py Pos :=
  if s ≤ 1 then pyPlain fr s
  else match fr with
    | [] => .ok .sys
    | f :: _ => if internalFn f.filename then pyPlain fr s else pyExt fr ps s

/-! ## The context -/

/-- What `warn_explicit` is called with. -/
structure WCtx where
  filename : String
  lineno : Int
  /-- whose registry is passed -/
  g : Nat
  module : ModArg
  reg : RegArg
  deriving DecidableEq

/-- The registry `setup_context` passes, :1078-1091: `PyDict_GetItemRef(globals,
"__warningregistry__")`, and a new dict stored there when it is missing. A dict subclass is a dict
(`.dict`), anything else is passed as it is. -/
def cRegOf : RegV → RegArg
  | .missing => .dict []
  | .dict r => .dict r
  | .none => .none
  | .obj => .obj

/-- The registry Python `warn` passes, :510: `globals.setdefault("__warningregistry__", {})`. -/
def pyRegOf (v : RegV) : RegArg :=
  match v with
  | .dict r => .dict r
  | .none => .none
  | .obj => .obj
  | .missing => .dict []

def frameAt (W : WEnv) : Pos → Nat × String × Int
  | .self => (W.self.globals, W.self.filename, W.self.lineno)
  | .idx i => match W.frames[i]? with
    | some f => (f.globals, f.filename, f.lineno)
    | none => (W.sysG, "<sys>", 0)
  | .sys => (W.sysG, "<sys>", 0)

/-- The up-front type check of `setup_context`, :1027-1041: every prefix must be a str. -/
def cCheckPrefixes : List PElem → Py (List String)
  | [] => .ok []
  | .str p :: rest => (cCheckPrefixes rest).map (p :: ·)
  | .tup _ :: _ => .error (.typeError "Found non-str 'tuple' in skip_file_prefixes.")
  | .obj tp :: _ => .error (.typeError s!"Found non-str '{tp}' in skip_file_prefixes.")

/-- `__name__` as C takes it, :1094-1107: `None` or a str, else `"<string>"`. -/
def cModule : NameV → ModArg
  | .str m => .some m
  | .none => .none
  | _ => .some "<string>"

/-- `__name__` as Python takes it, :506-509: anything present, else `"<string>"`. -/
def pyModule : NameV → ModArg
  | .str n => .some n
  | .none => .none
  | .obj => .obj
  | .missing => .some "<string>"

/-- `setup_context`, :1015-1116: prefixes checked up front, the walk, then the registry (created
when missing) and the module (`__name__` if `None` or a str, else `"<string>"`). -/
def cSetup (W : WEnv) (s : Int) (skip : Option (List PElem)) : Py WCtx := do
  let ps ← match skip with
    | none => pure []
    | some es => cCheckPrefixes es
  let pos : Pos := match cWalk W.frames ps s with
    | some i => .idx i
    | none => .sys
  let (g, fn, ln) := frameAt W pos
  let G := W.globals g
  return ⟨fn, ln, g, cModule G.name, cRegOf G.reg⟩

/-- `get_category`, :1119-1144. -/
def cGetCategory (W : WEnv) (m : MsgA) (c : CatA) : Py Nat :=
  match m with
  | .warn k _ _ => .ok k
  | .str _ _ =>
    match c with
    | .none => .ok W.userWarning
    | .obj _ fq => .error (.typeError s!"category must be a Warning subclass, not '{fq}'")
    | .cls k _ fq w => if w then .ok k else .error (.typeError s!"category must be a Warning subclass, not class '{fq}'")

def textOf : MsgA → String
  | .str s _ => s
  | .warn _ t _ => t

def clsOf : MsgA → ClsV
  | .str _ d => d
  | .warn _ _ d => d

def isInst : MsgA → Bool
  | .str _ _ => false
  | .warn _ _ _ => true

/-- The call `warn_explicit` gets: the message as it was passed, with the category the twin's `warn`
computed. -/
def callOf (W : WEnv) (m : MsgA) (cat : Nat) (x : WCtx) : Call :=
  ⟨textOf m, cat, x.filename, .int x.lineno, x.module,
   match m with | .warn _ _ _ => .ok () | .str _ _ => W.mkMsg cat, .none, W.lines x.g, isInst m, clsOf m⟩

/-- C `warn(message, category, stacklevel, source, *, skip_file_prefixes)`: the clinic
conversions (:1172-1190: `stacklevel` to `Py_ssize_t`, `skip_file_prefixes` a tuple), then
`warnings_warn_impl`, :1193-1211, and `do_warn`, :1147-1170. -/
def cWarnSetup (W : WEnv) (m : MsgA) (c : CatA) (s : Int) (skip : SkipA) : Py (Nat × WCtx) := do
  if s > ssizeMax ∨ s < -ssizeMax - 1 then .error (.overflowError "Python int too large to convert to C ssize_t")
  let ps ← match skip with
    | .tuple ps => pure ps
    | .other tp => .error (.typeError s!"warn() argument 'skip_file_prefixes' must be tuple, not {tp}")
  let cat ← cGetCategory W m c
  let (s, skip) := if ps.isEmpty then (s, none) else (if s < 2 then 2 else s, some ps)
  let x ← cSetup W s skip
  return (cat, x)

/-- The category checks of Python `warn`, :468-479 (`category` is not `None`, a class, a Warning
subclass). -/
def pyCheckCat (W : WEnv) (c : CatA) : Py Nat :=
  match c with
  | .none => .ok W.userWarning
  | .obj tp _ => .error (.typeError s!"category must be a Warning subclass, not '{tp}'")
  | .cls k n _ w => if w then .ok k else .error (.typeError s!"category must be a Warning subclass, not class '{n}'")

/-- Python `warn`'s category, :468-479: `if isinstance(message, Warning): category =
message.__class__`, then the checks. `isinstance` holds at once for a Warning instance; for a str
it reads `__class__` (a raising read whose class is under `AttributeError` gives false, another
propagates), and `category = message.__class__` reads it again. -/
def pyGetCategory (H : Hier) (W : WEnv) (m : MsgA) (c : CatA) : Py Nat :=
  match m with
  | .warn k _ dc =>
    match dc with
    | .own => .ok k
    | .cls k' n w => pyCheckCat W (.cls k' n n w)
    | .raises e => .error e
  | .str _ dc =>
    match dc with
    | .cls k _ true => .ok k
    | .raises e => if isA H e "AttributeError" then pyCheckCat W c else .error e
    | _ => pyCheckCat W c

/-- Python `warn`, :465-520, up to the `warn_explicit` call. -/
def pyWarnSetup (H : Hier) (W : WEnv) (m : MsgA) (c : CatA) (s : Int) (skip : SkipA) : Py (Nat × WCtx) := do
  let cat ← pyGetCategory H W m c
  let ps ← match skip with
    | .tuple ps => pure ps
    | .other _ => .error (.typeError "skip_file_prefixes must be a tuple of strs.")
  let s := if ps.isEmpty then s else max 2 s
  let pos ← pyWalk W.frames ps s
  let (g, fn, ln) := frameAt W pos
  let G := W.globals g
  return (cat, ⟨fn, ln, g, pyModule G.name, pyRegOf G.reg⟩)

/-- What a `warn` call leaves: its result, whose registry it used and what that registry holds
after (when it is a dict), and the once registry. -/
structure WRes where
  out : Py Bool
  reg : Option (Nat × Reg)
  once : Reg
  /-- the context `warn_explicit` got -/
  ctx : Option WCtx

def finish (x : Py (Nat × WCtx)) (W : WEnv) (m : MsgA) (we : Call → RegArg → Res) (once : Reg) : WRes :=
  match x with
  | .error e => ⟨.error e, none, once, none⟩
  | .ok (cat, ctx) =>
    let r := we (callOf W m cat ctx) ctx.reg
    ⟨r.out, r.reg.map (fun r' => (ctx.g, r')), r.once, some ctx⟩

/-- C `warnings.warn`: `do_warn` calls `warn_explicit` with no `module_globals` (:1163-1164). -/
def cWarn (W : WEnv) (E : Env) (K : WCfg) (fs : List Item) (ver : Int)
    (m : MsgA) (c : CatA) (s : Int) (skip : SkipA) : WRes :=
  finish (cWarnSetup W m c s skip) W m (fun call reg => cWarnExplicit E K fs ver call reg) (onceReg K.once)

/-- Python `warnings.warn`: `_wm.warn_explicit(..., globals, ...)`, :511-520. -/
def pyWarn (W : WEnv) (E : Env) (K : WCfg) (fs : List Item) (ver : Int)
    (m : MsgA) (c : CatA) (s : Int) (skip : SkipA) : WRes :=
  finish (pyWarnSetup E.hier W m c s skip) W m (fun call reg => pyWarnExplicit E K fs ver call reg) (onceReg K.once)

end PyLean.CoreLibs.Warn
