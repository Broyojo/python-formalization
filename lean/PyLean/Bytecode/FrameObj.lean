import PyLean.Bytecode.Ceval

/-!
The `f_lineno` setter of `Objects/frameobject.c`, CPython 3.14.7: the stack-kind
analysis `mark_stacks` (lines 1161-1519), `compatible_stack`, the line table search
and `frame_lineno_set_impl` (lines 1639-1835). All line numbers are in that file.
A stack is an `int64_t` with three bits per entry; the model keeps it as `Int` and
applies C's narrowing where the source narrows.
-/

namespace PyLean.Bytecode.FrameObj

open PyLean.Bytecode

/-- `enum kind`, lines 1167-1173. -/
def Iterator : Nat := 1
def Except : Nat := 2
def Object : Nat := 3
def Null : Nat := 4
def Lasti : Nat := 5

def UNINITIALIZED : Int := -2
def OVERFLOWED : Int := -1
def EMPTY_STACK : Int := 0
/-- `WILL_OVERFLOW`, line 1195: `1ULL << ((21 - 1) * 3)`. -/
def WILL_OVERFLOW : Nat := 2 ^ 60

/-- `compatible_kind`, lines 1175-1187. -/
def compatibleKind (from_ to : Nat) : Bool :=
  if to == 0 then false
  else if to == Object then from_ != Null
  else if to == Null then true
  else from_ == to

/-- `(uint64_t)stack`. -/
def asU64 (s : Int) : Nat := (s % (2 : Int) ^ 64).toNat

/-- `push_value`, lines 1199-1208. A negative stack is huge as a `uint64_t`. -/
def pushValue (stack : Int) (kind : Nat) : Int :=
  if WILL_OVERFLOW ≤ asU64 stack then OVERFLOWED else stack * 8 + kind

/-- `pop_value`, lines 1210-1214: an arithmetic shift. -/
def popValue (stack : Int) : Int := Int.fdiv stack 8

/-- `top_of_stack`, lines 1218-1222. -/
def topOfStack (stack : Int) : Nat := (Int.fmod stack 8).toNat

/-- `peek`, lines 1224-1229. -/
def peek (stack : Int) (n : Nat) : Nat := (Int.fmod (Int.fdiv stack ((2 : Int) ^ (3 * (n - 1)))) 8).toNat

/-- `stack_swap`, lines 1231-1241. The result type of the C function is `Kind`, an
enum with unsigned underlying type on the compilers CPython supports, so the
`int64_t` it computes is narrowed to 32 bits on the way out. -/
def stackSwap (stack : Int) (n : Nat) : Int :=
  let toSwap := peek stack n
  let top := topOfStack stack
  let shift := 3 * (n - 1)
  let w : Int := (2 : Int) ^ shift
  -- `(stack & ~(MASK << shift)) | (top << shift)`
  let replacedLow := stack - (peek stack n : Int) * w + (top : Int) * w
  -- `(replaced_low & ~MASK) | to_swap`
  let replacedTop := replacedLow - (Int.fmod replacedLow 8) + toSwap
  Int.fmod replacedTop ((2 : Int) ^ 32)

/-- The same operation in 64 bits, as the callers intend. -/
def stackSwap64 (stack : Int) (n : Nat) : Int :=
  let toSwap := peek stack n
  let top := topOfStack stack
  let shift := 3 * (n - 1)
  let w : Int := (2 : Int) ^ shift
  let replacedLow := stack - (peek stack n : Int) * w + (top : Int) * w
  replacedLow - (Int.fmod replacedLow 8) + toSwap

/-- `pop_to_level`, lines 1243-1254, fuelled by the 21 entries of a stack. -/
def popToLevel (stack : Int) (level : Nat) : Int :=
  if level == 0 then EMPTY_STACK
  else
    let levelMax : Int := 7 * (2 : Int) ^ (3 * (level - 1))
    let rec go : Nat → Int → Int
      | 0, s => s
      | k + 1, s => if s > levelMax then go k (popValue s) else s
    go 64 stack

/-- A `co_code` unit, already de-specialized. -/
structure Unit' where
  op : Op
  arg : Nat
  deriving Inhabited

/-- `PyCompile_OpcodeStackEffect`: `pushed - popped`, `Python/flowgraph.c`. -/
def stackEffect (o : Op) (a : Nat) : Int := (numPushed o a : Int) - numPopped o a

/-- `delta` applied by the `default:` case, lines 1471-1484. -/
def applyDelta (s : Int) (delta : Int) : Int :=
  if delta < 0 then (List.range delta.natAbs).foldl (fun st _ => popValue st) s
  else (List.range delta.toNat).foldl (fun st _ => pushValue st Object) s

abbrev Stacks := Array Int

def setS (a : Stacks) (i : Nat) (v : Int) : Stacks := a.setIfInBounds i v

/-- The `switch (opcode)` of `mark_stacks`, lines 1348-1485: the new `stacks` and
whether `todo` was set. `i` is the instruction, `nextI` the one after it. -/
def markOne (o : Op) (oparg i nextI : Nat) (s : Int) (st : Stacks) : Stacks × Bool :=
  let cont (ns : Int) := (setS st nextI ns, false)
  match o with
  | .POP_JUMP_IF_FALSE | .POP_JUMP_IF_TRUE | .POP_JUMP_IF_NONE | .POP_JUMP_IF_NOT_NONE =>
    let j := nextI + oparg
    let ns := popValue s
    (setS (setS st j ns) nextI ns, false)
  | .SEND =>
    let j := oparg + i + 1 + 1
    (setS (setS st j s) nextI s, false)
  | .JUMP_FORWARD => (setS st (oparg + i + 1) s, false)
  | .JUMP_BACKWARD | .JUMP_BACKWARD_NO_INTERRUPT =>
    let j := nextI - oparg
    (setS st j s, st.getD j UNINITIALIZED == UNINITIALIZED && j < i)
  | .GET_ITER => cont (pushValue (pushValue (popValue s) Iterator) Iterator)
  | .GET_AITER => cont (pushValue (popValue s) Iterator)
  | .FOR_ITER =>
    let target := pushValue s Object
    (setS (setS st nextI target) (oparg + 1 + 1 + i) target, false)
  | .END_ASYNC_FOR => cont (popValue (popValue s))
  | .PUSH_EXC_INFO => cont (pushValue s Except)
  | .POP_EXCEPT => cont (popValue s)
  | .RETURN_VALUE | .RAISE_VARARGS | .RERAISE => (st, false)
  | .PUSH_NULL => cont (pushValue s Null)
  | .LOAD_GLOBAL =>
    let ns := pushValue s Object
    cont (if oparg &&& 1 != 0 then pushValue ns Null else ns)
  | .LOAD_ATTR =>
    if oparg &&& 1 != 0 then cont (pushValue (pushValue (popValue s) Object) Null) else cont s
  | .SWAP => cont (stackSwap s oparg)
  | .COPY => cont (pushValue s (peek s oparg))
  | o => cont (applyDelta s (stackEffect o oparg))

/-- The scan of the instructions, lines 1329-1487. `EXTENDED_ARG` copies the stack
to each prefix, line 1340. -/
def scanCode (code : Array Unit') (len : Nat) : Nat → Nat → Stacks → Bool → Stacks × Bool
  | 0, _, st, todo => (st, todo)
  | fuel + 1, i, st, todo =>
    if i < len then
      let s := st.getD i UNINITIALIZED
      let rec ext : Nat → Nat → Nat → Stacks → Nat × Nat × Stacks
        | 0, j, a, st => (j, a, st)
        | k + 1, j, a, st =>
          match code[j]? with
          | some u =>
            if u.op == .EXTENDED_ARG then
              ext k (j + 1) ((a <<< 8) ||| u.arg) (setS st (j + 1) s)
            else (j, a, st)
          | none => (j, a, st)
      let (j, a, st) := ext 4 i 0 st
      let u := code.getD j default
      let oparg := (a <<< 8) ||| u.arg
      let nextI := j + u.op.caches + 1
      if s == UNINITIALIZED then scanCode code len fuel nextI st todo
      else
        let (st, t) := markOne u.op oparg j nextI s st
        scanCode code len fuel nextI st (todo || t)
    else (st, todo)

/-- The scan of the exception table, lines 1489-1515. -/
def scanTable (t : Array Nat) : Nat → Nat → Stacks → Bool → Stacks × Bool
  | 0, _, st, todo => (st, todo)
  | fuel + 1, p, st, todo =>
    if p < t.size then
      let (startOffset, p) := parseVarint t p
      let (_, p) := parseVarint t p
      let (handler, p) := parseVarint t p
      let (dl, p) := parseVarint t p
      let level := dl >>> 1
      let lasti := dl &&& 1 != 0
      let s0 := st.getD startOffset UNINITIALIZED
      if s0 != UNINITIALIZED && st.getD handler UNINITIALIZED == UNINITIALIZED then
        let target := popToLevel s0 level
        let target := if lasti then pushValue target Lasti else target
        let target := pushValue target Except
        scanTable t fuel p (setS st handler target) true
      else scanTable t fuel p st todo
    else (st, todo)

/-- `mark_stacks`, lines 1307-1519. -/
def markStacks (code : Array Unit') (table : Array Nat) : Stacks :=
  let len := code.size
  let init : Stacks := (Array.replicate (len + 1) UNINITIALIZED).setIfInBounds 0 EMPTY_STACK
  let rec go : Nat → Stacks → Stacks
    | 0, st => st
    | n + 1, st =>
      let (st, t1) := scanCode code len (len + 1) 0 st false
      let (st, t2) := scanTable table table.size 0 st t1
      if t2 then go n st else st
  go (len + 2) init

/-- `compatible_stack`, lines 1521-1540. -/
def compatibleStack (fromS toS : Int) : Bool :=
  if fromS < 0 || toS < 0 then false
  else
    let rec down : Nat → Int → Int
      | 0, f => f
      | k + 1, f => if f > toS then down k (popValue f) else f
    let rec walk : Nat → Int → Int → Bool
      | 0, _, t => t == 0
      | k + 1, f, t =>
        if f != 0 then
          if !compatibleKind (topOfStack f) (topOfStack t) then false
          else walk k (popValue f) (popValue t)
        else t == 0
    walk 40 (down 64 fromS) toS

/-- `explain_incompatible_stack`, lines 1542-1566. -/
def explainIncompatible (toS : Int) : String :=
  if toS == OVERFLOWED then "stack is too deep to analyze"
  else if toS == UNINITIALIZED then
    "can't jump into an exception handler, or code may be unreachable"
  else
    match topOfStack toS with
    | 2 => "can't jump into an 'except' block as there's no exception"
    | 5 => "can't jump into a re-raising block as there's no location"
    | 3 | 4 => "incompatible stacks"
    | _ => "can't jump into the body of a for loop"

/-- `first_line_not_before`, lines 1594-1607; `lines` holds `-1` where no line starts. -/
def firstLineNotBefore (lines : Array Int) (line : Int) : Int :=
  let r := lines.foldl (fun acc l =>
    if l ≥ line then
      match acc with
      | none => some l
      | some a => if l < a then some l else some a
    else acc) (none : Option Int)
  r.getD (-1)

/-- What `frame_lineno_set_impl` decides, lines 1705-1787, on a line event. -/
inductive Jump where
  /-- `ValueError` with this message. -/
  | error (msg : String)
  /-- `instr_ptr = best_addr`, after popping down to `best_stack`. -/
  | ok (addr : Nat) (bestStack : Int)
  deriving Repr, DecidableEq

/-- Lines 1723-1787: `value` is the requested line, `lasti` the current instruction. -/
def linenoDecide (code : Array Unit') (table : Array Nat) (lines : Array Int)
    (firstLine value : Int) (lasti : Nat) : Jump :=
  if value < firstLine then .error s!"line {value} comes before the current code block"
  else
    let newLine := firstLineNotBefore lines value
    if newLine < 0 then .error s!"line {value} comes after the current code block"
    else
      let stacks := markStacks code table
      let startStack := stacks.getD lasti UNINITIALIZED
      let step (acc : Int × Nat × Int × String) (ii : Int × Nat) :=
        let (best, addr, err, msg) := acc
        let (l, i) := ii
        if l != newLine then acc
        else
          let target := stacks.getD i UNINITIALIZED
          if compatibleStack startStack target then
            if target > best then (target, i, 0, msg) else (best, addr, 0, msg)
          else if err < 0 then
            if startStack == OVERFLOWED then (best, addr, err, "stack to deep to analyze")
            else if startStack == UNINITIALIZED then
              (best, addr, err, "can't jump from unreachable code")
            else (best, addr, 1, explainIncompatible target)
          else acc
      let (best, addr, err, msg) := (lines.toList.zipIdx).foldl step
        (OVERFLOWED, 0, (-1 : Int), "cannot find bytecode for specified line")
      if err != 0 then .error msg else .ok addr best

end PyLean.Bytecode.FrameObj
