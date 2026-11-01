p='lean/PyLean/Bytecode/State.lean'
s=open(p).read()
s=s.replace('''  /-- Instances have a `__dict__`. -/
  hasDict : Bool := true
  deriving Inhabited''','''  /-- Instances have a `__dict__`. -/
  hasDict : Bool := true
  /-- `__abstractmethods__`; non-empty is `Py_TPFLAGS_IS_ABSTRACT`. -/
  abstractMethods : List String := []
  deriving Inhabited''')
open(p,'w').write(s)

p='lean/PyLean/Bytecode/Builtins.lean'
s=open(p).read()
s=s.replace('''      if isExc then
        let t ← mkTuple (args.take npos)''','''      -- `object_new`, `Objects/typeobject.c:6867`
      if let .ref ca := c then
        if let .cls k ← getObj ca then
          if !k.abstractMethods.isEmpty then
            let names := joinStrs "', '" k.abstractMethods
            typeError s!"Can't instantiate abstract class {k.name} without an implementation for abstract method{if k.abstractMethods.length == 1 then "" else "s"} '{names}'"
      if isExc then
        let t ← mkTuple (args.take npos)''')
open(p,'w').write(s)

p='lean/PyLean/Bytecode/Props.lean'
s=open(p).read()
s=s.replace('''import PyLean.Bytecode.FrameObj
''','''import PyLean.Bytecode.FrameProps
import PyLean.Bytecode.Builtins
''')
a=s.index('/-! ## The recursion check -/')
s=s[:a]+r'''/-! ## The recursion check -/

/-- Whether an instruction raised, or completed. -/
def completed {σ : Type} : EStateM.Result Err σ Unit → Bool
  | .ok _ _ => true
  | .error .dispatch _ => true
  | _ => false

/-- A suspended generator at address 0. -/
def susp : GenObj := { frameState := -2, frame := { code := 2 } }

/-- `yield from` on it with the recursion budget spent. -/
def recSt : St :=
  { regs := { rt := { heap := #[.gen susp], pyRecursionRemaining := 0 } },
    stack := [.none, .ref 0] }

def recEnv : Env :=
  { P := #[{}, {}, {}], om := Proto.mkOM #[] 0, ctx := ⟨fun _ _ => throw .fuel⟩,
    opcode := .SEND_GEN, oparg := 0, this := 0 }

/-- `SEND_GEN` is `SEND`, the same as every other specialization is its generic form.
False: the generic path goes through `start_frame`, which enforces the recursion
limit, and `_PUSH_FRAME` does not check it. -/
def SendGenAgrees : Prop := ∀ (e : Env) (s : St),
  completed (execOp e .SEND_GEN s) = completed (execOp e .SEND s)

theorem sendGenAgrees_refuted : ¬SendGenAgrees := by
  intro h
  exact absurd (h recEnv recSt) (by decide)

/-! ## `__abstractmethods__` -/

/-- A class with an abstract method, `__init__` a simple function, specialized. -/
def absSt : St :=
  { regs := { rt := { heap := #[.dict {}, .cls { name := "C", dict := 0, version := 7,
                                                 abstractMethods := ["f"] },
                                .func { code := 2 }] },
              frame := { code := 2 } },
    stack := [.null, .ref 1] }

def absEnv : Env :=
  { P := #[{}, {}, { argcount := 1, nlocalsplus := 1 }], om := Proto.mkOM #[] 0,
    ctx := ⟨fun _ _ => throw .fuel⟩, opcode := .CALL_ALLOC_AND_ENTER_INIT, oparg := 0, this := 0,
    cache := [.tagged 7, .ref 2] }

/-- Instantiating a class with abstract methods never allocates: `object_new` refuses
(`Objects/typeobject.c:6867`). False for `CALL_ALLOC_AND_ENTER_INIT`, which skips
`object_new` and which `specialize_class_call` does not withhold from such a class. -/
def AbstractNeverAllocates : Prop := ∀ (e : Env) (s : St) (k : ClassObj),
  s.stack.getD 1 .null = .ref 1 → s.regs.rt.heap[1]? = some (.cls k) → k.abstractMethods ≠ [] →
  completed (CALL_ALLOC_AND_ENTER_INIT e s) = false

theorem abstractNeverAllocates_refuted : ¬AbstractNeverAllocates := by
  intro h
  have := h absEnv absSt { name := "C", dict := 0, version := 7, abstractMethods := ["f"] }
    rfl rfl (by decide)
  exact absurd this (by decide)

/-! ## List iterators -/

def iterSt : St :=
  { regs := { rt := { heap := #[.list #[.int 1], .listIter (some 0) (-1)] } },
    stack := [.ref 1] }

/-- `FOR_ITER_LIST` and `listiter_next` leave an exhausted iterator in the same state.
False for `it.__setstate__(-1)`: `listiter_next` returns without dropping `it_seq`,
`_ITER_JUMP_LIST` drops it, and `__reduce__` shows which one ran. -/
def ListIterExhaust : Prop := ∀ (a : Addr) (seq : Option Addr) (i : Int) (rt : Rt) (e : Env),
  rt.heap[a]? = some (.listIter seq i) → i < 0 →
  (_ITER_JUMP_LIST e ⟨{ rt := rt }, [.ref a]⟩ |> fun
    | .error _ s => s.regs.rt.heap[a]? == some (.listIter seq i) |>.not.not
    | _ => true) = true

end PyLean.Bytecode
'''
open(p,'w').write(s)
