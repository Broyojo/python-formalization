import PyLean.Bytecode.SpecLocals
import PyLean.Bytecode.LawfulBuiltin

/-!
Closure cells and the tuple and list builders, `Python/bytecodes.c`: `MAKE_CELL`, `DELETE_DEREF`,
`LOAD_DEREF`, `STORE_DEREF`, `BUILD_TUPLE`, `BUILD_LIST`.

A cell is a heap object holding one value or NULL. What `STORE_DEREF` writes, `LOAD_DEREF`
reads back; `DELETE_DEREF` empties the cell, after which reading or deleting it again raises
the error `_PyEval_FormatExcUnbound` builds (a `NameError` for a free variable, an
`UnboundLocalError` for a cell variable). `MAKE_CELL` wraps the local's current value, which is
an argument's value when the function's own parameter is captured.

A builder pops its `oparg` operands and pushes one new object holding them in the order they
were pushed, leaving everything below untouched.
-/

namespace PyLean.Bytecode

open Uop

/-- The state after writing object `o` at address `c`. -/
abbrev withObj (s : St) (c : Addr) (o : Obj) : St :=
  { s with regs := { s.regs with rt := { s.regs.rt with heap := s.regs.rt.heap.setIfInBounds c o } } }

theorem cellGet_ok {rt : Rt} {c : Addr} {v : Val} (h : rt.heap[c]? = some (.cell v)) :
    cellGet (.ref c) rt = .ok v rt := by
  simp [cellGet, getObj, h, bind, EStateM.bind, pure, EStateM.pure]

/-- `STORE_DEREF` puts the value in the cell; `LOAD_DEREF` pushes what a bound cell holds, and
after a store it pushes what was stored; `DELETE_DEREF` empties a bound cell. On an empty cell
`LOAD_DEREF` and `DELETE_DEREF` raise the same exception and leave the stack and the cell alone.
The hypothesis is that local `oparg` holds a cell, which the compiler guarantees for these
opcodes after `MAKE_CELL` or `COPY_FREE_VARS`. -/
def CellRules : Prop := ∀ (e : Env) (s : St) (c : Addr) (old : Val),
  s.regs.frame.fast[e.oparg]? = some (.ref c) → s.regs.rt.heap[c]? = some (.cell old) →
    (∀ v rest, s.stack = v :: rest →
      execOp e .STORE_DEREF s = .ok () { withObj s c (.cell v) with stack := rest } ∧
      (v ≠ .null → (execOp e .STORE_DEREF *> execOp e .LOAD_DEREF) s =
        .ok () (withObj s c (.cell v)))) ∧
    (old ≠ .null →
      execOp e .LOAD_DEREF s = .ok () { s with stack := old :: s.stack } ∧
      execOp e .DELETE_DEREF s = .ok () (withObj s c (.cell .null))) ∧
    (old = .null → ∀ (co : Code) x rt, e.P[s.regs.frame.code]? = some co →
      (formatExcUnbound co e.oparg : RM Unit) s.regs.rt = .error x rt →
      execOp e .LOAD_DEREF s = .error x { s with regs := { s.regs with rt := rt } } ∧
      execOp e .DELETE_DEREF s = .error x { s with regs := { s.regs with rt := rt } })

theorem storeDeref_ok (e : Env) (s : St) (c : Addr) (v : Val) (rest : List Val)
    (hf : s.regs.frame.fast[e.oparg]? = some (.ref c)) (hs : s.stack = v :: rest) :
    execOp e .STORE_DEREF s = .ok () { withObj s c (.cell v) with stack := rest } := by
  show stk 1 0 _ s = _
  obtain ⟨regs, stack⟩ := s
  simp only at hs hf
  subst hs
  exact stk_ok (outs := []) (r := _) (by simp)
    (by simp [bind, EStateM.bind, getLocal_ok hf, cellSet, setObj, RM.lift, liftM, monadLift,
      MonadLift.monadLift, pure, EStateM.pure]) rfl

theorem loadDeref_ok (e : Env) (s : St) (c : Addr) (v : Val)
    (hf : s.regs.frame.fast[e.oparg]? = some (.ref c)) (hc : s.regs.rt.heap[c]? = some (.cell v))
    (hn : v ≠ .null) :
    execOp e .LOAD_DEREF s = .ok () { s with stack := v :: s.stack } := by
  have hb : (v == Val.null) = false := by simpa using hn
  show stk 0 1 _ s = _
  exact stk_ok (outs := [v]) (r := s.regs) (by simp)
    (by simp [bind, EStateM.bind, getLocal_ok hf, cellGet_ok hc, hb, RM.lift, liftM, monadLift,
      MonadLift.monadLift, pure, EStateM.pure]) rfl

theorem cellRules_proven : CellRules := by
  intro e s c old hf hc
  refine ⟨fun v rest hs => ⟨storeDeref_ok e s c v rest hf hs, fun hn => ?_⟩, fun hn => ⟨?_, ?_⟩,
    fun hn co x rt hco hx => ⟨?_, ?_⟩⟩
  · simp only [SeqRight.seqRight, EStateM.seqRight, storeDeref_ok e s c v rest hf hs]
    have hf' : ({ withObj s c (.cell v) with stack := rest } : St).regs.frame.fast[e.oparg]? =
        some (.ref c) := hf
    have hc' : ({ withObj s c (.cell v) with stack := rest } : St).regs.rt.heap[c]? = some (.cell v) := by
      simp [withObj, Array.getElem?_setIfInBounds, (Array.getElem?_eq_some_iff.1 hc).1]
    rw [loadDeref_ok e _ c v hf' hc' hn]
    obtain ⟨regs, stack⟩ := s
    simp only at hs
    subst hs
    rfl
  · exact loadDeref_ok e s c old hf hc hn
  · have hb : (old == Val.null) = false := by simpa using hn
    show stk 0 0 _ s = _
    exact stk_ok (outs := []) (r := _) (by simp)
      (by simp [bind, EStateM.bind, getLocal_ok hf, cellGet_ok hc, hb, cellSet, setObj, RM.lift, liftM,
        monadLift, MonadLift.monadLift, pure, EStateM.pure]) rfl
  · subst hn
    show stk 0 1 _ s = _
    exact stk_err (by simp) (by
      simp [bind, EStateM.bind, getLocal_ok hf, cellGet_ok hc, getCode_ok hco, RM.lift, liftM, monadLift,
        MonadLift.monadLift, hx])
  · subst hn
    show stk 0 0 _ s = _
    exact stk_err (by simp) (by
      simp [bind, EStateM.bind, getLocal_ok hf, cellGet_ok hc, getCode_ok hco, RM.lift, liftM, monadLift,
        MonadLift.monadLift, hx])

/-- `MAKE_CELL` replaces local `oparg` with a new cell holding the local's value, so a following
`LOAD_DEREF` reads that value back. -/
def MakeCellRules : Prop := ∀ (e : Env) (s : St) (old : Val),
  s.regs.frame.fast[e.oparg]? = some old →
    execOp e .MAKE_CELL s = .ok ()
      { s with regs := { s.regs with
          rt := { s.regs.rt with heap := s.regs.rt.heap.push (.cell old) },
          frame := { s.regs.frame with
            fast := s.regs.frame.fast.setIfInBounds e.oparg (.ref s.regs.rt.heap.size) } } } ∧
    (old ≠ .null → (execOp e .MAKE_CELL *> execOp e .LOAD_DEREF) s = .ok ()
      { s with
        regs := { s.regs with
          rt := { s.regs.rt with heap := s.regs.rt.heap.push (.cell old) },
          frame := { s.regs.frame with
            fast := s.regs.frame.fast.setIfInBounds e.oparg (.ref s.regs.rt.heap.size) } },
        stack := old :: s.stack })

theorem makeCellRules_proven : MakeCellRules := by
  intro e s old hf
  have h1 : execOp e .MAKE_CELL s = .ok ()
      { s with regs := { s.regs with
          rt := { s.regs.rt with heap := s.regs.rt.heap.push (.cell old) },
          frame := { s.regs.frame with
            fast := s.regs.frame.fast.setIfInBounds e.oparg (.ref s.regs.rt.heap.size) } } } := by
    show stk 0 0 _ s = _
    exact stk_ok (outs := []) (r := _) (by simp)
      (by simp [bind, EStateM.bind, getLocal_ok hf, cellNew, alloc, setLocal, RM.lift, liftM, monadLift,
        MonadLift.monadLift, pure, EStateM.pure]) rfl
  refine ⟨h1, fun hn => ?_⟩
  simp only [SeqRight.seqRight, EStateM.seqRight, h1]
  apply loadDeref_ok e _ s.regs.rt.heap.size old _ _ hn
  · have hlt : e.oparg < s.regs.frame.fast.size := (Array.getElem?_eq_some_iff.1 hf).1
    simp [Array.getElem?_setIfInBounds, hlt]
  · simp

/-- `BUILD_TUPLE n` and `BUILD_LIST n` pop their `n` operands, leaving the rest of the stack alone.
`BUILD_LIST n` always pushes a new list, and `BUILD_TUPLE n` for `n > 0` a new tuple, holding the
operands in the order they were pushed; `BUILD_TUPLE 0` pushes no new object but the `tuple_empty`
singleton (`_PyTuple_FromStackRefStealOnSuccess`, `Objects/tupleobject.c:474-476`),
made on first use and the same object after. -/
def BuildRules : Prop := ∀ (e : Env) (regs : Regs) (top rest : List Val), top.length = e.oparg →
    (top ≠ [] → execOp e .BUILD_TUPLE ⟨regs, top ++ rest⟩ = .ok ()
      ⟨{ regs with rt := { regs.rt with heap := regs.rt.heap.push (.tuple top.reverse.toArray) } },
        .ref regs.rt.heap.size :: rest⟩) ∧
    (top = [] → regs.rt.emptyTuple ≠ .null → execOp e .BUILD_TUPLE ⟨regs, top ++ rest⟩ = .ok ()
      ⟨regs, regs.rt.emptyTuple :: rest⟩) ∧
    (top = [] → regs.rt.emptyTuple = .null → execOp e .BUILD_TUPLE ⟨regs, top ++ rest⟩ = .ok ()
      ⟨{ regs with rt := { regs.rt with heap := regs.rt.heap.push (.tuple #[]),
                                        emptyTuple := .ref regs.rt.heap.size } },
        .ref regs.rt.heap.size :: rest⟩) ∧
    execOp e .BUILD_LIST ⟨regs, top ++ rest⟩ = .ok ()
      ⟨{ regs with rt := { regs.rt with heap := regs.rt.heap.push (.list top.reverse.toArray) } },
        .ref regs.rt.heap.size :: rest⟩

theorem buildRules_proven : BuildRules := by
  intro e regs top rest hn
  have ht : ((top ++ rest).take e.oparg).reverse = top.reverse := by rw [← hn]; simp
  have hd : (top ++ rest).drop e.oparg = rest := by rw [← hn]; simp
  refine ⟨fun hne => ?_, fun he hs => ?_, fun he hs => ?_, ?_⟩
  · have hne' : top.reverse.isEmpty = false := by cases top <;> simp_all
    show stk _ 1 _ _ = _
    refine (stk_ok (outs := [.ref regs.rt.heap.size])
      (r := { regs with rt := { regs.rt with heap := regs.rt.heap.push (.tuple top.reverse.toArray) } })
      (by simp; omega) ?_ rfl).trans ?_
    · simp only [ht]
      simp [bind, EStateM.bind, mkTuple, hne', alloc, RM.lift, liftM, monadLift, MonadLift.monadLift, pure,
        EStateM.pure]
    · simp [hd]
  · subst he
    have h0 : e.oparg = 0 := by simp at hn; omega
    show stk _ 1 _ _ = _
    refine (stk_ok (outs := [regs.rt.emptyTuple]) (r := regs) (by simp [h0]) ?_ rfl).trans ?_
    · simp only [ht]
      cases h : regs.rt.emptyTuple <;> simp_all [bind, EStateM.bind, mkTuple, RM.lift, liftM, monadLift,
        MonadLift.monadLift, pure, EStateM.pure]
    · simp [h0]
  · subst he
    have h0 : e.oparg = 0 := by simp at hn; omega
    show stk _ 1 _ _ = _
    refine (stk_ok (outs := [.ref regs.rt.heap.size])
      (r := { regs with rt := { regs.rt with heap := regs.rt.heap.push (.tuple #[]),
                                             emptyTuple := .ref regs.rt.heap.size } })
      (by simp [h0]) ?_ rfl).trans ?_
    · simp only [ht]
      simp [bind, EStateM.bind, mkTuple, hs, RM.lift, liftM, monadLift, MonadLift.monadLift, pure,
        EStateM.pure]
    · simp [h0]
  · show stk _ 1 _ _ = _
    refine (stk_ok (outs := [.ref regs.rt.heap.size])
      (r := { regs with rt := { regs.rt with heap := regs.rt.heap.push (.list top.reverse.toArray) } })
      (by simp; omega) ?_ rfl).trans ?_
    · simp only [ht]
      simp [bind, EStateM.bind, mkList, alloc, RM.lift, liftM, monadLift, MonadLift.monadLift, pure,
        EStateM.pure]
    · simp [hd]

/-- `UNARY_NEGATIVE` and `UNARY_INVERT` replace the operand with the result of `__neg__` and
`__invert__`, and when that raises they propagate the exception with the operand still on the
stack (`ERROR_NO_POP`, `Python/bytecodes.c:456`, `:609`), for any object model. On an int
with the builtin slots `~x` is `-(x+1)`, as the language reference states (`Doc/reference/
expressions.rst`, "The bitwise inversion of x is defined as -(x+1)"). -/
def UnaryRules : Prop := ∀ (e : Env) (regs : Regs) (v : Val) (rest : List Val),
    (∀ r rt, e.om.negative e.ctx v regs.rt = .ok r rt →
      execOp e .UNARY_NEGATIVE ⟨regs, v :: rest⟩ = .ok () ⟨{ regs with rt := rt }, r :: rest⟩) ∧
    (∀ x rt, e.om.negative e.ctx v regs.rt = .error x rt →
      execOp e .UNARY_NEGATIVE ⟨regs, v :: rest⟩ = .error x ⟨{ regs with rt := rt }, v :: rest⟩) ∧
    (∀ r rt, e.om.invert e.ctx v regs.rt = .ok r rt →
      execOp e .UNARY_INVERT ⟨regs, v :: rest⟩ = .ok () ⟨{ regs with rt := rt }, r :: rest⟩) ∧
    (∀ x rt, e.om.invert e.ctx v regs.rt = .error x rt →
      execOp e .UNARY_INVERT ⟨regs, v :: rest⟩ = .error x ⟨{ regs with rt := rt }, v :: rest⟩) ∧
    (Lawful e.om → ∀ i : Int, v = .int i →
      execOp e .UNARY_INVERT ⟨regs, v :: rest⟩ = .ok () ⟨regs, .int (-(i + 1)) :: rest⟩ ∧
      execOp e .UNARY_NEGATIVE ⟨regs, v :: rest⟩ = .ok () ⟨regs, .int (-i) :: rest⟩)

theorem unaryRules_proven : UnaryRules := by
  intro e regs v rest
  refine ⟨fun r rt h => ?_, fun x rt h => ?_, fun r rt h => ?_, fun x rt h => ?_, fun hom i hv => ?_⟩
  · simp [execOp, UNARY_NEGATIVE, stkK, peekN, popN, pushAll, bind, EStateM.bind, BM.lift, RM.lift, liftM,
      monadLift, MonadLift.monadLift, pure, EStateM.pure, h]
  · simp [execOp, UNARY_NEGATIVE, stkK, peekN, popN, bind, EStateM.bind, BM.lift, RM.lift, liftM,
      monadLift, MonadLift.monadLift, pure, EStateM.pure, h]
  · simp [execOp, UNARY_INVERT, stkK, peekN, popN, pushAll, bind, EStateM.bind, BM.lift, RM.lift, liftM,
      monadLift, MonadLift.monadLift, pure, EStateM.pure, h]
  · simp [execOp, UNARY_INVERT, stkK, peekN, popN, bind, EStateM.bind, BM.lift, RM.lift, liftM,
      monadLift, MonadLift.monadLift, pure, EStateM.pure, h]
  · subst hv
    have hi := hom.invert_int e.ctx i regs.rt
    have hn := hom.neg_int e.ctx i regs.rt
    have e1 : -i - 1 = -(i + 1) := by omega
    rw [e1] at hi
    constructor
    · simp [execOp, UNARY_INVERT, stkK, peekN, popN, pushAll, bind, EStateM.bind, BM.lift, RM.lift, liftM,
        monadLift, MonadLift.monadLift, pure, EStateM.pure, hi]
    · simp [execOp, UNARY_NEGATIVE, stkK, peekN, popN, pushAll, bind, EStateM.bind, BM.lift, RM.lift, liftM,
        monadLift, MonadLift.monadLift, pure, EStateM.pure, hn]

/-- `LIST_APPEND n` appends the top of the stack to the list `n` below it and pops only the value:
the comprehension accumulator stays where it was. -/
def ListAppendRules : Prop := ∀ (e : Env) (regs : Regs) (v : Val) (mid rest : List Val) (a : Addr)
    (items : Array Val), mid.length + 1 = e.oparg → regs.rt.heap[a]? = some (.list items) →
    execOp e .LIST_APPEND ⟨regs, v :: mid ++ .ref a :: rest⟩ = .ok ()
      ⟨{ regs with rt := { regs.rt with heap := regs.rt.heap.setIfInBounds a (.list (items.push v)) } },
        mid ++ .ref a :: rest⟩

theorem listAppendRules_proven : ListAppendRules := by
  intro e regs v mid rest a items hn ha
  show stkE _ _ _ _ _ = _
  have ht : ((v :: mid ++ .ref a :: rest).take (e.oparg + 1)).reverse = .ref a :: mid.reverse ++ [v] := by
    rw [← hn]; have := take_app (v :: mid) (.ref a) rest; simp only [List.cons_append, List.length_cons] at this ⊢
    simp [this]
  have hd : (v :: mid ++ .ref a :: rest).drop (e.oparg + 1) = rest := by
    rw [← hn]; have := drop_app (v :: mid) (.ref a) rest; simpa using this
  refine (stkE_ok (outs := .ref a :: mid.reverse)
    (r := { regs with rt := { regs.rt with heap := regs.rt.heap.setIfInBounds a (.list (items.push v)) } })
    (by simp; omega) ?_ (by simp; omega)).trans ?_
  · have hdl : (Val.ref a :: (mid.reverse ++ [v])).dropLast = Val.ref a :: mid.reverse := by
      rw [← List.cons_append, List.dropLast_concat]
    have hgl : (Val.ref a :: (mid.reverse ++ [v])).getLastD .null = v := by
      rw [← List.cons_append, List.getLastD_eq_getLast?, List.getLast?_concat]; rfl
    dsimp only
    rw [ht]
    show ((do liftM (listAppend (((Val.ref a :: (mid.reverse ++ [v])).dropLast).headD .null)
      ((Val.ref a :: (mid.reverse ++ [v])).getLastD .null)); pure (Val.ref a :: (mid.reverse ++ [v])).dropLast :
        BM (List Val)) regs) = _
    rw [hdl, hgl]
    simp [bind, EStateM.bind, listAppend, getObj, ha, setObj, RM.lift, liftM, monadLift, MonadLift.monadLift,
      pure, EStateM.pure]
  · have hd2 : (mid ++ Val.ref a :: rest).drop e.oparg = rest := by rw [← hn, drop_app]
    simp [hd2]

/-- `BUILD_SLICE 2` and `BUILD_SLICE 3` push a new slice of their operands in order, the step
`None` when there are two. -/
def BuildSliceRules : Prop := ∀ (e : Env) (regs : Regs) (a b c : Val) (rest : List Val),
    (e.oparg = 2 → execOp e .BUILD_SLICE ⟨regs, b :: a :: rest⟩ = .ok ()
      ⟨{ regs with rt := { regs.rt with heap := regs.rt.heap.push (.slice a b .none) } },
        .ref regs.rt.heap.size :: rest⟩) ∧
    (e.oparg = 3 → execOp e .BUILD_SLICE ⟨regs, c :: b :: a :: rest⟩ = .ok ()
      ⟨{ regs with rt := { regs.rt with heap := regs.rt.heap.push (.slice a b c) } },
        .ref regs.rt.heap.size :: rest⟩)

theorem buildSliceRules_proven : BuildSliceRules := by
  intro e regs a b c rest
  constructor
  · intro h
    show stk _ 1 _ _ = _
    simp [stk, popN, h, pushAll, bind, EStateM.bind, BM.lift, RM.lift, liftM, monadLift,
      MonadLift.monadLift, alloc, pure, EStateM.pure]
  · intro h
    show stk _ 1 _ _ = _
    simp [stk, popN, h, pushAll, bind, EStateM.bind, BM.lift, RM.lift, liftM, monadLift,
      MonadLift.monadLift, alloc, pure, EStateM.pure]

/-- `BUILD_STRING n` on `n` strings pushes their concatenation in the order they were pushed.
The compiler only emits it over the results of `FORMAT_SIMPLE`/`FORMAT_WITH_SPEC`, which are
strs. -/
def BuildStringRules : Prop := ∀ (e : Env) (regs : Regs) (pieces : List String) (rest : List Val),
  pieces.length = e.oparg →
    execOp e .BUILD_STRING ⟨regs, (pieces.map Val.str).reverse ++ rest⟩ =
      .ok () ⟨regs, .str (String.join pieces) :: rest⟩

theorem buildStringRules_proven : BuildStringRules := by
  intro e regs pieces rest hn
  show stk _ 1 _ _ = _
  have hlen : (pieces.map Val.str).reverse.length = e.oparg := by simp [hn]
  have ht : (((pieces.map Val.str).reverse ++ rest).take e.oparg).reverse = pieces.map Val.str := by
    rw [← hlen, List.take_left]; simp
  have hd : ((pieces.map Val.str).reverse ++ rest).drop e.oparg = rest := by
    rw [← hlen, List.drop_left]
  refine (stk_ok (outs := [.str (String.join pieces)]) (r := regs) (by simp; omega) ?_ rfl).trans ?_
  · simp only [ht]
    have hj : ∀ ps : List String,
        (ps.map Val.str).map (fun | .str s => s | _ => "") = ps := by
      intro ps
      induction ps with
      | nil => rfl
      | cons x xs ih => simp only [List.map_cons, ih]
    show ((pure [Val.str (String.join ((pieces.map Val.str).map (fun | .str s => s | _ => "")))] :
      BM (List Val)) regs) = _
    rw [hj]
    rfl
  · simp [hd]

/-- `GET_LEN` pushes `len(o)` above `o` and keeps `o`; when `__len__` raises, nothing is popped
(`ERROR_NO_POP`), for any object model. -/
def GetLenRules : Prop := ∀ (e : Env) (regs : Regs) (o : Val) (rest : List Val),
    (∀ n rt, e.om.length e.ctx o regs.rt = .ok n rt →
      execOp e .GET_LEN ⟨regs, o :: rest⟩ = .ok () ⟨{ regs with rt := rt }, .int n :: o :: rest⟩) ∧
    (∀ x rt, e.om.length e.ctx o regs.rt = .error x rt →
      execOp e .GET_LEN ⟨regs, o :: rest⟩ = .error x ⟨{ regs with rt := rt }, o :: rest⟩)

theorem getLenRules_proven : GetLenRules := by
  intro e regs o rest
  constructor
  · intro n rt h
    simp [execOp, GET_LEN, stkK, peekN, popN, pushAll, bind, EStateM.bind, BM.lift, RM.lift, liftM,
      monadLift, MonadLift.monadLift, pure, EStateM.pure, h]
  · intro x rt h
    simp [execOp, GET_LEN, stkK, peekN, bind, EStateM.bind, BM.lift, RM.lift, liftM, monadLift,
      MonadLift.monadLift, pure, EStateM.pure, h]

/-- `x in c` asks the container, not the element: `CONTAINS_OP` calls `PySequence_Contains(c, x)`
and pushes the answer, inverted for `not in`; when the lookup raises it keeps both operands
(`ERROR_NO_POP`). `STORE_SUBSCR` and `DELETE_SUBSCR` call `PyObject_SetItem(c, k, v)` and
`PyObject_DelItem(c, k)` and pop their operands on success and failure alike. All for any object
model. -/
def DispatchRules : Prop := ∀ (e : Env) (regs : Regs) (c x k v : Val) (rest : List Val),
    (∀ b rt, e.om.contains e.ctx c x regs.rt = .ok b rt →
      (e.oparg = 0 → execOp e .CONTAINS_OP ⟨regs, c :: x :: rest⟩ =
        .ok () ⟨{ regs with rt := rt }, .bool b :: rest⟩) ∧
      (e.oparg = 1 → execOp e .CONTAINS_OP ⟨regs, c :: x :: rest⟩ =
        .ok () ⟨{ regs with rt := rt }, .bool (!b) :: rest⟩)) ∧
    (∀ y rt, e.om.contains e.ctx c x regs.rt = .error y rt →
      execOp e .CONTAINS_OP ⟨regs, c :: x :: rest⟩ = .error y ⟨{ regs with rt := rt }, c :: x :: rest⟩) ∧
    (∀ r, e.om.setItem e.ctx c k v regs.rt = r →
      execOp e .STORE_SUBSCR ⟨regs, k :: c :: v :: rest⟩ = match r with
        | .ok _ rt => .ok () ⟨{ regs with rt := rt }, rest⟩
        | .error y rt => .error y ⟨{ regs with rt := rt }, rest⟩) ∧
    (∀ r, e.om.delItem e.ctx c k regs.rt = r →
      execOp e .DELETE_SUBSCR ⟨regs, k :: c :: rest⟩ = match r with
        | .ok _ rt => .ok () ⟨{ regs with rt := rt }, rest⟩
        | .error y rt => .error y ⟨{ regs with rt := rt }, rest⟩)

theorem dispatchRules_proven : DispatchRules := by
  intro e regs c x k v rest
  refine ⟨fun b rt h => ⟨fun h0 => ?_, fun h1 => ?_⟩, fun y rt h => ?_, fun r h => ?_, fun r h => ?_⟩
  · cases b <;>
    simp [execOp, CONTAINS_OP, _SPECIALIZE_CONTAINS_OP, _CONTAINS_OP, stkK, peekN, popN, pushAll, bind,
      EStateM.bind, BM.lift, RM.lift, liftM, monadLift, MonadLift.monadLift, pure, EStateM.pure, h, h0]
  · cases b <;>
    simp [execOp, CONTAINS_OP, _SPECIALIZE_CONTAINS_OP, _CONTAINS_OP, stkK, peekN, popN, pushAll, bind,
      EStateM.bind, BM.lift, RM.lift, liftM, monadLift, MonadLift.monadLift, pure, EStateM.pure, h, h1]
  · simp [execOp, CONTAINS_OP, _SPECIALIZE_CONTAINS_OP, _CONTAINS_OP, stkK, peekN, bind, EStateM.bind,
      BM.lift, RM.lift, liftM, monadLift, MonadLift.monadLift, pure, EStateM.pure, h]
  · subst h
    cases hs : e.om.setItem e.ctx c k v regs.rt <;>
    simp [execOp, STORE_SUBSCR, _SPECIALIZE_STORE_SUBSCR, _STORE_SUBSCR, stk, popN, pushAll, bind,
      EStateM.bind, BM.lift, RM.lift, liftM, monadLift, MonadLift.monadLift, pure, EStateM.pure, hs]
  · subst h
    cases hs : e.om.delItem e.ctx c k regs.rt <;>
    simp [execOp, DELETE_SUBSCR, stk, popN, pushAll, bind, EStateM.bind, BM.lift, RM.lift, liftM,
      monadLift, MonadLift.monadLift, pure, EStateM.pure, hs]

/-- The attribute opcodes take the name from `co_names`: `STORE_ATTR` and `DELETE_ATTR` at
`oparg`, `LOAD_ATTR` at `oparg >> 1`. `STORE_ATTR` calls `PyObject_SetAttr(owner, name, v)` and
`DELETE_ATTR` `PyObject_DelAttr(owner, name)`, popping their operands either way. `LOAD_ATTR`
pushes `getattr(owner, name)`, or with the low bit set the method form `attr, self_or_null` that
`CALL` expects, with `self_or_null` on top; a failure pops `owner`. For any object model. -/
def AttrRules : Prop := ∀ (e : Env) (regs : Regs) (c : Code) (owner v : Val) (rest : List Val),
  e.P[regs.frame.code]? = some c →
    (∀ name r, c.names[e.oparg]? = some name → e.om.setAttr e.ctx owner name v regs.rt = r →
      execOp e .STORE_ATTR ⟨regs, owner :: v :: rest⟩ = match r with
        | .ok _ rt => .ok () ⟨{ regs with rt := rt }, rest⟩
        | .error y rt => .error y ⟨{ regs with rt := rt }, rest⟩) ∧
    (∀ name r, c.names[e.oparg]? = some name → e.om.delAttr e.ctx owner name regs.rt = r →
      execOp e .DELETE_ATTR ⟨regs, owner :: rest⟩ = match r with
        | .ok _ rt => .ok () ⟨{ regs with rt := rt }, rest⟩
        | .error y rt => .error y ⟨{ regs with rt := rt }, rest⟩) ∧
    (∀ name r, c.names[e.oparg >>> 1]? = some name → e.oparg &&& 1 = 0 →
      e.om.getAttr e.ctx owner name regs.rt = r →
      execOp e .LOAD_ATTR ⟨regs, owner :: rest⟩ = match r with
        | .ok a rt => .ok () ⟨{ regs with rt := rt }, a :: rest⟩
        | .error y rt => .error y ⟨{ regs with rt := rt }, rest⟩) ∧
    (∀ name r, c.names[e.oparg >>> 1]? = some name → e.oparg &&& 1 = 1 →
      e.om.getMethod e.ctx owner name regs.rt = r →
      execOp e .LOAD_ATTR ⟨regs, owner :: rest⟩ = match r with
        | .ok (a, slf) rt => .ok () ⟨{ regs with rt := rt }, slf :: a :: rest⟩
        | .error y rt => .error y ⟨{ regs with rt := rt }, rest⟩)

theorem attrRules_proven : AttrRules := by
  intro e regs c owner v rest hc
  have hco := getCode_ok (P := e.P) (r := regs) hc
  have nm : ∀ i name, c.names[i]? = some name → getName e i regs = .ok name regs := by
    intro i name h
    simp [getName, bind, EStateM.bind, hco, h, pure, EStateM.pure]
  refine ⟨fun name r hn h => ?_, fun name r hn h => ?_, fun name r hn h0 h => ?_, fun name r hn h1 h => ?_⟩
  · subst h
    cases hs : e.om.setAttr e.ctx owner name v regs.rt <;>
    simp [execOp, STORE_ATTR, _SPECIALIZE_STORE_ATTR, _STORE_ATTR, stk, popN, pushAll, bind, EStateM.bind,
      BM.lift, RM.lift, liftM, monadLift, MonadLift.monadLift, pure, EStateM.pure, nm _ _ hn, hs]
  · subst h
    cases hs : e.om.delAttr e.ctx owner name regs.rt <;>
    simp [execOp, DELETE_ATTR, stk, popN, pushAll, bind, EStateM.bind, BM.lift, RM.lift, liftM, monadLift,
      MonadLift.monadLift, pure, EStateM.pure, nm _ _ hn, hs]
  · subst h
    have hb : (e.oparg &&& 1 != 0) = false := by simp [h0]
    cases hs : e.om.getAttr e.ctx owner name regs.rt <;>
    simp [execOp, LOAD_ATTR, _SPECIALIZE_LOAD_ATTR, _LOAD_ATTR, stk, popN, pushAll, bind, EStateM.bind,
      BM.lift, RM.lift, liftM, monadLift, MonadLift.monadLift, pure, EStateM.pure, nm _ _ hn, hs, hb, h0]
  · subst h
    have hb : (e.oparg &&& 1 != 0) = true := by simp [h1]
    cases hs : e.om.getMethod e.ctx owner name regs.rt with
    | ok p rt =>
      obtain ⟨a, slf⟩ := p
      simp [execOp, LOAD_ATTR, _SPECIALIZE_LOAD_ATTR, _LOAD_ATTR, stk, popN, pushAll, bind, EStateM.bind,
        BM.lift, RM.lift, liftM, monadLift, MonadLift.monadLift, pure, EStateM.pure, nm _ _ hn, hs, hb, h1]
    | error y rt =>
      simp [execOp, LOAD_ATTR, _SPECIALIZE_LOAD_ATTR, _LOAD_ATTR, stk, popN, pushAll, bind, EStateM.bind,
        BM.lift, RM.lift, liftM, monadLift, MonadLift.monadLift, pure, EStateM.pure, nm _ _ hn, hs, hb, h1]

end PyLean.Bytecode
