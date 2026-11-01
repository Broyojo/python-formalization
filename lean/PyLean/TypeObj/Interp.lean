import PyLean.TypeObj.Call

/-!
Ties the knot: `rtOf exec fuel` is the runtime in which `call`, `getAttr`, ... are the real
model functions, with `fuel` levels of re-entrancy left. `exec` runs user code; the
difftest harness and the `Bytecode` interpreter each supply their own. Running out of fuel
is `PyErr.fuel`, not a Python outcome.

The fields are written as lambdas so that building an `Rt` costs nothing: each level is
constructed only when a call reaches it.
-/

namespace PyLean.TypeObj

/-- The runtime with `fuel` levels of re-entrancy. -/
def rtOf (exec : Rt → Nat → Val → NameDict → M Val) : Nat → Rt
  | 0 =>
    { exec := fun _ _ _ => raise .fuel
      call := fun _ _ _ => raise .fuel
      getAttr := fun _ _ => raise .fuel
      getOptionalAttr := fun _ _ => raise .fuel
      setAttr := fun _ _ _ => raise .fuel
      isTrue := fun _ => raise .fuel
      richCompare := fun _ _ _ => raise .fuel
      repr := fun _ => raise .fuel
      str := fun _ => raise .fuel
      hash := fun _ => raise .fuel
      getIter := fun _ => raise .fuel
      iterNext := fun _ => raise .fuel
      listItems := fun _ => raise .fuel
      getItem := fun _ _ => raise .fuel
      size := fun _ => raise .fuel
      contains := fun _ _ => raise .fuel
      numberOr := fun _ _ => raise .fuel
      getsetGet := fun _ _ _ => raise .fuel
      getsetSet := fun _ _ _ _ => raise .fuel
      tpNew := fun _ _ _ _ => raise .fuel
      tpCall := fun _ _ _ _ => raise .fuel }
  | n + 1 =>
    { exec := fun c f l => exec (rtOf exec n) c f l
      call := fun f a k => pyCall (rtOf exec n) f a k
      getAttr := fun v m => pyGetAttr (rtOf exec n) v m
      getOptionalAttr := fun v m => pyGetOptionalAttr (rtOf exec n) v m
      setAttr := fun v m x => pySetAttr (rtOf exec n) v m x
      isTrue := fun v => pyIsTrue (rtOf exec n) v
      richCompare := fun v w op => doRichcompare (rtOf exec n) v w op
      repr := fun v => pyRepr (rtOf exec n) v
      str := fun v => pyStr (rtOf exec n) v
      hash := fun v => pyHash (rtOf exec n) v
      getIter := fun v => pyGetIter (rtOf exec n) v
      iterNext := fun v => pyIterNext (rtOf exec n) v
      listItems := fun v => pySequenceList (rtOf exec n) v
      getItem := fun o k => pyGetItem (rtOf exec n) o k
      size := fun o => pyObjectSize (rtOf exec n) o
      contains := fun o k => pySequenceContains (rtOf exec n) o k
      numberOr := fun a b => binaryOp (rtOf exec n) a b .nb_or "|"
      getsetGet := fun o m v => getsetGetImpl (rtOf exec n) o m v
      getsetSet := fun o m v x => getsetSetImpl (rtOf exec n) o m v x
      tpNew := fun f t a k => callTpNew (rtOf exec n) f t a k
      tpCall := fun f s a k => callTpCall (rtOf exec n) f s a k }

end PyLean.TypeObj
