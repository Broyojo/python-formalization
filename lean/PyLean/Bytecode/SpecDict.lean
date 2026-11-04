import PyLean.Bytecode.SpecCells

/-!
The str-keyed dict operations the name opcodes use (`Python/ceval.c`, `Objects/dictobject.c` as
the model's `dictFind`, `dictGetStr`, `dictSetStr`, `dictPopStr`): what is stored under a name is
what a lookup of that name returns, a store under one name leaves every other name alone, and a
pop removes the name. The lookup walks the entries in insertion order and compares the stored
hash and then the key, as `unicodekeys_lookup_unicode` does for str keys.
-/

namespace PyLean.Bytecode

open Uop

/-- The first entry from `i` on, within `n` steps, whose hash and key match `name`. -/
def findStr (es : Array DictEntry) (name : String) (h : Int) : Nat → Nat → Option Nat
  | 0, _ => none
  | n + 1, i =>
    match es[i]? with
    | none => none
    | some e => if e.hash == h && e.key == .str name then some i else findStr es name h n (i + 1)

theorem dictFind_go (d : DictObj) (name : String) (h : Int) (rt : Rt) :
    ∀ n i, dictFind.go (strKeyEq name) d h n i rt = .ok (findStr d.entries name h n i) rt := by
  intro n
  induction n with
  | zero => intro i; rfl
  | succ n ih =>
    intro i
    simp only [dictFind.go, findStr]
    cases he : d.entries[i]? with
    | none => rfl
    | some e =>
      by_cases hh : (e.hash == h) = true
      · by_cases hk : (e.key == Val.str name) = true
        · simp [hh, hk, strKeyEq, bind, EStateM.bind, pure, EStateM.pure]
        · simp only [Bool.not_eq_true] at hk
          simp [hh, hk, strKeyEq, bind, EStateM.bind, pure, EStateM.pure, ih]
      · simp only [Bool.not_eq_true] at hh
        simp [hh, ih]

theorem dictFind_str (d : DictObj) (name : String) (h : Int) (rt : Rt) :
    dictFind (strKeyEq name) d h rt = .ok (findStr d.entries name h d.entries.size 0) rt :=
  dictFind_go d name h rt _ _

/-- A match found is a match: the entry at the index has the hash and the key. -/
theorem findStr_some (es : Array DictEntry) (name : String) (h : Int) :
    ∀ n i j, findStr es name h n i = some j → ∃ e, es[j]? = some e ∧ e.hash = h ∧ e.key = .str name ∧ i ≤ j := by
  intro n
  induction n with
  | zero => intro i j h; simp [findStr] at h
  | succ n ih =>
    intro i j hf
    simp only [findStr] at hf
    cases he : es[i]? with
    | none => simp [he] at hf
    | some e =>
      simp only [he] at hf
      by_cases hm : (e.hash == h && e.key == .str name) = true
      · simp only [hm, ite_true, Option.some.injEq] at hf
        subst hf
        simp only [Bool.and_eq_true, beq_iff_eq] at hm
        exact ⟨e, he, hm.1, hm.2, Nat.le_refl _⟩
      · simp only [hm] at hf
        obtain ⟨e', h1, h2, h3, h4⟩ := ih (i + 1) j hf
        exact ⟨e', h1, h2, h3, by omega⟩

/-- No match in range means no entry there has the hash and the key. -/
theorem findStr_none (es : Array DictEntry) (name : String) (h : Int) :
    ∀ n i, findStr es name h n i = none → i + n ≥ es.size →
      ∀ j e, i ≤ j → es[j]? = some e → ¬ (e.hash = h ∧ e.key = .str name) := by
  intro n
  induction n with
  | zero => intro i _ hs j e hij hj; have := (Array.getElem?_eq_some_iff.1 hj).1; omega
  | succ n ih =>
    intro i hf hs j e hij hj
    simp only [findStr] at hf
    cases he : es[i]? with
    | none => have := (Array.getElem?_eq_some_iff.1 hj).1; simp at he; omega
    | some e0 =>
      simp only [he] at hf
      by_cases hm : (e0.hash == h && e0.key == .str name) = true
      · simp [hm] at hf
      · simp only [hm] at hf
        by_cases hji : j = i
        · subst hji
          rw [he] at hj
          cases hj
          simpa using hm
        · exact ih (i + 1) hf (by omega) j e (by omega) hj

/-- Changing a value leaves every lookup where it was: only hashes and keys are compared. -/
theorem findStr_modify (es : Array DictEntry) (name : String) (h : Int) (k : Nat) (v : Val) :
    ∀ n i, findStr (es.modify k fun e => { e with value := v }) name h n i = findStr es name h n i := by
  intro n
  induction n with
  | zero => intro i; rfl
  | succ n ih =>
    intro i
    simp only [findStr, Array.getElem?_modify]
    by_cases hk : k = i
    · subst hk
      cases es[k]? <;> simp [ih]
    · simp [hk, ih]

/-- Appending an entry no lookup in range matched: the scan reaches it. -/
theorem findStr_push (es : Array DictEntry) (name' : String) (h' : Int) (e : DictEntry) :
    ∀ n i, i + n = es.size → findStr es name' h' n i = none →
      findStr (es.push e) name' h' (n + 1) i =
        if e.hash == h' && e.key == .str name' then some es.size else none := by
  intro n
  induction n with
  | zero =>
    intro i hi _
    simp only [Nat.add_zero] at hi
    subst hi
    simp [findStr]
  | succ n ih =>
    intro i hi hf
    have hlt : i < es.size := by omega
    have he : es[i]? = some es[i] := by simp [hlt]
    rw [findStr.eq_2] at hf
    rw [findStr.eq_2, Array.getElem?_push_lt hlt]
    simp only [he] at hf ⊢
    by_cases hm : (es[i].hash == h' && es[i].key == .str name') = true
    · simp [hm] at hf
    · simp only [hm, Bool.false_eq_true, ite_false] at hf ⊢
      exact ih (i + 1) (by omega) hf

/-- A match before the end stays the match after appending. -/
theorem findStr_push_some (es : Array DictEntry) (name' : String) (h' : Int) (e : DictEntry) :
    ∀ n i j, i + n = es.size → findStr es name' h' n i = some j →
      findStr (es.push e) name' h' (n + 1) i = some j := by
  intro n
  induction n with
  | zero => intro i j _ hf; simp [findStr] at hf
  | succ n ih =>
    intro i j hi hf
    have hlt : i < es.size := by omega
    have he : es[i]? = some es[i] := by simp [hlt]
    rw [findStr.eq_2] at hf
    rw [findStr.eq_2, Array.getElem?_push_lt hlt]
    simp only [he] at hf ⊢
    by_cases hm : (es[i].hash == h' && es[i].key == .str name') = true
    · simp only [hm, ite_true] at hf ⊢
      exact hf
    · simp only [hm, Bool.false_eq_true, ite_false] at hf ⊢
      exact ih (i + 1) j (by omega) hf

/-- The value stored at a found index. -/
def lookupStr (d : DictObj) (name : String) : Option Val :=
  match findStr d.entries name (hashStr name) d.entries.size 0 with
  | some i => d.entries[i]?.map (·.value)
  | none => none

/-- The dict after `dictSetStr` (versions aside). -/
def storeStr (d : DictObj) (name : String) (v : Val) (ver : Nat) : DictObj :=
  match findStr d.entries name (hashStr name) d.entries.size 0 with
  | some i => { d with entries := d.entries.modify i fun e => { e with value := v } }
  | none => { entries := d.entries.push { hash := hashStr name, key := .str name, value := v }, version := ver }

/-- What is stored under a name is what a lookup returns, and every other name keeps its value. -/
theorem lookup_store (d : DictObj) (name name' : String) (v : Val) (ver : Nat) :
    lookupStr (storeStr d name v ver) name' = if name' = name then some v else lookupStr d name' := by
  unfold lookupStr storeStr
  cases hf : findStr d.entries name (hashStr name) d.entries.size 0 with
  | some i =>
    obtain ⟨e, he, hh, hk, -⟩ := findStr_some _ _ _ _ _ _ hf
    simp only [Array.size_modify, findStr_modify]
    by_cases hn : name' = name
    · subst hn
      simp [hf, Array.getElem?_modify, he]
    · simp only [hn, ite_false]
      cases hf' : findStr d.entries name' (hashStr name') d.entries.size 0 with
      | none => rfl
      | some j =>
        obtain ⟨e', he', -, hk', -⟩ := findStr_some _ _ _ _ _ _ hf'
        have hij : i ≠ j := by
          intro hij; subst hij; rw [he] at he'; cases he'; rw [hk] at hk'; cases hk'; exact hn rfl
        simp [Array.getElem?_modify, hij]
  | none =>
    simp only [Array.size_push]
    by_cases hn : name' = name
    · subst hn
      rw [findStr_push _ _ _ _ _ 0 (by simp) hf]
      simp
    · simp only [hn, ite_false]
      cases hf' : findStr d.entries name' (hashStr name') d.entries.size 0 with
      | none =>
        rw [findStr_push _ name' _ _ _ 0 (by simp) hf']
        have : ((Val.str name) == Val.str name') = false := by simp [Ne.symm hn]
        simp [this]
      | some j =>
        rw [findStr_push_some _ _ _ _ _ 0 j (by simp) hf']
        have hj : j < d.entries.size := by
          obtain ⟨e', he', -⟩ := findStr_some _ _ _ _ _ _ hf'
          exact (Array.getElem?_eq_some_iff.1 he').1
        simp [Array.getElem?_push_lt hj, hj]

theorem dictGetStr_ref (a : Addr) (d : DictObj) (name : String) (rt : Rt)
    (h : rt.heap[a]? = some (.dict d)) : dictGetStr (.ref a) name rt = .ok (lookupStr d name) rt := by
  simp only [dictGetStr, getDict, getObj, h, bind, EStateM.bind, dictFind_str, lookupStr, pure, EStateM.pure]
  cases hf : findStr d.entries name (hashStr name) d.entries.size 0 <;> simp [hf, pure, EStateM.pure]

/-- The runtime after `dictSetStr` on the dict at `a`. -/
def storedRt (rt : Rt) (a : Addr) (d : DictObj) (name : String) (v : Val) : Rt :=
  match findStr d.entries name (hashStr name) d.entries.size 0 with
  | some _ => { rt with heap := rt.heap.setIfInBounds a (.dict (storeStr d name v rt.nextVersion)) }
  | none => { rt with heap := rt.heap.setIfInBounds a (.dict (storeStr d name v rt.nextVersion)),
                      nextVersion := rt.nextVersion + 1 }

theorem dictSetStr_ref (a : Addr) (d : DictObj) (name : String) (v : Val) (rt : Rt)
    (h : rt.heap[a]? = some (.dict d)) : dictSetStr (.ref a) name v rt = .ok () (storedRt rt a d name v) := by
  simp only [dictSetStr, getDict, getObj, h, bind, EStateM.bind, dictFind_str, storedRt, storeStr]
  cases hf : findStr d.entries name (hashStr name) d.entries.size 0 <;>
  simp [hf, dictInsertAt, putDict, setObj, freshVersion, bind, EStateM.bind, pure, EStateM.pure]

theorem storedRt_heap (rt : Rt) (a : Addr) (d : DictObj) (name : String) (v : Val)
    (h : rt.heap[a]? = some (.dict d)) :
    (storedRt rt a d name v).heap[a]? = some (.dict (storeStr d name v rt.nextVersion)) := by
  have hlt : a < rt.heap.size := (Array.getElem?_eq_some_iff.1 h).1
  unfold storedRt
  cases hf : findStr d.entries name (hashStr name) d.entries.size 0 <;> simp [Array.getElem?_setIfInBounds, hlt]

/-- `STORE_GLOBAL name` then `LOAD_GLOBAL name` pushes the stored value and nothing else, on a
frame whose globals are an exact dict (as for every function defined in a module). Every other
name keeps its value (`lookup_store`). -/
def GlobalRoundTrip : Prop := ∀ (e : Env) (s : St) (g : Addr) (d : DictObj) (c : Code) (i : Nat)
    (name : String) (v : Val) (rest : List Val),
  s.regs.frame.globals = .ref g → s.regs.rt.heap[g]? = some (.dict d) →
  e.P[s.regs.frame.code]? = some c → c.names[i]? = some name → s.stack = v :: rest →
    (execOp { e with oparg := i } .STORE_GLOBAL *> execOp { e with oparg := 2 * i } .LOAD_GLOBAL) s =
      .ok () ⟨{ s.regs with rt := storedRt s.regs.rt g d name v }, v :: rest⟩

theorem globalRoundTrip_proven : GlobalRoundTrip := by
  intro e s g d c i name v rest hg hd hc hn hs
  obtain ⟨regs, stack⟩ := s
  simp only at hg hd hc hs
  subst hs
  have hco := getCode_ok (P := e.P) (r := regs) hc
  have hset := dictSetStr_ref g d name v regs.rt hd
  have hsh : (2 * i) >>> 1 = i := by rw [Nat.shiftRight_eq_div_pow]; omega
  have hlo : (2 * i) &&& 1 = 0 := by rw [Nat.and_one_is_mod]; omega
  have hheap := storedRt_heap regs.rt g d name v hd
  have hget : dictGetStr (.ref g) name (storedRt regs.rt g d name v) =
      .ok (some v) (storedRt regs.rt g d name v) := by
    rw [dictGetStr_ref g _ name _ hheap, lookup_store]; simp
  have hcode : ({ regs with rt := storedRt regs.rt g d name v } : Regs).frame.code = regs.frame.code := rfl
  simp [SeqRight.seqRight, EStateM.seqRight, execOp, STORE_GLOBAL, LOAD_GLOBAL, _SPECIALIZE_LOAD_GLOBAL,
    _LOAD_GLOBAL, _PUSH_NULL_CONDITIONAL, loadGlobal, optItem, stk, popN, pushAll, bind, EStateM.bind,
    BM.lift, RM.lift, liftM, monadLift, MonadLift.monadLift, pure, EStateM.pure, getName, getCode, hc, hn,
    getFrame, hg, hset, hsh, hlo, isExactDict, getObj, hheap, hget]

/-- `LOAD_GLOBAL` (`Python/bytecodes.c:2270-2289`, `_PyEval_LoadGlobalStackRef`,
`Python/ceval.c:3597-3630`) looks the name up in the frame's globals, then its builtins, as
`PyMapping_GetOptionalItem` does (a dict lookup for an exact dict, `__getitem__` with `KeyError`
swallowed for anything else, such as a dict subclass passed to `exec`), and pushes the value,
followed by a NULL when the low bit of the oparg asks for the call form; when neither has the name
it raises `NameError` through `_PyEval_FormatExcCheckArg`, and when a lookup raises it propagates
that exception; in both failures the stack is unchanged. For every pair of namespaces and every
object model. The exact-dict fast path `_PyDict_LoadGlobalStackRef` gives the same answers as
`PyMapping_GetOptionalItem` on exact dicts, so the model takes one route. A lazy-import object
(`PyLazyImport_CheckExact`, `:3622-3630`) does not exist in the model. -/
def LoadGlobalRules : Prop := ∀ (e : Env) (s : St) (c : Code) (name : String),
  e.P[s.regs.frame.code]? = some c → c.names[e.oparg >>> 1]? = some name →
    (∀ v rt, optItem e s.regs.frame.globals name s.regs.rt = .ok (some v) rt →
      execOp e .LOAD_GLOBAL s = .ok ()
        ⟨{ s.regs with rt := rt }, List.replicate (e.oparg &&& 1) .null ++ v :: s.stack⟩) ∧
    (∀ rt v rt', optItem e s.regs.frame.globals name s.regs.rt = .ok none rt →
      optItem e s.regs.frame.builtins name rt = .ok (some v) rt' →
      execOp e .LOAD_GLOBAL s = .ok ()
        ⟨{ s.regs with rt := rt' }, List.replicate (e.oparg &&& 1) .null ++ v :: s.stack⟩) ∧
    (∀ rt rt' x rt'', optItem e s.regs.frame.globals name s.regs.rt = .ok none rt →
      optItem e s.regs.frame.builtins name rt = .ok none rt' →
      (formatExcCheckArg "NameError" (nameErrorMsg name) name : RM Val) rt' = .error x rt'' →
      execOp e .LOAD_GLOBAL s = .error x ⟨{ s.regs with rt := rt'' }, s.stack⟩) ∧
    (∀ x rt, optItem e s.regs.frame.globals name s.regs.rt = .error x rt →
      execOp e .LOAD_GLOBAL s = .error x ⟨{ s.regs with rt := rt }, s.stack⟩) ∧
    (∀ rt x rt', optItem e s.regs.frame.globals name s.regs.rt = .ok none rt →
      optItem e s.regs.frame.builtins name rt = .error x rt' →
      execOp e .LOAD_GLOBAL s = .error x ⟨{ s.regs with rt := rt' }, s.stack⟩)

theorem loadGlobalRules_proven : LoadGlobalRules := by
  intro e s c name hc hn
  obtain ⟨regs, stack⟩ := s
  simp only at hc ⊢
  have hrep : (List.replicate (e.oparg &&& 1) Val.null).length = e.oparg &&& 1 := by simp
  have hco := getCode_ok (P := e.P) (r := regs) hc
  refine ⟨fun v rt h => ?_, fun rt v rt' h1 h2 => ?_, fun rt rt' x rt'' h1 h2 h3 => ?_,
    fun x rt h => ?_, fun rt x rt' h1 h2 => ?_⟩
  · simp [bind, EStateM.bind, BM.lift, RM.lift, liftM, monadLift, MonadLift.monadLift, pure,
      EStateM.pure, throw, throwThe, MonadExcept.throw, EStateM.throw, MonadExceptOf.throw, peekN, popN,
      pushAll, stk, getObj, execOp, LOAD_GLOBAL, _SPECIALIZE_LOAD_GLOBAL, _LOAD_GLOBAL, _PUSH_NULL_CONDITIONAL, loadGlobal,
      getName, hco, hn, getFrame, h]
  · simp [bind, EStateM.bind, BM.lift, RM.lift, liftM, monadLift, MonadLift.monadLift, pure,
      EStateM.pure, throw, throwThe, MonadExcept.throw, EStateM.throw, MonadExceptOf.throw, peekN, popN,
      pushAll, stk, getObj, execOp, LOAD_GLOBAL, _SPECIALIZE_LOAD_GLOBAL, _LOAD_GLOBAL, _PUSH_NULL_CONDITIONAL, loadGlobal,
      getName, hco, hn, getFrame, h1, h2]
  · simp [bind, EStateM.bind, BM.lift, RM.lift, liftM, monadLift, MonadLift.monadLift, pure,
      EStateM.pure, throw, throwThe, MonadExcept.throw, EStateM.throw, MonadExceptOf.throw, peekN, popN,
      pushAll, stk, getObj, execOp, LOAD_GLOBAL, _SPECIALIZE_LOAD_GLOBAL, _LOAD_GLOBAL, loadGlobal, getName, hco, hn,
      getFrame, h1, h2, h3]
  · simp [bind, EStateM.bind, BM.lift, RM.lift, liftM, monadLift, MonadLift.monadLift, pure,
      EStateM.pure, throw, throwThe, MonadExcept.throw, EStateM.throw, MonadExceptOf.throw, peekN, popN,
      pushAll, stk, getObj, execOp, LOAD_GLOBAL, _SPECIALIZE_LOAD_GLOBAL, _LOAD_GLOBAL, loadGlobal, getName, hco, hn,
      getFrame, h]
  · simp [bind, EStateM.bind, BM.lift, RM.lift, liftM, monadLift, MonadLift.monadLift, pure,
      EStateM.pure, throw, throwThe, MonadExcept.throw, EStateM.throw, MonadExceptOf.throw, peekN, popN,
      pushAll, stk, getObj, execOp, LOAD_GLOBAL, _SPECIALIZE_LOAD_GLOBAL, _LOAD_GLOBAL, loadGlobal, getName, hco, hn,
      getFrame, h1, h2]

/-- With no exception being handled, the `NameError` that `_PyEval_FormatExcCheckArg` raises
(`Python/ceval.c:3463-3472`) carries the name in its `name` member, and the `UnboundLocalError` it
raises for a local does not (`exc == PyExc_NameError` compares the class itself). -/
def NameErrorName : Prop := ∀ (rt : Rt) (msg n : String), rt.excInfo = [.null] →
  (∀ x rt', (formatExcCheckArg "NameError" msg n : RM Val) rt = .error x rt' →
    ∃ a args, x = .exc (.ref a) ∧
      rt'.heap[a]? = some (.inst { cls := .cls "NameError", exc := some { args := args, name := .str n } })) ∧
  (∀ x rt', (formatExcCheckArg "UnboundLocalError" msg n : RM Val) rt = .error x rt' →
    ∃ a args, x = .exc (.ref a) ∧
      rt'.heap[a]? = some (.inst { cls := .cls "UnboundLocalError", exc := some { args := args } }))

theorem nameErrorName_proven : NameErrorName := by
  intro rt msg n he
  constructor
  · intro x rt' h
    simp [formatExcCheckArg, newExc, mkTuple, alloc, excData, setExcData, setObj, raiseVal, setObject,
      topmostExc, topmostExc.go, he, getObj, bind, EStateM.bind, pure, EStateM.pure, throw, throwThe,
      MonadExcept.throw, EStateM.throw, MonadExceptOf.throw, Array.getElem_push, Array.size_push,
      Array.getElem?_push] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rt.heap.size + 1, .ref rt.heap.size, rfl, ?_⟩
    simp
  · intro x rt' h
    simp [formatExcCheckArg, newExc, mkTuple, alloc, raiseVal, setObject, topmostExc, topmostExc.go, he,
      bind, EStateM.bind, pure, EStateM.pure, throw, throwThe, MonadExcept.throw, EStateM.throw,
      MonadExceptOf.throw] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rt.heap.size + 1, .ref rt.heap.size, rfl, ?_⟩
    simp [Array.getElem_push]

def LoadGlobalFull : Prop := LoadGlobalRules ∧ NameErrorName
theorem loadGlobalFull_proven : LoadGlobalFull := ⟨loadGlobalRules_proven, nameErrorName_proven⟩

/-- `LOAD_NAME` looks the name up in the frame's locals, then its globals, then its builtins, and
pushes it; when none has it, it raises `NameError` naming it and leaves the stack alone. For a
frame whose namespaces are exact dicts, as in a class body or at module level. -/
def LoadNameRules : Prop := ∀ (e : Env) (s : St) (l g b : Addr) (dl dg db : DictObj) (c : Code)
    (name : String),
  s.regs.frame.locals = .ref l → s.regs.frame.globals = .ref g → s.regs.frame.builtins = .ref b →
  s.regs.rt.heap[l]? = some (.dict dl) → s.regs.rt.heap[g]? = some (.dict dg) →
  s.regs.rt.heap[b]? = some (.dict db) →
  e.P[s.regs.frame.code]? = some c → c.names[e.oparg]? = some name →
    (∀ v, (lookupStr dl name = some v ∨ (lookupStr dl name = none ∧ lookupStr dg name = some v) ∨
        (lookupStr dl name = none ∧ lookupStr dg name = none ∧ lookupStr db name = some v)) →
      execOp e .LOAD_NAME s = .ok () { s with stack := v :: s.stack }) ∧
    (lookupStr dl name = none → lookupStr dg name = none → lookupStr db name = none → ∀ x rt,
      (formatExcCheckArg "NameError" (nameErrorMsg name) name : RM Val) s.regs.rt = .error x rt →
      execOp e .LOAD_NAME s = .error x { s with regs := { s.regs with rt := rt } })

theorem loadNameRules_proven : LoadNameRules := by
  intro e s l g b dl dg db c name hl hg hb hdl hdg hdb hc hn
  obtain ⟨regs, stack⟩ := s
  simp only at hl hg hb hdl hdg hdb hc ⊢
  have hgl := dictGetStr_ref l dl name regs.rt hdl
  have hgg := dictGetStr_ref g dg name regs.rt hdg
  have hgb := dictGetStr_ref b db name regs.rt hdb
  have hnn : (Val.ref l == Val.null) = false := rfl
  constructor
  · intro v hv
    rcases hv with hv | ⟨h0, hv⟩ | ⟨h0, h1, hv⟩ <;>
    simp [execOp, LOAD_NAME, loadName, optItem, stk, popN, pushAll, bind, EStateM.bind, BM.lift, RM.lift, liftM,
      monadLift, MonadLift.monadLift, pure, EStateM.pure, getName, getCode, hc, hn, getFrame, hl, hg, hb,
      isExactDict, getObj, hdl, hdg, hdb, hgl, hgg, hgb, hv, hnn, *]
  · intro h0 h1 h2 x rt hx
    simp [execOp, LOAD_NAME, loadName, optItem, stk, popN, bind, EStateM.bind, BM.lift, RM.lift, liftM, monadLift,
      MonadLift.monadLift, pure, EStateM.pure, getName, getCode, hc, hn, getFrame, hl, hg, hb, isExactDict,
      getObj, hdl, hdg, hdb, hgl, hgg, hgb, h0, h1, h2, hnn, hx]

/-- `STORE_NAME name` then `LOAD_NAME name` pushes the stored value, on a frame whose locals are an
exact dict (a class body or module level). -/
def NameRoundTrip : Prop := ∀ (e : Env) (s : St) (l : Addr) (dl : DictObj) (c : Code) (i : Nat)
    (name : String) (v : Val) (rest : List Val),
  s.regs.frame.locals = .ref l → s.regs.rt.heap[l]? = some (.dict dl) →
  e.P[s.regs.frame.code]? = some c → c.names[i]? = some name → s.stack = v :: rest →
    (execOp { e with oparg := i } .STORE_NAME *> execOp { e with oparg := i } .LOAD_NAME) s =
      .ok () ⟨{ s.regs with rt := storedRt s.regs.rt l dl name v }, v :: rest⟩

theorem nameRoundTrip_proven : NameRoundTrip := by
  intro e s l dl c i name v rest hl hd hc hn hs
  obtain ⟨regs, stack⟩ := s
  simp only at hl hd hc hs
  subst hs
  have hset := dictSetStr_ref l dl name v regs.rt hd
  have hheap := storedRt_heap regs.rt l dl name v hd
  have hget : dictGetStr (.ref l) name (storedRt regs.rt l dl name v) =
      .ok (some v) (storedRt regs.rt l dl name v) := by
    rw [dictGetStr_ref l _ name _ hheap, lookup_store]; simp
  have hnn : (Val.ref l == Val.null) = false := rfl
  simp [SeqRight.seqRight, EStateM.seqRight, execOp, STORE_NAME, LOAD_NAME, loadName, optItem, stk, popN,
    pushAll, bind, EStateM.bind, BM.lift, RM.lift, liftM, monadLift, MonadLift.monadLift, pure, EStateM.pure,
    getName, getCode, hc, hn, getFrame, hl, hset, isExactDict, getObj, hd, hheap, hget, hnn]

end PyLean.Bytecode
