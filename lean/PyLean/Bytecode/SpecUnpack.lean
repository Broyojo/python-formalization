import PyLean.Bytecode.GenericProps

/-!
`UNPACK_SEQUENCE` and `UNPACK_EX` (`Python/bytecodes.c:2057-2064`, `:2148-2153`) over
`_PyEval_UnpackIterableStackRef` (`Python/ceval.c:2357-2459`), for every object model.

The iterator is abstract: `PyObject_GetIter` and `PyIter_Next` are the model's slots, so each step
may run Python code, change the heap, or raise. `NextChain it rt xs rt'` says that calling
`PyIter_Next(it)` repeatedly from `rt` returns the items `xs` in order and leaves `rt'`. The
statements fix how many times the iterator is called, in which runtime each call happens, which
values end up where on the stack, and the exact messages of the `ValueError`s and of the
`TypeError` for a non-iterable. An unpack that skipped the final exhaustion call, called
`__next__` once too often, reversed the targets, or counted wrongly in a message fails one of them.
-/

namespace PyLean.Bytecode

open Uop

/-- `PyIter_Next(it)` (`iterNextOpt`: `tp_iternext`, with a `StopIteration` cleared into the
end) called once per element of `xs`, from `rt`, returns them in order and leaves `rt'`. -/
def NextChain (om : ObjModel) (ctx : Ctx) (it : Val) : Rt → List Val → Rt → Prop
  | rt, [], rt' => rt' = rt
  | rt, x :: xs, rt' => ∃ rt1, iterNextOpt om ctx it rt = .ok (some x) rt1 ∧ NextChain om ctx it rt1 xs rt'

theorem first_chain (om : ObjModel) (ctx : Ctx) (argcnt : Nat) (after : Option Nat) (it : Val) :
    ∀ (xs : List Val) (rt rt' : Rt) (m i : Nat) (acc : List Val), NextChain om ctx it rt xs rt' →
      unpackIterable.first om ctx argcnt after it (xs.length + m) i acc rt =
        unpackIterable.first om ctx argcnt after it m (i + xs.length) (xs.reverse ++ acc) rt' := by
  intro xs
  induction xs with
  | nil => intro rt rt' m i acc h; simp only [NextChain] at h; subst h; simp
  | cons x xs ih =>
    intro rt rt' m i acc h
    obtain ⟨rt1, h1, h2⟩ := h
    have hl : (x :: xs).length + m = (xs.length + m) + 1 := by simp; omega
    rw [hl]
    simp only [unpackIterable.first, bind, EStateM.bind, h1]
    rw [ih rt1 rt' m (i + 1) (x :: acc) h2]
    simp only [List.length_cons, List.reverse_cons, List.append_assoc, List.singleton_append]
    congr 1
    omega

theorem drain_chain (om : ObjModel) (ctx : Ctx) (it : Val) :
    ∀ (xs : List Val) (rt rt' : Rt) (m : Nat) (acc : List Val), NextChain om ctx it rt xs rt' →
      drain om ctx it (xs.length + m) acc rt = drain om ctx it m (xs.reverse ++ acc) rt' := by
  intro xs
  induction xs with
  | nil => intro rt rt' m acc h; simp only [NextChain] at h; subst h; simp
  | cons x xs ih =>
    intro rt rt' m acc h
    obtain ⟨rt1, h1, h2⟩ := h
    have hl : (x :: xs).length + m = (xs.length + m) + 1 := by simp; omega
    rw [hl]
    simp only [drain, bind, EStateM.bind, h1]
    rw [ih rt1 rt' m (x :: acc) h2]
    simp

/-- The `ValueError` message of `:2401-2425` when the iterator has one item too many: with the
size of an exact list, tuple or dict `v` as it is after that extra item (`Py_SIZE(v)`,
`PyDict_Size(v)`), when that size exceeds the count, and without it otherwise. `none` for a
dangling reference, which no program produces. -/
def tooManyMsg (rt : Rt) (v : Val) (n : Nat) : Option String :=
  let plain := s!"too many values to unpack (expected {n})"
  let sized (ll : Nat) := if ll > n then s!"too many values to unpack (expected {n}, got {ll})" else plain
  match v with
  | .ref a =>
    match rt.heap[a]? with
    | some (.list items) => some (sized items.size)
    | some (.tuple items) => some (sized items.size)
    | some (.dict d) => some (sized d.entries.size)
    | some _ => some plain
    | none => none
  | _ => some plain

/-- `UNPACK_SEQUENCE n` on any value `v`, for every object model, with `PyObject_GetIter(v)`
returning `it` and the items `xs` coming out of `it` one call at a time:
* exactly `n` items, then the end: the items replace `v`, the first one on top, and the runtime is
  the one the final (exhausting) call left;
* fewer than `n`, then the end: `ValueError("not enough values to unpack (expected n, got k)")`
  with `v` popped, raised after that last call;
* `n` items and then one more: `ValueError` with `tooManyMsg`, raised after that extra call;
* the iterator raising after `k ≤ n` items: that exception, with `v` popped;
* `PyObject_GetIter` raising a `TypeError` on a value that has neither `tp_iter` nor the sequence
  protocol: `TypeError("cannot unpack non-iterable T object")`, `T` the type name cut to 200
  bytes; a `TypeError` on an iterable value, or any other exception, propagates. -/
def UnpackSeqRules : Prop := ∀ (e : Env) (regs : Regs) (v : Val) (rest : List Val),
  (∀ it rt1 xs rt2 rt3, e.om.getIter e.ctx v regs.rt = .ok it rt1 → NextChain e.om e.ctx it rt1 xs rt2 →
    iterNextOpt e.om e.ctx it rt2 = .ok none rt3 →
    (xs.length = e.oparg →
      execOp e .UNPACK_SEQUENCE ⟨regs, v :: rest⟩ = .ok () ⟨{ regs with rt := rt3 }, xs ++ rest⟩) ∧
    (xs.length < e.oparg → ∀ x rt4,
      valueError (α := List Val)
        s!"not enough values to unpack (expected {e.oparg}, got {xs.length})" rt3 = .error x rt4 →
      execOp e .UNPACK_SEQUENCE ⟨regs, v :: rest⟩ = .error x ⟨{ regs with rt := rt4 }, rest⟩)) ∧
  (∀ it rt1 xs rt2 w rt3 msg, e.om.getIter e.ctx v regs.rt = .ok it rt1 →
    NextChain e.om e.ctx it rt1 xs rt2 → xs.length = e.oparg →
    iterNextOpt e.om e.ctx it rt2 = .ok (some w) rt3 → tooManyMsg rt3 v e.oparg = some msg →
    ∀ x rt4, valueError (α := List Val) msg rt3 = .error x rt4 →
      execOp e .UNPACK_SEQUENCE ⟨regs, v :: rest⟩ = .error x ⟨{ regs with rt := rt4 }, rest⟩) ∧
  (∀ it rt1 xs rt2 x rt3, e.om.getIter e.ctx v regs.rt = .ok it rt1 →
    NextChain e.om e.ctx it rt1 xs rt2 → xs.length ≤ e.oparg →
    iterNextOpt e.om e.ctx it rt2 = .error x rt3 →
      execOp e .UNPACK_SEQUENCE ⟨regs, v :: rest⟩ = .error x ⟨{ regs with rt := rt3 }, rest⟩) ∧
  (∀ x rt1 rt2, e.om.getIter e.ctx v regs.rt = .error (.exc x) rt1 →
    givenMatches x 8 (.cls "TypeError") rt1 = .ok false rt2 →
      execOp e .UNPACK_SEQUENCE ⟨regs, v :: rest⟩ = .error (.exc x) ⟨{ regs with rt := rt2 }, rest⟩) ∧
  (∀ x rt1 rt2 rt3, e.om.getIter e.ctx v regs.rt = .error (.exc x) rt1 →
    givenMatches x 8 (.cls "TypeError") rt1 = .ok true rt2 → e.om.isIterable v rt2 = .ok true rt3 →
      execOp e .UNPACK_SEQUENCE ⟨regs, v :: rest⟩ = .error (.exc x) ⟨{ regs with rt := rt3 }, rest⟩) ∧
  (∀ x rt1 rt2 rt3 name rt4 y rt5, e.om.getIter e.ctx v regs.rt = .error (.exc x) rt1 →
    givenMatches x 8 (.cls "TypeError") rt1 = .ok true rt2 → e.om.isIterable v rt2 = .ok false rt3 →
    tpName v rt3 = .ok name rt4 →
    typeError (α := Val) s!"cannot unpack non-iterable {trunc200 name} object" rt4 = .error y rt5 →
      execOp e .UNPACK_SEQUENCE ⟨regs, v :: rest⟩ = .error y ⟨{ regs with rt := rt5 }, rest⟩)

/-- The first loop of the unpacking helper over a chain of `k ≤ n` items. -/
theorem first_run (om : ObjModel) (ctx : Ctx) (it : Val) (n : Nat) (after : Option Nat)
    (rt1 rt2 : Rt) (xs : List Val) (hc : NextChain om ctx it rt1 xs rt2) (hn : xs.length ≤ n) :
    unpackIterable.first om ctx n after it n 0 [] rt1 =
      unpackIterable.first om ctx n after it (n - xs.length) xs.length xs.reverse rt2 := by
  have hf := first_chain om ctx n after it xs rt1 rt2 (n - xs.length) 0 [] hc
  have hn' : xs.length + (n - xs.length) = n := by omega
  rw [hn'] at hf
  simpa using hf

theorem unpackSeqRules_proven : UnpackSeqRules := by
  intro e regs v rest
  refine ⟨fun it rt1 xs rt2 rt3 h0 hc hend => ⟨fun hlen => ?_, fun hlt x rt4 hv => ?_⟩,
    fun it rt1 xs rt2 w rt3 msg h0 hc hlen hw hm x rt4 hv => ?_,
    fun it rt1 xs rt2 x rt3 h0 hc hle hx => ?_,
    fun x rt1 rt2 h0 hm => ?_, fun x rt1 rt2 rt3 h0 hm hi => ?_,
    fun x rt1 rt2 rt3 name rt4 y rt5 h0 hm hi hn ht => ?_⟩
  · have hr : unpackIterable e.om e.ctx v e.oparg none regs.rt = .ok xs rt3 := by
      simp only [unpackIterable, tryExc, h0, bind, EStateM.bind]
      rw [first_run e.om e.ctx it e.oparg none rt1 rt2 xs hc (by omega)]
      have hz : e.oparg - xs.length = 0 := by omega
      rw [hz]
      simp [unpackIterable.first, hend, pure, EStateM.pure]
    have hl : xs.reverse.length = e.oparg := by simp [hlen]
    bc_simp [execOp, UNPACK_SEQUENCE, _SPECIALIZE_UNPACK_SEQUENCE, _UNPACK_SEQUENCE, hr, hl]
  · have hr : unpackIterable e.om e.ctx v e.oparg none regs.rt = .error x rt4 := by
      simp only [unpackIterable, tryExc, h0, bind, EStateM.bind]
      rw [first_run e.om e.ctx it e.oparg none rt1 rt2 xs hc (by omega)]
      obtain ⟨m, hm⟩ : ∃ m, e.oparg - xs.length = m + 1 := ⟨e.oparg - xs.length - 1, by omega⟩
      rw [hm]
      simp at hv
      simp [unpackIterable.first, bind, EStateM.bind, hend, hv]
    bc_simp [execOp, UNPACK_SEQUENCE, _SPECIALIZE_UNPACK_SEQUENCE, _UNPACK_SEQUENCE, hr]
  · have hr : unpackIterable e.om e.ctx v e.oparg none regs.rt = .error x rt4 := by
      simp only [unpackIterable, tryExc, h0, bind, EStateM.bind]
      rw [first_run e.om e.ctx it e.oparg none rt1 rt2 xs hc (by omega)]
      have hz : e.oparg - xs.length = 0 := by omega
      rw [hz]
      simp only [unpackIterable.first, pure, EStateM.pure, hw]
      cases v with
      | ref a =>
        cases ho : rt3.heap[a]? with
        | none => simp [tooManyMsg, ho] at hm
        | some o =>
          cases o <;> simp [tooManyMsg, ho] at hm <;> subst hm <;>
            simp [getObj, ho, pure, EStateM.pure, bind, EStateM.bind] <;> (try split) <;> simp_all
      | _ =>
        simp [tooManyMsg] at hm
        subst hm
        simp [hv, pure, EStateM.pure, bind, EStateM.bind]
    bc_simp [execOp, UNPACK_SEQUENCE, _SPECIALIZE_UNPACK_SEQUENCE, _UNPACK_SEQUENCE, hr]
  · have hr : unpackIterable e.om e.ctx v e.oparg none regs.rt = .error x rt3 := by
      simp only [unpackIterable, tryExc, h0, bind, EStateM.bind]
      rw [first_run e.om e.ctx it e.oparg none rt1 rt2 xs hc hle]
      by_cases hz : e.oparg - xs.length = 0
      · rw [hz]; simp [unpackIterable.first, pure, EStateM.pure, hx]
      · obtain ⟨m, hm⟩ : ∃ m, e.oparg - xs.length = m + 1 := ⟨e.oparg - xs.length - 1, by omega⟩
        rw [hm]; simp [unpackIterable.first, bind, EStateM.bind, hx]
    bc_simp [execOp, UNPACK_SEQUENCE, _SPECIALIZE_UNPACK_SEQUENCE, _UNPACK_SEQUENCE, hr]
  · have hr : unpackIterable e.om e.ctx v e.oparg none regs.rt = .error (.exc x) rt2 := by
      simp [unpackIterable, tryExc, h0, bind, EStateM.bind, hm, throw, throwThe, MonadExcept.throw,
        EStateM.throw, MonadExceptOf.throw]
    bc_simp [execOp, UNPACK_SEQUENCE, _SPECIALIZE_UNPACK_SEQUENCE, _UNPACK_SEQUENCE, hr]
  · have hr : unpackIterable e.om e.ctx v e.oparg none regs.rt = .error (.exc x) rt3 := by
      simp [unpackIterable, tryExc, h0, bind, EStateM.bind, hm, hi, throw, throwThe, MonadExcept.throw,
        EStateM.throw, MonadExceptOf.throw]
    bc_simp [execOp, UNPACK_SEQUENCE, _SPECIALIZE_UNPACK_SEQUENCE, _UNPACK_SEQUENCE, hr]
  · have hr : unpackIterable e.om e.ctx v e.oparg none regs.rt = .error y rt5 := by
      simp [unpackIterable, tryExc, h0, bind, EStateM.bind, hm, hi, hn, ht, pure, EStateM.pure]
    bc_simp [execOp, UNPACK_SEQUENCE, _SPECIALIZE_UNPACK_SEQUENCE, _UNPACK_SEQUENCE, hr]

/-- The message of `:2385-2388` and `:2428-2430`. -/
def atLeastMsg (n k : Nat) : String := s!"not enough values to unpack (expected at least {n}, got {k})"

/-- `UNPACK_EX` with `oparg = before | after << 8` (`Python/bytecodes.c:2148-2153`, the
`argcntafter >= 0` paths of `Python/ceval.c:2380-2440`), for every object model, with
`PyObject_GetIter(v)` returning `it`: the first `before` items `xs` come out one call at a time,
then `PySequence_List(it)` drains the remaining items `ys` (up to the end, a call that returns
`NULL`). When `ys` has at least `after` items the stack gets, from the top, the `xs`, a new list of
all but the last `after` of the `ys`, and those last `after` items in order; otherwise
`ValueError("not enough values to unpack (expected at least before+after, got before+len(ys))")`.
When the iterator ends among the first `before` items, after `k` of them, the message is
`"... (expected at least before+after, got k)"`. `v` is popped on every error. The model's
`PySequence_List` is bounded at a million items (`ys.length < 1000000`); beyond that it stops
with fuel, which is not a Python outcome. -/
def UnpackExRules : Prop := ∀ (e : Env) (regs : Regs) (v : Val) (rest : List Val)
    (it : Val) (rt1 : Rt) (xs : List Val) (rt2 : Rt),
  e.om.getIter e.ctx v regs.rt = .ok it rt1 → NextChain e.om e.ctx it rt1 xs rt2 →
  (xs.length = e.oparg &&& 255 → ∀ ys rt3 rt4, NextChain e.om e.ctx it rt2 ys rt3 →
    iterNextOpt e.om e.ctx it rt3 = .ok none rt4 → ys.length < 1000000 →
    (e.oparg >>> 8 ≤ ys.length →
      execOp e .UNPACK_EX ⟨regs, v :: rest⟩ = .ok ()
        ⟨{ regs with rt := { rt4 with
            heap := (rt4.heap.push (Obj.list (ys.take (ys.length - (e.oparg >>> 8))).toArray)) } },
         xs ++ (Val.ref rt4.heap.size :: (ys.drop (ys.length - (e.oparg >>> 8)) ++ rest))⟩) ∧
    (ys.length < e.oparg >>> 8 → ∀ x rt5,
      valueError (α := Unit) (atLeastMsg ((e.oparg &&& 255) + (e.oparg >>> 8)) ((e.oparg &&& 255) + ys.length)) rt4 = .error x rt5 →
      execOp e .UNPACK_EX ⟨regs, v :: rest⟩ = .error x ⟨{ regs with rt := rt5 }, rest⟩)) ∧
  (xs.length < e.oparg &&& 255 → ∀ rt3, iterNextOpt e.om e.ctx it rt2 = .ok none rt3 → ∀ x rt4,
    valueError (α := List Val) (atLeastMsg ((e.oparg &&& 255) + (e.oparg >>> 8)) xs.length) rt3 = .error x rt4 →
    execOp e .UNPACK_EX ⟨regs, v :: rest⟩ = .error x ⟨{ regs with rt := rt4 }, rest⟩)

theorem unpackExRules_proven : UnpackExRules := by
  intro e regs v rest it rt1 xs rt2 h0 hc
  constructor
  · intro hlen ys rt3 rt4 hys hend hbound
    have hf := first_run e.om e.ctx it (e.oparg &&& 255) (some (e.oparg >>> 8)) rt1 rt2 xs hc (by omega)
    have hz : (e.oparg &&& 255) - xs.length = 0 := by omega
    rw [hz] at hf
    have hd := drain_chain e.om e.ctx it ys rt2 rt3 (1000000 - ys.length) [] hys
    have hd' : ys.length + (1000000 - ys.length) = 1000000 := by omega
    rw [hd'] at hd
    obtain ⟨k, hk⟩ : ∃ k, 1000000 - ys.length = k + 1 := ⟨1000000 - ys.length - 1, by omega⟩
    rw [hk] at hd
    have hdr : drain e.om e.ctx it 1000000 [] rt2 = .ok ys rt4 := by
      rw [hd]; simp [drain, bind, EStateM.bind, hend, pure, EStateM.pure]
    constructor
    · intro hge
      have hnlt : ¬ ys.length < e.oparg >>> 8 := by omega
      have hr : unpackIterable e.om e.ctx v (e.oparg &&& 255) (some (e.oparg >>> 8)) regs.rt =
          .ok (xs ++ [Val.ref rt4.heap.size] ++ ys.drop (ys.length - (e.oparg >>> 8)))
            { rt4 with heap := rt4.heap.push (.list (ys.take (ys.length - (e.oparg >>> 8))).toArray) } := by
        simp only [unpackIterable, tryExc, h0, bind, EStateM.bind]
        rw [hf]
        simp [unpackIterable.first, hdr, hnlt, pure, EStateM.pure, EStateM.bind, mkList, alloc]
      have hl : ys.length - (ys.length - (e.oparg >>> 8)) + (xs.length + 1) =
          (e.oparg &&& 255) + 1 + (e.oparg >>> 8) := by omega
      bc_simp [execOp, UNPACK_EX, hr, hl]
    · intro hlt x rt5 hv
      have hr : unpackIterable e.om e.ctx v (e.oparg &&& 255) (some (e.oparg >>> 8)) regs.rt = .error x rt5 := by
        simp only [unpackIterable, tryExc, h0, bind, EStateM.bind]
        rw [hf]
        simp [atLeastMsg] at hv
        simp [unpackIterable.first, hdr, hlt, hv, hlen, pure, EStateM.pure, EStateM.bind]
      bc_simp [execOp, UNPACK_EX, hr]
  · intro hlt rt3 hend x rt4 hv
    have hf := first_run e.om e.ctx it (e.oparg &&& 255) (some (e.oparg >>> 8)) rt1 rt2 xs hc (by omega)
    obtain ⟨m, hm⟩ : ∃ m, (e.oparg &&& 255) - xs.length = m + 1 := ⟨(e.oparg &&& 255) - xs.length - 1, by omega⟩
    rw [hm] at hf
    have hr : unpackIterable e.om e.ctx v (e.oparg &&& 255) (some (e.oparg >>> 8)) regs.rt = .error x rt4 := by
      simp only [unpackIterable, tryExc, h0, bind, EStateM.bind]
      simp [atLeastMsg] at hv
      rw [hf]; simp [unpackIterable.first, bind, EStateM.bind, hend, hv]
    bc_simp [execOp, UNPACK_EX, hr]

/-- The failure paths of `UNPACK_EX` that are not its own messages: `__next__` raising among the
first `before` items, or while `PySequence_List` drains the rest, and `PyObject_GetIter` raising
anything but a `TypeError`. Each propagates with `v` popped (`ERROR_IF(res == 0)`, `:2152`),
raised in the runtime the failing call left. -/
def UnpackExErrors : Prop := ∀ (e : Env) (regs : Regs) (v : Val) (rest : List Val),
  (∀ it rt1 xs rt2 x rt3, e.om.getIter e.ctx v regs.rt = .ok it rt1 → NextChain e.om e.ctx it rt1 xs rt2 →
    xs.length < e.oparg &&& 255 → iterNextOpt e.om e.ctx it rt2 = .error x rt3 →
    execOp e .UNPACK_EX ⟨regs, v :: rest⟩ = .error x ⟨{ regs with rt := rt3 }, rest⟩) ∧
  (∀ it rt1 xs rt2 ys rt3 x rt4, e.om.getIter e.ctx v regs.rt = .ok it rt1 →
    NextChain e.om e.ctx it rt1 xs rt2 → xs.length = e.oparg &&& 255 →
    NextChain e.om e.ctx it rt2 ys rt3 → ys.length < 1000000 → iterNextOpt e.om e.ctx it rt3 = .error x rt4 →
    execOp e .UNPACK_EX ⟨regs, v :: rest⟩ = .error x ⟨{ regs with rt := rt4 }, rest⟩) ∧
  (∀ x rt1 rt2, e.om.getIter e.ctx v regs.rt = .error (.exc x) rt1 →
    givenMatches x 8 (.cls "TypeError") rt1 = .ok false rt2 →
      execOp e .UNPACK_EX ⟨regs, v :: rest⟩ = .error (.exc x) ⟨{ regs with rt := rt2 }, rest⟩)

theorem unpackExErrors_proven : UnpackExErrors := by
  intro e regs v rest
  refine ⟨fun it rt1 xs rt2 x rt3 h0 hc hlt hx => ?_, fun it rt1 xs rt2 ys rt3 x rt4 h0 hc hlen hys hb hx => ?_,
    fun x rt1 rt2 h0 hm => ?_⟩
  · have hf := first_run e.om e.ctx it (e.oparg &&& 255) (some (e.oparg >>> 8)) rt1 rt2 xs hc (by omega)
    obtain ⟨m, hm⟩ : ∃ m, (e.oparg &&& 255) - xs.length = m + 1 := ⟨(e.oparg &&& 255) - xs.length - 1, by omega⟩
    rw [hm] at hf
    have hr : unpackIterable e.om e.ctx v (e.oparg &&& 255) (some (e.oparg >>> 8)) regs.rt = .error x rt3 := by
      simp only [unpackIterable, tryExc, h0, bind, EStateM.bind]
      rw [hf]; simp [unpackIterable.first, bind, EStateM.bind, hx]
    bc_simp [execOp, UNPACK_EX, hr]
  · have hf := first_run e.om e.ctx it (e.oparg &&& 255) (some (e.oparg >>> 8)) rt1 rt2 xs hc (by omega)
    have hz : (e.oparg &&& 255) - xs.length = 0 := by omega
    rw [hz] at hf
    have hd := drain_chain e.om e.ctx it ys rt2 rt3 (1000000 - ys.length) [] hys
    have hd' : ys.length + (1000000 - ys.length) = 1000000 := by omega
    rw [hd'] at hd
    obtain ⟨k, hk⟩ : ∃ k, 1000000 - ys.length = k + 1 := ⟨1000000 - ys.length - 1, by omega⟩
    rw [hk] at hd
    have hdr : drain e.om e.ctx it 1000000 [] rt2 = .error x rt4 := by
      rw [hd]; simp [drain, bind, EStateM.bind, hx]
    have hr : unpackIterable e.om e.ctx v (e.oparg &&& 255) (some (e.oparg >>> 8)) regs.rt = .error x rt4 := by
      simp only [unpackIterable, tryExc, h0, bind, EStateM.bind]
      rw [hf]
      simp [unpackIterable.first, hdr, pure, EStateM.pure, EStateM.bind]
    bc_simp [execOp, UNPACK_EX, hr]
  · have hr : unpackIterable e.om e.ctx v (e.oparg &&& 255) (some (e.oparg >>> 8)) regs.rt = .error (.exc x) rt2 := by
      simp [unpackIterable, tryExc, h0, bind, EStateM.bind, hm, throw, throwThe, MonadExcept.throw,
        EStateM.throw, MonadExceptOf.throw]
    bc_simp [execOp, UNPACK_EX, hr]

def UnpackExFull : Prop := UnpackExRules ∧ UnpackExErrors
theorem unpackExFull_proven : UnpackExFull := ⟨unpackExRules_proven, unpackExErrors_proven⟩

/-! ## The specialized forms -/

theorem withDeopt_of {m g : M Unit} {s s' : St} (h : m s = .error .deopt s') : withDeopt m g s = g s := by
  simp [withDeopt, h]

theorem withDeopt_ok {m g : M Unit} {s s' : St} (h : m s = .ok () s') : withDeopt m g s = .ok () s' := by
  simp [withDeopt, h]

/-- `UNPACK_SEQUENCE_TUPLE` (`Python/bytecodes.c:2099-2112`: `_GUARD_TOS_TUPLE` then
`_UNPACK_SEQUENCE_TUPLE`, `EXIT_IF(PyTuple_GET_SIZE(seq_o) != oparg)`), `UNPACK_SEQUENCE_LIST`
(`:2128-2146`, `DEOPT_IF` on the size) and `UNPACK_SEQUENCE_TWO_TUPLE` (`:2066-2078`, `EXIT_IF` on a
size other than 2): on an exact tuple (list) of exactly `oparg` items (two items) the items replace
it, item 0 on top (`for (i = oparg; --i >= 0;) *values++ = items[i]`); on any other value, an exact
tuple or list of another size included, the instruction is the generic `UNPACK_SEQUENCE` on the
same state. -/
def UnpackFast : Prop := ∀ (e : Env) (regs : Regs) (v : Val) (rest : List Val), Live regs.rt v →
  (∀ a items, v = .ref a → regs.rt.heap[a]? = some (.tuple items) → items.size = e.oparg →
    execOp e .UNPACK_SEQUENCE_TUPLE ⟨regs, v :: rest⟩ = .ok () ⟨regs, items.toList ++ rest⟩) ∧
  ((¬ ∃ a items, v = .ref a ∧ regs.rt.heap[a]? = some (.tuple items) ∧ items.size = e.oparg) →
    execOp e .UNPACK_SEQUENCE_TUPLE ⟨regs, v :: rest⟩ = execOp e .UNPACK_SEQUENCE ⟨regs, v :: rest⟩) ∧
  (∀ a items, v = .ref a → regs.rt.heap[a]? = some (.list items) → items.size = e.oparg →
    execOp e .UNPACK_SEQUENCE_LIST ⟨regs, v :: rest⟩ = .ok () ⟨regs, items.toList ++ rest⟩) ∧
  ((¬ ∃ a items, v = .ref a ∧ regs.rt.heap[a]? = some (.list items) ∧ items.size = e.oparg) →
    execOp e .UNPACK_SEQUENCE_LIST ⟨regs, v :: rest⟩ = execOp e .UNPACK_SEQUENCE ⟨regs, v :: rest⟩) ∧
  (∀ a items, v = .ref a → regs.rt.heap[a]? = some (.tuple items) → items.size = 2 →
    execOp e .UNPACK_SEQUENCE_TWO_TUPLE ⟨regs, v :: rest⟩ = .ok () ⟨regs, items.toList ++ rest⟩) ∧
  ((¬ ∃ a items, v = .ref a ∧ regs.rt.heap[a]? = some (.tuple items) ∧ items.size = 2) →
    execOp e .UNPACK_SEQUENCE_TWO_TUPLE ⟨regs, v :: rest⟩ = execOp e .UNPACK_SEQUENCE ⟨regs, v :: rest⟩)

theorem unpackFast_proven : UnpackFast := by
  intro e regs v rest hl
  have gT := guardRules_proven.2.2.2.2.2.2.2.2.2.2.2.1 regs rest v hl
  have gL := guardRules_proven.2.2.2.2.2.2.2.1 regs rest v hl
  refine ⟨fun a items hv ho hn => ?_, fun hn => ?_, fun a items hv ho hn => ?_, fun hn => ?_,
    fun a items hv ho hn => ?_, fun hn => ?_⟩
  · subst hv
    have g1 := gT.1 ⟨a, items, rfl, ho⟩
    have hb : (items.size != e.oparg) = false := by simp [hn]
    have hl' : items.toList.reverse.length = e.oparg := by simp [hn]
    simp only [execOp]
    apply withDeopt_ok
    simp only [UNPACK_SEQUENCE_TUPLE, bind, EStateM.bind, g1]
    bc_simp [_UNPACK_SEQUENCE_TUPLE, ho, hb, hl']
  · simp only [execOp]
    by_cases ht : IsTuple regs.rt v
    · obtain ⟨a, items, rfl, ho⟩ := ht
      have g1 := gT.1 ⟨a, items, rfl, ho⟩
      have hne : items.size ≠ e.oparg := fun h => hn ⟨a, items, rfl, ho, h⟩
      have hb : (items.size != e.oparg) = true := by simpa using hne
      refine withDeopt_of (s' := ⟨regs, rest⟩) ?_
      simp only [UNPACK_SEQUENCE_TUPLE, bind, EStateM.bind, g1]
      bc_simp [_UNPACK_SEQUENCE_TUPLE, ho, hb]
    · exact withDeopt_of (s' := ⟨regs, v :: rest⟩)
        (by simp only [UNPACK_SEQUENCE_TUPLE, bind, EStateM.bind, gT.2 ht])
  · subst hv
    have g1 := gL.1 ⟨a, items, rfl, ho⟩
    have hb : (items.size != e.oparg) = false := by simp [hn]
    have hl' : items.toList.reverse.length = e.oparg := by simp [hn]
    simp only [execOp]
    apply withDeopt_ok
    simp only [UNPACK_SEQUENCE_LIST, bind, EStateM.bind, g1]
    bc_simp [_UNPACK_SEQUENCE_LIST, ho, hb, hl']
  · simp only [execOp]
    by_cases ht : IsList regs.rt v
    · obtain ⟨a, items, rfl, ho⟩ := ht
      have g1 := gL.1 ⟨a, items, rfl, ho⟩
      have hne : items.size ≠ e.oparg := fun h => hn ⟨a, items, rfl, ho, h⟩
      have hb : (items.size != e.oparg) = true := by simpa using hne
      refine withDeopt_of (s' := ⟨regs, rest⟩) ?_
      simp only [UNPACK_SEQUENCE_LIST, bind, EStateM.bind, g1]
      bc_simp [_UNPACK_SEQUENCE_LIST, ho, hb]
    · exact withDeopt_of (s' := ⟨regs, v :: rest⟩)
        (by simp only [UNPACK_SEQUENCE_LIST, bind, EStateM.bind, gL.2 ht])
  · subst hv
    have g1 := gT.1 ⟨a, items, rfl, ho⟩
    have hb : (items.size != 2) = false := by simp [hn]
    have h2 : [items.getD 0 .null, items.getD 1 .null] = items.toList := by
      rcases items with ⟨l⟩
      match l, hn with
      | [x, y], _ => rfl
    simp only [execOp]
    apply withDeopt_ok
    simp only [UNPACK_SEQUENCE_TWO_TUPLE, bind, EStateM.bind, g1]
    bc_simp [_UNPACK_SEQUENCE_TWO_TUPLE, ho, hb, ← h2]
  · simp only [execOp]
    by_cases ht : IsTuple regs.rt v
    · obtain ⟨a, items, rfl, ho⟩ := ht
      have g1 := gT.1 ⟨a, items, rfl, ho⟩
      have hne : items.size ≠ 2 := fun h => hn ⟨a, items, rfl, ho, h⟩
      have hb : (items.size != 2) = true := by simpa using hne
      refine withDeopt_of (s' := ⟨regs, rest⟩) ?_
      simp only [UNPACK_SEQUENCE_TWO_TUPLE, bind, EStateM.bind, g1]
      bc_simp [_UNPACK_SEQUENCE_TWO_TUPLE, ho, hb]
    · exact withDeopt_of (s' := ⟨regs, v :: rest⟩)
        (by simp only [UNPACK_SEQUENCE_TWO_TUPLE, bind, EStateM.bind, gT.2 ht])

def UnpackRules : Prop := UnpackSeqRules ∧ UnpackFast
theorem unpackRules_proven : UnpackRules := ⟨unpackSeqRules_proven, unpackFast_proven⟩

end PyLean.Bytecode
