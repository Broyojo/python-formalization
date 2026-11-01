import PyLean.CoreLibs.Misc.HeapP

/-!
`Lib/sched.py`, CPython 3.14.7: `scheduler`.

Generic over the time type `T` ("Numeric type compatible with the return value of the timefunc
function", Lib/sched.py:36), the priority type `P`, the action type `A`, the argument values `V`
and a world `W` that `timefunc`, `delayfunc` and the actions run in. `Env` holds what `sched.py`
receives from outside: the comparisons, the arithmetic, the two clock functions and the way to call
an action. An action gets the scheduler's state because "It is legal for both the delay function
and the action function to modify the queue" (Lib/sched.py:116-117).

`Lock` acquisition has no effect in a single thread and is dropped. Events are ordered as Python
orders tuples: the first field that differs under `==` decides under `<`.
-/

namespace PyLean.CoreLibs.Misc.Sched

open PyLean PyLean.Accel

/-- The `Event` namedtuple, Lib/sched.py:35. -/
structure Event (T P A V : Type) where
  time : T
  priority : P
  sequence : Nat
  action : A
  argument : List V
  kwargs : List (String × V)
  deriving Repr, DecidableEq, Inhabited

/-- The attributes of a `scheduler`, Lib/sched.py:53-60. `seq` is the next value of
`_sequence_generator`. -/
structure Sched (T P A V W : Type) where
  queue : List (Event T P A V)
  seq : Nat
  world : W
  deriving Repr

/-- `__eq__` and `__lt__` of a field type. -/
structure Cmp (T : Type) where
  eq : T → T → Py Bool
  lt : T → T → Py Bool

/-- What `sched.py` gets from outside. -/
structure Env (T P A V W : Type) where
  ct : Cmp T
  cp : Cmp P
  /-- `time > now`, Lib/sched.py:141. -/
  gt : T → T → Py Bool
  /-- `time - now`, Lib/sched.py:148-149. -/
  sub : T → T → Py T
  /-- `self.timefunc() + delay`, Lib/sched.py:84. -/
  add : T → T → Py T
  /-- The int `0` passed to `delayfunc` at Lib/sched.py:152. -/
  zero : T
  timefunc : W → W × Py T
  delayfunc : W → T → W × Py Unit
  /-- `action(*argument, **kwargs)`, Lib/sched.py:151. -/
  call : A → List V → List (String × V) → Sched T P A V W → Sched T P A V W × Py Unit
  /-- `==` on the remaining fields, used by `cancel`'s `list.remove`. -/
  eqRest : Event T P A V → Event T P A V → Bool

variable {T P A V W : Type}

/-- Tuple `<` on events, `tuplerichcompare`, Objects/tupleobject.c. `sequence` is unique within a
scheduler, so comparison never goes past it. -/
def eventLt (e : Env T P A V W) (a b : Event T P A V) : Py Bool := do
  if ← e.ct.eq a.time b.time then
    if ← e.cp.eq a.priority b.priority then
      return decide (a.sequence < b.sequence)
    else e.cp.lt a.priority b.priority
  else e.ct.lt a.time b.time

/-- `scheduler.__init__`, Lib/sched.py:53-60. -/
def init (w : W) : Sched T P A V W := { queue := [], seq := 0, world := w }

/-- `scheduler.enterabs`, Lib/sched.py:62-76. `kwargs = none` is the `_sentinel` default. The
sequence number is consumed and the event is in the list before `heappush` compares anything, so
both survive a comparison that raises. -/
def enterabs [Inhabited T] [Inhabited P] [Inhabited A] (e : Env T P A V W) (s : Sched T P A V W)
    (time : T) (priority : P) (action : A) (argument : List V)
    (kwargs : Option (List (String × V))) : Sched T P A V W × Py (Event T P A V) :=
  let kwargs := kwargs.getD []
  let event : Event T P A V :=
    { time, priority, sequence := s.seq, action, argument, kwargs }
  let (q, exc) := heappushP (eventLt e) s.queue event
  let s := { s with queue := q, seq := s.seq + 1 }
  match exc with
  | some x => (s, .error x)
  | none => (s, .ok event)

/-- `scheduler.enter`, Lib/sched.py:78-85. -/
def enter [Inhabited T] [Inhabited P] [Inhabited A] (e : Env T P A V W) (s : Sched T P A V W)
    (delay : T) (priority : P) (action : A) (argument : List V)
    (kwargs : Option (List (String × V))) : Sched T P A V W × Py (Event T P A V) :=
  let (w, now) := e.timefunc s.world
  let s := { s with world := w }
  match now with
  | .error x => (s, .error x)
  | .ok now =>
    match e.add now delay with
    | .error x => (s, .error x)
    | .ok time => enterabs e s time priority action argument kwargs

/-- Tuple `==` on events, with the identity shortcut of `list.remove` carried by equal fields. -/
def eventEq (e : Env T P A V W) (a b : Event T P A V) : Py Bool := do
  if ← e.ct.eq a.time b.time then
    if ← e.cp.eq a.priority b.priority then
      return decide (a.sequence = b.sequence) && e.eqRest a b
    else return false
  else return false

/-- `list.remove`, Objects/listobject.c:3425-3445: drop the first element equal to `x`. -/
def listRemove (e : Env T P A V W) (x : Event T P A V) :
    List (Event T P A V) → Py (List (Event T P A V))
  | [] => .error (.valueError "list.remove(x): x not in list")
  | a :: rest => do
    if ← eventEq e a x then return rest
    else return a :: (← listRemove e x rest)

/-- `scheduler.cancel`, Lib/sched.py:87-96. -/
def cancel [Inhabited T] [Inhabited P] [Inhabited A] (e : Env T P A V W) (s : Sched T P A V W)
    (event : Event T P A V) : Sched T P A V W × Py Unit :=
  match listRemove e event s.queue with
  | .error x => (s, .error x)
  | .ok q =>
    let (q, exc) := heapifyP (eventLt e) q
    let s := { s with queue := q }
    match exc with
    | some x => (s, .error x)
    | none => (s, .ok ())

/-- `scheduler.empty`, Lib/sched.py:98-101. -/
def empty (s : Sched T P A V W) : Bool := s.queue.isEmpty

/-- The `while True:` loop of `scheduler.run`, Lib/sched.py:134-152. -/
def runLoop [Inhabited T] [Inhabited P] [Inhabited A] (e : Env T P A V W) (blocking : Bool) :
    Nat → Sched T P A V W → Sched T P A V W × Py (Option T)
  | 0, s => (s, .error .modelFuel)
  | fuel + 1, s =>
    match s.queue with
    | [] => (s, .ok none)
    | ev :: _ =>
      let (w, now) := e.timefunc s.world
      let s := { s with world := w }
      match now with
      | .error x => (s, .error x)
      | .ok now =>
        match e.gt ev.time now with
        | .error x => (s, .error x)
        | .ok true =>
          if !blocking then
            match e.sub ev.time now with
            | .error x => (s, .error x)
            | .ok d => (s, .ok (some d))
          else
            match e.sub ev.time now with
            | .error x => (s, .error x)
            | .ok d =>
              let (w, r) := e.delayfunc s.world d
              let s := { s with world := w }
              match r with
              | .error x => (s, .error x)
              | .ok () => runLoop e blocking fuel s
        | .ok false =>
          let (q, r) := heappopP (eventLt e) s.queue
          let s := { s with queue := q }
          match r with
          | .error x => (s, .error x)
          | .ok _ =>
            match e.call ev.action ev.argument ev.kwargs s with
            | (s, .error x) => (s, .error x)
            | (s, .ok ()) =>
              let (w, r) := e.delayfunc s.world e.zero
              let s := { s with world := w }
              match r with
              | .error x => (s, .error x)
              | .ok () => runLoop e blocking fuel s

/-- `scheduler.run`, Lib/sched.py:103-152. The value is what `run` returns: `None` on `break`, the
remaining delay when not blocking. -/
def run [Inhabited T] [Inhabited P] [Inhabited A] (e : Env T P A V W) (fuel : Nat)
    (s : Sched T P A V W) (blocking : Bool) : Sched T P A V W × Py (Option T) :=
  runLoop e blocking fuel s

/-- `scheduler.queue`, Lib/sched.py:154-167: `list(map(heapq.heappop, [events]*len(events)))` on
a copy of the heap. -/
def queue [Inhabited T] [Inhabited P] [Inhabited A] (e : Env T P A V W) (s : Sched T P A V W) :
    Py (List (Event T P A V)) :=
  popsP (eventLt e) s.queue.length s.queue

end PyLean.CoreLibs.Misc.Sched
