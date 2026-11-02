import PyLean.CoreLibs.Misc.HeapP

/-!
`Lib/queue.py`, CPython 3.14.7, single-threaded outcomes.

`Queue` is generic in the representation `ρ` through `Impl`, which is the four override points
`_init`, `_qsize`, `_put`, `_get` of Lib/queue.py:258-275. `Queue`, `PriorityQueue` and `LifoQueue`
are the instances `fifo`, `prio` and `lifo`, over any item type; `PriorityQueue` takes the item
comparison `lt`, which can raise.

No other thread exists, so a `Condition.wait()` without timeout never returns: that outcome is the
marker exception `blocksForever`, which is not a Python exception (the difftest predicts it and does
not make the call). `wait(remaining)` returns after `remaining` has passed, which is the only effect
it has here: `now` is the value of `time()`. Mutex and notify calls have no single-threaded effect.
A timeout is an `Int`, in arbitrary units, because `queue.py` only compares it with 0 and adds it to
`time()`.
-/

namespace PyLean.CoreLibs.Misc.Queue

open PyLean PyLean.Accel

/-- Not a Python outcome: the call waits on a condition that only another thread could notify. -/
def blocksForever : PyExc := .named "<blocks forever>" ""

def full : PyExc := .named "Full" ""
def empty : PyExc := .named "Empty" ""
def shutDown : PyExc := .named "ShutDown" ""
def negTimeout : PyExc := .valueError "'timeout' must be a non-negative number"

/-- The override points of Lib/queue.py:258-275. -/
structure Impl (α ρ : Type) where
  init : Int → ρ
  qsize : ρ → Nat
  put : ρ → α → ρ × Py Unit
  get : ρ → ρ × Py α

/-- `Queue._init`, `_qsize`, `_put`, `_get`, Lib/queue.py:263-275: a deque. -/
def fifo {α : Type} : Impl α (List α) where
  init := fun _ => []
  qsize := fun q => q.length
  put := fun q item => (q ++ [item], .ok ())
  get := fun q => match q with
    | [] => ([], .error (.indexError "pop from an empty deque"))
    | a :: rest => (rest, .ok a)

/-- `LifoQueue._init`, `_qsize`, `_put`, `_get`, Lib/queue.py:302-312: a list used as a stack. -/
def lifo {α : Type} : Impl α (List α) where
  init := fun _ => []
  qsize := fun q => q.length
  put := fun q item => (q ++ [item], .ok ())
  get := fun q => match q.getLast? with
    | none => ([], .error (.indexError "pop from empty list"))
    | some a => (q.dropLast, .ok a)

/-- `PriorityQueue._init`, `_qsize`, `_put`, `_get`, Lib/queue.py:286-296: a heap. -/
def prio {α : Type} [Inhabited α] (lt : LtP α) : Impl α (List α) where
  init := fun _ => []
  qsize := fun q => q.length
  put := fun q item =>
    match heappushP lt q item with
    | (q, some e) => (q, .error e)
    | (q, none) => (q, .ok ())
  get := fun q => heappopP lt q

/-- The attributes of `Queue`, Lib/queue.py:46-70. `now` is the value `time()` would return. -/
structure Q (ρ : Type) where
  maxsize : Int
  queue : ρ
  unfinished : Int
  isShutdown : Bool
  now : Int
  deriving Repr

variable {α ρ : Type}

/-- `Queue.__init__`, Lib/queue.py:46-70. -/
def init (I : Impl α ρ) (maxsize : Int) : Q ρ :=
  { maxsize, queue := I.init maxsize, unfinished := 0, isShutdown := false, now := 0 }

/-- `Queue.task_done`, Lib/queue.py:72-92. -/
def taskDone (q : Q ρ) : Q ρ × Py Unit :=
  let unfinished := q.unfinished - 1
  if unfinished ≤ 0 ∧ unfinished < 0 then
    (q, .error (.valueError "task_done() called too many times"))
  else ({ q with unfinished }, .ok ())

/-- `Queue.join`, Lib/queue.py:94-105. -/
def join (q : Q ρ) : Py Unit :=
  if q.unfinished ≠ 0 then .error blocksForever else .ok ()

/-- `Queue.qsize`, Lib/queue.py:107-110. -/
def qsize (I : Impl α ρ) (q : Q ρ) : Nat := I.qsize q.queue

/-- `Queue.empty`, Lib/queue.py:112-124. -/
def isEmpty (I : Impl α ρ) (q : Q ρ) : Bool := I.qsize q.queue == 0

/-- `Queue.full`, Lib/queue.py:126-135. -/
def isFull (I : Impl α ρ) (q : Q ρ) : Bool :=
  decide (0 < q.maxsize) && decide (q.maxsize ≤ (I.qsize q.queue : Int))

/-- The timed wait of `put`, Lib/queue.py:165-172, and of `get`, :205-212: the loop runs while the
blocking condition holds, and with no other thread that condition stays true. The first pass
computes `remaining = timeout`. If it is positive the wait consumes it and the second pass raises.
The state is unchanged except for `now`. -/
def timedOut (q : Q ρ) (timeout : Int) (exc : PyExc) : Q ρ × Py Unit :=
  let endtime := q.now + timeout
  let remaining := endtime - q.now
  if remaining ≤ 0 then (q, .error exc)
  else ({ q with now := q.now + remaining }, .error exc)

/-- The tail of `put`, Lib/queue.py:173-175. -/
def putTail (I : Impl α ρ) (q : Q ρ) (item : α) : Q ρ × Py Unit :=
  match I.put q.queue item with
  | (r, .error e) => ({ q with queue := r }, .error e)
  | (r, .ok ()) => ({ q with queue := r, unfinished := q.unfinished + 1 }, .ok ())

/-- `Queue.put`, Lib/queue.py:137-175. -/
def put (I : Impl α ρ) (q : Q ρ) (item : α) (block : Bool := true) (timeout : Option Int := none) :
    Q ρ × Py Unit :=
  if q.isShutdown then (q, .error shutDown)
  else if q.maxsize > 0 then
    if !block then
      if (I.qsize q.queue : Int) ≥ q.maxsize then (q, .error full)
      else putTail I q item
    else
      match timeout with
      | none =>
        if (I.qsize q.queue : Int) ≥ q.maxsize then (q, .error blocksForever)
        else putTail I q item
      | some t =>
        if t < 0 then (q, .error negTimeout)
        else if (I.qsize q.queue : Int) ≥ q.maxsize then timedOut q t full
        else putTail I q item
  else putTail I q item

/-- The tail of `get`, Lib/queue.py:213-215. -/
def getTail (I : Impl α ρ) (q : Q ρ) : Q ρ × Py α :=
  match I.get q.queue with
  | (r, x) => ({ q with queue := r }, x)

/-- Lift the `Py Unit` of `timedOut`, which is always an exception, to any result type. -/
def timedOut' {β : Type} (r : Q ρ × Py Unit) : Q ρ × Py β :=
  match r with
  | (q, .error e) => (q, .error e)
  | (q, .ok ()) => (q, .error .modelFuel)

/-- `Queue.get`, Lib/queue.py:177-215. -/
def get (I : Impl α ρ) (q : Q ρ) (block : Bool := true) (timeout : Option Int := none) :
    Q ρ × Py α :=
  if q.isShutdown ∧ I.qsize q.queue = 0 then (q, .error shutDown)
  else if !block then
    if I.qsize q.queue = 0 then (q, .error empty)
    else getTail I q
  else
    match timeout with
    | none =>
      if I.qsize q.queue = 0 then (q, .error blocksForever)
      else getTail I q
    | some t =>
      if t < 0 then (q, .error negTimeout)
      else if I.qsize q.queue = 0 then timedOut' (timedOut q t empty)
      else getTail I q

/-- `Queue.put_nowait`, Lib/queue.py:217-223. -/
def putNowait (I : Impl α ρ) (q : Q ρ) (item : α) : Q ρ × Py Unit := put I q item false

/-- `Queue.get_nowait`, Lib/queue.py:225-231. -/
def getNowait (I : Impl α ρ) (q : Q ρ) : Q ρ × Py α := get I q false

/-- The `while self._qsize():` loop of `shutdown`, Lib/queue.py:248-251. An exception from `_get`
(a `PriorityQueue` comparison) escapes with `is_shutdown` already set. -/
def drain (I : Impl α ρ) : Nat → Q ρ → Q ρ × Py Unit
  | 0, q => (q, .error .modelFuel)
  | fuel + 1, q =>
    if I.qsize q.queue ≠ 0 then
      match I.get q.queue with
      | (r, .error e) => ({ q with queue := r }, .error e)
      | (r, .ok _) =>
        let q := { q with queue := r }
        let q := if q.unfinished > 0 then { q with unfinished := q.unfinished - 1 } else q
        drain I fuel q
    else (q, .ok ())

/-- `Queue.shutdown`, Lib/queue.py:233-256. `_get` shrinks the queue by one each pass, so
`qsize + 1` iterations are enough. -/
def shutdown (I : Impl α ρ) (q : Q ρ) (immediate : Bool := false) : Q ρ × Py Unit :=
  let q := { q with isShutdown := true }
  if immediate then drain I (I.qsize q.queue + 1) q else (q, .ok ())

/-! ### `threading.Semaphore.acquire` and `_PySimpleQueue` -/

/-- The `while self._value == 0:` loop of `Semaphore.acquire`, Lib/threading.py:506-520, entered
with `_value == 0` and a timeout. No other thread can raise the value, so the loop leaves through
`break` on its second pass, when `endtime - _time()` has dropped to 0 because `wait(timeout)`
consumed the timeout. The result is the clock after the loop. -/
def semTimedWait (now timeout : Int) : Int :=
  if timeout > 0 then now + timeout else now

/-- `Semaphore.acquire(blocking, timeout)`, Lib/threading.py:477-520: the new value, the clock and
the result. -/
def semAcquire (value now : Int) (blocking : Bool) (timeout : Option Int) : Py (Int × Int × Bool) :=
  if !blocking ∧ timeout.isSome then
    .error (.valueError "can't specify timeout for non-blocking acquire")
  else if value = 0 then
    if !blocking then .ok (value, now, false)
    else match timeout with
      | none => .error blocksForever
      | some t => .ok (value, semTimedWait now t, false)
  else .ok (value - 1, now, true)

/-- The attributes of `_PySimpleQueue`, Lib/queue.py:325-327. -/
structure PySQ (α : Type) where
  queue : List α
  count : Int
  now : Int
  deriving Repr

/-- `_PySimpleQueue.__init__`, Lib/queue.py:325-327. -/
def PySQ.init : PySQ α := { queue := [], count := 0, now := 0 }

/-- `_PySimpleQueue.put`, Lib/queue.py:329-336; `block` and `timeout` are ignored. -/
def PySQ.put (q : PySQ α) (item : α) (_block : Bool := true) (_timeout : Option Int := none) :
    PySQ α :=
  { q with queue := q.queue ++ [item], count := q.count + 1 }

/-- `_PySimpleQueue.get`, Lib/queue.py:338-355. With `block` false the timeout is dropped first, :349-350. -/
def PySQ.get (q : PySQ α) (block : Bool := true) (timeout : Option Int := none) :
    PySQ α × Py α :=
  let timeout := if block then timeout else none
  if timeout.isSome ∧ (timeout.getD 0) < 0 then (q, .error negTimeout)
  else
    match semAcquire q.count q.now block timeout with
    | .error e => (q, .error e)
    | .ok (count, now, rc) =>
      let q := { q with count, now }
      if !rc then (q, .error empty)
      else
        match q.queue with
        | [] => (q, .error (.indexError "pop from an empty deque"))
        | a :: rest => ({ q with queue := rest }, .ok a)

/-- `_PySimpleQueue.put_nowait`, Lib/queue.py:357-363. -/
def PySQ.putNowait (q : PySQ α) (item : α) : PySQ α := q.put item false

/-- `_PySimpleQueue.get_nowait`, Lib/queue.py:365-371. -/
def PySQ.getNowait (q : PySQ α) : PySQ α × Py α := q.get false

/-- `_PySimpleQueue.empty`, Lib/queue.py:373-375. -/
def PySQ.isEmpty (q : PySQ α) : Bool := q.queue.length == 0

/-- `_PySimpleQueue.qsize`, Lib/queue.py:377-379. -/
def PySQ.qsize (q : PySQ α) : Nat := q.queue.length

/-! ### `_queue.SimpleQueue`, the C twin -/

/-- `_queue_SimpleQueue_put_impl`, Modules/_queuemodule.c:302-318. -/
def cPut (q : List α) (item : α) : List α := q ++ [item]

/-- `_queue_SimpleQueue_get_impl`, Modules/_queuemodule.c:377-454: the timeout is looked at only
when `block` is true (:385). -/
def cGet (q : List α) (block : Bool := true) (timeout : Option Int := none) : List α × Py α :=
  let check : Py Unit :=
    if block ∧ timeout.isSome ∧ (timeout.getD 0) < 0 then .error negTimeout else .ok ()
  match check with
  | .error e => (q, .error e)
  | .ok () =>
    match q with
    | a :: rest => (rest, .ok a)
    | [] =>
      if !block then ([], .error empty)
      else match timeout with
        | some _ => ([], .error empty)
        | none => ([], .error blocksForever)

end PyLean.CoreLibs.Misc.Queue
