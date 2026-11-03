import PyLean.PyIO.BufChecks

/-!
The lock of `Modules/_io/bufferedio.c` (`ENTER_BUFFERED`/`LEAVE_BUFFERED`,
:329-338, and `_enter_buffered_busy`, :294-327) over the bodies of the methods:
every method of `BufferedReader`, `BufferedWriter` and `BufferedRandom`, on every
state, raw stream and re-entered call, ends with the lock as it found it, unless
the process died; and a call that needs the lock while this thread holds it is
refused with `RuntimeError("reentrant call inside <...>")` and changes nothing.
-/

namespace PyLean.PyIO

open PyLean

namespace BC2

/-- The lock is as it was (the same lock, held or not as before), or `__init__`
replaced it by a new, free one, or the process died (then the call raised). -/
def LInv {α : Type} (s s' : BufS) (r : Py α) : Prop :=
  (s'.crashed = true ∧ ∃ e, r = .error e) ∨
  (s'.locked = s.locked ∧ s'.lockGen = s.lockGen) ∨
  (s.lockGen < s'.lockGen ∧ s'.locked = false)

/-- A handler for re-entered calls that keeps the lock. -/
def RK (R : CH) : Prop := ∀ op s, LInv s (R op s).1 (R op s).2

/-- `m` keeps the lock whenever re-entered calls do. -/
structure Keeps {α : Type} (m : BM α) : Prop where
  run : ∀ R, RK R → ∀ s, LInv s (m R s).1 (m R s).2

theorem bind_err {α β : Type} {m : BM α} {f : α → BM β} {R : CH} {s s1 : BufS} {e : PyExc}
    (h : m R s = (s1, .error e)) : (m >>= f) R s = (s1, .error e) := by
  show (match m R s with | (s', .ok a) => f a R s' | (s', .error e) => (s', .error e)) = _
  rw [h]

theorem linv_same {α : Type} (s : BufS) (r : Py α) : LInv s s r := .inr (.inl ⟨rfl, rfl⟩)

theorem keeps_pure {α : Type} (a : α) : Keeps (pure a : BM α) := ⟨fun _ _ s => linv_same s _⟩
theorem keeps_get : Keeps get := ⟨fun _ _ s => linv_same s _⟩
theorem keeps_thr {α : Type} (e : PyExc) : Keeps (thr e : BM α) := ⟨fun _ _ s => linv_same s _⟩
theorem keeps_ofPy {α : Type} (r : Py α) : Keeps (ofPy r : BM α) := ⟨fun _ _ s => linv_same s _⟩

theorem keeps_mod {f : BufS → BufS} (hf : ∀ s, (f s).locked = s.locked ∧ (f s).lockGen = s.lockGen) :
    Keeps (mod f) := ⟨fun _ _ s => .inr (.inl (hf s))⟩

/-- A new lock, free (`_buffered_init`, :853-860). -/
theorem keeps_relock {f : BufS → BufS} (hf : ∀ s, (f s).lockGen = s.lockGen + 1 ∧ (f s).locked = false) :
    Keeps (mod f) := ⟨fun _ _ s => .inr (.inr ⟨show s.lockGen < (f s).lockGen by rw [(hf s).1]; omega, (hf s).2⟩)⟩

theorem linv_trans {α β : Type} {s s1 s2 : BufS} {a : α} {r : Py β}
    (h1 : LInv s s1 (.ok a : Py α)) (h2 : LInv s1 s2 r) : LInv s s2 r := by
  rcases h1 with ⟨_, e, he⟩ | ⟨l1, g1⟩ | ⟨g1, l1⟩
  · cases he
  · rcases h2 with h2 | ⟨l2, g2⟩ | ⟨g2, l2⟩
    · exact .inl h2
    · exact .inr (.inl ⟨l2.trans l1, g2.trans g1⟩)
    · exact .inr (.inr ⟨by omega, l2⟩)
  · rcases h2 with h2 | ⟨l2, g2⟩ | ⟨g2, l2⟩
    · exact .inl h2
    · exact .inr (.inr ⟨by omega, l2.trans l1⟩)
    · exact .inr (.inr ⟨by omega, l2⟩)

theorem linv_err {α β : Type} {s s1 : BufS} {e : PyExc} (h : LInv s s1 (.error e : Py α)) :
    LInv s s1 (.error e : Py β) := by
  rcases h with ⟨hc, _, _⟩ | h | h
  · exact .inl ⟨hc, e, rfl⟩
  · exact .inr (.inl h)
  · exact .inr (.inr h)

theorem keeps_bind {α β : Type} {m : BM α} {f : α → BM β} (hm : Keeps m) (hf : ∀ a, Keeps (f a)) :
    Keeps (m >>= f) := by
  constructor
  intro R hR s
  have h1 := hm.run R hR s
  rcases hms : m R s with ⟨s1, r1⟩
  rw [hms] at h1
  cases r1 with
  | error e =>
    rw [bind_err hms]
    exact linv_err h1
  | ok a =>
    rw [bind_of_ok hms]
    exact linv_trans h1 ((hf a).run R hR s1)

theorem keeps_ite {α : Type} {c : Prop} [Decidable c] {a b : BM α} (ha : Keeps a) (hb : Keeps b) :
    Keeps (if c then a else b) := by
  split
  · exact ha
  · exact hb

theorem keeps_attempt {α : Type} {m : BM α} (hm : Keeps m) : Keeps (attempt m) := by
  constructor
  intro R hR s
  have h1 := hm.run R hR s
  unfold attempt
  rcases hms : m R s with ⟨s1, r1⟩
  rw [hms] at h1
  dsimp only
  split
  · next hc =>
    rcases h1 with ⟨_, e, he⟩ | h1 | h1
    · subst he; exact .inl ⟨hc, e, rfl⟩
    · exact .inr (.inl h1)
    · exact .inr (.inr h1)
  · next hc =>
    rcases h1 with ⟨h, _⟩ | h1 | h1
    · exact absurd h hc
    · exact .inr (.inl h1)
    · exact .inr (.inr h1)

theorem keeps_crash {α : Type} : Keeps (crash : BM α) := ⟨fun _ _ _ => .inl ⟨rfl, _, rfl⟩⟩
theorem keeps_hangC {α : Type} : Keeps (hangC : BM α) := ⟨fun _ _ _ => .inl ⟨rfl, _, rfl⟩⟩

theorem enter_held (R : CH) (s : BufS) (h : s.locked = true) :
    enter R s = (s, .error (.named "RuntimeError" s!"reentrant call inside {reprC s}")) := by
  rcases s with ⟨raw, ok, det, rn, rd, wr, lk, ap, hb, buf, pos, rp, re, wp, we, sz, cr, lg, mk, bl⟩
  simp only at h
  subst h
  rfl

theorem enter_free (R : CH) (s : BufS) (h : s.locked = false) :
    enter R s = ({ s with locked := true }, .ok ()) := by
  rcases s with ⟨raw, ok, det, rn, rd, wr, lk, ap, hb, buf, pos, rp, re, wp, we, sz, cr, lg, mk, bl⟩
  simp only at h
  subst h
  rfl

/-- A locked section keeps the lock whatever its body does: refused while held;
otherwise released on every path, and if `__init__` replaced the lock meanwhile the
release aborts the process. -/
theorem keeps_locked {α : Type} (m : BM α) : Keeps (locked m) := by
  constructor
  intro R _ s
  unfold locked
  cases hl : s.locked with
  | true =>
    rw [bind_err (enter_held R s hl)]
    exact linv_same s _
  | false =>
    rw [bind_of_ok (enter_free R s hl)]
    rw [bind_of_ok (get_apply R _)]
    dsimp only
    rcases ha : attempt m R { s with locked := true } with ⟨s2, r2⟩
    cases r2 with
    | error e =>
      rw [bind_err ha]
      -- `attempt` raises only when the process died
      unfold attempt at ha
      rcases hm : m R { s with locked := true } with ⟨s3, r3⟩
      rw [hm] at ha
      dsimp only at ha
      split at ha
      · next hc =>
        simp only [Prod.mk.injEq] at ha
        obtain ⟨rfl, -⟩ := ha
        exact .inl ⟨hc, e, rfl⟩
      · simp at ha
    | ok r =>
      rw [bind_of_ok ha]
      rw [bind_of_ok (get_apply R s2)]
      try dsimp only
      by_cases hg : s2.lockGen = s.lockGen
      · have hn : ¬ (s2.lockGen ≠ ({ s with locked := true } : BufS).lockGen) := fun h => h hg
        rw [if_neg hn]
        refine .inr (.inl ⟨?_, ?_⟩)
        · show false = s.locked
          rw [hl]
        · exact hg
      · have hn : s2.lockGen ≠ ({ s with locked := true } : BufS).lockGen := hg
        rw [if_pos hn]
        exact .inl ⟨rfl, _, rfl⟩

theorem keeps_callback (c : RCall) : Keeps (callback c) := by
  constructor
  intro R hR s
  unfold callback
  dsimp only
  split
  · exact .inr (.inl ⟨rfl, rfl⟩)
  · next op _ =>
    have h1 := hR op { s with raw := (s.raw.enter c).1 }
    rcases hro : R op { s with raw := (s.raw.enter c).1 } with ⟨s2, v⟩
    rw [hro] at h1
    dsimp only
    split
    · next hc => exact .inl ⟨hc, _, rfl⟩
    · next hc =>
      rcases h1 with ⟨h, _⟩ | h1 | h1
      · exact absurd h hc
      · exact .inr (.inl h1)
      · exact .inr (.inr h1)

theorem keeps_getput {α : Type} (f : Raw → Raw × α) :
    Keeps (do
      let s ← get
      let (r, a) := f s.raw
      put { s with raw := r }
      pure a : BM α) := by
  constructor
  intro R _ s
  refine .inr (.inl ⟨?_, ?_⟩)
  · show ((match f s.raw with | (r, a) => (put { s with raw := r } >>= fun _ => pure a : BM α)) R s).1.locked
      = s.locked
    rcases f s.raw with ⟨r, a⟩
    rfl
  · show ((match f s.raw with | (r, a) => (put { s with raw := r } >>= fun _ => pure a : BM α)) R s).1.lockGen
      = s.lockGen
    rcases f s.raw with ⟨r, a⟩
    rfl

theorem keeps_wrapArg {α : Type} (a : Py α) (f : α → BM Val) (hf : ∀ v, Keeps (f v)) :
    Keeps (wrapArg a f) := by
  unfold wrapArg
  split
  · exact keeps_thr _
  · exact hf _

end BC2

/-- One step of taking a method body apart; later `macro_rules` are tried first. -/
syntax "keeps_step" : tactic
macro_rules | `(tactic| keeps_step) => `(tactic| split)
macro_rules | `(tactic| keeps_step) => `(tactic| (intro _; try dsimp only))
macro_rules | `(tactic| keeps_step) => `(tactic| apply PyLean.PyIO.BC2.keeps_ite)
macro_rules | `(tactic| keeps_step) => `(tactic| apply PyLean.PyIO.BC2.keeps_bind)
macro_rules | `(tactic| keeps_step) => `(tactic| apply PyLean.PyIO.BC2.keeps_wrapArg)
macro_rules | `(tactic| keeps_step) => `(tactic| apply PyLean.PyIO.BC2.keeps_attempt)
macro_rules | `(tactic| keeps_step) => `(tactic| (apply PyLean.PyIO.BC2.keeps_mod; intro _; (first | exact ⟨rfl, rfl⟩ | (split <;> exact ⟨rfl, rfl⟩))))
macro_rules | `(tactic| keeps_step) => `(tactic| (apply PyLean.PyIO.BC2.keeps_relock; intro _; exact ⟨rfl, rfl⟩))
macro_rules | `(tactic| keeps_step) => `(tactic| exact PyLean.PyIO.BC2.keeps_getput _)
macro_rules | `(tactic| keeps_step) => `(tactic| exact PyLean.PyIO.BC2.keeps_callback _)
macro_rules | `(tactic| keeps_step) => `(tactic| exact PyLean.PyIO.BC2.keeps_locked _)
macro_rules | `(tactic| keeps_step) => `(tactic| exact PyLean.PyIO.BC2.keeps_crash)
macro_rules | `(tactic| keeps_step) => `(tactic| exact PyLean.PyIO.BC2.keeps_hangC)
macro_rules | `(tactic| keeps_step) => `(tactic| exact PyLean.PyIO.BC2.keeps_ofPy _)
macro_rules | `(tactic| keeps_step) => `(tactic| exact PyLean.PyIO.BC2.keeps_thr _)
macro_rules | `(tactic| keeps_step) => `(tactic| exact PyLean.PyIO.BC2.keeps_get)
macro_rules | `(tactic| keeps_step) => `(tactic| exact PyLean.PyIO.BC2.keeps_pure _)

/-- Take a method body apart into steps that keep the lock. -/
macro "keeps" : tactic => `(tactic| ((try dsimp only); repeat' keeps_step))

/-- Make `keeps` use the lemma `l` for the call it is about. -/
macro "keeps_use" l:ident : command =>
  `(macro_rules | `(tactic| keeps_step) => `(tactic| apply $l))

namespace BC2

theorem keeps_onRaw {α : Type} (c : RCall) (f : Raw → Raw × α) : Keeps (onRaw c f) := by
  unfold onRaw; keeps
end BC2
keeps_use PyLean.PyIO.BC2.keeps_onRaw
namespace BC2

theorem keeps_onRawObj {α : Type} (c : RCall) (f : Raw → Raw × α) : Keeps (onRawObj c f) := by
  unfold onRawObj; keeps
theorem keeps_checkInit : Keeps checkInit := by unfold checkInit; keeps
end BC2
keeps_use PyLean.PyIO.BC2.keeps_onRawObj
keeps_use PyLean.PyIO.BC2.keeps_checkInit
namespace BC2
theorem keeps_bufferedClosed : Keeps bufferedClosed := by unfold bufferedClosed; keeps
end BC2
keeps_use PyLean.PyIO.BC2.keeps_bufferedClosed
namespace BC2
theorem keeps_isClosed : Keeps isClosed := by unfold isClosed; keeps
end BC2
keeps_use PyLean.PyIO.BC2.keeps_isClosed
namespace BC2
theorem keeps_checkClosed (msg : String) : Keeps (checkClosed msg) := by unfold checkClosed; keeps
theorem keeps_asOff (v : Int) : Keeps (asOff v) := by unfold asOff; keeps
theorem keeps_inquiry (c : RCall) (fl : Raw → Bool) : Keeps (inquiry c fl) := by unfold inquiry; keeps
theorem keeps_checkInq (a : QAns) (msg : String) : Keeps (checkInq a msg) := by unfold checkInq; keeps
theorem keeps_readFast (n : Int) : Keeps (readFast n) := by unfold readFast; keeps
end BC2
keeps_use PyLean.PyIO.BC2.keeps_checkClosed
keeps_use PyLean.PyIO.BC2.keeps_asOff
keeps_use PyLean.PyIO.BC2.keeps_inquiry
keeps_use PyLean.PyIO.BC2.keeps_checkInq
keeps_use PyLean.PyIO.BC2.keeps_readFast
namespace BC2
theorem keeps_inquiryObj (c : RCall) (fl : Raw → Bool) : Keeps (inquiryObj c fl) := by
  unfold inquiryObj; keeps
theorem keeps_checkPos (v : IRes) : Keeps (checkPos v) := by unfold checkPos; keeps
theorem keeps_checkRawSeekable : Keeps checkRawSeekable := by unfold checkRawSeekable; keeps
theorem keeps_flush : Keeps flush := by unfold flush; keeps
theorem keeps_simpleFlush : Keeps simpleFlush := by unfold simpleFlush; keeps
end BC2
keeps_use PyLean.PyIO.BC2.keeps_checkPos
keeps_use PyLean.PyIO.BC2.keeps_inquiryObj
keeps_use PyLean.PyIO.BC2.keeps_checkRawSeekable
keeps_use PyLean.PyIO.BC2.keeps_flush
keeps_use PyLean.PyIO.BC2.keeps_simpleFlush
namespace BC2
theorem keeps_rawTell : Keeps rawTell := by unfold rawTell; keeps
end BC2
keeps_use PyLean.PyIO.BC2.keeps_rawTell
namespace BC2
theorem keeps_init (kind : Nat) (size : Int) : Keeps (init kind size) := by unfold init; keeps
theorem keeps_flushMethod : Keeps flushMethod := by unfold flushMethod; keeps
end BC2
keeps_use PyLean.PyIO.BC2.keeps_init
keeps_use PyLean.PyIO.BC2.keeps_flushMethod
namespace BC2
theorem keeps_read (n : Int) : Keeps (read n) := by unfold read; keeps
theorem keeps_read1 (n : Int) : Keeps (read1 n) := by unfold read1; keeps
theorem keeps_readinto (len : Nat) (one : Bool) : Keeps (readinto len one) := by unfold readinto; keeps
theorem keeps_readlineRaw (l : Int) : Keeps (readlineRaw l) := by unfold readlineRaw; keeps
theorem keeps_peek : Keeps peek := by unfold peek; keeps
theorem keeps_tell : Keeps tell := by unfold tell; keeps
theorem keeps_seek (p w : Int) : Keeps (seek p w) := by unfold seek; keeps
theorem keeps_truncate (p : Option Int) : Keeps (truncate p) := by unfold truncate; keeps
theorem keeps_close : Keeps close := by unfold close; keeps
theorem keeps_detach : Keeps detach := by unfold detach; keeps
theorem keeps_write (b : List Nat) : Keeps (write b) := by unfold write; keeps
theorem keeps_unsupported (m : String) : Keeps (bufferediobaseUnsupported m) := by
  unfold bufferediobaseUnsupported; keeps
end BC2
keeps_use PyLean.PyIO.BC2.keeps_read
keeps_use PyLean.PyIO.BC2.keeps_read1
keeps_use PyLean.PyIO.BC2.keeps_readinto
keeps_use PyLean.PyIO.BC2.keeps_readlineRaw
keeps_use PyLean.PyIO.BC2.keeps_peek
keeps_use PyLean.PyIO.BC2.keeps_tell
keeps_use PyLean.PyIO.BC2.keeps_seek
keeps_use PyLean.PyIO.BC2.keeps_truncate
keeps_use PyLean.PyIO.BC2.keeps_close
keeps_use PyLean.PyIO.BC2.keeps_detach
keeps_use PyLean.PyIO.BC2.keeps_write
keeps_use PyLean.PyIO.BC2.keeps_unsupported
namespace BC2
theorem keeps_iternext : Keeps iternext := by unfold iternext; keeps
theorem keeps_bioReadinto (len : Nat) (one : Bool) : Keeps (bufferediobaseReadinto len one) := by
  unfold bufferediobaseReadinto; keeps
end BC2
keeps_use PyLean.PyIO.BC2.keeps_iternext
keeps_use PyLean.PyIO.BC2.keeps_bioReadinto
namespace BC2
theorem keeps_stepOp (op : BfOp) : Keeps (stepOp op) := by
  unfold stepOp; keeps

end BC2

theorem stepC_keeps : ∀ fuel, BC2.RK (stepC fuel) := by
  intro fuel
  induction fuel with
  | zero => intro op s; exact BC2.linv_same s _
  | succ n ih => intro op s; exact (BC2.keeps_stepOp op).run (stepC n) ih s

/-- Over the bodies of every method of `BufferedReader`, `BufferedWriter` and
`BufferedRandom` (bufferedio.c:2550-2749), `__init__` included, with re-entered calls
run by the same methods (`stepC`), for every state and raw stream:

1. a call ends with the same lock, held or not as it found it, unless the process
   died or `__init__` replaced the lock (:853-860) by a new, free one: every
   `ENTER_BUFFERED` (:329-332) is matched by a `LEAVE_BUFFERED` (:334-338) on every
   path, success or exception, and a refused `ENTER_BUFFERED` leaves the lock alone;
2. so a call made with the lock free leaves it free, unless the process died;
3. a call that must take the lock while this thread holds it (here `close()`, and
   `write(b)` on a writer) is refused by `_enter_buffered_busy` (:299-303) with
   `RuntimeError("reentrant call inside <_io.Buffered...>")` and leaves the object
   exactly as it was.

Invariant: the lock serializes and a failure never leaves it held. The scope is a
single thread and no interpreter finalization (:305-325). A re-entrant `__init__`
is the exception in 1, and the section it interrupts then aborts when it unlocks:
`bufferedCNoCrash_refuted_reinit`. -/
def LockDiscipline : Prop :=
  (∀ (fuel : Nat) (op : BfOp) (s : BufS),
    (stepC fuel op s).1.crashed = true ∨
    ((stepC fuel op s).1.locked = s.locked ∧ (stepC fuel op s).1.lockGen = s.lockGen) ∨
    (s.lockGen < (stepC fuel op s).1.lockGen ∧ (stepC fuel op s).1.locked = false)) ∧
  (∀ (fuel : Nat) (op : BfOp) (s : BufS), s.locked = false →
    (stepC fuel op s).1.crashed = true ∨ (stepC fuel op s).1.locked = false) ∧
  (∀ (fuel : Nat) (s : BufS), s.ok = true → s.locked = true →
    stepC (fuel + 1) .close s =
      (s, .error (.named "RuntimeError" s!"reentrant call inside <_io.{BC2.className s}>"))) ∧
  (∀ (fuel : Nat) (s : BufS) (b : List Nat), s.ok = true → s.writable = true → s.locked = true →
    stepC (fuel + 1) (.write b) s =
      (s, .error (.named "RuntimeError" s!"reentrant call inside <_io.{BC2.className s}>")))

theorem lockDiscipline_proven : LockDiscipline := by
  refine ⟨fun fuel op s => ?_, fun fuel op s hl => ?_, fun fuel s hok hl => ?_, fun fuel s b hok hw hl => ?_⟩
  · rcases stepC_keeps fuel op s with ⟨h, _⟩ | h | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr h)
  · rcases stepC_keeps fuel op s with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩
    · exact .inl h
    · exact .inr (h.trans hl)
    · exact .inr h
  · rcases s with ⟨raw, ok, det, rn, rd, wr, lk, ap, hb, buf, pos, rp, re, wp, we, sz, cr, lg, mk, bl⟩
    simp only at hok hl
    subst hok hl
    rfl
  · rcases s with ⟨raw, ok, det, rn, rd, wr, lk, ap, hb, buf, pos, rp, re, wp, we, sz, cr, lg, mk, bl⟩
    simp only at hok hw hl
    subst hok hw hl
    rfl

end PyLean.PyIO
