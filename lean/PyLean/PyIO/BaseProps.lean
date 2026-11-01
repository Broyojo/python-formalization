import PyLean.PyIO.Base

/-! Properties of the abstract base classes `IOBase`/`RawIOBase` (iobase.c and
`_pyio`), over the scripted `UObj` model of `PyIO/Base.lean`. These are the
default-method behaviours that need no subclass callbacks, so they hold for
every object and both twins. -/

namespace PyLean.PyIO

open PyLean

/-- Default inquiry methods: on every `IOBase` (both twins) `seekable()`,
`readable()` and `writable()` return `False` and leave the object unchanged.
Mirrors the C default slots and `_pyio` `IOBase.seekable/readable/writable`. -/
def BaseInquiriesFalse : Prop := ∀ (u : UObj) (o : UOp),
  (o = .seekable ∨ o = .readable ∨ o = .writable) →
  BC.step u o = (u, .ok (.bool false)) ∧ BP.step u o = (u, .ok (.bool false))

theorem baseInquiriesFalse_proven : BaseInquiriesFalse := by
  intro u o ho; rcases ho with rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩

/-- `_checkSeekable`/`_checkReadable`/`_checkWritable` raise
`io.UnsupportedOperation` with the same message in both twins and do not touch
the object (iobase.c `check_seekable/readable/writable`; `_pyio`
`IOBase._checkSeekable/_checkReadable/_checkWritable`, via `_unsupported`). -/
def BaseChecksUnsupported : Prop := ∀ (u : UObj) (o : UOp),
  (o = .checkSeekable ∨ o = .checkReadable ∨ o = .checkWritable) →
  BC.step u o = BP.step u o ∧ ∃ m, BC.step u o = (u, .error (.named "UnsupportedOperation" m))

theorem baseChecksUnsupported_proven : BaseChecksUnsupported := by
  intro u o ho; rcases ho with rfl | rfl | rfl <;> exact ⟨rfl, _, rfl⟩

/-- `seek`, `tell`, `truncate` and `fileno` are unsupported on a bare `IOBase`:
both twins raise `io.UnsupportedOperation` and leave the object unchanged. The
message differs by implementation — C gives the bare method name, `_pyio` gives
`"<Class>.<method>() not supported"` — so only the class is shared. Mirrors
iobase.c `_io__IOBase_{seek,tell,truncate,fileno}_impl` and `_pyio`
`IOBase.{seek,tell,truncate,fileno}`. -/
def BaseUnsupportedOps : Prop := ∀ (u : UObj) (o : UOp),
  (o = .seek ∨ o = .tell ∨ o = .truncate ∨ o = .fileno) →
  (∃ m, BC.step u o = (u, .error (.named "UnsupportedOperation" m))) ∧
  (∃ m, BP.step u o = (u, .error (.named "UnsupportedOperation" m)))

theorem baseUnsupportedOps_proven : BaseUnsupportedOps := by
  intro u o ho
  rcases ho with rfl | rfl | rfl | rfl <;> exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩

/-- Closed-aware default methods. `closed` reflects the flag; on an open object
(both twins) `__enter__`, `__iter__`, `_checkClosed` return `None` and
`isatty()` returns `False`; on a closed object each of those four raises
`ValueError('I/O operation on closed file.')`. Mirrors iobase.c
`iobase_closed_get`, `iobase_check_closed`, `iobase_enter`, `iobase_iter`,
`_io__IOBase_isatty_impl` and the `_pyio` equivalents. -/
def BaseClosedProtocol : Prop := ∀ (u : UObj),
  BC.step u .closed = (u, .ok (.bool u.isClosed)) ∧
  BP.step u .closed = (u, .ok (.bool u.isClosed)) ∧
  (∀ o, (o = .enter ∨ o = .iter ∨ o = .checkClosed) →
    (if u.isClosed then
        BC.step u o = (u, .error (.valueError "I/O operation on closed file.")) ∧
        BP.step u o = (u, .error (.valueError "I/O operation on closed file."))
     else BC.step u o = (u, .ok .none) ∧ BP.step u o = (u, .ok .none))) ∧
  (if u.isClosed then
      BC.step u .isatty = (u, .error (.valueError "I/O operation on closed file.")) ∧
      BP.step u .isatty = (u, .error (.valueError "I/O operation on closed file."))
   else BC.step u .isatty = (u, .ok (.bool false)) ∧ BP.step u .isatty = (u, .ok (.bool false)))

theorem baseClosedProtocol_proven : BaseClosedProtocol := by
  intro u
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro o ho
    rcases ho with rfl | rfl | rfl <;>
      (cases h : u.isClosed <;> simp [BC.step, BP.step, h, closedDotE])
  · cases h : u.isClosed <;> simp [BC.step, BP.step, h, closedDotE]

end PyLean.PyIO
