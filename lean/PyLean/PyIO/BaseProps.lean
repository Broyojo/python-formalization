import PyLean.PyIO.Base
import PyLean.PyIO.Spec

/-! Properties of the abstract base classes `IOBase`/`RawIOBase` (iobase.c and
`_pyio`), over the scripted `UObj` model of `PyIO/Base.lean`: a user subclass that
may override `seek`, the inquiries and the `closed` property, each able to answer any
object or raise. -/

namespace PyLean.PyIO

open PyLean

/-- Default inquiry methods: on every `IOBase` whose class does not override them (both
twins) `seekable()`, `readable()` and `writable()` return `False` and leave the object
unchanged. Mirrors the C default slots and `_pyio` `IOBase.seekable/readable/writable`. -/
def BaseInquiriesFalse : Prop := ∀ (u : UObj) (o : UOp), u.inqs = none →
  (o = .seekable ∨ o = .readable ∨ o = .writable) →
  BC.step u o = (u, .ok (.bool false)) ∧ BP.step u o = (u, .ok (.bool false))

theorem baseInquiriesFalse_proven : BaseInquiriesFalse := by
  intro u o hi ho
  rcases ho with rfl | rfl | rfl <;>
    simp [BC.step, BP.step, UObj.callInq, hi, BC.answer, IRet.val]

/-- What `_pyio`'s `if not self.seekable(): raise UnsupportedOperation(...)` gives for an
answer `r` of the inquiry: its exception, `None` for a truthy answer, else
`UnsupportedOperation` with `msg` or the default message. -/
def pyCheckOutcome (r : IRet) (dflt : String) (msg : Option String) : Py Val :=
  match r with
  | .raise c m => .error (excOf c m)
  | r => if r.truthy then .ok .none else .error (unsup (msg.getD dflt))

/-- What C's `_PyIOBase_check_*` gives for an answer `r`: its exception, the object
`True` back for exactly `True`, else `UnsupportedOperation` with the default message. -/
def cCheckOutcome (r : IRet) (dflt : String) : Py Val :=
  match r with
  | .raise c m => .error (excOf c m)
  | .bool true => .ok (.bool true)
  | _ => .error (unsup dflt)

/-- The three checks: the operation, the inquiry it calls and its default message. -/
def checkTable : List ((Option String → UOp) × String × String) :=
  [(.checkSeekable, "seekable", "File or stream is not seekable."),
   (.checkReadable, "readable", "File or stream is not readable."),
   (.checkWritable, "writable", "File or stream is not writable.")]

/-- `_checkSeekable`, `_checkReadable` and `_checkWritable` over an inquiry that may be
overridden, answer any object, or raise. Each twin calls the object's own inquiry once
(logged) and propagates its exception. `_pyio` (_pyio.py:430-463) tests the answer's
truth and returns `None`, raising `UnsupportedOperation(msg)` for a falsy answer, or the
default message when `msg` is `None`. C (iobase.c:414-494) accepts only the object
`True` and returns it, and as a `METH_NOARGS` method (iobase.c:845-848) refuses a `msg`
argument with `TypeError` before asking. With the base inquiries (`False`) both raise the
default `UnsupportedOperation` and change nothing. -/
def BaseChecks : Prop := ∀ (u : UObj) (msg : Option String),
  ∀ k ∈ checkTable,
    (∀ m, BC.step u (k.1 (some m)) = (u, .error (.typeError s!"_IOBase._check{k.2.1.capitalize}() takes no arguments (1 given)"))) ∧
    (u.inqs = none →
      BC.step u (k.1 none) = (u, .error (unsup k.2.2)) ∧
      BP.step u (k.1 msg) = (u, .error (unsup (msg.getD k.2.2)))) ∧
    (∀ r rs, u.inqs = some (r :: rs) →
      let u' := { u with log := u.log ++ [Call.inquiry k.2.1], inqs := some rs }
      BC.step u (k.1 none) = (u', cCheckOutcome r k.2.2) ∧
      BP.step u (k.1 msg) = (u', pyCheckOutcome r k.2.2 msg))

theorem baseChecks_proven : BaseChecks := by
  intro u msg k hk
  simp only [checkTable, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl <;>
  · refine ⟨fun m => rfl, ?_, ?_⟩
    · intro hi
      simp [BC.step, BP.step, BC.checkInq, BP.checkInq, UObj.callInq, hi, IRet.truthy]
    · intro r rs hi
      cases r with
      | bool b =>
        cases b <;>
          simp [BC.step, BP.step, BC.checkInq, BP.checkInq, UObj.callInq, hi, cCheckOutcome,
            pyCheckOutcome, IRet.truthy]
      | int n =>
        by_cases hn : n = 0 <;>
          simp [BC.step, BP.step, BC.checkInq, BP.checkInq, UObj.callInq, hi, cCheckOutcome,
            pyCheckOutcome, IRet.truthy, hn]
      | _ =>
        simp [BC.step, BP.step, BC.checkInq, BP.checkInq, UObj.callInq, hi, cCheckOutcome,
          pyCheckOutcome, IRet.truthy]

/-- `_checkSeekable()` returns the same value or raises the same exception class in both
twins, for every answer of the object's `seekable()`. -/
def BaseChecksTwins : Prop := ∀ (u : UObj),
  sameClass (BC.step u (.checkSeekable none)).2 (BP.step u (.checkSeekable none)).2 = true

/-- `seekable()` returning `1`: C refuses anything but the object `True`
(`UnsupportedOperation`); `_pyio` tests truth and returns `None`. -/
theorem baseChecksTwins_refuted : ¬BaseChecksTwins := by
  intro h
  have := h { (default : UObj) with inqs := some [.int 1] }
  revert this
  decide

/-- The exact `UnsupportedOperation` of `seek`, `truncate` and `fileno` on a bare `IOBase`
(and of `tell` when `seek` is not overridden), on every object, which they leave
unchanged: C passes the method name (iobase.c:119-125, :153-159, :528-533), `_pyio`'s
`_unsupported` (_pyio.py:341-344) formats `"%s.%s() not supported"` with the class name. -/
def BaseUnsupportedOps : Prop := ∀ (u : UObj),
  BC.step u .seek = (u, .error (.named "UnsupportedOperation" "seek")) ∧
  BP.step u .seek = (u, .error (.named "UnsupportedOperation" s!"{u.name}.seek() not supported")) ∧
  BC.step u .truncate = (u, .error (.named "UnsupportedOperation" "truncate")) ∧
  BP.step u .truncate = (u, .error (.named "UnsupportedOperation" s!"{u.name}.truncate() not supported")) ∧
  BC.step u .fileno = (u, .error (.named "UnsupportedOperation" "fileno")) ∧
  BP.step u .fileno = (u, .error (.named "UnsupportedOperation" s!"{u.name}.fileno() not supported")) ∧
  (u.seeks = none →
    BC.step u .tell = (u, .error (.named "UnsupportedOperation" "seek")) ∧
    BP.step u .tell = (u, .error (.named "UnsupportedOperation" s!"{u.name}.seek() not supported")))

theorem baseUnsupportedOps_proven : BaseUnsupportedOps := by
  intro u
  refine ⟨rfl, ?_, rfl, ?_, rfl, ?_, ?_⟩
  · simp [BP.step, BP.unsupported, pyUnsupported, unsup, unsupportedOp, String.append_assoc]; decide
  · simp [BP.step, BP.unsupported, pyUnsupported, unsup, unsupportedOp, String.append_assoc]; decide
  · simp [BP.step, BP.unsupported, pyUnsupported, unsup, unsupportedOp, String.append_assoc]; decide
  · intro h
    simp [BC.step, BP.step, BC.tell, BP.tell, h, BP.unsupported, pyUnsupported, unsup, unsupportedOp, String.append_assoc]
    decide

/-- `tell()` is `self.seek(0, 1)` in both twins (iobase.c:134-138, _pyio.py:366-368): with
an overriding `seek`, it calls that `seek` once with `(0, 1)` (logged), and returns what
it returned or raises what it raised. -/
def BaseTellDispatch : Prop := ∀ (u : UObj) (r : Ret) (rs : List Ret),
  u.seeks = some (r :: rs) →
  let u' := { u with log := u.log ++ [Call.seek 0 1], seeks := some rs }
  let out : Py Val := match r with
    | .raise c m => .error (excOf c m)
    | .bytes b => .ok (.bytes b)
    | .none => .ok .none
    | .int n => .ok (.int n)
  BC.step u .tell = (u', out) ∧ BP.step u .tell = (u', out)

theorem baseTellDispatch_proven : BaseTellDispatch := by
  intro u r rs h
  cases r <;> simp [BC.step, BP.step, BC.tell, BP.tell, h, UObj.callSeek, BC.seekAnswer]

/-- What `_checkClosed()` gives in C for the `closed` attribute's answer `r`
(`iobase_check_closed`, iobase.c:197-214): an `AttributeError` counts as open, another
exception propagates, a true value raises `ValueError`. -/
def cClosedOutcome (r : IRet) : Py Unit :=
  match r with
  | .raise "AttributeError" _ => .ok ()
  | .raise c m => .error (excOf c m)
  | r => if r.truthy then .error (.valueError "I/O operation on closed file.") else .ok ()

/-- What `_checkClosed(msg)` gives in `_pyio` (_pyio.py:473-478): every exception of
`self.closed` propagates, a true value raises `ValueError(msg)`, or the default message. -/
def pyClosedOutcome (r : IRet) (msg : Option String) : Py Unit :=
  match r with
  | .raise c m => .error (excOf c m)
  | r => if r.truthy then .error (.valueError (msg.getD "I/O operation on closed file.")) else .ok ()

/-- The closed checks over a `closed` that may be the base property (the flag) or an
override answering any object or raising. `closed` returns the answer; `__enter__` and
`__iter__` return `self` (encoded as `None`), `_checkClosed` `None` and `isatty()`
`False` after the check, which is `cClosedOutcome` in C and `pyClosedOutcome` in
`_pyio`, where `_checkClosed(msg)` raises `ValueError(msg)` and C's `METH_NOARGS`
refuses the argument. None of them changes the object. -/
def BaseClosedProtocol : Prop := ∀ (u : UObj) (msg : Option String),
  BC.step u .closed = BC.answer u u.readClosed ∧
  BP.step u .closed = BC.answer u u.readClosed ∧
  (∀ o, (o = .enter ∨ o = .iter ∨ o = .checkClosed none) →
    BC.step u o = (u, (cClosedOutcome u.readClosed).map (fun _ => .none)) ∧
    BP.step u o = (u, (pyClosedOutcome u.readClosed none).map (fun _ => .none))) ∧
  BP.step u (.checkClosed msg) = (u, (pyClosedOutcome u.readClosed msg).map (fun _ => .none)) ∧
  (∀ m, BC.step u (.checkClosed (some m)) = (u, .error (.typeError "_IOBase._checkClosed() takes no arguments (1 given)"))) ∧
  BC.step u .isatty = (u, (cClosedOutcome u.readClosed).map (fun _ => .bool false)) ∧
  BP.step u .isatty = (u, (pyClosedOutcome u.readClosed none).map (fun _ => .bool false))

theorem baseClosedProtocol_proven : BaseClosedProtocol := by
  intro u msg
  have hc : BC.checkClosed u = cClosedOutcome u.readClosed := by
    unfold BC.checkClosed cClosedOutcome; rfl
  have hp : ∀ m, BP.checkClosed u m = pyClosedOutcome u.readClosed m := by
    intro m; unfold BP.checkClosed pyClosedOutcome; rfl
  refine ⟨rfl, rfl, ?_, ?_, fun _ => rfl, ?_, ?_⟩
  · intro o ho
    rcases ho with rfl | rfl | rfl <;>
      (simp only [BC.step, BP.step, hc, hp]; constructor <;> split <;> simp_all [Except.map])
  · simp only [BP.step, hp]; split <;> simp_all [Except.map]
  · simp only [BC.step, hc]; split <;> simp_all [Except.map]
  · simp only [BP.step, hp]; split <;> simp_all [Except.map]

/-- Index of the first write answer that raises, with its exception. -/
def raiseIdx : List Ret → Option (Nat × String × String)
  | [] => none
  | .raise c m :: _ => some (0, c, m)
  | _ :: rs => (raiseIdx rs).map (fun (i, c, m) => (i + 1, c, m))

/-- The answers of `n` calls of a scripted method: the script, then `None`. -/
def scriptAnswers : List Ret → Nat → List Ret
  | _, 0 => []
  | [], n + 1 => Ret.none :: scriptAnswers [] n
  | r :: rs, n + 1 => r :: scriptAnswers rs n

/-- The outcome of the iterator after the last line. -/
def stopResult : Option (String × String) → Py Val
  | some (c, m) => .error (excOf c m)
  | none => .ok .none

/-- `writelines` raised the first raising write's exception after writing the lines up to
it, or, with no raising write, wrote every line and ended as the iterator did. -/
def WLSpec (stop : Option (String × String)) (ls : List (List Nat)) (u : UObj) (res : UObj × Py Val) : Prop :=
  match raiseIdx (scriptAnswers u.writes ls.length) with
  | some (i, c, m) => res.2 = .error (excOf c m) ∧ res.1.log = u.log ++ (ls.take (i + 1)).map Call.write
  | none => res.2 = stopResult stop ∧ res.1.log = u.log ++ ls.map Call.write

/-- `_pyio`'s `IOBase.writelines(lines)` (_pyio.py:583-591), over a fallible `closed`,
fallible `write` calls and an iterator that may raise after its lines: if
`_checkClosed()` fails, its exception is raised before any `write`; otherwise `write` is
called with each line in order until one raises, whose exception propagates with no
later line written; if none raises, the iterator's exception propagates, or the result is
`None`. (A `write` past the end of the script answers `None`.) -/
def BaseWritelines : Prop := ∀ (u : UObj) (ls : List (List Nat)) (stop : Option (String × String)),
  (∀ e, BP.checkClosed u none = .error e → BP.step u (.writelines ls stop) = (u, .error e)) ∧
  (BP.checkClosed u none = .ok () → WLSpec stop ls u (BP.step u (.writelines ls stop)))

theorem raiseIdx_cons_ok (r : Ret) (rs : List Ret) (h : ∀ c m, r ≠ .raise c m) :
    raiseIdx (r :: rs) = (raiseIdx rs).map (fun (i, c, m) => (i + 1, c, m)) := by
  cases r with
  | raise c m => exact absurd rfl (h c m)
  | _ => rfl

theorem wlSpec_cons (stop : Option (String × String)) (l : List Nat) (ls : List (List Nat))
    (u u' : UObj) (r : Ret) (res : UObj × Py Val) (hr : ∀ c m, r ≠ .raise c m)
    (hlog : u'.log = u.log ++ [Call.write l])
    (hans : scriptAnswers u.writes (l :: ls).length = r :: scriptAnswers u'.writes ls.length)
    (ih : WLSpec stop ls u' res) : WLSpec stop (l :: ls) u res := by
  unfold WLSpec at ih ⊢
  rw [hans, raiseIdx_cons_ok r _ hr]
  revert ih
  cases raiseIdx (scriptAnswers u'.writes ls.length) with
  | none => intro ih; simp only [Option.map_none]; exact ⟨ih.1, by rw [ih.2, hlog]; simp⟩
  | some x =>
    obtain ⟨i, c, m⟩ := x
    intro ih
    simp only [Option.map_some]
    exact ⟨ih.1, by rw [ih.2, hlog]; simp⟩

theorem writelinesLoop_spec (stop : Option (String × String)) : ∀ (ls : List (List Nat)) (u : UObj),
    WLSpec stop ls u (BP.writelinesLoop stop u ls) := by
  intro ls
  induction ls with
  | nil =>
    intro u
    unfold WLSpec
    simp only [List.length_nil, scriptAnswers, raiseIdx]
    cases stop <;> simp [BP.writelinesLoop, stopResult]
  | cons l ls ih =>
    intro u
    cases hw : u.writes with
    | nil =>
      have hu : u.callWrite l = ({ u with log := u.log ++ [Call.write l] }, Ret.none) := by
        simp [UObj.callWrite, hw]
      have e : BP.writelinesLoop stop u (l :: ls) =
          BP.writelinesLoop stop { u with log := u.log ++ [Call.write l] } ls := by
        simp only [BP.writelinesLoop, hu]
      rw [e]
      exact wlSpec_cons stop l ls u _ Ret.none _ (by intro c m h; cases h) rfl
        (by simp [hw, scriptAnswers]) (ih _)
    | cons r rs =>
      have hu : u.callWrite l = ({ u with log := u.log ++ [Call.write l], writes := rs }, r) := by
        simp [UObj.callWrite, hw]
      cases r with
      | raise c m =>
        unfold WLSpec
        simp [BP.writelinesLoop, hu, hw, scriptAnswers, raiseIdx]
      | bytes b =>
        have e : BP.writelinesLoop stop u (l :: ls) =
            BP.writelinesLoop stop { u with log := u.log ++ [Call.write l], writes := rs } ls := by
          simp only [BP.writelinesLoop, hu]
        rw [e]
        exact wlSpec_cons stop l ls u _ (.bytes b) _ (by intro c m h; cases h) rfl
          (by simp [hw, scriptAnswers]) (ih _)
      | none =>
        have e : BP.writelinesLoop stop u (l :: ls) =
            BP.writelinesLoop stop { u with log := u.log ++ [Call.write l], writes := rs } ls := by
          simp only [BP.writelinesLoop, hu]
        rw [e]
        exact wlSpec_cons stop l ls u _ .none _ (by intro c m h; cases h) rfl
          (by simp [hw, scriptAnswers]) (ih _)
      | int n =>
        have e : BP.writelinesLoop stop u (l :: ls) =
            BP.writelinesLoop stop { u with log := u.log ++ [Call.write l], writes := rs } ls := by
          simp only [BP.writelinesLoop, hu]
        rw [e]
        exact wlSpec_cons stop l ls u _ (.int n) _ (by intro c m h; cases h) rfl
          (by simp [hw, scriptAnswers]) (ih _)

theorem baseWritelines_proven : BaseWritelines := by
  intro u ls stop
  constructor
  · intro e he
    simp [BP.step, he]
  · intro he
    simp only [BP.step, he]
    exact writelinesLoop_spec stop ls u

theorem nlPrefix_cons (x : Nat) (xs : List Nat) :
    nlPrefix (x :: xs) = if x = 10 then 1 else 1 + nlPrefix xs := by
  unfold nlPrefix
  simp only [findIdx?]
  by_cases h : x = 10
  · simp [h]
  · simp only [h, ite_false]
    cases findIdx? xs 10 <;> simp <;> omega

theorem scanNl_eq (R : Int) : ∀ (l : List Nat) (n : Nat), (n : Int) ≤ R →
    (BC.scanNl R n l : Int) = min ((n + nlPrefix l : Nat) : Int) R := by
  intro l
  induction l with
  | nil => intro n h; simp [BC.scanNl, nlPrefix, findIdx?]; omega
  | cons x xs ih =>
    intro n h
    simp only [BC.scanNl, nlPrefix_cons]
    by_cases hR : (n : Int) ≥ R
    · simp only [hR, ite_true]; split <;> omega
    · simp only [hR, ite_false]
      by_cases hx : x = 10
      · simp only [hx, ite_true]; omega
      · simp only [hx, ite_false]
        rw [ih (n + 1) (by omega)]
        omega

/-- The bytes `IOBase.readline` asks for after a non-empty `peek`: up to and including
the first newline in what `peek` returned, but no more than the `size - len(res)`
still wanted, or to the first newline if `size` is negative (both twins). Until 3.15
both bounded this by `size`, so a line assembled over several peeks could overshoot. -/
def ReadlineReadahead : Prop := ∀ (limit : Int) (len : Nat) (r : List Nat), r ≠ [] →
  ((len : Int) < limit →
    (BC.readahead limit len r : Int) = min (nlPrefix r : Int) (limit - len) ∧
    BP.nreadahead limit len (.bytes r) = .ok (BC.readahead limit len r)) ∧
  (limit < 0 → BC.readahead limit len r = nlPrefix r ∧ BP.nreadahead limit len (.bytes r) = .ok (nlPrefix r))

theorem readlineReadahead_proven : ReadlineReadahead := by
  intro limit len r hr
  have hl : r.length > 0 := List.length_pos_iff.mpr hr
  constructor
  · intro h
    have h0 : limit ≥ 0 := by omega
    have e : (BC.readahead limit len r : Int) = min (nlPrefix r : Int) (limit - len) := by
      simp only [BC.readahead, hl, h0, ite_true]
      rw [scanNl_eq _ _ _ (by omega)]
      simp
    refine ⟨e, ?_⟩
    cases r with
    | nil => exact absurd rfl hr
    | cons x xs =>
      simp only [BP.nreadahead, h0, ite_true]
      congr 1
      omega
  · intro h
    have h0 : ¬ limit ≥ 0 := by omega
    constructor
    · simp [BC.readahead, hl, h0]
    · cases r with
      | nil => exact absurd rfl hr
      | cons x xs => simp [BP.nreadahead, h0]

end PyLean.PyIO
