import PyLean.BytesObj.Mem.Fallible
import PyLean.BytesObj.Mem.Contig

/-!
The effects of a memoryview operation that are neither its result nor its error: what the
last reference to an object runs, what is held while Python code runs, what is given back on
the way out, and which callback runs first. Every statement here names the function and the
line that does it; a model without that line fails the proof.
-/

namespace PyLean.BytesObj.Mem

open PyLean

/-! ## What a release leaves behind -/

theorem memoryRelease_released (i : Nat) (st : St) (h : i < st.mvs.length) :
    ((memoryRelease i st).2.mv i).flags.released = true := by
  unfold memoryRelease
  dsimp only
  split
  · assumption
  · have hr : ((st.setMv i { st.mv i with flags := { (st.mv i).flags with released := true } }).mv i).flags.released
        = true := by
      rw [St.mv_setMv _ _ _ h]
    split
    · refine (mbufRelease_mono _ _).mv i ?_
      rw [St.mv_setMb]
      exact hr
    · dsimp only
      rw [St.mv_setMb]
      exact hr

theorem memoryReleaseAt_released (f i : Nat) (st : St) (h : i < st.mvs.length) :
    ((memoryReleaseAt (f + 1) i st).2.mv i).flags.released = true := by
  unfold memoryReleaseAt
  dsimp only
  split
  · assumption
  · have hr : ((st.setMv i { st.mv i with flags := { (st.mv i).flags with released := true } }).mv i).flags.released
        = true := by
      rw [St.mv_setMv _ _ _ h]
    split
    · refine (mbufReleaseWith_mono _ (fun t s => memoryReleaseAt_mono f t s) _ _).mv i ?_
      rw [St.mv_setMb]
      exact hr
    · dsimp only
      rw [St.mv_setMb]
      exact hr

theorem memoryRelease0_released (i : Nat) (st : St) (h : i < st.mvs.length) :
    ((memoryRelease0 i st).2.mv i).flags.released = true := by
  unfold memoryRelease0
  obtain ⟨f, hf⟩ : ∃ f, st.mvs.length = f + 1 := ⟨st.mvs.length - 1, by omega⟩
  simp only [hf]
  exact memoryReleaseAt_released f i st h

/-- `PyBuffer_Release` runs the `__release_buffer__` of the buffer it gives back. -/
theorem pyBufferRelease_hook (b : Buf) (t : Nat) (st : St) (hb : b.hook = some t)
    (ht : t < st.mvs.length) (h0 : (st.mv t).exports = 0) :
    ((pyBufferRelease b st).2.mv t).flags.released = true := by
  unfold pyBufferRelease
  rw [hb]
  dsimp only
  rw [if_pos h0]
  exact (pyBufferRelease0_mono _ _).mv t (memoryRelease0_released t st ht)

/-! ## `memory_dealloc`, `mbuf_dealloc` -/

theorem deallocMono (i : Nat) (st : St) : Mono st (memoryDealloc i st).2 := by
  unfold memoryDealloc
  dsimp only
  have h := memoryRelease_mono i st
  rcases hr : memoryRelease i st with ⟨r, s⟩
  rw [hr] at h
  dsimp only at h ⊢
  split
  · split
    · exact h.trans (memoryRelease_mono _ _)
    · exact h
  · exact h

/-- `memory_dealloc`, :1150-1161, on the last reference to a view: the release comes first
(:1156), and only then `PyObject_ClearWeakRefs` (:1158-1159), so the callback of a weakref runs
on a view that has given up its export and, if it was the last view, on a released exporter.
A view the callback releases must have no exports left; a view with exports is refused, and
the state is what the release left. Hypotheses: `i` and `t` exist. -/
def DeallocRules : Prop :=
  ∀ (st : St) (i : Nat), i < st.mvs.length →
    let s := (memoryRelease i st).2
    (memoryDealloc i st).1 = .ok () ∧
    ((memoryDealloc i st).2.mv i).flags.released = true ∧
    ((st.mv i).weakcb = none → memoryDealloc i st = memoryRelease i st) ∧
    (∀ t, (st.mv i).weakcb = some t → getExports s t ≠ 0 → memoryDealloc i st = memoryRelease i st) ∧
    (∀ t, (st.mv i).weakcb = some t → getExports s t = 0 → t < s.mvs.length →
      memoryDealloc i st = memoryRelease t s ∧ ((memoryDealloc i st).2.mv t).flags.released = true)

theorem deallocRules_proven : DeallocRules := by
  intro st i h
  have hrel := memoryRelease_released i st h
  have hd : memoryDealloc i st =
      match (st.mv i).weakcb with
      | some t =>
        if getExports (memoryRelease i st).2 t = 0 then memoryRelease t (memoryRelease i st).2
        else memoryRelease i st
      | none => memoryRelease i st := by
    unfold memoryDealloc
    dsimp only
    generalize memoryRelease i st = p
    cases p
    rfl
  dsimp only
  refine ⟨memoryDealloc_ok i st, ?_, ?_, ?_, ?_⟩
  · rw [hd]
    split
    · split
      · exact (memoryRelease_mono _ _).mv i hrel
      · exact hrel
    · exact hrel
  · intro h0
    rw [hd, h0]
  · intro t h1 h2
    rw [hd, h1]
    simp only [if_neg h2]
  · intro t h1 h2 h3
    rw [hd, h1]
    simp only [if_pos h2]
    exact ⟨trivial, memoryRelease_released t _ h3⟩

/-- `mbuf_dealloc`, :120-128, is reached once with a live master: when `mbuf_add_view` refuses
the buffer, :811-819, the `Py_DECREF(mbuf)` releases it. `memoryview(x)` raises `ValueError`,
the managed buffer ends released, and the exporter's `__release_buffer__` has run: the request
that failed does not leak its buffer. Hypothesis: `__buffer__` gave a buffer of more than 64
dimensions, which is the case. -/
def MbufDeallocOnFail : Prop :=
  ∀ (st : St) (b : Buf), 64 < b.ndim →
    let r := memoryviewNew (.exporter (.val b) none) st
    r.1 = .error (.valueError "memoryview: number of dimensions must not exceed 64") ∧
    (r.2.mb st.mbufs.length).released = true ∧
    (∀ t, b.hook = some t → t < st.mvs.length → (st.mv t).exports = 0 → (r.2.mv t).flags.released = true)

theorem mbufDeallocOnFail_proven : MbufDeallocOnFail := by
  intro st b hn
  obtain ⟨m, hg, hnd, hhk⟩ : ∃ m : Buf, simpleGetbuffer b bufFullRO = .ok m ∧ m.ndim = b.ndim ∧
      m.hook = b.hook := by
    have hw : req bufFullRO bufWritable = false := by decide
    refine ⟨{ b with
      format := if req bufFullRO bufFormat then b.format else none,
      shape := if req bufFullRO bufND then b.shape else none,
      strides := if req bufFullRO bufStrides then b.strides else none,
      suboffsets := if req bufFullRO bufIndirect then b.suboffsets else none }, ?_, rfl, rfl⟩
    unfold simpleGetbuffer
    rw [if_neg (by simp [hw])]
  obtain ⟨st2, hst2⟩ : ∃ s2, s2 = let st1 : St := { st with mbufs := st.mbufs ++ [{}] }
      st1.setMb st.mbufs.length { st1.mb st.mbufs.length with master := m } := ⟨_, rfl⟩
  have hmb : st2.mb st.mbufs.length = { master := m } := by
    rw [hst2]
    exact fresh_mb st m
  have hlen : st2.mbufs.length = st.mbufs.length + 1 := by
    rw [hst2]
    simp [St.setMb]
  have hmvs : ∀ j, st2.mv j = st.mv j := by
    intro j
    rw [hst2]
    rfl
  have hmvlen : st2.mvs.length = st.mvs.length := by
    rw [hst2]
    rfl
  have hadd : mbufAddView st.mbufs.length none st2 =
      (.error (.valueError "memoryview: number of dimensions must not exceed 64"), st2) := by
    simp only [mbufAddView, M.bind_app, M.get, Option.getD_none, hmb]
    rw [if_pos (by simpa [hnd] using hn)]
    rfl
  have e : memoryviewNew (.exporter (.val b) none) st =
      (.error (.valueError "memoryview: number of dimensions must not exceed 64"),
        (pyBufferRelease m (st2.setMb st.mbufs.length { st2.mb st.mbufs.length with released := true })).2) := by
    simp only [memoryviewNew, memoryViewFromObject, memoryViewFromObjectAndFlags, M.bind_app, fire,
      M.pure_app, viewOfExporter, managedBufferFromObject, mbufAlloc, M.lift, hg, M.modify, Ret.get_val]
    rw [← hst2]
    simp only [M.onError, hadd, mbufDealloc, mbufRelease, hmb]
    rfl
  dsimp only
  rw [e]
  refine ⟨rfl, ?_, ?_⟩
  · apply (pyBufferRelease_mono _ _).mb
    rw [St.mb_setMb _ _ _ (by omega)]
  · intro t ht hv h0
    apply pyBufferRelease_hook _ _ _ (hhk.trans ht)
    · simpa [St.setMb, hmvlen] using hv
    · show (st2.mv t).exports = 0
      rw [hmvs]
      exact h0

/-- `mbuf_release`, :107-117, and `mbuf_clear`, :139-145: the first release of a managed buffer
marks it and gives its master back, which runs the exporter's `__release_buffer__` or takes back
an export of the view it came from; any later release does nothing. Hypothesis: `k` exists. -/
def MbufReleaseRules : Prop :=
  ∀ (st : St) (k : Nat), k < st.mbufs.length →
    ((st.mb k).released = true → mbufRelease k st = (.ok (), st) ∧ mbufClear k st = (.ok (), st)) ∧
    ((st.mb k).released = false →
      ((mbufClear k st).2.mb k).released = true ∧
      (∀ t, (st.mb k).master.hook = some t → t < st.mvs.length → (st.mv t).exports = 0 →
        ((mbufClear k st).2.mv t).flags.released = true) ∧
      (∀ j, (st.mb k).master.hook = none → (st.mb k).master.obj = some (.mv j) → j < st.mvs.length →
        ((mbufClear k st).2.mv j).exports = (st.mv j).exports - 1))

theorem mbufReleaseRules_proven : MbufReleaseRules := by
  intro st k hk
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have e : mbufRelease k st = (.ok (), st) := by
      simp only [mbufRelease, h, ↓reduceIte]
    exact ⟨e, e⟩
  · obtain ⟨s3, hs3⟩ : ∃ s3, s3 = st.setMb k { st.mb k with released := true } := ⟨_, rfl⟩
    have e : mbufClear k st = pyBufferRelease (st.mb k).master s3 := by
      simp only [mbufClear, mbufRelease, h, Bool.false_eq_true, ↓reduceIte, hs3]
    have hmv : ∀ j, s3.mv j = st.mv j := fun j => by
      rw [hs3]
      exact St.mv_setMb _ _ _ _
    have hlen : s3.mvs.length = st.mvs.length := by
      rw [hs3]
      rfl
    rw [e]
    refine ⟨?_, fun t hh ht h0 => ?_, fun j hh ho hj => ?_⟩
    · apply (pyBufferRelease_mono _ _).mb
      rw [hs3, St.mb_setMb _ _ _ hk]
    · apply pyBufferRelease_hook _ _ _ hh (by rw [hlen]; exact ht)
      rw [hmv]
      exact h0
    · unfold pyBufferRelease
      rw [hh]
      dsimp only
      unfold pyBufferRelease0
      rw [ho]
      dsimp only
      rw [St.mv_setMv _ _ _ (by rw [hlen]; exact hj), hmv]

/-! ## The export held around Python code -/

/-- The view a callback releases by `self.release()` while `withExport self` holds one. -/
theorem fire_held (st : St) (i : Nat) (h : i < st.mvs.length) (h0 : 0 ≤ (st.mv i).exports)
    (s : St) (hs : s = st.setMv i { st.mv i with exports := (st.mv i).exports + 1 }) :
    fire (some i) s = (.ok (), s) := by
  show (if getExports s i = 0 then memoryRelease i s else (.ok (), s)) = _
  have : getExports s i ≠ 0 := by
    rw [getExports, hs, St.mv_setMv _ _ _ h]
    dsimp only
    omega
  rw [if_neg this]

/-- What a `sep` with `__len__` ends in: pystrhex.c takes the length first, then the type. -/
def sepError : Ret Int → PyExc
  | .raises e => e
  | .wrong t => lenWrong t
  | .val n =>
    if n < 0 then .valueError "__len__() should return >= 0"
    else if n ≠ 1 then .valueError "sep must be length 1."
    else .typeError "sep must be str or bytes."

/-- `sep` with `__len__` is never a separator: every outcome is an error, after the callback. -/
theorem strhexWithSepM_len (arg : M (List Nat)) (r : Ret Int) (rel : Option Nat) (bps : Int) (s s' : St)
    (hf : fire rel s = (.ok (), s')) :
    strhexWithSepM arg (some (.lenLike r rel)) bps s = (.error (sepError r), s') := by
  unfold strhexWithSepM
  simp only [M.bind_app, hf]
  cases r with
  | raises e => rfl
  | wrong t => rfl
  | val n =>
    simp only [Ret.get_val, sepError]
    by_cases h1 : n < 0
    · simp [h1, M.bind_app, M.throw_app]
    · by_cases h2 : n = 1
      · simp [h1, h2, M.bind_app, M.throw_app, M.pure_app]
      · simp [h1, h2, M.bind_app, M.throw_app, M.pure_app]

/-- `memoryview_hex_impl`, :2448-2484, with a `sep` whose `__len__` calls `self.release()`.
`hex` raises in every case. A contiguous view hexes its own memory, so it holds an export over
the call (:2463-2465, gh-143195): the release is refused and the view is exactly as before. A
view that is not contiguous hexes a private copy and holds nothing: it is released, and that is
safe, because `bytes` is not the view's memory. Hypotheses: a live view; an export count is not
negative; `tobytes` succeeds, otherwise `__len__` never runs. -/
def HexHoldsExport : Prop :=
  ∀ (st : St) (self : Nat) (r : Ret Int) (bps : Int), self < st.mvs.length →
    baseInaccessible st self = false → 0 ≤ (st.mv self).exports →
    let v := (st.mv self).view
    let out := memoryviewHex self (some (.lenLike r (some self))) bps st
    ((st.mv self).flags.isC = true → out.1 = .error (sepError r) ∧ out.2.mv self = (st.mv self)) ∧
    ((st.mv self).flags.isC = false → (st.mv self).exports = 0 →
      ∀ b, pyBufferToContiguous st.mem v v.len 'C' = .ok b →
      out.1 = .error (sepError r) ∧ (out.2.mv self).flags.released = true)

theorem hexHoldsExport_proven : HexHoldsExport := by
  intro st self r bps hv hl h0
  dsimp only
  refine ⟨fun hC => ?_, fun hC h00 b hb => ?_⟩
  · have he := strhexWithSepM_len
      (fun s => (.ok (rdBytes s.mem (st.mv self).view.buf (st.mv self).view.len.toNat), s)) r (some self) bps
      (st.setMv self { st.mv self with exports := (st.mv self).exports + 1 }) _
      (fire_held st self hv h0 _ rfl)
    have hw := withExport_same self _ st hv he
    have hx : memoryviewHex self (some (.lenLike r (some self))) bps st = (.error (sepError r), st) := by
      simp only [memoryviewHex, M.bind_app, checkReleased_ok _ _ hl, M.get, hC, ↓reduceIte, M.pure_app]
      rw [hw]
    rw [hx]
    exact ⟨rfl, rfl⟩
  · obtain ⟨s, hs⟩ : ∃ s, fire (some self) st = (.ok (), s) := fire_ok _ _
    have hs' : s = (memoryRelease self st).2 := by
      have : fire (some self) st = memoryRelease self st := by
        show (if getExports st self = 0 then memoryRelease self st else (.ok (), st)) = _
        rw [if_pos (show getExports st self = 0 from h00)]
      rw [this] at hs
      rw [hs]
    have he := strhexWithSepM_len (pure b) r (some self) bps st s hs
    have hx : memoryviewHex self (some (.lenLike r (some self))) bps st = (.error (sepError r), s) := by
      simp only [memoryviewHex, M.bind_app, checkReleased_ok _ _ hl, M.get, hC, Bool.false_eq_true,
        ↓reduceIte, M.lift, hb]
      exact he
    rw [hx, hs']
    exact ⟨rfl, memoryRelease_released self st hv⟩

/-- What `memory_hash` checks before it asks the exporter for a hash, :3328-3338. -/
structure HashGuards (st : St) (i : Nat) : Prop where
  valid : i < st.mvs.length
  live : baseInaccessible st i = false
  fresh : (st.mv i).hash = none
  readonly : (st.mv i).view.readonly = true
  format : ∃ c size, getNativeFmtchar ((st.mv i).view.format.getD []) = some (c, size) ∧ isByteFormat c = true

/-- `memory_hash`, :3342-3344, holds an export around `PyObject_Hash(view->obj)` (gh-142664).
A `__hash__` that calls `self.release()` is refused and the view stays live; a `__hash__` that
raises passes its exception up, with the export given back and no cached hash, so a later `hash`
asks again. A `__hash__` that releases another view succeeds at that. Hypotheses: the checks of
the function; an export count is not negative. -/
def HashHoldsExport : Prop :=
  ∀ (st : St) (self e : Nat), HashGuards st self → (st.mv self).view.obj = some (.exp e) →
    0 ≤ (st.mv self).exports →
    (st.hashHook.getD e none = some self →
      let r := memoryHash self st
      (r.2.mv self).flags = (st.mv self).flags ∧ (r.2.mv self).exports = (st.mv self).exports) ∧
    (∀ err, st.unhashable.getD e none = some err →
      (st.hashHook.getD e none = none ∨ st.hashHook.getD e none = some self) →
      memoryHash self st = (.error err, st)) ∧
    (∀ j, st.hashHook.getD e none = some j → j ≠ self → j < st.mvs.length → (st.mv j).exports = 0 →
      ((memoryHash self st).2.mv j).flags.released = true)

/-- The end of `memory_hash`, :3348-3368: the bytes, and the cache. -/
def hashTail (st : St) (self : Nat) : M (List Nat) := do
  let mem ← if !(st.mv self).flags.isC then M.lift (bufferToContiguous st.mem (st.mv self).view 'C')
    else pure (rdBytes st.mem (st.mv self).view.buf (st.mv self).view.len.toNat)
  M.modify fun st => st.setMv self { st.mv self with hash := some mem }
  return mem

theorem hash_split (st : St) (self e : Nat) (h : HashGuards st self)
    (ho : (st.mv self).view.obj = some (.exp e)) :
    memoryHash self st =
      (withExport self (do
        fire (st.hashHook.getD e none)
        match st.unhashable.getD e none with
        | some err => throw err
        | Option.none => pure ()) >>= fun _ => hashTail st self) st := by
  obtain ⟨c, size, hf, hb⟩ := h.format
  have hc := checkReleased_ok st self h.live
  unfold memoryHash hashTail
  simp only [memoryHashF, M.bind_app, M.get, h.fresh, hc, h.readonly, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, hf, hb, M.pure_app, ho]
  rfl

theorem hashTail_keeps (st : St) (self : Nat) (s : St) (hv : self < s.mvs.length) :
    ((hashTail st self s).2.mv self).flags = (s.mv self).flags ∧
      ((hashTail st self s).2.mv self).exports = (s.mv self).exports := by
  unfold hashTail
  by_cases hC : (st.mv self).flags.isC = true
  · simp only [M.bind_app, hC, Bool.not_true, Bool.false_eq_true, ↓reduceIte, M.pure_app, M.modify]
    rw [St.mv_setMv _ _ _ hv]
    exact ⟨rfl, rfl⟩
  · simp only [M.bind_app, hC, Bool.not_false, ↓reduceIte, M.lift, Bool.not_eq_true]
    cases hb : bufferToContiguous st.mem (st.mv self).view 'C' with
    | error x => exact ⟨rfl, rfl⟩
    | ok b =>
      simp only [M.modify, M.pure_app]
      rw [St.mv_setMv _ _ _ hv]
      exact ⟨rfl, rfl⟩

theorem hashTail_mono (st : St) (self : Nat) (s : St) : Mono s (hashTail st self s).2 := by
  unfold hashTail
  by_cases hC : (st.mv self).flags.isC = true
  · simp only [M.bind_app, hC, Bool.not_true, Bool.false_eq_true, ↓reduceIte, M.pure_app, M.modify]
    exact Mono.setMv _ _ _ id rfl rfl
  · simp only [M.bind_app, hC, Bool.not_false, ↓reduceIte, M.lift, Bool.not_eq_true]
    cases hb : bufferToContiguous st.mem (st.mv self).view 'C' with
    | error x => exact Mono.refl _
    | ok b =>
      simp only [M.modify, M.pure_app]
      exact Mono.setMv _ _ _ id rfl rfl

theorem hashHoldsExport_proven : HashHoldsExport := by
  intro st self e h ho h0
  have hv := h.valid
  have hsplit := hash_split st self e h ho
  have held := fire_held st self hv h0 _ rfl
  have body : ∀ k : Option Nat, (k = Option.none ∨ k = some self) →
      ∀ s, s = st.setMv self { st.mv self with exports := (st.mv self).exports + 1 } →
      fire k s = (.ok (), s) := by
    intro k hk s hs
    rcases hk with rfl | rfl
    · rfl
    · rw [hs]
      exact held
  refine ⟨fun hk => ?_, fun err hu hk => ?_, fun j hk hne hj h00 => ?_⟩
  · cases hu : st.unhashable.getD e Option.none with
    | none =>
      have hw : withExport self (do
          fire (st.hashHook.getD e Option.none)
          match st.unhashable.getD e Option.none with
          | some err => throw err
          | Option.none => pure ()) st = (.ok (), st) := by
        apply withExport_same _ _ _ hv
        simp only [M.bind_app, body _ (Or.inr hk) _ rfl, hu, M.pure_app]
      dsimp only
      rw [hsplit, M.bind_app, hw]
      exact hashTail_keeps st self st hv
    | some err =>
      have hw : withExport self (do
          fire (st.hashHook.getD e Option.none)
          match st.unhashable.getD e Option.none with
          | some err => throw err
          | Option.none => pure ()) st = (.error err, st) := by
        apply withExport_same _ _ _ hv
        simp only [M.bind_app, body _ (Or.inr hk) _ rfl, hu, M.throw_app]
      dsimp only
      rw [hsplit, M.bind_app, hw]
      exact ⟨rfl, rfl⟩
  · have hw : withExport self (do
        fire (st.hashHook.getD e Option.none)
        match st.unhashable.getD e Option.none with
        | some err => throw err
        | Option.none => pure ()) st = (.error err, st) := by
      apply withExport_same _ _ _ hv
      simp only [M.bind_app, body _ hk _ rfl, hu, M.throw_app]
    rw [hsplit, M.bind_app, hw]
  · -- the release happens at the bumped state, and every later step keeps it
    obtain ⟨s0, hs0⟩ : ∃ s0, s0 = st.setMv self { st.mv self with exports := (st.mv self).exports + 1 } :=
      ⟨_, rfl⟩
    have hj0 : s0.mvs.length = st.mvs.length := by
      rw [hs0]
      simp [St.setMv]
    have hmvj : s0.mv j = st.mv j := by
      rw [hs0]
      exact St.mv_setMv_ne _ _ _ _ (Ne.symm hne)
    have hf : fire (some j) s0 = memoryRelease j s0 := by
      show (if getExports s0 j = 0 then memoryRelease j s0 else (.ok (), s0)) = _
      rw [if_pos (by rw [getExports, hmvj]; exact h00)]
    obtain ⟨s1, hs1⟩ : ∃ s1, fire (some j) s0 = (.ok (), s1) := fire_ok _ _
    have hrel : (s1.mv j).flags.released = true := by
      have h1 := memoryRelease_released j s0 (by rw [hj0]; exact hj)
      rw [← hf, hs1] at h1
      exact h1
    have hmono : Mono s1 (s1.setMv self { s1.mv self with exports := (s1.mv self).exports + -1 }) :=
      Mono.setMv _ _ _ id rfl rfl
    rw [hsplit, M.bind_app]
    simp only [withExport, ← hs0, M.bind_app, hk, hs1]
    cases hu : st.unhashable.getD e Option.none with
    | none =>
      simp only [M.pure_app]
      exact (hashTail_mono st self _).mv j (hmono.mv j hrel)
    | some err =>
      simp only [M.throw_app]
      exact hmono.mv j hrel

/-- `memory_hash` when the exporter is another memoryview: `PyObject_Hash(view->obj)` is
`memory_hash` of that view, under the same held export. A cached hash there lets this view go on;
a view that cannot be hashed passes its `ValueError` up, with this view left without a hash and its
export given back. Hypotheses: the checks of the function, on two different views. -/
def HashViewExporter : Prop :=
  ∀ (st : St) (self i : Nat), HashGuards st self → (st.mv self).view.obj = some (.mv i) → i ≠ self →
    (∀ h, (st.mv i).hash = some h → (memoryHash self st).1 = (hashTail st self st).1) ∧
    ((st.mv i).hash = none → baseInaccessible st i = false → (st.mv i).view.readonly = false →
      memoryHash self st = (.error (.valueError "cannot hash writable memoryview object"), st))

theorem hashViewExporter_proven : HashViewExporter := by
  intro st self i h ho hne
  obtain ⟨c, size, hf, hb⟩ := h.format
  have hc := checkReleased_ok st self h.live
  have hv := h.valid
  obtain ⟨s0, hs0⟩ : ∃ s0, s0 = st.setMv self { st.mv self with exports := (st.mv self).exports + 1 } :=
    ⟨_, rfl⟩
  have hmvi : s0.mv i = st.mv i := by
    rw [hs0]
    exact St.mv_setMv_ne _ _ _ _ (Ne.symm hne)
  obtain ⟨k, hk⟩ : ∃ k, st.mvs.length = k + 1 := ⟨st.mvs.length - 1, by omega⟩
  have hsplit : memoryHash self st =
      (withExport self (memoryHashF st.mvs.length i) >>= fun _ => hashTail st self) st := by
    unfold memoryHash hashTail
    simp only [memoryHashF, M.bind_app, M.get, h.fresh, hc, h.readonly, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, hf, hb, M.pure_app, ho]
  constructor
  · intro x hx
    have hin : memoryHashF st.mvs.length i s0 = (.ok x, s0) := by
      rw [hk]
      simp only [memoryHashF, M.bind_app, M.get, hmvi, hx, M.pure_app]
    have hw : withExport self (memoryHashF st.mvs.length i) st = (.ok x, st) :=
      withExport_same _ _ _ hv (by rw [← hs0]; exact hin)
    rw [hsplit, M.bind_app, hw]
  · intro h1 h2 h3
    have hl0 : baseInaccessible s0 i = false := by
      have hmb : ∀ j, s0.mb j = st.mb j := fun j => by rw [hs0]; rfl
      simp only [baseInaccessible, hmvi, hmb] at h2 ⊢
      exact h2
    have hin : memoryHashF st.mvs.length i s0 =
        (.error (.valueError "cannot hash writable memoryview object"), s0) := by
      rw [hk]
      simp only [memoryHashF, M.bind_app, M.get, hmvi, h1, checkReleased_ok _ _ hl0, h3, Bool.not_false,
        ↓reduceIte, M.throw_app]
    have hw : withExport self (memoryHashF st.mvs.length i) st =
        (.error (.valueError "cannot hash writable memoryview object"), st) :=
      withExport_same _ _ _ hv (by rw [← hs0]; exact hin)
    rw [hsplit, M.bind_app, hw]

/-! ## `memory_richcompare` gives the buffer back -/

theorem getBufferFull_val (b : Buf) (st : St) (hn : b.ndim ≤ 64) :
    getBufferFull (.exporter (.val b) none) st = (.ok b, st) := by
  simp only [getBufferFull, M.bind_app, fire, M.pure_app, Ret.get_val]
  rw [if_neg (by omega)]
  rfl

/-- `memory_richcompare`, :3303-3310: the right side's buffer is released after the result is
known, and that release is Python code when the right side has `__release_buffer__`. `v == w`
gives what the two buffers compare to, even when that callback releases `v` itself, and the
callback's release has happened by the time `==` returns. Hypotheses: a live `v`; `__buffer__`
succeeds with a valid buffer (`__buffer__` failing is `NotImplemented`, `BufferFailures`). -/
def CompareReleases : Prop :=
  ∀ (st : St) (v t : Nat) (b : Buf), baseInaccessible st v = false → b.ndim ≤ 64 → b.hook = some t →
    t < st.mvs.length → (st.mv t).exports = 0 →
    let r := memoryRichEqual v (.exporter (.val b) none) st
    r.1 = some <$> compareBufs st.mem st.noStruct (st.mv v).view b ∧ (r.2.mv t).flags.released = true

theorem compareReleases_proven : CompareReleases := by
  intro st v t b hl hn hh ht h0
  have gb := getBufferFull_val b st hn
  have tc : (tryCatch (some <$> getBufferFull (.exporter (.val b) none))
      (fun _ => pure Option.none) : M (Option Buf)) st = (.ok (some b), st) := by
    have hm : (some <$> getBufferFull (.exporter (.val b) none) : M (Option Buf)) st = (.ok (some b), st) := by
      show (getBufferFull (.exporter (.val b) none) >>= fun a => pure (some a)) st = _
      rw [M.bind_app, gb]
      rfl
    simp [tryCatch, MonadExcept.tryCatch, hm]
  have hrel := pyBufferRelease_hook b t st hh ht h0
  have hok := pyBufferRelease_ok b st
  have e : memoryRichEqual v (.exporter (.val b) none) st =
      (some <$> compareBufs st.mem st.noStruct (st.mv v).view b, (pyBufferRelease b st).2) := by
    simp only [memoryRichEqual, M.bind_app, M.get, hl, Bool.false_eq_true, ↓reduceIte, tc]
    rcases hr : pyBufferRelease b st with ⟨r0, s⟩
    rw [hr] at hok
    simp only at hok
    subst hok
    simp only [M.lift, M.pure_app]
    cases compareBufs st.mem st.noStruct (st.mv v).view b <;> rfl
  dsimp only
  rw [e]
  exact ⟨rfl, hrel⟩

/-! ## `__eq__` in `count` and `index` -/

theorem iter_released (st : St) (it self : Nat) (index n : Int) (fmt : List Char)
    (hI : IterAt st it self index n fmt) (h : index < n) (hr : baseInaccessible st self = true) :
    memoryiterNext it st = (.error releasedError, st) := by
  simp only [memoryiterNext, M.bind_app, M.get, hI.state, h, ↓reduceIte, checkReleased_err _ _ hr]

/-- `Ret.get` of a value of an `__eq__`, and the release a callback does. -/
theorem fire_self (st : St) (i : Nat) (h : getExports st i = 0) :
    fire (some i) st = memoryRelease i st := by
  show (if getExports st i = 0 then memoryRelease i st else (.ok (), st)) = _
  rw [if_pos h]

theorem released_inaccessible (st : St) (i : Nat) (h : (st.mv i).flags.released = true) :
    baseInaccessible st i = true := by
  simp [baseInaccessible, h]

/-- The start of `count`: an iterator at item 0, and `self`'s buffer as it was. -/
theorem count_start (st : St) (self : Nat) (n d : Int) (f : List Char) (c : Char) (value : Obj)
    (hL : Live1D st self n d f) (hf : adjustFmt (st.mv self).view = .ok [c]) :
    memoryviewCount self value st =
      countLoop st.iters.length value (n.toNat + 2) 0 (newIter st self n [c]) := by
  have hlen : ((newIter st self n [c]).iters.getD st.iters.length default).length = n := by
    simp [newIter, List.getD_eq_getElem?_getD]
  simp only [memoryviewCount, M.bind_app, memoryIter_spec st self n d f [c] hL hf, M.get, hlen]

/-- The loops of `memoryview_count_impl`, :2908-2927, and `memoryview_index_impl`, :2983-3006,
with a value whose `__eq__` runs Python code. An exception from `__eq__` is passed up at once. An
`__eq__` that calls `self.release()` succeeds, because an iterator holds no export, and the next
step refuses with the `CHECK_RELEASED` of `memoryiter_next` or `memory_item`. On a view of one
item there is no next step, so `count` returns normally. Hypotheses: a live, native-format view
with no export left to refuse the release; `NoNull`, a type invariant. -/
def EqFailures : Prop :=
  ∀ (st : St) (self : Nat) (n d : Int) (f : List Char) (c : Char),
    Live1D st self n d f → adjustFmt (st.mv self).view = .ok [c] → nativeChar c = true →
    NoNull st self d n → 0 < n →
    (∀ e rel, (memoryviewCount self (.eqLike (.raises e) rel) st).1 = .error e) ∧
    (∀ e rel, (memoryviewIndex self (.eqLike (.raises e) rel) 0 n st).1 = .error e) ∧
    (getExports st self = 0 →
      (1 < n → ∀ b, (memoryviewCount self (.eqLike (.val b) (some self)) st).1 = .error releasedError) ∧
      (1 < n → (memoryviewIndex self (.eqLike (.val false) (some self)) 0 n st).1 = .error releasedError) ∧
      (n = 1 → ∀ b : Bool, (memoryviewCount self (.eqLike (.val b) (some self)) st).1 =
        .ok (if b then 1 else 0)))

theorem index_start (st : St) (self : Nat) (n : Int) (value : Obj) (d : Int) (f : List Char)
    (hL : Live1D st self n d f) (hn : 0 < n) :
    memoryviewIndex self value 0 n st = indexLoop self value (n + 1).toNat 0 n st := by
  have h1 : min n n = n := by omega
  have h2 : min (0 : Int) n = 0 := by omega
  simp only [memoryviewIndex, M.bind_app, checkReleased_ok _ _ hL.live, M.get, hL.ndim, Nat.one_ne_zero,
    ↓reduceIte, hL.shape, Option.getD_some, List.getD_cons_zero]
  rw [if_neg (by omega), if_neg (by omega), h1, h2]
  simp only [Int.sub_zero]

/-- The first item of `indexLoop`. -/
theorem index_first (st : St) (self : Nat) (n d : Int) (f fmt : List Char) (g : Int → Item)
    (hL : Live1D st self n d f) (hf : adjustFmt (st.mv self).view = .ok fmt)
    (hg : ItemAt st self fmt g) (hn : 0 < n) :
    memoryItem self 0 st = (.ok (g (st.mv self).view.buf), st) := by
  have hm := memoryItem_eq st self 0 n d f fmt hL hf
  rw [lookup_in _ _ _ 0 n d hL.shape hL.strides (by omega)] at hm
  have hg' : ∀ p, unpackRaw st.mem (adjustPtr st.mem p (st.mv self).view.suboffsets 0) fmt = .ok (g p) := hg
  simp only [pos, show ¬ (0 : Int) < 0 by omega, ↓reduceIte, Int.mul_zero, Int.add_zero, hg'] at hm
  exact hm

theorem memoryItem_released (st : St) (self : Nat) (i : Int) (h : baseInaccessible st self = true) :
    memoryItem self i st = (.error releasedError, st) := by
  simp only [memoryItem, M.bind_app, checkReleased_err _ _ h]

theorem eqFailures_proven : EqFailures := by
  intro st self n d f c hL hf hc hnn hpos
  obtain ⟨g0, hg0⟩ := native_total st.mem c hc
  have hg : ItemAt st self [c] (fun p => g0 (adjustPtr st.mem p (st.mv self).view.suboffsets 0)) :=
    fun p => hg0 _
  have hL' : Live1D (newIter st self n [c]) self n d f := live_iters st self n d f _ hL
  have hI := iterAt_new st self n [c]
  have hnn' : NoNull (newIter st self n [c]) self d n := hnn
  have e0 := iter_step (newIter st self n [c]) st.iters.length self 0 n d f [c] hL' hI hpos (Int.le_refl 0)
    hnn' _ hg
  have hk : n.toNat + 2 = (n.toNat + 1) + 1 := rfl
  obtain ⟨s1, hs1⟩ : ∃ s1, s1 = stepIter (newIter st self n [c]) st.iters.length self 0 n [c] := ⟨_, rfl⟩
  have hI1 : IterAt s1 st.iters.length self (0 + 1) n [c] := hs1 ▸ iterAt_step _ _ _ _ _ _ hI
  rw [← hs1] at e0
  have hn1 : (n + 1).toNat = (n.toNat) + 1 := by omega
  -- the release by `__eq__`, on the iterator's state and on the plain state
  have after : ∀ s : St, self < s.mvs.length → getExports s self = 0 →
      ∃ s2, fire (some self) s = (.ok (), s2) ∧ Mono s s2 ∧ baseInaccessible s2 self = true := by
    intro s hv hex
    obtain ⟨s2, hs2⟩ := fire_ok (some self) s
    have hm := (fire_self s self hex).symm.trans hs2
    have hmono := memoryRelease_mono self s
    have hr := memoryRelease_released self s hv
    rw [hm] at hmono hr
    exact ⟨s2, hs2, hmono, released_inaccessible _ _ hr⟩
  refine ⟨fun e rel => ?_, fun e rel => ?_, fun h0 => ⟨fun h1 b => ?_, fun h1 => ?_, fun h1 b => ?_⟩⟩
  · obtain ⟨s, hs⟩ := fire_ok rel s1
    rw [count_start st self n d f c _ hL hf, hk]
    simp only [countLoop, M.bind_app, e0, itemEqM, hs, Ret.get, M.throw_app]
  · obtain ⟨s, hs⟩ := fire_ok rel st
    rw [index_start st self n _ d f hL hpos, hn1, indexLoop]
    simp only [hpos, ↓reduceIte, M.bind_app, index_first st self n d f [c] _ hL hf hg hpos, itemEqM, hs,
      Ret.get, M.throw_app]
  · obtain ⟨s2, hs2, hmono, hr⟩ := after s1 (by rw [hs1]; exact hL.valid) (by rw [hs1]; exact h0)
    have hI2 : IterAt s2 st.iters.length self (0 + 1) n [c] :=
      ⟨by rw [hmono.iters]; exact hI1.valid, by rw [hmono.iters]; exact hI1.state⟩
    have hstop := iter_released s2 _ self (0 + 1) n [c] hI2 (by omega) hr
    rw [count_start st self n d f c _ hL hf, hk]
    simp only [countLoop, M.bind_app, e0, itemEqM, hs2, Ret.get, M.pure_app, hstop]
  · obtain ⟨s2, hs2, -, hr⟩ := after st hL.valid h0
    obtain ⟨k, hk'⟩ : ∃ k, n.toNat = k + 1 := ⟨n.toNat - 1, by omega⟩
    have hloop : indexLoop self (.eqLike (.val false) (some self)) n.toNat (0 + 1) n s2 =
        (.error releasedError, s2) := by
      rw [hk', indexLoop, if_pos (by omega)]
      simp only [M.bind_app, memoryItem_released _ _ _ hr]
    rw [index_start st self n _ d f hL hpos, hn1, indexLoop]
    simp only [hpos, ↓reduceIte, M.bind_app, index_first st self n d f [c] _ hL hf hg hpos, itemEqM, hs2,
      Ret.get, M.pure_app, Bool.false_eq_true]
    rw [hloop]
  · obtain ⟨s2, hs2, hmono, -⟩ := after s1 (by rw [hs1]; exact hL.valid) (by rw [hs1]; exact h0)
    have hI2 : IterAt s2 st.iters.length self (0 + 1) n [c] :=
      ⟨by rw [hmono.iters]; exact hI1.valid, by rw [hmono.iters]; exact hI1.state⟩
    have hstop := iter_stop s2 _ self (0 + 1) n [c] hI2 (by omega)
    rw [count_start st self n d f c _ hL hf, hk]
    simp only [countLoop, M.bind_app, e0, itemEqM, hs2, Ret.get, M.pure_app, hstop]
    cases b <;> rfl

/-! ## Views that are not 1-D -/

/-- What iteration, `len`, `count`, `index` and `m[i]` do on views that are not 1-D. `len` is
`shape[0]` on every view with dimensions (:2857-2867), and a 0-dim view has none. A 0-dim view
has no iterator, no items and no lookup (:3640-3643, :2577-2580, :2958-2961); a view of two or more
dimensions refuses them as not implemented (:3644-3648, :2587-2589, :3011-3014), and so does
`count`, which iterates. Hypotheses: a live view, and for `m[i]` a format `adjust_fmt` accepts. -/
def RankRules : Prop :=
  ∀ (st : St) (self : Nat) (v : Obj) (a b i : Int) (fmt : List Char),
    baseInaccessible st self = false → adjustFmt (st.mv self).view = .ok fmt →
    let x := (st.mv self).view
    (x.ndim ≠ 0 → memoryLength self st = (.ok ((x.shape.getD []).getD 0 0), st)) ∧
    (x.ndim = 0 →
      memoryLength self st = (.error (.typeError "0-dim memory has no length"), st) ∧
      memoryIter self st = (.error (.typeError "invalid indexing of 0-dim memory"), st) ∧
      memoryviewCount self v st = (.error (.typeError "invalid indexing of 0-dim memory"), st) ∧
      memoryviewIndex self v a b st = (.error (.typeError "invalid lookup on 0-dim memory"), st) ∧
      memoryItem self i st = (.error (.typeError "invalid indexing of 0-dim memory"), st)) ∧
    (2 ≤ x.ndim →
      memoryIter self st = (.error (notImplError "multi-dimensional sub-views are not implemented"), st) ∧
      memoryviewCount self v st =
        (.error (notImplError "multi-dimensional sub-views are not implemented"), st) ∧
      memoryviewIndex self v a b st = (.error (notImplError "multi-dimensional lookup is not implemented"), st) ∧
      memoryItem self i st = (.error (notImplError "multi-dimensional sub-views are not implemented"), st))

theorem rankRules_proven : RankRules := by
  intro st self v a b i fmt hl hf
  have hc := checkReleased_ok st self hl
  dsimp only
  refine ⟨fun h => ?_, fun h => ⟨?_, ?_, ?_, ?_, ?_⟩, fun h => ?_⟩
  · simp only [memoryLength, M.bind_app, hc, M.get, h, ↓reduceIte, M.pure_app]
  · simp only [memoryLength, M.bind_app, hc, M.get, h, ↓reduceIte, M.throw_app]
  · simp only [memoryIter, M.bind_app, hc, M.get, h, ↓reduceIte, M.throw_app]
  · simp only [memoryviewCount, memoryIter, M.bind_app, hc, M.get, h, ↓reduceIte, M.throw_app]
  · simp only [memoryviewIndex, M.bind_app, hc, M.get, h, ↓reduceIte, M.throw_app]
  · simp only [memoryItem, M.bind_app, hc, M.get, M.lift, hf, h, ↓reduceIte, M.throw_app]
  · have h0 : ¬ (st.mv self).view.ndim = 0 := by omega
    have h1 : ¬ (st.mv self).view.ndim = 1 := by omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [memoryIter, M.bind_app, hc, M.get, h0, h1, ↓reduceIte, ne_eq, not_false_eq_true,
        M.throw_app]
    · simp only [memoryviewCount, memoryIter, M.bind_app, hc, M.get, h0, h1, ↓reduceIte, ne_eq,
        not_false_eq_true, M.throw_app]
    · simp only [memoryviewIndex, M.bind_app, hc, M.get, h0, h1, ↓reduceIte, M.throw_app]
    · simp only [memoryItem, M.bind_app, hc, M.get, M.lift, hf, h0, h1, ↓reduceIte, M.throw_app]

/-! ## `ptr == NULL` in `memoryiter_next` -/

/-- `memoryiter_next`, :3619-3621: an item at `NULL` returns NULL with no exception set, which
is `StopIteration`, though the iterator has not reached `it_length` and keeps its view: it has
stepped past the item, so the next `next` goes on from the item after. Hypotheses: a live view,
the iterator inside it, and the case itself, the item's address being `NULL`. -/
def IterNull : Prop :=
  ∀ (st : St) (it self : Nat) (index n d : Int) (f fmt : List Char),
    Live1D st self n d f → IterAt st it self index n fmt → index < n →
    adjustPtr st.mem ((st.mv self).view.buf + d * index) (st.mv self).view.suboffsets 0 = nullPtr →
    memoryiterNext it st = (.ok none, stepIter st it self index n fmt) ∧
      IterAt (stepIter st it self index n fmt) it self (index + 1) n fmt

theorem iterNull_proven : IterNull := by
  intro st it self index n d f fmt hL hI h hp
  refine ⟨?_, iterAt_step st it self index n fmt hI⟩
  simp only [memoryiterNext, M.bind_app, M.get, hI.state, h, ↓reduceIte, checkReleased_ok _ _ hL.live,
    hL.strides, Option.getD_some, List.getD_cons_zero, M.modify, M.pure_app, hp]
  rfl

/-! ## Slices whose parts run Python code -/

theorem sliceStage_hit (rel : Option Nat) (f : SliceFail) (e : PyExc) (s s' : St)
    (hf : fire rel s = (.ok (), s'))
    (hfail : ∀ s', (f.how.get indexWrong : M Unit) s' = (.error e, s')) :
    sliceStage f.part f.part rel (some f) s = (.error e, s') := by
  simp only [sliceStage, ↓reduceIte, M.bind_app, hf, hfail]

theorem sliceStage_miss (a p : SlicePart) (rel : Option Nat) (fail : Option SliceFail) (s : St) (h : p ≠ a) :
    sliceStage a p rel fail s = (.ok (), s) := by
  simp only [sliceStage, h, ↓reduceIte, M.pure_app]

/-- `PySlice_Unpack`, Objects/sliceobject.c:219-259, on a slice with a part that fails: `step`
is converted first, so its failure comes first; a zero step is refused next, so with a zero step
the `__index__` of `start` and `stop` never runs; then `start`, then `stop`. Hypothesis: the
failing part's callback fails with `e`, the case. -/
def SliceFailures : Prop :=
  ∀ (s : PyLean.RangeSlice.Slice) (rel : Option Nat) (f : SliceFail) (e : PyExc) (st : St),
    (∀ s', (f.how.get indexWrong : M Unit) s' = (.error e, s')) →
    (f.part = .step → (sliceEvents s rel (some f) st).1 = .error e) ∧
    (f.part ≠ .step → s.step = some 0 →
      sliceEvents s rel (some f) st = (.error (.valueError "slice step cannot be zero"), st)) ∧
    (f.part ≠ .step → s.step ≠ some 0 → (sliceEvents s rel (some f) st).1 = .error e)

theorem sliceEvents_fail (s : PyLean.RangeSlice.Slice) (rel : Option Nat) (f : SliceFail) (e : PyExc) (st : St)
    (hfail : ∀ s', (f.how.get indexWrong : M Unit) s' = (.error e, s'))
    (h : f.part = .step ∨ s.step ≠ some 0) :
    ∃ s', sliceEvents s rel (some f) st = (.error e, s') ∧ fire rel st = (.ok (), s') := by
  obtain ⟨s', hs⟩ := fire_ok rel st
  refine ⟨s', ?_, hs⟩
  have hp : slicePartOf s (some f) = f.part := rfl
  unfold sliceEvents
  simp only [M.bind_app, hp]
  cases hc : f.part with
  | step =>
    rw [← hc, sliceStage_hit rel f e _ _ hs hfail]
  | start =>
    have h0 : s.step ≠ some 0 := by
      rcases h with h | h
      · rw [hc] at h
        cases h
      · exact h
    rw [sliceStage_miss .start .step rel (some f) st (by decide)]
    simp only [if_neg h0, M.bind_app]
    rw [← hc, sliceStage_hit rel f e _ _ hs hfail]
  | stop =>
    have h0 : s.step ≠ some 0 := by
      rcases h with h | h
      · rw [hc] at h
        cases h
      · exact h
    rw [sliceStage_miss .stop .step rel (some f) st (by decide)]
    simp only [if_neg h0, M.bind_app]
    rw [sliceStage_miss .stop .start rel (some f) st (by decide)]
    dsimp only
    rw [← hc, sliceStage_hit rel f e _ _ hs hfail]

theorem sliceFailures_proven : SliceFailures := by
  intro s rel f e st hfail
  refine ⟨fun h => ?_, fun h h0 => ?_, fun _ h0 => ?_⟩
  · obtain ⟨s', he, -⟩ := sliceEvents_fail s rel f e st hfail (Or.inl h)
    rw [he]
  · unfold sliceEvents
    simp only [M.bind_app, show slicePartOf s (some f) = f.part from rfl]
    rw [sliceStage_miss _ _ _ _ _ (Ne.symm h)]
    simp only [h0, ↓reduceIte, M.throw_app, M.bind_app]
  · obtain ⟨s', he, -⟩ := sliceEvents_fail s rel f e st hfail (Or.inr h0)
    rw [he]

/-- `memory_subscript`, :2619-2626, and `memory_ass_sub`, :2702-2721, when `PySlice_Unpack`
fails. `m[s]` has already made the sliced view with `mbuf_add_view`, and the `Py_DECREF(sliced)`
gives its export of the managed buffer back; `m[s] = x` has already asked `x` for its buffer,
and gives that back, running its `__release_buffer__`. Hypotheses: a live 1-D view, the failing
part as in `SliceFailures`, a buffer of `self` that counts `self` among its views (type
invariant, needed for the export count); for `m[s] = x`, a writable view of a format `adjust_fmt`
accepts, and no earlier callback. -/
def SliceCleanup : Prop :=
  ∀ (st : St) (self : Nat) (n d : Int) (fm : List Char) (s : PyLean.RangeSlice.Slice) (f : SliceFail)
    (e : PyExc),
    Live1D st self n d fm → (∀ s', (f.how.get indexWrong : M Unit) s' = (.error e, s')) →
    (f.part = .step ∨ s.step ≠ some 0) →
    (∀ rel, (memorySubscript self (.one (.slice s rel (some f))) st).1 = .error e) ∧
    ((st.mb (st.mv self).mbuf).exports ≠ 0 →
      ((memorySubscript self (.one (.slice s none (some f))) st).2.mb (st.mv self).mbuf).exports =
        (st.mb (st.mv self).mbuf).exports) ∧
    (∀ (src : Buf) (t : Nat) (fmt : List Char), adjustFmt (st.mv self).view = .ok fmt →
      (st.mv self).view.readonly = false → src.ndim ≤ 64 → src.hook = some t → t < st.mvs.length →
      (st.mv t).exports = 0 →
      let r := memoryAssSub self (.one (.slice s none (some f))) (some (.exporter (.val src) none)) st
      r.1 = .error e ∧ (r.2.mv t).flags.released = true)

theorem memoryRelease_exports (s : St) (i : Nat) (hnr : (s.mv i).flags.released = false)
    (hne : (s.mb (s.mv i).mbuf).exports - 1 ≠ 0) (hk : (s.mv i).mbuf < s.mbufs.length) :
    ((memoryRelease i s).2.mb (s.mv i).mbuf).exports = (s.mb (s.mv i).mbuf).exports - 1 := by
  unfold memoryRelease
  dsimp only
  rw [if_neg (by simp [hnr])]
  split
  · rename_i hc
    simp only [St.mb_setMv] at hc
    exact absurd hc hne
  · dsimp only
    rw [St.mb_setMb _ _ _ (show (s.mv i).mbuf < (s.setMv i _).mbufs.length from hk)]
    simp only [St.mb_setMv]

theorem sliceCleanup_proven : SliceCleanup := by
  intro st self n d fm s f e hL hfail hcase
  have hnd : ¬ (st.mv self).view.ndim = 0 := by rw [hL.ndim]; omega
  have hview : viewCopy (st.mv self).view = (st.mv self).view :=
    viewCopy_1d _ n d fm hL.ndim hL.shape hL.strides hL.subs hL.format
  have ⟨hr1, hA⟩ := mbufAddView_added (st.mv self).mbuf (st.mv self).view st (by rw [hL.ndim]; omega)
  rw [hview] at hA
  rcases hrr : mbufAddView (st.mv self).mbuf (some (st.mv self).view) st with ⟨r1, s1⟩
  rw [hrr] at hr1 hA
  simp only at hr1 hA
  subst hr1
  have hsub : ∀ rel s', sliceEvents s rel (some f) s1 = (.error e, s') →
      memorySubscript self (.one (.slice s rel (some f))) st =
        (.error e, (memoryDealloc st.mvs.length s').2) := by
    intro rel s' h
    simp only [memorySubscript, M.bind_app, checkReleased_ok _ _ hL.live, M.get, hnd, ↓reduceIte,
      checkRestricted_ok _ _ hL.unres, hrr]
    simp only [M.onError, M.bind_app, h]
  refine ⟨fun rel => ?_, fun hne => ?_, fun src t fmt hf hro hn hh ht h0 => ?_⟩
  · obtain ⟨s', he, -⟩ := sliceEvents_fail s rel f e s1 hfail hcase
    rw [hsub rel s' he]
  · obtain ⟨s', he, hs'⟩ := sliceEvents_fail s Option.none f e s1 hfail hcase
    have hs1 : s' = s1 := by
      simpa [fire, pure] using hs'.symm
    subst hs1
    rw [hsub Option.none _ he]
    have hk := hL.mbuf
    have hnew := hA.new
    -- the view just made is on `self`'s buffer, unreleased, with no weakref
    have hdeal : memoryDealloc st.mvs.length s' = memoryRelease st.mvs.length s' := by
      unfold memoryDealloc
      rw [hnew]
    have hrel0 : (initFlags (st.mv self).view).released = false := by
      unfold initFlags
      dsimp only
      split <;> first | rfl | (split <;> first | rfl | (split <;> rfl))
    have hm : (s'.mv st.mvs.length).mbuf = (st.mv self).mbuf := by rw [hnew]
    have hexp := hA.exports hk
    have hx := memoryRelease_exports s' st.mvs.length (by rw [hnew]; exact hrel0)
      (by rw [hm, hexp]; omega) (by rw [hm, hA.mbufs]; exact hk)
    rw [hm, hexp] at hx
    dsimp only
    rw [hdeal, hx]
    omega
  · have hgb := getBufferFull_val src st hn
    obtain ⟨s', he, hs'⟩ := sliceEvents_fail s Option.none f e st hfail hcase
    have hs1 : s' = st := by
      simpa [fire, pure] using hs'.symm
    subst hs1
    have e1 : memoryAssSub self (.one (.slice s Option.none (some f))) (some (.exporter (.val src) Option.none)) s' =
        (.error e, (pyBufferRelease src s').2) := by
      simp only [memoryAssSub, M.bind_app, checkReleased_ok _ _ hL.live, M.get, M.lift, hf, hro,
        Bool.false_eq_true, ↓reduceIte, hL.ndim, Nat.one_ne_zero, hgb, M.onError, he]
    dsimp only
    rw [e1]
    exact ⟨rfl, pyBufferRelease_hook src t s' hh ht h0⟩

end PyLean.BytesObj.Mem
