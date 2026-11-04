import PyLean.PyIO.StringExtra

/-!
`_pyio.TextIOWrapper.__next__` and `flush` and the `tell()` they disable and re-enable
(`Lib/_pyio.py:2255-2257`, :2409-2413, :2629-2636), over the `_pyio.StringIO` model.
-/

namespace PyLean.PyIO

open PyLean

def disabledErr : PyExc := osError "telling position disabled by next() call"

/-- What the decoder can raise. -/
def DecErr (e : PyExc) : Prop := e = unicodeDecodeError ∨ e = .modelFuel

theorem utf8DecF_err (f : Bool) : ∀ (n : Nat) (l : List Nat) (e : PyExc), utf8DecF f n l = .error e → DecErr e := by
  intro n
  induction n with
  | zero => intro l e h; simp [utf8DecF] at h; exact Or.inr h.symm
  | succ n ih =>
    intro l e h
    cases l with
    | nil => simp [utf8DecF] at h
    | cons x xs =>
      simp only [utf8DecF] at h
      split at h
      · simp at h; exact Or.inl h.symm
      · split at h
        · simp at h; exact Or.inl h.symm
        · simp at h
      · split at h
        · rename_i heq; simp at h; subst h; exact ih _ _ heq
        · simp at h

theorem dec_err (d : Dec) (x : List Nat) (f : Bool) (e : PyExc) (h : d.decode x f = .error e) : DecErr e := by
  unfold Dec.decode at h
  cases hu : utf8Dec f (d.ubuf ++ x) with
  | error e' =>
    rw [hu] at h; simp [bind, Except.bind] at h; subst h; exact utf8DecF_err f _ _ _ hu
  | ok r =>
    rw [hu] at h; simp [bind, Except.bind, pure, Except.pure] at h
    split at h <;> simp at h

theorem tellSkip_err (next : List Nat) : ∀ (fuel : Nat) (d : Dec) (sb : Int) (back flags cts : Nat) (e : PyExc),
    (TP.tellSkip next d sb back flags cts fuel).2 = .error e → DecErr e := by
  intro fuel
  induction fuel with
  | zero => intro d sb back flags cts e h; simp [TP.tellSkip] at h; exact Or.inr h.symm
  | succ fuel ih =>
    intro d sb back flags cts e h
    simp only [TP.tellSkip] at h
    split at h
    · split at h
      · rename_i heq; simp at h; subst h; exact dec_err _ _ _ _ heq
      · split at h
        · split at h
          · simp at h
          · exact ih _ _ _ _ _ _ h
        · exact ih _ _ _ _ _ _ h
    · simp at h

theorem tellFeed_err : ∀ (l : List Nat) (d : Dec) (sp sf bf cd cts : Nat) (e : PyExc),
    (TP.tellFeed l d sp sf bf cd cts).2 = .error e → DecErr e := by
  intro l
  induction l with
  | nil => intro d sp sf bf cd cts e h; simp [TP.tellFeed] at h
  | cons x xs ih =>
    intro d sp sf bf cd cts e h
    cases hd : d.decode [x] false with
    | error e' =>
      simp only [TP.tellFeed, hd] at h; simp at h; subst h; exact dec_err _ _ _ _ hd
    | ok r =>
      obtain ⟨d2, out⟩ := r
      simp only [TP.tellFeed, hd] at h
      try dsimp only at h
      repeat' split at h
      all_goals first | (simp at h; done) | exact ih _ _ _ _ _ _ _ h

theorem tellBody_err (t : TState) (d : Dec) (position decFlags : Nat) (next : List Nat) (cts : Nat) (e : PyExc)
    (h : (TP.tellBody t d position decFlags next cts).2 = .error e) : e ≠ disabledErr := by
  have hne : ∀ e, DecErr e → e ≠ disabledErr := by
    intro e he; rcases he with rfl | rfl <;> simp [disabledErr, osError, unicodeDecodeError]
  have ho : ∀ m, m ≠ "telling position disabled by next() call" → osError m ≠ disabledErr := by
    intro m hm h; simp [disabledErr, osError] at h; exact hm h
  unfold TP.tellBody at h
  try dsimp only at h
  split at h
  · simp at h; subst h; simp [disabledErr, osError]
  · cases hs : TP.tellSkip next d _ 1 decFlags cts _ with
    | mk d1 r1 =>
      rw [hs] at h
      cases r1 with
      | error e1 => simp at h; subst h; exact hne _ (tellSkip_err _ _ _ _ _ _ _ _ (by rw [hs]))
      | ok v1 =>
        obtain ⟨sb, fl, cs⟩ := v1
        try dsimp only at h
        split at h
        · simp at h
        · cases hf : TP.tellFeed _ d1 _ fl 0 0 cs with
          | mk d2 r2 =>
            rw [hf] at h
            cases r2 with
            | error e2 => simp at h; subst h; exact hne _ (tellFeed_err _ _ _ _ _ _ _ _ (by rw [hf]))
            | ok v2 =>
              obtain ⟨a, b, c, cd, ct, br⟩ := v2
              cases br
              · cases hdd : d2.decode [] true with
                | error e3 => simp [hdd] at h; subst h; exact hne _ (dec_err _ _ _ _ hdd)
                | ok r3 =>
                  obtain ⟨d3, o3⟩ := r3
                  simp only [hdd] at h
                  try dsimp only at h
                  split at h
                  · simp at h; subst h; exact ho _ (by decide)
                  · simp at h
              · simp at h

/-- With `telling` set on an open stream, `tell()` never raises the "disabled by next()"
error, whatever else it may raise. -/
theorem tell_not_disabled (t : TState) (ht : t.telling = true) (hc : t.b.closed = false) (e : PyExc)
    (h : (TP.tell t).2 = .error e) : e ≠ disabledErr := by
  unfold TP.tell at h
  simp only [ht, Bool.not_true, Bool.false_eq_true, ite_false, TP.flush, hc] at h
  split at h
  · split at h
    · simp at h; subst h; simp [disabledErr, osError]
    · split at h
      · simp at h
      · cases hb : TP.tellBody _ _ _ _ _ _ with
        | mk d r =>
          rw [hb] at h
          cases r with
          | error e' =>
            simp [Functor.map, Except.map] at h; subst h; exact tellBody_err _ _ _ _ _ _ _ (by rw [hb])
          | ok n => simp [Functor.map, Except.map] at h
  · split at h
    · simp at h; subst h; simp [disabledErr, osError]
    · simp at h

/-! ## What reading leaves alone -/

/-- `telling` and the `BytesIO`'s closed flag. -/
def Keeps (t t' : TState) : Prop := t'.telling = t.telling ∧ t'.b.closed = t.b.closed

theorem keeps_refl (t : TState) : Keeps t t := ⟨rfl, rfl⟩

theorem keeps_trans {a b c : TState} (h1 : Keeps a b) (h2 : Keeps b c) : Keeps a c :=
  ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

theorem readRaw_closed (s : BState) (n : Option Int) : (P.readRaw s n).1.closed = s.closed := by
  unfold P.readRaw
  split
  · rfl
  · dsimp only; split <;> rfl

theorem readChunk_keeps (t : TState) : Keeps t (TP.readChunk t).1 := by
  unfold TP.readChunk
  split
  · exact keeps_refl t
  · dsimp only
    have hc := readRaw_closed t.b (some 2048)
    cases hr : P.readRaw t.b (some 2048) with
    | mk b' r =>
      rw [hr] at hc
      simp only at hc
      cases r with
      | error e => exact ⟨rfl, hc⟩
      | ok chunk =>
        dsimp only
        split
        · exact ⟨rfl, hc⟩
        · split <;> simp [Keeps, TP.setDecoded, hc]

theorem chunkLoop_keeps : ∀ (fuel : Nat) (t : TState), Keeps t (TP.chunkLoop t fuel).1 := by
  intro fuel
  induction fuel with
  | zero => intro t; exact keeps_refl t
  | succ fuel ih =>
    intro t
    simp only [TP.chunkLoop]
    have hk := readChunk_keeps t
    cases hr : TP.readChunk t with
    | mk t' r =>
      rw [hr] at hk
      cases r with
      | error e => exact hk
      | ok more =>
        dsimp only
        split
        · exact keeps_trans hk (ih t')
        · exact hk

theorem finishLine_keeps (t : TState) (size : Int) (line : List Nat) (endpos : Nat) :
    Keeps t (TP.finishLine t size line endpos).1 := by
  simp only [TP.finishLine]; (repeat' split) <;> simp [Keeps]

theorem lineLoop_keeps (size : Int) : ∀ (fuel : Nat) (t : TState) (line : List Nat) (start : Nat),
    Keeps t (TP.lineLoop size t line start fuel).1 := by
  intro fuel
  induction fuel with
  | zero => intro t line start; exact keeps_refl t
  | succ fuel ih =>
    intro t line start
    simp only [TP.lineLoop]
    split
    · exact finishLine_keeps _ _ _ _
    · split
      · exact finishLine_keeps _ _ _ _
      · have hk := chunkLoop_keeps (t.b.buf.length - t.b.pos + 3) t
        cases hc : TP.chunkLoop t (t.b.buf.length - t.b.pos + 3) with
        | mk t' r =>
          rw [hc] at hk
          cases r with
          | error e => exact hk
          | ok u =>
            dsimp only
            split
            · exact keeps_trans hk (keeps_trans ⟨rfl, rfl⟩ (ih _ _ _))
            · exact keeps_trans hk ⟨rfl, rfl⟩

theorem readlineRaw_keeps (t : TState) (size : Option Int) : Keeps t (TP.readlineRaw t size).1 := by
  unfold TP.readlineRaw
  split
  · exact keeps_refl t
  · dsimp only
    have h1 : Keeps t (TP.getDecoder (TP.getDecodedChars t none).1).1 := by
      simp only [TP.getDecodedChars, TP.getDecoder]; split <;> simp [Keeps]
    exact keeps_trans h1 (lineLoop_keeps _ _ _ _ _)

/-- `__next__` (_pyio.py:2629-2636) and `flush` (:2255-2257) on every open `_pyio.StringIO`
state. `next()` is `readline()` with `tell()` disabled first: a line is returned and the
stream stays open, after which `tell()` raises
`OSError('telling position disabled by next() call')` (:2412-2413) until `flush()`, which
returns `None` and re-enables it, so that error can no longer come from `tell()`; an empty
line ends the iteration with `StopIteration`, the snapshot dropped and `tell()` enabled
again. On a closed stream `flush()` raises `ValueError('I/O operation on closed file.')`
and changes nothing. -/
def StringIONextFlush : Prop := ∀ (t : TState),
  (t.b.closed = true → TP.xstep t .flush = (t, .error (.valueError "I/O operation on closed file."))) ∧
  (t.b.closed = false →
    let r := TP.readlineRaw { t with telling := false } none
    (∀ e, r.2 = .error e → TP.next t = (r.1, .error e)) ∧
    (r.2 = .ok [] → TP.next t = ({ r.1 with snapshot := none, telling := true }, .error .stopIteration)) ∧
    (∀ l, l ≠ [] → r.2 = .ok l →
      TP.next t = (r.1, .ok (.str l)) ∧
      (TP.tell r.1).2 = .error disabledErr ∧
      TP.xstep r.1 .flush = ({ r.1 with telling := true }, .ok .none) ∧
      ∀ e, (TP.tell { r.1 with telling := true }).2 = .error e → e ≠ disabledErr))

theorem stringIONextFlush_proven : StringIONextFlush := by
  intro t
  refine ⟨?_, ?_⟩
  · intro hc; simp [TP.xstep, TP.flush, hc, TP.closedDot]
  · intro hc
    have hk := readlineRaw_keeps { t with telling := false } none
    obtain ⟨hk1, hk2⟩ := hk
    simp only at hk1 hk2
    have hc' : (TP.readlineRaw { t with telling := false } none).1.b.closed = false := by rw [hk2]; exact hc
    refine ⟨?_, ?_, ?_⟩
    · intro e he
      unfold TP.next
      cases hr : TP.readlineRaw { t with telling := false } none with
      | mk t' r => rw [hr] at he; simp only at he; subst he; rfl
    · intro he
      unfold TP.next
      cases hr : TP.readlineRaw { t with telling := false } none with
      | mk t' r => rw [hr] at he; simp only at he; subst he; simp
    · intro l hl he
      refine ⟨?_, ?_, ?_, ?_⟩
      · unfold TP.next
        cases hr : TP.readlineRaw { t with telling := false } none with
        | mk t' r => rw [hr] at he; simp only at he; subst he; simp [hl]
      · simp [TP.tell, hk1, disabledErr]
      · simp [TP.xstep, TP.flush, hc']
      · intro e he'
        exact tell_not_disabled { (TP.readlineRaw { t with telling := false } none).1 with telling := true }
          rfl hc' e he'

end PyLean.PyIO
