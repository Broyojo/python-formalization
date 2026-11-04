import PyLean.PyIO.Newline

/-!
Properties of `IncrementalNewlineDecoder` (`Lib/_pyio.py:1972-2054`,
`Modules/_io/textio.c:248-663`) over the models of `PyIO/Newline.lean`: its purpose
("translating \r\n and \r into \n ... ensures that the newline sequence is returned in
one piece", _pyio.py:1973-1977) for every split of the input into chunks, and the state
that `getstate`, `setstate` and `reset` carry.
-/

namespace PyLean.PyIO

open PyLean

/-! ## Newline kinds and translation over a concatenation -/

def nlNone : NlKinds := ⟨false, false, false⟩

theorem none_union (a : NlKinds) : nlNone.union a = a := by
  cases a; simp [NlKinds.union, nlNone]

theorem union_none (a : NlKinds) : a.union nlNone = a := by
  cases a; simp [NlKinds.union, nlNone]

theorem union_assoc (a b c : NlKinds) : (a.union b).union c = a.union (b.union c) := by
  cases a; cases b; cases c; simp [NlKinds.union, Bool.or_assoc]

theorem union_right_comm (a b c : NlKinds) : (a.union b).union c = (a.union c).union b := by
  cases a; cases b; cases c; simp [NlKinds.union, Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]

/-- `a ++ b` does not cut a `\r\n` in two. -/
def Splits (a b : List Nat) : Prop := ¬ (a.getLast? = some 13 ∧ b.head? = some 10)

theorem splits_tail {x : Nat} {t b : List Nat} (h : Splits (x :: t) b) (ht : t ≠ []) : Splits t b := by
  intro ⟨h1, h2⟩; apply h; refine ⟨?_, h2⟩
  rw [List.getLast?_cons, h1]; rfl

theorem nl_other (x : Nat) (r : List Nat) (h13 : x ≠ 13) (h10 : x ≠ 10) : nlKinds (x :: r) = nlKinds r := by
  rw [nlKinds.eq_5] <;> simp_all

theorem nl_cr (r : List Nat) (h : r.head? ≠ some 10) :
    nlKinds (13 :: r) = (nlKinds r).union ⟨true, false, false⟩ := by
  rw [nlKinds.eq_3]; intro r' e; subst e; simp at h

theorem tl_other (x : Nat) (r : List Nat) (h13 : x ≠ 13) : translateNl (x :: r) = x :: translateNl r := by
  rw [translateNl.eq_4] <;> simp_all

theorem tl_cr (r : List Nat) (h : r.head? ≠ some 10) : translateNl (13 :: r) = 10 :: translateNl r := by
  rw [translateNl.eq_3]; intro r' e; subst e; simp at h

theorem nlKinds_append : ∀ (n : Nat) (a b : List Nat), a.length ≤ n → Splits a b →
    nlKinds (a ++ b) = (nlKinds a).union (nlKinds b) := by
  intro n
  induction n with
  | zero =>
    intro a b ha _
    have : a = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; simp only [List.nil_append, nlKinds.eq_1]; exact (none_union _).symm
  | succ n ih =>
    intro a b ha hs
    match a with
    | [] => simp only [List.nil_append, nlKinds.eq_1]; exact (none_union _).symm
    | x :: t =>
      by_cases h13 : x = 13
      · subst h13
        cases t with
        | nil =>
          have hb : b.head? ≠ some 10 := by intro h; exact hs ⟨rfl, h⟩
          rw [List.singleton_append, nl_cr b hb, nl_cr [] (by simp), nlKinds.eq_1, ← none_union (nlKinds b)]
          exact union_right_comm _ _ _
        | cons y r =>
          by_cases h10 : y = 10
          · subst h10
            have ihr : nlKinds (r ++ b) = (nlKinds r).union (nlKinds b) := by
              cases r with
              | nil => simp only [List.nil_append, nlKinds.eq_1]; exact (none_union _).symm
              | cons z r' =>
                exact ih _ b (by simp at ha ⊢; omega)
                  (splits_tail (splits_tail hs (by simp)) (by simp))
            simp only [List.cons_append, nlKinds.eq_2, ihr]
            exact union_right_comm _ _ _
          · have ihr := ih (y :: r) b (by simp at ha ⊢; omega) (splits_tail hs (by simp))
            simp only [List.cons_append] at ihr ⊢
            rw [nl_cr _ (by simp [h10]), nl_cr _ (by simp [h10]), ihr]
            exact union_right_comm _ _ _
      · by_cases h10 : x = 10
        · subst h10
          have iht : nlKinds (t ++ b) = (nlKinds t).union (nlKinds b) := by
            cases t with
            | nil => simp only [List.nil_append, nlKinds.eq_1]; exact (none_union _).symm
            | cons z r => exact ih _ b (by simp at ha ⊢; omega) (splits_tail hs (by simp))
          simp only [List.cons_append, nlKinds.eq_4, iht]
          exact union_right_comm _ _ _
        · have iht : nlKinds (t ++ b) = (nlKinds t).union (nlKinds b) := by
            cases t with
            | nil => simp only [List.nil_append, nlKinds.eq_1]; exact (none_union _).symm
            | cons z r => exact ih _ b (by simp at ha ⊢; omega) (splits_tail hs (by simp))
          rw [List.cons_append, nl_other x _ h13 h10, nl_other x _ h13 h10, iht]

theorem translateNl_append : ∀ (n : Nat) (a b : List Nat), a.length ≤ n → Splits a b →
    translateNl (a ++ b) = translateNl a ++ translateNl b := by
  intro n
  induction n with
  | zero =>
    intro a b ha _
    have : a = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; simp [translateNl]
  | succ n ih =>
    intro a b ha hs
    match a with
    | [] => simp [translateNl]
    | x :: t =>
      by_cases h13 : x = 13
      · subst h13
        cases t with
        | nil =>
          have hb : b.head? ≠ some 10 := by intro h; exact hs ⟨rfl, h⟩
          rw [List.singleton_append, tl_cr b hb, tl_cr [] (by simp)]; simp [translateNl]
        | cons y r =>
          by_cases h10 : y = 10
          · subst h10
            have ihr : translateNl (r ++ b) = translateNl r ++ translateNl b := by
              cases r with
              | nil => simp [translateNl]
              | cons z r' =>
                exact ih _ b (by simp at ha ⊢; omega)
                  (splits_tail (splits_tail hs (by simp)) (by simp))
            simp only [List.cons_append, translateNl.eq_2, ihr]
          · have ihr := ih (y :: r) b (by simp at ha ⊢; omega) (splits_tail hs (by simp))
            simp only [List.cons_append] at ihr ⊢
            rw [tl_cr _ (by simp [h10]), tl_cr _ (by simp [h10]), ihr]; rfl
      · have iht : translateNl (t ++ b) = translateNl t ++ translateNl b := by
          cases t with
          | nil => simp [translateNl]
          | cons z r => exact ih _ b (by simp at ha ⊢; omega) (splits_tail hs (by simp))
        rw [List.cons_append, tl_other x _ h13, tl_other x _ h13, iht]; rfl

/-! ## `decode`: the chunks do not matter -/

/-- The text the decoder holds back: `\r` while `pendingcr`. -/
def pre (d : NDec) : List Nat := if d.pendingcr then [13] else []

theorem dropLast_concat {l : List Nat} {a : Nat} (h : l.getLast? = some a) : l.dropLast ++ [a] = l := by
  rw [List.getLast?_eq_some_iff] at h
  obtain ⟨ys, rfl⟩ := h
  simp

/-- `translate`: `\r\n` and `\r` become `\n` (_pyio.py:2009-2013). -/
def tr (t : Bool) (x : List Nat) : List Nat := if t then translateNl x else x

theorem tr_append (t : Bool) (a b : List Nat) (h : Splits a b) : tr t (a ++ b) = tr t a ++ tr t b := by
  cases t
  · rfl
  · exact translateNl_append a.length a b (Nat.le_refl _) h

/-- One `decode(c, final=False)` of a text decoder (`decoder is None`), _pyio.py:1986-2015:
the pending `\r` and `c` are split into a part that is recorded and translated and the
new pending `\r`, and that split never cuts a `\r\n` (the part ends with `\r` only when
another `\r` is held back). -/
theorem decode_step (d : NDec) (c : List Nat) (hi : d.inner = none) :
    ∃ core p, NP.decode d c false =
        .ok ({ d with pendingcr := p, seennl := d.seennl.union (nlKinds core) }, tr d.translate core) ∧
      core ++ (if p then [13] else []) = pre d ++ c ∧ (p = false → core.getLast? ≠ some 13) := by
  have hin : d.inputStep c false = .ok (d, c) := by simp [NDec.inputStep, hi]
  -- `if self.pendingcr and (output or final)`: `out` is the text after that step
  have h1 : ∃ q out, (if d.pendingcr && (false || !c.isEmpty) then ({ d with pendingcr := false }, 13 :: c) else (d, c))
      = ({ d with pendingcr := q }, out) ∧ out ++ (if q then [13] else []) = pre d ++ c ∧
        (q = true → out = []) := by
    cases hp : d.pendingcr
    · cases c with
      | nil => exact ⟨false, [], by simp [hp, pre]; cases d; simp_all⟩
      | cons x r => exact ⟨false, x :: r, by simp [hp, pre]; cases d; simp_all⟩
    · cases c with
      | nil => exact ⟨true, [], by simp [hp, pre]; cases d; simp_all⟩
      | cons x r => exact ⟨false, 13 :: x :: r, by simp [hp, pre]⟩
  obtain ⟨q, out, h1e, h1s, h1q⟩ := h1
  have hdec : NP.decode d c false =
      let (d', o) := NDec.pendStep d c false
      .ok ({ d' with seennl := d'.seennl.union (nlKinds o) }, if d'.translate then translateNl o else o) := by
    simp [NP.decode, hin]
  rw [hdec]
  simp only [NDec.pendStep, h1e]
  by_cases hend : out.getLast? = some 13
  · -- `if output.endswith("\r") and not final`: keep it back
    have hq : q = false := by
      cases q
      · rfl
      · simp [h1q rfl] at hend
    subst hq
    refine ⟨out.dropLast, true, ?_, ?_, by simp⟩
    · simp [hend, tr]
    · simp only [Bool.false_eq_true, ite_false, List.append_nil] at h1s
      rw [← h1s]; simp only [ite_true]; exact dropLast_concat hend
  · refine ⟨out, q, ?_, h1s, fun _ => hend⟩
    have : (out.getLast? == some 13) = false := by simpa using hend
    simp [this, tr]

/-- Decode the chunks with `final=False`, then `decode(b'', final=True)`; the outputs. -/
def NP.decodeAll (d : NDec) : List (List Nat) → Py (NDec × List (List Nat))
  | [] =>
    match NP.decode d [] true with
    | .error e => .error e
    | .ok (d, o) => .ok (d, [o])
  | c :: cs =>
    match NP.decode d c false with
    | .error e => .error e
    | .ok (d, o) =>
      match NP.decodeAll d cs with
      | .error e => .error e
      | .ok (d, os) => .ok (d, o :: os)

theorem decodeAll_spec : ∀ (cs : List (List Nat)) (d : NDec), d.inner = none →
    ∃ d' os, NP.decodeAll d cs = .ok (d', os) ∧
      os.flatten = tr d.translate (pre d ++ cs.flatten) ∧
      d'.seennl = d.seennl.union (nlKinds (pre d ++ cs.flatten)) ∧
      d'.pendingcr = false ∧ d'.translate = d.translate ∧ d'.inner = none := by
  intro cs
  induction cs with
  | nil =>
    intro d hi
    have hin : d.inputStep [] true = .ok (d, []) := by simp [NDec.inputStep, hi]
    cases hp : d.pendingcr
    · refine ⟨{ d with seennl := d.seennl.union (nlKinds []) }, [tr d.translate []], ?_, ?_, ?_, ?_, rfl, hi⟩
      · simp [NP.decodeAll, NP.decode, hin, NDec.pendStep, hp, tr]
      · simp [pre, hp]
      · simp [pre, hp]
      · simp [hp]
    · refine ⟨{ d with pendingcr := false, seennl := d.seennl.union (nlKinds [13]) }, [tr d.translate [13]],
        ?_, ?_, ?_, rfl, rfl, hi⟩
      · simp [NP.decodeAll, NP.decode, hin, NDec.pendStep, hp, tr]
      · simp [pre, hp]
      · simp [pre, hp]
  | cons c cs ih =>
    intro d hi
    obtain ⟨core, p, hd, hsplit, hnt⟩ := decode_step d c hi
    let d1 : NDec := { d with pendingcr := p, seennl := d.seennl.union (nlKinds core) }
    obtain ⟨d', os, hrun, hjoin, hseen, hpend, htr, hin'⟩ := ih d1 hi
    -- the cut after `core` is never inside a `\r\n`
    have hs : Splits core (pre d1 ++ cs.flatten) := by
      intro ⟨h1, h2⟩
      cases p
      · exact hnt rfl h1
      · simp [d1, pre] at h2
    have hcat : pre d ++ (c :: cs).flatten = core ++ (pre d1 ++ cs.flatten) := by
      simp only [List.flatten_cons, ← List.append_assoc, ← hsplit]; simp [d1, pre]
    refine ⟨d', tr d.translate core :: os, ?_, ?_, ?_, hpend, ?_, hin'⟩
    · simp [NP.decodeAll, hd, hrun, d1]
    · rw [List.flatten_cons, hjoin, hcat, tr_append _ _ _ hs]
    · rw [hseen, hcat, nlKinds_append _ core _ (Nat.le_refl _) hs, union_assoc]
    · rw [htr]

/-- `IncrementalNewlineDecoder(None, translate)` over text: for every split of a text
into chunks fed with `final=False` and a last `decode('', final=True)`, the outputs
concatenate to the text with `\r\n` and `\r` translated to `\n` when `translate` is set
and to the text itself otherwise, and `newlines` records exactly the kinds of the whole
text: a `\r\n` cut between two chunks is still one `\r\n`, never a `\r` and a `\n`. The
decoder ends with nothing pending. -/
def NDecodeChunks : Prop := ∀ (translate : Bool) (cs : List (List Nat)),
  ∃ d os, NP.decodeAll (NDec.fresh none translate) cs = .ok (d, os) ∧
    os.flatten = tr translate cs.flatten ∧ d.seennl = nlKinds cs.flatten ∧ d.pendingcr = false

theorem nDecodeChunks_proven : NDecodeChunks := by
  intro t cs
  obtain ⟨d, os, h, hj, hs, hp, _, _⟩ := decodeAll_spec cs (NDec.fresh none t) rfl
  refine ⟨d, os, h, ?_, ?_, hp⟩
  · simpa [pre, NDec.fresh] using hj
  · rw [hs]
    have := none_union (nlKinds cs.flatten)
    simpa [pre, NDec.fresh, nlNone] using this

/-! ## `getstate`, `setstate`, `reset` -/

theorem pendStep_seennl (d : NDec) (k : NlKinds) (out : List Nat) (f : Bool) :
    NDec.pendStep { d with seennl := k } out f =
      ({ (NDec.pendStep d out f).1 with seennl := k }, (NDec.pendStep d out f).2) ∧
    (NDec.pendStep d out f).1.translate = d.translate := by
  obtain ⟨inner, t, p, s⟩ := d
  unfold NDec.pendStep
  cases p <;> cases f <;> simp <;> (repeat' split) <;> simp_all

theorem decode_seennl (d : NDec) (k : NlKinds) (x : List Nat) (f : Bool) :
    (NP.decode { d with seennl := k } x f).map (·.2) = (NP.decode d x f).map (·.2) := by
  have hin : ∀ (e : NDec), (({ e with seennl := k } : NDec).inputStep x f) =
      (e.inputStep x f).map (fun r => ({ r.1 with seennl := k }, r.2)) := by
    intro e
    obtain ⟨inner, t, p, s⟩ := e
    cases inner with
    | none => rfl
    | some b =>
      simp only [NDec.inputStep]
      cases utf8Dec f (b ++ x) <;> rfl
  have hint : ∀ (e : NDec) r, e.inputStep x f = .ok r → r.1.translate = e.translate := by
    intro e r h
    obtain ⟨inner, t, p, s⟩ := e
    cases inner with
    | none => simp [NDec.inputStep] at h; subst h; rfl
    | some b =>
      simp only [NDec.inputStep] at h
      cases hu : utf8Dec f (b ++ x) <;> simp [hu] at h; subst h; rfl
  simp only [NP.decode, hin]
  cases h : d.inputStep x f with
  | error e => rfl
  | ok r =>
    have ht := hint d r h
    obtain ⟨e1, e2⟩ := pendStep_seennl r.1 k r.2 f
    simp only [Except.map, e1]

/-- `setstate(getstate())` carries what decoding depends on (_pyio.py:2017-2032): restored
into any decoder of the same kind and `translate`, every later `decode` returns what the
original would. The state is the wrapped decoder's buffer and `pendingcr` as the low bit
of the flag; `seennl` is not part of it. `reset()` (:2034-2038) makes the decoder a fresh
one: nothing pending, an empty buffer, and `newlines` is `None`. -/
def NDecState : Prop := ∀ (d d2 : NDec),
  (d2.translate = d.translate → d2.inner.isSome = d.inner.isSome →
    ∀ x f, (NP.decode (d2.setstate d.getstate.1 d.getstate.2) x f).map (·.2) = (NP.decode d x f).map (·.2)) ∧
  d.reset = NDec.fresh (d.inner.map (fun _ => [])) d.translate ∧
  newlinesVal d.reset.seennl = .none

theorem nDecState_proven : NDecState := by
  intro d d2
  refine ⟨?_, ?_, ?_⟩
  · intro ht hk x f
    have e : d2.setstate d.getstate.1 d.getstate.2 = { d with seennl := d2.seennl } := by
      obtain ⟨i, t, p, s⟩ := d
      obtain ⟨i2, t2, p2, s2⟩ := d2
      simp only at ht hk; subst ht
      cases i <;> cases i2 <;> cases p <;> simp_all [NDec.setstate, NDec.getstate]
    rw [e]
    exact decode_seennl _ _ _ _
  · simp [NDec.reset, NDec.fresh]
  · simp [NDec.reset, newlinesVal]

end PyLean.PyIO
