import PyLean.PyIO.StringTwins
import PyLean.PyIO.Utf8Props
import PyLean.PyIO.BytesDocs

/-!
Proven `StringIO` properties: the narrowed versions of the refuted twin
statements in `StringTwins`.
-/

namespace PyLean.PyIO

open PyLean

theorem takeWhile_nonzero (l : List Nat) (h : ∀ b ∈ l, b ≠ 0) : l.takeWhile (fun b => b ≠ 0) = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hx : x ≠ 0 := h x (List.mem_cons_self ..)
    have ih' := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    rw [List.takeWhile_cons]
    simp only [hx, ne_eq, not_false_eq_true, decide_true, ite_true]
    rw [ih']

/-- Without NUL characters in `newline`, the C constructor accepts exactly
the legal values. (`newline` is a `str`: its code points are below
0x110000.) -/
def CStringIONewlineLegalNoNul : Prop :=
  ∀ nl : Option (List Nat), (∀ l, nl = some l → ∀ c ∈ l, c ≠ 0 ∧ c < 0x110000) →
    ((SC.init none nl).toBool = true ↔ LegalNewline nl)

theorem cStringIONewlineLegalNoNul_proven : CStringIONewlineLegalNoNul := by
  intro nl hnl
  cases nl with
  | none => simp [SC.init, LegalNewline, Except.toBool, pure, Except.pure, bind, Except.bind]
  | some l =>
    have hl := hnl l rfl
    have hv : ValidStr l := fun c hc => (hl c hc).2
    have hnz := utf8Enc_nonzero l (fun c hc => (hl c hc).1)
    have htw := takeWhile_nonzero (utf8Enc l) hnz
    have e0 := utf8Enc_small l hv [] rfl
    have e1 := utf8Enc_small l hv [10] rfl
    have e2 := utf8Enc_small l hv [13] rfl
    have e3 := utf8Enc_small l hv [13, 10] rfl
    unfold SC.init
    by_cases hs : l.any isSurrogate = true
    · have : ¬ LegalNewline (some l) := by
        intro hleg
        rcases hleg with h | h | h | h | h <;> simp at h <;> subst h <;> simp [isSurrogate] at hs
      simp [hs, this, Except.toBool, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
    · simp only [hs, Bool.false_eq_true, ite_false, htw]
      by_cases hleg : l = [] ∨ l = [10] ∨ l = [13] ∨ l = [13, 10]
      · have hc : utf8Enc l = [] ∨ utf8Enc l = [10] ∨ utf8Enc l = [13] ∨ utf8Enc l = [13, 10] := by
          rw [e0, e1, e2, e3]; exact hleg
        have hL : LegalNewline (some l) := by
          rcases hleg with h | h | h | h <;> simp [LegalNewline, h]
        simp [hc, hL, Except.toBool, bind, Except.bind, pure, Except.pure]
      · have hc : ¬ (utf8Enc l = [] ∨ utf8Enc l = [10] ∨ utf8Enc l = [13] ∨ utf8Enc l = [13, 10]) := by
          rw [e0, e1, e2, e3]; exact hleg
        have hL : ¬ LegalNewline (some l) := by
          unfold LegalNewline; simp only [reduceCtorEq, false_or, Option.some.injEq]; exact hleg
        rw [not_or, not_or, not_or] at hc
        simp [hc, hL, Except.toBool, bind, Except.bind, pure, Except.pure, throw, throwThe,
          MonadExceptOf.throw]

/-! ## Write-only sequences -/

theorem utf8Enc_append (a b : List Nat) : utf8Enc (a ++ b) = utf8Enc a ++ utf8Enc b := by
  simp [utf8Enc, List.flatMap_append]

theorem utf8Enc1_length_le (c : Nat) : (utf8Enc1 c).length ≤ 4 := by
  unfold utf8Enc1; split <;> (try split) <;> (try split) <;> simp

theorem utf8Enc_length_le (s : List Nat) : (utf8Enc s).length ≤ 4 * s.length := by
  induction s with
  | nil => simp [utf8Enc_nil]
  | cons c r ih => rw [utf8Enc_cons, List.length_append]; have := utf8Enc1_length_le c; simp; omega

theorem utf8Enc_eq_nil (s : List Nat) : utf8Enc s = [] ↔ s = [] := by
  cases s with
  | nil => simp [utf8Enc_nil]
  | cons c r =>
    rw [utf8Enc_cons]; simp only [List.append_eq_nil_iff, reduceCtorEq, iff_false, not_and]
    intro h; exact absurd h (utf8Enc1_ne_nil c)

theorem replaceLf_length_le (n w : List Nat) (hn : n.length ≤ 2) : (replaceLf n w).length ≤ 2 * w.length := by
  induction w with
  | nil => simp [replaceLf]
  | cons c r ih => simp only [replaceLf]; split <;> simp <;> omega

theorem replaceLf_no_lf (n w : List Nat) (h : w.contains 10 = false) : replaceLf n w = w := by
  induction w with
  | nil => rfl
  | cons c r ih =>
    simp only [List.contains_cons, Bool.or_eq_false_iff] at h
    have hc : c ≠ 10 := by
      intro e; subst e; simp at h
    simp [replaceLf, hc, ih h.2]

theorem replaceLf_eq_nil (n w : List Nat) (hn : n ≠ []) : replaceLf n w = [] ↔ w = [] := by
  cases w with
  | nil => simp [replaceLf]
  | cons c r => simp only [replaceLf]; split <;> simp [hn]

theorem replaceLf_valid (n w : List Nat) (hn : ValidStr n) (hw : ValidStr w) : ValidStr (replaceLf n w) := by
  induction w with
  | nil => intro c hc; simp [replaceLf] at hc
  | cons c r ih =>
    have hr : ValidStr r := fun x hx => hw x (List.mem_cons_of_mem _ hx)
    have hc : c < 0x110000 := hw c (List.mem_cons_self ..)
    intro x hx
    simp only [replaceLf] at hx
    split at hx
    · rcases List.mem_append.mp hx with h | h
      · exact hn x h
      · exact ih hr x h
    · rcases List.mem_cons.mp hx with h | h
      · omega
      · exact ih hr x h

/-- C-side invariant after writes: contents `B`, position at the end. -/
def CInv (B : List Nat) (s : SCState) (tr : List Nat → List Nat) : Prop :=
  s.buf = B ∧ s.pos = B.length ∧ s.closed = false ∧ s.translate = false ∧
  ∀ w, (match s.writenl with
    | some n => replaceLf n w
    | none => w) = tr w

theorem C_writeStr_end (s : SCState) (w D : List Nat)
    (hc : s.closed = false) (hp : s.pos = s.buf.length) (ht : s.translate = false)
    (hD : (match s.writenl with
      | some n => replaceLf n w
      | none => w) = D)
    (hb : 4 * (s.buf.length + D.length) + 8 < memLimit) (hDn : D ≠ []) :
    (SC.writeStr s w).2 = .ok () ∧ (SC.writeStr s w).1.buf = s.buf ++ D ∧
    (SC.writeStr s w).1.pos = (s.buf ++ D).length ∧ (SC.writeStr s w).1.closed = false ∧
    (SC.writeStr s w).1.translate = false ∧ (SC.writeStr s w).1.writenl = s.writenl := by
  obtain ⟨buf, pos, closed, readnl, ru, rt, writenl, hd, translate, seennl⟩ := s
  simp only at hc hp ht hD hb
  subst hc hp ht
  have hmax : memLimit ≤ ssizeMax := by decide
  have hDl : 0 < D.length := List.length_pos_iff.mpr hDn
  have c1 : ¬ ((buf.length : Int) > ssizeMax - (D.length : Int)) := by omega
  have c2 : buf.length + D.length > buf.length := by omega
  have c3 : SC.resizeCheck (buf.length + D.length) = .ok () := by
    unfold SC.resizeCheck
    have d1 : ¬ (((buf.length + D.length + 1 : Nat) : Int) > ssizeMax) := by omega
    have d2 : ¬ (buf.length + D.length + 1 + 1 > (2 ^ 64 - 1) / 4) := by
      have : memLimit ≤ (2 ^ 64 - 1) / 4 := by decide
      omega
    have d3 : ¬ (4 * (buf.length + D.length + 1 + 1) ≥ memLimit) := by omega
    simp only [d1, d2, d3, ite_false]
  unfold SC.writeStr
  cases writenl with
  | none =>
    simp only at hD; subst hD
    cases hd <;> simp only [Bool.false_eq_true, ite_false, ite_true, c1, c2, c3, writeAt_end] <;>
      simp
  | some nl =>
    simp only at hD; subst hD
    cases hd <;> simp only [Bool.false_eq_true, ite_false, ite_true, c1, c2, c3, writeAt_end] <;>
      simp

theorem C_write_end (B : List Nat) (s : SCState) (tr : List Nat → List Nat) (w : List Nat)
    (hI : CInv B s tr) (hb : 4 * (B.length + (tr w).length) + 8 < memLimit) (hnil : tr w = [] ↔ w = []) :
    (SC.step s (.write w)).2 = .ok (.int w.length) ∧ CInv (B ++ tr w) (SC.step s (.write w)).1 tr := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hI
  by_cases hw : w = []
  · subst hw
    have : tr [] = [] := hnil.mpr rfl
    simp [SC.step, h3, this, CInv, h1, h2, h4, h5]
  · have hlen : 0 < w.length := List.length_pos_iff.mpr hw
    have htr : tr w ≠ [] := fun e => hw (hnil.mp e)
    have hws := C_writeStr_end s w (tr w) h3 (by rw [h2, h1]) h4 (h5 w) (by rw [h1]; exact hb) htr
    obtain ⟨r1, r2, r3, r4, r5, r6⟩ := hws
    simp only [SC.step, h3, Bool.false_eq_true, ite_false, hlen, ite_true]
    cases hW : SC.writeStr s w with
    | mk s' r =>
      rw [hW] at r1 r2 r3 r4 r5 r6
      simp only at r1 r2 r3 r4 r5 r6
      subst r1
      refine ⟨rfl, ?_, ?_, r4, r5, ?_⟩
      · rw [r2, h1]
      · rw [r3, h1]
      · rw [r6]; exact h5

theorem P_write_end (s : BState) (b : List Nat) (hc : s.closed = false) (hp : s.pos = s.buf.length)
    (he : s.exports = 0) (hb : s.buf.length + b.length < memLimit) :
    P.write s b = (if b = [] then s else { s with buf := s.buf ++ b, pos := s.pos + b.length },
      .ok (.int b.length)) := by
  obtain ⟨buf, pos, closed, ex, sh⟩ := s
  simp only at hc hp he hb
  subst hc hp he
  unfold P.write
  by_cases hbn : b = []
  · subst hbn; simp
  · have hl : b.length ≠ 0 := fun e => hbn (List.eq_nil_of_length_eq_zero e)
    have c : ¬ (buf.length + b.length ≥ memLimit) := by omega
    simp [hbn, hl, c, writeAt_end]

/-- The `_pyio` translation of a written string (_pyio.py:2288-2290). -/
def pyTrans (t : TState) (w : List Nat) : List Nat :=
  if (t.writetranslate && w.contains 10) && t.writetranslate && decide (t.writenl ≠ [10])
  then replaceLf t.writenl w else w

/-- Python-side invariant after writes: the `BytesIO` holds the UTF-8
encoding of `B` with its position at the end, and nothing was read. -/
def PInv (B : List Nat) (t : TState) (tr : List Nat → List Nat) : Prop :=
  t.b.buf = utf8Enc B ∧ t.b.pos = (utf8Enc B).length ∧ t.b.closed = false ∧ t.b.exports = 0 ∧
  t.decoder = none ∧ t.snapshot = none ∧ t.readtranslate = false ∧ ∀ w, pyTrans t w = tr w

theorem P_write_step (B : List Nat) (t : TState) (tr : List Nat → List Nat) (w : List Nat)
    (hI : PInv B t tr) (hb : (utf8Enc B).length + 4 * (tr w).length < memLimit) (hnil : tr w = [] ↔ w = []) :
    (TP.step t (.write w)).2 = .ok (.int w.length) ∧ PInv (B ++ tr w) (TP.step t (.write w)).1 tr := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hI
  have hbytes : t.b.buf.length + (utf8Enc (tr w)).length < memLimit := by
    have := utf8Enc_length_le (tr w); rw [h1]; omega
  have hpw := P_write_end t.b (utf8Enc (tr w)) h3 (by rw [h2, h1]) h4 hbytes
  have ht : (if (t.writetranslate && w.contains 10) && t.writetranslate && decide (t.writenl ≠ [10])
      then replaceLf t.writenl w else w) = tr w := h8 w
  simp only [TP.step, TP.write, h3, Bool.false_eq_true, ite_false]
  rw [ht, hpw]
  simp only [h6, Option.isSome_none, Bool.false_eq_true, ite_false, h5, Option.map_none]
  constructor
  · first | rfl | trivial
  by_cases hw : tr w = []
  · simp only [hw, utf8Enc_nil, ite_true, List.append_nil]
    exact ⟨h1, h2, h3, h4, rfl, rfl, h7, h8⟩
  · have : utf8Enc (tr w) ≠ [] := fun e => hw ((utf8Enc_eq_nil _).mp e)
    simp only [this, ite_false]
    refine ⟨?_, ?_, h3, h4, rfl, rfl, h7, h8⟩
    · simp [h1, utf8Enc_append]
    · simp [h1, h2, utf8Enc_append]

theorem P_getvalue (B : List Nat) (t : TState) (tr : List Nat → List Nat) (hI : PInv B t tr)
    (hv : ValidStr B) : (TP.step t .getvalue).2 = .ok (.str B) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hI
  simp only [TP.step, TP.getvalue, TP.flush, h3, Bool.false_eq_true, ite_false, TP.getDecoder, h5]
  simp only [Dec.reset, Dec.decode, h1]
  cases hu : t.readuniversal <;>
    simp [utf8Dec_enc true B hv, h7, bind, Except.bind, pure, Except.pure]

theorem runOps'_eq (step : SCState → SOp → SCState × Py Val) (s : SCState) (ops : List SOp) :
    runSC.runOps' step s ops = (runOps step s ops).2 := by
  induction ops generalizing s with
  | nil => rfl
  | cons o os ih => simp [runSC.runOps', runOps, ih]

theorem C_run (tr : List Nat → List Nat) : ∀ (ws : List (List Nat)) (B : List Nat) (s : SCState),
    CInv B s tr → (∀ w ∈ ws, tr w = [] ↔ w = []) →
    4 * (B.length + (ws.map (fun w => (tr w).length)).sum) + 8 < memLimit →
    (runOps SC.step s (ws.map SOp.write ++ [.getvalue])).2 =
      ws.map (fun w => .ok (.int w.length)) ++ [.ok (.str (B ++ (ws.map tr).flatten))] := by
  intro ws
  induction ws with
  | nil =>
    intro B s hI _ _
    obtain ⟨h1, -, h3, -⟩ := hI
    simp [runOps, SC.step, h1, h3]
  | cons w ws ih =>
    intro B s hI hn hb
    simp only [List.map_cons, List.sum_cons] at hb
    obtain ⟨r1, r2⟩ := C_write_end B s tr w hI (by omega) (hn w (List.mem_cons_self ..))
    simp only [List.map_cons, List.cons_append, runOps]
    rw [r1, ih (B ++ tr w) _ r2 (fun w' h => hn w' (List.mem_cons_of_mem _ h))
      (by simp only [List.length_append]; omega)]
    simp

theorem P_run (tr : List Nat → List Nat) : ∀ (ws : List (List Nat)) (B : List Nat) (t : TState),
    PInv B t tr → (∀ w ∈ ws, tr w = [] ↔ w = []) → ValidStr B → (∀ w ∈ ws, ValidStr (tr w)) →
    (utf8Enc B).length + 4 * (ws.map (fun w => (tr w).length)).sum < memLimit →
    (runOps TP.step t (ws.map SOp.write ++ [.getvalue])).2 =
      ws.map (fun w => .ok (.int w.length)) ++ [.ok (.str (B ++ (ws.map tr).flatten))] := by
  intro ws
  induction ws with
  | nil =>
    intro B t hI _ hv _ _
    simp [runOps, P_getvalue B t tr hI hv]
  | cons w ws ih =>
    intro B t hI hn hv hvw hb
    simp only [List.map_cons, List.sum_cons] at hb
    obtain ⟨r1, r2⟩ := P_write_step B t tr w hI (by omega) (hn w (List.mem_cons_self ..))
    have hvB : ValidStr (B ++ tr w) := by
      intro c hc
      rcases List.mem_append.mp hc with h | h
      · exact hv c h
      · exact hvw w (List.mem_cons_self ..) c h
    simp only [List.map_cons, List.cons_append, runOps]
    rw [r1, ih (B ++ tr w) _ r2 (fun w' h => hn w' (List.mem_cons_of_mem _ h)) hvB
      (fun w' h => hvw w' (List.mem_cons_of_mem _ h))
      (by rw [utf8Enc_append, List.length_append]; have := utf8Enc_length_le (tr w); omega)]
    simp

/-- The translation both twins apply to written text for a legal `newline`
other than `None`: `'
'` becomes `newline` when it starts with `'
'`. -/
def tcOf (nl : List Nat) (w : List Nat) : List Nat :=
  match nl with
  | 13 :: _ => replaceLf nl w
  | _ => w

/-- For a legal `newline` other than `None` (so no newline translation on
input), writing any strings into a fresh `StringIO()` and calling
`getvalue()` gives exactly the same results in both twins. Hypotheses: the
strings are `str` values (code points below 0x110000), and their total
length is below the allocation bound (no `MemoryError`). -/
def StringIOWritesTwinsNotNone : Prop :=
  ∀ (nl : List Nat) (ws : List (List Nat)), LegalNewline (some nl) →
    (∀ w ∈ ws, ValidStr w) → 8 * (ws.map List.length).sum + 16 < memLimit →
    runSC none (some nl) (ws.map SOp.write ++ [.getvalue]) =
      runSPy none (some nl) (ws.map SOp.write ++ [.getvalue])

theorem sum_le_map {α : Type} (l : List α) (f g : α → Nat) (h : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    have := h x (List.mem_cons_self ..)
    have := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    omega

instance (s : List Nat) : Decidable (ValidStr s) := inferInstanceAs (Decidable (∀ c ∈ s, c < 0x110000))

theorem if_contains_replace (n w : List Nat) :
    (if w.contains 10 = true then replaceLf n w else w) = replaceLf n w := by
  cases h : w.contains 10
  · simp [replaceLf_no_lf n w h]
  · simp

/-- The final assembly, for given initial states of both twins. -/
theorem writes_twins_of_init (nl : List Nat) (ws : List (List Nat)) (s0 : SCState) (t0 : TState)
    (hs0 : SC.init none (some nl) = .ok s0) (ht0 : TP.init none (some nl) = .ok t0)
    (hC0 : CInv [] s0 (tcOf nl)) (hP0 : PInv [] t0 (tcOf nl))
    (hnil : ∀ w ∈ ws, tcOf nl w = [] ↔ w = []) (hvalid : ∀ w ∈ ws, ValidStr (tcOf nl w))
    (hbound : 4 * (ws.map (fun w => (tcOf nl w).length)).sum + 8 < memLimit) :
    runSC none (some nl) (ws.map SOp.write ++ [.getvalue]) =
      runSPy none (some nl) (ws.map SOp.write ++ [.getvalue]) := by
  have hC := C_run (tcOf nl) ws [] s0 hC0 hnil (by simp; omega)
  have hP := P_run (tcOf nl) ws [] t0 hP0 hnil (by intro c hc; simp at hc) hvalid
    (by simp [utf8Enc_nil]; omega)
  unfold runSC runSPy
  rw [hs0, ht0]
  simp only [runOps'_eq, hC, hP]

theorem stringIOWritesTwinsNotNone_proven : StringIOWritesTwinsNotNone := by
  intro nl ws hleg hvw hb
  have hnl : nl = [] ∨ nl = [10] ∨ nl = [13] ∨ nl = [13, 10] := by
    rcases hleg with h | h | h | h | h <;> simp at h <;> simp [h]
  have hlen : ∀ w, (tcOf nl w).length ≤ 2 * w.length := by
    intro w
    rcases hnl with h | h | h | h <;> subst h <;> (try simp only [tcOf]) <;>
      first | omega | exact replaceLf_length_le _ _ (by decide)
  have hsum : (ws.map (fun w => (tcOf nl w).length)).sum ≤ 2 * (ws.map List.length).sum := by
    have := sum_le_map ws (fun w => (tcOf nl w).length) (fun w => 2 * w.length) (fun w _ => hlen w)
    have e : (ws.map (fun w => 2 * w.length)).sum = 2 * (ws.map List.length).sum := by
      clear this
      induction ws with
      | nil => rfl
      | cons x xs ih => simp only [List.map_cons, List.sum_cons]; rw [ih (fun w h => hvw w (List.mem_cons_of_mem _ h)) (by simp at hb; omega)]; omega
    omega
  have hnil : ∀ w ∈ ws, tcOf nl w = [] ↔ w = [] := by
    intro w _
    rcases hnl with h | h | h | h <;> subst h <;> (try simp only [tcOf]) <;>
      first | exact Iff.rfl | exact replaceLf_eq_nil _ _ (by decide)
  have hvalid : ∀ w ∈ ws, ValidStr (tcOf nl w) := by
    intro w hw
    rcases hnl with h | h | h | h <;> subst h <;> (try simp only [tcOf]) <;>
      first | exact hvw w hw | exact replaceLf_valid _ _ (by decide) (hvw w hw)
  have hbound : 4 * (ws.map (fun w => (tcOf nl w).length)).sum + 8 < memLimit := by omega
  rcases hnl with h | h | h | h <;> subst h
  · exact writes_twins_of_init [] ws _ _ rfl rfl ⟨rfl, rfl, rfl, rfl, fun w => rfl⟩
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun w => rfl⟩ hnil hvalid hbound
  · exact writes_twins_of_init [10] ws _ _ rfl rfl ⟨rfl, rfl, rfl, rfl, fun w => rfl⟩
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun w => by simp [pyTrans, tcOf]⟩ hnil hvalid hbound
  · exact writes_twins_of_init [13] ws _ _ rfl rfl ⟨rfl, rfl, rfl, rfl, fun w => rfl⟩
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun w => by simp [pyTrans, tcOf]; intro h; exact (replaceLf_no_lf _ _ (by simp [h])).symm⟩
      hnil hvalid hbound
  · exact writes_twins_of_init [13, 10] ws _ _ rfl rfl ⟨rfl, rfl, rfl, rfl, fun w => rfl⟩
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun w => by simp [pyTrans, tcOf]; intro h; exact (replaceLf_no_lf _ _ (by simp [h])).symm⟩
      hnil hvalid hbound

end PyLean.PyIO
