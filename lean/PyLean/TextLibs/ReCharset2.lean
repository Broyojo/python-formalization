import PyLean.TextLibs.ReCharset

/-!
The `for op, av in charset` loop of `_optimize_charset`, without case folding: the charmap and the
tail hold what the items said, through both sizes of the map and the `IndexError` fallbacks.
-/

namespace PyLean.TextLibs.Re

open PyLean

set_option linter.unusedSimpArgs false

/-- The map at `i`; `false` past its end. -/
def cmAt (cm : Array Bool) (i : Nat) : Bool := cm.getD i false

theorem cmAt_set (cm : Array Bool) (i x : Nat) (h : i < cm.size) :
    cmAt (cm.set! i true) x = (cmAt cm x || x == i) := by
  simp only [cmAt, Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds]
  by_cases hx : i = x
  · subst hx
    simp [h]
  · have : (x == i) = false := by simpa using fun h => hx h.symm
    simp [hx, this]

theorem cmAt_widen (cm : Array Bool) (x n : Nat) :
    cmAt (cm ++ Array.replicate n false) x = cmAt cm x := by
  simp only [cmAt, Array.getD_eq_getD_getElem?, Array.getElem?_append]
  split
  · rfl
  · rename_i h
    have h1 : cm[x]? = none := by simpa using h
    rw [h1]
    simp only [Option.getD_none, Array.getElem?_replicate]
    split <;> rfl

theorem cmAt_of_size (cm : Array Bool) (x : Nat) (h : cm.size ≤ x) : cmAt cm x = false := by
  simp [cmAt, Array.getD_eq_getD_getElem?, h]

/-- The map holds one of its two sizes. -/
def SizeOk (cm : Array Bool) : Prop := cm.size = 256 ∨ cm.size = 65536

/-- What a state says about `c`. -/
def stHit (flags : Nat) (st : OSt) (c : Nat) : Bool :=
  cmAt st.cm c || st.tail.any (siHit flags · c)

/-- An item of the parser's: what the loop can meet after `NEGATE`. -/
def Plain : CItem → Prop
  | .lit _ | .rng _ _ | .cat _ => True
  | _ => False

/-- The rest of a step's result: what does not change. -/
structure StepOk (flags : Nat) (st st' : OSt) (add : Nat → Bool) : Prop where
  out : st'.out = st.out
  size : SizeOk st'.cm
  cased : st'.cased = st.cased
  tail : (∀ x ∈ st.tail, Plain x) → ∀ x ∈ st'.tail, Plain x
  hit : ∀ c, stHit flags st' c = (stHit flags st c || add c)

theorem cmSet_some {cm : Array Bool} {i : Nat} (h : i < cm.size) :
    cmSet cm i = some (cm.set! i true) := by
  simp [cmSet, h]

theorem cmSet_none {cm : Array Bool} {i : Nat} (h : cm.size ≤ i) : cmSet cm i = none := by
  simp [cmSet]
  omega

theorem cmSet_some_none {cm : Array Bool} {i : Nat} (h : cm.size ≤ i) : cmSet cm i = none :=
  cmSet_none h

theorem size_set (cm : Array Bool) (i : Nat) : (cm.set! i true).size = cm.size := by
  simp

theorem size_app (cm : Array Bool) (n : Nat) : (cm ++ Array.replicate n false).size = cm.size + n := by
  simp

theorem mk_out (a b : List CItem) (c : Array Bool) (d : Bool) : (OSt.mk a b c d).out = a := rfl
theorem mk_tail (a b : List CItem) (c : Array Bool) (d : Bool) : (OSt.mk a b c d).tail = b := rfl
theorem mk_cm (a b : List CItem) (c : Array Bool) (d : Bool) : (OSt.mk a b c d).cm = c := rfl
theorem mk_cased (a b : List CItem) (c : Array Bool) (d : Bool) : (OSt.mk a b c d).cased = d := rfl

theorem widen_eq (st : OSt) :
    widen st = OSt.mk st.out st.tail (st.cm ++ Array.replicate widenBy false) st.cased := rfl

/-- What the proofs use of `widen`. They take it as a parameter, and these go through `mk_out` and
the like, because a plain `rfl` compares `widen st` with `st`, and the kernel then builds the 65280
elements of the padding. -/
structure WdOk (wd : OSt → OSt) : Prop where
  out : ∀ st, (wd st).out = st.out
  tail : ∀ st, (wd st).tail = st.tail
  cased : ∀ st, (wd st).cased = st.cased
  at_ : ∀ st x, cmAt (wd st).cm x = cmAt st.cm x
  size : ∀ st, st.cm.size = 256 → (wd st).cm.size = 65536

theorem widen_ok : WdOk widen := by
  refine ⟨fun st => ?_, fun st => ?_, fun st => ?_, fun st x => ?_, fun st h => ?_⟩
  · rw [widen_eq]
  · rw [widen_eq]
  · rw [widen_eq]
  · rw [widen_eq, mk_cm, cmAt_widen]
  · rw [widen_eq, mk_cm, size_app, h]
    rfl

theorem stHit_set (flags : Nat) (st : OSt) (c av : Nat) (h : av < st.cm.size) :
    stHit flags { st with cm := st.cm.set! av true } c = (stHit flags st c || c == av) := by
  simp only [stHit, cmAt_set _ _ _ h]
  cases cmAt st.cm c <;> cases c == av <;> simp

theorem stHit_wd {wd : OSt → OSt} (hw : WdOk wd) (flags : Nat) (st : OSt) (c : Nat) :
    stHit flags (wd st) c = stHit flags st c := by
  unfold stHit
  rw [hw.tail, hw.at_]

theorem stHit_tail (flags : Nat) (st : OSt) (c : Nat) (it : CItem) :
    stHit flags { st with tail := st.tail ++ [it] } c = (stHit flags st c || siHit flags it c) := by
  simp only [stHit, List.any_append, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]

theorem lit_out (st : OSt) (av : Nat) (h : st.cm.size ≤ av) : literalPass none st av = (st, av, true) := by
  unfold literalPass
  rw [cmSet_none h]

theorem lit_in (st : OSt) (av : Nat) (h : av < st.cm.size) :
    literalPass none st av = ({ st with cm := st.cm.set! av true }, av, false) := by
  unfold literalPass
  rw [cmSet_some h]

/-- `charmap[av] = 1`, with the `except IndexError`. -/
theorem doLiteral_none {wd : OSt → OSt} (hw : WdOk wd) (flags : Nat) (st : OSt) (av : Nat)
    (hs : SizeOk st.cm) : StepOk flags st (doLiteralW wd none st av) (fun c => c == av) := by
  by_cases h : av < st.cm.size
  · have e : doLiteralW wd none st av = { st with cm := st.cm.set! av true } := by
      simp [doLiteralW, lit_in st av h]
    rw [e]
    exact ⟨rfl, by simpa only [SizeOk, size_set] using hs, rfl, fun h x hx => h x hx,
      fun c => stHit_set _ _ _ _ h⟩
  · have h' : st.cm.size ≤ av := by omega
    by_cases h256 : st.cm.size = 256
    · have hz := hw.size st h256
      have hb : (st.cm.size == 256) = true := by simpa using h256
      by_cases h2 : av < (wd st).cm.size
      · have e : doLiteralW wd none st av = { wd st with cm := (wd st).cm.set! av true } := by
          simp [doLiteralW, lit_out st av h', hb, lit_in (wd st) av h2]
        rw [e]
        refine ⟨hw.out st, .inr (by rw [size_set]; exact hz), hw.cased st,
          fun h x hx => h x (hw.tail st ▸ hx), fun c => ?_⟩
        rw [stHit_set _ _ _ _ h2, stHit_wd hw]
      · have e : doLiteralW wd none st av = { wd st with tail := (wd st).tail ++ [.lit av] } := by
          simp [doLiteralW, lit_out st av h', hb, lit_out (wd st) av (by omega)]
        rw [e]
        refine ⟨hw.out st, .inr hz, hw.cased st, ?_, fun c => ?_⟩
        · intro h x hx
          simp only [List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | rfl
          · exact h x (hw.tail st ▸ hx)
          · trivial
        · rw [stHit_tail, stHit_wd hw]
          rfl
    · have hb : (st.cm.size == 256) = false := by simpa using h256
      have e : doLiteralW wd none st av = { st with tail := st.tail ++ [.lit av] } := by
        simp [doLiteralW, lit_out st av h', hb]
      rw [e]
      refine ⟨rfl, hs, rfl, ?_, fun c => ?_⟩
      · intro h x hx
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact h x hx
        · trivial
      · rw [stHit_tail]
        rfl

/-- The loop of a range: it marks what fits. -/
theorem rangeMark_none : ∀ (n i : Nat) (cm : Array Bool),
    (rangeMark none n i cm).1.size = cm.size ∧
    (∀ x, cmAt cm x = true → cmAt (rangeMark none n i cm).1 x = true) ∧
    (∀ x, cmAt (rangeMark none n i cm).1 x = true → cmAt cm x = true ∨ (i ≤ x ∧ x < i + n)) ∧
    ((rangeMark none n i cm).2 = false → ∀ x, i ≤ x → x < i + n → cmAt (rangeMark none n i cm).1 x = true) := by
  intro n
  induction n with
  | zero =>
    intro i cm
    have e : rangeMark none 0 i cm = (cm, false) := rfl
    rw [e]
    exact ⟨rfl, fun _ h => h, fun _ h => .inl h, fun _ x h1 h2 => by omega⟩
  | succ n ih =>
    intro i cm
    by_cases h : i < cm.size
    · have e : rangeMark none (n + 1) i cm = rangeMark none n (i + 1) (cm.set! i true) := by
        simp [rangeMark, cmSet_some h]
      rw [e]
      obtain ⟨h1, h2, h3, h4⟩ := ih (i + 1) (cm.set! i true)
      refine ⟨by rw [h1]; simp, fun x hx => h2 x ?_, fun x hx => ?_, fun he x h5 h6 => ?_⟩
      · rw [cmAt_set _ _ _ h, hx]
        rfl
      · rcases h3 x hx with h7 | ⟨h7, h8⟩
        · rw [cmAt_set _ _ _ h] at h7
          simp only [Bool.or_eq_true, beq_iff_eq] at h7
          rcases h7 with h7 | h7
          · exact .inl h7
          · exact .inr (by omega)
        · exact .inr (by omega)
      · by_cases h7 : x = i
        · subst h7
          apply h2
          rw [cmAt_set _ _ _ h]
          simp
        · exact h4 he x (by omega) (by omega)
    · have e : rangeMark none (n + 1) i cm = (cm, true) := by
        simp [rangeMark, cmSet_none (by omega : cm.size ≤ i)]
      rw [e]
      exact ⟨rfl, fun _ h => h, fun _ h => .inl h, by simp⟩

/-- The range's `try`, `:269-284`, with its fallbacks. -/
theorem doRange_none {wd : OSt → OSt} (hw : WdOk wd) (flags : Nat) (st : OSt) (lo hi : Nat)
    (hs : SizeOk st.cm) :
    StepOk flags st (doRangeW wd none st lo hi) (fun c => decide (lo ≤ c) && decide (c ≤ hi)) := by
  have hmem : ∀ c, (decide (lo ≤ c) && decide (c ≤ hi)) = true ↔ lo ≤ c ∧ c < lo + (hi + 1 - lo) := by
    intro c
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega
  obtain ⟨h1, h2, h3, h4⟩ := rangeMark_none (hi + 1 - lo) lo st.cm
  generalize hr : rangeMark none (hi + 1 - lo) lo st.cm = r1 at h1 h2 h3 h4
  obtain ⟨c1, e1⟩ := r1
  simp only at h1 h2 h3 h4
  /- A map that took the whole range. -/
  have full : ∀ cm : Array Bool, SizeOk cm → (∀ x, cmAt st.cm x = true → cmAt cm x = true) →
      (∀ x, cmAt cm x = true → cmAt st.cm x = true ∨ (lo ≤ x ∧ x < lo + (hi + 1 - lo))) →
      (∀ x, lo ≤ x → x < lo + (hi + 1 - lo) → cmAt cm x = true) →
      StepOk flags st { st with cm } (fun c => decide (lo ≤ c) && decide (c ≤ hi)) := by
    intro cm h5 h6 h7 h8
    refine ⟨rfl, h5, rfl, fun h x hx => h x hx, fun c => ?_⟩
    simp only [stHit]
    cases h9 : cmAt cm c with
    | true =>
      rcases h7 c h9 with h10 | h10
      · simp [h10]
      · have := (hmem c).2 h10
        simp [this]
    | false =>
      have h11 : cmAt st.cm c = false := by
        cases h : cmAt st.cm c with
        | false => rfl
        | true => rw [h6 c h] at h9; cases h9
      have h12 : (decide (lo ≤ c) && decide (c ≤ hi)) = false := by
        cases h : (decide (lo ≤ c) && decide (c ≤ hi)) with
        | false => rfl
        | true =>
          obtain ⟨h13, h14⟩ := (hmem c).1 h
          rw [h8 c h13 h14] at h9
          cases h9
      simp [h11, h12]
  /- A map that took part of it, with the range in the tail. -/
  have part : ∀ (cm : Array Bool), SizeOk cm → (∀ x, cmAt st.cm x = true → cmAt cm x = true) →
      (∀ x, cmAt cm x = true → cmAt st.cm x = true ∨ (lo ≤ x ∧ x < lo + (hi + 1 - lo))) →
      StepOk flags st { st with cm, tail := st.tail ++ [.rng lo hi] }
        (fun c => decide (lo ≤ c) && decide (c ≤ hi)) := by
    intro cm h5 h6 h7
    refine ⟨rfl, h5, rfl, ?_, fun c => ?_⟩
    · intro h x hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact h x hx
      · trivial
    · simp only [stHit, List.any_append, List.any_cons, List.any_nil, Bool.or_false, siHit]
      cases h9 : (decide (lo ≤ c) && decide (c ≤ hi)) with
      | true => simp
      | false =>
        have h10 : cmAt cm c = cmAt st.cm c := by
          cases h11 : cmAt st.cm c with
          | true => exact h6 c h11
          | false =>
            cases h12 : cmAt cm c with
            | false => rfl
            | true =>
              rcases h7 c h12 with h13 | h13
              · rw [h13] at h11; cases h11
              · rw [(hmem c).2 h13] at h9; cases h9
        simp [h10]
  cases e1 with
  | false =>
    have e : doRangeW wd none st lo hi = { st with cm := c1 } := by
      simp [doRangeW, hr]
    rw [e]
    exact full c1 (by simpa [SizeOk, h1] using hs) h2 h3 (h4 rfl)
  | true =>
    by_cases h256 : c1.size = 256
    · have hb : (c1.size == 256) = true := by simpa using h256
      generalize hW : wd { st with cm := c1 } = W
      have w1 : W.out = st.out := by rw [← hW]; exact hw.out _
      have w2 : W.tail = st.tail := by rw [← hW]; exact hw.tail _
      have w3 : W.cased = st.cased := by rw [← hW]; exact hw.cased _
      have w4 : ∀ x, cmAt W.cm x = cmAt c1 x := by
        intro x
        rw [← hW]
        exact hw.at_ _ x
      have hwz : W.cm.size = 65536 := by
        rw [← hW]
        exact hw.size _ h256
      obtain ⟨h5, h6, h7, h8⟩ := rangeMark_none (hi + 1 - lo) lo W.cm
      generalize hr2 : rangeMark none (hi + 1 - lo) lo W.cm = r2 at h5 h6 h7 h8
      obtain ⟨c2, e2⟩ := r2
      simp only at h5 h6 h7 h8
      have hsz : SizeOk c2 := .inr (by rw [h5]; exact hwz)
      have h9 : ∀ x, cmAt st.cm x = true → cmAt c2 x = true := fun x hx =>
        h6 x (by rw [w4]; exact h2 x hx)
      have h10 : ∀ x, cmAt c2 x = true → cmAt st.cm x = true ∨ (lo ≤ x ∧ x < lo + (hi + 1 - lo)) := by
        intro x hx
        rcases h7 x hx with h11 | h11
        · rw [w4] at h11
          exact h3 x h11
        · exact .inr h11
      cases e2 with
      | false =>
        have e : doRangeW wd none st lo hi = { W with cm := c2 } := by
          simp [doRangeW, hr, hb, hW, hr2]
        rw [e]
        have := full c2 hsz h9 h10 (h8 rfl)
        exact ⟨w1, hsz, w3, fun h x hx => h x (w2 ▸ hx), fun c => by
          have h13 := this.hit c
          exact (by simpa only [stHit, w2] using h13)⟩
      | true =>
        have e : doRangeW wd none st lo hi = { W with cm := c2, tail := W.tail ++ [.rng lo hi] } := by
          simp [doRangeW, hr, hb, hW, hr2]
        rw [e]
        have := part c2 hsz h9 h10
        refine ⟨w1, hsz, w3, ?_, fun c => ?_⟩
        · intro h x hx
          simp only [List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | rfl
          · exact h x (w2 ▸ hx)
          · trivial
        · have h13 := this.hit c
          simpa only [stHit, w2] using h13
    · have e : doRangeW wd none st lo hi = { st with cm := c1, tail := st.tail ++ [.rng lo hi] } := by
        simp [doRangeW, hr, h256]
      rw [e]
      exact part c1 (by simpa [SizeOk, h1] using hs) h2 h3

/-- `\d` and `\D`, under any flags, cover everything. -/
theorem cat_complement (flags c : Nat) (k : Cat) :
    (sreCategory (catCode flags k) c || sreCategory (catCode flags (chNegate k)) c) = true := by
  unfold catCode
  cases hl : hasFlag flags FLAG_LOCALE <;> cases hu : hasFlag flags FLAG_UNICODE <;> cases k <;>
    simp [chNegate, sreCategory]

/-- The loop, over items with no `NEGATE`. -/
theorem optLoop_none (flags : Nat) : ∀ (r : List CItem) (st : OSt), (∀ it ∈ r, Plain it) →
    SizeOk st.cm → (∀ x ∈ st.tail, Plain x) →
    match optLoop none r st with
    | .inr st' => st'.out = st.out ∧ SizeOk st'.cm ∧ (∀ x ∈ st'.tail, Plain x) ∧
        (∀ c, stHit flags st' c = (stHit flags st c || r.any (siHit flags · c)))
    | .inl out => out = (if st.out.isEmpty then [.neg] else []) ∧
        ∀ c, (stHit flags st c || r.any (siHit flags · c)) = true := by
  intro r
  induction r with
  | nil =>
    intro st _ hs ht
    exact ⟨rfl, hs, ht, fun c => by simp⟩
  | cons it r ih =>
    intro st hr hs ht
    have hr' : ∀ x ∈ r, Plain x := fun x hx => hr x (by simp [hx])
    have hit : Plain it := hr it (by simp)
    /- A step, then the rest. -/
    have step : ∀ st1 : OSt, ∀ (a : Nat → Bool), StepOk flags st st1 a →
        (∀ c, a c = siHit flags it c) →
        (match optLoop none r st1 with
         | .inr st' => st'.out = st.out ∧ SizeOk st'.cm ∧ (∀ x ∈ st'.tail, Plain x) ∧
             (∀ c, stHit flags st' c = (stHit flags st c || (it :: r).any (siHit flags · c)))
         | .inl out => out = (if st.out.isEmpty then [.neg] else []) ∧
             ∀ c, (stHit flags st c || (it :: r).any (siHit flags · c)) = true) := by
      intro st1 a h1 ha
      have h2 := ih st1 hr' h1.size (h1.tail ht)
      have hall : ∀ c, (stHit flags st1 c || r.any (siHit flags · c)) =
          (stHit flags st c || (it :: r).any (siHit flags · c)) := by
        intro c
        rw [h1.hit, ha, List.any_cons, Bool.or_assoc]
      cases h3 : optLoop none r st1 with
      | inr st' =>
        rw [h3] at h2
        obtain ⟨h4, h5, h6, h7⟩ := h2
        exact ⟨h4.trans h1.out, h5, h6, fun c => by rw [h7, hall]⟩
      | inl out =>
        rw [h3] at h2
        obtain ⟨h4, h5⟩ := h2
        rw [h1.out] at h4
        exact ⟨h4, fun c => by rw [← hall]; exact h5 c⟩
    match it, hit with
    | .lit av, _ =>
      show (match optLoop none r (doLiteral none st av) with
        | .inr st' => _
        | .inl out => _)
      exact step _ _ (doLiteral_none widen_ok flags st av hs) (fun _ => rfl)
    | .rng lo hi, _ =>
      show (match optLoop none r (doRange none st lo hi) with
        | .inr st' => _
        | .inl out => _)
      exact step _ _ (doRange_none widen_ok flags st lo hi hs) (fun _ => rfl)
    | .cat k, _ =>
      by_cases hc : (!st.tail.isEmpty) = true ∧ CItem.cat (chNegate k) ∈ st.tail
      · have e : optLoop none (.cat k :: r) st = .inl (if st.out.isEmpty then [.neg] else []) := by
          simp only [optLoop]
          rw [if_pos hc]
        rw [e]
        refine ⟨rfl, fun c => ?_⟩
        have h1 : st.tail.any (siHit flags · c) = true ∨
            sreCategory (catCode flags k) c = true := by
          have h2 := cat_complement flags c k
          simp only [Bool.or_eq_true] at h2
          rcases h2 with h2 | h2
          · exact .inr h2
          · exact .inl (List.any_eq_true.2 ⟨_, hc.2, h2⟩)
        simp only [stHit, List.any_cons, siHit, Bool.or_eq_true]
        rcases h1 with h1 | h1
        · exact .inl (.inr h1)
        · exact .inr (.inl h1)
      · have e : optLoop none (.cat k :: r) st = optLoop none r { st with tail := st.tail ++ [.cat k] } := by
          simp only [optLoop]
          rw [if_neg hc]
        rw [e]
        refine step _ (siHit flags (.cat k)) ⟨rfl, hs, rfl, ?_, fun c => stHit_tail _ _ _ _⟩ (fun _ => rfl)
        intro h x hx
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact h x hx
        · trivial

/-- A list with no `NEGATE`, read by `hitList`. -/
theorem hitList_plain (flags c : Nat) : ∀ (r : List CItem) (ok : Bool), (∀ x ∈ r, x ≠ .neg) →
    hitList flags ok r c = if r.any (siHit flags · c) then ok else !ok := by
  intro r
  induction r with
  | nil => intro ok _; simp [hitList]
  | cons it r ih =>
    intro ok h
    have hr := ih ok (fun x hx => h x (by simp [hx]))
    have hne := h it (by simp)
    cases it with
    | neg => exact absurd rfl hne
    | lit a =>
      simp only [hitList, hr, List.any_cons]
      by_cases h1 : siHit flags (.lit a) c = true <;> simp [h1]
    | rng a b =>
      simp only [hitList, hr, List.any_cons]
      by_cases h1 : siHit flags (.rng a b) c = true <;> simp [h1]
    | rngUni a b =>
      simp only [hitList, hr, List.any_cons]
      by_cases h1 : siHit flags (.rngUni a b) c = true <;> simp [h1]
    | cat k =>
      simp only [hitList, hr, List.any_cons]
      by_cases h1 : siHit flags (.cat k) c = true <;> simp [h1]
    | charset d =>
      simp only [hitList, hr, List.any_cons]
      by_cases h1 : siHit flags (.charset d) c = true <;> simp [h1]
    | big d =>
      simp only [hitList, hr, List.any_cons]
      by_cases h1 : siHit flags (.big d) c = true <;> simp [h1]

end PyLean.TextLibs.Re
