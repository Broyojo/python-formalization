import PyLean.TextLibs.ReEngine

/-!
The zero-width shortcut of `zwSkip` changes no result of the engine.

`Env.fast := false` turns the shortcut off: `exec` then runs `MAX_UNTIL` and `MIN_UNTIL` below
`min` exactly as `Modules/_sre/sre_lib.h:1220-1232` and `:1284-1296` do, one item per level. With
the shortcut on, a run the step-by-step engine finishes gives the same result, with no more fuel
(`fast_complete`), and two finished runs never disagree (`fast_sound`). So the shortcut only lets
the model finish runs the C finishes but the fuel does not reach, such as `(?=){4294967294}x`.
-/

namespace PyLean.TextLibs.Re

open PyLean

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def Env.withFast (e : Env) (b : Bool) : Env := { e with fast := b }

section withFast
variable (e : Env) (b : Bool)
@[simp] theorem Env.withFast_c (i : Nat) : (e.withFast b).c i = e.c i := rfl
@[simp] theorem Env.withFast_ch (i : Nat) : (e.withFast b).ch i = e.ch i := rfl
@[simp] theorem Env.withFast_endp : (e.withFast b).endp = e.endp := rfl
@[simp] theorem Env.withFast_matchAll : (e.withFast b).matchAll = e.matchAll := rfl
@[simp] theorem Env.withFast_code : (e.withFast b).code = e.code := rfl
@[simp] theorem Env.withFast_s : (e.withFast b).s = e.s := rfl
@[simp] theorem Env.withFast_fast : (e.withFast b).fast = b := rfl
@[simp] theorem Env.withFast_self : e.withFast e.fast = e := rfl
theorem sreCharset_withFast (ch : Nat) : ∀ fuel set ok,
    sreCharset (e.withFast b) ch fuel set ok = sreCharset e ch fuel set ok := by
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ n ih => intro set ok; simp only [sreCharset, Env.withFast_c, ih]
@[simp] theorem Env.withFast_charset (set ch : Nat) : (e.withFast b).charset set ch = e.charset set ch := by
  simp only [Env.charset, sreCharset_withFast, Env.withFast_code]
@[simp] theorem Env.withFast_charset' (set : Nat) : (e.withFast b).charset set = e.charset set :=
  funext fun ch => Env.withFast_charset e b set ch
@[simp] theorem Env.withFast_charsetLoc (set ch : Nat) : (e.withFast b).charsetLoc set ch = e.charsetLoc set ch := by
  simp only [Env.charsetLoc, Env.withFast_charset]
theorem Env.withFast_countWhile (cond : Nat → Bool) (lim : Nat) : ∀ fuel ptr,
    (e.withFast b).countWhile cond lim fuel ptr = e.countWhile cond lim fuel ptr := by
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ n ih => intro ptr; simp only [Env.countWhile, Env.withFast_ch, ih]
@[simp] theorem Env.withFast_countSimple (pc ptr lim : Nat) :
    (e.withFast b).countSimple pc ptr lim = e.countSimple pc ptr lim := by
  simp only [Env.countSimple, Env.withFast_c, Env.withFast_countWhile, Env.withFast_charset']
@[simp] theorem Env.withFast_countEnd (ptr mc : Nat) : (e.withFast b).countEnd ptr mc = e.countEnd ptr mc := rfl
theorem Env.withFast_refMatch' (norm : Nat → Nat) : ∀ fuel p q ptr,
    (e.withFast b).refMatch norm fuel p q ptr = e.refMatch norm fuel p q ptr := by
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ n ih => intro p q ptr; simp only [Env.refMatch, Env.withFast_ch, Env.withFast_endp, ih]; rfl
@[simp] theorem Env.withFast_refMatch (norm : Nat → Nat) (fuel p q ptr : Nat) :
    (e.withFast b).refMatch norm fuel p q ptr = e.refMatch norm fuel p q ptr :=
  Env.withFast_refMatch' e b norm fuel p q ptr
@[simp] theorem Env.withFast_oneChar (op p cur : Nat) : (e.withFast b).oneChar op p cur = e.oneChar op p cur := by
  simp only [Env.oneChar, Env.withFast_c, Env.withFast_charset, Env.withFast_charsetLoc]
@[simp] theorem sreAt_withFast (ptr a : Nat) : sreAt (e.withFast b) ptr a = sreAt e ptr a := rfl
@[simp] theorem Env.withFast_mfuel : (e.withFast b).mfuel = e.mfuel := rfl
@[simp] theorem zwSkip_slow (pc ptr : Nat) (top : Bool) (i : Nat) (count mn : Int) (pat : Nat) (st : SSt) :
    zwSkip (e.withFast false) pc ptr top i count mn pat st = none := by
  simp [zwSkip]
theorem lin_withFast : ∀ fuel stop pc ptr top st,
    lin (e.withFast b) stop fuel pc ptr top st = lin e stop fuel pc ptr top st := by
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ n ih =>
    intro stop pc ptr top st
    simp only [lin, Env.withFast_c, Env.withFast_ch, Env.withFast_endp, Env.withFast_matchAll,
      Env.withFast_oneChar, sreAt_withFast, ih]
    rfl
end withFast

/-- The opcodes as numerals, so that `simp` decides which branch of `exec` runs. -/
macro "op_simp" : tactic => `(tactic| simp only [OP_FAILURE, OP_SUCCESS, OP_ANY, OP_ANY_ALL,
  OP_ASSERT, OP_ASSERT_NOT, OP_AT, OP_BRANCH, OP_CATEGORY, OP_CHARSET, OP_BIGCHARSET, OP_GROUPREF,
  OP_GROUPREF_EXISTS, OP_IN, OP_INFO, OP_JUMP, OP_LITERAL, OP_MARK, OP_MAX_UNTIL, OP_MIN_UNTIL,
  OP_NOT_LITERAL, OP_NEGATE, OP_RANGE, OP_REPEAT, OP_REPEAT_ONE, OP_MIN_REPEAT_ONE,
  OP_ATOMIC_GROUP, OP_POSSESSIVE_REPEAT, OP_POSSESSIVE_REPEAT_ONE, OP_GROUPREF_IGNORE,
  OP_IN_IGNORE, OP_LITERAL_IGNORE, OP_NOT_LITERAL_IGNORE, OP_GROUPREF_LOC_IGNORE, OP_IN_LOC_IGNORE,
  OP_LITERAL_LOC_IGNORE, OP_NOT_LITERAL_LOC_IGNORE, OP_GROUPREF_UNI_IGNORE, OP_IN_UNI_IGNORE,
  OP_LITERAL_UNI_IGNORE, OP_NOT_LITERAL_UNI_IGNORE, OP_RANGE_UNI_IGNORE, Bool.false_eq_true,
  ↓reduceIte, beq_self_eq_true, Bool.or_false, Bool.false_or, Bool.true_or, Bool.or_true,
  Bool.and_true, Bool.true_and, Nat.reduceBEq])

/-! ### One step of `exec` on the ops of `lin` -/

section steps
variable (e : Env) (F pc ptr : Nat) (top : Bool) (st : SSt)

set_option hygiene false in
/-- One op of `Env.oneChar`: either it is this op, and `exec` takes the same step, or `h` moves on. -/
macro "oc_step" op:term : tactic => `(tactic| (
  by_cases hop : (e.c pc == $op) = true
  · rw [if_pos hop] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    rw [beq_iff_eq] at hop
    simp only [exec, hop]
    op_simp
    try simp only [bne, Bool.not_not, Bool.not_true, Bool.or_false]
  rw [if_neg hop] at h))

theorem exec_oneChar (ok : Bool) (nxt : Nat) (h : e.oneChar (e.c pc) (pc + 1) (e.ch ptr) = some (ok, nxt)) :
    exec e (F + 1) pc ptr top st =
      if (!decide (ptr < e.endp) || !ok) = true then some (false, st)
      else exec e F nxt (ptr + 1) top st := by
  unfold Env.oneChar at h
  oc_step OP_LITERAL
  oc_step OP_NOT_LITERAL
  oc_step OP_CATEGORY
  oc_step OP_ANY
  oc_step OP_ANY_ALL
  oc_step OP_IN
  oc_step OP_LITERAL_IGNORE
  oc_step OP_LITERAL_UNI_IGNORE
  oc_step OP_LITERAL_LOC_IGNORE
  oc_step OP_NOT_LITERAL_IGNORE
  oc_step OP_NOT_LITERAL_UNI_IGNORE
  oc_step OP_NOT_LITERAL_LOC_IGNORE
  oc_step OP_IN_IGNORE
  oc_step OP_IN_UNI_IGNORE
  oc_step OP_IN_LOC_IGNORE
  cases h

theorem exec_mark (h : e.c pc = OP_MARK) :
    exec e (F + 1) pc ptr top st = exec e F (pc + 1 + 1) ptr top (doMark st (e.c (pc + 1)) ptr) := by
  simp only [exec, h]; op_simp; try rfl

theorem exec_success (h : e.c pc = OP_SUCCESS) :
    exec e (F + 1) pc ptr top st =
      if (top && ((e.matchAll && ptr != e.endp) || (st.mustAdvance && ptr == st.start))) = true then
        some (false, st)
      else some (true, { st with ptr }) := by
  simp only [exec, h]; op_simp; try rfl

theorem exec_at (h : e.c pc = OP_AT) :
    exec e (F + 1) pc ptr top st =
      if (!sreAt e ptr (e.c (pc + 1))) = true then some (false, st)
      else exec e F (pc + 1 + 1) ptr top st := by
  simp only [exec, h]; op_simp; try rfl

theorem exec_jump (h : e.c pc = OP_JUMP ∨ e.c pc = OP_INFO) :
    exec e (F + 1) pc ptr top st = exec e F (pc + 1 + e.c (pc + 1)) ptr top st := by
  rcases h with h | h <;> simp only [exec, h] <;> op_simp

theorem exec_failure (h : e.c pc = OP_FAILURE) : exec e (F + 1) pc ptr top st = some (false, st) := by
  simp only [exec, h]; op_simp; try rfl

theorem exec_assert (h : e.c pc = OP_ASSERT) :
    exec e (F + 1) pc ptr top st =
      if ptr < e.c (pc + 1 + 1) then some (false, st)
      else
        match matchAt e F (pc + 1 + 2) false { st with ptr := ptr - e.c (pc + 1 + 1) } with
        | none => none
        | some (false, st) => some (false, st)
        | some (true, st) => exec e F (pc + 1 + e.c (pc + 1)) ptr top st := by
  simp only [exec, h]; op_simp; try rfl

theorem exec_assertNot (h : e.c pc = OP_ASSERT_NOT) :
    exec e (F + 1) pc ptr top st =
      if ptr ≥ e.c (pc + 1 + 1) then
        match matchAt e F (pc + 1 + 2) false { st with ptr := ptr - e.c (pc + 1 + 1) } with
        | none => none
        | some (true, st) => some (false, st)
        | some (false, st2) =>
          let st2 := if st.repeat_.isSome then markPop st2 (if st.repeat_.isSome then markSnap st st.lastmark else #[]) else st2
          exec e F (pc + 1 + e.c (pc + 1)) ptr top (lastRestore st2 st.lastmark st.lastindex)
      else exec e F (pc + 1 + e.c (pc + 1)) ptr top st := by
  simp only [exec, h]; op_simp; try rfl

theorem matchAt_noinfo (h : e.c pc ≠ OP_INFO) : matchAt e (F + 1) pc top st = exec e F pc st.ptr top st := by
  simp only [matchAt]
  rw [if_neg (by simpa using h)]

theorem exec_until_ptr (q : Nat) (h : e.c pc = OP_MAX_UNTIL ∨ e.c pc = OP_MIN_UNTIL) :
    ∀ F, exec e F pc ptr top { st with ptr := q } = exec e F pc ptr top st
  | 0 => by simp only [exec]
  | F + 1 => by rcases h with h | h <;> simp only [exec, h] <;> op_simp <;> rfl

end steps

/-! ### `lin` is `exec` -/

/-- What a run of `exec` with fuel `F` that gives `r` says about the `lin` result `lr`. -/
def LinR.Sat (e : Env) (stop : Option Nat) (top : Bool) (F : Nat) (r : Bool × SSt) : LinR → Prop
  | .done r' => r' = some r
  | .reach ptr' st' => ∃ s F', stop = some s ∧ F' ≤ F ∧ exec e F' s ptr' top st' = some r

theorem LinR.Sat.mono {e : Env} {stop top F G r} {lr : LinR} (h : lr.Sat e stop top F r) (hFG : F ≤ G) :
    lr.Sat e stop top G r := by
  cases lr with
  | done r' => exact h
  | reach p s =>
    obtain ⟨s', F', h1, h2, h3⟩ := h
    exact ⟨s', F', h1, Nat.le_trans h2 hFG, h3⟩

/-- Whatever `lin` returns, `exec` agrees with it: the same outcome, or the same state at `stop`. -/
theorem lin_exec (e : Env) : ∀ k stop pc ptr top st lr, lin e stop k pc ptr top st = some lr →
    ∀ F r, exec e F pc ptr top st = some r → lr.Sat e stop top F r := by
  intro k
  induction k with
  | zero => intro stop pc ptr top st lr hl; simp only [lin] at hl; cases hl
  | succ k ih =>
    intro stop pc ptr top st lr hl F r hx
    cases F with
    | zero => simp only [exec] at hx; cases hx
    | succ F =>
    simp only [lin] at hl
    by_cases hs : (stop == some pc) = true
    · rw [if_pos hs] at hl
      cases hl
      exact ⟨pc, F + 1, beq_iff_eq.mp hs, Nat.le_refl _, hx⟩
    rw [if_neg hs] at hl
    cases hoc : e.oneChar (e.c pc) (pc + 1) (e.ch ptr) with
    | some okn =>
      obtain ⟨ok, nxt⟩ := okn
      rw [hoc] at hl
      simp only at hl
      rw [exec_oneChar e F pc ptr top st ok nxt hoc] at hx
      by_cases hf : (!decide (ptr < e.endp) || !ok) = true
      · rw [if_pos hf] at hl hx
        cases hl; cases hx; rfl
      · rw [if_neg hf] at hl hx
        exact (ih _ _ _ _ _ _ hl F r hx).mono (Nat.le_succ F)
    | none =>
      rw [hoc] at hl
      simp only at hl
      by_cases hm : (e.c pc == OP_MARK) = true
      · rw [if_pos hm] at hl
        rw [exec_mark e F pc ptr top st (beq_iff_eq.mp hm)] at hx
        exact (ih _ _ _ _ _ _ hl F r hx).mono (Nat.le_succ F)
      rw [if_neg hm] at hl
      by_cases hsu : (e.c pc == OP_SUCCESS) = true
      · rw [if_pos hsu] at hl
        rw [exec_success e F pc ptr top st (beq_iff_eq.mp hsu)] at hx
        split at hl <;> split at hx <;> (first | contradiction | (cases hl; cases hx; rfl))
      rw [if_neg hsu] at hl
      by_cases ha : (e.c pc == OP_AT) = true
      · rw [if_pos ha] at hl
        rw [exec_at e F pc ptr top st (beq_iff_eq.mp ha)] at hx
        split at hl <;> split at hx <;> (first | contradiction | (cases hl; cases hx; rfl) |
          exact (ih _ _ _ _ _ _ hl F r hx).mono (Nat.le_succ F))
      rw [if_neg ha] at hl
      by_cases hj : (e.c pc == OP_JUMP || e.c pc == OP_INFO) = true
      · rw [if_pos hj] at hl
        rw [exec_jump e F pc ptr top st (by simpa [Bool.or_eq_true, beq_iff_eq] using hj)] at hx
        exact (ih _ _ _ _ _ _ hl F r hx).mono (Nat.le_succ F)
      rw [if_neg hj] at hl
      by_cases has : (e.c pc == OP_ASSERT) = true
      · rw [if_pos has] at hl
        rw [exec_assert e F pc ptr top st (beq_iff_eq.mp has)] at hx
        by_cases hlt : ptr < e.c (pc + 1 + 1)
        · rw [if_pos hlt] at hl hx
          cases hl; cases hx; rfl
        rw [if_neg hlt] at hl hx
        by_cases hi : (e.c (pc + 1 + 2) == OP_INFO) = true
        · rw [if_pos hi] at hl; cases hl
        rw [if_neg hi] at hl
        cases hsub : lin e none k (pc + 1 + 2) (ptr - e.c (pc + 1 + 1)) false
            { st with ptr := ptr - e.c (pc + 1 + 1) } with
        | none => rw [hsub] at hl; simp only at hl; cases hl
        | some lr2 =>
          rw [hsub] at hl
          cases hm2 : matchAt e F (pc + 1 + 2) false { st with ptr := ptr - e.c (pc + 1 + 1) } with
          | none => rw [hm2] at hx; simp only at hx; cases hx
          | some v =>
            rw [hm2] at hx
            cases F with
            | zero => simp only [matchAt] at hm2; cases hm2
            | succ F1 =>
              rw [matchAt_noinfo e F1 _ false _ (by simpa using hi)] at hm2
              have hs2 := ih _ _ _ _ _ _ hsub F1 v hm2
              cases lr2 with
              | reach p s => obtain ⟨s', _, hs', _⟩ := hs2; cases hs'
              | done r2 =>
                cases hs2
                obtain ⟨b, s⟩ := v
                cases b
                · simp only at hl hx
                  cases hl; cases hx; rfl
                · simp only at hl hx
                  exact (ih _ _ _ _ _ _ hl (F1 + 1) r hx).mono (by omega)
      rw [if_neg has] at hl
      by_cases hn : (e.c pc == OP_ASSERT_NOT) = true
      · rw [if_pos hn] at hl
        rw [exec_assertNot e F pc ptr top st (beq_iff_eq.mp hn)] at hx
        by_cases hge : ptr ≥ e.c (pc + 1 + 1)
        · rw [if_pos hge] at hl hx
          by_cases hi : (e.c (pc + 1 + 2) == OP_INFO) = true
          · rw [if_pos hi] at hl; cases hl
          rw [if_neg hi] at hl
          cases hsub : lin e none k (pc + 1 + 2) (ptr - e.c (pc + 1 + 1)) false
              { st with ptr := ptr - e.c (pc + 1 + 1) } with
          | none => rw [hsub] at hl; simp only at hl; cases hl
          | some lr2 =>
            rw [hsub] at hl
            cases hm2 : matchAt e F (pc + 1 + 2) false { st with ptr := ptr - e.c (pc + 1 + 1) } with
            | none => rw [hm2] at hx; simp only at hx; cases hx
            | some v =>
              rw [hm2] at hx
              cases F with
              | zero => simp only [matchAt] at hm2; cases hm2
              | succ F1 =>
                rw [matchAt_noinfo e F1 _ false _ (by simpa using hi)] at hm2
                have hs2 := ih _ _ _ _ _ _ hsub F1 v hm2
                cases lr2 with
                | reach p s => obtain ⟨s', _, hs', _⟩ := hs2; cases hs'
                | done r2 =>
                  cases hs2
                  obtain ⟨b, s⟩ := v
                  cases b
                  · simp only at hl hx
                    exact (ih _ _ _ _ _ _ hl (F1 + 1) r hx).mono (by omega)
                  · simp only at hl hx
                    cases hl; cases hx; rfl
        · rw [if_neg hge] at hl hx
          exact (ih _ _ _ _ _ _ hl F r hx).mono (Nat.le_succ F)
      rw [if_neg hn] at hl
      by_cases hfa : (e.c pc == OP_FAILURE) = true
      · rw [if_pos hfa] at hl
        rw [exec_failure e F pc ptr top st (beq_iff_eq.mp hfa)] at hx
        cases hl; cases hx; rfl
      rw [if_neg hfa] at hl
      cases hl

/-! ### `lin` does not read the repeats -/

def LinR.withReps (R : Array Rep) : LinR → LinR
  | .done (some (b, s)) => .done (some (b, { s with reps := R }))
  | .done none => .done none
  | .reach p s => .reach p { s with reps := R }

theorem lin_withReps (e : Env) : ∀ k stop pc ptr top st lr, lin e stop k pc ptr top st = some lr →
    ∀ R, lin e stop k pc ptr top { st with reps := R } = some (lr.withReps R) := by
  intro k
  induction k with
  | zero => intro stop pc ptr top st lr hl; simp only [lin] at hl; cases hl
  | succ k ih =>
    intro stop pc ptr top st lr hl R
    simp only [lin] at hl ⊢
    by_cases hs : (stop == some pc) = true
    · rw [if_pos hs] at hl ⊢
      cases hl; rfl
    rw [if_neg hs] at hl ⊢
    cases hoc : e.oneChar (e.c pc) (pc + 1) (e.ch ptr) with
    | some okn =>
      obtain ⟨ok, nxt⟩ := okn
      simp only [hoc] at hl ⊢
      by_cases hf : (!decide (ptr < e.endp) || !ok) = true
      · rw [if_pos hf] at hl ⊢
        cases hl; rfl
      · rw [if_neg hf] at hl ⊢
        exact ih _ _ _ _ _ _ hl R
    | none =>
      simp only [hoc] at hl ⊢
      by_cases hm : (e.c pc == OP_MARK) = true
      · rw [if_pos hm] at hl ⊢
        exact ih _ _ _ _ _ _ hl R
      rw [if_neg hm] at hl ⊢
      by_cases hsu : (e.c pc == OP_SUCCESS) = true
      · rw [if_pos hsu] at hl ⊢
        by_cases hc : (top && (e.matchAll && ptr != e.endp || st.mustAdvance && ptr == st.start)) = true
        · rw [if_pos hc] at hl ⊢; cases hl; rfl
        · rw [if_neg hc] at hl ⊢; cases hl; rfl
      rw [if_neg hsu] at hl ⊢
      by_cases ha : (e.c pc == OP_AT) = true
      · rw [if_pos ha] at hl ⊢
        by_cases hc : (!sreAt e ptr (e.c (pc + 1))) = true
        · rw [if_pos hc] at hl ⊢; cases hl; rfl
        · rw [if_neg hc] at hl ⊢; exact ih _ _ _ _ _ _ hl R
      rw [if_neg ha] at hl ⊢
      by_cases hj : (e.c pc == OP_JUMP || e.c pc == OP_INFO) = true
      · rw [if_pos hj] at hl ⊢
        exact ih _ _ _ _ _ _ hl R
      rw [if_neg hj] at hl ⊢
      by_cases has : (e.c pc == OP_ASSERT) = true
      · rw [if_pos has] at hl ⊢
        by_cases hlt : ptr < e.c (pc + 1 + 1)
        · rw [if_pos hlt] at hl ⊢; cases hl; rfl
        rw [if_neg hlt] at hl ⊢
        by_cases hi : (e.c (pc + 1 + 2) == OP_INFO) = true
        · rw [if_pos hi] at hl; cases hl
        rw [if_neg hi] at hl ⊢
        cases hsub : lin e none k (pc + 1 + 2) (ptr - e.c (pc + 1 + 1)) false
            { st with ptr := ptr - e.c (pc + 1 + 1) } with
        | none => rw [hsub] at hl; simp only at hl; cases hl
        | some lr2 =>
          have h2 := ih _ _ _ _ _ _ hsub R
          simp only at h2
          rw [hsub] at hl
          rw [h2]
          cases lr2 with
          | reach p s => simp only at hl; cases hl
          | done r2 =>
            cases r2 with
            | none => simp only at hl; cases hl
            | some v =>
              obtain ⟨b, s⟩ := v
              cases b
              · simp only [LinR.withReps] at hl ⊢; cases hl; rfl
              · simp only [LinR.withReps] at hl ⊢; exact ih _ _ _ _ _ _ hl R
      rw [if_neg has] at hl ⊢
      by_cases hn : (e.c pc == OP_ASSERT_NOT) = true
      · rw [if_pos hn] at hl ⊢
        by_cases hge : ptr ≥ e.c (pc + 1 + 1)
        · rw [if_pos hge] at hl ⊢
          by_cases hi : (e.c (pc + 1 + 2) == OP_INFO) = true
          · rw [if_pos hi] at hl; cases hl
          rw [if_neg hi] at hl ⊢
          cases hsub : lin e none k (pc + 1 + 2) (ptr - e.c (pc + 1 + 1)) false
              { st with ptr := ptr - e.c (pc + 1 + 1) } with
          | none => rw [hsub] at hl; simp only at hl; cases hl
          | some lr2 =>
            have h2 := ih _ _ _ _ _ _ hsub R
            simp only at h2
            rw [hsub] at hl
            rw [h2]
            cases lr2 with
            | reach p s => simp only at hl; cases hl
            | done r2 =>
              cases r2 with
              | none => simp only at hl; cases hl
              | some v =>
                obtain ⟨b, s⟩ := v
                cases b
                · simp only [LinR.withReps] at hl ⊢
                  by_cases hr : st.repeat_.isSome = true <;> simp only [hr] at hl ⊢ <;>
                    exact ih _ _ _ _ _ _ hl R
                · simp only [LinR.withReps] at hl ⊢; cases hl; rfl
        · rw [if_neg hge] at hl ⊢
          exact ih _ _ _ _ _ _ hl R
      rw [if_neg hn] at hl ⊢
      by_cases hfa : (e.c pc == OP_FAILURE) = true
      · rw [if_pos hfa] at hl ⊢; cases hl; rfl
      rw [if_neg hfa] at hl
      cases hl

/-! ### The `count < min` case, level by level -/

theorem modify_modify_same {α : Type} (a : Array α) (i : Nat) (f g : α → α) :
    (a.modify i f).modify i g = a.modify i (g ∘ f) := by
  apply Array.ext_getElem?
  intro j
  simp only [Array.getElem?_modify]
  by_cases h : i = j <;> simp [h, Option.map_map]

theorem setRep_setRep (st : SSt) (i : Nat) (f g : Rep → Rep) :
    (st.setRep i f).setRep i g = st.setRep i (g ∘ f) := by
  simp only [SSt.setRep, modify_modify_same]

theorem setRep_get (st : SSt) (i : Nat) (f : Rep → Rep) (h : i < st.reps.size) :
    (st.setRep i f).reps[i]! = f st.reps[i]! := by
  simp only [SSt.setRep]
  rw [getElem!_pos (st.reps.modify i f) i (by simpa using h), getElem!_pos st.reps i h,
    Array.getElem_modify_self]

/-- Setting the count again to the value it was set to changes nothing. -/
theorem setRep_idem (st X : SSt) (i : Nat) (f : Rep → Rep) (hf : ∀ r, f (f r) = f r)
    (h : st.reps = (X.setRep i f).reps) : st.setRep i f = st := by
  have : st.reps.modify i f = st.reps := by
    rw [h]
    simp only [SSt.setRep, modify_modify_same]
    congr 1
    funext r
    exact hf r
  unfold SSt.setRep
  rw [this]

theorem untilBack_mono {a b : R} (hab : ∀ v, a = some v → b = some v) {i p : Nat} {c : Int} {r : Bool × SSt}
    (h : untilBack i p c a = some r) : untilBack i p c b = some r := by
  cases a with
  | none => cases h
  | some v => rw [hab v rfl]; exact h

/-- Two failed levels leave what the outer one leaves: `count` and `ptr` are overwritten. -/
theorem untilBack_twice (i p : Nat) (c d : Int) (r : R) :
    untilBack i p c (untilBack i p d r) = untilBack i p c r := by
  rcases r with _ | ⟨b, s⟩
  · rfl
  · cases b
    · simp only [untilBack, SSt.setRep, modify_modify_same, Function.comp_def]
    · rfl

theorem ite_sim {α : Type} {c : Prop} [Decidable c] {a b a' b' : Option α} {r : α}
    (h : (if c then a else b) = some r) (ha : c → a = some r → a' = some r)
    (hb : ¬c → b = some r → b' = some r) : (if c then a' else b') = some r := by
  by_cases hc : c
  · rw [if_pos hc] at h ⊢; exact ha hc h
  · rw [if_neg hc] at h ⊢; exact hb hc h

/-- The step-by-step `UNTIL` below `min`: the item, then this `UNTIL` again, under `untilBack`. -/
theorem exec_until_low (e : Env) (F pc ptr : Nat) (top : Bool) (st : SSt) (i : Nat) (c : Int)
    (pat : Nat) (S : SSt) (hop : e.c pc = OP_MAX_UNTIL ∨ e.c pc = OP_MIN_UNTIL)
    (hrep : st.repeat_ = some i) (hc : st.reps[i]!.count + 1 = c) (hpat : st.reps[i]!.pat = pat)
    (hlt : c < (e.c (pat + 1) : Int))
    (hS : ({ st with ptr } : SSt).setRep i (fun r => { r with count := c }) = S) :
    exec (e.withFast false) (F + 1) pc ptr top st =
      untilBack i ptr c (matchAt (e.withFast false) F (pat + 3) top S) := by
  subst hc hpat hS
  rcases hop with hop | hop <;>
    simp only [exec, Env.withFast_c, hop, hrep, hlt, zwSkip_slow, ↓reduceIte] <;> op_simp <;> rfl

/-- Below `min`, with `lin` taking every level from `UNTIL` back to `UNTIL` unchanged, the
step-by-step run from count `min - 2 - n` reaches the one at `min - 1`. -/
theorem until_chain (e : Env) (pc ptr : Nat) (top : Bool) (i L : Nat) (Y : SSt) (mn : Int)
    (hop : e.c pc = OP_MAX_UNTIL ∨ e.c pc = OP_MIN_UNTIL) (hrep : Y.repeat_ = some i)
    (hptr : Y.ptr = ptr) (hi : i < Y.reps.size) (hinfo : e.c (Y.reps[i]!.pat + 3) ≠ OP_INFO)
    (hmn : mn = (e.c (Y.reps[i]!.pat + 1) : Int))
    (hlin : ∀ j : Int, ∃ y2, lin e (some pc) L (Y.reps[i]!.pat + 3) ptr top
        (Y.setRep i (fun r => { r with count := j })) = some (.reach ptr y2) ∧
        ({ y2 with ptr } : SSt) = Y.setRep i (fun r => { r with count := j })) :
    ∀ n : Nat, ∀ F v, exec (e.withFast false) F pc ptr top
        (Y.setRep i (fun r => { r with count := mn - 2 - n })) = some v →
      ∃ F' < F, ∃ v', exec (e.withFast false) F' pc ptr top
          (Y.setRep i (fun r => { r with count := mn - 1 })) = some v' ∧
        some v = untilBack i ptr (mn - 1 - n) (some v') := by
  have step : ∀ (k : Int) F v, k + 1 < mn →
      exec (e.withFast false) F pc ptr top (Y.setRep i (fun r => { r with count := k })) = some v →
      ∃ F' < F, ∃ v0, exec (e.withFast false) F' pc ptr top
          (Y.setRep i (fun r => { r with count := k + 1 })) = some v0 ∧
        some v = untilBack i ptr (k + 1) (some v0) := by
    intro k F v hk hx
    cases F with
    | zero => simp only [exec] at hx; cases hx
    | succ F =>
    have hg := setRep_get Y i (fun r => { r with count := k }) hi
    have hS : ({ Y.setRep i (fun r => { r with count := k }) with ptr } : SSt).setRep i
        (fun r => { r with count := k + 1 }) = Y.setRep i (fun r => { r with count := k + 1 }) := by
      have hZ : ({ Y.setRep i (fun r => { r with count := k }) with ptr } : SSt) =
          Y.setRep i (fun r => { r with count := k }) := by
        rw [← hptr]; rfl
      rw [hZ, setRep_setRep]
      rfl
    rw [exec_until_low e F pc ptr top (Y.setRep i (fun r => { r with count := k })) i (k + 1)
      Y.reps[i]!.pat _ hop hrep (by rw [hg])
      (by rw [hg]) (by rw [← hmn]; exact hk) hS] at hx
    cases hm : matchAt (e.withFast false) F (Y.reps[i]!.pat + 3) top
        (Y.setRep i (fun r => { r with count := k + 1 })) with
    | none => rw [hm] at hx; cases hx
    | some v0 =>
      rw [hm] at hx
      cases F with
      | zero => simp only [matchAt] at hm; cases hm
      | succ F1 =>
      rw [matchAt_noinfo _ F1 _ top _ (by simpa using hinfo)] at hm
      rw [show (Y.setRep i (fun r => { r with count := k + 1 })).ptr = ptr from hptr] at hm
      obtain ⟨y2, hl, hy2⟩ := hlin (k + 1)
      obtain ⟨s, F', hs1, hF', hx2⟩ :=
        lin_exec (e.withFast false) _ _ _ _ _ _ _ (by rw [lin_withFast]; exact hl) F1 v0 hm
      cases hs1
      rw [← exec_until_ptr (e.withFast false) pc ptr top y2 ptr (by simpa using hop), hy2] at hx2
      exact ⟨F', by omega, v0, hx2, hx.symm⟩
  intro n
  induction n with
  | zero =>
    intro F v hx
    obtain ⟨F', hF', v0, h1, h2⟩ := step (mn - 2 - ((0 : Nat) : Int)) F v (by omega) hx
    rw [show mn - 2 - ((0 : Nat) : Int) + 1 = mn - 1 by omega] at h1 h2
    exact ⟨F', hF', v0, h1, by rw [h2, show mn - 1 - ((0 : Nat) : Int) = mn - 1 by omega]⟩
  | succ n ih =>
    intro F v hx
    obtain ⟨F', hF', v0, h1, h2⟩ := step (mn - 2 - ((n + 1 : Nat) : Int)) F v (by omega) hx
    rw [show mn - 2 - ((n + 1 : Nat) : Int) + 1 = mn - 2 - (n : Int) by omega] at h1 h2
    obtain ⟨F'', hF'', v', h3, h4⟩ := ih F' v0 h1
    refine ⟨F'', by omega, v', h3, ?_⟩
    rw [h2, h4, untilBack_twice, show mn - 1 - ((n + 1 : Nat) : Int) = mn - 2 - (n : Int) by omega]

/-- What `zwSkip` checked, when it gives a state. -/
theorem zwSkip_spec {e : Env} {pc ptr : Nat} {top : Bool} {i : Nat} {count mn : Int} {pat : Nat}
    {st st2 : SSt} (h : zwSkip e pc ptr top i count mn pat st = some st2) :
    e.fast = true ∧ count + 1 < mn ∧ i < st.reps.size ∧ e.c (pat + 3) ≠ OP_INFO ∧
    ∃ y0 y2, lin e (some pc) (e.code.size + 1) (pat + 3) ptr top st = some (.reach ptr y0) ∧
      ({ y0 with ptr } : SSt).reps = st.reps ∧ ({ y0 with ptr } : SSt).repeat_ = st.repeat_ ∧
      lin e (some pc) (e.code.size + 1) (pat + 3) ptr top
        (({ y0 with ptr } : SSt).setRep i (fun r => { r with count := count + 1 })) = some (.reach ptr y2) ∧
      ({ y2 with ptr } : SSt) = ({ y0 with ptr } : SSt).setRep i (fun r => { r with count := count + 1 }) ∧
      st2 = ({ y0 with ptr } : SSt).setRep i (fun r => { r with count := mn - 1 }) := by
  simp only [zwSkip] at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hc
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
    split at h
    · rename_i p2 y0 hl1
      split at h
      · rename_i hc2
        simp only [Bool.and_eq_true, beq_iff_eq] at hc2
        obtain ⟨⟨hp2, hr1⟩, hr2⟩ := hc2
        subst hp2
        split at h
        · rename_i p3 y2 hl2
          split at h
          · rename_i hc3
            simp only [Bool.and_eq_true, beq_iff_eq] at hc3
            obtain ⟨hp3, hy⟩ := hc3
            subst hp3
            cases h
            exact ⟨h1, h2, h3, h4, y0, y2, hl1, hr1, hr2, hl2, hy, rfl⟩
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

/-- The shortcut against the step-by-step run, at the first `UNTIL` below `min`. -/
theorem until_first (e : Env) (F pc ptr : Nat) (top : Bool) (i : Nat) (X st2 : SSt) (v : Bool × SSt)
    (hop : e.c pc = OP_MAX_UNTIL ∨ e.c pc = OP_MIN_UNTIL) (hrep : X.repeat_ = some i) (hptr : X.ptr = ptr)
    (hz : zwSkip e pc ptr top i (X.reps[i]!.count + 1) (e.c (X.reps[i]!.pat + 1)) X.reps[i]!.pat
      (X.setRep i (fun r => { r with count := X.reps[i]!.count + 1 })) = some st2)
    (h : matchAt (e.withFast false) F (X.reps[i]!.pat + 3) top
      (X.setRep i (fun r => { r with count := X.reps[i]!.count + 1 })) = some v) :
    ∃ F' < F, ∃ v', exec (e.withFast false) F' pc ptr top st2 = some v' ∧
      untilBack i ptr (X.reps[i]!.count + 1) (some v) =
        untilBack i ptr (X.reps[i]!.count + 1) (some v') := by
  obtain ⟨-, hlt, hi, hinfo, y0, y2, hl1, hr1, hr2, hl2, hy2, rfl⟩ := zwSkip_spec hz
  cases F with
  | zero => simp only [matchAt] at h; cases h
  | succ F1 =>
  rw [matchAt_noinfo _ F1 _ top _ (by simpa using hinfo)] at h
  rw [show (X.setRep i (fun r => { r with count := X.reps[i]!.count + 1 })).ptr = ptr from hptr] at h
  obtain ⟨s, F', hs1, hF', hx⟩ :=
    lin_exec (e.withFast false) _ _ _ _ _ _ _ (by rw [lin_withFast]; exact hl1) F1 v h
  cases hs1
  rw [← exec_until_ptr (e.withFast false) pc ptr top y0 ptr (by simpa using hop)] at hx
  have hsz : i < X.reps.size := by simpa [SSt.setRep] using hi
  have hYget : ({ y0 with ptr } : SSt).reps[i]! = { X.reps[i]! with count := X.reps[i]!.count + 1 } := by
    rw [hr1]; exact setRep_get X i _ hsz
  have hYpat : ({ y0 with ptr } : SSt).reps[i]!.pat = X.reps[i]!.pat := by rw [hYget]
  have hYfix : ({ y0 with ptr } : SSt).setRep i (fun r => { r with count := X.reps[i]!.count + 1 }) =
      ({ y0 with ptr } : SSt) := setRep_idem _ X i _ (fun r => rfl) hr1
  have hYsz : i < ({ y0 with ptr } : SSt).reps.size := by rw [hr1]; exact hi
  have hlin : ∀ j : Int, ∃ y3, lin e (some pc) (e.code.size + 1) (({ y0 with ptr } : SSt).reps[i]!.pat + 3) ptr top
      (({ y0 with ptr } : SSt).setRep i (fun r => { r with count := j })) = some (.reach ptr y3) ∧
      ({ y3 with ptr } : SSt) = ({ y0 with ptr } : SSt).setRep i (fun r => { r with count := j }) := by
    intro j
    have h3 := lin_withReps e _ _ _ _ _ _ _ hl2 (({ y0 with ptr } : SSt).setRep i (fun r => { r with count := j })).reps
    refine ⟨{ y2 with reps := (({ y0 with ptr } : SSt).setRep i (fun r => { r with count := j })).reps }, ?_, ?_⟩
    · rw [hYpat]; exact h3
    · have := congrArg (fun s : SSt => { s with reps := (({ y0 with ptr } : SSt).setRep i (fun r => { r with count := j })).reps }) hy2
      exact this
  have hchain := until_chain e pc ptr top i (e.code.size + 1) ({ y0 with ptr } : SSt) (e.c (X.reps[i]!.pat + 1))
    hop (by rw [hr2]; exact hrep) rfl hYsz (by rw [hYpat]; simpa using hinfo) (by rw [hYpat]) hlin
  have hn : (e.c (X.reps[i]!.pat + 1) : Int) - 2 - ((((e.c (X.reps[i]!.pat + 1) : Int) - 2 -
      (X.reps[i]!.count + 1)).toNat : Nat) : Int) = X.reps[i]!.count + 1 := by omega
  have hx' := hx
  rw [← hYfix, ← hn] at hx'
  obtain ⟨F'', hF'', v', h3, h4⟩ := hchain _ F' v hx'
  refine ⟨F'', by omega, v', h3, ?_⟩
  rw [h4, untilBack_twice]

/-- The `count < min` case when the shortcut fires, against the step-by-step run. -/
theorem until_sim_slow (e : Env) (F G pc ptr : Nat) (top : Bool) (i : Nat) (X st2 : SSt) {r : Bool × SSt}
    (hop : e.c pc = OP_MAX_UNTIL ∨ e.c pc = OP_MIN_UNTIL) (hrep : X.repeat_ = some i) (hptr : X.ptr = ptr)
    (hz : zwSkip e pc ptr top i (X.reps[i]!.count + 1) (e.c (X.reps[i]!.pat + 1)) X.reps[i]!.pat
      (X.setRep i (fun r => { r with count := X.reps[i]!.count + 1 })) = some st2)
    (ihE : ∀ F' < F, ∀ pc ptr top st r, exec (e.withFast false) F' pc ptr top st = some r →
      ∀ G, F' ≤ G → exec e G pc ptr top st = some r)
    (hle : F ≤ G)
    (h : untilBack i ptr (X.reps[i]!.count + 1) (matchAt (e.withFast false) F (X.reps[i]!.pat + 3) top
      (X.setRep i (fun r => { r with count := X.reps[i]!.count + 1 }))) = some r) :
    untilBack i ptr (X.reps[i]!.count + 1) (exec e G pc ptr top st2) = some r := by
  cases hm : matchAt (e.withFast false) F (X.reps[i]!.pat + 3) top
      (X.setRep i (fun r => { r with count := X.reps[i]!.count + 1 })) with
  | none => rw [hm] at h; cases h
  | some v =>
    rw [hm] at h
    obtain ⟨F', hF', v', h1, h2⟩ := until_first e F pc ptr top i X st2 v hop hrep hptr hz hm
    rw [ihE F' hF' _ _ _ _ _ h1 G (by omega), ← h2]
    exact h

/-! ### The whole engine -/

/-- Each function of the engine, run with `e.withFast b` and fuel `F`, gives what it gives with
`e` and any fuel `G ≥ F`. -/
def SimAt (e : Env) (b : Bool) (F : Nat) : Prop :=
  (∀ pc top st r, matchAt (e.withFast b) F pc top st = some r →
    ∀ G, F ≤ G → matchAt e G pc top st = some r) ∧
  (∀ pc ptr top st r, exec (e.withFast b) F pc ptr top st = some r →
    ∀ G, F ≤ G → exec e G pc ptr top st = some r) ∧
  (∀ p ptr top i st r, maxTail (e.withFast b) F p ptr top i st = some r →
    ∀ G, F ≤ G → maxTail e G p ptr top i st = some r) ∧
  (∀ p ptr top lm li snap st r, branchLoop (e.withFast b) F p ptr top lm li snap st = some r →
    ∀ G, F ≤ G → branchLoop e G p ptr top lm li snap st = some r) ∧
  (∀ pc mc st r, countFn (e.withFast b) F pc mc st = some r →
    ∀ G, F ≤ G → countFn e G pc mc st = some r) ∧
  (∀ pc lim st r, countLoop (e.withFast b) F pc lim st = some r →
    ∀ G, F ≤ G → countLoop e G pc lim st = some r) ∧
  (∀ next chr mn start ptr top lm li snap st r,
    repOneLit (e.withFast b) F next chr mn start ptr top lm li snap st = some r →
    ∀ G, F ≤ G → repOneLit e G next chr mn start ptr top lm li snap st = some r) ∧
  (∀ next mn start ptr top lm li snap st r,
    repOneGen (e.withFast b) F next mn start ptr top lm li snap st = some r →
    ∀ G, F ≤ G → repOneGen e G next mn start ptr top lm li snap st = some r) ∧
  (∀ p next cnt ptr top lm li snap st r,
    minRepOne (e.withFast b) F p next cnt ptr top lm li snap st = some r →
    ∀ G, F ≤ G → minRepOne e G p next cnt ptr top lm li snap st = some r) ∧
  (∀ p ptr top count prev st r, possMin (e.withFast b) F p ptr top count prev st = some r →
    ∀ G, F ≤ G → possMin e G p ptr top count prev st = some r) ∧
  (∀ p top count ptr prev st r, possMore (e.withFast b) F p top count ptr prev st = some r →
    ∀ G, F ≤ G → possMore e G p top count ptr prev st = some r)

set_option hygiene false in
/-- Close a branch: the same value, `none`, or one recursive call (by the induction hypothesis). -/
macro "sim_leaf" : tactic => `(tactic| first
  | exact h
  | (exfalso; cases h; done)
  | exact iM _ _ _ _ h _ hle
  | exact iE _ _ _ _ _ h _ hle
  | exact iT _ _ _ _ _ _ h _ hle
  | exact iB _ _ _ _ _ _ _ _ h _ hle
  | exact iC _ _ _ _ h _ hle
  | exact iL _ _ _ _ h _ hle
  | exact iRL _ _ _ _ _ _ _ _ _ _ _ h _ hle
  | exact iRG _ _ _ _ _ _ _ _ _ _ h _ hle
  | exact iMR _ _ _ _ _ _ _ _ _ _ h _ hle
  | exact iPM _ _ _ _ _ _ _ h _ hle
  | exact iPX _ _ _ _ _ _ _ h _ hle
  | exact untilBack_mono (fun _ hv => iE _ _ _ _ _ hv _ hle) h
  | exact untilBack_mono (fun _ hv => iM _ _ _ _ hv _ hle) h)

set_option hygiene false in
/-- Split the `match` at the head of `h`, and take the same case in the goal. -/
macro "sim_split" : tactic => `(tactic| (split at h <;> rename_i hq <;> first
  | (exfalso; cases h; done)
  | (rw [if_pos hq])
  | (rw [if_neg hq])
  | (rw [hq]; try dsimp only)
  | (rw [iM _ _ _ _ hq _ hle]; try dsimp only)
  | (rw [iE _ _ _ _ _ hq _ hle]; try dsimp only)
  | (rw [iC _ _ _ _ hq _ hle]; try dsimp only)
  | (rw [iL _ _ _ _ hq _ hle]; try dsimp only)
  -- `split` already took the case in the goal: the same discriminant
  | skip))

set_option hygiene false in
macro "sim_auto" : tactic => `(tactic| repeat' (first
  | sim_leaf
  | (apply ite_sim h <;> intro hc h)
  | sim_split))

set_option hygiene false in
macro "unf_h" : tactic => `(tactic| try simp only [Env.withFast_c, Env.withFast_ch, Env.withFast_endp,
  Env.withFast_matchAll, Env.withFast_charset, Env.withFast_charset', Env.withFast_charsetLoc,
  Env.withFast_countSimple, Env.withFast_countEnd, Env.withFast_refMatch, sreAt_withFast,
  Env.withFast_code, Env.withFast_s, Env.withFast_self, Env.withFast_mfuel, zwSkip_slow] at h)

set_option hygiene false in
macro "op_simp_h" : tactic => `(tactic| simp only [OP_FAILURE, OP_SUCCESS, OP_ANY, OP_ANY_ALL,
  OP_ASSERT, OP_ASSERT_NOT, OP_AT, OP_BRANCH, OP_CATEGORY, OP_CHARSET, OP_BIGCHARSET, OP_GROUPREF,
  OP_GROUPREF_EXISTS, OP_IN, OP_INFO, OP_JUMP, OP_LITERAL, OP_MARK, OP_MAX_UNTIL, OP_MIN_UNTIL,
  OP_NOT_LITERAL, OP_NEGATE, OP_RANGE, OP_REPEAT, OP_REPEAT_ONE, OP_MIN_REPEAT_ONE,
  OP_ATOMIC_GROUP, OP_POSSESSIVE_REPEAT, OP_POSSESSIVE_REPEAT_ONE, OP_GROUPREF_IGNORE,
  OP_IN_IGNORE, OP_LITERAL_IGNORE, OP_NOT_LITERAL_IGNORE, OP_GROUPREF_LOC_IGNORE, OP_IN_LOC_IGNORE,
  OP_LITERAL_LOC_IGNORE, OP_NOT_LITERAL_LOC_IGNORE, OP_GROUPREF_UNI_IGNORE, OP_IN_UNI_IGNORE,
  OP_LITERAL_UNI_IGNORE, OP_NOT_LITERAL_UNI_IGNORE, OP_RANGE_UNI_IGNORE, Bool.false_eq_true,
  ↓reduceIte, beq_self_eq_true, Bool.or_false, Bool.false_or, Bool.true_or, Bool.or_true,
  Bool.and_true, Bool.true_and, Nat.reduceBEq] at h ⊢)

set_option hygiene false in
/-- One op of `exec`: both runs take its branch. -/
macro "op_case" hn:ident op:term : tactic => `(tactic| (
  by_cases $hn:ident : e.c pc = $op
  case pos =>
    simp only [exec, $hn:ident] at h ⊢
    unf_h
    simp only [$hn:ident] at h
    op_simp_h
    sim_auto))

set_option maxHeartbeats 20000000 in
theorem simAt (e : Env) (b : Bool) (hb : b = false ∨ b = e.fast) : ∀ F, SimAt e b F := by
  intro F
  induction F using Nat.strongRecOn with
  | ind F ih =>
  cases F with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;>
      simp_all [matchAt, exec, maxTail, branchLoop, countFn, countLoop, repOneLit, repOneGen,
        minRepOne, possMin, possMore]
  | succ F =>
  have ihE : ∀ F' < F, ∀ pc ptr top st r, exec (e.withFast b) F' pc ptr top st = some r →
      ∀ G, F' ≤ G → exec e G pc ptr top st = some r := fun F' hF' => (ih F' (by omega)).2.1
  obtain ⟨iM, iE, iT, iB, iC, iL, iRL, iRG, iMR, iPM, iPX⟩ := ih F (Nat.lt_succ_self F)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro pc top st r h G hG
    obtain ⟨G, rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hle : F ≤ G := by omega
    simp only [matchAt] at h ⊢
    unf_h
    sim_auto
  · intro pc ptr top st r h G hG
    obtain ⟨G, rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hle : F ≤ G := by omega
    op_case h01 OP_MARK
    op_case h02 OP_LITERAL
    op_case h03 OP_NOT_LITERAL
    op_case h04 OP_SUCCESS
    op_case h05 OP_AT
    op_case h06 OP_CATEGORY
    op_case h07 OP_ANY
    op_case h08 OP_ANY_ALL
    op_case h09 OP_IN
    op_case h10 OP_LITERAL_IGNORE
    op_case h11 OP_LITERAL_UNI_IGNORE
    op_case h12 OP_LITERAL_LOC_IGNORE
    op_case h13 OP_NOT_LITERAL_IGNORE
    op_case h14 OP_NOT_LITERAL_UNI_IGNORE
    op_case h15 OP_NOT_LITERAL_LOC_IGNORE
    op_case h16 OP_IN_IGNORE
    op_case h17 OP_IN_UNI_IGNORE
    op_case h18 OP_IN_LOC_IGNORE
    op_case h19 OP_JUMP
    op_case h20 OP_INFO
    op_case h21 OP_BRANCH
    op_case h22 OP_REPEAT_ONE
    by_cases h23 : e.c pc = OP_MIN_REPEAT_ONE
    case pos =>
      simp only [exec, h23] at h ⊢
      unf_h
      simp only [h23] at h
      op_simp_h
      apply ite_sim h <;> intro hc h
      · sim_auto
      · -- `counted` is an `if` inside a `match`: take its case on both sides first
        by_cases hz : (e.c (pc + 1 + 1) == 0) = true
        · simp only [hz, ↓reduceIte] at h ⊢
          sim_auto
        · simp only [hz, Bool.false_eq_true, ↓reduceIte] at h ⊢
          sim_auto
    op_case h24 OP_POSSESSIVE_REPEAT_ONE
    op_case h25 OP_REPEAT
    op_case h28 OP_POSSESSIVE_REPEAT
    op_case h29 OP_ATOMIC_GROUP
    op_case h30 OP_GROUPREF
    op_case h31 OP_GROUPREF_IGNORE
    op_case h32 OP_GROUPREF_UNI_IGNORE
    op_case h33 OP_GROUPREF_LOC_IGNORE
    op_case h34 OP_GROUPREF_EXISTS
    op_case h35 OP_ASSERT
    op_case h36 OP_ASSERT_NOT
    op_case h37 OP_FAILURE
    by_cases hu : e.c pc = OP_MAX_UNTIL ∨ e.c pc = OP_MIN_UNTIL
    case pos =>
      have hu' := hu
      rcases hu with hu | hu <;>
      · simp only [exec, hu] at h ⊢
        unf_h
        simp only [hu] at h
        op_simp_h
        split at h
        · exfalso; cases h
        rename_i i hrep
        apply ite_sim h <;> intro hc h
        · rcases hb with rfl | rfl
          · split
            · rename_i st2 hz
              exact until_sim_slow e F G pc ptr top i { st with ptr } st2 hu' hrep rfl hz ihE hle h
            · sim_leaf
          · simp only [Env.withFast_self] at h
            sim_auto
        · sim_auto
    -- no op: `exec` is `none`
    simp only [exec, beq_iff_eq, Bool.or_eq_true, h01, h02, h03, h04, h05, h06, h07, h08, h09, h10,
      h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h28, h29, h30, h31,
      h32, h33, h34, h35, h36, h37, Env.withFast_c, hu, or_self, or_false, false_or, ↓reduceIte] at h
    cases h
  all_goals
    intros
    rename_i h G hG
    obtain ⟨G, rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
    have hle : F ≤ G := by omega
  · simp only [maxTail] at h ⊢; unf_h; sim_auto
  · simp only [branchLoop] at h ⊢; unf_h; sim_auto
  · simp only [countFn] at h ⊢; unf_h; sim_auto
  · simp only [countLoop] at h ⊢; unf_h; sim_auto
  · simp only [repOneLit] at h ⊢; unf_h; sim_auto
  · simp only [repOneGen] at h ⊢; unf_h; sim_auto
  · simp only [minRepOne] at h ⊢; unf_h; sim_auto
  · simp only [possMin] at h ⊢; unf_h; sim_auto
  · simp only [possMore] at h ⊢; unf_h; sim_auto

/-! ### What this means for `SRE(match)` and `SRE(search)` -/

/-- Completeness: whatever the step-by-step engine gives with fuel `F`, the engine with the
shortcut gives with the same fuel. -/
theorem fast_complete (e : Env) {F pc : Nat} {top : Bool} {st : SSt} {r : Bool × SSt}
    (h : matchAt (e.withFast false) F pc top st = some r) : matchAt e F pc top st = some r :=
  (simAt e false (.inl rfl) F).1 pc top st r h F (Nat.le_refl F)

/-- More fuel never changes a result. -/
theorem fast_mono (e : Env) {F G pc : Nat} {top : Bool} {st : SSt} {r : Bool × SSt} (hFG : F ≤ G)
    (h : matchAt e F pc top st = some r) : matchAt e G pc top st = some r :=
  (simAt e e.fast (.inr rfl) F).1 pc top st r (by rwa [Env.withFast_self]) G hFG

/-- Soundness: when the engine with the shortcut finishes, and the step-by-step engine finishes
with any fuel at all, they agree. So a result the shortcut finds is the one the C finds by
looping. -/
theorem fast_sound (e : Env) {F F' pc : Nat} {top : Bool} {st : SSt} {r r' : Bool × SSt}
    (h1 : matchAt (e.withFast false) F pc top st = some r) (h2 : matchAt e F' pc top st = some r') :
    r = r' := by
  have a := fast_mono e (Nat.le_max_left F F') (fast_complete e h1)
  have b := fast_mono e (Nat.le_max_right F F') h2
  rw [a] at b
  exact Option.some.inj b

set_option hygiene false in
macro "srch_auto" : tactic => `(tactic| repeat' (first
  | exact h
  | (exfalso; cases h; done)
  | exact ihA _ _ _ h
  | exact ihB _ _ _ _ h
  | exact fast_complete e h
  | (apply ite_sim h <;> intro hc h)
  | (split at h <;> rename_i hq <;> first
      | (exfalso; cases h; done)
      | (rw [fast_complete e hq]; try dsimp only)
      | skip)))

theorem searchLit_fast (e : Env) (code c skip fl : Nat) : ∀ fuel ptr st r,
    searchLit (e.withFast false) code c skip fl fuel ptr st = some r →
    searchLit e code c skip fl fuel ptr st = some r := by
  intro fuel
  induction fuel with
  | zero => intro ptr st r h; simp only [searchLit] at h; cases h
  | succ n ihA =>
    intro ptr st r h
    simp only [searchLit] at h ⊢
    unf_h
    srch_auto

theorem searchOuter_fast (e : Env) (code plen skip fl pfx : Nat) : ∀ fuel,
    (∀ ptr st r, searchOuter (e.withFast false) code plen skip fl pfx fuel ptr st = some r →
      searchOuter e code plen skip fl pfx fuel ptr st = some r) ∧
    (∀ ptr i st r, searchInner (e.withFast false) code plen skip fl pfx fuel ptr i st = some r →
      searchInner e code plen skip fl pfx fuel ptr i st = some r) := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨fun _ _ _ h => ?_, fun _ _ _ _ h => ?_⟩
    · simp only [searchOuter] at h; cases h
    · simp only [searchInner] at h; cases h
  | succ n ih =>
    obtain ⟨ihA, ihB⟩ := ih
    refine ⟨fun ptr st r h => ?_, fun ptr i st r h => ?_⟩
    · simp only [searchOuter] at h ⊢
      unf_h
      srch_auto
    · simp only [searchInner] at h ⊢
      unf_h
      srch_auto

theorem searchSet_fast (e : Env) (code set : Nat) : ∀ fuel ptr st r,
    searchSet (e.withFast false) code set fuel ptr st = some r → searchSet e code set fuel ptr st = some r := by
  intro fuel
  induction fuel with
  | zero => intro ptr st r h; simp only [searchSet] at h; cases h
  | succ n ihA =>
    intro ptr st r h
    simp only [searchSet] at h ⊢
    unf_h
    srch_auto

theorem searchGen_fast (e : Env) (code lim : Nat) : ∀ fuel ptr st r,
    searchGen (e.withFast false) code lim fuel ptr st = some r → searchGen e code lim fuel ptr st = some r := by
  intro fuel
  induction fuel with
  | zero => intro ptr st r h; simp only [searchGen] at h; cases h
  | succ n ihA =>
    intro ptr st r h
    simp only [searchGen] at h ⊢
    unf_h
    srch_auto

set_option maxHeartbeats 4000000 in
/-- Every search the step-by-step engine finishes ends the same with the shortcut: no result of
the model changes. -/
theorem sreSearch_fast (e : Env) (st : SSt) (r : Bool × SSt)
    (h : sreSearch (e.withFast false) st = some r) : sreSearch e st = some r := by
  simp only [sreSearch] at h ⊢
  unf_h
  apply ite_sim h <;> intro hc h
  · exact h
  apply ite_sim h <;> intro hc h
  · exact h
  apply ite_sim h <;> intro hc h
  · apply ite_sim h <;> intro hc h
    · exact searchLit_fast e _ _ _ _ _ _ _ _ h
    · apply ite_sim h <;> intro hc h
      · exact h
      · exact (searchOuter_fast e _ _ _ _ _ _).1 _ _ _ h
  · apply ite_sim h <;> intro hc h
    · exact searchSet_fast e _ _ _ _ _ _ h
    · split at h
      · cases h
      · rename_i hq
        erw [fast_complete e hq]
        exact h
      · rename_i hq
        erw [fast_complete e hq]; dsimp only
        apply ite_sim h <;> intro hc h
        · exact h
        · exact searchGen_fast e _ _ _ _ _ _ h

end PyLean.TextLibs.Re
