import PyLean.UnicodeObj.ObjectUtf8
import PyLean.UnicodeObj.ObjectWriterProps
import PyLean.UnicodeObj.CodecCallbackProps

/-!
Properties of the UTF-8 decoder with any error handler.
-/

namespace PyLean.UnicodeObj

open PyLean

theorem isCont_ge {x : Nat} (h : (!isCont x) = false) : 128 ≤ x := by
  simp only [isCont, Bool.not_eq_false', Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem step2_err {a b k : Nat} (h : step2 a b = .err k) : k = 2 := by
  unfold step2 at h
  split at h
  · cases h
    rfl
  · cases h

theorem step3_err {a b c k : Nat} (h : step3 a b c = .err k) : k = 2 ∨ (k = 3 ∧ 128 ≤ b) := by
  unfold step3 at h
  split at h
  · cases h
    exact .inl rfl
  · next h1 =>
    split at h
    · cases h
      exact .inl rfl
    · split at h
      · cases h
        exact .inl rfl
      · split at h
        · cases h
          exact .inr ⟨rfl, isCont_ge (by simpa using h1)⟩
        · cases h

theorem step4_err {a b c d k : Nat} (h : step4 a b c d = .err k) :
    k = 2 ∨ (k = 3 ∧ 128 ≤ b) ∨ (k = 4 ∧ 128 ≤ b ∧ 128 ≤ c) := by
  unfold step4 at h
  split at h
  · cases h
    exact .inl rfl
  · next h1 =>
    split at h
    · cases h
      exact .inl rfl
    · split at h
      · cases h
        exact .inl rfl
      · split at h
        · cases h
          exact .inr (.inl ⟨rfl, isCont_ge (by simpa using h1)⟩)
        · next h2 =>
          split at h
          · cases h
            exact .inr (.inr ⟨rfl, isCont_ge (by simpa using h1), isCont_ge (by simpa using h2)⟩)
          · cases h

theorem step2_stop {a b : Nat} (h : step2 a b = .stop) : False := by
  unfold step2 at h
  split at h <;> cases h

theorem step3_stop {a b c : Nat} (h : step3 a b c = .stop) : False := by
  unfold step3 at h
  repeat' split at h
  all_goals cases h

theorem step4_stop {a b c d : Nat} (h : step4 a b c d = .stop) : False := by
  unfold step4 at h
  repeat' split at h
  all_goals cases h

theorem ite_err2 {p : Prop} [Decidable p] {k : Nat}
    (h : (if p then U8.err 2 else U8.stop) = .err k) : k = 2 := by
  by_cases q : p
  · rw [if_pos q] at h
    cases h
    rfl
  · rw [if_neg q] at h
    cases h

theorem ite_stop2 {p : Prop} [Decidable p] (h : (if p then U8.err 2 else U8.stop) = .stop) : ¬p := by
  intro q
  rw [if_pos q] at h
  cases h

theorem ite3_err {p q : Prop} [Decidable p] [Decidable q] {k : Nat}
    (h : (if p then U8.err 2 else if q then U8.err 3 else U8.stop) = .err k) :
    k = 2 ∨ (k = 3 ∧ ¬p) := by
  by_cases a : p
  · rw [if_pos a] at h
    cases h
    exact .inl rfl
  · rw [if_neg a] at h
    by_cases b : q
    · rw [if_pos b] at h
      cases h
      exact .inr ⟨rfl, a⟩
    · rw [if_neg b] at h
      cases h

theorem ite3_stop {p q : Prop} [Decidable p] [Decidable q]
    (h : (if p then U8.err 2 else if q then U8.err 3 else U8.stop) = .stop) : ¬p ∧ ¬q := by
  by_cases a : p
  · rw [if_pos a] at h
    cases h
  · rw [if_neg a] at h
    by_cases b : q
    · rw [if_pos b] at h
      cases h
    · exact ⟨a, b⟩

/-- Not a continuation byte, or the test on it, is what `(!isCont c || x)` being false says. -/
theorem cont_of_not {c : Nat} {x : Bool} (h : ¬((!isCont c || x) = true)) : 128 ≤ c := by
  apply isCont_ge
  cases e : !isCont c with
  | false => rfl
  | true => simp [e] at h

/-- What an error of `utf8Step` covers: `invalid start byte` one byte, and an invalid continuation
`k - 1` bytes, every one of them not ASCII. -/
theorem step_err {b : Nat} {t : List Nat} {k : Nat} (h : utf8Step (b :: t) = .err k) :
    128 ≤ b ∧ (k = 1 ∨ k = 2 ∨ (k = 3 ∧ ∃ b2 r, t = b2 :: r ∧ 128 ≤ b2) ∨
      (k = 4 ∧ ∃ b2 b3 r, t = b2 :: b3 :: r ∧ 128 ≤ b2 ∧ 128 ≤ b3)) := by
  simp only [utf8Step] at h
  by_cases h1 : b < 128
  · rw [if_pos h1] at h
    cases h
  rw [if_neg h1] at h
  refine ⟨by omega, ?_⟩
  by_cases h2 : b < 224
  · rw [if_pos h2] at h
    by_cases h3 : b < 194
    · rw [if_pos h3] at h
      cases h
      exact .inl rfl
    · rw [if_neg h3] at h
      cases t with
      | nil => cases h
      | cons c r => exact .inr (.inl (step2_err h))
  rw [if_neg h2] at h
  by_cases h3 : b < 240
  · rw [if_pos h3] at h
    cases t with
    | nil => cases h
    | cons c r =>
      cases r with
      | nil => exact .inr (.inl (ite_err2 h))
      | cons d u =>
        rcases step3_err h with e | ⟨e, h4⟩
        · exact .inr (.inl e)
        · exact .inr (.inr (.inl ⟨e, c, d :: u, rfl, h4⟩))
  rw [if_neg h3] at h
  by_cases h4 : b < 245
  · rw [if_pos h4] at h
    cases t with
    | nil => cases h
    | cons c r =>
      cases r with
      | nil => exact .inr (.inl (ite_err2 h))
      | cons d u =>
        cases u with
        | nil =>
          dsimp only at h
          rcases ite3_err h with x | ⟨x, hq⟩
          · exact .inr (.inl x)
          · exact .inr (.inr (.inl ⟨x, c, [d], rfl, cont_of_not hq⟩))
        | cons e v =>
          rcases step4_err h with x | ⟨x, h5⟩ | ⟨x, h5, h6⟩
          · exact .inr (.inl x)
          · exact .inr (.inr (.inl ⟨x, c, d :: e :: v, rfl, h5⟩))
          · exact .inr (.inr (.inr ⟨x, c, d, e :: v, rfl, h5, h6⟩))
  · rw [if_neg h4] at h
    cases h
    exact .inl rfl

/-- The input ends inside a character: at most three bytes, none of them ASCII. -/
theorem step_stop {b : Nat} {t : List Nat} (h : utf8Step (b :: t) = .stop) :
    128 ≤ b ∧ t.length ≤ 2 ∧ ∀ x ∈ t, 128 ≤ x := by
  simp only [utf8Step] at h
  by_cases h1 : b < 128
  · rw [if_pos h1] at h
    cases h
  rw [if_neg h1] at h
  refine ⟨by omega, ?_⟩
  by_cases h2 : b < 224
  · rw [if_pos h2] at h
    by_cases h3 : b < 194
    · rw [if_pos h3] at h
      cases h
    · rw [if_neg h3] at h
      cases t with
      | nil => simp
      | cons c r => exact (step2_stop h).elim
  rw [if_neg h2] at h
  by_cases h3 : b < 240
  · rw [if_pos h3] at h
    cases t with
    | nil => simp
    | cons c r =>
      cases r with
      | nil =>
        have := cont_of_not (ite_stop2 h)
        simp [this]
      | cons d u => exact (step3_stop h).elim
  rw [if_neg h3] at h
  by_cases h4 : b < 245
  · rw [if_pos h4] at h
    cases t with
    | nil => simp
    | cons c r =>
      cases r with
      | nil =>
        have := cont_of_not (ite_stop2 h)
        simp [this]
      | cons d u =>
        cases u with
        | nil =>
          dsimp only at h
          obtain ⟨hq, hr⟩ := ite3_stop h
          have a := cont_of_not hq
          have e := isCont_ge (x := d) (by simpa using hr)
          simp [a, e]
        | cons e v => exact (step4_stop h).elim
  · rw [if_neg h4] at h
    cases h

theorem escape_all : ∀ (n : Nat) (l : List Nat), (∀ x ∈ l, 128 ≤ x) → l.length ≤ n →
    escapeRun n l = l := by
  intro n
  induction n with
  | zero =>
    intro l _ h
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [this]
    rfl
  | succ n ih =>
    intro l hl h
    cases l with
    | nil => rfl
    | cons x t =>
      have hx := hl x List.mem_cons_self
      simp only [escapeRun]
      rw [if_neg (by omega), ih t (fun y hy => hl y (List.mem_cons_of_mem _ hy)) (by simpa using h)]

theorem code_utf8 : codeOf "utf-8" = .utf8 := by decide

/-- One call of a standard handler through the Python path, as the callback sees it. -/
theorem mimic_step (h : ErrHandler) (input : Bytes) (hs : (input.length : Int) ≤ ssizeMax)
    (hist : List DecView) (reason : String) (pos stop : Nat) (hstop : stop ≤ input.length) :
    handlerStep (.custom (mimicDec h)) "utf-8" .utf8 reason input hist pos stop =
      match decodeHandlerCall h "utf-8" .utf8 input pos stop reason with
      | .error e => .error e
      | .ok (rep, np) =>
        .ok (hist ++ [{ object := input, encoding := "utf-8", start := pos, stop, reason }],
          input, rep, np) := by
  simp only [handlerStep]
  have hl : (hist ++ [({ object := input, encoding := "utf-8", start := pos, stop, reason } : DecView)]).getLast? =
      some { object := input, encoding := "utf-8", start := pos, stop, reason } := by
    simp
  cases hd : decodeHandlerCall h "utf-8" .utf8 input pos stop reason with
  | error e =>
    simp only [decodeCallback, bind, Except.bind, pure, Except.pure]
    simp [mimicDec, hl, code_utf8, hd]
  | ok r =>
    obtain ⟨rep, np⟩ := r
    apply decodeCallback_ok hs (decodeHandler_bound hstop hd)
    simp [mimicDec, hl, code_utf8, hd]

/-- The bytes an error span covers. -/
theorem span_err {b : Nat} {t : List Nat} {k : Nat} (h : utf8Step (b :: t) = .err k) (hk : k ≠ 1) :
    2 ≤ k ∧ k ≤ 4 ∧ k - 1 ≤ (b :: t).length ∧ ∀ x ∈ (b :: t).take (k - 1), 128 ≤ x := by
  obtain ⟨hb, hc⟩ := step_err h
  rcases hc with rfl | rfl | ⟨rfl, b2, r, rfl, h2⟩ | ⟨rfl, b2, b3, r, rfl, h2, h3⟩
  · exact absurd rfl hk
  · refine ⟨by omega, by omega, by simp, ?_⟩
    intro x hx
    simp at hx
    omega
  · refine ⟨by omega, by omega, by simp, ?_⟩
    intro x hx
    simp at hx
    omega
  · refine ⟨by omega, by omega, by simp, ?_⟩
    intro x hx
    simp at hx
    omega

/-- A failure at `pos`, in the three forms of `onError`, for a span that is all not ASCII. -/
theorem mimic_fail (h : ErrHandler) (input : Bytes) (hs : (input.length : Int) ≤ ssizeMax)
    (consumed : Bool) (fuel : Nat)
    (ih : ∀ (hist1 hist2 : List DecView) (pos : Nat) (rest : List Nat) (out : Str),
      rest = input.drop pos → pos ≤ input.length →
      utf8DecodeLoopX (.custom (mimicDec h)) consumed fuel input hist1 pos rest out =
        utf8DecodeLoopX (.std h) consumed fuel input hist2 pos rest out)
    (hist1 hist2 : List DecView) (pos : Nat) (rest : List Nat) (out : Str) (reason : String)
    (stopAt : Nat) (hr : rest = input.drop pos) (hp : stopAt ≤ input.length) (hn : pos ≤ stopAt)
    (hspan : ∀ x ∈ rest.take (stopAt - pos), 128 ≤ x) (hl : stopAt - pos ≤ 4)
    (hpos : pos < stopAt) :
    (match handlerStep (.custom (mimicDec h)) "utf-8" .utf8 reason input hist1 pos stopAt with
      | .error e => .error e
      | .ok (hist', input', rep, newpos) =>
        utf8DecodeLoopX (.custom (mimicDec h)) consumed fuel input' hist' newpos (input'.drop newpos)
          (out ++ rep)) =
    (match (generalizing := false) (DH.std h) with
      | .std .ignore => utf8DecodeLoopX (.std h) consumed fuel input hist2 stopAt
          (rest.drop (stopAt - pos)) (out ++ [])
      | .std .replace => utf8DecodeLoopX (.std h) consumed fuel input hist2 stopAt
          (rest.drop (stopAt - pos)) (out ++ [0xfffd])
      | .std .surrogateescape => utf8DecodeLoopX (.std h) consumed fuel input hist2 stopAt
          (rest.drop (stopAt - pos)) (out ++ (rest.take (stopAt - pos)).map (· + 0xdc00))
      | _ =>
        match handlerStep (.std h) "utf-8" .utf8 reason input hist2 pos stopAt with
        | .error e => .error e
        | .ok (hist', input', rep, newpos) =>
          utf8DecodeLoopX (.std h) consumed fuel input' hist' newpos (input'.drop newpos)
            (out ++ rep)) := by
  have hdrop : rest.drop (stopAt - pos) = input.drop stopAt := by
    rw [hr, List.drop_drop]
    congr 1
    omega
  rw [mimic_step h input hs hist1 reason pos stopAt hp]
  have key : (match (match decodeHandlerCall h "utf-8" .utf8 input pos stopAt reason with
        | .error e => (.error e : Py (List DecView × Bytes × Str × Nat))
        | .ok (rep, np) =>
          .ok (hist1 ++ [({ object := input, encoding := "utf-8", start := pos, stop := stopAt, reason } : DecView)],
            input, rep, np)) with
      | .error e => (.error e : Py (Str × Nat))
      | .ok (hist', input', rep, newpos) =>
        utf8DecodeLoopX (.custom (mimicDec h)) consumed fuel input' hist' newpos (input'.drop newpos)
          (out ++ rep)) =
      (match handlerStep (.std h) "utf-8" .utf8 reason input hist2 pos stopAt with
        | .error e => (.error e : Py (Str × Nat))
        | .ok (hist', input', rep, newpos) =>
          utf8DecodeLoopX (.std h) consumed fuel input' hist' newpos (input'.drop newpos)
            (out ++ rep)) := by
    simp only [handlerStep]
    cases hd : decodeHandlerCall h "utf-8" .utf8 input pos stopAt reason with
    | error e => rfl
    | ok r =>
      obtain ⟨rep, np⟩ := r
      exact ih _ _ _ _ _ rfl (decodeHandler_bound hp hd)
  cases h
  case ignore =>
    simp only [decodeHandlerCall]
    rw [hdrop]
    exact ih _ _ _ _ _ rfl hp
  case replace =>
    simp only [decodeHandlerCall]
    rw [hdrop]
    exact ih _ _ _ _ _ rfl hp
  case surrogateescape =>
    have hslice : (input.drop pos).take (stopAt - pos) = rest.take (stopAt - pos) := by rw [hr]
    have hlen : (rest.take (stopAt - pos)).length = stopAt - pos := by
      rw [hr]
      simp only [List.length_take, List.length_drop]
      omega
    have hrun := escape_all 4 (rest.take (stopAt - pos)) hspan (by omega)
    have hne : (rest.take (stopAt - pos)).isEmpty = false := by
      cases e : rest.take (stopAt - pos) with
      | nil =>
        rw [e] at hlen
        simp at hlen
        omega
      | cons _ _ => rfl
    simp only [decodeHandlerCall, hslice, hrun, hne, Bool.false_eq_true, if_false]
    have hstop : pos + (rest.take (stopAt - pos)).length = stopAt := by omega
    rw [hstop, hdrop]
    exact ih _ _ _ _ _ rfl hp
  all_goals exact key

theorem step2_char {a b c n : Nat} (h : step2 a b = .char c n) : n = 2 := by
  unfold step2 at h
  split at h
  · cases h
  · exact (U8.char.inj h).2.symm

theorem step3_char {a b c d n : Nat} (h : step3 a b c = .char d n) : n = 3 := by
  unfold step3 at h
  repeat' split at h
  all_goals first | exact (U8.char.inj h).2.symm | (cases h; done)

theorem step4_char {a b c d e n : Nat} (h : step4 a b c d = .char e n) : n = 4 := by
  unfold step4 at h
  repeat' split at h
  all_goals first | exact (U8.char.inj h).2.symm | (cases h; done)

theorem ite_char2 {p : Prop} [Decidable p] {c n : Nat}
    (h : (if p then U8.err 2 else U8.stop) = .char c n) : False := by
  by_cases q : p
  · rw [if_pos q] at h
    cases h
  · rw [if_neg q] at h
    cases h

theorem ite3_char {p q : Prop} [Decidable p] [Decidable q] {c n : Nat}
    (h : (if p then U8.err 2 else if q then U8.err 3 else U8.stop) = .char c n) : False := by
  by_cases a : p
  · rw [if_pos a] at h
    cases h
  · rw [if_neg a] at h
    by_cases b : q
    · rw [if_pos b] at h
      cases h
    · rw [if_neg b] at h
      cases h

/-- A character takes one to four bytes of what is there. -/
theorem step_char_len {r : List Nat} {c n : Nat} (h : utf8Step r = .char c n) :
    1 ≤ n ∧ n ≤ r.length := by
  cases r with
  | nil => cases h
  | cons b t =>
    simp only [utf8Step] at h
    by_cases h1 : b < 128
    · rw [if_pos h1] at h
      cases h
      simp
    rw [if_neg h1] at h
    by_cases h2 : b < 224
    · rw [if_pos h2] at h
      by_cases h3 : b < 194
      · rw [if_pos h3] at h
        cases h
      · rw [if_neg h3] at h
        cases t with
        | nil => cases h
        | cons x r =>
          rw [step2_char h]
          simp
    rw [if_neg h2] at h
    by_cases h3 : b < 240
    · rw [if_pos h3] at h
      cases t with
      | nil => cases h
      | cons x r =>
        cases r with
        | nil => exact (ite_char2 h).elim
        | cons y u =>
          rw [step3_char h]
          simp
    rw [if_neg h3] at h
    by_cases h4 : b < 245
    · rw [if_pos h4] at h
      cases t with
      | nil => cases h
      | cons x r =>
        cases r with
        | nil => exact (ite_char2 h).elim
        | cons y u =>
          cases u with
          | nil => exact (ite3_char h).elim
          | cons z v =>
            rw [step4_char h]
            simp
    · rw [if_neg h4] at h
      cases h

theorem utf8_mimic (h : ErrHandler) (input : Bytes) (hs : (input.length : Int) ≤ ssizeMax)
    (consumed : Bool) : ∀ (fuel : Nat) (hist1 hist2 : List DecView) (pos : Nat) (rest : List Nat)
      (out : Str), rest = input.drop pos → pos ≤ input.length →
      utf8DecodeLoopX (.custom (mimicDec h)) consumed fuel input hist1 pos rest out =
        utf8DecodeLoopX (.std h) consumed fuel input hist2 pos rest out := by
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ fuel ih =>
    intro hist1 hist2 pos rest out hr hp
    have hlen : rest.length = input.length - pos := by rw [hr, List.length_drop]
    cases rest with
    | nil => rfl
    | cons b0 tl =>
      have hl1 : 0 < (b0 :: tl).length := by simp
      simp only [utf8DecodeLoopX]
      cases hst : utf8Step (b0 :: tl) with
      | char c n =>
        obtain ⟨n1, n2⟩ := step_char_len hst
        exact ih _ _ _ _ _ (by rw [hr, List.drop_drop]) (by omega)
      | stop =>
        dsimp only
        split
        · rfl
        · obtain ⟨a, b, d⟩ := step_stop hst
          have ht : (b0 :: tl).take (input.length - pos) = b0 :: tl :=
            List.take_of_length_le (by omega)
          exact mimic_fail h input hs consumed fuel ih _ _ pos _ out _ input.length hr (Nat.le_refl _) hp
            (by
              rw [ht]
              intro x hx
              rcases List.mem_cons.1 hx with rfl | hx
              · exact a
              · exact d x hx)
            (by simp only [List.length_cons] at hlen; omega) (by omega)
      | err k =>
        by_cases hk : k = 1
        · subst hk
          obtain ⟨a, _⟩ := step_err hst
          exact mimic_fail h input hs consumed fuel ih _ _ pos _ out _ (pos + 1) hr (by omega) (by omega)
            (by
              intro x hx
              have e : pos + 1 - pos = 1 := by omega
              rw [e] at hx
              simp at hx
              omega)
            (by omega) (by omega)
        · obtain ⟨k2, k4, k3, k5⟩ := span_err hst hk
          rcases k with _ | _ | j
          · omega
          · omega
          · change ite _ _ _ = ite _ _ _
            split
            · rfl
            · have e : pos + (j + 1 + 1) - 1 - pos = j + 1 + 1 - 1 := by omega
              exact mimic_fail h input hs consumed fuel ih _ _ pos _ out _ (pos + (j + 1 + 1) - 1) hr
                (by omega) (by omega) (by rw [e]; exact k5) (by omega) (by omega)

/-- `ignore`, `replace` and `surrogateescape` are written out inside `unicode_decode_utf8_impl`.
They do what the registered handlers of the same names do through the Python path, for every input
and every handler: same text, same position, same exception. That is a statement about the bytes an
error can cover: `surrogateescape` called through Python stops at an ASCII byte, and the inline
code does not, so they agree because no error span of UTF-8 holds one. -/
def Utf8StdIsCallback : Prop :=
  ∀ (input : Bytes) (h : ErrHandler) (consumed : Bool) (fuel : Nat),
    (input.length : Int) ≤ ssizeMax →
    utf8DecodeX input (.custom (mimicDec h)) consumed fuel = utf8DecodeX input (.std h) consumed fuel

theorem utf8StdIsCallback_proven : Utf8StdIsCallback := by
  intro input h consumed fuel hs
  exact utf8_mimic h input hs consumed fuel [] [] 0 input [] rfl (Nat.zero_le _)

end PyLean.UnicodeObj
