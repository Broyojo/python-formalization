import PyLean.UnicodeObj.ObjectUtf8Props
import PyLean.UnicodeObj.ObjectChunksCodecs

/-!
The chunk property for UTF-8.

`utf8DecodeLoop` is not a `decodeDriver`: it has the handlers of `unicode_decode_utf8_impl` inline.
`utf8_driver` shows it is one anyway, with `stepU8`, and the engine does the rest.

UTF-8 is the one decoder where `handler_loc` is not enough. `surrogatepass` reads three bytes from
the start of the error, and an error can sit in fewer than that at the end of a chunk. So what
happens at a short end has to be worked out, and it is why the decoder has its odd case for
`ED A0..BF` at the end of the input with `consumed`, unicodeobject.c:5227-5234: those two bytes are
an error by themselves, but with a third they are a surrogate to `surrogatepass`.
-/

namespace PyLean.UnicodeObj

open PyLean

/-- One round of `unicode_decode_utf8_impl` as a step of `decodeDriver`. -/
def stepU8 (consumed : Bool) : List Nat → DStep
  | [] => .stop
  | b0 :: tl =>
    match utf8Step (b0 :: tl) with
    | .char c n => .char c n
    | .stop => if consumed then .stop else .fail "unexpected end of data" 0 (b0 :: tl).length
    | .err 1 => .fail "invalid start byte" 0 1
    | .err code =>
      if code == 2 && consumed && b0 == 0xED && (b0 :: tl).length == 2 &&
          decide (0xA0 ≤ tl.headD 0) && decide (tl.headD 0 ≤ 0xBF) then .stop
      else .fail "invalid continuation byte" 0 (code - 1)

/-- The inline handlers are the handlers, on a span that is not ASCII. -/
theorem u8_fail (h : ErrHandler) (input : Bytes) (consumed : Bool) (fuel : Nat)
    (ih : ∀ (pos : Nat) (rest : List Nat) (out : Str), rest = input.drop pos → pos ≤ input.length →
      utf8DecodeLoop input h consumed fuel pos rest out =
        decodeDriver (stepU8 consumed) h "utf-8" .utf8 input fuel pos rest out)
    (pos : Nat) (rest : List Nat) (out : Str) (reason : String) (stopAt : Nat)
    (hr : rest = input.drop pos) (hp : stopAt ≤ input.length) (hn : pos < stopAt)
    (hspan : ∀ x ∈ rest.take (stopAt - pos), 128 ≤ x) (hl : stopAt - pos ≤ 4) :
    (match (generalizing := false) h with
      | .ignore => utf8DecodeLoop input h consumed fuel stopAt (rest.drop (stopAt - pos)) (out ++ [])
      | .replace => utf8DecodeLoop input h consumed fuel stopAt (rest.drop (stopAt - pos)) (out ++ [0xfffd])
      | .surrogateescape => utf8DecodeLoop input h consumed fuel stopAt (rest.drop (stopAt - pos))
          (out ++ (rest.take (stopAt - pos)).map (· + 0xdc00))
      | _ =>
        match decodeHandlerCall h "utf-8" .utf8 input pos stopAt reason with
        | .error e => .error e
        | .ok (rep, newpos) =>
          utf8DecodeLoop input h consumed fuel newpos (input.drop newpos) (out ++ rep)) =
    (match decodeHandlerCall h "utf-8" .utf8 input pos stopAt reason with
      | .error x => .error x
      | .ok (rep, newpos) =>
        decodeDriver (stepU8 consumed) h "utf-8" .utf8 input fuel newpos (input.drop newpos) (out ++ rep)) := by
  have hdrop : rest.drop (stopAt - pos) = input.drop stopAt := by
    rw [hr, List.drop_drop]
    congr 1
    omega
  have key : (match decodeHandlerCall h "utf-8" .utf8 input pos stopAt reason with
      | .error e => (.error e : Py (Str × Nat))
      | .ok (rep, newpos) =>
        utf8DecodeLoop input h consumed fuel newpos (input.drop newpos) (out ++ rep)) =
      (match decodeHandlerCall h "utf-8" .utf8 input pos stopAt reason with
        | .error x => (.error x : Py (Str × Nat))
        | .ok (rep, newpos) =>
          decodeDriver (stepU8 consumed) h "utf-8" .utf8 input fuel newpos (input.drop newpos)
            (out ++ rep)) := by
    cases hd : decodeHandlerCall h "utf-8" .utf8 input pos stopAt reason with
    | error e => rfl
    | ok r =>
      obtain ⟨rep, np⟩ := r
      exact ih _ _ _ rfl (decodeHandler_bound hp hd)
  cases h
  case ignore =>
    simp only [decodeHandlerCall]
    rw [hdrop]
    exact ih _ _ _ rfl hp
  case replace =>
    simp only [decodeHandlerCall]
    rw [hdrop]
    exact ih _ _ _ rfl hp
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
    exact ih _ _ _ rfl hp
  all_goals exact key

theorem utf8_driver (input : Bytes) (h : ErrHandler) (consumed : Bool) :
    ∀ (fuel pos : Nat) (rest : List Nat) (out : Str), rest = input.drop pos → pos ≤ input.length →
      utf8DecodeLoop input h consumed fuel pos rest out =
        decodeDriver (stepU8 consumed) h "utf-8" .utf8 input fuel pos rest out := by
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ fuel ih =>
    intro pos rest out hr hp
    have hlen : rest.length = input.length - pos := by rw [hr, List.length_drop]
    cases rest with
    | nil => rfl
    | cons b0 tl =>
      have hl1 : 0 < (b0 :: tl).length := by simp
      simp only [utf8DecodeLoop, decodeDriver, stepU8]
      cases hst : utf8Step (b0 :: tl) with
      | char c n =>
        obtain ⟨n1, n2⟩ := step_char_len hst
        exact ih _ _ _ (by rw [hr, List.drop_drop]) (by omega)
      | stop =>
        dsimp only
        cases consumed
        · simp only [Bool.false_eq_true, if_false, Nat.add_zero]
          obtain ⟨a, b, d⟩ := step_stop hst
          have ht : (b0 :: tl).take (input.length - pos) = b0 :: tl :=
            List.take_of_length_le (by omega)
          have e : pos + (b0 :: tl).length = input.length := by omega
          rw [e]
          exact u8_fail h input false fuel ih pos _ out _ input.length hr (Nat.le_refl _) (by omega)
            (by
              rw [ht]
              intro x hx
              rcases List.mem_cons.1 hx with rfl | hx
              · exact a
              · exact d x hx)
            (by simp only [List.length_cons] at hlen; omega)
        · rfl
      | err k =>
        by_cases hk : k = 1
        · subst hk
          obtain ⟨a, _⟩ := step_err hst
          simp only [Nat.add_zero]
          exact u8_fail h input consumed fuel ih pos _ out _ (pos + 1) hr (by omega) (by omega)
            (by
              intro x hx
              have e : pos + 1 - pos = 1 := by omega
              rw [e] at hx
              simp at hx
              omega)
            (by omega)
        · obtain ⟨k2, k4, k3, k5⟩ := span_err hst hk
          rcases k with _ | _ | j
          · omega
          · omega
          · change ite _ _ _ = (match ite _ DStep.stop _ with
              | .char c n => _
              | .multi w n => _
              | .stop => _
              | .raise e => _
              | .fail r s e => _)
            by_cases hc : (j + 1 + 1 == 2 && consumed && b0 == 0xED && (b0 :: tl).length == 2 &&
                decide (0xA0 ≤ tl.headD 0) && decide (tl.headD 0 ≤ 0xBF)) = true
            · rw [if_pos hc, if_pos hc]
            · rw [if_neg hc, if_neg hc]
              have e : pos + (j + 1 + 1) - 1 - pos = j + 1 + 1 - 1 := by omega
              have e2 : pos + (j + 1 + 1 - 1) = pos + (j + 1 + 1) - 1 := by omega
              simp only [Nat.add_zero]
              rw [e2]
              exact u8_fail h input consumed fuel ih pos _ out _ (pos + (j + 1 + 1) - 1) hr
                (by omega) (by omega) (by rw [e]; exact k5) (by omega)

theorem u8_moves (c : Bool) : Moves (stepU8 c) := by
  refine ⟨rfl, ?_⟩
  intro r
  cases r with
  | nil => trivial
  | cons b tl =>
    simp only [stepU8]
    cases hst : utf8Step (b :: tl) with
    | char x n =>
      have := step_char_len hst
      show 0 < n
      omega
    | stop => exact okStep_ite trivial (show 0 < (b :: tl).length by simp)
    | err k =>
      by_cases hk : k = 1
      · subst hk
        show 0 < 1
        omega
      · obtain ⟨k2, _, _, _⟩ := span_err hst hk
        rcases k with _ | _ | j
        · omega
        · omega
        · exact okStep_ite trivial (show 0 < j + 1 + 1 - 1 by omega)

theorem step3_short {ch x y : Nat}
    (h : (!isCont x || (if x < 0xA0 then ch == 0xE0 else ch == 0xED)) = true) :
    step3 ch x y = .err 2 := by
  unfold step3
  by_cases h1 : (!isCont x) = true
  · rw [if_pos h1]
  rw [if_neg h1]
  have h2 : (if x < 0xA0 then ch == 0xE0 else ch == 0xED) = true := by
    simpa [h1] using h
  by_cases h3 : x < 0xA0
  · rw [if_pos h3] at h2
    have : (ch == 0xE0 && decide (x < 0xA0)) = true := by simp [h2, h3]
    rw [if_pos this]
  · rw [if_neg h3] at h2
    have e : ch = 0xED := by simpa using h2
    subst e
    have n1 : ¬((237 == 0xE0 && decide (x < 0xA0)) = true) := by simp
    have n2 : ((237 != 0xE0 && 237 == 0xED && decide (x ≥ 0xA0)) = true) := by
      simp
      omega
    rw [if_neg n1, if_pos n2]

theorem step4_short {ch x y z : Nat}
    (h : (!isCont x || (if x < 0x90 then ch == 0xF0 else ch == 0xF4)) = true) :
    step4 ch x y z = .err 2 := by
  unfold step4
  by_cases h1 : (!isCont x) = true
  · rw [if_pos h1]
  rw [if_neg h1]
  have h2 : (if x < 0x90 then ch == 0xF0 else ch == 0xF4) = true := by
    simpa [h1] using h
  by_cases h3 : x < 0x90
  · rw [if_pos h3] at h2
    have : (ch == 0xF0 && decide (x < 0x90)) = true := by simp [h2, h3]
    rw [if_pos this]
  · rw [if_neg h3] at h2
    have e : ch = 0xF4 := by simpa using h2
    subst e
    have n1 : ¬((244 == 0xF0 && decide (x < 0x90)) = true) := by simp
    have n2 : ((244 != 0xF0 && 244 == 0xF4 && decide (x ≥ 0x90)) = true) := by
      simp
      omega
    rw [if_neg n1, if_pos n2]

theorem step4_short3 {ch x y z : Nat}
    (h : ¬(!isCont x || (if x < 0x90 then ch == 0xF0 else ch == 0xF4)) = true)
    (hy : (!isCont y) = true) : step4 ch x y z = .err 3 := by
  unfold step4
  have h1 : ¬(!isCont x) = true := fun q => h (by simp [q])
  have h2 : ¬(if x < 0x90 then ch == 0xF0 else ch == 0xF4) = true := fun q => h (by simp [q])
  rw [if_neg h1]
  have c1 : ¬(ch == 0xF0 && decide (x < 0x90)) = true := by
    intro q
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at q
    apply h2
    rw [if_pos q.2]
    simp [q.1]
  have c2 : ¬(ch != 0xF0 && ch == 0xF4 && decide (x ≥ 0x90)) = true := by
    intro q
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne] at q
    apply h2
    rw [if_neg (by omega)]
    simp [q.1.2]
  rw [if_neg c1, if_neg c2, if_pos hy]

/-- More bytes after a piece change nothing, unless the piece ran out. -/
theorem step_app (r t : List Nat) : utf8Step r = .stop ∨ utf8Step (r ++ t) = utf8Step r := by
  cases r with
  | nil => exact .inl rfl
  | cons ch r =>
    rw [List.cons_append]
    by_cases h1 : ch < 128
    · right
      simp only [utf8Step, if_pos h1]
    by_cases h2 : ch < 224
    · by_cases h3 : ch < 194
      · right
        simp only [utf8Step, if_neg h1, if_pos h2, if_pos h3]
      · cases r with
        | nil =>
          left
          simp only [utf8Step, if_neg h1, if_pos h2, if_neg h3]
        | cons x r =>
          right
          simp only [utf8Step, if_neg h1, if_pos h2, if_neg h3, List.cons_append]
    by_cases h3 : ch < 240
    · cases r with
      | nil =>
        left
        simp only [utf8Step, if_neg h1, if_neg h2, if_pos h3]
      | cons x r =>
        cases r with
        | nil =>
          by_cases c : (!isCont x || (if x < 0xA0 then ch == 0xE0 else ch == 0xED)) = true
          · right
            cases t with
            | nil => simp
            | cons y u =>
              simp only [utf8Step, if_neg h1, if_neg h2, if_pos h3, List.cons_append, List.nil_append,
                step3_short c, if_pos c]
          · left
            simp only [utf8Step, if_neg h1, if_neg h2, if_pos h3, if_neg c]
        | cons y u =>
          right
          simp only [utf8Step, if_neg h1, if_neg h2, if_pos h3, List.cons_append]
    by_cases h4 : ch < 245
    · cases r with
      | nil =>
        left
        simp only [utf8Step, if_neg h1, if_neg h2, if_neg h3, if_pos h4]
      | cons x r =>
        cases r with
        | nil =>
          by_cases c : (!isCont x || (if x < 0x90 then ch == 0xF0 else ch == 0xF4)) = true
          · right
            cases t with
            | nil => simp
            | cons y u =>
              cases u with
              | nil =>
                simp only [utf8Step, if_neg h1, if_neg h2, if_neg h3, if_pos h4, List.cons_append,
                  List.nil_append, if_pos c]
              | cons z v =>
                simp only [utf8Step, if_neg h1, if_neg h2, if_neg h3, if_pos h4, List.cons_append,
                  List.nil_append, step4_short c, if_pos c]
          · left
            simp only [utf8Step, if_neg h1, if_neg h2, if_neg h3, if_pos h4, if_neg c]
        | cons y u =>
          cases u with
          | nil =>
            by_cases c : (!isCont x || (if x < 0x90 then ch == 0xF0 else ch == 0xF4)) = true
            · right
              cases t with
              | nil => simp
              | cons z v =>
                simp only [utf8Step, if_neg h1, if_neg h2, if_neg h3, if_pos h4, List.cons_append,
                  List.nil_append, step4_short c, if_pos c]
            · by_cases d : (!isCont y) = true
              · right
                cases t with
                | nil => simp
                | cons z v =>
                  simp only [utf8Step, if_neg h1, if_neg h2, if_neg h3, if_pos h4, List.cons_append,
                    List.nil_append, step4_short3 c d, if_neg c, if_pos d]
              · left
                simp only [utf8Step, if_neg h1, if_neg h2, if_neg h3, if_pos h4, if_neg c, if_neg d]
          | cons z v =>
            right
            simp only [utf8Step, if_neg h1, if_neg h2, if_neg h3, if_pos h4, List.cons_append]
    · right
      simp only [utf8Step, if_neg h1, if_neg h2, if_neg h3, if_neg h4]

theorem u8_agree (r t : List Nat) : Agree (stepU8 true r) (stepU8 false (r ++ t)) r.length := by
  cases r with
  | nil => trivial
  | cons b tl =>
    simp only [stepU8, List.cons_append]
    rw [← List.cons_append]
    rcases step_app (b :: tl) t with hs | he
    · rw [hs]
      simp [Agree]
    · rw [he]
      cases hst : utf8Step (b :: tl) with
      | char c n =>
        exact ⟨rfl, (step_char_len hst).2⟩
      | stop => simp [Agree]
      | err k =>
        by_cases hk : k = 1
        · subst hk
          exact ⟨rfl, by simp⟩
        · obtain ⟨k2, k4, k3, k5⟩ := span_err hst hk
          rcases k with _ | _ | j
          · omega
          · omega
          · change Agree (ite _ _ _) (ite _ _ _) _
            by_cases hc : (j + 1 + 1 == 2 && true && b == 0xED && (b :: tl).length == 2 &&
                decide (0xA0 ≤ tl.headD 0) && decide (tl.headD 0 ≤ 0xBF)) = true
            · rw [if_pos hc]
              trivial
            · rw [if_neg hc]
              have hf : ¬(j + 1 + 1 == 2 && false && b == 0xED && ((b :: tl) ++ t).length == 2 &&
                  decide (0xA0 ≤ (tl ++ t).headD 0) && decide ((tl ++ t).headD 0 ≤ 0xBF)) = true := by
                simp
              rw [if_neg hf]
              exact ⟨rfl, k3⟩

theorem u8_fail_zero {r : List Nat} {why : String} {s e : Nat} (h : stepU8 true r = .fail why s e) :
    s = 0 := by
  cases r with
  | nil => cases h
  | cons b tl =>
    simp only [stepU8] at h
    cases hst : utf8Step (b :: tl) with
    | char c n =>
      rw [hst] at h
      cases h
    | stop =>
      rw [hst] at h
      simp at h
    | err k =>
      rw [hst] at h
      rcases k with _ | _ | j
      · change ite _ _ _ = _ at h
        split at h
        · cases h
        · injection h with _ h2
          exact h2.symm
      · injection h with _ h2
        exact h2.symm
      · change ite _ _ _ = _ at h
        split at h
        · cases h
        · injection h with _ h2
          exact h2.symm

theorem and_f0 : ∀ a : Fin 256, (a.val &&& 0xf0) = 0xe0 → 224 ≤ a.val ∧ a.val ≤ 239 := by
  decide +kernel

theorem and_c0 : ∀ a : Fin 256, (a.val &&& 0xc0) = 0x80 → 128 ≤ a.val ∧ a.val ≤ 191 := by
  decide +kernel

/-- `surrogatepass` takes three bytes for a surrogate only if they start `ED A0..BF`. -/
theorem pass_utf8 {p q w : Nat} {u : List Nat} (hp : p < 256) (hq : q < 256)
    (hs : isSurrogate (surrogatePassRead .utf8 (p :: q :: w :: u)) = true) :
    p = 0xED ∧ 0xA0 ≤ q ∧ q ≤ 0xBF := by
  simp only [surrogatePassRead] at hs
  by_cases c : (p &&& 0xf0 == 0xe0 && q &&& 0xc0 == 0x80 && w &&& 0xc0 == 0x80) = true
  · rw [if_pos c] at hs
    simp only [Bool.and_eq_true, beq_iff_eq] at c
    obtain ⟨⟨c1, c2⟩, _⟩ := c
    have a1 := and_f0 ⟨p, hp⟩ c1
    have b1 := and_c0 ⟨q, hq⟩ c2
    dsimp only at a1 b1
    have e1 : p &&& 0x0f = p % 16 := Nat.and_two_pow_sub_one_eq_mod p 4
    have e2 : q &&& 0x3f = q % 64 := Nat.and_two_pow_sub_one_eq_mod q 6
    have e3 : w &&& 0x3f ≤ 63 := Nat.and_le_right
    have s1 : (2 : Nat) ^ 12 = 4096 := rfl
    have s2 : (2 : Nat) ^ 6 = 64 := rfl
    simp only [isSurrogate, Bool.and_eq_true, decide_eq_true_eq, Nat.shiftLeft_eq, e1, e2, s1, s2] at hs
    omega
  · rw [if_neg c] at hs
    simp [isSurrogate] at hs

/-- At a short end of a chunk, `surrogatepass` gives up, and it would with more bytes too. The two
bytes that would make it change its mind are the ones the decoder waits on. -/
theorem u8_short {r t : List Nat} {why : String} {s e : Nat} (hs : stepU8 true r = .fail why s e)
    (hl : r.length < 3) (hb : ∀ x ∈ r ++ t, x < 256) :
    isSurrogate (surrogatePassRead .utf8 (r ++ t)) = false := by
  rcases r with _ | ⟨x, _ | ⟨y, _ | ⟨z, r⟩⟩⟩
  · cases hs
  · rcases t with _ | ⟨y, _ | ⟨z, u⟩⟩
    · rfl
    · rfl
    · cases hc : isSurrogate (surrogatePassRead .utf8 ([x] ++ y :: z :: u)) with
      | false => rfl
      | true =>
        obtain ⟨h1, _, _⟩ := pass_utf8 (hb x (by simp)) (hb y (by simp)) hc
        subst h1
        simp [stepU8, utf8Step] at hs
  · rcases t with _ | ⟨z, u⟩
    · rfl
    · cases hc : isSurrogate (surrogatePassRead .utf8 ([x, y] ++ z :: u)) with
      | false => rfl
      | true =>
        obtain ⟨h1, h2, h3⟩ := pass_utf8 (hb x (by simp)) (hb y (by simp)) hc
        subst h1
        have hc1 : ¬(y < 0xA0) := by omega
        have ht : isCont y = true := by
          simp only [isCont, Bool.and_eq_true, decide_eq_true_eq]
          omega
        simp [stepU8, utf8Step, hc1, ht, h2, h3] at hs
  · simp at hl
    omega

theorem u8_loc {a t : Bytes} (hb : ∀ x ∈ a ++ t, x < 256) (h : ErrHandler) {i : Nat} {why : String}
    {s e : Nat} (hs : stepU8 true (a.drop i) = .fail why s e) :
    handlerLoc h "utf-8" .utf8 a t (i + s) (i + e) why := by
  have hag := u8_agree (a.drop i) t
  rw [hs] at hag
  have hok := (u8_moves true).ok (a.drop i)
  rw [hs] at hok
  simp only [okStep] at hok
  have hle := hag.2
  have hs0 := u8_fail_zero hs
  subst hs0
  have hne : a.drop i ≠ [] := by
    intro he
    rw [he] at hs
    cases hs
  have hpos := List.length_pos_iff.2 hne
  simp only [List.length_drop] at hle hpos
  by_cases hl : 3 ≤ a.length - i
  · exact handler_loc h _ _ _ _ _ _ _ (by omega) (by omega) (fun _ => .inr (by
      simp only [EncCode.bytelength]
      omega))
  by_cases hh : h = .surrogatepass
  · subst hh
    have hdrop : (a ++ t).drop (i + 0) = a.drop i ++ t := by
      rw [Nat.add_zero]
      exact List.drop_append_of_le_length (by omega)
    have hbb : ∀ x ∈ a.drop i ++ t, x < 256 := by
      intro x hx
      apply hb
      rw [← hdrop] at hx
      exact List.mem_of_mem_drop hx
    have hsh := u8_short hs (by simp only [List.length_drop]; omega) hbb
    have h0 : isSurrogate 0 = false := by decide
    have hn : ¬a.length - (i + 0) ≥ EncCode.utf8.bytelength := by
      simp only [EncCode.bytelength]
      omega
    unfold handlerLoc
    simp only [decodeHandlerCall, hdrop]
    have hu : (EncCode.utf8 == EncCode.unknown) = false := rfl
    simp only [hu, Bool.false_eq_true, if_false, if_neg hn, h0]
    by_cases hg : (a ++ t).length - (i + 0) ≥ EncCode.utf8.bytelength
    · simp only [if_pos hg, hsh, Bool.false_eq_true, if_false]
      exact ⟨_, rfl⟩
    · simp only [if_neg hg, h0, Bool.false_eq_true, if_false]
      exact ⟨_, rfl⟩
  · exact handler_loc h _ _ _ _ _ _ _ (by omega) (by omega) (fun q => absurd q hh)

/-- UTF-8 in two chunks, wherever the input is cut, inside a character included, for every standard
handler. `surrogatepass` is the interesting one: with a cut after `ED A0` the first chunk must not
report the error it would report at the very end. `∀ x ∈ b, x < 256` is the type invariant of
`bytes`, which the mask tests of `surrogatepass` need. -/
def Utf8Chunks : Prop :=
  ∀ (b : Bytes) (k : Nat) (h : ErrHandler), (∀ x ∈ b, x < 256) →
    Chunked (fun x final => utf8DecodeLoop x h (!final) (x.length + 1) 0 x []) b k

theorem utf8Chunks_proven : Utf8Chunks := by
  intro b k h hb
  refine chunked_driver (u8_moves true) (u8_moves false) h "utf-8" .utf8 b k
    (fun i => u8_agree _ _) ?_ _
    (fun x => utf8_driver x h _ _ 0 x [] rfl (Nat.zero_le _))
    (fun x => utf8_driver x h _ _ 0 x [] rfl (Nat.zero_le _))
  intro i why s e hs
  exact u8_loc (by rw [List.take_append_drop]; exact hb) h hs

end PyLean.UnicodeObj
