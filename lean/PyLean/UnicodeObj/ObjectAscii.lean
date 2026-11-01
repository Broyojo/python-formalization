import PyLean.UnicodeObj.ObjectUtf8Writer

/-!
`PyUnicode_DecodeASCII` as C writes it, unicodeobject.c:7578-7675: the fast paths, the writer, and the
three handlers written out inside the loop. `asciiDecodeX` goes through `handlerStep` for all of them.

`AsciiDecodeSpec` is that the two are the same decoder, and that the kind of the result is canonical.
The buffer starts ASCII and is only ever widened, by `PrepareKind` for the inline handlers and by
`_PyUnicodeWriter_WriteStr` for a callback, so nothing here can leave it too wide. `ascii_decode` is
`asciiPrefix`, as in `ObjectUtf8.lean`.
-/

namespace PyLean.UnicodeObj

open PyLean

/-- The `while (s < e)` of `PyUnicode_DecodeASCII`, unicodeobject.c:7616-7665. -/
def asciiLoopC (H : DH) : Nat → Bytes → List DecView → Nat → List Nat → UWriter → Py UWriter
  | 0, _, _, _, _, _ => .error .modelFuel
  | _ + 1, _, _, _, [], w => .ok w
  | fuel + 1, input, hist, pos, c :: t, w =>
    if c < 128 then
      asciiLoopC H fuel input hist (pos + 1) t { w with text := w.text ++ [c] }
    else
      let viaCallback : Py UWriter :=
        match handlerStep H "ascii" .unknown "ordinal not in range(128)" input hist pos (pos + 1) with
        | .error e => .error e
        | .ok (hist', input', rep, newpos) =>
          asciiLoopC H fuel input' hist' newpos (input'.drop newpos) (writeText w rep)
      match H with
      | .std .replace =>
        asciiLoopC H fuel input hist (pos + 1) t
          { text := w.text ++ [0xfffd], cap := prepareCap w.cap 0xffff }
      | .std .surrogateescape =>
        asciiLoopC H fuel input hist (pos + 1) t
          { text := w.text ++ [c + 0xdc00], cap := prepareCap w.cap 0xffff }
      | .std .ignore => asciiLoopC H fuel input hist (pos + 1) t w
      | _ => viaCallback

/-- `PyUnicode_DecodeASCII`, with the kind of what it returns. -/
def asciiDecodeC (b : Bytes) (H : DH) (fuel : Nat) : Py (Str × Kind) :=
  if b.isEmpty then .ok ([], .ascii)
  else if b.length = 1 ∧ b.getD 0 0 < 128 then .ok (b, .ascii)
  else
    let pre := asciiPrefix b
    if pre.length = b.length then .ok (b, .ascii)
    else
      match asciiLoopC H (fuel - pre.length) b [] pre.length (b.drop pre.length)
          { text := pre, cap := 127 } with
      | .error e => .error e
      | .ok w => .ok w.finish

/-- The capacity is what the text needs. -/
abbrev WTight (w : UWriter) : Prop := w.cap = capNeed (maxCharOf w.text)

theorem tight_char {w : UWriter} (h : WTight w) {c : Nat} (hc : c < 128) :
    WTight { w with text := w.text ++ [c] } := by
  show w.cap = capNeed (maxCharOf (w.text ++ [c]))
  have e : maxCharOf [c] = c := by simp [maxCharOf]
  rw [maxCharOf_append, capNeed_max, e, ← h]
  have h1 : capNeed c = 127 := by
    have := need_ascii (s := [c]) (by simpa using hc)
    rwa [e] at this
  have h2 := need_value (maxCharOf w.text)
  rw [h1]
  omega

theorem tight_wide {w : UWriter} (h : WTight w) {c : Nat} (h1 : 256 ≤ c) (h2 : c < 65536) :
    WTight { text := w.text ++ [c], cap := prepareCap w.cap 0xffff } := by
  have hv : CapValue w.cap := by
    have := need_value (maxCharOf w.text)
    unfold CapValue
    omega
  show prepareCap w.cap 0xffff = capNeed (maxCharOf (w.text ++ [c]))
  have e : maxCharOf [c] = c := by simp [maxCharOf]
  have n1 : capNeed c = 0xffff := by
    unfold capNeed kindOfMax
    repeat' split
    all_goals (try simp only [capOf])
    all_goals omega
  have n2 : capNeed 0xffff = 0xffff := by decide
  rw [prepare_max hv, maxCharOf_append, capNeed_max, e, n1, n2, ← h]

theorem tight_write {w : UWriter} (h : WTight w) (rep : Str) : WTight (writeText w rep) := by
  have hv : CapValue w.cap := by
    have := need_value (maxCharOf w.text)
    unfold CapValue
    omega
  rw [writeText_eq hv]
  unfold wExpect
  split
  · exact h
  · show max w.cap (capNeed (maxCharOf rep)) = capNeed (maxCharOf (w.text ++ rep))
    rw [maxCharOf_append, capNeed_max, ← h]

/-- The characters of a byte under the two inline handlers. -/
theorem escape_one {c : Nat} (hc : ¬c < 128) (t : List Nat) (input : Bytes) (pos : Nat)
    (hr : c :: t = input.drop pos) :
    (input.drop pos).take (pos + 1 - pos) = [c] ∧ input.drop (pos + 1) = t := by
  constructor
  · rw [← hr]
    have e : pos + 1 - pos = 1 := by omega
    rw [e]
    simp
  · have := congrArg (List.drop 1) hr
    rw [List.drop_drop] at this
    simpa [Nat.add_comm] using this.symm

theorem asciiLoop_tie (H : DH) : ∀ (fuel : Nat) (input : Bytes) (hist : List DecView) (pos : Nat)
    (rest : List Nat) (w : UWriter), rest = input.drop pos → WTight w →
    (H = .std .surrogateescape → ∀ x ∈ input, x < 256) →
    match decodeDriverX stepAscii H "ascii" .unknown none fuel input hist pos rest w.text with
    | .ok (s, _) => asciiLoopC H fuel input hist pos rest w =
        .ok { text := s, cap := capNeed (maxCharOf s) }
    | .error e => asciiLoopC H fuel input hist pos rest w = .error e := by
  intro fuel
  induction fuel with
  | zero => intro input hist pos rest w _ _ _; rfl
  | succ fuel ih =>
    intro input hist pos rest w hr hw hb
    cases rest with
    | nil =>
      simp only [decodeDriverX, stepAscii, stopPos, asciiLoopC]
      rw [← hw]
    | cons c t =>
      have hd : t = input.drop (pos + 1) := by
        have := congrArg (List.drop 1) hr
        rw [List.drop_drop] at this
        simpa [Nat.add_comm] using this
      by_cases hc : c < 128
      · simp only [decodeDriverX, stepAscii, asciiLoopC, if_pos hc, List.drop_succ_cons, List.drop_zero]
        exact ih input hist (pos + 1) t { w with text := w.text ++ [c] } hd (tight_char hw hc) hb
      · obtain ⟨hs, hn⟩ := escape_one hc t input pos hr
        simp only [decodeDriverX, stepAscii, asciiLoopC, if_neg hc, Nat.add_zero]
        have general : H ≠ .std .surrogateescape →
            match (match handlerStep H "ascii" .unknown "ordinal not in range(128)" input hist pos (pos + 1) with
              | .error x => (.error x : Py (Str × Nat))
              | .ok (hist', input', rep, newpos) =>
                decodeDriverX stepAscii H "ascii" .unknown none fuel input' hist' newpos
                  (input'.drop newpos) (w.text ++ rep)) with
            | .ok (s, _) =>
              (match handlerStep H "ascii" .unknown "ordinal not in range(128)" input hist pos (pos + 1) with
                | .error e => (.error e : Py UWriter)
                | .ok (hist', input', rep, newpos) =>
                  asciiLoopC H fuel input' hist' newpos (input'.drop newpos) (writeText w rep)) =
                .ok { text := s, cap := capNeed (maxCharOf s) }
            | .error e =>
              (match handlerStep H "ascii" .unknown "ordinal not in range(128)" input hist pos (pos + 1) with
                | .error e => (.error e : Py UWriter)
                | .ok (hist', input', rep, newpos) =>
                  asciiLoopC H fuel input' hist' newpos (input'.drop newpos) (writeText w rep)) = .error e := by
          intro hne
          cases hh : handlerStep H "ascii" .unknown "ordinal not in range(128)" input hist pos (pos + 1) with
          | error e => rfl
          | ok r =>
            obtain ⟨hist', input', rep, newpos⟩ := r
            have := ih input' hist' newpos (input'.drop newpos) (writeText w rep) rfl (tight_write hw rep)
              (fun e => absurd e hne)
            rw [writeText_text] at this
            exact this
        cases H with
        | custom cb' => exact general (by simp)
        | missing n => exact general (by simp)
        | std h =>
          cases h
          case replace =>
            simp only [handlerStep, decodeHandlerCall]
            rw [← hd]
            exact ih input hist (pos + 1) t _ hd (tight_wide hw (by omega) (by omega)) hb
          case ignore =>
            simp only [handlerStep, decodeHandlerCall, List.append_nil]
            rw [← hd]
            exact ih input hist (pos + 1) t w hd hw hb
          case surrogateescape =>
            have hc2 : c < 256 := hb rfl c (by
              have : c ∈ input.drop pos := by rw [← hr]; exact List.mem_cons_self
              exact List.mem_of_mem_drop this)
            have hrun : escapeRun 4 [c] = [c] := by
              simp only [escapeRun]
              rw [if_neg hc]
            simp only [handlerStep, decodeHandlerCall, hs, hrun, List.isEmpty_cons, Bool.false_eq_true,
              if_false, List.map_cons, List.map_nil, List.length_singleton]
            rw [← hd]
            exact ih input hist (pos + 1) t _ hd (tight_wide hw (by omega) (by omega)) hb
          all_goals exact general (by simp)

/-- The ASCII bytes at the head of the input are decoded one by one, as the fast path does at once. -/
theorem asciiDriver_skip (H : DH) (input : Bytes) (hist : List DecView) (pre : Bytes)
    (hp : ∀ x ∈ pre, x < 128) (fuel pos : Nat) (rest : List Nat) (out : Str) :
    decodeDriverX stepAscii H "ascii" .unknown none (pre.length + fuel) input hist pos (pre ++ rest) out =
      decodeDriverX stepAscii H "ascii" .unknown none fuel input hist (pos + pre.length) rest (out ++ pre) := by
  induction pre generalizing pos out with
  | nil => simp
  | cons x t ih =>
    have hx := hp x List.mem_cons_self
    have e : (x :: t).length + fuel = (t.length + fuel) + 1 := by simp; omega
    rw [e, List.cons_append]
    simp only [decodeDriverX, stepAscii, if_pos hx, List.drop_succ_cons, List.drop_zero]
    rw [ih (fun y hy => hp y (List.mem_cons_of_mem _ hy))]
    have e2 : pos + 1 + t.length = pos + (x :: t).length := by simp; omega
    rw [e2]
    simp

/-- `PyUnicode_DecodeASCII`, unicodeobject.c:7578-7675. The inline `replace`, `surrogateescape` and
`ignore` do what the registered handlers do, the two fast paths and `ascii_decode` change nothing,
and the kind of the result is canonical, for every handler, including one that rewinds or replaces
the object.

`∀ x ∈ b, x < 256` is the type invariant of `bytes`. `b.length < fuel` is the budget of the model. -/
def AsciiDecodeSpec : Prop :=
  ∀ (b : Bytes) (H : DH) (fuel : Nat), (∀ x ∈ b, x < 256) → b.length < fuel →
    match asciiDecodeX b H fuel with
    | .ok s => asciiDecodeC b H fuel = .ok (s, canonicalKind s)
    | .error e => asciiDecodeC b H fuel = .error e

theorem asciiDecodeSpec_proven : AsciiDecodeSpec := by
  intro b H fuel hb hf
  have kindAscii : (∀ x ∈ b, x < 128) → canonicalKind b = .ascii := by
    intro ha
    have hm : maxCharOf b ≤ 127 :=
      foldl_max_le b 0 127 (by omega) (fun x hx => by have := ha x hx; omega)
    unfold canonicalKind kindOfMax
    rw [if_pos (by omega)]
  have allAscii : (∀ x ∈ b, x < 128) → asciiDecodeX b H fuel = .ok b := by
    intro ha
    have h := asciiDriver_skip H b [] b ha (fuel - b.length - 1 + 1) 0 [] []
    have e : b.length + (fuel - b.length - 1 + 1) = fuel := by omega
    rw [e] at h
    simp only [List.append_nil, decodeDriverX, stepAscii, List.nil_append] at h
    simp only [asciiDecodeX, h]
    rfl
  unfold asciiDecodeC
  by_cases he : b.isEmpty = true
  · have hl : b = [] := List.isEmpty_iff.1 he
    subst hl
    rw [allAscii (by simp)]
    rfl
  rw [if_neg he]
  by_cases h1 : b.length = 1 ∧ b.getD 0 0 < 128
  · rw [if_pos h1]
    have ha : ∀ x ∈ b, x < 128 := by
      cases b with
      | nil => simp at h1
      | cons y r =>
        cases r with
        | nil =>
          simp only [List.getD_cons_zero] at h1
          intro x hx
          rw [List.mem_singleton.1 hx]
          exact h1.2
        | cons _ _ => simp at h1
    rw [allAscii ha]
    dsimp only
    rw [kindAscii ha]
  rw [if_neg h1]
  by_cases h2 : (asciiPrefix b).length = b.length
  · have hpb : asciiPrefix b = b := by
      obtain ⟨_, hb'⟩ := asciiPrefix_parts b
      have : b.drop (asciiPrefix b).length = [] := by
        rw [h2]
        simp
      rw [this] at hb'
      simpa using hb'
    have ha : ∀ x ∈ b, x < 128 := by
      intro x hx
      exact asciiPrefix_lt b x (by rw [hpb]; exact hx)
    dsimp only
    rw [if_pos h2, allAscii ha]
    dsimp only
    rw [kindAscii ha]
  dsimp only
  rw [if_neg h2]
  have hlt : (asciiPrefix b).length < b.length := by
    have hl := congrArg List.length (asciiPrefix_parts b).2
    simp only [List.length_append, List.length_drop] at hl
    omega
  obtain ⟨hp, hparts⟩ := asciiPrefix_parts b
  have hrun := asciiDriver_skip H b [] (asciiPrefix b) hp (fuel - (asciiPrefix b).length) 0
    (b.drop (asciiPrefix b).length) []
  rw [hparts, show (asciiPrefix b).length + (fuel - (asciiPrefix b).length) = fuel by omega] at hrun
  simp only [Nat.zero_add, List.nil_append] at hrun
  have hw0 : WTight { text := asciiPrefix b, cap := 127 } := (need_ascii hp).symm
  have tie := asciiLoop_tie H (fuel - (asciiPrefix b).length) b [] (asciiPrefix b).length
    (b.drop (asciiPrefix b).length) { text := asciiPrefix b, cap := 127 } rfl hw0 (fun _ => hb)
  dsimp only at tie
  rw [← hrun] at tie
  simp only [asciiDecodeX]
  cases hd : decodeDriverX stepAscii H "ascii" .unknown none fuel b [] 0 b [] with
  | error e =>
    rw [hd] at tie
    dsimp only at tie
    rw [tie]
    rfl
  | ok r =>
    obtain ⟨s, n⟩ := r
    rw [hd] at tie
    dsimp only at tie
    rw [tie]
    have hW : WInv ({ text := s, cap := capNeed (maxCharOf s) } : UWriter) := .inl rfl
    dsimp only
    rw [hW.finish]
    rfl

end PyLean.UnicodeObj
