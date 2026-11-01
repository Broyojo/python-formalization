import PyLean.UnicodeObj.ObjectUtf8Props

/-!
The decoder into a writer, with any handler, and its fast paths.
-/

namespace PyLean.UnicodeObj

open PyLean

/-- `utf8WriterLoopX` is `utf8DecodeLoopX`: same text, same consumed, same exception. -/
theorem utf8WriterLoopX_tie (H : DH) (consumed : Bool) :
    ∀ fuel input hist pos rest out, Tied (utf8DecodeLoopX H consumed fuel input hist pos rest out)
      (utf8WriterLoopX H consumed fuel input hist pos rest out) := by
  intro fuel
  induction fuel with
  | zero => intro input hist pos rest out; simp [utf8DecodeLoopX, utf8WriterLoopX, Tied]
  | succ fuel ih =>
    intro input hist pos rest out
    cases rest with
    | nil => simp [utf8DecodeLoopX, utf8WriterLoopX, Tied]
    | cons b0 tl =>
      have via : ∀ (reason : String) (stopAt : Nat),
          Tied
            (match handlerStep H "utf-8" .utf8 reason input hist pos stopAt with
              | .error e => .error e
              | .ok (hist', input', rep, newpos) =>
                utf8DecodeLoopX H consumed fuel input' hist' newpos (input'.drop newpos) (out ++ rep))
            (match handlerStep H "utf-8" .utf8 reason input hist pos stopAt with
              | .error e => (out, .error e)
              | .ok (hist', input', rep, newpos) =>
                utf8WriterLoopX H consumed fuel input' hist' newpos (input'.drop newpos) (out ++ rep)) := by
        intro reason stopAt
        cases hc : handlerStep H "utf-8" .utf8 reason input hist pos stopAt with
        | error e => rfl
        | ok r =>
          obtain ⟨hist', input', rep, newpos⟩ := r
          exact ih _ _ _ _ _
      have key : ∀ (reason : String) (stopAt : Nat),
          Tied
            (match (generalizing := false) H with
              | .std .ignore => utf8DecodeLoopX H consumed fuel input hist stopAt
                  ((b0 :: tl).drop (stopAt - pos)) (out ++ [])
              | .std .replace => utf8DecodeLoopX H consumed fuel input hist stopAt
                  ((b0 :: tl).drop (stopAt - pos)) (out ++ [0xfffd])
              | .std .surrogateescape => utf8DecodeLoopX H consumed fuel input hist stopAt
                  ((b0 :: tl).drop (stopAt - pos))
                  (out ++ ((b0 :: tl).take (stopAt - pos)).map (· + 0xdc00))
              | _ =>
                match handlerStep H "utf-8" .utf8 reason input hist pos stopAt with
                | .error e => .error e
                | .ok (hist', input', rep, newpos) =>
                  utf8DecodeLoopX H consumed fuel input' hist' newpos (input'.drop newpos) (out ++ rep))
            (match (generalizing := false) H with
              | .std .ignore => utf8WriterLoopX H consumed fuel input hist stopAt
                  ((b0 :: tl).drop (stopAt - pos)) (out ++ [])
              | .std .replace => utf8WriterLoopX H consumed fuel input hist stopAt
                  ((b0 :: tl).drop (stopAt - pos)) (out ++ [0xfffd])
              | .std .surrogateescape => utf8WriterLoopX H consumed fuel input hist stopAt
                  ((b0 :: tl).drop (stopAt - pos))
                  (out ++ ((b0 :: tl).take (stopAt - pos)).map (· + 0xdc00))
              | _ =>
                match handlerStep H "utf-8" .utf8 reason input hist pos stopAt with
                | .error e => (out, .error e)
                | .ok (hist', input', rep, newpos) =>
                  utf8WriterLoopX H consumed fuel input' hist' newpos (input'.drop newpos) (out ++ rep)) := by
        intro reason stopAt
        have v := via reason stopAt
        cases H with
        | std h =>
          cases h
          case ignore | replace | surrogateescape => exact ih _ _ _ _ _
          all_goals exact v
        | custom cb => exact v
        | missing n => exact v
      simp only [utf8DecodeLoopX, utf8WriterLoopX]
      cases hs : utf8Step (b0 :: tl) with
      | char c n => exact ih _ _ _ _ _
      | stop =>
        dsimp only
        split
        · rfl
        · exact key _ _
      | err code =>
        rcases code with _ | _ | code
        all_goals (try dsimp only)
        all_goals first
          | exact key _ _
          | (change Tied (ite _ _ _) (ite _ _ _)
             split
             · rfl
             · exact key _ _)

/-- The ASCII bytes at the head of the input are decoded one by one, as the fast path does at once. -/
theorem loop_asciiX (H : DH) (c : Bool) (input : Bytes) (hist : List DecView) (pre : Bytes)
    (hp : ∀ x ∈ pre, x < 128) (fuel pos : Nat) (rest : List Nat) (out : Str) :
    utf8WriterLoopX H c (pre.length + fuel) input hist pos (pre ++ rest) out =
      utf8WriterLoopX H c fuel input hist (pos + pre.length) rest (out ++ pre) := by
  induction pre generalizing pos out with
  | nil => simp
  | cons x t ih =>
    have hx := hp x List.mem_cons_self
    have e : (x :: t).length + fuel = (t.length + fuel) + 1 := by simp; omega
    have hs : utf8Step (x :: (t ++ rest)) = .char x 1 := by
      simp only [utf8Step]
      rw [if_pos hx]
    rw [e, List.cons_append]
    simp only [utf8WriterLoopX, hs, List.drop_succ_cons, List.drop_zero]
    rw [ih (fun y hy => hp y (List.mem_cons_of_mem _ hy))]
    have e2 : pos + 1 + t.length = pos + (x :: t).length := by simp; omega
    rw [e2]
    simp

/-- The decode with no fast path. -/
def decodeWholeX (w : UWriter) (b : Bytes) (H : DH) (consumed : Bool) (fuel : Nat) : UWriter × Py Nat :=
  if b.isEmpty then (w, .ok 0) else decodeRestX w (prepareCap w.cap 127) b [] H consumed fuel

/-- From the buffer's point of view the fast path, finished or not, is the loop. -/
theorem decodeWriterX_whole (w : UWriter) (b : Bytes) (H : DH) (c : Bool) (fuel : Nat)
    (hf : b.length < fuel) : decodeWriterX w b H c fuel = decodeWholeX w b H c fuel := by
  unfold decodeWriterX decodeWholeX
  split
  · rfl
  · dsimp only
    split
    · obtain ⟨hp, hb⟩ := asciiPrefix_parts b
      have hl : (asciiPrefix b).length + (b.drop (asciiPrefix b).length).length = b.length := by
        have := congrArg List.length hb
        simpa using this
      have hrest : ∀ k, utf8WriterLoopX H c ((asciiPrefix b).length + k) b [] 0 b [] =
          utf8WriterLoopX H c k b [] (asciiPrefix b).length (b.drop (asciiPrefix b).length)
            (asciiPrefix b) := by
        intro k
        have := loop_asciiX H c b [] (asciiPrefix b) hp k 0 (b.drop (asciiPrefix b).length) []
        rw [hb] at this
        simpa using this
      have hfuel : fuel = (asciiPrefix b).length + (fuel - (asciiPrefix b).length) := by omega
      split
      · next he =>
        have hnil : b.drop (asciiPrefix b).length = [] := by
          apply List.eq_nil_of_length_eq_zero
          omega
        have heq : asciiPrefix b = b := by
          rw [hnil] at hb
          simpa using hb
        have hl1 := hrest (fuel - (asciiPrefix b).length)
        rw [← hfuel, hnil, heq] at hl1
        have hk : fuel - b.length = (fuel - b.length - 1) + 1 := by omega
        rw [hk] at hl1
        simp only [utf8WriterLoopX] at hl1
        simp only [decodeRestX, List.length_nil, Nat.sub_zero, List.drop_zero]
        rw [hl1, heq]
        have hm : maxCharOf b ≤ 127 :=
          foldl_max_le b 0 127 (by omega) (fun x hx => by
            have hx' : x ∈ asciiPrefix b := by
              rw [heq]
              exact hx
            have := hp x hx'
            omega)
        have hg := prepare_ge w.cap
        have hc : prepareCap (prepareCap w.cap 127) (maxCharOf b) = prepareCap w.cap 127 := by
          rw [prepareCap, if_neg (by omega)]
        simp only [hc]
      · simp only [decodeRestX, List.length_nil, Nat.sub_zero, List.drop_zero]
        rw [← hrest, ← hfuel]
    · rfl

theorem tied_writer_ok {d : Py (Str × Nat)} {s : Str} {n : Nat} (t : Tied d (s, .ok n)) :
    d = .ok (s, n) := by
  cases d with
  | error e => simp [Tied] at t
  | ok r =>
    obtain ⟨a, m⟩ := r
    simp only [Tied, Prod.mk.injEq, Except.ok.injEq] at t
    rw [t.1, t.2]

/-- An empty input decodes to nothing, with any budget, as long as there is one. -/
theorem decodeX_nil {H : DH} {c : Bool} {fuel : Nat} (hf : 0 < fuel) :
    utf8DecodeX [] H c fuel = .ok ([], 0) := by
  obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
  rfl

theorem decodeWriterX_ok {b : Bytes} {H : DH} {c : Bool} {fuel : Nat} {s : Str} {n : Nat}
    (hf : b.length < fuel) (hd : utf8DecodeX b H c fuel = .ok (s, n)) (w : UWriter) :
    decodeWriterX w b H c fuel =
      (if b.isEmpty then w
        else { text := w.text ++ s, cap := prepareCap (prepareCap w.cap 127) (maxCharOf s) },
       .ok n) := by
  rw [decodeWriterX_whole w b H c fuel hf]
  cases b with
  | nil =>
    rw [decodeX_nil (by simpa using hf)] at hd
    injection hd with hd
    injection hd with h1 h2
    subst h2
    simp [decodeWholeX]
  | cons x xs =>
    have t := utf8WriterLoopX_tie H c fuel (x :: xs) [] 0 (x :: xs) []
    rw [show utf8DecodeLoopX H c fuel (x :: xs) [] 0 (x :: xs) [] = .ok (s, n) from hd] at t
    simp only [Tied] at t
    simp only [decodeWholeX, decodeRestX, List.length_nil, Nat.sub_zero, List.drop_zero, t,
      List.isEmpty_cons, Bool.false_eq_true, if_false]

theorem decodeWriterX_err {b : Bytes} {H : DH} {c : Bool} {fuel : Nat} {e : PyExc}
    (hf : b.length < fuel) (hd : utf8DecodeX b H c fuel = .error e) (w : UWriter) :
    (decodeWriterX w b H c fuel).1.text = w.text ∧ (decodeWriterX w b H c fuel).2 = .error e := by
  have hne : b.isEmpty = false := by
    cases b with
    | nil =>
      rw [decodeX_nil (by simpa using hf)] at hd
      cases hd
    | cons _ _ => rfl
  have t := utf8WriterLoopX_tie H c fuel b [] 0 b []
  rw [show utf8DecodeLoopX H c fuel b [] 0 b [] = .error e from hd] at t
  simp only [Tied] at t
  rw [decodeWriterX_whole w b H c fuel hf]
  cases hw : utf8WriterLoopX H c fuel b [] 0 b [] with
  | mk out r =>
    rw [hw] at t
    simp only at t
    subst t
    simp only [decodeWholeX, decodeRestX, hne, Bool.false_eq_true, if_false, List.length_nil,
      Nat.sub_zero, List.drop_zero, hw]
    constructor <;> first | rfl | trivial

/-- `unicode_decode_utf8_writer`, with any handler: what it adds is what the decoder of
`bytes.decode` gives, whatever the handler does, including replacing the input. If that raises, the
same exception comes out and none of the text stays. A success keeps the writer's capacity exactly
what its text needs. `b.length < fuel` is the budget of the model: the fast path spends none of it,
and the loop one a character. -/
def WriterDecodeX : Prop :=
  ∀ (w : UWriter) (b : Bytes) (H : DH) (c : Bool) (fuel : Nat), b.length < fuel →
    match utf8DecodeX b H c fuel with
    | .ok (s, n) =>
      (decodeWriterX w b H c fuel).1.text = w.text ++ s ∧ (decodeWriterX w b H c fuel).2 = .ok n ∧
        (WInv w → WInv (decodeWriterX w b H c fuel).1)
    | .error e =>
      (decodeWriterX w b H c fuel).1.text = w.text ∧ (decodeWriterX w b H c fuel).2 = .error e

theorem writerDecodeX_proven : WriterDecodeX := by
  intro w b H c fuel hf
  cases hd : utf8DecodeX b H c fuel with
  | error e => exact decodeWriterX_err hf hd w
  | ok r =>
    obtain ⟨s, n⟩ := r
    dsimp only
    rw [decodeWriterX_ok hf hd]
    refine ⟨?_, rfl, ?_⟩
    · dsimp only
      split
      · next he =>
        have hb : b = [] := List.isEmpty_iff.1 he
        subst hb
        rw [decodeX_nil (by simpa using hf)] at hd
        injection hd with hd
        injection hd with h1 h2
        simp [← h1]
      · rfl
    · intro hI
      have hc := hI.capValue
      dsimp only
      split
      · exact hI
      · left
        show prepareCap (prepareCap w.cap 127) (maxCharOf s) = capNeed (maxCharOf (w.text ++ s))
        rw [prepare_max (capValue_prepare hc _), prepare_max hc, maxCharOf_append, capNeed_max]
        have e : capNeed 127 = 127 := by decide
        have := need_value (maxCharOf s)
        rcases hI with hi | ⟨hi, ht⟩
        · have := need_value (maxCharOf w.text)
          rw [e, hi]
          omega
        · rw [e, hi, ht, need_empty]
          omega

/-- `PyUnicodeWriter_DecodeUTF8Stateful`, unicodeobject.c@3.14.7:14171-14192, with any handler. `size` picks
the bytes, negative meaning up to the first NUL. With `consumed` the result is `*consumed`; without
it nothing is reported. On a failure the position is put back, so no text stays, and `*consumed` is
0 however far the decoder got. -/
def WriterDecodeStatefulX : Prop :=
  ∀ (w : UWriter) (b : Bytes) (size : Int) (H : DH) (c : Bool) (fuel : Nat),
    (sizedBytes b size).length < fuel →
    let r := writerDecodeStateful w b size H c fuel
    match utf8DecodeX (sizedBytes b size) H c fuel with
    | .ok (s, n) => r.1.text = w.text ++ s ∧ r.2 = .ok (if c then n else 0)
    | .error e => r.1.text = w.text ∧ r.2 = .error e ∧ consumedOut r.2 = 0

theorem writerDecodeStatefulX_proven : WriterDecodeStatefulX := by
  intro w b size H c fuel hf
  have main := writerDecodeX_proven w (sizedBytes b size) H c fuel hf
  dsimp only
  cases hd : utf8DecodeX (sizedBytes b size) H c fuel with
  | error e =>
    rw [hd] at main
    obtain ⟨h1, h2⟩ := main
    cases c
    · simp [writerDecodeStateful, noConsumed, h1, h2, Except.map, consumedOut]
    · simp [writerDecodeStateful, h1, h2, consumedOut]
  | ok r =>
    obtain ⟨s, n⟩ := r
    rw [hd] at main
    obtain ⟨h1, h2, _⟩ := main
    cases c
    · simp [writerDecodeStateful, noConsumed, h1, h2, Except.map]
    · simp [writerDecodeStateful, h1, h2]

/-! ## `unicode_decode_utf8` -/

theorem contByte_ge {x : Nat} (h : ¬(!isCont x) = true) : 128 ≤ x :=
  isCont_ge (by simpa using h)

theorem step2_val {a b c n : Nat} (h : step2 a b = .char c n) :
    c = a * 64 + b - (0xC0 * 64 + 0x80) ∧ 128 ≤ b := by
  unfold step2 at h
  by_cases h1 : (!isCont b) = true
  · rw [if_pos h1] at h
    cases h
  · rw [if_neg h1] at h
    exact ⟨(U8.char.inj h).1.symm, contByte_ge h1⟩

theorem step3_val {a b c d n : Nat} (h : step3 a b c = .char d n) :
    d = a * 4096 + b * 64 + c - (0xE0 * 4096 + 0x80 * 64 + 0x80) ∧ 128 ≤ b ∧ 128 ≤ c ∧
      (a = 0xE0 → 0xA0 ≤ b) := by
  unfold step3 at h
  by_cases h1 : (!isCont b) = true
  · rw [if_pos h1] at h
    cases h
  rw [if_neg h1] at h
  by_cases h2 : (a == 0xE0 && decide (b < 0xA0)) = true
  · rw [if_pos h2] at h
    cases h
  rw [if_neg h2] at h
  by_cases h3 : (a != 0xE0 && a == 0xED && decide (b ≥ 0xA0)) = true
  · rw [if_pos h3] at h
    cases h
  rw [if_neg h3] at h
  by_cases h4 : (!isCont c) = true
  · rw [if_pos h4] at h
    cases h
  rw [if_neg h4] at h
  refine ⟨(U8.char.inj h).1.symm, contByte_ge h1, contByte_ge h4, ?_⟩
  intro e
  subst e
  simpa using h2

theorem step4_val {a b c d e n : Nat} (h : step4 a b c d = .char e n) :
    e = a * 262144 + b * 4096 + c * 64 + d - (0xF0 * 262144 + 0x80 * 4096 + 0x80 * 64 + 0x80) ∧
      128 ≤ b ∧ 128 ≤ c ∧ 128 ≤ d ∧ (a = 0xF0 → 0x90 ≤ b) := by
  unfold step4 at h
  by_cases h1 : (!isCont b) = true
  · rw [if_pos h1] at h
    cases h
  rw [if_neg h1] at h
  by_cases h2 : (a == 0xF0 && decide (b < 0x90)) = true
  · rw [if_pos h2] at h
    cases h
  rw [if_neg h2] at h
  by_cases h3 : (a != 0xF0 && a == 0xF4 && decide (b ≥ 0x90)) = true
  · rw [if_pos h3] at h
    cases h
  rw [if_neg h3] at h
  by_cases h4 : (!isCont c) = true
  · rw [if_pos h4] at h
    cases h
  rw [if_neg h4] at h
  by_cases h5 : (!isCont d) = true
  · rw [if_pos h5] at h
    cases h
  rw [if_neg h5] at h
  refine ⟨(U8.char.inj h).1.symm, contByte_ge h1, contByte_ge h4, contByte_ge h5, ?_⟩
  intro q
  subst q
  simpa using h2

theorem need_ge1 {c : Nat} (h : 128 ≤ c) : 255 ≤ capNeed c := by
  unfold capNeed kindOfMax
  repeat' split
  all_goals (try simp only [capOf])
  all_goals omega

theorem need_ge2 {c : Nat} (h : 256 ≤ c) : 65535 ≤ capNeed c := by
  unfold capNeed kindOfMax
  repeat' split
  all_goals (try simp only [capOf])
  all_goals omega

theorem need_ge3 {c : Nat} (h : 65536 ≤ c) : 0x10ffff ≤ capNeed c := by
  unfold capNeed kindOfMax
  repeat' split
  all_goals (try simp only [capOf])
  all_goals omega

/-- What the first byte promises about the character it starts. This is why the guess of
`unicode_decode_utf8` is never too wide: `0xC4` is where two bytes stop fitting in Latin-1, and `0xF0`
is where three bytes stop being enough. -/
theorem lead_need {ch : Nat} {t : List Nat} {c n : Nat} (hs : utf8Step (ch :: t) = .char c n)
    (h2 : 0xc2 ≤ ch) : leadCap ch ≤ capNeed c := by
  have lo : (ch < 0xc4 → 128 ≤ c) ∧ (0xc4 ≤ ch → ch < 0xf0 → 256 ≤ c) ∧ (0xf0 ≤ ch → 65536 ≤ c) := by
    simp only [utf8Step] at hs
    rw [if_neg (by omega)] at hs
    by_cases h3 : ch < 0xE0
    · rw [if_pos h3, if_neg (by omega)] at hs
      cases t with
      | nil => cases hs
      | cons x r =>
        obtain ⟨e, hx⟩ := step2_val hs
        omega
    rw [if_neg h3] at hs
    by_cases h4 : ch < 0xF0
    · rw [if_pos h4] at hs
      cases t with
      | nil => cases hs
      | cons x r =>
        cases r with
        | nil => exact (ite_char2 hs).elim
        | cons y u =>
          obtain ⟨e, hx, hy, h0⟩ := step3_val hs
          by_cases q : ch = 0xE0
          · have := h0 q
            omega
          · omega
    rw [if_neg h4] at hs
    by_cases h5 : ch < 0xF5
    · rw [if_pos h5] at hs
      cases t with
      | nil => cases hs
      | cons x r =>
        cases r with
        | nil => exact (ite_char2 hs).elim
        | cons y u =>
          cases u with
          | nil => exact (ite3_char hs).elim
          | cons z v =>
            obtain ⟨e, hx, hy, hz, h0⟩ := step4_val hs
            by_cases q : ch = 0xF0
            · have := h0 q
              omega
            · omega
    · rw [if_neg h5] at hs
      cases hs
  unfold leadCap
  split
  · next q => exact need_ge1 (lo.1 q)
  · next q =>
    split
    · next r => exact need_ge2 (lo.2.1 (by omega) r)
    · next r => exact need_ge3 (lo.2.2 (by omega))

/-- What strict decoding wrote stays: it never rewinds. -/
theorem strict_keeps {x : Nat} : ∀ (f : Nat) (input : Bytes) (hist : List DecView) (pos : Nat)
    (rest : List Nat) (out : Str), x ∈ out →
    x ∈ (utf8WriterLoopX (.std .strict) false f input hist pos rest out).1 := by
  intro f
  induction f with
  | zero => intro input hist pos rest out h; exact h
  | succ f ih =>
    intro input hist pos rest out h
    cases rest with
    | nil => exact h
    | cons b0 tl =>
      simp only [utf8WriterLoopX]
      cases hs : utf8Step (b0 :: tl) with
      | char c n => exact ih _ _ _ _ _ (List.mem_append_left _ h)
      | stop => exact h
      | err k =>
        rcases k with _ | _ | k
        all_goals first
          | exact h
          | (simp [handlerStep, decodeHandlerCall]; exact h)

/-- A strict decode that got past a byte got a character from it. -/
theorem strict_head {f : Nat} {input : Bytes} {hist : List DecView} {pos : Nat} {ch : Nat}
    {tl : List Nat} {out s : Str} {n : Nat}
    (hw : utf8WriterLoopX (.std .strict) false (f + 1) input hist pos (ch :: tl) out = (s, .ok n)) :
    ∃ c k, utf8Step (ch :: tl) = .char c k ∧ c ∈ s := by
  simp only [utf8WriterLoopX] at hw
  cases hs : utf8Step (ch :: tl) with
  | char c k =>
    rw [hs] at hw
    refine ⟨c, k, rfl, ?_⟩
    have := strict_keeps (x := c) f input hist (pos + k) ((ch :: tl).drop k) (out ++ [c])
      (List.mem_append_right _ (List.mem_singleton.2 rfl))
    have hw' : utf8WriterLoopX (.std .strict) false f input hist (pos + k) ((ch :: tl).drop k)
        (out ++ [c]) = (s, .ok n) := hw
    rw [hw'] at this
    exact this
  | stop =>
    rw [hs] at hw
    simp [handlerStep, decodeHandlerCall] at hw
  | err k =>
    rw [hs] at hw
    rcases k with _ | _ | k
    all_goals simp [handlerStep, decodeHandlerCall] at hw

theorem drop_head {b : Bytes} {k : Nat} (h : k < b.length) :
    ∃ tl, b.drop k = b.getD k 0 :: tl := by
  refine ⟨b.drop (k + 1), ?_⟩
  have : b.getD k 0 = b[k] := by simp [List.getD, h]
  rw [this]
  exact List.drop_eq_getElem_cons h

/-- From where the fast path stopped, the loop gets what it gets from the start. -/
theorem loop_from_pre (H : DH) (c : Bool) (b : Bytes) (fuel : Nat)
    (hf : (asciiPrefix b).length ≤ fuel) :
    utf8WriterLoopX H c (fuel - (asciiPrefix b).length) b [] (asciiPrefix b).length
        (b.drop (asciiPrefix b).length) (asciiPrefix b) =
      utf8WriterLoopX H c fuel b [] 0 b [] := by
  obtain ⟨hp, hb⟩ := asciiPrefix_parts b
  have h := loop_asciiX H c b [] (asciiPrefix b) hp (fuel - (asciiPrefix b).length) 0
    (b.drop (asciiPrefix b).length) []
  rw [hb] at h
  have e : (asciiPrefix b).length + (fuel - (asciiPrefix b).length) = fuel := by omega
  rw [e] at h
  simpa using h.symm

theorem cap_guess {m cap : Nat} (hc : CapValue cap) (hle : cap ≤ capNeed m) :
    prepareCap cap m = capNeed m := by
  rw [prepare_max hc]
  omega

theorem leadCap_value (ch : Nat) : CapValue (leadCap ch) := by
  unfold leadCap CapValue
  repeat' split
  all_goals omega

/-- `PyUnicode_DecodeUTF8Stateful` and `unicode_decode_utf8`, unicodeobject.c:5310-5399. The fast paths
and the guess of `maxchr` change nothing: the result is what the plain loop gives, and its kind is
the canonical kind of the text, for every handler. The guess is the part that could go wrong: a
buffer too wide stays too wide, since `_PyUnicodeWriter_Finish` does not narrow it. It is safe
because it is made only when `strict` means any error raises, so every byte that is not refused
starts the character the guess assumes.

The precondition `strict → H = .std .strict` is what `PyUnicode_DecodeUTF8Stateful` passes: errors
NULL gives `_Py_ERROR_STRICT`. `b.length < fuel` is the budget of the model. -/
def DecodeUtf8Spec : Prop :=
  ∀ (b : Bytes) (H : DH) (strict c : Bool) (fuel : Nat), b.length < fuel →
    (strict = true → H = .std .strict) →
    match utf8DecodeX b H c fuel with
    | .ok (s, n) => unicodeDecodeUtf8 b H strict c fuel = .ok ((s, canonicalKind s), n)
    | .error e => unicodeDecodeUtf8 b H strict c fuel = .error e

theorem decodeUtf8Spec_proven : DecodeUtf8Spec := by
  intro b H strict c fuel hf hs
  have t := utf8WriterLoopX_tie H c fuel b [] 0 b []
  have allAscii : (∀ x ∈ b, x < 128) →
      utf8DecodeX b H c fuel = .ok (b, b.length) ∧ canonicalKind b = .ascii := by
    intro ha
    have h := loop_asciiX H c b [] b ha (fuel - b.length - 1 + 1) 0 [] []
    have e : b.length + (fuel - b.length - 1 + 1) = fuel := by omega
    rw [e] at h
    simp only [List.append_nil, utf8WriterLoopX, List.nil_append, Nat.zero_add] at h
    rw [h] at t
    refine ⟨tied_writer_ok t, ?_⟩
    have hm : maxCharOf b ≤ 127 :=
      foldl_max_le b 0 127 (by omega) (fun x hx => by have := ha x hx; omega)
    unfold canonicalKind kindOfMax
    rw [if_pos (by omega)]
  unfold unicodeDecodeUtf8
  by_cases he : b.isEmpty = true
  · have hb : b = [] := List.isEmpty_iff.1 he
    subst hb
    rw [decodeX_nil (by simpa using hf)]
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
    obtain ⟨d, k⟩ := allAscii ha
    rw [d, ← k, h1.1]
  rw [if_neg h1]
  by_cases h2 : (asciiPrefix b).length = b.length
  · have hpb : asciiPrefix b = b := by
      obtain ⟨_, hb⟩ := asciiPrefix_parts b
      have : b.drop (asciiPrefix b).length = [] := by
        rw [h2]
        simp
      rw [this] at hb
      simpa using hb
    have ha : ∀ x ∈ b, x < 128 := by
      intro x hx
      exact asciiPrefix_lt b x (by rw [hpb]; exact hx)
    obtain ⟨d, k⟩ := allAscii ha
    dsimp only
    rw [if_pos h2, d, ← k]
  dsimp only
  rw [if_neg h2]
  have hlt : (asciiPrefix b).length < b.length := by
    have hl := congrArg List.length (asciiPrefix_parts b).2
    simp only [List.length_append, List.length_drop] at hl
    omega
  generalize hch : b.getD (asciiPrefix b).length 0 = ch
  generalize hmax : (if strict && !c && decide (ch ≥ 0xc2) then leadCap ch else 127) = maxchr
  have hcv : CapValue maxchr := by
    rw [← hmax]
    split
    · exact leadCap_value ch
    · unfold CapValue
      omega
  have hloop : utf8WriterLoopX H c (fuel - (if maxchr ≤ 255 then asciiPrefix b else []).length) b []
      (if maxchr ≤ 255 then asciiPrefix b else []).length
      (b.drop (if maxchr ≤ 255 then asciiPrefix b else []).length)
      (if maxchr ≤ 255 then asciiPrefix b else []) = utf8WriterLoopX H c fuel b [] 0 b [] := by
    split
    · exact loop_from_pre H c b fuel (by omega)
    · simp
  rw [hloop]
  cases hd : utf8DecodeX b H c fuel with
  | error e =>
    rw [show utf8DecodeLoopX H c fuel b [] 0 b [] = .error e from hd] at t
    simp only [Tied] at t
    cases hw : utf8WriterLoopX H c fuel b [] 0 b [] with
    | mk out r =>
      rw [hw] at t
      simp only at t
      subst t
      rfl
  | ok r =>
    obtain ⟨s, n⟩ := r
    rw [show utf8DecodeLoopX H c fuel b [] 0 b [] = .ok (s, n) from hd] at t
    simp only [Tied] at t
    rw [t]
    dsimp only
    have hbound : maxchr ≤ capNeed (maxCharOf s) := by
      rw [← hmax]
      split
      · next q =>
        simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at q
        obtain ⟨⟨q1, q2⟩, q3⟩ := q
        have hH := hs q1
        subst hH
        subst q2
        rw [← loop_from_pre _ _ b fuel (by omega)] at t
        obtain ⟨tl, hdr⟩ := drop_head hlt
        rw [hdr, hch] at t
        have hk : fuel - (asciiPrefix b).length = (fuel - (asciiPrefix b).length - 1) + 1 := by omega
        rw [hk] at t
        obtain ⟨d, k, hst, hmem⟩ := strict_head t
        have h1 := lead_need hst q3
        have h2 : d ≤ maxCharOf s := foldl_max_mem s 0 d hmem
        have h3 := need_mono h2
        omega
      · have := need_value (maxCharOf s)
        omega
    have hW : WInv ({ text := s, cap := prepareCap maxchr (maxCharOf s) } : UWriter) :=
      .inl (cap_guess hcv hbound)
    rw [hW.finish]

end PyLean.UnicodeObj
