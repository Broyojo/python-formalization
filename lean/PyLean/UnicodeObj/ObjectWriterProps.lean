import PyLean.UnicodeObj.ObjectWriter
import PyLean.UnicodeObj.ObjectKinds

/-!
Properties of `PyUnicodeWriter`.

`CapValue` is the type invariant of `writer->maxchar`, and every operation keeps it. `WInv` is
sharper: the capacity is exactly what the text needs. Every operation keeps that too, unless a
decode fails, and that one exception is the defect of gh-158439 on 3.14.
-/

namespace PyLean.UnicodeObj

open PyLean PyLean.Binary64

/-- The capacity a text of largest character `m` needs: `PyUnicode_New(n, max(m, 127))`. -/
def capNeed (m : Nat) : Nat := capOf (kindOfMax (max m 127))

theorem capNeed_max (a b : Nat) : capNeed (max a b) = max (capNeed a) (capNeed b) := by
  unfold capNeed kindOfMax
  repeat' split
  all_goals (try simp only [capOf] at *)
  all_goals omega

theorem prepare_need (a m : Nat) : prepareCap (capNeed a) m = capNeed (max a m) := by
  unfold prepareCap capNeed kindOfMax
  repeat' split
  all_goals (try simp only [capOf] at *)
  all_goals omega

theorem prepare_zero (m : Nat) : prepareCap 0 m = capNeed m := by
  unfold prepareCap capNeed
  exact if_pos (by omega)

theorem kind_need (m : Nat) : kindOfMax (capNeed m) = kindOfMax m := by
  unfold capNeed kindOfMax
  repeat' split
  all_goals first | rfl | (simp only [capOf] at *; omega) | omega

theorem need_eq (m : Nat) : capNeed m = capOf (kindOfMax m) := by
  unfold capNeed kindOfMax
  repeat' split
  all_goals (try simp only [capOf] at *)
  all_goals omega

theorem need_capOf (m : Nat) : capNeed (capOf (kindOfMax m)) = capNeed m := by
  unfold capNeed kindOfMax
  repeat' split
  all_goals (try simp only [capOf] at *)
  all_goals omega

theorem need_value (m : Nat) :
    capNeed m = 127 ∨ capNeed m = 255 ∨ capNeed m = 65535 ∨ capNeed m = 0x10ffff := by
  unfold capNeed kindOfMax
  repeat' split
  all_goals simp [capOf]

theorem need_mono {a b : Nat} (h : a ≤ b) : capNeed a ≤ capNeed b := by
  have e : b = max a b := by omega
  rw [e, capNeed_max]
  omega

theorem need_ascii {s : Str} (h : ∀ c ∈ s, c < 128) : capNeed (maxCharOf s) = 127 := by
  have hm : maxCharOf s ≤ 127 :=
    foldl_max_le s 0 127 (by omega) (fun c hc => by have := h c hc; omega)
  have := need_mono hm
  have e : capNeed 127 = 127 := by decide
  have := need_value (maxCharOf s)
  omega

/-- The type invariant of `writer->maxchar`: no buffer, or the limit of a kind. -/
def CapValue (c : Nat) : Prop := c = 0 ∨ c = 127 ∨ c = 255 ∨ c = 65535 ∨ c = 0x10ffff

theorem prepare_max {c : Nat} (hc : CapValue c) (m : Nat) :
    prepareCap c m = max c (capNeed m) := by
  unfold prepareCap capNeed kindOfMax
  rcases hc with rfl | rfl | rfl | rfl | rfl
  all_goals
    repeat' split
  all_goals (try simp only [capOf] at *)
  all_goals omega

theorem capValue_max {c : Nat} (hc : CapValue c) (m : Nat) : CapValue (max c (capNeed m)) := by
  have := need_value m
  unfold CapValue at *
  omega

theorem capValue_prepare {c : Nat} (hc : CapValue c) (m : Nat) : CapValue (prepareCap c m) := by
  rw [prepare_max hc]
  exact capValue_max hc m

/-- The writer after writing `s`, seen from the outside. -/
def wExpect (w : UWriter) (s : Str) : UWriter :=
  if s.isEmpty then w else { text := w.text ++ s, cap := max w.cap (capNeed (maxCharOf s)) }

theorem writeText_eq {w : UWriter} (hc : CapValue w.cap) (s : Str) :
    writeText w s = wExpect w s := by
  unfold writeText wExpect canonicalKind
  split
  · rfl
  · rw [prepare_max hc, need_capOf]

theorem writeAscii_eq {w : UWriter} (hc : CapValue w.cap) {s : Str} (hs : ∀ c ∈ s, c < 128) :
    writeAsciiText w s = wExpect w s := by
  unfold writeAsciiText wExpect
  split
  · rfl
  · rw [prepare_max hc, need_ascii hs]
    rfl

theorem take_drop_mem {s : Str} {a n c : Nat} (h : c ∈ (s.drop a).take n) : c ∈ s :=
  List.mem_of_mem_drop (List.mem_of_mem_take h)

/-- The scan of `_PyUnicodeWriter_WriteSubstring` decides nothing the kind of the slice would not:
what it skips is what fits anyway. -/
theorem writeSubstring_eq {w : UWriter} (hc : CapValue w.cap) (s : Str) {a b : Nat}
    (hab : a ≤ b) (hb : b ≤ s.length) :
    writeSubstring w s a b = wExpect w ((s.drop a).take (b - a)) := by
  unfold writeSubstring
  by_cases h0 : a = 0 ∧ b = s.length
  · rw [if_pos h0, writeText_eq hc, h0.1, h0.2]
    simp
  · rw [if_neg h0]
    by_cases hz : b - a = 0
    · rw [if_pos hz, hz]
      simp [wExpect]
    · rw [if_neg hz]
      have hlen : ((s.drop a).take (b - a)).length = b - a := by
        simp only [List.length_take, List.length_drop]
        omega
      have hne : ((s.drop a).take (b - a)).isEmpty = false := by
        cases hp : (s.drop a).take (b - a) with
        | nil => rw [hp] at hlen; simp at hlen; omega
        | cons _ _ => rfl
      unfold wExpect
      rw [hne]
      simp only [Bool.false_eq_true, if_false]
      split
      · rw [prepare_max hc]
      · next hn =>
        have hle : maxCharOf ((s.drop a).take (b - a)) ≤ maxCharOf s :=
          foldl_max_le _ 0 _ (Nat.zero_le _) (fun c hm => foldl_max_mem s 0 c (take_drop_mem hm))
        have h1 : capNeed (maxCharOf ((s.drop a).take (b - a))) ≤ w.cap := by
          have := need_mono hle
          rw [need_eq (maxCharOf s)] at this
          simp only [canonicalKind] at hn
          omega
        have h2 : capNeed w.cap = w.cap := by
          have hv := need_value (maxCharOf ((s.drop a).take (b - a)))
          rcases hc with h | h | h | h | h
          · omega
          all_goals (rw [h]; decide)
        rw [prepare_max hc, h2]
        congr 1
        omega

theorem take_all_int (s : List Nat) : s.take (s.length : Int).toNat = s := by
  simp

/-! ## The decode loop is the decoder -/

/-- A run of `utf8DecodeLoop` against a run of `utf8WriterLoop`. -/
def Tied : Py (Str × Nat) → Str × Py Nat → Prop
  | .ok (s, n), b => b = (s, .ok n)
  | .error e, b => b.2 = .error e

/-- `utf8WriterLoop` is `utf8DecodeLoop`: same text, same consumed, same exception. -/
theorem utf8WriterLoop_tie (input : Bytes) (h : ErrHandler) (consumed : Bool) :
    ∀ fuel pos rest out, Tied (utf8DecodeLoop input h consumed fuel pos rest out)
      (utf8WriterLoop input h consumed fuel pos rest out) := by
  intro fuel
  induction fuel with
  | zero => intro pos rest out; simp [utf8DecodeLoop, utf8WriterLoop, Tied]
  | succ fuel ih =>
    intro pos rest out
    cases rest with
    | nil => simp [utf8DecodeLoop, utf8WriterLoop, Tied]
    | cons b0 tl =>
      have key : ∀ (reason : String) (stopAt : Nat),
          Tied
            (match (generalizing := false) h with
              | .ignore => utf8DecodeLoop input h consumed fuel stopAt
                  ((b0 :: tl).drop (stopAt - pos)) (out ++ [])
              | .replace => utf8DecodeLoop input h consumed fuel stopAt
                  ((b0 :: tl).drop (stopAt - pos)) (out ++ [0xfffd])
              | .surrogateescape => utf8DecodeLoop input h consumed fuel stopAt
                  ((b0 :: tl).drop (stopAt - pos))
                  (out ++ ((b0 :: tl).take (stopAt - pos)).map (· + 0xdc00))
              | _ =>
                match decodeHandlerCall h "utf-8" .utf8 input pos stopAt reason with
                | .error e => .error e
                | .ok (rep, newpos) =>
                  utf8DecodeLoop input h consumed fuel newpos (input.drop newpos) (out ++ rep))
            (match (generalizing := false) h with
              | .ignore => utf8WriterLoop input h consumed fuel stopAt
                  ((b0 :: tl).drop (stopAt - pos)) (out ++ [])
              | .replace => utf8WriterLoop input h consumed fuel stopAt
                  ((b0 :: tl).drop (stopAt - pos)) (out ++ [0xfffd])
              | .surrogateescape => utf8WriterLoop input h consumed fuel stopAt
                  ((b0 :: tl).drop (stopAt - pos))
                  (out ++ ((b0 :: tl).take (stopAt - pos)).map (· + 0xdc00))
              | _ =>
                match decodeHandlerCall h "utf-8" .utf8 input pos stopAt reason with
                | .error e => (out, .error e)
                | .ok (rep, newpos) =>
                  utf8WriterLoop input h consumed fuel newpos (input.drop newpos) (out ++ rep)) := by
        intro reason stopAt
        cases h
        case ignore | replace | surrogateescape => exact ih _ _ _
        all_goals
          dsimp only
          cases hc : decodeHandlerCall _ "utf-8" .utf8 input pos stopAt reason with
          | error e => rfl
          | ok r =>
            obtain ⟨rep, newpos⟩ := r
            exact ih _ _ _
      simp only [utf8DecodeLoop, utf8WriterLoop]
      cases hs : utf8Step (b0 :: tl) with
      | char c n => exact ih _ _ _
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

/-- What each operation writes, in terms of the object-level functions. A decode is what
`bytes.decode` computes, `WriteStr` is `str()` and `WriteRepr` is `repr()`, for every object: the
fast paths for an exact `str` and an exact `int` have to come to the same thing. -/
def opText : WOp → Py Str
  | .char c =>
    if c > maxUnicode then .error (.valueError "character must be in range(0x110000)")
    else .ok [c]
  | .str o => strG reprFuel o
  | .repr none => .ok (lit "<NULL>")
  | .repr (some o) => reprG reprFuel o
  | .ascii b size => .ok (asciiBytes b size)
  | .ucs4 s size =>
    if size < 0 then .error (.valueError "size must be positive") else .ok (s.take size.toNat)
  | .wide s size =>
    match (sizedWide s size).find? (· > maxUnicode) with
    | some c => .error (wideError c)
    | none => .ok (sizedWide s size)
  | .sub o start stop =>
    match o with
    | .str s =>
      if start < 0 ∨ start > stop then .error (.valueError "invalid start argument")
      else if stop > s.length then .error (.valueError "invalid end argument")
      else .ok ((s.drop start.toNat).take (stop.toNat - start.toNat))
    | o => .error (.typeError s!"expect str, not {o.tpName}")
  | .utf8 b size => utf8Decode (sizedBytes b size) .strict
  | .decode b size h true => (utf8DecodeStateful (sizedBytes b size) h).map (·.1)
  | .decode b size h false => utf8Decode (sizedBytes b size) h

/-- What a run shows of an operation's result. -/
def Agrees (w w' : UWriter) (r : Py Nat) : Py Str → Prop
  | .ok s => w'.text = w.text ++ s ∧ ∃ n, r = .ok n
  | .error e => w'.text = w.text ∧ r = .error e

theorem writeText_text (w : UWriter) (s : Str) : (writeText w s).text = w.text ++ s := by
  unfold writeText
  split
  · next h => simp [List.isEmpty_iff.1 h]
  · rfl

theorem writeAscii_text (w : UWriter) (s : Str) : (writeAsciiText w s).text = w.text ++ s := by
  unfold writeAsciiText
  split
  · next h => simp [List.isEmpty_iff.1 h]
  · rfl

theorem writeSubstring_text (w : UWriter) (s : Str) {a b : Nat} :
    (writeSubstring w s a b).text = w.text ++ (s.drop a).take (b - a) := by
  unfold writeSubstring
  split
  · next h =>
    rw [writeText_text, h.1, h.2]
    simp
  · split
    · next h => simp [h]
    · rfl

/-- `WriteStr` either raises what `str()` raises and changes nothing, or writes what it returns. -/
theorem writeStrOp_cases (w : UWriter) (o : GObj) :
    (∃ s, strG reprFuel o = .ok s ∧
      (writeStrOp w o = (writeText w s, .ok 0) ∨
        (writeStrOp w o = (writeAsciiText w s, .ok 0) ∧ ∃ v, o = .int v))) ∨
    (∃ e, strG reprFuel o = .error e ∧ writeStrOp w o = (w, .error e)) := by
  by_cases hi : ∃ v, o = .int v
  · obtain ⟨v, rfl⟩ := hi
    have e : strG reprFuel (.int v) = longFormat v 10 false := rfl
    cases hl : longFormat v 10 false with
    | ok s => exact .inl ⟨s, by rw [e, hl], .inr ⟨by simp [writeStrOp, hl], v, rfl⟩⟩
    | error x => exact .inr ⟨x, by rw [e, hl], by simp [writeStrOp, hl]⟩
  · cases hl : strG reprFuel o with
    | ok s =>
      refine .inl ⟨s, rfl, .inl ?_⟩
      cases o with
      | str t => simp [strG] at hl; subst hl; rfl
      | int v => exact absurd ⟨v, rfl⟩ hi
      | _ => simp only [writeStrOp, hl]
    | error x =>
      refine .inr ⟨x, rfl, ?_⟩
      cases o with
      | str t => simp [strG] at hl
      | int v => exact absurd ⟨v, rfl⟩ hi
      | _ => simp only [writeStrOp, hl]

theorem writeReprOp_cases (w : UWriter) (o : GObj) :
    (∃ s, reprG reprFuel o = .ok s ∧
      (writeReprOp w (some o) = (writeText w s, .ok 0) ∨
        (writeReprOp w (some o) = (writeAsciiText w s, .ok 0) ∧ ∃ v, o = .int v))) ∨
    (∃ e, reprG reprFuel o = .error e ∧ writeReprOp w (some o) = (w, .error e)) := by
  by_cases hi : ∃ v, o = .int v
  · obtain ⟨v, rfl⟩ := hi
    have e : reprG reprFuel (.int v) = longFormat v 10 false := rfl
    cases hl : longFormat v 10 false with
    | ok s => exact .inl ⟨s, by rw [e, hl], .inr ⟨by simp [writeReprOp, hl], v, rfl⟩⟩
    | error x => exact .inr ⟨x, by rw [e, hl], by simp [writeReprOp, hl]⟩
  · cases hl : reprG reprFuel o with
    | ok s =>
      refine .inl ⟨s, rfl, .inl ?_⟩
      cases o with
      | int v => exact absurd ⟨v, rfl⟩ hi
      | _ => simp only [writeReprOp, hl]
    | error x =>
      refine .inr ⟨x, rfl, ?_⟩
      cases o with
      | int v => exact absurd ⟨v, rfl⟩ hi
      | _ => simp only [writeReprOp, hl]

/-- `find_maxchar_surrogates`: the first character out of range raises, whatever comes before it,
and otherwise it computes the maximum. -/
theorem findMax_spec (t : Str) (m : Nat) (hm : m ≤ maxUnicode) :
    findMaxcharSurrogates t m =
      match t.find? (· > maxUnicode) with
      | some c => .error (wideError c)
      | none => .ok (t.foldl max m) := by
  induction t generalizing m with
  | nil => rfl
  | cons ch t ih =>
    simp only [findMaxcharSurrogates, List.find?_cons, List.foldl_cons]
    by_cases h1 : ch > maxUnicode
    · have h2 : ch > m := by omega
      simp [h1, h2]
    · simp only [h1, decide_false, if_false]
      by_cases h2 : ch > m
      · rw [if_pos h2, ih ch (by omega)]
        have : max m ch = ch := by omega
        rw [this]
      · rw [if_neg h2, ih m hm]
        have : max m ch = m := by omega
        rw [this]

/-- The ASCII bytes at the head of the input are decoded one by one, as the fast path does at once. -/
theorem loop_ascii (input : Bytes) (h : ErrHandler) (c : Bool) (pre : Bytes)
    (hp : ∀ x ∈ pre, x < 128) (fuel pos : Nat) (rest : List Nat) (out : Str) :
    utf8WriterLoop input h c (pre.length + fuel) pos (pre ++ rest) out =
      utf8WriterLoop input h c fuel (pos + pre.length) rest (out ++ pre) := by
  induction pre generalizing pos out with
  | nil => simp
  | cons x t ih =>
    have hx := hp x List.mem_cons_self
    have e : (x :: t).length + fuel = (t.length + fuel) + 1 := by simp; omega
    have hs : utf8Step (x :: (t ++ rest)) = .char x 1 := by
      simp only [utf8Step]
      rw [if_pos hx]
    rw [e, List.cons_append]
    simp only [utf8WriterLoop, hs, List.drop_succ_cons, List.drop_zero]
    rw [ih (fun y hy => hp y (List.mem_cons_of_mem _ hy))]
    have e2 : pos + 1 + t.length = pos + (x :: t).length := by simp; omega
    rw [e2]
    simp

/-- The decode with no fast path. -/
def decodeWhole (w : UWriter) (b : Bytes) (h : ErrHandler) (consumed : Bool) : UWriter × Py Nat :=
  if b.isEmpty then (w, .ok 0) else decodeRest w (prepareCap w.cap 127) b [] h consumed

theorem asciiPrefix_lt (b : Bytes) : ∀ x ∈ asciiPrefix b, x < 128 := by
  unfold asciiPrefix
  induction b with
  | nil => simp
  | cons a t ih =>
    simp only [List.takeWhile_cons]
    split
    · next h =>
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · simpa using h
      · exact ih x hx
    · simp

theorem asciiPrefix_parts (b : Bytes) :
    (∀ x ∈ asciiPrefix b, x < 128) ∧ asciiPrefix b ++ b.drop (asciiPrefix b).length = b := by
  have hs : asciiPrefix b ++ b.dropWhile (· < 128) = b := List.takeWhile_append_dropWhile
  have hd : b.drop (asciiPrefix b).length = b.dropWhile (· < 128) := by
    conv => lhs; arg 2; rw [← hs]
    simp
  refine ⟨asciiPrefix_lt b, ?_⟩
  rw [hd]
  exact hs

theorem prepare_ge (c : Nat) : 127 ≤ prepareCap c 127 := by
  unfold prepareCap
  split
  · decide
  · omega

/-- `ascii_decode` is an optimisation: from the buffer's point of view the fast path, finished or
not, is the loop. -/
theorem decodeWriter_whole (w : UWriter) (b : Bytes) (h : ErrHandler) (c : Bool) :
    decodeWriter w b h c = decodeWhole w b h c := by
  unfold decodeWriter decodeWhole
  split
  · rfl
  · dsimp only
    split
    · obtain ⟨hp, hb⟩ := asciiPrefix_parts b
      have hl : (asciiPrefix b).length + (b.drop (asciiPrefix b).length).length = b.length := by
        have := congrArg List.length hb
        simpa using this
      have hle : (asciiPrefix b).length ≤ b.length := by omega
      have hrest : ∀ fuel,
          utf8WriterLoop b h c ((asciiPrefix b).length + fuel) 0 b [] =
            utf8WriterLoop b h c fuel (asciiPrefix b).length (b.drop (asciiPrefix b).length)
              (asciiPrefix b) := by
        intro fuel
        have := loop_ascii b h c (asciiPrefix b) hp fuel 0 (b.drop (asciiPrefix b).length) []
        rw [hb] at this
        simpa using this
      split
      · next he =>
        have hnil : b.drop (asciiPrefix b).length = [] := by
          apply List.eq_nil_of_length_eq_zero
          omega
        have heq : asciiPrefix b = b := by
          rw [hnil] at hb
          simpa using hb
        have hl1 := hrest 1
        rw [hnil, heq] at hl1
        simp only [utf8WriterLoop] at hl1
        simp only [decodeRest, List.length_nil, Nat.sub_zero, List.drop_zero]
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
      · have e : b.length + 1 = (asciiPrefix b).length + (b.length + 1 - (asciiPrefix b).length) := by
          omega
        simp only [decodeRest, List.length_nil, Nat.sub_zero, List.drop_zero]
        rw [← hrest, ← e]
    · rfl

theorem decodeWriter_ok {b : Bytes} {h : ErrHandler} {c : Bool} {s : Str} {n : Nat}
    (hd : utf8DecodeLoop b h c (b.length + 1) 0 b [] = .ok (s, n)) (w : UWriter) :
    decodeWriter w b h c =
      (if b.isEmpty then w
        else { text := w.text ++ s, cap := prepareCap (prepareCap w.cap 127) (maxCharOf s) },
       .ok n) := by
  rw [decodeWriter_whole]
  cases b with
  | nil =>
    simp only [utf8DecodeLoop] at hd
    injection hd with hd
    injection hd with h1 h2
    subst h2
    simp [decodeWhole]
  | cons x xs =>
    have t := utf8WriterLoop_tie (x :: xs) h c ((x :: xs).length + 1) 0 (x :: xs) []
    rw [hd] at t
    simp only [Tied] at t
    simp only [decodeWhole, decodeRest, List.length_nil, Nat.sub_zero, List.drop_zero, t,
      List.isEmpty_cons, Bool.false_eq_true, if_false]

theorem decodeWriter_err {b : Bytes} {h : ErrHandler} {c : Bool} {e : PyExc}
    (hd : utf8DecodeLoop b h c (b.length + 1) 0 b [] = .error e) (w : UWriter) :
    (decodeWriter w b h c).1.text = w.text ∧ (decodeWriter w b h c).2 = .error e := by
  have hne : b.isEmpty = false := by
    cases b with
    | nil => simp [utf8DecodeLoop] at hd
    | cons _ _ => rfl
  have t := utf8WriterLoop_tie b h c (b.length + 1) 0 b []
  rw [hd] at t
  simp only [Tied] at t
  rw [decodeWriter_whole]
  cases hw : utf8WriterLoop b h c (b.length + 1) 0 b [] with
  | mk out r =>
    rw [hw] at t
    simp only at t
    subst t
    simp only [decodeWhole, decodeRest, hne, Bool.false_eq_true, if_false, List.length_nil,
      Nat.sub_zero, List.drop_zero, hw]
    constructor <;> first | rfl | trivial

theorem decode_agrees (w : UWriter) (b : Bytes) (h : ErrHandler) (c : Bool) :
    Agrees w (decodeWriter w b h c).1 (decodeWriter w b h c).2
      ((utf8DecodeLoop b h c (b.length + 1) 0 b []).map (·.1)) := by
  cases hd : utf8DecodeLoop b h c (b.length + 1) 0 b [] with
  | error e => exact decodeWriter_err hd w
  | ok r =>
    obtain ⟨s, n⟩ := r
    rw [decodeWriter_ok hd]
    refine ⟨?_, n, rfl⟩
    split
    · next he =>
      have : b = [] := List.isEmpty_iff.1 he
      subst this
      simp only [utf8DecodeLoop] at hd
      injection hd with hd
      injection hd with h1 h2
      simp [← h1]
    · rfl

theorem utf8Decode_map (b : Bytes) (h : ErrHandler) :
    utf8Decode b h = (utf8DecodeLoop b h false (b.length + 1) 0 b []).map (·.1) := by
  simp only [utf8Decode]
  cases utf8DecodeLoop b h false (b.length + 1) 0 b [] <;> rfl

theorem noConsumed_agrees {w : UWriter} {r : UWriter × Py Nat} {t : Py Str}
    (h : Agrees w r.1 r.2 t) : Agrees w (noConsumed r).1 (noConsumed r).2 t := by
  cases t with
  | ok s =>
    obtain ⟨h1, n, hn⟩ := h
    exact ⟨h1, 0, by simp [noConsumed, hn, Except.map]⟩
  | error e =>
    obtain ⟨h1, hn⟩ := h
    exact ⟨h1, by simp [noConsumed, hn, Except.map]⟩

/-- Each operation writes `opText` or raises what it raises, and a failure writes nothing. -/
theorem applyOp_agrees (w : UWriter) (op : WOp) :
    Agrees w (applyOp w op).1 (applyOp w op).2 (opText op) := by
  cases op with
  | char c =>
    simp only [applyOp, opText]
    by_cases h : c > maxUnicode
    · simp only [if_pos h]
      exact ⟨rfl, rfl⟩
    · simp only [if_neg h]
      exact ⟨rfl, 0, rfl⟩
  | str o =>
    simp only [applyOp, opText]
    rcases writeStrOp_cases w o with ⟨s, hs, hw | ⟨hw, _⟩⟩ | ⟨e, he, hw⟩
    · rw [hs, hw]
      exact ⟨writeText_text w s, 0, rfl⟩
    · rw [hs, hw]
      exact ⟨writeAscii_text w s, 0, rfl⟩
    · rw [he, hw]
      exact ⟨rfl, rfl⟩
  | repr o =>
    cases o with
    | none => exact ⟨writeAscii_text w _, 0, rfl⟩
    | some o =>
      simp only [applyOp, opText]
      rcases writeReprOp_cases w o with ⟨s, hs, hw | ⟨hw, _⟩⟩ | ⟨e, he, hw⟩
      · rw [hs, hw]
        exact ⟨writeText_text w s, 0, rfl⟩
      · rw [hs, hw]
        exact ⟨writeAscii_text w s, 0, rfl⟩
      · rw [he, hw]
        exact ⟨rfl, rfl⟩
  | ascii b size => exact ⟨writeAscii_text w _, 0, rfl⟩
  | ucs4 s size =>
    simp only [applyOp, opText, writeUCS4]
    by_cases h : size < 0
    · simp only [if_pos h]
      exact ⟨rfl, rfl⟩
    · simp only [if_neg h]
      split
      · next he => exact ⟨by simp [List.isEmpty_iff.1 he], 0, rfl⟩
      · exact ⟨rfl, 0, rfl⟩
  | wide s size =>
    simp only [applyOp, opText, writeWide]
    cases hf : (sizedWide s size).find? (· > maxUnicode) with
    | none =>
      split
      · next he => exact ⟨by simp [List.isEmpty_iff.1 he], 0, rfl⟩
      · rw [findMax_spec _ 0 (by simp [maxUnicode]), hf]
        exact ⟨rfl, 0, rfl⟩
    | some c =>
      split
      · next he =>
        rw [List.isEmpty_iff.1 he] at hf
        simp at hf
      · rw [findMax_spec _ 0 (by simp [maxUnicode]), hf]
        exact ⟨rfl, rfl⟩
  | sub o start stop =>
    simp only [applyOp, opText, writeSubOp]
    cases o with
    | str s =>
      dsimp only
      split
      · exact ⟨rfl, rfl⟩
      · split
        · exact ⟨rfl, rfl⟩
        · exact ⟨writeSubstring_text w s, 0, rfl⟩
    | _ => exact ⟨rfl, rfl⟩
  | utf8 b size =>
    simp only [applyOp, opText, utf8Decode_map]
    exact noConsumed_agrees (decode_agrees _ _ _ _)
  | decode b size h consumed =>
    cases consumed with
    | true => exact decode_agrees _ _ _ _
    | false =>
      simp only [applyOp, opText, utf8Decode_map]
      exact noConsumed_agrees (decode_agrees _ _ _ _)

/-- What an operation contributes to the text. -/
def written (op : WOp) : Str :=
  match opText op with
  | .ok s => s
  | .error _ => []

/-- Whether an operation raised, and what. -/
def okShape {α : Type} (r : Py α) : Py Unit := r.map fun _ => ()

theorem applyOp_shape (w : UWriter) (op : WOp) :
    (applyOp w op).1.text = w.text ++ written op ∧
      okShape (applyOp w op).2 = okShape (opText op) := by
  have h := applyOp_agrees w op
  unfold written
  cases ht : opText op with
  | ok s =>
    rw [ht] at h
    obtain ⟨h1, n, hn⟩ := h
    exact ⟨h1, by simp [okShape, hn, Except.map]⟩
  | error e =>
    rw [ht] at h
    obtain ⟨h1, hn⟩ := h
    exact ⟨by simp [h1], by simp [okShape, hn, Except.map]⟩

/-- The text of any script, from any writer, is what the successful operations wrote, in order, and
each operation returns what the object-level function returns. So a failed operation leaves no
characters, whatever it had got through: the put back of `pos` works. No precondition: an exact
`str` or `int` goes through a fast path, and the theorem says that comes to `str()` and `repr()`. -/
def WriterText : Prop := ∀ (w : UWriter) (ops : List WOp),
  (runOps w ops).1.text = w.text ++ ops.flatMap written ∧
    (runOps w ops).2.map okShape = ops.map fun op => okShape (opText op)

theorem writerText_proven : WriterText := by
  intro w ops
  induction ops generalizing w with
  | nil => simp [runOps]
  | cons op t ih =>
    have h := applyOp_shape w op
    have i := ih (applyOp w op).1
    simp only [runOps, List.flatMap_cons, List.map_cons]
    rw [i.1, h.1, i.2, h.2]
    simp

/-- `*consumed`, and the text, are what the stateful decoder gives, for every handler. -/
def WriterConsumed : Prop := ∀ (w : UWriter) (b : Bytes) (size : Int) (h : ErrHandler) (s : Str)
    (n : Nat), utf8DecodeStateful (sizedBytes b size) h = .ok (s, n) →
  (applyOp w (.decode b size h true)).1.text = w.text ++ s ∧
    (applyOp w (.decode b size h true)).2 = .ok n

theorem writerConsumed_proven : WriterConsumed := by
  intro w b size h s n hd
  simp only [utf8DecodeStateful] at hd
  have ha := decode_agrees w (sizedBytes b size) h true
  rw [hd] at ha
  refine ⟨ha.1, ?_⟩
  simp only [applyOp]
  rw [decodeWriter_ok hd]

/-- The failure half: when the stateful decoder raises, for any handler, the writer raises the same
exception, no text stays, and `*consumed` is 0, whatever the decoder had got through. So a caller
that retries from `*consumed` starts from the beginning of what it passed. -/
def WriterConsumedFailure : Prop :=
  ∀ (w : UWriter) (b : Bytes) (size : Int) (h : ErrHandler) (e : PyExc),
    utf8DecodeStateful (sizedBytes b size) h = .error e →
    (applyOp w (.decode b size h true)).1.text = w.text ∧
      (applyOp w (.decode b size h true)).2 = .error e ∧
      consumedOut (applyOp w (.decode b size h true)).2 = 0

theorem writerConsumedFailure_proven : WriterConsumedFailure := by
  intro w b size h e hd
  simp only [utf8DecodeStateful] at hd
  have r := decodeWriter_err hd w
  simp only [applyOp]
  rw [r.2]
  exact ⟨r.1, rfl, rfl⟩

/-- A writer's capacity stays the limit of a kind, whatever happens: the premise of the theorems
below holds of every writer, including one a failed decode left too wide. -/
def WriterCapValue : Prop := ∀ (w : UWriter) (op : WOp), CapValue w.cap →
  CapValue (applyOp w op).1.cap

theorem writeText_cap {w : UWriter} (hc : CapValue w.cap) (s : Str) :
    CapValue (writeText w s).cap := by
  unfold writeText
  split
  · exact hc
  · exact capValue_prepare hc _

theorem writeAscii_cap {w : UWriter} (hc : CapValue w.cap) (s : Str) :
    CapValue (writeAsciiText w s).cap := by
  unfold writeAsciiText
  split
  · exact hc
  · exact capValue_prepare hc _

theorem writeSubstring_cap {w : UWriter} (hc : CapValue w.cap) (s : Str) (a b : Nat) :
    CapValue (writeSubstring w s a b).cap := by
  unfold writeSubstring
  split
  · exact writeText_cap hc s
  · split
    · exact hc
    · exact capValue_prepare hc _

theorem decodeWriter_cap {w : UWriter} (hc : CapValue w.cap) (b : Bytes) (h : ErrHandler)
    (c : Bool) : CapValue (decodeWriter w b h c).1.cap := by
  rw [decodeWriter_whole]
  unfold decodeWhole decodeRest
  split
  · exact hc
  · simp only [List.length_nil, Nat.sub_zero, List.drop_zero]
    cases hw : utf8WriterLoop b h c (b.length + 1) 0 b [] with
    | mk out r =>
      cases r with
      | ok n => exact capValue_prepare (capValue_prepare hc _) _
      | error e => exact capValue_prepare (capValue_prepare hc _) _

theorem writerCapValue_proven : WriterCapValue := by
  intro w op hc
  cases op with
  | char c =>
    simp only [applyOp]
    split
    · exact hc
    · exact capValue_prepare hc _
  | str o =>
    simp only [applyOp]
    rcases writeStrOp_cases w o with ⟨s, _, hw | ⟨hw, _⟩⟩ | ⟨e, _, hw⟩
    · rw [hw]; exact writeText_cap hc s
    · rw [hw]; exact writeAscii_cap hc s
    · rw [hw]; exact hc
  | repr o =>
    cases o with
    | none => exact writeAscii_cap hc _
    | some o =>
      simp only [applyOp]
      rcases writeReprOp_cases w o with ⟨s, _, hw | ⟨hw, _⟩⟩ | ⟨e, _, hw⟩
      · rw [hw]; exact writeText_cap hc s
      · rw [hw]; exact writeAscii_cap hc s
      · rw [hw]; exact hc
  | ascii b size => exact writeAscii_cap hc _
  | ucs4 s size =>
    simp only [applyOp, writeUCS4]
    split
    · exact hc
    · split
      · exact hc
      · exact capValue_prepare hc _
  | wide s size =>
    simp only [applyOp, writeWide]
    split
    · exact hc
    · split
      · exact hc
      · exact capValue_prepare hc _
  | sub o start stop =>
    simp only [applyOp, writeSubOp]
    cases o with
    | str s =>
      dsimp only
      split
      · exact hc
      · split
        · exact hc
        · exact writeSubstring_cap hc s _ _
    | _ => exact hc
  | utf8 b size => exact decodeWriter_cap hc _ _ _
  | decode b size h c => cases c <;> exact decodeWriter_cap hc _ _ _

/-! ## The canonical kind -/

/-- The invariant: the capacity is what the text needs, or the writer has no buffer yet. -/
def WInv (w : UWriter) : Prop :=
  w.cap = capNeed (maxCharOf w.text) ∨ (w.cap = 0 ∧ w.text = [])

theorem WInv.capValue {w : UWriter} (h : WInv w) : CapValue w.cap := by
  have hv := need_value (maxCharOf w.text)
  unfold CapValue
  rcases h with h | ⟨h, _⟩ <;> omega

theorem need_empty : capNeed (maxCharOf []) = 127 := by decide

theorem WInv.expect {w : UWriter} (h : WInv w) (s : Str) : WInv (wExpect w s) := by
  unfold wExpect
  split
  · exact h
  · left
    show max w.cap (capNeed (maxCharOf s)) = capNeed (maxCharOf (w.text ++ s))
    rw [maxCharOf_append, capNeed_max]
    rcases h with h | ⟨h, ht⟩
    · rw [h]
    · have := need_value (maxCharOf s)
      rw [h, ht, need_empty]
      omega

/-- In the invariant, `Finish` gives the canonical kind. -/
theorem WInv.finish {w : UWriter} (h : WInv w) : w.finish = (w.text, canonicalKind w.text) := by
  have hc : w.text ≠ [] → w.cap = capNeed (maxCharOf w.text) := fun hne => by
    rcases h with h | ⟨_, h⟩
    · exact h
    · exact absurd h hne
  unfold UWriter.finish canonicalKind
  cases ht : w.text with
  | nil => simp [maxCharOf, kindOfMax]
  | cons c t =>
    have hk := hc (by simp [ht])
    rw [ht] at hk
    cases t with
    | nil =>
      have e : maxCharOf [c] = c := by simp [maxCharOf]
      rw [e] at hk ⊢
      dsimp only
      split
      · rfl
      · rw [hk, kind_need]
    | cons d r =>
      dsimp only
      rw [hk, kind_need]

theorem natDigits_ascii (fuel n : Nat) (acc : Str) (h : ∀ c ∈ acc, c < 128) :
    ∀ c ∈ natDigits 10 fuel n acc, c < 128 := by
  induction fuel generalizing n acc with
  | zero => simpa [natDigits] using h
  | succ fuel ih =>
    have hd : hexLower (n % 10) < 128 := by
      have : n % 10 < 10 := Nat.mod_lt _ (by omega)
      simp only [hexLower]
      split <;> omega
    have hc : ∀ c ∈ hexLower (n % 10) :: acc, c < 128 := by
      intro c hm
      rcases List.mem_cons.1 hm with rfl | hm
      · exact hd
      · exact h c hm
    simp only [natDigits]
    split
    · exact hc
    · exact ih _ _ hc

/-- The text of an `int`, which is why `_PyLong_FormatWriter` can ask for no more than ASCII. -/
theorem longFormat_ascii {v : Int} {s : Str} (h : longFormat v 10 false = .ok s) :
    ∀ c ∈ s, c < 128 := by
  simp only [longFormat] at h
  split at h
  · simp at h
  · have hd := natDigits_ascii (v.natAbs + 1) v.natAbs [] (by simp)
    simp only [Except.ok.injEq] at h
    subst h
    intro c hm
    simp only [Bool.not_false, if_true, List.append_nil, List.mem_append] at hm
    rcases hm with hm | hm
    · split at hm
      · simp at hm
        omega
      · simp at hm
    · exact hd c hm

theorem write_char_eq {w : UWriter} (hc : CapValue w.cap) (c : Nat) :
    ({ text := w.text ++ [c], cap := prepareCap w.cap c } : UWriter) = wExpect w [c] := by
  have e : maxCharOf [c] = c := by simp [maxCharOf]
  simp [wExpect, e, prepare_max hc]

theorem write_part_eq {w : UWriter} (hc : CapValue w.cap) {t : Str} (ht : ¬t.isEmpty = true) :
    ({ text := w.text ++ t, cap := prepareCap w.cap (maxCharOf t) } : UWriter) = wExpect w t := by
  simp [wExpect, ht, prepare_max hc]

theorem foldl_is_maxChar (t : Str) : t.foldl max 0 = maxCharOf t := rfl

/-- The characters of a decode, once it succeeded, decide the capacity like any other write. -/
theorem decode_inv {w : UWriter} (hI : WInv w) {b : Bytes} {h : ErrHandler} {c : Bool} {s : Str}
    {n : Nat} (hd : utf8DecodeLoop b h c (b.length + 1) 0 b [] = .ok (s, n)) :
    WInv (decodeWriter w b h c).1 := by
  have hc := hI.capValue
  rw [decodeWriter_ok hd]
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

/-- The writes that return a failure and cannot have widened anything before it. -/
def WOp.isDecode : WOp → Bool
  | .utf8 .. | .decode .. => true
  | _ => false

/-- The documented precondition of `WriteASCII`. -/
def WOp.valid : WOp → Prop
  | .ascii b size => ∀ c ∈ asciiBytes b size, c < 128
  | _ => True

theorem map_ok {α β : Type} {r : Py α} {f : α → β} {s : β} (h : r.map f = .ok s) :
    ∃ a, r = .ok a ∧ f a = s := by
  cases r with
  | error e => simp [Except.map] at h
  | ok a =>
    simp only [Except.map, Except.ok.injEq] at h
    exact ⟨a, rfl, h⟩

theorem applyOp_inv {w : UWriter} (hI : WInv w) {op : WOp} (hv : op.valid)
    (hd : op.isDecode = true → ∃ s, opText op = .ok s) : WInv (applyOp w op).1 := by
  have hc := hI.capValue
  cases op with
  | char c =>
    simp only [applyOp]
    split
    · exact hI
    · dsimp only
      rw [write_char_eq hc]
      exact hI.expect _
  | str o =>
    simp only [applyOp]
    rcases writeStrOp_cases w o with ⟨s, hs, hw | ⟨hw, v, rfl⟩⟩ | ⟨e, _, hw⟩
    · rw [hw]
      dsimp only
      rw [writeText_eq hc]
      exact hI.expect s
    · rw [hw]
      dsimp only
      have : longFormat v 10 false = .ok s := hs
      rw [writeAscii_eq hc (longFormat_ascii this)]
      exact hI.expect s
    · rw [hw]
      exact hI
  | repr o =>
    cases o with
    | none =>
      have e : ∀ c ∈ lit "<NULL>", c < 128 := by decide
      show WInv (writeAsciiText w (lit "<NULL>"))
      rw [writeAscii_eq hc e]
      exact hI.expect _
    | some o =>
      simp only [applyOp]
      rcases writeReprOp_cases w o with ⟨s, hs, hw | ⟨hw, v, rfl⟩⟩ | ⟨e, _, hw⟩
      · rw [hw]
        dsimp only
        rw [writeText_eq hc]
        exact hI.expect s
      · rw [hw]
        dsimp only
        have : longFormat v 10 false = .ok s := hs
        rw [writeAscii_eq hc (longFormat_ascii this)]
        exact hI.expect s
      · rw [hw]
        exact hI
  | ascii b size =>
    show WInv (writeAsciiText w (asciiBytes b size))
    rw [writeAscii_eq hc hv]
    exact hI.expect _
  | ucs4 s size =>
    simp only [applyOp, writeUCS4]
    split
    · exact hI
    · split
      · exact hI
      · next ht =>
        rw [write_part_eq hc ht]
        exact hI.expect _
  | wide s size =>
    simp only [applyOp, writeWide]
    split
    · exact hI
    · next ht =>
      rw [findMax_spec _ 0 (by simp [maxUnicode])]
      cases hf : (sizedWide s size).find? (· > maxUnicode) with
      | some c => exact hI
      | none =>
        dsimp only
        rw [foldl_is_maxChar, write_part_eq hc ht]
        exact hI.expect _
  | sub o start stop =>
    simp only [applyOp, writeSubOp]
    cases o with
    | str s =>
      dsimp only
      split
      · exact hI
      · next h1 =>
        split
        · exact hI
        · next h2 =>
          dsimp only
          rw [writeSubstring_eq hc s (by omega) (by omega)]
          exact hI.expect _
    | _ => exact hI
  | utf8 b size =>
    obtain ⟨s, hs⟩ := hd rfl
    simp only [opText, utf8Decode_map] at hs
    obtain ⟨⟨s', n⟩, hl, _⟩ := map_ok hs
    exact decode_inv hI hl
  | decode b size h c =>
    obtain ⟨s, hs⟩ := hd rfl
    cases c with
    | true =>
      simp only [opText, utf8DecodeStateful] at hs
      obtain ⟨⟨s', n⟩, hl, _⟩ := map_ok hs
      exact decode_inv hI hl
    | false =>
      simp only [opText, utf8Decode_map] at hs
      obtain ⟨⟨s', n⟩, hl, _⟩ := map_ok hs
      exact decode_inv hI hl

theorem runOps_inv {w : UWriter} (hI : WInv w) {ops : List WOp} (hv : ∀ op ∈ ops, op.valid)
    (hd : ∀ op ∈ ops, op.isDecode = true → ∃ s, opText op = .ok s) : WInv (runOps w ops).1 := by
  induction ops generalizing w with
  | nil => exact hI
  | cons op t ih =>
    exact ih (applyOp_inv hI (hv op List.mem_cons_self) (hd op List.mem_cons_self))
      (fun x hx => hv x (List.mem_cons_of_mem _ hx)) (fun x hx => hd x (List.mem_cons_of_mem _ hx))

theorem create_inv {n : Int} {w : UWriter} (h : writerCreate n = .ok w) : WInv w := by
  simp only [writerCreate] at h
  split at h
  · simp at h
  · split at h
    · simp only [Except.ok.injEq] at h
      subst h
      exact .inl need_empty.symm
    · simp only [Except.ok.injEq] at h
      subst h
      exact .inr ⟨rfl, rfl⟩

/-- `PyUnicode_New` promises a canonical kind for the characters it will hold, and
`_PyUnicode_CheckConsistency` demands one. Unless a decode fails, `Finish` gives one: for every
script of operations, from any `PyUnicodeWriter_Create`. The precondition on `WriteASCII` is its
documented one. The decode precondition is the point of the layering: `WriterAlwaysCanonical` is
this statement without it, and it is false on 3.14. -/
def WriterFinishCanonical : Prop :=
  ∀ (n : Int) (w : UWriter) (ops : List WOp), writerCreate n = .ok w →
    (∀ op ∈ ops, op.valid) → (∀ op ∈ ops, op.isDecode = true → ∃ s, opText op = .ok s) →
    (runOps w ops).1.finish = ((runOps w ops).1.text, canonicalKind (runOps w ops).1.text)

theorem writerFinishCanonical_proven : WriterFinishCanonical := by
  intro n w ops hw hv hd
  exact (runOps_inv (create_inv hw) hv hd).finish

/-- What `WriterFinishCanonical` cannot see, since under its invariant these branches change nothing:
a one-byte buffer holding at most one character gives the canonical kind whatever the writer has
been through, failed decodes included. That is the `LATIN1` singleton of `unicode_result`, and
`pos == 0` in `_PyUnicodeWriter_Finish`. A `Finish` that kept the buffer's kind fails this at
`{ text := [97], cap := 255 }`, which a failed decode of `\xc3\xa9\xff` reaches. -/
def WriterFinishOneByte : Prop :=
  ∀ w : UWriter, w.cap ≤ 255 → w.text.length ≤ 1 →
    w.finish = (w.text, canonicalKind w.text)

theorem writerFinishOneByte_proven : WriterFinishOneByte := by
  intro w hc hl
  unfold UWriter.finish canonicalKind
  cases ht : w.text with
  | nil => simp [maxCharOf, kindOfMax]
  | cons c t =>
    rw [ht] at hl
    cases t with
    | nil =>
      have e : maxCharOf [c] = c := by simp [maxCharOf]
      simp only [e, if_pos hc]
    | cons d r => simp at hl

/-- The broad form: every script, failed decodes included. Refuted: 'a', then a decode of
`€` followed by a bad byte, returns a two-byte string holding only `a`. -/
def WriterAlwaysCanonical : Prop :=
  ∀ (n : Int) (w : UWriter) (ops : List WOp), writerCreate n = .ok w →
    (∀ op ∈ ops, op.valid) →
    (runOps w ops).1.finish = ((runOps w ops).1.text, canonicalKind (runOps w ops).1.text)

theorem writerAlwaysCanonical_refuted : ¬WriterAlwaysCanonical := by
  intro h
  have := h 0 {} [.char 97, .utf8 [0xe2, 0x82, 0xac, 0xff] 4] (by simp [writerCreate])
    (by simp [WOp.valid])
  revert this
  decide +kernel

/-- "On error, set an exception, leave the writer unchanged", Doc/c-api/unicode.rst, for the
operations that check first and write after. -/
def WriterFailureKeepsState : Prop :=
  ∀ (w : UWriter) (op : WOp) (e : PyExc), op.isDecode = false →
    (applyOp w op).2 = .error e → (applyOp w op).1 = w

theorem writerFailureKeepsState_proven : WriterFailureKeepsState := by
  intro w op x hd he
  cases op with
  | char c =>
    simp only [applyOp] at he ⊢
    split at he
    · simp [*]
    · simp at he
  | str o =>
    simp only [applyOp] at he ⊢
    rcases writeStrOp_cases w o with ⟨s, _, hw | ⟨hw, _⟩⟩ | ⟨e, _, hw⟩
    · simp [hw] at he
    · simp [hw] at he
    · rw [hw]
  | repr o =>
    cases o with
    | none => simp [applyOp, writeReprOp] at he
    | some o =>
      simp only [applyOp] at he ⊢
      rcases writeReprOp_cases w o with ⟨s, _, hw | ⟨hw, _⟩⟩ | ⟨e, _, hw⟩
      · simp [hw] at he
      · simp [hw] at he
      · rw [hw]
  | ascii b size => simp [applyOp] at he
  | ucs4 s size =>
    simp only [applyOp, writeUCS4] at he ⊢
    split at he
    · simp [*]
    · split at he <;> simp at he
  | wide s size =>
    simp only [applyOp, writeWide] at he ⊢
    split
    · rfl
    · split
      · rfl
      · next hne m hm =>
        simp [*] at he
  | sub o start stop =>
    simp only [applyOp, writeSubOp] at he ⊢
    cases o with
    | str s =>
      dsimp only at he ⊢
      split
      · rfl
      · split
        · rfl
        · next h1 h2 =>
          simp [h1, h2] at he
    | _ => rfl
  | utf8 b size => simp [WOp.isDecode] at hd
  | decode b size h c => simp [WOp.isDecode] at hd

/-- The same sentence for every operation: a failed operation is not observable afterwards, by
`Finish` or by anything written later. Refuted on 3.14, by `WriteUTF8` itself, whose documentation
says it. -/
def WriterFailureUnobservable : Prop :=
  ∀ (w : UWriter) (op : WOp) (e : PyExc) (rest : List WOp), WInv w →
    (applyOp w op).2 = .error e →
    (runOps (applyOp w op).1 rest).1.finish = (runOps w rest).1.finish

theorem writerFailureUnobservable_refuted : ¬WriterFailureUnobservable := by
  intro h
  have := h { text := [97], cap := 127 } (.utf8 [0xe2, 0x82, 0xac, 0xff] 4)
    (decodeError "utf-8" [0xe2, 0x82, 0xac, 0xff] 3 4 "invalid start byte") []
    (.inl (by decide)) (by decide +kernel)
  revert this
  decide +kernel

/-! ## The ways to write one string -/

theorem chars_run {w : UWriter} (hc : CapValue w.cap) {s : Str} (hs : ∀ c ∈ s, c ≤ maxUnicode) :
    (runOps w (s.map .char)).1 = wExpect w s := by
  induction s generalizing w with
  | nil => simp [runOps, wExpect]
  | cons c t ih =>
    have hc1 := hs c List.mem_cons_self
    have hstep : (applyOp w (.char c)).1 = wExpect w [c] := by
      simp only [applyOp]
      rw [if_neg (by omega)]
      exact write_char_eq hc c
    have hcap : CapValue (wExpect w [c]).cap := by
      rw [← hstep]
      exact writerCapValue_proven w _ hc
    simp only [List.map_cons, runOps]
    rw [hstep, ih hcap (fun x hx => hs x (List.mem_cons_of_mem _ hx))]
    have e : maxCharOf (c :: t) = max c (maxCharOf t) := by
      have := maxCharOf_append [c] t
      simpa [maxCharOf] using this
    have e1 : maxCharOf [c] = c := by simp [maxCharOf]
    cases t with
    | nil => simp [wExpect]
    | cons d r =>
      simp only [wExpect, List.isEmpty_cons, Bool.false_eq_true, if_false, List.cons_append,
        List.nil_append, List.append_assoc, e, e1, capNeed_max]
      simp [Nat.max_assoc]

theorem path_ucs4 {w : UWriter} (hc : CapValue w.cap) (s : Str) :
    (applyOp w (.ucs4 s s.length)).1 = wExpect w s := by
  have h0 : ¬((s.length : Int) < 0) := by omega
  simp only [applyOp, writeUCS4, if_neg h0, take_all_int]
  split
  · next he => simp [wExpect, he]
  · next he => exact write_part_eq hc he

theorem sized_all {b : List Nat} : (if ((b.length : Int) < 0) then b.takeWhile (· != 0)
    else b.take (b.length : Int).toNat) = b := by
  have h0 : ¬((b.length : Int) < 0) := by omega
  rw [if_neg h0]
  exact take_all_int b

theorem path_wide {w : UWriter} (hc : CapValue w.cap) {s : Str} (hs : ∀ c ∈ s, c ≤ maxUnicode) :
    (applyOp w (.wide s s.length)).1 = wExpect w s := by
  have hz : sizedWide s s.length = s := sized_all
  have hf : s.find? (· > maxUnicode) = none := by
    apply List.find?_eq_none.2
    intro c hm
    have := hs c hm
    simp only [decide_eq_true_eq]
    omega
  simp only [applyOp, writeWide, hz]
  split
  · next he => simp [wExpect, he]
  · next he =>
    rw [findMax_spec _ 0 (by simp [maxUnicode]), hf]
    exact write_part_eq hc he

theorem path_sub {w : UWriter} (hc : CapValue w.cap) (s : Str) {a b : Nat} (hab : a ≤ b)
    (hb : b ≤ s.length) :
    (applyOp w (.sub (.str s) a b)).1 = wExpect w ((s.drop a).take (b - a)) := by
  simp only [applyOp, writeSubOp]
  rw [if_neg (by omega), if_neg (by omega)]
  simp only [Int.toNat_natCast]
  exact writeSubstring_eq hc s hab hb

/-- The bytes of a string decode to it, through the writer, for every handler. -/
theorem path_decode {w : UWriter} (hc : CapValue w.cap) {s : Str} (h : ErrHandler) (c : Bool)
    (hs : ∀ x ∈ s, x ≤ maxUnicode ∧ isSurrogate x = false) :
    (decodeWriter w (s.flatMap utf8EncodeChar) h c).1 = wExpect w s := by
  have hl := length_le_flatMap s
  have hd := utf8Loop_flatMap (s.flatMap utf8EncodeChar) h c s hs
    ((s.flatMap utf8EncodeChar).length + 1) 0 [] (by omega)
  rw [List.nil_append] at hd
  rw [decodeWriter_ok hd]
  dsimp only
  cases s with
  | nil => simp [wExpect]
  | cons x xs =>
    have hne : ((x :: xs).flatMap utf8EncodeChar).isEmpty = false := by
      cases he : (x :: xs).flatMap utf8EncodeChar with
      | nil => rw [he] at hl; simp at hl
      | cons _ _ => rfl
    rw [hne]
    simp only [Bool.false_eq_true, if_false, wExpect, List.isEmpty_cons]
    rw [prepare_max (capValue_prepare hc _), prepare_max hc]
    have e : capNeed 127 = 127 := by decide
    have := need_value (maxCharOf (x :: xs))
    rw [e]
    congr 1
    unfold CapValue at hc
    omega

/-- Every public way of writing the same string leaves the same writer: `WriteStr`, `WriteUCS4`,
`WriteWideChar`, `WriteSubstring` of all of it, `WriteChar` for each character, and `WriteUTF8` or
`DecodeUTF8Stateful`, for any handler, of its encoding. These paths share no code that computes the
kind: one reads the kind of the string, two scan for the maximum, one widens at each character and
one at each character that does not fit. `CapValue` is the type invariant, kept by
`WriterCapValue`, so this covers a writer a failed decode left too wide. Characters are in range,
which a `str` guarantees; for `WriteUCS4` it is a caller's contract, and CPython's test marks the
other case `# CRASHES`. -/
def WriterPathsAgree : Prop :=
  ∀ (w : UWriter) (s : Str), CapValue w.cap → (∀ c ∈ s, c ≤ maxUnicode) →
    let direct := (applyOp w (.str (.str s))).1
    (applyOp w (.ucs4 s s.length)).1 = direct ∧
    (applyOp w (.wide s s.length)).1 = direct ∧
    (applyOp w (.sub (.str s) 0 s.length)).1 = direct ∧
    (runOps w (s.map .char)).1 = direct ∧
    ((∀ c ∈ s, isSurrogate c = false) →
      let b := s.flatMap utf8EncodeChar
      (applyOp w (.utf8 b b.length)).1 = direct ∧
      ∀ (h : ErrHandler) (consumed : Bool), (applyOp w (.decode b b.length h consumed)).1 = direct)

theorem writerPathsAgree_proven : WriterPathsAgree := by
  intro w s hc hs
  have hd : (applyOp w (.str (.str s))).1 = wExpect w s := writeText_eq hc s
  have hsub := path_sub hc s (Nat.zero_le _) (Nat.le_refl _)
  simp only [List.drop_zero, Nat.sub_zero, List.take_length] at hsub
  dsimp only
  rw [hd]
  refine ⟨path_ucs4 hc s, path_wide hc hs, hsub, chars_run hc hs, ?_⟩
  intro hn
  have hz : sizedBytes (s.flatMap utf8EncodeChar) (s.flatMap utf8EncodeChar).length =
      s.flatMap utf8EncodeChar := sized_all
  have hb : ∀ x ∈ s, x ≤ maxUnicode ∧ isSurrogate x = false := fun x hx => ⟨hs x hx, hn x hx⟩
  refine ⟨?_, ?_⟩
  · simp only [applyOp, hz]
    exact path_decode hc .strict false hb
  · intro h c
    cases c with
    | true =>
      simp only [applyOp, hz]
      exact path_decode hc h true hb
    | false =>
      simp only [applyOp, hz]
      exact path_decode hc h false hb

/-- `WriteSubstring(s, a, b)` is `WriteStr(s[a:b])`, for every in-range slice and every writer.
`_PyUnicodeWriter_WriteSubstring` reads the whole string's kind, and scans the characters only if
that does not fit; a slice can be narrower than its string, so this says the skipped scan could not
have mattered, and that the scan does not widen the writer to the whole string. -/
def WriterSubstringIsSlice : Prop :=
  ∀ (w : UWriter) (s : Str) (a b : Nat), CapValue w.cap → a ≤ b → b ≤ s.length →
    (applyOp w (.sub (.str s) a b)).1 = (applyOp w (.str (.str ((s.drop a).take (b - a))))).1

theorem writerSubstringIsSlice_proven : WriterSubstringIsSlice := by
  intro w s a b hc hab hb
  rw [path_sub hc s hab hb]
  exact (writeText_eq hc _).symm

end PyLean.UnicodeObj
