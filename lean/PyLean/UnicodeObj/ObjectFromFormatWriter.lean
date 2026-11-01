import PyLean.UnicodeObj.ObjectFromFormatProps

/-!
`PyUnicodeWriter_Format` against `PyUnicode_FromFormat`, and the text of the format itself.
-/

namespace PyLean.UnicodeObj

open PyLean PyLean.Binary64

/-- Two runs from different writers with the same result. -/
def SameW (w1 w2 : UWriter) : Py UWriter → Py UWriter → Prop
  | .ok u1, .ok u2 => ∃ x, u1.text = w1.text ++ x ∧ u2.text = w2.text ++ x
  | .error e1, .error e2 => e1 = e2
  | _, _ => False

def SameArg {β : Type} (w1 w2 : UWriter) : Py (UWriter × β) → Py (UWriter × β) → Prop
  | .ok (u1, b1), .ok (u2, b2) =>
    b1 = b2 ∧ ∃ x, u1.text = w1.text ++ x ∧ u2.text = w2.text ++ x
  | .error e1, .error e2 => e1 = e2
  | _, _ => False

theorem same_lift {w1 w2 : UWriter} {r1 r2 : Py UWriter} (h : SameW w1 w2 r1 r2) (t : List VArg) :
    SameArg w1 w2 (do return (← r1, t)) (do return (← r2, t)) := by
  cases r1 <;> cases r2 <;> first | exact h | (exact False.elim h) | exact ⟨rfl, h⟩

theorem same_writeStr (w1 w2 : UWriter) (s : Str) (width precision : Int) (lj : Bool) :
    SameW w1 w2 (fmtWriteStr w1 s width precision lj) (fmtWriteStr w2 s width precision lj) := by
  unfold fmtWriteStr
  dsimp only
  split
  · exact ⟨s, writeText_text _ _, writeText_text _ _⟩
  · generalize (if precision ≠ -1 then min precision (s.length : Int) else (s.length : Int)) = length
    split
    · rfl
    · exact ⟨_, rfl, rfl⟩

theorem same_bindStr {α : Type} (w1 w2 : UWriter) (x : Py α) (f : α → Str) (wd : Int) (lj : Bool) :
    SameW w1 w2 (do let v ← x; fmtWriteStr w1 (f v) wd (-1) lj)
      (do let v ← x; fmtWriteStr w2 (f v) wd (-1) lj) := by
  cases x with
  | error e => rfl
  | ok v => exact same_writeStr w1 w2 (f v) wd (-1) lj

theorem same_writeUtf8 (w1 w2 : UWriter) (str : Bytes) (width precision : Int) (lj : Bool) :
    SameW w1 w2 (fmtWriteUtf8 w1 str width precision lj) (fmtWriteUtf8 w2 str width precision lj) := by
  unfold fmtWriteUtf8
  dsimp only
  generalize (if precision = -1 then ((cstrOf str).length, false)
    else (boundedLen (cstrOf str) precision,
      decide ((boundedLen (cstrOf str) precision : Int) = precision))) = pr
  obtain ⟨length, stateful⟩ := pr
  dsimp only
  split
  · have h1 := decode_agrees w1 ((cstrOf str).take length) .replace stateful
    have h2 := decode_agrees w2 ((cstrOf str).take length) .replace stateful
    generalize decodeWriter w1 ((cstrOf str).take length) .replace stateful = r1 at h1 ⊢
    generalize decodeWriter w2 ((cstrOf str).take length) .replace stateful = r2 at h2 ⊢
    obtain ⟨u1, x1⟩ := r1
    obtain ⟨u2, x2⟩ := r2
    cases hl : (utf8DecodeLoop ((cstrOf str).take length) .replace stateful
        (((cstrOf str).take length).length + 1) 0 ((cstrOf str).take length) []).map (·.1) with
    | ok s =>
      rw [hl] at h1 h2
      obtain ⟨t1, n1, rfl⟩ := h1
      obtain ⟨t2, n2, rfl⟩ := h2
      exact ⟨s, t1, t2⟩
    | error e =>
      rw [hl] at h1 h2
      obtain ⟨_, rfl⟩ := h1
      obtain ⟨_, rfl⟩ := h2
      rfl
  · split
    · exact same_bindStr w1 w2 _ id width lj
    · exact same_bindStr w1 w2 _ id width lj

theorem same_writeWcstr (w1 w2 : UWriter) (str : Str) (width precision : Int) (lj : Bool) :
    SameW w1 w2 (fmtWriteWcstr w1 str width precision lj) (fmtWriteWcstr w2 str width precision lj) := by
  unfold fmtWriteWcstr
  dsimp only
  generalize (if precision = -1 then (str.takeWhile (· != 0)).length
    else boundedLen (str.takeWhile (· != 0)) precision) = length
  generalize List.take length (str.takeWhile (· != 0)) = part
  split
  · have h1 := applyOp_agrees w1 (.wide part length)
    have h2 := applyOp_agrees w2 (.wide part length)
    simp only [applyOp] at h1 h2
    generalize writeWide w1 part length = r1 at h1 ⊢
    generalize writeWide w2 part length = r2 at h2 ⊢
    obtain ⟨u1, x1⟩ := r1
    obtain ⟨u2, x2⟩ := r2
    cases hl : opText (.wide part length) with
    | ok s =>
      rw [hl] at h1 h2
      obtain ⟨t1, n1, rfl⟩ := h1
      obtain ⟨t2, n2, rfl⟩ := h2
      exact ⟨s, t1, t2⟩
    | error e =>
      rw [hl] at h1 h2
      obtain ⟨_, rfl⟩ := h1
      obtain ⟨_, rfl⟩ := h2
      rfl
  · split
    · exact same_writeStr w1 w2 _ _ _ _
    · exact same_bindStr w1 w2 _ (fun _ => part) width lj

theorem same_bindPair (w1 w2 : UWriter) (x : Py Str) (t : List VArg) (wd pr : Int) (lj : Bool) :
    SameArg w1 w2 (do let text ← x; return (← fmtWriteStr w1 text wd pr lj, t))
      (do let text ← x; return (← fmtWriteStr w2 text wd pr lj, t)) := by
  cases x with
  | error e => rfl
  | ok v => exact same_lift (same_writeStr w1 w2 v wd pr lj) t

theorem same_err {β : Type} (w1 w2 : UWriter) (e : PyExc) :
    SameArg (β := β) w1 w2 (.error e) (.error e) := rfl

theorem same_ascii (w1 w2 : UWriter) (s : Str) (t : List VArg) :
    SameArg w1 w2 (.ok (writeAsciiText w1 s, t)) (.ok (writeAsciiText w2 s, t)) :=
  ⟨rfl, s, writeAscii_text _ _, writeAscii_text _ _⟩

theorem same_text (w1 w2 : UWriter) (s : Str) (c1 c2 : Nat) (t : List VArg) :
    SameArg w1 w2 (.ok (({ text := w1.text ++ s, cap := c1 } : UWriter), t))
      (.ok (({ text := w2.text ++ s, cap := c2 } : UWriter), t)) :=
  ⟨rfl, s, rfl, rfl⟩

theorem same_switch (w1 w2 : UWriter) (p : List Nat) (s : FSpec) (c : Nat) (args : List VArg) :
    SameArg w1 w2 (fromFormatSwitch w1 p s c args) (fromFormatSwitch w2 p s c args) := by
  unfold fromFormatSwitch
  by_cases h1 : c = 99
  · simp only [if_pos h1]
    rcases args with _ | ⟨a, t⟩
    · exact same_err _ _ _
    · cases a
      case int v =>
        dsimp only
        split
        · exact same_err _ _ _
        · exact same_text _ _ _ _ _ _
      all_goals exact same_err _ _ _
  simp only [if_neg h1]
  by_cases h2 : c = 100 ∨ c = 105 ∨ c = 111 ∨ c = 117 ∨ c = 120 ∨ c = 88
  · simp only [if_pos h2]
    rcases args with _ | ⟨a, t⟩
    · exact same_err _ _ _
    · cases a
      case int v => exact same_ascii _ _ _ _
      all_goals exact same_err _ _ _
  simp only [if_neg h2]
  by_cases h3 : c = 112
  · simp only [if_pos h3]
    rcases args with _ | ⟨a, t⟩
    · exact same_err _ _ _
    · cases a
      case ptr v => exact same_ascii _ _ _ _
      all_goals exact same_err _ _ _
  simp only [if_neg h3]
  by_cases h4 : c = 115
  · simp only [if_pos h4]
    split
    · rcases args with _ | ⟨a, t⟩
      · exact same_err _ _ _
      · cases a
        case wstr x => exact same_lift (same_writeWcstr w1 w2 _ _ _ _) _
        all_goals exact same_err _ _ _
    · rcases args with _ | ⟨a, t⟩
      · exact same_err _ _ _
      · cases a
        case cstr b => exact same_lift (same_writeUtf8 w1 w2 _ _ _ _) _
        all_goals exact same_err _ _ _
  simp only [if_neg h4]
  by_cases h5 : c = 85
  · simp only [if_pos h5]
    rcases args with _ | ⟨a, t⟩
    · exact same_err _ _ _
    · cases a
      case obj o =>
        cases o
        case str x => exact same_lift (same_writeStr w1 w2 _ _ _ _) _
        all_goals exact same_err _ _ _
      all_goals exact same_err _ _ _
  simp only [if_neg h5]
  by_cases h6 : c = 86
  · simp only [if_pos h6]
    rcases args with _ | ⟨a, _ | ⟨b, t⟩⟩
    · exact same_err _ _ _
    · exact same_err _ _ _
    · cases a
      case obj o =>
        cases o
        case str x => exact same_lift (same_writeStr w1 w2 _ _ _ _) _
        all_goals exact same_err _ _ _
      case nullObj =>
        cases b
        case wstr x =>
          dsimp only
          split
          · exact same_lift (same_writeWcstr w1 w2 _ _ _ _) _
          · exact same_err _ _ _
        case cstr x =>
          dsimp only
          split
          · exact same_lift (same_writeUtf8 w1 w2 _ _ _ _) _
          · exact same_err _ _ _
        all_goals exact same_err _ _ _
      all_goals exact same_err _ _ _
  simp only [if_neg h6]
  by_cases h7 : c = 83 ∨ c = 82 ∨ c = 65
  · simp only [if_pos h7]
    rcases args with _ | ⟨a, t⟩
    · exact same_err _ _ _
    · cases a
      case obj o =>
        dsimp only
        split
        · exact same_bindPair w1 w2 _ _ _ _ _
        · split
          · exact same_bindPair w1 w2 _ _ _ _ _
          · exact same_bindPair w1 w2 _ _ _ _ _
      all_goals exact same_err _ _ _
  simp only [if_neg h7]
  by_cases h8 : c = 84
  · simp only [if_pos h8]
    rcases args with _ | ⟨a, t⟩
    · exact same_err _ _ _
    · cases a
      case obj o => exact same_lift (same_writeStr w1 w2 _ _ _ _) _
      case inst n => exact same_lift (same_writeStr w1 w2 _ _ _ _) _
      all_goals exact same_err _ _ _
  simp only [if_neg h8]
  by_cases h9 : c = 78
  · simp only [if_pos h9]
    rcases args with _ | ⟨a, t⟩
    · exact same_err _ _ _
    · cases a
      case type n => exact same_lift (same_writeStr w1 w2 _ _ _ _) _
      all_goals exact same_err _ _ _
  simp only [if_neg h9]
  exact same_err _ _ _

theorem same_conv (w1 w2 : UWriter) (p : List Nat) (s : FSpec) (f : List Nat) (args : List VArg) :
    SameArg w1 w2 (fromFormatConv w1 p s f args) (fromFormatConv w2 p s f args) := by
  unfold fromFormatConv
  split
  · exact same_err _ _ _
  · exact same_switch _ _ _ _ _ _

theorem same_arg (w1 w2 : UWriter) (p : List Nat) (args : List VArg) :
    SameArg w1 w2 (fromFormatArg w1 p args) (fromFormatArg w2 p args) := by
  simp only [fromFormatArg]
  cases p with
  | nil => exact same_err _ _ _
  | cons c f0 =>
    dsimp only
    split
    · exact ⟨rfl, [37], rfl, rfl⟩
    · cases hp : parseSpec f0 args with
      | error e => exact same_err _ _ _
      | ok r =>
        obtain ⟨s, f, a⟩ := r
        have h := same_conv w1 w2 (c :: f0) s f a
        simp only [bind, Except.bind]
        cases h1 : fromFormatConv w1 (c :: f0) s f a <;>
          cases h2 : fromFormatConv w2 (c :: f0) s f a <;>
          rw [h1, h2] at h
        · exact h
        · exact False.elim h
        · exact False.elim h
        · next r1 r2 =>
          obtain ⟨u1, b1⟩ := r1
          obtain ⟨u2, b2⟩ := r2
          obtain ⟨rfl, hx⟩ := h
          exact ⟨rfl, hx⟩

/-- Two runs of the loop from different writers come to the same end. -/
theorem same_loop : ∀ (fuel : Nat) (f : List Nat) (args : List VArg) (w1 w2 : UWriter),
    (fromFormatLoop fuel f args w1).2 = (fromFormatLoop fuel f args w2).2 ∧
      ∃ x, (fromFormatLoop fuel f args w1).1.text = w1.text ++ x ∧
        (fromFormatLoop fuel f args w2).1.text = w2.text ++ x := by
  intro fuel
  induction fuel with
  | zero => intro f args w1 w2; exact ⟨rfl, [], by simp [fromFormatLoop], by simp [fromFormatLoop]⟩
  | succ fuel ih =>
    intro f args w1 w2
    cases f with
    | nil => exact ⟨rfl, [], by simp [fromFormatLoop], by simp [fromFormatLoop]⟩
    | cons c t =>
      simp only [fromFormatLoop]
      split
      · have h := same_arg w1 w2 (c :: t) args
        cases h1 : fromFormatArg w1 (c :: t) args <;>
          cases h2 : fromFormatArg w2 (c :: t) args <;>
          rw [h1, h2] at h
        · have e : _ = _ := h
          subst e
          exact ⟨rfl, [], by simp, by simp⟩
        · exact False.elim h
        · exact False.elim h
        · next r1 r2 =>
          obtain ⟨u1, f1, a1⟩ := r1
          obtain ⟨u2, f2, a2⟩ := r2
          obtain ⟨he, x, hx1, hx2⟩ := h
          simp only [Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          obtain ⟨hs, y, h3, h4⟩ := ih f1 a1 u1 u2
          exact ⟨hs, x ++ y, by rw [h3, hx1, List.append_assoc],
            by rw [h4, hx2, List.append_assoc]⟩
      · obtain ⟨hs, y, h3, h4⟩ := ih ((c :: t).drop ((c :: t).takeWhile (· != 37)).length) args
          (writeAsciiText w1 ((c :: t).takeWhile (· != 37)))
          (writeAsciiText w2 ((c :: t).takeWhile (· != 37)))
        exact ⟨hs, (c :: t).takeWhile (· != 37) ++ y, by rw [h3, writeAscii_text, List.append_assoc],
          by rw [h4, writeAscii_text, List.append_assoc]⟩

theorem finish_text (w : UWriter) : w.finish.1 = w.text := by
  unfold UWriter.finish
  cases h : w.text with
  | nil => rfl
  | cons c t =>
    cases t with
    | nil =>
      dsimp only
      split <;> rfl
    | cons d r => rfl

/-- `PyUnicodeWriter_Format` is `PyUnicode_FromFormat` appended to what the writer holds: same
exception, same text, for every writer and every format, or, on failure, no text at all. So the
widths, the scans of `unicode_fromformat_write_str` and the decoder's fast path, which all read
the writer, change nothing but the buffer. -/
def WriterFormatAppends : Prop :=
  ∀ (w : UWriter) (fmt : Bytes) (args : List VArg),
    match pyUnicodeFromFormat fmt args with
    | .ok r => (writerFormat w fmt args).2 = .ok () ∧ (writerFormat w fmt args).1.text = w.text ++ r.1
    | .error e => (writerFormat w fmt args).2 = .error e ∧ (writerFormat w fmt args).1.text = w.text

theorem same_format (w1 w2 : UWriter) (fmt : Bytes) (args : List VArg) :
    (unicodeFromFormat w1 fmt args).2 = (unicodeFromFormat w2 fmt args).2 ∧
      ∃ x, (unicodeFromFormat w1 fmt args).1.text = w1.text ++ x ∧
        (unicodeFromFormat w2 fmt args).1.text = w2.text ++ x := by
  unfold unicodeFromFormat
  dsimp only
  split
  · exact ⟨rfl, [], by simp, by simp⟩
  · exact same_loop _ _ _ _ _

theorem writerFormatAppends_proven : WriterFormatAppends := by
  intro w fmt args
  obtain ⟨hs, x, h1, h2⟩ := same_format w {} fmt args
  simp only [List.nil_append] at h2
  unfold pyUnicodeFromFormat writerFormat
  dsimp only
  cases hu : unicodeFromFormat w fmt args with
  | mk w' r =>
    cases hv : unicodeFromFormat {} fmt args with
    | mk v' q =>
      rw [hu, hv] at hs
      simp only at hs
      subst hs
      rw [hu] at h1
      rw [hv] at h2
      simp only at h1 h2
      cases r with
      | error e => exact ⟨rfl, rfl⟩
      | ok u =>
        refine ⟨rfl, ?_⟩
        show w'.text = w.text ++ v'.finish.1
        rw [finish_text, h1, h2]

/-- A format holding only text, with `%` doubled. -/
def escapePct (s : Bytes) : Bytes := s.flatMap fun c => if c = 37 then [37, 37] else [c]

theorem take_pend (pend x : List Nat) (h : ∀ c ∈ pend, c ≠ 37) :
    (pend ++ 37 :: x).takeWhile (· != 37) = pend := by
  induction pend with
  | nil => simp
  | cons p ps ih =>
    have hp := h p List.mem_cons_self
    simp [List.takeWhile_cons, hp, ih (fun c hc => h c (List.mem_cons_of_mem _ hc))]

theorem take_all (pend : List Nat) (h : ∀ c ∈ pend, c ≠ 37) :
    pend.takeWhile (· != 37) = pend := by
  induction pend with
  | nil => simp
  | cons p ps ih =>
    have hp := h p List.mem_cons_self
    simp [List.takeWhile_cons, hp, ih (fun c hc => h c (List.mem_cons_of_mem _ hc))]

theorem escape_cons (c : Nat) (t : Bytes) :
    escapePct (c :: t) = (if c = 37 then [37, 37] else [c]) ++ escapePct t := by
  simp [escapePct]

/-- The loop on a format with `pend` pending in a text chunk. -/
theorem escape_loop : ∀ (s pend : Bytes) (fuel : Nat) (w : UWriter), (∀ c ∈ pend, c ≠ 37) →
    (pend ++ escapePct s).length < fuel →
    (fromFormatLoop fuel (pend ++ escapePct s) [] w).2 = .ok () ∧
      (fromFormatLoop fuel (pend ++ escapePct s) [] w).1.text = w.text ++ pend ++ s := by
  intro s
  induction s with
  | nil =>
    intro pend fuel w hp hf
    simp only [escapePct, List.flatMap_nil, List.append_nil] at hf ⊢
    cases pend with
    | nil =>
      cases fuel with
      | zero => omega
      | succ f => simp [fromFormatLoop]
    | cons p ps =>
      cases fuel with
      | zero => omega
      | succ f =>
        cases f with
        | zero => simp at hf
        | succ g =>
          have hn := hp p List.mem_cons_self
          have ht := take_all (p :: ps) hp
          simp only [fromFormatLoop, hn, if_false, ht, List.drop_length]
          refine ⟨trivial, ?_⟩
          rw [writeAscii_text]
  | cons c t ih =>
    intro pend fuel w hp hf
    rw [escape_cons] at hf ⊢
    by_cases hc : c = 37
    · subst hc
      simp only [if_true] at hf ⊢
      have base : ∀ (fuel : Nat) (w : UWriter), (escapePct t).length + 2 < fuel + 1 →
          (fromFormatLoop fuel (37 :: 37 :: escapePct t) [] w).2 = .ok () ∧
            (fromFormatLoop fuel (37 :: 37 :: escapePct t) [] w).1.text = w.text ++ 37 :: t := by
        intro fuel w h
        cases fuel with
        | zero => omega
        | succ f =>
          have hr := ih [] f { text := w.text ++ [37], cap := prepareCap w.cap 37 } (by simp) (by
            simp only [List.nil_append]
            omega)
          simp only [List.nil_append] at hr
          simp only [fromFormatLoop, if_true, fromFormatArg, ffChar, bind, Except.bind, List.tail_cons]
          simpa using hr
      cases pend with
      | nil =>
        simp only [List.nil_append, List.cons_append] at hf ⊢
        have := base fuel w (by
          simp only [List.length_cons] at hf
          omega)
        simpa using this
      | cons p ps =>
        have hn := hp p List.mem_cons_self
        have hlen : ((p :: ps) ++ ([37, 37] ++ escapePct t)).length =
            ps.length + 1 + (escapePct t).length + 2 := by
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        cases fuel with
        | zero => omega
        | succ f =>
          have e : (p :: ps) ++ ([37, 37] ++ escapePct t) = (p :: ps) ++ 37 :: (37 :: escapePct t) := by
            simp
          have ht := take_pend (p :: ps) (37 :: escapePct t) hp
          have hd : ((p :: ps) ++ 37 :: 37 :: escapePct t).drop (p :: ps).length =
              37 :: 37 :: escapePct t := List.drop_left
          have hstep : fromFormatLoop (f + 1) ((p :: ps) ++ 37 :: 37 :: escapePct t) [] w =
              fromFormatLoop f (37 :: 37 :: escapePct t) [] (writeAsciiText w (p :: ps)) := by
            rw [List.cons_append]
            simp only [fromFormatLoop]
            rw [if_neg hn]
            rw [← List.cons_append, ht, hd]
          rw [e, hstep]
          have hb := base f (writeAsciiText w (p :: ps)) (by omega)
          refine ⟨hb.1, ?_⟩
          rw [hb.2, writeAscii_text]
    · simp only [hc, if_false] at hf ⊢
      have hr := ih (pend ++ [c]) fuel w (by
        intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact hp x hx
        · rw [List.mem_singleton.1 hx]
          exact hc) (by rw [List.append_assoc]; exact hf)
      rw [List.append_assoc] at hr
      simpa using hr

theorem escape_chars {s : Bytes} (h : ∀ c ∈ s, 0 < c ∧ c < 128) :
    ∀ c ∈ escapePct s, 0 < c ∧ c < 128 := by
  intro c hc
  simp only [escapePct, List.mem_flatMap] at hc
  obtain ⟨a, ha, hm⟩ := hc
  split at hm
  · simp at hm
    omega
  · simp only [List.mem_singleton] at hm
    rw [hm]
    exact h a ha

theorem cstr_self {b : Bytes} (h : ∀ c ∈ b, 0 < c ∧ c < 128) : cstrOf b = b := by
  unfold cstrOf
  induction b with
  | nil => rfl
  | cons c t ih =>
    have hc := (h c List.mem_cons_self).1
    have hne : c ≠ 0 := by omega
    simp [List.takeWhile_cons, hne, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- `%%` is the way to write `%`: doubling the `%` of a string and formatting it with no arguments
gives the string back, with the canonical kind, for every string of ASCII characters other than
NUL. The text chunks of the loop and the `%%` branch have to meet exactly. -/
def FromFormatEscape : Prop :=
  ∀ s : Bytes, (∀ c ∈ s, 0 < c ∧ c < 128) →
    pyUnicodeFromFormat (escapePct s) [] = .ok (s, canonicalKind s)

theorem fromFormatEscape_proven : FromFormatEscape := by
  intro s hs
  have hc := escape_chars hs
  have he : cstrOf (escapePct s) = escapePct s := cstr_self hc
  have hf : (escapePct s).find? (· > 127) = none := by
    apply List.find?_eq_none.2
    intro c hm
    have := (hc c hm).2
    simp only [decide_eq_true_eq]
    omega
  obtain ⟨h1, h2⟩ := escape_loop s [] ((escapePct s).length + 1) {} (by simp) (by simp)
  simp only [List.nil_append] at h1 h2
  have hu : unicodeFromFormat {} (escapePct s) [] =
      ((fromFormatLoop ((escapePct s).length + 1) (escapePct s) [] {}).1, .ok ()) := by
    unfold unicodeFromFormat
    dsimp only
    rw [he, hf]
    dsimp only
    rw [Prod.ext_iff]
    exact ⟨rfl, h1⟩
  have hI := unicodeFromFormat_inv (w0 := {}) (.inr ⟨rfl, rfl⟩) hu
  unfold pyUnicodeFromFormat
  rw [hu]
  dsimp only
  rw [hI.finish, h2]

end PyLean.UnicodeObj
