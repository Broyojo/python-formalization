import PyLean.UnicodeObj.CodecCallbackProps

/-!
Decoding in two chunks against decoding at once.

A stateful decoder (`consumed != NULL`) stops at an incomplete sequence and reports how far it got.
An incremental decoder passes the rest back in front of the next chunk. So the bytes around a cut
are seen twice, once with `consumed` and once without. The contract is that the result is what
decoding everything at once gives. That ties the `consumed` branch of every decoder to the branch
without it, and every error path on the way.

The engine here is for `decodeDriver` and a standard handler, and needs three things of a decoder:
it moves (`Moves`), what it does with `consumed` on a piece it does the same with more after it
(`Agree`), and the handler it calls cannot tell the piece from the whole (`handlerLoc`).
-/

namespace PyLean.UnicodeObj

open PyLean

/-- One round is progress. -/
def okStep : DStep → Prop
  | .char _ n => 0 < n
  | .multi _ n => 0 < n
  | .fail _ s e => s < e
  | .stop => True
  | .raise _ => False

theorem okStep_ite {P : Prop} [Decidable P] {a b : DStep} (h1 : okStep a) (h2 : okStep b) :
    okStep (if P then a else b) := by
  split <;> assumption

structure Moves (step : List Nat → DStep) : Prop where
  nil : step [] = .stop
  ok : ∀ r, okStep (step r)

/-- What a step with `consumed` said about a piece of length `L` holds with more after it, without
`consumed`, and it needed no byte past the piece. `.stop` is the waiting for more: nothing claimed. -/
def Agree (d d' : DStep) (L : Nat) : Prop :=
  match d with
  | .char c n => d' = .char c n ∧ n ≤ L
  | .multi w n => d' = .multi w n ∧ n ≤ L
  | .fail why s e => d' = .fail why s e ∧ e ≤ L
  | .stop => True
  | .raise _ => False

theorem agree_ite {P : Prop} [Decidable P] {a b c d : DStep} {L : Nat} (h1 : P → Agree a c L)
    (h2 : ¬P → Agree b d L) : Agree (if P then a else b) (if P then c else d) L := by
  by_cases q : P
  · rw [if_pos q, if_pos q]
    exact h1 q
  · rw [if_neg q, if_neg q]
    exact h2 q

theorem handler_moves {h : ErrHandler} {enc : String} {code : EncCode} {input : Bytes}
    {start stop : Nat} {why : String} {rep : Str} {np : Nat} (hs : start < stop)
    (he : decodeHandlerCall h enc code input start stop why = .ok (rep, np)) : start < np := by
  cases h <;> simp only [decodeHandlerCall] at he
  case strict | xmlcharrefreplace | namereplace => cases he
  case ignore | replace | backslashreplace =>
    simp only [Except.ok.injEq, Prod.mk.injEq] at he
    omega
  case surrogateescape =>
    split at he
    · cases he
    · rename_i hne
      simp only [Except.ok.injEq, Prod.mk.injEq] at he
      have : 0 < (escapeRun 4 ((input.drop start).take (stop - start))).length := by
        cases hr : escapeRun 4 ((input.drop start).take (stop - start)) with
        | nil =>
          rw [hr] at hne
          simp at hne
        | cons _ _ => simp
      omega
  case surrogatepass =>
    split at he
    · cases he
    · rename_i hu
      generalize (if input.length - start ≥ code.bytelength then
        surrogatePassRead code (input.drop start) else 0) = ch at he
      split at he
      · simp only [Except.ok.injEq, Prod.mk.injEq] at he
        have : 0 < code.bytelength := by
          cases code <;> simp_all [EncCode.bytelength]
        omega
      · cases he

/-- With enough fuel, how much does not matter. -/
theorem driver_stable {step : List Nat → DStep} (hm : Moves step) (h : ErrHandler) (enc : String)
    (code : EncCode) (input : Bytes) :
    ∀ (f f' pos : Nat) (rest : List Nat) (out : Str), rest = input.drop pos → rest.length < f →
      rest.length < f' →
      decodeDriver step h enc code input f pos rest out =
        decodeDriver step h enc code input f' pos rest out := by
  intro f
  induction f with
  | zero => intro f' pos rest out _ h1; omega
  | succ f ih =>
    intro f' pos rest out hr h1 h2
    cases f' with
    | zero => omega
    | succ k =>
      have hne : ∀ d, step rest = d → d ≠ .stop → rest ≠ [] := by
        intro d hd hn he
        rw [he, hm.nil] at hd
        exact hn hd.symm
      have hok := hm.ok rest
      have hlen : rest.length = input.length - pos := by rw [hr, List.length_drop]
      simp only [decodeDriver]
      cases hs : step rest with
      | char c n =>
        rw [hs] at hok
        have hl := List.length_pos_iff.2 (hne _ hs (by simp))
        simp only [okStep] at hok
        exact ih _ _ _ _ (by rw [hr, List.drop_drop]) (by simp; omega) (by simp; omega)
      | multi w n =>
        rw [hs] at hok
        have hl := List.length_pos_iff.2 (hne _ hs (by simp))
        simp only [okStep] at hok
        exact ih _ _ _ _ (by rw [hr, List.drop_drop]) (by simp; omega) (by simp; omega)
      | stop => rfl
      | raise e => rfl
      | fail why s e =>
        rw [hs] at hok
        have hl := List.length_pos_iff.2 (hne _ hs (by simp))
        simp only [okStep] at hok
        dsimp only
        cases hc : decodeHandlerCall h enc code input (pos + s) (pos + e) why with
        | error x => rfl
        | ok p =>
          obtain ⟨w, np⟩ := p
          have hnp := handler_moves (by omega) hc
          dsimp only
          exact ih _ _ _ _ rfl (by simp; omega) (by simp; omega)

/-- A handler looks at the bytes from the start of the error, and only those. -/
theorem handler_shift (h : ErrHandler) (enc : String) (code : EncCode) (p q : Bytes) (s e : Nat)
    (why : String) :
    match decodeHandlerCall h enc code q s e why with
    | .ok (w, n) =>
      decodeHandlerCall h enc code (p ++ q) (p.length + s) (p.length + e) why = .ok (w, p.length + n)
    | .error _ => ∃ x, decodeHandlerCall h enc code (p ++ q) (p.length + s) (p.length + e) why = .error x := by
  have hd : (p ++ q).drop (p.length + s) = q.drop s := by simp [List.drop_append]
  have hdiff : p.length + e - (p.length + s) = e - s := by omega
  have hlen : (p ++ q).length - (p.length + s) = q.length - s := by simp; omega
  cases h
  case surrogateescape =>
    simp only [decodeHandlerCall, hd, hdiff]
    by_cases hq : (escapeRun 4 ((q.drop s).take (e - s))).isEmpty = true
    · simp only [hq, if_true]
      exact ⟨_, rfl⟩
    · simp only [hq, Bool.false_eq_true, if_false, Nat.add_assoc]
  case surrogatepass =>
    simp only [decodeHandlerCall, hd, hlen]
    by_cases hu : (code == .unknown) = true
    · simp only [hu, if_true]
      exact ⟨_, rfl⟩
    · simp only [hu, Bool.false_eq_true, if_false]
      generalize (if q.length - s ≥ code.bytelength then surrogatePassRead code (q.drop s) else 0) = ch
      by_cases hch : isSurrogate ch = true
      · simp only [hch, if_true, Nat.add_assoc]
      · simp only [hch, Bool.false_eq_true, if_false]
        exact ⟨_, rfl⟩
  all_goals first
    | (simp only [decodeHandlerCall, hd, hdiff]; done)
    | (simp only [decodeHandlerCall, hd, hdiff]; exact ⟨_, rfl⟩)
    | (simp only [decodeHandlerCall, hd, hdiff]; rfl)

/-- Two runs of the driver, one `p.length` further along in its input than the other, and with
different text so far. -/
def Shifted (p : Nat) (out out' : Str) : Py (Str × Nat) → Py (Str × Nat) → Prop
  | .ok (s, n), .ok (s', n') => ∃ u, s = out ++ u ∧ s' = out' ++ u ∧ n = p + n'
  | .error _, .error _ => True
  | _, _ => False

theorem shifted_app {p : Nat} {out out' x : Str} {r r' : Py (Str × Nat)}
    (t : Shifted p (out ++ x) (out' ++ x) r r') : Shifted p out out' r r' := by
  cases r with
  | error e =>
    cases r' with
    | error _ => trivial
    | ok _ => exact t
  | ok a =>
    obtain ⟨s, n⟩ := a
    cases r' with
    | error _ => exact t
    | ok b =>
      obtain ⟨s', n'⟩ := b
      obtain ⟨u, h1, h2, h3⟩ := t
      exact ⟨x ++ u, by simp [h1], by simp [h2], h3⟩

theorem driver_shift (step : List Nat → DStep) (h : ErrHandler) (enc : String) (code : EncCode)
    (p q : Bytes) :
    ∀ (f pos : Nat) (rest : List Nat) (out out' : Str),
      Shifted p.length out out' (decodeDriver step h enc code (p ++ q) f (p.length + pos) rest out)
        (decodeDriver step h enc code q f pos rest out') := by
  intro f
  induction f with
  | zero => intro pos rest out out'; trivial
  | succ f ih =>
    intro pos rest out out'
    simp only [decodeDriver]
    cases hs : step rest with
    | char c n =>
      exact shifted_app (x := [c]) (by
        have := ih (pos + n) (rest.drop n) (out ++ [c]) (out' ++ [c])
        rwa [← Nat.add_assoc] at this)
    | multi w n =>
      exact shifted_app (x := w) (by
        have := ih (pos + n) (rest.drop n) (out ++ w) (out' ++ w)
        rwa [← Nat.add_assoc] at this)
    | stop => exact ⟨[], by simp, by simp, rfl⟩
    | raise e => trivial
    | fail why s e =>
      dsimp only
      have hh := handler_shift h enc code p q (pos + s) (pos + e) why
      rw [← Nat.add_assoc, ← Nat.add_assoc] at hh
      cases hq : decodeHandlerCall h enc code q (pos + s) (pos + e) why with
      | error x =>
        rw [hq] at hh
        obtain ⟨y, hy⟩ := hh
        rw [hy]
        trivial
      | ok r =>
        obtain ⟨w, n⟩ := r
        rw [hq] at hh
        dsimp only at hh
        rw [hh]
        dsimp only
        have := ih n (q.drop n) (out ++ w) (out' ++ w)
        have hdp : (p ++ q).drop (p.length + n) = q.drop n := by simp [List.drop_append]
        rw [hdp]
        exact shifted_app this

/-- The handler cannot tell the piece from the whole: what it does on `a` it does on `a ++ t`. A
failure stays a failure, with a message that may name other bytes. -/
def handlerLoc (h : ErrHandler) (enc : String) (code : EncCode) (a t : Bytes) (start stop : Nat)
    (why : String) : Prop :=
  match decodeHandlerCall h enc code a start stop why with
  | .ok r => decodeHandlerCall h enc code (a ++ t) start stop why = .ok r
  | .error _ => ∃ x, decodeHandlerCall h enc code (a ++ t) start stop why = .error x

theorem read_prefix (code : EncCode) (r t : List Nat) (hb : code.bytelength ≤ r.length) :
    surrogatePassRead code (r ++ t) = surrogatePassRead code r := by
  cases code
  all_goals
    rcases r with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, r⟩⟩⟩⟩
  all_goals first
    | (simp [EncCode.bytelength] at hb; done)
    | simp [surrogatePassRead]
    | rfl

/-- With the bytes a `surrogatepass` reads all inside the piece, or none read at all, the handler is
local. UTF-16 and UTF-32 are like that; the escapes have no `surrogatepass`. -/
theorem handler_loc (h : ErrHandler) (enc : String) (code : EncCode) (a t : Bytes) (start stop : Nat)
    (why : String) (hs : start ≤ stop) (hstop : stop ≤ a.length)
    (hb : h = .surrogatepass → code = .unknown ∨ start + code.bytelength ≤ a.length) :
    handlerLoc h enc code a t start stop why := by
  have hd : ((a ++ t).drop start).take (stop - start) = (a.drop start).take (stop - start) := by
    rw [List.drop_append_of_le_length (by omega)]
    rw [List.take_append_of_le_length (by simp; omega)]
  unfold handlerLoc
  cases h
  case surrogateescape =>
    simp only [decodeHandlerCall, hd]
    by_cases hq : (escapeRun 4 ((a.drop start).take (stop - start))).isEmpty = true
    · simp only [hq, if_true]
      exact ⟨_, rfl⟩
    · simp only [hq, Bool.false_eq_true, if_false]
  case surrogatepass =>
    simp only [decodeHandlerCall]
    by_cases hu : (code == .unknown) = true
    · simp only [hu, if_true]
      exact ⟨_, rfl⟩
    · have hc : code ≠ .unknown := by
        intro e
        subst e
        simp at hu
      have hb' : start + code.bytelength ≤ a.length := by
        rcases hb rfl with e | e
        · exact absurd e hc
        · exact e
      have hl : (a ++ t).length - start ≥ code.bytelength := by simp; omega
      have hl2 : a.length - start ≥ code.bytelength := by omega
      have hr : surrogatePassRead code ((a ++ t).drop start) = surrogatePassRead code (a.drop start) := by
        rw [List.drop_append_of_le_length (by omega)]
        exact read_prefix code _ t (by simp; omega)
      simp only [hu, Bool.false_eq_true, if_false, if_pos hl, if_pos hl2, hr]
      generalize surrogatePassRead code (a.drop start) = ch
      by_cases hch : isSurrogate ch = true
      · simp only [hch, if_true]
      · simp only [hch, Bool.false_eq_true, if_false]
        exact ⟨_, rfl⟩
  all_goals first
    | (simp only [decodeHandlerCall, hd]; done)
    | (simp only [decodeHandlerCall, hd]; exact ⟨_, rfl⟩)
    | (simp only [decodeHandlerCall, hd]; rfl)

/-- Lock step: a run with `consumed` on `a`, and a run without it on `a ++ t`. -/
theorem driver_cut {sc sf : List Nat → DStep} (hc : Moves sc) (h : ErrHandler) (enc : String)
    (code : EncCode) (a t : Bytes)
    (hA : ∀ i, Agree (sc (a.drop i)) (sf (a.drop i ++ t)) (a.drop i).length)
    (hL : ∀ i why s e, sc (a.drop i) = .fail why s e → handlerLoc h enc code a t (i + s) (i + e) why) :
    ∀ (f g pos : Nat) (rest : List Nat) (out : Str), rest = a.drop pos → pos ≤ a.length →
      rest.length < f →
      match decodeDriver sc h enc code a f pos rest out with
      | .ok (s, n) =>
        n ≤ a.length ∧ ∃ g', g ≤ g' ∧
          decodeDriver sf h enc code (a ++ t) (f + g) pos (rest ++ t) out =
            decodeDriver sf h enc code (a ++ t) g' n (a.drop n ++ t) s
      | .error _ => ∃ x, decodeDriver sf h enc code (a ++ t) (f + g) pos (rest ++ t) out = .error x := by
  intro f
  induction f with
  | zero => intro g pos rest out _ _ h1; omega
  | succ k ih =>
    intro g pos rest out hr hp h1
    have hag := hA pos
    rw [← hr] at hag
    have hok := hc.ok rest
    have hlen : rest.length = a.length - pos := by rw [hr, List.length_drop]
    have ek : k + 1 + g = (k + g) + 1 := by omega
    have hdrop : ∀ n, n ≤ rest.length → (rest ++ t).drop n = rest.drop n ++ t := fun n hn =>
      List.drop_append_of_le_length hn
    cases hs : sc rest with
    | stop =>
      have e1 : decodeDriver sc h enc code a (k + 1) pos rest out = .ok (out, pos) := by
        simp only [decodeDriver, hs]
      rw [e1]
      exact ⟨hp, k + 1 + g, by omega, by rw [hr]⟩
    | raise x =>
      rw [hs] at hok
      exact hok.elim
    | char c n =>
      rw [hs] at hag hok
      obtain ⟨hf, hn⟩ := hag
      simp only [okStep] at hok
      have e1 : decodeDriver sc h enc code a (k + 1) pos rest out =
          decodeDriver sc h enc code a k (pos + n) (rest.drop n) (out ++ [c]) := by
        simp only [decodeDriver, hs]
      have e2 : decodeDriver sf h enc code (a ++ t) (k + 1 + g) pos (rest ++ t) out =
          decodeDriver sf h enc code (a ++ t) (k + g) (pos + n) (rest.drop n ++ t) (out ++ [c]) := by
        rw [ek]
        simp only [decodeDriver, hf]
        rw [hdrop n hn]
      rw [e1, e2]
      exact ih g (pos + n) (rest.drop n) (out ++ [c]) (by rw [hr, List.drop_drop]) (by omega)
        (by simp; omega)
    | multi w n =>
      rw [hs] at hag hok
      obtain ⟨hf, hn⟩ := hag
      simp only [okStep] at hok
      have e1 : decodeDriver sc h enc code a (k + 1) pos rest out =
          decodeDriver sc h enc code a k (pos + n) (rest.drop n) (out ++ w) := by
        simp only [decodeDriver, hs]
      have e2 : decodeDriver sf h enc code (a ++ t) (k + 1 + g) pos (rest ++ t) out =
          decodeDriver sf h enc code (a ++ t) (k + g) (pos + n) (rest.drop n ++ t) (out ++ w) := by
        rw [ek]
        simp only [decodeDriver, hf]
        rw [hdrop n hn]
      rw [e1, e2]
      exact ih g (pos + n) (rest.drop n) (out ++ w) (by rw [hr, List.drop_drop]) (by omega)
        (by simp; omega)
    | fail why s e =>
      rw [hs] at hag hok
      obtain ⟨hf, he⟩ := hag
      simp only [okStep] at hok
      have hl := hL pos why s e (by rw [← hr]; exact hs)
      unfold handlerLoc at hl
      have e0 : decodeDriver sc h enc code a (k + 1) pos rest out =
          (match decodeHandlerCall h enc code a (pos + s) (pos + e) why with
            | .error x => .error x
            | .ok (rep, newpos) =>
              decodeDriver sc h enc code a k newpos (a.drop newpos) (out ++ rep)) := by
        simp only [decodeDriver, hs]
        generalize decodeHandlerCall h enc code a (pos + s) (pos + e) why = d
        cases d <;> rfl
      have e2 : decodeDriver sf h enc code (a ++ t) (k + 1 + g) pos (rest ++ t) out =
          (match decodeHandlerCall h enc code (a ++ t) (pos + s) (pos + e) why with
            | .error x => .error x
            | .ok (rep, newpos) =>
              decodeDriver sf h enc code (a ++ t) (k + g) newpos ((a ++ t).drop newpos) (out ++ rep)) := by
        rw [ek]
        simp only [decodeDriver, hf]
        generalize decodeHandlerCall h enc code (a ++ t) (pos + s) (pos + e) why = d
        cases d <;> rfl
      rw [e0, e2]
      cases hd : decodeHandlerCall h enc code a (pos + s) (pos + e) why with
      | error x =>
        rw [hd] at hl
        obtain ⟨y, hy⟩ := hl
        rw [hy]
        exact ⟨y, rfl⟩
      | ok r =>
        obtain ⟨w, np⟩ := r
        rw [hd] at hl
        dsimp only at hl
        rw [hl]
        dsimp only
        have hstop : pos + e ≤ a.length := by omega
        have hnp := handler_moves (by omega) hd
        have hbd := decodeHandler_bound hstop hd
        have hdp : (a ++ t).drop np = a.drop np ++ t := List.drop_append_of_le_length hbd
        rw [hdp]
        have hne : rest ≠ [] := by
          intro he0
          rw [he0, hc.nil] at hs
          cases hs
        have hl0 := List.length_pos_iff.2 hne
        exact ih g np (a.drop np) (out ++ w) rfl hbd (by simp; omega)

/-- Two chunks against one shot, for a decoder that satisfies the three conditions. -/
theorem driver_chunks {sc sf : List Nat → DStep} (hc : Moves sc) (hf : Moves sf) (h : ErrHandler)
    (enc : String) (code : EncCode) (a t : Bytes)
    (hA : ∀ i, Agree (sc (a.drop i)) (sf (a.drop i ++ t)) (a.drop i).length)
    (hL : ∀ i why s e, sc (a.drop i) = .fail why s e → handlerLoc h enc code a t (i + s) (i + e) why) :
    match decodeDriver sc h enc code a (a.length + 1) 0 a [] with
    | .ok (s1, n) =>
      n ≤ a.length ∧
      match decodeDriver sf h enc code (a.drop n ++ t) ((a.drop n ++ t).length + 1) 0
          (a.drop n ++ t) [] with
      | .ok (s2, m) =>
        decodeDriver sf h enc code (a ++ t) ((a ++ t).length + 1) 0 (a ++ t) [] = .ok (s1 ++ s2, n + m)
      | .error _ =>
        ∃ x, decodeDriver sf h enc code (a ++ t) ((a ++ t).length + 1) 0 (a ++ t) [] = .error x
    | .error _ =>
      ∃ x, decodeDriver sf h enc code (a ++ t) ((a ++ t).length + 1) 0 (a ++ t) [] = .error x := by
  have hstable := driver_stable hf h enc code (a ++ t) ((a ++ t).length + 1) (a.length + 1 + ((a ++ t).length + 1))
    0 (a ++ t) [] (by simp) (by omega) (by omega)
  have cut := driver_cut hc h enc code a t hA hL (a.length + 1) ((a ++ t).length + 1) 0 a [] (by simp)
    (by omega) (by omega)
  rw [hstable]
  cases hd : decodeDriver sc h enc code a (a.length + 1) 0 a [] with
  | error x =>
    rw [hd] at cut
    exact cut
  | ok r =>
    obtain ⟨s1, n⟩ := r
    rw [hd] at cut
    obtain ⟨hn, g', hg, hrun⟩ := cut
    dsimp only
    refine ⟨hn, ?_⟩
    rw [hrun]
    have hsplit : a.take n ++ (a.drop n ++ t) = a ++ t := by
      rw [← List.append_assoc, List.take_append_drop]
    have hlen : (a.take n).length = n := List.length_take_of_le hn
    have hq : (a.drop n ++ t).length < g' := by
      have : (a.drop n ++ t).length ≤ (a ++ t).length := by simp <;> omega
      omega
    have hsh := driver_shift sf h enc code (a.take n) (a.drop n ++ t) g' 0 (a.drop n ++ t) s1 []
    rw [hsplit, hlen, Nat.add_zero] at hsh
    have hst := driver_stable hf h enc code (a.drop n ++ t) ((a.drop n ++ t).length + 1) g' 0
      (a.drop n ++ t) [] (by simp) (by omega) hq
    rw [hst]
    cases h2 : decodeDriver sf h enc code (a.drop n ++ t) g' 0 (a.drop n ++ t) [] with
    | error x =>
      rw [h2] at hsh
      cases h3 : decodeDriver sf h enc code (a ++ t) g' n (a.drop n ++ t) s1 with
      | error y => exact ⟨y, rfl⟩
      | ok w =>
        rw [h3] at hsh
        exact hsh.elim
    | ok r2 =>
      obtain ⟨s2, m⟩ := r2
      rw [h2] at hsh
      cases h3 : decodeDriver sf h enc code (a ++ t) g' n (a.drop n ++ t) s1 with
      | error y =>
        rw [h3] at hsh
        exact hsh.elim
      | ok w =>
        obtain ⟨s3, m3⟩ := w
        rw [h3] at hsh
        obtain ⟨u, e1, e2, e3⟩ := hsh
        dsimp only
        simp only [List.nil_append] at e2
        rw [e1, e3, e2]

/-- Two chunks against one shot, as an incremental decoder uses a stateful one. `dec b final` is the
decoder. The first chunk goes in with `final` false. What it left, and the rest, go in with `final`
true. That gives what everything at once gives, and raises if that raises. If the first chunk
raises, so does everything at once. `Exception` values differ: they name their own input. -/
def Chunked (dec : Bytes → Bool → Py (Str × Nat)) (b : Bytes) (k : Nat) : Prop :=
  match dec (b.take k) false with
  | .ok (s1, n) =>
    match dec (b.drop n) true with
    | .ok (s2, m) => dec b true = .ok (s1 ++ s2, n + m)
    | .error _ => ∃ x, dec b true = .error x
  | .error _ => ∃ x, dec b true = .error x

theorem chunked_driver {sc sf : List Nat → DStep} (hc : Moves sc) (hf : Moves sf) (h : ErrHandler)
    (enc : String) (code : EncCode) (b : Bytes) (k : Nat)
    (hA : ∀ i, Agree (sc ((b.take k).drop i)) (sf ((b.take k).drop i ++ b.drop k))
      ((b.take k).drop i).length)
    (hL : ∀ i why s e, sc ((b.take k).drop i) = .fail why s e →
      handlerLoc h enc code (b.take k) (b.drop k) (i + s) (i + e) why)
    (dec : Bytes → Bool → Py (Str × Nat))
    (hd : ∀ x, dec x false = decodeDriver sc h enc code x (x.length + 1) 0 x [])
    (he : ∀ x, dec x true = decodeDriver sf h enc code x (x.length + 1) 0 x []) :
    Chunked dec b k := by
  have main := driver_chunks hc hf h enc code (b.take k) (b.drop k) hA hL
  rw [List.take_append_drop] at main
  unfold Chunked
  rw [hd, he]
  cases h1 : decodeDriver sc h enc code (b.take k) ((b.take k).length + 1) 0 (b.take k) [] with
  | error x =>
    rw [h1] at main
    exact main
  | ok r =>
    obtain ⟨s1, n⟩ := r
    rw [h1] at main
    obtain ⟨hn, hrest⟩ := main
    have hsplit : (b.take k).drop n ++ b.drop k = b.drop n := by
      conv => rhs; rw [← List.take_append_drop k b]
      rw [List.drop_append_of_le_length hn]
    rw [hsplit] at hrest
    dsimp only
    rw [he]
    exact hrest

end PyLean.UnicodeObj
