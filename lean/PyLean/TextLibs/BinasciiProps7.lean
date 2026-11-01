import PyLean.TextLibs.BinasciiProps6

/-!
The multi-line interface. `encodebytes` cuts its input at every 57 bytes, and the lines join up in
the decoder because 57 is a multiple of 3, which leaves no padding before the last line. The file
functions `encode` and `decode` run over scripted files whose `read`, `readline` and `write` can
return short, raise, or stop early.
-/

namespace PyLean.TextLibs.Binascii

open PyLean

set_option linter.unusedSimpArgs false

/-! ### `casefold` and `map01` -/

theorem upper_length (s : List Nat) : (upper s).length = s.length := by
  simp [upper]

/-- `b32decode`'s two options rewrite the input before anything is decoded, `map01` first: with
`casefold`, a `map01` of `b'l'` still reads as `L`. The hypothesis is the function's own assertion
that `map01` is one byte. -/
def B32OptionLaw : Prop :=
  ∀ (alpha s m : List Nat), m.length = 1 →
    b32decode alpha (.bytes s) true (some (.bytes m)) =
      b32decode alpha (.bytes (upper (translate [48, 49] (79 :: m) s))) false none

theorem b32OptionLaw_proven : B32OptionLaw := by
  intro alpha s m hm
  have h1 : (upper (translate [48, 49] (79 :: m) s)).length = s.length := by
    rw [upper_length]
    simp [translate]
  simp only [b32decode, bytesFromDecodeData, bind, Except.bind, pure, Except.pure, hm, h1,
    Bool.false_eq_true, if_true, if_false, ne_eq, not_true_eq_false]

/-! ### Lenient decoding is a fold -/

/-- One byte of the lenient loop. -/
def stepL (st : Dec) (c : Nat) : Dec :=
  if c = 61 then { st with pads := st.pads + 1 }
  else if a2bChar c ≥ 64 then st
  else decStep { st with pads := 0 } (a2bChar c)

theorem lenient_fold (s : List Nat) : ∀ (i : Nat) (st : Dec),
    a2bLoop false s i st = .ok (s.foldl stepL st) := by
  induction s with
  | nil => intro _ _; rfl
  | cons c cs ih =>
    intro i st
    rw [List.foldl_cons, ← ih (i + 1)]
    unfold stepL
    rw [a2bLoop]
    by_cases h : c = 61
    · simp [h]
    · by_cases hv : a2bChar c ≥ 64
      · simp [h, hv]
      · simp [h, hv]

theorem lenient_append (a b : List Nat) (i j : Nat) (st st' : Dec)
    (h : a2bLoop false a i st = .ok st') : a2bLoop false (a ++ b) j st = a2bLoop false b i st' := by
  rw [lenient_fold] at h
  cases h
  rw [lenient_fold, lenient_fold, List.foldl_append]

theorem stepL_newline (st : Dec) : stepL st 10 = st := rfl

theorem lenient_newline (i : Nat) (st : Dec) : a2bLoop false [10] i st = .ok st := by
  rw [lenient_fold]
  rfl

theorem b2aBase64_true (d : List Nat) : b2aBase64 d true = enc d 0 ++ [10] := by
  simp [b2aBase64, enc]

/-- A multiple of three bytes leaves the decoder on a group boundary, whatever `leftchar` held. -/
theorem three_clean : ∀ (n : Nat) (d : List Nat), d.length ≤ n → d.length % 3 = 0 →
    (∀ x ∈ d, x < 256) → ∀ (left i l0 : Nat) (o : List Nat),
    ∃ l', a2bLoop false (enc d left) i ⟨0, 0, l0, o⟩ = .ok ⟨0, 0, l', o ++ d⟩ := by
  intro n
  induction n with
  | zero =>
    intro d h _ _ left i l0 o
    have : d = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    exact ⟨l0, by simp; rfl⟩
  | succ n ih =>
    intro d h h3 hb left i l0 o
    match d, h, h3, hb with
    | [], _, _, _ => exact ⟨l0, by simp; rfl⟩
    | [a], _, h3, _ => simp at h3
    | [a, b], _, h3, _ => simp at h3
    | a :: b :: c :: r, h, h3, hb =>
      have ha' : a < 256 := hb a (by simp)
      have hb' : b < 256 := hb b (by simp)
      have hc : c < 256 := hb c (by simp)
      rw [enc_three a b c ha' hb' hc, a2bLoop_group false a b c ha' hb' hc]
      obtain ⟨l', h1⟩ := ih r (by simp at h; omega) (by simp at h3; omega)
        (fun x hx => hb x (by simp [hx])) (L c (L b (L a left))) (i + 1 + 1 + 1 + 1) 0
        (o ++ [a, b, c])
      exact ⟨l', by rw [h1]; simp⟩

theorem stream_nil (f : Nat) : encodeStream f [] = [] := by
  cases f <;> rfl

theorem stream_cons (f x : Nat) (t : List Nat) :
    encodeStream (f + 1) (x :: t) =
      b2aBase64 ((x :: t).take MAXBINSIZE) true ++ encodeStream f ((x :: t).drop MAXBINSIZE) := rfl

theorem drop_lt (x : Nat) (t : List Nat) :
    ((x :: t).drop MAXBINSIZE).length + 1 ≤ (x :: t).length := by
  simp only [List.length_drop, List.length_cons, MAXBINSIZE]
  omega

theorem stream_fuel : ∀ (f g : Nat) (s : List Nat), s.length + 1 ≤ f → s.length + 1 ≤ g →
    encodeStream f s = encodeStream g s := by
  intro f
  induction f with
  | zero => intro g s h; omega
  | succ f ih =>
    intro g s h1 h2
    match g, s with
    | 0, _ => omega
    | g + 1, [] => rw [stream_nil, stream_nil]
    | g + 1, x :: t =>
      have := drop_lt x t
      rw [stream_cons, stream_cons, ih g _ (by omega) (by omega)]

/-- `encodebytes` by its first line. -/
theorem encodebytes_cons (d : List Nat) (h : d ≠ []) :
    encodebytes d = b2aBase64 (d.take MAXBINSIZE) true ++ encodebytes (d.drop MAXBINSIZE) := by
  match d, h with
  | x :: t, _ =>
    show encodeStream ((x :: t).length + 1) (x :: t) = _
    rw [show (x :: t).length + 1 = t.length + 1 + 1 from rfl, stream_cons]
    congr 1
    have := drop_lt x t
    simp only [List.length_cons] at this
    exact stream_fuel _ _ _ (by omega) (Nat.le_refl _)

theorem stream_go : ∀ (n : Nat) (s : List Nat), s.length ≤ n → (∀ x ∈ s, x < 256) →
    ∀ (f i l0 : Nat) (o : List Nat), s.length + 1 ≤ f →
    ∃ st, a2bLoop false (encodeStream f s) i ⟨0, 0, l0, o⟩ = .ok st ∧ Finished st (o ++ s) := by
  intro n
  induction n with
  | zero =>
    intro s h _ f i l0 o _
    have : s = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    exact ⟨_, by rw [stream_nil]; rfl, by simp [Finished]⟩
  | succ n ih =>
    intro s h hb f i l0 o hf
    match s, h, hb, hf with
    | [], _, _, _ => exact ⟨_, by rw [stream_nil]; rfl, by simp [Finished]⟩
    | x :: t, h, hb, hf =>
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp at hf; omega⟩
      rw [stream_cons, b2aBase64_true]
      generalize hs : x :: t = s at *
      have hsb : ∀ y ∈ s.take MAXBINSIZE, y < 256 := fun y hy => hb y (List.mem_of_mem_take hy)
      by_cases hl : s.length ≤ MAXBINSIZE
      · rw [List.take_of_length_le hl, List.drop_of_length_le hl, stream_nil, List.append_nil]
        obtain ⟨st, h1, h2⟩ := roundtrip_go false s.length s (Nat.le_refl _) hb 0 i l0 o
        exact ⟨st, by rw [lenient_append _ _ i i _ _ h1, lenient_newline], h2⟩
      · have h57 : (s.take MAXBINSIZE).length = MAXBINSIZE := by
          simp only [List.length_take]
          omega
        obtain ⟨l', h1⟩ := three_clean _ (s.take MAXBINSIZE) (Nat.le_refl _)
          (by rw [h57]; rfl) hsb 0 i l0 o
        have hdl : (s.drop MAXBINSIZE).length + 1 ≤ g := by
          simp only [List.length_drop, MAXBINSIZE] at hl hf ⊢
          omega
        obtain ⟨st, h2, h3⟩ := ih (s.drop MAXBINSIZE)
          (by simp only [List.length_drop, MAXBINSIZE] at hl h ⊢; omega)
          (fun y hy => hb y (List.mem_of_mem_drop hy)) g i l' (o ++ s.take MAXBINSIZE) hdl
        refine ⟨st, ?_, ?_⟩
        · rw [List.append_assoc, lenient_append _ _ i i _ _ h1, List.singleton_append,
            lenient_fold, List.foldl_cons, stepL_newline, ← lenient_fold _ i]
          exact h2
        · have := List.take_append_drop MAXBINSIZE s
          rwa [List.append_assoc, this] at h3

/-- `decodebytes(encodebytes(d)) == d`, for every `bytes` value. -/
def DecodebytesRoundTrip : Prop :=
  ∀ d : List Nat, (∀ x ∈ d, x < 256) → decodebytes (encodebytes d) = .ok d

theorem finished_decode (s want : List Nat) (st : Dec) (h1 : a2bLoop false s 0 {} = .ok st)
    (h2 : Finished st want) : a2bBase64 false (.bytes s) = .ok want := by
  obtain ⟨h2, h3, h4⟩ := h2
  simp only [a2bBase64, asciiBuffer, a2bBase64Bytes, bind, Except.bind, pure, Except.pure]
  rw [h1]
  simp only [if_neg h3, if_neg h4, h2]

theorem decodebytesRoundTrip_proven : DecodebytesRoundTrip := by
  intro d hd
  obtain ⟨st, h1, h2⟩ := stream_go d.length d (Nat.le_refl _) hd (d.length + 1) 0 0 [] (Nat.le_refl _)
  exact finished_decode _ d st h1 (by simpa using h2)

/-- A line of `b2a_base64` decodes by itself. -/
theorem line_roundtrip (c : List Nat) (hc : ∀ x ∈ c, x < 256) :
    a2bBase64 false (.bytes (b2aBase64 c true)) = .ok c := by
  obtain ⟨st, h1, h2⟩ := roundtrip_go false c.length c (Nat.le_refl _) hc 0 0 0 []
  have h3 : a2bLoop false (enc c 0 ++ [10]) 0 ⟨0, 0, 0, []⟩ = .ok st := by
    rw [lenient_append _ _ 0 0 _ _ h1, lenient_newline]
  rw [b2aBase64_true]
  exact finished_decode _ c st h3 (by simpa using h2)

/-- Every line `encodebytes` writes but the last holds exactly 76 characters and its newline. -/
def EncodebytesLineLength : Prop :=
  ∀ d : List Nat, (∀ x ∈ d, x < 256) → MAXBINSIZE < d.length →
    (encodebytes d).take 77 = enc (d.take MAXBINSIZE) 0 ++ [10] ∧
      (enc (d.take MAXBINSIZE) 0).length = 76

theorem encodebytesLineLength_proven : EncodebytesLineLength := by
  intro d hd hl
  have hne : d ≠ [] := by
    intro h
    subst h
    simp at hl
  have h57 : (d.take MAXBINSIZE).length = MAXBINSIZE := by
    simp only [List.length_take]
    omega
  have hlen : (enc (d.take MAXBINSIZE) 0).length = 76 := by
    rw [enc_length _ _ (Nat.le_refl _) (fun y hy => hd y (List.mem_of_mem_take hy)), h57]
    rfl
  refine ⟨?_, hlen⟩
  rw [encodebytes_cons d hne, b2aBase64_true, List.take_append, List.take_of_length_le (by
    simp [hlen])]
  simp [hlen]

/-! ### Scripted files -/

/-- `read` keeps the file contract the code relies on: it returns nothing only at end of file. -/
def Steady (f : FileSim) : Prop := ∀ st ∈ f.reads, st ≠ .give 0

theorem read_law (f : FileSim) (n : Nat) (hn : 1 ≤ n) (hs : Steady f) :
    (∃ e g, f.read n = (g, .error e) ∧ g.data = f.data ∧ g.written = f.written ∧
      g.writes = f.writes ∧ .raises e ∈ f.reads ∧ ∀ x ∈ g.reads, x ∈ f.reads) ∨
    (∃ m g, 1 ≤ m ∧ m ≤ n ∧ f.read n = (g, .ok (f.data.take m)) ∧ g.data = f.data.drop m ∧
      g.written = f.written ∧ g.writes = f.writes ∧ ∀ x ∈ g.reads, x ∈ f.reads) := by
  unfold FileSim.read
  match h : f.reads with
  | [] => exact .inr ⟨n, _, hn, Nat.le_refl _, rfl, rfl, rfl, rfl, fun x hx => hx⟩
  | .raises e :: r =>
    exact .inl ⟨e, _, rfl, rfl, rfl, rfl, by simp, fun x hx => by simp [hx]⟩
  | .give k :: r =>
    have hk : k ≠ 0 := by
      intro h0
      subst h0
      exact hs (.give 0) (by simp [h]) rfl
    exact .inr ⟨min k n, _, by omega, by omega, rfl, rfl, rfl, rfl, fun x hx => by simp [hx]⟩

theorem write_law (f : FileSim) (line : List Nat) :
    (∃ g, f.write line = (g, .ok ()) ∧ g.data = f.data ∧ g.reads = f.reads ∧
      g.written = f.written ++ [line] ∧ ∀ x ∈ g.writes, x ∈ f.writes) ∨
    (∃ g e, f.write line = (g, .error e) ∧ g.written = f.written ++ [line] ∧ .error e ∈ f.writes) := by
  unfold FileSim.write
  match h : f.writes with
  | [] =>
    exact .inl ⟨{ f with written := f.written ++ [line] }, by simp [h], rfl, rfl, rfl,
      fun x hx => by simp [h] at hx⟩
  | .error e :: r =>
    exact .inr ⟨{ f with written := f.written ++ [line], writes := r }, e, by simp [h], rfl,
      by simp [h]⟩
  | .ok () :: r =>
    exact .inl ⟨{ f with written := f.written ++ [line], writes := r }, by simp [h], rfl, rfl, rfl,
      fun x hx => by simp [h, hx]⟩

theorem fillChunk_succ (fuel : Nat) (f : FileSim) (s : List Nat) :
    fillChunk (fuel + 1) f s =
      if s.length < MAXBINSIZE then
        match f.read (MAXBINSIZE - s.length) with
        | (f, .error e) => (f, .error e)
        | (f, .ok ns) => if ns.isEmpty then (f, .ok s) else fillChunk fuel f (s ++ ns)
      else (f, .ok s) := rfl

/-- The inner loop: it stops with `MAXBINSIZE` bytes or at end of file. -/
theorem fill_go : ∀ (n : Nat) (f : FileSim) (s : List Nat), MAXBINSIZE - s.length ≤ n →
    s.length ≤ MAXBINSIZE → Steady f → ∀ fuel, n + 1 ≤ fuel →
    ∃ g r, fillChunk fuel f s = (g, r) ∧ g.written = f.written ∧ g.writes = f.writes ∧
      (∀ x ∈ g.reads, x ∈ f.reads) ∧
      (∀ s', r = .ok s' → s' = (s ++ f.data).take MAXBINSIZE ∧
        g.data = (s ++ f.data).drop MAXBINSIZE) ∧
      (∀ e, r = .error e → .raises e ∈ f.reads ∧ g.data ++ [] = g.data) := by
  intro n
  induction n with
  | zero =>
    intro f s h1 h2 _ fuel hf
    obtain ⟨g, rfl⟩ : ∃ g, fuel = g + 1 := ⟨fuel - 1, by omega⟩
    have h57 : s.length = MAXBINSIZE := by omega
    rw [fillChunk_succ, if_neg (by omega)]
    refine ⟨_, _, rfl, rfl, rfl, fun x hx => hx, ?_, by simp⟩
    intro s' hs
    cases hs
    simp [List.take_append, List.drop_append, h57]
  | succ n ih =>
    intro f s h1 h2 hs fuel hf
    obtain ⟨g, rfl⟩ : ∃ g, fuel = g + 1 := ⟨fuel - 1, by omega⟩
    rw [fillChunk_succ]
    by_cases hlt : s.length < MAXBINSIZE
    · rw [if_pos hlt]
      rcases read_law f (MAXBINSIZE - s.length) (by omega) hs with
        ⟨e, g', h3, _, h5, h6, h7, h8⟩ | ⟨m, g', hm1, hm2, h3, h4, h5, h6, h8⟩
      · rw [h3]
        exact ⟨_, _, rfl, h5, h6, h8, by simp, fun e' he => by cases he; exact ⟨h7, by simp⟩⟩
      · rw [h3]
        by_cases hd : f.data = []
        · simp only [hd, List.take_nil, List.isEmpty_nil, if_true]
          rw [hd] at h4
          refine ⟨_, _, rfl, h5, h6, h8, ?_, by simp⟩
          intro s' he
          cases he
          simp [hd, h4, List.take_of_length_le h2, List.drop_of_length_le h2]
        · have hne : (f.data.take m).isEmpty = false := by
            cases hf' : f.data with
            | nil => exact absurd hf' hd
            | cons y t =>
              obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
              rfl
          have hll : (f.data.take m).length ≤ m := by simp only [List.length_take]; omega
          have hl1 : 1 ≤ (f.data.take m).length := by
            cases hk : f.data.take m with
            | nil => simp [hk] at hne
            | cons y t => simp
          simp only [hne, Bool.false_eq_true, if_false]
          have hs' : Steady g' := fun st hst => hs st (h8 st hst)
          obtain ⟨g2, r, h9, h10, h11, h12, h13, h14⟩ := ih g' (s ++ f.data.take m)
            (by simp only [List.length_append] at *; omega)
            (by simp only [List.length_append]; omega) hs' g (by omega)
          refine ⟨g2, r, h9, h10.trans h5, h11.trans h6, fun x hx => h8 x (h12 x hx), ?_, ?_⟩
          · intro s' he
            have := h13 s' he
            rwa [h4, List.append_assoc, List.take_append_drop] at this
          · intro e he
            exact ⟨h8 _ (h14 e he).1, by simp⟩
    · rw [if_neg hlt]
      have h57 : s.length = MAXBINSIZE := by omega
      refine ⟨_, _, rfl, rfl, rfl, fun x hx => hx, ?_, by simp⟩
      intro s' he
      cases he
      simp [List.take_append, List.drop_append, h57]

theorem encodeFile_succ (fuel : Nat) (f : FileSim) :
    encodeFile (fuel + 1) f =
      match f.read MAXBINSIZE with
      | (f, .error e) => (f, .error e)
      | (f, .ok s) =>
        if s.isEmpty then (f, .ok ())
        else
          match fillChunk (MAXBINSIZE + 1) f s with
          | (f, .error e) => (f, .error e)
          | (f, .ok s) =>
            match f.write (b2aBase64 s true) with
            | (f, .error e) => (f, .error e)
            | (f, .ok ()) => encodeFile fuel f := rfl

/-- What a run of `encode` leaves: the lines written are a prefix of `encodebytes` of the input,
all of it on success, and a failure is one the file raised. -/
def EncodeOut (f g : FileSim) (r : Py Unit) : Prop :=
  ∃ ext : List (List Nat), g.written = f.written ++ ext ∧
    (∃ rest, ext.flatten ++ rest = encodebytes f.data) ∧
    (r = .ok () → ext.flatten = encodebytes f.data) ∧
    (∀ e, r = .error e → .raises e ∈ f.reads ∨ .error e ∈ f.writes)

theorem encode_go : ∀ (n : Nat) (f : FileSim), f.data.length ≤ n → Steady f →
    ∀ fuel, n + 1 ≤ fuel → ∃ g r, encodeFile fuel f = (g, r) ∧ EncodeOut f g r := by
  intro n
  induction n with
  | zero => ?_
  | succ n ih => ?_
  all_goals
    intro f hn hs fuel hf
    obtain ⟨h, rfl⟩ : ∃ h, fuel = h + 1 := ⟨fuel - 1, by omega⟩
    rw [encodeFile_succ]
    rcases read_law f MAXBINSIZE (by decide) hs with
      ⟨e, g', h3, _, h5, h6, h7, h8⟩ | ⟨m, g', hm1, hm2, h3, h4, h5, h6, h8⟩
    · rw [h3]
      exact ⟨_, _, rfl, [], by simp [h5], ⟨_, rfl⟩, by simp, fun e' he => by cases he; exact .inl h7⟩
  case zero =>
    have hd : f.data = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [h3, hd]
    simp only [List.take_nil, List.isEmpty_nil, if_true]
    refine ⟨_, _, rfl, [], by simp [h5], ⟨[], ?_⟩, ?_, by simp⟩
    · simp [hd, encodebytes, stream_nil]
    · intro _
      simp [hd, encodebytes, stream_nil]
  case succ =>
    rw [h3]
    by_cases hd : f.data = []
    · simp only [hd, List.take_nil, List.isEmpty_nil, if_true]
      refine ⟨_, _, rfl, [], by simp [h5], ⟨[], ?_⟩, ?_, by simp⟩
      · simp [hd, encodebytes, stream_nil]
      · intro _
        simp [hd, encodebytes, stream_nil]
    · have hne : (f.data.take m).isEmpty = false := by
        cases hf' : f.data with
        | nil => exact absurd hf' hd
        | cons y t =>
          obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
          rfl
      have hl1 : 1 ≤ (f.data.take m).length := by
        cases hk : f.data.take m with
        | nil => simp [hk] at hne
        | cons y t => simp
      have hll : (f.data.take m).length ≤ m := by simp only [List.length_take]; omega
      simp only [hne, Bool.false_eq_true, if_false]
      have hs' : Steady g' := fun st hst => hs st (h8 st hst)
      obtain ⟨g1, r1, h9, h10, h11, h12, h13, h14⟩ := fill_go 56 g' (f.data.take m)
        (by simp only [MAXBINSIZE] at *; omega) (by omega) hs' (MAXBINSIZE + 1) (by decide)
      rw [h9]
      rw [h4, List.take_append_drop] at h13
      have hfull := encodebytes_cons f.data hd
      cases r1 with
      | error e =>
        exact ⟨_, _, rfl, [], by simp [h10, h5], ⟨_, rfl⟩, by simp,
          fun e' he => by cases he; exact .inl (h8 _ (h14 e rfl).1)⟩
      | ok s' =>
        obtain ⟨h15, h16⟩ := h13 s' rfl
        rw [h15]
        have hlen : (f.data.drop MAXBINSIZE).length ≤ n := by
          have : 1 ≤ f.data.length := by
            cases hf' : f.data with
            | nil => exact absurd hf' hd
            | cons y t => simp
          simp only [List.length_drop, MAXBINSIZE]
          omega
        dsimp only
        rcases write_law g1 (b2aBase64 (f.data.take MAXBINSIZE) true) with
          ⟨g2, h17, h18, h19, h20, h21⟩ | ⟨g2, e, h17, h20, h21⟩
        · rw [h17]
          have hsg : Steady g2 := fun st hst => hs st (h8 _ (h12 st (h19 ▸ hst)))
          obtain ⟨g3, r, h22, ext, h23, ⟨rest, h24⟩, h25, h26⟩ :=
            ih g2 (by rw [h18, h16]; exact hlen) hsg h (by omega)
          rw [h18, h16] at h24 h25
          refine ⟨g3, r, h22, b2aBase64 (f.data.take MAXBINSIZE) true :: ext, ?_, ⟨rest, ?_⟩, ?_, ?_⟩
          · rw [h23, h20, h10, h5]
            simp
          · rw [hfull, ← h24]
            simp
          · intro hr
            rw [hfull, ← h25 hr]
            simp
          · intro e he
            rcases h26 e he with h27 | h27
            · exact .inl (h8 _ (h12 _ (h19 ▸ h27)))
            · exact .inr (by rw [← h6, ← h11]; exact h21 _ h27)
        · rw [h17]
          refine ⟨_, _, rfl, [b2aBase64 (f.data.take MAXBINSIZE) true], ?_,
            ⟨encodebytes (f.data.drop MAXBINSIZE), ?_⟩, by simp, ?_⟩
          · rw [h20, h10, h5]
          · rw [hfull]
            simp
          · intro e' he
            cases he
            exact .inr (by rw [← h6, ← h11]; exact h21)

/-- `base64.encode` over a file that may return short reads, with or without failures, writes a
prefix of `encodebytes(data)`, and all of it unless the file raised. The hypothesis is the file
contract the docs state: `read` returns nothing only at end of file. `encode_go` does not need the
file to be well behaved in any other way. -/
def EncodeFileLaw : Prop :=
  ∀ f : FileSim, Steady f → ∀ fuel, f.data.length + 1 ≤ fuel →
    ∃ g r, encodeFile fuel f = (g, r) ∧ EncodeOut f g r

theorem encodeFileLaw_proven : EncodeFileLaw :=
  fun f hs fuel hf => encode_go f.data.length f (Nat.le_refl _) hs fuel hf

/-- With no failing call, `encode` is `encodebytes`. -/
def EncodeFileAgrees : Prop :=
  ∀ f : FileSim, Steady f → (∀ e, .raises e ∉ f.reads) → (∀ e, .error e ∉ f.writes) →
    ∀ fuel, f.data.length + 1 ≤ fuel →
    ∃ g ext, encodeFile fuel f = (g, .ok ()) ∧ g.written = f.written ++ ext ∧
      ext.flatten = encodebytes f.data

theorem encodeFileAgrees_proven : EncodeFileAgrees := by
  intro f hs h1 h2 fuel hf
  obtain ⟨g, r, h3, ext, h4, _, h5, h6⟩ := encodeFileLaw_proven f hs fuel hf
  cases r with
  | error e =>
    rcases h6 e rfl with h7 | h7
    · exact absurd h7 (h1 e)
    · exact absurd h7 (h2 e)
  | ok u =>
    cases u
    exact ⟨g, ext, h3, h4, h5 rfl⟩

/-- A file that returns nothing before its end cuts `encode` short, with no error: the only way
out of the file contract above, on record. -/
def EncodeEmptyReadStops : Prop :=
  ∀ f : FileSim, f.reads = [.give 0] → ∀ fuel,
    (encodeFile (fuel + 1) f).2 = .ok () ∧ (encodeFile (fuel + 1) f).1.written = f.written

theorem encodeEmptyReadStops_proven : EncodeEmptyReadStops := by
  intro f h fuel
  have : f.read MAXBINSIZE = ({ f with reads := [], data := f.data }, .ok []) := by
    unfold FileSim.read
    simp [h]
  rw [encodeFile_succ, this]
  exact ⟨rfl, rfl⟩

/-! ### `decode` -/

theorem b2aDrain_no_nl (left : Nat) : ∀ (fuel bits : Nat), 10 ∉ (b2aDrain left fuel bits).1 := by
  intro fuel
  induction fuel with
  | zero => intro _; simp [b2aDrain]
  | succ fuel ih =>
    intro bits
    simp only [b2aDrain]
    split
    · have hc : ∀ v, v < 64 → b2aChar v ≠ 10 := by decide
      have := hc (left / 2 ^ (bits - 6) % 64) (by omega)
      simp only [List.mem_cons, not_or]
      refine ⟨fun h => this h.symm, ih _⟩
    · simp

theorem b2aLoop_no_nl (d : List Nat) : ∀ (l b : Nat), 10 ∉ (b2aLoop d l b).1 := by
  induction d with
  | nil => intro _ _; simp [b2aLoop]
  | cons x r ih =>
    intro l b
    simp only [b2aLoop, List.mem_append, not_or]
    exact ⟨b2aDrain_no_nl _ _ _, ih _ _⟩

theorem enc_no_nl (d : List Nat) (left : Nat) : 10 ∉ enc d left := by
  have hc : ∀ v, v < 64 → b2aChar v ≠ 10 := by decide
  rw [enc_eq]
  simp only [List.mem_append, not_or]
  refine ⟨b2aLoop_no_nl _ _ _, ?_⟩
  split
  · have := hc ((b2aLoop d left 0).2.1 % 4 * 16) (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨fun h => this h.symm, by decide⟩
  · split
    · have := hc ((b2aLoop d left 0).2.1 % 16 * 4) (by omega)
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fun h => this h.symm, by decide⟩
    · simp

theorem findIdx_line (l : List Nat) (hl : 10 ∉ l) (rest : List Nat) :
    (l ++ 10 :: rest).findIdx? (· == 10) = some l.length := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    have hx : (x == 10) = false := by
      apply beq_false_of_ne
      intro h
      exact hl (by simp [h])
    have h2 : 10 ∉ t := fun h => hl (by simp [h])
    simp [List.findIdx?_cons, hx, ih h2]

/-- `readline` on one line of `b2a_base64`. -/
theorem splitLines_line (fuel : Nat) (c rest : List Nat) :
    splitLines (fuel + 1) (b2aBase64 c true ++ rest) =
      b2aBase64 c true :: splitLines fuel rest := by
  rw [b2aBase64_true]
  generalize he : enc c 0 = l
  have hn : 10 ∉ l := he ▸ enc_no_nl c 0
  have h1 : l ++ [10] ++ rest = l ++ 10 :: rest := by simp
  have h2 : ∃ x t, l ++ [10] ++ rest = x :: t := by
    cases l <;> exact ⟨_, _, rfl⟩
  obtain ⟨x, t, h3⟩ := h2
  have h4 : splitLines (fuel + 1) (x :: t) =
      match (x :: t).findIdx? (· == 10) with
      | some i => (x :: t).take (i + 1) :: splitLines fuel ((x :: t).drop (i + 1))
      | none => [x :: t] := rfl
  rw [h3, h4, ← h3, h1, findIdx_line l hn]
  simp only
  have h5 : (l ++ 10 :: rest).take (l.length + 1) = l ++ [10] := by
    simp [List.take_append]
    exact List.take_of_length_le (by omega)
  have h6 : (l ++ 10 :: rest).drop (l.length + 1) = rest := by
    simp [List.drop_append]
  rw [h5, h6]

theorem decodeFile_line (l c : List Nat) (ls : List (Py (List Nat))) (g h : FileSim)
    (hl : l.isEmpty = false) (h1 : a2bBase64 false (.bytes l) = .ok c)
    (h2 : g.write c = (h, .ok ())) :
    decodeFile (.ok l :: ls) g = decodeFile ls h := by
  simp only [decodeFile, hl, Bool.false_eq_true, if_false, h1, h2]

/-- `base64.decode` reads back what `base64.encode` wrote, with every line split as `readline`
splits it. -/
theorem decode_go : ∀ (n : Nat) (s : List Nat), s.length ≤ n → (∀ x ∈ s, x < 256) →
    ∀ (fe fs : Nat) (f : FileSim), f.writes = [] → s.length + 1 ≤ fe →
    (encodeStream fe s).length + 1 ≤ fs →
    ∃ g, decodeFile (((splitLines fs (encodeStream fe s)).map .ok) ++ [.ok []]) f = (g, .ok ()) ∧
      g.writes = [] ∧ g.written.flatten = f.written.flatten ++ s := by
  intro n
  induction n with
  | zero =>
    intro s h _ fe fs f hw _ hf
    have : s = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rw [stream_nil] at hf ⊢
    obtain ⟨k, rfl⟩ : ∃ k, fs = k + 1 := ⟨fs - 1, by simp at hf; omega⟩
    exact ⟨f, rfl, hw, by simp⟩
  | succ n ih =>
    intro s h hb fe fs f hw hfe hf
    match s, h, hb, hfe, hf with
    | [], _, _, _, hf =>
      rw [stream_nil] at hf ⊢
      obtain ⟨k, rfl⟩ : ∃ k, fs = k + 1 := ⟨fs - 1, by simp at hf; omega⟩
      exact ⟨f, rfl, hw, by simp⟩
    | x :: t, h, hb, hfe, hf =>
      obtain ⟨g, rfl⟩ : ∃ g, fe = g + 1 := ⟨fe - 1, by simp at hfe; omega⟩
      rw [stream_cons] at hf ⊢
      generalize hs : x :: t = s at *
      have hne : (b2aBase64 (s.take MAXBINSIZE) true).isEmpty = false := by
        rw [b2aBase64_true]
        simp
      have hl1 : 1 ≤ (b2aBase64 (s.take MAXBINSIZE) true).length := by
        cases hk : b2aBase64 (s.take MAXBINSIZE) true with
        | nil => simp [hk] at hne
        | cons y t => simp
      simp only [List.length_append] at hf
      obtain ⟨k, rfl⟩ : ∃ k, fs = k + 1 := ⟨fs - 1, by omega⟩
      have hline := line_roundtrip (s.take MAXBINSIZE) fun y hy => hb y (List.mem_of_mem_take hy)
      have hw2 : (f.write (s.take MAXBINSIZE)) =
          ({ f with written := f.written ++ [s.take MAXBINSIZE] }, .ok ()) := by
        unfold FileSim.write
        simp [hw]
      rw [splitLines_line, List.map_cons, List.cons_append]
      rw [decodeFile_line _ _ _ f _ hne hline hw2]
      have hd1 : 1 ≤ s.length := by rw [← hs]; simp
      obtain ⟨g2, h1, h2, h3⟩ := ih (s.drop MAXBINSIZE)
        (by simp only [List.length_drop, MAXBINSIZE] at h ⊢; omega)
        (fun y hy => hb y (List.mem_of_mem_drop hy)) g k
        { f with written := f.written ++ [s.take MAXBINSIZE] } hw
        (by simp only [List.length_drop, MAXBINSIZE] at hfe ⊢; omega) (by omega)
      refine ⟨g2, h1, h2, ?_⟩
      rw [h3]
      simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
        List.append_assoc, List.take_append_drop]

/-- `base64.decode` over the lines `readline` finds in `encodebytes(d)` writes `d` back. -/
def DecodeFileRoundTrip : Prop :=
  ∀ (d : List Nat) (f : FileSim), (∀ x ∈ d, x < 256) → f.writes = [] →
    ∃ g, decodeFile (((splitLines ((encodebytes d).length + 1) (encodebytes d)).map .ok) ++ [.ok []]) f =
        (g, .ok ()) ∧ g.written.flatten = f.written.flatten ++ d

theorem decodeFileRoundTrip_proven : DecodeFileRoundTrip := by
  intro d f hd hw
  obtain ⟨g, h1, _, h2⟩ := decode_go d.length d (Nat.le_refl _) hd (d.length + 1)
    ((encodebytes d).length + 1) f hw (Nat.le_refl _) (Nat.le_refl _)
  exact ⟨g, h1, h2⟩

/-- A failure stops `decode` at once: nothing after it is read, decoded or written. -/
def DecodeFileStops : Prop :=
  ∀ (e : PyExc) (ls after : List (Py (List Nat))) (f : FileSim),
    decodeFile (.error e :: after) f = (f, .error e) ∧
    (∀ l, l.isEmpty = false → (∀ c, a2bBase64 false (.bytes l) ≠ .ok c) →
      (decodeFile (.ok l :: after) f).1.written = f.written)

theorem decodeFileStops_proven : DecodeFileStops := by
  intro e _ after f
  refine ⟨rfl, fun l hl h => ?_⟩
  simp only [decodeFile, hl, Bool.false_eq_true, if_false]
  cases hd : a2bBase64 false (.bytes l) with
  | error e => rfl
  | ok c => exact absurd hd (h c)

/-- `decode` and `decodebytes` agree on the bytes of the file. They do not: `decode` passes each
line to `a2b_base64` alone, so a group split across lines is padding error for one and valid for
the other, though RFC 2045 lets lines break anywhere. -/
def DecodeAgreesDecodebytes : Prop :=
  ∀ (d out : List Nat), decodebytes d = .ok out →
    (decodeFile ((splitLines (d.length + 1) d).map .ok ++ [.ok []]) { data := [] }).2 = .ok ()

theorem decodeAgreesDecodebytes_refuted : ¬DecodeAgreesDecodebytes := by
  intro h
  have h2 := h [89, 87, 10, 74, 106, 10] [97, 98, 99] rfl
  have e : (decodeFile ((splitLines (6 + 1) [89, 87, 10, 74, 106, 10]).map .ok ++ [.ok []])
      { data := [] }).2 = .error (err "Incorrect padding") := rfl
  rw [show ([89, 87, 10, 74, 106, 10] : List Nat).length = 6 from rfl, e] at h2
  cases h2

end PyLean.TextLibs.Binascii
