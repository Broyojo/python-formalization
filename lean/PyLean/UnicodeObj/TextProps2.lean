import PyLean.UnicodeObj.TextProps

/-!
Properties of the text slice, second part: translate, maketrans, `isprintable`,
the `bytes` twins, the decimal transform, the bloom mask, dedent, simple vs. full
case mapping.
-/

namespace PyLean.UnicodeObj

open PyLean

/-! ## `isprintable` and `repr` -/

/-- `s.isprintable()` is the docstring's "`repr()` may use every character": for a
string without `'` and `\`, it holds exactly when `repr` copies each character
unchanged. Quantified over every string. -/
def IsPrintableRepr : Prop :=
  ∀ s : Str, (∀ c ∈ s, c ≠ 39 ∧ c ≠ 92) →
    (unicodeIsPrintable s = true ↔ ∀ c ∈ s, reprChar 39 c = [c])

theorem reprChar_self (c : Nat) (h1 : c ≠ 39) (h2 : c ≠ 92) :
    reprChar 39 c = [c] ↔ isPrintable c = true := by
  by_cases h128 : c < 128
  · have hp := (ascii_facts c h128).2.2.2.2.2.2.2.2.2.2.2
    rw [hp]
    simp only [reprChar]
    repeat' split
    all_goals simp_all <;> omega
  · simp only [reprChar]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega)]
    by_cases hp : isPrintable c = true
    · simp [hp]
    · simp only [Bool.not_eq_true] at hp
      simp only [hp, Bool.not_false, if_true, Bool.false_eq_true, iff_false]
      repeat' split
      all_goals simp [hexDigits]
      all_goals omega

theorem unicodeIsPrintable_all (s : Str) :
    unicodeIsPrintable s = s.all isPrintable := by
  match s with
  | [] => rfl
  | [c] => simp [unicodeIsPrintable]
  | a :: b :: t => rfl

theorem isPrintableRepr_proven : IsPrintableRepr := by
  intro s h
  rw [unicodeIsPrintable_all, List.all_eq_true]
  constructor
  · intro hp c hc
    exact (reprChar_self c (h c hc).1 (h c hc).2).2 (hp c hc)
  · intro hp c hc
    exact (reprChar_self c (h c hc).1 (h c hc).2).1 (hp c hc)

/-! ## `translate`: fast path vs. general path -/

/-- `str.translate` with a pure table, read as a function of each character in
turn: the first lookup that fails raises, otherwise the outputs are concatenated. -/
def translateSpec (m : Mapping) : List Nat → Py Str
  | [] => .ok []
  | c :: cs => do
    let w ← charmaptranslateOutput m c
    let t ← translateSpec m cs
    .ok (w.getD [] ++ t)

theorem collect_spec (m : Mapping) (cs : List Nat) :
    match collectUndefined m cs with
    | .error e => translateSpec m cs = .error e
    | .ok r => r.length ≤ cs.length ∧ translateSpec m cs = translateSpec m r := by
  induction cs with
  | nil => simp [collectUndefined]
  | cons x xs ih =>
    simp only [collectUndefined, translateSpec, charmaptranslateOutput]
    cases hl : charmaptranslateLookup m x with
    | error e => simp [bind, Except.bind]
    | ok v =>
      cases v with
      | pyNone =>
        simp only [bind, Except.bind, pure, Except.pure, Option.getD_none, List.nil_append]
        cases hc : collectUndefined m xs with
        | error e =>
          rw [hc] at ih
          simp [ih]
        | ok r =>
          rw [hc] at ih
          simp only at ih
          refine ⟨by simp; omega, ?_⟩
          rw [ih.2]
          cases translateSpec m r <;> rfl
      | null => simp [bind, Except.bind, pure, Except.pure, translateSpec, charmaptranslateOutput, hl]
      | long v => simp [bind, Except.bind, pure, Except.pure, translateSpec, charmaptranslateOutput, hl]
      | str s => simp [bind, Except.bind, pure, Except.pure, translateSpec, charmaptranslateOutput, hl]

/-- The output prefix a partial result carries. -/
def withPrefix (out : Str) (r : Py Str) : Py Str := r.map (out ++ ·)

theorem translateLoop_spec (m : Mapping) (input : Str) (fuel i : Nat) (rest out : List Nat)
    (hf : rest.length < fuel) :
    translateLoop m true input fuel i rest out = withPrefix out (translateSpec m rest) := by
  induction fuel generalizing i rest out with
  | zero => omega
  | succ fuel ih =>
    cases rest with
    | nil => simp [translateLoop, translateSpec, withPrefix, Except.map]
    | cons c cs =>
      simp only [List.length_cons] at hf
      simp only [translateLoop, translateSpec]
      cases ho : charmaptranslateOutput m c with
      | error e => simp [bind, Except.bind, withPrefix, Except.map]
      | ok w =>
        cases w with
        | some w =>
          simp only [bind, Except.bind, pure, Except.pure, Option.getD_some]
          rw [ih _ _ _ (by omega)]
          cases translateSpec m cs <;> simp [withPrefix, Except.map]
        | none =>
          simp only [bind, Except.bind, pure, Except.pure, Option.getD_none, List.nil_append]
          have hc := collect_spec m cs
          cases hk : collectUndefined m cs with
          | error e =>
            rw [hk] at hc
            simp only at hc
            simp [hc, withPrefix, Except.map]
          | ok r =>
            rw [hk] at hc
            simp only at hc
            obtain ⟨h1, h2⟩ := hc
            simp only [↓reduceIte]
            rw [ih _ _ _ (by omega), h2]
            cases translateSpec m r <;> simp [withPrefix, Except.map]

/-- `ascii_table` agrees with the mapping wherever it is set. -/
def TableOk (m : Mapping) (t : AsciiTable) : Prop :=
  ∀ c, t c ≠ 0xff →
    (t c = 0xfe ∧ charmaptranslateOutput m c = .ok none) ∨
    (t c < 128 ∧ charmaptranslateOutput m c = .ok (some [t c]))

theorem tableSet_ok {m t ch v} (h : TableOk m t)
    (hv : (v = 0xfe ∧ charmaptranslateOutput m ch = .ok none) ∨
      (v < 128 ∧ charmaptranslateOutput m ch = .ok (some [v]))) :
    TableOk m (tableSet t ch v) := by
  intro c hc
  simp only [tableSet] at hc ⊢
  by_cases e : c = ch
  · subst e; simpa using hv
  · simp only [e, if_false] at hc ⊢; exact h c hc

/-- What the fast loop's outcome means. -/
def FastOutcome (m : Mapping) (s : List Nat) (out : Str) (pos : Nat) :
    Py (Bool × Str × Nat) → Prop
  | .error e => translateSpec m s = .error e
  | .ok (true, o, _) => withPrefix out (translateSpec m s) = .ok o
  | .ok (false, o, p) =>
    pos ≤ p ∧ p - pos ≤ s.length ∧ ∃ w, o = out ++ w ∧
      withPrefix out (translateSpec m s) = withPrefix o (translateSpec m (s.drop (p - pos)))

theorem fastLookup_spec (m : Mapping) (ch : Nat) (hch : ch < 128) (t : AsciiTable)
    (ht : TableOk m t) :
    match fastTranslateLookup m ch t with
    | .error e => charmaptranslateOutput m ch = .error e
    | .ok (true, t') => TableOk m t' ∧ t' ch ≠ 0xff
    | .ok (false, _) => True := by
  simp only [fastTranslateLookup, charmaptranslateOutput]
  cases hl : charmaptranslateLookup m ch with
  | error e => simp [bind, Except.bind]
  | ok v =>
    have hout : ∀ x, charmaptranslateOutput m ch = .ok x ↔
        (match v with
         | .null => some [ch] | .pyNone => none | .long r => some [r] | .str s => some s) = x := by
      intro x
      simp only [charmaptranslateOutput, hl, bind, Except.bind]
      cases v <;> simp [pure, Except.pure]
    cases v with
    | pyNone =>
      simp only [bind, Except.bind]
      refine ⟨tableSet_ok ht (Or.inl ⟨rfl, (hout _).2 rfl⟩), by simp [tableSet]⟩
    | null =>
      simp only [bind, Except.bind]
      refine ⟨tableSet_ok ht (Or.inr ⟨hch, (hout _).2 rfl⟩), ?_⟩
      simp [tableSet]; omega
    | long r =>
      simp only [bind, Except.bind]
      by_cases hr : r > 127
      · rw [if_pos hr]; trivial
      · rw [if_neg hr]
        refine ⟨tableSet_ok ht (Or.inr ⟨by omega, (hout _).2 rfl⟩), ?_⟩
        simp [tableSet]; omega
    | str s =>
      simp only [bind, Except.bind]
      cases s with
      | nil => trivial
      | cons r rs =>
        cases rs with
        | cons a l => trivial
        | nil =>
          by_cases hr : r > 127
          · simp only [if_pos hr]
          · simp only [if_neg hr]
            refine ⟨tableSet_ok ht (Or.inr ⟨by omega, (hout _).2 rfl⟩), ?_⟩
            simp [tableSet]; omega

theorem spec_cons (m : Mapping) (c : Nat) (cs : List Nat) (w : Option Str)
    (h : charmaptranslateOutput m c = .ok w) (out : Str) :
    withPrefix out (translateSpec m (c :: cs)) =
      withPrefix (out ++ w.getD []) (translateSpec m cs) := by
  simp only [translateSpec, h, bind, Except.bind, pure, Except.pure]
  cases translateSpec m cs <;> simp [withPrefix, Except.map]

theorem outcome_lift (m : Mapping) (c : Nat) (cs : List Nat) (w : Option Str)
    (h : charmaptranslateOutput m c = .ok w) (out : Str) (pos : Nat)
    (r : Py (Bool × Str × Nat))
    (hr : FastOutcome m cs (out ++ w.getD []) (pos + 1) r) :
    FastOutcome m (c :: cs) out pos r := by
  match r, hr with
  | .error e, hr =>
    simp only [FastOutcome] at hr ⊢
    simp [translateSpec, h, bind, Except.bind, hr]
  | .ok (true, o, _), hr =>
    simp only [FastOutcome] at hr ⊢
    rw [spec_cons m c cs w h]
    exact hr
  | .ok (false, o, p), hr =>
    simp only [FastOutcome] at hr ⊢
    obtain ⟨h1, h2, v, h3, h4⟩ := hr
    refine ⟨by omega, by simp only [List.length_cons]; omega, w.getD [] ++ v,
      by simp [h3], ?_⟩
    rw [spec_cons m c cs w h, h4]
    have e : p - pos = (p - (pos + 1)) + 1 := by omega
    rw [e, List.drop_succ_cons]

theorem fastLoop_spec (m : Mapping) (ignore : Bool) (s : List Nat) (hs : ∀ c ∈ s, c < 128)
    (t : AsciiTable) (ht : TableOk m t) (out : Str) (pos : Nat) :
    FastOutcome m s out pos (fastTranslateLoop m ignore s t out pos) := by
  induction s generalizing t out pos with
  | nil => simp [fastTranslateLoop, FastOutcome, translateSpec, withPrefix, Except.map]
  | cons c cs ih =>
    have hc := hs c List.mem_cons_self
    have hcs : ∀ x ∈ cs, x < 128 := fun x hx => hs x (List.mem_cons_of_mem _ hx)
    have stop : FastOutcome m (c :: cs) out pos (.ok (false, out, pos)) :=
      ⟨Nat.le_refl _, by simp, [], by simp, by simp⟩
    have step : ∀ t', TableOk m t' → t' c ≠ 0xff →
        FastOutcome m (c :: cs) out pos
          (if t' c = 0xfe then
             (if ignore then fastTranslateLoop m ignore cs t' out (pos + 1)
              else .ok (false, out, pos))
           else fastTranslateLoop m ignore cs t' (out ++ [t' c]) (pos + 1)) := by
      intro t' ht' hne
      rcases ht' c hne with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [if_pos h1]
        cases ignore with
        | false => exact stop
        | true =>
          exact outcome_lift m c cs none h2 out pos _ (by simpa using ih hcs t' ht' out (pos + 1))
      · rw [if_neg (by omega)]
        exact outcome_lift m c cs (some [t' c]) h2 out pos _ (ih hcs t' ht' _ (pos + 1))
    simp only [fastTranslateLoop, bind, Except.bind]
    by_cases hff : t c = 0xff
    · simp only [hff, if_true]
      have hl := fastLookup_spec m c hc t ht
      cases hk : fastTranslateLookup m c t with
      | error e =>
        rw [hk] at hl
        simp only at hl
        simp [FastOutcome, translateSpec, hl, bind, Except.bind]
      | ok v =>
        obtain ⟨tr, t'⟩ := v
        rw [hk] at hl
        cases tr with
        | false =>
          simp only [Bool.not_false, if_true]
          exact stop
        | true =>
          simp only at hl
          simpa using step t' hl.1 hl.2
    · simp only [hff, if_false]
      exact step t ht hff

theorem withPrefix_nil (r : Py Str) : withPrefix [] r = r := by
  cases r <;> simp [withPrefix, Except.map]

/-- For every pure table, `str.translate` equals the per-character reading, whether
the ASCII fast path ran to the end, handed over midway to the general loop, or was
not taken. So the fast path and the general path cannot disagree. -/
def TranslateFastSlow : Prop :=
  ∀ (m : Mapping) (s : Str), unicodeTranslate s m = translateSpec m s

theorem translateFastSlow_proven : TranslateFastSlow := by
  intro m s
  unfold unicodeTranslate translateCharmap
  by_cases h0 : s.length = 0
  · have : s = [] := List.eq_nil_of_length_eq_zero h0
    subst this
    rfl
  rw [if_neg h0]
  simp only
  by_cases ha : isAscii s = true
  · rw [if_pos ha]
    have hf := fastLoop_spec m true s (fun c hc => mem_ascii ha hc) (fun _ => 0xff)
      (fun c h => absurd rfl h) [] 0
    simp only [bind, Except.bind]
    cases hk : fastTranslateLoop m true s (fun _ => 0xff) [] 0 with
    | error e =>
      rw [hk] at hf
      exact hf.symm
    | ok v =>
      obtain ⟨res, o, p⟩ := v
      rw [hk] at hf
      cases res with
      | true =>
        simp only [FastOutcome, withPrefix_nil] at hf
        exact hf.symm
      | false =>
        simp only [FastOutcome, withPrefix_nil, Nat.sub_zero] at hf
        obtain ⟨-, h2, _, _, h4⟩ := hf
        simp only [Bool.false_eq_true, if_false]
        rw [translateLoop_spec m s _ _ _ _ (by simp only [List.length_drop]; omega), h4]
  · rw [if_neg ha, translateLoop_spec m s _ _ _ _ (by omega), withPrefix_nil]

theorem translateLoop_strict (m : Mapping) (input : Str) (fuel i : Nat) (rest out : List Nat)
    (hf : rest.length < fuel) (hn : ∀ c ∈ rest, charmaptranslateOutput m c ≠ .ok none) :
    translateLoop m false input fuel i rest out = withPrefix out (translateSpec m rest) := by
  induction fuel generalizing i rest out with
  | zero => omega
  | succ fuel ih =>
    cases rest with
    | nil => simp [translateLoop, translateSpec, withPrefix, Except.map]
    | cons c cs =>
      simp only [List.length_cons] at hf
      have hc := hn c List.mem_cons_self
      simp only [translateLoop, translateSpec]
      cases ho : charmaptranslateOutput m c with
      | error e => simp [bind, Except.bind, withPrefix, Except.map]
      | ok w =>
        cases w with
        | none => exact absurd ho hc
        | some w =>
          simp only [bind, Except.bind, pure, Except.pure, Option.getD_some]
          rw [ih _ _ _ (by omega) (fun x hx => hn x (List.mem_cons_of_mem _ hx))]
          cases translateSpec m cs <;> simp [withPrefix, Except.map]

/-- `PyUnicode_Translate(s, table, NULL)`: when no character maps to `None`, the
strict mode gives the same result as the per-character reading, through the fast
path or not. -/
def TranslateStrict : Prop :=
  ∀ (m : Mapping) (s : Str), (∀ c ∈ s, charmaptranslateOutput m c ≠ .ok none) →
    pyUnicodeTranslateStrict s m = translateSpec m s

theorem translateStrict_proven : TranslateStrict := by
  intro m s hn
  unfold pyUnicodeTranslateStrict translateCharmap
  by_cases h0 : s.length = 0
  · have : s = [] := List.eq_nil_of_length_eq_zero h0
    subst this
    rfl
  rw [if_neg h0]
  simp only
  by_cases ha : isAscii s = true
  · rw [if_pos ha]
    have hf := fastLoop_spec m false s (fun c hc => mem_ascii ha hc) (fun _ => 0xff)
      (fun c h => absurd rfl h) [] 0
    simp only [bind, Except.bind]
    cases hk : fastTranslateLoop m false s (fun _ => 0xff) [] 0 with
    | error e =>
      rw [hk] at hf
      exact hf.symm
    | ok v =>
      obtain ⟨res, o, p⟩ := v
      rw [hk] at hf
      cases res with
      | true =>
        simp only [FastOutcome, withPrefix_nil] at hf
        exact hf.symm
      | false =>
        simp only [FastOutcome, withPrefix_nil, Nat.sub_zero] at hf
        obtain ⟨-, h2, _, _, h4⟩ := hf
        simp only [Bool.false_eq_true, if_false]
        rw [translateLoop_strict m s _ _ _ _ (by simp only [List.length_drop]; omega)
          (fun x hx => hn x (List.mem_of_mem_drop hx)), h4]
  · rw [if_neg ha, translateLoop_strict m s _ _ _ _ (by omega) hn, withPrefix_nil]

/-! ## `maketrans` -/

/-- The dict form of `maketrans`: "Character keys will be then converted to
ordinals", a string key of another length raises `ValueError`, and a key that is
neither `str` nor `int` raises `TypeError`, for every value and every remaining
items. -/
def MaketransDict : Prop :=
  (∀ (c : Nat) v rest d, maketransFromDict ((.str [c], v) :: rest) d =
    maketransFromDict ((.int c, v) :: rest) d) ∧
  (∀ (s : Str) v rest d, s.length ≠ 1 → maketransFromDict ((.str s, v) :: rest) d =
    .error (.valueError "string keys in translatetable must be of length 1")) ∧
  (∀ v rest d, maketransFromDict ((.other, v) :: rest) d =
    .error (.typeError "keys in translate table mustbe strings or integers"))

theorem maketransDict_proven : MaketransDict := by
  refine ⟨fun c v rest d => ?_, fun s v rest d h => ?_, fun v rest d => ?_⟩
  · simp only [maketransFromDict]
  · cases s with
    | nil => simp only [maketransFromDict]
    | cons a l =>
      cases l with
      | nil => simp at h
      | cons b t => simp only [maketransFromDict]
  · simp only [maketransFromDict]

theorem find_dictSet (d : TransDict) (k : Int) (v : MapItem) (c : Int) :
    (dictSet d k v).find? (·.1 == c) =
      if c = k then some (k, v) else d.find? (·.1 == c) := by
  induction d with
  | nil =>
    by_cases h : c = k
    · simp [dictSet, h]
    · have : ¬ k = c := fun e => h e.symm
      simp [dictSet, h, this]
  | cons e es ih =>
    simp only [dictSet]
    by_cases he : e.1 = k
    · rw [if_pos he]
      by_cases h : c = k
      · simp [h]
      · have h1 : ¬ k = c := fun e => h e.symm
        have h2 : ¬ e.1 = c := fun e' => h (e'.symm.trans he)
        simp [List.find?_cons, h, h1, h2]
    · rw [if_neg he]
      by_cases h2 : e.1 = c
      · have h : ¬ c = k := fun e' => he (h2.trans e')
        simp [List.find?_cons, h, h2]
      · have h3 : (e.1 == c) = false := by simpa using h2
        simp only [List.find?_cons, h3, ih]

theorem dictMapping_set (d : TransDict) (k : Nat) (v : MapItem) (c : Nat) :
    dictMapping (dictSet d k v) c = if c = k then v else dictMapping d c := by
  simp only [dictMapping, find_dictSet]
  by_cases h : c = k
  · simp [h]
  · have : ¬ ((c : Int) = k) := by omega
    simp [h, this]

theorem dictMapping_delete (d : TransDict) (z : List Nat) (c : Nat) :
    dictMapping (maketransDelete d z) c = if c ∈ z then .pyNone else dictMapping d c := by
  induction z generalizing d with
  | nil => simp [maketransDelete]
  | cons x xs ih =>
    have e : maketransDelete d (x :: xs) = maketransDelete (dictSet d x .pyNone) xs := rfl
    rw [e, ih, dictMapping_set]
    by_cases h1 : c ∈ xs
    · simp [h1]
    · by_cases h2 : c = x <;> simp [h1, h2]

/-- The last `y[i]` with `x[i] == c`, or `c`. -/
def lastMap (c : Nat) : List Nat → List Nat → Nat → Nat
  | x :: xs, y :: ys, acc => lastMap c xs ys (if c = x then y else acc)
  | _, _, acc => acc

theorem dictMapping_pairs (d : TransDict) (xs ys : List Nat) (c acc : Nat)
    (hd : dictMapping d c = .missing ∧ acc = c ∨ dictMapping d c = .int acc) :
    dictMapping (maketransPairs d xs ys) c = .missing ∧ lastMap c xs ys acc = c ∨
      dictMapping (maketransPairs d xs ys) c = .int (lastMap c xs ys acc) := by
  induction xs generalizing d ys acc with
  | nil => simpa [maketransPairs, lastMap] using hd
  | cons x xs ih =>
    cases ys with
    | nil => simpa [maketransPairs, lastMap] using hd
    | cons y ys =>
      simp only [maketransPairs, lastMap]
      apply ih
      rw [dictMapping_set]
      by_cases h : c = x
      · simp [h]
      · simpa [h] using hd

theorem lastMap_valid (c : Nat) (xs ys : List Nat) (acc : Nat) (hy : Str.Valid ys)
    (ha : acc ≤ maxUnicode) : lastMap c xs ys acc ≤ maxUnicode := by
  induction xs generalizing ys acc with
  | nil => simpa [lastMap] using ha
  | cons x xs ih =>
    cases ys with
    | nil => simpa [lastMap] using ha
    | cons y ys =>
      simp only [lastMap]
      apply ih _ _ (fun v hv => hy v (List.mem_cons_of_mem _ hv))
      split
      · exact hy y List.mem_cons_self
      · exact ha

/-- `str.maketrans(x, y, z)` then `translate` does what the docstring says: each
character of `z` is deleted, and otherwise each character of `x` becomes the
character at the same position in `y`, the last occurrence winning. For all strings
of equal length and every `s`. -/
def MaketransTranslate : Prop :=
  ∀ x y z s : Str, Str.Valid y → Str.Valid s → x.length = y.length →
    ∃ d, unicodeMaketrans (.str x) (some y) (some z) = .ok d ∧
      unicodeTranslate s (dictMapping d) =
        .ok (s.flatMap fun c => if c ∈ z then [] else [lastMap c x y c])

theorem maketransTranslate_proven : MaketransTranslate := by
  intro x y z s hy hs hlen
  refine ⟨maketransDelete (maketransPairs [] x y) z, ?_, ?_⟩
  · simp [unicodeMaketrans, hlen]
  · rw [translateFastSlow_proven]
    induction s with
    | nil => rfl
    | cons c cs ih =>
      have hc : c ≤ maxUnicode := hs c List.mem_cons_self
      have ih' := ih (fun v hv => hs v (List.mem_cons_of_mem _ hv))
      simp only [translateSpec, ih', bind, Except.bind, pure, Except.pure, List.flatMap_cons]
      have hm := dictMapping_pairs [] x y c c (Or.inl ⟨by simp [dictMapping], rfl⟩)
      have hv := lastMap_valid c x y c hy hc
      have hmax : maxUnicode = 0x10FFFF := rfl
      simp only [charmaptranslateOutput, charmaptranslateLookup, dictMapping_delete]
      by_cases hz : c ∈ z
      · simp [hz, bind, Except.bind, pure, Except.pure]
      · simp only [hz, if_false]
        rcases hm with ⟨h1, h2⟩ | h1
        · simp [h1, h2, bind, Except.bind, pure, Except.pure]
        · have hn : ¬ ((lastMap c x y c : Int) < 0 ∨ (lastMap c x y c : Int) > maxUnicode) := by
            omega
          rw [h1]
          dsimp only
          rw [if_neg hn]
          simp [bind, Except.bind, pure, Except.pure]

/-! ## `bytes` twins on ASCII -/

theorem ascii_bytes_facts : ∀ c, c < 128 →
    (isLowercase c = pyIsLower c ∧ isUppercase c = pyIsUpper c ∧ isTitlecase c = false ∧
     isCased c = (pyIsLower c || pyIsUpper c) ∧
     (¬ (0x1C ≤ c ∧ c ≤ 0x1F) → isSpace c = pyIsSpace c)) := by
  decide +kernel

/-- The methods `bytes` and `str` share agree on ASCII data: `lower`, `upper`,
`swapcase`, `title`, `capitalize`, `islower`, `isupper`, `istitle`, `isalpha`,
`isdigit` and `isalnum`, and `isspace` away from `\x1c`-`\x1f`, which only `str`
treats as whitespace. For every ASCII string of at most `PY_SSIZE_T_MAX // 12`
characters (`case_operation`'s precondition; `bytes` has no such limit). -/
def BytesStrTwin : Prop :=
  ∀ b : Bytes, (∀ c ∈ b, c < 128) → b.length ≤ caseLengthLimit →
    unicodeLower b = .ok (bytesLower b) ∧ unicodeUpper b = .ok (bytesUpper b) ∧
    unicodeSwapcase b = .ok (bytesSwapcase b) ∧ unicodeTitle b = .ok (bytesTitle b) ∧
    unicodeCapitalize b = .ok (bytesCapitalize b) ∧
    unicodeIsLower b = bytesIsLower b ∧ unicodeIsUpper b = bytesIsUpper b ∧
    unicodeIsTitle b = bytesIsTitle b ∧
    unicodeIsAlpha b = allShape pyIsAlpha b ∧ unicodeIsDigit b = allShape pyIsDigit b ∧
    unicodeIsAlnum b = allShape pyIsAlnum b ∧
    ((∀ c ∈ b, ¬ (0x1C ≤ c ∧ c ≤ 0x1F)) → unicodeIsSpace b = allShape pyIsSpace b)

theorem allShape_congr (p q : Nat → Bool) (s : Str) (h : ∀ c ∈ s, p c = q c) :
    allShape p s = allShape q s := by
  have e : s.all p = s.all q := by
    induction s with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.all_cons, h x List.mem_cons_self,
        ih (fun c hc => h c (List.mem_cons_of_mem _ hc))]
  rw [allShape_eq, allShape_eq, e]

theorem title_step : ∀ p : Bool, ∀ c, c < 128 →
    (if pyIsLower c then (if !p then pyToUpper c else c)
     else if pyIsUpper c then (if p then pyToLower c else c) else c) =
    (if p then pyToLower c else pyToUpper c) := by
  intro p
  cases p <;> decide +kernel

theorem bytesTitle_cons (p : Bool) (c : Nat) (cs : List Nat) (hc : c < 128) :
    bytesTitleLoop p (c :: cs) =
      (if p then pyToLower c else pyToUpper c) ::
        bytesTitleLoop (pyIsLower c || pyIsUpper c) cs := by
  rw [← title_step p c hc]
  simp only [bytesTitleLoop]
  cases pyIsLower c <;> cases pyIsUpper c <;> simp

theorem titleLoop_bytes (cs : List Nat) (hs : ∀ c ∈ cs, c < 128) (p before o) :
    (titleLoop p before cs o).res = o.res ++ bytesTitleLoop p cs := by
  induction cs generalizing p before o with
  | nil => simp [titleLoop, bytesTitleLoop]
  | cons c cs ih =>
    have hc := hs c List.mem_cons_self
    have hcs : ∀ x ∈ cs, x < 128 := fun x hx => hs x (List.mem_cons_of_mem _ hx)
    have f := ascii_facts c hc
    have g := ascii_bytes_facts c hc
    have hl : lowerUcs4 before c cs = [pyToLower c] := by
      unfold lowerUcs4; rw [if_neg (by omega), f.2.1]
    have hmap : (if p = true then lowerUcs4 before c cs else toTitleFull c) =
        [if p then pyToLower c else pyToUpper c] := by
      cases p
      · simpa using f.2.2.1
      · simpa using hl
    have hb := bytesTitle_cons p c cs hc
    simp only [titleLoop, hmap, ih hcs, emit, hb, g.2.2.2.1]
    simp

theorem isLowerLoop_bytes (cs : List Nat) (hs : ∀ c ∈ cs, c < 128) (b : Bool) :
    isLowerLoop cs b = bytesIsLowerLoop cs b := by
  induction cs generalizing b with
  | nil => rfl
  | cons c cs ih =>
    have f := ascii_bytes_facts c (hs c List.mem_cons_self)
    simp only [isLowerLoop, bytesIsLowerLoop, f.1, f.2.1, f.2.2.1, Bool.or_false]
    rw [ih (fun x hx => hs x (List.mem_cons_of_mem _ hx))]

theorem isUpperLoop_bytes (cs : List Nat) (hs : ∀ c ∈ cs, c < 128) (b : Bool) :
    isUpperLoop cs b = bytesIsUpperLoop cs b := by
  induction cs generalizing b with
  | nil => rfl
  | cons c cs ih =>
    have f := ascii_bytes_facts c (hs c List.mem_cons_self)
    simp only [isUpperLoop, bytesIsUpperLoop, f.1, f.2.1, f.2.2.1, Bool.or_false]
    rw [ih (fun x hx => hs x (List.mem_cons_of_mem _ hx))]

theorem isTitleLoop_bytes (cs : List Nat) (hs : ∀ c ∈ cs, c < 128) (b p : Bool) :
    isTitleLoop cs b p = bytesIsTitleLoop cs b p := by
  induction cs generalizing b p with
  | nil => rfl
  | cons c cs ih =>
    have f := ascii_bytes_facts c (hs c List.mem_cons_self)
    have ih' := ih (fun x hx => hs x (List.mem_cons_of_mem _ hx))
    simp only [isTitleLoop, bytesIsTitleLoop, f.1, f.2.1, f.2.2.1, Bool.or_false, ih']

theorem isAscii_of (b : Bytes) (h : ∀ c ∈ b, c < 128) : isAscii b = true := by
  simpa [isAscii] using h

theorem swap_step : ∀ c, c < 128 →
    (if pyIsUpper c then pyToLower c else if pyIsLower c then pyToUpper c else c) =
    (if pyIsLower c then pyToUpper c else if pyIsUpper c then pyToLower c else c) := by
  decide +kernel

theorem bytesStrTwin_proven : BytesStrTwin := by
  intro b hb hlen
  have ha := isAscii_of b hb
  have hnot : ¬ b.length > caseLengthLimit := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [unicodeLower, ha, asciiUpperOrLower, bytesLower]
  · simp [unicodeUpper, ha, asciiUpperOrLower, bytesUpper]
  · have : (doSwapcase b).res = bytesSwapcase b := by
      have := mapLoop_map swapcaseMap (fun c => if pyIsLower c then pyToUpper c
        else if pyIsUpper c then pyToLower c else c) b (fun c hc x y => by
          have hc' := hb c hc
          have f := ascii_facts c hc'
          have g := ascii_bytes_facts c hc'
          have s := swap_step c hc'
          simp only [swapcaseMap, lowerUcs4, g.2.1, g.1]
          rw [if_neg (by omega : ¬ c = 0x3A3), f.2.1, f.1, ← s]
          cases pyIsUpper c <;> cases pyIsLower c <;> simp) [] startOut
      simpa [doSwapcase, bytesSwapcase, startOut] using this
    simp [unicodeSwapcase, caseOperation, hnot, this]
  · have := titleLoop_bytes b hb false [] startOut
    simp only [unicodeTitle, caseOperation, if_neg hnot, doTitle, bytesTitle, this]
    rfl
  · cases b with
    | nil => simp [unicodeCapitalize, bytesCapitalize]
    | cons c cs =>
      have hc := hb c List.mem_cons_self
      have f := ascii_facts c hc
      have := mapLoop_map lowerUcs4 pyToLower cs (fun x hx b' a' => by
        have hx' := hb x (List.mem_cons_of_mem _ hx)
        have g := ascii_facts x hx'
        unfold lowerUcs4
        rw [if_neg (by omega), g.2.1]) [c] (emit startOut (toTitleFull c))
      have hres : (doCapitalize (c :: cs)).res = pyToUpper c :: cs.map pyToLower := by
        simpa [doCapitalize, f.2.2.1, emit, startOut] using this
      have h0 : ¬ (c :: cs).length = 0 := by simp
      simp only [unicodeCapitalize, if_neg h0, caseOperation, if_neg hnot, hres, bytesCapitalize,
        bytesLower]
  · match b, hb with
    | [], _ => rfl
    | [c], hb => exact (ascii_bytes_facts c (hb c List.mem_cons_self)).1
    | a :: b :: t, hb => exact isLowerLoop_bytes _ hb _
  · match b, hb with
    | [], _ => rfl
    | [c], hb => exact (ascii_bytes_facts c (hb c List.mem_cons_self)).2.1
    | a :: b :: t, hb => exact isUpperLoop_bytes _ hb _
  · match b, hb with
    | [], _ => rfl
    | [c], hb =>
      have f := ascii_bytes_facts c (hb c List.mem_cons_self)
      simp [unicodeIsTitle, bytesIsTitle, f.2.1, f.2.2.1]
    | a :: b :: t, hb => exact isTitleLoop_bytes _ hb _ _
  · exact allShape_congr _ _ _ fun c hc => (ascii_facts c (hb c hc)).2.2.2.2.2.2.2.2.1
  · exact allShape_congr _ _ _ fun c hc => (ascii_facts c (hb c hc)).2.2.2.2.2.2.2.2.2.1
  · exact allShape_congr _ _ _ fun c hc => (ascii_facts c (hb c hc)).2.2.2.2.2.2.2.2.2.2.1
  · intro hs
    exact allShape_congr _ _ _ fun c hc => (ascii_bytes_facts c (hb c hc)).2.2.2.2 (hs c hc)

/-! ## Decimal transform -/

/-- `_PyUnicode_TransformDecimalAndSpaceToASCII`, used by `int()`, `float()` and
`complex()`: for every string the result is ASCII; and a string of ASCII characters
below 0x7F, whitespace and decimal digits keeps its length. -/
def TransformDecimal : Prop :=
  ∀ s : Str, Str.Valid s →
    (∀ c ∈ transformDecimalAndSpace s, c < 128) ∧
    ((∀ c ∈ s, c < 127 ∨ isSpace c = true ∨ isDecimalDigit c = true) →
      (transformDecimalAndSpace s).length = s.length)

theorem transformLoop_ascii (s : Str) (hs : Str.Valid s) : ∀ c ∈ transformLoop s, c < 128 := by
  induction s with
  | nil => simp [transformLoop]
  | cons x xs ih =>
    have hx : x ≤ maxUnicode := hs x List.mem_cons_self
    have ih' := ih (fun v hv => hs v (List.mem_cons_of_mem _ hv))
    intro c hc
    simp only [transformLoop] at hc
    repeat' split at hc
    all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    · rcases hc with rfl | hc
      · omega
      · exact ih' c hc
    · rcases hc with rfl | hc
      · omega
      · exact ih' c hc
    · omega
    · rcases hc with rfl | hc
      · have := decimal_bound hx
        omega
      · exact ih' c hc

theorem transformLoop_length (s : Str)
    (h : ∀ c ∈ s, c < 127 ∨ isSpace c = true ∨ isDecimalDigit c = true) :
    (transformLoop s).length = s.length := by
  induction s with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x List.mem_cons_self
    have ih' := ih (fun v hv => h v (List.mem_cons_of_mem _ hv))
    simp only [transformLoop]
    by_cases h1 : x < 127
    · simp [h1, ih']
    · by_cases h2 : isSpace x = true
      · simp [h1, h2, ih']
      · have h3 : isDecimalDigit x = true := by
          rcases hx with hx | hx | hx
          · exact absurd hx h1
          · exact absurd hx h2
          · exact hx
        have h4 : ¬ toDecimalDigit x < 0 := by simpa [isDecimalDigit] using h3
        simp [h1, h2, h4, ih']

theorem transformDecimal_proven : TransformDecimal := by
  intro s hs
  constructor
  · intro c hc
    unfold transformDecimalAndSpace at hc
    split at hc
    · rename_i ha
      exact mem_ascii ha hc
    · exact transformLoop_ascii s hs c hc
  · intro h
    unfold transformDecimalAndSpace
    split
    · rfl
    · exact transformLoop_length s h

/-! ## Bloom mask -/

/-- `make_bloom_mask` has no false negatives: every character of the string passes
`BLOOM`, which is what lets `strip` and `splitlines` skip characters with it. -/
def BloomSuperset : Prop := ∀ (s : Str), ∀ c ∈ s, bloom (makeBloomMask s) c = true

theorem bloom_testBit (m c : Nat) : bloom m c = m.testBit (c &&& 63) := by
  simp only [bloom, Nat.one_shiftLeft]
  generalize c &&& 63 = k
  have key : (m &&& 2 ^ k).testBit k = m.testBit k := by
    simp [Nat.testBit_and, Nat.testBit_two_pow_self]
  by_cases h : m &&& 2 ^ k = 0
  · rw [h] at key
    simp only [Nat.zero_testBit] at key
    simp [h, ← key]
  · have hb : m.testBit k = true := by
      cases hm : m.testBit k with
      | true => rfl
      | false =>
        exfalso
        apply h
        apply Nat.eq_of_testBit_eq
        intro j
        by_cases hj : k = j
        · subst hj
          simp [hm]
        · simp [Nat.testBit_and, Nat.testBit_two_pow, hj]
    simp [h, hb]

theorem bloom_keep (s : Str) (m k : Nat) (h : m.testBit k = true) :
    (s.foldl (fun m ch => m ||| (1 <<< (ch &&& 63))) m).testBit k = true := by
  induction s generalizing m with
  | nil => exact h
  | cons x xs ih =>
    simp only [List.foldl_cons]
    exact ih _ (by simp [Nat.testBit_or, h])

theorem bloomSuperset_proven : BloomSuperset := by
  intro s c hc
  rw [bloom_testBit]
  unfold makeBloomMask
  suffices h : ∀ (s : Str) (m : Nat), c ∈ s →
      (s.foldl (fun m ch => m ||| (1 <<< (ch &&& 63))) m).testBit (c &&& 63) = true from h s 0 hc
  intro s m hc
  induction s generalizing m with
  | nil => simp at hc
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.1 hc with rfl | hc
    · exact bloom_keep _ _ _ (by simp [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow_self])
    · exact ih _ hc

/-! ## Dedent -/

/-- `_PyUnicode_Dedent` is defined on every string: the `memcpy` length
`new_line_len` is never negative (`assert(new_line_len >= 0)`, unicodeobject.c:13708). -/
def DedentDefined : Prop := ∀ src : Str, (pyUnicodeDedent src).isSome = true

/-- A final blank line shorter than the margin, with no newline after it. -/
theorem dedentDefined_refuted : ¬ DedentDefined := by
  intro h
  have := h (lit "    a\n  ")
  revert this
  decide

/-- The comment on `_PyUnicode_Dedent`: "Behaviour is expected to be an exact match
of `textwrap.dedent`." Stated for input ending in `'\n'`, which is the only input
`python -c` passes. -/
def DedentMatchesTextwrap : Prop :=
  ∀ src : Str, src.getLast? = some 10 → pyUnicodeDedent src = some (textwrapDedent src)

/-- A line holding only a form feed is blank to `str.isspace` and so to
`textwrap.dedent`, but the C code sees a line with no indent and gives up. -/
theorem dedentMatchesTextwrap_refuted : ¬ DedentMatchesTextwrap := by
  intro h
  have := h (lit "  a\n\x0c\n") (by decide)
  revert this
  decide

/-! ## Simple and full case mappings -/

/-- Every full case mapping is 1 to 3 valid code points, for every code point
(the `mapped[3]` arrays cannot overflow), and the simple mappings
`_PyUnicode_ToUppercase`, `ToLowercase`, `ToTitlecase` are the first element of
the full ones. Also the facts relating the flags of `_PyUnicode_TypeRecords`. -/
def CaseTables : Prop :=
  ∀ c, c ≤ maxUnicode →
    goodMapping (toLowerFull c) = true ∧ goodMapping (toUpperFull c) = true ∧
    goodMapping (toTitleFull c) = true ∧ goodMapping (toFoldedFull c) = true ∧
    (toLowerFull c).head? = some (toLowercase c) ∧
    (toUpperFull c).head? = some (toUppercase c) ∧
    (toTitleFull c).head? = some (toTitlecase c) ∧
    flagFact (isDecimalDigit c) (isDigit c) (isNumeric c) (isLowercase c) (isUppercase c)
      (isTitlecase c) (isCased c) (isXidStart c) (isXidContinue c) = true

theorem head_of_good (field : TypeRecord → Int) (c : Nat)
    (h : goodMapping (toFull field c) = true) :
    (toFull field c).head? = some
      (if hasFlag (gettyperecord c) EXTENDED_CASE_MASK then
        extendedCaseAt ((field (gettyperecord c)).toNat &&& 0xFFFF)
       else addUCS4 c (field (gettyperecord c))) := by
  simp only [goodMapping, Bool.and_eq_true, decide_eq_true_eq] at h
  have h1 := h.1.1
  revert h1
  simp only [toFull]
  split
  · simp only [extendedRun, List.length_map, List.length_range]
    intro h1
    cases hn : (field (gettyperecord c)).toNat >>> 24 with
    | zero => omega
    | succ n => simp [List.range_succ_eq_map]
  · simp

theorem caseTables_proven : CaseTables := by
  intro c h
  obtain ⟨a, b, d, e⟩ := charFact_case h
  refine ⟨a, b, d, e, head_of_good _ _ a, head_of_good _ _ b, head_of_good _ _ d, flags_ok h⟩

end PyLean.UnicodeObj
