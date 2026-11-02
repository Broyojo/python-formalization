import PyLean.PyGrammar.Lexer.Get

/-!
The fixed-size arrays of `struct tok_state`. `parenstack[MAXLEVEL]`, `indstack[MAXINDENT]`,
`altindstack[MAXINDENT]` and `tok_mode_stack[MAXFSTRINGLEVEL]` are written through `level`, `indent`
and `tok_mode_stack_index`, and nothing but the checks in `tok_get` keeps those in range. `LexStacks`
says that across any call of `tok_get`, on any state that starts sound, every counter matches its
stack and stays in range, and the stack of indentation columns stays strictly increasing. It covers
every branch of `tok_get_normal_mode` and `tok_get_fstring_mode`, including the error returns.

The model's lists cannot overflow and its `Nat` subtraction cannot go below zero, so the counters
are what is checked. `bottom` is what rules out `tok_mode_stack_index--` at index `0`.
-/

namespace PyLean.PyGrammar.Lexer

/-- The `fstringMode` flags of the mode stack, top first. -/
def fmFlags (s : TokState) : List Bool := s.modes.map (·.fstringMode)

/-- A sound tokenizer state. `bottom`: the mode at the bottom of the stack is the regular mode. -/
structure LexInv (s : TokState) : Prop where
  level : s.level = s.parenstack.length
  levelMax : s.level ≤ MAXLEVEL
  ind : s.indstack.length = s.indent + 1
  alt : s.altindstack.length = s.indent + 1
  indMax : s.indent < MAXINDENT
  chain : s.indstack.Pairwise (· > ·)
  modes : s.modes.length = s.modeIndex + 1
  modeMax : s.modeIndex < MAXFSTRINGLEVEL
  bottom : (fmFlags s).getLast? = some false

/-- `LexInv`, and, when `b`, that we are inside an f-string. -/
def I (b : Bool) (s : TokState) : Prop := LexInv s ∧ (b = true → 0 < s.modeIndex)

/-- What `t` shares with `s`. -/
structure Same (s t : TokState) : Prop where
  level : t.level = s.level
  paren : t.parenstack = s.parenstack
  indent : t.indent = s.indent
  ind : t.indstack = s.indstack
  alt : t.altindstack = s.altindstack
  mi : t.modeIndex = s.modeIndex
  fm : fmFlags t = fmFlags s

theorem modes_length_of_flags {s t : TokState} (h : fmFlags t = fmFlags s) :
    t.modes.length = s.modes.length := by
  have := congrArg List.length h
  simpa [fmFlags] using this

theorem I.keep {b : Bool} {s t : TokState} (h : I b s) (e : Same s t) : I b t := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩, h10⟩ := h
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [e.level, e.paren]; exact h1
  · rw [e.level]; exact h2
  · rw [e.ind, e.indent]; exact h3
  · rw [e.alt, e.indent]; exact h4
  · rw [e.indent]; exact h5
  · rw [e.ind]; exact h6
  · rw [modes_length_of_flags e.fm, e.mi]; exact h7
  · rw [e.mi]; exact h8
  · rw [e.fm]; exact h9
  · rw [e.mi]; exact h10

/-- The state a run ends in, on a value or on `MAKE_TOKEN`. -/
def after {α : Type} : EStateM.Result Ret TokState α → TokState
  | .ok _ s => s
  | .error _ s => s

/-- `f` keeps `I b`. -/
def LP (b : Bool) {α : Type} (f : M α) : Prop := ∀ s, I b s → I b (after (f s))

theorem LP.pure {b : Bool} {α : Type} (a : α) : LP b (pure a : M α) := fun _ h => h

theorem LP.get {b : Bool} : LP b (get : M TokState) := fun _ h => h

theorem LP.throw {b : Bool} {α : Type} (e : Ret) : LP b (throw e : M α) := fun _ h => h

theorem LP.bind {b : Bool} {α β : Type} {m : M α} {k : α → M β} (hm : LP b m)
    (hk : ∀ a, LP b (k a)) : LP b (m >>= k) := by
  intro s h
  have h1 := hm s h
  show I b (after (EStateM.bind m k s))
  unfold EStateM.bind
  cases hr : m s with
  | ok a s' =>
    rw [hr] at h1
    exact hk a s' h1
  | error e s' =>
    rw [hr] at h1
    exact h1

theorem LP.ite {b : Bool} {α : Type} {c : Prop} [Decidable c] {x y : M α} (hx : LP b x) (hy : LP b y) :
    LP b (if c then x else y) := by
  by_cases h : c
  · rw [if_pos h]
    exact hx
  · rw [if_neg h]
    exact hy

theorem LP.modify' {b : Bool} (f : TokState → TokState) (h : ∀ s, I b s → I b (f s)) :
    LP b (modify f) := h

theorem LP.same {b : Bool} (f : TokState → TokState) (h : ∀ s, Same s (f s)) : LP b (modify f) :=
  LP.modify' f fun s hs => hs.keep (h s)

theorem setMode_modes (s : TokState) (f : Mode → Mode) (m : Mode) (ms : List Mode)
    (h : s.modes = m :: ms) : (s.setMode f).modes = f m :: ms := by
  show (match s.modes with
    | m :: ms => f m :: ms
    | [] => []) = _
  rw [h]

theorem modes_cons {s : TokState} (h : LexInv s) : ∃ m ms, s.modes = m :: ms := by
  have := h.modes
  cases hm : s.modes with
  | nil => rw [hm] at this; cases this
  | cons m ms => exact ⟨m, ms, rfl⟩

/-- Inside an f-string there are at least two modes. -/
theorem modes_two {s : TokState} (h : LexInv s) (hi : 0 < s.modeIndex) :
    ∃ m m' ms, s.modes = m :: m' :: ms := by
  have := h.modes
  cases hm : s.modes with
  | nil => rw [hm] at this; cases this
  | cons m ms =>
    cases ms with
    | nil =>
      rw [hm] at this
      simp at this
      omega
    | cons m' ms => exact ⟨m, m', ms, rfl⟩

/-- In `fstringMode`, there is an f-string to end. -/
theorem inside_of_mode {s : TokState} (h : LexInv s) (hf : s.mode.fstringMode = true) :
    0 < s.modeIndex := by
  have hm := h.modes
  have hb := h.bottom
  cases hi : s.modeIndex with
  | succ n => omega
  | zero =>
    rw [hi] at hm
    cases hs : s.modes with
    | nil => rw [hs] at hm; cases hm
    | cons m ms =>
      cases ms with
      | nil =>
        have e : s.mode = m := by
          show s.modes.headD {} = m
          rw [hs]
          rfl
        rw [e] at hf
        simp [fmFlags, hs, hf] at hb
      | cons a b =>
        rw [hs] at hm
        simp at hm

theorem same_setMode (s : TokState) (f : Mode → Mode)
    (hf : ∀ m, (f m).fstringMode = m.fstringMode) : fmFlags (s.setMode f) = fmFlags s := by
  cases hs : s.modes with
  | nil =>
    have : (s.setMode f).modes = [] := by
      show (match s.modes with
        | m :: ms => f m :: ms
        | [] => []) = _
      rw [hs]
    simp [fmFlags, this, hs]
  | cons m ms =>
    simp [fmFlags, setMode_modes s f m ms hs, hs, hf]

/-- `setMode` inside an f-string may do anything to the mode's fields. -/
theorem I_setMode_inside {b : Bool} {s : TokState} (h : I b s) (hi : 0 < s.modeIndex)
    (f : Mode → Mode) : I b (s.setMode f) := by
  obtain ⟨m, m', ms, hm⟩ := modes_two h.1 hi
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩, h10⟩ := h
  have e := setMode_modes s f m (m' :: ms) hm
  refine ⟨⟨h1, h2, h3, h4, h5, h6, ?_, h8, ?_⟩, h10⟩
  · show (s.setMode f).modes.length = s.modeIndex + 1
    rw [e]
    rw [hm] at h7
    exact h7
  · simp only [fmFlags, e]
    simp only [fmFlags, hm] at h9
    simpa [List.getLast?_cons_cons] using h9

/-- `setMode` that does not turn f-string mode on, anywhere. -/
theorem I_setMode {b : Bool} {s : TokState} (h : I b s) (f : Mode → Mode)
    (hf : ∀ m, (f m).fstringMode = m.fstringMode ∨ (f m).fstringMode = false) : I b (s.setMode f) := by
  by_cases hi : 0 < s.modeIndex
  · exact I_setMode_inside h hi f
  · obtain ⟨m, ms, hm⟩ := modes_cons h.1
    obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩, h10⟩ := h
    have e := setMode_modes s f m ms hm
    refine ⟨⟨h1, h2, h3, h4, h5, h6, ?_, h8, ?_⟩, h10⟩
    · show (s.setMode f).modes.length = s.modeIndex + 1
      rw [e]
      rw [hm] at h7
      exact h7
    · have hl : ms = [] := by
        rw [hm] at h7
        simp at h7
        cases ms with
        | nil => rfl
        | cons a b =>
          simp at h7
          omega
      subst hl
      simp only [fmFlags, e]
      simp only [fmFlags, hm] at h9
      rcases hf m with e2 | e2
      · simpa [e2] using h9
      · simp [e2]

theorem LP.setMode {b : Bool} (f : Mode → Mode)
    (hf : ∀ m, (f m).fstringMode = m.fstringMode ∨ (f m).fstringMode = false) :
    LP b (modify fun s => s.setMode f) :=
  LP.modify' _ fun _ h => I_setMode h f hf

theorem LP.setModeIn {b : Bool} (f : Mode → Mode) :
    LP b (modify fun s => if s.insideFString then s.setMode f else s) := by
  refine LP.modify' _ fun s h => ?_
  split
  · rename_i hi
    exact I_setMode_inside h (by simpa [TokState.insideFString] using hi) f
  · exact h

/-- Inside an f-string, `setMode` may do anything. -/
theorem LP.setModeT (f : Mode → Mode) : LP true (modify fun s => s.setMode f) :=
  LP.modify' _ fun _ h => I_setMode_inside h (h.2 rfl) f

theorem same_syntaxErrorRange (m : String) (a b : Int) (s : TokState) :
    Same s (syntaxErrorRange m a b s) := by
  unfold syntaxErrorRange
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem I_syntaxErrorRange {b : Bool} {s : TokState} (m : String) (x y : Int) (h : I b s) :
    I b (syntaxErrorRange m x y s) := h.keep (same_syntaxErrorRange m x y s)

/-- The leaves of `lp`, extended as each function is proved. -/
syntax "lp_leaf" : tactic

macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible exact LP.pure _)
macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible exact LP.get)
macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible exact LP.throw _)
macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible assumption)
macro_rules
  | `(tactic| lp_leaf) =>
    `(tactic| (with_reducible refine LP.same _ ?_); intro _; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
macro_rules
  | `(tactic| lp_leaf) =>
    `(tactic| (with_reducible refine LP.setMode _ ?_); intro _; first | exact Or.inl rfl | exact Or.inr rfl)
macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible exact LP.setModeIn _)

/-- Walk a monadic body down to its leaves. -/
macro "lp" : tactic => `(tactic| repeat' (first
  | lp_leaf
  | with_reducible refine LP.bind ?_ (fun _ => ?_)
  | with_reducible refine LP.ite ?_ ?_
  | dsimp only
  | split))

theorem lp_fuelOut {b : Bool} {α : Type} : LP b (fuelOut : M α) := fun _ h => h
theorem lp_emit0 {b : Bool} {α : Type} (t : Nat) : LP b (emit0 t : M α) := fun _ h => h
theorem lp_emit {b : Bool} {α : Type} (t x y : Nat) : LP b (emit t x y : M α) := fun _ h => h
theorem lp_errTok {b : Bool} {α : Type} : LP b (errTok : M α) := fun _ h => h

theorem lp_backup {b : Bool} (c : Int) : LP b (backup c) := by
  refine LP.modify' _ fun s h => ?_
  split
  · exact h.keep ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact h

theorem I_underflow {b : Bool} {s : TokState} (h : I b s) : I b (underflow s).2 := by
  unfold underflow
  dsimp only
  repeat' split
  all_goals first
    | exact h.keep ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    | exact h.keep ⟨rfl, rfl, rfl, rfl, rfl, rfl, same_setMode _ _ (fun _ => rfl)⟩

theorem I_nextcFast {b : Bool} {s : TokState} (h : I b s) : I b (nextcFast s).2 := by
  unfold nextcFast
  split <;> exact h.keep ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem I_nextcS {b : Bool} {s : TokState} (h : I b s) : I b (nextcS s).2 := by
  unfold nextcS
  split
  · exact I_nextcFast h
  · split
    · exact h
    · have hu := I_underflow h
      generalize underflow s = r at hu ⊢
      obtain ⟨rc, t⟩ := r
      dsimp only at hu ⊢
      split
      · exact hu.keep ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · have hl : I b { t with lineStart := t.cur } :=
          hu.keep ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        split
        · exact (I_syntaxErrorRange _ _ _ hl).keep ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        · exact I_nextcFast hl

theorem lp_nextc {b : Bool} : LP b nextc := fun _ h => I_nextcS h

macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible exact lp_fuelOut)
macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible exact lp_emit0 _)
macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible exact lp_emit _ _ _)
macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible exact lp_errTok)
macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible exact lp_backup _)
macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible exact lp_nextc)

theorem lp_syntaxerror {b : Bool} (m : String) : LP b (syntaxerror m) := by
  unfold syntaxerror
  exact LP.bind (LP.modify' _ fun _ h => I_syntaxErrorRange m _ _ h) fun _ => LP.pure _

theorem lp_syntaxerrorKnownRange {b : Bool} (x y : Int) (m : String) :
    LP b (syntaxerrorKnownRange x y m) := by
  unfold syntaxerrorKnownRange
  exact LP.bind (LP.modify' _ fun _ h => I_syntaxErrorRange m _ _ h) fun _ => LP.pure _

theorem lp_indenterror {b : Bool} : LP b indenterror := by
  unfold indenterror
  lp

theorem lp_parserWarn {b : Bool} (c m : String) : LP b (parserWarn c m) := by
  refine LP.modify' _ fun s h => ?_
  split
  · exact h.keep ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact h

theorem lp_warnInvalidEscape {b : Bool} (c : Nat) : LP b (warnInvalidEscape c) := lp_parserWarn _ _

macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible exact lp_syntaxerror _)
macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible exact lp_syntaxerrorKnownRange _ _ _)
macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible exact lp_indenterror)
macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible exact lp_parserWarn _ _)
macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible exact lp_warnInvalidEscape _)

theorem lp_setFtstringExpr {b : Bool} : LP b setFtstringExpr := by
  unfold setFtstringExpr
  lp

theorem LP.forM {b : Bool} {β : Type} (l : List β) (f : β → M Unit) (h : ∀ x, LP b (f x)) :
    LP b (l.forM f) := by
  induction l with
  | nil => exact LP.pure _
  | cons x xs ih =>
    show LP b (f x >>= fun _ => xs.forM f)
    exact LP.bind (h x) fun _ => ih

macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible exact lp_setFtstringExpr)

theorem lp_setExprStart {b : Bool} : LP b setExprStart :=
  LP.modify' _ fun _ h => I_setMode h _ fun _ => Or.inl rfl

macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible exact lp_setExprStart)
macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible refine LP.forM _ _ (fun _ => ?_))

theorem lp_lookahead_go {b : Bool} (rest consumed : List Nat) :
    LP b (lookahead.go rest consumed) := by
  induction rest generalizing consumed with
  | nil =>
    unfold lookahead.go
    lp
  | cons t ts ih =>
    unfold lookahead.go
    lp
    all_goals exact ih _

theorem lp_lookahead {b : Bool} (t : List Nat) : LP b (lookahead t) := lp_lookahead_go _ _

macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible exact lp_lookahead _)

theorem lp_verifyEndOfNumber {b : Bool} (c : Int) (k : String) : LP b (verifyEndOfNumber c k) := by
  unfold verifyEndOfNumber
  lp

theorem lp_verifyIdentifier {b : Bool} : LP b verifyIdentifier := by
  unfold verifyIdentifier
  lp

theorem lp_skipWhile {b : Bool} (p : Int → Bool) (f : Nat) : LP b (skipWhile p f) := by
  induction f with
  | zero =>
    unfold skipWhile
    exact lp_fuelOut
  | succ f ih =>
    unfold skipWhile
    lp

macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible exact lp_verifyEndOfNumber _ _)
macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible exact lp_verifyIdentifier)
macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible exact lp_skipWhile _ _)

theorem lp_decimalTail {b : Bool} (f : Nat) : LP b (decimalTail f) := by
  induction f with
  | zero =>
    unfold decimalTail
    exact lp_fuelOut
  | succ f ih =>
    unfold decimalTail
    lp

theorem lp_continuationLine {b : Bool} : LP b continuationLine := by
  unfold continuationLine
  lp

theorem lp_prefixError {b : Bool} (a c d e g : Bool) : LP b (prefixError a c d e g) := by
  unfold prefixError
  lp

theorem lp_errMsg {b : Bool} {α : Type} (m : String) : LP b (errMsg m : M α) := by
  unfold errMsg
  lp

macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible exact lp_decimalTail _)
macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible exact lp_continuationLine)
macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible exact lp_prefixError _ _ _ _ _)
macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible exact lp_errMsg _)

theorem lp_endNumber {b : Bool} {α : Type} (c : Int) : LP b (endNumber c : M α) := by
  unfold endNumber
  lp

macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible exact lp_endNumber _)

theorem lp_imaginaryPart {b : Bool} {α : Type} : LP b (imaginaryPart : M α) := by
  unfold imaginaryPart
  lp

macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible exact lp_imaginaryPart)

theorem lp_afterExponent {b : Bool} {α : Type} (c : Int) : LP b (afterExponent c : M α) := by
  unfold afterExponent
  lp

macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible exact lp_afterExponent _)

theorem lp_exponentPart {b : Bool} {α : Type} (f : Nat) (e : Int) : LP b (exponentPart f e : M α) := by
  unfold exponentPart
  lp

macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible exact lp_exponentPart _ _)

theorem lp_fractionPart {b : Bool} {α : Type} (f : Nat) (c : Int) : LP b (fractionPart f c : M α) := by
  unfold fractionPart
  lp

theorem lp_radixBody {b : Bool} (f : Nat) (d : Int → Bool) (k : String) (r : Bool) (n : Nat) (c : Int) :
    LP b (radixDigits.radixBody f d k r n c) := by
  induction n generalizing c with
  | zero =>
    unfold radixDigits.radixBody
    exact lp_fuelOut
  | succ n ih =>
    unfold radixDigits.radixBody
    lp
    all_goals exact ih _

macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible exact lp_radixBody _ _ _ _ _ _)

theorem lp_radixDigits {b : Bool} (f : Nat) (d : Int → Bool) (k : String) (r : Bool) (n : Nat) :
    LP b (radixDigits f d k r n) := by
  cases n with
  | zero =>
    unfold radixDigits
    exact lp_fuelOut
  | succ n =>
    unfold radixDigits
    lp

macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible exact lp_fractionPart _ _)
macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible exact lp_radixDigits _ _ _ _ _)

theorem lp_zeros {b : Bool} (f : Nat) (c : Int) : LP b (numberBranch.zeros f c) := by
  induction f generalizing c with
  | zero =>
    unfold numberBranch.zeros
    lp
  | succ f ih =>
    unfold numberBranch.zeros
    lp
    all_goals exact ih _

macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible exact lp_zeros _ _)

set_option maxHeartbeats 8000000 in
theorem lp_numberBranch {b : Bool} {α : Type} (c : Int) (f : Nat) :
    LP b (numberBranch c f : M α) := by
  unfold numberBranch
  lp

theorem lp_stringBody {b : Bool} (q qs : Int) (n : Nat) (e : Int) (x : Bool) :
    LP b (stringBody q qs n e x) := by
  induction n generalizing e x with
  | zero =>
    unfold stringBody
    exact lp_fuelOut
  | succ n ih =>
    unfold stringBody
    lp
    all_goals exact ih _ _

macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible exact lp_numberBranch _ _)
macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible exact lp_stringBody _ _ _ _ _)

set_option maxHeartbeats 8000000 in
theorem lp_letterQuote {b : Bool} {α : Type} (c : Int) (f : Nat) : LP b (letterQuote c f : M α) := by
  unfold letterQuote
  lp

theorem lp_pushMode {b : Bool} (m : Mode) (t : Ret) : LP b (pushMode m t) := by
  intro s h
  have e : pushMode m t s = if s.modeIndex + 1 ≥ MAXFSTRINGLEVEL then tooManyFStrings t s
      else .ok () { s with modes := m :: s.modes, modeIndex := s.modeIndex + 1 } := rfl
  rw [e]
  by_cases hc : s.modeIndex + 1 ≥ MAXFSTRINGLEVEL
  · rw [if_pos hc]
    exact (LP.bind (lp_syntaxerror _) fun _ => LP.throw _) s h
  · rw [if_neg hc]
    obtain ⟨hm0, ms, hm⟩ := modes_cons h.1
    obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩, _⟩ := h
    refine ⟨⟨h1, h2, h3, h4, h5, h6, ?_, ?_, ?_⟩, fun _ => Nat.succ_pos _⟩
    · show (m :: s.modes).length = s.modeIndex + 1 + 1
      simp [h7]
    · show s.modeIndex + 1 < MAXFSTRINGLEVEL
      omega
    · show (fmFlags { s with modes := m :: s.modes }).getLast? = _
      simp only [fmFlags, hm] at h9 ⊢
      simpa [List.getLast?_cons_cons] using h9

theorem lp_openBracket {b : Bool} (c : Int) : LP b (openBracket c) := by
  intro s h
  have e : openBracket c s = if s.level ≥ MAXLEVEL then tooManyParens s else
      let s1 := { s with parenstack := (c.toNat, s.lineno,
        (s.start.getD 0 : Int) - (s.lineStart : Int)) :: s.parenstack, level := s.level + 1 }
      .ok () (if s1.insideFString then s1.setMode fun m => { m with curlyDepth := m.curlyDepth + 1 }
        else s1) := rfl
  rw [e]
  by_cases hc : s.level ≥ MAXLEVEL
  · rw [if_pos hc]
    exact (lp_errMsg _) s h
  · rw [if_neg hc]
    have h1 : I b { s with parenstack := (c.toNat, s.lineno,
        (s.start.getD 0 : Int) - (s.lineStart : Int)) :: s.parenstack, level := s.level + 1 } := by
      obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩, a10⟩ := h
      refine ⟨⟨?_, ?_, a3, a4, a5, a6, a7, a8, a9⟩, a10⟩
      · show s.level + 1 = s.parenstack.length + 1
        omega
      · show s.level + 1 ≤ MAXLEVEL
        omega
    show I b (if _ then _ else _)
    split
    · exact I_setMode h1 _ fun _ => Or.inl rfl
    · exact h1

theorem lp_popParen {b : Bool} :
    LP b (modify fun s => { s with level := s.level - 1, parenstack := s.parenstack.drop 1 }) := by
  refine LP.modify' _ fun s h => ?_
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩, a10⟩ := h
  refine ⟨⟨?_, ?_, a3, a4, a5, a6, a7, a8, a9⟩, a10⟩
  · show s.level - 1 = (s.parenstack.drop 1).length
    simp [a1]
  · show s.level - 1 ≤ MAXLEVEL
    omega

macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible exact lp_letterQuote _ _)
macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible exact lp_pushMode _ _)
macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible exact lp_openBracket _)
macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible exact lp_popParen)

set_option maxHeartbeats 8000000 in
theorem lp_fStringQuote {b : Bool} {α : Type} (c : Int) : LP b (fStringQuote c : M α) := by
  unfold fStringQuote
  lp

macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible exact lp_fStringQuote _)

theorem lp_punctFString {b : Bool} (c : Int) : LP b (punctFString c) := by
  unfold punctFString
  lp

theorem lp_punctTwo {b : Bool} (c : Int) : LP b (punctTwo c) := by
  unfold punctTwo
  lp

set_option maxHeartbeats 8000000 in
theorem lp_punctBracket {b : Bool} (c : Int) : LP b (punctBracket c) := by
  unfold punctBracket
  lp

theorem lp_punctFinal {b : Bool} {α : Type} (c : Int) : LP b (punctFinal c : M α) := by
  unfold punctFinal
  lp

theorem lp_punctuation {b : Bool} {α : Type} (c : Int) : LP b (punctuation c : M α) := by
  unfold punctuation
  exact LP.bind (lp_punctFString c) fun _ => LP.bind (lp_punctTwo c) fun _ =>
    LP.bind (lp_punctBracket c) fun _ => lp_punctFinal c

macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible exact lp_punctuation _)

theorem lp_fromFStringQuote {b : Bool} (c : Int) (f : Nat) : LP b (fromFStringQuote c f) := by
  unfold fromFStringQuote
  lp

theorem lp_prefixLoop {b : Bool} (n : Nat) (a1 a2 a3 a4 a5 : Bool) (c : Int) :
    LP b (prefixLoop n a1 a2 a3 a4 a5 c) := by
  induction n generalizing a1 a2 a3 a4 a5 c with
  | zero =>
    unfold prefixLoop
    exact lp_fuelOut
  | succ n ih =>
    unfold prefixLoop
    lp
    all_goals exact ih _ _ _ _ _ _

macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible exact lp_fromFStringQuote _ _)
macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible exact lp_prefixLoop _ _ _ _ _ _ _)

theorem lp_eat {b : Bool} (n : Nat) (c : Int) : LP b (commentBranch.eat n c) := by
  induction n generalizing c with
  | zero =>
    unfold commentBranch.eat
    lp
  | succ n ih =>
    unfold commentBranch.eat
    lp
    all_goals exact ih _

macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible exact lp_eat _ _)

set_option maxHeartbeats 8000000 in
theorem lp_commentBranch {b : Bool} (f : Nat) (x : Bool) (c : Int) : LP b (commentBranch f x c) := by
  unfold commentBranch
  lp

macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible exact lp_commentBranch _ _ _)

theorem lp_idTail {b : Bool} (n : Nat) (c : Int) (x : Bool) : LP b (againPass.idTail n c x) := by
  induction n generalizing c x with
  | zero =>
    unfold againPass.idTail
    lp
  | succ n ih =>
    unfold againPass.idTail
    lp
    all_goals exact ih _ _

macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible exact lp_idTail _ _ _)

set_option maxHeartbeats 8000000 in
theorem lp_againPass {b : Bool} (f : Nat) (x : Bool) : LP b (againPass f x) := by
  unfold againPass
  lp

theorem lp_popIndents {b : Bool} (col n : Nat) : LP b (popIndents col n) := by
  induction n with
  | zero => exact LP.pure _
  | succ n ih =>
    intro s h
    have e : popIndents col (n + 1) s =
        if (decide (s.indent > 0) && decide (col < s.indstack.headD 0)) = true then
          popIndents col n { s with pendin := s.pendin - 1, indent := s.indent - 1,
                                    indstack := s.indstack.drop 1,
                                    altindstack := s.altindstack.drop 1 }
        else .ok () s := rfl
    rw [e]
    by_cases hc : (decide (s.indent > 0) && decide (col < s.indstack.headD 0)) = true
    · rw [if_pos hc]
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      refine ih _ ?_
      obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩, a10⟩ := h
      refine ⟨⟨a1, a2, ?_, ?_, ?_, ?_, a7, a8, a9⟩, a10⟩
      · show (s.indstack.drop 1).length = s.indent - 1 + 1
        simp [a3]
        omega
      · show (s.altindstack.drop 1).length = s.indent - 1 + 1
        simp [a4]
        omega
      · show s.indent - 1 < MAXINDENT
        omega
      · show (s.indstack.drop 1).Pairwise (· > ·)
        cases hl : s.indstack with
        | nil => simp
        | cons x xs =>
          rw [hl] at a6
          exact (List.pairwise_cons.mp a6).2
    · rw [if_neg hc]
      exact h

theorem head_gt_all {l : List Nat} {col : Nat} (h : col > l.headD 0) (hp : l.Pairwise (· > ·)) :
    ∀ a, a ∈ l → col > a := by
  cases l with
  | nil => intro a ha; cases ha
  | cons x xs =>
    intro a ha
    have hx : col > x := h
    rcases List.mem_cons.mp ha with e | e
    · rw [e]
      exact hx
    · have := (List.pairwise_cons.mp hp).1 a e
      omega

theorem lp_tabError {b : Bool} : LP b tabError := by
  unfold tabError
  lp

macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible exact lp_tabError)
macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible exact lp_popIndents _ _)

theorem lp_tooDeep {b : Bool} : LP b tooDeep := by
  unfold tooDeep
  lp

theorem lp_dedentTo {b : Bool} (c a n : Nat) : LP b (dedentTo c a n) := by
  unfold dedentTo
  lp

theorem I_pushIndent {b : Bool} {s : TokState} (col altcol : Nat) (hc : col > s.indstack.headD 0)
    (h : I b s) : I b (after (pushIndent col altcol s)) := by
  have e : pushIndent col altcol s =
      if s.indent + 1 ≥ MAXINDENT then tooDeep s
      else if altcol ≤ s.altindstack.headD 0 then tabError s
      else .ok () { s with pendin := s.pendin + 1, indent := s.indent + 1,
                           indstack := col :: s.indstack,
                           altindstack := altcol :: s.altindstack } := rfl
  rw [e]
  by_cases h0 : s.indent + 1 ≥ MAXINDENT
  · rw [if_pos h0]
    exact lp_tooDeep s h
  · rw [if_neg h0]
    by_cases h1 : altcol ≤ s.altindstack.headD 0
    · rw [if_pos h1]
      exact lp_tabError s h
    · rw [if_neg h1]
      obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩, a10⟩ := h
      refine ⟨⟨a1, a2, ?_, ?_, ?_, ?_, a7, a8, a9⟩, a10⟩
      · show (col :: s.indstack).length = s.indent + 1 + 1
        simp [a3]
      · show (altcol :: s.altindstack).length = s.indent + 1 + 1
        simp [a4]
      · show s.indent + 1 < MAXINDENT
        omega
      · show (col :: s.indstack).Pairwise (· > ·)
        exact List.pairwise_cons.mpr ⟨head_gt_all hc a6, a6⟩

theorem lp_indentStack {b : Bool} (col altcol : Nat) : LP b (indentStack col altcol) := by
  intro s h
  have e : indentStack col altcol s =
      if col == s.indstack.headD 0 then
        (if altcol != s.altindstack.headD 0 then tabError s else .ok () s)
      else if col > s.indstack.headD 0 then pushIndent col altcol s
      else dedentTo col altcol (s.indent + 1) s := rfl
  rw [e]
  by_cases h0 : (col == s.indstack.headD 0) = true
  · rw [if_pos h0]
    by_cases h1 : (altcol != s.altindstack.headD 0) = true
    · rw [if_pos h1]
      exact lp_tabError s h
    · rw [if_neg h1]
      exact h
  · rw [if_neg h0]
    by_cases h1 : col > s.indstack.headD 0
    · rw [if_pos h1]
      exact I_pushIndent col altcol h1 h
    · rw [if_neg h1]
      exact lp_dedentTo _ _ _ s h

macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible exact lp_againPass _ _)
macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible exact lp_indentStack _ _)

theorem lp_scan {b : Bool} (f a c d : Nat) : LP b (indentation.scan f a c d) := by
  induction f generalizing a c d with
  | zero =>
    unfold indentation.scan
    exact lp_fuelOut
  | succ f ih =>
    unfold indentation.scan
    lp
    all_goals exact ih _ _ _

macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible exact lp_scan _ _ _ _)

theorem lp_indentation {b : Bool} (f : Nat) : LP b (indentation f) := by
  unfold indentation
  lp

macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible exact lp_indentation _)

theorem lp_normalMode {b : Bool} (fuel n : Nat) (x : Option Bool) : LP b (normalMode fuel n x) := by
  induction n generalizing x with
  | zero =>
    unfold normalMode
    exact lp_fuelOut
  | succ n ih =>
    cases x with
    | none =>
      unfold normalMode
      lp
      all_goals exact ih _
    | some y =>
      unfold normalMode
      lp
      all_goals exact ih _

macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible exact lp_normalMode _ _ _)

set_option maxHeartbeats 8000000 in
theorem lp_fstringMiddle {b : Bool} (n k : Nat) (x : Bool) : LP b (fstringMiddle n k x) := by
  induction n generalizing k x with
  | zero =>
    unfold fstringMiddle
    exact lp_fuelOut
  | succ n ih =>
    unfold fstringMiddle
    lp
    all_goals exact ih _ _

macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible exact lp_fstringMiddle _ _ _)

theorem lp_atEnd {b : Bool} (q n : Nat) (c : Mode) : LP b (fstringMode.atEnd c n) := by
  induction n with
  | zero =>
    unfold fstringMode.atEnd
    lp
  | succ n ih =>
    unfold fstringMode.atEnd
    lp

macro_rules | `(tactic| lp_leaf) => `(tactic| with_reducible exact lp_atEnd 0 _ _)

/-- Starts inside an f-string, may end outside. -/
def LPF {α : Type} (f : M α) : Prop := ∀ s, I true s → I false (after (f s))

theorem LPF.ofLP {α : Type} {f : M α} (h : LP true f) : LPF f := fun s hs => ⟨(h s hs).1, nofun⟩

theorem LPF.bind {α β : Type} {m : M α} {k : α → M β} (hm : LP true m) (hk : ∀ a, LPF (k a)) :
    LPF (m >>= k) := by
  intro s h
  have h1 := hm s h
  show I false (after (EStateM.bind m k s))
  unfold EStateM.bind
  cases hr : m s with
  | ok a s' =>
    rw [hr] at h1
    exact hk a s' h1
  | error e s' =>
    rw [hr] at h1
    exact ⟨h1.1, nofun⟩

theorem LPF.ite {α : Type} {c : Prop} [Decidable c] {x y : M α} (hx : LPF x) (hy : LPF y) :
    LPF (if c then x else y) := by
  by_cases h : c
  · rw [if_pos h]
    exact hx
  · rw [if_neg h]
    exact hy

theorem lpf_pop {β : Type} {k : Unit → M β} (hk : ∀ a, LP false (k a)) : LPF (popMode >>= k) := by
  intro s h
  obtain ⟨m, m', ms, hm⟩ := modes_two h.1 (h.2 rfl)
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩, a10⟩ := h
  have hp : I false { s with modes := s.modes.drop 1, modeIndex := s.modeIndex - 1 } := by
    have hpos := a10 rfl
    refine ⟨⟨a1, a2, a3, a4, a5, a6, ?_, ?_, ?_⟩, nofun⟩
    · show (s.modes.drop 1).length = s.modeIndex - 1 + 1
      rw [List.length_drop, a7]
      omega
    · show s.modeIndex - 1 < MAXFSTRINGLEVEL
      omega
    · show (fmFlags { s with modes := s.modes.drop 1 }).getLast? = _
      simp only [fmFlags, hm, List.drop_succ_cons, List.drop_zero] at a9 ⊢
      simpa [List.getLast?_cons_cons] using a9
  exact hk () _ hp

set_option maxHeartbeats 8000000 in
theorem lpf_fstringMode (fuel : Nat) : LPF (fstringMode fuel) := by
  unfold fstringMode
  repeat' (first
    | with_reducible refine lpf_pop (fun _ => ?_)
    | lp_leaf
    | with_reducible refine LP.bind ?_ (fun _ => ?_)
    | with_reducible refine LPF.bind ?_ (fun _ => ?_)
    | with_reducible refine LP.ite ?_ ?_
    | with_reducible refine LPF.ite ?_ ?_
    | dsimp only
    | split
    | refine LPF.ofLP ?_)

/-- Across any call of `tok_get`, on any state that starts sound, the state stays sound: `level`
matches `parenstack` and stays within `MAXLEVEL`, `indent` matches `indstack` and `altindstack`
and stays below `MAXINDENT`, indentation columns strictly increase, and `tok_mode_stack_index`
matches the mode stack, stays below `MAXFSTRINGLEVEL`, and is never decremented at the regular
mode. So the fixed-size arrays of `struct tok_state` are written in bounds, on every source. -/
def LexStacks : Prop := ∀ s : TokState, LexInv s → LexInv (tokenizerGet s).1

theorem lexInv_err (t : TokState) (h : I false t) (e : Option PyError) (d : Nat) :
    LexInv { t with err := e, done := d } := by
  have : I false { t with err := e, done := d } := h.keep ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact this.1

theorem lexInv_done (t : TokState) (h : I false t) (d : Nat) : LexInv { t with done := d } := by
  have : I false { t with done := d } := h.keep ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact this.1

theorem lexStacks_proven : LexStacks := by
  intro s h
  have h0 : I false { s with metadata := none } :=
    I.keep (s := s) ⟨h, nofun⟩ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  unfold tokenizerGet
  dsimp only
  have hb : ∀ fuel, I false (after ((if ({ s with metadata := none } : TokState).mode.fstringMode
      then fstringMode fuel else normalMode fuel fuel none) { s with metadata := none })) := by
    intro fuel
    split
    · rename_i hf
      exact lpf_fstringMode fuel _ ⟨h0.1, fun _ => inside_of_mode h0.1 hf⟩
    · exact lp_normalMode fuel fuel none _ h0
  have hb' := hb (s.src.size + 16)
  generalize (if ({ s with metadata := none } : TokState).mode.fstringMode
      then fstringMode (s.src.size + 16)
      else normalMode (s.src.size + 16) (s.src.size + 16) none) { s with metadata := none } = r
    at hb' ⊢
  cases r with
  | ok a t => exact lexInv_err t hb' _ _
  | error e t =>
    dsimp only
    split
    · exact lexInv_err t hb' _ _
    · split
      · exact lexInv_done t hb' _
      · exact hb'.1

/-- A tokenizer starts sound: `_PyTokenizer_tok_new`, whatever the source. -/
theorem lexInv_new (src : Array Nat) (enc : Option String) :
    LexInv { src := src, encoding := enc } :=
  ⟨rfl, Nat.zero_le _, rfl, rfl, show 0 < MAXINDENT by decide, by simp, rfl,
    show 0 < MAXFSTRINGLEVEL by decide, rfl⟩

end PyLean.PyGrammar.Lexer
