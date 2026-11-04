import PyLean.PyGrammar.Peg.TokenProps

/-!
The frame lemma of the parser: nothing an action does moves the parser. Every helper of
`Parser/action_helpers.c` and every macro of `Parser/pegen.h` that a generated action calls leaves
`p->mark` where it was, keeps the tokens already read, leaves the memo table alone, and never
clears `error_indicator`. Reading a token is the one thing an action may do to the token array,
through `RAISE_SYNTAX_ERROR_ON_NEXT_TOKEN`, and it only appends.

`Frame` is proved for each function the actions reach, and through `evalA`, so it covers every
action in the grammar data. It depends on those bodies: an action that moved the mark would break
`frame_callHelper`.
-/

namespace PyLean.PyGrammar.Peg

open Lexer

/-- Tokens are only appended. -/
structure TokGrows (p q : PS) : Prop where
  le : p.fill ≤ q.fill
  same : ∀ i, i < p.fill → q.tokenAt i = p.tokenAt i

theorem TokGrows.refl (p : PS) : TokGrows p p := ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem TokGrows.trans {p q r : PS} (a : TokGrows p q) (b : TokGrows q r) : TokGrows p r :=
  ⟨Nat.le_trans a.le b.le, fun i h => (b.same i (Nat.lt_of_lt_of_le h a.le)).trans (a.same i h)⟩

/-- What holds between any two states of one parse: tokens only grow, and `error_indicator` is
never cleared. -/
structure Grows (p q : PS) : Prop where
  toks : TokGrows p q
  err : p.errorIndicator = true → q.errorIndicator = true

theorem Grows.refl (p : PS) : Grows p p := ⟨TokGrows.refl p, fun h => h⟩

theorem Grows.trans {p q r : PS} (a : Grows p q) (b : Grows q r) : Grows p r :=
  ⟨a.toks.trans b.toks, fun h => b.err (a.err h)⟩

/-- `error_indicator` still clear at the end means it was clear all along. -/
theorem Grows.err_false {p q : PS} (g : Grows p q) (h : q.errorIndicator = false) :
    p.errorIndicator = false := by
  cases hp : p.errorIndicator with
  | false => rfl
  | true => rw [g.err hp] at h; exact h

/-- One step that leaves the parser's position and memo alone. -/
structure Step (p q : PS) : Prop where
  mark : q.mark = p.mark
  grows : Grows p q
  memo : ∀ i, q.memo.getD i [] = p.memo.getD i []

theorem Step.refl (p : PS) : Step p p := ⟨rfl, Grows.refl p, fun _ => rfl⟩

theorem Step.trans {p q r : PS} (a : Step p q) (b : Step q r) : Step p r :=
  ⟨b.mark.trans a.mark, a.grows.trans b.grows, fun i => (b.memo i).trans (a.memo i)⟩

/-- From `Keeps`, and `error_indicator` not cleared. -/
theorem Step.ofKeep {p q : PS} (h : q.mark = p.mark ∧ q.tokens = p.tokens ∧ q.memo = p.memo)
    (e : p.errorIndicator = true → q.errorIndicator = true) : Step p q := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, ⟨⟨?_, fun i _ => ?_⟩, e⟩, fun i => by rw [h3]⟩
  · simp only [PS.fill, h2, Nat.le_refl]
  · simp only [PS.tokenAt, h2]

/-- `f` leaves the parser where it was, whatever state it starts from. -/
def Frame {α : Type} (f : PM α) : Prop := ∀ p, Step p (f p).2

theorem Frame.pure {α : Type} (a : α) : Frame (pure a : PM α) := fun p => Step.refl p

theorem Frame.get : Frame (get : PM PS) := fun p => Step.refl p

theorem Frame.bind {α β : Type} {m : PM α} {k : α → PM β} (hm : Frame m) (hk : ∀ a, Frame (k a)) :
    Frame (m >>= k) := fun p => (hm p).trans (hk (m p).1 (m p).2)

theorem Frame.modify_ (f : PS → PS) (h1 : ∀ p, (f p).mark = p.mark)
    (h2 : ∀ p, (f p).tokens = p.tokens) (h3 : ∀ p, (f p).memo = p.memo)
    (h4 : ∀ p, p.errorIndicator = true → (f p).errorIndicator = true) : Frame (modify f) :=
  fun p => Step.ofKeep ⟨h1 p, h2 p, h3 p⟩ (h4 p)

/-- The leaves of `frame`, extended as each function is proved. -/
syntax "frame_leaf" : tactic

macro_rules | `(tactic| frame_leaf) => `(tactic| with_reducible exact Frame.pure _)
macro_rules | `(tactic| frame_leaf) => `(tactic| with_reducible exact Frame.get)
macro_rules | `(tactic| frame_leaf) => `(tactic| with_reducible assumption)
macro_rules
  | `(tactic| frame_leaf) =>
    `(tactic| (with_reducible refine Frame.modify_ _ ?_ ?_ ?_ ?_) <;> intros <;>
      first | rfl | assumption)

/-- Walk a monadic body down to its leaves. -/
macro "frame" : tactic => `(tactic| repeat' (first
  | frame_leaf
  | with_reducible refine Frame.bind ?_ (fun _ => ?_)
  | split
  | dsimp only))

theorem frame_setErr (e : PyError) : Frame (setErr e) := by
  unfold setErr
  frame

macro_rules | `(tactic| frame_leaf) => `(tactic| with_reducible exact frame_setErr _)

/-- `_PyPegen_raise_error_known_location` leaves `error_indicator` set, with or without an
exception before it. -/
theorem raiseKnownLocation_ei (cls msg : String) (a b c d : Int) (p : PS) :
    (raiseKnownLocation cls a b c d msg p).2.errorIndicator = true := by
  by_cases h : Fresh p
  · obtain ⟨_, _, _, _, _, _, h6⟩ := raiseKnownLocation_err p cls msg a b c d h
    exact h6
  · have h' : p.errorIndicator = true ∧ p.errOccurred = true := by simpa [Fresh] using h
    rw [(firstErrorWins_proven p h'.1 h'.2).1 cls msg a b c d]
    exact h'.1

theorem frame_raiseKnownLocation (cls msg : String) (a b c d : Int) :
    Frame (raiseKnownLocation cls a b c d msg) := fun p =>
  Step.ofKeep (keeps_raiseKnownLocation cls msg a b c d p)
    (fun _ => raiseKnownLocation_ei cls msg a b c d p)

macro_rules | `(tactic| frame_leaf) => `(tactic| with_reducible exact frame_raiseKnownLocation _ _ _ _ _ _)

theorem frame_raiseErrorKnownLocation (cls msg : String) (a b c d : Int) :
    Frame (raiseErrorKnownLocation cls a b c d msg) := frame_raiseKnownLocation _ _ _ _ _ _

macro_rules | `(tactic| frame_leaf) => `(tactic| with_reducible exact frame_raiseErrorKnownLocation _ _ _ _ _ _)

theorem frame_raiseUnclosed : Frame raiseUnclosed := by
  unfold raiseUnclosed
  frame

theorem frame_stackOverflow : Frame stackOverflow := by
  unfold stackOverflow
  frame

theorem frame_raiseAtToken (cls : String) (t : Token) (msg : String) :
    Frame (raiseAtToken cls t msg) := by
  unfold raiseAtToken
  frame

macro_rules | `(tactic| frame_leaf) => `(tactic| with_reducible exact frame_raiseUnclosed)
macro_rules | `(tactic| frame_leaf) => `(tactic| with_reducible exact frame_stackOverflow)
macro_rules | `(tactic| frame_leaf) => `(tactic| with_reducible exact frame_raiseAtToken _ _ _)

theorem frame_raiseError0 (cls msg : String) : Frame (raiseError0 cls msg) := by
  unfold raiseError0
  frame

macro_rules | `(tactic| frame_leaf) => `(tactic| with_reducible exact frame_raiseError0 _ _)

theorem frame_tokenizerErrorSwitch (s : TokState) : Frame (tokenizerErrorSwitch s) := by
  unfold tokenizerErrorSwitch
  frame

macro_rules | `(tactic| frame_leaf) => `(tactic| with_reducible exact frame_tokenizerErrorSwitch _)

theorem frame_tokenizerError : Frame tokenizerError := by
  unfold tokenizerError
  frame

theorem frame_raiseDecodeBody (l : Option Loc) (e : Option PyError) : Frame (raiseDecodeBody l e) := by
  cases e with
  | none => exact Frame.pure _
  | some x =>
    unfold raiseDecodeBody
    frame

macro_rules | `(tactic| frame_leaf) => `(tactic| with_reducible exact frame_raiseDecodeBody _ _)

theorem frame_raiseDecodeError : Frame raiseDecodeError := by
  unfold raiseDecodeError
  frame

theorem frame_raiseDecodeKnown (l : Loc) : Frame (raiseDecodeKnown l) := by
  unfold raiseDecodeKnown
  frame

macro_rules | `(tactic| frame_leaf) => `(tactic| with_reducible exact frame_raiseDecodeKnown _)

macro_rules | `(tactic| frame_leaf) => `(tactic| with_reducible exact frame_tokenizerError)
macro_rules | `(tactic| frame_leaf) => `(tactic| with_reducible exact frame_raiseDecodeError)

/-- `pushToken` adds a token and an empty memo slot. -/
theorem step_pushToken (p : PS) : Step p (pushToken p).1 := by
  obtain ⟨h1, h2, h3, h4⟩ := pushToken_fields p
  have he : (pushToken p).1.errorIndicator = p.errorIndicator := by
    unfold pushToken
    dsimp only
    generalize getTokSkippingIgnores (p.tok.src.size + 2) p.tok p.typeIgnores = r
    obtain ⟨s, ty, t, ig⟩ := r
    dsimp only
    repeat' split
    all_goals rfl
  refine ⟨h1, ⟨⟨?_, h3⟩, fun h => he.trans h⟩, fun i => ?_⟩
  · show p.tokens.size ≤ (pushToken p).1.tokens.size
    omega
  · rw [h4]
    by_cases hi : i < p.memo.size
    · simp [Array.getD_eq_getD_getElem?, Array.getElem?_push, hi, Nat.ne_of_lt hi]
    · by_cases he : i = p.memo.size
      · subst he
        simp [Array.getD_eq_getD_getElem?]
      · have h1 : p.memo.size ≤ i := Nat.le_of_not_lt hi
        have h2 : ¬ i = p.memo.size := he
        simp [Array.getD_eq_getD_getElem?, Array.getElem?_push, h1, h2]

theorem frame_fillToken : Frame fillToken := by
  intro p
  refine (step_pushToken p).trans ?_
  rw [fillToken_step]
  dsimp only
  split
  · split
    · exact frame_raiseDecodeError _
    · exact frame_tokenizerError _
  · exact Step.refl _

macro_rules | `(tactic| frame_leaf) => `(tactic| with_reducible exact frame_fillToken)

theorem frame_ensureToken : Frame ensureToken := by
  intro p
  rw [ensureToken_eq]
  split
  · split
    · have s := frame_fillToken p
      exact ⟨s.mark, ⟨⟨s.grows.toks.le, s.grows.toks.same⟩, fun _ => rfl⟩, s.memo⟩
    · exact frame_fillToken p
  · exact Step.refl _

macro_rules | `(tactic| frame_leaf) => `(tactic| with_reducible exact frame_ensureToken)

theorem frame_raiseError (cls : String) (m : Bool) (msg : String) :
    Frame (raiseError cls m msg) := by
  unfold raiseError
  frame

macro_rules | `(tactic| frame_leaf) => `(tactic| with_reducible exact frame_raiseError _ _ _)

theorem frame_warnInvalidEscapeSeq (buf : Array Nat) (ptr : Nat) (t : Token) :
    Frame (warnInvalidEscapeSeq buf ptr t) := by
  unfold warnInvalidEscapeSeq
  frame

macro_rules | `(tactic| frame_leaf) => `(tactic| with_reducible exact frame_warnInvalidEscapeSeq _ _ _)

theorem frame_decodeUnicodeWithEscapes (s : List Nat) (t : Option Token) :
    Frame (decodeUnicodeWithEscapes s t) := by
  unfold decodeUnicodeWithEscapes
  frame

macro_rules | `(tactic| frame_leaf) => `(tactic| with_reducible exact frame_decodeUnicodeWithEscapes _ _)

theorem frame_decodeString (raw : Bool) (s : List Nat) (t : Option Token) :
    Frame (decodeString raw s t) := by
  unfold decodeString
  frame

macro_rules | `(tactic| frame_leaf) => `(tactic| with_reducible exact frame_decodeString _ _ _)

theorem frame_parseString (t : Token) : Frame (parseString t) := by
  unfold parseString
  frame

macro_rules | `(tactic| frame_leaf) => `(tactic| with_reducible exact frame_parseString _)

theorem frame_decodeFstringPart (r : Bool) (c t : Ast) : Frame (decodeFstringPart r c t) := by
  unfold decodeFstringPart
  frame

macro_rules | `(tactic| frame_leaf) => `(tactic| with_reducible exact frame_decodeFstringPart _ _ _)

theorem frame_resizedLoop (r t : Bool) (b : Ast) (xs acc : List Ast) :
    Frame (resizedLoop r t b xs acc) := by
  induction xs generalizing acc with
  | nil =>
    unfold resizedLoop
    frame
  | cons x xs ih =>
    unfold resizedLoop
    frame
    all_goals exact ih _

macro_rules | `(tactic| frame_leaf) => `(tactic| with_reducible exact frame_resizedLoop _ _ _ _ _)

theorem frame_getResizedExprs (a r b : Ast) (t : Bool) : Frame (getResizedExprs a r b t) := by
  unfold getResizedExprs
  frame

theorem frame_concatenateStrings (s : Ast) (a b c d : Int) :
    Frame (concatenateStrings s a b c d) := by
  unfold concatenateStrings
  frame

macro_rules | `(tactic| frame_leaf) => `(tactic| with_reducible exact frame_getResizedExprs _ _ _ _)
macro_rules | `(tactic| frame_leaf) => `(tactic| with_reducible exact frame_concatenateStrings _ _ _ _ _)

theorem frame_setupFullFormatSpec (c s : Ast) (a b e d : Int) :
    Frame (setupFullFormatSpec c s a b e d) := by
  unfold setupFullFormatSpec
  frame

theorem frame_ensureImaginary (e : Ast) : Frame (ensureImaginary e) := by
  unfold ensureImaginary
  frame

theorem frame_ensureReal (e : Ast) : Frame (ensureReal e) := by
  unfold ensureReal
  frame

theorem frame_checkBarry (t : Ast) : Frame (checkBarry t) := by
  unfold checkBarry
  frame

theorem frame_raiseRange (cls : String) (a b : Ast) (msg : String) :
    Frame (raiseRange cls a b msg) := frame_raiseKnownLocation _ _ _ _ _ _

macro_rules | `(tactic| frame_leaf) => `(tactic| with_reducible exact frame_raiseRange _ _ _ _)

theorem frame_checkFstringConversion (a b : Ast) : Frame (checkFstringConversion a b) := by
  unfold checkFstringConversion
  frame

theorem frame_argumentsParsingError (e : Ast) : Frame (argumentsParsingError e) := by
  unfold argumentsParsingError
  frame

theorem frame_nonparenGenexp (a b : Ast) : Frame (nonparenGenexp a b) := by
  unfold nonparenGenexp
  frame

theorem frame_registerStmts (a : Ast) : Frame (registerStmts a) := by
  unfold registerStmts
  frame

macro_rules | `(tactic| frame_leaf) => `(tactic| with_reducible exact frame_setupFullFormatSpec _ _ _ _ _ _)
macro_rules | `(tactic| frame_leaf) => `(tactic| with_reducible exact frame_ensureImaginary _)
macro_rules | `(tactic| frame_leaf) => `(tactic| with_reducible exact frame_ensureReal _)
macro_rules | `(tactic| frame_leaf) => `(tactic| with_reducible exact frame_checkBarry _)
macro_rules | `(tactic| frame_leaf) => `(tactic| with_reducible exact frame_checkFstringConversion _ _)
macro_rules | `(tactic| frame_leaf) => `(tactic| with_reducible exact frame_argumentsParsingError _)
macro_rules | `(tactic| frame_leaf) => `(tactic| with_reducible exact frame_nonparenGenexp _ _)
macro_rules | `(tactic| frame_leaf) => `(tactic| with_reducible exact frame_registerStmts _)

theorem frame_raiseErrorForMissingComma (a b : Ast) : Frame (raiseErrorForMissingComma a b) := by
  unfold raiseErrorForMissingComma
  frame

theorem frame_emitSyntaxWarning (msg : String) (a b c d : Int) :
    Frame (emitSyntaxWarning msg a b c d) := by
  unfold emitSyntaxWarning
  frame

macro_rules | `(tactic| frame_leaf) => `(tactic| with_reducible exact frame_emitSyntaxWarning _ _ _ _ _)

theorem frame_warnRelativeImportOfLazy (d m : Ast) : Frame (warnRelativeImportOfLazy d m) := by
  unfold warnRelativeImportOfLazy
  frame

macro_rules | `(tactic| frame_leaf) => `(tactic| with_reducible exact frame_warnRelativeImportOfLazy _ _)

theorem frame_checkedFromImport (d m n z : Ast) (a b c e : Int) :
    Frame (checkedFromImport d m n z a b c e) := by
  unfold checkedFromImport
  frame

macro_rules | `(tactic| frame_leaf) => `(tactic| with_reducible exact frame_raiseErrorForMissingComma _ _)
macro_rules | `(tactic| frame_leaf) => `(tactic| with_reducible exact frame_checkedFromImport _ _ _ _ _ _ _ _)

set_option maxHeartbeats 4000000 in
/-- Every helper of `Parser/action_helpers.c` and macro of `Parser/pegen.h` an action calls. -/
theorem frame_callHelper (h : Helper) (args : List Ast) : Frame (callHelper h args) := by
  unfold callHelper
  cases h <;> frame

macro_rules | `(tactic| frame_leaf) => `(tactic| with_reducible exact frame_callHelper _ _)

mutual
  theorem frame_evalA (env : Array Ast) (ex : Extra) : (e : AE) → Frame (evalA env ex e)
    | .var _ | .null | .extra0 | .extra1 | .extra2 | .extra3 | .tokState | .pyNone | .pyTrue
    | .pyFalse | .pyEllipsis | .int _ | .str _ | .ctor _ | .lastTok => by
      unfold evalA
      frame
    | .mk c args => by
      have := frame_evalList env ex args
      unfold evalA
      frame
    | .call h args => by
      have := frame_evalList env ex args
      unfold evalA
      frame
    | .check e => by
      have := frame_evalA env ex e
      unfold evalA
      frame
    | .checkNull e => by
      have := frame_evalA env ex e
      unfold evalA
      frame
    | .checkVersion v m n => by
      have := frame_evalA env ex v
      have := frame_evalA env ex m
      have := frame_evalA env ex n
      unfold evalA
      frame
    | .ite c a b => by
      have := frame_evalA env ex c
      have := frame_evalA env ex a
      have := frame_evalA env ex b
      unfold evalA
      frame
    | .and_ a b => by
      have := frame_evalA env ex a
      have := frame_evalA env ex b
      unfold evalA
      frame
    | .or_ a b => by
      have := frame_evalA env ex a
      have := frame_evalA env ex b
      unfold evalA
      frame
    | .eq a b => by
      have := frame_evalA env ex a
      have := frame_evalA env ex b
      unfold evalA
      frame
    | .not_ a => by
      have := frame_evalA env ex a
      unfold evalA
      frame
    | .sub a b => by
      have := frame_evalA env ex a
      have := frame_evalA env ex b
      unfold evalA
      frame
    | .add a b => by
      have := frame_evalA env ex a
      have := frame_evalA env ex b
      unfold evalA
      frame
    | .field e _ => by
      have := frame_evalA env ex e
      unfold evalA
      frame
    | .kind e => by
      have := frame_evalA env ex e
      unfold evalA
      frame
    | .attr e _ => by
      have := frame_evalA env ex e
      unfold evalA
      frame

  theorem frame_evalList (env : Array Ast) (ex : Extra) :
      (l : List AE) → Frame (evalA.evalList env ex l)
    | [] => by
      unfold evalA.evalList
      frame
    | a :: as => by
      have := frame_evalA env ex a
      have := frame_evalList env ex as
      unfold evalA.evalList
      frame
end

end PyLean.PyGrammar.Peg
