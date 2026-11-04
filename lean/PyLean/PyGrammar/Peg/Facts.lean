import PyLean.PyGrammar.Peg.Interp

/-!
Universally quantified facts about the parser's runtime helpers: errors, the memo, and the
actions that build `arguments` and concatenate strings. Hypotheses, where any, are the type
invariants of the C structures and are named in the docstrings.
-/

namespace PyLean.PyGrammar.Peg

open Lexer

/-! ### First error wins -/

/-- `// Bail out if we already have an error set.`: with `error_indicator` and an exception
set, no raise replaces the exception or changes the parser, whichever entry point is
used. -/
def FirstErrorWins : Prop :=
  ∀ (p : PS), p.errorIndicator = true → p.errOccurred = true →
    (∀ (cls msg : String) (a b c d : Int), (raiseKnownLocation cls a b c d msg p).2 = p) ∧
    (∀ (cls msg : String), (raiseError0 cls msg p).2 = p) ∧
    (∀ (cls msg : String) (m : Bool), (raiseError cls m msg p).2 = p)

theorem firstErrorWins_proven : FirstErrorWins := by
  intro p h1 h2
  refine ⟨?_, ?_, ?_⟩
  · intro cls msg a b c d
    simp [raiseKnownLocation, h1, h2, bind, StateT.bind, get, getThe, MonadStateOf.get,
      StateT.get, pure, StateT.pure]
  · intro cls msg
    simp [raiseError0, h1, h2, bind, StateT.bind, get, getThe, MonadStateOf.get,
      StateT.get, pure, StateT.pure]
  · intro cls msg m
    simp [raiseError, h1, h2, bind, StateT.bind, get, getThe, MonadStateOf.get,
      StateT.get, pure, StateT.pure]

/-- `_Pypegen_tokenizer_error` returns `-1` from every branch of its switch. -/
def TokenizerErrorIsFailure : Prop := ∀ p : PS, (tokenizerError p).1 = -1

/-! ### `arguments` -/

theorem seqOf_getNames (s : Ast) : (seqOf (getNames s)).length = (seqOf s).length := by
  simp [getNames, seqOf]

theorem seqOf_getDefaults (s : Ast) : (seqOf (getDefaults s)).length = (seqOf s).length := by
  simp [getDefaults, seqOf]

theorem seqOf_join (a b : Ast) :
    (seqOf (joinSeq a b)).length = (seqOf a).length + (seqOf b).length := by
  simp [joinSeq, seqOf]

/-- `_PyAST_arguments` as `_PyPegen_make_arguments` calls it never has more positional
defaults than positional parameters, which is `validate_arguments`'s check: the parser cannot
build what the validator refuses. Precondition, from the grammar's calls: at most one of
`slash_without_default` and `slash_with_default` is given. -/
def MakeArgumentsDefaultsFit : Prop :=
  ∀ (a b c d : Ast), (isNullA a = true ∨ isNullA b = true) →
    (seqOf (posdefaultsOf b d)).length ≤
      (seqOf (posonlyOf a b)).length + (seqOf (posargsOf c d)).length

theorem seqOf_seq (xs : List Ast) : seqOf (.seq xs) = xs := rfl

theorem makeArgumentsDefaultsFit_proven : MakeArgumentsDefaultsFit := by
  intro a b c d h
  unfold posdefaultsOf posonlyOf posargsOf
  cases ha : isNullA a <;> cases hb : isNullA b <;> cases hc : isNullA c <;>
    cases hd : isNullA d <;>
    simp [ha, hb, hc, hd, seqOf_getNames, seqOf_getDefaults, seqOf_join, seqOf_seq] <;>
    first
    | omega
    | (simp [ha, hb] at h)

/-- `NameDefaultPair`s, as `_PyPegen_name_default_pair` builds them: the parameter, then its
default (`NULL` for a keyword-only parameter without one). -/
def ndPairs (ps : List (Ast × Ast)) : List Ast := ps.map fun q => rec_ .PNameDefaultPair [q.1, q.2]

/-- A sequence argument that may be `NULL`. -/
def optSeqA : Option (List Ast) → Ast
  | none => .null
  | some xs => .seq xs

/-- A `names_with_default` argument that may be `NULL`. -/
def optPairsA : Option (List (Ast × Ast)) → Ast
  | none => .null
  | some ps => .seq (ndPairs ps)

/-- A `SlashWithDefault *` (`_PyPegen_slash_with_default`): plain names, then pairs. -/
def slashWithA : Option (List Ast × List (Ast × Ast)) → Ast
  | none => .null
  | some (pn, ps) => rec_ .PSlashWithDefault [.seq pn, .seq (ndPairs ps)]

/-- A `StarEtc *` (`_PyPegen_star_etc`): vararg, keyword-only pairs, kwarg. -/
def starEtcA : Option (Ast × Option (List (Ast × Ast)) × Ast) → Ast
  | none => .null
  | some (v, kw, k) => rec_ .PStarEtc [v, optPairsA kw, k]

/-- `_PyPegen_make_arguments`, `Parser/action_helpers.c:655-692` with `_make_posonlyargs`,
`_make_posargs`, `_make_posdefaults`, `_make_kwargs` (`:535-652`), `_get_names` and `_get_defaults`
(`:504-532`), for every combination of its five arguments being `NULL` or not: the
positional-only parameters are `slash_without_default`, else the plain names of
`slash_with_default` then the names of its pairs; the positional parameters are the plain names
then the names of `names_with_default`; the positional defaults are the defaults of the
`slash_with_default` pairs then those of `names_with_default`; vararg, the keyword-only names, their
defaults (`NULL` where absent) and kwarg come from `star_etc`, and are empty or `NULL` without it.
The `assert(0)` branch (plain names without `names_with_default`, `:577-582`) is included. -/
def MakeArgumentsExact : Prop :=
  ∀ (sn : Option (List Ast)) (sw : Option (List Ast × List (Ast × Ast))) (pl : Option (List Ast))
    (nd : Option (List (Ast × Ast))) (se : Option (Ast × Option (List (Ast × Ast)) × Ast)),
  makeArguments (optSeqA sn) (slashWithA sw) (optSeqA pl) (optPairsA nd) (starEtcA se) =
    .node .arguments_
      [.seq (match sn, sw with
          | some xs, _ => xs
          | none, some (pn, ps) => pn ++ ps.map Prod.fst
          | none, none => []),
       .seq (pl.getD [] ++ (nd.getD []).map Prod.fst),
       (match se with
          | some (v, _, _) => v
          | none => .null),
       .seq (match se with
          | some (_, some kw, _) => kw.map Prod.fst
          | _ => []),
       .seq (match se with
          | some (_, some kw, _) => kw.map Prod.snd
          | _ => []),
       (match se with
          | some (_, _, k) => k
          | none => .null),
       .seq ((match sw with
          | some (_, ps) => ps.map Prod.snd
          | none => []) ++ (nd.getD []).map Prod.snd)] none

theorem isNullA_rec (c : Ctor) (fs : List Ast) : isNullA (rec_ c fs) = false := rfl

theorem isNullA_null : isNullA .null = true := rfl

theorem isNullA_seq (xs : List Ast) : isNullA (.seq xs) = false := rfl

theorem recField_pair0 (c : Ctor) (a b : Ast) : recField (rec_ c [a, b]) 0 = a := rfl

theorem recField_pair1 (c : Ctor) (a b : Ast) : recField (rec_ c [a, b]) 1 = b := rfl

theorem ndPairs_names (ps : List (Ast × Ast)) :
    (ndPairs ps).map (fun p => recField p 0) = ps.map Prod.fst := by
  simp [ndPairs, recField_pair0]

theorem ndPairs_defaults (ps : List (Ast × Ast)) :
    (ndPairs ps).map (fun p => recField p 1) = ps.map Prod.snd := by
  simp [ndPairs, recField_pair1]

theorem posonly_exact (sn : Option (List Ast)) (sw : Option (List Ast × List (Ast × Ast))) :
    posonlyOf (optSeqA sn) (slashWithA sw) = .seq (match sn, sw with
      | some xs, _ => xs
      | none, some (pn, ps) => pn ++ ps.map Prod.fst
      | none, none => []) := by
  rcases sn with _ | sn <;> rcases sw with _ | ⟨pn, ps⟩ <;>
    simp only [posonlyOf, optSeqA, slashWithA, isNullA_rec, isNullA_null, isNullA_seq, joinSeq, getNames, seqOf, recField_pair0,
      recField_pair1, ndPairs_names, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte]

theorem posargs_exact (pl : Option (List Ast)) (nd : Option (List (Ast × Ast))) :
    posargsOf (optSeqA pl) (optPairsA nd) = .seq (pl.getD [] ++ (nd.getD []).map Prod.fst) := by
  rcases pl with _ | pl <;> rcases nd with _ | nd <;>
    simp only [posargsOf, optSeqA, optPairsA, isNullA, joinSeq, getNames, seqOf, ndPairs_names,
      Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte, Option.getD_none,
      Option.getD_some, List.map_nil, List.append_nil, List.nil_append]

theorem posdefaults_exact (sw : Option (List Ast × List (Ast × Ast))) (nd : Option (List (Ast × Ast))) :
    posdefaultsOf (slashWithA sw) (optPairsA nd) = .seq ((match sw with
      | some (_, ps) => ps.map Prod.snd
      | none => []) ++ (nd.getD []).map Prod.snd) := by
  rcases sw with _ | ⟨pn, ps⟩ <;> rcases nd with _ | nd <;>
    simp only [posdefaultsOf, slashWithA, optPairsA, isNullA_rec, isNullA_null, isNullA_seq, joinSeq, getDefaults, seqOf,
      recField_pair1, ndPairs_defaults, Bool.not_true, Bool.not_false, Bool.false_eq_true,
      Bool.and_true, Bool.and_false, Bool.true_and, Bool.false_and, ↓reduceIte, Option.getD_none,
      Option.getD_some, List.map_nil, List.append_nil, List.nil_append]

theorem kwonly_exact (se : Option (Ast × Option (List (Ast × Ast)) × Ast)) :
    getNames (recField (starEtcA se) 1) = .seq (match se with
      | some (_, some kw, _) => kw.map Prod.fst
      | _ => []) ∧
    getDefaults (recField (starEtcA se) 1) = .seq (match se with
      | some (_, some kw, _) => kw.map Prod.snd
      | _ => []) := by
  rcases se with _ | ⟨v, _ | kw, k⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨by simp only [getNames, starEtcA, optPairsA]; rw [show recField (rec_ .PStarEtc
        [v, .seq (ndPairs kw), k]) 1 = .seq (ndPairs kw) from rfl]; simp only [seqOf, ndPairs_names],
      by simp only [getDefaults, starEtcA, optPairsA]; rw [show recField (rec_ .PStarEtc
        [v, .seq (ndPairs kw), k]) 1 = .seq (ndPairs kw) from rfl]; simp only [seqOf, ndPairs_defaults]⟩

theorem vararg_exact (se : Option (Ast × Option (List (Ast × Ast)) × Ast)) :
    recField (starEtcA se) 0 = (match se with
      | some (v, _, _) => v
      | none => .null) ∧
    recField (starEtcA se) 2 = (match se with
      | some (_, _, k) => k
      | none => .null) := by
  rcases se with _ | ⟨v, kw, k⟩ <;> simp [starEtcA, recField, rec_]

theorem mkAst_arguments (a b d e g : List Ast) (c f : Ast) :
    mkAst .arguments_ [.seq a, .seq b, c, .seq d, .seq e, f, .seq g] =
      .node .arguments_ [.seq a, .seq b, c, .seq d, .seq e, f, .seq g] none := by
  cases c <;> cases f <;> rfl

theorem makeArgumentsExact_proven : MakeArgumentsExact := by
  intro sn sw pl nd se
  simp only [makeArguments]
  rw [posonly_exact, posargs_exact, posdefaults_exact, (kwonly_exact se).1, (kwonly_exact se).2,
    (vararg_exact se).1, (vararg_exact se).2, mkAst_arguments]

/-! ### String concatenation -/

theorem foldConsts_len (xs : List Ast) (acc : List Nat) (last : Ast) :
    (foldConsts xs acc last).2.2.length ≤ xs.length := by
  induction xs generalizing acc last with
  | nil => simp [foldConsts]
  | cons x xs ih =>
    unfold foldConsts
    split
    · have := ih (acc ++ constStr x) x
      simp only [List.length_cons]
      omega
    · simp

/-- `_build_concatenated_str`: "Drop all empty contanst strings". What the folding loop
returns holds no constant empty string, for any input list. -/
def ConcatNormalForm : Prop :=
  ∀ (f : Nat) (xs : List Ast), xs.length < f →
    (foldLoop f xs).all (fun e => !isEmptyStrConst e) = true

theorem isEmptyStrConst_mkAt (s : List Nat) (k : Ast) (l : Loc) (h : s.isEmpty = false) :
    isEmptyStrConst (mkAt .Constant [.const (.str s), k] l) = false := by
  cases s with
  | nil => simp at h
  | cons x xs => rfl

theorem concatNormalForm_proven : ConcatNormalForm := by
  intro f
  induction f with
  | zero => intro xs h; simp at h
  | succ f ih =>
    intro xs h
    cases xs with
    | nil => simp [foldLoop]
    | cons e rest =>
      simp only [List.length_cons] at h
      have hlen := foldConsts_len rest (constStr e) e
      rw [foldLoop]
      split
      · dsimp only
        split
        · exact ih _ (by omega)
        · rename_i hs
          simp only [List.all_cons, Bool.and_eq_true]
          refine ⟨?_, ih _ (by omega)⟩
          have hs' : (foldConsts rest (constStr e) e).1.isEmpty = false := by simpa using hs
          simp [isEmptyStrConst_mkAt _ _ _ hs']
      · split
        · exact ih _ (by omega)
        · rename_i hemp
          simp only [List.all_cons, Bool.and_eq_true]
          exact ⟨by simpa using hemp, ih _ (by omega)⟩

/-! ### Identifiers -/

/-- `_PyPegen_new_identifier` refuses exactly the spellings the keyword table cannot have
made names, after NFKC: no `Name` in a tree is called `None`, `True` or `False`. -/
def IdentifierNeverConstant : Prop :=
  ∀ (bytes : List Nat) (p : PS),
    match (newIdentifier bytes p).1 with
    | .ident s => s ≠ [78, 111, 110, 101] ∧ s ≠ [84, 114, 117, 101]
        ∧ s ≠ [70, 97, 108, 115, 101]
    | _ => True

/-! ### Numbers -/

/-- Integer literals: decimal digits read as their value, whatever the digit-group
underscores, for literals not starting with `0`. -/
def DecimalValue : Prop :=
  ∀ ds : List Nat, ds ≠ [] → (∀ d ∈ ds, 49 ≤ d ∧ d ≤ 57) → ds.length ≤ 19 →
    match parseNumber ds with
    | .ok (.int v) => v = (ds.foldl (fun a d => a * 10 + (d - 48)) 0 : Nat)
    | _ => False

/-! ### Other action helpers -/

theorem dropSpace_tail (r : List Nat) (nl : Bool) :
    ∃ pre, r = pre ++ (dropTrailingSpace r nl).1 ∧ ∀ c ∈ pre, isUnicodeSpace c = true := by
  induction r generalizing nl with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons c t ih =>
    unfold dropTrailingSpace
    split
    · rename_i hc
      obtain ⟨pre, e, hp⟩ := ih (nl || c == 13 || c == 10)
      refine ⟨c :: pre, by simpa using e, fun x hx => ?_⟩
      rcases List.mem_cons.1 hx with q | q
      · exact q ▸ hc
      · exact hp x q
    · exact ⟨[], rfl, by simp⟩

theorem stripTail_tail (f : Nat) (r : List Nat) :
    ∃ pre, r = pre ++ stripDebugTail f r ∧
      ∀ c ∈ pre, isUnicodeSpace c = true ∨ c = 92 := by
  induction f generalizing r with
  | zero => exact ⟨[], rfl, by simp⟩
  | succ f ih =>
    unfold stripDebugTail
    split
    · exact ⟨[], rfl, by simp⟩
    · obtain ⟨pre, e, hp⟩ := dropSpace_tail r false
      have hsp : ∀ c ∈ pre, isUnicodeSpace c = true ∨ c = 92 := fun c hc => Or.inl (hp c hc)
      split
      · rename_i t hq
        rw [hq] at e
        simp only at e
        obtain ⟨pre2, e2, hp2⟩ := ih t
        refine ⟨pre ++ 92 :: pre2, ?_, fun c hc => ?_⟩
        · rw [e]
          simp only [List.append_assoc, List.cons_append]
          rw [← e2]
        · rcases List.mem_append.1 hc with q | q
          · exact hsp c q
          · rcases List.mem_cons.1 q with q | q
            · exact Or.inr q
            · exact hp2 c q
      · rw [‹dropTrailingSpace r false = _›] at e
        exact ⟨pre, e, hsp⟩

theorem dropSpace_all (pre r : List Nat) (nl : Bool) (hp : ∀ c ∈ pre, isUnicodeSpace c = true)
    (hr : isUnicodeSpace 61 = false) :
    (dropTrailingSpace (pre ++ 61 :: r) nl).1 = 61 :: r := by
  induction pre generalizing nl with
  | nil =>
    simp only [List.nil_append, dropTrailingSpace, hr]
    rfl
  | cons c t ih =>
    simp only [List.cons_append, dropTrailingSpace]
    rw [if_pos (hp c (List.mem_cons_self ..))]
    exact ih _ fun x hx => hp x (List.mem_cons_of_mem _ hx)

/-- `_strip_interpolation_debug_expr`, from its comments: "Discard whitespace ... after the debug
'=' but preserve whitespace before it", and "Preserve unexpected metadata instead of dropping
source text". Whitespace after the `=` goes, whatever comes before it, and in no case is anything
removed but a final `=` and what follows it, which is whitespace and continuation backslashes. -/
def StripInterpolation : Prop :=
  (∀ r tail : List Nat, (∀ c ∈ tail, isUnicodeSpace c = true) →
    stripInterpolationDebugExpr (r ++ 61 :: tail) = r) ∧
  (∀ s : List Nat, stripInterpolationDebugExpr s = s ∨
    ∃ tail, s = stripInterpolationDebugExpr s ++ 61 :: tail ∧
      ∀ c ∈ tail, isUnicodeSpace c = true ∨ c = 92)

theorem strip_step (f : Nat) (r t : List Nat) (nl : Bool) (hne : r ≠ [])
    (h : dropTrailingSpace r false = (61 :: t, nl)) : stripDebugTail (f + 1) r = 61 :: t := by
  cases r with
  | nil => exact (hne rfl).elim
  | cons c cs =>
    show (match dropTrailingSpace (c :: cs) false with
      | (92 :: t, true) => stripDebugTail f t
      | (r', _) => r') = _
    rw [h]
    rfl

theorem stripInterpolation_proven : StripInterpolation := by
  have h61 : isUnicodeSpace 61 = false := by decide
  constructor
  · intro r tail ht
    unfold stripInterpolationDebugExpr
    have er : (r ++ 61 :: tail).reverse = tail.reverse ++ 61 :: r.reverse := by simp
    have hd := dropSpace_all tail.reverse r.reverse false (fun c hc => ht c (by simpa using hc)) h61
    have hne : tail.reverse ++ 61 :: r.reverse ≠ [] := by simp
    have hn : (r ++ 61 :: tail).length = (r.length + tail.length) + 1 := by
      simp
      omega
    generalize hq : dropTrailingSpace (tail.reverse ++ 61 :: r.reverse) false = q at hd
    obtain ⟨r', nl⟩ := q
    simp only at hd
    subst hd
    rw [hn, er, strip_step _ _ _ nl hne hq]
    simp
  · intro s
    unfold stripInterpolationDebugExpr
    obtain ⟨pre, e, hp⟩ := stripTail_tail s.length s.reverse
    generalize hs : stripDebugTail s.length s.reverse = out at e
    match out, e with
    | 61 :: t, e =>
      refine Or.inr ⟨pre.reverse, ?_, fun c hc => hp c (by simpa using hc)⟩
      have : s = (pre ++ 61 :: t).reverse := by rw [← e]; simp
      rw [this]
      simp
    | [], _ => exact Or.inl rfl
    | c :: t, _ =>
      by_cases hc : c = 61
      · subst hc
        rename_i e
        refine Or.inr ⟨pre.reverse, ?_, fun c hc => hp c (by simpa using hc)⟩
        have : s = (pre ++ 61 :: t).reverse := by rw [← e]; simp
        rw [this]
        simp
      · left
        split
        · rename_i h
          cases h
          exact (hc rfl).elim
        · rfl

/-- A whitespace run holding a line end: what may follow an explicit line continuation. -/
def NlSpace (w : List Nat) : Prop := (∀ c ∈ w, isUnicodeSpace c = true) ∧ (10 ∈ w ∨ 13 ∈ w)

theorem dropSpace_gen (pre rest : List Nat) (c : Nat) (nl : Bool)
    (hp : ∀ x ∈ pre, isUnicodeSpace x = true) (hc : isUnicodeSpace c = false) :
    dropTrailingSpace (pre ++ c :: rest) nl =
      (c :: rest, nl || pre.any (fun x => x == 13 || x == 10)) := by
  induction pre generalizing nl with
  | nil => simp [dropTrailingSpace, hc]
  | cons x t ih =>
    simp only [List.cons_append, dropTrailingSpace, hp x (List.mem_cons_self ..), ↓reduceIte]
    rw [ih _ fun y hy => hp y (List.mem_cons_of_mem _ hy)]
    simp [Bool.or_assoc]

theorem nlSpace_any {w : List Nat} (h : NlSpace w) :
    w.reverse.any (fun x => x == 13 || x == 10) = true := by
  rcases h.2 with h10 | h13
  · exact List.any_eq_true.2 ⟨10, List.mem_reverse.2 h10, by decide⟩
  · exact List.any_eq_true.2 ⟨13, List.mem_reverse.2 h13, by decide⟩

/-- The outer loop of `_strip_interpolation_debug_expr` on reversed text: each continuation (a
whitespace run with a line end, then a backslash) goes, then the inner loop reaches the `=`. -/
theorem strip_conts (base t : List Nat) (nl : Bool) (hne : base ≠ [])
    (hb : dropTrailingSpace base false = (61 :: t, nl)) :
    ∀ (L : List (List Nat)) (f : Nat), (∀ w ∈ L, NlSpace w) → L.length < f →
      stripDebugTail f (L.flatMap (fun w => w.reverse ++ [92]) ++ base) = 61 :: t := by
  intro L
  induction L with
  | nil =>
    intro f _ hf
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp at hf; omega⟩
    exact strip_step f base t nl hne hb
  | cons w L ih =>
    intro f hw hf
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp at hf; omega⟩
    have hsp : ∀ x ∈ w.reverse, isUnicodeSpace x = true :=
      fun x hx => (hw w (List.mem_cons_self ..)).1 x (List.mem_reverse.1 hx)
    have hd := dropSpace_gen w.reverse (L.flatMap (fun w => w.reverse ++ [92]) ++ base) 92 false hsp
      (by decide)
    rw [nlSpace_any (hw w (List.mem_cons_self ..))] at hd
    simp only [List.flatMap_cons, List.append_assoc, List.cons_append, List.nil_append]
    generalize hX : w.reverse ++ 92 :: (L.flatMap (fun w => w.reverse ++ [92]) ++ base) = X at hd
    have hX0 : X ≠ [] := by
      rw [← hX]
      simp
    match X, hX0, hd with
    | c :: cs, _, hd =>
      show (match dropTrailingSpace (c :: cs) false with
        | (92 :: t, true) => stripDebugTail f t
        | (r', _) => r') = _
      rw [hd]
      exact ih f (fun v hv => hw v (List.mem_cons_of_mem _ hv)) (by simp at hf; omega)

theorem length_flatMap_ge (segs : List (List Nat)) :
    segs.length ≤ (segs.flatMap (fun w => 92 :: w)).length := by
  induction segs with
  | nil => simp
  | cons w ws ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

theorem reverse_conts (segs : List (List Nat)) :
    (segs.flatMap (fun w => 92 :: w)).reverse =
      segs.reverse.flatMap (fun w => w.reverse ++ [92]) := by
  induction segs with
  | nil => rfl
  | cons w ws ih => simp [ih, List.flatMap_append]

/-- The continuation half of `_strip_interpolation_debug_expr`'s comment: "Discard whitespace and
explicit line continuations after the debug '='" (`Parser/action_helpers.c:1548-1549`). After the
`=` come whitespace and then any number of continuations, each a backslash followed by whitespace
holding a line end; all of it goes with the `=`, and what is before the `=` is kept. -/
def StripContinuations : Prop := ∀ (r ws0 : List Nat) (segs : List (List Nat)),
  (∀ c ∈ ws0, isUnicodeSpace c = true) → (∀ w ∈ segs, NlSpace w) →
  stripInterpolationDebugExpr (r ++ 61 :: (ws0 ++ segs.flatMap (fun w => 92 :: w))) = r

theorem stripContinuations_proven : StripContinuations := by
  intro r ws0 segs h0 hs
  unfold stripInterpolationDebugExpr
  have er : (r ++ 61 :: (ws0 ++ segs.flatMap (fun w => 92 :: w))).reverse =
      segs.reverse.flatMap (fun w => w.reverse ++ [92]) ++ (ws0.reverse ++ 61 :: r.reverse) := by
    simp [List.reverse_append, reverse_conts]
  have hb := dropSpace_gen ws0.reverse r.reverse 61 false
    (fun x hx => h0 x (List.mem_reverse.1 hx)) (by decide)
  have hne : ws0.reverse ++ 61 :: r.reverse ≠ [] := by simp
  have hl := length_flatMap_ge segs
  have hlen : segs.reverse.length <
      (r ++ 61 :: (ws0 ++ segs.flatMap (fun w => 92 :: w))).length := by
    simp only [List.length_reverse, List.length_append, List.length_cons]
    omega
  rw [er, strip_conts _ r.reverse _ hne hb _ _ (fun w hw => hs w (List.mem_reverse.1 hw)) hlen]
  simp

/-- `_PyPegen_register_stmts`, `Parser/action_helpers.c:2116-2134`: the statements come back
unchanged in every case. In the first pass the parser is untouched (`:2118-2120`), and so it is for
an empty sequence (`:2121-2124`). In the second pass `last_stmt_location` takes the last
statement's position, unless the one recorded is on a later line (`:2126-2128`), in which case it
is kept. `_PyPegen_set_syntax_error_metadata` (`Parser/pegen.c:921-925`) reads it into the
`SyntaxError`'s `_metadata`; the end positions it also stores have no reader and are not modelled. -/
def RegisterStmts : Prop := ∀ (a : Ast) (xs : List Ast) (c : Ctor) (fs : List Ast) (loc : Loc) (p : PS),
  (p.callInvalidRules = false → registerStmts a p = (a, p)) ∧
  registerStmts (.seq []) p = (.seq [], p) ∧
  (p.callInvalidRules = true → p.lastStmt.1 > loc.lineno →
    registerStmts (.seq (xs ++ [.node c fs (some loc)])) p = (.seq (xs ++ [.node c fs (some loc)]), p)) ∧
  (p.callInvalidRules = true → p.lastStmt.1 ≤ loc.lineno →
    registerStmts (.seq (xs ++ [.node c fs (some loc)])) p =
      (.seq (xs ++ [.node c fs (some loc)]), { p with lastStmt := (loc.lineno, loc.colOffset) }))

theorem registerStmts_proven : RegisterStmts := by
  intro a xs c fs loc p
  refine ⟨fun h => ?_, ?_, fun h1 h2 => ?_, fun h1 h2 => ?_⟩
  · simp [registerStmts, h, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      pure, StateT.pure]
  · cases h : p.callInvalidRules <;>
      simp [registerStmts, h, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
        pure, StateT.pure, seqOf]
  · simp [registerStmts, h1, h2, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      pure, StateT.pure, seqOf, locOf]
  · have : ¬ p.lastStmt.1 > loc.lineno := by omega
    simp [registerStmts, h1, this, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      pure, StateT.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
      MonadState.modifyGet, seqOf, locOf]

end PyLean.PyGrammar.Peg
