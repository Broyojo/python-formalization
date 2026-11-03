import PyLean.TextLibs.EmailEw

/-!
`get_encoded_word` on well-formed RFC 2047 words, the `=XX` re-split of :1093-1099 included,
with its defects; and `get_unstructured` on a word followed by an encoded word, with and without
whitespace between them (Lib/email/_header_value_parser.py, CPython 3.15.2).
-/

namespace PyLean.TextLibs.Email

open PyLean.UnicodeObj

/-- `=?cs?e?txt?=`. -/
def ewWord (cs : Str) (e : Nat) (txt : Str) : Str :=
  [61, 63] ++ cs ++ [63, e, 63] ++ txt ++ [63, 61]

/-- The text of an encoded word starts with an `=XX` escape or not with `=`: the shapes a
Q-encoded or B-encoded text has. -/
def TxtStart (txt : Str) : Prop :=
  txt.head? ≠ some 61 ∨ ∃ a b t', txt = 61 :: a :: b :: t' ∧ isHexDigit a = true ∧ isHexDigit b = true

/-- `get_encoded_word` on `=?cs?e?txt?=` followed by anything, where `cs` and `txt` hold no `?`,
`e` is not `?` or `=`, and `txt` starts with an `=XX` escape or not with `=`: it hands
`_ew.decode` exactly the word, also when the first `?=` it finds is the `?` before an `=XX`
escape (the re-split of :1093-1099), and returns the rest of the value. When the word decodes,
the `EncodedWord`'s `str()` is the decoded text and its defects are, in order, "whitespace
inside encoded word" when the token holds two words (:1100-1102), `_ew.decode`'s defects
(:1112), and "missing trailing whitespace after encoded-word" when the rest does not start
with a space or tab (:1124-1126). When `_ew.decode` raises `ValueError`/`KeyError` it raises
`_InvalidEwError("encoded word format invalid: '<value>'")` (:1107-1109); another exception
propagates. -/
def EncodedWordSpec : Prop :=
  ∀ (cfg : Cfg) (cs txt y : Str) (e : Nat) (ty : String),
    63 ∉ cs → 63 ∉ txt → e ≠ 63 → e ≠ 61 → TxtStart txt →
    match cfg.dec (ewWord cs e txt) with
    | .caught => getEncodedWord cfg (ewWord cs e txt ++ y) ty =
        .error (.invalidEw (S "encoded word format invalid: '" ++ (ewWord cs e txt ++ y) ++ S "'"))
    | .raise c m => getEncodedWord cfg (ewWord cs e txt ++ y) ty = .error (.decRaise c m)
    | .ok t _ _ ds => ∃ ew, getEncodedWord cfg (ewWord cs e txt ++ y) ty = .ok (ew, y) ∧
        ew.str = t ∧ ew.ty = "encoded-word" ∧ tokClass ew = "EncodedWord" ∧
        ew.ds = (if twoWords (cs ++ [63, e, 63] ++ txt) then
            [invalidHeader (S "whitespace inside encoded word")] else []) ++ ds ++
          (if headIs (fun c => !isWsp c) y then
            [invalidHeader (S "missing trailing whitespace after encoded-word")] else [])

/-! ## `split1` on a two-character separator -/

theorem split1_pair {x y : Nat} (hxy : x ≠ y) {a : Str} (h : ¬ Occurs a [x, y]) (z : Str) :
    split1 (a ++ x :: y :: z) [x, y] = (a, some z) := by
  induction a with
  | nil => simp [split1, List.isPrefixOf]
  | cons c a ih =>
    have h' : ¬ Occurs a [x, y] := fun ho => h (occurs_append_left [c] ho)
    have hnp : [x, y].isPrefixOf (c :: (a ++ x :: y :: z)) = false := by
      cases a with
      | nil =>
        simp only [List.isPrefixOf, List.nil_append, Bool.and_eq_false_imp, beq_iff_eq]
        intro _ h2; exact absurd h2.symm hxy
      | cons d a' =>
        by_cases hcd : c = x ∧ d = y
        · exfalso; obtain ⟨rfl, rfl⟩ := hcd; exact h ⟨[], a', by simp⟩
        · simp only [List.isPrefixOf, List.cons_append, Bool.and_eq_false_imp, beq_iff_eq]
          intro h1 h2
          exact (hcd ⟨h1.symm, h2.symm⟩).elim
    rw [List.cons_append, split1, if_neg (by simp [hnp])]
    simp [ih h']

/-- No `x` at all, no `[x, y]`. -/
theorem not_occurs_of_not_mem {x y : Nat} {s : Str} (h : x ∉ s) : ¬ Occurs s [x, y] := by
  rintro ⟨p, q, rfl⟩; simp at h

theorem not_occurs_cons {x y c : Nat} {s : Str} (h : ¬ Occurs s [x, y])
    (hc : c ≠ x ∨ s.head? ≠ some y) : ¬ Occurs (c :: s) [x, y] := by
  rintro ⟨p, q, hpq⟩
  cases p with
  | nil =>
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at hpq
    obtain ⟨rfl, rfl⟩ := hpq
    rcases hc with hc | hc
    · exact hc rfl
    · simp at hc
  | cons d p' =>
    simp only [List.cons_append, List.cons.injEq] at hpq
    exact h ⟨p', q, by simpa using hpq.2⟩

theorem not_occurs_append {x y : Nat} {a s : Str} (ha : x ∉ a) (h : ¬ Occurs s [x, y]) :
    ¬ Occurs (a ++ s) [x, y] := by
  induction a with
  | nil => simpa using h
  | cons c a ih =>
    simp only [List.mem_cons, not_or] at ha
    exact not_occurs_cons (ih ha.2) (.inl (Ne.symm ha.1))

/-! ## The re-split -/

theorem count_zero {s : Str} {x : Nat} (h : x ∉ s) : s.count x = 0 := List.count_eq_zero.mpr h

theorem getEncodedWord_eq {cfg : Cfg} {cs txt : Str} {e : Nat} (y : Str) (ty : String)
    (hcs : 63 ∉ cs) (htxt : 63 ∉ txt) (he63 : e ≠ 63) (he61 : e ≠ 61) (hs : TxtStart txt) :
    getEncodedWord cfg (ewWord cs e txt ++ y) ty =
      match cfg.dec (ewWord cs e txt) with
      | .caught => .error (.invalidEw (S "encoded word format invalid: '" ++
          (ewWord cs e txt ++ y) ++ S "'"))
      | .raise c m => .error (.decRaise c m)
      | .ok text charset lang dds =>
        ewBuild ty (ewWord cs e txt ++ y) (cs ++ [63, e, 63] ++ txt) y text charset lang dds := by
  have hst : startsWith (ewWord cs e txt ++ y) (S "=?") = true := by
    simp [startsWith, ewWord, S]
  have hS : S "?=" = [63, 61] := rfl
  unfold getEncodedWord
  simp only [hst, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hS]
  rcases hs with hh | ⟨a, b, t', rfl, ha, hb⟩
  · -- the first `?=` closes the word
    have hno : ¬ Occurs (cs ++ [63, e, 63] ++ txt) [63, 61] := by
      have h1 : ¬ Occurs (63 :: txt) [63, 61] :=
        not_occurs_cons (not_occurs_of_not_mem htxt) (.inr hh)
      have h2 : ¬ Occurs (e :: 63 :: txt) [63, 61] := not_occurs_cons h1 (.inl he63)
      have h3 : ¬ Occurs (63 :: e :: 63 :: txt) [63, 61] :=
        not_occurs_cons h2 (.inr (by simpa using he61))
      simpa using not_occurs_append hcs h3
    have hv2 : (ewWord cs e txt ++ y).drop 2 = cs ++ [63, e, 63] ++ txt ++ 63 :: 61 :: y := by
      simp [ewWord]
    rw [hv2, split1_pair (x := 63) (y := 61) (by decide) hno y]
    have hne : ((cs ++ [63, e, 63] ++ txt) == cs ++ [63, e, 63] ++ txt ++ 63 :: 61 :: y) =
        false := by
      simp only [beq_eq_false_iff_ne]; intro h; have := congrArg List.length h; simp at this
    simp only [hne, Bool.false_eq_true, ↓reduceIte, Option.getD_some]
    have hcount : (cs ++ [63, e, 63] ++ txt).count 63 = 2 := by
      simp [List.count_append, List.count_cons, count_zero hcs, count_zero htxt, he63]
    have hfix : ewHexFix (cs ++ [63, e, 63] ++ txt) y = (cs ++ [63, e, 63] ++ txt, y) := by
      unfold ewHexFix; rw [hcount]; simp
    rw [hfix]
    simp only
    rw [show S "=?" ++ (cs ++ [63, e, 63] ++ txt) ++ [63, 61] = ewWord cs e txt by
      simp [ewWord, S]]
    rfl
  · -- the first `?=` is the `?` before the `=XX` escape: the token is re-split
    have hno : ¬ Occurs (cs ++ [63, e]) [63, 61] := by
      have h2 : ¬ Occurs [e] [63, 61] :=
        not_occurs_cons (by rintro ⟨p, q, hpq⟩; cases p <;> simp at hpq) (.inl he63)
      have h3 : ¬ Occurs [63, e] [63, 61] := not_occurs_cons h2 (.inr (by simpa using he61))
      exact not_occurs_append hcs h3
    have hr : 63 ∉ a :: b :: t' := fun h => htxt (List.mem_cons_of_mem _ h)
    have hv2 : (ewWord cs e (61 :: a :: b :: t') ++ y).drop 2 =
        cs ++ [63, e] ++ 63 :: 61 :: ((a :: b :: t') ++ 63 :: 61 :: y) := by
      simp [ewWord]
    rw [hv2, split1_pair (x := 63) (y := 61) (by decide) hno]
    have hne : ((cs ++ [63, e]) == cs ++ [63, e] ++ 63 :: 61 :: ((a :: b :: t') ++ 63 :: 61 :: y)) =
        false := by
      simp only [beq_eq_false_iff_ne]; intro h; have := congrArg List.length h; simp at this
    simp only [hne, Bool.false_eq_true, ↓reduceIte, Option.getD_some]
    have hcount : (cs ++ [63, e]).count 63 = 1 := by
      simp [List.count_append, List.count_cons, count_zero hcs, he63]
    have hfix : ewHexFix (cs ++ [63, e]) ((a :: b :: t') ++ 63 :: 61 :: y) =
        (cs ++ [63, e, 63] ++ 61 :: a :: b :: t', y) := by
      unfold ewHexFix
      rw [hcount, hS, split1_pair (x := 63) (y := 61) (by decide) (not_occurs_of_not_mem hr) y]
      simp [ha, hb]
    rw [hfix]
    simp only
    rw [show S "=?" ++ (cs ++ [63, e, 63] ++ 61 :: a :: b :: t') ++ [63, 61] =
      ewWord cs e (61 :: a :: b :: t') by simp [ewWord, S]]
    rfl

theorem encodedWordSpec_proven : EncodedWordSpec := by
  intro cfg cs txt y e ty hcs htxt he63 he61 hs
  have heq := getEncodedWord_eq (cfg := cfg) y ty hcs htxt he63 he61 hs
  split
  · rename_i h; rw [heq, h]
  · rename_i c m h; rw [heq, h]
  · rename_i t chs l ds h
    rw [heq, h]
    obtain ⟨r, hr⟩ := ewTextLoop_ok ty (t.length + 1) t [] (Nat.lt_succ_self _)
    refine ⟨.node .encodedWord "encoded-word" r
      ((if twoWords (cs ++ [63, e, 63] ++ txt) then
          [invalidHeader (S "whitespace inside encoded word")] else []) ++ ds ++
        (if headIs (fun c => !isWsp c) y then
          [invalidHeader (S "missing trailing whitespace after encoded-word")] else []))
      [("cte", .s (ewWord cs e txt ++ y)), ("charset", .s chs), ("lang", .s l)],
      ?_, ?_, rfl, rfl, rfl⟩
    · simp [ewBuild, hr]; rfl
    · have := ewTextLoop_strs ty _ _ _ _ hr
      simp [strs] at this
      simp [Tok.str, this]

/-! ## A word, then an encoded word -/

/-- For every word `p` (no space or tab, no `=?`) followed by an encoded word `=?cs?e?txt?=` that
`_ew.decode` decodes (`e` one of `qQbB`, no `?`, space, tab or newline in `cs` and `txt`, so that
`rfc2047_matcher` sees it), with or without whitespace `sep` between them, `get_unstructured`
returns `p`'s text, `sep`, and the decoded text (`str()`), and
* with no whitespace: splits the word at the `=?` (:1188-1189), and records "missing whitespace
  before encoded word" (:1170-1174): elements `ValueTerminal`, `EncodedWord`;
* with whitespace: keeps it as an ordinary `WhiteSpaceTerminal`, since the token before it is not
  an encoded word (:1175-1178), and records nothing: elements `ValueTerminal`,
  `WhiteSpaceTerminal`, `EncodedWord`. -/
def UnstructuredWordThenEw : Prop :=
  ∀ (cfg : Cfg) (n : Nat) (p sep cs txt : Str) (e : Nat) (t chs l : Str) (ds : List Defect),
    p ≠ [] → (∀ x ∈ p, isWsp x = false) → ¬ Occurs p [61, 63] →
    63 ∉ cs → 63 ∉ txt → 10 ∉ txt → (∀ x ∈ cs ++ txt, isWsp x = false) → mem "qQbB" e = true →
    TxtStart txt → cfg.dec (ewWord cs e txt) = .ok t chs l ds →
    (sep = [] ∨ GoodSep sep) → (p ++ sep ++ ewWord cs e txt).length < n →
    ∃ u, getUnstructured cfg n (p ++ sep ++ ewWord cs e txt) = .ok u ∧
      u.str = p ++ sep ++ t ∧
      (sep = [] → u.ds = [invalidHeader (S "missing whitespace before encoded word")] ∧
        u.kids.map tokClass = ["ValueTerminal", "EncodedWord"]) ∧
      (sep ≠ [] → u.ds = [] ∧
        u.kids.map tokClass = ["ValueTerminal", "WhiteSpaceTerminal", "EncodedWord"])

theorem qeBeforeNl_tail : ∀ {txt : Str}, 63 ∉ txt → 10 ∉ txt → ∀ z,
    qeBeforeNl (txt ++ 63 :: 61 :: z) = true
  | [], _, _, z => by simp [qeBeforeNl]
  | c :: t, h1, h2, z => by
    simp only [List.mem_cons, not_or] at h1 h2
    have ih := qeBeforeNl_tail h1.2 h2.2 z
    rw [List.cons_append]
    unfold qeBeforeNl
    split
    · rename_i heq; simp at heq; exact absurd heq.1 (Ne.symm h1.1)
    · rename_i heq; simp at heq; exact absurd heq.1 (Ne.symm h2.1)
    · rename_i heq; simp at heq; obtain ⟨_, rfl⟩ := heq; exact ih
    · rename_i heq; simp at heq

theorem rfcMatchAt_ew {cs txt : Str} {e : Nat} (hcs : 63 ∉ cs) (htxt : 63 ∉ txt) (hn : 10 ∉ txt)
    (he : mem "qQbB" e = true) (z : Str) : rfcMatchAt (ewWord cs e txt ++ z) = true := by
  have hall : ∀ a ∈ cs, (a != 63) = true := fun a ha => by
    simp only [bne_iff_ne, ne_eq]; rintro rfl; exact hcs ha
  have hv : ewWord cs e txt ++ z = 61 :: 63 :: (cs ++ 63 :: e :: 63 :: (txt ++ 63 :: 61 :: z)) := by
    simp [ewWord]
  rw [hv]
  unfold rfcMatchAt
  simp only
  rw [dropWhile_append_all _ hall]
  simp only [List.dropWhile_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, he,
    Bool.true_and]
  exact qeBeforeNl_tail htxt hn z

theorem rfcSearch_append_left {s : Str} (h : rfcSearch s = true) : ∀ x, rfcSearch (x ++ s) = true
  | [] => h
  | c :: x => by
    rw [List.cons_append, rfcSearch, rfcSearch_append_left h x]; simp

theorem takeWhile_all {p : Nat → Bool} : ∀ {A : Str}, (∀ a ∈ A, p a = true) → A.takeWhile p = A
  | [], _ => rfl
  | a :: A, h => by
    simp only [List.takeWhile_cons, h a (by simp), ↓reduceIte,
      takeWhile_all (A := A) (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem dropWhile_all {p : Nat → Bool} : ∀ {A : Str}, (∀ a ∈ A, p a = true) → A.dropWhile p = []
  | [], _ => rfl
  | a :: A, h => by
    simp only [List.dropWhile_cons, h a (by simp), ↓reduceIte]
    exact dropWhile_all (A := A) (fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem startsWith_word {p z : Str} (hp : p ≠ []) (hno : ¬ Occurs p [61, 63])
    (hz : z.head? ≠ some 63) : startsWith (p ++ z) (S "=?") = false := by
  obtain ⟨c, p', rfl⟩ := List.exists_cons_of_ne_nil hp
  cases hs : startsWith (c :: p' ++ z) (S "=?") with
  | false => rfl
  | true =>
    exfalso
    simp only [startsWith, S, List.isPrefixOf_iff_prefix] at hs
    obtain ⟨u, hu⟩ := hs
    cases p' with
    | nil =>
      cases z with
      | nil => simp at hu
      | cons d z' => simp at hu; exact hz (by simp [hu.2.1.symm])
    | cons d p'' =>
      simp at hu
      exact hno ⟨[], p'', by simp [hu.1.symm, hu.2.1.symm]⟩

theorem getFws_spaces {sep w : Str} (hs : ∀ x ∈ sep, isSpace x = true) (hw : w.head? = some 61) :
    getFws (sep ++ w) = (WT sep "fws", w) := by
  obtain ⟨w', rfl⟩ : ∃ w', w = 61 :: w' := by
    cases w with
    | nil => simp at hw
    | cons a w' => simp at hw; exact ⟨w', by rw [hw]⟩
  have h61 : isSpace 61 = false := by decide
  apply Prod.ext
  · rw [getFws_fst, takeWhile_append_all _ hs]; simp [List.takeWhile_cons, h61]
  · rw [getFws_snd, dropWhile_append_all _ hs]; simp [List.dropWhile_cons, h61]

theorem ewAttempt_word {cfg : Cfg} {cs txt : Str} {e : Nat} {t chs l : Str} {ds : List Defect}
    (hcs : 63 ∉ cs) (htxt : 63 ∉ txt) (he : mem "qQbB" e = true) (hs : TxtStart txt)
    (hdec : cfg.dec (ewWord cs e txt) = .ok t chs l ds) :
    ∃ ew, ewAttempt cfg (ewWord cs e txt) = .ok (some (ew, []), true) ∧ ew.str = t ∧
      tokClass ew = "EncodedWord" := by
  have he63 : e ≠ 63 := by rintro rfl; revert he; decide
  have he61 : e ≠ 61 := by rintro rfl; revert he; decide
  have hspec := encodedWordSpec_proven cfg cs txt [] e "utext" hcs htxt he63 he61 hs
  rw [hdec] at hspec
  obtain ⟨ew, h1, h2, -, h3, -⟩ := hspec
  rw [List.append_nil] at h1
  have hst : startsWith (ewWord cs e txt) (S "=?") = true := by simp [startsWith, ewWord, S]
  exact ⟨ew, by simp [ewAttempt, hst, h1]; rfl, h2, h3⟩

theorem unstructuredWordThenEw_proven : UnstructuredWordThenEw := by
  intro cfg n p sep cs txt e t chs l ds hp hpw hno hcs htxt hn hcw he hs hdec hsep hlen
  obtain ⟨ew, hew, hstr, hcls⟩ := ewAttempt_word hcs htxt he hs hdec
  have hW : (ewWord cs e txt).head? = some 61 := by simp [ewWord]
  have hWlen : 6 ≤ (ewWord cs e txt).length := by simp [ewWord]; omega
  obtain ⟨dsv, hvt⟩ := validateXtext_term .val p "utext" []
  have hvt' : validateXtext (VT p "utext") = .term .val p "utext" dsv := hvt
  obtain ⟨c, p', rfl⟩ := List.exists_cons_of_ne_nil hp
  have hc : isWsp c = false := hpw c (by simp)
  have hpre : ∀ x ∈ c :: p', (fun x => !isWsp x) x = true := fun x hx => by simp [hpw x hx]
  have hWnw : ∀ x ∈ ewWord cs e txt, (fun x => !isWsp x) x = true := by
    intro x hx
    cases hxw : isWsp x
    · simp [hxw]
    · exfalso
      have hx' : x = 32 ∨ x = 9 := by simpa [isWsp] using hxw
      have h61 : x ≠ 61 := by rcases hx' with rfl | rfl <;> decide
      have h63 : x ≠ 63 := by rcases hx' with rfl | rfl <;> decide
      have hxe : x ≠ e := by rintro rfl; rcases hx' with rfl | rfl <;> revert he <;> decide
      have hct : x ∉ cs ++ txt := fun hm => by rw [hcw x hm] at hxw; cases hxw
      simp only [List.mem_append, not_or] at hct
      simp only [ewWord, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with ((((h | h) | h) | (h | h | h)) | h) | (h | h)
      all_goals first | exact h61 h | exact h63 h | exact hxe h | exact hct.1 h | exact hct.2 h
  rcases hsep with rfl | ⟨⟨d, sep', hsd, hd⟩, hsall⟩
  · -- no whitespace before the encoded word
    have hsplit : wspSplit (c :: p' ++ ewWord cs e txt) = (c :: p' ++ ewWord cs e txt, []) := by
      have hall : ∀ x ∈ c :: p' ++ ewWord cs e txt, (fun x => !isWsp x) x = true := by
        intro x hx
        rw [List.mem_append] at hx
        rcases hx with hx | hx
        · exact hpre x hx
        · exact hWnw x hx
      simp only [wspSplit, takeWhile_all hall, dropWhile_all hall]
    have hm : rfcMatchAt (ewWord cs e txt) = true := by
      simpa using rfcMatchAt_ew hcs htxt hn he []
    have hW' : ewWord cs e txt = 61 :: (ewWord cs e txt).tail := by simp [ewWord]
    have hrW : rfcSearch (ewWord cs e txt) = true := by
      rw [hW', rfcSearch, ← hW', hm]; rfl
    have hrfc : rfcSearch (c :: p' ++ ewWord cs e txt) = true := rfcSearch_append_left hrW (c :: p')
    have hpart : partitionEq (c :: p' ++ ewWord cs e txt) = (c :: p', ewWord cs e txt) := by
      have hv : c :: p' ++ ewWord cs e txt = (c :: p') ++ 61 :: 63 :: (ewWord cs e txt).drop 2 := by
        simp [ewWord]
      unfold partitionEq
      rw [hv, show S "=?" = [61, 63] from rfl, split1_pair (by decide) hno]
      simp [ewWord]
    have hatt : ewAttempt cfg (c :: p' ++ ewWord cs e txt) = .ok (none, true) := by
      unfold ewAttempt
      rw [show c :: p' ++ ewWord cs e txt = (c :: p') ++ ewWord cs e txt from rfl,
        startsWith_word hp hno (by rw [hW]; simp)]
      rfl
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by simp at hlen; omega⟩
    refine ⟨.node .unstructured "unstructured" [.term .val (c :: p') "utext" dsv, ew]
      [invalidHeader (S "missing whitespace before encoded word")] [], ?_, ?_, ?_, ?_⟩
    · unfold getUnstructured
      rw [List.append_nil, List.cons_append, unstructLoop]
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
      rw [← List.cons_append, hatt]
      simp only
      rw [wordSplit, hsplit]
      simp only [hrfc, Bool.and_self, ↓reduceIte]
      rw [hpart]
      simp only [hvt', mkL, LC.defTy, Tok.push]
      rw [hW', unstructLoop]
      simp only [show isWsp 61 = false from rfl, Bool.false_eq_true, ↓reduceIte]
      rw [← hW', hew]
      simp only
      rw [unstructLoop]
      simp [ewAppend, Tok.kids, Tok.ty, Tok.addDefect, Tok.push]
      rfl
    · simp [Tok.str, strs, hstr]
    · intro _; exact ⟨rfl, by simp only [Tok.kids, List.map_cons, List.map_nil, hcls]; rfl⟩
    · intro h; exact absurd rfl h
  · -- whitespace before the encoded word
    have hsp : ∀ x ∈ d :: sep', isSpace x = true := by rw [← hsd]; exact hsall
    have hd' : (!isWsp d) = false := by simp [hd]
    have hsplit : wspSplit (c :: p' ++ (d :: sep' ++ ewWord cs e txt)) =
        (c :: p', d :: sep' ++ ewWord cs e txt) := by
      simp only [wspSplit]
      rw [takeWhile_append_all _ hpre, dropWhile_append_all _ hpre]
      simp [List.takeWhile_cons, List.dropWhile_cons, hd']
    have hrfc : rfcSearch (c :: p') = false := by
      cases h : rfcSearch (c :: p') with
      | false => rfl
      | true => exact absurd (rfcSearch_start h) hno
    have hatt : ewAttempt cfg (c :: p' ++ (d :: sep' ++ ewWord cs e txt)) = .ok (none, true) := by
      unfold ewAttempt
      rw [startsWith_word hp hno (by
        simp only [List.cons_append, List.head?_cons, ne_eq, Option.some.injEq]
        rintro rfl; revert hd; decide)]
      rfl
    have hfws := getFws_spaces hsp hW
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by subst hsd; simp at hlen; omega⟩
    refine ⟨.node .unstructured "unstructured"
      [.term .val (c :: p') "utext" dsv, WT (d :: sep') "fws", ew] [] [], ?_, ?_, ?_, ?_⟩
    · unfold getUnstructured
      rw [hsd, List.append_assoc, List.cons_append, unstructLoop]
      simp only [hc, Bool.false_eq_true, ↓reduceIte]
      rw [← List.cons_append, hatt]
      simp only
      rw [wordSplit, hsplit]
      simp only [hrfc, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      simp only [hvt', mkL, LC.defTy, Tok.push]
      rw [List.cons_append, unstructLoop]
      simp only [hd, ↓reduceIte]
      rw [← List.cons_append, hfws]
      simp only [Tok.push]
      have hW' : ewWord cs e txt = 61 :: (ewWord cs e txt).tail := by simp [ewWord]
      rw [hW', unstructLoop]
      simp only [show isWsp 61 = false from rfl, Bool.false_eq_true, ↓reduceIte]
      rw [← hW', hew]
      simp only
      rw [unstructLoop]
      simp [ewAppend, Tok.kids, Tok.ty, Tok.push, WT]
      rfl
    · rw [hsd]; simp [Tok.str, strs, hstr, WT]
    · intro h; rw [hsd] at h; cases h
    · intro _; exact ⟨rfl, by simp only [Tok.kids, List.map_cons, List.map_nil, hcls]; rfl⟩

end PyLean.TextLibs.Email
