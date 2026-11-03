import PyLean.TextLibs.EmailQuote

/-!
`get_unstructured` (Lib/email/_header_value_parser.py:1129-1194, CPython 3.15.2) on encoded words
that decode: adjacent encoded words separated by whitespace become `EncodedWord` tokens with
`EWWhiteSpaceTerminal`s between them, so `str()` is the decoded texts run together.
-/

namespace PyLean.TextLibs.Email

open PyLean.UnicodeObj

/-- `=?tok?=`. -/
def ewStr (tok : Str) : Str := [61, 63] ++ tok ++ [63, 61]

/-- The text `_ew.decode` returns for `=?tok?=` (`[]` when it raises). -/
def decText (cfg : Cfg) (tok : Str) : Str :=
  match cfg.dec (ewStr tok) with
  | .ok t _ _ _ => t
  | _ => []

/-- The header value `=?tok0?=` followed, for each `(sep, tok)`, by `sep` and `=?tok?=`. -/
def ewsValue (tok0 : Str) (rest : List (Str × Str)) : Str :=
  ewStr tok0 ++ rest.flatMap (fun p => p.1 ++ ewStr p.2)

/-- The class name of a token. -/
def tokClass : Tok → String
  | .term c .. => c.name
  | .node c .. => c.name

/-- The token token is a word `_ew.decode` accepts, and `?=` does not occur in it. -/
def GoodTok (cfg : Cfg) (tok : Str) : Prop :=
  ¬ Occurs tok [63, 61] ∧ ∃ t cs l d, cfg.dec (ewStr tok) = .ok t cs l d

/-- A separator: whitespace (`str.isspace`) that starts with a space or tab. -/
def GoodSep (s : Str) : Prop := (∃ c t, s = c :: t ∧ isWsp c = true) ∧ ∀ x ∈ s, isSpace x = true

/-- For every list of encoded words `=?tok?=` that `_ew.decode` decodes (with no `?=` inside the
token) separated by runs of whitespace, `get_unstructured` returns a token list with no defects
whose elements are the `EncodedWord`s with an `EWWhiteSpaceTerminal` between each two, and whose
`str()` is the decoded texts run together: "any 'linear-white-space' that separates a pair of
adjacent 'encoded-word's is ignored" (RFC 2047 section 6.2), which :1170-1178 implement. -/
def UnstructuredEncodedWords : Prop :=
  ∀ (cfg : Cfg) (n : Nat) (tok0 : Str) (rest : List (Str × Str)),
    GoodTok cfg tok0 → (∀ p ∈ rest, GoodSep p.1 ∧ GoodTok cfg p.2) →
    (ewsValue tok0 rest).length < n →
    ∃ t, getUnstructured cfg n (ewsValue tok0 rest) = .ok t ∧
      t.str = decText cfg tok0 ++ rest.flatMap (fun p => decText cfg p.2) ∧ t.ds = [] ∧
      t.kids.map tokClass =
        "EncodedWord" :: rest.flatMap (fun _ => ["EWWhiteSpaceTerminal", "EncodedWord"])

/-! ## `get_encoded_word` on a well-formed word -/

theorem split1_qe {tok : Str} (h : ¬ Occurs tok [63, 61]) (y : Str) :
    split1 (tok ++ 63 :: 61 :: y) [63, 61] = (tok, some y) := by
  induction tok with
  | nil => simp [split1, List.isPrefixOf]
  | cons c tok ih =>
    have h' : ¬ Occurs tok [63, 61] := fun ho => h (occurs_append_left [c] ho)
    have hnp : [63, 61].isPrefixOf (c :: (tok ++ 63 :: 61 :: y)) = false := by
      cases tok with
      | nil => simp [List.isPrefixOf]
      | cons d tok' =>
        by_cases hcd : c = 63 ∧ d = 61
        · exfalso; obtain ⟨rfl, rfl⟩ := hcd; exact h ⟨[], tok', by simp⟩
        · simp only [List.isPrefixOf, List.cons_append, Bool.and_eq_false_imp, beq_iff_eq]
          intro h1 h2
          exact (hcd ⟨h1.symm, h2.symm⟩).elim
    rw [List.cons_append, split1, if_neg (by simp [hnp])]
    simp [ih h']

theorem ewTextLoop_strs (ty : String) :
    ∀ (n : Nat) (text : Str) (acc r : List Tok), ewTextLoop ty n text acc = .ok r →
      strs r = strs acc ++ text
  | 0, _, _, _, h => by simp [ewTextLoop] at h
  | n + 1, [], acc, r, h => by simp [ewTextLoop] at h; cases h; simp
  | n + 1, c :: cs, acc, r, h => by
    unfold ewTextLoop at h
    simp only at h
    split at h
    · have := ewTextLoop_strs ty n _ _ r h
      rw [this, strs_append, getFws_fst, getFws_snd]
      simp [strs, Tok.str, WT, List.takeWhile_append_dropWhile]
    · have := ewTextLoop_strs ty n _ _ r h
      rw [this, strs_append]
      simp only [strs, List.append_nil, (validateXtext_VT _ ty).1]
      rw [List.append_assoc, wspSplit_append]

/-- What `get_encoded_word` returns on `=?tok?=` followed by nothing or whitespace. -/
theorem getEncodedWord_good {cfg : Cfg} {tok : Str} (h : GoodTok cfg tok) (y : Str)
    (hy : y = [] ∨ ∃ c t, y = c :: t ∧ isWsp c = true) (ty : String) :
    ∃ ew, getEncodedWord cfg (ewStr tok ++ y) ty = .ok (ew, y) ∧ ew.str = decText cfg tok ∧
      tokClass ew = "EncodedWord" ∧ ew.ty = "encoded-word" := by
  obtain ⟨hno, t, cs, l, d, hdec⟩ := h
  have hv2 : (ewStr tok ++ y).drop 2 = tok ++ 63 :: 61 :: y := by simp [ewStr]
  have hsp := split1_qe hno y
  have hhex : ewHexFix tok y = (tok, y) := by
    unfold ewHexFix
    rw [if_neg]
    rcases hy with rfl | ⟨c, t', rfl, hc⟩
    · simp
    · have : isHexDigit c = false := by
        simp only [isWsp, Bool.or_eq_true, beq_iff_eq] at hc
        rcases hc with rfl | rfl <;> decide
      simp [this]
  obtain ⟨r, hr⟩ := ewTextLoop_ok ty (t.length + 1) t [] (Nat.lt_succ_self _)
  refine ⟨.node .encodedWord "encoded-word" r
    ((if twoWords tok then [invalidHeader (S "whitespace inside encoded word")] else []) ++ d ++
      (if headIs (fun c => !isWsp c) y then
        [invalidHeader (S "missing trailing whitespace after encoded-word")] else []))
    [("cte", .s (ewStr tok ++ y)), ("charset", .s cs), ("lang", .s l)], ?_, ?_, rfl, rfl⟩
  · unfold getEncodedWord
    have hst : startsWith (ewStr tok ++ y) (S "=?") = true := by
      simp [startsWith, ewStr, S]
    have hS : S "?=" = [63, 61] := rfl
    simp only [hst, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hv2, hS, hsp]
    have hne : (tok == tok ++ 63 :: 61 :: y) = false := by
      simp only [beq_eq_false_iff_ne]
      intro he
      have := congrArg List.length he
      simp at this
    simp only [hne, Bool.false_eq_true, ↓reduceIte, Option.getD_some, hhex]
    have hw : S "=?" ++ tok ++ [63, 61] = ewStr tok := rfl
    rw [hw, hdec]
    simp [ewBuild, hr]
    rfl
  · have := ewTextLoop_strs ty _ _ _ _ hr
    simp [strs] at this
    simp [Tok.str, this, decText, hdec]

theorem ewAttempt_good {cfg : Cfg} {tok : Str} (h : GoodTok cfg tok) (y : Str)
    (hy : y = [] ∨ ∃ c t, y = c :: t ∧ isWsp c = true) :
    ∃ ew, ewAttempt cfg (ewStr tok ++ y) = .ok (some (ew, y), true) ∧ ew.str = decText cfg tok ∧
      tokClass ew = "EncodedWord" ∧ ew.ty = "encoded-word" := by
  obtain ⟨ew, h1, h2, h3, hty⟩ := getEncodedWord_good h y hy "utext"
  refine ⟨ew, ?_, h2, h3, hty⟩
  have hst : startsWith (ewStr tok ++ y) (S "=?") = true := by simp [startsWith, ewStr, S]
  simp [ewAttempt, hst, h1]
  rfl

/-! ## The loop -/

theorem flat_tail {rest : List (Str × Str)} (h : ∀ p ∈ rest, GoodSep p.1) :
    rest.flatMap (fun p => p.1 ++ ewStr p.2) = [] ∨
      ∃ c t, rest.flatMap (fun p => p.1 ++ ewStr p.2) = c :: t ∧ isWsp c = true := by
  cases rest with
  | nil => exact .inl rfl
  | cons p rest =>
    obtain ⟨⟨c, t, hs, hc⟩, _⟩ := h p (by simp)
    exact .inr ⟨c, t ++ ewStr p.2 ++ rest.flatMap (fun p => p.1 ++ ewStr p.2), by simp [hs], hc⟩

theorem ewAppend_first (ty : String) (ds : List Defect) (atts : List (String × AV)) (ew : Tok) :
    ewAppend (.node .unstructured ty [] ds atts) ew = .node .unstructured ty [ew] ds atts := by
  simp [ewAppend, Tok.kids, Tok.push]

theorem ewAppend_after (K0 : List Tok) (x f ew : Tok) (hx : x.ty = "encoded-word")
    (hf : f.ty = "fws") (ty : String) (ds : List Defect) (atts : List (String × AV)) :
    ewAppend (.node .unstructured ty (K0 ++ [x, f]) ds atts) ew =
      .node .unstructured ty (K0 ++ [x, ewws f, ew]) ds atts := by
  have hlast : (K0 ++ [x, f]).getLast? = some f := by simp
  have hd : (K0 ++ [x, f]).getD ((K0 ++ [x, f]).length - 2) default = x := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]
  have hdl : (K0 ++ [x, f]).dropLast = K0 ++ [x] := by
    rw [show K0 ++ [x, f] = (K0 ++ [x]) ++ [f] by simp, List.dropLast_concat]
  simp only [ewAppend, Tok.kids, hlast, hf, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    Option.getD_some, hd, hx, hdl]
  simp [Tok.setKids, Tok.push]

theorem getFws_sep {s : Str} (hs : GoodSep s) (tok : Str) (y : Str) :
    (getFws (s ++ ewStr tok ++ y)).1 = WT s "fws" ∧ (getFws (s ++ ewStr tok ++ y)).2 = ewStr tok ++ y := by
  have hall : ∀ a ∈ s, isSpace a = true := hs.2
  have h61 : isSpace 61 = false := by decide
  have he : ewStr tok ++ y = 61 :: (63 :: (tok ++ [63, 61] ++ y)) := by simp [ewStr]
  rw [getFws_fst, getFws_snd, List.append_assoc, takeWhile_append_all _ hall,
    dropWhile_append_all _ hall, he]
  simp [List.takeWhile_cons, List.dropWhile_cons, h61]

theorem loopA {cfg : Cfg} : ∀ (rest : List (Str × Str)) (n : Nat) (K0 : List Tok) (x : Tok)
    (ty : String) (ds : List Defect) (atts : List (String × AV)),
    x.ty = "encoded-word" → (∀ p ∈ rest, GoodSep p.1 ∧ GoodTok cfg p.2) →
    (rest.flatMap (fun p => p.1 ++ ewStr p.2)).length < n →
    ∃ more, unstructLoop cfg n (rest.flatMap (fun p => p.1 ++ ewStr p.2))
        (.node .unstructured ty (K0 ++ [x]) ds atts) =
        .ok (.node .unstructured ty (K0 ++ [x] ++ more) ds atts) ∧
      strs more = rest.flatMap (fun p => decText cfg p.2) ∧
      more.map tokClass = rest.flatMap (fun _ => ["EWWhiteSpaceTerminal", "EncodedWord"])
  | [], n, K0, x, ty, ds, atts, _, _, hlen => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hlen; omega⟩
    exact ⟨[], by simp [unstructLoop]; rfl, rfl, rfl⟩
  | (s, tok) :: rest, n, K0, x, ty, ds, atts, hx, hr, hlen => by
    obtain ⟨hsep, hgood⟩ := hr (s, tok) (by simp)
    have hr' : ∀ p ∈ rest, GoodSep p.1 ∧ GoodTok cfg p.2 := fun p hp => hr p (by simp [hp])
    obtain ⟨⟨c, t, hs, hc⟩, hsp⟩ := hsep
    simp only at hs hsp
    have hval : ((s, tok) :: rest).flatMap (fun p => p.1 ++ ewStr p.2) =
        s ++ ewStr tok ++ rest.flatMap (fun p => p.1 ++ ewStr p.2) := by simp
    have hL : (((s, tok) :: rest).flatMap (fun p => p.1 ++ ewStr p.2)).length =
        s.length + (tok.length + 4) + (rest.flatMap (fun p => p.1 ++ ewStr p.2)).length := by
      rw [hval]; simp [ewStr]; omega
    have hs1 : 1 ≤ s.length := by rw [hs]; simp
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    obtain ⟨ew, hew, hstr, hcls, hty⟩ := ewAttempt_good hgood _ (flat_tail (fun p hp => (hr' p hp).1))
    obtain ⟨more, h1, h2, h3⟩ := loopA rest m (K0 ++ [x, ewws (WT s "fws")]) ew ty ds atts hty hr'
      (by omega)
    refine ⟨[ewws (WT s "fws"), ew] ++ more, ?_, ?_, ?_⟩
    · have hfws := getFws_sep (s := s) ⟨⟨c, t, hs, hc⟩, hsp⟩ tok
        (rest.flatMap (fun p => p.1 ++ ewStr p.2))
      have hv' : s ++ ewStr tok ++ rest.flatMap (fun p => p.1 ++ ewStr p.2) =
          c :: (t ++ (ewStr tok ++ rest.flatMap (fun p => p.1 ++ ewStr p.2))) := by
        rw [hs]; simp
      rw [hval, hv', unstructLoop]
      simp only [hc, ↓reduceIte]
      rw [← hv', hfws.1, hfws.2]
      have he : ewStr tok ++ rest.flatMap (fun p => p.1 ++ ewStr p.2) =
          61 :: (63 :: (tok ++ [63, 61] ++ rest.flatMap (fun p => p.1 ++ ewStr p.2))) := by
        simp [ewStr]
      rw [he, unstructLoop]
      simp only [show isWsp 61 = false from rfl, Bool.false_eq_true, ↓reduceIte]
      rw [← he, hew]
      simp only [Tok.push]
      rw [show K0 ++ [x] ++ [WT s "fws"] = K0 ++ [x, WT s "fws"] by simp,
        ewAppend_after K0 x (WT s "fws") ew hx rfl]
      rw [show K0 ++ [x, ewws (WT s "fws"), ew] = K0 ++ [x, ewws (WT s "fws")] ++ [ew] by simp, h1]
      simp
    · simp [strs, ewws, Tok.str, hstr, h2, WT]
    · rw [List.map_append, h3]
      simp only [List.map_cons, List.map_nil, hcls]
      simp [tokClass, ewws, TC.name]

theorem unstructuredEncodedWords_proven : UnstructuredEncodedWords := by
  intro cfg n tok0 rest h0 hr hlen
  have hL : (ewsValue tok0 rest).length =
      tok0.length + 4 + (rest.flatMap (fun p => p.1 ++ ewStr p.2)).length := by
    simp [ewsValue, ewStr]; omega
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨ew, hew, hstr, hcls, hty⟩ := ewAttempt_good h0 _ (flat_tail (fun p hp => (hr p hp).1))
  obtain ⟨more, h1, h2, h3⟩ := loopA rest m [] ew "unstructured" [] [] hty hr (by omega)
  refine ⟨.node .unstructured "unstructured" ([] ++ [ew] ++ more) [] [], ?_, ?_, rfl, ?_⟩
  · have he : ewsValue tok0 rest =
        61 :: (63 :: (tok0 ++ [63, 61] ++ rest.flatMap (fun p => p.1 ++ ewStr p.2))) := by
      simp [ewsValue, ewStr]
    unfold getUnstructured
    rw [he, unstructLoop]
    simp only [show isWsp 61 = false from rfl, Bool.false_eq_true, ↓reduceIte]
    have he' : 61 :: (63 :: (tok0 ++ [63, 61] ++ rest.flatMap (fun p => p.1 ++ ewStr p.2))) =
        ewStr tok0 ++ rest.flatMap (fun p => p.1 ++ ewStr p.2) := by simp [ewStr]
    rw [he', hew]
    simp only [mkL, LC.defTy]
    rw [ewAppend_first]
    rw [show [ew] = [] ++ [ew] by rfl, h1]
    simp
  · simp [Tok.str, strs, hstr, h2]
  · simp only [Tok.kids, List.map_append, List.map_cons, List.map_nil, hcls, h3]
    simp

end PyLean.TextLibs.Email
