import PyLean.TextLibs.EmailRefute

/-!
`get_unstructured` (Lib/email/_header_value_parser.py:1129-1194, CPython 3.15.2) always
returns, and keeps the text: its `str()` is the input, and its `value` is the input with each
run of whitespace that starts with a space or tab collapsed to one space.
-/

namespace PyLean.TextLibs.Email

open PyLean.UnicodeObj

theorem dropWhile_length_le (p : Nat → Bool) : ∀ l : Str, (l.dropWhile p).length ≤ l.length
  | [] => Nat.le_refl _
  | c :: cs => by
    rw [List.dropWhile_cons]
    split
    · have := dropWhile_length_le p cs
      simp; omega
    · exact Nat.le_refl _

/-- The input with every run of whitespace that starts with a space or a tab, together with the
whitespace (`str.isspace`) after it, replaced by one space: what `value` of an unstructured
header is, by the module docstring (:35-39, "The value of all whitespace tokens ... is a single
space"). Other whitespace (a line feed not after a space, say) stays. -/
def collapse : Str → Str
  | [] => []
  | c :: cs => if isWsp c then 32 :: collapse (cs.dropWhile isSpace) else c :: collapse cs
termination_by s => s.length
decreasing_by
  all_goals simp_wf
  all_goals (have := dropWhile_length_le isSpace cs; omega)

/-- `get_unstructured` returns, whatever `_ew.decode` returns, if it raises nothing
`get_encoded_word` does not catch; the loop needs no more iterations than the value has
characters (each iteration consumes one at least; the `=?` split of :1188-1189 always does,
because a word starting with `=?` that holds an encoded word is one `get_encoded_word` parsed or
rejected as `_InvalidEwError`, the comment at :1185-1187). When `_ew.decode` rejects every
encoded word, as CPython's does for malformed ones, the token list's `str()` is the value and
its `value` is `collapse` of it: `str()` keeps whitespace runs, `value` collapses them
(module docstring, :35-49). -/
def UnstructuredSpec : Prop :=
  (∀ (cfg : Cfg) (v : Str) (n : Nat), DecSafe cfg → v.length < n →
    ∃ t, getUnstructured cfg n v = .ok t) ∧
  (∀ (cfg : Cfg) (v : Str) (n : Nat) (t : Tok), (∀ s, cfg.dec s = .caught) →
    getUnstructured cfg n v = .ok t → t.str = v ∧ t.value = .ok (collapse v))

/-! ## List lemmas -/

theorem isSpace_of_wsp {c : Nat} (h : isWsp c = true) : isSpace c = true := by
  simp only [isWsp, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | rfl <;> decide

theorem take_sub_dropWhile (p : Nat → Bool) :
    ∀ v : Str, v.take (v.length - (v.dropWhile p).length) = v.takeWhile p
  | [] => rfl
  | c :: cs => by
    by_cases hc : p c = true
    · have ih := take_sub_dropWhile p cs
      have hle := dropWhile_length_le p cs
      simp only [List.dropWhile_cons, List.takeWhile_cons, hc, ↓reduceIte, List.length_cons]
      rw [show cs.length + 1 - (cs.dropWhile p).length = (cs.length - (cs.dropWhile p).length) + 1
        by omega]
      simp [ih]
    · simp [hc]

theorem getFws_fst (v : Str) : (getFws v).1 = WT (v.takeWhile isSpace) "fws" := by
  simp [getFws, lstrip, take_sub_dropWhile]

theorem getFws_snd (v : Str) : (getFws v).2 = v.dropWhile isSpace := rfl

/-- An occurrence of `sep` in `s`. -/
def Occurs (s sep : Str) : Prop := ∃ p q, s = p ++ sep ++ q

theorem split1_some {sep : Str} : ∀ {s b a : Str}, split1 s sep = (b, some a) → b ++ sep ++ a = s
  | [], b, a, h => by simp [split1] at h
  | c :: cs, b, a, h => by
    unfold split1 at h
    split at h
    · rename_i hp
      simp only [Prod.mk.injEq, Option.some.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨t, ht⟩ := (List.isPrefixOf_iff_prefix.mp hp)
      rw [← ht]; simp
    · simp only [Prod.mk.injEq] at h
      obtain ⟨hb, ha⟩ := h
      have ih := split1_some (s := cs) (b := (split1 cs sep).1) (a := a) (by
        rw [← ha])
      rw [← hb]; simp [ih]

theorem split1_min {sep : Str} (hsep : sep ≠ []) :
    ∀ {s p q : Str}, s = p ++ sep ++ q →
      ∃ b a, split1 s sep = (b, some a) ∧ b.length ≤ p.length
  | [], p, q, h => by
    have := congrArg List.length h
    simp at this
    cases sep with
    | nil => exact absurd rfl hsep
    | cons _ _ => simp at this; omega
  | c :: cs, p, q, h => by
    unfold split1
    split
    · exact ⟨[], _, rfl, Nat.zero_le _⟩
    · rename_i hp
      cases p with
      | nil =>
        exfalso; apply hp
        simp only [List.nil_append] at h
        rw [h]; exact List.isPrefixOf_iff_prefix.mpr (List.prefix_append _ _)
      | cons x p' =>
        simp only [List.cons_append, List.cons.injEq] at h
        obtain ⟨_, hcs⟩ := h
        obtain ⟨b, a, hb, hl⟩ := split1_min hsep hcs
        exact ⟨c :: b, a, by simp [hb], by simp; omega⟩

theorem split1_none_not_occurs {sep : Str} (hsep : sep ≠ []) {s b : Str}
    (h : split1 s sep = (b, none)) : ¬ Occurs s sep := by
  rintro ⟨p, q, hs⟩
  obtain ⟨b', a', h', _⟩ := split1_min hsep hs
  rw [h] at h'
  simp at h'

theorem occurs_append_left {s sep : Str} (x : Str) (h : Occurs s sep) : Occurs (x ++ s) sep := by
  obtain ⟨p, q, rfl⟩ := h
  exact ⟨x ++ p, q, by simp⟩

theorem occurs_append_right {s sep : Str} (y : Str) (h : Occurs s sep) : Occurs (s ++ y) sep := by
  obtain ⟨p, q, rfl⟩ := h
  exact ⟨p, q ++ y, by simp⟩

/-! ## `rfc2047_matcher` needs a `?=` after the `=?` -/

theorem qeBeforeNl_occurs : ∀ {r : Str}, qeBeforeNl r = true → Occurs r [63, 61]
  | [], h => by simp [qeBeforeNl] at h
  | [x], h => by
    unfold qeBeforeNl at h
    split at h <;> simp_all [qeBeforeNl]
  | x :: y :: t, h => by
    by_cases h1 : x = 63 ∧ y = 61
    · obtain ⟨rfl, rfl⟩ := h1
      exact ⟨[], t, rfl⟩
    · have h' : qeBeforeNl (y :: t) = true := by
        unfold qeBeforeNl at h
        split at h
        · rename_i heq; simp at heq; omega
        · simp at h
        · rename_i heq; simp at heq; obtain ⟨_, rfl⟩ := heq; exact h
        · simp at h
      exact occurs_append_left [x] (qeBeforeNl_occurs h')

theorem rfcMatchAt_occurs {s : Str} (h : rfcMatchAt s = true) : Occurs (s.drop 2) [63, 61] := by
  unfold rfcMatchAt at h
  split at h
  · rename_i r
    split at h
    · rename_i c r' heq
      simp only [Bool.and_eq_true] at h
      have hr' := qeBeforeNl_occurs h.2
      have hsplit := List.takeWhile_append_dropWhile (p := (· != 63)) (l := r)
      rw [heq] at hsplit
      simp only [List.drop_succ_cons, List.drop_zero]
      rw [← hsplit]
      exact occurs_append_left _ (occurs_append_left [63, c, 63] hr')
    · simp at h
  · simp at h

theorem drop_one_eq (l : Str) : ∃ a, l.drop 1 = a ++ l.drop 2 := by
  match l with
  | [] => exact ⟨[], rfl⟩
  | [_] => exact ⟨[], rfl⟩
  | _ :: y :: z => exact ⟨[y], rfl⟩

theorem rfcSearch_occurs : ∀ {s : Str}, rfcSearch s = true → Occurs (s.drop 2) [63, 61]
  | [], h => by simp [rfcSearch] at h
  | c :: t, h => by
    unfold rfcSearch at h
    simp only [Bool.or_eq_true] at h
    rcases h with h | h
    · exact rfcMatchAt_occurs h
    · have ih := rfcSearch_occurs h
      obtain ⟨a, ha⟩ := drop_one_eq t
      simp only [List.drop_succ_cons]
      rw [ha]
      exact occurs_append_left a ih

theorem rfcMatchAt_start {s : Str} (h : rfcMatchAt s = true) : Occurs s [61, 63] := by
  unfold rfcMatchAt at h
  split at h
  · rename_i r
    exact ⟨[], r, rfl⟩
  · simp at h

theorem rfcSearch_start : ∀ {s : Str}, rfcSearch s = true → Occurs s [61, 63]
  | [], h => by simp [rfcSearch] at h
  | c :: t, h => by
    unfold rfcSearch at h
    simp only [Bool.or_eq_true] at h
    rcases h with h | h
    · exact rfcMatchAt_start h
    · exact occurs_append_left [c] (rfcSearch_start h)

/-! ## `split1` -/

theorem split1_none_fst {sep : Str} : ∀ {s : Str}, (split1 s sep).2 = none → (split1 s sep).1 = s
  | [], _ => rfl
  | c :: cs, h => by
    unfold split1 at h ⊢
    split
    · rename_i hp; simp [hp] at h
    · rename_i hp
      simp only [hp] at h
      simp [split1_none_fst h]

theorem split1_snd_le {sep : Str} {s a : Str} (h : (split1 s sep).2 = some a) :
    a.length + sep.length ≤ s.length := by
  have := split1_some (s := s) (b := (split1 s sep).1) (a := a) (by rw [← h])
  have := congrArg List.length this
  simp at this; omega

/-! ## `get_fws` and the encoded-word text loop -/

theorem getFws_snd_lt {c : Nat} {cs : Str} (hc : isWsp c = true) :
    (getFws (c :: cs)).2.length ≤ cs.length := by
  rw [getFws_snd, List.dropWhile_cons, if_pos (isSpace_of_wsp hc)]
  exact dropWhile_length_le _ _

theorem wspSplit_snd_lt {c : Nat} {cs : Str} (hc : isWsp c = false) :
    (wspSplit (c :: cs)).2.length ≤ cs.length := by
  simp only [wspSplit, List.dropWhile_cons, hc, Bool.not_false, ↓reduceIte]
  exact dropWhile_length_le _ _

theorem ewTextLoop_ok (ty : String) :
    ∀ (n : Nat) (text : Str) (acc : List Tok), text.length < n → ∃ r, ewTextLoop ty n text acc = .ok r
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, [], acc, _ => ⟨acc, by simp [ewTextLoop]; rfl⟩
  | n + 1, c :: cs, acc, h => by
    simp only [List.length_cons] at h
    unfold ewTextLoop
    simp only
    split
    · rename_i hc
      exact ewTextLoop_ok ty n _ _ (Nat.lt_of_le_of_lt (getFws_snd_lt hc) (by omega))
    · rename_i hc
      exact ewTextLoop_ok ty n _ _
        (Nat.lt_of_le_of_lt (wspSplit_snd_lt (Bool.eq_false_iff.mpr hc)) (by omega))

theorem ewBuild_ok (ty : String) (value tok rest text charset lang : Str) (dds : List Defect) :
    ∃ t, ewBuild ty value tok rest text charset lang dds = .ok (t, rest) := by
  obtain ⟨r, hr⟩ := ewTextLoop_ok ty (text.length + 1) text [] (Nat.lt_succ_self _)
  exact ⟨_, by simp [ewBuild, hr]; rfl⟩

/-! ## `get_encoded_word` -/

theorem getEncodedWord_err {cfg : Cfg} (hs : DecSafe cfg) {v : Str} {ty : String} {e : EExc}
    (h : getEncodedWord cfg v ty = .error e) : (∃ m, e = .hpe m) ∨ (∃ m, e = .invalidEw m) := by
  unfold getEncodedWord at h
  simp only at h
  split at h
  · cases h; exact .inl ⟨_, rfl⟩
  · split at h
    · cases h; exact .inl ⟨_, rfl⟩
    · split at h
      · cases h; exact .inr ⟨_, rfl⟩
      · rename_i c m heq; exact absurd heq (hs _ c m)
      · rename_i text cs lang dds _
        obtain ⟨t, ht⟩ := ewBuild_ok ty v _ _ text cs lang dds
        rw [ht] at h; cases h

theorem getEncodedWord_hpe {cfg : Cfg} {v : Str} {ty : String} {m : Str}
    (h : getEncodedWord cfg v ty = .error (.hpe m)) (hst : startsWith v (S "=?") = true) :
    (split1 (v.drop 2) (S "?=")).2 = none := by
  unfold getEncodedWord at h
  simp only at h
  split at h
  · rename_i hn; simp [hst] at hn
  · split at h
    · rename_i heq
      cases h2 : (split1 (v.drop 2) (S "?=")).2 with
      | none => rfl
      | some a =>
        have h5 := split1_some (s := v.drop 2) (b := (split1 (v.drop 2) (S "?=")).1) (a := a)
          (by rw [← h2])
        rw [beq_iff_eq.mp heq] at h5
        have := congrArg List.length h5
        simp only [List.length_append] at this
        have : (S "?=").length = 2 := rfl
        omega
    · split at h
      · cases h
      · cases h
      · rename_i text cs lang dds _
        obtain ⟨t, ht⟩ := ewBuild_ok ty v _ _ text cs lang dds
        rw [ht] at h; cases h

theorem ewHexFix_le (tok0 remstr : Str) : (ewHexFix tok0 remstr).2.length ≤ remstr.length := by
  unfold ewHexFix
  split
  · cases h : (split1 remstr (S "?=")).2 with
    | none => simp
    | some a => have := split1_snd_le h; simp; omega
  · exact Nat.le_refl _

theorem getEncodedWord_ok_lt {cfg : Cfg} {v : Str} {ty : String} {t : Tok} {rest : Str}
    (h : getEncodedWord cfg v ty = .ok (t, rest)) : rest.length < v.length := by
  unfold getEncodedWord at h
  simp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i hne
      split at h
      · cases h
      · cases h
      · rename_i text cs lang dds _
        obtain ⟨t', ht⟩ := ewBuild_ok ty v _ _ text cs lang dds
        rw [ht] at h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl⟩ := h
        cases h2 : (split1 (v.drop 2) (S "?=")).2 with
        | none =>
          exfalso; apply hne
          rw [split1_none_fst h2]; simp
        | some a =>
          have h3 := split1_snd_le h2
          have h4 := ewHexFix_le (split1 (v.drop 2) (S "?=")).1 a
          simp only [h2, Option.getD_some]
          simp [S] at h3
          have : (v.drop 2).length ≤ v.length := by simp
          omega

theorem getEncodedWord_caught {cfg : Cfg} (hc : ∀ s, cfg.dec s = .caught) (v : Str) (ty : String)
    (r : Tok × Str) : getEncodedWord cfg v ty ≠ .ok r := by
  intro h
  unfold getEncodedWord at h
  simp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · rw [hc] at h; cases h

/-! ## The steps of `get_unstructured` -/

theorem ewAttempt_ok {cfg : Cfg} (hs : DecSafe cfg) (v : Str) : ∃ r, ewAttempt cfg v = .ok r := by
  unfold ewAttempt
  split
  · split
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
    · rename_i e h1 h2 h3
      rcases getEncodedWord_err hs h3 with ⟨m, rfl⟩ | ⟨m, rfl⟩
      · exact absurd rfl (h2 m)
      · exact absurd rfl (h1 m)
  · exact ⟨_, rfl⟩

theorem ewAttempt_none_true {cfg : Cfg} {v : Str} (h : ewAttempt cfg v = .ok (none, true))
    (hst : startsWith v (S "=?") = true) : (split1 (v.drop 2) (S "?=")).2 = none := by
  unfold ewAttempt at h
  rw [if_pos hst] at h
  split at h
  · cases h
  · cases h
  · rename_i m heq; exact getEncodedWord_hpe heq hst
  · cases h

theorem ewAttempt_some_lt {cfg : Cfg} {v v' : Str} {tok : Tok} {b : Bool}
    (h : ewAttempt cfg v = .ok (some (tok, v'), b)) : v'.length < v.length := by
  unfold ewAttempt at h
  split at h
  · split at h
    · rename_i r heq
      cases h
      exact getEncodedWord_ok_lt heq
    · cases h
    · cases h
    · cases h
  · cases h

theorem ewAttempt_caught {cfg : Cfg} (hc : ∀ s, cfg.dec s = .caught) {v : Str} {r : Tok × Str}
    {b : Bool} : ewAttempt cfg v ≠ .ok (some r, b) := by
  intro h
  unfold ewAttempt at h
  split at h
  · split at h
    · rename_i r' heq; exact getEncodedWord_caught hc v "utext" r' heq
    · cases h
    · cases h
    · cases h
  · cases h

theorem mem_takeWhile_p {p : Nat → Bool} {x : Nat} : ∀ {l : Str}, x ∈ l.takeWhile p → p x = true
  | [], h => by simp at h
  | c :: cs, h => by
    rw [List.takeWhile_cons] at h
    split at h
    · rename_i hc
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · exact hc
      · exact mem_takeWhile_p h
    · simp at h

theorem wspSplit_append (v : Str) : (wspSplit v).1 ++ (wspSplit v).2 = v :=
  List.takeWhile_append_dropWhile

/-- What `wordSplit` returns when it splits at `=?`: the text before the first `=?`, a prefix
of the word. -/
theorem partitionEq_of_occurs {frag r : Str} (h : Occurs frag [61, 63]) :
    ∃ b a, partitionEq (frag ++ r) = (b, [61, 63] ++ a) ∧ b ++ [61, 63] ++ a = frag ++ r ∧
      b.length < frag.length := by
  obtain ⟨p, q, hpq⟩ := h
  have hv : frag ++ r = p ++ [61, 63] ++ (q ++ r) := by rw [hpq]; simp
  obtain ⟨b, a, hs, hl⟩ := split1_min (sep := [61, 63]) (by simp) hv
  refine ⟨b, a, ?_, split1_some hs, ?_⟩
  · simp [partitionEq, S, hs]
  · have := congrArg List.length hpq; simp at this; omega

theorem wordSplit_append (b : Bool) (v : Str) : (wordSplit b v).1 ++ (wordSplit b v).2 = v := by
  unfold wordSplit
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    have hv := wspSplit_append v
    obtain ⟨b', a, hp, hs, _⟩ := partitionEq_of_occurs (r := (wspSplit v).2) (rfcSearch_start h.2)
    rw [hv] at hp hs
    rw [hp]; simpa using hs
  · exact wspSplit_append v

theorem wordSplit_noWsp (b : Bool) (v : Str) : ∀ x ∈ (wordSplit b v).1, isWsp x = false := by
  have hw : ∀ x ∈ (wspSplit v).1, isWsp x = false := by
    intro x hx
    have := mem_takeWhile_p hx
    simpa using this
  unfold wordSplit
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    have hv := wspSplit_append v
    obtain ⟨b', a, hp, hs, hl⟩ := partitionEq_of_occurs (r := (wspSplit v).2) (rfcSearch_start h.2)
    rw [hv] at hp
    rw [hp]
    intro x hx
    apply hw x
    have : b' = (wspSplit v).1.take b'.length := by
      have := congrArg (List.take b'.length) hs
      simp at this
      rw [List.take_append_of_le_length (by omega)] at this
      exact this
    rw [this] at hx
    exact List.mem_of_mem_take hx
  · exact hw

theorem wordSplit_lt {b : Bool} {c : Nat} {cs : Str} (hc : isWsp c = false)
    (hb : b = true → startsWith (c :: cs) (S "=?") = true →
      (split1 ((c :: cs).drop 2) (S "?=")).2 = none) :
    (wordSplit b (c :: cs)).2.length < (c :: cs).length := by
  unfold wordSplit
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    have hv := wspSplit_append (c :: cs)
    have hocc := rfcSearch_start h.2
    obtain ⟨b', a, hp, hs, hl⟩ := partitionEq_of_occurs (r := (wspSplit (c :: cs)).2) hocc
    rw [hv] at hp hs
    rw [hp]
    cases b' with
    | cons x b'' =>
      have := congrArg List.length hs
      simp at this ⊢; omega
    | nil =>
      exfalso
      simp only [List.nil_append] at hs
      have hst : startsWith (c :: cs) (S "=?") = true := by
        rw [← hs]; simp [startsWith, S]
      have hnone := hb h.1 hst
      apply split1_none_not_occurs (sep := S "?=") (by simp [S]) (b := (split1 _ _).1)
        (by rw [← hnone])
      -- the `?=` of the encoded word lies after the `=?` that starts the value
      have hocc2 := rfcSearch_occurs h.2
      obtain ⟨p, q, hpq⟩ := hocc
      have hlen : 2 ≤ (wspSplit (c :: cs)).1.length := by
        have := congrArg List.length hpq; simp at this; omega
      rw [← hv, List.drop_append_of_le_length hlen]
      exact occurs_append_right _ hocc2
  · have := wspSplit_snd_lt (cs := cs) hc
    simp; omega

/-! ## The loop always returns -/

theorem unstructLoop_total {cfg : Cfg} (hs : DecSafe cfg) :
    ∀ (n : Nat) (v : Str) (u : Tok), v.length < n → ∃ t, unstructLoop cfg n v u = .ok t
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, [], u, _ => ⟨u, by simp [unstructLoop]; rfl⟩
  | n + 1, c :: cs, u, h => by
    simp only [List.length_cons] at h
    unfold unstructLoop
    simp only
    split
    · rename_i hc
      exact unstructLoop_total hs n _ _ (Nat.lt_of_le_of_lt (getFws_snd_lt hc) (by omega))
    · rename_i hc
      obtain ⟨r, hr⟩ := ewAttempt_ok hs (c :: cs)
      rw [hr]
      rcases r with ⟨_ | ⟨tok, v'⟩, b⟩
      · simp only
        have := wordSplit_lt (b := b) (cs := cs) (Bool.eq_false_iff.mpr hc) (by
          intro hb hst; subst hb; exact ewAttempt_none_true hr hst)
        exact unstructLoop_total hs n _ _ (by simp at this; omega)
      · simp only
        have := ewAttempt_some_lt hr
        exact unstructLoop_total hs n _ _ (by simp at this; omega)

/-! ## Text and value when no encoded word decodes -/

/-- The value of a whitespace or value terminal. -/
def termVal : Tok → Str
  | .term .ws _ _ _ => [32]
  | .term .val s _ _ => s
  | _ => []

/-- A `WhiteSpaceTerminal` or `ValueTerminal`. -/
def simple : Tok → Bool
  | .term .ws .. => true
  | .term .val .. => true
  | _ => false

theorem collapse_cons_noWsp {c : Nat} {cs : Str} (hc : isWsp c = false) :
    collapse (c :: cs) = c :: collapse cs := by
  rw [collapse.eq_2]; simp [hc]

theorem collapse_cons_wsp {c : Nat} {cs : Str} (hc : isWsp c = true) :
    collapse (c :: cs) = 32 :: collapse (cs.dropWhile isSpace) := by
  rw [collapse.eq_2]; simp [hc]

theorem collapse_append_noWsp : ∀ (tok rem : Str), (∀ x ∈ tok, isWsp x = false) →
    collapse (tok ++ rem) = tok ++ collapse rem
  | [], rem, _ => rfl
  | c :: tok, rem, h => by
    rw [List.cons_append, collapse_cons_noWsp (h c (by simp))]
    rw [collapse_append_noWsp tok rem (fun x hx => h x (by simp [hx]))]
    rfl

theorem validateXtext_term (c : TC) (s : Str) (ty : String) (ds : List Defect) :
    ∃ ds', validateXtext (.term c s ty ds) = .term c s ty ds' := by
  simp only [validateXtext]
  exact ⟨_, rfl⟩

theorem strs_append : ∀ (xs ys : List Tok), strs (xs ++ ys) = strs xs ++ strs ys
  | [], ys => by simp [strs]
  | x :: xs, ys => by simp [strs, strs_append xs ys]

theorem unstructLoop_caught {cfg : Cfg} (hc : ∀ s, cfg.dec s = .caught) :
    ∀ (n : Nat) (v : Str) (ty : String) (ks : List Tok) (ds : List Defect)
      (atts : List (String × AV)) (t : Tok),
      unstructLoop cfg n v (.node .unstructured ty ks ds atts) = .ok t →
      ∃ ks', t = .node .unstructured ty (ks ++ ks') ds atts ∧ (∀ k ∈ ks', simple k = true) ∧
        strs ks' = v ∧ ks'.flatMap termVal = collapse v
  | 0, _, _, _, _, _, _, h => by simp [unstructLoop] at h
  | n + 1, [], ty, ks, ds, atts, t, h => by
    simp [unstructLoop] at h
    cases h
    exact ⟨[], by simp, by simp, rfl, by simp [collapse]⟩
  | n + 1, c :: cs, ty, ks, ds, atts, t, h => by
    unfold unstructLoop at h
    simp only at h
    split at h
    · rename_i hw
      obtain ⟨ks', ht, hsim, hstr, hval⟩ := unstructLoop_caught hc n _ ty _ ds atts t h
      refine ⟨(getFws (c :: cs)).1 :: ks', by rw [ht]; simp [Tok.push], ?_, ?_, ?_⟩
      · intro k hk
        simp only [List.mem_cons] at hk
        rcases hk with rfl | hk
        · simp [getFws_fst, WT, simple]
        · exact hsim k hk
      · rw [strs, hstr, getFws_fst, getFws_snd]
        simp [Tok.str, WT]
      · rw [List.flatMap_cons, hval, getFws_fst, getFws_snd, collapse_cons_wsp hw,
          List.dropWhile_cons, if_pos (isSpace_of_wsp hw)]
        simp [termVal, WT]
    · rename_i hw
      split at h
      · cases h
      · rename_i tok v' b heq
        exact absurd heq (ewAttempt_caught hc)
      · rename_i b heq
        obtain ⟨ds', hds⟩ := validateXtext_term .val (wordSplit b (c :: cs)).1 "utext" []
        simp only [VT] at h
        rw [hds] at h
        obtain ⟨ks', ht, hsim, hstr, hval⟩ := unstructLoop_caught hc n _ ty _ ds atts t h
        refine ⟨.term .val (wordSplit b (c :: cs)).1 "utext" ds' :: ks',
          by rw [ht]; simp [Tok.push], ?_, ?_, ?_⟩
        · intro k hk
          simp only [List.mem_cons] at hk
          rcases hk with rfl | hk
          · rfl
          · exact hsim k hk
        · rw [strs, hstr]
          simpa [Tok.str] using wordSplit_append b (c :: cs)
        · rw [List.flatMap_cons, hval]
          have h1 := wordSplit_append b (c :: cs)
          have h2 : collapse (c :: cs) =
              collapse ((wordSplit b (c :: cs)).1 ++ (wordSplit b (c :: cs)).2) := by rw [h1]
          rw [h2, collapse_append_noWsp _ _ (wordSplit_noWsp b (c :: cs))]
          rfl

theorem foldlM_simple (n : Nat) : ∀ (ks : List Tok) (acc : Str), (∀ k ∈ ks, simple k = true) →
    ks.foldlM (fun acc t => do pure (acc ++ (← valueF (n + 1) t))) acc =
      (.ok (acc ++ ks.flatMap termVal) : EPy Str)
  | [], acc, _ => by simp; rfl
  | k :: ks, acc, h => by
    have hk := h k (by simp)
    have hv : valueF (n + 1) k = .ok (termVal k) := by
      match k, hk with
      | .term .ws s ty d, _ => rfl
      | .term .val s ty d, _ => rfl
    have ih := foldlM_simple n ks (acc ++ termVal k) (fun x hx => h x (by simp [hx]))
    simp only [bind, Except.bind, pure, Except.pure] at ih
    rw [List.foldlM_cons]
    simp only [hv, bind, Except.bind, pure, Except.pure]
    rw [ih]
    simp

theorem value_unstructured (ty : String) (ks : List Tok) (ds : List Defect)
    (atts : List (String × AV)) (h : ∀ k ∈ ks, simple k = true) :
    (Tok.node .unstructured ty ks ds atts).value = .ok (ks.flatMap termVal) := by
  simp only [Tok.value, Tok.size]
  rw [valueF]
  · have := foldlM_simple (sizeL ks) ks [] h
    simpa using this
  all_goals (intro h; cases h)

theorem unstructuredSpec_proven : UnstructuredSpec := by
  refine ⟨fun cfg v n hs hn => unstructLoop_total hs n v _ hn, ?_⟩
  intro cfg v n t hc h
  obtain ⟨ks', rfl, hsim, hstr, hval⟩ :=
    unstructLoop_caught hc n v "unstructured" [] [] [] t h
  refine ⟨?_, ?_⟩
  · simpa [Tok.str] using hstr
  · rw [value_unstructured _ _ _ _ (by simpa using hsim)]
    simpa using hval

end PyLean.TextLibs.Email
