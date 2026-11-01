import PyLean.TextLibs.TextwrapModel

/-!
`textwrap`: what `_wrap_chunks` does for any chunks. Width and termination need room for the text, so
the broad statements are refuted and the narrowed ones proven. `bodies` removes the indents, and `vw`
is the text that has to survive: all of it, or with `drop_whitespace` all but the whitespace.
-/

namespace PyLean.TextLibs.Textwrap

open PyLean

theorem lenOf_append (a b : Textwrap.L) : lenOf (a ++ b) = lenOf a + lenOf b := by
  induction a with
  | nil => simp [lenOf]
  | cons x r ih => simp [lenOf, ih]; omega

theorem lenOf_reverse (a : Textwrap.L) : lenOf a.reverse = lenOf a := by
  induction a with
  | nil => rfl
  | cons x r ih => simp [lenOf, lenOf_append, ih]; omega

theorem lenOf_flatten (a : Textwrap.L) : a.flatten.length = lenOf a := by
  induction a with
  | nil => rfl
  | cons x r ih => simp [lenOf, ih]

/-- The text that has to survive. -/
def vw (t : TW) (s : List Nat) : List Nat :=
  if t.dropWs then s.filter (fun c => !PyLean.UnicodeObj.isSpace c) else s

/-- The chunks that have to survive. -/
def vwc (t : TW) (l : Textwrap.L) : Textwrap.L := if t.dropWs then l.filter (fun c => !blank c) else l

theorem vw_append (t : TW) (a b : List Nat) : vw t (a ++ b) = vw t a ++ vw t b := by
  unfold vw; split <;> simp

theorem vwc_append (t : TW) (a b : Textwrap.L) : vwc t (a ++ b) = vwc t a ++ vwc t b := by
  unfold vwc; split <;> simp

theorem vw_blank (t : TW) (h : t.dropWs = true) (x : List Nat) (hb : blank x = true) : vw t x = [] := by
  simp only [vw, h, if_true]
  simp only [List.filter_eq_nil_iff]
  simp only [blank, List.all_eq_true] at hb
  intro c hc
  simp [hb c hc]

theorem vwc_blank (t : TW) (h : t.dropWs = true) (x : List Nat) (hb : blank x = true) : vwc t [x] = [] := by
  simp [vwc, h, hb]

/-! ### The stages of one line -/

theorem fill_spec (w : Int) (chunks cur : Textwrap.L) (n : Nat) :
    ∃ taken rest, fill w chunks cur n = (cur ++ taken, n + lenOf taken, rest) ∧ chunks = taken ++ rest ∧
      ((n : Int) ≤ w → ((n + lenOf taken : Nat) : Int) ≤ w) ∧
      (∀ c r, rest = c :: r → w < ((n + lenOf taken + c.length : Nat) : Int)) ∧
      (w < n → taken = []) := by
  induction chunks generalizing cur n with
  | nil => exact ⟨[], [], by simp [fill, lenOf], by simp, by simp [lenOf], by simp, by simp⟩
  | cons c r ih =>
    by_cases h : ((n + c.length : Nat) : Int) ≤ w
    · obtain ⟨tk, rs, h1, h2, h3, h4, _⟩ := ih (cur ++ [c]) (n + c.length)
      refine ⟨c :: tk, rs, ?_, by simp [← h2], ?_, ?_, ?_⟩
      · simp only [fill, if_pos h, h1]
        simp [lenOf, Nat.add_assoc]
      · intro _
        have := h3 h
        simp only [lenOf]
        omega
      · intro c' r' he
        have := h4 c' r' he
        simp only [lenOf]
        omega
      · intro hlt
        omega
    · refine ⟨[], c :: r, ?_, by simp, ?_, ?_, by simp⟩
      · simp only [fill, if_neg h]
        simp [lenOf]
      · intro hn; simpa [lenOf] using hn
      · intro c' r' he
        cases he
        simp only [lenOf]
        omega

theorem rfindHyphen_le (pre : List Nat) (h : Nat) (hp : pre ≠ []) (hr : rfindHyphen pre = some h) :
    h + 1 ≤ pre.length := by
  have : 0 < pre.length := List.length_pos_iff.mpr hp
  simp only [rfindHyphen, Option.map_eq_some_iff] at hr
  obtain ⟨i, _, rfl⟩ := hr
  omega

theorem cutEnd_bounds (t : TW) (c : List Nat) (s : Nat) (hs : 1 ≤ s) :
    1 ≤ cutEnd t c s ∧ cutEnd t c s ≤ s := by
  unfold cutEnd
  split
  · rename_i h
    have hl : c.length > s := by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.2
    split
    · rename_i hy hr
      split
      · have hne : c.take s ≠ [] := by
          intro he
          have := congrArg List.length he
          simp only [List.length_take, List.length_nil] at this
          omega
        have := rfindHyphen_le _ _ hne hr
        simp only [List.length_take] at this
        omega
      · omega
    · omega
  · omega

theorem handleLong_cases (t : TW) (c : List Nat) (r cur : Textwrap.L) (n : Nat) (w : Int) :
    (t.breakLong = true ∧ spaceLeft n w > 0 ∧ ∃ e : Nat, 1 ≤ e ∧ (e : Int) ≤ spaceLeft n w ∧
      handleLong t c r cur n w = (c.drop e :: r, cur ++ [c.take e])) ∨
    ((t.breakLong = false ∨ spaceLeft n w ≤ 0) ∧ cur = [] ∧ handleLong t c r cur n w = (r, [c])) ∨
    ((t.breakLong = false ∨ spaceLeft n w ≤ 0) ∧ cur ≠ [] ∧ handleLong t c r cur n w = (c :: r, cur)) := by
  by_cases h : t.breakLong = true ∧ spaceLeft n w > 0
  · left
    obtain ⟨h1, h2⟩ := h
    have hs : 1 ≤ (spaceLeft n w).toNat := by omega
    have := cutEnd_bounds t c _ hs
    refine ⟨h1, h2, cutEnd t c (spaceLeft n w).toNat, this.1, by omega, ?_⟩
    simp [handleLong, h1, h2]
  · right
    have h' : t.breakLong = false ∨ spaceLeft n w ≤ 0 := by
      cases hb : t.breakLong with
      | false => exact .inl rfl
      | true =>
        right
        have : ¬ spaceLeft n w > 0 := fun hp => h ⟨hb, hp⟩
        omega
    have hif : (t.breakLong && decide (spaceLeft n w > 0)) = false := by
      rcases h' with h' | h'
      · simp [h']
      · have : ¬ spaceLeft n w > 0 := by omega
        simp [this]
    by_cases hc : cur = []
    · left
      subst hc
      exact ⟨h', rfl, by simp [handleLong, hif]⟩
    · right
      refine ⟨h', hc, ?_⟩
      have : cur.isEmpty = false := by cases cur <;> simp_all
      simp [handleLong, hif, this]

theorem dropTail_spec (t : TW) (cur : Textwrap.L) (n : Nat) (hn : n = lenOf cur) :
    (dropTail t cur n).2 = lenOf (dropTail t cur n).1 ∧ (dropTail t cur n).2 ≤ n ∧
    vw t (dropTail t cur n).1.flatten = vw t cur.flatten ∧
    vwc t (dropTail t cur n).1 = vwc t cur ∧
    (dropTail t cur n).1.length ≤ cur.length := by
  unfold dropTail
  split
  · rename_i h
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨hd, hne⟩, hb⟩ := h
    rcases List.eq_nil_or_concat cur with rfl | ⟨p, a, he⟩
    · simp at hne
    · rw [List.concat_eq_append] at he
      subst he
      have hb' : blank a = true := by simpa using hb
      have hg : (p ++ [a]).getLastD [] = a := by simp
      simp only [List.dropLast_concat, hg]
      refine ⟨?_, by omega, ?_, ?_, by simp⟩
      · simp only [hn, lenOf_append, lenOf]
        omega
      · simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil, vw_append,
          vw_blank t hd a hb']
      · simp only [vwc_append, vwc_blank t hd a hb', List.append_nil]
  · exact ⟨hn, Nat.le_refl _, rfl, rfl, Nat.le_refl _⟩

theorem startChunks_spec (t : TW) (lines chunks : Textwrap.L) :
    vw t (startChunks t lines chunks).flatten = vw t chunks.flatten ∧
    vwc t (startChunks t lines chunks) = vwc t chunks ∧
    size (startChunks t lines chunks) ≤ size chunks := by
  cases chunks with
  | nil => exact ⟨rfl, rfl, Nat.le_refl _⟩
  | cons c r =>
    simp only [startChunks]
    split
    · rename_i h
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
      obtain ⟨⟨hd, hb⟩, _⟩ := h
      refine ⟨?_, ?_, ?_⟩
      · simp [vw_append, vw_blank t hd c hb]
      · have : c :: r = [c] ++ r := rfl
        rw [this, vwc_append, vwc_blank t hd c hb]; rfl
      · simp only [size, lenOf, List.length_cons]; omega
    · exact ⟨rfl, rfl, Nat.le_refl _⟩

theorem size_append (a b : Textwrap.L) : size (a ++ b) = size a + size b := by
  simp only [size, lenOf_append, List.length_append]; omega

theorem size_cons_pos (c : List Nat) (r : Textwrap.L) : 2 ≤ size (c :: r) := by
  simp only [size, List.length_cons]; omega

theorem longStep_spec (t : TW) (w : Int) (cur rs : Textwrap.L) (n : Nat) (hn : n = lenOf cur)
    (hcur : (n : Int) ≤ w ∨ cur = [])
    (hstop : ∀ c r, rs = c :: r → w < ((n + c.length : Nat) : Int)) :
    (longStep t w cur n rs).2.2 = lenOf (longStep t w cur n rs).2.1 ∧
    (longStep t w cur n rs).2.1.flatten ++ (longStep t w cur n rs).1.flatten = cur.flatten ++ rs.flatten ∧
    (t.breakLong = false → (longStep t w cur n rs).2.1 ++ (longStep t w cur n rs).1 = cur ++ rs) ∧
    (t.breakLong = false →
      (longStep t w cur n rs).2.1.length ≤ 1 ∨ ((longStep t w cur n rs).2.2 : Int) ≤ w) ∧
    (t.breakLong = true → 1 ≤ w → ((longStep t w cur n rs).2.2 : Int) ≤ w) ∧
    (0 ≤ w → size (longStep t w cur n rs).1 ≤ size rs ∧
      (cur = [] → rs ≠ [] → size (longStep t w cur n rs).1 < size rs)) := by
  have hle : cur ≠ [] → (n : Int) ≤ w := fun hc => by
    rcases hcur with h | h
    · exact h
    · exact absurd h hc
  cases rs with
  | nil =>
    have hs : longStep t w cur n [] = ([], cur, n) := rfl
    rw [hs]
    dsimp only
    refine ⟨hn, rfl, fun _ => rfl, ?_, ?_, ?_⟩
    · intro _
      by_cases hc : cur = []
      · subst hc; simp
      · right; exact hle hc
    · intro _ h1
      by_cases hc : cur = []
      · subst hc
        simp only [lenOf] at hn
        omega
      · exact hle hc
    · intro _
      exact ⟨Nat.le_refl _, by simp⟩
  | cons c r =>
    by_cases hlong : (c.length : Int) > w
    · have hl0 : longStep t w cur n (c :: r) = ((handleLong t c r cur n w).1, (handleLong t c r cur n w).2,
          lenOf (handleLong t c r cur n w).2) := by simp only [longStep, if_pos hlong]
      rw [hl0]
      rcases handleLong_cases t c r cur n w with ⟨hb, hsp, e, he1, he2, hh⟩ | ⟨hs, hc, hh⟩ | ⟨hs, hc, hh⟩
      · rw [hh]
        dsimp only
        have hlen : (c.drop e).length + (c.take e).length = c.length := by
          simp only [List.length_drop, List.length_take]; omega
        refine ⟨rfl, ?_, by simp [hb], by simp [hb], ?_, ?_⟩
        · simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]
          rw [← List.append_assoc (c.take e), List.take_append_drop]
        · intro _ h1
          simp only [lenOf_append, lenOf, ← hn]
          have : spaceLeft n w = w - n := by simp only [spaceLeft]; rw [if_neg (by omega)]
          simp only [List.length_take]
          omega
        · intro h0
          have hc0 : 0 < c.length := by omega
          have : size (c.drop e :: r) < size (c :: r) := by
            simp only [size, lenOf, List.length_cons, List.length_drop]
            omega
          exact ⟨Nat.le_of_lt this, fun _ _ => this⟩
      · subst hc
        rw [hh]
        dsimp only
        simp only [lenOf] at hn
        refine ⟨rfl, by simp, by simp, by simp, ?_, ?_⟩
        · intro hb h1
          have : spaceLeft n w = w - n := by simp only [spaceLeft]; rw [if_neg (by omega)]
          rcases hs with hs | hs
          · simp [hb] at hs
          · omega
        · intro _
          have : size r < size (c :: r) := by
            simp only [size, lenOf, List.length_cons]; omega
          exact ⟨Nat.le_of_lt this, fun _ _ => this⟩
      · rw [hh]
        dsimp only
        rw [← hn]
        refine ⟨rfl, rfl, by simp, fun _ => .inr (hle hc), fun _ _ => hle hc, fun _ => ⟨Nat.le_refl _, fun h => absurd h hc⟩⟩
    · have hl0 : longStep t w cur n (c :: r) = (c :: r, cur, n) := by simp only [longStep, if_neg hlong]
      rw [hl0]
      dsimp only
      refine ⟨hn, rfl, by simp, ?_, ?_, ?_⟩
      · intro _
        by_cases hc : cur = []
        · subst hc; simp
        · right; exact hle hc
      · intro _ h1
        by_cases hc : cur = []
        · subst hc
          simp only [lenOf] at hn
          omega
        · exact hle hc
      · intro _
        refine ⟨Nat.le_refl _, ?_⟩
        intro hc _
        subst hc
        simp only [lenOf] at hn
        have := hstop c r rfl
        omega

/-- What one pass does, for any chunks. -/
theorem lineOf_spec (t : TW) (lines chunks cur ch : Textwrap.L) (n : Nat)
    (h : lineOf t lines chunks = (cur, n, ch)) :
    n = lenOf cur ∧
    vw t (cur.flatten ++ ch.flatten) = vw t chunks.flatten ∧
    (t.breakLong = false → vwc t (cur ++ ch) = vwc t chunks) ∧
    (t.breakLong = false → cur.length ≤ 1 ∨ (n : Int) ≤ widthOf t lines) ∧
    (t.breakLong = true → 1 ≤ widthOf t lines → (n : Int) ≤ widthOf t lines) ∧
    (0 ≤ widthOf t lines → chunks ≠ [] → size ch < size chunks) := by
  obtain ⟨h1, h2, h3⟩ := startChunks_spec t lines chunks
  obtain ⟨tk, rs, hf, he, hw, hstop, hemp⟩ := fill_spec (widthOf t lines) (startChunks t lines chunks) [] 0
  have hn0 : (0 + lenOf tk) = lenOf tk := by omega
  simp only [List.nil_append, hn0] at hf hw hstop
  have hcur : ((lenOf tk : Nat) : Int) ≤ widthOf t lines ∨ tk = [] := by
    by_cases hz : (0 : Int) ≤ widthOf t lines
    · exact .inl (hw hz)
    · exact .inr (hemp (by omega))
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := longStep_spec t (widthOf t lines) tk rs (lenOf tk) rfl hcur hstop
  have hline : lineOf t lines chunks =
      ((dropTail t (longStep t (widthOf t lines) tk (lenOf tk) rs).2.1
          (longStep t (widthOf t lines) tk (lenOf tk) rs).2.2).1,
       (dropTail t (longStep t (widthOf t lines) tk (lenOf tk) rs).2.1
          (longStep t (widthOf t lines) tk (lenOf tk) rs).2.2).2,
       (longStep t (widthOf t lines) tk (lenOf tk) rs).1) := by
    simp [lineOf, hf]
  rw [hline] at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  obtain ⟨d1, d2, d3, d4, d5⟩ := dropTail_spec t _ _ b1
  refine ⟨d1, ?_, ?_, ?_, ?_, ?_⟩
  · rw [vw_append, d3, ← vw_append, b2, ← List.flatten_append, ← he, h1]
  · intro hb
    rw [vwc_append, d4, ← vwc_append, b3 hb, ← he, h2]
  · intro hb
    rcases b4 hb with h' | h'
    · exact .inl (by omega)
    · exact .inr (by omega)
  · intro hb hw1
    have := b5 hb hw1
    omega
  · intro hw0 hne
    obtain ⟨b61, b62⟩ := b6 hw0
    cases rs with
    | nil =>
      cases chunks with
      | nil => exact absurd rfl hne
      | cons c r =>
        have := size_cons_pos c r
        have hz : size [] = 0 := rfl
        rw [hz] at b61
        omega
    | cons c r =>
      by_cases ht : tk = []
      · subst ht
        have := b62 rfl (by simp)
        simp only [List.nil_append] at he
        rw [he] at h3
        omega
      · obtain ⟨x, y, rfl⟩ := List.exists_cons_of_ne_nil ht
        have h5 := size_cons_pos x y
        rw [he, size_append] at h3
        omega

/-! ### The outer loop -/

theorem loop_ind (t : TW) (P : Textwrap.L → Textwrap.L → Prop) (Q : Textwrap.L → Prop)
    (stop : ∀ lines, P lines [] → Q lines)
    (skip : ∀ lines c r n ch, P lines (c :: r) → lineOf t lines (c :: r) = ([], n, ch) → P lines ch)
    (push : ∀ lines c r cur n ch, cur ≠ [] → P lines (c :: r) → lineOf t lines (c :: r) = (cur, n, ch) →
      fits t lines ch n = true → P (lines ++ [indentOf t lines ++ cur.flatten]) ch)
    (trunc : ∀ lines c r cur n ch, cur ≠ [] → P lines (c :: r) → lineOf t lines (c :: r) = (cur, n, ch) →
      fits t lines ch n = false →
      Q (placeLoop t (indentOf t lines) lines (widthOf t lines) cur.reverse n)) :
    ∀ fuel lines chunks ls, P lines chunks → loop t fuel lines chunks = .ok ls → Q ls := by
  intro fuel
  induction fuel with
  | zero =>
    intro lines chunks ls _ h
    simp [loop] at h
  | succ f ih =>
    intro lines chunks ls hp h
    cases chunks with
    | nil =>
      simp only [loop] at h
      cases h
      exact stop _ hp
    | cons c r =>
      rcases hl : lineOf t lines (c :: r) with ⟨cur, n, ch⟩
      simp only [loop, hl] at h
      by_cases hc : cur = []
      · subst hc
        simp only [List.isEmpty_nil, if_true] at h
        exact ih _ _ _ (skip _ _ _ _ _ hp hl) h
      · have hce : cur.isEmpty = false := by cases cur <;> simp_all
        simp only [hce, Bool.false_eq_true, if_false] at h
        cases hfit : fits t lines ch n with
        | true =>
          simp only [hfit, if_true] at h
          exact ih _ _ _ (push _ _ _ _ _ _ hc hp hl hfit) h
        | false =>
          simp only [hfit, Bool.false_eq_true, if_false] at h
          cases h
          exact trunc _ _ _ _ _ _ hc hp hl hfit

theorem loop_total (t : TW) (hw : ∀ lines, 0 ≤ widthOf t lines) :
    ∀ fuel lines chunks, size chunks < fuel → ∃ ls, loop t fuel lines chunks = .ok ls := by
  intro fuel
  induction fuel with
  | zero => intro _ _ h; omega
  | succ f ih =>
    intro lines chunks hs
    cases chunks with
    | nil => exact ⟨lines, by simp [loop]⟩
    | cons c r =>
      rcases hl : lineOf t lines (c :: r) with ⟨cur, n, ch⟩
      have := (lineOf_spec t lines _ cur ch n hl).2.2.2.2.2 (hw lines) (by simp)
      simp only [loop, hl]
      by_cases hc : cur = []
      · subst hc
        simp only [List.isEmpty_nil, if_true]
        exact ih _ _ (by omega)
      · have hce : cur.isEmpty = false := by cases cur <;> simp_all
        simp only [hce, Bool.false_eq_true, if_false]
        cases hfit : fits t lines ch n with
        | true =>
          simp only [hfit, if_true]
          exact ih _ _ (by omega)
        | false => simp

/-- The indents with the text removed. -/
def bodies (t : TW) : Textwrap.L → Textwrap.L
  | [] => []
  | l :: r => l.drop t.initial.length :: r.map (·.drop t.subsequent.length)

theorem bodies_push (t : TW) (lines : Textwrap.L) (x : List Nat) :
    bodies t (lines ++ [indentOf t lines ++ x]) = bodies t lines ++ [x] := by
  cases lines with
  | nil => simp [bodies, indentOf]
  | cons a r => simp [bodies, indentOf]

theorem placeLoop_end (t : TW) (ind : List Nat) (lines : Textwrap.L) (w : Int) :
    ∀ rcur n, ∃ p, (placeLoop t ind lines w rcur n).getLast? = some (p ++ lstrip t.placeholder) := by
  have hph : t.placeholder = t.placeholder.takeWhile PyLean.UnicodeObj.isSpace ++ lstrip t.placeholder :=
    (List.takeWhile_append_dropWhile).symm
  intro rcur
  induction rcur with
  | nil =>
    intro n
    simp only [placeLoop]
    split
    · rename_i last _
      split
      · refine ⟨rstrip last ++ t.placeholder.takeWhile PyLean.UnicodeObj.isSpace, ?_⟩
        rw [List.append_assoc, ← hph]
        simp
      · exact ⟨ind, by simp⟩
    · exact ⟨ind, by simp⟩
  | cons x rest ih =>
    intro n
    simp only [placeLoop]
    split
    · refine ⟨ind ++ (x :: rest).reverse.flatten ++ t.placeholder.takeWhile PyLean.UnicodeObj.isSpace, ?_⟩
      have : ((x :: rest).reverse ++ [t.placeholder]).flatten =
          (x :: rest).reverse.flatten ++ t.placeholder := by simp
      rw [this]
      simp only [List.getLast?_append, List.append_assoc]
      rw [← hph]
      simp
    · exact ih _

/-- Nothing but whitespace is lost, unless `max_lines` cut the text, and then the placeholder ends
the output. Holds for all indents, and `loop_total` says when the loop returns. -/
theorem loop_content (t : TW) (chunks₀ : Textwrap.L) (fuel : Nat) (ls : Textwrap.L)
    (h : loop t fuel [] chunks₀ = .ok ls) :
    vw t (bodies t ls).flatten = vw t chunks₀.flatten ∨
      (t.maxLines ≠ none ∧ ∃ p, ls.getLast? = some (p ++ lstrip t.placeholder)) := by
  refine loop_ind t
    (fun lines chunks => vw t (bodies t lines).flatten ++ vw t chunks.flatten = vw t chunks₀.flatten)
    (fun ls => vw t (bodies t ls).flatten = vw t chunks₀.flatten ∨
      (t.maxLines ≠ none ∧ ∃ p, ls.getLast? = some (p ++ lstrip t.placeholder)))
    ?_ ?_ ?_ ?_ fuel [] chunks₀ ls ?_ h
  · intro lines hp
    left
    simpa [vw] using hp
  · intro lines c r n ch hp hl
    have := (lineOf_spec t lines _ [] ch n hl).2.1
    rw [← hp, ← this]
    simp
  · intro lines c r cur n ch _ hp hl _
    have := (lineOf_spec t lines _ cur ch n hl).2.1
    rw [bodies_push, ← hp, ← this]
    simp [vw_append]
  · intro lines c r cur n ch _ _ _ hf
    right
    refine ⟨?_, placeLoop_end t _ _ _ _ _⟩
    intro hm
    simp [fits, hm] at hf
  · simp [bodies, vw]

/-! ### `max_lines` -/

/-- `chunks` is what the check of `Lib/textwrap.py:313-316` lets through. -/
def Done (t : TW) (chunks : Textwrap.L) : Prop :=
  chunks = [] ∨ (t.dropWs = true ∧ ∃ b, chunks = [b] ∧ blank b = true)

def MaxInv (t : TW) (m : Int) (lines chunks : Textwrap.L) : Prop :=
  lines = [] ∨ (lines.length : Int) < m ∨ (Done t chunks ∧ (lines.length : Int) ≤ max m 1)

theorem done_line (t : TW) (lines : Textwrap.L) (b : List Nat) (hd : t.dropWs = true)
    (hb : blank b = true) (hne : lines ≠ []) : lineOf t lines [b] = ([], 0, []) := by
  have hl : lines.isEmpty = false := by cases lines <;> simp_all
  simp [lineOf, startChunks, hd, hb, hl, fill, longStep, dropTail]

/-- After `lines ≠ []`, chunks that are done give no line. -/
theorem done_empty (t : TW) (lines : Textwrap.L) (c : List Nat) (r cur ch : Textwrap.L) (n : Nat)
    (hd : Done t (c :: r)) (hne : lines ≠ []) (hl : lineOf t lines (c :: r) = (cur, n, ch)) :
    cur = [] ∧ ch = [] := by
  rcases hd with hd | ⟨hd, b, he, hb⟩
  · simp at hd
  · simp only [List.cons.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    rw [done_line t lines c hd hb hne] at hl
    simp only [Prod.mk.injEq] at hl
    exact ⟨hl.1.symm, hl.2.2.symm⟩

theorem fits_some (t : TW) (m : Int) (hm : t.maxLines = some m) (lines ch : Textwrap.L) (n : Nat)
    (h : fits t lines ch n = true) : (lines.length + 1 : Int) < m ∨ Done t ch := by
  simp only [fits, hm, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h
  rcases h with h | ⟨h, _⟩
  · exact .inl h
  · right
    rcases h with h | ⟨⟨h1, h2⟩, h3⟩
    · left; cases ch <;> simp_all
    · right
      cases ch with
      | nil => simp at h2
      | cons a b =>
        cases b with
        | nil => exact ⟨h1, a, rfl, by simpa using h3⟩
        | cons _ _ => simp at h2

theorem fits_false (t : TW) (lines ch : Textwrap.L) (n : Nat) (h : fits t lines ch n = false) :
    ∃ m, t.maxLines = some m ∧ m ≤ (lines.length + 1 : Int) := by
  cases hm : t.maxLines with
  | none => simp [fits, hm] at h
  | some m =>
    simp only [fits, hm, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
    exact ⟨m, rfl, by omega⟩

theorem maxInv_skip (t : TW) (m : Int) (lines : Textwrap.L) (c : List Nat) (r ch : Textwrap.L) (n : Nat)
    (hp : MaxInv t m lines (c :: r)) (hl : lineOf t lines (c :: r) = ([], n, ch)) :
    MaxInv t m lines ch := by
  rcases hp with hp | hp | ⟨hd, hb⟩
  · exact .inl hp
  · exact .inr (.inl hp)
  · by_cases hne : lines = []
    · exact .inl hne
    · have := (done_empty t lines c r [] ch n hd hne hl).2
      subst this
      exact .inr (.inr ⟨.inl rfl, hb⟩)

theorem maxInv_len (t : TW) (m : Int) (lines : Textwrap.L) (c : List Nat) (r cur ch : Textwrap.L) (n : Nat)
    (hc : cur ≠ []) (hp : MaxInv t m lines (c :: r)) (hl : lineOf t lines (c :: r) = (cur, n, ch)) :
    (lines.length + 1 : Int) ≤ max m 1 := by
  rcases hp with hp | hp | ⟨hd, hb⟩
  · subst hp; simpa using Int.le_max_right m 1
  · have := Int.le_max_left m 1
    omega
  · by_cases hne : lines = []
    · subst hne; simpa using Int.le_max_right m 1
    · exact absurd (done_empty t lines c r cur ch n hd hne hl).1 hc

theorem maxInv_push (t : TW) (m : Int) (hm : t.maxLines = some m) (lines : Textwrap.L) (c : List Nat)
    (r cur ch : Textwrap.L) (n : Nat) (x : List Nat) (hc : cur ≠ [])
    (hp : MaxInv t m lines (c :: r)) (hl : lineOf t lines (c :: r) = (cur, n, ch))
    (hf : fits t lines ch n = true) : MaxInv t m (lines ++ [x]) ch := by
  have := maxInv_len t m lines c r cur ch n hc hp hl
  rcases fits_some t m hm lines ch n hf with h | h
  · right; left; simp; omega
  · right; right
    refine ⟨h, ?_⟩
    simp
    omega

theorem placeLoop_len (t : TW) (ind : List Nat) (lines : Textwrap.L) (w : Int) :
    ∀ rcur n, (placeLoop t ind lines w rcur n).length ≤ lines.length + 1 := by
  intro rcur
  induction rcur with
  | nil =>
    intro n
    simp only [placeLoop]
    split
    · split <;> simp <;> omega
    · simp
  | cons x rest ih =>
    intro n
    simp only [placeLoop]
    split
    · simp
    · exact ih _

/-- At most `max(max_lines, 1)` lines: with `max_lines` below 1, one short text still gets its line. -/
theorem loop_maxLines (t : TW) (m : Int) (hm : t.maxLines = some m) (chunks : Textwrap.L) (fuel : Nat)
    (ls : Textwrap.L) (h : loop t fuel [] chunks = .ok ls) : (ls.length : Int) ≤ max m 1 := by
  refine loop_ind t (MaxInv t m) (fun ls => (ls.length : Int) ≤ max m 1) ?_ ?_ ?_ ?_ fuel [] chunks ls
    (.inl rfl) h
  · intro lines hp
    rcases hp with hp | hp | ⟨_, hb⟩
    · subst hp; simp; omega
    · omega
    · exact hb
  · intro lines c r n ch hp hl
    exact maxInv_skip t m lines c r ch n hp hl
  · intro lines c r cur n ch hc hp hl hf
    exact maxInv_push t m hm lines c r cur ch n _ hc hp hl hf
  · intro lines c r cur n ch hc hp hl _
    have h1 := maxInv_len t m lines c r cur ch n hc hp hl
    have h2 := placeLoop_len t (indentOf t lines) lines (widthOf t lines) cur.reverse n
    omega

/-! ### Width -/

theorem placeLoop_width (t : TW) (ind : List Nat) (lines : Textwrap.L) (w : Int)
    (hw : (ind.length : Int) + w = t.width)
    (hl : ∀ l ∈ lines, (l.length : Int) ≤ t.width)
    (hp : ((ind.length + (lstrip t.placeholder).length : Nat) : Int) ≤ t.width) :
    ∀ (rcur : Textwrap.L) (n : Int), n = lenOf rcur →
      ∀ l ∈ placeLoop t ind lines w rcur n, (l.length : Int) ≤ t.width := by
  have hend : ∀ l ∈ lines ++ [ind ++ lstrip t.placeholder], (l.length : Int) ≤ t.width := by
    intro l hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hl l hm
    · simp only [List.mem_singleton] at hm
      subst hm
      simpa using hp
  intro rcur
  induction rcur with
  | nil =>
    intro n _
    simp only [placeLoop]
    split
    · split
      · rename_i hg
        intro l hm
        rcases List.mem_append.mp hm with hm | hm
        · rw [List.dropLast_eq_take] at hm
          exact hl l (List.mem_of_mem_take hm)
        · simp only [List.mem_singleton] at hm
          subst hm
          simpa using hg
      · exact hend
    · exact hend
  | cons x rest ih =>
    intro n hn
    simp only [placeLoop]
    split
    · rename_i hg
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
      intro l hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hl l hm
      · simp only [List.mem_singleton] at hm
        subst hm
        have h1 := lenOf_flatten ((x :: rest).reverse ++ [t.placeholder])
        have h2 := lenOf_reverse (x :: rest)
        rw [lenOf_append] at h1
        simp only [List.length_append, h1, h2, lenOf]
        simp only [lenOf] at hn
        have := hg.2
        omega
    · exact ih _ (by simp only [lenOf] at hn; omega)

theorem indent_len (t : TW) (lines : Textwrap.L) :
    indentOf t lines = t.initial ∨ indentOf t lines = t.subsequent := by
  unfold indentOf; split <;> simp

/-- The check of `Lib/textwrap.py:254-260` covers the indent of the line that gets the placeholder. -/
theorem trunc_indent (t : TW) (m : Int) (hm : t.maxLines = some m) (hb : tooBig t = false)
    (lines : Textwrap.L) (c : List Nat) (r cur ch : Textwrap.L) (n : Nat) (hc : cur ≠ [])
    (hp : MaxInv t m lines (c :: r)) (hl : lineOf t lines (c :: r) = (cur, n, ch))
    (hle : m ≤ (lines.length + 1 : Int)) :
    (((indentOf t lines).length + (lstrip t.placeholder).length : Nat) : Int) ≤ t.width := by
  simp only [tooBig, hm, decide_eq_false_iff_not] at hb
  have hi : indentOf t lines = if m > 1 then t.subsequent else t.initial := by
    by_cases hne : lines = []
    · subst hne
      have : ¬ m > 1 := by simp at hle; omega
      simp [indentOf, this]
    · have hL : lines.isEmpty = false := by cases lines <;> simp_all
      have h1 : 0 < lines.length := List.length_pos_iff.mpr hne
      have : m > 1 := by
        rcases hp with hp | hp | ⟨hd, _⟩
        · exact absurd hp hne
        · omega
        · exact absurd (done_empty t lines c r cur ch n hd hne hl).1 hc
      simp [indentOf, this, hL]
  rw [hi]
  omega

/-- Every line is within `width`, given `break_long_words` and an indent that leaves room. -/
theorem loop_width (t : TW) (hb : t.breakLong = true) (hi : (t.initial.length : Int) < t.width)
    (hs : (t.subsequent.length : Int) < t.width) (hbig : tooBig t = false) (chunks : Textwrap.L) (fuel : Nat)
    (ls : Textwrap.L) (h : loop t fuel [] chunks = .ok ls) : ∀ l ∈ ls, (l.length : Int) ≤ t.width := by
  have hw1 : ∀ lines, 1 ≤ widthOf t lines := by
    intro lines
    rcases indent_len t lines with he | he <;> simp only [widthOf, he] <;> omega
  refine loop_ind t
    (fun lines chunks => (∀ l ∈ lines, (l.length : Int) ≤ t.width) ∧
      ∀ m, t.maxLines = some m → MaxInv t m lines chunks)
    (fun ls => ∀ l ∈ ls, (l.length : Int) ≤ t.width) ?_ ?_ ?_ ?_ fuel [] chunks ls
    ⟨by simp, fun _ _ => .inl rfl⟩ h
  · intro lines hp
    exact hp.1
  · intro lines c r n ch hp hl
    exact ⟨hp.1, fun m hm => maxInv_skip t m lines c r ch n (hp.2 m hm) hl⟩
  · intro lines c r cur n ch hc hp hl hf
    refine ⟨?_, fun m hm => maxInv_push t m hm lines c r cur ch n _ hc (hp.2 m hm) hl hf⟩
    intro l hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hp.1 l hm
    · simp only [List.mem_singleton] at hm
      subst hm
      obtain ⟨h1, _, _, _, h5, _⟩ := lineOf_spec t lines _ cur ch n hl
      have := h5 hb (hw1 lines)
      simp only [List.length_append, lenOf_flatten, ← h1, Int.natCast_add]
      simp only [widthOf] at this
      omega
  · intro lines c r cur n ch hc hp hl hf
    obtain ⟨m, hm, hle⟩ := fits_false t lines ch n hf
    have h1 := (lineOf_spec t lines _ cur ch n hl).1
    refine placeLoop_width t _ lines _ (by simp only [widthOf]; omega) hp.1
      (trunc_indent t m hm hbig lines c r cur ch n hc (hp.2 m hm) hl hle) _ _ ?_
    rw [lenOf_reverse, h1]

/-! ### `break_long_words=False` -/

/-- No chunk is cut: the lines are runs of the chunks, and only a run of one exceeds `width`. -/
theorem loop_noBreak (t : TW) (hb : t.breakLong = false) (hm : t.maxLines = none) (chunks₀ : Textwrap.L)
    (fuel : Nat) (ls : Textwrap.L) (h : loop t fuel [] chunks₀ = .ok ls) :
    ∃ gs : List Textwrap.L, bodies t ls = gs.map List.flatten ∧ vwc t gs.flatten = vwc t chunks₀ ∧
      ∀ g ∈ gs, g.length ≤ 1 ∨ (lenOf g : Int) ≤ t.width := by
  refine loop_ind t
    (fun lines chunks => ∃ gs : List Textwrap.L, bodies t lines = gs.map List.flatten ∧
      vwc t gs.flatten ++ vwc t chunks = vwc t chunks₀ ∧
      ∀ g ∈ gs, g.length ≤ 1 ∨ (lenOf g : Int) ≤ t.width)
    (fun ls => ∃ gs : List Textwrap.L, bodies t ls = gs.map List.flatten ∧
      vwc t gs.flatten = vwc t chunks₀ ∧ ∀ g ∈ gs, g.length ≤ 1 ∨ (lenOf g : Int) ≤ t.width)
    ?_ ?_ ?_ ?_ fuel [] chunks₀ ls ?_ h
  · rintro lines ⟨gs, h1, h2, h3⟩
    exact ⟨gs, h1, by simpa [vwc] using h2, h3⟩
  · rintro lines c r n ch ⟨gs, h1, h2, h3⟩ hl
    refine ⟨gs, h1, ?_, h3⟩
    have := (lineOf_spec t lines _ [] ch n hl).2.2.1 hb
    rw [← h2, ← this]
    simp
  · rintro lines c r cur n ch _ ⟨gs, h1, h2, h3⟩ hl _
    obtain ⟨s1, _, s3, s4, _, _⟩ := lineOf_spec t lines _ cur ch n hl
    refine ⟨gs ++ [cur], ?_, ?_, ?_⟩
    · rw [bodies_push, h1]; simp
    · rw [← h2, ← s3 hb]
      simp [vwc_append]
    · intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact h3 g hg
      · simp only [List.mem_singleton] at hg
        subst hg
        rcases s4 hb with h' | h'
        · exact .inl h'
        · right
          simp only [widthOf] at h'
          omega
  · intro lines c r cur n ch _ _ _ hf
    simp [fits, hm] at hf
  · exact ⟨[], rfl, by simp [vwc], by simp⟩

/-! ### Greedy filling -/

/-- Each line is full: the next chunk would not have fitted after it, with that line's indent. `nx` is
the chunk after the last line. -/
def Greedy (t : TW) (ind : List Nat) : List Textwrap.L → Option (List Nat) → Prop
  | [], _ => True
  | [_], none => True
  | [g], some c => t.width < ((ind.length + lenOf g + c.length : Nat) : Int)
  | g :: h :: r, nx =>
    t.width < ((ind.length + lenOf g + (h.headD []).length : Nat) : Int) ∧ Greedy t t.subsequent (h :: r) nx

theorem greedy_push (t : TW) (cur : Textwrap.L) (nx : Option (List Nat)) (c : List Nat) (hh : cur.headD [] = c) :
    ∀ (gs : List Textwrap.L) (ind : List Nat), Greedy t ind gs (some c) →
      (∀ c', nx = some c' →
        t.width < (((if gs = [] then ind else t.subsequent).length + lenOf cur + c'.length : Nat) : Int)) →
      Greedy t ind (gs ++ [cur]) nx := by
  intro gs
  induction gs with
  | nil =>
    intro ind _ hs
    cases nx with
    | none => simp [Greedy]
    | some c' => simpa [Greedy] using hs c' rfl
  | cons a r ih =>
    intro ind hg hs
    cases r with
    | nil =>
      simp only [Greedy] at hg
      simp only [List.cons_append, List.nil_append, Greedy]
      refine ⟨by rw [hh]; exact hg, ?_⟩
      cases nx with
      | none => simp [Greedy]
      | some c' => simpa [Greedy] using hs c' rfl
    | cons b r =>
      simp only [Greedy] at hg
      simp only [List.cons_append, Greedy]
      refine ⟨hg.1, ih _ hg.2 ?_⟩
      intro c' hc'
      simpa using hs c' hc'

theorem longStep_stop (t : TW) (hb : t.breakLong = false) (w : Int) (cur rs : Textwrap.L) (n : Nat)
    (hn : n = lenOf cur) (hstop : ∀ c r, rs = c :: r → w < ((n + c.length : Nat) : Int)) :
    ∀ c r, (longStep t w cur n rs).1 = c :: r →
      w < (((longStep t w cur n rs).2.2 + c.length : Nat) : Int) := by
  cases rs with
  | nil => intro c r h; simp [longStep] at h
  | cons x y =>
    by_cases hlong : (x.length : Int) > w
    · have hl0 : longStep t w cur n (x :: y) = ((handleLong t x y cur n w).1, (handleLong t x y cur n w).2,
          lenOf (handleLong t x y cur n w).2) := by simp only [longStep, if_pos hlong]
      rw [hl0]
      rcases handleLong_cases t x y cur n w with ⟨hb', _⟩ | ⟨_, _, hh⟩ | ⟨_, _, hh⟩
      · simp [hb] at hb'
      · rw [hh]
        dsimp only
        intro c r _
        simp only [lenOf]
        omega
      · rw [hh]
        dsimp only
        rw [← hn]
        intro c r h
        exact hstop c r h
    · have hl0 : longStep t w cur n (x :: y) = (x :: y, cur, n) := by simp only [longStep, if_neg hlong]
      rw [hl0]
      intro c r h
      exact hstop c r h

/-- With nothing dropped and nothing cut, a line ends only because the next chunk would not fit. -/
theorem lineOf_greedy (t : TW) (hb : t.breakLong = false) (hd : t.dropWs = false)
    (lines chunks cur ch : Textwrap.L) (n : Nat) (h : lineOf t lines chunks = (cur, n, ch)) :
    ∀ c r, ch = c :: r → widthOf t lines < ((n + c.length : Nat) : Int) := by
  obtain ⟨tk, rs, hf, _, _, hstop, _⟩ := fill_spec (widthOf t lines) (startChunks t lines chunks) [] 0
  have hn0 : (0 + lenOf tk) = lenOf tk := by omega
  simp only [List.nil_append, hn0] at hf hstop
  have hs := longStep_stop t hb (widthOf t lines) tk rs (lenOf tk) rfl hstop
  have hline : lineOf t lines chunks =
      ((longStep t (widthOf t lines) tk (lenOf tk) rs).2.1,
       (longStep t (widthOf t lines) tk (lenOf tk) rs).2.2,
       (longStep t (widthOf t lines) tk (lenOf tk) rs).1) := by
    simp [lineOf, hf, dropTail, hd]
  rw [hline] at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact hs

/-- A line of chunks, with `drop_whitespace` and `break_long_words` off, in a greedy partition. -/
theorem loop_greedy (t : TW) (hb : t.breakLong = false) (hd : t.dropWs = false) (hm : t.maxLines = none)
    (chunks₀ : Textwrap.L) (fuel : Nat) (ls : Textwrap.L) (h : loop t fuel [] chunks₀ = .ok ls) :
    ∃ gs : List Textwrap.L, bodies t ls = gs.map List.flatten ∧ gs.flatten = chunks₀ ∧ Greedy t t.initial gs none := by
  have hv : ∀ l : Textwrap.L, vwc t l = l := by intro l; simp [vwc, hd]
  refine loop_ind t
    (fun lines chunks => ∃ gs : List Textwrap.L, bodies t lines = gs.map List.flatten ∧
      gs.flatten ++ chunks = chunks₀ ∧ Greedy t t.initial gs chunks.head?)
    (fun ls => ∃ gs : List Textwrap.L, bodies t ls = gs.map List.flatten ∧
      gs.flatten = chunks₀ ∧ Greedy t t.initial gs none)
    ?_ ?_ ?_ ?_ fuel [] chunks₀ ls ?_ h
  · rintro lines ⟨gs, h1, h2, h3⟩
    exact ⟨gs, h1, by simpa using h2, h3⟩
  · rintro lines c r n ch hp hl
    have := (lineOf_spec t lines _ [] ch n hl).2.2.1 hb
    simp only [hv, List.nil_append] at this
    subst this
    exact hp
  · rintro lines c r cur n ch hc ⟨gs, h1, h2, h3⟩ hl _
    obtain ⟨s1, _, s3, _, _, _⟩ := lineOf_spec t lines _ cur ch n hl
    have s3' := s3 hb
    simp only [hv] at s3'
    refine ⟨gs ++ [cur], ?_, ?_, ?_⟩
    · rw [bodies_push, h1]; simp
    · rw [← h2, ← s3']
      simp
    · have hhead : cur.headD [] = c := by
        cases cur with
        | nil => exact absurd rfl hc
        | cons a b =>
          simp only [List.cons_append, List.cons.injEq] at s3'
          simpa using s3'.1
      have hemp : (if gs = [] then t.initial else t.subsequent) = indentOf t lines := by
        by_cases hg : gs = []
        · subst hg
          have : lines = [] := by
            cases lines with
            | nil => rfl
            | cons a b => simp [bodies] at h1
          subst this
          simp [indentOf]
        · have : lines ≠ [] := by
            rintro rfl
            have : gs.map List.flatten = [] := h1.symm
            simp only [List.map_eq_nil_iff] at this
            exact hg this
          have hL : lines.isEmpty = false := by cases lines <;> simp_all
          simp [indentOf, hg, hL]
      refine greedy_push t cur ch.head? c hhead gs t.initial h3 ?_
      intro c' hc'
      obtain ⟨r', rfl⟩ : ∃ r', ch = c' :: r' := by
        cases ch with
        | nil => simp at hc'
        | cons a b => simp only [List.head?_cons, Option.some.injEq] at hc'; exact ⟨b, by rw [hc']⟩
      have := lineOf_greedy t hb hd lines _ cur _ n hl c' r' rfl
      rw [hemp, ← s1]
      simp only [widthOf] at this
      omega
  · intro lines c r cur n ch _ _ _ hf
    simp [fits, hm] at hf
  · refine ⟨[], rfl, by simp, ?_⟩
    simp [Greedy]

/-! ### The registered statements -/

/-- Every non-terminating input is ruled out: for a positive `width`, enough steps end the loop. It is
false: an indent wider than `width` leaves an empty chunk that no pass removes. -/
def WrapTerminates : Prop :=
  ∀ (t : TW) (chunks : Textwrap.L), 0 < t.width → ∃ fuel, loop t fuel [] chunks ≠ .error .modelFuel

private def t₀ : TW := { width := 1, initial := [120, 120, 120] }

private theorem stuck (f : Nat) : loop t₀ f [] [[]] = .error .modelFuel := by
  induction f with
  | zero => rfl
  | succ f ih =>
    have : lineOf t₀ [] [[]] = ([], 0, [[]]) := by decide
    simp only [loop, this]
    exact ih

theorem wrapTerminates_refuted : ¬WrapTerminates := by
  intro h
  obtain ⟨fuel, hf⟩ := h t₀ [[32]] (by decide)
  apply hf
  cases fuel with
  | zero => rfl
  | succ f =>
    have : lineOf t₀ [] [[32]] = ([], 0, [[]]) := by decide
    simp only [loop, this]
    exact stuck f

/-- Precondition, narrowing `WrapTerminates`: the indents are at most `width`, which is what the refutation
excludes. The function returns exactly when the two checks at its top pass. -/
def WrapSucceeds : Prop :=
  ∀ (t : TW) (chunks : Textwrap.L), (t.initial.length : Int) ≤ t.width → (t.subsequent.length : Int) ≤ t.width →
    ((∃ ls, wrapChunks t chunks = .ok ls) ↔ 0 < t.width ∧ tooBig t = false)

theorem wrapSucceeds_proven : WrapSucceeds := by
  intro t chunks h1 h2
  have hw : ∀ lines, 0 ≤ widthOf t lines := by
    intro lines
    rcases indent_len t lines with he | he <;> simp only [widthOf, he] <;> omega
  constructor
  · rintro ⟨ls, h⟩
    unfold wrapChunks at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · rename_i h3 h4
        exact ⟨by omega, by simpa using h4⟩
  · rintro ⟨h3, h4⟩
    have : ¬ t.width ≤ 0 := by omega
    obtain ⟨ls, hl⟩ := loop_total t hw (size chunks + 2) [] chunks (by omega)
    exact ⟨ls, by simp [wrapChunks, this, h4, hl]⟩

/-- The two checks, in order, with their messages, `Lib/textwrap.py:252-260`. -/
def WrapErrors : Prop :=
  ∀ (t : TW) (chunks : Textwrap.L),
    (t.width ≤ 0 → wrapChunks t chunks = .error (.valueError s!"invalid width {t.width} (must be > 0)")) ∧
    (0 < t.width → tooBig t = true →
      wrapChunks t chunks = .error (.valueError "placeholder too large for max width"))

theorem wrapErrors_proven : WrapErrors := by
  intro t chunks
  constructor
  · intro h
    simp [wrapChunks, h]
  · intro h h2
    have : ¬ t.width ≤ 0 := by omega
    simp [wrapChunks, this, h2]

/-- Docstring of `TextWrapper.wrap`: lines of no more than `width`, with `break_long_words` on. False
when an indent leaves no room. -/
def WrapWidthLaw : Prop :=
  ∀ (t : TW) (chunks ls : Textwrap.L), t.breakLong = true → wrapChunks t chunks = .ok ls →
    ∀ l ∈ ls, (l.length : Int) ≤ t.width

theorem wrapWidthLaw_refuted : ¬WrapWidthLaw := by
  intro h
  have := h { width := 1, initial := [32] } [[97]] [[32, 97]] rfl (by decide) [32, 97] (by simp)
  simp at this

/-- Precondition, narrowing `WrapWidthLaw`: each indent is shorter than `width`, which is what the
refutation excludes. `break_long_words` is the documented condition. -/
def WrapWidthNarrow : Prop :=
  ∀ (t : TW) (chunks ls : Textwrap.L), t.breakLong = true → (t.initial.length : Int) < t.width →
    (t.subsequent.length : Int) < t.width → wrapChunks t chunks = .ok ls →
    ∀ l ∈ ls, (l.length : Int) ≤ t.width

theorem wrapWidthNarrow_proven : WrapWidthNarrow := by
  intro t chunks ls hb hi hs h
  unfold wrapChunks at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i h4
      exact loop_width t hb hi hs (by simpa using h4) chunks _ ls h

/-- Without `max_lines`, the text of the chunks is all in the lines: exactly, or apart from whitespace
with `drop_whitespace`. No hypothesis on the indents. -/
def WrapKeepsText : Prop :=
  ∀ (t : TW) (chunks ls : Textwrap.L), t.maxLines = none → wrapChunks t chunks = .ok ls →
    vw t (bodies t ls).flatten = vw t chunks.flatten

theorem wrapKeepsText_proven : WrapKeepsText := by
  intro t chunks ls hm h
  unfold wrapChunks at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rcases loop_content t chunks _ ls h with h' | ⟨h', _⟩
      · exact h'
      · exact absurd hm h'

/-- Doc of `max_lines`: at most that many lines, and "with placeholder appearing at the end of the
output". If text was cut, the last line ends in the stripped placeholder. A `max_lines` below 1 still
lets one short text through. -/
def WrapMaxLines : Prop :=
  ∀ (t : TW) (m : Int) (chunks ls : Textwrap.L), t.maxLines = some m → wrapChunks t chunks = .ok ls →
    (ls.length : Int) ≤ max m 1 ∧
    (vw t (bodies t ls).flatten = vw t chunks.flatten ∨ ∃ p, ls.getLast? = some (p ++ lstrip t.placeholder))

theorem wrapMaxLines_proven : WrapMaxLines := by
  intro t m chunks ls hm h
  unfold wrapChunks at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · refine ⟨loop_maxLines t m hm chunks _ ls h, ?_⟩
      rcases loop_content t chunks _ ls h with h' | ⟨_, h'⟩
      · exact .inl h'
      · exact .inr h'

/-- "each chunk is indivisible (modulo 'break_long_words')": with it off, the lines are runs of the
chunks, whitespace chunks may go under `drop_whitespace`, and only a single chunk exceeds `width`. -/
def WrapNoBreak : Prop :=
  ∀ (t : TW) (chunks ls : Textwrap.L), t.breakLong = false → t.maxLines = none → wrapChunks t chunks = .ok ls →
    ∃ gs : List Textwrap.L, bodies t ls = gs.map List.flatten ∧ vwc t gs.flatten = vwc t chunks ∧
      ∀ g ∈ gs, g.length ≤ 1 ∨ (lenOf g : Int) ≤ t.width

theorem wrapNoBreak_proven : WrapNoBreak := by
  intro t chunks ls hb hm h
  unfold wrapChunks at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · exact loop_noBreak t hb hm chunks _ ls h

/-- With `break_long_words` and `drop_whitespace` off, the output is the greedy partition of the chunks:
a line ends only because the next chunk would not fit, so a list of one chunk per line fails it. -/
def WrapGreedy : Prop :=
  ∀ (t : TW) (chunks ls : Textwrap.L), t.breakLong = false → t.dropWs = false → t.maxLines = none →
    wrapChunks t chunks = .ok ls →
    ∃ gs : List Textwrap.L, bodies t ls = gs.map List.flatten ∧ gs.flatten = chunks ∧ Greedy t t.initial gs none

theorem wrapGreedy_proven : WrapGreedy := by
  intro t chunks ls hb hd hm h
  unfold wrapChunks at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · exact loop_greedy t hb hd hm chunks _ ls h

/-- `shorten`'s doc: text that fits "is returned as is". False, since the placeholder check comes first
and does not look at the text. -/
def FittingTextPasses : Prop :=
  ∀ (t : TW) (chunks : Textwrap.L), 0 < t.width →
    (((t.initial.length + lenOf chunks : Nat) : Int) ≤ t.width) → ∃ ls, wrapChunks t chunks = .ok ls

theorem fittingTextPasses_refuted : ¬FittingTextPasses := by
  intro h
  obtain ⟨ls, hl⟩ := h { width := 4, maxLines := some 1 } [[97, 98]] (by decide) (by decide)
  have : wrapChunks { width := 4, maxLines := some 1 } [[97, 98]] =
      .error (.valueError "placeholder too large for max width") := by decide
  rw [this] at hl
  simp at hl

end PyLean.TextLibs.Textwrap
