import PyLean.TextLibs.TomlModel

/-! Position and slicing lemmas for the `tomllib` model. -/

namespace PyLean.TextLibs.Toml

theorem getElem?_of_drop {src : Str} {pos c : Nat} {r : Str} (h : src.drop pos = c :: r) :
    src[pos]? = some c := by
  have : (src.drop pos)[0]? = some c := by rw [h]; rfl
  simpa [List.getElem?_drop] using this

theorem getElem?_of_drop_nil {src : Str} {pos : Nat} (h : src.drop pos = []) : src[pos]? = none := by
  have : (src.drop pos)[0]? = none := by rw [h]; rfl
  simpa [List.getElem?_drop] using this

theorem drop_add_of_drop {src : Str} {pos : Nat} {a r : Str} (h : src.drop pos = a ++ r) :
    src.drop (pos + a.length) = r := by
  have : (src.drop pos).drop a.length = r := by rw [h]; simp
  simpa [List.drop_drop, Nat.add_comm] using this

theorem drop_succ_of_drop {src : Str} {pos c : Nat} {r : Str} (h : src.drop pos = c :: r) :
    src.drop (pos + 1) = r := drop_add_of_drop (a := [c]) h

theorem sl_of_drop {src : Str} {pos : Nat} {a r : Str} (h : src.drop pos = a ++ r) :
    sl src pos (pos + a.length) = a := by
  simp [sl, h]

theorem sl_self (src : Str) (pos : Nat) : sl src pos pos = [] := by simp [sl]

theorem sl_snoc {src : Str} {start pos c : Nat} {r : Str} (hs : start ≤ pos) (h : src.drop pos = c :: r) :
    sl src start (pos + 1) = sl src start pos ++ [c] := by
  have hc := getElem?_of_drop h
  unfold sl
  rw [show pos + 1 - start = (pos - start) + 1 by omega, List.take_add_one]
  congr
  rw [List.getElem?_drop, show start + (pos - start) = pos by omega, hc]
  rfl

theorem takeWhile_append_stop {p : Nat → Bool} {a r : Str} (ha : ∀ x ∈ a, p x = true)
    (hr : ∀ x, r.head? = some x → p x = false) : (a ++ r).takeWhile p = a := by
  induction a with
  | nil =>
    cases r with
    | nil => rfl
    | cons x t => simp [List.takeWhile_cons, hr x rfl]
  | cons y t ih =>
    have hy := ha y (by simp)
    simp [List.takeWhile_cons, hy, ih (fun x hx => ha x (by simp [hx]))]

theorem skipChars_of_drop {src : Str} {pos : Nat} {p : Nat → Bool} {a r : Str}
    (h : src.drop pos = a ++ r) (ha : ∀ x ∈ a, p x = true) (hr : ∀ x, r.head? = some x → p x = false) :
    skipChars src pos p = pos + a.length := by
  simp [skipChars, h, takeWhile_append_stop ha hr]

theorem skipChars_stop {src : Str} {pos : Nat} {p : Nat → Bool}
    (hr : ∀ x, (src.drop pos).head? = some x → p x = false) : skipChars src pos p = pos := by
  have := skipChars_of_drop (src := src) (pos := pos) (a := []) (r := src.drop pos) (p := p) (by simp)
    (by simp) hr
  simpa using this

theorem startsAt_of_drop {src : Str} {pos : Nat} {p r : Str} (h : src.drop pos = p ++ r) :
    startsAt src pos p = true := by
  simp [startsAt, h]

theorem firstIdx_none {p : Nat → Bool} : ∀ {s : Str}, (∀ x ∈ s, p x = false) → firstIdx p s = none
  | [], _ => rfl
  | c :: r, h => by
    have := h c (by simp)
    simp [firstIdx, this, firstIdx_none (s := r) (fun x hx => h x (by simp [hx]))]

theorem firstIdx_append {p : Nat → Bool} {a : Str} {c : Nat} {r : Str} (ha : ∀ x ∈ a, p x = false)
    (hc : p c = true) : firstIdx p (a ++ c :: r) = some a.length := by
  induction a with
  | nil => simp [firstIdx, hc]
  | cons y t ih =>
    have hy := ha y (by simp)
    simp [firstIdx, hy, ih (fun x hx => ha x (by simp [hx]))]

theorem findSub_single_none {c : Nat} : ∀ {s : Str}, c ∉ s → findSub [c] s = none
  | [], _ => rfl
  | x :: r, h => by
    have hx : x ≠ c := fun e => h (by simp [e])
    have hr : c ∉ r := fun m => h (by simp [m])
    simp [findSub, List.isPrefixOf, hx, findSub_single_none hr, Ne.symm hx]

theorem findSub_single {c : Nat} {a r : Str} (ha : c ∉ a) : findSub [c] (a ++ c :: r) = some a.length := by
  induction a with
  | nil => simp [findSub, List.isPrefixOf]
  | cons y t ih =>
    have hy : y ≠ c := fun e => ha (by simp [e])
    have ht : c ∉ t := fun m => ha (by simp [m])
    simp [findSub, List.isPrefixOf, hy, ih ht, Ne.symm hy]

/-! ## Frames -/

theorem need_ok {α : Type} {r n : Nat} (h : n ≤ r) (x : Py α) : need r n x = x := by
  simp [need, h]

theorem need_err {α : Type} {r n : Nat} (h : r < n) (x : Py α) : need r n x = .error recErr := by
  simp [need]; omega

theorem skipUntilN_le (src : Str) (pos : Nat) (e : Str) (f : Nat → Bool) (b : Bool) :
    skipUntilN src pos e f b ≤ 2 := by
  unfold skipUntilN; split <;> omega

theorem skipCommentN_le (src : Str) (pos : Nat) : skipCommentN src pos ≤ 3 := by
  have := skipUntilN_le src (pos + 1) [10] illegalBasic false
  unfold skipCommentN; split <;> omega

theorem skipCawNAux_le (src : Str) : ∀ fuel pos, skipCawNAux src fuel pos ≤ 3
  | 0, _ => by simp [skipCawNAux]
  | fuel + 1, pos => by
    have ih := skipCawNAux_le src fuel
    have h1 := skipCommentN_le src (skipChars src pos tomlWsNl)
    simp only [skipCawNAux]
    repeat' (first | omega | exact ih _ | split | (apply Nat.max_le.mpr; constructor))

theorem skipCawN_le (src : Str) (pos : Nat) : skipCawN src pos ≤ 4 := by
  have := skipCawNAux_le src (src.length + 1) pos
  unfold skipCawN; omega

theorem parseBasicStrEscapeN_le (src : Str) (pos : Nat) (ml : Bool) : parseBasicStrEscapeN src pos ml ≤ 3 := by
  simp only [parseBasicStrEscapeN, parseHexCharN]
  repeat' (first | omega | split)

theorem basicStrNAux_le (src : Str) (ml : Bool) : ∀ fuel pos, basicStrNAux src ml fuel pos ≤ 4
  | 0, _ => by simp [basicStrNAux]
  | fuel + 1, pos => by
    have ih := basicStrNAux_le src ml fuel
    have he1 := parseBasicStrEscapeN_le src pos true
    have he2 := parseBasicStrEscapeN_le src pos false
    simp only [basicStrNAux]
    repeat' (first | omega | exact ih _ | split | (apply Nat.max_le.mpr; constructor))

theorem parseBasicStrN_le (src : Str) (pos : Nat) (ml : Bool) : parseBasicStrN src pos ml ≤ 5 := by
  have := basicStrNAux_le src ml (src.length + 1) pos
  unfold parseBasicStrN; omega

theorem parseOneLineBasicStrN_le (src : Str) (pos : Nat) : parseOneLineBasicStrN src pos ≤ 6 := by
  have := parseBasicStrN_le src (pos + 1) false
  unfold parseOneLineBasicStrN; omega

theorem parseLiteralStrN_le (src : Str) (pos : Nat) : parseLiteralStrN src pos ≤ 3 := by
  have := skipUntilN_le src (pos + 1) [39] illegalBasic true
  unfold parseLiteralStrN; omega

theorem parseMultilineStrN_le (src : Str) (pos : Nat) (lit : Bool) : parseMultilineStrN src pos lit ≤ 6 := by
  have h1 := skipUntilN_le src (pos + 3) [39, 39, 39] illegalMl true
  have h2 := skipUntilN_le src (pos + 3 + 1) [39, 39, 39] illegalMl true
  have h3 := parseBasicStrN_le src (pos + 3) true
  have h4 := parseBasicStrN_le src (pos + 3 + 1) true
  simp only [parseMultilineStrN]
  repeat' (first | omega | split)

theorem parseKeyPartN_le (src : Str) (pos : Nat) : parseKeyPartN src pos ≤ 7 := by
  have := parseLiteralStrN_le src pos
  have := parseOneLineBasicStrN_le src pos
  simp only [parseKeyPartN]
  repeat' (first | omega | split)

theorem parseKeyPartN_ge (src : Str) (pos : Nat) : 2 ≤ parseKeyPartN src pos := by
  have h1 : 1 ≤ parseLiteralStrN src pos := by unfold parseLiteralStrN; exact Nat.le_add_right 1 _
  have h2 : 1 ≤ parseOneLineBasicStrN src pos := by unfold parseOneLineBasicStrN; exact Nat.le_add_right 1 _
  unfold parseKeyPartN
  repeat' (first | omega | split)

theorem keyLoopN_le (maxK : Nat) (src : Str) : ∀ fuel pos key, keyLoopN maxK src fuel pos key ≤ 7
  | 0, _, _ => by simp [keyLoopN]
  | fuel + 1, pos, key => by
    have ih := keyLoopN_le maxK src fuel
    have h1 := parseKeyPartN_le src (skipChars src (pos + 1) tomlWs)
    simp only [keyLoopN]
    repeat' (first | omega | exact ih _ _ | split | (apply Nat.max_le.mpr; constructor))

theorem parseKeyN_le (maxK : Nat) (src : Str) (pos : Nat) : parseKeyN maxK src pos ≤ 8 := by
  have := parseKeyPartN_le src pos
  simp only [parseKeyN]
  split
  · omega
  · next p part _ =>
    have := keyLoopN_le maxK src (src.length + 1) (skipChars src p tomlWs) [part]
    rw [Nat.max_def]; split <;> omega

/-- `parse_key` needs at least three frames: its own, `parse_key_part`'s, and one below. -/
theorem parseKeyN_ge (maxK : Nat) (src : Str) (pos : Nat) : 3 ≤ parseKeyN maxK src pos := by
  have := parseKeyPartN_ge src pos
  simp only [parseKeyN]
  split
  · omega
  · rw [Nat.max_def]; split <;> omega

theorem createRuleN_le (maxK : Nat) (src : Str) (pos skip : Nat) : createRuleN maxK src pos skip ≤ 9 := by
  have := parseKeyN_le maxK src (skipChars src (pos + skip) tomlWs)
  unfold createRuleN; omega

theorem matchToDatetimeN_le (tz : Str → Str → Nat → Bool) (m : DtM) : matchToDatetimeN tz m ≤ 2 := by
  simp only [matchToDatetimeN]
  repeat' (first | omega | split)

theorem need_skipCaw {α : Type} {r : Nat} (h : 4 ≤ r) (src : Str) (pos : Nat) (x : Py α) :
    need r (skipCawN src pos) x = x := need_ok (Nat.le_trans (skipCawN_le src pos) h) x

theorem need_skipComment {α : Type} {r : Nat} (h : 3 ≤ r) (src : Str) (pos : Nat) (x : Py α) :
    need r (skipCommentN src pos) x = x := need_ok (Nat.le_trans (skipCommentN_le src pos) h) x

theorem need_parseKey {α : Type} {r : Nat} (h : 8 ≤ r) (maxK : Nat) (src : Str) (pos : Nat) (x : Py α) :
    need r (parseKeyN maxK src pos) x = x := need_ok (Nat.le_trans (parseKeyN_le maxK src pos) h) x

theorem need_createRule {α : Type} {r : Nat} (h : 9 ≤ r) (maxK : Nat) (src : Str) (pos skip : Nat) (x : Py α) :
    need r (createRuleN maxK src pos skip) x = x := need_ok (Nat.le_trans (createRuleN_le maxK src pos skip) h) x

end PyLean.TextLibs.Toml
