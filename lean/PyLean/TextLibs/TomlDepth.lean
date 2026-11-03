import PyLean.TextLibs.TomlDoc

/-!
Nesting and the recursion limit. The docs of `tomllib` say nesting is limited by the recursion
limit; here is exactly where: `x = [[…]]` with `n` arrays parses exactly when `2n + 5` frames are
left when `loads` is called (two per array: `parse_value` and `parse_array`).
-/

namespace PyLean.TextLibs.Toml

/-- `n` opening and `n` closing brackets. -/
def nestText (n : Nat) : Str := List.replicate n 91 ++ List.replicate n 93

/-- The value of `nestText (m + 1)`: `m + 1` nested empty lists. -/
def nestArr : Nat → TVal
  | 0 => .arr []
  | m + 1 => .arr [nestArr m]

theorem nestText_length (n : Nat) : (nestText n).length = 2 * n := by simp [nestText]; omega

theorem nestText_succ (m : Nat) : nestText (m + 2) = 91 :: (nestText (m + 1) ++ [93]) := by
  simp only [nestText]
  rw [List.replicate_succ (n := m + 1) (a := 91), List.replicate_succ' (n := m + 1) (a := 93)]
  simp

theorem nestText_head (m : Nat) : ∃ t, nestText (m + 1) = 91 :: t := by
  simp only [nestText, List.replicate_succ]; exact ⟨_, rfl⟩

/-- `skip_comments_and_array_ws` before a character that is neither whitespace, a newline nor
`#`: it moves nothing, and needs two frames (its own, then `skip_chars` and `skip_comment`). -/
theorem skipCaw_stop {src : Str} {p c : Nat} (hc : src[p]? = some c) (h1 : tomlWsNl c = false) (h2 : c ≠ 35) :
    skipCawF src p = .ok p ∧ skipCawN src p = 2 := by
  have hs : skipChars src p tomlWsNl = p := skipChars_at hc h1
  have hcm : skipComment src p = .ok p := by simp [skipComment, hc, h2]
  have hcn : skipCommentN src p = 1 := by simp [skipCommentN, hc, h2]
  constructor
  · simp [skipCawF, skipCaw, hs, hcm, bind, Except.bind, pure, Except.pure]
  · simp [skipCawN, skipCawNAux, hs, hcm, hcn]

/-- `parse_value` on `m + 1` nested empty arrays, with `r` frames left below it, returns them
exactly when `2m + 3 ≤ r`, and raises `RecursionError` otherwise. -/
theorem nest_parse (cfg : Cfg) (src : Str) : ∀ (m r pos fuel : Nat) (rest : Str),
    src.drop pos = nestText (m + 1) ++ rest → 3 * (m + 1) ≤ fuel →
    parseValue cfg src r fuel pos =
      if 2 * m + 3 ≤ r then .ok (pos + 2 * (m + 1), nestArr m) else .error recErr
  | 0, r, pos, fuel, rest, h, hf => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 + 1 := ⟨fuel - 2, by omega⟩
    have h0 : src.drop pos = 91 :: 93 :: rest := by simpa [nestText] using h
    rw [parseValue_arr (getElem?_of_drop h0)]
    have h1 : src.drop (pos + 1) = 93 :: rest := drop_succ_of_drop h0
    obtain ⟨hs1, hn1⟩ := skipCaw_stop (getElem?_of_drop h1) (by decide) (by decide)
    have hst : startsAt src (pos + 1) [93] = true := startsAt_of_drop (p := [93]) (by simpa using h1)
    by_cases hr : 3 ≤ r
    · rw [if_pos (by omega), need_ok (show 1 ≤ r by omega)]
      simp only [parseArray, hn1, need_ok (show 2 ≤ r - 1 by omega), hs1, bind, Except.bind, hst, ite_true,
        pure, Except.pure, nestArr]
    · rw [if_neg (by omega)]
      by_cases hr1 : 1 ≤ r
      · rw [need_ok hr1]
        simp only [parseArray, hn1, need_err (show r - 1 < 2 by omega), bind, Except.bind]
      · rw [need_err (show r < 1 by omega)]
  | m + 1, r, pos, fuel, rest, h, hf => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 + 1 + 1 := ⟨fuel - 3, by omega⟩
    have h0 : src.drop pos = 91 :: (nestText (m + 1) ++ 93 :: rest) := by
      rw [h, nestText_succ]; simp
    rw [parseValue_arr (getElem?_of_drop h0)]
    have h1 : src.drop (pos + 1) = nestText (m + 1) ++ 93 :: rest := drop_succ_of_drop h0
    obtain ⟨t, ht⟩ := nestText_head m
    have hc1 : src[pos + 1]? = some 91 := getElem?_of_drop (r := t ++ 93 :: rest) (by rw [h1, ht]; rfl)
    obtain ⟨hs1, hn1⟩ := skipCaw_stop hc1 (by decide) (by decide)
    have hst : startsAt src (pos + 1) [93] = false := by
      unfold startsAt; rw [h1, ht]; simp [List.isPrefixOf]
    have hd2 : src.drop (pos + 1 + 2 * (m + 1)) = 93 :: rest := by
      have := drop_add_of_drop h1; rwa [nestText_length] at this
    obtain ⟨hs2, hn2⟩ := skipCaw_stop (getElem?_of_drop hd2) (by decide) (by decide)
    have hc2 : sl src (pos + 1 + 2 * (m + 1)) (pos + 1 + 2 * (m + 1) + 1) = [93] :=
      sl_of_drop (a := [93]) (by simpa using hd2)
    have ih := nest_parse cfg src m (r - 1 - 1) (pos + 1) f (93 :: rest) h1 (by omega)
    by_cases hr : 2 * (m + 1) + 3 ≤ r
    · rw [if_pos hr, need_ok (show 1 ≤ r by omega)]
      rw [if_pos (by omega)] at ih
      simp only [parseArray, hn1, need_ok (show 2 ≤ r - 1 by omega), hs1, bind, Except.bind, hst,
        Bool.false_eq_true, ite_false, arrayLoop, need_ok (show 1 ≤ r - 1 by omega), ih, hn2, hs2, hc2,
        show ([93] == [93]) = true from rfl, ite_true, pure, Except.pure, nestArr]
      congr 2; omega
    · rw [if_neg hr]
      by_cases hr1 : 1 ≤ r
      · rw [need_ok hr1]
        by_cases hr3 : 3 ≤ r
        · rw [if_neg (by omega)] at ih
          simp only [parseArray, hn1, need_ok (show 2 ≤ r - 1 by omega), hs1, bind, Except.bind, hst,
            Bool.false_eq_true, ite_false, arrayLoop, need_ok (show 1 ≤ r - 1 by omega), ih]
        · simp only [parseArray, hn1, need_err (show r - 1 < 2 by omega), bind, Except.bind]
      · rw [need_err (show r < 1 by omega)]

/-- `parse_key` on a bare key followed by a space and `=`: three frames. -/
theorem parseKeyN_bare {maxK : Nat} {src : Str} {x t : Str} (hx : x ≠ []) (hxb : ∀ c ∈ x, bareKey c = true)
    (h : src = x ++ 32 :: 61 :: t) :
    parseKey maxK src 0 = .ok (x.length + 1, [x]) ∧ parseKeyN maxK src 0 = 3 := by
  have hk : (KPart.bare x).ok := ⟨hx, hxb⟩
  have hpart := parseKeyPart_ok (src := src) (pos := 0) hk (r := 32 :: 61 :: t) (by rw [h]; rfl)
    (by intro c hc; simp at hc; subst hc; decide)
  simp only [KPart.enc, KPart.val, Nat.zero_add] at hpart
  have hd : src.drop x.length = 32 :: 61 :: t := by rw [h]; simp
  have hsk : skipChars src x.length tomlWs = x.length + 1 :=
    skipChars_of_drop (a := [32]) (by simpa using hd) (by simp; decide)
      (by intro c hc; simp at hc; subst hc; decide)
  have hd1 : src.drop (x.length + 1) = 61 :: t := drop_succ_of_drop hd
  have hg1 := getElem?_of_drop hd1
  obtain ⟨c, tt, hct⟩ : ∃ c tt, x = c :: tt := List.exists_cons_of_ne_nil hx
  have hg0 : src[0]? = some c := by rw [h, hct]; rfl
  have hb0 : bareKey c = true := hxb c (by rw [hct]; simp)
  constructor
  · simp [parseKey, hpart, bind, Except.bind, hsk, keyLoop, hg1, pure, Except.pure]
  · simp [parseKeyN, hpart, parseKeyPartN, hg0, hb0, hsk, keyLoopN, hg1]

/-- Nesting, docs of `tomllib` ("nesting is limited by the recursion limit"): for every bare key
`x` and every `m`, `loads('x = ' + '[' * (m + 1) + ']' * (m + 1))`, called with `fr` frames left
(`sys.getrecursionlimit()` minus the frames on the stack), returns `{x: [[…]]}` exactly when
`2m + 7 ≤ fr`, and raises `RecursionError("maximum recursion depth exceeded")` otherwise: each
level of array takes two frames. -/
def NestingDepthLimit : Prop :=
  ∀ (pf : ParseFloat) (maxK maxD : Nat) (tz : TzCache) (fr : Nat) (x : Str) (m : Nat),
    x ≠ [] → (∀ c ∈ x, bareKey c = true) →
    loads pf maxK maxD tz fr (.str (x ++ S " = " ++ nestText (m + 1))) =
      if 2 * m + 7 ≤ fr then .ok [(x, nestArr m)] else .error recErr

theorem nest_no13 (m : Nat) : 13 ∉ nestText m := by simp [nestText]

theorem nestingDepthLimit_proven : NestingDepthLimit := by
  intro pf maxK maxD tz fr x m hx hxb
  have hx13 : 13 ∉ x := fun hm => absurd (hxb 13 hm) (by decide)
  generalize hsrc : x ++ S " = " ++ nestText (m + 1) = src
  have h13 : 13 ∉ src := by
    rw [← hsrc]; simp only [List.mem_append, not_or]
    exact ⟨⟨hx13, by decide⟩, nest_no13 _⟩
  have hsrc' : src = x ++ 32 :: 61 :: (32 :: nestText (m + 1)) := by rw [← hsrc]; simp [S]
  obtain ⟨hkey, hkn⟩ := parseKeyN_bare (maxK := (mkCfg pf maxK maxD tz).maxKeyParts) hx hxb hsrc'
  obtain ⟨c, tt, hct⟩ : ∃ c tt, x = c :: tt := List.exists_cons_of_ne_nil hx
  have hb0 : bareKey c = true := hxb c (by rw [hct]; simp)
  have hg0 : src[0]? = some c := by rw [hsrc', hct]; rfl
  have hki : keyInitial c = true := by simp [keyInitial, hb0]
  have hcws : tomlWs c = false := by revert hb0; simp [bareKey, tomlWs, inR]; omega
  have hc10 : c ≠ 10 := by intro e; subst e; exact absurd hb0 (by decide)
  have hs0 : skipChars src 0 tomlWs = 0 := skipChars_at hg0 hcws
  have hd1 : src.drop (x.length + 1) = 61 :: 32 :: nestText (m + 1) := by rw [hsrc']; simp
  have hg1 := getElem?_of_drop hd1
  have hd2 : src.drop (x.length + 1 + 1) = 32 :: nestText (m + 1) := drop_succ_of_drop hd1
  have hd3 : src.drop (x.length + 3) = nestText (m + 1) ++ [] := by
    simpa using drop_succ_of_drop hd2
  obtain ⟨t, ht⟩ := nestText_head m
  have hsk : skipChars src (x.length + 1 + 1) tomlWs = x.length + 3 :=
    skipChars_of_drop (a := [32]) (by simpa using hd2) (by simp; decide)
      (by intro c hc; rw [ht] at hc; simp at hc; subst hc; decide)
  have hlen : src.length = x.length + 3 + 2 * (m + 1) := by
    rw [hsrc']; simp [nestText_length]; omega
  have hval := nest_parse (mkCfg pf maxK maxD tz) src m (fr - 1 - 1 - 1 - 1) (x.length + 3) (vFuel src - 1) []
    hd3 (by unfold vFuel; omega)
  have hfuel : vFuel src = vFuel src - 1 + 1 := by unfold vFuel; omega
  -- the frames: `loads`, `Output()`, `key_value_rule`, `parse_key_value_pair`, `parse_key`
  by_cases h4 : 4 ≤ fr
  · rw [loads_eq pf maxK maxD tz fr src h13 h4]
    by_cases h6 : 6 ≤ fr
    · have hpkv : parseKeyValuePair (mkCfg pf maxK maxD tz) src (fr - 1 - 1 - 1) (vFuel src) 0 =
          (if 2 * m + 7 ≤ fr then .ok (x.length + 3 + 2 * (m + 1), [x], nestArr m) else .error recErr) := by
        rw [hfuel]
        simp only [parseKeyValuePair, hkn, need_ok (show 3 ≤ fr - 1 - 1 - 1 by omega), hkey, bind,
          Except.bind, hg1, show (some 61 != some 61) = false from rfl, Bool.false_eq_true, ite_false, hsk,
          need_ok (show 1 ≤ fr - 1 - 1 - 1 by omega), hval]
        by_cases hm : 2 * m + 7 ≤ fr
        · rw [if_pos (by omega), if_pos hm]; rfl
        · rw [if_neg (by omega), if_neg hm]
      by_cases hm : 2 * m + 7 ≤ fr
      · rw [if_pos hm] at hpkv ⊢
        have hrule := kvr_one (R := fr - 1 - 1) (out := Out.init) (by omega) hpkv rfl
        rw [mainLoop_kv hg0 hki hcws hc10 hrule (by omega)]
        have hend : src[x.length + 3 + 2 * (m + 1)]? = none := by
          rw [List.getElem?_eq_none_iff]; omega
        simp [hend, kvOut, Out.init]
      · rw [if_neg hm] at hpkv ⊢
        simp only [mainLoop, hs0, hg0, show (c == 10) = false by simp [hc10], Bool.false_eq_true, ite_false,
          hki, ite_true, need_ok (show 1 ≤ fr - 1 by omega), keyValueRule,
          need_ok (show 1 ≤ fr - 1 - 1 by omega), hpkv, bind, Except.bind]
    · rw [if_neg (by omega)]
      simp only [mainLoop, hs0, hg0, show (c == 10) = false by simp [hc10], Bool.false_eq_true, ite_false,
        hki, ite_true, need_ok (show 1 ≤ fr - 1 by omega), keyValueRule,
        need_ok (show 1 ≤ fr - 1 - 1 by omega), bind, Except.bind]
      rw [hfuel]
      simp only [parseKeyValuePair, hkn, need_err (show fr - 1 - 1 - 1 < 3 by omega), bind, Except.bind]
  · rw [if_neg (by omega)]
    by_cases h1 : 1 ≤ fr
    · simp only [loads, need_ok h1, crlf_id src h13, need_err (show fr - 1 < 3 by omega)]
    · simp only [loads, need_err (show fr < 1 by omega)]

/-- The statement the docs rule out: with frames enough for every flat document of this shape,
every nesting depth would parse. -/
def NestingUnbounded : Prop :=
  ∀ (pf : ParseFloat) (maxK maxD : Nat) (tz : TzCache) (fr : Nat) (x : Str) (m : Nat),
    x ≠ [] → (∀ c ∈ x, bareKey c = true) → 16 ≤ fr →
    loads pf maxK maxD tz fr (.str (x ++ S " = " ++ nestText (m + 1))) = .ok [(x, nestArr m)]

/-- With sixteen frames left (`sys.setrecursionlimit(depth + 16)`), seventeen nested arrays raise
`RecursionError`. -/
theorem nestingUnbounded_refuted : ¬ NestingUnbounded := by
  intro h
  have h1 := h { isFloat := true, call := fun _ => .ok .other } 1000 4300 (fun _ _ _ => true) 16 (S "a") 16
    (by decide) (by decide) (by omega)
  have h2 := nestingDepthLimit_proven { isFloat := true, call := fun _ => .ok .other } 1000 4300
    (fun _ _ _ => true) 16 (S "a") 16 (by decide) (by decide)
  rw [h1, if_neg (by omega)] at h2
  cases h2

end PyLean.TextLibs.Toml
