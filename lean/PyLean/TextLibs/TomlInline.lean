import PyLean.TextLibs.TomlScen

/-!
The errors of arrays and inline tables: "Unclosed array", and the four errors of
`parse_inline_table` with dotted keys inside the braces.
-/

namespace PyLean.TextLibs.Toml

/-! ## Arrays, _parser.py:508-529 -/

/-- Arrays, TOML 1.1 "Array" ("Square brackets surround arrays. Values are separated by
commas"): `[`, filler, a value of `ArrayTableSpec`, filler, then anything but `]`, `,` or `"`
(the end of the document included) raises "Unclosed array" there, with `3 * depth + 13` frames
left below `parse_value`. -/
def UnclosedArray : Prop :=
  ∀ (cfg : Cfg) (src : Str) (r pos fuel : Nat) (lead fa : List Fill) (v : SV) (tail : Str),
    (∀ f ∈ lead, f.ok) → (∀ f ∈ fa, f.ok) → v.ok → notFill tail →
    (∀ c, tail.head? = some c → c ≠ 93 ∧ c ≠ 44 ∧ c ≠ 34) → 3 * v.depth + 13 ≤ r → v.need + 3 ≤ fuel →
    src.drop pos = 91 :: fillEnc lead ++ v.enc ++ fillEnc fa ++ tail →
    parseValue cfg src r fuel pos =
      .error (tdeS "Unclosed array" src (pos + 1 + (fillEnc lead).length + v.enc.length + (fillEnc fa).length))

theorem unclosedArray_proven : UnclosedArray := by
  intro cfg src r pos fuel lead fa v tail hlead hfa hv hnf htail hr hf h
  obtain ⟨g, rfl⟩ : ∃ g, fuel = g + 1 + 1 + 1 := ⟨fuel - 3, by omega⟩
  have h0 : src.drop pos = 91 :: (fillEnc lead ++ (v.enc ++ (fillEnc fa ++ tail))) := by simpa using h
  rw [parseValue_arr (getElem?_of_drop h0), need_ok (show 1 ≤ r by omega)]
  have hd1 : src.drop (pos + 1) = fillEnc lead ++ (v.enc ++ (fillEnc fa ++ tail)) := drop_succ_of_drop h0
  have hsk := skipCawF_fill hlead (SV.head_props v (fillEnc fa ++ tail)).1 hd1
  have hd2 : src.drop (pos + 1 + (fillEnc lead).length) = v.enc ++ (fillEnc fa ++ tail) := drop_add_of_drop hd1
  have hst : startsAt src (pos + 1 + (fillEnc lead).length) [93] = false := by
    obtain ⟨c, t, he, -⟩ := SV.head v
    have := ((SV.head_props v (fillEnc fa ++ tail)).2 c (by rw [he]; rfl)).1
    unfold startsAt; rw [hd2, he]; simp [List.isPrefixOf, Ne.symm this]
  have hvp := SV.parse cfg src v (r - 1 - 1) _ g (fillEnc fa ++ tail) hv
    (fill_head_ne34 fa hfa tail (fun c hc => (htail c hc).2.2)) hd2 (by omega) (by omega)
  have hd3 : src.drop (pos + 1 + (fillEnc lead).length + v.enc.length) = fillEnc fa ++ tail := drop_add_of_drop hd2
  have hsk2 := skipCawF_fill hfa hnf hd3
  have hd4 : src.drop (pos + 1 + (fillEnc lead).length + v.enc.length + (fillEnc fa).length) = tail :=
    drop_add_of_drop hd3
  have hc : sl src (pos + 1 + (fillEnc lead).length + v.enc.length + (fillEnc fa).length)
      (pos + 1 + (fillEnc lead).length + v.enc.length + (fillEnc fa).length + 1) = tail.take 1 := by
    simp [sl, hd4]
  simp only [parseArray, need_skipCaw (show 4 ≤ r - 1 by omega), hsk, bind, Except.bind, hst, Bool.false_eq_true,
    ite_false, arrayLoop, need_ok (show 1 ≤ r - 1 by omega), hvp, need_skipCaw (show 4 ≤ r - 1 by omega), hsk2, hc]
  cases ht : tail with
  | nil => rfl
  | cons c t =>
    obtain ⟨h93, h44, -⟩ := htail c (by simp [ht])
    have e1 : ([c] == [93]) = false := by simp [h93]
    have e2 : ([c] != [44]) = true := by simp [h44]
    simp [e1, e2]

/-! ## Inline tables, _parser.py:532-563 -/

/-- The loop of `parse_inline_table` after `parse_key_value_pair` returned `pos`, `key`, `value`. -/
def inlineBody (cfg : Cfg) (src : Str) (r fuel pos : Nat) (data : Dict) (flags : Flags) (key : Key) (value : TVal) :
    Py (Nat × TVal) := do
  let keyParent := key.dropLast
  let keyStem := key.getLastD []
  if flags.is_ key FROZEN then
    .error (tde (S "Cannot mutate immutable namespace " ++ keyRepr key) src pos)
  else
    let (data, _) ← overwriteErr src pos <| withNest false (fun nest =>
      if (dget nest keyStem).isSome then
        .error (tde (S "Duplicate inline table key " ++ reprS keyStem) src pos)
      else .ok (dset nest keyStem value, ())) keyParent data
    let pos ← need r (skipCawN src pos) (skipCawF src pos)
    let c := sl src pos (pos + 1)
    if c == [125] then return (pos + 1, .tbl data)
    if c != [44] then .error (tdeS "Unclosed inline table" src pos)
    else
      let pos := pos + 1
      let pos ← need r (skipCawN src pos) (skipCawF src pos)
      if startsAt src pos [125] then return (pos + 1, .tbl data)
      let flags ← if value.isDictOrList then flags.set key FROZEN true else pure flags
      inlineLoop cfg src r fuel pos data flags

/-- One entry `K=v` of an inline table. -/
theorem inline_entry {cfg : Cfg} {src : Str} {r pos g : Nat} {p0 : KPart} {ps : List KPart} {v : SV} {rest : Str}
    {data : Dict} {flags : Flags}
    (h0 : p0.ok) (hps : ∀ p ∈ ps, p.ok) (hmax : ps.length + 1 ≤ cfg.maxKeyParts) (hv : v.ok)
    (hr34 : ∀ c, rest.head? = some c → c ≠ 34) (hg : v.need ≤ g) (hr : 3 * v.depth + 12 ≤ r)
    (h : src.drop pos = keyEnc p0 ps ++ 61 :: v.enc ++ rest) :
    inlineLoop cfg src r (g + 1 + 1) pos data flags =
      inlineBody cfg src r (g + 1) (pos + (keyEnc p0 ps).length + 1 + v.enc.length) data flags (keyVal p0 ps) v.val := by
  have hp := pkv_at (cfg := cfg) (r := r - 1) (fuel := g) h0 hps hmax hv hr34 hg (by omega) h
  simp only [inlineLoop, need_ok (show 1 ≤ r by omega), hp, bind, Except.bind, inlineBody]

/-- `{` then filler, entering the loop. -/
theorem parseValue_brace {cfg : Cfg} {src : Str} {r pos g : Nat} {lead : List Fill} {rest : Str}
    (hlead : ∀ f ∈ lead, f.ok) (hnf : notFill rest) (h125 : ∀ c, rest.head? = some c → c ≠ 125) (hr : 5 ≤ r)
    (h : src.drop pos = 123 :: fillEnc lead ++ rest) :
    parseValue cfg src r (g + 1 + 1) pos =
      inlineLoop cfg src (r - 1) g (pos + 1 + (fillEnc lead).length) [] Flags.init := by
  have h0 : src.drop pos = 123 :: (fillEnc lead ++ rest) := by simpa using h
  rw [parseValue_tbl (getElem?_of_drop h0), need_ok (show 1 ≤ r by omega)]
  have hd1 : src.drop (pos + 1) = fillEnc lead ++ rest := drop_succ_of_drop h0
  have hsk := skipCawF_fill hlead hnf hd1
  have hd2 : src.drop (pos + 1 + (fillEnc lead).length) = rest := drop_add_of_drop hd1
  have hst : startsAt src (pos + 1 + (fillEnc lead).length) [125] = false := by
    unfold startsAt; rw [hd2]
    cases hr' : rest with
    | nil => rfl
    | cons c t => have := h125 c (by simp [hr']); simp [List.isPrefixOf, Ne.symm this]
  simp only [parseInlineTable, need_skipCaw (show 4 ≤ r - 1 by omega), hsk, bind, Except.bind, hst,
    Bool.false_eq_true, ite_false]

theorem kpart_notFill {k : KPart} (hk : k.ok) (x : Str) :
    notFill (k.enc ++ x) ∧ ∀ c, (k.enc ++ x).head? = some c → c ≠ 125 := kpart_head_props k hk x

theorem keyEnc_notFill {p0 : KPart} {ps : List KPart} (h0 : p0.ok) (x : Str) :
    notFill (keyEnc p0 ps ++ x) ∧ ∀ c, (keyEnc p0 ps ++ x).head? = some c → c ≠ 125 := by
  have := kpart_head_props p0 h0 (ps.flatMap (fun p => 46 :: p.enc) ++ x)
  simpa [keyEnc] using this

/-- Inline tables, TOML 1.1 "Inline Table" ("No newlines are allowed between the curly braces
unless they are valid within a value" — TOML 1.1 relaxes this; keys may be dotted; "Inline tables
are fully self-contained ... Keys and sub-tables cannot be added outside the braces"; a key may not
be defined twice), with `{`, fillers around each `,`, and entries `K=v`: for one-part keys `k`,
`k'` with the same value and a value `v` that is not a table or array, `{k=v, k'=w}` raises
"Duplicate inline table key 'k'" after `w`; for a bare `x`, `{k=v, k.x=w}` raises "Cannot overwrite
a value" after `w` when `v` is not a table or array, and "Cannot mutate immutable namespace (k, x)"
when it is; `{k=v` followed by anything but `}` or `,` raises "Unclosed inline table" there. With
`3 * depth + 16` frames left for the deeper value. -/
def InlineTableRules : Prop :=
  ∀ (cfg : Cfg) (src : Str) (r pos fuel : Nat) (lead fa fb : List Fill) (k k' : KPart) (v w : SV) (tail : Str),
    (∀ f ∈ lead, f.ok) → (∀ f ∈ fa, f.ok) → (∀ f ∈ fb, f.ok) → k.ok → k'.ok → v.ok → w.ok →
    2 ≤ cfg.maxKeyParts → 3 * v.depth + 16 ≤ r → 3 * w.depth + 16 ≤ r → v.need + w.need + 8 ≤ fuel →
    (∀ c, tail.head? = some c → c ≠ 34) →
    (k'.val = k.val → v.val.isDictOrList = false →
      src.drop pos = 123 :: fillEnc lead ++ k.enc ++ 61 :: v.enc ++ fillEnc fa ++ 44 :: fillEnc fb ++
        k'.enc ++ 61 :: w.enc ++ tail →
      parseValue cfg src r fuel pos = .error (tde (S "Duplicate inline table key " ++ reprS k.val) src
        (pos + 1 + (fillEnc lead).length + k.enc.length + 1 + v.enc.length + (fillEnc fa).length + 1 +
          (fillEnc fb).length + k'.enc.length + 1 + w.enc.length))) ∧
    (∀ x : Str, bareOk x →
      src.drop pos = 123 :: fillEnc lead ++ k.enc ++ 61 :: v.enc ++ fillEnc fa ++ 44 :: fillEnc fb ++
        k.enc ++ 46 :: x ++ 61 :: w.enc ++ tail →
      parseValue cfg src r fuel pos =
        .error (if v.val.isDictOrList then tde (S "Cannot mutate immutable namespace " ++ keyRepr [k.val, x]) src
            (pos + 1 + (fillEnc lead).length + k.enc.length + 1 + v.enc.length + (fillEnc fa).length + 1 +
              (fillEnc fb).length + k.enc.length + 1 + x.length + 1 + w.enc.length)
          else tdeS "Cannot overwrite a value" src
            (pos + 1 + (fillEnc lead).length + k.enc.length + 1 + v.enc.length + (fillEnc fa).length + 1 +
              (fillEnc fb).length + k.enc.length + 1 + x.length + 1 + w.enc.length))) ∧
    (notFill tail → (∀ c, tail.head? = some c → c ≠ 125 ∧ c ≠ 44) →
      src.drop pos = 123 :: fillEnc lead ++ k.enc ++ 61 :: v.enc ++ fillEnc fa ++ tail →
      parseValue cfg src r fuel pos = .error (tdeS "Unclosed inline table" src
        (pos + 1 + (fillEnc lead).length + k.enc.length + 1 + v.enc.length + (fillEnc fa).length)))

/-- After the first entry `k=v` and `,`: the loop goes on with `{k: v}`. -/
theorem inline_first_comma {cfg : Cfg} {src : Str} {r p2 g : Nat} {k : KPart} {v : SV} {fa fb : List Fill}
    {rest : Str} (hfa : ∀ f ∈ fa, f.ok) (hfb : ∀ f ∈ fb, f.ok) (hnf : notFill rest)
    (h125 : ∀ c, rest.head? = some c → c ≠ 125) (hr : 4 ≤ r)
    (h : src.drop p2 = fillEnc fa ++ 44 :: fillEnc fb ++ rest) :
    inlineBody cfg src r (g + 1) p2 [] Flags.init [k.val] v.val =
      inlineLoop cfg src r (g + 1) (p2 + (fillEnc fa).length + 1 + (fillEnc fb).length) [(k.val, v.val)]
        (if v.val.isDictOrList then { tree := fsetAux FROZEN true [k.val] [], pending := [] } else Flags.init) := by
  have hsk := skipCawF_fill hfa (notFill_44 _) (by simpa using h)
  have hd2 : src.drop (p2 + (fillEnc fa).length) = [44] ++ (fillEnc fb ++ rest) := by
    simpa using drop_add_of_drop (a := fillEnc fa) (by simpa using h)
  have hc := sl_of_drop hd2
  simp only [List.length_singleton] at hc
  have hd3 : src.drop (p2 + (fillEnc fa).length + 1) = fillEnc fb ++ rest := drop_add_of_drop hd2
  have hsk2 := skipCawF_fill hfb hnf hd3
  have hd4 : src.drop (p2 + (fillEnc fa).length + 1 + (fillEnc fb).length) = rest := drop_add_of_drop hd3
  have hst : startsAt src (p2 + (fillEnc fa).length + 1 + (fillEnc fb).length) [125] = false := by
    unfold startsAt; rw [hd4]
    cases hr' : rest with
    | nil => rfl
    | cons c t => have := h125 c (by simp [hr']); simp [List.isPrefixOf, Ne.symm this]
  have his : Flags.init.is_ [k.val] FROZEN = false := by simp [Flags.init, Flags.is_, isAux, dget_nil]
  simp only [inlineBody, his, Bool.false_eq_true, ite_false, show ([k.val] : Key).dropLast = [] from rfl,
    show ([k.val] : Key).getLastD [] = k.val from rfl, withNest, dget_nil, Option.isSome_none, dset_nil,
    overwriteErr, bind, Except.bind, need_skipCaw hr, hsk, hc, show ([44] == [125]) = false from rfl,
    show ([44] != [44]) = false from rfl, hsk2, hst]
  cases hd : v.val.isDictOrList <;> simp [Flags.set, Flags.init, pure, Except.pure]

theorem drop_of_eq_pre {src : Str} {pos n : Nat} {a b : Str} (h : src.drop pos = a ++ b) (hn : n = pos + a.length) :
    src.drop n = b := by subst hn; exact drop_add_of_drop h

theorem inlineTableRules_proven : InlineTableRules := by
  intro cfg src r pos fuel lead fa fb k k' v w tail hlead hfa hfb hk hk' hv hw hmax hrv hrw hf htail
  obtain ⟨g, rfl⟩ : ∃ g, fuel = g + 1 + 1 + 1 + 1 + 1 := ⟨fuel - 5, by omega⟩
  have hK : ∀ q : KPart, keyEnc q [] = q.enc := by intro q; simp [keyEnc]
  have hKv : ∀ q : KPart, keyVal q [] = [q.val] := by intro q; simp [keyVal]
  have hmax1 : ([] : List KPart).length + 1 ≤ cfg.maxKeyParts := by simp; omega
  have hv34 := fill_head_ne34 fa hfa (44 :: fillEnc fb) (by intro c hc; simp at hc; omega)
  refine ⟨?_, ?_, ?_⟩
  · intro hkk hvd h
    have h0 : src.drop pos = 123 :: fillEnc lead ++ (keyEnc k [] ++ (61 :: v.enc ++
        (fillEnc fa ++ 44 :: fillEnc fb ++ k'.enc ++ 61 :: w.enc ++ tail))) := by rw [h, hK]; simp
    rw [parseValue_brace hlead (keyEnc_notFill hk _).1 (keyEnc_notFill hk _).2 (by omega) h0]
    have hd1 : src.drop (pos + 1 + (fillEnc lead).length) = keyEnc k [] ++ 61 :: v.enc ++
        (fillEnc fa ++ 44 :: fillEnc fb ++ (k'.enc ++ 61 :: w.enc ++ tail)) :=
      drop_of_eq_pre (a := 123 :: fillEnc lead) (by rw [h, hK]; simp) (by simp; omega)
    rw [inline_entry (g := g + 1) hk (by simp) hmax1 hv (fun c hc => hv34 c (by simpa using hc)) (by omega)
      (by omega) hd1, hK, hKv]
    have hd2 : src.drop (pos + 1 + (fillEnc lead).length + k.enc.length + 1 + v.enc.length) =
        fillEnc fa ++ 44 :: fillEnc fb ++ (k'.enc ++ (61 :: w.enc ++ tail)) :=
      drop_of_eq_pre (a := 123 :: fillEnc lead ++ k.enc ++ 61 :: v.enc) (by rw [h]; simp) (by simp; omega)
    rw [inline_first_comma hfa hfb (kpart_notFill hk' _).1 (kpart_notFill hk' _).2 (by omega) hd2, hvd]
    simp only [Bool.false_eq_true, ite_false]
    have hd3 : src.drop (pos + 1 + (fillEnc lead).length + k.enc.length + 1 + v.enc.length + (fillEnc fa).length + 1 +
        (fillEnc fb).length) = keyEnc k' [] ++ 61 :: w.enc ++ tail :=
      drop_of_eq_pre (a := 123 :: fillEnc lead ++ k.enc ++ 61 :: v.enc ++ fillEnc fa ++ 44 :: fillEnc fb)
        (by rw [h, hK]; simp) (by simp; omega)
    rw [inline_entry (g := g) hk' (by simp) hmax1 hw htail (by omega) (by omega) hd3, hK, hKv]
    have his : Flags.init.is_ [k.val] FROZEN = false := by simp [Flags.init, Flags.is_, isAux, dget_nil]
    rw [hkk]
    simp only [inlineBody, his, Bool.false_eq_true, ite_false, show ([k.val] : Key).dropLast = [] from rfl,
      show ([k.val] : Key).getLastD [] = k.val from rfl, withNest, dget_cons, ite_true, Option.isSome_some,
      overwriteErr_tde, bind, Except.bind]
  · intro x hx h
    have h0 : src.drop pos = 123 :: fillEnc lead ++ (keyEnc k [] ++ (61 :: v.enc ++
        (fillEnc fa ++ 44 :: fillEnc fb ++ k.enc ++ 46 :: x ++ 61 :: w.enc ++ tail))) := by rw [h, hK]; simp
    rw [parseValue_brace hlead (keyEnc_notFill hk _).1 (keyEnc_notFill hk _).2 (by omega) h0]
    have hd1 : src.drop (pos + 1 + (fillEnc lead).length) = keyEnc k [] ++ 61 :: v.enc ++
        (fillEnc fa ++ 44 :: fillEnc fb ++ (k.enc ++ 46 :: x ++ 61 :: w.enc ++ tail)) :=
      drop_of_eq_pre (a := 123 :: fillEnc lead) (by rw [h, hK]; simp) (by simp; omega)
    rw [inline_entry (g := g + 1) hk (by simp) hmax1 hv (fun c hc => hv34 c (by simpa using hc)) (by omega)
      (by omega) hd1, hK, hKv]
    have hd2 : src.drop (pos + 1 + (fillEnc lead).length + k.enc.length + 1 + v.enc.length) =
        fillEnc fa ++ 44 :: fillEnc fb ++ (k.enc ++ (46 :: x ++ 61 :: w.enc ++ tail)) :=
      drop_of_eq_pre (a := 123 :: fillEnc lead ++ k.enc ++ 61 :: v.enc) (by rw [h]; simp) (by simp; omega)
    rw [inline_first_comma hfa hfb (kpart_notFill hk _).1 (kpart_notFill hk _).2 (by omega) hd2]
    have hd3 : src.drop (pos + 1 + (fillEnc lead).length + k.enc.length + 1 + v.enc.length + (fillEnc fa).length + 1 +
        (fillEnc fb).length) = keyEnc k [.bare x] ++ 61 :: w.enc ++ tail :=
      drop_of_eq_pre (a := 123 :: fillEnc lead ++ k.enc ++ 61 :: v.enc ++ fillEnc fa ++ 44 :: fillEnc fb)
        (by rw [h]; simp [keyEnc, KPart.enc]) (by simp; omega)
    rw [inline_entry (g := g) hk (by intro p hp; simp at hp; subst hp; exact hx) (by simp; omega) hw htail
      (by omega) (by omega) hd3]
    have hKx : (keyEnc k [.bare x]).length = k.enc.length + 1 + x.length := by
      simp [keyEnc, KPart.enc]; omega
    have hKvx : keyVal k [.bare x] = [k.val, x] := by simp [keyVal, KPart.val]
    rw [hKx, hKvx]
    cases v with
    | str ps =>
      simp [inlineBody, SV.val, TVal.isDictOrList, Flags.init, Flags.is_, isAux, dget_nil, withNest, dget_cons,
        overwriteErr, noNest, bind, Except.bind]
      congr 1; omega
    | bool bb =>
      simp [inlineBody, SV.val, TVal.isDictOrList, Flags.init, Flags.is_, isAux, dget_nil, withNest, dget_cons,
        overwriteErr, noNest, bind, Except.bind]
      congr 1; omega
    | arr ld its =>
      simp [inlineBody, SV.val, TVal.isDictOrList, Flags.is_, isAux, fsetAux, dset, dget_cons, dget_nil,
        FNode.empty, FNode.rflags, addFlag, FROZEN, bind, Except.bind]
      congr 1; omega
    | tbl ld its =>
      simp [inlineBody, SV.val, TVal.isDictOrList, Flags.is_, isAux, fsetAux, dset, dget_cons, dget_nil,
        FNode.empty, FNode.rflags, addFlag, FROZEN, bind, Except.bind]
      congr 1; omega
  · intro hnf h125 h
    have h0 : src.drop pos = 123 :: fillEnc lead ++ (keyEnc k [] ++ (61 :: v.enc ++ (fillEnc fa ++ tail))) := by
      rw [h, hK]; simp
    rw [parseValue_brace hlead (keyEnc_notFill hk _).1 (keyEnc_notFill hk _).2 (by omega) h0]
    have hd1 : src.drop (pos + 1 + (fillEnc lead).length) = keyEnc k [] ++ 61 :: v.enc ++ (fillEnc fa ++ tail) :=
      drop_of_eq_pre (a := 123 :: fillEnc lead) (by rw [h, hK]; simp) (by simp; omega)
    rw [inline_entry (g := g + 1) hk (by simp) hmax1 hv
      (fill_head_ne34 fa hfa _ (fun c hc => htail c hc)) (by omega) (by omega) hd1, hK, hKv]
    have hd2 : src.drop (pos + 1 + (fillEnc lead).length + k.enc.length + 1 + v.enc.length) = fillEnc fa ++ tail :=
      drop_of_eq_pre (a := 123 :: fillEnc lead ++ k.enc ++ 61 :: v.enc) (by rw [h]; simp) (by simp; omega)
    have hsk := skipCawF_fill hfa hnf hd2
    have hd3 : src.drop (pos + 1 + (fillEnc lead).length + k.enc.length + 1 + v.enc.length + (fillEnc fa).length) =
        tail := drop_add_of_drop hd2
    have his : Flags.init.is_ [k.val] FROZEN = false := by simp [Flags.init, Flags.is_, isAux, dget_nil]
    have hc : sl src (pos + 1 + (fillEnc lead).length + k.enc.length + 1 + v.enc.length + (fillEnc fa).length)
        (pos + 1 + (fillEnc lead).length + k.enc.length + 1 + v.enc.length + (fillEnc fa).length + 1) =
          tail.take 1 := by
      simp only [sl, hd3]; simp
    simp only [inlineBody, his, Bool.false_eq_true, ite_false, show ([k.val] : Key).dropLast = [] from rfl,
      show ([k.val] : Key).getLastD [] = k.val from rfl, withNest, dget_nil, Option.isSome_none, dset_nil,
      overwriteErr, bind, Except.bind, need_skipCaw (show 4 ≤ r - 1 by omega), hsk, hc]
    cases ht : tail with
    | nil => rfl
    | cons c t =>
      obtain ⟨h1, h2⟩ := h125 c (by simp [ht])
      have e1 : ([c] == [125]) = false := by simp [h1]
      have e2 : ([c] != [44]) = true := by simp [h2]
      simp [e1, e2]

/-! ## Multi-line literal strings, _parser.py:623-651, 704-705 -/

theorem findSub_triple {s x : Str} (hs : 39 ∉ s) (hx : [39, 39, 39].isPrefixOf x = true) :
    findSub [39, 39, 39] (s ++ x) = some s.length := by
  induction s with
  | nil =>
    cases x with
    | nil => simp [List.isPrefixOf] at hx
    | cons c r => simp [findSub, hx]
  | cons c r ih =>
    have hc : c ≠ 39 := fun e => hs (by simp [e])
    have hr : 39 ∉ r := fun m => hs (by simp [m])
    simp [findSub, List.isPrefixOf, Ne.symm hc, ih hr]

theorem findSub_triple_none : ∀ {s : Str}, 39 ∉ s → findSub [39, 39, 39] s = none
  | [], _ => rfl
  | c :: r, hs => by
    have hc : c ≠ 39 := fun e => hs (by simp [e])
    have hr : 39 ∉ r := fun m => hs (by simp [m])
    simp [findSub, List.isPrefixOf, Ne.symm hc, findSub_triple_none hr]

theorem parseMultilineStrN_lit_le (src : Str) (pos : Nat) : parseMultilineStrN src pos true ≤ 3 := by
  have h1 := skipUntilN_le src (pos + 3) [39, 39, 39] illegalMl true
  have h2 := skipUntilN_le src (pos + 3 + 1) [39, 39, 39] illegalMl true
  have hall : ∀ p, skipUntilN src p [39, 39, 39] illegalMl true ≤ 2 := fun p => skipUntilN_le src p _ _ _
  simp only [parseMultilineStrN, ite_true]
  have := hall (if startsAt src (pos + 3) [10] = true then pos + 3 + 1 else pos + 3)
  omega

/-- Multi-line literal strings, TOML 1.1 "String" ("Multi-line literal strings are surrounded by
three single quotes on each side ... A newline immediately following the opening delimiter will
be trimmed. All other content between the delimiters is interpreted as-is without modification";
"You can write 1 or 2 single quotes anywhere within a multi-line literal string, but sequences of
three or more single quotes are not permitted"), with at least three frames left: for every text
without `'` and without control characters other than tab and newline, an optional newline right
after `'''` (trimmed), and one or two `'` before the closing `'''` (kept), `parse_value` returns
the text and the position after the quotes; without a closing `'''` it raises "Expected \"'''\""
at the end of the document; a control character other than tab or newline before the closing
quotes raises "Found invalid character" there. -/
def MultilineLiteralSpec : Prop :=
  (∀ (cfg : Cfg) (src : Str) (r pos fuel : Nat) (nl s q rest : Str), 3 ≤ r → (nl = [] ∨ nl = [10]) →
    (q = [] ∨ q = [39] ∨ q = [39, 39]) → (∀ c ∈ s, c ≠ 39 ∧ illegalMl c = false) →
    (nl = [] → (s ++ q).head? ≠ some 10) → (∀ c, rest.head? = some c → c ≠ 39) →
    src.drop pos = [39, 39, 39] ++ nl ++ s ++ q ++ [39, 39, 39] ++ rest →
    parseValue cfg src r (fuel + 1) pos = .ok (pos + 6 + nl.length + s.length + q.length, .str (s ++ q))) ∧
  (∀ (cfg : Cfg) (src : Str) (r pos fuel : Nat) (s : Str), 3 ≤ r → 39 ∉ s →
    src.drop pos = [39, 39, 39] ++ s →
    parseValue cfg src r (fuel + 1) pos = .error (tde (S "Expected " ++ reprS [39, 39, 39]) src src.length)) ∧
  (∀ (cfg : Cfg) (src : Str) (r pos fuel c : Nat) (s1 s2 rest : Str), 3 ≤ r →
    (∀ x ∈ s1, x ≠ 39 ∧ illegalMl x = false) → s1.head? ≠ some 10 → illegalMl c = true → 39 ∉ s2 →
    src.drop pos = [39, 39, 39] ++ s1 ++ c :: s2 ++ [39, 39, 39] ++ rest →
    parseValue cfg src r (fuel + 1) pos =
      .error (tde (S "Found invalid character " ++ reprS [c]) src (pos + 3 + s1.length)))

theorem multilineLiteralSpec_proven : MultilineLiteralSpec := by
  refine ⟨?_, ?_, ?_⟩
  · intro cfg src r pos fuel nl s q rest hr hnl hq hs hhead hrest h
    have hg : src[pos]? = some 39 := getElem?_of_drop (r := [39, 39] ++ nl ++ s ++ q ++ [39, 39, 39] ++ rest)
      (by rw [h]; simp)
    have hst3 : startsAt src pos [39, 39, 39] = true :=
      startsAt_of_drop (r := nl ++ s ++ q ++ [39, 39, 39] ++ rest) (by rw [h]; simp)
    have hd3 : src.drop (pos + 3) = nl ++ (s ++ q ++ [39, 39, 39] ++ rest) := by
      simpa using drop_add_of_drop (a := [39, 39, 39]) (by rw [h]; simp)
    have hn39 : 39 ∉ s := fun m => (hs 39 m).1 rfl
    obtain ⟨p, hp, hpp, hdp⟩ : ∃ p, (if startsAt src (pos + 3) [10] = true then pos + 3 + 1 else pos + 3) = p ∧
        p = pos + 3 + nl.length ∧ src.drop p = s ++ (q ++ [39, 39, 39] ++ rest) := by
      rcases hnl with rfl | rfl
      · have hns : startsAt src (pos + 3) [10] = false := by
          have hd' : src.drop (pos + 3) = s ++ q ++ [39, 39, 39] ++ rest := by simpa using hd3
          unfold startsAt; rw [hd']
          cases hx : s ++ q with
          | nil => simp [List.isPrefixOf]
          | cons c t =>
            have := hhead rfl
            rw [hx] at this; simp at this
            simp [List.isPrefixOf, Ne.symm this]
        exact ⟨pos + 3, by simp [hns], by simp, by simpa using hd3⟩
      · have hys : startsAt src (pos + 3) [10] = true := startsAt_of_drop (by simpa using hd3)
        exact ⟨pos + 3 + 1, by simp [hys], by simp, by simpa using drop_succ_of_drop (c := 10) (by simpa using hd3)⟩
    subst hpp
    have hfind : findSub [39, 39, 39] (src.drop (pos + 3 + nl.length)) = some s.length := by
      rw [hdp]
      refine findSub_triple hn39 ?_
      rcases hq with rfl | rfl | rfl <;> simp [List.isPrefixOf]
    have hsl : sl src (pos + 3 + nl.length) (pos + 3 + nl.length + s.length) = s := sl_of_drop hdp
    have hfi : firstIdx illegalMl s = none := firstIdx_none (fun x hx => (hs x hx).2)
    have hdq : src.drop (pos + 3 + nl.length + s.length + 3) = q ++ rest := by
      have := drop_add_of_drop (a := s ++ [39, 39, 39]) (r := q ++ rest) (by
        rw [hdp]; rcases hq with rfl | rfl | rfl <;> simp)
      simp only [List.length_append, List.length_cons, List.length_nil] at this
      rw [show pos + 3 + nl.length + s.length + 3 = pos + 3 + nl.length + (s.length + (0 + 1 + 1 + 1)) by omega]
      exact this
    simp only [parseValue, hg, show (some 39 == some 34) = false from rfl, show (some 39 == some 39) = true from rfl,
      Bool.false_eq_true, ite_false, ite_true, hst3,
      need_ok (Nat.le_trans (parseMultilineStrN_lit_le src pos) hr), parseMultilineStr, hp, skipUntil, hfind,
      hsl, hfi, bind, Except.bind, pure, Except.pure, Except.map]
    rcases hq with rfl | rfl | rfl
    · have h1 : startsAt src (pos + 3 + nl.length + s.length + 3) [39] = false := by
        unfold startsAt; rw [hdq]
        cases rest with
        | nil => rfl
        | cons c r => have := hrest c rfl; simp [List.isPrefixOf, Ne.symm this]
      simp [h1]; omega
    · have h1 : startsAt src (pos + 3 + nl.length + s.length + 3) [39] = true := startsAt_of_drop (by simpa using hdq)
      have h2 : startsAt src (pos + 3 + nl.length + s.length + 3 + 1) [39] = false := by
        unfold startsAt; rw [drop_succ_of_drop (by simpa using hdq)]
        cases rest with
        | nil => rfl
        | cons c r => have := hrest c rfl; simp [List.isPrefixOf, Ne.symm this]
      simp [h1, h2]; omega
    · have h1 : startsAt src (pos + 3 + nl.length + s.length + 3) [39] = true := startsAt_of_drop (by simpa using hdq)
      have hd1 : src.drop (pos + 3 + nl.length + s.length + 3 + 1) = 39 :: rest := drop_succ_of_drop (by simpa using hdq)
      have h2 : startsAt src (pos + 3 + nl.length + s.length + 3 + 1) [39] = true := startsAt_of_drop (by simpa using hd1)
      simp [h1, h2]; omega
  · intro cfg src r pos fuel s hr hs h
    have hg : src[pos]? = some 39 := getElem?_of_drop (r := [39, 39] ++ s) (by rw [h]; simp)
    have hst3 : startsAt src pos [39, 39, 39] = true := startsAt_of_drop (r := s) (by rw [h])
    have hd3 : src.drop (pos + 3) = s := by simpa using drop_add_of_drop (a := [39, 39, 39]) (by rw [h])
    have hnone : ∀ p, p = pos + 3 ∨ p = pos + 3 + 1 → findSub [39, 39, 39] (src.drop p) = none := by
      intro p hp
      rcases hp with rfl | rfl
      · rw [hd3]; exact findSub_triple_none hs
      · rw [show pos + 3 + 1 = (pos + 3) + 1 from rfl, ← List.drop_drop, hd3]
        exact findSub_triple_none (fun m => hs (List.mem_of_mem_drop m))
    simp only [parseValue, hg, show (some 39 == some 34) = false from rfl, show (some 39 == some 39) = true from rfl,
      Bool.false_eq_true, ite_false, ite_true, hst3,
      need_ok (Nat.le_trans (parseMultilineStrN_lit_le src pos) hr), parseMultilineStr]
    split
    · simp [skipUntil, hnone (pos + 3 + 1) (Or.inr rfl), bind, Except.bind, Except.map]
    · simp [skipUntil, hnone (pos + 3) (Or.inl rfl), bind, Except.bind, Except.map]
  · intro cfg src r pos fuel c s1 s2 rest hr hs1 h10 hc hs2 h
    have hc39 : c ≠ 39 := by intro e; subst e; simp [illegalMl, asciiCtrl] at hc
    have hg : src[pos]? = some 39 := getElem?_of_drop (r := [39, 39] ++ s1 ++ c :: s2 ++ [39, 39, 39] ++ rest)
      (by rw [h]; simp)
    have hst3 : startsAt src pos [39, 39, 39] = true :=
      startsAt_of_drop (r := s1 ++ c :: s2 ++ [39, 39, 39] ++ rest) (by rw [h]; simp)
    have hd3 : src.drop (pos + 3) = (s1 ++ c :: s2) ++ ([39, 39, 39] ++ rest) := by
      simpa using drop_add_of_drop (a := [39, 39, 39]) (by rw [h]; simp)
    have hns : startsAt src (pos + 3) [10] = false := by
      unfold startsAt; rw [hd3]
      cases s1 with
      | nil =>
        have : c ≠ 10 := by intro e; subst e; simp [illegalMl, asciiCtrl] at hc
        simp [List.isPrefixOf, Ne.symm this]
      | cons x xs => simp at h10; simp [List.isPrefixOf, Ne.symm h10]
    have hn39 : 39 ∉ s1 ++ c :: s2 := by
      simp only [List.mem_append, List.mem_cons, not_or]
      exact ⟨fun m => (hs1 39 m).1 rfl, fun e => hc39 e.symm, hs2⟩
    have hfind : findSub [39, 39, 39] (src.drop (pos + 3)) = some (s1 ++ c :: s2).length := by
      rw [hd3]; exact findSub_triple hn39 (by simp [List.isPrefixOf])
    have hsl : sl src (pos + 3) (pos + 3 + (s1 ++ c :: s2).length) = s1 ++ c :: s2 := sl_of_drop hd3
    have hfi : firstIdx illegalMl (s1 ++ c :: s2) = some s1.length :=
      firstIdx_append (fun x hx => (hs1 x hx).2) hc
    have hgc : src.getD (pos + 3 + s1.length) 0 = c := by
      have : src.drop (pos + 3 + s1.length) = c :: (s2 ++ ([39, 39, 39] ++ rest)) :=
        drop_add_of_drop (a := s1) (by simpa using hd3)
      simp [List.getD, getElem?_of_drop this]
    simp only [parseValue, hg, show (some 39 == some 34) = false from rfl, show (some 39 == some 39) = true from rfl,
      Bool.false_eq_true, ite_false, ite_true, hst3,
      need_ok (Nat.le_trans (parseMultilineStrN_lit_le src pos) hr), parseMultilineStr, hns, skipUntil, hfind,
      hsl, hfi, hgc, bind, Except.bind, Except.map]

end PyLean.TextLibs.Toml
