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

/-- The first `'''` of `s ++ x` is at `len(s)` when `s` holds no `'''`, does not end with `'`,
and `x` starts with `'''`. -/
theorem findSub_triple_gen : ∀ (s x : Str), findSub [39, 39, 39] s = none → s.getLast? ≠ some 39 →
    [39, 39, 39].isPrefixOf x = true → findSub [39, 39, 39] (s ++ x) = some s.length
  | [], x, _, _, hx => by
    cases x with
    | nil => simp [List.isPrefixOf] at hx
    | cons c r => simp [findSub, hx]
  | c :: r, x, hn, hl, hx => by
    simp only [findSub] at hn
    split at hn
    · cases hn
    · next hpre =>
      have hr : findSub [39, 39, 39] r = none := by
        cases h : findSub [39, 39, 39] r with
        | none => rfl
        | some _ => rw [h] at hn; cases hn
      have hlr : r.getLast? ≠ some 39 := by
        cases r with
        | nil => simp
        | cons d t => rwa [List.getLast?_cons_cons] at hl
      have hnp : [39, 39, 39].isPrefixOf (c :: (r ++ x)) = false := by
        match r, hl, hpre with
        | [], hl, _ =>
          have : c ≠ 39 := by intro e; apply hl; simp [e]
          simp [List.isPrefixOf, Ne.symm this]
        | [d], hl, _ =>
          have : d ≠ 39 := by intro e; apply hl; simp [e]
          simp [List.isPrefixOf, Ne.symm this]
        | d :: e :: t, _, hpre => simpa [List.isPrefixOf] using hpre
      have ih := findSub_triple_gen r x hr hlr hx
      simp [findSub, hnp, ih]

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
without `'''` that does not end with `'` (one or two `'` inside are kept) and has no control
characters other than tab and newline, an optional newline right after `'''` (trimmed), and one or two `'` before the closing `'''` (kept), `parse_value` returns
the text and the position after the quotes; without a closing `'''` it raises "Expected \"'''\""
at the end of the document; a control character other than tab or newline before the closing
quotes raises "Found invalid character" there. -/
def MultilineLiteralSpec : Prop :=
  (∀ (cfg : Cfg) (src : Str) (r pos fuel : Nat) (nl s q rest : Str), 3 ≤ r → (nl = [] ∨ nl = [10]) →
    (q = [] ∨ q = [39] ∨ q = [39, 39]) → (∀ c ∈ s, illegalMl c = false) →
    findSub [39, 39, 39] s = none → s.getLast? ≠ some 39 →
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
  · intro cfg src r pos fuel nl s q rest hr hnl hq hs hns3 hlast hhead hrest h
    have hg : src[pos]? = some 39 := getElem?_of_drop (r := [39, 39] ++ nl ++ s ++ q ++ [39, 39, 39] ++ rest)
      (by rw [h]; simp)
    have hst3 : startsAt src pos [39, 39, 39] = true :=
      startsAt_of_drop (r := nl ++ s ++ q ++ [39, 39, 39] ++ rest) (by rw [h]; simp)
    have hd3 : src.drop (pos + 3) = nl ++ (s ++ q ++ [39, 39, 39] ++ rest) := by
      simpa using drop_add_of_drop (a := [39, 39, 39]) (by rw [h]; simp)
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
      refine findSub_triple_gen s _ hns3 hlast ?_
      rcases hq with rfl | rfl | rfl <;> simp [List.isPrefixOf]
    have hsl : sl src (pos + 3 + nl.length) (pos + 3 + nl.length + s.length) = s := sl_of_drop hdp
    have hfi : firstIdx illegalMl s = none := firstIdx_none hs
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

/-! ## Multi-line basic string errors, _parser.py:654-683 -/

/-- The multi-line loop of `parse_basic_str` over raw characters. -/
theorem mlRaw (src : Str) : ∀ (s : Str) (fuel pos start : Nat) (res rest : Str),
    (∀ x ∈ s, x ≠ 34 ∧ x ≠ 92 ∧ illegalMl x = false) → src.drop pos = s ++ rest →
    basicStrLoop src true (fuel + s.length) pos start res = basicStrLoop src true fuel (pos + s.length) start res
  | [], _, _, _, _, _, _, _ => by simp
  | c :: t, fuel, pos, start, res, rest, hs, h => by
    obtain ⟨h34, h92, hill⟩ := hs c (by simp)
    have h1 : src.drop pos = c :: (t ++ rest) := by simpa using h
    have hg := getElem?_of_drop h1
    have ih := mlRaw src t fuel (pos + 1) start res rest (fun x hx => hs x (by simp [hx])) (drop_succ_of_drop h1)
    rw [show fuel + (c :: t).length = (fuel + t.length) + 1 by simp; omega]
    simp only [basicStrLoop, hg, beq_iff_eq, h34, h92, ite_false, hill, Bool.false_eq_true, ite_true, if_true]
    rw [ih]; congr 1; simp; omega

/-- Multi-line basic strings, TOML 1.1 "String" ("Any Unicode character may be used except those
that must be escaped: backslash and the control characters other than tab, line feed, and
carriage return"), with at least six frames left: `"""`, an optional newline, characters, then a
control character other than tab and newline raises "Illegal character" there; `"""`, an optional
newline and characters up to the end of the document raise "Unterminated string" at the end. -/
def MultilineBasicErrors : Prop :=
  (∀ (cfg : Cfg) (src : Str) (r pos fuel : Nat) (nl s : Str) (c : Nat) (rest : Str), 6 ≤ r →
    (nl = [] ∨ nl = [10]) → (∀ x ∈ s, x ≠ 34 ∧ x ≠ 92 ∧ illegalMl x = false) → illegalMl c = true →
    (nl = [] → s.head? ≠ some 10) → src.drop pos = [34, 34, 34] ++ nl ++ s ++ c :: rest →
    parseValue cfg src r (fuel + 1) pos =
      .error (tde (S "Illegal character " ++ reprS [c]) src (pos + 3 + nl.length + s.length))) ∧
  (∀ (cfg : Cfg) (src : Str) (r pos fuel : Nat) (nl s : Str), 6 ≤ r → (nl = [] ∨ nl = [10]) →
    (∀ x ∈ s, x ≠ 34 ∧ x ≠ 92 ∧ illegalMl x = false) → (nl = [] → s.head? ≠ some 10) →
    src.drop pos = [34, 34, 34] ++ nl ++ s →
    parseValue cfg src r (fuel + 1) pos = .error (tdeS "Unterminated string" src (pos + 3 + nl.length + s.length)))

/-- `"""` and the optional newline: the position where `parse_basic_str` starts. -/
theorem ml_open {src : Str} {pos : Nat} {nl t : Str} (hnl : nl = [] ∨ nl = [10]) (hh : nl = [] → t.head? ≠ some 10)
    (h : src.drop pos = [34, 34, 34] ++ nl ++ t) :
    (if startsAt src (pos + 3) [10] = true then pos + 3 + 1 else pos + 3) = pos + 3 + nl.length ∧
      src.drop (pos + 3 + nl.length) = t := by
  have hd3 : src.drop (pos + 3) = nl ++ t := by
    simpa using drop_add_of_drop (a := [34, 34, 34]) (by rw [h]; simp)
  rcases hnl with rfl | rfl
  · have hns : startsAt src (pos + 3) [10] = false := by
      unfold startsAt; rw [hd3]
      cases ht : t with
      | nil => rfl
      | cons c r => have := hh rfl; rw [ht] at this; simp at this; simp [List.isPrefixOf, Ne.symm this]
    exact ⟨by simp [hns], by simpa using hd3⟩
  · have hys : startsAt src (pos + 3) [10] = true := startsAt_of_drop (by simpa using hd3)
    exact ⟨by simp [hys], by simpa using drop_succ_of_drop (c := 10) (by simpa using hd3)⟩

theorem multilineBasicErrors_proven : MultilineBasicErrors := by
  refine ⟨?_, ?_⟩
  · intro cfg src r pos fuel nl s c rest hr hnl hs hc hh h
    have hc34 : c ≠ 34 := by intro e; subst e; simp [illegalMl, asciiCtrl] at hc
    have hc92 : c ≠ 92 := by intro e; subst e; simp [illegalMl, asciiCtrl] at hc
    have hg : src[pos]? = some 34 := getElem?_of_drop (r := [34, 34] ++ nl ++ s ++ c :: rest) (by rw [h]; simp)
    have hst3 : startsAt src pos [34, 34, 34] = true := startsAt_of_drop (r := nl ++ s ++ c :: rest) (by rw [h]; simp)
    obtain ⟨hp, hdp⟩ := ml_open (t := s ++ c :: rest) hnl
      (by intro e; cases s with
        | nil => simp; intro e'; subst e'; simp [illegalMl, asciiCtrl] at hc
        | cons x xs => have := hh e; simpa using this) (by rw [h]; simp)
    have hlen : s.length < src.length + 1 := by have := congrArg List.length h; simp at this; omega
    have hloop := mlRaw src s (src.length + 1 - s.length) (pos + 3 + nl.length) (pos + 3 + nl.length) [] (c :: rest) hs hdp
    rw [show src.length + 1 - s.length + s.length = src.length + 1 by omega] at hloop
    obtain ⟨f, hf⟩ : ∃ f, src.length + 1 - s.length = f + 1 := ⟨src.length - s.length, by omega⟩
    have hgc : src[pos + 3 + nl.length + s.length]? = some c := getElem?_of_drop (by simpa using drop_add_of_drop hdp)
    have hstep : basicStrLoop src true (src.length + 1 - s.length) (pos + 3 + nl.length + s.length)
        (pos + 3 + nl.length) [] = .error (tde (S "Illegal character " ++ reprS [c]) src (pos + 3 + nl.length + s.length)) := by
      rw [hf]; simp [basicStrLoop, hgc, hc34, hc92, hc]
    simp only [parseValue, hg, show (some 34 == some 34) = true from rfl, ite_true, hst3,
      need_ok (Nat.le_trans (parseMultilineStrN_le src pos false) hr), parseMultilineStr, hp, Bool.false_eq_true,
      ite_false, parseBasicStr, hloop, hstep, bind, Except.bind, Except.map]
  · intro cfg src r pos fuel nl s hr hnl hs hh h
    have hg : src[pos]? = some 34 := getElem?_of_drop (r := [34, 34] ++ nl ++ s) (by rw [h]; simp)
    have hst3 : startsAt src pos [34, 34, 34] = true := startsAt_of_drop (r := nl ++ s) (by rw [h]; simp)
    obtain ⟨hp, hdp⟩ := ml_open (t := s ++ []) hnl (by simpa using hh) (by rw [h]; simp)
    have hlen : s.length < src.length + 1 := by have := congrArg List.length h; simp at this; omega
    have hloop := mlRaw src s (src.length + 1 - s.length) (pos + 3 + nl.length) (pos + 3 + nl.length) [] [] hs hdp
    rw [show src.length + 1 - s.length + s.length = src.length + 1 by omega] at hloop
    obtain ⟨f, hf⟩ : ∃ f, src.length + 1 - s.length = f + 1 := ⟨src.length - s.length, by omega⟩
    have hgn : src[pos + 3 + nl.length + s.length]? = none := getElem?_of_drop_nil (by simpa using drop_add_of_drop hdp)
    have hstep : basicStrLoop src true (src.length + 1 - s.length) (pos + 3 + nl.length + s.length)
        (pos + 3 + nl.length) [] = .error (tdeS "Unterminated string" src (pos + 3 + nl.length + s.length)) := by
      rw [hf]; simp [basicStrLoop, hgn]
    simp only [parseValue, hg, show (some 34 == some 34) = true from rfl, ite_true, hst3,
      need_ok (Nat.le_trans (parseMultilineStrN_le src pos false) hr), parseMultilineStr, hp, Bool.false_eq_true,
      ite_false, parseBasicStr, hloop, hstep, bind, Except.bind, Except.map]

/-! ## Dotted keys inside inline tables, _parser.py:540-563 -/

/-- Inline tables, TOML 1.1 "Inline Table" (keys may be dotted, as in `{ type.name = "pug" }`),
with fillers around `,` and before `}`: for all bare keys `a`, `b ≠ c` and values `v`, `w` of
`ArrayTableSpec`, `{a.b=v, a.c=w}` gives `{a: {b: v, c: w}}` and the position after `}`. With
`3 * depth + 16` frames left for the deeper value. -/
def InlineDotted : Prop :=
  ∀ (cfg : Cfg) (src : Str) (r pos fuel : Nat) (lead fa fb fc : List Fill) (a b c : Str) (v w : SV) (rest : Str),
    (∀ f ∈ lead, f.ok) → (∀ f ∈ fa, f.ok) → (∀ f ∈ fb, f.ok) → (∀ f ∈ fc, f.ok) →
    bareOk a → bareOk b → bareOk c → b ≠ c → v.ok → w.ok →
    2 ≤ cfg.maxKeyParts → 3 * v.depth + 16 ≤ r → 3 * w.depth + 16 ≤ r → v.need + w.need + 8 ≤ fuel →
    src.drop pos = 123 :: fillEnc lead ++ a ++ 46 :: b ++ 61 :: v.enc ++ fillEnc fa ++ 44 :: fillEnc fb ++
      a ++ 46 :: c ++ 61 :: w.enc ++ fillEnc fc ++ 125 :: rest →
    parseValue cfg src r fuel pos =
      .ok (pos + 1 + (fillEnc lead).length + (a ++ 46 :: b).length + 1 + v.enc.length + (fillEnc fa).length + 1 +
        (fillEnc fb).length + (a ++ 46 :: c).length + 1 + w.enc.length + (fillEnc fc).length + 1,
        .tbl [(a, .tbl [(b, v.val), (c, w.val)])])

theorem inlineDotted_proven : InlineDotted := by
  intro cfg src r pos fuel lead fa fb fc a b c v w rest hlead hfa hfb hfc ha hb hc hbc hv hw hmax hrv hrw hf h
  obtain ⟨g, rfl⟩ : ∃ g, fuel = g + 1 + 1 + 1 + 1 + 1 := ⟨fuel - 5, by omega⟩
  have hps : ∀ z, bareOk z → ∀ p ∈ [KPart.bare z], p.ok := by intro z hz p hp; simp at hp; subst hp; exact hz
  have hmax2 : [KPart.bare b].length + 1 ≤ cfg.maxKeyParts := by simp; omega
  have hcb : c ≠ b := Ne.symm hbc
  have h0 : src.drop pos = 123 :: fillEnc lead ++ (keyEnc (.bare a) [.bare b] ++ (61 :: v.enc ++ (fillEnc fa ++
      44 :: fillEnc fb ++ a ++ 46 :: c ++ 61 :: w.enc ++ fillEnc fc ++ 125 :: rest))) := by
    rw [h, keyEnc_bare2]; simp
  rw [parseValue_brace hlead (keyEnc_notFill (bareOk_kpart ha) _).1 (keyEnc_notFill (bareOk_kpart ha) _).2
    (by omega) h0]
  have hd1 : src.drop (pos + 1 + (fillEnc lead).length) = keyEnc (.bare a) [.bare b] ++ 61 :: v.enc ++
      (fillEnc fa ++ 44 :: fillEnc fb ++ (a ++ 46 :: c ++ 61 :: w.enc ++ fillEnc fc ++ 125 :: rest)) :=
    drop_of_eq_pre (a := 123 :: fillEnc lead) (by rw [h, keyEnc_bare2]; simp) (by simp; omega)
  have hv34 := fill_head_ne34 fa hfa (44 :: fillEnc fb) (by intro x hx; simp at hx; omega)
  rw [inline_entry (g := g + 1) (bareOk_kpart ha) (hps b hb) hmax2 hv
    (fun x hx => hv34 x (by simpa using hx)) (by omega) (by omega) hd1, keyEnc_bare2, keyVal_bare2]
  -- the first entry and the comma
  generalize hP2 : pos + 1 + (fillEnc lead).length + (a ++ 46 :: b).length + 1 + v.enc.length = P2
  have hd2 : src.drop P2 = fillEnc fa ++ (44 :: (fillEnc fb ++ (a ++ 46 :: c ++ 61 :: w.enc ++ fillEnc fc ++
      125 :: rest))) :=
    drop_of_eq_pre (a := 123 :: fillEnc lead ++ (a ++ 46 :: b) ++ 61 :: v.enc) (by rw [h]; simp)
      (by rw [← hP2]; simp; omega)
  have hsk := skipCawF_fill hfa (notFill_44 _) hd2
  have hd2c : src.drop (P2 + (fillEnc fa).length) = [44] ++ (fillEnc fb ++ (a ++ 46 :: c ++ 61 :: w.enc ++
      fillEnc fc ++ 125 :: rest)) := by simpa using drop_add_of_drop hd2
  have hcomma := sl_of_drop hd2c
  simp only [List.length_singleton] at hcomma
  have hd3 : src.drop (P2 + (fillEnc fa).length + 1) = fillEnc fb ++ (a ++ 46 :: c ++ 61 :: w.enc ++
      fillEnc fc ++ 125 :: rest) := drop_add_of_drop hd2c
  obtain ⟨a0, at', hat, ha0⟩ := bare_head ha
  have hnf2 : notFill (a ++ 46 :: c ++ 61 :: w.enc ++ fillEnc fc ++ 125 :: rest) := by
    rw [hat]; intro x hx; simp at hx; subst hx; obtain ⟨-, hw0, h10, -, h35, -⟩ := bare_char ha0
    exact ⟨by simp [tomlWsNl, hw0, h10], h35⟩
  have hsk2 := skipCawF_fill hfb hnf2 hd3
  have hd4 : src.drop (P2 + (fillEnc fa).length + 1 + (fillEnc fb).length) = keyEnc (.bare a) [.bare c] ++
      61 :: w.enc ++ (fillEnc fc ++ 125 :: rest) := by
    rw [keyEnc_bare2]; have := drop_add_of_drop hd3; simpa using this
  have hst : startsAt src (P2 + (fillEnc fa).length + 1 + (fillEnc fb).length) [125] = false := by
    unfold startsAt; rw [hd4, keyEnc_bare2, hat]
    have : a0 ≠ 125 := by intro e; subst e; simp [bareKey, inR] at ha0
    simp [List.isPrefixOf, Ne.symm this]
  have his1 : Flags.init.is_ [a, b] FROZEN = false := by simp [Flags.init, Flags.is_, isAux, dget_nil]
  have hfl : ∀ fl : Flags, fl = Flags.init ∨ fl = { tree := fsetAux FROZEN true [a, b] [], pending := [] } →
      fl.is_ [a, c] FROZEN = false := by
    intro fl hfl
    rcases hfl with rfl | rfl
    · simp [Flags.init, Flags.is_, isAux, dget_nil]
    · simp [Flags.is_, isAux, fsetAux, dset, dget_cons, dget_nil, hcb, FNode.empty, FNode.rflags, FNode.nested,
        FNode.flags, addFlag]
  simp only [inlineBody, his1, Bool.false_eq_true, ite_false, show ([a, b] : Key).dropLast = [a] from rfl,
    show ([a, b] : Key).getLastD [] = b from rfl, withNest_empty, dget_nil, Option.isSome_none, dset_nil,
    Except.map, overwriteErr, bind, Except.bind, nestDict, need_skipCaw (show 4 ≤ r - 1 by omega), hsk, hcomma,
    show ([44] == [125]) = false from rfl, show ([44] != [44]) = false from rfl, hsk2, hst]
  -- the second entry
  have hrest2 : ∀ x, (fillEnc fc ++ 125 :: rest).head? = some x → x ≠ 34 :=
    fill_head_ne34 fc hfc _ (by intro x hx; simp at hx; omega)
  generalize hP5 : P2 + (fillEnc fa).length + 1 + (fillEnc fb).length + (a ++ 46 :: c).length + 1 + w.enc.length = P5
  have hd5 : src.drop P5 = fillEnc fc ++ (125 :: rest) := by
    exact drop_of_eq_pre (a := 123 :: fillEnc lead ++ (a ++ 46 :: b) ++ 61 :: v.enc ++ fillEnc fa ++ 44 :: fillEnc fb ++
      (a ++ 46 :: c) ++ 61 :: w.enc) (by rw [h]; simp) (by rw [← hP5, ← hP2]; simp; omega)
  have hsk3 := skipCawF_fill hfc (notFill_125 rest) hd5
  have hd6 : src.drop (P5 + (fillEnc fc).length) = [125] ++ rest := by simpa using drop_add_of_drop hd5
  have hclose := sl_of_drop hd6
  simp only [List.length_singleton] at hclose
  have hdc : dget [(b, v.val)] c = none := by simp [dget_cons, dget_nil, hcb]
  cases hvd : v.val.isDictOrList
  · simp only [Bool.false_eq_true, ite_false, pure, Except.pure]
    rw [inline_entry (g := g) (bareOk_kpart ha) (hps c hc) (by simp; omega) hw hrest2 (by omega) (by omega) hd4,
      keyEnc_bare2, keyVal_bare2, hP5]
    simp only [inlineBody, hfl Flags.init (Or.inl rfl), Bool.false_eq_true, ite_false,
      show ([a, c] : Key).dropLast = [a] from rfl, show ([a, c] : Key).getLastD [] = c from rfl, withNest,
      dget_cons, ite_true, Option.isSome_some, hdc, Option.isSome_none, overwriteErr, bind,
      Except.bind, need_skipCaw (show 4 ≤ r - 1 by omega), hsk3, hclose, show ([125] == [125]) = true from rfl,
      pure, Except.pure]
    simp [dset, dget_cons, hcb, hbc]
  · simp only [ite_true, Flags.set, List.isEmpty_cons, Bool.false_eq_true, ite_false, Flags.init]
    rw [inline_entry (g := g) (bareOk_kpart ha) (hps c hc) (by simp; omega) hw hrest2 (by omega) (by omega) hd4,
      keyEnc_bare2, keyVal_bare2, hP5]
    simp only [inlineBody, hfl _ (Or.inr rfl), Bool.false_eq_true, ite_false,
      show ([a, c] : Key).dropLast = [a] from rfl, show ([a, c] : Key).getLastD [] = c from rfl, withNest,
      dget_cons, ite_true, Option.isSome_some, hdc, Option.isSome_none, overwriteErr, bind,
      Except.bind, need_skipCaw (show 4 ≤ r - 1 by omega), hsk3, hclose, show ([125] == [125]) = true from rfl,
      pure, Except.pure]
    simp [dset, dget_cons, hcb, hbc]

end PyLean.TextLibs.Toml
