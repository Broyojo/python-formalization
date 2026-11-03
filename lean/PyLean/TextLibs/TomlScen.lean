import PyLean.TextLibs.TomlDepth
import PyLean.TextLibs.TomlPending
import PyLean.TextLibs.TomlErrors

/-!
Documents that tell the table and flag rules apart: pending flags, `finalize_pending`,
`unset_all`, recursive (`FROZEN`) flags, `get_or_create_nest`, nested arrays of tables, and the
errors of `create_dict_rule`, `create_list_rule` and `key_value_rule`. Keys are bare (`A-Za-z0-9_-`);
the rules compare keys only for equality.
-/

namespace PyLean.TextLibs.Toml

/-- A bare key part, TOML 1.1 "Keys". -/
def bareOk (x : Str) : Prop := x ≠ [] ∧ ∀ c ∈ x, bareKey c = true

theorem bareOk_kpart {x : Str} (h : bareOk x) : (KPart.bare x).ok := h

theorem bare_char {c : Nat} (h : bareKey c = true) :
    keyInitial c = true ∧ tomlWs c = false ∧ c ≠ 10 ∧ c ≠ 91 ∧ c ≠ 35 ∧ c ≠ 13 ∧ c ≠ 46 ∧ c ≠ 61 ∧ c ≠ 93 ∧
      c ≠ 34 := by
  refine ⟨by simp [keyInitial, h], ?_⟩
  simp [bareKey, inR] at h; simp [tomlWs]; omega

theorem bare_head {x : Str} (h : bareOk x) : ∃ c t, x = c :: t ∧ bareKey c = true := by
  obtain ⟨hne, hall⟩ := h
  cases x with
  | nil => exact absurd rfl hne
  | cons c t => exact ⟨c, t, rfl, hall c (by simp)⟩

theorem bare_no13 {x : Str} (h : bareOk x) : 13 ∉ x := fun m => absurd (h.2 13 m) (by decide)

theorem boolText_no13 (b : Bool) : 13 ∉ (if b then S "true" else S "false") := by cases b <;> decide

/-- `parse_key_value_pair` on `K=v` for a dotted key and a value of `ArrayTableSpec`. -/
theorem pkv_at {cfg : Cfg} {src : Str} {r pos fuel : Nat} {p0 : KPart} {ps : List KPart} {v : SV} {rest : Str}
    (h0 : p0.ok) (hps : ∀ p ∈ ps, p.ok) (hmax : ps.length + 1 ≤ cfg.maxKeyParts) (hv : v.ok)
    (hr34 : ∀ c, rest.head? = some c → c ≠ 34) (hf : v.need ≤ fuel) (hr : 3 * v.depth + 11 ≤ r)
    (h : src.drop pos = keyEnc p0 ps ++ 61 :: v.enc ++ rest) :
    parseKeyValuePair cfg src r (fuel + 1) pos =
      .ok (pos + (keyEnc p0 ps).length + 1 + v.enc.length, keyVal p0 ps, v.val) := by
  have hk := parseKey_enc (maxK := cfg.maxKeyParts) (src := src) (pos := pos) h0 hps hmax
    (rest := 61 :: (v.enc ++ rest)) (by intro c hc; simp at hc; subst hc; decide) (by simpa using h)
  have hd : src.drop (pos + (keyEnc p0 ps).length) = 61 :: (v.enc ++ rest) := by
    simpa using drop_add_of_drop (a := keyEnc p0 ps) (by simpa using h)
  have hg := getElem?_of_drop hd
  have hd1 : src.drop (pos + (keyEnc p0 ps).length + 1) = v.enc ++ rest := drop_succ_of_drop hd
  have hsk : skipChars src (pos + (keyEnc p0 ps).length + 1) tomlWs = pos + (keyEnc p0 ps).length + 1 :=
    skipChars_stop (fun c hc => by rw [hd1] at hc; exact ((SV.head_props v rest).2 c hc).2.2.2)
  have hvp := SV.parse cfg src v (r - 1) _ fuel rest hv hr34 hd1 hf (by omega)
  simp only [parseKeyValuePair, need_parseKey (show 8 ≤ r by omega), hk, bind, Except.bind, hg,
    show (some 61 != some 61) = false from rfl, Bool.false_eq_true, ite_false, hsk,
    need_ok (show 1 ≤ r by omega), hvp, pure, Except.pure]

/-- One round of the statement loop on a key/value line, under any header. -/
theorem mainLoop_kv_hdr {cfg : Cfg} {src : Str} {R f pos p c : Nat} {out out' : Out} {header : Key}
    (hc : src[pos]? = some c) (hkey : keyInitial c = true) (hws : tomlWs c = false) (h10 : c ≠ 10)
    (hrule : keyValueRule cfg src (R - 1) pos out header = .ok (p, out')) (hR : 3 ≤ R) :
    mainLoop cfg src R (f + 1) pos out header =
      if src[p]? = none then .ok out'.data
      else if src[p]? = some 10 then mainLoop cfg src R f (p + 1) out' header
      else mainLoop cfg src R (f + 1) pos out header := by
  have hs0 : skipChars src pos tomlWs = pos := skipChars_at hc hws
  have hb : (c == 10) = false := by simp [h10]
  rcases hp : src[p]? with _ | d
  · have hs1 : skipChars src p tomlWs = p := skipChars_stop (fun x hx => by rw [List.head?_drop, hp] at hx; cases hx)
    have hcm : skipComment src p = .ok p := by simp [skipComment, hp]
    simp only [mainLoop, hs0, hc, hb, Bool.false_eq_true, ite_false, hkey, ite_true, need_ok (show 1 ≤ R by omega),
      hrule, bind, Except.bind, pure, Except.pure, hs1, need_skipComment hR, hcm, hp]
    try simp
  · by_cases hd : d = 10
    · subst hd
      have hs1 : skipChars src p tomlWs = p := skipChars_at hp (by decide)
      have hcm : skipComment src p = .ok p := by simp [skipComment, hp]
      simp only [mainLoop, hs0, hc, hb, Bool.false_eq_true, ite_false, hkey, ite_true, need_ok (show 1 ≤ R by omega),
        hrule, bind, Except.bind, pure, Except.pure, hs1, need_skipComment hR, hcm, hp,
        show ((10 : Nat) != 10) = false from rfl]
      try simp
    · simp [hd]

/-- ... whose rule raises. -/
theorem mainLoop_kv_err {cfg : Cfg} {src : Str} {R f pos c : Nat} {out : Out} {header : Key} {e : PyExc}
    (hc : src[pos]? = some c) (hkey : keyInitial c = true) (hws : tomlWs c = false) (h10 : c ≠ 10)
    (hrule : keyValueRule cfg src (R - 1) pos out header = .error e) (hR : 3 ≤ R) :
    mainLoop cfg src R (f + 1) pos out header = .error e := by
  have hs0 : skipChars src pos tomlWs = pos := skipChars_at hc hws
  have hb : (c == 10) = false := by simp [h10]
  simp only [mainLoop, hs0, hc, hb, Bool.false_eq_true, ite_false, hkey, ite_true, need_ok (show 1 ≤ R by omega),
    hrule, bind, Except.bind]

theorem dget_cons {α : Type} (k k' : Str) (v : α) (d : List (Str × α)) :
    dget ((k, v) :: d) k' = if k' = k then some v else dget d k' := by
  by_cases h : k' = k
  · subst h; simp [dget, List.lookup]
  · have : (k' == k) = false := by simp [h]
    simp [dget, List.lookup, this, h]

/-! ## Pending flags, _parser.py:235-241, 415-446 -/

/-- Dotted keys, TOML 1.1 "Keys" ("Dotted keys create and define a table for each key part
before the last one"; defining `a.b` then `a.c` is valid): for all bare keys `a`, `b ≠ c` and
booleans, `loads('a.b=X\na.c=Y')` gives `{a: {b: X, c: Y}}`. The tables a dotted key defines are
only marked pending (`add_pending`): marking them at once would make the second line raise
"Cannot redefine namespace". With at least sixteen frames left. -/
def PendingDotted : Prop :=
  ∀ (pf : ParseFloat) (maxK maxD : Nat) (tz : TzCache) (fr : Nat) (a b c : Str) (x y : Bool),
    bareOk a → bareOk b → bareOk c → b ≠ c → 2 ≤ maxK → 16 ≤ fr →
    loads pf maxK maxD tz fr (.str (a ++ 46 :: b ++ 61 :: (if x then S "true" else S "false") ++
      10 :: a ++ 46 :: c ++ 61 :: (if y then S "true" else S "false"))) =
      .ok [(a, .tbl [(b, .bool x), (c, .bool y)])]

theorem pendingDotted_proven : PendingDotted := by
  intro pf maxK maxD tz fr a b c x y ha hb hc hbc hk hfr
  obtain ⟨a0, at', rfl, ha0⟩ := bare_head ha
  obtain ⟨hai, haws, ha10, -⟩ := bare_char ha0
  generalize hX : (if x then S "true" else S "false") = X
  generalize hY : (if y then S "true" else S "false") = Y
  generalize hsrc : (a0 :: at') ++ 46 :: b ++ 61 :: X ++ 10 :: (a0 :: at') ++ 46 :: c ++ 61 :: Y = src
  have h13 : 13 ∉ src := by
    rw [← hsrc, ← hX, ← hY]
    simp only [List.mem_append, List.mem_cons, not_or]
    have := bare_no13 ha; have := bare_no13 hb; have := bare_no13 hc
    have := boolText_no13 x; have := boolText_no13 y
    simp_all
  rw [loads_eq pf maxK maxD tz fr src h13 (by omega)]
  have hK : ∀ z, keyEnc (.bare (a0 :: at')) [.bare z] = (a0 :: at') ++ 46 :: z := by simp [keyEnc, KPart.enc]
  have hKv : ∀ z, keyVal (.bare (a0 :: at')) [.bare z] = [a0 :: at', z] := by simp [keyVal, KPart.val]
  have hps : ∀ z, bareOk z → ∀ p ∈ [KPart.bare z], p.ok := by intro z hz p hp; simp at hp; subst hp; exact hz
  have hcfg : (mkCfg pf maxK maxD tz).maxKeyParts = maxK := rfl
  -- line 1: `a.b=X`
  have hd0 : src.drop 0 = keyEnc (.bare (a0 :: at')) [.bare b] ++ 61 :: (SV.bool x).enc ++
      (10 :: (a0 :: at') ++ 46 :: c ++ 61 :: Y) := by
    rw [hK, ← hsrc, ← hX]; simp [SV.enc]
  have hp1 := pkv_at (cfg := mkCfg pf maxK maxD tz) (r := fr - 1 - 1 - 1) (fuel := vFuel src - 1) (bareOk_kpart ha)
    (hps b hb) (by rw [hcfg]; simp; omega) (show (SV.bool x).ok from trivial)
    (by intro c hc; simp at hc; omega) (by simp [SV.need]; unfold vFuel; omega)
    (by simp [SV.depth]; omega) hd0
  rw [hK, hKv, show vFuel src - 1 + 1 = vFuel src by unfold vFuel; omega] at hp1
  generalize hP1 : 0 + ((a0 :: at') ++ 46 :: b).length + 1 + (SV.bool x).enc.length = P1 at hp1
  have hr1 : keyValueRule (mkCfg pf maxK maxD tz) src (fr - 1 - 1) 0 Out.init [] =
      .ok (P1, { data := [(a0 :: at', .tbl [(b, .bool x)])],
                 flags := { tree := [], pending := [([a0 :: at'], EXPLICIT_NEST)] } }) := by
    simp only [keyValueRule, need_ok (show 1 ≤ fr - 1 - 1 by omega), hp1, bind, Except.bind]
    simp [contKeysLoop, Flags.is_, isAux, Out.init, Flags.init, Flags.addPending, withNest, dget, dset,
      overwriteErr, SV.val, TVal.isDictOrList, Except.map, pure, Except.pure, bind, Except.bind]
  have hg0 : src[0]? = some a0 := by rw [← hsrc]; rfl
  rw [mainLoop_kv_hdr hg0 hai haws ha10 hr1 (by omega)]
  have hdP1 : src.drop P1 = 10 :: ((a0 :: at') ++ 46 :: c ++ 61 :: Y) := by
    have := drop_add_of_drop (src := src) (pos := 0) (a := (a0 :: at') ++ 46 :: b ++ 61 :: (SV.bool x).enc)
      (r := 10 :: ((a0 :: at') ++ 46 :: c ++ 61 :: Y)) (by rw [hK] at hd0; simpa using hd0)
    have e : 0 + ((a0 :: at') ++ 46 :: b ++ 61 :: (SV.bool x).enc).length =
        0 + ((a0 :: at') ++ 46 :: b).length + 1 + (SV.bool x).enc.length := by simp; omega
    rw [← hP1, ← e]; exact this
  have hgP1 : src[P1]? = some 10 := getElem?_of_drop hdP1
  simp only [hgP1, reduceCtorEq, ite_false, ite_true]
  -- line 2: `a.c=Y`
  have hd2 : src.drop (P1 + 1) = keyEnc (.bare (a0 :: at')) [.bare c] ++ 61 :: (SV.bool y).enc ++ [] := by
    rw [drop_succ_of_drop hdP1, hK, ← hY]; simp [SV.enc]
  have hp2 := pkv_at (cfg := mkCfg pf maxK maxD tz) (r := fr - 1 - 1 - 1) (fuel := vFuel src - 1) (bareOk_kpart ha)
    (hps c hc) (by rw [hcfg]; simp; omega) (show (SV.bool y).ok from trivial)
    (by intro c hc; simp at hc) (by simp [SV.need]; unfold vFuel; omega)
    (by simp [SV.depth]; omega) hd2
  rw [hK, hKv, show vFuel src - 1 + 1 = vFuel src by unfold vFuel; omega] at hp2
  generalize hP2 : P1 + 1 + ((a0 :: at') ++ 46 :: c).length + 1 + (SV.bool y).enc.length = P2 at hp2
  have hcb : c ≠ b := Ne.symm hbc
  have hr2 : keyValueRule (mkCfg pf maxK maxD tz) src (fr - 1 - 1) (P1 + 1)
      { data := [(a0 :: at', .tbl [(b, .bool x)])],
        flags := { tree := [], pending := [([a0 :: at'], EXPLICIT_NEST)] } } [] =
      .ok (P2, { data := [(a0 :: at', .tbl [(b, .bool x), (c, .bool y)])],
                 flags := { tree := [], pending := [([a0 :: at'], EXPLICIT_NEST)] } }) := by
    simp only [keyValueRule, need_ok (show 1 ≤ fr - 1 - 1 by omega), hp2, bind, Except.bind]
    simp [contKeysLoop, Flags.is_, isAux, Flags.addPending, withNest, dget_cons, dget_nil, dset, hcb,
      overwriteErr, SV.val, TVal.isDictOrList, Except.map, pure, Except.pure, bind, Except.bind]
  have hgP1' : src[P1 + 1]? = some a0 := getElem?_of_drop (r := at' ++ 46 :: c ++ 61 :: Y) (by
    rw [drop_succ_of_drop hdP1]; simp)
  obtain ⟨f, hf⟩ : ∃ f, src.length = f + 1 := ⟨src.length - 1, by rw [← hsrc]; simp⟩
  rw [hf, mainLoop_kv_hdr hgP1' hai haws ha10 hr2 (by omega)]
  have hXl : (SV.bool x).enc.length = X.length := by rw [← hX]; rfl
  have hYl : (SV.bool y).enc.length = Y.length := by rw [← hY]; rfl
  have hlen : src.length = (a0 :: at').length + 1 + b.length + 1 + X.length + 1 + (a0 :: at').length + 1 +
      c.length + 1 + Y.length := by rw [← hsrc]; simp; omega
  have hend : src[P2]? = none := by
    rw [List.getElem?_eq_none_iff, ← hP2, ← hP1, hXl, hYl, hlen]; simp; omega
  simp [hend]

/-! ## `unset_all` and nested arrays of tables, _parser.py:243-249, 285-311, 392-412 -/

theorem keyEnc_bare (a : Str) : keyEnc (.bare a) [] = a := by simp [keyEnc, KPart.enc]
theorem keyVal_bare (a : Str) : keyVal (.bare a) [] = [a] := by simp [keyVal, KPart.val]
theorem keyEnc_bare2 (a b : Str) : keyEnc (.bare a) [.bare b] = a ++ 46 :: b := by simp [keyEnc, KPart.enc]
theorem keyVal_bare2 (a b : Str) : keyVal (.bare a) [.bare b] = [a, b] := by simp [keyVal, KPart.val]

/-- Arrays of tables, TOML 1.1 ("Any reference to an array of tables points to the most recently
defined table element of the array"; a table defined once cannot be defined again): for all bare
keys `a ≠ b`, `loads('[a]\n[[b]]\n[a]')` raises "Cannot declare ('a',) twice" at the position
after the last `a`. Starting the array `b` drops only the flags under `b` (`unset_all`), so `a`
stays declared. With at least ten frames left. -/
def UnsetAllScope : Prop :=
  ∀ (pf : ParseFloat) (maxK maxD : Nat) (tz : TzCache) (fr : Nat) (a b : Str),
    bareOk a → bareOk b → a ≠ b → 1 ≤ maxK → 10 ≤ fr →
    loads pf maxK maxD tz fr (.str (hdr a ++ 10 :: aot b ++ 10 :: hdr a)) =
      .error (tde (S "Cannot declare " ++ keyRepr [a] ++ S " twice") (hdr a ++ 10 :: aot b ++ 10 :: hdr a)
        (2 * a.length + b.length + 9))

theorem unsetAllScope_proven : UnsetAllScope := by
  intro pf maxK maxD tz fr a b ha hb hab hk hfr
  have hba : b ≠ a := Ne.symm hab
  generalize hsrc : hdr a ++ 10 :: aot b ++ 10 :: hdr a = src
  have h13 : 13 ∉ src := by
    rw [← hsrc]; have := bare_no13 ha; have := bare_no13 hb; simp [hdr, aot]; simp_all
  rw [loads_eq pf maxK maxD tz fr src h13 (by omega)]
  have hR9 : 9 ≤ fr - 1 := by omega
  obtain ⟨f, hf⟩ : ∃ f, src.length + 1 = f + 1 + 1 + 1 := ⟨src.length - 2, by rw [← hsrc]; simp [hdr, aot]; omega⟩
  rw [hf]
  have hmax : ([] : List KPart).length + 1 ≤ (mkCfg pf maxK maxD tz).maxKeyParts := by simp [mkCfg]; omega
  -- `[a]`
  have hr1 := first_dict (cfg := mkCfg pf maxK maxD tz) (src := src) (p0 := .bare a) (ps := []) (rest := 10 :: aot b ++ 10 :: hdr a)
    (bareOk_kpart ha) (by simp) hmax (by rw [keyEnc_bare, ← hsrc]; simp)
  rw [keyEnc_bare, keyVal_bare] at hr1
  have hg0 : src[0]? = some 91 := by rw [← hsrc]; rfl
  have hnl1 : src[a.length + 2]? = some 10 :=
    getElem_of_eq (a := hdr a) (b := aot b ++ 10 :: hdr a) (by rw [← hsrc]; simp) _ (by simp [hdr])
  rw [mainLoop_hdr_ok (hR := hR9) hg0 (finalize_nil _ rfl) hr1 hnl1]
  -- `[[b]]`
  have hd2 : src.drop (a.length + 2 + 1) = aot (keyEnc (.bare b) []) ++ (10 :: hdr a) := by
    rw [keyEnc_bare]; exact drop_eq_of (a := hdr a ++ [10]) (by rw [← hsrc]; simp) _ (by simp [hdr] <;> omega)
  have hr2 := list_at (cfg := mkCfg pf maxK maxD tz)
    (out := { data := nestDict [a] [], flags := { tree := fsetAux EXPLICIT_NEST false [a] [], pending := [] } })
    (bareOk_kpart hb) (by simp) hmax hd2
  rw [keyEnc_bare, keyVal_bare] at hr2
  have hfz : ({ tree := fsetAux EXPLICIT_NEST false [a] [], pending := [] } : Flags).is_ [b] FROZEN = false := by
    simp [Flags.is_, isAux, fsetAux, dset, dget_cons, hba, dget_nil]
  have hap : appendNestToList [b] (nestDict [a] []) = .ok [(a, .tbl []), (b, .arr [.tbl []])] := by
    simp [appendNestToList, withNest, nestDict, dget_cons, hba, dset, dget_nil, Except.map]
  simp only [hfz, Bool.false_eq_true, ite_false, hap, overwriteErr, Except.map] at hr2
  have hg3 : src[a.length + 2 + 1]? = some 91 := getElem?_of_drop (by rw [hd2]; rfl)
  have hnl2 : src[a.length + 2 + 1 + 2 + b.length + 2]? = some 10 :=
    getElem_of_eq (a := hdr a ++ [10] ++ aot b) (b := hdr a) (by rw [← hsrc]; simp) _ (by simp [hdr, aot]; omega)
  rw [mainLoop_hdr_ok (hR := hR9) hg3 (finalize_nil _ rfl) hr2 hnl2]
  -- `[a]` again
  have hd3 : src.drop (a.length + 2 + 1 + 2 + b.length + 2 + 1) = hdr (keyEnc (.bare a) []) ++ [] := by
    rw [keyEnc_bare]; exact drop_eq_of (a := hdr a ++ [10] ++ aot b ++ [10]) (by rw [← hsrc]; simp) _
      (by simp [hdr, aot]; omega)
  have hr3 := dict_at (cfg := mkCfg pf maxK maxD tz)
    (out := { data := [(a, .tbl []), (b, .arr [.tbl []])],
              flags := { tree := fsetAux EXPLICIT_NEST false [b] (unsetAux [b] (fsetAux EXPLICIT_NEST false [a] [])),
                         pending := [] } })
    (bareOk_kpart ha) (by simp) hmax hd3
  rw [keyEnc_bare, keyVal_bare] at hr3
  have hex : (Flags.mk (fsetAux EXPLICIT_NEST false [b] (unsetAux [b] (fsetAux EXPLICIT_NEST false [a] [])))
      []).is_ [a] EXPLICIT_NEST = true := by
    simp [Flags.is_, isAux, fsetAux, unsetAux, dpop, dset, dget_cons, hab, hba, dget_nil, FNode.flags, FNode.empty, addFlag,
      EXPLICIT_NEST]
  simp only [hex, Bool.true_or, ite_true] at hr3
  have hg4 : src[a.length + 2 + 1 + 2 + b.length + 2 + 1]? = some 91 := getElem?_of_drop (by rw [hd3]; rfl)
  rw [mainLoop_hdr_err (hR := hR9) hg4 (finalize_nil _ rfl) hr3]
  congr 2; omega

/-- Nested arrays of tables, TOML 1.1 "Array of Tables" (a sub-array of tables goes into the
last element of its parent array): for all bare keys `a` and `b`, `loads('[[a]]\n[[a.b]]')` gives
`{a: [{b: [{}]}]}`: `append_nest_to_list` walks into the last element of `a`. With at least ten
frames left. -/
def NestedArrayTables : Prop :=
  ∀ (pf : ParseFloat) (maxK maxD : Nat) (tz : TzCache) (fr : Nat) (a b : Str),
    bareOk a → bareOk b → 2 ≤ maxK → 10 ≤ fr →
    loads pf maxK maxD tz fr (.str (aot a ++ 10 :: aot (a ++ 46 :: b))) =
      .ok [(a, .arr [.tbl [(b, .arr [.tbl []])]])]

theorem nestedArrayTables_proven : NestedArrayTables := by
  intro pf maxK maxD tz fr a b ha hb hk hfr
  generalize hsrc : aot a ++ 10 :: aot (a ++ 46 :: b) = src
  have h13 : 13 ∉ src := by
    rw [← hsrc]; have := bare_no13 ha; have := bare_no13 hb; simp [aot]; simp_all
  rw [loads_eq pf maxK maxD tz fr src h13 (by omega)]
  have hR9 : 9 ≤ fr - 1 := by omega
  obtain ⟨f, hf⟩ : ∃ f, src.length + 1 = f + 1 + 1 := ⟨src.length - 1, by rw [← hsrc]; simp [aot]⟩
  rw [hf]
  have hmax1 : ([] : List KPart).length + 1 ≤ (mkCfg pf maxK maxD tz).maxKeyParts := by simp [mkCfg]; omega
  have hmax2 : [KPart.bare b].length + 1 ≤ (mkCfg pf maxK maxD tz).maxKeyParts := by simp [mkCfg]; omega
  have hr1 := first_list (cfg := mkCfg pf maxK maxD tz) (src := src) (p0 := .bare a) (ps := []) (rest := 10 :: aot (a ++ 46 :: b))
    (bareOk_kpart ha) (by simp) hmax1 (by rw [keyEnc_bare, ← hsrc])
  rw [keyEnc_bare, keyVal_bare] at hr1
  simp only [show ([a] : Key).dropLast = [] from rfl, show ([a] : Key).getLastD [] = a from rfl, nestDict] at hr1
  have hg0 : src[0]? = some 91 := by rw [← hsrc]; rfl
  have hnl1 : src[a.length + 4]? = some 10 :=
    getElem_of_eq (a := aot a) (b := aot (a ++ 46 :: b)) (by rw [← hsrc]) _ (by simp [aot])
  rw [mainLoop_hdr_ok (hR := hR9) hg0 (finalize_nil _ rfl) hr1 hnl1]
  have hd2 : src.drop (a.length + 4 + 1) = aot (keyEnc (.bare a) [.bare b]) ++ [] := by
    rw [keyEnc_bare2]; exact drop_eq_of (a := aot a ++ [10]) (by rw [← hsrc]; simp) _ (by simp [aot] <;> omega)
  have hr2 := list_at (cfg := mkCfg pf maxK maxD tz)
    (out := { data := [(a, .arr [.tbl []])], flags := { tree := fsetAux EXPLICIT_NEST false [a] [], pending := [] } })
    (bareOk_kpart ha) (by intro p hp; simp at hp; subst hp; exact bareOk_kpart hb) hmax2 hd2
  rw [keyEnc_bare2, keyVal_bare2] at hr2
  have hfz : ({ tree := fsetAux EXPLICIT_NEST false [a] [], pending := [] } : Flags).is_ [a, b] FROZEN = false := by
    simp [Flags.is_, isAux, fsetAux, dset, dget_cons, dget_nil, FNode.rflags, FNode.nested, FNode.flags, FNode.empty, addFlag, FROZEN, EXPLICIT_NEST]
  have hap : appendNestToList [a, b] [(a, .arr [.tbl []])] = .ok [(a, .arr [.tbl [(b, .arr [.tbl []])]])] := by
    simp [appendNestToList, withNest, dget_cons, dset, dget_nil, Except.map, bind, Except.bind, pure, Except.pure]
  simp only [hfz, Bool.false_eq_true, ite_false, hap, overwriteErr, Except.map] at hr2
  have hg2 : src[a.length + 4 + 1]? = some 91 := getElem?_of_drop (by rw [hd2]; rfl)
  have hend : src[a.length + 4 + 1 + 2 + (a ++ 46 :: b).length + 2]? = none := by
    rw [List.getElem?_eq_none_iff, ← hsrc]; simp [aot]; omega
  rw [mainLoop_hdr_end (hR := hR9) hg2 (finalize_nil _ rfl) hr2 hend]

/-! ## `TOMLDecodeError.pos` past the end of the document -/

/-- `loads('a = "\\')` (a backslash as the last character of a basic string) raises
`TOMLDecodeError("Unescaped '\\' in a string", doc, 7)` for a document of length 6. -/
theorem loads_escape_eof (pf : ParseFloat) (maxK maxD : Nat) (tz : TzCache) (fr : Nat) (hfr : 12 ≤ fr) :
    loads pf maxK maxD tz fr (.str [97, 32, 61, 32, 34, 92]) =
      .error (tdeS "Unescaped '\\' in a string" [97, 32, 61, 32, 34, 92] 7) := by
  have h13 : 13 ∉ ([97, 32, 61, 32, 34, 92] : Str) := by decide
  rw [loads_eq pf maxK maxD tz fr _ h13 (by omega)]
  generalize hsrc : ([97, 32, 61, 32, 34, 92] : Str) = src
  have hesc := escapeErrors_proven.2.2.2.2 src 5 false (by rw [← hsrc]; rfl)
  have hkey := parseKeyN_bare (maxK := (mkCfg pf maxK maxD tz).maxKeyParts) (src := src) (x := [97]) (t := [32, 34, 92])
    (by decide) (by decide) (by rw [← hsrc]; rfl)
  have hg0 : src[0]? = some 97 := by rw [← hsrc]; rfl
  have hg2 : src[1 + 1]? = some 61 := by rw [← hsrc]; rfl
  have hsk : skipChars src (1 + 1 + 1) tomlWs = 4 := by rw [← hsrc]; decide
  have hg4 : src[4]? = some 34 := by rw [← hsrc]; rfl
  have hst : startsAt src 4 [34, 34, 34] = false := by rw [← hsrc]; decide
  have hg5 : src[5]? = some 92 := by rw [← hsrc]; rfl
  have hlen : src.length = 6 := by rw [← hsrc]; rfl
  have hloop : basicStrLoop src false (src.length + 1) 5 5 [] =
      .error (tdeS "Unescaped '\\' in a string" src 7) := by
    rw [hlen]
    simp only [basicStrLoop, hg5, show (92 == 34) = false from rfl, show (92 == 92) = true from rfl,
      Bool.false_eq_true, ite_false, ite_true, hesc, bind, Except.bind]
  have hval : parseValue (mkCfg pf maxK maxD tz) src (fr - 1 - 1 - 1 - 1) (vFuel src - 1) 4 =
      .error (tdeS "Unescaped '\\' in a string" src 7) := by
    rw [show vFuel src - 1 = (vFuel src - 2) + 1 by unfold vFuel; omega]
    simp only [parseValue, hg4, show (some 34 == some 34) = true from rfl, ite_true, hst, Bool.false_eq_true,
      ite_false, need_ok (Nat.le_trans (parseOneLineBasicStrN_le src 4) (show 6 ≤ fr - 1 - 1 - 1 - 1 by omega)),
      parseOneLineBasicStr, parseBasicStr, hloop]
    rfl
  have hpkv : parseKeyValuePair (mkCfg pf maxK maxD tz) src (fr - 1 - 1 - 1) (vFuel src) 0 =
      .error (tdeS "Unescaped '\\' in a string" src 7) := by
    rw [show vFuel src = (vFuel src - 1) + 1 by unfold vFuel; omega]
    simp only [parseKeyValuePair, hkey.2, need_ok (show 3 ≤ fr - 1 - 1 - 1 by omega), hkey.1, bind, Except.bind,
      List.length_singleton, hg2, show (some 61 != some 61) = false from rfl, Bool.false_eq_true, ite_false, hsk,
      need_ok (show 1 ≤ fr - 1 - 1 - 1 by omega), hval]
  have hrule : keyValueRule (mkCfg pf maxK maxD tz) src (fr - 1 - 1) 0 Out.init [] =
      .error (tdeS "Unescaped '\\' in a string" src 7) := by
    simp only [keyValueRule, need_ok (show 1 ≤ fr - 1 - 1 by omega), hpkv, bind, Except.bind]
  rw [hlen]
  exact mainLoop_kv_err hg0 (by decide) (by decide) (by decide) hrule (by omega)

/-- `TOMLDecodeError.pos`, docs: "The index of *doc* where parsing failed": every
`TOMLDecodeError(msg, doc, pos)` that `loads` raises has `pos ≤ len(doc)`, where `doc` is the text
after CRLF normalisation (a raised error carries its `pos`, `tdeExc`). -/
def DecodeErrorPosInDoc : Prop :=
  ∀ (pf : ParseFloat) (maxK maxD : Nat) (tz : TzCache) (fr : Nat) (s msg : Str) (p : Nat),
    loads pf maxK maxD tz fr (.str s) = .error (tde msg (crlf s) p) → p ≤ (crlf s).length

/-- `'a = "\\'` has length 6, and `loads` raises at 7. -/
theorem decodeErrorPosInDoc_refuted : ¬ DecodeErrorPosInDoc := by
  intro h
  have hc : crlf ([97, 32, 61, 32, 34, 92] : Str) = [97, 32, 61, 32, 34, 92] := by decide
  have := h { isFloat := true, call := fun _ => .ok .other } 1000 4300 (fun _ _ _ => true) 1000
    [97, 32, 61, 32, 34, 92] (S "Unescaped '\\' in a string") 7
    (by rw [hc]; exact loads_escape_eof _ _ _ _ _ (by omega))
  rw [hc] at this
  revert this; decide

end PyLean.TextLibs.Toml
