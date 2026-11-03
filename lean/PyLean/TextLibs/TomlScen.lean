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
    getElem_of_eq (a := hdr a) (b := aot b ++ 10 :: hdr a) (by rw [← hsrc]; try simp) _ (by simp [hdr])
  rw [mainLoop_hdr_ok (hR := hR9) hg0 (finalize_nil _ rfl) hr1 hnl1]
  -- `[[b]]`
  have hd2 : src.drop (a.length + 2 + 1) = aot (keyEnc (.bare b) []) ++ (10 :: hdr a) := by
    rw [keyEnc_bare]; exact drop_eq_of (a := hdr a ++ [10]) (by rw [← hsrc]; try simp) _ (by simp [hdr] <;> omega)
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
    getElem_of_eq (a := hdr a ++ [10] ++ aot b) (b := hdr a) (by rw [← hsrc]; try simp) _ (by simp [hdr, aot]; omega)
  rw [mainLoop_hdr_ok (hR := hR9) hg3 (finalize_nil _ rfl) hr2 hnl2]
  -- `[a]` again
  have hd3 : src.drop (a.length + 2 + 1 + 2 + b.length + 2 + 1) = hdr (keyEnc (.bare a) []) ++ [] := by
    rw [keyEnc_bare]; exact drop_eq_of (a := hdr a ++ [10] ++ aot b ++ [10]) (by rw [← hsrc]; try simp) _
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
    rw [keyEnc_bare2]; exact drop_eq_of (a := aot a ++ [10]) (by rw [← hsrc]; try simp) _ (by simp [aot] <;> omega)
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

/-! ## Key/value lines under the flags, _parser.py:415-446 -/

/-- `TOMLDecodeError.__init__` on a `str` doc and an `int` pos raises nothing but `ValueError`
(from `rindex`), so a raised `TOMLDecodeError` is never a `KeyError`. -/
theorem tdeFull_error {msg doc : Str} {pos : Int} {e : PyExc} (h : tdeFull msg doc pos = .error e) :
    e = .valueError "substring not found" := by
  unfold tdeFull at h
  by_cases h1 : ((doc.take (sliceEnd pos doc.length)).count 10 + 1 == 1) = true
  · simp [h1, bind, Except.bind, pure, Except.pure] at h
  · cases hl : lastIdx 10 (doc.take (sliceEnd pos doc.length)) with
    | none => simp [h1, hl, bind, Except.bind] at h; exact h.symm
    | some i => simp [h1, hl, bind, Except.bind, pure, Except.pure] at h

theorem overwriteErr_tde {α : Type} (src : Str) (pos : Nat) (msg s : Str) (p : Nat) :
    overwriteErr (α := α) src pos (.error (tde msg s p)) = .error (tde msg s p) := by
  unfold tde
  split
  · rfl
  · next e he => rw [tdeFull_error he]; rfl

theorem overwriteErr_tdeS {α : Type} (src : Str) (pos : Nat) (msg : String) (s : Str) (p : Nat) :
    overwriteErr (α := α) src pos (.error (tdeS msg s p)) = .error (tdeS msg s p) :=
  overwriteErr_tde src pos (S msg) s p

/-- `key_value_rule` after `parse_key_value_pair` has returned `pos`, `key` and `value`. -/
def kvBody (src : Str) (pos : Nat) (out : Out) (header key : Key) (value : TVal) : Py (Nat × Out) := do
  let keyParent := key.dropLast
  let keyStem := key.getLastD []
  let absKeyParent := header ++ keyParent
  let contKeys := (List.range (key.length - 1)).map (fun i => header ++ key.take (i + 1))
  let flags ← contKeysLoop src pos contKeys out.flags
  if flags.is_ absKeyParent FROZEN then
    .error (tde (S "Cannot mutate immutable namespace " ++ keyRepr absKeyParent) src pos)
  else
    let (data, _) ← overwriteErr src pos <| withNest true (fun nest =>
      if (dget nest keyStem).isSome then .error (tdeS "Cannot overwrite a value" src pos)
      else .ok (dset nest keyStem value, ())) absKeyParent out.data
    let flags ← if value.isDictOrList then flags.set (header ++ key) FROZEN true else pure flags
    pure (pos, { data, flags })

theorem kvr_at {cfg : Cfg} {src : Str} {R pos : Nat} {p0 : KPart} {ps : List KPart} {v : SV} {rest : Str}
    {out : Out} {header : Key}
    (h0 : p0.ok) (hps : ∀ p ∈ ps, p.ok) (hmax : ps.length + 1 ≤ cfg.maxKeyParts) (hv : v.ok)
    (hr34 : ∀ c, rest.head? = some c → c ≠ 34) (hR : 3 * v.depth + 13 ≤ R)
    (h : src.drop pos = keyEnc p0 ps ++ 61 :: v.enc ++ rest) :
    keyValueRule cfg src (R - 1) pos out header =
      kvBody src (pos + (keyEnc p0 ps).length + 1 + v.enc.length) out header (keyVal p0 ps) v.val := by
  have hl : v.enc.length ≤ src.length := by
    have := congrArg List.length h; simp at this; omega
  have hp := pkv_at (cfg := cfg) (r := R - 1 - 1) (fuel := vFuel src - 1) h0 hps hmax hv hr34
    (by have := SV.need_le v; unfold vFuel; omega) (by omega) h
  rw [show vFuel src - 1 + 1 = vFuel src by unfold vFuel; omega] at hp
  simp only [keyValueRule, need_ok (show 1 ≤ R - 1 by omega), hp, bind, Except.bind, kvBody]

def boolText (x : Bool) : Str := if x then S "true" else S "false"

theorem boolText_enc (x : Bool) : (SV.bool x).enc = boolText x := rfl
theorem boolText_no13' (x : Bool) : 13 ∉ boolText x := by cases x <;> decide

/-- The inline values `{}` and `[]`. -/
def emptyTbl : SV := .tbl [] .nil
def emptyArr : SV := .arr [] .nil

theorem emptyTbl_enc : emptyTbl.enc = [123, 125] := rfl
theorem emptyArr_enc : emptyArr.enc = [91, 93] := rfl

theorem kv_line_pos {src : Str} {pos : Nat} {a tail : Str}
    (h : src.drop pos = a ++ tail) (ha : bareOk a) :
    ∃ c, src[pos]? = some c ∧ keyInitial c = true ∧ tomlWs c = false ∧ c ≠ 10 := by
  obtain ⟨c, t, rfl, hc⟩ := bare_head ha
  obtain ⟨hi, hw, h10, -⟩ := bare_char hc
  exact ⟨c, getElem?_of_drop (r := t ++ tail) (by rw [h]; simp), hi, hw, h10⟩

/-- Recursive flags, TOML 1.1 "Inline Table" ("Inline tables are fully self-contained ... Keys
and sub-tables cannot be added outside the braces") and "Array" (a static array cannot be
appended to by an array of tables): for all bare keys `a` and `b` and boolean `X`:
`loads('a={}\n[a.b]')` raises "Cannot declare ('a', 'b') twice" (the `FROZEN` flag `a` got
recursively answers for `a.b`, `Flags.is_`'s early return); `loads('a=[]\n[[a]]')` raises "Cannot
mutate immutable namespace ('a',)"; `loads('a={}\na.b=X')` raises "Cannot mutate immutable
namespace ('a',)". Each at the position after the second key (after the value for the last).
With at least eighteen frames left. -/
def FrozenRules : Prop :=
  ∀ (pf : ParseFloat) (maxK maxD : Nat) (tz : TzCache) (fr : Nat) (a b : Str) (x : Bool),
    bareOk a → bareOk b → 2 ≤ maxK → 18 ≤ fr →
    loads pf maxK maxD tz fr (.str (a ++ 61 :: emptyTbl.enc ++ 10 :: hdr (a ++ 46 :: b))) =
      .error (tde (S "Cannot declare " ++ keyRepr [a, b] ++ S " twice")
        (a ++ 61 :: emptyTbl.enc ++ 10 :: hdr (a ++ 46 :: b)) (2 * a.length + b.length + 6)) ∧
    loads pf maxK maxD tz fr (.str (a ++ 61 :: emptyArr.enc ++ 10 :: aot a)) =
      .error (tde (S "Cannot mutate immutable namespace " ++ keyRepr [a])
        (a ++ 61 :: emptyArr.enc ++ 10 :: aot a) (2 * a.length + 6)) ∧
    loads pf maxK maxD tz fr (.str (a ++ 61 :: emptyTbl.enc ++ 10 :: a ++ 46 :: b ++ 61 :: boolText x)) =
      .error (tde (S "Cannot mutate immutable namespace " ++ keyRepr [a])
        (a ++ 61 :: emptyTbl.enc ++ 10 :: a ++ 46 :: b ++ 61 :: boolText x)
        (2 * a.length + b.length + 6 + (boolText x).length))

/-- The state after `a=V` on an empty document, for a table or array value `V`. -/
theorem first_frozen {cfg : Cfg} {src : Str} {a : Str} {v : SV} {rest : Str} {R : Nat}
    (ha : bareOk a) (hv : v.ok) (hd : v.val.isDictOrList = true) (hr34 : ∀ c, rest.head? = some c → c ≠ 34)
    (hmax : 1 ≤ cfg.maxKeyParts) (hR : 3 * v.depth + 13 ≤ R)
    (h : src = a ++ 61 :: v.enc ++ rest) :
    keyValueRule cfg src (R - 1) 0 Out.init [] =
      .ok (a.length + 1 + v.enc.length,
        { data := [(a, v.val)], flags := { tree := [(a, .mk [] [FROZEN] [])], pending := [] } }) := by
  rw [kvr_at (p0 := .bare a) (ps := []) (bareOk_kpart ha) (by simp) (by simp; exact hmax) hv hr34 hR
    (by rw [keyEnc_bare, h]; simp)]
  simp [kvBody, keyEnc_bare, keyVal_bare, contKeysLoop, Flags.is_, Out.init, Flags.init, withNest, dget_nil,
    dset, overwriteErr, hd, Flags.set, fsetAux, FNode.empty, addFlag, bind, Except.bind, pure, Except.pure]

theorem frozenRules_proven : FrozenRules := by
  intro pf maxK maxD tz fr a b x ha hb hk hfr
  have hmax1 : 1 ≤ (mkCfg pf maxK maxD tz).maxKeyParts := by simp [mkCfg]; omega
  have hmax2 : [KPart.bare b].length + 1 ≤ (mkCfg pf maxK maxD tz).maxKeyParts := by simp [mkCfg]; omega
  have hR9 : 9 ≤ fr - 1 := by omega
  obtain ⟨c0, t0, hc0, hci, hcws, hc10⟩ : ∃ c t, a = c :: t ∧ keyInitial c = true ∧ tomlWs c = false ∧ c ≠ 10 := by
    obtain ⟨c, t, h, hc⟩ := bare_head ha; obtain ⟨hi, hw, h10, -⟩ := bare_char hc; exact ⟨c, t, h, hi, hw, h10⟩
  have hna := bare_no13 ha
  have hnb := bare_no13 hb
  refine ⟨?_, ?_, ?_⟩
  · generalize hsrc : a ++ 61 :: emptyTbl.enc ++ 10 :: hdr (a ++ 46 :: b) = src
    have h13 : 13 ∉ src := by rw [← hsrc]; simp [emptyTbl_enc, hdr]; simp_all
    rw [loads_eq pf maxK maxD tz fr src h13 (by omega)]
    obtain ⟨f, hf⟩ : ∃ f, src.length + 1 = f + 1 + 1 := ⟨src.length - 1, by rw [← hsrc]; simp <;> omega⟩
    rw [hf]
    have hr1 := first_frozen (cfg := mkCfg pf maxK maxD tz) (src := src) (R := fr - 1) ha (v := emptyTbl) (by simp [emptyTbl, SV.ok, TItems.ok]) rfl
      (rest := 10 :: hdr (a ++ 46 :: b)) (by intro c hc; simp at hc; subst hc; decide) hmax1
      (by simp [emptyTbl, SV.depth, TItems.depth]; omega) hsrc.symm
    have hg0 : src[0]? = some c0 := by rw [← hsrc, hc0]; rfl
    rw [mainLoop_kv_hdr hg0 hci hcws hc10 hr1 (by omega)]
    have hd1 : src.drop (a.length + 1 + emptyTbl.enc.length) = 10 :: (hdr (keyEnc (.bare a) [.bare b]) ++ []) := by
      rw [keyEnc_bare2]; exact drop_eq_of (a := a ++ 61 :: emptyTbl.enc) (by rw [← hsrc]; try simp) _ (by simp <;> omega)
    simp only [getElem?_of_drop hd1, reduceCtorEq, ite_false, ite_true]
    have hd2 := drop_succ_of_drop hd1
    have hr2 := dict_at (cfg := mkCfg pf maxK maxD tz)
      (out := { data := [(a, emptyTbl.val)], flags := { tree := [(a, .mk [] [FROZEN] [])], pending := [] } })
      (bareOk_kpart ha) (by intro p hp; simp at hp; subst hp; exact bareOk_kpart hb) hmax2 hd2
    rw [keyEnc_bare2, keyVal_bare2] at hr2
    have hfz : ((Flags.mk [(a, .mk [] [FROZEN] [])] []).is_ [a, b] EXPLICIT_NEST ||
        (Flags.mk [(a, .mk [] [FROZEN] [])] []).is_ [a, b] FROZEN) = true := by
      simp [Flags.is_, isAux, dget_cons, FNode.rflags, FNode.nested, FNode.flags, dget_nil, FROZEN, EXPLICIT_NEST]
    simp only [hfz, ite_true] at hr2
    have hg2 : src[a.length + 1 + emptyTbl.enc.length + 1]? = some 91 := getElem?_of_drop (by rw [hd2]; rfl)
    rw [mainLoop_hdr_err (hR := hR9) hg2 (finalize_nil _ rfl) hr2]
    congr 2; simp [emptyTbl_enc]; omega
  · generalize hsrc : a ++ 61 :: emptyArr.enc ++ 10 :: aot a = src
    have h13 : 13 ∉ src := by rw [← hsrc]; simp [emptyArr_enc, aot]; simp_all
    rw [loads_eq pf maxK maxD tz fr src h13 (by omega)]
    obtain ⟨f, hf⟩ : ∃ f, src.length + 1 = f + 1 + 1 := ⟨src.length - 1, by rw [← hsrc]; simp <;> omega⟩
    rw [hf]
    have hr1 := first_frozen (cfg := mkCfg pf maxK maxD tz) (src := src) (R := fr - 1) ha (v := emptyArr) (by simp [emptyArr, SV.ok, AItems.ok]) rfl
      (rest := 10 :: aot a) (by intro c hc; simp at hc; subst hc; decide) hmax1
      (by simp [emptyArr, SV.depth, AItems.depth]; omega) hsrc.symm
    have hg0 : src[0]? = some c0 := by rw [← hsrc, hc0]; rfl
    rw [mainLoop_kv_hdr hg0 hci hcws hc10 hr1 (by omega)]
    have hd1 : src.drop (a.length + 1 + emptyArr.enc.length) = 10 :: (aot (keyEnc (.bare a) []) ++ []) := by
      rw [keyEnc_bare]; exact drop_eq_of (a := a ++ 61 :: emptyArr.enc) (by rw [← hsrc]; try simp) _ (by simp <;> omega)
    simp only [getElem?_of_drop hd1, reduceCtorEq, ite_false, ite_true]
    have hd2 := drop_succ_of_drop hd1
    have hr2 := list_at (cfg := mkCfg pf maxK maxD tz)
      (out := { data := [(a, emptyArr.val)], flags := { tree := [(a, .mk [] [FROZEN] [])], pending := [] } })
      (bareOk_kpart ha) (by simp) (by simp; exact hmax1) hd2
    rw [keyEnc_bare, keyVal_bare] at hr2
    have hfz : (Flags.mk [(a, .mk [] [FROZEN] [])] []).is_ [a] FROZEN = true := by
      simp [Flags.is_, isAux, dget_cons, FNode.rflags, FNode.flags, FROZEN]
    simp only [hfz, ite_true] at hr2
    have hg2 : src[a.length + 1 + emptyArr.enc.length + 1]? = some 91 := getElem?_of_drop (by rw [hd2]; rfl)
    rw [mainLoop_hdr_err (hR := hR9) hg2 (finalize_nil _ rfl) hr2]
    congr 2; simp [emptyArr_enc]; omega
  · generalize hsrc : a ++ 61 :: emptyTbl.enc ++ 10 :: a ++ 46 :: b ++ 61 :: boolText x = src
    have h13 : 13 ∉ src := by
      rw [← hsrc]; have := boolText_no13' x; simp [emptyTbl_enc]; simp_all
    rw [loads_eq pf maxK maxD tz fr src h13 (by omega)]
    obtain ⟨f, hf⟩ : ∃ f, src.length + 1 = f + 1 + 1 := ⟨src.length - 1, by rw [← hsrc]; simp <;> omega⟩
    rw [hf]
    have hr1 := first_frozen (cfg := mkCfg pf maxK maxD tz) (src := src) (R := fr - 1) ha (v := emptyTbl) (by simp [emptyTbl, SV.ok, TItems.ok]) rfl
      (rest := 10 :: a ++ 46 :: b ++ 61 :: boolText x) (by intro c hc; simp at hc; subst hc; decide) hmax1
      (by simp [emptyTbl, SV.depth, TItems.depth]; omega) (by rw [← hsrc]; try simp)
    have hg0 : src[0]? = some c0 := by rw [← hsrc, hc0]; rfl
    rw [mainLoop_kv_hdr hg0 hci hcws hc10 hr1 (by omega)]
    have hd1 : src.drop (a.length + 1 + emptyTbl.enc.length) =
        10 :: (keyEnc (.bare a) [.bare b] ++ 61 :: (SV.bool x).enc ++ []) := by
      rw [keyEnc_bare2, boolText_enc]; exact drop_eq_of (a := a ++ 61 :: emptyTbl.enc) (by rw [← hsrc]; try simp) _ (by simp <;> omega)
    simp only [getElem?_of_drop hd1, reduceCtorEq, ite_false, ite_true]
    have hd2 := drop_succ_of_drop hd1
    have hr2 := kvr_at (cfg := mkCfg pf maxK maxD tz) (R := fr - 1) (header := [])
      (out := { data := [(a, emptyTbl.val)], flags := { tree := [(a, .mk [] [FROZEN] [])], pending := [] } })
      (bareOk_kpart ha) (by intro p hp; simp at hp; subst hp; exact bareOk_kpart hb) hmax2 (v := SV.bool x) trivial
      (by simp) (by simp [SV.depth]; omega) hd2
    rw [keyEnc_bare2, keyVal_bare2] at hr2
    simp [kvBody, contKeysLoop, Flags.is_, isAux, dget_cons, FNode.flags, FNode.rflags, FROZEN, EXPLICIT_NEST,
      Flags.addPending, bind, Except.bind] at hr2
    obtain ⟨c1, hg1, hi1, hw1, h101⟩ := kv_line_pos (a := a) (tail := 46 :: b ++ 61 :: (SV.bool x).enc ++ [])
      (by rw [hd2, keyEnc_bare2]; simp) ha
    refine (mainLoop_kv_err hg1 hi1 hw1 h101 hr2 (by omega)).trans ?_
    congr 2; simp [emptyTbl_enc, boolText_enc]; omega

/-- Dotted keys and tables, TOML 1.1 "Table" ("You cannot define any key or table more than once")
and the error of `get_or_create_nest` ("There is no nest behind this key", turned into "Cannot
overwrite a value"): for all bare keys `a` and `b` and booleans `X`, `Y`: `loads('a=X\n[a.b]')`
and `loads('a=X\n[a]')` raise "Cannot overwrite a value" after the header's key (`a` holds no
table); `loads('a=X\na=Y')` raises it after `Y` (a key defined twice). With at least sixteen
frames left. -/
def OverwriteRules : Prop :=
  ∀ (pf : ParseFloat) (maxK maxD : Nat) (tz : TzCache) (fr : Nat) (a b : Str) (x y : Bool),
    bareOk a → bareOk b → 2 ≤ maxK → 16 ≤ fr →
    loads pf maxK maxD tz fr (.str (a ++ 61 :: boolText x ++ 10 :: hdr (a ++ 46 :: b))) =
      .error (tdeS "Cannot overwrite a value" (a ++ 61 :: boolText x ++ 10 :: hdr (a ++ 46 :: b))
        (2 * a.length + b.length + 4 + (boolText x).length)) ∧
    loads pf maxK maxD tz fr (.str (a ++ 61 :: boolText x ++ 10 :: hdr a)) =
      .error (tdeS "Cannot overwrite a value" (a ++ 61 :: boolText x ++ 10 :: hdr a)
        (2 * a.length + 3 + (boolText x).length)) ∧
    loads pf maxK maxD tz fr (.str (a ++ 61 :: boolText x ++ 10 :: a ++ 61 :: boolText y)) =
      .error (tdeS "Cannot overwrite a value" (a ++ 61 :: boolText x ++ 10 :: a ++ 61 :: boolText y)
        (2 * a.length + 3 + (boolText x).length + (boolText y).length))

/-- The state after `a=X` on an empty document, for a boolean `X`. -/
theorem first_bool {cfg : Cfg} {src : Str} {a : Str} {x : Bool} {rest : Str} {R : Nat}
    (ha : bareOk a) (hr34 : ∀ c, rest.head? = some c → c ≠ 34) (hmax : 1 ≤ cfg.maxKeyParts) (hR : 13 ≤ R)
    (h : src = a ++ 61 :: boolText x ++ rest) :
    keyValueRule cfg src (R - 1) 0 Out.init [] =
      .ok (a.length + 1 + (boolText x).length, { data := [(a, .bool x)], flags := Flags.init }) := by
  rw [kvr_at (p0 := .bare a) (ps := []) (v := SV.bool x) (bareOk_kpart ha) (by simp) (by simp; exact hmax) trivial hr34
    (by simp [SV.depth]; omega) (by rw [keyEnc_bare, h, boolText_enc]; simp)]
  simp [kvBody, keyEnc_bare, keyVal_bare, contKeysLoop, Flags.is_, Out.init, Flags.init, withNest, dget_nil,
    dset, overwriteErr, SV.val, TVal.isDictOrList, boolText_enc, bind, Except.bind, pure, Except.pure]

theorem overwriteRules_proven : OverwriteRules := by
  intro pf maxK maxD tz fr a b x y ha hb hk hfr
  have hmax1 : 1 ≤ (mkCfg pf maxK maxD tz).maxKeyParts := by simp [mkCfg]; omega
  have hmax2 : [KPart.bare b].length + 1 ≤ (mkCfg pf maxK maxD tz).maxKeyParts := by simp [mkCfg]; omega
  have hR9 : 9 ≤ fr - 1 := by omega
  obtain ⟨c0, t0, hc0, hci, hcws, hc10⟩ : ∃ c t, a = c :: t ∧ keyInitial c = true ∧ tomlWs c = false ∧ c ≠ 10 := by
    obtain ⟨c, t, h, hc⟩ := bare_head ha; obtain ⟨hi, hw, h10, -⟩ := bare_char hc; exact ⟨c, t, h, hi, hw, h10⟩
  have hna := bare_no13 ha
  have hnb := bare_no13 hb
  have hnx := boolText_no13' x
  have hny := boolText_no13' y
  refine ⟨?_, ?_, ?_⟩
  · generalize hsrc : a ++ 61 :: boolText x ++ 10 :: hdr (a ++ 46 :: b) = src
    have h13 : 13 ∉ src := by rw [← hsrc]; simp [hdr]; simp_all
    rw [loads_eq pf maxK maxD tz fr src h13 (by omega)]
    obtain ⟨f, hf⟩ : ∃ f, src.length + 1 = f + 1 + 1 := ⟨src.length - 1, by rw [← hsrc]; simp <;> omega⟩
    rw [hf]
    have hr1 := first_bool (cfg := mkCfg pf maxK maxD tz) (src := src) (R := fr - 1) (x := x) ha
      (rest := 10 :: hdr (a ++ 46 :: b)) (by intro c hc; simp at hc; subst hc; decide) hmax1 (by omega) (by rw [← hsrc]; try simp)
    have hg0 : src[0]? = some c0 := by rw [← hsrc, hc0]; rfl
    rw [mainLoop_kv_hdr hg0 hci hcws hc10 hr1 (by omega)]
    have hd1 : src.drop (a.length + 1 + (boolText x).length) = 10 :: (hdr (keyEnc (.bare a) [.bare b]) ++ []) := by
      rw [keyEnc_bare2]; exact drop_eq_of (a := a ++ 61 :: boolText x) (by rw [← hsrc]; try simp) _ (by simp <;> omega)
    simp only [getElem?_of_drop hd1, reduceCtorEq, ite_false, ite_true]
    have hd2 := drop_succ_of_drop hd1
    have hr2 := dict_at (cfg := mkCfg pf maxK maxD tz) (out := { data := [(a, .bool x)], flags := Flags.init })
      (bareOk_kpart ha) (by intro p hp; simp at hp; subst hp; exact bareOk_kpart hb) hmax2 hd2
    rw [keyEnc_bare2, keyVal_bare2] at hr2
    have hfz : (Flags.init.is_ [a, b] EXPLICIT_NEST || Flags.init.is_ [a, b] FROZEN) = false := by
      simp [Flags.init, Flags.is_, isAux, dget_nil]
    have hgo : getOrCreateNest true [a, b] [(a, .bool x)] = .error noNest := by
      simp [getOrCreateNest, withNest, dget_cons, Except.map]
    simp only [hfz, Bool.false_eq_true, ite_false, hgo, overwriteErr, Except.map] at hr2
    have hg2 : src[a.length + 1 + (boolText x).length + 1]? = some 91 := getElem?_of_drop (by rw [hd2]; rfl)
    rw [mainLoop_hdr_err (hR := hR9) hg2 (finalize_nil _ rfl) hr2]
    congr 2; simp; omega
  · generalize hsrc : a ++ 61 :: boolText x ++ 10 :: hdr a = src
    have h13 : 13 ∉ src := by rw [← hsrc]; simp [hdr]; simp_all
    rw [loads_eq pf maxK maxD tz fr src h13 (by omega)]
    obtain ⟨f, hf⟩ : ∃ f, src.length + 1 = f + 1 + 1 := ⟨src.length - 1, by rw [← hsrc]; simp <;> omega⟩
    rw [hf]
    have hr1 := first_bool (cfg := mkCfg pf maxK maxD tz) (src := src) (R := fr - 1) (x := x) ha
      (rest := 10 :: hdr a) (by intro c hc; simp at hc; subst hc; decide) hmax1 (by omega) (by rw [← hsrc]; try simp)
    have hg0 : src[0]? = some c0 := by rw [← hsrc, hc0]; rfl
    rw [mainLoop_kv_hdr hg0 hci hcws hc10 hr1 (by omega)]
    have hd1 : src.drop (a.length + 1 + (boolText x).length) = 10 :: (hdr (keyEnc (.bare a) []) ++ []) := by
      rw [keyEnc_bare]; exact drop_eq_of (a := a ++ 61 :: boolText x) (by rw [← hsrc]; try simp) _ (by simp <;> omega)
    simp only [getElem?_of_drop hd1, reduceCtorEq, ite_false, ite_true]
    have hd2 := drop_succ_of_drop hd1
    have hr2 := dict_at (cfg := mkCfg pf maxK maxD tz) (out := { data := [(a, .bool x)], flags := Flags.init })
      (bareOk_kpart ha) (by simp) (by simp; exact hmax1) hd2
    rw [keyEnc_bare, keyVal_bare] at hr2
    have hfz : (Flags.init.is_ [a] EXPLICIT_NEST || Flags.init.is_ [a] FROZEN) = false := by
      simp [Flags.init, Flags.is_, isAux, dget_nil]
    have hgo : getOrCreateNest true [a] [(a, .bool x)] = .error noNest := by
      simp [getOrCreateNest, withNest, dget_cons, Except.map]
    simp only [hfz, Bool.false_eq_true, ite_false, hgo, overwriteErr, Except.map] at hr2
    have hg2 : src[a.length + 1 + (boolText x).length + 1]? = some 91 := getElem?_of_drop (by rw [hd2]; rfl)
    rw [mainLoop_hdr_err (hR := hR9) hg2 (finalize_nil _ rfl) hr2]
    congr 2; omega
  · generalize hsrc : a ++ 61 :: boolText x ++ 10 :: a ++ 61 :: boolText y = src
    have h13 : 13 ∉ src := by rw [← hsrc]; simp; simp_all
    rw [loads_eq pf maxK maxD tz fr src h13 (by omega)]
    obtain ⟨f, hf⟩ : ∃ f, src.length + 1 = f + 1 + 1 := ⟨src.length - 1, by rw [← hsrc]; simp <;> omega⟩
    rw [hf]
    have hr1 := first_bool (cfg := mkCfg pf maxK maxD tz) (src := src) (R := fr - 1) (x := x) ha
      (rest := 10 :: a ++ 61 :: boolText y) (by intro c hc; simp at hc; subst hc; decide) hmax1 (by omega) (by rw [← hsrc]; try simp)
    have hg0 : src[0]? = some c0 := by rw [← hsrc, hc0]; rfl
    rw [mainLoop_kv_hdr hg0 hci hcws hc10 hr1 (by omega)]
    have hd1 : src.drop (a.length + 1 + (boolText x).length) =
        10 :: (keyEnc (.bare a) [] ++ 61 :: (SV.bool y).enc ++ []) := by
      rw [keyEnc_bare, boolText_enc]; exact drop_eq_of (a := a ++ 61 :: boolText x) (by rw [← hsrc]; try simp) _ (by simp <;> omega)
    simp only [getElem?_of_drop hd1, reduceCtorEq, ite_false, ite_true]
    have hd2 := drop_succ_of_drop hd1
    have hr2 := kvr_at (cfg := mkCfg pf maxK maxD tz) (R := fr - 1) (header := [])
      (out := { data := [(a, .bool x)], flags := Flags.init })
      (bareOk_kpart ha) (by simp) (by simp; exact hmax1) (v := SV.bool y) trivial
      (by simp) (by simp [SV.depth]; omega) hd2
    rw [keyEnc_bare, keyVal_bare] at hr2
    simp [kvBody, contKeysLoop, Flags.is_, Flags.init, withNest, dget_cons, overwriteErr_tdeS, bind,
      Except.bind] at hr2
    obtain ⟨c1, hg1, hi1, hw1, h101⟩ := kv_line_pos (a := a) (tail := 61 :: (SV.bool y).enc ++ [])
      (by rw [hd2, keyEnc_bare]; simp) ha
    refine (mainLoop_kv_err hg1 hi1 hw1 h101 hr2 (by omega)).trans ?_
    congr 2; simp [boolText_enc]; omega

/-- Header-relative keys, TOML 1.1 "Table" ("Under that, and until the next table or EOF are
the key/values of that table"): for all bare keys `t`, `k` and boolean `X`, `loads('[t]\nk=X')`
gives `{t: {k: X}}`. With at least sixteen frames left. -/
def HeaderRelative : Prop :=
  ∀ (pf : ParseFloat) (maxK maxD : Nat) (tz : TzCache) (fr : Nat) (t k : Str) (x : Bool),
    bareOk t → bareOk k → 1 ≤ maxK → 16 ≤ fr →
    loads pf maxK maxD tz fr (.str (hdr t ++ 10 :: k ++ 61 :: boolText x)) = .ok [(t, .tbl [(k, .bool x)])]

theorem headerRelative_proven : HeaderRelative := by
  intro pf maxK maxD tz fr t k x ht hk hm hfr
  have hmax1 : ([] : List KPart).length + 1 ≤ (mkCfg pf maxK maxD tz).maxKeyParts := by simp [mkCfg]; omega
  have hR9 : 9 ≤ fr - 1 := by omega
  generalize hsrc : hdr t ++ 10 :: k ++ 61 :: boolText x = src
  have h13 : 13 ∉ src := by
    rw [← hsrc]; have := bare_no13 ht; have := bare_no13 hk; have := boolText_no13' x; simp [hdr]; simp_all
  rw [loads_eq pf maxK maxD tz fr src h13 (by omega)]
  obtain ⟨f, hf⟩ : ∃ f, src.length + 1 = f + 1 + 1 := ⟨src.length - 1, by rw [← hsrc]; simp [hdr]⟩
  rw [hf]
  have hr1 := first_dict (cfg := mkCfg pf maxK maxD tz) (src := src) (p0 := .bare t) (ps := [])
    (rest := 10 :: k ++ 61 :: boolText x) (bareOk_kpart ht) (by simp) hmax1 (by rw [keyEnc_bare, ← hsrc]; simp)
  rw [keyEnc_bare, keyVal_bare] at hr1
  have hg0 : src[0]? = some 91 := by rw [← hsrc]; rfl
  have hnl1 : src[t.length + 2]? = some 10 :=
    getElem_of_eq (a := hdr t) (b := k ++ 61 :: boolText x) (by rw [← hsrc]; try simp) _ (by simp [hdr])
  rw [mainLoop_hdr_ok (hR := hR9) hg0 (finalize_nil _ rfl) hr1 hnl1]
  have hd2 : src.drop (t.length + 2 + 1) = keyEnc (.bare k) [] ++ 61 :: (SV.bool x).enc ++ [] := by
    rw [keyEnc_bare, boolText_enc]
    exact drop_eq_of (a := hdr t ++ [10]) (by rw [← hsrc]; try simp) _ (by simp [hdr] <;> omega)
  have hr2 := kvr_at (cfg := mkCfg pf maxK maxD tz) (R := fr - 1) (header := [t])
    (out := { data := nestDict [t] [], flags := { tree := fsetAux EXPLICIT_NEST false [t] [], pending := [] } })
    (bareOk_kpart hk) (by simp) hmax1 (v := SV.bool x) trivial (by simp) (by simp [SV.depth]; omega) hd2
  rw [keyEnc_bare, keyVal_bare] at hr2
  simp [kvBody, contKeysLoop, Flags.is_, isAux, fsetAux, dset, dget_cons, dget_nil, FNode.empty, FNode.flags,
    FNode.rflags, addFlag, FROZEN, EXPLICIT_NEST, withNest, nestDict, overwriteErr, SV.val, TVal.isDictOrList,
    bind, Except.bind, pure, Except.pure] at hr2
  obtain ⟨c1, hg1, hi1, hw1, h101⟩ := kv_line_pos (tail := 61 :: (SV.bool x).enc ++ []) (by rw [hd2, keyEnc_bare]; simp) hk
  refine (mainLoop_kv_hdr hg1 hi1 hw1 h101 hr2 (by omega)).trans ?_
  have hend : src[t.length + 2 + 1 + k.length + 1 + (SV.bool x).enc.length]? = none := by
    rw [List.getElem?_eq_none_iff, ← hsrc, boolText_enc]; simp [hdr]; omega
  simp [hend]

/-! ## Redefinition and unclosed headers -/

/-- Dotted keys, TOML 1.1 "Table" ("Since tables cannot be defined more than once, redefining
such tables using a [table] header is not allowed. Likewise, using dotted keys to redefine tables
already defined in [table] form is not allowed"): for all bare keys `a`, `b`, `c` and boolean `X`,
`loads('[a.b]\n[a]\nb.c=X')` raises "Cannot redefine namespace ('a', 'b')" after `X`. With at
least sixteen frames left. -/
def RedefineNamespace : Prop :=
  ∀ (pf : ParseFloat) (maxK maxD : Nat) (tz : TzCache) (fr : Nat) (a b c : Str) (x : Bool),
    bareOk a → bareOk b → bareOk c → 2 ≤ maxK → 16 ≤ fr →
    loads pf maxK maxD tz fr (.str (hdr (a ++ 46 :: b) ++ 10 :: hdr a ++ 10 :: b ++ 46 :: c ++ 61 :: boolText x)) =
      .error (tde (S "Cannot redefine namespace " ++ keyRepr [a, b])
        (hdr (a ++ 46 :: b) ++ 10 :: hdr a ++ 10 :: b ++ 46 :: c ++ 61 :: boolText x)
        (2 * a.length + 2 * b.length + c.length + 9 + (boolText x).length))

theorem redefineNamespace_proven : RedefineNamespace := by
  intro pf maxK maxD tz fr a b c x ha hb hc hk hfr
  have hmax1 : ([] : List KPart).length + 1 ≤ (mkCfg pf maxK maxD tz).maxKeyParts := by simp [mkCfg]; omega
  have hmax2 : [KPart.bare b].length + 1 ≤ (mkCfg pf maxK maxD tz).maxKeyParts := by simp [mkCfg]; omega
  have hmax2' : [KPart.bare c].length + 1 ≤ (mkCfg pf maxK maxD tz).maxKeyParts := by simp [mkCfg]; omega
  have hR9 : 9 ≤ fr - 1 := by omega
  have hna := bare_no13 ha
  have hnb := bare_no13 hb
  have hnc := bare_no13 hc
  have hnx := boolText_no13' x
  generalize hsrc : hdr (a ++ 46 :: b) ++ 10 :: hdr a ++ 10 :: b ++ 46 :: c ++ 61 :: boolText x = src
  have h13 : 13 ∉ src := by rw [← hsrc]; simp [hdr]; simp_all
  rw [loads_eq pf maxK maxD tz fr src h13 (by omega)]
  obtain ⟨f, hf⟩ : ∃ f, src.length + 1 = f + 1 + 1 + 1 := ⟨src.length - 2, by rw [← hsrc]; simp [hdr] <;> omega⟩
  rw [hf]
  -- `[a.b]`
  have hr1 := first_dict (cfg := mkCfg pf maxK maxD tz) (src := src) (p0 := .bare a) (ps := [.bare b])
    (rest := 10 :: hdr a ++ 10 :: b ++ 46 :: c ++ 61 :: boolText x)
    (bareOk_kpart ha) (by intro p hp; simp at hp; subst hp; exact bareOk_kpart hb) hmax2
    (by rw [keyEnc_bare2, ← hsrc]; simp)
  rw [keyEnc_bare2, keyVal_bare2] at hr1
  have hg0 : src[0]? = some 91 := by rw [← hsrc]; rfl
  have hnl1 : src[(a ++ 46 :: b).length + 2]? = some 10 :=
    getElem_of_eq (a := hdr (a ++ 46 :: b)) (b := hdr a ++ 10 :: b ++ 46 :: c ++ 61 :: boolText x)
      (by rw [← hsrc]; simp) _ (by simp [hdr] <;> omega)
  rw [mainLoop_hdr_ok (hR := hR9) hg0 (finalize_nil _ rfl) hr1 hnl1]
  -- `[a]`
  have hd2 : src.drop ((a ++ 46 :: b).length + 2 + 1) =
      hdr (keyEnc (.bare a) []) ++ (10 :: b ++ 46 :: c ++ 61 :: boolText x) := by
    rw [keyEnc_bare]; exact drop_eq_of (a := hdr (a ++ 46 :: b) ++ [10]) (by rw [← hsrc]; simp) _
      (by simp [hdr] <;> omega)
  have hr2 := dict_at (cfg := mkCfg pf maxK maxD tz)
    (out := { data := nestDict [a, b] [], flags := { tree := fsetAux EXPLICIT_NEST false [a, b] [], pending := [] } })
    (bareOk_kpart ha) (by simp) hmax1 hd2
  rw [keyEnc_bare, keyVal_bare] at hr2
  have hfz : ((Flags.mk (fsetAux EXPLICIT_NEST false [a, b] []) []).is_ [a] EXPLICIT_NEST ||
      (Flags.mk (fsetAux EXPLICIT_NEST false [a, b] []) []).is_ [a] FROZEN) = false := by
    simp [Flags.is_, isAux, fsetAux, dset, dget_cons, dget_nil, FNode.empty, FNode.flags, FNode.rflags, addFlag,
      FROZEN, EXPLICIT_NEST]
  have hgo : getOrCreateNest true [a] (nestDict [a, b] []) = .ok (nestDict [a, b] []) := by
    simp [getOrCreateNest, withNest, nestDict, dget_cons, dset, Except.map, bind, Except.bind, pure, Except.pure]
  simp only [hfz, Bool.false_eq_true, ite_false, hgo, overwriteErr, Except.map] at hr2
  have hg2 : src[(a ++ 46 :: b).length + 2 + 1]? = some 91 := getElem?_of_drop (by rw [hd2]; rfl)
  have hnl2 : src[(a ++ 46 :: b).length + 2 + 1 + 1 + a.length + 1]? = some 10 :=
    getElem_of_eq (a := hdr (a ++ 46 :: b) ++ [10] ++ hdr a) (b := b ++ 46 :: c ++ 61 :: boolText x)
      (by rw [← hsrc]; simp) _ (by simp [hdr] <;> omega)
  rw [mainLoop_hdr_ok (hR := hR9) hg2 (finalize_nil _ rfl) hr2 hnl2]
  -- `b.c=X` under `[a]`
  have hd3 : src.drop ((a ++ 46 :: b).length + 2 + 1 + 1 + a.length + 1 + 1) =
      keyEnc (.bare b) [.bare c] ++ 61 :: (SV.bool x).enc ++ [] := by
    rw [keyEnc_bare2, boolText_enc]
    exact drop_eq_of (a := hdr (a ++ 46 :: b) ++ [10] ++ hdr a ++ [10]) (by rw [← hsrc]; simp) _
      (by simp [hdr] <;> omega)
  have hr3 := kvr_at (cfg := mkCfg pf maxK maxD tz) (R := fr - 1) (header := [a])
    (out := { data := nestDict [a, b] [],
              flags := { tree := fsetAux EXPLICIT_NEST false [a] (fsetAux EXPLICIT_NEST false [a, b] []), pending := [] } })
    (bareOk_kpart hb) (by intro p hp; simp at hp; subst hp; exact bareOk_kpart hc) hmax2' (v := SV.bool x) trivial
    (by simp) (by simp [SV.depth]; omega) hd3
  rw [keyEnc_bare2, keyVal_bare2] at hr3
  generalize hP : (a ++ 46 :: b).length + 2 + 1 + 1 + a.length + 1 + 1 + (b ++ 46 :: c).length + 1 +
    (SV.bool x).enc.length = P at hr3
  have hbody : kvBody src P (Out.mk (nestDict [a, b] [])
      (Flags.mk (fsetAux EXPLICIT_NEST false [a] (fsetAux EXPLICIT_NEST false [a, b] [])) []))
      [a] [b, c] (SV.bool x).val = .error (tde (S "Cannot redefine namespace " ++ keyRepr [a, b]) src P) := by
    simp [kvBody, contKeysLoop, Flags.is_, isAux, fsetAux, dset, dget_cons, dget_nil, FNode.empty, FNode.flags,
      FNode.rflags, FNode.nested, addFlag, FROZEN, EXPLICIT_NEST, bind, Except.bind]
  rw [hbody] at hr3
  obtain ⟨c1, hg1, hi1, hw1, h101⟩ := kv_line_pos (a := b) (tail := 46 :: c ++ 61 :: (SV.bool x).enc ++ [])
    (by rw [hd3, keyEnc_bare2]; simp) hb
  refine (mainLoop_kv_err hg1 hi1 hw1 h101 hr3 (by omega)).trans ?_
  rw [← hP]; congr 2; simp [hdr, boolText_enc]; omega

/-- Table headers, TOML 1.1 "Table" (a header is a key in square brackets): for every dotted key
`K` (bare, literal or basic parts, at most `MAX_KEY_PARTS`) followed by anything that does not
continue it and is not `]` (the end of the document included), `loads('[' + K + rest)` raises
"Expected ']' at the end of a table declaration" after `K`; for `'[[' + K + rest` where `rest`
does not start with `]]`, "Expected ']]' at the end of an array declaration". With at least ten
frames left. -/
def HeaderUnclosed : Prop :=
  ∀ (pf : ParseFloat) (maxK maxD : Nat) (tz : TzCache) (fr : Nat) (p0 : KPart) (ps : List KPart) (rest : Str),
    p0.ok → (∀ p ∈ ps, p.ok) → ps.length + 1 ≤ maxK → 10 ≤ fr → 13 ∉ rest →
    (∀ c, rest.head? = some c → tomlWs c = false ∧ c ≠ 46 ∧ bareKey c = false) →
    (rest.head? ≠ some 93 →
      loads pf maxK maxD tz fr (.str (91 :: keyEnc p0 ps ++ rest)) =
        .error (tdeS "Expected ']' at the end of a table declaration" (91 :: keyEnc p0 ps ++ rest)
          ((keyEnc p0 ps).length + 1))) ∧
    ([93, 93].isPrefixOf rest = false →
      loads pf maxK maxD tz fr (.str (91 :: 91 :: keyEnc p0 ps ++ rest)) =
        .error (tdeS "Expected ']]' at the end of an array declaration" (91 :: 91 :: keyEnc p0 ps ++ rest)
          ((keyEnc p0 ps).length + 2)))

theorem headerUnclosed_proven : HeaderUnclosed := by
  intro pf maxK maxD tz fr p0 ps rest h0 hps hmax hfr h13r hrest
  have hR9 : 9 ≤ fr - 1 := by omega
  obtain ⟨c, t, hKe, hcws, hc91⟩ := keyEnc_head (ps := ps) h0
  have hK13 := keyEnc_no13 h0 hps
  have hne := keyVal_ne p0 ps
  constructor
  · intro h93
    generalize hsrc : 91 :: keyEnc p0 ps ++ rest = src
    have h13 : 13 ∉ src := by rw [← hsrc]; simp; exact ⟨hK13, h13r⟩
    rw [loads_eq pf maxK maxD tz fr src h13 (by omega)]
    obtain ⟨f, hf⟩ : ∃ f, src.length + 1 = f + 1 := ⟨src.length, rfl⟩
    rw [hf]
    have hg0 : src[0]? = some 91 := by rw [← hsrc]; rfl
    have hd1 : src.drop (0 + 1) = keyEnc p0 ps ++ rest := by rw [← hsrc]; simp
    have hg1 : src[0 + 1]? = some c := getElem?_of_drop (r := t ++ rest) (by rw [hd1, hKe]; simp)
    have hk := parseKey_enc (maxK := (mkCfg pf maxK maxD tz).maxKeyParts) h0 hps (by simp [mkCfg]; exact hmax)
      (fun c hc => hrest c hc) hd1
    have hws : skipChars src (0 + 1) tomlWs = 0 + 1 := skipChars_at hg1 hcws
    have hcl : startsAt src (0 + 1 + (keyEnc p0 ps).length) [93] = false := by
      have hd2 : src.drop (0 + 1 + (keyEnc p0 ps).length) = rest := drop_add_of_drop hd1
      unfold startsAt; rw [hd2]
      cases hr : rest with
      | nil => rfl
      | cons d r => rw [hr] at h93; simp [List.isPrefixOf] at h93 ⊢; omega
    have hrule : (if src[0 + 1]? == some 91 then createListRule (mkCfg pf maxK maxD tz) src 0
          { Out.init with flags := Flags.init }
        else createDictRule (mkCfg pf maxK maxD tz) src 0 { Out.init with flags := Flags.init }) =
        .error (tdeS "Expected ']' at the end of a table declaration" src ((keyEnc p0 ps).length + 1)) := by
      rw [if_neg (by simp [hg1, hc91])]
      simp only [createDictRule, hws, hk, bind, Except.bind, Out.init, Flags.init, flags_is _ _ hne, isAux_nil,
        Bool.or_false, Bool.false_eq_true, ite_false, Flags.set, List.isEmpty_iff, hne, getOrCreateNest,
        withNest_empty, overwriteErr, Except.map, hcl, Bool.not_false, ite_true]
      congr 2; omega
    exact mainLoop_hdr_err (hR := hR9) hg0 (finalize_nil _ rfl) hrule
  · intro h93
    generalize hsrc : 91 :: 91 :: keyEnc p0 ps ++ rest = src
    have h13 : 13 ∉ src := by rw [← hsrc]; simp; exact ⟨hK13, h13r⟩
    rw [loads_eq pf maxK maxD tz fr src h13 (by omega)]
    obtain ⟨f, hf⟩ : ∃ f, src.length + 1 = f + 1 := ⟨src.length, rfl⟩
    rw [hf]
    have hg0 : src[0]? = some 91 := by rw [← hsrc]; rfl
    have hg1 : src[0 + 1]? = some 91 := by rw [← hsrc]; rfl
    have hd2 : src.drop (0 + 2) = keyEnc p0 ps ++ rest := by rw [← hsrc]; simp
    have hg2 : src[0 + 2]? = some c := getElem?_of_drop (r := t ++ rest) (by rw [hd2, hKe]; simp)
    have hk := parseKey_enc (maxK := (mkCfg pf maxK maxD tz).maxKeyParts) h0 hps (by simp [mkCfg]; exact hmax)
      (fun c hc => hrest c hc) hd2
    have hws : skipChars src (0 + 2) tomlWs = 0 + 2 := skipChars_at hg2 hcws
    have hcl : startsAt src (0 + 2 + (keyEnc p0 ps).length) [93, 93] = false := by
      have hd3 : src.drop (0 + 2 + (keyEnc p0 ps).length) = rest := drop_add_of_drop hd2
      unfold startsAt; rw [hd3]; exact h93
    have hrule : (if src[0 + 1]? == some 91 then createListRule (mkCfg pf maxK maxD tz) src 0
          { Out.init with flags := Flags.init }
        else createDictRule (mkCfg pf maxK maxD tz) src 0 { Out.init with flags := Flags.init }) =
        .error (tdeS "Expected ']]' at the end of an array declaration" src ((keyEnc p0 ps).length + 2)) := by
      rw [if_pos (by simp [hg1])]
      simp only [createListRule, hws, hk, bind, Except.bind, Out.init, Flags.init, flags_is _ _ hne, isAux_nil,
        Bool.false_eq_true, ite_false, Flags.unsetAll, Flags.set, List.isEmpty_iff, hne, unsetAux_nil,
        append_empty hne, overwriteErr, Except.map, hcl, Bool.not_false, ite_true]
      congr 2; omega
    exact mainLoop_hdr_err (hR := hR9) hg0 (finalize_nil _ rfl) hrule

/-! ## `finalize_pending` empties the pending set, _parser.py:238-241 -/

/-- Arrays of tables and dotted keys, TOML 1.1 "Array of Tables" (each `[[t]]` starts a new
table, in which sub-tables may be defined afresh): for all bare keys `t`, `a`, `b` and boolean `X`,
`loads('[[t]]\na.b=X\n[[t]]\n[t.a]')` gives `{t: [{a: {b: X}}, {a: {}}]}`. The dotted key marks
`t.a` pending; the second `[[t]]` turns it into a flag and clears the pending set, then drops the
flags under `t`, so `[t.a]` is new. Were the pending set not cleared, the next header would mark
`t.a` again and `[t.a]` would raise "Cannot declare". With at least sixteen frames left. -/
def FinalizeClears : Prop :=
  ∀ (pf : ParseFloat) (maxK maxD : Nat) (tz : TzCache) (fr : Nat) (t a b : Str) (x : Bool),
    bareOk t → bareOk a → bareOk b → 2 ≤ maxK → 16 ≤ fr →
    loads pf maxK maxD tz fr (.str (aot t ++ 10 :: a ++ 46 :: b ++ 61 :: boolText x ++ 10 :: aot t ++ 10 ::
      hdr (t ++ 46 :: a))) =
      .ok [(t, .arr [.tbl [(a, .tbl [(b, .bool x)])], .tbl [(a, .tbl [])]])]

set_option maxHeartbeats 1600000 in
theorem finalizeClears_proven : FinalizeClears := by
  intro pf maxK maxD tz fr t a b x ht ha hb hk hfr
  have hmax1 : ([] : List KPart).length + 1 ≤ (mkCfg pf maxK maxD tz).maxKeyParts := by simp [mkCfg]; omega
  have hmaxa : [KPart.bare a].length + 1 ≤ (mkCfg pf maxK maxD tz).maxKeyParts := by simp [mkCfg]; omega
  have hmaxb : [KPart.bare b].length + 1 ≤ (mkCfg pf maxK maxD tz).maxKeyParts := by simp [mkCfg]; omega
  have hR9 : 9 ≤ fr - 1 := by omega
  have hnt := bare_no13 ht
  have hna := bare_no13 ha
  have hnb := bare_no13 hb
  have hnx := boolText_no13' x
  generalize hsrc : aot t ++ 10 :: a ++ 46 :: b ++ 61 :: boolText x ++ 10 :: aot t ++ 10 :: hdr (t ++ 46 :: a) = src
  have h13 : 13 ∉ src := by rw [← hsrc]; simp [hdr, aot]; simp_all
  rw [loads_eq pf maxK maxD tz fr src h13 (by omega)]
  obtain ⟨f, hf⟩ : ∃ f, src.length + 1 = f + 1 + 1 + 1 + 1 := ⟨src.length - 3, by rw [← hsrc]; simp [hdr, aot] <;> omega⟩
  rw [hf]
  -- `[[t]]`
  have hr1 := first_list (cfg := mkCfg pf maxK maxD tz) (src := src) (p0 := .bare t) (ps := [])
    (rest := 10 :: a ++ 46 :: b ++ 61 :: boolText x ++ 10 :: aot t ++ 10 :: hdr (t ++ 46 :: a))
    (bareOk_kpart ht) (by simp) hmax1 (by rw [keyEnc_bare, ← hsrc]; simp)
  rw [keyEnc_bare, keyVal_bare] at hr1
  simp only [show ([t] : Key).dropLast = [] from rfl, show ([t] : Key).getLastD [] = t from rfl, nestDict] at hr1
  have hg0 : src[0]? = some 91 := by rw [← hsrc]; rfl
  have hnl1 : src[t.length + 4]? = some 10 :=
    getElem_of_eq (a := aot t) (b := a ++ 46 :: b ++ 61 :: boolText x ++ 10 :: aot t ++ 10 :: hdr (t ++ 46 :: a))
      (by rw [← hsrc]; simp) _ (by simp [aot] <;> omega)
  rw [mainLoop_hdr_ok (hR := hR9) hg0 (finalize_nil _ rfl) hr1 hnl1]
  -- `a.b=X` under `[[t]]`
  have hd2 : src.drop (t.length + 4 + 1) =
      keyEnc (.bare a) [.bare b] ++ 61 :: (SV.bool x).enc ++ (10 :: aot t ++ 10 :: hdr (t ++ 46 :: a)) := by
    rw [keyEnc_bare2, boolText_enc]
    exact drop_eq_of (a := aot t ++ [10]) (by rw [← hsrc]; simp) _ (by simp [aot] <;> omega)
  have hr2 := kvr_at (cfg := mkCfg pf maxK maxD tz) (R := fr - 1) (header := [t])
    (out := Out.mk [(t, .arr [.tbl []])] (Flags.mk (fsetAux EXPLICIT_NEST false [t] []) []))
    (bareOk_kpart ha) (by intro p hp; simp at hp; subst hp; exact bareOk_kpart hb) hmaxb (v := SV.bool x) trivial
    (by intro c hc; simp at hc; subst hc; decide) (by simp [SV.depth]; omega) hd2
  rw [keyEnc_bare2, keyVal_bare2] at hr2
  generalize hP2 : t.length + 4 + 1 + (a ++ 46 :: b).length + 1 + (SV.bool x).enc.length = P2 at hr2
  have hb2 : kvBody src P2 (Out.mk [(t, .arr [.tbl []])] (Flags.mk (fsetAux EXPLICIT_NEST false [t] []) []))
      [t] [a, b] (SV.bool x).val =
      .ok (P2, Out.mk [(t, .arr [.tbl [(a, .tbl [(b, .bool x)])]])]
        (Flags.mk (fsetAux EXPLICIT_NEST false [t] []) [([t, a], EXPLICIT_NEST)])) := by
    simp [kvBody, contKeysLoop, Flags.is_, isAux, fsetAux, dset, dget_cons, dget_nil, FNode.empty, FNode.flags,
      FNode.rflags, FNode.nested, addFlag, Flags.addPending, withNest, overwriteErr, SV.val, TVal.isDictOrList,
      FROZEN, EXPLICIT_NEST, bind, Except.bind, pure, Except.pure]
  rw [hb2] at hr2
  obtain ⟨c1, hg1, hi1, hw1, h101⟩ := kv_line_pos (a := a)
    (tail := 46 :: b ++ 61 :: (SV.bool x).enc ++ (10 :: aot t ++ 10 :: hdr (t ++ 46 :: a)))
    (by rw [hd2, keyEnc_bare2]; simp) ha
  rw [mainLoop_kv_hdr hg1 hi1 hw1 h101 hr2 (by omega)]
  have hdP2 : src.drop P2 = 10 :: (aot (keyEnc (.bare t) []) ++ 10 :: hdr (t ++ 46 :: a)) := by
    rw [← hP2, keyEnc_bare, boolText_enc]
    exact drop_eq_of (a := aot t ++ 10 :: a ++ 46 :: b ++ 61 :: boolText x) (by rw [← hsrc]; simp) _
      (by simp [aot, boolText_enc] <;> omega)
  simp only [getElem?_of_drop hdP2, reduceCtorEq, ite_false, ite_true]
  -- `[[t]]` again
  have hd3 := drop_succ_of_drop hdP2
  have hr3 := list_at (cfg := mkCfg pf maxK maxD tz)
    (out := Out.mk [(t, .arr [.tbl [(a, .tbl [(b, .bool x)])]])]
      (Flags.mk (fsetAux EXPLICIT_NEST false [t, a] (fsetAux EXPLICIT_NEST false [t] [])) []))
    (bareOk_kpart ht) (by simp) hmax1 hd3
  rw [keyEnc_bare, keyVal_bare] at hr3
  have hfz3 : (Flags.mk (fsetAux EXPLICIT_NEST false [t, a] (fsetAux EXPLICIT_NEST false [t] [])) []).is_ [t]
      FROZEN = false := by
    simp [Flags.is_, isAux, fsetAux, dset, dget_cons, dget_nil, FNode.empty, FNode.flags, FNode.rflags, addFlag,
      FROZEN, EXPLICIT_NEST]
  have hap3 : appendNestToList [t] [(t, .arr [.tbl [(a, .tbl [(b, .bool x)])]])] =
      .ok [(t, .arr [.tbl [(a, .tbl [(b, .bool x)])], .tbl []])] := by
    simp [appendNestToList, withNest, dget_cons, dset, Except.map]
  have hun3 : unsetAux [t] (fsetAux EXPLICIT_NEST false [t, a] (fsetAux EXPLICIT_NEST false [t] [])) = [] := by
    simp [unsetAux, dpop, fsetAux, dset, dget_cons, dget_nil, FNode.empty]
  simp only [hfz3, Bool.false_eq_true, ite_false, hap3, overwriteErr, Except.map, hun3] at hr3
  have hfin : (Flags.mk (fsetAux EXPLICIT_NEST false [t] []) [([t, a], EXPLICIT_NEST)]).finalizePending =
      .ok (Flags.mk (fsetAux EXPLICIT_NEST false [t, a] (fsetAux EXPLICIT_NEST false [t] [])) []) := by
    simp [Flags.finalizePending, Flags.set, List.foldlM, bind, Except.bind, pure, Except.pure]
  have hg3 : src[P2 + 1]? = some 91 := getElem?_of_drop (by rw [hd3]; rfl)
  have hd3b : src.drop (P2 + 1 + 2 + t.length + 2) = 10 :: hdr (t ++ 46 :: a) := by
    have := drop_add_of_drop (a := aot (keyEnc (.bare t) [])) hd3
    rw [keyEnc_bare] at this
    have e : P2 + 1 + (aot t).length = P2 + 1 + 2 + t.length + 2 := by simp [aot]; omega
    rw [← e]; exact this
  have hnl3 := getElem?_of_drop hd3b
  rw [mainLoop_hdr_ok (hR := hR9) hg3 hfin hr3 hnl3]
  -- `[t.a]`
  have hd4 : src.drop (P2 + 1 + 2 + t.length + 2 + 1) = hdr (keyEnc (.bare t) [.bare a]) ++ [] := by
    rw [keyEnc_bare2]; simpa using drop_succ_of_drop hd3b
  have hr4 := dict_at (cfg := mkCfg pf maxK maxD tz)
    (out := Out.mk [(t, .arr [.tbl [(a, .tbl [(b, .bool x)])], .tbl []])]
      (Flags.mk (fsetAux EXPLICIT_NEST false [t] []) []))
    (bareOk_kpart ht) (by intro p hp; simp at hp; subst hp; exact bareOk_kpart ha) hmaxa hd4
  rw [keyEnc_bare2, keyVal_bare2] at hr4
  have hfz4 : ((Flags.mk (fsetAux EXPLICIT_NEST false [t] []) []).is_ [t, a] EXPLICIT_NEST ||
      (Flags.mk (fsetAux EXPLICIT_NEST false [t] []) []).is_ [t, a] FROZEN) = false := by
    simp [Flags.is_, isAux, fsetAux, dset, dget_cons, dget_nil, FNode.empty, FNode.flags, FNode.rflags,
      FNode.nested, addFlag, FROZEN, EXPLICIT_NEST]
  have hgo4 : getOrCreateNest true [t, a] [(t, .arr [.tbl [(a, .tbl [(b, .bool x)])], .tbl []])] =
      .ok [(t, .arr [.tbl [(a, .tbl [(b, .bool x)])], .tbl [(a, .tbl [])]])] := by
    simp [getOrCreateNest, withNest, dget_cons, dget_nil, dset, Except.map, bind, Except.bind, pure, Except.pure]
  simp only [hfz4, Bool.false_eq_true, ite_false, hgo4, overwriteErr, Except.map] at hr4
  have hg4 : src[P2 + 1 + 2 + t.length + 2 + 1]? = some 91 := getElem?_of_drop (by rw [hd4]; rfl)
  have hend : src[P2 + 1 + 2 + t.length + 2 + 1 + 1 + (t ++ 46 :: a).length + 1]? = none := by
    have := drop_add_of_drop (a := hdr (t ++ 46 :: a)) (r := []) (by rw [keyEnc_bare2] at hd4; exact hd4)
    have e : P2 + 1 + 2 + t.length + 2 + 1 + (hdr (t ++ 46 :: a)).length =
        P2 + 1 + 2 + t.length + 2 + 1 + 1 + (t ++ 46 :: a).length + 1 := by simp [hdr]; omega
    rw [e] at this; exact getElem?_of_drop_nil this
  rw [mainLoop_hdr_end (hR := hR9) hg4 (finalize_nil _ rfl) hr4 hend]

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
