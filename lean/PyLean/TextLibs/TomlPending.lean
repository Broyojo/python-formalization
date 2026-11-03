import PyLean.TextLibs.TomlDoc

/-!
Dotted keys and table headers: `key_value_rule` records the tables a dotted key defines as
pending flags (`Flags.add_pending`), and the next header turns them on
(`Flags.finalize_pending`), so `[K]` after `K.x = v` is rejected.
-/

namespace PyLean.TextLibs.Toml

/-- The proper prefixes `k[:1], ..., k[:n]`. -/
def pref (k : Key) (n : Nat) : List Key := (List.range n).map (fun i => k.take (i + 1))

theorem contKeys_dotted (k : Key) (x : Str) :
    (List.range ((k ++ [x]).length - 1)).map (fun i => ([] : Key) ++ (k ++ [x]).take (i + 1)) = pref k k.length := by
  simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel, List.nil_append, pref]
  apply List.map_congr_left
  intro i hi
  simp at hi
  rw [List.take_append_of_le_length (by omega)]

theorem contKeysLoop_append (src : Str) (pos : Nat) :
    ∀ (L1 L2 : List Key) (fl : Flags), contKeysLoop src pos (L1 ++ L2) fl =
      (contKeysLoop src pos L1 fl).bind (contKeysLoop src pos L2)
  | [], L2, fl => rfl
  | a :: L1, L2, fl => by
    simp only [List.cons_append, contKeysLoop]
    split
    · rfl
    · exact contKeysLoop_append src pos L1 L2 _

theorem contKeys_pending (src : Str) (pos : Nat) (k : Key) : ∀ n, n ≤ k.length →
    contKeysLoop src pos (pref k n) { tree := [], pending := [] } =
      .ok { tree := [], pending := (pref k n).map (·, EXPLICIT_NEST) }
  | 0, _ => rfl
  | n + 1, h => by
    have hsplit : pref k (n + 1) = pref k n ++ [k.take (n + 1)] := by simp [pref, List.range_succ]
    rw [hsplit, contKeysLoop_append, contKeys_pending src pos k n (by omega)]
    have hmem : k.take (n + 1) ∉ pref k n := by
      intro hm
      simp only [pref, List.mem_map, List.mem_range] at hm
      obtain ⟨i, hi, he⟩ := hm
      have := congrArg List.length he
      simp at this; omega
    have hnc : ((pref k n).map (·, EXPLICIT_NEST)).contains (k.take (n + 1), EXPLICIT_NEST) = false := by
      rw [Bool.eq_false_iff]
      intro hc
      rw [List.contains_iff_mem, List.mem_map] at hc
      obtain ⟨a, ha, he⟩ := hc
      simp only [Prod.mk.injEq] at he
      exact hmem (he.1 ▸ ha)
    simp [Except.bind, contKeysLoop, Flags.is_, isAux_nil, Flags.addPending, hnc, hmem]

theorem pref_ne (k : Key) (n : Nat) (hk : k ≠ []) : ∀ a ∈ pref k n, a ≠ [] := by
  intro a ha
  simp only [pref, List.mem_map, List.mem_range] at ha
  obtain ⟨i, _, rfl⟩ := ha
  cases k with
  | nil => exact absurd rfl hk
  | cons c t => simp

theorem foldl_pending_last (k : Key) (hk : k ≠ []) : ∀ (L : List Key) (fl : Flags), (∀ a ∈ L, a ≠ []) →
    ∃ t, ((L ++ [k]).map (·, EXPLICIT_NEST)).foldlM
      (fun (acc : Flags) (kf : Key × Nat) => acc.set kf.1 kf.2 false) fl =
      .ok { fl with tree := fsetAux EXPLICIT_NEST false k t }
  | [], fl, _ => ⟨fl.tree, by simp [List.foldlM, Flags.set, hk]⟩
  | a :: L, fl, h => by
    have ha := h a (by simp)
    obtain ⟨t, ht⟩ := foldl_pending_last k hk L { fl with tree := fsetAux EXPLICIT_NEST false a fl.tree }
      (fun b hb => h b (by simp [hb]))
    refine ⟨t, ?_⟩
    have e : Flags.set fl a EXPLICIT_NEST false = .ok { fl with tree := fsetAux EXPLICIT_NEST false a fl.tree } := by
      simp [Flags.set, ha]
    rw [List.cons_append, List.map_cons, List.foldlM_cons]
    dsimp only
    rw [e]
    exact ht

/-- `finalize_pending` turns the flag of the last pending key on. -/
theorem finalize_last (k : Key) (hk : k ≠ []) :
    ∃ t, Flags.finalizePending { tree := [], pending := (pref k k.length).map (·, EXPLICIT_NEST) } =
      .ok { tree := fsetAux EXPLICIT_NEST false k t, pending := [] } := by
  obtain ⟨m, hm⟩ : ∃ m, k.length = m + 1 := ⟨k.length - 1, by cases k <;> simp_all⟩
  have hsplit : pref k k.length = pref k m ++ [k] := by
    rw [hm]; simp only [pref, List.range_succ, List.map_append, List.map_singleton]
    rw [List.take_of_length_le (by omega)]
  rw [hsplit]
  obtain ⟨t, ht⟩ := foldl_pending_last k hk (pref k m)
    { tree := [], pending := (pref k m ++ [k]).map (·, EXPLICIT_NEST) } (pref_ne k m hk)
  refine ⟨t, ?_⟩
  simp only [Flags.finalizePending]
  rw [ht]; rfl

/-- Dotted keys, TOML 1.1 "Table": "Since tables cannot be defined more than once, redefining such
tables using a [table] header is not allowed": for every dotted key `K` (bare, literal or basic
parts) and bare key `x`, `loads('K.x=true\n[K]')` raises "Cannot declare K twice" at the position
after the header's key. -/
def DottedThenHeader : Prop :=
  ∀ (pf : ParseFloat) (maxK maxD : Nat) (p0 : KPart) (ps : List KPart) (x : Str),
    p0.ok → (∀ p ∈ ps, p.ok) → ps.length + 2 ≤ maxK → x ≠ [] → (∀ c ∈ x, bareKey c = true) →
    let K := keyEnc p0 ps
    let k := keyVal p0 ps
    loads pf maxK maxD (.str ((K ++ 46 :: x) ++ S "=true" ++ 10 :: hdr K)) =
      .error (tde (S "Cannot declare " ++ keyRepr k ++ S " twice") ((K ++ 46 :: x) ++ S "=true" ++ 10 :: hdr K)
        (2 * K.length + x.length + 8))

theorem dottedThenHeader_proven : DottedThenHeader := by
  intro pf maxK maxD p0 ps x h0 hps hmax hx hxb
  simp only
  have hne := keyVal_ne p0 ps
  have hKx : keyEnc p0 (ps ++ [.bare x]) = keyEnc p0 ps ++ 46 :: x := by simp [keyEnc, KPart.enc]
  have hkx : keyVal p0 (ps ++ [.bare x]) = keyVal p0 ps ++ [x] := by simp [keyVal, KPart.val]
  have hpsx : ∀ p ∈ ps ++ [.bare x], p.ok := by
    intro p hp; simp only [List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · exact hps p hp
    · exact ⟨hx, hxb⟩
  have h13x := keyEnc_no13 h0 hpsx
  rw [hKx] at h13x
  generalize hK : keyEnc p0 ps = K at hKx h13x
  generalize hk : keyVal p0 ps = k at hne hkx
  have h13K : 13 ∉ K := by rw [← hK]; exact keyEnc_no13 h0 hps
  generalize hsrc : (K ++ 46 :: x) ++ S "=true" ++ 10 :: hdr K = src
  have h13 : 13 ∉ src := by
    rw [← hsrc]; simp only [hdr, S, List.cons_append, List.mem_cons, List.mem_append, not_or]
    (simp_all) <;> decide
  rw [loads_eq pf maxK maxD src h13]
  obtain ⟨f, hf⟩ : ∃ f, src.length + 1 = f + 1 + 1 := ⟨src.length - 1, by rw [← hsrc]; simp [hdr] <;> omega⟩
  rw [hf]
  -- the line `K.x=true`
  have hd0 : src.drop 0 = keyEnc p0 (ps ++ [.bare x]) ++ (61 :: (S "true" ++ 10 :: hdr K)) := by
    rw [hKx, ← hsrc]; simp; rfl
  have hkey := parseKey_enc (maxK := (mkCfg pf maxK maxD).maxKeyParts) (src := src) (pos := 0) h0 hpsx
    (show (ps ++ [KPart.bare x]).length + 1 ≤ maxK by simp; omega)
    (by intro c hc; simp at hc; subst hc; decide) hd0
  rw [hKx, hkx] at hkey
  have hd1 : src.drop ((K ++ 46 :: x).length) = 61 :: (S "true" ++ 10 :: hdr K) := by
    simpa using drop_add_of_drop (src := src) (pos := 0) (a := K ++ 46 :: x) (r := 61 :: (S "true" ++ 10 :: hdr K))
      (by rw [← hKx]; exact hd0)
  have hg1 := getElem?_of_drop hd1
  have hd2 : src.drop ((K ++ 46 :: x).length + 1) = S "true" ++ (10 :: hdr K) := drop_succ_of_drop hd1
  have hsk : skipChars src ((K ++ 46 :: x).length + 1) tomlWs = (K ++ 46 :: x).length + 1 :=
    skipChars_at (c := 116) (getElem?_of_drop (r := S "rue" ++ 10 :: hdr K) (by rw [hd2]; rfl)) (by decide)
  have hval := parseValue_bool (cfg := mkCfg pf maxK maxD) (src := src) (pos := (K ++ 46 :: x).length + 1)
    (f := vFuel src - 1 - 1) (rest := 10 :: hdr K) true (by simpa using hd2)
  have hfuel : vFuel src - 1 = vFuel src - 1 - 1 + 1 := by unfold vFuel; omega
  have hpkv : parseKeyValuePair (mkCfg pf maxK maxD) src (vFuel src) 0 =
      .ok ((K ++ 46 :: x).length + 1 + 4, k ++ [x], .bool true) := by
    rw [show vFuel src = vFuel src - 1 + 1 by unfold vFuel; omega]
    simp only [parseKeyValuePair, hkey, bind, Except.bind, Nat.zero_add, hg1,
      show (some 61 != some 61) = false from rfl, Bool.false_eq_true, ite_false, hsk]
    rw [hfuel, hval]; rfl
  have hrule : keyValueRule (mkCfg pf maxK maxD) src 0 Out.init [] =
      .ok ((K ++ 46 :: x).length + 1 + 4,
        { data := nestDict k [(x, .bool true)],
          flags := { tree := [], pending := (pref k k.length).map (·, EXPLICIT_NEST) } }) := by
    simp only [keyValueRule, hpkv, bind, Except.bind]
    rw [contKeys_dotted, show Out.init.flags = { tree := [], pending := [] } from rfl,
      contKeys_pending src _ k k.length (Nat.le_refl _)]
    simp only [List.dropLast_concat, List.getLastD_concat, List.nil_append, Flags.is_, List.isEmpty_iff, hne,
      ite_false, isAux_nil, Bool.false_eq_true]
    rw [show Out.init.data = [] from rfl, withNest_empty]
    simp [dget_nil, dset_nil, overwriteErr, Except.map, TVal.isDictOrList, pure, Except.pure, nestDict]
  -- the first statement
  obtain ⟨c, t, hke, hki, hcws, hc10⟩ := keyInitial_head p0 h0
  have hc : src[0]? = some c := by
    have : src = c :: (t ++ (ps ++ [KPart.bare x]).flatMap (fun p => 46 :: p.enc) ++ 61 :: (S "true" ++ 10 :: hdr K)) := by
      have := hd0; simp only [List.drop_zero] at this; rw [this]; simp [keyEnc, hke]
    rw [this]; rfl
  rw [mainLoop_kv hc hki hcws hc10 hrule]
  have hd4 : src.drop ((K ++ 46 :: x).length + 1 + 4) = 10 :: hdr K := by
    have := drop_add_of_drop (a := S "true") (r := 10 :: hdr K) hd2
    rw [show (S "true").length = 4 from rfl] at this; exact this
  have hn : src[(K ++ 46 :: x).length + 1 + 4]? = some 10 := getElem?_of_drop hd4
  simp only [hn, reduceCtorEq, ite_false, ite_true]
  -- the header `[K]`
  obtain ⟨tt, hfin⟩ := finalize_last k hne
  have hd5 : src.drop ((K ++ 46 :: x).length + 1 + 4 + 1) = hdr K ++ [] := by simpa using drop_succ_of_drop hd4
  have hg5 : src[(K ++ 46 :: x).length + 1 + 4 + 1]? = some 91 := getElem?_of_drop (by rw [hd5]; rfl)
  have hr := dict_at (cfg := mkCfg pf maxK maxD)
    (out := { data := nestDict k [(x, .bool true)],
              flags := { tree := fsetAux EXPLICIT_NEST false k tt, pending := [] } })
    h0 hps (show ps.length + 1 ≤ maxK by omega) (by rw [hK]; exact hd5)
  rw [hK, hk] at hr
  simp only [flags_is _ _ hne, isAux_fsetAux_self _ _ k tt hne, Bool.true_or, ite_true] at hr
  rw [show (K ++ 46 :: x).length + 1 + 4 + 1 + 1 + K.length = 2 * K.length + x.length + 8 by simp; omega] at hr
  exact mainLoop_hdr_err (f := f)
    (out := { data := nestDict k [(x, .bool true)],
              flags := { tree := [], pending := (pref k k.length).map (·, EXPLICIT_NEST) } })
    hg5 hfin hr

end PyLean.TextLibs.Toml
