import PyLean.JsonMod.RoundTripDec

/-!
`json.dumps` output is accepted by `json.loads`, and `loads(dumps(v))` gives `v`
back for JSON-representable values.
-/

namespace PyLean.JsonMod

open PyLean

theorem dumpsC_eq (cfg : ECfg) (hc : cfg.customEnc = none) (v : EVal) :
    dumpsC cfg v = cEnc cfg (encFuel cfg v) 0 [] v := by
  cases v with
  | str x =>
    have e : encFuel cfg (.str x) = cfg.dfltDepth + 1 := by simp [encFuel, EVal.depth]; omega
    simp [dumpsC, e, cEnc, cEncStr_std hc, cStrEnc]
  | _ => rfl

theorem DCfg.Rec.real {dcfg : DCfg} (h : dcfg.Rec) : dcfg.Real :=
  ⟨fun a => by rw [h.fin]; simp [fuelOut], fun a => by rw [h.arr]; simp [fuelOut], h.flt,
   fun g hg t => by obtain ⟨j, e⟩ := h.int g hg t; rw [e]; simp [fuelOut], h.con⟩

/-- `loads` from the result of the C scanner at index 0 (no white space first). -/
theorem loads_of_scan (dcfg : DCfg) (d : PStr) (j : JVal)
    (hscan : cScanOnce dcfg d (docFuel d) 0 = .ok (j, d.length)) (hw0 : wsEnd d 0 = 0) :
    loadsC dcfg d = .ok j ∧ loadsPy dcfg d = .ok j := by
  have hraw : rawDecodeC dcfg d ((0 : Nat) : Int) = .ok (j, (d.length : Int)) := by
    have hr : ¬ (((0 : Nat) : Int) < ssizeMin ∨ ((0 : Nat) : Int) > ssizeMax) := by
      simp only [ssizeMin, ssizeMax]; omega
    have hn : ¬ (((0 : Nat) : Int) < 0) := by omega
    simp only [rawDecodeC, hr, hn, ↓reduceIte, Int.toNat_natCast, hscan]
    rfl
  have hpy : rawDecodePy dcfg d ((0 : Nat) : Int) = .ok (j, (d.length : Int)) := by
    have h0 : ((0 : Nat) : Int) ≤ ssizeMax := by simp only [ssizeMax]; omega
    rcases raw_nat_twin dcfg d 0 h0 with h | ⟨_, _, _, _, h, _⟩ | ⟨_, _, _, _, h, _⟩
    · rw [h, hraw]
    · rw [hraw] at h; cases h
    · rw [hraw] at h; cases h
  have hend : wsEndPy d (d.length : Int) = (d.length : Int) := by
    rw [wsEndPy_nat (Nat.le_refl _), wsEnd_of_none (by simp)]
  constructor
  · unfold loadsC decodeWith
    rw [hw0, hraw]
    simp [hend]
  · unfold loadsPy decodeWith
    rw [hw0, hpy]
    simp [hend]

/-- `loads` on the text written by `dumps`, in both decoders. -/
theorem loads_enc (cfg : ECfg) (dcfg : DCfg) (v : EVal) (d : PStr) (hL : Layout cfg) (hR : dcfg.Rec)
    (hok : v.okJ = true) (he : dumpsC cfg v = .ok d) :
    loadsC dcfg d = .ok (decV cfg dcfg (encFuel cfg v) v) ∧
    loadsPy dcfg d = .ok (decV cfg dcfg (encFuel cfg v) v) := by
  rw [dumpsC_eq cfg hL.cst] at he
  have hs : d.drop 0 = d ++ [] := by simp
  have hD := (dec_enc cfg dcfg d hL hR (docFuel d)).1 _ 0 [] v d 0 [] hok he hs (Or.inl rfl)
  have hg := docFuel_good dcfg hR.real d 0
  have hscan : cScanOnce dcfg d (docFuel d) 0 = .ok (decV cfg dcfg (encFuel cfg v) v, d.length) := by
    rcases hD with h | h
    · exact absurd h hg.1
    · simpa using h
  obtain ⟨c, r, hdc, hc⟩ := cEnc_head hL hok he
  have hw0 : wsEnd d 0 = 0 := by
    have hc1 := hc.not.1
    rw [hdc]
    simp [wsEnd, wsLen, hc1]
  exact loads_of_scan dcfg d _ hscan hw0

theorem Layout.ok {cfg : ECfg} (hL : Layout cfg) : cfg.Ok :=
  ⟨hL.cst, fun n t v' h => EVal.ok_of_okJ v' (hL.dfl n t v' h)⟩

/-- `json.dumps` output is accepted by `json.loads`: for every value without
float values (`EVal.okJ`; see `json-dumps-accepted-float`), every `default`
returning such values, every `ensure_ascii`, `sort_keys`, `skipkeys`,
`check_circular`, every white-space `indent` and separators made of `,`/`:` with
white space, if either encoder writes a text, both decoders return a value for
it, for every `strict` and every decoder whose hooks return (`DCfg.Rec`). -/
def DumpsAccepted : Prop :=
  ∀ (cfg : ECfg) (dcfg : DCfg) (v : EVal) (d : PStr), Layout cfg → dcfg.Rec → v.okJ = true →
    (dumpsPy cfg v = .ok d ∨ dumpsC cfg v = .ok d) →
    ∃ j, loadsPy dcfg d = .ok j ∧ loadsC dcfg d = .ok j

theorem dumpsAccepted_proven : DumpsAccepted := by
  intro cfg dcfg v d hL hR hok he
  have he' : dumpsC cfg v = .ok d := by
    rcases he with h | h
    · rw [← dumpsTwins_proven cfg v hL.ok (EVal.ok_of_okJ v hok)]; exact h
    · exact h
  obtain ⟨h1, h2⟩ := loads_enc cfg dcfg v d hL hR hok he'
  exact ⟨_, h2, h1⟩

/-! ### JSON-representable values -/

mutual
/-- The JSON value of a Python value, when it has one: `None`, bools, ints,
strings, lists, and dicts with str keys. Objects decode to the list of their
items. -/
def EVal.toJ : EVal → Option JVal
  | .none => some .null
  | .bool b => some (.bool b)
  | .int n => some (.int n)
  | .str s => some (.str s)
  | .list xs => (EVal.toJList xs).map .arr
  | .dict kvs => (EVal.toJItems kvs).map .obj
  | _ => Option.none
def EVal.toJList : List EVal → Option (List JVal)
  | [] => some []
  | x :: xs =>
    match EVal.toJ x, EVal.toJList xs with
    | some j, some js => some (j :: js)
    | _, _ => Option.none
def EVal.toJItems : List (EKey × EVal) → Option (List (PStr × JVal))
  | [] => some []
  | (.str k, x) :: r =>
    match EVal.toJ x, EVal.toJItems r with
    | some j, some ps => some ((k, j) :: ps)
    | _, _ => Option.none
  | _ => Option.none
end

/-- Distinct keys: a type invariant of `dict`. -/
def keysNodup : List (EKey × EVal) → Bool
  | [] => true
  | (k, _) :: r => r.all (fun q => decide (q.1 ≠ k)) && keysNodup r

mutual
/-- A value with a faithful round trip: with `ensure_ascii=True` (`ascii`) no
string, key or value, holds a high surrogate followed by a low surrogate; and,
as for every `dict`, the keys are distinct. -/
def EVal.clean (ascii : Bool) : EVal → Bool
  | .str s => !ascii || noSurrPair s
  | .list xs => EVal.cleanList ascii xs
  | .dict kvs => keysNodup kvs && EVal.cleanItems ascii kvs
  | _ => true
def EVal.cleanList (ascii : Bool) : List EVal → Bool
  | [] => true
  | x :: xs => EVal.clean ascii x && EVal.cleanList ascii xs
def EVal.cleanItems (ascii : Bool) : List (EKey × EVal) → Bool
  | [] => true
  | (.str k, x) :: r => (!ascii || noSurrPair k) && EVal.clean ascii x && EVal.cleanItems ascii r
  | (_, x) :: r => EVal.clean ascii x && EVal.cleanItems ascii r
end

theorem mergeSurr_of_no : ∀ t : PStr, noSurrPair t = true → mergeSurr t = t
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: t, h => by
    simp only [noSurrPair, Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff] at h
    have hn : ¬ (isHigh a = true ∧ isLow b = true) := by
      rintro ⟨h1, h2⟩
      rcases h.1 with h3 | h3 <;> simp_all
    simp only [mergeSurr, hn, ↓reduceIte]
    rw [mergeSurr_of_no (b :: t) h.2]

theorem decS_clean {ascii : Bool} {t : PStr} (h : (!ascii || noSurrPair t) = true) : decS ascii t = t := by
  cases ascii with
  | false => rfl
  | true => simpa [decS] using mergeSurr_of_no t (by simpa using h)

theorem dictSet_new (k : PStr) (v : JVal) : ∀ acc : List (PStr × JVal), (∀ q ∈ acc, q.1 ≠ k) →
    dictSet k v acc = acc ++ [(k, v)]
  | [], _ => rfl
  | (k', v') :: t, h => by
    have h1 : k' ≠ k := h (k', v') (by simp)
    simp only [dictSet, h1, ↓reduceIte, List.cons_append]
    rw [dictSet_new k v t (fun q hq => h q (by simp [hq]))]

theorem addAll_eq (dcfg : DCfg) : ∀ (ps acc : List (PStr × JVal)),
    ps.Pairwise (fun p q => p.1 ≠ q.1) → (∀ p ∈ ps, ∀ q ∈ acc, q.1 ≠ p.1) →
    addAll dcfg acc ps = acc ++ ps
  | [], acc, _, _ => by simp [addAll]
  | p :: ps, acc, h1, h2 => by
    obtain ⟨k, v⟩ := p
    rw [← addAll_cons]
    have hp := List.pairwise_cons.mp h1
    have hadd : cAddPair dcfg acc k v = acc ++ [(k, v)] := by
      unfold cAddPair
      split
      · rfl
      · exact dictSet_new k v acc (h2 (k, v) (by simp))
    rw [hadd, addAll_eq dcfg ps (acc ++ [(k, v)]) hp.2 ?_]
    · simp
    · intro p hp' q hq
      simp only [List.mem_append, List.mem_singleton] at hq
      rcases hq with hq | rfl
      · exact h2 p (by simp [hp']) q hq
      · exact (hp.1 p hp')

theorem toJItems_keys : ∀ (kvs : List (EKey × EVal)) (ps : List (PStr × JVal)), EVal.toJItems kvs = some ps →
    ∀ p ∈ ps, ∃ x, (EKey.str p.1, x) ∈ kvs
  | [], ps, h => by simp only [EVal.toJItems, Option.some.injEq] at h; subst h; simp
  | (k, x) :: r, ps, h => by
    cases k with
    | str s =>
      simp only [EVal.toJItems] at h
      cases h1 : EVal.toJ x with
      | none => rw [h1] at h; cases h
      | some j =>
        cases h2 : EVal.toJItems r with
        | none => rw [h1, h2] at h; cases h
        | some ps' =>
          rw [h1, h2] at h
          simp only [Option.some.injEq] at h
          subst h
          intro p hp
          simp only [List.mem_cons] at hp
          rcases hp with rfl | hp
          · exact ⟨x, by simp⟩
          · obtain ⟨y, hy⟩ := toJItems_keys r ps' h2 p hp
            exact ⟨y, by simp [hy]⟩
    | _ => simp [EVal.toJItems] at h

theorem toJItems_pairwise : ∀ (kvs : List (EKey × EVal)) (ps : List (PStr × JVal)), EVal.toJItems kvs = some ps →
    keysNodup kvs = true → ps.Pairwise (fun p q => p.1 ≠ q.1)
  | [], ps, h, _ => by simp only [EVal.toJItems, Option.some.injEq] at h; subst h; simp
  | (k, x) :: r, ps, h, hn => by
    simp only [keysNodup, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hn
    cases k with
    | str s =>
      simp only [EVal.toJItems] at h
      cases h1 : EVal.toJ x with
      | none => rw [h1] at h; cases h
      | some j =>
        cases h2 : EVal.toJItems r with
        | none => rw [h1, h2] at h; cases h
        | some ps' =>
          rw [h1, h2] at h
          simp only [Option.some.injEq] at h
          subst h
          refine List.pairwise_cons.mpr ⟨?_, toJItems_pairwise r ps' h2 hn.2⟩
          intro p hp
          obtain ⟨y, hy⟩ := toJItems_keys r ps' h2 p hp
          intro e
          have := hn.1 _ hy
          simp only at e this
          exact this (by rw [e])
    | _ => simp [EVal.toJItems] at h

theorem decList_eq (cfg : ECfg) (dcfg : DCfg) (f lvl : Nat) (seen : List Nat) (sep : PStr)
    (ih : ∀ lvl' seen' v t j, cEnc cfg f lvl' seen' v = .ok t → EVal.toJ v = some j →
      EVal.clean cfg.ensureAscii v = true → decV cfg dcfg f v = j) :
    ∀ (xs : List EVal) (i : Nat) (body : PStr) (js : List JVal), cEncList cfg f lvl seen sep i xs = .ok body →
      EVal.toJList xs = some js → EVal.cleanList cfg.ensureAscii xs = true →
      xs.map (decV cfg dcfg f) = js := by
  intro xs
  induction xs with
  | nil =>
    intro i body js _ h2 _
    simp only [EVal.toJList, Option.some.injEq] at h2
    simpa using h2
  | cons x xs ihx =>
    intro i body js h1 h2 h3
    obtain ⟨t, b, h4, h5, _⟩ := cEncList_cons h1
    simp only [EVal.cleanList, Bool.and_eq_true] at h3
    simp only [EVal.toJList] at h2
    cases h6 : EVal.toJ x with
    | none => rw [h6] at h2; cases h2
    | some j =>
      cases h7 : EVal.toJList xs with
      | none => rw [h6, h7] at h2; cases h2
      | some js' =>
        rw [h6, h7] at h2
        simp only [Option.some.injEq] at h2
        subst h2
        simp only [List.map_cons, List.cons.injEq]
        exact ⟨ih lvl seen x t j h4 h6 h3.1, ihx (i + 1) b js' h5 h7 h3.2⟩

theorem decItems_eq (cfg : ECfg) (hc : cfg.customEnc = none) (dcfg : DCfg) (f lvl : Nat) (seen : List Nat) (sep : PStr)
    (ih : ∀ lvl' seen' v t j, cEnc cfg f lvl' seen' v = .ok t → EVal.toJ v = some j →
      EVal.clean cfg.ensureAscii v = true → decV cfg dcfg f v = j) :
    ∀ (items : List (EKey × EVal)) (first : Bool) (r : PStr × Bool) (ps : List (PStr × JVal)),
      cEncItems cfg f lvl seen sep first items = .ok r → EVal.toJItems items = some ps →
      EVal.cleanItems cfg.ensureAscii items = true →
      decI cfg (decV cfg dcfg f) items = ps := by
  intro items
  induction items with
  | nil =>
    intro first r ps _ h2 _
    simp only [EVal.toJItems, Option.some.injEq] at h2
    simpa [decI] using h2
  | cons p items ihx =>
    obtain ⟨k, x⟩ := p
    intro first r ps h1 h2 h3
    cases k with
    | str key =>
      simp only [EVal.cleanItems, Bool.and_eq_true] at h3
      simp only [EVal.toJItems] at h2
      simp only [cEncItems, cKeyStr, cEncStr_std hc] at h1
      cases h6 : EVal.toJ x with
      | none => rw [h6] at h2; cases h2
      | some j =>
        cases h7 : EVal.toJItems items with
        | none => rw [h6, h7] at h2; cases h2
        | some ps' =>
          rw [h6, h7] at h2
          simp only [Option.some.injEq] at h2
          subst h2
          cases h8 : cEnc cfg f lvl seen x with
          | error e => rw [h8] at h1; cases h1
          | ok t =>
            rw [h8] at h1
            simp only at h1
            cases h9 : cEncItems cfg f lvl seen sep false items with
            | error e => rw [h9] at h1; cases h1
            | ok r' =>
              simp only [decI, cKeyStr, decS_clean h3.1.1, ih lvl seen x t j h8 h6 h3.1.2]
              rw [ihx false r' ps' h9 h7 h3.2]
    | _ => simp [EVal.toJItems] at h2

/-- `decV` is the JSON value of a representable value. -/
theorem decV_toJ (cfg : ECfg) (dcfg : DCfg) (hL : Layout cfg) (hs : cfg.sortKeys = false)
    (hi : dcfg.parseIntFn = none) : ∀ (f lvl : Nat) (seen : List Nat) (v : EVal) (t : PStr) (j : JVal),
    cEnc cfg f lvl seen v = .ok t → EVal.toJ v = some j → EVal.clean cfg.ensureAscii v = true →
    decV cfg dcfg f v = j := by
  intro f
  induction f with
  | zero => intro lvl seen v t j h; simp [cEnc] at h
  | succ f ih =>
    intro lvl seen v t j he hj hc
    cases v with
    | none => simp only [EVal.toJ, Option.some.injEq] at hj; subst hj; rfl
    | bool b => simp only [EVal.toJ, Option.some.injEq] at hj; subst hj; rfl
    | int n =>
      simp only [EVal.toJ, Option.some.injEq] at hj
      subst hj
      simp only [cEnc] at he
      simp [decV, decInt, he, parseInt, hi, pyInt_repr he]
    | str x =>
      simp only [EVal.toJ, Option.some.injEq] at hj
      subst hj
      simp only [decV, decS_clean (ascii := cfg.ensureAscii) hc]
    | flt b r => simp [EVal.toJ] at hj
    | back k => simp [EVal.toJ] at hj
    | other n t' => simp [EVal.toJ] at hj
    | list xs =>
      simp only [EVal.toJ, Option.map_eq_some_iff] at hj
      obtain ⟨js, h1, rfl⟩ := hj
      simp only [decV]
      by_cases hx : xs = []
      · subst hx
        simp only [EVal.toJList, Option.some.injEq] at h1
        subst h1
        rfl
      · obtain ⟨lvl', _, sep, _, body, _, _, _, hb, _⟩ := cEnc_list_view hL hx he
        rw [decList_eq cfg dcfg f lvl' seen sep ih xs 0 body js hb h1 hc]
    | dict kvs =>
      simp only [EVal.toJ, Option.map_eq_some_iff] at hj
      obtain ⟨ps, h1, rfl⟩ := hj
      simp only [EVal.clean, Bool.and_eq_true] at hc
      have hsort : sortedItems cfg kvs = kvs := by simp [sortedItems, hs]
      have hpw := toJItems_pairwise kvs ps h1 hc.1
      simp only [decV, hsort]
      by_cases hx : kvs = []
      · subst hx
        simp only [EVal.toJItems, Option.some.injEq] at h1
        subst h1
        rfl
      · obtain ⟨lvl', sep, body, first, _, _, _, _, _, hb, _⟩ := cEnc_dict_view hL hx he
        rw [hsort] at hb
        rw [decItems_eq cfg hL.cst dcfg f lvl' seen sep ih kvs true _ ps hb h1 hc.2,
          addAll_eq dcfg ps [] hpw (by simp)]
        rfl

/-- `json.loads(json.dumps(v)) == v` for every JSON-representable value
(`None`, bools, ints, strs, lists, dicts with str keys), with both encoders and
both decoders, for every `strict` and `object_pairs_hook`, every white-space
`indent` and separators built from `,` and `:`, provided that with
`ensure_ascii=True` no string holds a high surrogate followed by a low surrogate
(the excluded case is `json-roundtrip-str`). `parse_int` is the default and the
object hooks build the items (`DCfg.Rec`), `sort_keys` is false (with it the
items come back reordered), and `v` is a real Python value (`EVal.okJ`, distinct
dict keys). Objects compare as lists of items, which is stronger than `dict`
equality. Floats are `json-roundtrip-float`. -/
def RoundTrip : Prop :=
  ∀ (cfg : ECfg) (dcfg : DCfg) (v : EVal) (j : JVal) (d : PStr), Layout cfg → dcfg.Rec → cfg.sortKeys = false →
    dcfg.parseIntFn = none → v.okJ = true → EVal.toJ v = some j → EVal.clean cfg.ensureAscii v = true →
    (dumpsPy cfg v = .ok d ∨ dumpsC cfg v = .ok d) →
    loadsPy dcfg d = .ok j ∧ loadsC dcfg d = .ok j

theorem roundTrip_proven : RoundTrip := by
  intro cfg dcfg v j d hL hR hs hi hok hj hc he
  have he' : dumpsC cfg v = .ok d := by
    rcases he with h | h
    · rw [← dumpsTwins_proven cfg v hL.ok (EVal.ok_of_okJ v hok)]; exact h
    · exact h
  obtain ⟨h1, h2⟩ := loads_enc cfg dcfg v d hL hR hok he'
  rw [dumpsC_eq cfg hL.cst] at he'
  rw [decV_toJ cfg dcfg hL hs hi _ 0 [] v d j he' hj hc] at h1 h2
  exact ⟨h2, h1⟩

end PyLean.JsonMod
