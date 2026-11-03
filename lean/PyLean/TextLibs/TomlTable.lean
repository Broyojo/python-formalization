import PyLean.TextLibs.TomlKey
import PyLean.TextLibs.TomlNum

/-!
Tables: the TOML 1.1 rules on defining tables and arrays of tables, through `Flags`,
`NestedDict`, `create_dict_rule`, `create_list_rule`, `key_value_rule` and `loads`.
-/

namespace PyLean.TextLibs.Toml

/-! ## Association lists -/

theorem lookup_map_set {α : Type} (d : List (Str × α)) (k : Str) (v : α) (h : (d.lookup k).isSome) :
    (d.map (fun p => if p.1 == k then (k, v) else p)).lookup k = some v := by
  induction d with
  | nil => simp [List.lookup] at h
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    by_cases ha : a = k
    · subst ha; simp [List.lookup]
    · have h1 : (a == k) = false := by simp [ha]
      have h2 : (k == a) = false := by simp [Ne.symm ha]
      simp only [List.map_cons, h1, Bool.false_eq_true, ite_false, List.lookup, h2] at h ⊢
      exact ih h

theorem lookup_append_new {α : Type} (d : List (Str × α)) (k : Str) (v : α) (h : d.lookup k = none) :
    (d ++ [(k, v)]).lookup k = some v := by
  induction d with
  | nil => simp [List.lookup]
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    have hne : (k == a) = false := by
      cases hk : k == a
      · rfl
      · simp [List.lookup, hk] at h
    have ht : t.lookup k = none := by simpa [List.lookup, hne] using h
    simp [List.lookup, hne, ih ht]

theorem dget_dset_self {α : Type} (d : List (Str × α)) (k : Str) (v : α) : dget (dset d k v) k = some v := by
  unfold dget dset
  split
  · rename_i h; exact lookup_map_set d k v h
  · rename_i h
    exact lookup_append_new d k v (by cases hh : d.lookup k with
      | none => rfl
      | some _ => simp [hh] at h)

theorem dget_nil {α : Type} (k : Str) : dget ([] : List (Str × α)) k = none := rfl

theorem dset_nil {α : Type} (k : Str) (v : α) : dset ([] : List (Str × α)) k v = [(k, v)] := by
  simp [dset, List.lookup]

theorem dset_single {α : Type} (k : Str) (v w : α) : dset [(k, v)] k w = [(k, w)] := by
  simp [dset, List.lookup]

theorem dget_single {α : Type} (k : Str) (v : α) : dget [(k, v)] k = some v := by
  simp [dget, List.lookup]

/-! ## `Flags` -/

theorem isAux_fsetAux_self (flag : Nat) (r : Bool) :
    ∀ (key : Key) (t : List (Str × FNode)), key ≠ [] → isAux flag key (fsetAux flag r key t) = true
  | [], _, h => absurd rfl h
  | [stem], t, _ => by
    simp only [fsetAux, isAux, dget_dset_self]
    cases (dget t stem).getD .empty with
    | mk f rf ns => cases r <;> simp [FNode.flags, FNode.rflags, addFlag] <;> split <;> simp_all
  | k :: k2 :: ks, t, _ => by
    simp only [fsetAux]
    cases hn : (dget t k).getD .empty with
    | mk f rf ns =>
      simp only [isAux, dget_dset_self]
      by_cases hc : (FNode.mk f rf (fsetAux flag r (k2 :: ks) ns)).rflags.contains flag = true
      · rw [if_pos hc]
      · rw [if_neg hc]; exact isAux_fsetAux_self flag r (k2 :: ks) ns (by simp)

/-- Setting a flag on a fresh tree leaves every other flag unset along its path. -/
theorem isAux_fsetAux_nil_ne (flag g : Nat) (hne : flag ≠ g) :
    ∀ (key : Key), isAux flag key (fsetAux g false key []) = false
  | [] => rfl
  | [stem] => by
    simp [fsetAux, isAux, dget_dset_self, dget_nil, FNode.empty, addFlag, FNode.flags, FNode.rflags, hne]
  | k :: k2 :: ks => by
    simp only [fsetAux, dget_nil, Option.getD_none, FNode.empty, isAux, dget_dset_self, FNode.rflags,
      FNode.nested]
    simp only [List.contains_nil, Bool.false_eq_true, ite_false]
    exact isAux_fsetAux_nil_ne flag g hne (k2 :: ks)

/-- On a fresh tree, setting a flag on `key ++ [x]` sets nothing on `key`. -/
theorem isAux_fsetAux_nil_prefix (flag g : Nat) (x : Str) :
    ∀ (key : Key), isAux flag key (fsetAux g false (key ++ [x]) []) = false
  | [] => rfl
  | [stem] => by
    simp [fsetAux, isAux, dget_dset_self, dget_nil, FNode.empty, FNode.flags, FNode.rflags]
  | k :: k2 :: ks => by
    have : k :: k2 :: ks ++ [x] = k :: (k2 :: ks ++ [x]) := rfl
    rw [this]
    have h2 : k2 :: ks ++ [x] = k2 :: (ks ++ [x]) := rfl
    simp only [fsetAux, h2, dget_nil, Option.getD_none, FNode.empty, isAux, dget_dset_self, FNode.rflags,
      FNode.nested, List.contains_nil, Bool.false_eq_true, ite_false]
    rw [← h2]
    exact isAux_fsetAux_nil_prefix flag g x (k2 :: ks)

theorem unsetAux_nil : ∀ (key : Key), unsetAux key [] = []
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ => rfl

/-! ## `NestedDict` -/

/-- `{k1: {k2: ... d}}`. -/
def nestDict : Key → Dict → Dict
  | [], d => d
  | k :: ks, d => [(k, .tbl (nestDict ks d))]

theorem withNest_nest {α : Type} (acc : Bool) (f : Dict → Py (Dict × α)) :
    ∀ (key : Key) (d : Dict), withNest acc f key (nestDict key d) =
      (f d).map (fun r => (nestDict key r.1, r.2))
  | [], d => by simp [withNest, nestDict]; cases f d <;> rfl
  | k :: ks, d => by
    simp only [nestDict, withNest, dget_single, Option.isSome_some, ite_true]
    rw [withNest_nest acc f ks d]
    cases f d <;> simp [Except.map, bind, Except.bind, dset_single, pure, Except.pure]

theorem nestDict_nil_eq : ∀ (key : Key), nestDict key [] = [] ∨ True := fun _ => Or.inr trivial

theorem withNest_empty {α : Type} (acc : Bool) (f : Dict → Py (Dict × α)) :
    ∀ (key : Key), withNest acc f key [] = (f []).map (fun r => (nestDict key r.1, r.2))
  | [] => by simp [withNest, nestDict]; cases f [] <;> rfl
  | k :: ks => by
    simp only [withNest, dget_nil, Option.isSome_none, Bool.false_eq_true, ite_false, dset_nil, dget_single]
    rw [withNest_empty acc f ks]
    cases f [] <;> simp [Except.map, bind, Except.bind, dset_single, nestDict, pure, Except.pure]

theorem nestDict_append : ∀ (k1 k2 : Key) (d : Dict), nestDict (k1 ++ k2) d = nestDict k1 (nestDict k2 d)
  | [], _, _ => rfl
  | k :: ks, k2, d => by simp [nestDict, nestDict_append ks k2 d]

theorem dropLast_concat (key : Key) (x : Str) : (key ++ [x]).dropLast = key := by simp

/-! ## The statement loop -/

theorem skipChars_at {src : Str} {pos c : Nat} {p : Nat → Bool} (h : src[pos]? = some c) (hc : p c = false) :
    skipChars src pos p = pos :=
  skipChars_stop (fun x hx => by rw [List.head?_drop, h] at hx; cases hx; exact hc)

theorem finalize_nil (fl : Flags) (h : fl.pending = []) : fl.finalizePending = .ok fl := by
  cases fl with
  | mk tree pending => subst h; rfl

/-- One round of the statement loop on a table header whose rule succeeds, followed by a
newline. -/
theorem mainLoop_hdr_ok {cfg : Cfg} {src : Str} {f pos p : Nat} {out o : Out} {header key : Key} {fl : Flags}
    (h0 : src[pos]? = some 91) (hfin : out.flags.finalizePending = .ok fl)
    (hrule : (if src[pos + 1]? == some 91 then createListRule cfg src pos { out with flags := fl }
      else createDictRule cfg src pos { out with flags := fl }) = .ok (p, key, o))
    (hnl : src[p]? = some 10) :
    mainLoop cfg src (f + 1) pos out header = mainLoop cfg src f (p + 1) o key := by
  have hs0 : skipChars src pos tomlWs = pos := skipChars_at h0 (by decide)
  have hs1 : skipChars src p tomlWs = p := skipChars_at hnl (by decide)
  have hc1 : skipComment src p = .ok p := by simp [skipComment, hnl]
  simp only [mainLoop, hs0, h0, show ((91 : Nat) == 10) = false from rfl, Bool.false_eq_true, ite_false,
    show keyInitial 91 = false from rfl, show ((91 : Nat) == 91) = true from rfl, ite_true, hfin, bind,
    Except.bind]
  by_cases hc : (src[pos + 1]? == some 91) = true
  · rw [if_pos hc] at hrule ⊢; rw [hrule]
    simp only [pure, Except.pure, hs1, hc1, hnl, show ((10 : Nat) != 10) = false from rfl, Bool.false_eq_true,
      ite_false]
  · rw [if_neg hc] at hrule ⊢; rw [hrule]
    simp only [pure, Except.pure, hs1, hc1, hnl, show ((10 : Nat) != 10) = false from rfl, Bool.false_eq_true,
      ite_false]

/-- ... whose rule succeeds at the end of the document. -/
theorem mainLoop_hdr_end {cfg : Cfg} {src : Str} {f pos p : Nat} {out o : Out} {header key : Key} {fl : Flags}
    (h0 : src[pos]? = some 91) (hfin : out.flags.finalizePending = .ok fl)
    (hrule : (if src[pos + 1]? == some 91 then createListRule cfg src pos { out with flags := fl }
      else createDictRule cfg src pos { out with flags := fl }) = .ok (p, key, o))
    (hend : src[p]? = none) :
    mainLoop cfg src (f + 1) pos out header = .ok o.data := by
  have hs0 : skipChars src pos tomlWs = pos := skipChars_at h0 (by decide)
  have hs1 : skipChars src p tomlWs = p := skipChars_stop (fun x hx => by rw [List.head?_drop, hend] at hx; cases hx)
  have hc1 : skipComment src p = .ok p := by simp [skipComment, hend]
  simp only [mainLoop, hs0, h0, show ((91 : Nat) == 10) = false from rfl, Bool.false_eq_true, ite_false,
    show keyInitial 91 = false from rfl, show ((91 : Nat) == 91) = true from rfl, ite_true, hfin, bind,
    Except.bind]
  by_cases hc : (src[pos + 1]? == some 91) = true
  · rw [if_pos hc] at hrule ⊢; rw [hrule]; simp only [pure, Except.pure, hs1, hc1, hend]
  · rw [if_neg hc] at hrule ⊢; rw [hrule]; simp only [pure, Except.pure, hs1, hc1, hend]

/-- ... whose rule raises. -/
theorem mainLoop_hdr_err {cfg : Cfg} {src : Str} {f pos : Nat} {out : Out} {header : Key} {fl : Flags} {e : PyExc}
    (h0 : src[pos]? = some 91) (hfin : out.flags.finalizePending = .ok fl)
    (hrule : (if src[pos + 1]? == some 91 then createListRule cfg src pos { out with flags := fl }
      else createDictRule cfg src pos { out with flags := fl }) = .error e) :
    mainLoop cfg src (f + 1) pos out header = .error e := by
  have hs0 : skipChars src pos tomlWs = pos := skipChars_at h0 (by decide)
  simp only [mainLoop, hs0, h0, show ((91 : Nat) == 10) = false from rfl, Bool.false_eq_true, ite_false,
    show keyInitial 91 = false from rfl, show ((91 : Nat) == 91) = true from rfl, ite_true, hfin, bind,
    Except.bind]
  by_cases hc : (src[pos + 1]? == some 91) = true
  · rw [if_pos hc] at hrule ⊢; rw [hrule]
  · rw [if_neg hc] at hrule ⊢; rw [hrule]

/-! ## Header rules -/

theorem createDictRule_eq {cfg : Cfg} {src : Str} {pos p : Nat} {out : Out} {k : Key}
    (hws : skipChars src (pos + 1) tomlWs = pos + 1)
    (hk : parseKey cfg.maxKeyParts src (pos + 1) = .ok (p, k)) (hne : k ≠ [])
    (hclose : startsAt src p [93] = true) :
    createDictRule cfg src pos out =
      if out.flags.is_ k EXPLICIT_NEST || out.flags.is_ k FROZEN then
        .error (tde (S "Cannot declare " ++ keyRepr k ++ S " twice") src p)
      else (overwriteErr src p (getOrCreateNest true k out.data)).map (fun data =>
        (p + 1, k, { data, flags := { out.flags with tree := fsetAux EXPLICIT_NEST false k out.flags.tree } })) := by
  have hset : out.flags.set k EXPLICIT_NEST false = .ok { out.flags with tree := fsetAux EXPLICIT_NEST false k out.flags.tree } := by
    simp [Flags.set, hne]
  simp only [createDictRule, hws, hk, bind, Except.bind]
  split
  · rfl
  · rw [hset]; simp only
    cases overwriteErr src p (getOrCreateNest true k out.data) with
    | error e => rfl
    | ok d => simp [hclose, Except.map, pure, Except.pure]

theorem createListRule_eq {cfg : Cfg} {src : Str} {pos p : Nat} {out : Out} {k : Key}
    (hws : skipChars src (pos + 2) tomlWs = pos + 2)
    (hk : parseKey cfg.maxKeyParts src (pos + 2) = .ok (p, k)) (hne : k ≠ [])
    (hclose : startsAt src p [93, 93] = true) :
    createListRule cfg src pos out =
      if out.flags.is_ k FROZEN then
        .error (tde (S "Cannot mutate immutable namespace " ++ keyRepr k) src p)
      else (overwriteErr src p (appendNestToList k out.data)).map (fun data =>
        (p + 2, k, { data, flags := { out.flags with
          tree := fsetAux EXPLICIT_NEST false k (unsetAux k out.flags.tree) } })) := by
  have hun : out.flags.unsetAll k = .ok { out.flags with tree := unsetAux k out.flags.tree } := by
    simp [Flags.unsetAll, hne]
  simp only [createListRule, hws, hk, bind, Except.bind]
  split
  · rfl
  · rw [hun]; simp only [Flags.set, List.isEmpty_iff, hne, ite_false]
    cases overwriteErr src p (appendNestToList k out.data) with
    | error e => rfl
    | ok d => simp [hclose, Except.map, pure, Except.pure]

/-! ## Keys written in headers -/

/-- A dotted key without whitespace. -/
def keyEnc (p0 : KPart) (ps : List KPart) : Str := p0.enc ++ ps.flatMap (fun p => 46 :: p.enc)

def keyVal (p0 : KPart) (ps : List KPart) : Key := p0.val :: ps.map KPart.val

theorem flatMap_more (ps : List KPart) :
    (ps.map (fun p => (([] : Str), p, ([] : Str)))).flatMap moreEnc = ps.flatMap (fun p => 46 :: p.enc) := by
  induction ps with
  | nil => rfl
  | cons p t ih => simp [moreEnc, ih]

theorem parseKey_enc {maxK : Nat} {src : Str} {pos : Nat} {p0 : KPart} {ps : List KPart} {rest : Str}
    (h0 : p0.ok) (hps : ∀ p ∈ ps, p.ok) (hmax : ps.length + 1 ≤ maxK)
    (hrest : ∀ c, rest.head? = some c → tomlWs c = false ∧ c ≠ 46 ∧ bareKey c = false)
    (h : src.drop pos = keyEnc p0 ps ++ rest) :
    parseKey maxK src pos = .ok (pos + (keyEnc p0 ps).length, keyVal p0 ps) := by
  have := keySpec_proven maxK src pos p0 [] (ps.map (fun p => ([], p, []))) rest h0 (by simp [allWs])
    (by
      intro m hm
      simp only [List.mem_map] at hm
      obtain ⟨p, hp, rfl⟩ := hm
      exact ⟨by simp [allWs], hps p hp, by simp [allWs]⟩)
    hrest (by rw [h, flatMap_more]; simp [keyEnc])
  rw [this, if_pos (Or.inl (by simpa using hmax))]
  simp [keyEnc, keyVal, flatMap_more]

theorem kpart_no13 (k : KPart) (hk : k.ok) : ∀ c ∈ k.enc, c ≠ 13 := by
  intro c hc
  cases k with
  | bare s =>
    rintro rfl; exact absurd (hk.2 13 hc) (by decide)
  | lit s =>
    simp only [KPart.enc, List.cons_append, List.mem_cons, List.mem_append, List.mem_singleton,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | hc | rfl
    · decide
    · rintro rfl; exact absurd (hk 13 hc).2 (by decide)
    · decide
  | basic ps =>
    simp only [KPart.enc, List.cons_append, List.mem_cons, List.mem_append, List.mem_singleton,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | hc | rfl
    · decide
    · simp only [encAll, List.mem_flatMap] at hc
      obtain ⟨p, hp, hc⟩ := hc
      have hpo := hk p hp
      cases p with
      | raw x =>
        simp [Piece.enc] at hc; subst hc
        rintro rfl; exact absurd hpo.2.2 (by decide)
      | short x =>
        simp only [Piece.ok] at hpo
        obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp hpo
        simp only [Piece.enc, hl, Option.getD_some, List.mem_cons, List.mem_singleton, List.not_mem_nil,
          or_false] at hc
        have : l = 98 ∨ l = 116 ∨ l = 110 ∨ l = 102 ∨ l = 114 ∨ l = 101 ∨ l = 34 ∨ l = 92 := by
          unfold escLetter at hl; split at hl <;> simp at hl <;> omega
        rcases hc with rfl | rfl
        · decide
        · omega
      | x x up | u x up | U x up =>
        simp only [Piece.enc, List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
          false_or] at hc
        rcases hc with rfl | rfl | hc
        any_goals decide
        · have := hexD_all up _ x c hc
          rintro rfl; exact absurd this (by decide)
    · decide

theorem keyEnc_no13 {p0 : KPart} {ps : List KPart} (h0 : p0.ok) (hps : ∀ p ∈ ps, p.ok) :
    13 ∉ keyEnc p0 ps := by
  intro hc
  simp only [keyEnc, List.mem_append, List.mem_flatMap, List.mem_cons] at hc
  rcases hc with hc | ⟨p, hp, h | hc⟩
  · exact kpart_no13 p0 h0 13 hc rfl
  · exact absurd h (by decide)
  · exact kpart_no13 p (hps p hp) 13 hc rfl

theorem keyEnc_head {p0 : KPart} {ps : List KPart} (h0 : p0.ok) :
    ∃ c t, keyEnc p0 ps = c :: t ∧ tomlWs c = false ∧ c ≠ 91 := by
  obtain ⟨c, t, he, hws, -⟩ := KPart.head_not_ws h0
  refine ⟨c, t ++ ps.flatMap (fun p => 46 :: p.enc), by simp [keyEnc, he], hws, ?_⟩
  cases p0 with
  | bare s =>
    have := h0.2 c (by simp [KPart.enc] at he; rw [he]; simp)
    rintro rfl; exact absurd this (by decide)
  | lit s => simp [KPart.enc] at he; omega
  | basic ps => simp [KPart.enc] at he; omega

theorem crlf_id : ∀ (s : Str), 13 ∉ s → crlf s = s
  | [], _ => rfl
  | c :: r, h => by
    have hc : c ≠ 13 := fun e => h (by simp [e])
    have hr : 13 ∉ r := fun m => h (by simp [m])
    unfold crlf
    split
    · rename_i heq; simp at heq; exact absurd heq.1 hc
    · rename_i heq; simp at heq; obtain ⟨rfl, rfl⟩ := heq; rw [crlf_id r hr]
    · simp at *

theorem keyVal_ne (p0 : KPart) (ps : List KPart) : keyVal p0 ps ≠ [] := by simp [keyVal]

theorem flags_is (fl : Flags) (k : Key) (hk : k ≠ []) (flag : Nat) : fl.is_ k flag = isAux flag k fl.tree := by
  simp [Flags.is_, List.isEmpty_iff, hk]

theorem isAux_nil (flag : Nat) (k : Key) : isAux flag k [] = false := by
  match k with
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ => rfl

/-! ## Scenarios -/

/-- `[K]` -/
def hdr (K : Str) : Str := 91 :: K ++ [93]
/-- `[[K]]` -/
def aot (K : Str) : Str := 91 :: 91 :: K ++ [93, 93]

theorem hrest93 : ∀ (r : Str) c, (93 :: r).head? = some c → tomlWs c = false ∧ c ≠ 46 ∧ bareKey c = false := by
  intro r c hc; simp at hc; subst hc; decide

theorem drop_eq_of {src a b : Str} (h : src = a ++ b) (n : Nat) (hn : n = a.length) : src.drop n = b := by
  subst h; subst hn; simp

theorem getElem_of_eq {src a : Str} {c : Nat} {b : Str} (h : src = a ++ c :: b) (n : Nat) (hn : n = a.length) :
    src[n]? = some c := by
  subst h; subst hn; simp

theorem loads_eq (pf : ParseFloat) (maxK maxD : Nat) (src : Str) (h : 13 ∉ src) :
    loads pf maxK maxD (.str src) = mainLoop (mkCfg pf maxK maxD) src (src.length + 1) 0 Out.init [] := by
  simp [loads, crlf_id src h]

/-- The state after a first header `[K]` on an empty document. -/
theorem first_dict {cfg : Cfg} {src : Str} {p0 : KPart} {ps : List KPart} {rest : Str}
    (h0 : p0.ok) (hps : ∀ p ∈ ps, p.ok) (hmax : ps.length + 1 ≤ cfg.maxKeyParts)
    (h : src = hdr (keyEnc p0 ps) ++ rest) :
    (if src[0 + 1]? == some 91 then createListRule cfg src 0 { Out.init with flags := Flags.init }
      else createDictRule cfg src 0 { Out.init with flags := Flags.init }) =
      .ok ((keyEnc p0 ps).length + 2, keyVal p0 ps,
        { data := nestDict (keyVal p0 ps) [],
          flags := { tree := fsetAux EXPLICIT_NEST false (keyVal p0 ps) [], pending := [] } }) := by
  obtain ⟨c, t, hKe, hcws, hc91⟩ := keyEnc_head (ps := ps) h0
  have h1 : src[0 + 1]? = some c := getElem_of_eq (a := [91]) (b := t ++ 93 :: rest) (by rw [h, hdr, hKe]; simp) _ rfl
  rw [if_neg (by simp [h1, hc91])]
  have hd1 : src.drop (0 + 1) = keyEnc p0 ps ++ (93 :: rest) := drop_eq_of (a := [91]) (by rw [h, hdr]; simp) _ rfl
  have hk := parseKey_enc (maxK := cfg.maxKeyParts) h0 hps hmax (hrest93 rest) hd1
  have hws : skipChars src (0 + 1) tomlWs = 0 + 1 := skipChars_at h1 hcws
  have hd2 : src.drop ((keyEnc p0 ps).length + 1) = [93] ++ rest :=
    drop_eq_of (a := 91 :: keyEnc p0 ps) (by rw [h, hdr]; simp) _ (by simp)
  have hcl : startsAt src (0 + 1 + (keyEnc p0 ps).length) [93] = true := by
    rw [show 0 + 1 + (keyEnc p0 ps).length = (keyEnc p0 ps).length + 1 by omega]
    exact startsAt_of_drop hd2
  rw [createDictRule_eq hws hk (keyVal_ne p0 ps) hcl]
  simp only [Out.init, Flags.init, flags_is _ _ (keyVal_ne p0 ps), isAux_nil, Bool.or_false, Bool.false_eq_true,
    ite_false, getOrCreateNest, withNest_empty, overwriteErr, Except.map, pure, Except.pure]
  simp; omega

/-- Tables, TOML 1.1 "Table" and "Array of Tables": for every dotted header key `K` (bare,
literal or basic parts, at most `MAX_KEY_PARTS` - 1 parts) and bare key `x`:
(1) `[K]` twice raises "Cannot declare K twice" ("you cannot define a table more than once");
(2) `[[K]]` twice gives `K = [{}, {}]`;
(3) `[K]` then `[[K]]` raises "Cannot overwrite a value" (a table is not an array);
(4) `[[K]]` then `[K]` raises "Cannot declare K twice";
(5) `[K.x]` then `[K]` gives `K = {x = {}}` (a super-table may follow its sub-table);
(6) `[[K]]`, `[K.x]`, `[[K]]`, `[K.x]` gives `K = [{x = {}}, {x = {}}]` (each element of an array of
tables has its own sub-tables). -/
def TableRules : Prop :=
  ∀ (pf : ParseFloat) (maxK maxD : Nat) (p0 : KPart) (ps : List KPart) (x : Str),
    p0.ok → (∀ p ∈ ps, p.ok) → ps.length + 2 ≤ maxK → x ≠ [] → (∀ c ∈ x, bareKey c = true) →
    let K := keyEnc p0 ps
    let k := keyVal p0 ps
    loads pf maxK maxD (.str (hdr K ++ 10 :: hdr K)) =
      .error (tde (S "Cannot declare " ++ keyRepr k ++ S " twice") (hdr K ++ 10 :: hdr K) (2 * K.length + 4)) ∧
    loads pf maxK maxD (.str (aot K ++ 10 :: aot K)) =
      .ok (nestDict k.dropLast [(k.getLastD [], .arr [.tbl [], .tbl []])]) ∧
    loads pf maxK maxD (.str (hdr K ++ 10 :: aot K)) =
      .error (tdeS "Cannot overwrite a value" (hdr K ++ 10 :: aot K) (2 * K.length + 5)) ∧
    loads pf maxK maxD (.str (aot K ++ 10 :: hdr K)) =
      .error (tde (S "Cannot declare " ++ keyRepr k ++ S " twice") (aot K ++ 10 :: hdr K) (2 * K.length + 6)) ∧
    loads pf maxK maxD (.str (hdr (K ++ 46 :: x) ++ 10 :: hdr K)) = .ok (nestDict k [(x, .tbl [])]) ∧
    loads pf maxK maxD (.str (aot K ++ 10 :: hdr (K ++ 46 :: x) ++ 10 :: aot K ++ 10 :: hdr (K ++ 46 :: x))) =
      .ok (nestDict k.dropLast [(k.getLastD [], .arr [.tbl [(x, .tbl [])], .tbl [(x, .tbl [])]])])

theorem scen1 (pf : ParseFloat) (maxK maxD : Nat) (p0 : KPart) (ps : List KPart)
    (h0 : p0.ok) (hps : ∀ p ∈ ps, p.ok) (hmax : ps.length + 1 ≤ maxK) :
    loads pf maxK maxD (.str (hdr (keyEnc p0 ps) ++ 10 :: hdr (keyEnc p0 ps))) =
      .error (tde (S "Cannot declare " ++ keyRepr (keyVal p0 ps) ++ S " twice")
        (hdr (keyEnc p0 ps) ++ 10 :: hdr (keyEnc p0 ps)) (2 * (keyEnc p0 ps).length + 4)) := by
  generalize hK : keyEnc p0 ps = K
  generalize hk : keyVal p0 ps = k
  generalize hsrc : hdr K ++ 10 :: hdr K = src
  have h13 : 13 ∉ src := by
    rw [← hsrc, ← hK]; simp [hdr, keyEnc_no13 h0 hps]
  rw [loads_eq pf maxK maxD src h13]
  obtain ⟨f, hf⟩ : ∃ f, src.length + 1 = f + 1 + 1 := ⟨src.length - 1, by rw [← hsrc]; simp [hdr] <;> omega⟩
  rw [hf]
  have hr1 := first_dict (cfg := mkCfg pf maxK maxD) (rest := 10 :: hdr K) h0 hps hmax (by rw [hK, hsrc])
  rw [hK, hk] at hr1
  have hg0 : src[0]? = some 91 := by rw [← hsrc]; rfl
  have hnl : src[K.length + 2]? = some 10 := getElem_of_eq (a := hdr K) (b := hdr K) (by rw [hsrc]) _ (by simp [hdr])
  rw [mainLoop_hdr_ok hg0 (finalize_nil _ rfl) hr1 hnl]
  -- the second header
  obtain ⟨c, t, hKe, hcws, hc91⟩ := keyEnc_head (ps := ps) h0
  rw [hK] at hKe
  have hpos : K.length + 2 + 1 = K.length + 3 := rfl
  have hg3 : src[K.length + 3]? = some 91 :=
    getElem_of_eq (a := hdr K ++ [10]) (b := K ++ [93]) (by rw [← hsrc]; simp [hdr]) _ (by simp [hdr])
  have hg4 : src[K.length + 3 + 1]? = some c :=
    getElem_of_eq (a := hdr K ++ [10, 91]) (b := t ++ [93]) (by rw [← hsrc, hKe]; simp [hdr]) _ (by simp [hdr] <;> omega)
  have hd4 : src.drop (K.length + 3 + 1) = K ++ [93] :=
    drop_eq_of (a := hdr K ++ [10, 91]) (by rw [← hsrc]; simp [hdr]) _ (by simp [hdr] <;> omega)
  have hk2 := parseKey_enc (maxK := (mkCfg pf maxK maxD).maxKeyParts) h0 hps hmax (hrest93 [])
    (by rw [hK]; exact hd4)
  rw [hK, hk] at hk2
  have hws : skipChars src (K.length + 3 + 1) tomlWs = K.length + 3 + 1 := skipChars_at hg4 hcws
  have hcl : startsAt src (K.length + 3 + 1 + K.length) [93] = true :=
    startsAt_of_drop (r := []) (drop_eq_of (a := hdr K ++ [10, 91] ++ K) (by rw [← hsrc]; simp [hdr]) _
      (by simp [hdr] <;> omega))
  have hknil : k ≠ [] := by rw [← hk]; exact keyVal_ne p0 ps
  have hrule : (if src[K.length + 3 + 1]? == some 91 then
      createListRule (mkCfg pf maxK maxD) src (K.length + 3)
        { data := nestDict k [], flags := { tree := fsetAux EXPLICIT_NEST false k [], pending := [] } }
      else createDictRule (mkCfg pf maxK maxD) src (K.length + 3)
        { data := nestDict k [], flags := { tree := fsetAux EXPLICIT_NEST false k [], pending := [] } }) =
      .error (tde (S "Cannot declare " ++ keyRepr k ++ S " twice") src (2 * K.length + 4)) := by
    rw [if_neg (by simp [hg4, hc91])]
    rw [createDictRule_eq hws hk2 hknil hcl]
    simp only [flags_is _ _ hknil, isAux_fsetAux_self _ _ k [] hknil, Bool.true_or, ite_true]
    congr 2; omega
  exact mainLoop_hdr_err (f := f) hg3 (finalize_nil _ rfl) hrule

theorem getLast?_ne {k : Key} (h : k ≠ []) : k.getLast? = some (k.getLastD []) := by
  cases k with
  | nil => exact absurd rfl h
  | cons a t => rfl

theorem nestDict_split {k : Key} (h : k ≠ []) (d : Dict) :
    nestDict k d = nestDict k.dropLast [(k.getLastD [], .tbl d)] := by
  have e := List.dropLast_concat_getLast h
  have : k.getLast h = k.getLastD [] := by
    cases k with
    | nil => exact absurd rfl h
    | cons a t => rfl
  calc nestDict k d = nestDict (k.dropLast ++ [k.getLast h]) d := by rw [e]
    _ = nestDict k.dropLast [(k.getLastD [], .tbl d)] := by rw [nestDict_append, this]; rfl

theorem append_empty {k : Key} (h : k ≠ []) :
    appendNestToList k [] = .ok (nestDict k.dropLast [(k.getLastD [], .arr [.tbl []])]) := by
  simp only [appendNestToList, withNest_empty, getLast?_ne h, dget_nil, dset_nil, Except.map]

theorem append_again {k : Key} (h : k ≠ []) :
    appendNestToList k (nestDict k.dropLast [(k.getLastD [], .arr [.tbl []])]) =
      .ok (nestDict k.dropLast [(k.getLastD [], .arr [.tbl [], .tbl []])]) := by
  simp only [appendNestToList, withNest_nest, getLast?_ne h, dget_single, dset_single, Except.map]
  rfl

theorem append_onto_table {k : Key} (h : k ≠ []) :
    appendNestToList k (nestDict k []) = .error (.keyError "An object other than list found behind this key") := by
  rw [nestDict_split h]
  simp only [appendNestToList, withNest_nest, getLast?_ne h, dget_single, Except.map]

/-- The state after a first header `[[K]]` on an empty document. -/
theorem first_list {cfg : Cfg} {src : Str} {p0 : KPart} {ps : List KPart} {rest : Str}
    (h0 : p0.ok) (hps : ∀ p ∈ ps, p.ok) (hmax : ps.length + 1 ≤ cfg.maxKeyParts)
    (h : src = aot (keyEnc p0 ps) ++ rest) :
    (if src[0 + 1]? == some 91 then createListRule cfg src 0 { Out.init with flags := Flags.init }
      else createDictRule cfg src 0 { Out.init with flags := Flags.init }) =
      .ok ((keyEnc p0 ps).length + 4, keyVal p0 ps,
        { data := nestDict (keyVal p0 ps).dropLast [((keyVal p0 ps).getLastD [], .arr [.tbl []])],
          flags := { tree := fsetAux EXPLICIT_NEST false (keyVal p0 ps) [], pending := [] } }) := by
  obtain ⟨c, t, hKe, hcws, hc91⟩ := keyEnc_head (ps := ps) h0
  have h1 : src[0 + 1]? = some 91 := getElem_of_eq (a := [91]) (b := keyEnc p0 ps ++ 93 :: 93 :: rest) (by rw [h, aot]; simp) _ rfl
  rw [if_pos (by simp [h1])]
  have h2 : src[0 + 2]? = some c := getElem_of_eq (a := [91, 91]) (b := t ++ 93 :: 93 :: rest) (by rw [h, aot, hKe]; simp) _ rfl
  have hd2 : src.drop (0 + 2) = keyEnc p0 ps ++ (93 :: 93 :: rest) := drop_eq_of (a := [91, 91]) (by rw [h, aot]; simp) _ rfl
  have hk := parseKey_enc (maxK := cfg.maxKeyParts) h0 hps hmax (hrest93 (93 :: rest)) hd2
  have hws : skipChars src (0 + 2) tomlWs = 0 + 2 := skipChars_at h2 hcws
  have hd3 : src.drop ((keyEnc p0 ps).length + 2) = [93, 93] ++ rest :=
    drop_eq_of (a := 91 :: 91 :: keyEnc p0 ps) (by rw [h, aot]; simp) _ (by simp)
  have hcl : startsAt src (0 + 2 + (keyEnc p0 ps).length) [93, 93] = true := by
    rw [show 0 + 2 + (keyEnc p0 ps).length = (keyEnc p0 ps).length + 2 by omega]
    exact startsAt_of_drop hd3
  have hne := keyVal_ne p0 ps
  rw [createListRule_eq hws hk hne hcl]
  simp only [Out.init, Flags.init, flags_is _ _ hne, isAux_nil, Bool.false_eq_true, ite_false,
    append_empty hne, overwriteErr, Except.map, unsetAux_nil]
  simp; omega

theorem scen2 (pf : ParseFloat) (maxK maxD : Nat) (p0 : KPart) (ps : List KPart)
    (h0 : p0.ok) (hps : ∀ p ∈ ps, p.ok) (hmax : ps.length + 1 ≤ maxK) :
    loads pf maxK maxD (.str (aot (keyEnc p0 ps) ++ 10 :: aot (keyEnc p0 ps))) =
      .ok (nestDict (keyVal p0 ps).dropLast [((keyVal p0 ps).getLastD [], .arr [.tbl [], .tbl []])]) := by
  have hne := keyVal_ne p0 ps
  generalize hK : keyEnc p0 ps = K
  generalize hk : keyVal p0 ps = k
  rw [hk] at hne
  generalize hsrc : aot K ++ 10 :: aot K = src
  have h13 : 13 ∉ src := by
    rw [← hsrc, ← hK]; simp [aot, keyEnc_no13 h0 hps]
  rw [loads_eq pf maxK maxD src h13]
  obtain ⟨f, hf⟩ : ∃ f, src.length + 1 = f + 1 + 1 := ⟨src.length - 1, by rw [← hsrc]; simp [aot] <;> omega⟩
  rw [hf]
  have hr1 := first_list (cfg := mkCfg pf maxK maxD) (rest := 10 :: aot K) h0 hps hmax (by rw [hK, hsrc])
  rw [hK, hk] at hr1
  have hg0 : src[0]? = some 91 := by rw [← hsrc]; rfl
  have hnl : src[K.length + 4]? = some 10 :=
    getElem_of_eq (a := aot K) (b := aot K) (by rw [hsrc]) _ (by simp [aot] <;> omega)
  rw [mainLoop_hdr_ok hg0 (finalize_nil _ rfl) hr1 hnl]
  obtain ⟨c, t, hKe, hcws, hc91⟩ := keyEnc_head (ps := ps) h0
  rw [hK] at hKe
  have hg5 : src[K.length + 4 + 1]? = some 91 :=
    getElem_of_eq (a := aot K ++ [10]) (b := 91 :: K ++ [93, 93]) (by rw [← hsrc]; simp [aot]) _ (by simp [aot] <;> omega)
  have hg6 : src[K.length + 4 + 1 + 1]? = some 91 :=
    getElem_of_eq (a := aot K ++ [10, 91]) (b := K ++ [93, 93]) (by rw [← hsrc]; simp [aot]) _ (by simp [aot] <;> omega)
  have hg7 : src[K.length + 4 + 1 + 2]? = some c :=
    getElem_of_eq (a := aot K ++ [10, 91, 91]) (b := t ++ [93, 93]) (by rw [← hsrc, hKe]; simp [aot]) _ (by simp [aot] <;> omega)
  have hd7 : src.drop (K.length + 4 + 1 + 2) = K ++ [93, 93] :=
    drop_eq_of (a := aot K ++ [10, 91, 91]) (by rw [← hsrc]; simp [aot]) _ (by simp [aot] <;> omega)
  have hk2 := parseKey_enc (maxK := (mkCfg pf maxK maxD).maxKeyParts) h0 hps hmax (hrest93 [93]) (by rw [hK]; exact hd7)
  rw [hK, hk] at hk2
  have hws : skipChars src (K.length + 4 + 1 + 2) tomlWs = K.length + 4 + 1 + 2 := skipChars_at hg7 hcws
  have hcl : startsAt src (K.length + 4 + 1 + 2 + K.length) [93, 93] = true :=
    startsAt_of_drop (r := []) (drop_eq_of (a := aot K ++ [10, 91, 91] ++ K) (by rw [← hsrc]; simp [aot]) _
      (by simp [aot] <;> omega))
  have hend : src[K.length + 4 + 1 + 2 + K.length + 2]? = none := by
    rw [← hsrc]; simp [aot]; omega
  have hrule : (if src[K.length + 4 + 1 + 1]? == some 91 then
      createListRule (mkCfg pf maxK maxD) src (K.length + 4 + 1)
        { data := nestDict k.dropLast [(k.getLastD [], .arr [.tbl []])],
          flags := { tree := fsetAux EXPLICIT_NEST false k [], pending := [] } }
      else createDictRule (mkCfg pf maxK maxD) src (K.length + 4 + 1)
        { data := nestDict k.dropLast [(k.getLastD [], .arr [.tbl []])],
          flags := { tree := fsetAux EXPLICIT_NEST false k [], pending := [] } }) =
      .ok (K.length + 4 + 1 + 2 + K.length + 2, k,
        { data := nestDict k.dropLast [(k.getLastD [], .arr [.tbl [], .tbl []])],
          flags := { tree := fsetAux EXPLICIT_NEST false k (unsetAux k (fsetAux EXPLICIT_NEST false k [])),
                     pending := [] } }) := by
    rw [if_pos (by simp [hg6])]
    rw [createListRule_eq hws hk2 hne hcl]
    simp only [flags_is _ _ hne, isAux_fsetAux_nil_ne FROZEN EXPLICIT_NEST (by decide), Bool.false_eq_true,
      ite_false, append_again hne, overwriteErr, Except.map]
  exact mainLoop_hdr_end (f := f)
    (out := { data := nestDict k.dropLast [(k.getLastD [], .arr [.tbl []])],
              flags := { tree := fsetAux EXPLICIT_NEST false k [], pending := [] } })
    hg5 (finalize_nil _ rfl) hrule hend

theorem scen3 (pf : ParseFloat) (maxK maxD : Nat) (p0 : KPart) (ps : List KPart)
    (h0 : p0.ok) (hps : ∀ p ∈ ps, p.ok) (hmax : ps.length + 1 ≤ maxK) :
    loads pf maxK maxD (.str (hdr (keyEnc p0 ps) ++ 10 :: aot (keyEnc p0 ps))) =
      .error (tdeS "Cannot overwrite a value" (hdr (keyEnc p0 ps) ++ 10 :: aot (keyEnc p0 ps))
        (2 * (keyEnc p0 ps).length + 5)) := by
  have hne := keyVal_ne p0 ps
  generalize hK : keyEnc p0 ps = K
  generalize hk : keyVal p0 ps = k
  rw [hk] at hne
  generalize hsrc : hdr K ++ 10 :: aot K = src
  have h13 : 13 ∉ src := by
    rw [← hsrc, ← hK]; simp [hdr, aot, keyEnc_no13 h0 hps]
  rw [loads_eq pf maxK maxD src h13]
  obtain ⟨f, hf⟩ : ∃ f, src.length + 1 = f + 1 + 1 := ⟨src.length - 1, by rw [← hsrc]; simp [hdr, aot] <;> omega⟩
  rw [hf]
  have hr1 := first_dict (cfg := mkCfg pf maxK maxD) (rest := 10 :: aot K) h0 hps hmax (by rw [hK, hsrc])
  rw [hK, hk] at hr1
  have hg0 : src[0]? = some 91 := by rw [← hsrc]; rfl
  have hnl : src[K.length + 2]? = some 10 :=
    getElem_of_eq (a := hdr K) (b := aot K) (by rw [hsrc]) _ (by simp [hdr] <;> omega)
  rw [mainLoop_hdr_ok hg0 (finalize_nil _ rfl) hr1 hnl]
  obtain ⟨c, t, hKe, hcws, hc91⟩ := keyEnc_head (ps := ps) h0
  rw [hK] at hKe
  have hg3 : src[K.length + 2 + 1]? = some 91 :=
    getElem_of_eq (a := hdr K ++ [10]) (b := 91 :: K ++ [93, 93]) (by rw [← hsrc]; simp [hdr, aot]) _ (by simp [hdr] <;> omega)
  have hg4 : src[K.length + 2 + 1 + 1]? = some 91 :=
    getElem_of_eq (a := hdr K ++ [10, 91]) (b := K ++ [93, 93]) (by rw [← hsrc]; simp [hdr, aot]) _ (by simp [hdr] <;> omega)
  have hg5 : src[K.length + 2 + 1 + 2]? = some c :=
    getElem_of_eq (a := hdr K ++ [10, 91, 91]) (b := t ++ [93, 93]) (by rw [← hsrc, hKe]; simp [hdr, aot]) _ (by simp [hdr] <;> omega)
  have hd5 : src.drop (K.length + 2 + 1 + 2) = K ++ [93, 93] :=
    drop_eq_of (a := hdr K ++ [10, 91, 91]) (by rw [← hsrc]; simp [hdr, aot]) _ (by simp [hdr] <;> omega)
  have hk2 := parseKey_enc (maxK := (mkCfg pf maxK maxD).maxKeyParts) h0 hps hmax (hrest93 [93]) (by rw [hK]; exact hd5)
  rw [hK, hk] at hk2
  have hws : skipChars src (K.length + 2 + 1 + 2) tomlWs = K.length + 2 + 1 + 2 := skipChars_at hg5 hcws
  have hcl : startsAt src (K.length + 2 + 1 + 2 + K.length) [93, 93] = true :=
    startsAt_of_drop (r := []) (drop_eq_of (a := hdr K ++ [10, 91, 91] ++ K) (by rw [← hsrc]; simp [hdr, aot]) _
      (by simp [hdr] <;> omega))
  have hrule : (if src[K.length + 2 + 1 + 1]? == some 91 then
      createListRule (mkCfg pf maxK maxD) src (K.length + 2 + 1)
        { data := nestDict k [], flags := { tree := fsetAux EXPLICIT_NEST false k [], pending := [] } }
      else createDictRule (mkCfg pf maxK maxD) src (K.length + 2 + 1)
        { data := nestDict k [], flags := { tree := fsetAux EXPLICIT_NEST false k [], pending := [] } }) =
      .error (tdeS "Cannot overwrite a value" src (2 * K.length + 5)) := by
    rw [if_pos (by simp [hg4])]
    rw [createListRule_eq hws hk2 hne hcl]
    simp only [flags_is _ _ hne, isAux_fsetAux_nil_ne FROZEN EXPLICIT_NEST (by decide), Bool.false_eq_true,
      ite_false, append_onto_table hne, overwriteErr, Except.map]
    congr 2; omega
  exact mainLoop_hdr_err (f := f) hg3 (finalize_nil _ rfl) hrule

theorem scen4 (pf : ParseFloat) (maxK maxD : Nat) (p0 : KPart) (ps : List KPart)
    (h0 : p0.ok) (hps : ∀ p ∈ ps, p.ok) (hmax : ps.length + 1 ≤ maxK) :
    loads pf maxK maxD (.str (aot (keyEnc p0 ps) ++ 10 :: hdr (keyEnc p0 ps))) =
      .error (tde (S "Cannot declare " ++ keyRepr (keyVal p0 ps) ++ S " twice")
        (aot (keyEnc p0 ps) ++ 10 :: hdr (keyEnc p0 ps)) (2 * (keyEnc p0 ps).length + 6)) := by
  have hne := keyVal_ne p0 ps
  generalize hK : keyEnc p0 ps = K
  generalize hk : keyVal p0 ps = k
  rw [hk] at hne
  generalize hsrc : aot K ++ 10 :: hdr K = src
  have h13 : 13 ∉ src := by
    rw [← hsrc, ← hK]; simp [hdr, aot, keyEnc_no13 h0 hps]
  rw [loads_eq pf maxK maxD src h13]
  obtain ⟨f, hf⟩ : ∃ f, src.length + 1 = f + 1 + 1 := ⟨src.length - 1, by rw [← hsrc]; simp [hdr, aot] <;> omega⟩
  rw [hf]
  have hr1 := first_list (cfg := mkCfg pf maxK maxD) (rest := 10 :: hdr K) h0 hps hmax (by rw [hK, hsrc])
  rw [hK, hk] at hr1
  have hg0 : src[0]? = some 91 := by rw [← hsrc]; rfl
  have hnl : src[K.length + 4]? = some 10 :=
    getElem_of_eq (a := aot K) (b := hdr K) (by rw [hsrc]) _ (by simp [aot] <;> omega)
  rw [mainLoop_hdr_ok hg0 (finalize_nil _ rfl) hr1 hnl]
  obtain ⟨c, t, hKe, hcws, hc91⟩ := keyEnc_head (ps := ps) h0
  rw [hK] at hKe
  have hg5 : src[K.length + 4 + 1]? = some 91 :=
    getElem_of_eq (a := aot K ++ [10]) (b := K ++ [93]) (by rw [← hsrc]; simp [hdr, aot]) _ (by simp [aot] <;> omega)
  have hg6 : src[K.length + 4 + 1 + 1]? = some c :=
    getElem_of_eq (a := aot K ++ [10, 91]) (b := t ++ [93]) (by rw [← hsrc, hKe]; simp [hdr, aot]) _ (by simp [aot] <;> omega)
  have hd6 : src.drop (K.length + 4 + 1 + 1) = K ++ [93] :=
    drop_eq_of (a := aot K ++ [10, 91]) (by rw [← hsrc]; simp [hdr, aot]) _ (by simp [aot] <;> omega)
  have hk2 := parseKey_enc (maxK := (mkCfg pf maxK maxD).maxKeyParts) h0 hps hmax (hrest93 []) (by rw [hK]; exact hd6)
  rw [hK, hk] at hk2
  have hws : skipChars src (K.length + 4 + 1 + 1) tomlWs = K.length + 4 + 1 + 1 := skipChars_at hg6 hcws
  have hcl : startsAt src (K.length + 4 + 1 + 1 + K.length) [93] = true :=
    startsAt_of_drop (r := []) (drop_eq_of (a := aot K ++ [10, 91] ++ K) (by rw [← hsrc]; simp [hdr, aot]) _
      (by simp [aot] <;> omega))
  have hrule : (if src[K.length + 4 + 1 + 1]? == some 91 then
      createListRule (mkCfg pf maxK maxD) src (K.length + 4 + 1)
        { data := nestDict k.dropLast [(k.getLastD [], .arr [.tbl []])],
          flags := { tree := fsetAux EXPLICIT_NEST false k [], pending := [] } }
      else createDictRule (mkCfg pf maxK maxD) src (K.length + 4 + 1)
        { data := nestDict k.dropLast [(k.getLastD [], .arr [.tbl []])],
          flags := { tree := fsetAux EXPLICIT_NEST false k [], pending := [] } }) =
      .error (tde (S "Cannot declare " ++ keyRepr k ++ S " twice") src (2 * K.length + 6)) := by
    rw [if_neg (by simp [hg6, hc91])]
    rw [createDictRule_eq hws hk2 hne hcl]
    simp only [flags_is _ _ hne, isAux_fsetAux_self _ _ k [] hne, Bool.true_or, ite_true]
    congr 2; omega
  exact mainLoop_hdr_err (f := f) hg5 (finalize_nil _ rfl) hrule

theorem scen5 (pf : ParseFloat) (maxK maxD : Nat) (p0 : KPart) (ps : List KPart) (x : Str)
    (h0 : p0.ok) (hps : ∀ p ∈ ps, p.ok) (hmax : ps.length + 2 ≤ maxK) (hx : x ≠ [])
    (hxb : ∀ c ∈ x, bareKey c = true) :
    loads pf maxK maxD (.str (hdr (keyEnc p0 ps ++ 46 :: x) ++ 10 :: hdr (keyEnc p0 ps))) =
      .ok (nestDict (keyVal p0 ps) [(x, .tbl [])]) := by
  have hne := keyVal_ne p0 ps
  have hKx : keyEnc p0 (ps ++ [.bare x]) = keyEnc p0 ps ++ 46 :: x := by simp [keyEnc, KPart.enc]
  have hkx : keyVal p0 (ps ++ [.bare x]) = keyVal p0 ps ++ [x] := by simp [keyVal, KPart.val]
  have hpsx : ∀ p ∈ ps ++ [.bare x], p.ok := by
    intro p hp; simp only [List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · exact hps p hp
    · exact ⟨hx, hxb⟩
  generalize hK : keyEnc p0 ps = K
  generalize hk : keyVal p0 ps = k
  rw [hk] at hne
  rw [hK] at hKx; rw [hk] at hkx
  generalize hsrc : hdr (K ++ 46 :: x) ++ 10 :: hdr K = src
  have h13 : 13 ∉ src := by
    rw [← hsrc, ← hKx]; simp only [hdr, List.cons_append, List.mem_cons, List.mem_append, not_or]
    refine ⟨by decide, ⟨keyEnc_no13 h0 hpsx, by decide⟩, by decide, by decide, ?_, by decide⟩
    rw [← hK]; exact keyEnc_no13 h0 hps
  rw [loads_eq pf maxK maxD src h13]
  obtain ⟨f, hf⟩ : ∃ f, src.length + 1 = f + 1 + 1 := ⟨src.length - 1, by rw [← hsrc]; simp [hdr] <;> omega⟩
  rw [hf]
  have hr1 := first_dict (cfg := mkCfg pf maxK maxD) (ps := ps ++ [.bare x]) (rest := 10 :: hdr K) h0 hpsx
    (show (ps ++ [KPart.bare x]).length + 1 ≤ maxK by simp; omega) (by rw [hKx, hsrc])
  rw [hKx, hkx] at hr1
  have hg0 : src[0]? = some 91 := by rw [← hsrc]; rfl
  have hnl : src[(K ++ 46 :: x).length + 2]? = some 10 :=
    getElem_of_eq (a := hdr (K ++ 46 :: x)) (b := hdr K) (by rw [hsrc]) _ (by simp [hdr] <;> omega)
  rw [mainLoop_hdr_ok hg0 (finalize_nil _ rfl) hr1 hnl]
  obtain ⟨c, t, hKe, hcws, hc91⟩ := keyEnc_head (ps := ps) h0
  rw [hK] at hKe
  generalize hL : (K ++ 46 :: x).length + 2 + 1 = L
  have hg3 : src[L]? = some 91 :=
    getElem_of_eq (a := hdr (K ++ 46 :: x) ++ [10]) (b := K ++ [93]) (by rw [← hsrc]; simp [hdr]) _ (by rw [← hL]; simp [hdr] <;> omega)
  have hg4 : src[L + 1]? = some c :=
    getElem_of_eq (a := hdr (K ++ 46 :: x) ++ [10, 91]) (b := t ++ [93]) (by rw [← hsrc, hKe]; simp [hdr]) _ (by rw [← hL]; simp [hdr] <;> omega)
  have hd4 : src.drop (L + 1) = K ++ [93] :=
    drop_eq_of (a := hdr (K ++ 46 :: x) ++ [10, 91]) (by rw [← hsrc]; simp [hdr]) _ (by rw [← hL]; simp [hdr] <;> omega)
  have hk2 := parseKey_enc (maxK := (mkCfg pf maxK maxD).maxKeyParts) h0 hps
    (show ps.length + 1 ≤ maxK by omega) (hrest93 [])
    (by rw [hK]; exact hd4)
  rw [hK, hk] at hk2
  have hws : skipChars src (L + 1) tomlWs = L + 1 := skipChars_at hg4 hcws
  have hcl : startsAt src (L + 1 + K.length) [93] = true :=
    startsAt_of_drop (r := []) (drop_eq_of (a := hdr (K ++ 46 :: x) ++ [10, 91] ++ K) (by rw [← hsrc]; simp [hdr]) _
      (by rw [← hL]; simp [hdr] <;> omega))
  have hend : src[L + 1 + K.length + 1]? = none := by
    rw [← hsrc, ← hL]; simp [hdr]; omega
  have hrule : (if src[L + 1]? == some 91 then
      createListRule (mkCfg pf maxK maxD) src L
        { data := nestDict (k ++ [x]) [], flags := { tree := fsetAux EXPLICIT_NEST false (k ++ [x]) [], pending := [] } }
      else createDictRule (mkCfg pf maxK maxD) src L
        { data := nestDict (k ++ [x]) [], flags := { tree := fsetAux EXPLICIT_NEST false (k ++ [x]) [], pending := [] } }) =
      .ok (L + 1 + K.length + 1, k,
        { data := nestDict k [(x, .tbl [])],
          flags := { tree := fsetAux EXPLICIT_NEST false k (fsetAux EXPLICIT_NEST false (k ++ [x]) []),
                     pending := [] } }) := by
    rw [if_neg (by simp [hg4, hc91])]
    rw [createDictRule_eq hws hk2 hne hcl]
    simp only [flags_is _ _ hne, isAux_fsetAux_nil_prefix, Bool.or_false, Bool.false_eq_true, ite_false,
      getOrCreateNest, nestDict_append, nestDict, withNest_nest, overwriteErr, Except.map]
  exact mainLoop_hdr_end (f := f)
    (out := { data := nestDict (k ++ [x]) [],
              flags := { tree := fsetAux EXPLICIT_NEST false (k ++ [x]) [], pending := [] } })
    hg3 (finalize_nil _ rfl) hrule hend

/-! ## Sub-tables of array-of-tables elements -/

/-- The flags tree along one key path: empty nodes, then `n` at the end. -/
def chainT : Key → FNode → List (Str × FNode)
  | [], _ => []
  | [s], n => [(s, n)]
  | s :: ks, n => [(s, .mk [] [] (chainT ks n))]

theorem chainT_set (g : Nat) : ∀ (k : Key), k ≠ [] → fsetAux g false k [] = chainT k (.mk [g] [] [])
  | [], h => absurd rfl h
  | [s], _ => by simp [fsetAux, chainT, dget_nil, FNode.empty, addFlag, dset_nil]
  | s :: s2 :: ks, _ => by
    simp only [fsetAux, dget_nil, Option.getD_none, FNode.empty, dset_nil, chainT]
    rw [chainT_set g (s2 :: ks) (by simp)]

theorem chainT_ext (g : Nat) (x : Str) (fl : List Nat) (ns : List (Str × FNode)) :
    ∀ (k : Key), k ≠ [] → fsetAux g false (k ++ [x]) (chainT k (.mk fl [] ns)) =
      chainT k (.mk fl [] (fsetAux g false [x] ns))
  | [], h => absurd rfl h
  | [s], _ => by
    show fsetAux g false [s, x] [(s, .mk fl [] ns)] = [(s, .mk fl [] (fsetAux g false [x] ns))]
    simp only [fsetAux, dget_single, Option.getD_some, dset_single]
  | s :: s2 :: ks, _ => by
    have ih := chainT_ext g x fl ns (s2 :: ks) (by simp)
    generalize hX : fsetAux g false [x] ns = X at ih ⊢
    show fsetAux g false (s :: (s2 :: ks ++ [x])) [(s, .mk [] [] (chainT (s2 :: ks) (.mk fl [] ns)))] =
      [(s, .mk [] [] (chainT (s2 :: ks) (.mk fl [] X)))]
    have h2 : s2 :: ks ++ [x] = s2 :: (ks ++ [x]) := rfl
    rw [h2]
    simp only [fsetAux, dget_single, Option.getD_some, dset_single]
    rw [← h2, ih]

theorem chainT_reset (g : Nat) (n : FNode) : ∀ (k : Key), k ≠ [] →
    fsetAux g false k (unsetAux k (chainT k n)) = chainT k (.mk [g] [] [])
  | [], h => absurd rfl h
  | [s], _ => by simp [chainT, unsetAux, dpop, fsetAux, dget_nil, FNode.empty, addFlag, dset_nil]
  | s :: s2 :: ks, _ => by
    cases n with
    | mk f r ns =>
      show fsetAux g false (s :: s2 :: ks) (unsetAux (s :: s2 :: ks) [(s, .mk [] [] (chainT (s2 :: ks) (.mk f r ns)))]) = _
      simp only [unsetAux, dget_single, dset_single, fsetAux, Option.getD_some]
      rw [chainT_reset g (.mk f r ns) (s2 :: ks) (by simp)]
      rfl

theorem chainT_query_ext (flag : Nat) (x : Str) (fl : List Nat) : ∀ (k : Key), k ≠ [] →
    isAux flag (k ++ [x]) (chainT k (.mk fl [] [])) = false
  | [], h => absurd rfl h
  | [s], _ => by
    show isAux flag [s, x] [(s, .mk fl [] [])] = false
    simp [isAux, dget_single, FNode.rflags, FNode.nested, dget_nil]
  | s :: s2 :: ks, _ => by
    show isAux flag (s :: (s2 :: ks ++ [x])) [(s, .mk [] [] (chainT (s2 :: ks) (.mk fl [] [])))] = false
    have h2 : s2 :: ks ++ [x] = s2 :: (ks ++ [x]) := rfl
    rw [h2]
    simp only [isAux, dget_single, FNode.rflags, FNode.nested, List.contains_nil, Bool.false_eq_true, ite_false]
    rw [← h2]; exact chainT_query_ext flag x fl (s2 :: ks) (by simp)

theorem chainT_query (flag : Nat) (fl : List Nat) (ns : List (Str × FNode)) (hf : flag ∉ fl) :
    ∀ (k : Key), k ≠ [] → isAux flag k (chainT k (.mk fl [] ns)) = false
  | [], h => absurd rfl h
  | [s], _ => by simp [chainT, isAux, dget_single, FNode.flags, FNode.rflags, hf]
  | s :: s2 :: ks, _ => by
    show isAux flag (s :: s2 :: ks) [(s, .mk [] [] (chainT (s2 :: ks) (.mk fl [] ns)))] = false
    simp only [isAux, dget_single, FNode.rflags, FNode.nested, List.contains_nil, Bool.false_eq_true, ite_false]
    exact chainT_query flag fl ns hf (s2 :: ks) (by simp)

theorem withNest_nest_append {α : Type} (acc : Bool) (f : Dict → Py (Dict × α)) :
    ∀ (k1 k2 : Key) (D : Dict), withNest acc f (k1 ++ k2) (nestDict k1 D) =
      (withNest acc f k2 D).map (fun r => (nestDict k1 r.1, r.2))
  | [], k2, D => by simp [nestDict]; cases withNest acc f k2 D <;> rfl
  | k :: ks, k2, D => by
    simp only [List.cons_append, nestDict, withNest, dget_single, Option.isSome_some, ite_true]
    rw [withNest_nest_append acc f ks k2 D]
    cases withNest acc f k2 D <;> simp [Except.map, bind, Except.bind, dset_single, pure, Except.pure]

theorem withNest_aot {α : Type} (f : Dict → Py (Dict × α)) (l x : Str) (xs : List TVal) (d : Dict) :
    withNest true f [l, x] [(l, .arr (xs ++ [.tbl d]))] =
      (withNest true f [x] d).map (fun r => ([(l, .arr (xs ++ [.tbl r.1]))], r.2)) := by
  simp only [withNest, dget_single, Option.isSome_some, ite_true, List.getLast?_concat, List.dropLast_concat]
  cases withNest true f [x] d <;> simp [Except.map, bind, Except.bind, dset_single, pure, Except.pure]

theorem key_split {k : Key} (h : k ≠ []) (x : Str) : k ++ [x] = k.dropLast ++ [k.getLastD [], x] := by
  have e := List.dropLast_concat_getLast h
  have : k.getLast h = k.getLastD [] := by
    cases k with
    | nil => exact absurd rfl h
    | cons a t => rfl
  conv => lhs; rw [← e]
  rw [this]; simp

theorem nest_aot {k : Key} (h : k ≠ []) (x : Str) (xs : List TVal) :
    getOrCreateNest true (k ++ [x]) (nestDict k.dropLast [(k.getLastD [], .arr (xs ++ [.tbl []]))]) =
      .ok (nestDict k.dropLast [(k.getLastD [], .arr (xs ++ [.tbl [(x, .tbl [])]]))]) := by
  unfold getOrCreateNest
  rw [key_split h x, withNest_nest_append, withNest_aot, withNest_empty]
  simp [Except.map, nestDict]

theorem append_aot {k : Key} (h : k ≠ []) (ys : List TVal) :
    appendNestToList k (nestDict k.dropLast [(k.getLastD [], .arr ys)]) =
      .ok (nestDict k.dropLast [(k.getLastD [], .arr (ys ++ [.tbl []]))]) := by
  simp only [appendNestToList, withNest_nest, getLast?_ne h, dget_single, dset_single, Except.map]

theorem dict_at {cfg : Cfg} {src : Str} {pos : Nat} {p0 : KPart} {ps : List KPart} {rest : Str} {out : Out}
    (h0 : p0.ok) (hps : ∀ p ∈ ps, p.ok) (hmax : ps.length + 1 ≤ cfg.maxKeyParts)
    (h : src.drop pos = hdr (keyEnc p0 ps) ++ rest) :
    (if src[pos + 1]? == some 91 then createListRule cfg src pos out else createDictRule cfg src pos out) =
      if out.flags.is_ (keyVal p0 ps) EXPLICIT_NEST || out.flags.is_ (keyVal p0 ps) FROZEN then
        .error (tde (S "Cannot declare " ++ keyRepr (keyVal p0 ps) ++ S " twice") src (pos + 1 + (keyEnc p0 ps).length))
      else (overwriteErr src (pos + 1 + (keyEnc p0 ps).length) (getOrCreateNest true (keyVal p0 ps) out.data)).map
        (fun data => (pos + 1 + (keyEnc p0 ps).length + 1, keyVal p0 ps,
          { data, flags := { out.flags with tree := fsetAux EXPLICIT_NEST false (keyVal p0 ps) out.flags.tree } })) := by
  obtain ⟨c, t, hKe, hcws, hc91⟩ := keyEnc_head (ps := ps) h0
  have h' : src.drop pos = 91 :: (keyEnc p0 ps ++ 93 :: rest) := by rw [h, hdr]; simp
  have hd1 : src.drop (pos + 1) = keyEnc p0 ps ++ (93 :: rest) := drop_succ_of_drop h'
  have h1 : src[pos + 1]? = some c := getElem?_of_drop (r := t ++ 93 :: rest) (by rw [hd1, hKe]; simp)
  rw [if_neg (by simp [h1, hc91])]
  have hk := parseKey_enc (maxK := cfg.maxKeyParts) h0 hps hmax (hrest93 rest) hd1
  have hws : skipChars src (pos + 1) tomlWs = pos + 1 := skipChars_at h1 hcws
  have hcl : startsAt src (pos + 1 + (keyEnc p0 ps).length) [93] = true :=
    startsAt_of_drop (r := rest) (by simpa using drop_add_of_drop hd1)
  exact createDictRule_eq hws hk (keyVal_ne p0 ps) hcl

theorem list_at {cfg : Cfg} {src : Str} {pos : Nat} {p0 : KPart} {ps : List KPart} {rest : Str} {out : Out}
    (h0 : p0.ok) (hps : ∀ p ∈ ps, p.ok) (hmax : ps.length + 1 ≤ cfg.maxKeyParts)
    (h : src.drop pos = aot (keyEnc p0 ps) ++ rest) :
    (if src[pos + 1]? == some 91 then createListRule cfg src pos out else createDictRule cfg src pos out) =
      if out.flags.is_ (keyVal p0 ps) FROZEN then
        .error (tde (S "Cannot mutate immutable namespace " ++ keyRepr (keyVal p0 ps)) src (pos + 2 + (keyEnc p0 ps).length))
      else (overwriteErr src (pos + 2 + (keyEnc p0 ps).length) (appendNestToList (keyVal p0 ps) out.data)).map
        (fun data => (pos + 2 + (keyEnc p0 ps).length + 2, keyVal p0 ps,
          { data, flags := { out.flags with
            tree := fsetAux EXPLICIT_NEST false (keyVal p0 ps) (unsetAux (keyVal p0 ps) out.flags.tree) } })) := by
  obtain ⟨c, t, hKe, hcws, hc91⟩ := keyEnc_head (ps := ps) h0
  have h' : src.drop pos = 91 :: 91 :: (keyEnc p0 ps ++ 93 :: 93 :: rest) := by rw [h, aot]; simp
  have h1 : src[pos + 1]? = some 91 := getElem?_of_drop (drop_succ_of_drop h')
  rw [if_pos (by simp [h1])]
  have hd2 : src.drop (pos + 2) = keyEnc p0 ps ++ (93 :: 93 :: rest) := by
    simpa using drop_add_of_drop (a := [91, 91]) (by simpa using h')
  have h2 : src[pos + 2]? = some c := getElem?_of_drop (r := t ++ 93 :: 93 :: rest) (by rw [hd2, hKe]; simp)
  have hk := parseKey_enc (maxK := cfg.maxKeyParts) h0 hps hmax (hrest93 (93 :: rest)) hd2
  have hws : skipChars src (pos + 2) tomlWs = pos + 2 := skipChars_at h2 hcws
  have hcl : startsAt src (pos + 2 + (keyEnc p0 ps).length) [93, 93] = true :=
    startsAt_of_drop (r := rest) (by simpa using drop_add_of_drop hd2)
  exact createListRule_eq hws hk (keyVal_ne p0 ps) hcl

/-- `[[K]]`, `[K.x]`, `[[K]]`, `[K.x]`: each element of the array of tables gets its own
sub-table (the flags of the old element are dropped when the new one starts). -/
theorem scen6 (pf : ParseFloat) (maxK maxD : Nat) (p0 : KPart) (ps : List KPart) (x : Str)
    (h0 : p0.ok) (hps : ∀ p ∈ ps, p.ok) (hmax : ps.length + 2 ≤ maxK) (hx : x ≠ [])
    (hxb : ∀ c ∈ x, bareKey c = true) :
    loads pf maxK maxD (.str (aot (keyEnc p0 ps) ++ 10 :: hdr (keyEnc p0 ps ++ 46 :: x) ++ 10 ::
        aot (keyEnc p0 ps) ++ 10 :: hdr (keyEnc p0 ps ++ 46 :: x))) =
      .ok (nestDict (keyVal p0 ps).dropLast
        [((keyVal p0 ps).getLastD [], .arr [.tbl [(x, .tbl [])], .tbl [(x, .tbl [])]])]) := by
  have hne := keyVal_ne p0 ps
  have hKx : keyEnc p0 (ps ++ [.bare x]) = keyEnc p0 ps ++ 46 :: x := by simp [keyEnc, KPart.enc]
  have hkx : keyVal p0 (ps ++ [.bare x]) = keyVal p0 ps ++ [x] := by simp [keyVal, KPart.val]
  have hpsx : ∀ p ∈ ps ++ [.bare x], p.ok := by
    intro p hp; simp only [List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · exact hps p hp
    · exact ⟨hx, hxb⟩
  have hmx : (ps ++ [KPart.bare x]).length + 1 ≤ (mkCfg pf maxK maxD).maxKeyParts := by
    show (ps ++ [KPart.bare x]).length + 1 ≤ maxK; simp; omega
  have hm1 : ps.length + 1 ≤ (mkCfg pf maxK maxD).maxKeyParts := by show ps.length + 1 ≤ maxK; omega
  have h13x := keyEnc_no13 h0 hpsx
  rw [hKx] at h13x
  generalize hK : keyEnc p0 ps = K at hKx h13x
  generalize hk : keyVal p0 ps = k at hne hkx
  have h13K : 13 ∉ K := by rw [← hK]; exact keyEnc_no13 h0 hps
  generalize hsrc : aot K ++ 10 :: hdr (K ++ 46 :: x) ++ 10 :: aot K ++ 10 :: hdr (K ++ 46 :: x) = src
  have h13 : 13 ∉ src := by
    rw [← hsrc]; simp only [aot, hdr, List.cons_append, List.mem_cons, List.mem_append, not_or]
    simp_all
  rw [loads_eq pf maxK maxD src h13]
  obtain ⟨f, hf⟩ : ∃ f, src.length + 1 = f + 1 + 1 + 1 + 1 :=
    ⟨src.length - 3, by rw [← hsrc]; simp [aot, hdr] <;> omega⟩
  rw [hf]
  -- step 1: `[[K]]`
  have hr1 := first_list (cfg := mkCfg pf maxK maxD) (src := src) (rest := 10 :: hdr (K ++ 46 :: x) ++ 10 :: aot K ++ 10 ::
    hdr (K ++ 46 :: x)) h0 hps hm1 (by rw [hK, ← hsrc]; simp)
  rw [hK, hk] at hr1
  have hg0 : src[0]? = some 91 := by rw [← hsrc]; rfl
  have hn1 : src[K.length + 4]? = some 10 :=
    getElem_of_eq (a := aot K) (b := hdr (K ++ 46 :: x) ++ 10 :: aot K ++ 10 :: hdr (K ++ 46 :: x))
      (by rw [← hsrc]; simp) _ (by simp [aot] <;> omega)
  rw [mainLoop_hdr_ok hg0 (finalize_nil _ rfl) hr1 hn1]
  -- step 2: `[K.x]`
  have hd2 : src.drop (K.length + 4 + 1) = hdr (K ++ 46 :: x) ++ (10 :: aot K ++ 10 :: hdr (K ++ 46 :: x)) :=
    drop_eq_of (a := aot K ++ [10]) (by rw [← hsrc]; simp) _ (by simp [aot] <;> omega)
  have hr2 := dict_at (cfg := mkCfg pf maxK maxD)
    (out := { data := nestDict k.dropLast [(k.getLastD [], .arr [.tbl []])],
              flags := { tree := fsetAux EXPLICIT_NEST false k [], pending := [] } })
    h0 hpsx hmx (by rw [hKx]; exact hd2)
  rw [hKx, hkx] at hr2
  have hq1 : ∀ fl, isAux fl (k ++ [x]) (fsetAux EXPLICIT_NEST false k []) = false := by
    intro fl; rw [chainT_set _ k hne]; exact chainT_query_ext fl x _ k hne
  have hna := nest_aot hne x []
  simp only [List.nil_append] at hna
  simp only [flags_is _ _ (by simp : k ++ [x] ≠ []), hq1, Bool.or_false, Bool.false_eq_true, ite_false,
    hna, overwriteErr, Except.map] at hr2
  have hg2 : src[K.length + 4 + 1]? = some 91 := getElem?_of_drop (by rw [hd2]; rfl)
  have hn2 : src[K.length + 4 + 1 + 1 + (K ++ 46 :: x).length + 1]? = some 10 :=
    getElem_of_eq (a := aot K ++ [10] ++ hdr (K ++ 46 :: x)) (b := aot K ++ 10 :: hdr (K ++ 46 :: x))
      (by rw [← hsrc]; simp) _ (by simp [aot, hdr] <;> omega)
  rw [mainLoop_hdr_ok
    (out := { data := nestDict k.dropLast [(k.getLastD [], .arr [.tbl []])],
              flags := { tree := fsetAux EXPLICIT_NEST false k [], pending := [] } })
    hg2 (finalize_nil _ rfl) hr2 hn2]
  -- step 3: `[[K]]`
  generalize hE2 : K.length + 4 + 1 + 1 + (K ++ 46 :: x).length + 1 + 1 = E2
  have hd3 : src.drop E2 = aot K ++ (10 :: hdr (K ++ 46 :: x)) :=
    drop_eq_of (a := aot K ++ [10] ++ hdr (K ++ 46 :: x) ++ [10]) (by rw [← hsrc]; simp) _
      (by rw [← hE2]; simp [aot, hdr] <;> omega)
  have hr3 := list_at (cfg := mkCfg pf maxK maxD)
    (out := { data := nestDict k.dropLast [(k.getLastD [], .arr [.tbl [(x, .tbl [])]])],
              flags := { tree := fsetAux EXPLICIT_NEST false (k ++ [x]) (fsetAux EXPLICIT_NEST false k []),
                         pending := [] } })
    h0 hps hm1 (by rw [hK]; exact hd3)
  rw [hK, hk] at hr3
  have hq2 : isAux FROZEN k (fsetAux EXPLICIT_NEST false (k ++ [x]) (fsetAux EXPLICIT_NEST false k [])) = false := by
    rw [chainT_set _ k hne, chainT_ext _ x _ _ k hne]; exact chainT_query FROZEN _ _ (by decide) k hne
  have hreset : fsetAux EXPLICIT_NEST false k (unsetAux k
      (fsetAux EXPLICIT_NEST false (k ++ [x]) (fsetAux EXPLICIT_NEST false k []))) = fsetAux EXPLICIT_NEST false k [] := by
    rw [chainT_set _ k hne, chainT_ext _ x _ _ k hne, chainT_reset _ _ k hne]
  simp only [flags_is _ _ hne, hq2, Bool.false_eq_true, ite_false, append_aot hne, overwriteErr, Except.map,
    hreset] at hr3
  have hg3 : src[E2]? = some 91 := getElem?_of_drop (by rw [hd3]; rfl)
  have hn3 : src[E2 + 2 + K.length + 2]? = some 10 :=
    getElem_of_eq (a := aot K ++ [10] ++ hdr (K ++ 46 :: x) ++ [10] ++ aot K) (b := hdr (K ++ 46 :: x))
      (by rw [← hsrc]; simp) _
      (by rw [← hE2]; simp [aot, hdr] <;> omega)
  rw [mainLoop_hdr_ok
    (out := { data := nestDict k.dropLast [(k.getLastD [], .arr [.tbl [(x, .tbl [])]])],
              flags := { tree := fsetAux EXPLICIT_NEST false (k ++ [x]) (fsetAux EXPLICIT_NEST false k []),
                         pending := [] } })
    hg3 (finalize_nil _ rfl) hr3 hn3]
  -- step 4: `[K.x]`
  generalize hE3 : E2 + 2 + K.length + 2 + 1 = E3
  have hd4 : src.drop E3 = hdr (K ++ 46 :: x) ++ [] :=
    drop_eq_of (a := aot K ++ [10] ++ hdr (K ++ 46 :: x) ++ [10] ++ aot K ++ [10]) (by rw [← hsrc]; simp) _
      (by rw [← hE3, ← hE2]; simp [aot, hdr] <;> omega)
  have hr4 := dict_at (cfg := mkCfg pf maxK maxD)
    (out := { data := nestDict k.dropLast [(k.getLastD [], .arr [.tbl [(x, .tbl [])], .tbl []])],
              flags := { tree := fsetAux EXPLICIT_NEST false k [], pending := [] } })
    h0 hpsx hmx (by rw [hKx]; exact hd4)
  rw [hKx, hkx] at hr4
  simp only [flags_is _ _ (by simp : k ++ [x] ≠ []), hq1, Bool.or_false, Bool.false_eq_true, ite_false,
    show [TVal.tbl [(x, .tbl [])], .tbl []] = [TVal.tbl [(x, .tbl [])]] ++ [.tbl []] from rfl,
    nest_aot hne x [TVal.tbl [(x, .tbl [])]], overwriteErr, Except.map] at hr4
  have hg4 : src[E3]? = some 91 := getElem?_of_drop (by rw [hd4]; rfl)
  have hend : src[E3 + 1 + (K ++ 46 :: x).length + 1]? = none := by
    rw [← hE3, ← hE2, ← hsrc]; simp [aot, hdr]; omega
  exact mainLoop_hdr_end (f := f)
    (out := { data := nestDict k.dropLast [(k.getLastD [], .arr [.tbl [(x, .tbl [])], .tbl []])],
              flags := { tree := fsetAux EXPLICIT_NEST false k [], pending := [] } })
    hg4 (finalize_nil _ rfl) hr4 hend

theorem tableRules_proven : TableRules := by
  intro pf maxK maxD p0 ps x h0 hps hmax hx hxb
  exact ⟨scen1 pf maxK maxD p0 ps h0 hps (by omega), scen2 pf maxK maxD p0 ps h0 hps (by omega),
    scen3 pf maxK maxD p0 ps h0 hps (by omega), scen4 pf maxK maxD p0 ps h0 hps (by omega),
    scen5 pf maxK maxD p0 ps x h0 hps hmax hx hxb, scen6 pf maxK maxD p0 ps x h0 hps hmax hx hxb⟩

end PyLean.TextLibs.Toml
