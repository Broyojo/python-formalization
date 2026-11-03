import PyLean.TextLibs.TomlArr

/-!
Documents of `key = value` lines: `loads` through `key_value_rule` reads back every such
document with distinct one-part keys and values built from strings, booleans, arrays and inline
tables.
-/

namespace PyLean.TextLibs.Toml

/-- A line `k w1 = w2 v`. -/
structure Line where
  k : KPart
  w1 : Str
  w2 : Str
  v : SV

def Line.enc (l : Line) : Str := l.k.enc ++ l.w1 ++ 61 :: l.w2 ++ l.v.enc

def Line.ok (l : Line) : Prop := l.k.ok ∧ allWs l.w1 ∧ allWs l.w2 ∧ l.v.ok

/-- Lines joined by newlines. -/
def docEnc : List Line → Str
  | [] => []
  | [l] => l.enc
  | l :: ls => l.enc ++ 10 :: docEnc ls

/-- The state after `key_value_rule` stores a one-part key at the root. -/
def kvOut (out : Out) (kv : Str) (val : TVal) : Out :=
  { data := out.data ++ [(kv, val)],
    flags := if val.isDictOrList then { out.flags with tree := fsetAux FROZEN true [kv] out.flags.tree }
             else out.flags }

theorem keyInitial_head (k : KPart) (hk : k.ok) :
    ∃ c t, k.enc = c :: t ∧ keyInitial c = true ∧ tomlWs c = false ∧ c ≠ 10 := by
  obtain ⟨c, t, he, hws, -⟩ := KPart.head_not_ws hk
  refine ⟨c, t, he, ?_, hws, ?_⟩
  · cases k with
    | bare s =>
      have := hk.2 c (by simp [KPart.enc] at he; rw [he]; simp)
      simp [keyInitial, this]
    | lit s =>
      have : 39 = c := by simp [KPart.enc] at he; exact he.1
      subst this; decide
    | basic ps =>
      have : 34 = c := by simp [KPart.enc] at he; exact he.1
      subst this; decide
  · cases k with
    | bare s =>
      have := hk.2 c (by simp [KPart.enc] at he; rw [he]; simp)
      intro e; subst e; exact absurd this (by decide)
    | lit s =>
      have : 39 = c := by simp [KPart.enc] at he; exact he.1
      omega
    | basic ps =>
      have : 34 = c := by simp [KPart.enc] at he; exact he.1
      omega

/-- `key_value_rule` on a one-part key at the document root. -/
theorem kvr_one {cfg : Cfg} {src : Str} {pos p : Nat} {out : Out} {kv : Str} {val : TVal}
    (hpkv : parseKeyValuePair cfg src (vFuel src) pos = .ok (p, [kv], val))
    (hfresh : dget out.data kv = none) :
    keyValueRule cfg src pos out [] = .ok (p, kvOut out kv val) := by
  simp only [keyValueRule, hpkv, bind, Except.bind]
  simp only [List.length_singleton, Nat.sub_self, List.range_zero, List.map_nil, contKeysLoop,
    List.append_nil, Flags.is_, List.isEmpty_nil, ite_true, Bool.false_eq_true, ite_false, withNest,
    show ([kv] : Key).dropLast = [] from rfl, show ([kv] : Key).getLastD [] = kv from rfl, hfresh,
    Option.isSome_none, overwriteErr, dset_absent _ _ _ hfresh]
  unfold kvOut
  cases val.isDictOrList <;> simp [Flags.set, pure, Except.pure]

theorem mainLoop_kv {cfg : Cfg} {src : Str} {f pos p c : Nat} {out out' : Out}
    (hc : src[pos]? = some c) (hkey : keyInitial c = true) (hws : tomlWs c = false) (h10 : c ≠ 10)
    (hrule : keyValueRule cfg src pos out [] = .ok (p, out')) :
    mainLoop cfg src (f + 1) pos out [] =
      if src[p]? = none then .ok out'.data
      else if src[p]? = some 10 then mainLoop cfg src f (p + 1) out' []
      else mainLoop cfg src (f + 1) pos out [] := by
  have hs0 : skipChars src pos tomlWs = pos := skipChars_at hc hws
  have hb : (c == 10) = false := by simp [h10]
  rcases hp : src[p]? with _ | d
  · have hs1 : skipChars src p tomlWs = p := skipChars_stop (fun x hx => by rw [List.head?_drop, hp] at hx; cases hx)
    have hcm : skipComment src p = .ok p := by simp [skipComment, hp]
    simp only [mainLoop, hs0, hc, hb, Bool.false_eq_true, ite_false, hkey, ite_true, hrule, bind, Except.bind,
      pure, Except.pure, hs1, hcm, hp]
    try simp
  · by_cases hd : d = 10
    · subst hd
      have hs1 : skipChars src p tomlWs = p := skipChars_at hp (by decide)
      have hcm : skipComment src p = .ok p := by simp [skipComment, hp]
      simp only [mainLoop, hs0, hc, hb, Bool.false_eq_true, ite_false, hkey, ite_true, hrule, bind, Except.bind,
        pure, Except.pure, hs1, hcm, hp, show ((10 : Nat) != 10) = false from rfl]
      try simp
    · simp [hd]

theorem docEnc_cons (l : Line) (ls : List Line) (h : ls ≠ []) : docEnc (l :: ls) = l.enc ++ 10 :: docEnc ls := by
  cases ls with
  | nil => exact absurd rfl h
  | cons _ _ => rfl

/-- One line: `key_value_rule` stores it, and the loop goes on at the position after it. -/
theorem line_step (pf : ParseFloat) (maxK maxD : Nat) (src : Str) (l : Line) (pos f : Nat) (out : Out)
    (rest : Str) (hok : l.ok) (hfr : dget out.data l.k.val = none) (hd : src.drop pos = l.enc ++ rest)
    (hrest34 : ∀ c, rest.head? = some c → c ≠ 34) :
    mainLoop (mkCfg pf maxK maxD) src (f + 1) pos out [] =
      if src[pos + l.enc.length]? = none then .ok (kvOut out l.k.val l.v.val).data
      else if src[pos + l.enc.length]? = some 10 then
        mainLoop (mkCfg pf maxK maxD) src f (pos + l.enc.length + 1) (kvOut out l.k.val l.v.val) []
      else mainLoop (mkCfg pf maxK maxD) src (f + 1) pos out [] := by
  obtain ⟨hk, hw1, hw2, hv⟩ := hok
  have hvpos : src.drop (pos + l.k.enc.length + l.w1.length + 1 + l.w2.length) = l.v.enc ++ rest := by
    have := drop_add_of_drop (a := l.k.enc ++ l.w1 ++ 61 :: l.w2) (by simpa [Line.enc] using hd)
    have e : pos + (l.k.enc ++ l.w1 ++ 61 :: l.w2).length = pos + l.k.enc.length + l.w1.length + 1 + l.w2.length := by
      simp; omega
    rw [e] at this; exact this
  have hvlen : l.v.enc.length ≤ src.length := by
    have := congrArg List.length hd; simp [Line.enc] at this; omega
  have hneed := SV.need_le l.v
  have hvp := SV.parse (mkCfg pf maxK maxD) src l.v _ (vFuel src - 1) rest hv hrest34 hvpos
    (by unfold vFuel; omega)
  have hkv := pkv hk hw1 hw2 (fun c hc => ((SV.head_props l.v _).2 c hc).2.2.2) (by simpa [Line.enc] using hd) hvp
  rw [show vFuel src - 1 + 1 = vFuel src by unfold vFuel; omega] at hkv
  have hpend : pos + l.k.enc.length + l.w1.length + 1 + l.w2.length + l.v.enc.length = pos + l.enc.length := by
    simp [Line.enc]; omega
  simp only [hpend] at hkv
  have hrule := kvr_one hkv hfr
  obtain ⟨c, t, hke, hki, hcws, hc10⟩ := keyInitial_head l.k hk
  have hc : src[pos]? = some c := getElem?_of_drop (r := t ++ l.w1 ++ 61 :: l.w2 ++ l.v.enc ++ rest)
    (by rw [hd]; simp [Line.enc, hke])
  exact mainLoop_kv hc hki hcws hc10 hrule

theorem doc_loop (pf : ParseFloat) (maxK maxD : Nat) (src : Str) :
    ∀ (ls : List Line) (pos fuel : Nat) (out : Out), ls ≠ [] → (∀ l ∈ ls, l.ok) →
      (ls.map (·.k.val)).Nodup → (∀ l ∈ ls, dget out.data l.k.val = none) →
      src.drop pos = docEnc ls → ls.length < fuel →
      mainLoop (mkCfg pf maxK maxD) src fuel pos out [] = .ok (out.data ++ ls.map (fun l => (l.k.val, l.v.val)))
  | [], _, _, _, hne, _, _, _, _, _ => absurd rfl hne
  | l :: ls, pos, fuel, out, _, hok, hnd, hfresh, h, hf => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    have hfr := hfresh l (by simp)
    by_cases hls : ls = []
    · subst hls
      have hd : src.drop pos = l.enc ++ [] := by simpa [docEnc] using h
      rw [line_step pf maxK maxD src l pos f out [] (hok l (by simp)) hfr hd (by simp)]
      have hn : src[pos + l.enc.length]? = none := getElem?_of_drop_nil (by simpa using drop_add_of_drop hd)
      simp [hn, kvOut]
    · have hd : src.drop pos = l.enc ++ (10 :: docEnc ls) := by rw [h, docEnc_cons l ls hls]
      rw [line_step pf maxK maxD src l pos f out _ (hok l (by simp)) hfr hd
        (by intro c hc; simp at hc; subst hc; decide)]
      have hdrest : src.drop (pos + l.enc.length) = 10 :: docEnc ls := drop_add_of_drop hd
      have hn : src[pos + l.enc.length]? = some 10 := getElem?_of_drop hdrest
      simp only [hn, reduceCtorEq, ite_false, ite_true]
      have hmore : src.drop (pos + l.enc.length + 1) = docEnc ls := drop_succ_of_drop hdrest
      have hnd2 := List.nodup_cons.mp (by rw [List.map_cons] at hnd; exact hnd)
      have ih := doc_loop pf maxK maxD src ls (pos + l.enc.length + 1) f (kvOut out l.k.val l.v.val)
        hls (fun x hx => hok x (List.mem_cons_of_mem _ hx)) hnd2.2
        (by
          intro x hx
          have hne : x.k.val ≠ l.k.val := fun e => hnd2.1 (by rw [← e]; exact List.mem_map_of_mem hx)
          simp only [kvOut]
          rw [dget_append_ne _ _ _ _ hne]
          exact hfresh x (List.mem_cons_of_mem _ hx))
        hmore (by simp at hf; omega)
      rw [ih]
      simp [kvOut]

/-- Documents, TOML 1.1 "Key/Value Pair": for every document of `key = value` lines (one-part
keys written bare, literal or basic, all distinct; spaces or tabs around `=`; values built from
basic strings and booleans by arrays and inline tables, with comments and newlines inside them)
joined by newlines, `loads` returns the dict of the pairs in order. -/
def DocRoundTrip : Prop :=
  ∀ (pf : ParseFloat) (maxK maxD : Nat) (ls : List Line), (∀ l ∈ ls, l.ok) → (ls.map (·.k.val)).Nodup →
    loads pf maxK maxD (.str (docEnc ls)) = .ok (ls.map (fun l => (l.k.val, l.v.val)))

theorem line_no13 (l : Line) (h : l.ok) : 13 ∉ l.enc := by
  obtain ⟨hk, hw1, hw2, hv⟩ := h
  have := SV.no13 l.v hv; have := allWs_no13 hw1; have := allWs_no13 hw2
  have := fun m => kpart_no13 l.k hk 13 m rfl
  simp_all [Line.enc]

theorem docEnc_no13 : ∀ (ls : List Line), (∀ l ∈ ls, l.ok) → 13 ∉ docEnc ls
  | [], _ => by simp [docEnc]
  | [l], h => by simpa [docEnc] using line_no13 l (h l (by simp))
  | l :: l2 :: ls, h => by
    have h1 := line_no13 l (h l (by simp))
    have ih := docEnc_no13 (l2 :: ls) (fun x hx => h x (List.mem_cons_of_mem _ hx))
    rw [docEnc_cons l (l2 :: ls) (by simp)]
    simp_all

theorem docRoundTrip_proven : DocRoundTrip := by
  intro pf maxK maxD ls hok hnd
  rw [loads_eq pf maxK maxD _ (docEnc_no13 ls hok)]
  by_cases hls : ls = []
  · subst hls; simp [docEnc, mainLoop, skipChars, Out.init]
  · have hlen : ls.length < (docEnc ls).length + 1 := by
      clear hok hnd
      induction ls with
      | nil => exact absurd rfl hls
      | cons l t ih =>
        have hl : l.enc.length ≥ 1 := by simp [Line.enc]; omega
        by_cases ht : t = []
        · subst ht; simp [docEnc]; omega
        · have := ih ht; rw [docEnc_cons l t ht]; simp; omega
    have := doc_loop pf maxK maxD (docEnc ls) ls 0 _ Out.init hls hok hnd (by intro l _; rfl) (by simp) hlen
    simpa [Out.init] using this

end PyLean.TextLibs.Toml
