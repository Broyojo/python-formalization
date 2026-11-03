import PyLean.TextLibs.TomlTable

/-!
Arrays and inline tables (TOML 1.1): `parse_value` reads back every nested array and inline
table of strings and booleans, with whitespace, newlines and comments between the items and an
optional trailing comma.
-/

namespace PyLean.TextLibs.Toml

/-- One piece of what may stand between array items or inline-table entries in TOML 1.1:
a space or tab, a newline, or a comment up to its newline. -/
inductive Fill where
  | ws (c : Nat)
  | nl
  | cmt (t : Str)

def Fill.enc : Fill → Str
  | .ws c => [c]
  | .nl => [10]
  | .cmt t => 35 :: t ++ [10]

/-- A comment may hold any character except control characters other than tab. -/
def Fill.ok : Fill → Prop
  | .ws c => c = 32 ∨ c = 9
  | .nl => True
  | .cmt t => ∀ c ∈ t, illegalBasic c = false

def fillEnc (fs : List Fill) : Str := fs.flatMap Fill.enc

/-- What a filler may be followed by: anything but whitespace, a newline or `#`. -/
def notFill (rest : Str) : Prop := ∀ c, rest.head? = some c → tomlWsNl c = false ∧ c ≠ 35

/-- The text of a filler. -/
inductive FillStr : Str → Prop where
  | nil : FillStr []
  | wsnl {c : Nat} {s : Str} : tomlWsNl c = true → FillStr s → FillStr (c :: s)
  | cmt {t s : Str} : (∀ x ∈ t, illegalBasic x = false) → FillStr s → FillStr (35 :: t ++ 10 :: s)

theorem fillStr_append {a b : Str} (ha : FillStr a) (hb : FillStr b) : FillStr (a ++ b) := by
  induction ha with
  | nil => simpa using hb
  | wsnl hc _ ih => exact FillStr.wsnl hc ih
  | cmt ht _ ih => simpa using FillStr.cmt ht ih

theorem fillEnc_fillStr : ∀ (fs : List Fill), (∀ f ∈ fs, f.ok) → FillStr (fillEnc fs)
  | [], _ => FillStr.nil
  | f :: fs, h => by
    have ih := fillEnc_fillStr fs (fun g hg => h g (by simp [hg]))
    have hf := h f (by simp)
    have : fillEnc (f :: fs) = f.enc ++ fillEnc fs := by simp [fillEnc]
    rw [this]
    refine fillStr_append ?_ ih
    cases f with
    | ws c => exact FillStr.wsnl (by rcases hf with rfl | rfl <;> rfl) FillStr.nil
    | nl => exact FillStr.wsnl rfl FillStr.nil
    | cmt t => simpa [Fill.enc] using FillStr.cmt (s := []) hf FillStr.nil

theorem fillStr_split {F : Str} (h : FillStr F) : ∃ W G, F = W ++ G ∧ (∀ c ∈ W, tomlWsNl c = true) ∧
    (G = [] ∨ ∃ t s, G = 35 :: t ++ 10 :: s ∧ (∀ x ∈ t, illegalBasic x = false) ∧ FillStr s) := by
  induction h with
  | nil => exact ⟨[], [], rfl, by simp, Or.inl rfl⟩
  | wsnl hc _ ih =>
    obtain ⟨W, G, hF, hW, hG⟩ := ih
    refine ⟨_ :: W, G, by rw [hF]; rfl, ?_, hG⟩
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hc
    · exact hW x hx
  | @cmt t s ht hs _ => exact ⟨[], _, rfl, by simp, Or.inr ⟨t, s, rfl, ht, hs⟩⟩

theorem fillStr_len_pos {t s : Str} : (35 :: t ++ 10 :: s).length = t.length + s.length + 2 := by simp; omega

/-- `skip_comments_and_array_ws` skips exactly a filler. -/
theorem skipCaw_fill (src rest : Str) (hr : notFill rest) :
    ∀ (n : Nat) (F : Str), F.length = n → FillStr F → ∀ (fuel pos : Nat), src.drop pos = F ++ rest →
      F.length < fuel → skipCaw src fuel pos = .ok (pos + F.length) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro F hn hF fuel pos h hfuel
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨W, G, rfl, hW, hG⟩ := fillStr_split hF
    have hdW : src.drop pos = W ++ (G ++ rest) := by simpa using h
    rcases hG with rfl | ⟨t, s, rfl, ht, hs⟩
    · -- only whitespace and newlines
      have hsk : skipChars src pos tomlWsNl = pos + W.length :=
        skipChars_of_drop hdW hW (fun c hc => (hr c (by simpa using hc)).1)
      have hd2 : src.drop (pos + W.length) = rest := by simpa using drop_add_of_drop hdW
      have hcm : skipComment src (pos + W.length) = .ok (pos + W.length) := by
        unfold skipComment
        cases hrr : rest with
        | nil => rw [hrr] at hd2; simp [getElem?_of_drop_nil hd2]
        | cons c r =>
          rw [hrr] at hd2
          have := (hr c (by simp [hrr])).2
          simp [getElem?_of_drop hd2, this]
      simp only [skipCaw, hsk, hcm, bind, Except.bind]
      by_cases hW0 : W = []
      · subst hW0; simp [pure, Except.pure]
      · have hlt : 0 < W.length := List.length_pos_iff.mpr hW0
        have hne : (pos + W.length == pos) = false := by simp; omega
        simp only [hne, Bool.false_eq_true, ite_false]
        have := ih 0 (by have := hn; simp at this; omega) [] rfl FillStr.nil f (pos + W.length) (by simpa using hd2)
          (by have := hfuel; simp at this ⊢; omega)
        simpa using this
    · -- whitespace, then a comment
      have h35 : src.drop pos = W ++ (35 :: (t ++ 10 :: s ++ rest)) := by simpa using hdW
      have hsk : skipChars src pos tomlWsNl = pos + W.length :=
        skipChars_of_drop h35 hW (fun c hc => by simp at hc; subst hc; decide)
      have hd2 : src.drop (pos + W.length) = 35 :: (t ++ 10 :: (s ++ rest)) := by
        simpa using drop_add_of_drop h35
      have hn10 : 10 ∉ t := fun m => absurd (ht 10 m) (by decide)
      have hd3 : src.drop (pos + W.length + 1) = t ++ 10 :: (s ++ rest) := by simpa using drop_succ_of_drop hd2
      have hfind : findSub [10] (src.drop (pos + W.length + 1)) = some t.length := by
        rw [hd3]; exact findSub_single hn10
      have hsl : sl src (pos + W.length + 1) (pos + W.length + 1 + t.length) = t := sl_of_drop hd3
      have hcm : skipComment src (pos + W.length) = .ok (pos + W.length + 1 + t.length) := by
        unfold skipComment
        simp only [getElem?_of_drop hd2, show (some 35 == some 35) = true from rfl, ite_true, skipUntil, hfind, hsl,
          firstIdx_none ht]
      simp only [skipCaw, hsk, hcm, bind, Except.bind]
      have hne : (pos + W.length + 1 + t.length == pos) = false := by simp; omega
      simp only [hne, Bool.false_eq_true, ite_false]
      have hF' : FillStr (10 :: s) := FillStr.wsnl rfl hs
      have hd4 : src.drop (pos + W.length + 1 + t.length) = (10 :: s) ++ rest := by
        simpa using drop_add_of_drop hd3
      have := ih (10 :: s).length (by rw [← hn]; simp; omega) (10 :: s) rfl hF' f _ hd4
        (by simp at hfuel ⊢; omega)
      rw [this]; congr 1; simp; omega

theorem skipCawF_fill {src : Str} {pos : Nat} {fs : List Fill} {rest : Str} (hfs : ∀ f ∈ fs, f.ok)
    (hr : notFill rest) (h : src.drop pos = fillEnc fs ++ rest) :
    skipCawF src pos = .ok (pos + (fillEnc fs).length) := by
  have hl : (fillEnc fs).length < src.length + 1 := by
    have := congrArg List.length h; simp at this; omega
  exact skipCaw_fill src rest hr _ _ rfl (fillEnc_fillStr fs hfs) _ pos h hl

/-! ## Values -/

mutual
/-- A value built from basic strings and booleans by arrays and inline tables, as written:
`lead` is the filler after `[` or `{`. -/
inductive SV where
  | str (ps : List Piece)
  | bool (b : Bool)
  | arr (lead : List Fill) (items : AItems)
  | tbl (lead : List Fill) (items : TItems)
/-- Array items: none (`]`), a last item and the filler before `]`, or an item, the fillers
around its `,`, and the rest (`nil` after a comma is a trailing comma). -/
inductive AItems where
  | nil
  | one (v : SV) (fa : List Fill)
  | cons (v : SV) (fa fb : List Fill) (rest : AItems)
/-- Inline-table entries `k w1 = w2 v`, as for arrays. -/
inductive TItems where
  | nil
  | one (k : KPart) (w1 w2 : Str) (v : SV) (fa : List Fill)
  | cons (k : KPart) (w1 w2 : Str) (v : SV) (fa fb : List Fill) (rest : TItems)
end

mutual
def SV.enc : SV → Str
  | .str ps => 34 :: encAll ps ++ [34]
  | .bool b => if b then S "true" else S "false"
  | .arr lead items => 91 :: fillEnc lead ++ items.enc
  | .tbl lead items => 123 :: fillEnc lead ++ items.enc
def AItems.enc : AItems → Str
  | .nil => [93]
  | .one v fa => v.enc ++ fillEnc fa ++ [93]
  | .cons v fa fb rest => v.enc ++ fillEnc fa ++ 44 :: fillEnc fb ++ rest.enc
def TItems.enc : TItems → Str
  | .nil => [125]
  | .one k w1 w2 v fa => k.enc ++ w1 ++ 61 :: w2 ++ v.enc ++ fillEnc fa ++ [125]
  | .cons k w1 w2 v fa fb rest => k.enc ++ w1 ++ 61 :: w2 ++ v.enc ++ fillEnc fa ++ 44 :: fillEnc fb ++ rest.enc
end

mutual
def SV.val : SV → TVal
  | .str ps => .str (ps.map Piece.val)
  | .bool b => .bool b
  | .arr _ items => .arr items.vals
  | .tbl _ items => .tbl items.vals
def AItems.vals : AItems → List TVal
  | .nil => []
  | .one v _ => [v.val]
  | .cons v _ _ rest => v.val :: rest.vals
def TItems.vals : TItems → List (Str × TVal)
  | .nil => []
  | .one k _ _ v _ => [(k.val, v.val)]
  | .cons k _ _ v _ _ rest => (k.val, v.val) :: rest.vals
end

def TItems.keys : TItems → List Str
  | .nil => []
  | .one k _ _ _ _ => [k.val]
  | .cons k _ _ _ _ _ rest => k.val :: rest.keys

mutual
/-- TOML 1.1: string pieces as the spec allows, fillers, whitespace around `=`, and the keys of
an inline table distinct. -/
def SV.ok : SV → Prop
  | .str ps => ∀ p ∈ ps, p.ok
  | .bool _ => True
  | .arr lead items => (∀ f ∈ lead, f.ok) ∧ items.ok
  | .tbl lead items => (∀ f ∈ lead, f.ok) ∧ items.ok
def AItems.ok : AItems → Prop
  | .nil => True
  | .one v fa => v.ok ∧ ∀ f ∈ fa, f.ok
  | .cons v fa fb rest => v.ok ∧ (∀ f ∈ fa, f.ok) ∧ (∀ f ∈ fb, f.ok) ∧ rest.ok
def TItems.ok : TItems → Prop
  | .nil => True
  | .one k w1 w2 v fa => k.ok ∧ allWs w1 ∧ allWs w2 ∧ v.ok ∧ ∀ f ∈ fa, f.ok
  | .cons k w1 w2 v fa fb rest =>
    k.ok ∧ allWs w1 ∧ allWs w2 ∧ v.ok ∧ (∀ f ∈ fa, f.ok) ∧ (∀ f ∈ fb, f.ok) ∧ rest.ok ∧ k.val ∉ rest.keys
end

mutual
/-- The fuel `parse_value` needs. -/
def SV.need : SV → Nat
  | .str _ | .bool _ => 1
  | .arr _ items => items.need + 2
  | .tbl _ items => items.need + 2
def AItems.need : AItems → Nat
  | .nil => 0
  | .one v _ => v.need + 1
  | .cons v _ _ rest => max v.need rest.need + 1
def TItems.need : TItems → Nat
  | .nil => 0
  | .one _ _ _ v _ => v.need + 2
  | .cons _ _ _ v _ _ rest => max (v.need + 1) rest.need + 1
end

/-! ## Parsing -/

theorem SV.head (v : SV) : ∃ c t, v.enc = c :: t ∧ (c = 34 ∨ c = 116 ∨ c = 102 ∨ c = 91 ∨ c = 123) := by
  cases v with
  | str ps => exact ⟨34, _, rfl, Or.inl rfl⟩
  | bool b =>
    cases b
    · exact ⟨102, _, rfl, by decide⟩
    · exact ⟨116, _, rfl, by decide⟩
  | arr lead items => exact ⟨91, _, rfl, by decide⟩
  | tbl lead items => exact ⟨123, _, rfl, by decide⟩

theorem SV.head_props (v : SV) (x : Str) : notFill (v.enc ++ x) ∧
    (∀ c, (v.enc ++ x).head? = some c → c ≠ 93 ∧ c ≠ 125 ∧ c ≠ 44 ∧ tomlWs c = false) := by
  obtain ⟨c, t, he, hc⟩ := SV.head v
  rw [he]
  constructor
  · intro c' hc'; simp at hc'; subst hc'; rcases hc with rfl | rfl | rfl | rfl | rfl <;> decide
  · intro c' hc'; simp at hc'; subst hc'; rcases hc with rfl | rfl | rfl | rfl | rfl <;> decide

theorem notFill_93 (x : Str) : notFill (93 :: x) := by intro c hc; simp at hc; subst hc; decide
theorem notFill_125 (x : Str) : notFill (125 :: x) := by intro c hc; simp at hc; subst hc; decide
theorem notFill_44 (x : Str) : notFill (44 :: x) := by intro c hc; simp at hc; subst hc; decide

theorem fill_head_ne34 (fs : List Fill) (hfs : ∀ f ∈ fs, f.ok) (x : Str) (hx : ∀ c, x.head? = some c → c ≠ 34) :
    ∀ c, (fillEnc fs ++ x).head? = some c → c ≠ 34 := by
  intro c hc
  cases fs with
  | nil => exact hx c (by simpa [fillEnc] using hc)
  | cons f fs =>
    have hf := hfs f (by simp)
    cases f with
    | ws w => simp [fillEnc, Fill.enc] at hc; subst hc; rcases hf with rfl | rfl <;> decide
    | nl => simp [fillEnc, Fill.enc] at hc; subst hc; decide
    | cmt t => simp [fillEnc, Fill.enc] at hc; subst hc; decide

theorem kpart_head_props (k : KPart) (hk : k.ok) (x : Str) :
    notFill (k.enc ++ x) ∧ ∀ c, (k.enc ++ x).head? = some c → c ≠ 125 := by
  obtain ⟨c, t, he, hws, h46⟩ := KPart.head_not_ws hk
  have hc : c ≠ 10 ∧ c ≠ 35 ∧ c ≠ 125 := by
    cases k with
    | bare s =>
      have := hk.2 c (by simp [KPart.enc] at he; rw [he]; simp)
      refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> exact absurd this (by decide)
    | lit s =>
      have h1 : 39 = c := by simp [KPart.enc] at he; exact he.1
      subst h1; decide
    | basic ps =>
      have h1 : 34 = c := by simp [KPart.enc] at he; exact he.1
      subst h1; decide
  rw [he]
  refine ⟨fun c' hc' => ?_, fun c' hc' => ?_⟩ <;> simp at hc' <;> subst hc'
  · simp [tomlWsNl, hws, hc.1, hc.2.1]
  · exact hc.2.2

theorem parseValue_arr {cfg : Cfg} {src : Str} {pos f : Nat} (hg : src[pos]? = some 91) :
    parseValue cfg src (f + 1) pos = parseArray cfg src f pos := by
  simp [parseValue, hg]

theorem parseValue_tbl {cfg : Cfg} {src : Str} {pos f : Nat} (hg : src[pos]? = some 123) :
    parseValue cfg src (f + 1) pos = parseInlineTable cfg src f pos := by
  simp [parseValue, hg]

theorem parseValue_bool {cfg : Cfg} {src : Str} {pos f : Nat} {rest : Str} (b : Bool)
    (h : src.drop pos = (if b then S "true" else S "false") ++ rest) :
    parseValue cfg src (f + 1) pos = .ok (pos + (if b then S "true" else S "false").length, .bool b) := by
  cases b
  · have h' : src.drop pos = S "false" ++ rest := by simpa using h
    have hg : src[pos]? = some 102 := getElem?_of_drop (r := S "alse" ++ rest) (by rw [h']; rfl)
    have hs : startsAt src pos (S "false") = true := startsAt_of_drop h'
    simp [parseValue, hg, hs]; rfl
  · have h' : src.drop pos = S "true" ++ rest := by simpa using h
    have hg : src[pos]? = some 116 := getElem?_of_drop (r := S "rue" ++ rest) (by rw [h']; rfl)
    have hs : startsAt src pos (S "true") = true := startsAt_of_drop h'
    simp [parseValue, hg, hs]; rfl

theorem lookup_map_ne {α : Type} (d : List (Str × α)) (k k' : Str) (v : α) (hne : k' ≠ k) :
    (d.map (fun p => if p.1 == k then (k, v) else p)).lookup k' = d.lookup k' := by
  induction d with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    by_cases ha : a = k
    · subst ha
      have h1 : (k' == a) = false := by simp [hne]
      simp only [List.map_cons, beq_self_eq_true, ite_true, List.lookup, h1]
      exact ih
    · have h1 : (a == k) = false := by simp [ha]
      simp only [List.map_cons, h1, Bool.false_eq_true, ite_false]
      by_cases hk : k' = a
      · subst hk; simp only [List.lookup, beq_self_eq_true]
      · have h2 : (k' == a) = false := by simp [hk]
        simp only [List.lookup, h2]
        exact ih

theorem lookup_append_ne {α : Type} (d : List (Str × α)) (k k' : Str) (v : α) (hne : k' ≠ k) :
    (d ++ [(k, v)]).lookup k' = d.lookup k' := by
  have hb : (k' == k) = false := by simp [hne]
  induction d with
  | nil => simp [List.lookup, hb]
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    by_cases hk : k' = a
    · subst hk; simp [List.lookup]
    · have h2 : (k' == a) = false := by simp [hk]
      simp only [List.cons_append, List.lookup, h2]
      exact ih

theorem dget_dset_ne {α : Type} (d : List (Str × α)) (k k' : Str) (v : α) (hne : k' ≠ k) :
    dget (dset d k v) k' = dget d k' := by
  unfold dget dset
  split
  · exact lookup_map_ne d k k' v hne
  · exact lookup_append_ne d k k' v hne

theorem dset_absent {α : Type} (d : List (Str × α)) (k : Str) (v : α) (h : dget d k = none) :
    dset d k v = d ++ [(k, v)] := by
  unfold dset; unfold dget at h; simp [h]

theorem dget_append_ne {α : Type} (d : List (Str × α)) (k k' : Str) (v : α) (hne : k' ≠ k) :
    dget (d ++ [(k, v)]) k' = dget d k' := lookup_append_ne d k k' v hne

theorem SV.enc_ne (v : SV) : v.enc ≠ [] := by
  obtain ⟨c, t, he, -⟩ := SV.head v; rw [he]; simp

theorem AItems.enc_ne (items : AItems) : items.enc ≠ [] := by
  cases items <;> simp [AItems.enc, SV.enc_ne]

theorem TItems.enc_ne (items : TItems) (hok : items.ok) : items.enc ≠ [] := by
  cases items with
  | nil => simp [TItems.enc]
  | one k _ _ _ _ =>
    obtain ⟨c, t, he, -, -⟩ := KPart.head_not_ws hok.1; simp [TItems.enc, he]
  | cons k _ _ _ _ _ _ =>
    obtain ⟨c, t, he, -, -⟩ := KPart.head_not_ws hok.1; simp [TItems.enc, he]

theorem AItems.head_props (items : AItems) (x : Str) : notFill (items.enc ++ x) ∧
    (items ≠ .nil → ∀ c, (items.enc ++ x).head? = some c → c ≠ 93 ∧ tomlWs c = false) := by
  cases items with
  | nil => exact ⟨by simpa [AItems.enc] using notFill_93 x, fun h => absurd rfl h⟩
  | one v fa =>
    have := SV.head_props v (fillEnc fa ++ [93] ++ x)
    refine ⟨by simpa [AItems.enc] using this.1, fun _ c hc => ?_⟩
    have := this.2 c (by simpa [AItems.enc] using hc)
    exact ⟨this.1, this.2.2.2⟩
  | cons v fa fb r =>
    have := SV.head_props v (fillEnc fa ++ 44 :: fillEnc fb ++ r.enc ++ x)
    refine ⟨by simpa [AItems.enc] using this.1, fun _ c hc => ?_⟩
    have := this.2 c (by simpa [AItems.enc] using hc)
    exact ⟨this.1, this.2.2.2⟩

theorem TItems.head_props (items : TItems) (hok : items.ok) (x : Str) : notFill (items.enc ++ x) ∧
    (items ≠ .nil → ∀ c, (items.enc ++ x).head? = some c → c ≠ 125) := by
  cases items with
  | nil => exact ⟨by simpa [TItems.enc] using notFill_125 x, fun h => absurd rfl h⟩
  | one k w1 w2 v fa =>
    have := kpart_head_props k hok.1 (w1 ++ 61 :: w2 ++ v.enc ++ fillEnc fa ++ [125] ++ x)
    exact ⟨by simpa [TItems.enc] using this.1, fun _ c hc => this.2 c (by simpa [TItems.enc] using hc)⟩
  | cons k w1 w2 v fa fb r =>
    have := kpart_head_props k hok.1 (w1 ++ 61 :: w2 ++ v.enc ++ fillEnc fa ++ 44 :: fillEnc fb ++ r.enc ++ x)
    exact ⟨by simpa [TItems.enc] using this.1, fun _ c hc => this.2 c (by simpa [TItems.enc] using hc)⟩

/-- `parse_key_value_pair` on `k w1 = w2 v` for a one-part key, given what `parse_value` does. -/
theorem pkv {cfg : Cfg} {src : Str} {pos fuel : Nat} {k : KPart} {w1 w2 vs rest : Str} {res : Nat × TVal}
    (hk : k.ok) (h1 : allWs w1) (h2 : allWs w2) (hvh : ∀ c, (vs ++ rest).head? = some c → tomlWs c = false)
    (h : src.drop pos = k.enc ++ w1 ++ 61 :: w2 ++ vs ++ rest)
    (hv : parseValue cfg src fuel (pos + k.enc.length + w1.length + 1 + w2.length) = .ok res) :
    parseKeyValuePair cfg src (fuel + 1) pos = .ok (res.1, [k.val], res.2) := by
  have hkey := keySpec_proven cfg.maxKeyParts src pos k w1 [] (61 :: w2 ++ vs ++ rest) hk h1 (by simp)
    (by intro c hc; simp at hc; subst hc; decide) (by simpa using h)
  rw [if_pos (Or.inr rfl)] at hkey
  simp only [List.flatMap_nil, List.append_nil, List.map_nil] at hkey
  have hd : src.drop (pos + (k.enc ++ w1).length) = 61 :: (w2 ++ (vs ++ rest)) := by
    simpa using drop_add_of_drop (a := k.enc ++ w1) (by simpa using h)
  have hg := getElem?_of_drop hd
  have hd1 : src.drop (pos + (k.enc ++ w1).length + 1) = w2 ++ (vs ++ rest) := drop_succ_of_drop hd
  have hsk : skipChars src (pos + (k.enc ++ w1).length + 1) tomlWs = pos + (k.enc ++ w1).length + 1 + w2.length :=
    skipChars_of_drop hd1 h2 hvh
  have hpos : pos + (k.enc ++ w1).length + 1 + w2.length = pos + k.enc.length + w1.length + 1 + w2.length := by
    simp; omega
  simp only [parseKeyValuePair, hkey, bind, Except.bind, hg, show (some 61 != some 61) = false from rfl,
    Bool.false_eq_true, ite_false, hsk, hpos, hv, pure, Except.pure]

mutual
theorem SV.parse (cfg : Cfg) (src : Str) : ∀ (v : SV) (pos fuel : Nat) (rest : Str), v.ok →
    (∀ c, rest.head? = some c → c ≠ 34) → src.drop pos = v.enc ++ rest → v.need ≤ fuel →
    parseValue cfg src fuel pos = .ok (pos + v.enc.length, v.val)
  | .str ps, pos, fuel, rest, hok, hr, h, hf => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [SV.need] at hf; omega⟩
    have := basicStrRoundTrip_proven.1 cfg src pos f ps rest hok (by simpa [SV.enc] using h)
      (fun hh => hr 34 hh.2 rfl)
    rw [this]; simp [SV.enc, SV.val]; omega
  | .bool b, pos, fuel, rest, _, _, h, hf => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [SV.need] at hf; omega⟩
    rw [parseValue_bool b (by simpa [SV.enc] using h)]; rfl
  | .arr lead items, pos, fuel, rest, hok, hr, h, hf => by
    obtain ⟨g, rfl⟩ : ∃ g, fuel = g + 2 := ⟨fuel - 2, by simp [SV.need] at hf; omega⟩
    obtain ⟨hlead, hitems⟩ := hok
    have h0 : src.drop pos = 91 :: (fillEnc lead ++ (items.enc ++ rest)) := by simpa [SV.enc] using h
    rw [parseValue_arr (getElem?_of_drop h0)]
    have hd1 : src.drop (pos + 1) = fillEnc lead ++ (items.enc ++ rest) := drop_succ_of_drop h0
    have hsk := skipCawF_fill hlead (AItems.head_props items rest).1 hd1
    have hd2 : src.drop (pos + 1 + (fillEnc lead).length) = items.enc ++ rest := drop_add_of_drop hd1
    simp only [parseArray, hsk, bind, Except.bind]
    by_cases hnil : items = .nil
    · subst hnil
      have hst : startsAt src (pos + 1 + (fillEnc lead).length) [93] = true :=
        startsAt_of_drop (by simpa [AItems.enc] using hd2)
      simp [hst, SV.enc, AItems.enc, SV.val, AItems.vals, pure, Except.pure]; omega
    · have hst : startsAt src (pos + 1 + (fillEnc lead).length) [93] = false := by
        obtain ⟨c, t, hct⟩ := List.exists_cons_of_ne_nil (by simp [AItems.enc_ne] : items.enc ++ rest ≠ [])
        have := ((AItems.head_props items rest).2 hnil c (by simp [hct])).1
        simp [startsAt, hd2, hct, List.isPrefixOf, Ne.symm this]
      simp only [hst, Bool.false_eq_true, ite_false]
      rw [AItems.parse cfg src items _ g [] rest hnil hitems hd2 (by simp [SV.need] at hf; omega)]
      simp [SV.enc, SV.val]; omega
  | .tbl lead items, pos, fuel, rest, hok, hr, h, hf => by
    obtain ⟨g, rfl⟩ : ∃ g, fuel = g + 2 := ⟨fuel - 2, by simp [SV.need] at hf; omega⟩
    obtain ⟨hlead, hitems⟩ := hok
    have h0 : src.drop pos = 123 :: (fillEnc lead ++ (items.enc ++ rest)) := by simpa [SV.enc] using h
    rw [parseValue_tbl (getElem?_of_drop h0)]
    have hd1 : src.drop (pos + 1) = fillEnc lead ++ (items.enc ++ rest) := drop_succ_of_drop h0
    have hsk := skipCawF_fill hlead (TItems.head_props items hitems rest).1 hd1
    have hd2 : src.drop (pos + 1 + (fillEnc lead).length) = items.enc ++ rest := drop_add_of_drop hd1
    simp only [parseInlineTable, hsk, bind, Except.bind]
    by_cases hnil : items = .nil
    · subst hnil
      have hst : startsAt src (pos + 1 + (fillEnc lead).length) [125] = true :=
        startsAt_of_drop (by simpa [TItems.enc] using hd2)
      simp [hst, SV.enc, TItems.enc, SV.val, TItems.vals, pure, Except.pure]; omega
    · have hst : startsAt src (pos + 1 + (fillEnc lead).length) [125] = false := by
        obtain ⟨c, t, hct⟩ := List.exists_cons_of_ne_nil (by simp [TItems.enc_ne items hitems] : items.enc ++ rest ≠ [])
        have := (TItems.head_props items hitems rest).2 hnil c (by simp [hct])
        simp [startsAt, hd2, hct, List.isPrefixOf, Ne.symm this]
      simp only [hst, Bool.false_eq_true, ite_false]
      rw [TItems.parse cfg src items _ g [] Flags.init rest hnil hitems (by intro k _; simp [dget_nil, Flags.init])
        hd2 (by simp [SV.need] at hf; omega)]
      simp [SV.enc, SV.val]; omega

theorem AItems.parse (cfg : Cfg) (src : Str) : ∀ (items : AItems) (pos fuel : Nat) (acc : List TVal) (rest : Str),
    items ≠ .nil → items.ok → src.drop pos = items.enc ++ rest → items.need ≤ fuel →
    arrayLoop cfg src fuel pos acc = .ok (pos + items.enc.length, .arr (acc ++ items.vals))
  | .nil, _, _, _, _, hne, _, _, _ => absurd rfl hne
  | .one v fa, pos, fuel, acc, rest, _, hok, h, hf => by
    obtain ⟨g, rfl⟩ : ∃ g, fuel = g + 1 := ⟨fuel - 1, by simp [AItems.need] at hf; omega⟩
    obtain ⟨hv, hfa⟩ := hok
    have h1 : src.drop pos = v.enc ++ (fillEnc fa ++ 93 :: rest) := by simpa [AItems.enc] using h
    have hvp := SV.parse cfg src v pos g _ hv (fill_head_ne34 fa hfa _ (by intro c hc; simp at hc; omega)) h1
      (by simp [AItems.need] at hf; omega)
    have hd1 : src.drop (pos + v.enc.length) = fillEnc fa ++ (93 :: rest) := drop_add_of_drop h1
    have hsk := skipCawF_fill hfa (notFill_93 rest) hd1
    have hd2 : src.drop (pos + v.enc.length + (fillEnc fa).length) = [93] ++ rest := drop_add_of_drop hd1
    have hc := sl_of_drop hd2
    simp only [List.length_singleton] at hc
    simp only [arrayLoop, hvp, bind, Except.bind, hsk, hc, show ([93] == [93]) = true from rfl, ite_true, pure,
      Except.pure]
    simp [AItems.enc, AItems.vals]; omega
  | .cons v fa fb r, pos, fuel, acc, rest, _, hok, h, hf => by
    obtain ⟨g, rfl⟩ : ∃ g, fuel = g + 1 := ⟨fuel - 1, by simp [AItems.need] at hf; omega⟩
    obtain ⟨hv, hfa, hfb, hr⟩ := hok
    have h1 : src.drop pos = v.enc ++ (fillEnc fa ++ 44 :: (fillEnc fb ++ (r.enc ++ rest))) := by
      simpa [AItems.enc] using h
    have hvp := SV.parse cfg src v pos g _ hv (fill_head_ne34 fa hfa _ (by intro c hc; simp at hc; omega)) h1
      (by simp [AItems.need] at hf; omega)
    have hd1 : src.drop (pos + v.enc.length) = fillEnc fa ++ (44 :: (fillEnc fb ++ (r.enc ++ rest))) :=
      drop_add_of_drop h1
    have hsk := skipCawF_fill hfa (notFill_44 _) hd1
    have hd2 : src.drop (pos + v.enc.length + (fillEnc fa).length) = [44] ++ (fillEnc fb ++ (r.enc ++ rest)) :=
      drop_add_of_drop hd1
    have hc := sl_of_drop hd2
    simp only [List.length_singleton] at hc
    have hd3 : src.drop (pos + v.enc.length + (fillEnc fa).length + 1) = fillEnc fb ++ (r.enc ++ rest) :=
      drop_add_of_drop hd2
    have hsk2 := skipCawF_fill hfb (AItems.head_props r rest).1 hd3
    have hd4 : src.drop (pos + v.enc.length + (fillEnc fa).length + 1 + (fillEnc fb).length) = r.enc ++ rest :=
      drop_add_of_drop hd3
    simp only [arrayLoop, hvp, bind, Except.bind, hsk, hc, show ([44] == [93]) = false from rfl,
      show ([44] != [44]) = false from rfl, Bool.false_eq_true, ite_false, hsk2]
    by_cases hnil : r = .nil
    · subst hnil
      have hst := startsAt_of_drop (p := [93]) (by simpa [AItems.enc] using hd4)
      simp [hst, AItems.enc, AItems.vals, pure, Except.pure]; omega
    · have hst : startsAt src (pos + v.enc.length + (fillEnc fa).length + 1 + (fillEnc fb).length) [93] = false := by
        obtain ⟨c, t, hct⟩ := List.exists_cons_of_ne_nil (by simp [AItems.enc_ne] : r.enc ++ rest ≠ [])
        have := ((AItems.head_props r rest).2 hnil c (by simp [hct])).1
        simp [startsAt, hd4, hct, List.isPrefixOf, Ne.symm this]
      simp only [hst, Bool.false_eq_true, ite_false]
      rw [AItems.parse cfg src r _ g (acc ++ [v.val]) rest hnil hr hd4 (by simp [AItems.need] at hf; omega)]
      simp [AItems.enc, AItems.vals]; omega

theorem TItems.parse (cfg : Cfg) (src : Str) : ∀ (items : TItems) (pos fuel : Nat) (data : Dict) (flags : Flags)
    (rest : Str), items ≠ .nil → items.ok → (∀ k ∈ items.keys, dget data k = none ∧ dget flags.tree k = none) →
    src.drop pos = items.enc ++ rest → items.need ≤ fuel →
    inlineLoop cfg src fuel pos data flags = .ok (pos + items.enc.length, .tbl (data ++ items.vals))
  | .nil, _, _, _, _, _, hne, _, _, _, _ => absurd rfl hne
  | .one k w1 w2 v fa, pos, fuel, data, flags, rest, _, hok, hfresh, h, hf => by
    obtain ⟨g, rfl⟩ : ∃ g, fuel = g + 2 := ⟨fuel - 2, by simp [TItems.need] at hf; omega⟩
    obtain ⟨hk, hw1, hw2, hv, hfa⟩ := hok
    have h1 : src.drop pos = k.enc ++ w1 ++ 61 :: w2 ++ v.enc ++ (fillEnc fa ++ 125 :: rest) := by
      simpa [TItems.enc] using h
    have hvpos : src.drop (pos + k.enc.length + w1.length + 1 + w2.length) = v.enc ++ (fillEnc fa ++ 125 :: rest) := by
      have := drop_add_of_drop (a := k.enc ++ w1 ++ 61 :: w2) (by simpa using h1)
      have e : pos + (k.enc ++ w1 ++ 61 :: w2).length = pos + k.enc.length + w1.length + 1 + w2.length := by
        simp; omega
      rw [e] at this; exact this
    have hvp := SV.parse cfg src v _ g _ hv (fill_head_ne34 fa hfa _ (by intro c hc; simp at hc; omega)) hvpos
      (by simp [TItems.need] at hf; omega)
    have hkv := pkv hk hw1 hw2 (fun c hc => ((SV.head_props v _).2 c hc).2.2.2) h1 hvp
    have hfr := hfresh k.val (by simp [TItems.keys])
    have hd1 : src.drop (pos + k.enc.length + w1.length + 1 + w2.length + v.enc.length) = fillEnc fa ++ (125 :: rest) :=
      drop_add_of_drop hvpos
    have hsk := skipCawF_fill hfa (notFill_125 rest) hd1
    have hd2 : src.drop (pos + k.enc.length + w1.length + 1 + w2.length + v.enc.length + (fillEnc fa).length) =
        [125] ++ rest := drop_add_of_drop hd1
    have hc := sl_of_drop hd2
    simp only [List.length_singleton] at hc
    simp only [inlineLoop, hkv, bind, Except.bind]
    simp only [Flags.is_, List.isEmpty_cons, Bool.false_eq_true, ite_false, isAux, hfr.2, show ([k.val] : Key).dropLast = [] from rfl,
      show ([k.val] : Key).getLastD [] = k.val from rfl, withNest, hfr.1, Option.isSome_none, overwriteErr, dset_absent data k.val v.val hfr.1,
      hsk, hc, show ([125] == [125]) = true from rfl, ite_true, pure, Except.pure]
    simp [TItems.enc, TItems.vals]; omega
  | .cons k w1 w2 v fa fb r, pos, fuel, data, flags, rest, _, hok, hfresh, h, hf => by
    obtain ⟨g, rfl⟩ : ∃ g, fuel = g + 1 := ⟨fuel - 1, by simp [TItems.need] at hf; omega⟩
    obtain ⟨g', hg'⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by simp [TItems.need] at hf; omega⟩
    obtain ⟨hk, hw1, hw2, hv, hfa, hfb, hr, hkr⟩ := hok
    have h1 : src.drop pos = k.enc ++ w1 ++ 61 :: w2 ++ v.enc ++
        (fillEnc fa ++ 44 :: (fillEnc fb ++ (r.enc ++ rest))) := by
      simpa [TItems.enc] using h
    have hvpos : src.drop (pos + k.enc.length + w1.length + 1 + w2.length) =
        v.enc ++ (fillEnc fa ++ 44 :: (fillEnc fb ++ (r.enc ++ rest))) := by
      have := drop_add_of_drop (a := k.enc ++ w1 ++ 61 :: w2) (by simpa using h1)
      have e : pos + (k.enc ++ w1 ++ 61 :: w2).length = pos + k.enc.length + w1.length + 1 + w2.length := by
        simp; omega
      rw [e] at this; exact this
    have hvp := SV.parse cfg src v _ g' _ hv (fill_head_ne34 fa hfa _ (by intro c hc; simp at hc; omega)) hvpos
      (by simp [TItems.need] at hf; omega)
    have hkv := pkv hk hw1 hw2 (fun c hc => ((SV.head_props v _).2 c hc).2.2.2) h1 hvp
    rw [← hg'] at hkv
    have hfr := hfresh k.val (by simp [TItems.keys])
    have hd1 : src.drop (pos + k.enc.length + w1.length + 1 + w2.length + v.enc.length) =
        fillEnc fa ++ (44 :: (fillEnc fb ++ (r.enc ++ rest))) := drop_add_of_drop hvpos
    have hsk := skipCawF_fill hfa (notFill_44 _) hd1
    have hd2 : src.drop (pos + k.enc.length + w1.length + 1 + w2.length + v.enc.length + (fillEnc fa).length) =
        [44] ++ (fillEnc fb ++ (r.enc ++ rest)) := drop_add_of_drop hd1
    have hc := sl_of_drop hd2
    simp only [List.length_singleton] at hc
    have hd3 : src.drop (pos + k.enc.length + w1.length + 1 + w2.length + v.enc.length + (fillEnc fa).length + 1) =
        fillEnc fb ++ (r.enc ++ rest) := drop_add_of_drop hd2
    have hsk2 := skipCawF_fill hfb (TItems.head_props r hr rest).1 hd3
    have hd4 : src.drop (pos + k.enc.length + w1.length + 1 + w2.length + v.enc.length + (fillEnc fa).length + 1 +
        (fillEnc fb).length) = r.enc ++ rest := drop_add_of_drop hd3
    simp only [inlineLoop, hkv, bind, Except.bind]
    simp only [Flags.is_, List.isEmpty_cons, Bool.false_eq_true, ite_false, isAux, hfr.2, show ([k.val] : Key).dropLast = [] from rfl,
      show ([k.val] : Key).getLastD [] = k.val from rfl, withNest, hfr.1, Option.isSome_none, overwriteErr, dset_absent data k.val v.val hfr.1,
      hsk, hc, show ([44] == [125]) = false from rfl, show ([44] != [44]) = false from rfl, hsk2]
    by_cases hnil : r = .nil
    · subst hnil
      have hst := startsAt_of_drop (p := [125]) (by simpa [TItems.enc] using hd4)
      simp [hst, TItems.enc, TItems.vals, pure, Except.pure]; omega
    · have hst : startsAt src (pos + k.enc.length + w1.length + 1 + w2.length + v.enc.length + (fillEnc fa).length + 1 +
          (fillEnc fb).length) [125] = false := by
        obtain ⟨c, t, hct⟩ := List.exists_cons_of_ne_nil (by simp [TItems.enc_ne r hr] : r.enc ++ rest ≠ [])
        have := (TItems.head_props r hr rest).2 hnil c (by simp [hct])
        simp [startsAt, hd4, hct, List.isPrefixOf, Ne.symm this]
      simp only [hst, Bool.false_eq_true, ite_false]
      have hfresh' : ∀ fl : Flags, (∀ k' ∈ r.keys, dget fl.tree k' = none) →
          ∀ k' ∈ r.keys, dget (data ++ [(k.val, v.val)]) k' = none ∧ dget fl.tree k' = none := by
        intro fl hfl k' hk'
        have hne : k' ≠ k.val := fun e => hkr (e ▸ hk')
        refine ⟨?_, hfl k' hk'⟩
        rw [dget_append_ne _ _ _ _ hne]
        exact (hfresh k' (by simp [TItems.keys, hk'])).1
      cases hdl : v.val.isDictOrList
      · simp only [hdl, Bool.false_eq_true, ite_false, pure, Except.pure]
        rw [TItems.parse cfg src r _ g _ flags rest hnil hr
          (hfresh' flags (fun k' hk' => (hfresh k' (by simp [TItems.keys, hk'])).2)) hd4
          (by simp [TItems.need] at hf; omega)]
        simp [TItems.enc, TItems.vals]; omega
      · simp only [hdl, ite_true, Flags.set, List.isEmpty_cons, Bool.false_eq_true, ite_false]
        rw [TItems.parse cfg src r _ g _ _ rest hnil hr
          (hfresh' _ (fun k' hk' => by
            have hne : k' ≠ k.val := fun e => hkr (e ▸ hk')
            simp only [fsetAux]
            rw [dget_dset_ne _ _ _ _ hne]
            exact (hfresh k' (by simp [TItems.keys, hk'])).2)) hd4
          (by simp [TItems.need] at hf; omega)]
        simp [TItems.enc, TItems.vals]; omega
end

mutual
theorem SV.need_le : ∀ v : SV, v.need ≤ 2 * v.enc.length
  | .str ps => by simp [SV.need, SV.enc]; omega
  | .bool b => by cases b <;> simp [SV.need, SV.enc] <;> decide
  | .arr lead items => by have := AItems.need_le items; simp [SV.need, SV.enc]; omega
  | .tbl lead items => by have := TItems.need_le items; simp [SV.need, SV.enc]; omega
theorem AItems.need_le : ∀ items : AItems, items.need ≤ 2 * items.enc.length
  | .nil => by simp [AItems.need]
  | .one v fa => by have := SV.need_le v; simp [AItems.need, AItems.enc]; omega
  | .cons v fa fb r => by
    have := SV.need_le v; have := AItems.need_le r; simp [AItems.need, AItems.enc]; omega
theorem TItems.need_le : ∀ items : TItems, items.need ≤ 2 * items.enc.length
  | .nil => by simp [TItems.need]
  | .one k w1 w2 v fa => by have := SV.need_le v; simp [TItems.need, TItems.enc]; omega
  | .cons k w1 w2 v fa fb r => by
    have := SV.need_le v; have := TItems.need_le r; simp [TItems.need, TItems.enc]; omega
end

theorem fill_no13 (fs : List Fill) (hfs : ∀ f ∈ fs, f.ok) : 13 ∉ fillEnc fs := by
  intro m
  simp only [fillEnc, List.mem_flatMap] at m
  obtain ⟨f, hf, hm⟩ := m
  have := hfs f hf
  cases f with
  | ws c => simp [Fill.enc] at hm; subst hm; rcases this with h | h <;> simp at h
  | nl => simp [Fill.enc] at hm
  | cmt t =>
    simp [Fill.enc] at hm
    exact absurd (this 13 hm) (by decide)

theorem allWs_no13 {w : Str} (h : allWs w) : 13 ∉ w := fun m => absurd (h 13 m) (by decide)

mutual
theorem SV.no13 : ∀ v : SV, v.ok → 13 ∉ v.enc
  | .str ps, h => by
    have := kpart_no13 (.basic ps) h 13
    intro m; exact this (by simpa [KPart.enc, SV.enc] using m) rfl
  | .bool b, _ => by cases b <;> decide
  | .arr lead items, h => by
    have := AItems.no13 items h.2; have := fill_no13 lead h.1
    simp_all [SV.enc]
  | .tbl lead items, h => by
    have := TItems.no13 items h.2; have := fill_no13 lead h.1
    simp_all [SV.enc]
theorem AItems.no13 : ∀ items : AItems, items.ok → 13 ∉ items.enc
  | .nil, _ => by decide
  | .one v fa, h => by
    have := SV.no13 v h.1; have := fill_no13 fa h.2
    simp_all [AItems.enc]
  | .cons v fa fb r, h => by
    have := SV.no13 v h.1; have := fill_no13 fa h.2.1; have := fill_no13 fb h.2.2.1
    have := AItems.no13 r h.2.2.2
    simp_all [AItems.enc]
theorem TItems.no13 : ∀ items : TItems, items.ok → 13 ∉ items.enc
  | .nil, _ => by decide
  | .one k w1 w2 v fa, h => by
    have h1 := fun m => kpart_no13 k h.1 13 m rfl
    have := SV.no13 v h.2.2.2.1; have := fill_no13 fa h.2.2.2.2
    have := allWs_no13 h.2.1; have := allWs_no13 h.2.2.1
    simp_all [TItems.enc]
  | .cons k w1 w2 v fa fb r, h => by
    have h1 := fun m => kpart_no13 k h.1 13 m rfl
    have := SV.no13 v h.2.2.2.1; have := fill_no13 fa h.2.2.2.2.1; have := fill_no13 fb h.2.2.2.2.2.1
    have := allWs_no13 h.2.1; have := allWs_no13 h.2.2.1
    have := TItems.no13 r h.2.2.2.2.2.2.1
    simp_all [TItems.enc]
end

/-- Arrays and inline tables, TOML 1.1 "Array" and "Inline Table": for every value built from
basic strings and booleans by arrays and inline tables (distinct keys, one-part keys written
bare, literal or basic, spaces or tabs around `=`), with any whitespace, newlines and comments
after `[`/`{`, around each `,` and before `]`/`}`, and an optional trailing comma, `parse_value`
(with the fuel `loads` gives it) returns the nested lists and dicts in order and the position
after the value. -/
def ArrayTableSpec : Prop :=
  ∀ (cfg : Cfg) (src : Str) (pos : Nat) (v : SV) (rest : Str), v.ok →
    (∀ c, rest.head? = some c → c ≠ 34) → src.drop pos = v.enc ++ rest →
    parseValue cfg src (vFuel src) pos = .ok (pos + v.enc.length, v.val)

theorem arrayTableSpec_proven : ArrayTableSpec := by
  intro cfg src pos v rest hok hr h
  have hl := congrArg List.length h
  simp at hl
  have := SV.need_le v
  exact SV.parse cfg src v pos _ rest hok hr h (by unfold vFuel; omega)

end PyLean.TextLibs.Toml
