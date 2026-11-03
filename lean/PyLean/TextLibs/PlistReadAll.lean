import PyLean.TextLibs.PlistRead

/-! The binary reader on a table of canonically encoded objects: `_read_object` reads every
object reachable from the one it is asked for, each to the object encoded, and stores lists and
dicts by their slots, so shared and cyclic references come back shared and cyclic. -/

namespace PyLean.TextLibs.Plist

open PyLean PyLean.TextLibs PyLean.UnicodeObj

/-- The slots an object refers to. -/
def children : Obj → List Nat
  | .arr refs => refs
  | .dict items => items.map (·.1) ++ items.map (·.2)
  | _ => []

def isCont : Obj → Bool
  | .arr _ | .dict _ => true
  | _ => false

/-- An object table in a buffer: object `j` is `os[j]`, and its bytes start at `offsets[j]`. -/
structure Tab where
  os : List Obj
  B : List Nat
  offsets : List Nat
  refSize : Nat

/-- The keys of a dict are slots holding pairwise different `str`s. -/
def DictKeysWf (os : List Obj) : Obj → Prop
  | .dict items =>
    (∀ q ∈ items, ∃ s, os[q.1]? = some (.str s)) ∧
    (items.map fun q => os[q.1]?).Pairwise (· ≠ ·)
  | _ => True

/-- What the reader needs of the table. -/
def TabWf (T : Tab) : Prop :=
  T.offsets.length = T.os.length ∧ binaryFormat T.refSize = true ∧
  ∀ j (hj : j < T.os.length), ObjWf T.refSize T.os[j] ∧ (∀ x ∈ children T.os[j], x < T.os.length) ∧
    DictKeysWf T.os T.os[j] ∧
    ∃ e rest, canon T.refSize T.os[j] = some e ∧ T.B.drop (T.offsets.getD j 0) = e ++ rest ∧
      T.offsets.getD j 0 + 1 ≤ 2 ^ 63 - 1 ∧ e.length < 2 ^ 64

def Defined (st : PState) (j : Nat) : Prop := ∃ o, st.objs[j]? = some (some o)

/-- The reader's state while slots `P` (lists and dicts being read) are open: every other
defined slot holds its object, whose elements are all defined. -/
def Good (T : Tab) (P : List Nat) (st : PState) : Prop :=
  st.objs.length = T.os.length ∧ st.fp.buf = T.B ∧
  (∀ j o, st.objs[j]? = some (some o) → j ∉ P → T.os[j]? = some o ∧ ∀ x ∈ children o, Defined st x) ∧
  (∀ j ∈ P, Defined st j ∧ ∃ o, T.os[j]? = some o ∧ isCont o = true)

/-- Defined slots keep their objects, except `ex`. -/
def StableExc (ex : Option Nat) (st st' : PState) : Prop :=
  ∀ j o, st.objs[j]? = some (some o) → some j ≠ ex → st'.objs[j]? = some (some o)

theorem defined_stable {ex : Option Nat} {st st' : PState} (h : StableExc ex st st') (j : Nat)
    (hj : some j ≠ ex) (hd : Defined st j) : Defined st' j := by
  obtain ⟨o, ho⟩ := hd; exact ⟨o, h j o ho hj⟩

theorem stable_trans {ex : Option Nat} {a b c : PState} (h1 : StableExc ex a b) (h2 : StableExc ex b c) :
    StableExc ex a c := fun j o h hj => h2 j o (h1 j o h hj) hj

theorem stable_refl (ex : Option Nat) (a : PState) : StableExc ex a a := fun _ _ h _ => h

theorem stable_none_any {ex : Option Nat} {a b : PState} (h : StableExc none a b) : StableExc ex a b :=
  fun j o h' _ => h j o h' (by simp)

theorem put_get_self (st : PState) (ref : Nat) (o : Obj) (h : ref < st.objs.length) :
    (st.put ref o).objs[ref]? = some (some o) := by
  simp [PState.put, h]

theorem put_get_ne (st : PState) (ref j : Nat) (o : Obj) (h : j ≠ ref) :
    (st.put ref o).objs[j]? = st.objs[j]? := by
  simp [PState.put, List.getElem?_set_ne (Ne.symm h)]

theorem writeSizeB_cons (H size : Nat) : ∃ tok ext, writeSizeB H size = tok :: ext := by
  unfold writeSizeB
  by_cases h1 : size < 15
  · simp [h1]
  · by_cases h2 : size < 2 ^ 8
    · simp [h1, h2]
    · by_cases h3 : size < 2 ^ 16
      · simp [h1, h2, h3]
      · by_cases h4 : size < 2 ^ 32
        · simp [h1, h2, h3, h4]
        · simp [h1, h2, h3, h4]

theorem writeInt_cons (v : Int) (b : List Nat) (h : writeInt v = .ok b) : ∃ tok tail, b = tok :: tail := by
  unfold writeInt at h
  by_cases h0 : v < 0
  · rw [if_pos h0] at h
    by_cases h1 : v ≥ -2 ^ 63
    · rw [if_pos h1] at h; cases h; exact ⟨_, _, rfl⟩
    · rw [if_neg h1] at h; cases h
  · rw [if_neg h0] at h
    by_cases h2 : v < 2 ^ 8
    · rw [if_pos h2] at h; cases h; exact ⟨_, _, rfl⟩
    · rw [if_neg h2] at h
      by_cases h3 : v < 2 ^ 16
      · rw [if_pos h3] at h; cases h; exact ⟨_, _, rfl⟩
      · rw [if_neg h3] at h
        by_cases h4 : v < 2 ^ 32
        · rw [if_pos h4] at h; cases h; exact ⟨_, _, rfl⟩
        · rw [if_neg h4] at h
          by_cases h5 : v < 2 ^ 63
          · rw [if_pos h5] at h; cases h; exact ⟨_, _, rfl⟩
          · rw [if_neg h5] at h
            by_cases h6 : v < 2 ^ 64
            · rw [if_pos h6] at h; cases h; exact ⟨_, _, rfl⟩
            · rw [if_neg h6] at h; cases h

theorem sized_cons (H size : Nat) (pay : List Nat) : ∃ tok tail, writeSizeB H size ++ pay = tok :: tail := by
  obtain ⟨t, e, h⟩ := writeSizeB_cons H size
  exact ⟨t, e ++ pay, by rw [h]; rfl⟩

theorem canon_cons (rs : Nat) (o : Obj) (e : List Nat) (h : canon rs o = some e) :
    ∃ tok tail, e = tok :: tail := by
  cases o with
  | none => simp [canon] at h; exact ⟨_, _, h.symm⟩
  | bool b => simp [canon] at h; exact ⟨_, _, h.symm⟩
  | int v =>
    simp only [canon] at h
    cases hw : writeInt v with
    | error _ => rw [hw] at h; simp [Except.toOption] at h
    | ok b => rw [hw] at h; simp [Except.toOption] at h; subst h; exact writeInt_cons v _ hw
  | real b => simp [canon] at h; exact ⟨_, _, h.symm⟩
  | date _ _ => simp [canon] at h
  | data b => simp only [canon, Option.some.injEq] at h; subst h; exact sized_cons _ _ _
  | str s =>
    simp only [canon, strBytes] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; exact sized_cons _ _ _
    · split at h
      · simp only [Option.some.injEq] at h; subst h; exact sized_cons _ _ _
      · cases h
  | uid d =>
    simp only [canon, uidBytes] at h
    by_cases h1 : d < 2 ^ 8
    · rw [if_pos h1] at h; cases h; exact ⟨_, _, rfl⟩
    · rw [if_neg h1] at h
      by_cases h2 : d < 2 ^ 16
      · rw [if_pos h2] at h; cases h; exact ⟨_, _, rfl⟩
      · rw [if_neg h2] at h
        by_cases h3 : d < 2 ^ 32
        · rw [if_pos h3] at h; cases h; exact ⟨_, _, rfl⟩
        · rw [if_neg h3] at h
          by_cases h4 : d < 2 ^ 64
          · rw [if_pos h4] at h; cases h; exact ⟨_, _, rfl⟩
          · rw [if_neg h4] at h; cases h
  | arr refs => simp only [canon, Option.some.injEq] at h; subst h; exact sized_cons _ _ _
  | dict items =>
    simp only [canon, Option.some.injEq] at h; subst h
    obtain ⟨t, tl, ht⟩ := sized_cons 0xD0 items.length
      (packRefs rs (items.map (·.1)) ++ packRefs rs (items.map (·.2)))
    exact ⟨t, tl, by rw [List.append_assoc]; exact ht⟩


theorem readObj_step (cfg : PCfg) (k ref : Nat) (st : PState) (tok : Nat) (tail rest : List Nat)
    (hs : st.objs[ref]? = some none) (hp : cfg.offsets.getD ref 0 + 1 ≤ 2 ^ 63 - 1)
    (hd : st.fp.buf.drop (cfg.offsets.getD ref 0) = tok :: tail ++ rest) :
    readObj cfg (k + 1) ref st =
      readToken cfg k (fun x st => readObj cfg k x st) ref st tok
        ⟨st.fp.buf, cfg.offsets.getD ref 0 + 1⟩ := by
  simp only [readObj, hs]
  have hseek : st.fp.seek (cfg.offsets.getD ref 0) = .ok ⟨st.fp.buf, cfg.offsets.getD ref 0⟩ := by
    simp only [FP.seek]
    rw [if_neg (by omega)]
  rw [hseek]
  simp only [bind, Except.bind]
  rw [read_one st.fp.buf (cfg.offsets.getD ref 0) tok (tail ++ rest) (by simpa using hd)]

theorem afterToken_leaf (cfg : PCfg) (k ref : Nat) (st : PState) (fp : FP) (o : Obj)
    (h : isCont o = false) :
    afterToken cfg k ref st fp o = .ok (({ fp := fp, objs := st.objs } : PState).put ref o) := by
  cases o <;> simp_all [afterToken, isCont]

theorem readToken_canon (cfg : PCfg) (k ref : Nat) (st : PState) (o : Obj) (B : List Nat) (p tok : Nat)
    (tail rest : List Nat) (hk : 4 ≤ k) (hrs : binaryFormat cfg.refSize = true)
    (hwf : ObjWf cfg.refSize o) (he : canon cfg.refSize o = some (tok :: tail))
    (hl : (tok :: tail).length < 2 ^ 64) (hb : B.drop p = tail ++ rest) :
    ∃ fp : FP, fp.buf = B ∧
      readToken cfg k (fun x st => readObj cfg k x st) ref st tok ⟨B, p⟩ = afterToken cfg k ref st fp o := by
  have hsz : 1 ≤ cfg.refSize := by simp [binaryFormat] at hrs; omega
  simp only [List.length_cons] at hl
  cases o with
  | none =>
    simp only [canon, Option.some.injEq, List.cons.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨⟨B, p⟩, rfl, by simp [readToken, afterToken]⟩
  | bool b =>
    simp only [canon, Option.some.injEq, List.cons.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    cases b <;> exact ⟨⟨B, p⟩, rfl, by simp [readToken, afterToken]⟩
  | int v =>
    simp only [canon] at he
    cases hw : writeInt v with
    | error _ => rw [hw] at he; simp [Except.toOption] at he
    | ok b =>
      rw [hw] at he
      simp only [Except.toOption, Option.some.injEq] at he
      subst he
      obtain ⟨fp, hfp, h⟩ := readToken_int cfg k ref st v B p tok tail rest hw hb
      exact ⟨fp, hfp, by rw [h]; rfl⟩
  | real bits =>
    simp only [canon, Option.some.injEq, List.cons.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have hr := read_prefix B p (beBytes bits 8) rest hb
    rw [beBytes_length] at hr
    refine ⟨⟨B, p + 8⟩, rfl, ?_⟩
    simp only [ObjWf] at hwf
    simp [readToken, afterToken, hr, unpackReal, beBytes_length, beVal_beBytes 8 bits (by omega),
      bind, Except.bind]
  | date _ _ => simp [canon] at he
  | data b =>
    simp only [canon, Option.some.injEq] at he
    have hbl : b.length < 2 ^ 64 := by
      have := congrArg List.length he; simp at this; omega
    obtain ⟨fp, hfp, h⟩ := readToken_data cfg k ref st b B p tok tail rest (by omega) hbl he hb
    exact ⟨fp, hfp, by rw [h]; rfl⟩
  | str s =>
    simp only [canon, strBytes] at he
    have hsp := ascii_encode_spec s
    split at he
    · rename_i t ht
      rw [ht] at hsp
      obtain ⟨rfl, ha⟩ := hsp
      simp only [Option.some.injEq] at he
      have hsl : t.length < 2 ^ 64 := by
        have := congrArg List.length he; simp at this; omega
      obtain ⟨fp, hfp, h⟩ := readToken_ascii cfg k ref st t B p tok tail rest (by omega) hsl ha he hb
      exact ⟨fp, hfp, by rw [h]; rfl⟩
    · split at he
      · rename_i t ht
        simp only [Option.some.injEq] at he
        obtain ⟨hev, hdec⟩ := utf16be_spec s hwf t ht
        have htl : t.length / 2 < 2 ^ 64 := by
          have := congrArg List.length he; simp at this; omega
        obtain ⟨fp, hfp, h⟩ := readToken_utf16 cfg k ref st s t B p tok tail rest (by omega) htl hev
          hdec he hb
        exact ⟨fp, hfp, by rw [h]; rfl⟩
      · cases he
  | uid d =>
    simp only [canon] at he
    obtain ⟨fp, hfp, h⟩ := readToken_uid cfg k ref st d B p tok tail rest (by omega) he hb
    exact ⟨fp, hfp, by rw [h]; rfl⟩
  | arr refs =>
    simp only [canon, Option.some.injEq] at he
    have hl2 : refs.length < 2 ^ 64 := by
      have := congrArg List.length he
      simp only [List.length_append, packRefs_length, List.length_cons] at this
      have : refs.length ≤ cfg.refSize * refs.length := Nat.le_mul_of_pos_left _ hsz
      omega
    exact readToken_arr cfg k ref st refs B p tok tail rest hk hl2 hrs hwf he hb
  | dict items =>
    simp only [canon, Option.some.injEq] at he
    rw [List.append_assoc] at he
    have hl2 : items.length < 2 ^ 64 := by
      have := congrArg List.length he
      simp only [List.length_append, packRefs_length, List.length_cons, List.length_map] at this
      have : items.length ≤ cfg.refSize * items.length := Nat.le_mul_of_pos_left _ hsz
      omega
    exact readToken_dict cfg k ref st items B p tok tail rest hk hl2 hrs hwf he hb


def cfgOf (T : Tab) (aware : Bool) : PCfg := ⟨T.offsets, T.refSize, aware⟩

theorem children_leaf (o : Obj) (h : isCont o = false) : children o = [] := by
  cases o <;> simp_all [children, isCont]

theorem keyEq_str (a b : List Nat) : keyEq (.str a) (.str b) = (a == b) := by
  simp [keyEq, numEq]

theorem dictSet_append (objs : List (Option Obj)) (k v : Nat) :
    ∀ acc : List (Nat × Nat), (∀ q ∈ acc, q.1 ≠ k ∧ ∀ a b, objs.getD q.1 none = some a →
      objs.getD k none = some b → keyEq a b = false) → dictSet objs k v acc = acc ++ [(k, v)]
  | [], _ => rfl
  | (k', v') :: acc, h => by
    have h1 := h (k', v') (by simp)
    have ih := dictSet_append objs k v acc (fun q hq => h q (by simp [hq]))
    simp only [dictSet]
    rw [if_neg]
    · rw [ih]
      simp
    · intro hsame
      simp only [Bool.or_eq_true, beq_iff_eq] at hsame
      rcases hsame with h' | h'
      · exact h1.1 h'
      · revert h'
        split
        · rename_i a b ha hb
          rw [h1.2 a b ha hb]
          simp
        · simp

theorem getD_of_getElem? {l : List (Option Obj)} {j : Nat} {o : Obj} (h : l[j]? = some (some o)) :
    l.getD j none = some o := by
  simp [List.getD_eq_getElem?_getD, h]

/-- Putting into an open slot keeps the reader's state good. -/
theorem good_put_open (T : Tab) (P : List Nat) (st : PState) (ref : Nat) (o : Obj) (fp : FP)
    (hg : Good T P st) (hP : ref ∈ P) (hfp : fp.buf = T.B) :
    Good T P (({ fp := fp, objs := st.objs } : PState).put ref o) := by
  obtain ⟨hl, _, hb, hc⟩ := hg
  have hlen : ref < st.objs.length := by
    obtain ⟨⟨o', ho'⟩, _⟩ := hc ref hP
    exact lt_of_getElem?_some ho'
  have hdef : ∀ x, Defined st x → Defined (({ fp := fp, objs := st.objs } : PState).put ref o) x := by
    intro x ⟨o', ho'⟩
    by_cases hx : x = ref
    · subst hx; exact ⟨o, put_get_self _ _ _ (by simpa using hlen)⟩
    · exact ⟨o', by rw [put_get_ne _ _ _ _ hx]; exact ho'⟩
  refine ⟨by simp [PState.put, hl], hfp, ?_, ?_⟩
  · intro j o' hj hjP
    have hne : j ≠ ref := fun h => hjP (h ▸ hP)
    rw [put_get_ne _ _ _ _ hne] at hj
    obtain ⟨h1, h2⟩ := hb j o' hj hjP
    exact ⟨h1, fun x hx => hdef x (h2 x hx)⟩
  · intro j hj
    obtain ⟨hd, h2⟩ := hc j hj
    exact ⟨hdef j hd, h2⟩

theorem arrLoop_tab (T : Tab) (aware : Bool) (k ref : Nat) (P : List Nat)
    (IH : ∀ x (st : PState) (P : List Nat), Good T P st → x < T.os.length → undef st.objs + 5 ≤ k →
      ∃ st', readObj (cfgOf T aware) k x st = .ok st' ∧ Good T P st' ∧ StableExc none st st' ∧
        Defined st' x ∧ undef st'.objs ≤ undef st.objs) :
    ∀ (xs acc : List Nat) (st : PState), Good T (ref :: P) st → (∀ x ∈ xs, x < T.os.length) →
      undef st.objs + 5 ≤ k → st.objs[ref]? = some (some (.arr acc)) →
      ∃ st', arrLoop (fun x st => readObj (cfgOf T aware) k x st) ref acc xs st = .ok st' ∧
        Good T (ref :: P) st' ∧ StableExc (some ref) st st' ∧ (∀ x ∈ xs, Defined st' x) ∧
        st'.objs[ref]? = some (some (.arr (acc ++ xs))) ∧ undef st'.objs ≤ undef st.objs
  | [], acc, st, hg, _, _, hr => ⟨st, rfl, hg, stable_refl _ _, by simp, by simpa using hr, Nat.le_refl _⟩
  | x :: xs, acc, st, hg, hx, hk, hr => by
    obtain ⟨st2, h2, hg2, hs2, hd2, hu2⟩ := IH x st (ref :: P) hg (hx x (by simp)) hk
    have hfp : st2.fp.buf = T.B := hg2.2.1
    have hr2 : st2.objs[ref]? = some (some (.arr acc)) := hs2 ref _ hr (by simp)
    let st3 := ({ fp := st2.fp, objs := st2.objs } : PState).put ref (.arr (acc ++ [x]))
    have hg3 : Good T (ref :: P) st3 := good_put_open T _ st2 ref _ st2.fp hg2 (by simp) hfp
    have hlen : ref < st2.objs.length := lt_of_getElem?_some hr2
    have hu3 : undef st3.objs ≤ undef st2.objs := put_undef_le _ _ _
    have hr3 : st3.objs[ref]? = some (some (.arr (acc ++ [x]))) := put_get_self _ _ _ (by simpa using hlen)
    obtain ⟨st', h', hg', hs', hd', hr', hu'⟩ :=
      arrLoop_tab T aware k ref P IH xs (acc ++ [x]) st3 hg3 (fun y hy => hx y (by simp [hy]))
        (by omega) hr3
    refine ⟨st', ?_, hg', ?_, ?_, by simpa using hr', by omega⟩
    · simp only [arrLoop, h2, bind, Except.bind]
      exact h'
    · intro j o hj hjr
      have hj2 := hs2 j o hj (by simp)
      have hne : j ≠ ref := fun h => hjr (by rw [h])
      have hj3 : st3.objs[j]? = some (some o) := by
        simp only [st3]; rw [put_get_ne _ _ _ _ hne]; exact hj2
      exact hs' j o hj3 hjr
    · intro y hy
      simp at hy
      rcases hy with rfl | hy
      · by_cases hyr : y = ref
        · subst hyr; exact ⟨_, hr'⟩
        · obtain ⟨o, ho⟩ := hd2
          have : st3.objs[y]? = some (some o) := by
            simp only [st3]; rw [put_get_ne _ _ _ _ hyr]; exact ho
          exact ⟨o, hs' y o this (by simpa using hyr)⟩
      · exact hd' y hy


theorem key_is_str (T : Tab) (P : List Nat) (st : PState) (k : Nat) (s : List Nat) (ko : Obj)
    (hg : Good T P st) (hos : T.os[k]? = some (.str s)) (hk : st.objs[k]? = some (some ko)) :
    ko = .str s := by
  obtain ⟨_, _, hb, hc⟩ := hg
  by_cases hkP : k ∈ P
  · obtain ⟨_, o, ho, hco⟩ := hc k hkP
    rw [hos] at ho; cases ho; simp [isCont] at hco
  · have := (hb k ko hk hkP).1
    rw [hos] at this; cases this; rfl

theorem pairwise_prefix_ne {α β : Type} (f : α → β) (done todo : List α) (x : α)
    (h : ((done ++ x :: todo).map f).Pairwise (· ≠ ·)) : ∀ q ∈ done, f q ≠ f x := by
  intro q hq
  rw [List.map_append, List.pairwise_append] at h
  exact h.2.2 (f q) (List.mem_map_of_mem hq) (f x) (by simp)

theorem dictLoop_tab (T : Tab) (aware : Bool) (k ref : Nat) (P : List Nat)
    (IH : ∀ x (st : PState) (P : List Nat), Good T P st → x < T.os.length → undef st.objs + 5 ≤ k →
      ∃ st', readObj (cfgOf T aware) k x st = .ok st' ∧ Good T P st' ∧ StableExc none st st' ∧
        Defined st' x ∧ undef st'.objs ≤ undef st.objs)
    (items : List (Nat × Nat))
    (hstr : ∀ q ∈ items, ∃ s, T.os[q.1]? = some (.str s))
    (hpw : (items.map fun q => T.os[q.1]?).Pairwise (· ≠ ·)) :
    ∀ (todo done : List (Nat × Nat)) (st : PState), done ++ todo = items → Good T (ref :: P) st →
      (∀ q ∈ todo, q.1 < T.os.length ∧ q.2 < T.os.length) → undef st.objs + 5 ≤ k →
      st.objs[ref]? = some (some (.dict done)) →
      (∀ q ∈ done, Defined st q.1 ∧ Defined st q.2) →
      ∃ st', dictLoop (fun x st => readObj (cfgOf T aware) k x st) ref done todo st = .ok st' ∧
        Good T (ref :: P) st' ∧ StableExc (some ref) st st' ∧
        (∀ q ∈ items, Defined st' q.1 ∧ Defined st' q.2) ∧
        st'.objs[ref]? = some (some (.dict items)) ∧ undef st'.objs ≤ undef st.objs
  | [], done, st, he, hg, _, _, hr, hd => by
    simp at he; subst he
    exact ⟨st, rfl, hg, stable_refl _ _, hd, hr, Nat.le_refl _⟩
  | (k1, o1) :: todo, done, st, he, hg, hx, hk, hr, hd => by
    have hx1 := hx (k1, o1) (by simp)
    obtain ⟨st2, h2, hg2, hs2, hd2, hu2⟩ := IH o1 st (ref :: P) hg hx1.2 hk
    obtain ⟨st3, h3, hg3, hs3, hd3, hu3⟩ := IH k1 st2 (ref :: P) hg2 hx1.1 (by omega)
    obtain ⟨s1, hs1⟩ := hstr (k1, o1) (by rw [← he]; simp)
    obtain ⟨ko, hko⟩ := hd3
    have hko' : ko = .str s1 := key_is_str T _ st3 k1 s1 ko hg3 hs1 hko
    subst hko'
    -- the keys read so far are other strs
    have hdef23 : ∀ x, Defined st x → Defined st3 x := fun x hx =>
      defined_stable hs3 x (by simp) (defined_stable hs2 x (by simp) hx)
    have hdone3 : ∀ q ∈ done, Defined st3 q.1 ∧ Defined st3 q.2 := fun q hq =>
      ⟨hdef23 _ (hd q hq).1, hdef23 _ (hd q hq).2⟩
    have hset : dictSet st3.objs k1 o1 done = done ++ [(k1, o1)] := by
      apply dictSet_append
      intro q hq
      obtain ⟨sq, hsq⟩ := hstr q (by rw [← he]; simp [hq])
      have hne := pairwise_prefix_ne (fun q => T.os[q.1]?) done todo (k1, o1) (by rw [he]; exact hpw) q hq
      simp only [hsq, hs1] at hne
      refine ⟨?_, ?_⟩
      · intro hq1
        rw [hq1, hs1] at hsq
        cases hsq
        exact hne rfl
      · intro a b ha hb
        obtain ⟨⟨oq, hoq⟩, _⟩ := hdone3 q hq
        have hoq' := key_is_str T _ st3 q.1 sq oq hg3 hsq hoq
        rw [getD_of_getElem? hoq, hoq'] at ha
        rw [getD_of_getElem? hko] at hb
        cases ha; cases hb
        rw [keyEq_str]
        simp only [beq_eq_false_iff_ne]
        intro heq; exact hne (by rw [heq])
    have hr3 : st3.objs[ref]? = some (some (.dict done)) :=
      hs3 ref _ (hs2 ref _ hr (by simp)) (by simp)
    have hfp : st3.fp.buf = T.B := hg3.2.1
    let st4 := ({ fp := st3.fp, objs := st3.objs } : PState).put ref (.dict (done ++ [(k1, o1)]))
    have hg4 : Good T (ref :: P) st4 := good_put_open T _ st3 ref _ st3.fp hg3 (by simp) hfp
    have hlen : ref < st3.objs.length := lt_of_getElem?_some hr3
    have hr4 : st4.objs[ref]? = some (some (.dict (done ++ [(k1, o1)]))) :=
      put_get_self _ _ _ (by simpa using hlen)
    have hdef4 : ∀ x, Defined st3 x → Defined st4 x := by
      intro x ⟨o, ho⟩
      by_cases hxr : x = ref
      · subst hxr; exact ⟨_, hr4⟩
      · exact ⟨o, by simp only [st4]; rw [put_get_ne _ _ _ _ hxr]; exact ho⟩
    have hd4 : ∀ q ∈ done ++ [(k1, o1)], Defined st4 q.1 ∧ Defined st4 q.2 := by
      intro q hq
      simp at hq
      rcases hq with hq | rfl
      · exact ⟨hdef4 _ (hdone3 q hq).1, hdef4 _ (hdone3 q hq).2⟩
      · exact ⟨hdef4 _ ⟨_, hko⟩, hdef4 _ (defined_stable hs3 o1 (by simp) hd2)⟩
    obtain ⟨st', h', hg', hs', hd', hr', hu'⟩ :=
      dictLoop_tab T aware k ref P IH items hstr hpw todo (done ++ [(k1, o1)]) st4 (by rw [← he]; simp)
        hg4 (fun q hq => hx q (by simp [hq])) (by have := put_undef_le ({ fp := st3.fp, objs := st3.objs } : PState) ref (.dict (done ++ [(k1, o1)])); simp only [st4] at *; omega) hr4 hd4
    refine ⟨st', ?_, hg', ?_, hd', hr', ?_⟩
    · simp only [dictLoop, h2, h3, bind, Except.bind, getD_of_getElem? hko, unhashable,
        Bool.false_eq_true, ↓reduceIte, hset]
      exact h'
    · intro j o hj hjr
      have hj3 := hs3 j o (hs2 j o hj (by simp)) (by simp)
      have hne : j ≠ ref := fun h => hjr (by rw [h])
      have hj4 : st4.objs[j]? = some (some o) := by
        simp only [st4]; rw [put_get_ne _ _ _ _ hne]; exact hj3
      exact hs' j o hj4 hjr
    · have := put_undef_le ({ fp := st3.fp, objs := st3.objs } : PState) ref (.dict (done ++ [(k1, o1)]))
      simp only [st4] at *
      omega


theorem good_put_new (T : Tab) (P : List Nat) (st : PState) (ref : Nat) (o : Obj) (fp : FP)
    (hg : Good T P st) (hs : st.objs[ref]? = some none) (hfp : fp.buf = T.B) (hos : T.os[ref]? = some o)
    (hleaf : isCont o = false) :
    Good T P (({ fp := fp, objs := st.objs } : PState).put ref o) ∧
      StableExc none st (({ fp := fp, objs := st.objs } : PState).put ref o) := by
  obtain ⟨hl, _, hb, hc⟩ := hg
  have hlen : ref < st.objs.length := lt_of_getElem?_some hs
  have hdef : ∀ x, Defined st x → Defined (({ fp := fp, objs := st.objs } : PState).put ref o) x := by
    intro x ⟨o', ho'⟩
    by_cases hx : x = ref
    · subst hx; exact ⟨o, put_get_self _ _ _ (by simpa using hlen)⟩
    · exact ⟨o', by rw [put_get_ne _ _ _ _ hx]; exact ho'⟩
  refine ⟨⟨by simp [PState.put, hl], hfp, ?_, ?_⟩, ?_⟩
  · intro j o' hj hjP
    by_cases hjr : j = ref
    · subst hjr
      rw [put_get_self _ _ _ (by simpa using hlen)] at hj
      cases hj
      exact ⟨hos, by simp [children_leaf o hleaf]⟩
    · rw [put_get_ne _ _ _ _ hjr] at hj
      obtain ⟨h1, h2⟩ := hb j o' hj hjP
      exact ⟨h1, fun x hx => hdef x (h2 x hx)⟩
  · intro j hj
    obtain ⟨hd, h2⟩ := hc j hj
    exact ⟨hdef j hd, h2⟩
  · intro j o' hj _
    have hjr : j ≠ ref := by intro h; subst h; rw [hs] at hj; cases hj
    rw [put_get_ne _ _ _ _ hjr]; exact hj

theorem readObj_tab (T : Tab) (hT : TabWf T) (aware : Bool) :
    ∀ k ref (st : PState) (P : List Nat), Good T P st → ref < T.os.length → undef st.objs + 5 ≤ k →
      ∃ st', readObj (cfgOf T aware) k ref st = .ok st' ∧ Good T P st' ∧ StableExc none st st' ∧
        Defined st' ref ∧ undef st'.objs ≤ undef st.objs
  | 0, _, _, _, _, _, h => by omega
  | k + 1, ref, st, P, hg, hr, hk => by
    have hlen : st.objs.length = T.os.length := hg.1
    match hs : st.objs[ref]? with
    | none =>
      rw [List.getElem?_eq_none_iff] at hs; omega
    | some (some o) =>
      refine ⟨st, ?_, hg, stable_refl _ _, ⟨o, hs⟩, Nat.le_refl _⟩
      simp only [readObj, hs]
    | some none =>
      have hu1 := undef_set_none st.objs ref .none hs
      have hrP : ref ∉ P := by
        intro h
        obtain ⟨⟨o, ho⟩, _⟩ := hg.2.2.2 ref h
        rw [hs] at ho; cases ho
      obtain ⟨_, hbf, hTj⟩ := hT
      obtain ⟨hwf, hch, hdk, e, rest, he, hd, hp, hel⟩ := hTj ref hr
      obtain ⟨tok, tail, rfl⟩ := canon_cons _ _ _ he
      have hbuf : st.fp.buf = T.B := hg.2.1
      have hstep := readObj_step (cfgOf T aware) k ref st tok tail rest hs hp (by rw [hbuf]; exact hd)
      have hd1 : T.B.drop (T.offsets.getD ref 0 + 1) = tail ++ rest :=
        drop_succ_of T.B _ tok (tail ++ rest) (by simpa using hd)
      obtain ⟨fp, hfp, htok⟩ := readToken_canon (cfgOf T aware) k ref st T.os[ref] T.B
        (T.offsets.getD ref 0 + 1) tok tail rest (by omega) hbf hwf he hel hd1
      rw [hbuf] at hstep
      simp only [show (cfgOf T aware).offsets = T.offsets from rfl] at hstep
      rw [hstep, htok]
      have hos : T.os[ref]? = some T.os[ref] := by simp [hr]
      have IH : ∀ x (st : PState) (P : List Nat), Good T P st → x < T.os.length → undef st.objs + 5 ≤ k →
          ∃ st', readObj (cfgOf T aware) k x st = .ok st' ∧ Good T P st' ∧ StableExc none st st' ∧
            Defined st' x ∧ undef st'.objs ≤ undef st.objs :=
        fun x st P hg hx hk => readObj_tab T ⟨by assumption, hbf, hTj⟩ aware k x st P hg hx hk
      -- the open slot `ref` while its elements are read
      have hopen : ∀ o0 : Obj, isCont T.os[ref] = true →
          Good T (ref :: P) (({ fp := fp, objs := st.objs } : PState).put ref o0) := by
        intro o0 hco
        obtain ⟨hl, _, hb, hc⟩ := hg
        have hl' : ref < st.objs.length := lt_of_getElem?_some hs
        have hdef : ∀ x, Defined st x → Defined (({ fp := fp, objs := st.objs } : PState).put ref o0) x := by
          intro x ⟨o', ho'⟩
          by_cases hx : x = ref
          · subst hx; exact ⟨o0, put_get_self _ _ _ (by simpa using hl')⟩
          · exact ⟨o', by rw [put_get_ne _ _ _ _ hx]; exact ho'⟩
        refine ⟨by simp [PState.put, hl], hfp, ?_, ?_⟩
        · intro j o' hj hjP
          have hne : j ≠ ref := fun h => hjP (by simp [h])
          rw [put_get_ne _ _ _ _ hne] at hj
          obtain ⟨h1, h2⟩ := hb j o' hj (fun h => hjP (by simp [h]))
          exact ⟨h1, fun x hx => hdef x (h2 x hx)⟩
        · intro j hj
          simp at hj
          rcases hj with rfl | hj
          · exact ⟨⟨o0, put_get_self _ _ _ (by simpa using hl')⟩, T.os[j], hos, hco⟩
          · obtain ⟨hd', h2⟩ := hc j hj
            exact ⟨hdef j hd', h2⟩
      -- closing the slot: from open to done
      have hclose : ∀ st' : PState, Good T (ref :: P) st' → st'.objs[ref]? = some (some T.os[ref]) →
          (∀ x ∈ children T.os[ref], Defined st' x) → Good T P st' := by
        intro st' hg' hr' hch'
        obtain ⟨hl, hb, hbb, hc⟩ := hg'
        refine ⟨hl, hb, ?_, fun j hj => hc j (by simp [hj])⟩
        intro j o' hj hjP
        by_cases hjr : j = ref
        · subst hjr
          rw [hr'] at hj; cases hj
          exact ⟨hos, hch'⟩
        · exact hbb j o' hj (by simp [hjr, hjP])
      have hstab_open : ∀ (o0 : Obj) (st' : PState),
          StableExc (some ref) (({ fp := fp, objs := st.objs } : PState).put ref o0) st' →
          StableExc none st st' := by
        intro o0 st' hs' j o hj _
        have hjr : j ≠ ref := by intro h; subst h; rw [hs] at hj; cases hj
        exact hs' j o (by rw [put_get_ne _ _ _ _ hjr]; exact hj) (by simp [hjr])
      have hu_put : ∀ o0 : Obj, undef (({ fp := fp, objs := st.objs } : PState).put ref o0).objs + 1 =
          undef st.objs := fun o0 => undef_set_none st.objs ref o0 hs
      by_cases hcont : isCont T.os[ref] = true
      · cases hc : T.os[ref] with
        | arr refs =>
          rw [hc] at hch hos
          simp only [afterToken]
          have hr0 : (({ fp := fp, objs := st.objs } : PState).put ref (.arr [])).objs[ref]? =
              some (some (.arr [])) := put_get_self _ _ _ (by simp; exact lt_of_getElem?_some hs)
          obtain ⟨st', h', hg', hs', hd', hr', hu'⟩ := arrLoop_tab T aware k ref P IH refs []
            _ (hopen (.arr []) hcont) (fun x hx => hch x hx) (by have := hu_put (.arr []); omega) hr0
          refine ⟨st', h', hclose st' hg' (by rw [hc]; simpa using hr') (by rw [hc]; exact hd'),
            hstab_open _ st' hs', ⟨_, hr'⟩, by have := hu_put (.arr []); omega⟩
        | dict items =>
          rw [hc] at hch hos hdk
          simp only [afterToken]
          have hr0 : (({ fp := fp, objs := st.objs } : PState).put ref (.dict [])).objs[ref]? =
              some (some (.dict [])) := put_get_self _ _ _ (by simp; exact lt_of_getElem?_some hs)
          obtain ⟨hstr, hpw⟩ := hdk
          obtain ⟨st', h', hg', hs', hd', hr', hu'⟩ := dictLoop_tab T aware k ref P IH items hstr hpw items []
            _ rfl (hopen (.dict []) hcont)
            (fun q hq => ⟨hch q.1 (by simp [children]; exact Or.inl ⟨q.2, hq⟩),
              hch q.2 (by simp [children]; exact Or.inr ⟨q.1, hq⟩)⟩)
            (by have := hu_put (.dict []); omega) hr0 (by simp)
          refine ⟨st', by simp [catchTypeError, h'], hclose st' hg' (by rw [hc]; exact hr') ?_,
            hstab_open _ st' hs', ⟨_, hr'⟩, by have := hu_put (.dict []); omega⟩
          rw [hc]
          intro x hx
          simp [children] at hx
          rcases hx with ⟨b, hb⟩ | ⟨a, ha⟩
          · exact (hd' _ hb).1
          · exact (hd' _ ha).2
        | _ => rw [hc] at hcont; simp [isCont] at hcont


      · rw [afterToken_leaf _ _ _ _ _ _ (by simpa using hcont)]
        obtain ⟨hg', hs'⟩ := good_put_new T P st ref T.os[ref] fp hg hs hfp hos (by simpa using hcont)
        refine ⟨_, rfl, hg', hs', ⟨_, put_get_self _ _ _ (by simp; exact lt_of_getElem?_some hs)⟩, ?_⟩
        have := hu_put T.os[ref]; omega

end PyLean.TextLibs.Plist
