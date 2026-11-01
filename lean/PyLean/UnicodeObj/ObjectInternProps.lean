import PyLean.UnicodeObj.ObjectIntern

/-!
Properties of interning. Objects are compared by id.
-/

namespace PyLean.UnicodeObj

open PyLean

/-- An interned state of the dict. -/
def DictState (s : InternState) : Prop := s = .mortal ∨ s = .immortal

/-- How the tables of the runtime fit together. The dict holds exact strings under their own text,
every string marked interned in the dict is there, the dict and the static tables do not overlap,
and an id from `next` on has not been used. -/
structure WOK (W : IWorld) : Prop where
  d1 : ∀ t i, W.dict t = some i → (W.objs i).text = t ∧ (W.objs i).isStr = true ∧
    (W.objs i).exact = true ∧ DictState (W.objs i).state
  d2 : ∀ i, DictState (W.objs i).state → W.dict (W.objs i).text = some i
  d3 : ∀ t i, W.dict t = some i → latin1Of t = none
  dc : ∀ t i, W.dict t = some i → W.cache t = none
  c1 : ∀ t i, W.cache t = some i → (W.objs i).text = t ∧ (W.objs i).isStr = true ∧
    (W.objs i).exact = true ∧ (W.objs i).state = .static
  l1 : ∀ c, c < 256 → (W.objs (W.latin1 c)).text = [c] ∧ (W.objs (W.latin1 c)).isStr = true ∧
    (W.objs (W.latin1 c)).exact = true ∧ (W.objs (W.latin1 c)).state = .static
  s1 : ∀ i, (W.objs i).state = .static →
    (∃ c, latin1Of (W.objs i).text = some c ∧ W.latin1 c = i) ∨
      (latin1Of (W.objs i).text = none ∧ W.cache (W.objs i).text = some i)
  e1 : W.cache [] = some W.empty
  fr : ∀ i, W.next ≤ i → (W.objs i).state = .none

theorem latin1Of_some {t : Str} {c : Nat} (h : latin1Of t = some c) : c < 256 ∧ t = [c] := by
  unfold latin1Of at h
  split at h
  · split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact ⟨by assumption, rfl⟩
    · simp at h
  · simp at h

theorem latin1Of_single {c : Nat} (h : c < 256) : latin1Of [c] = some c := by
  simp [latin1Of, h]

/-- Where an equal string ends up. -/
def canonOf (W : IWorld) (t : Str) : Option ObjId :=
  match latin1Of t with
  | some c => some (W.latin1 c)
  | none =>
    match W.cache t with
    | some r => some r
    | none => W.dict t

theorem WOK.immortalize {W : IWorld} (h : WOK W) {t : ObjId} (ht : DictState (W.objs t).state) :
    WOK (immortalizeInterned W t) := by
  have ho : ∀ i, (immortalizeInterned W t).objs i =
      if i = t then { W.objs t with immortal := true, state := .immortal } else W.objs i := fun _ => rfl
  have hne : ∀ i, (W.objs i).state = .static → i ≠ t := by
    intro i hi e
    subst e
    rcases ht with e | e <;> simp [hi] at e
  refine ⟨?_, ?_, h.d3, h.dc, ?_, ?_, ?_, h.e1, ?_⟩
  · intro k i hd
    obtain ⟨a, b, c, d⟩ := h.d1 k i hd
    show ((immortalizeInterned W t).objs i).text = k ∧ _
    rw [ho]
    by_cases e : i = t
    · subst e
      simp only [if_true]
      exact ⟨a, b, c, .inr rfl⟩
    · simp only [if_neg e]
      exact ⟨a, b, c, d⟩
  · intro i hi
    rw [ho] at hi ⊢
    by_cases e : i = t
    · subst e
      simp only [if_true]
      exact h.d2 _ ht
    · simp only [if_neg e] at hi ⊢
      exact h.d2 _ hi
  · intro k i hd
    obtain ⟨a, b, c, d⟩ := h.c1 k i hd
    rw [ho, if_neg (hne i d)]
    exact ⟨a, b, c, d⟩
  · intro c hc
    obtain ⟨a, b, x, d⟩ := h.l1 c hc
    have : (immortalizeInterned W t).latin1 c = W.latin1 c := rfl
    rw [this, ho, if_neg (hne _ d)]
    exact ⟨a, b, x, d⟩
  · intro i hi
    rw [ho] at hi ⊢
    by_cases e : i = t
    · rw [if_pos e] at hi
      simp at hi
    · simp only [if_neg e] at hi ⊢
      exact h.s1 i hi
  · intro i hi
    have hf := h.fr i hi
    rw [ho]
    by_cases e : i = t
    · subst e
      rcases ht with e | e <;> simp [hf] at e
    · simp only [if_neg e]
      exact hf

/-- The step that adds a new string to the dict. -/
theorem WOK.insert {W : IWorld} (h : WOK W) {s : ObjId} (hn : (W.objs s).state = .none)
    (hs : (W.objs s).isStr = true) (he : (W.objs s).exact = true)
    (hl : latin1Of (W.objs s).text = none) (hc : W.cache (W.objs s).text = none)
    (hd : W.dict (W.objs s).text = none) (hlt : s < W.next) :
    WOK (({ W with dict := fun k => if k = (W.objs s).text then some s else W.dict k } : IWorld).setObj s
      { W.objs s with state := .mortal }) := by
  generalize hW : (({ W with dict := fun k => if k = (W.objs s).text then some s else W.dict k } : IWorld).setObj s
      { W.objs s with state := .mortal }) = V
  have ho : ∀ i, V.objs i = if i = s then { W.objs s with state := .mortal } else W.objs i := by
    intro i
    rw [← hW]
    rfl
  have hdict : ∀ k, V.dict k = if k = (W.objs s).text then some s else W.dict k := by
    intro k
    rw [← hW]
    rfl
  have hcache : V.cache = W.cache := by rw [← hW]; rfl
  have hlat : V.latin1 = W.latin1 := by rw [← hW]; rfl
  have hemp : V.empty = W.empty := by rw [← hW]; rfl
  have hnext : V.next = W.next := by rw [← hW]; rfl
  have hstat : ∀ i, (W.objs i).state = .static → i ≠ s := by
    intro i hi e
    subst e
    simp [hn] at hi
  have hdk : ∀ k i, W.dict k = some i → i ≠ s := by
    intro k i hi e
    subst e
    rcases (h.d1 k _ hi).2.2.2 with e | e <;> simp [hn] at e
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k i hq
    rw [hdict] at hq
    split at hq
    · next ek =>
      simp only [Option.some.injEq] at hq
      subst hq
      rw [ho]
      simp only [if_true]
      exact ⟨ek.symm, hs, he, .inl rfl⟩
    · obtain ⟨a, b, c, d⟩ := h.d1 k i hq
      rw [ho, if_neg (hdk k i hq)]
      exact ⟨a, b, c, d⟩
  · intro i hi
    rw [ho] at hi ⊢
    by_cases e : i = s
    · subst e
      simp only [if_true]
      rw [hdict]
      simp
    · simp only [if_neg e] at hi ⊢
      rw [hdict]
      have hq := h.d2 i hi
      rw [if_neg]
      · exact hq
      · intro ek
        rw [ek, hd] at hq
        simp at hq
  · intro k i hq
    rw [hdict] at hq
    split at hq
    · next ek => rw [ek]; exact hl
    · exact h.d3 k i hq
  · intro k i hq
    rw [hdict] at hq
    rw [hcache]
    split at hq
    · next ek => rw [ek]; exact hc
    · exact h.dc k i hq
  · intro k i hq
    rw [hcache] at hq
    obtain ⟨a, b, c, d⟩ := h.c1 k i hq
    rw [ho, if_neg (hstat i d)]
    exact ⟨a, b, c, d⟩
  · intro c hc'
    obtain ⟨a, b, x, d⟩ := h.l1 c hc'
    rw [hlat, ho, if_neg (hstat _ d)]
    exact ⟨a, b, x, d⟩
  · intro i hi
    rw [ho] at hi ⊢
    by_cases e : i = s
    · rw [if_pos e] at hi
      simp at hi
    · simp only [if_neg e] at hi ⊢
      rw [hlat, hcache]
      exact h.s1 i hi
  · rw [hcache, hemp]
    exact h.e1
  · intro i hi
    rw [hnext] at hi
    rw [ho]
    have hf := h.fr i hi
    by_cases e : i = s
    · subst e
      exact absurd hi (Nat.not_le.2 hlt)
    · simp only [if_neg e]
      exact hf

/-- The result, when the object is an exact `str` in the state `none`. -/
theorem intern_none {W : IWorld} {s : ObjId} {imm : Bool} (hs : (W.objs s).isStr = true)
    (he : (W.objs s).exact = true) (hn : (W.objs s).state = .none) :
    internCommon W s imm =
      match latin1Of (W.objs s).text with
      | some c => (W, W.latin1 c)
      | none =>
        match W.cache (W.objs s).text with
        | some r => (W, r)
        | none =>
          match W.dict (W.objs s).text with
          | some t =>
            (if (imm || (W.objs s).immortal) && ((W.objs t).state == .mortal)
              then immortalizeInterned W t else W, t)
          | none =>
            let W1 : IWorld :=
              { W with dict := fun k => if k = (W.objs s).text then some s else W.dict k }
            let W2 := W1.setObj s { W.objs s with state := .mortal }
            (if (imm || (W.objs s).immortal) then immortalizeInterned W2 s else W2, s) := by
  unfold internCommon
  simp only [hs, he, hn, Bool.not_true, Bool.false_eq_true, if_false]
  rfl

theorem intern_skip {W : IWorld} {s : ObjId} {imm : Bool}
    (h : (W.objs s).isStr = false ∨ (W.objs s).exact = false) : internCommon W s imm = (W, s) := by
  unfold internCommon
  rcases h with h | h
  · simp [h]
  · simp only [h, Bool.not_false, if_true]
    split <;> rfl

theorem intern_done {W : IWorld} {s : ObjId} {imm : Bool} (hs : (W.objs s).isStr = true)
    (he : (W.objs s).exact = true)
    (h : (W.objs s).state = .static ∨ (W.objs s).state = .immortal) : internCommon W s imm = (W, s) := by
  unfold internCommon
  rcases h with h | h <;> simp [hs, he, h]

theorem intern_mortal {W : IWorld} {s : ObjId} {imm : Bool} (hs : (W.objs s).isStr = true)
    (he : (W.objs s).exact = true) (h : (W.objs s).state = .mortal) :
    internCommon W s imm = (if imm then immortalizeInterned W s else W, s) := by
  unfold internCommon
  simp [hs, he, h]

theorem immortalize_objs (W : IWorld) (t i : ObjId) :
    (immortalizeInterned W t).objs i =
      if i = t then { W.objs t with immortal := true, state := .immortal } else W.objs i := rfl

/-- What every step keeps: the text, and what kind of object it is. -/
def SameObjs (W V : IWorld) : Prop :=
  ∀ i, (V.objs i).text = (W.objs i).text ∧ (V.objs i).isStr = (W.objs i).isStr ∧
    (V.objs i).exact = (W.objs i).exact

theorem same_immortalize (W : IWorld) (t : ObjId) : SameObjs W (immortalizeInterned W t) := by
  intro i
  rw [immortalize_objs]
  by_cases e : i = t
  · subst e
    simp
  · simp [e]

/-- `internCommon` on an exact `str`: the table it ended in, and what the tables now say. -/
structure InternOut (W V : IWorld) (s r : ObjId) (imm : Bool) : Prop where
  ok : WOK V
  same : SameObjs W V
  text : (V.objs r).text = (W.objs s).text
  str : (V.objs r).isStr = true
  exact : (V.objs r).exact = true
  interned : (V.objs r).state ≠ .none
  strong : imm = true → (V.objs r).state ≠ .mortal
  canon : canonOf V (W.objs s).text = some r

theorem canon_dict {W : IWorld} (h : WOK W) {t : Str} {i : ObjId} (hd : W.dict t = some i) :
    canonOf W t = some i := by
  unfold canonOf
  rw [h.d3 t i hd, h.dc t i hd, hd]

theorem intern_out {W : IWorld} (h : WOK W) {s : ObjId} (imm : Bool) (hlt : s < W.next)
    (hs : (W.objs s).isStr = true) (he : (W.objs s).exact = true) :
    InternOut W (internCommon W s imm).1 s (internCommon W s imm).2 imm := by
  cases hst : (W.objs s).state with
  | none =>
    rw [intern_none hs he hst]
    cases hl : latin1Of (W.objs s).text with
    | some c =>
      obtain ⟨hc, ht⟩ := latin1Of_some hl
      obtain ⟨a, b, x, d⟩ := h.l1 c hc
      refine ⟨h, fun _ => ⟨rfl, rfl, rfl⟩, by rw [a, ht], b, x, by simp [d], by simp [d], ?_⟩
      unfold canonOf
      rw [hl]
    | none =>
      simp only [hl]
      cases hc : W.cache (W.objs s).text with
      | some r =>
        obtain ⟨a, b, x, d⟩ := h.c1 _ r hc
        refine ⟨h, fun _ => ⟨rfl, rfl, rfl⟩, a, b, x, by simp [d], by simp [d], ?_⟩
        unfold canonOf
        rw [hl, hc]
      | none =>
        simp only [hc]
        cases hd : W.dict (W.objs s).text with
        | some t =>
          simp only [hd]
          obtain ⟨a, b, x, d⟩ := h.d1 _ t hd
          split
          · next hq =>
            have hm : (W.objs t).state = .mortal := by
              simp only [Bool.and_eq_true, beq_iff_eq] at hq
              exact hq.2
            have ok := h.immortalize d
            have hs2 := same_immortalize W t
            refine ⟨ok, hs2, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · rw [(hs2 t).1, a]
            · rw [(hs2 t).2.1, b]
            · rw [(hs2 t).2.2, x]
            · rw [immortalize_objs, if_pos rfl]
              simp
            · intro _
              rw [immortalize_objs, if_pos rfl]
              simp
            · have : (immortalizeInterned W t).dict (W.objs s).text = some t := hd
              exact canon_dict ok this
          · next hq =>
            refine ⟨h, fun _ => ⟨rfl, rfl, rfl⟩, a, b, x, ?_, ?_, canon_dict h hd⟩
            · rcases d with d | d <;> simp [d]
            · intro hi
              rcases d with d | d
              · exfalso
                apply hq
                simp [hi, d]
              · simp [d]
        | none =>
          simp only [hd]
          have ok := h.insert hst hs he hl hc hd hlt
          generalize hV : (({ W with dict := fun k => if k = (W.objs s).text then some s else W.dict k } :
            IWorld).setObj s { W.objs s with state := .mortal }) = V at ok ⊢
          have hso : V.objs s = { W.objs s with state := .mortal } := by
            rw [← hV]
            simp [IWorld.setObj]
          have hsame : SameObjs W V := by
            intro i
            rw [← hV]
            by_cases e : i = s
            · subst e
              simp [IWorld.setObj]
            · simp [IWorld.setObj, e]
          have hdv : V.dict (W.objs s).text = some s := by
            rw [← hV]
            simp [IWorld.setObj]
          have hcn := canon_dict ok hdv
          split
          · have hd2 : DictState (V.objs s).state := by
              rw [hso]
              exact .inl rfl
            have ok2 := ok.immortalize hd2
            have hs2 := same_immortalize V s
            refine ⟨ok2, fun i => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · exact ⟨(hs2 i).1.trans (hsame i).1, (hs2 i).2.1.trans (hsame i).2.1,
                (hs2 i).2.2.trans (hsame i).2.2⟩
            · rw [(hs2 s).1, (hsame s).1]
            · rw [(hs2 s).2.1, (hsame s).2.1, hs]
            · rw [(hs2 s).2.2, (hsame s).2.2, he]
            · rw [immortalize_objs, if_pos rfl]
              simp
            · intro _
              rw [immortalize_objs, if_pos rfl]
              simp
            · have : (immortalizeInterned V s).dict (W.objs s).text = some s := hdv
              exact canon_dict ok2 this
          · next hq =>
            refine ⟨ok, hsame, (hsame s).1, ?_, ?_, ?_, ?_, hcn⟩
            · rw [(hsame s).2.1, hs]
            · rw [(hsame s).2.2, he]
            · rw [hso]
              simp
            · intro hi
              exfalso
              apply hq
              simp [hi]
  | mortal =>
    rw [intern_mortal hs he hst]
    have hdict := h.d2 s (.inl hst)
    split
    · next hi =>
      have ok := h.immortalize (t := s) (.inl hst)
      have hs2 := same_immortalize W s
      refine ⟨ok, hs2, (hs2 s).1, ?_, ?_, ?_, ?_, ?_⟩
      · rw [(hs2 s).2.1, hs]
      · rw [(hs2 s).2.2, he]
      · rw [immortalize_objs, if_pos rfl]
        simp
      · intro _
        rw [immortalize_objs, if_pos rfl]
        simp
      · have : (immortalizeInterned W s).dict (W.objs s).text = some s := hdict
        exact canon_dict ok this
    · next hi =>
      exact ⟨h, fun _ => ⟨rfl, rfl, rfl⟩, rfl, hs, he, by simp [hst], fun e => absurd e hi,
        canon_dict h hdict⟩
  | immortal =>
    rw [intern_done hs he (.inr hst)]
    exact ⟨h, fun _ => ⟨rfl, rfl, rfl⟩, rfl, hs, he, by simp [hst], by simp [hst],
      canon_dict h (h.d2 s (.inr hst))⟩
  | static =>
    rw [intern_done hs he (.inl hst)]
    refine ⟨h, fun _ => ⟨rfl, rfl, rfl⟩, rfl, hs, he, by simp [hst], by simp [hst], ?_⟩
    unfold canonOf
    rcases h.s1 s hst with ⟨c, h1, h2⟩ | ⟨h1, h2⟩
    · simp [h1, h2]
    · simp [h1, h2]

/-- `canonOf` decides the result for an object not yet interned, whatever its id. -/
theorem intern_canon {W : IWorld} (h : WOK W) {s r : ObjId} (imm : Bool) (hlt : s < W.next)
    (hs : (W.objs s).isStr = true) (he : (W.objs s).exact = true)
    (hc : canonOf W (W.objs s).text = some r) : (internCommon W s imm).2 = r := by
  cases hst : (W.objs s).state with
  | none =>
    rw [intern_none hs he hst]
    unfold canonOf at hc
    cases hl : latin1Of (W.objs s).text with
    | some c =>
      rw [hl] at hc
      simpa using hc
    | none =>
      rw [hl] at hc
      simp only [hl]
      cases hq : W.cache (W.objs s).text with
      | some x =>
        rw [hq] at hc
        simpa using hc
      | none =>
        rw [hq] at hc
        simp only [hc]
  | mortal =>
    rw [intern_mortal hs he hst]
    have := canon_dict h (h.d2 s (.inl hst))
    rw [this] at hc
    simpa using hc
  | immortal =>
    rw [intern_done hs he (.inr hst)]
    have := canon_dict h (h.d2 s (.inr hst))
    rw [this] at hc
    simpa using hc
  | static =>
    rw [intern_done hs he (.inl hst)]
    unfold canonOf at hc
    rcases h.s1 s hst with ⟨c, h1, h2⟩ | ⟨h1, h2⟩
    · simp only [h1, h2, Option.some.injEq] at hc
      exact hc
    · simp only [h1, h2, Option.some.injEq] at hc
      exact hc

theorem intern_next (W : IWorld) (s : ObjId) (imm : Bool) :
    (internCommon W s imm).1.next = W.next := by
  unfold internCommon
  dsimp only
  repeat' split
  all_goals rfl

/-- `sys.intern(a) is sys.intern(b)` when `a == b`: for every two exact strings of equal text, in
any state and any world the runtime can be in, mortal or immortal, the second call returns the
object of the first. The objects are compared by id. An identity function fails this. -/
def InternCanonical : Prop :=
  ∀ (W : IWorld) (a b : ObjId) (imm1 imm2 : Bool), WOK W → a < W.next → b < W.next →
    (W.objs a).isStr = true → (W.objs a).exact = true →
    (W.objs b).isStr = true → (W.objs b).exact = true → (W.objs a).text = (W.objs b).text →
    (internCommon (internCommon W a imm1).1 b imm2).2 = (internCommon W a imm1).2

theorem internCanonical_proven : InternCanonical := by
  intro W a b i1 i2 h ha hb s1 e1 s2 e2 ht
  have o := intern_out h i1 ha s1 e1
  have hnx : b < (internCommon W a i1).1.next := by
    rw [intern_next]
    exact hb
  exact intern_canon o.ok i2 hnx (by rw [(o.same b).2.1, s2]) (by rw [(o.same b).2.2, e2])
    (by rw [(o.same b).1, ← ht]; exact o.canon)

/-- What interning does to one object, for every object and every world: it keeps the tables
consistent and every object's text, it returns an object of the same text, it leaves a non-`str`
and an instance of a subclass alone, and what it returns from an exact `str` is interned, and not
mortal if immortality was asked for. Always returning one object fails the text. -/
def InternSpec : Prop :=
  ∀ (W : IWorld) (s : ObjId) (imm : Bool), WOK W → s < W.next →
    WOK (internCommon W s imm).1 ∧ SameObjs W (internCommon W s imm).1 ∧
    ((internCommon W s imm).1.objs (internCommon W s imm).2).text = (W.objs s).text ∧
    (((W.objs s).isStr = false ∨ (W.objs s).exact = false) → internCommon W s imm = (W, s)) ∧
    ((W.objs s).isStr = true → (W.objs s).exact = true →
      ((internCommon W s imm).1.objs (internCommon W s imm).2).state ≠ .none ∧
      (imm = true → ((internCommon W s imm).1.objs (internCommon W s imm).2).state ≠ .mortal))

theorem internSpec_proven : InternSpec := by
  intro W s imm h hlt
  by_cases hk : (W.objs s).isStr = false ∨ (W.objs s).exact = false
  · rw [intern_skip hk]
    exact ⟨h, fun _ => ⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, fun a b => by
      rcases hk with e | e
      · rw [a] at e
        simp at e
      · rw [b] at e
        simp at e⟩
  · have hs : (W.objs s).isStr = true := by
      cases e : (W.objs s).isStr with
      | true => rfl
      | false => exact absurd (.inl e) hk
    have he : (W.objs s).exact = true := by
      cases e : (W.objs s).exact with
      | true => rfl
      | false => exact absurd (.inr e) hk
    have o := intern_out h imm hlt hs he
    exact ⟨o.ok, o.same, o.text, fun x => absurd x hk, fun _ _ => ⟨o.interned, o.strong⟩⟩

/-- Interning what interning returned changes nothing. -/
def InternIdempotent : Prop :=
  ∀ (W : IWorld) (s : ObjId) (imm : Bool), WOK W → s < W.next →
    (W.objs s).isStr = true → (W.objs s).exact = true →
    internCommon (internCommon W s imm).1 (internCommon W s imm).2 imm = internCommon W s imm

theorem internIdempotent_proven : InternIdempotent := by
  intro W s imm h hlt hs he
  have o := intern_out h imm hlt hs he
  generalize hq : internCommon W s imm = q at o ⊢
  obtain ⟨V, r⟩ := q
  simp only at o ⊢
  cases hst : (V.objs r).state with
  | none => exact absurd hst o.interned
  | mortal =>
    rw [intern_mortal o.str o.exact hst]
    cases imm with
    | true => exact absurd hst (o.strong rfl)
    | false => rfl
  | immortal => exact intern_done o.str o.exact (.inr hst)
  | static => exact intern_done o.str o.exact (.inl hst)

/-- The difference between the two entry points, through them: `PyUnicode_InternInPlace` makes a
new interned string mortal, `PyUnicode_InternImmortal` makes it immortal, and asking for immortality
promotes what the dict already holds, while the mortal call leaves it. A wrapper with the flag
swapped, or an `intern_common` that ignores it, fails this. -/
def InternMortality : Prop :=
  ∀ (W : IWorld) (s i : ObjId), WOK W → s < W.next → (W.objs s).isStr = true →
    (W.objs s).exact = true → (W.objs s).state = .none → (W.objs s).immortal = false →
    latin1Of (W.objs s).text = none → W.cache (W.objs s).text = none →
    (W.dict (W.objs s).text = none →
      (internMortal W s).2 = s ∧ ((internMortal W s).1.objs s).state = .mortal ∧
        ((internMortal W s).1.objs s).immortal = false ∧
      (internImmortal W s).2 = s ∧ ((internImmortal W s).1.objs s).state = .immortal ∧
        ((internImmortal W s).1.objs s).immortal = true) ∧
    (W.dict (W.objs s).text = some i → (W.objs i).state = .mortal →
      (internMortal W s).2 = i ∧ ((internMortal W s).1.objs i).state = .mortal ∧
      (internImmortal W s).2 = i ∧ ((internImmortal W s).1.objs i).state = .immortal ∧
        ((internImmortal W s).1.objs i).immortal = true)

theorem internMortality_proven : InternMortality := by
  intro W s i h hlt hs he hn hi hl hc
  constructor
  · intro hd
    have hsv : ∀ (x : UObj), (((({ W with dict := fun k => if k = (W.objs s).text then some s else W.dict k } :
        IWorld).setObj s x).objs s) = x) := by
      intro x
      simp [IWorld.setObj]
    unfold internMortal internImmortal
    rw [intern_none hs he hn, intern_none hs he hn]
    simp only [hl, hc, hd, hi, Bool.or_false, Bool.false_eq_true, if_false, Bool.true_or, if_true]
    simp [IWorld.setObj, immortalizeInterned, hi]
  · intro hd hm
    unfold internMortal internImmortal
    rw [intern_none hs he hn, intern_none hs he hn]
    simp only [hl, hc, hd, hi, hm, Bool.or_false, Bool.false_and, Bool.false_eq_true, if_false,
      Bool.true_or, Bool.true_and, beq_self_eq_true, if_true]
    simp [immortalizeInterned, IWorld.setObj]

theorem lt_next {W : IWorld} (h : WOK W) {i : ObjId} (hs : (W.objs i).state ≠ .none) : i < W.next := by
  apply Nat.lt_of_not_le
  intro hi
  exact hs (h.fr i hi)

/-- A new object is not in any table. -/
theorem WOK.alloc {W : IWorld} (h : WOK W) (o : UObj) (ho : o.state = .none) :
    WOK { W.setObj W.next o with next := W.next + 1 } := by
  have hobj : ∀ i, ({ W.setObj W.next o with next := W.next + 1 } : IWorld).objs i =
      if i = W.next then o else W.objs i := fun _ => rfl
  have hold : ∀ i, (W.objs i).state ≠ .none → i ≠ W.next := fun i hi => Nat.ne_of_lt (lt_next h hi)
  refine ⟨?_, ?_, h.d3, h.dc, ?_, ?_, ?_, h.e1, ?_⟩
  · intro k i hd
    obtain ⟨a, b, c, d⟩ := h.d1 k i hd
    have : (W.objs i).state ≠ .none := by rcases d with e | e <;> simp [e]
    rw [hobj, if_neg (hold i this)]
    exact ⟨a, b, c, d⟩
  · intro i hi
    rw [hobj] at hi ⊢
    by_cases e : i = W.next
    · rw [if_pos e, ho] at hi
      rcases hi with x | x <;> simp at x
    · simp only [if_neg e] at hi ⊢
      exact h.d2 i hi
  · intro k i hd
    obtain ⟨a, b, c, d⟩ := h.c1 k i hd
    rw [hobj, if_neg (hold i (by simp [d]))]
    exact ⟨a, b, c, d⟩
  · intro c hc
    obtain ⟨a, b, x, d⟩ := h.l1 c hc
    have e : ({ W.setObj W.next o with next := W.next + 1 } : IWorld).latin1 c = W.latin1 c := rfl
    rw [e, hobj, if_neg (hold _ (by simp [d]))]
    exact ⟨a, b, x, d⟩
  · intro i hi
    rw [hobj] at hi ⊢
    by_cases e : i = W.next
    · rw [if_pos e, ho] at hi
      simp at hi
    · simp only [if_neg e] at hi ⊢
      exact h.s1 i hi
  · intro i hi
    have hi' : W.next + 1 ≤ i := hi
    rw [hobj, if_neg (by
      intro e
      rw [e] at hi'
      exact Nat.lt_irrefl _ hi')]
    exact h.fr i (Nat.le_of_succ_le hi')

/-- What `newStr` gives. -/
structure NewOut (W V : IWorld) (t : Str) (r : ObjId) : Prop where
  ok : WOK V
  lt : r < V.next
  text : (V.objs r).text = t
  str : (V.objs r).isStr = true
  exact : (V.objs r).exact = true
  canon : ∀ k, canonOf V k = canonOf W k

theorem newStr_out {W : IWorld} (h : WOK W) (t : Str) :
    NewOut W (newStr W t).1 t (newStr W t).2 := by
  unfold newStr
  cases hl : latin1Of t with
  | some c =>
    obtain ⟨hc, ht⟩ := latin1Of_some hl
    obtain ⟨a, b, x, d⟩ := h.l1 c hc
    exact ⟨h, lt_next h (by simp [d]), by rw [a, ht], b, x, fun _ => rfl⟩
  | none =>
    dsimp only
    split
    · next he =>
      have e : t = [] := List.isEmpty_iff.1 he
      obtain ⟨a, b, x, d⟩ := h.c1 _ _ h.e1
      exact ⟨h, lt_next h (by simp [d]), by rw [a, e], b, x, fun _ => rfl⟩
    · have ok := h.alloc { text := t } rfl
      refine ⟨ok, Nat.lt_succ_self _, ?_, ?_, ?_, fun _ => rfl⟩
      · show (if W.next = W.next then ({ text := t } : UObj) else W.objs W.next).text = t
        simp
      · show (if W.next = W.next then ({ text := t } : UObj) else W.objs W.next).isStr = true
        simp
      · show (if W.next = W.next then ({ text := t } : UObj) else W.objs W.next).exact = true
        simp

/-- `PyUnicode_InternFromString`: it raises what the strict decode raises, and otherwise gives an
interned string of the decoded text, the same object each time it is called with these bytes. -/
def InternFromStringSpec : Prop :=
  ∀ (W : IWorld) (b : Bytes), WOK W →
    match utf8Decode b .strict with
    | .error e => internFromString W b = .error e
    | .ok t => ∃ V r, internFromString W b = .ok (V, r) ∧ WOK V ∧ (V.objs r).text = t ∧
        (V.objs r).state ≠ .none ∧ ∃ V2, internFromString V b = .ok (V2, r)

theorem internFromStringSpec_proven : InternFromStringSpec := by
  intro W b h
  unfold internFromString
  cases hd : utf8Decode b .strict with
  | error e => rfl
  | ok t =>
    simp only
    have n1 := newStr_out h t
    generalize newStr W t = q at n1 ⊢
    obtain ⟨W1, s⟩ := q
    simp only at n1 ⊢
    have o := intern_out n1.ok false n1.lt n1.str n1.exact
    have oc : canonOf (internMortal W1 s).1 t = some (internMortal W1 s).2 := by
      have := o.canon
      rwa [n1.text] at this
    refine ⟨(internMortal W1 s).1, (internMortal W1 s).2, rfl, o.ok, ?_, o.interned, ?_⟩
    · exact o.text.trans n1.text
    · have n2 := newStr_out (W := (internMortal W1 s).1) o.ok t
      generalize hq : newStr (internMortal W1 s).1 t = q at n2 ⊢
      obtain ⟨W2, s2⟩ := q
      simp only at n2 ⊢
      refine ⟨(internMortal W2 s2).1, ?_⟩
      have hr : (internMortal W2 s2).2 = (internMortal W1 s).2 :=
        intern_canon n2.ok false n2.lt n2.str n2.exact (by
          rw [n2.text, n2.canon]
          exact oc)
      rw [← hr]

end PyLean.UnicodeObj
