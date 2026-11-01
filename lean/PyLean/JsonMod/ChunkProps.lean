import PyLean.JsonMod.Chunks
import PyLean.JsonMod.EncTwins

/-!
`iterencode` against `encode`: the chunks of the generators join to the text
`_make_iterencode` gives with `_one_shot`, and the exception is the same.
-/

namespace PyLean.JsonMod

open PyLean

/-- Text concatenation in `ER`. -/
def erThen (a b : ER) : ER :=
  match a with
  | .error e => .error e
  | .ok ta =>
    match b with
    | .error e => .error e
    | .ok tb => .ok (ta ++ tb)

theorem yRes_then (a b : Yield) : yRes (yThen a b) = erThen (yRes a) (yRes b) := by
  obtain ⟨ca, ea⟩ := a
  obtain ⟨cb, eb⟩ := b
  cases ea <;> cases eb <;> simp [yThen, yRes, erThen, List.flatten_append]

theorem yRes_cons (t : PStr) (y : Yield) : yRes (yCons t y) = (yRes y).map (t ++ ·) := by
  obtain ⟨c, e⟩ := y
  cases e <;> simp [yCons, yRes, Except.map]

theorem yRes_one (t : PStr) : yRes (yOne t) = .ok t := by simp [yOne, yRes]
theorem yRes_raise (e : PyExc) : yRes (yRaise e) = .error e := rfl

theorem pyScalar_enc {cfg : ECfg} {x : EVal} {r : ER} (h : pyScalar cfg x = some r) (f lvl : Nat)
    (seen : List Nat) : pyEnc cfg (f + 1) lvl seen x = r := by
  cases x with
  | str s => simp only [pyScalar, Option.some.injEq] at h; subst h; simp [pyEnc]
  | none => simp only [pyScalar, Option.some.injEq] at h; subst h; simp [pyEnc]
  | bool b =>
    cases b <;> simp only [pyScalar, Option.some.injEq] at h <;> subst h <;> simp [pyEnc]
  | int n => simp only [pyScalar, Option.some.injEq] at h; subst h; simp [pyEnc]
  | flt b t => simp only [pyScalar, Option.some.injEq] at h; subst h; simp [pyEnc]
  | list xs => simp [pyScalar] at h
  | dict kvs => simp [pyScalar] at h
  | back k => simp [pyScalar] at h
  | other n t => simp [pyScalar] at h

theorem iterList_join (cfg : ECfg) (f : Nat)
    (ih : ∀ lvl seen v, yRes (pyIter cfg f lvl seen v) = pyEnc cfg f lvl seen v)
    (lvl : Nat) (seen : List Nat) (sep buf : PStr) :
    ∀ (xs : List EVal) (i : Nat), (i ≠ 0 ∨ xs ≠ []) →
    yRes (pyIterList cfg f lvl seen sep buf i xs) =
      (pyEncList cfg f lvl seen sep (decide (i = 0)) xs).map ((if i = 0 then buf else []) ++ ·) := by
  intro xs
  induction xs with
  | nil =>
    intro i h
    rcases h with h | h
    · simp [pyIterList, pyEncList, yRes, Except.map, h]
    · exact absurd rfl h
  | cons x xs ih2 =>
    intro i _
    have rest := ih2 (i + 1) (Or.inl (by omega))
    simp only [Nat.add_one_ne_zero, decide_false, ↓reduceIte] at rest
    have hbuf : (if i ≠ 0 then sep else buf) = (if i = 0 then buf else sep) := by
      by_cases hi : i = 0 <;> simp [hi]
    simp only [pyIterList, pyEncList, yRes_then, rest, hbuf]
    cases f with
    | zero => simp [yRes_raise, erThen, pyEnc, Except.map]
    | succ g =>
      simp only [Nat.add_one_ne_zero, ↓reduceIte]
      cases hs : pyScalar cfg x with
      | none =>
        simp only [yRes_cons, ih]
        cases hx : pyEnc cfg (g + 1) lvl seen x with
        | error e => simp [erThen, Except.map]
        | ok t =>
          cases hr : pyEncList cfg (g + 1) lvl seen sep false xs with
          | error e => simp [erThen, Except.map]
          | ok r => by_cases hi : i = 0 <;> simp [erThen, Except.map, hi]
      | some r =>
        have e := pyScalar_enc hs g lvl seen
        rw [e]
        cases r with
        | error e => simp [yRes_raise, erThen, Except.map]
        | ok t =>
          simp only [yRes_one]
          cases hr : pyEncList cfg (g + 1) lvl seen sep false xs with
          | error e => simp [erThen, Except.map]
          | ok r => by_cases hi : i = 0 <;> simp [erThen, Except.map, hi]

theorem iterItems_join (cfg : ECfg) (f : Nat)
    (ih : ∀ lvl seen v, yRes (pyIter cfg f lvl seen v) = pyEnc cfg f lvl seen v)
    (lvl : Nat) (seen : List Nat) (nl : Option PStr) (sep : PStr) :
    ∀ (items : List (EKey × EVal)) (first : Bool),
    yRes (pyIterItems cfg f lvl seen nl sep first items).1 =
        (pyEncItems cfg f lvl seen nl sep first items).map (·.1) ∧
      (∀ b fst, pyEncItems cfg f lvl seen nl sep first items = .ok (b, fst) →
        (pyIterItems cfg f lvl seen nl sep first items).2 = fst) := by
  intro items
  induction items with
  | nil => intro first; simp [pyIterItems, pyEncItems, yRes, Except.map]
  | cons p xs ih2 =>
    obtain ⟨k, x⟩ := p
    intro first
    simp only [pyIterItems, pyEncItems]
    cases hk : pyKeyStr cfg k with
    | error e => simp [yRaise, yRes, Except.map]
    | ok o =>
      cases o with
      | none => exact ih2 first
      | some ks =>
        have hrest := ih2 false
        simp only
        constructor
        · simp only [yRes_then, ih, hrest.1]
          have hhead : yRes ((if first then nlChunks nl else [sep]) ++ [pyStrEnc cfg ks, cfg.keySep], Option.none) =
              .ok ((if first then nl.getD [] else sep) ++ pyStrEnc cfg ks ++ cfg.keySep) := by
            cases first <;> cases nl <;> simp [yRes, nlChunks]
          rw [hhead]
          cases hx : pyEnc cfg f lvl seen x with
          | error e => simp [erThen, Except.map]
          | ok t =>
            cases hr : pyEncItems cfg f lvl seen nl sep false xs with
            | error e => simp [erThen, Except.map]
            | ok r => obtain ⟨body, fst⟩ := r; simp [erThen, Except.map]
        · intro b fst h
          cases hx : pyEnc cfg f lvl seen x with
          | error e => rw [hx] at h; cases h
          | ok t =>
            rw [hx] at h
            cases hr : pyEncItems cfg f lvl seen nl sep false xs with
            | error e => rw [hr] at h; cases h
            | ok r =>
              obtain ⟨body, fst'⟩ := r
              rw [hr] at h
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              rw [← h.2]
              exact hrest.2 body fst' hr

theorem iter_join (cfg : ECfg) : ∀ (f lvl : Nat) (seen : List Nat) (v : EVal),
    yRes (pyIter cfg f lvl seen v) = pyEnc cfg f lvl seen v := by
  intro f
  induction f with
  | zero => intro lvl seen v; simp [pyIter, pyEnc, yRes_raise]
  | succ f ih =>
    intro lvl seen v
    cases v with
    | str s => simp [pyIter, pyEnc, yRes_one]
    | none => simp [pyIter, pyEnc, yRes_one]
    | bool b => cases b <;> simp [pyIter, pyEnc, yRes_one]
    | int n =>
      simp only [pyIter, pyEnc]
      cases intRepr n <;> simp [yRes_one, yRes_raise]
    | flt b r =>
      simp only [pyIter, pyEnc]
      cases pyFloatStr cfg b r <;> simp [yRes_one, yRes_raise]
    | back k => simp only [pyIter, pyEnc, yRes_raise]
    | other n t =>
      simp only [pyIter, pyEnc]
      split
      · rfl
      · cases cfg.dflt n t with
        | error e => rfl
        | ok v' => exact ih lvl (n :: seen) v'
    | list xs =>
      simp only [pyIter, pyEnc]
      by_cases hx : xs = []
      · subst hx; simp [yRes_one]
      · simp only [hx, ↓reduceIte]
        have hl := iterList_join cfg f ih
        cases hi : cfg.indent with
        | none =>
          simp only [yRes_then]
          rw [hl lvl seen _ _ xs 0 (Or.inr hx)]
          cases hb : pyEncList cfg f lvl seen cfg.itemSep true xs with
          | error e => simp [Except.map, erThen, hb]
          | ok b => simp [Except.map, erThen, hb, yRes]
        | some ind =>
          simp only [yRes_then, List.append_assoc]
          generalize cfg.itemSep ++ ([10] ++ rep ind (lvl + 1)) = sep
          rw [hl (lvl + 1) seen _ _ xs 0 (Or.inr hx)]
          simp only [decide_true, ↓reduceIte, Nat.add_sub_cancel, Option.getD_some]
          cases hb : pyEncList cfg f (lvl + 1) seen sep true xs with
          | error e => simp [Except.map, erThen]
          | ok b => simp [Except.map, erThen, yRes]
    | dict kvs =>
      simp only [pyIter, pyEnc]
      by_cases hx : kvs = []
      · subst hx; simp [yRes_one]
      · simp only [hx, ↓reduceIte, yRes_cons]
        have hl := iterItems_join cfg f ih
        cases hi : cfg.indent with
        | none =>
          simp only
          cases hs : (if cfg.sortKeys = true then sortItems kvs else Except.ok kvs) with
          | error e => simp [yRes_raise, Except.map]
          | ok items =>
            have h1 := (hl lvl seen none cfg.itemSep items true).1
            have h2 := (hl lvl seen none cfg.itemSep items true).2
            simp only [yRes_then, h1]
            cases hb : pyEncItems cfg f lvl seen none cfg.itemSep true items with
            | error e => simp [Except.map, erThen]
            | ok r =>
              obtain ⟨body, fst⟩ := r
              simp [Except.map, erThen, yRes]
        | some ind =>
          simp only [List.append_assoc]
          generalize cfg.itemSep ++ ([10] ++ rep ind (lvl + 1)) = sep
          cases hs : (if cfg.sortKeys = true then sortItems kvs else Except.ok kvs) with
          | error e => simp [yRes_raise, Except.map]
          | ok items =>
            have h1 := (hl (lvl + 1) seen (some ([10] ++ rep ind (lvl + 1))) sep items true).1
            have h2 := (hl (lvl + 1) seen (some ([10] ++ rep ind (lvl + 1))) sep items true).2
            simp only [yRes_then, h1]
            cases hb : pyEncItems cfg f (lvl + 1) seen (some ([10] ++ rep ind (lvl + 1))) sep true items with
            | error e => simp [Except.map, erThen]
            | ok r =>
              obtain ⟨body, fst⟩ := r
              have := h2 body fst hb
              simp only [Except.map, erThen, this, Nat.add_sub_cancel]
              cases fst <;> simp [yRes]

/-- The chunks of `JSONEncoder.iterencode` join to the result of `encode` with
the pure-Python encoder, or the generator ends with the same exception. Holds
for every value and every option. -/
def IterencodeJoin : Prop :=
  ∀ (cfg : ECfg) (v : EVal), yRes (iterencode cfg v) = dumpsPy cfg v

theorem iterencodeJoin_proven : IterencodeJoin := by
  intro cfg v
  have h := iter_join cfg (encFuel cfg v) 0 [] v
  unfold iterencode
  rw [h]
  cases v with
  | str s =>
    have : encFuel cfg (.str s) = cfg.dfltDepth + 1 := by simp [encFuel, EVal.depth]; omega
    simp [this, pyEnc, dumpsPy]
  | _ => rfl

theorem writeAll_none (k : Nat) (cs : List PStr) :
    writeAll (fun _ _ => none) k cs = (cs, none) := by
  induction cs generalizing k with
  | nil => rfl
  | cons c cs ih => simp [writeAll, ih]

theorem dumpTo_none (y : Yield) : dumpTo (fun _ _ => none) y = y := by
  simp [dumpTo, writeAll_none]

/-- What a failing `write` leaves: the chunks before it. -/
theorem writeAll_prefix (wr : Nat → PStr → Option PyExc) (k : Nat) (cs : List PStr) :
    (writeAll wr k cs).1 <+: cs := by
  induction cs generalizing k with
  | nil => simp [writeAll]
  | cons c cs ih =>
    simp only [writeAll]
    cases wr k c with
    | some e => simp
    | none => simpa using ih (k + 1)

end PyLean.JsonMod
