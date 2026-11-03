import PyLean.TextLibs.PlistWriteInv

/-! What `_write_object` writes for each object of the list: the canonical bytes of the object the
reader will make of it (`Rel`). -/

namespace PyLean.TextLibs.Plist

open PyLean PyLean.TextLibs

/-- `P` holds between the elements of two lists, pairwise (and they have the same length). -/
inductive Forall2 {α β : Type} (P : α → β → Prop) : List α → List β → Prop
  | nil : Forall2 P [] []
  | cons {a : α} {b : β} {l : List α} {m : List β} : P a b → Forall2 P l m → Forall2 P (a :: l) (b :: m)

/-- The object the reader makes of the bytes `_write_object(c)` writes. -/
def Rel (H : WHeap) (cfg : WCfg) (st : WState) (c : Nat) (o : Obj) : Prop :=
  match H.getD c .none, o with
  | .none, .none => True
  | .bool a, .bool b => a = b
  | .int a, .int b => a = b
  | .float a, .real b => a = b
  | .str a, .str b => a = b
  | .bytes a, .data b => a = b
  | .bytearray a, .data b => a = b
  | .uid a, .uid b => a = b
  | .list xs, .arr rs => Forall2 (fun x r => lookupW H st x = some r) xs rs
  | .tuple xs, .arr rs => Forall2 (fun x r => lookupW H st x = some r) xs rs
  | .dict items, .dict ps => ∃ kept, writtenItems H cfg items = .ok kept ∧
      Forall2 (fun q p => lookupW H st q.1 = some p.1 ∧ lookupW H st q.2 = some p.2) kept ps
  | .fdict items, .dict ps => ∃ kept, writtenItems H cfg items = .ok kept ∧
      Forall2 (fun q p => lookupW H st q.1 = some p.1 ∧ lookupW H st q.2 = some p.2) kept ps
  | _, _ => False

theorem getrefnumR_ok (r : Nat) (H : WHeap) (st : WState) (c n : Nat) (h : getrefnumR r H st c = .ok n) :
    lookupW H st c = some n := by
  cases r with
  | zero => simp [getrefnumR, call] at h
  | succ r =>
    simp only [getrefnumR, call] at h
    unfold lookupW isScalar
    split at h
    · rename_i m hm; cases h; exact hm
    · cases h

theorem mapM_getrefnum (r : Nat) (H : WHeap) (st : WState) :
    ∀ (xs rs : List Nat), xs.mapM (getrefnumR r H st) = .ok rs →
      Forall2 (fun x r => lookupW H st x = some r) xs rs
  | [], rs, h => by simp at h; cases h; exact .nil
  | x :: xs, rs, h => by
    simp only [List.mapM_cons, bind, Except.bind] at h
    cases h1 : getrefnumR r H st x with
    | error e => rw [h1] at h; cases h
    | ok n =>
      rw [h1] at h
      simp only at h
      cases h2 : xs.mapM (getrefnumR r H st) with
      | error e => rw [h2] at h; cases h
      | ok ns =>
        rw [h2] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact .cons (getrefnumR_ok r H st x n h1) (mapM_getrefnum r H st xs ns h2)

theorem mapM_getrefnum_fst (r : Nat) (H : WHeap) (st : WState) (f : Nat × Nat → Nat) :
    ∀ (kept : List (Nat × Nat)) (rs : List Nat), kept.mapM (fun q => getrefnumR r H st (f q)) = .ok rs →
      Forall2 (fun q r => lookupW H st (f q) = some r) kept rs
  | [], rs, h => by simp at h; cases h; exact .nil
  | q :: kept, rs, h => by
    simp only [List.mapM_cons, bind, Except.bind] at h
    cases h1 : getrefnumR r H st (f q) with
    | error e => rw [h1] at h; cases h
    | ok n =>
      rw [h1] at h
      simp only at h
      cases h2 : kept.mapM (fun q => getrefnumR r H st (f q)) with
      | error e => rw [h2] at h; cases h
      | ok ns =>
        rw [h2] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact .cons (getrefnumR_ok r H st (f q) n h1) (mapM_getrefnum_fst r H st f kept ns h2)

theorem mapM_getrefnum_g (r : Nat) (H : WHeap) (st : WState) (f : Nat × Nat → Nat)
    (g : Nat × Nat → Py Nat) (hg : ∀ q, g q = getrefnumR r H st (f q))
    (kept : List (Nat × Nat)) (rs : List Nat) (h : kept.mapM g = .ok rs) :
    Forall2 (fun q r => lookupW H st (f q) = some r) kept rs := by
  have : kept.mapM g = kept.mapM (fun q => getrefnumR r H st (f q)) := by
    congr 1; funext q; exact hg q
  rw [this] at h
  exact mapM_getrefnum_fst r H st f kept rs h

theorem forall2_zip {α : Type} (P : α → Nat → Prop) (Q : α → Nat → Prop) :
    ∀ (l : List α) (a b : List Nat), Forall2 P l a → Forall2 Q l b →
      Forall2 (fun q p => P q p.1 ∧ Q q p.2) l (a.zip b)
  | [], [], [], _, _ => .nil
  | x :: l, y :: a, z :: b, .cons h1 t1, .cons h2 t2 => .cons ⟨h1, h2⟩ (forall2_zip P Q l a b t1 t2)

theorem forall2_length {α β : Type} {P : α → β → Prop} : ∀ {l : List α} {m : List β},
    Forall2 P l m → l.length = m.length
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons _ t => by simp [forall2_length t]

theorem dictItemsR_ok' (r : Nat) (H : WHeap) (cfg : WCfg) (items its : List (Nat × Nat))
    (h : dictItemsR r H cfg items = .ok its) : dictItems H cfg items = .ok its := by
  cases r with
  | zero => simp [dictItemsR, call] at h
  | succ r => simpa [dictItemsR, call] using h

theorem writeSizeR_ok (r : Nat) (t s : Nat) (b : List Nat) (h : writeSizeR r t s = .ok b) :
    b = writeSizeB t s := by
  cases r with
  | zero => simp [writeSizeR, call] at h
  | succ r => simp [writeSizeR, call] at h; exact h.symm

theorem bind_pair_ok {α : Type} (x : Py α) (n : Nat) (ref : Nat) (enc : α)
    (h : (x >>= fun y => (pure (n, y) : Py (Nat × α))) = .ok (ref, enc)) : x = .ok enc ∧ n = ref := by
  cases hx : x with
  | error e => rw [hx] at h; cases h
  | ok y =>
    rw [hx] at h
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨by rw [h.2], h.1⟩

theorem call_ok {α : Type} {r : Nat} {x y : α} (h : (call r fun _ => (.ok x : Py α)) = .ok y) : y = x := by
  cases r with
  | zero => simp [call] at h
  | succ r => simp [call] at h; exact h.symm

theorem uidBytes_spec (d : Int) (enc : List Nat) (r : Nat)
    (h : (if d < 0 then (.error (.valueError "UIDs must be positive") : Py (List Nat))
      else if d < 2 ^ 8 then call r fun _ => .ok [0x80, d.toNat]
      else if d < 2 ^ 16 then call r fun _ => .ok (0x81 :: beBytes d.toNat 2)
      else if d < 2 ^ 32 then call r fun _ => .ok (0x83 :: beBytes d.toNat 4)
      else if d < 2 ^ 64 then call r fun _ => .ok (0x87 :: beBytes d.toNat 8)
      else .error (.overflowError s!"UID({d})")) = .ok enc) :
    uidBytes d.toNat = some enc := by
  unfold uidBytes
  by_cases h0 : d < 0
  · rw [if_pos h0] at h; cases h
  · rw [if_neg h0] at h
    by_cases h1 : d < 2 ^ 8
    · rw [if_pos h1] at h; have := call_ok h; subst this; rw [if_pos (by omega)]
    · rw [if_neg h1] at h; rw [if_neg (by omega)]
      by_cases h2 : d < 2 ^ 16
      · rw [if_pos h2] at h; have := call_ok h; subst this; rw [if_pos (by omega)]
      · rw [if_neg h2] at h; rw [if_neg (by omega)]
        by_cases h3 : d < 2 ^ 32
        · rw [if_pos h3] at h; have := call_ok h; subst this; rw [if_pos (by omega)]
        · rw [if_neg h3] at h; rw [if_neg (by omega)]
          by_cases h4 : d < 2 ^ 64
          · rw [if_pos h4] at h; have := call_ok h; subst this; rw [if_pos (by omega)]
          · rw [if_neg h4] at h; cases h

/-- `_write_object(c)` writes the canonical bytes of an object related to `c`. Datetimes are not
covered. -/
theorem writeObject_spec (r : Nat) (H : WHeap) (cfg : WCfg) (refSize : Nat) (st : WState) (c ref : Nat)
    (enc : List Nat) (hnd : ∀ us off, H.getD c .none ≠ .date us off)
    (h : writeObjectR r H cfg refSize st c = .ok (ref, enc)) :
    lookupW H st c = some ref ∧ ∃ o, canon refSize o = some enc ∧ Rel H cfg st c o := by
  cases r with
  | zero => simp [writeObjectR, call] at h
  | succ r =>
  simp only [writeObjectR, call, bind, Except.bind] at h
  cases hg : getrefnumR r H st c with
  | error e => rw [hg] at h; cases h
  | ok n =>
  rw [hg] at h
  simp only at h
  obtain ⟨hx, rfl⟩ := bind_pair_ok _ n ref enc h
  refine ⟨getrefnumR_ok r H st c n hg, ?_⟩
  unfold Rel
  cases ho : H.getD c .none with
  | none => rw [ho] at hx; cases hx; exact ⟨.none, rfl, trivial⟩
  | bool b => rw [ho] at hx; cases b <;> (cases hx; exact ⟨.bool _, rfl, rfl⟩)
  | int v => rw [ho] at hx; exact ⟨.int v, by simp [canon, hx, Except.toOption], rfl⟩
  | float bits => rw [ho] at hx; cases hx; exact ⟨.real bits, rfl, rfl⟩
  | date us off => exact absurd ho (hnd us off)
  | bytes b =>
    rw [ho] at hx
    try simp only [bind, Except.bind] at hx
    cases hw : writeSizeR r 0x40 b.length with
    | error e => rw [hw] at hx; cases hx
    | ok w => rw [hw] at hx; cases hx; exact ⟨.data b, by simp [canon, writeSizeR_ok r _ _ _ hw], rfl⟩
  | bytearray b =>
    rw [ho] at hx
    try simp only [bind, Except.bind] at hx
    cases hw : writeSizeR r 0x40 b.length with
    | error e => rw [hw] at hx; cases hx
    | ok w => rw [hw] at hx; cases hx; exact ⟨.data b, by simp [canon, writeSizeR_ok r _ _ _ hw], rfl⟩
  | str s =>
    rw [ho] at hx
    try simp only at hx
    refine ⟨.str s, ?_, rfl⟩
    simp only [canon, strBytes]
    cases ha : UnicodeObj.ucs1Encode s 128 .strict (fun _ => none) with
    | ok t =>
      rw [ha] at hx
      try simp only [bind, Except.bind] at hx
      cases hw : writeSizeR r 0x50 s.length with
      | error e => rw [hw] at hx; cases hx
      | ok w => rw [hw] at hx; cases hx; simp [writeSizeR_ok r _ _ _ hw]
    | error e =>
      rw [ha] at hx
      try simp only at hx
      split at hx
      · try simp only [bind, Except.bind] at hx
        cases hu : UnicodeObj.utf16EncodeFull s 1 .strict (fun _ => none) with
        | error e => rw [hu] at hx; cases hx
        | ok t =>
          rw [hu] at hx
          simp only at hx
          cases hw : writeSizeR r 0x60 (t.length / 2) with
          | error e => rw [hw] at hx; cases hx
          | ok w => rw [hw] at hx; cases hx; simp [writeSizeR_ok r _ _ _ hw]
      · cases hx
  | uid d =>
    rw [ho] at hx
    try simp only at hx
    have hd : 0 ≤ d := by
      by_cases hneg : d < 0
      · rw [if_pos hneg] at hx; cases hx
      · omega
    exact ⟨.uid d.toNat, uidBytes_spec d enc r hx, by show d = ((d.toNat : Nat) : Int); omega⟩
  | list xs =>
    rw [ho] at hx
    try simp only [bind, Except.bind] at hx
    cases hm : xs.mapM (getrefnumR r H st) with
    | error e => rw [hm] at hx; cases hx
    | ok refs =>
      rw [hm] at hx
      simp only at hx
      cases hw : writeSizeR r 0xA0 refs.length with
      | error e => rw [hw] at hx; cases hx
      | ok w =>
        rw [hw] at hx; cases hx
        exact ⟨.arr refs, by simp [canon, writeSizeR_ok r _ _ _ hw], mapM_getrefnum r H st xs refs hm⟩
  | tuple xs =>
    rw [ho] at hx
    try simp only [bind, Except.bind] at hx
    cases hm : xs.mapM (getrefnumR r H st) with
    | error e => rw [hm] at hx; cases hx
    | ok refs =>
      rw [hm] at hx
      simp only at hx
      cases hw : writeSizeR r 0xA0 refs.length with
      | error e => rw [hw] at hx; cases hx
      | ok w =>
        rw [hw] at hx; cases hx
        exact ⟨.arr refs, by simp [canon, writeSizeR_ok r _ _ _ hw], mapM_getrefnum r H st xs refs hm⟩
  | dict items | fdict items =>
    rw [ho] at hx
    try simp only at hx
    try simp only [bind, Except.bind] at hx
    cases hdi : dictItemsR r H cfg items with
    | error e => rw [hdi] at hx; cases hx
    | ok its =>
    rw [hdi] at hx
    try simp only at hx
    cases hk : keptItems H cfg.skipkeys its with
    | error e => rw [hk] at hx; cases hx
    | ok kept =>
    rw [hk] at hx
    try simp only at hx
    cases hkr : kept.mapM (fun x => match x with | (k, _) => getrefnumR r H st k) with
    | error e => rw [hkr] at hx; cases hx
    | ok keyRefs =>
    rw [hkr] at hx
    try simp only at hx
    cases hvr : kept.mapM (fun x => match x with | (_, v) => getrefnumR r H st v) with
    | error e => rw [hvr] at hx; cases hx
    | ok valRefs =>
    rw [hvr] at hx
    try simp only at hx
    cases hw : writeSizeR r 0xD0 keyRefs.length with
    | error e => rw [hw] at hx; cases hx
    | ok w =>
    rw [hw] at hx
    cases hx
    have f1 := mapM_getrefnum_g r H st Prod.fst _ (fun q => by rcases q; rfl) kept keyRefs hkr
    have f2 := mapM_getrefnum_g r H st Prod.snd _ (fun q => by rcases q; rfl) kept valRefs hvr
    have l1 := forall2_length f1
    have l2 := forall2_length f2
    refine ⟨.dict (keyRefs.zip valRefs), ?_, kept, ?_, forall2_zip _ _ kept keyRefs valRefs f1 f2⟩
    · simp only [canon, writeSizeR_ok r _ _ _ hw]
      rw [List.length_zip, show (keyRefs.zip valRefs).map (·.1) = keyRefs from
          List.map_fst_zip (by omega),
        show (keyRefs.zip valRefs).map (·.2) = valRefs from List.map_snd_zip (by omega)]
      simp [show min keyRefs.length valRefs.length = keyRefs.length by omega]
    · simp [writtenItems, dictItemsR_ok' r H cfg items its hdi, bind, Except.bind, hk]
  | other s t => rw [ho] at hx; cases hx

end PyLean.TextLibs.Plist
