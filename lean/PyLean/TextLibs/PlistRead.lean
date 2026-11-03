import PyLean.TextLibs.PlistCodec

/-! What `_read_object` does on the bytes `_write_object` writes (`canon`): every token is decoded
to the object it encodes. -/

namespace PyLean.TextLibs.Plist

open PyLean PyLean.TextLibs PyLean.UnicodeObj

/-- The UID branch of `_write_object`, :831-843, for a `UID` whose data is `d`. -/
def uidBytes (d : Nat) : Option (List Nat) :=
  if d < 2 ^ 8 then some [0x80, d]
  else if d < 2 ^ 16 then some (0x81 :: beBytes d 2)
  else if d < 2 ^ 32 then some (0x83 :: beBytes d 4)
  else if d < 2 ^ 64 then some (0x87 :: beBytes d 8)
  else none

/-- The `str` branch of `_write_object`, :821-829. -/
def strBytes (s : List Nat) : Option (List Nat) :=
  match ucs1Encode s 128 .strict (fun _ => none) with
  | .ok t => some (writeSizeB 0x50 s.length ++ t)
  | .error _ =>
    match utf16EncodeFull s 1 .strict (fun _ => none) with
    | .ok t => some (writeSizeB 0x60 (t.length / 2) ++ t)
    | .error _ => none

/-- The bytes `_write_object` writes for an object that reads back as `o`, with references of
`refSize` bytes. A datetime has none here (dates are not covered by the round trip). -/
def canon (refSize : Nat) : Obj → Option (List Nat)
  | .none => some [0x00]
  | .bool b => some [if b then 0x09 else 0x08]
  | .int v => (writeInt v).toOption
  | .real bits => some (0x23 :: beBytes bits 8)
  | .date _ _ => none
  | .data b => some (writeSizeB 0x40 b.length ++ b)
  | .str s => strBytes s
  | .uid d => uidBytes d
  | .arr refs => some (writeSizeB 0xA0 refs.length ++ packRefs refSize refs)
  | .dict items => some (writeSizeB 0xD0 items.length ++ packRefs refSize (items.map (·.1)) ++
      packRefs refSize (items.map (·.2)))

/-- Type invariants the decoding needs: a float is 64 bits, a `str` holds code points, and
references fit in `refSize` bytes. -/
def ObjWf (refSize : Nat) : Obj → Prop
  | .real bits => bits < 2 ^ 64
  | .str s => Str.Valid s
  | .arr refs => ∀ x ∈ refs, x < 256 ^ refSize
  | .dict items => ∀ p ∈ items, p.1 < 256 ^ refSize ∧ p.2 < 256 ^ refSize
  | _ => True

/-- What `_read_object` goes on to do once the bytes of `o` are read: store a leaf, or read the
elements of a container. -/
def afterToken (cfg : PCfg) (k ref : Nat) (st : PState) (fp : FP) : Obj → Py PState
  | .arr refs => arrLoop (fun x st => readObj cfg k x st) ref [] refs
      (({ fp := fp, objs := st.objs } : PState).put ref (.arr []))
  | .dict items => catchTypeError k (dictLoop (fun x st => readObj cfg k x st) ref [] items
      (({ fp := fp, objs := st.objs } : PState).put ref (.dict [])))
  | o => .ok (({ fp := fp, objs := st.objs } : PState).put ref o)

/-! ## The size field -/

theorem lowNibble (H : Nat) (hH : H = 0x40 ∨ H = 0x50 ∨ H = 0x60 ∨ H = 0xA0 ∨ H = 0xD0) :
    ∀ s, s < 15 → (H ||| s) &&& 0xF0 = H ∧ (H ||| s) &&& 0x0F = s := by
  rcases hH with rfl | rfl | rfl | rfl | rfl <;> decide

theorem drop_succ_of (B : List Nat) (p : Nat) (a : Nat) (t : List Nat) (h : B.drop p = a :: t) :
    B.drop (p + 1) = t := by
  rw [← List.drop_drop, h]; rfl

theorem read_one (B : List Nat) (p : Nat) (a : Nat) (t : List Nat) (h : B.drop p = a :: t) :
    FP.read ⟨B, p⟩ 1 = ([a], ⟨B, p + 1⟩) := by
  have := read_prefix B p [a] t (by simpa using h)
  simpa using this

theorem sizeField (H : Nat) (hH : H = 0x40 ∨ H = 0x50 ∨ H = 0x60 ∨ H = 0xA0 ∨ H = 0xD0)
    (size : Nat) (hs : size < 2 ^ 64) :
    ∃ tok ext, writeSizeB H size = tok :: ext ∧ tok &&& 0xF0 = H ∧
      ∀ k B p rest, 1 ≤ k → B.drop p = ext ++ rest →
        getSizeR k ⟨B, p⟩ (tok &&& 0x0F) = .ok (size, ⟨B, p + ext.length⟩) := by
  have hH15 : (H ||| 15) &&& 0xF0 = H ∧ (H ||| 15) &&& 0x0F = 15 := by
    rcases hH with rfl | rfl | rfl | rfl | rfl <;> decide
  by_cases h15 : size < 15
  · refine ⟨H ||| size, [], by simp [writeSizeB, h15], (lowNibble H hH size h15).1, ?_⟩
    intro k B p rest hk _
    obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [(lowNibble H hH size h15).2]
    simp [getSizeR, call, show size ≠ 15 by omega]
  · -- the marker byte, then 1, 2, 4 or 8 bytes
    have key : ∀ (m w : Nat), w = 2 ^ (m &&& 3) → size < 256 ^ w → m &&& 3 < 4 →
        ∀ k B p rest, 1 ≤ k → B.drop p = (m :: beBytes size w) ++ rest →
          getSizeR k ⟨B, p⟩ 15 = .ok (size, ⟨B, p + (m :: beBytes size w).length⟩) := by
      intro m w hw hsz _ k B p rest hk hd
      obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      simp only [getSizeR, call, ↓reduceIte]
      rw [read_one B p m _ (by simpa using hd)]
      dsimp only
      have hd2 : B.drop (p + 1) = beBytes size w ++ rest := drop_succ_of B p m _ (by simpa using hd)
      have hr := read_prefix B (p + 1) (beBytes size w) rest hd2
      rw [beBytes_length] at hr
      rw [← hw, hr]
      simp [beBytes_length, beVal_beBytes w size hsz, Nat.add_assoc, Nat.add_comm 1]
    by_cases h8 : size < 2 ^ 8
    · refine ⟨H ||| 0xF, [0x10, size], by simp [writeSizeB, h15, h8], hH15.1, ?_⟩
      intro k B p rest hk hd
      rw [hH15.2]
      have hb1 : beBytes size 1 = [size] := by simp [beBytes]; omega
      have := key 0x10 1 rfl (by simpa using h8) (by decide) k B p rest hk (by rw [hb1]; simpa using hd)
      rw [hb1] at this
      simpa using this
    · by_cases h16 : size < 2 ^ 16
      · refine ⟨H ||| 0xF, 0x11 :: beBytes size 2, by simp [writeSizeB, h15, h8, h16], hH15.1, ?_⟩
        intro k B p rest hk hd
        rw [hH15.2]
        exact key 0x11 2 rfl (by simpa using h16) (by decide) k B p rest hk hd
      · by_cases h32 : size < 2 ^ 32
        · refine ⟨H ||| 0xF, 0x12 :: beBytes size 4, by simp [writeSizeB, h15, h8, h16, h32], hH15.1, ?_⟩
          intro k B p rest hk hd
          rw [hH15.2]
          exact key 0x12 4 rfl (by simpa using h32) (by decide) k B p rest hk hd
        · refine ⟨H ||| 0xF, 0x13 :: beBytes size 8, by simp [writeSizeB, h15, h8, h16, h32], hH15.1, ?_⟩
          intro k B p rest hk hd
          rw [hH15.2]
          exact key 0x13 8 rfl (by simpa using hs) (by decide) k B p rest hk hd


/-! ## Tokens -/

theorem tokNe (tok H : Nat) (h : tok &&& 0xF0 = H) (hH : H = 0x40 ∨ H = 0x50 ∨ H = 0x60 ∨ H = 0x80 ∨
    H = 0xA0 ∨ H = 0xD0) :
    tok ≠ 0 ∧ tok ≠ 8 ∧ tok ≠ 9 ∧ tok ≠ 15 ∧ tok ≠ 0x22 ∧ tok ≠ 0x23 ∧ tok ≠ 0x33 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (intro he; subst he; rcases hH with rfl | rfl | rfl | rfl | rfl | rfl <;> simp at h)

theorem fromBytes_unsigned (b : List Nat) : fromBytes b false = beVal b := by
  simp [fromBytes]

theorem fromBytes_pos (b : List Nat) (h : beVal b < 2 ^ (8 * b.length - 1)) : fromBytes b true = beVal b := by
  simp only [fromBytes, Bool.true_and]
  split
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    omega
  · rfl

theorem readToken_leafEq (cfg : PCfg) (k ref : Nat) (st : PState) (fp : FP) (o : Obj)
    (h : ∀ refs, o ≠ .arr refs) (h' : ∀ items, o ≠ .dict items) :
    afterToken cfg k ref st fp o = .ok (({ fp := fp, objs := st.objs } : PState).put ref o) := by
  cases o <;> simp_all [afterToken]

theorem nib10 : ∀ L, L < 5 → (0x10 + L) &&& 0xF0 = 0x10 ∧ (0x10 + L) &&& 0x0F = L := by decide

theorem nib80 : ∀ L, L < 8 → (0x80 + L) &&& 0xF0 = 0x80 ∧ (0x80 + L) &&& 0x0F = L := by decide

theorem readToken_int (cfg : PCfg) (k ref : Nat) (st : PState) (v : Int) (B : List Nat) (p tok : Nat)
    (tail rest : List Nat) (he : writeInt v = .ok (tok :: tail)) (hb : B.drop p = tail ++ rest) :
    ∃ fp : FP, fp.buf = B ∧ readToken cfg k (fun x st => readObj cfg k x st) ref st tok ⟨B, p⟩ =
      .ok (({ fp := fp, objs := st.objs } : PState).put ref (.int v)) := by
  have go : ∀ (L : Nat) (signed : Bool), tok = 0x10 + L → L < 5 → tail.length = 2 ^ L →
      signed = decide (L ≥ 3) → fromBytes tail signed = v →
      ∃ fp : FP, fp.buf = B ∧ readToken cfg k (fun x st => readObj cfg k x st) ref st tok ⟨B, p⟩ =
        .ok (({ fp := fp, objs := st.objs } : PState).put ref (.int v)) := by
    intro L signed ht hL hl hs hv
    subst ht
    refine ⟨⟨B, p + tail.length⟩, rfl, ?_⟩
    have hr := read_prefix B p tail rest hb
    have hH := nib10 L hL
    have hn : 0x10 + L ≠ 0 ∧ 0x10 + L ≠ 8 ∧ 0x10 + L ≠ 9 ∧ 0x10 + L ≠ 15 := by omega
    simp only [readToken, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2, hH.1, hH.2, ↓reduceIte]
    rw [← hl, hr, ← hs, hv]
  unfold writeInt at he
  by_cases h0 : v < 0
  · rw [if_pos h0] at he
    by_cases h1 : v ≥ -2 ^ 63
    · rw [if_pos h1] at he
      simp only [Except.ok.injEq, List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have hbv := beVal_beBytes 8 (v + 2 ^ 64).toNat (by omega)
      exact go 3 true rfl (by omega) (by simp [beBytes_length]) rfl (by
        simp only [fromBytes, beBytes_length, hbv, Bool.true_and]
        rw [if_pos (by simp; omega)]
        omega)
    · rw [if_neg h1] at he; cases he
  · rw [if_neg h0] at he
    by_cases h8 : v < 2 ^ 8
    · rw [if_pos h8] at he
      simp only [Except.ok.injEq, List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact go 0 false rfl (by omega) (by simp) rfl (by simp [fromBytes, beVal]; omega)
    · rw [if_neg h8] at he
      by_cases h16 : v < 2 ^ 16
      · rw [if_pos h16] at he
        simp only [Except.ok.injEq, List.cons.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact go 1 false rfl (by omega) (by simp [beBytes_length]) rfl
          (by rw [fromBytes_unsigned, beVal_beBytes 2 _ (by omega)]; omega)
      · rw [if_neg h16] at he
        by_cases h32 : v < 2 ^ 32
        · rw [if_pos h32] at he
          simp only [Except.ok.injEq, List.cons.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          exact go 2 false rfl (by omega) (by simp [beBytes_length]) rfl
            (by rw [fromBytes_unsigned, beVal_beBytes 4 _ (by omega)]; omega)
        · rw [if_neg h32] at he
          by_cases h63 : v < 2 ^ 63
          · rw [if_pos h63] at he
            simp only [Except.ok.injEq, List.cons.injEq] at he
            obtain ⟨rfl, rfl⟩ := he
            have hbv := beVal_beBytes 8 v.toNat (by omega)
            exact go 3 true rfl (by omega) (by simp [beBytes_length]) rfl
              (by rw [fromBytes_pos _ (by rw [hbv, beBytes_length]; omega), hbv]; omega)
          · rw [if_neg h63] at he
            by_cases h64 : v < 2 ^ 64
            · rw [if_pos h64] at he
              simp only [Except.ok.injEq, List.cons.injEq] at he
              obtain ⟨rfl, rfl⟩ := he
              have hbv := beVal_beBytes 16 v.toNat (by omega)
              exact go 4 true rfl (by omega) (by simp [beBytes_length]) rfl
                (by rw [fromBytes_pos _ (by rw [hbv, beBytes_length]; omega), hbv]; omega)
            · rw [if_neg h64] at he; cases he


theorem drop_after (B : List Nat) (p : Nat) (ext pay rest : List Nat) (hb : B.drop p = (ext ++ pay) ++ rest) :
    B.drop (p + ext.length) = pay ++ rest := by
  rw [← List.drop_drop, hb, List.append_assoc, List.drop_left]

/-- The bytes of a sized token (`_write_size(H, size)` then a payload). -/
theorem sized (H : Nat) (hH : H = 0x40 ∨ H = 0x50 ∨ H = 0x60 ∨ H = 0xA0 ∨ H = 0xD0) (size : Nat)
    (hs : size < 2 ^ 64) (pay : List Nat) (tok : Nat) (tail : List Nat)
    (he : writeSizeB H size ++ pay = tok :: tail) :
    ∃ ext, tail = ext ++ pay ∧ tok &&& 0xF0 = H ∧
      ∀ k B p rest, 1 ≤ k → B.drop p = ext ++ rest →
        getSizeR k ⟨B, p⟩ (tok &&& 0x0F) = .ok (size, ⟨B, p + ext.length⟩) := by
  obtain ⟨tok', ext, hw, hT, hg⟩ := sizeField H hH size hs
  rw [hw] at he
  simp only [List.cons_append, List.cons.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨ext, rfl, hT, hg⟩

theorem readToken_data (cfg : PCfg) (k ref : Nat) (st : PState) (b B : List Nat) (p tok : Nat)
    (tail rest : List Nat) (hk : 2 ≤ k) (hbl : b.length < 2 ^ 64)
    (he : writeSizeB 0x40 b.length ++ b = tok :: tail) (hb : B.drop p = tail ++ rest) :
    ∃ fp : FP, fp.buf = B ∧ readToken cfg k (fun x st => readObj cfg k x st) ref st tok ⟨B, p⟩ =
      .ok (({ fp := fp, objs := st.objs } : PState).put ref (.data b)) := by
  obtain ⟨ext, rfl, hT, hg⟩ := sized 0x40 (by simp) b.length hbl b tok tail he
  have hn := tokNe tok 0x40 hT (by simp)
  refine ⟨⟨B, p + ext.length + b.length⟩, rfl, ?_⟩
  simp only [readToken, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2.1, hn.2.2.2.2.2.1,
    hn.2.2.2.2.2.2, hT, ↓reduceIte]
  rw [hg k B p (b ++ rest) (by omega) (by simpa using hb)]
  simp only [bind, Except.bind]
  rw [readR_prefix k hk B (p + ext.length) b rest (drop_after B p ext b rest hb)]
  simp

theorem readToken_ascii (cfg : PCfg) (k ref : Nat) (st : PState) (s B : List Nat) (p tok : Nat)
    (tail rest : List Nat) (hk : 2 ≤ k) (hsl : s.length < 2 ^ 64) (ha : ∀ c ∈ s, c < 128)
    (he : writeSizeB 0x50 s.length ++ s = tok :: tail) (hb : B.drop p = tail ++ rest) :
    ∃ fp : FP, fp.buf = B ∧ readToken cfg k (fun x st => readObj cfg k x st) ref st tok ⟨B, p⟩ =
      .ok (({ fp := fp, objs := st.objs } : PState).put ref (.str s)) := by
  obtain ⟨ext, rfl, hT, hg⟩ := sized 0x50 (by simp) s.length hsl s tok tail he
  have hn := tokNe tok 0x50 hT (by simp)
  refine ⟨⟨B, p + ext.length + s.length⟩, rfl, ?_⟩
  simp only [readToken, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2.1, hn.2.2.2.2.2.1,
    hn.2.2.2.2.2.2, hT, ↓reduceIte]
  rw [hg k B p (s ++ rest) (by omega) (by simpa using hb)]
  simp only [bind, Except.bind]
  rw [readR_prefix k hk B (p + ext.length) s rest (drop_after B p ext s rest hb)]
  simp [asciiDecode_ascii s ha]

theorem readToken_utf16 (cfg : PCfg) (k ref : Nat) (st : PState) (s t B : List Nat) (p tok : Nat)
    (tail rest : List Nat) (hk : 2 ≤ k) (htl : t.length / 2 < 2 ^ 64) (hev : t.length % 2 = 0)
    (hdec : utf16DecodeFull t 1 .strict true = .ok (s, t.length))
    (he : writeSizeB 0x60 (t.length / 2) ++ t = tok :: tail) (hb : B.drop p = tail ++ rest) :
    ∃ fp : FP, fp.buf = B ∧ readToken cfg k (fun x st => readObj cfg k x st) ref st tok ⟨B, p⟩ =
      .ok (({ fp := fp, objs := st.objs } : PState).put ref (.str s)) := by
  obtain ⟨ext, rfl, hT, hg⟩ := sized 0x60 (by simp) (t.length / 2) htl t tok tail he
  have hn := tokNe tok 0x60 hT (by simp)
  refine ⟨⟨B, p + ext.length + t.length⟩, rfl, ?_⟩
  simp only [readToken, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2.1, hn.2.2.2.2.2.1,
    hn.2.2.2.2.2.2, hT, ↓reduceIte]
  rw [hg k B p (t ++ rest) (by omega) (by simpa using hb)]
  simp only [bind, Except.bind]
  have h2 : t.length / 2 * 2 = t.length := by omega
  rw [h2, readR_prefix k hk B (p + ext.length) t rest (drop_after B p ext t rest hb)]
  simp [hdec]

theorem readToken_uid (cfg : PCfg) (k ref : Nat) (st : PState) (dd : Nat) (B : List Nat) (p tok : Nat)
    (tail rest : List Nat) (hk : 1 ≤ k) (he : uidBytes dd = some (tok :: tail))
    (hb : B.drop p = tail ++ rest) :
    ∃ fp : FP, fp.buf = B ∧ readToken cfg k (fun x st => readObj cfg k x st) ref st tok ⟨B, p⟩ =
      .ok (({ fp := fp, objs := st.objs } : PState).put ref (.uid dd)) := by
  have go : ∀ L, tok = 0x80 + L → L < 8 → tail.length = 1 + L → beVal tail = dd → dd < 2 ^ 64 →
      ∃ fp : FP, fp.buf = B ∧ readToken cfg k (fun x st => readObj cfg k x st) ref st tok ⟨B, p⟩ =
        .ok (({ fp := fp, objs := st.objs } : PState).put ref (.uid dd)) := by
    intro L ht hL hl hv hd
    subst ht
    refine ⟨⟨B, p + tail.length⟩, rfl, ?_⟩
    have hH := nib80 L hL
    have hn := tokNe (0x80 + L) 0x80 hH.1 (by simp)
    simp only [readToken, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2.1, hn.2.2.2.2.2.1,
      hn.2.2.2.2.2.2, hH.1, hH.2, ↓reduceIte]
    rw [← hl, read_prefix B p tail rest hb, hv]
    obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have h1 : ¬ ((18446744073709551616 : Int) ≤ (dd : Int)) := by omega
    have h2 : ¬ ((dd : Int) < 0) := by omega
    simp [uidR, call, h1, h2, bind, Except.bind]
  unfold uidBytes at he
  by_cases h8 : dd < 2 ^ 8
  · rw [if_pos h8] at he
    simp only [Option.some.injEq, List.cons.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact go 0 rfl (by omega) rfl (by simp [beVal]) (by omega)
  · rw [if_neg h8] at he
    by_cases h16 : dd < 2 ^ 16
    · rw [if_pos h16] at he
      simp only [Option.some.injEq, List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact go 1 rfl (by omega) (by simp [beBytes_length]) (beVal_beBytes 2 _ (by omega)) (by omega)
    · rw [if_neg h16] at he
      by_cases h32 : dd < 2 ^ 32
      · rw [if_pos h32] at he
        simp only [Option.some.injEq, List.cons.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact go 3 rfl (by omega) (by simp [beBytes_length]) (beVal_beBytes 4 _ (by omega)) (by omega)
      · rw [if_neg h32] at he
        by_cases h64 : dd < 2 ^ 64
        · rw [if_pos h64] at he
          simp only [Option.some.injEq, List.cons.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          exact go 7 rfl (by omega) (by simp [beBytes_length]) (beVal_beBytes 8 _ (by omega)) (by omega)
        · rw [if_neg h64] at he; cases he

theorem readIntsR_pack (k : Nat) (hk : 3 ≤ k) (B : List Nat) (p size : Nat) (hs : binaryFormat size = true)
    (xs rest : List Nat) (hx : ∀ x ∈ xs, x < 256 ^ size)
    (hb : B.drop p = packRefs size xs ++ rest) :
    readIntsR k ⟨B, p⟩ xs.length size = .ok (xs, ⟨B, p + size * xs.length⟩) := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hsz : 1 ≤ size := by simp [binaryFormat] at hs; omega
  simp only [readIntsR, call]
  have hr := readR_prefix k (by omega) B p (packRefs size xs) rest hb
  rw [packRefs_length] at hr
  rw [hr]
  simp only [bind, Except.bind, hs, ↓reduceIte]
  rw [chunks_packRefs size hsz xs hx]

theorem readRefsR_pack (k : Nat) (hk : 4 ≤ k) (cfg : PCfg) (B : List Nat) (p : Nat)
    (hs : binaryFormat cfg.refSize = true)
    (xs rest : List Nat) (hx : ∀ x ∈ xs, x < 256 ^ cfg.refSize)
    (hb : B.drop p = packRefs cfg.refSize xs ++ rest) :
    readRefsR k cfg ⟨B, p⟩ xs.length = .ok (xs, ⟨B, p + cfg.refSize * xs.length⟩) := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [readRefsR, call]
  exact readIntsR_pack k (by omega) B p cfg.refSize hs xs rest hx hb

theorem readToken_arr (cfg : PCfg) (k ref : Nat) (st : PState) (refs B : List Nat) (p tok : Nat)
    (tail rest : List Nat) (hk : 4 ≤ k) (hl : refs.length < 2 ^ 64) (hs : binaryFormat cfg.refSize = true)
    (hx : ∀ x ∈ refs, x < 256 ^ cfg.refSize)
    (he : writeSizeB 0xA0 refs.length ++ packRefs cfg.refSize refs = tok :: tail)
    (hb : B.drop p = tail ++ rest) :
    ∃ fp : FP, fp.buf = B ∧ readToken cfg k (fun x st => readObj cfg k x st) ref st tok ⟨B, p⟩ =
      afterToken cfg k ref st fp (.arr refs) := by
  obtain ⟨ext, rfl, hT, hg⟩ := sized 0xA0 (by simp) refs.length hl _ tok tail he
  have hn := tokNe tok 0xA0 hT (by simp)
  refine ⟨⟨B, p + ext.length + cfg.refSize * refs.length⟩, rfl, ?_⟩
  simp only [readToken, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2.1, hn.2.2.2.2.2.1,
    hn.2.2.2.2.2.2, hT, ↓reduceIte]
  rw [hg k B p (packRefs cfg.refSize refs ++ rest) (by omega) (by simpa using hb)]
  simp only [bind, Except.bind]
  rw [readRefsR_pack k hk cfg B (p + ext.length) hs refs rest hx (drop_after B p ext _ rest hb)]
  simp [afterToken]

theorem zip_fst_snd {α β : Type} (l : List (α × β)) : (l.map (·.1)).zip (l.map (·.2)) = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem readToken_dict (cfg : PCfg) (k ref : Nat) (st : PState) (items : List (Nat × Nat)) (B : List Nat)
    (p tok : Nat) (tail rest : List Nat) (hk : 4 ≤ k) (hl : items.length < 2 ^ 64)
    (hs : binaryFormat cfg.refSize = true)
    (hx : ∀ q ∈ items, q.1 < 256 ^ cfg.refSize ∧ q.2 < 256 ^ cfg.refSize)
    (he : writeSizeB 0xD0 items.length ++ (packRefs cfg.refSize (items.map (·.1)) ++
      packRefs cfg.refSize (items.map (·.2))) = tok :: tail)
    (hb : B.drop p = tail ++ rest) :
    ∃ fp : FP, fp.buf = B ∧ readToken cfg k (fun x st => readObj cfg k x st) ref st tok ⟨B, p⟩ =
      afterToken cfg k ref st fp (.dict items) := by
  obtain ⟨ext, rfl, hT, hg⟩ := sized 0xD0 (by simp) items.length hl _ tok tail he
  have hn := tokNe tok 0xD0 hT (by simp)
  have hk1 : ∀ x ∈ items.map (·.1), x < 256 ^ cfg.refSize := by
    intro x hm; simp at hm; obtain ⟨b, hb'⟩ := hm; exact (hx _ hb').1
  have hk2 : ∀ x ∈ items.map (·.2), x < 256 ^ cfg.refSize := by
    intro x hm; simp at hm; obtain ⟨a, ha'⟩ := hm; exact (hx _ ha').2
  refine ⟨⟨B, p + ext.length + cfg.refSize * items.length + cfg.refSize * items.length⟩, rfl, ?_⟩
  simp only [readToken, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2.1, hn.2.2.2.2.2.1,
    hn.2.2.2.2.2.2, hT, ↓reduceIte]
  rw [hg k B p _ (by omega) (by simpa using hb)]
  simp only [bind, Except.bind]
  have h1 := readRefsR_pack k hk cfg B (p + ext.length) hs (items.map (·.1))
    (packRefs cfg.refSize (items.map (·.2)) ++ rest) hk1
    (by rw [drop_after B p ext _ rest hb, List.append_assoc])
  rw [List.length_map] at h1
  rw [h1]
  simp only
  have h2 := readRefsR_pack k hk cfg B (p + ext.length + cfg.refSize * items.length) hs (items.map (·.2))
    rest hk2 (by
      have hd := drop_after B p ext _ rest hb
      rw [← List.drop_drop, hd, List.append_assoc]
      have : cfg.refSize * items.length = (packRefs cfg.refSize (items.map (·.1))).length := by
        rw [packRefs_length, List.length_map]
      rw [this, List.drop_left])
  rw [List.length_map] at h2
  rw [h2]
  simp [zip_fst_snd, afterToken]

end PyLean.TextLibs.Plist
