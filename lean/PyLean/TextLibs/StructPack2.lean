import PyLean.TextLibs.StructPack

/-!
Third review pass of `Modules/_struct.c`: the size `prepare_s` stores for an `s`/`p` code,
`Struct.pack` as `s_pack_internal` on zeros, `pack_into` writing what `pack` returns, and the
whitespace `prepare_s` skips between items.
-/

namespace PyLean.TextLibs.Struct

open PyLean PyLean.TextLibs

set_option linter.unusedSimpArgs false

/-! ### `Struct.pack` is `s_pack_internal` on zeros -/

/-- With the right number of arguments, `Struct.pack` is `s_pack_internal` over `s_size` zero bytes,
and its result is that buffer (2446-2458). With `PackItems` this pins the bytes `pack` returns; an
impl that ran `s_pack_internal` only for its errors and returned zeros fails it. -/
def PackValues : Prop :=
  ∀ (s : SObj) (args : List SV), args.length = s.sLen →
    structPack s args = sPackInternal s [] (List.replicate s.sSize 0) args

theorem packValues_proven : PackValues := by
  intro s args h
  simp [structPack, h]

/-! ### `pack_into` writes what `pack` returns -/

theorem resolve_ne (whole : List Nat) (v : SV) (h : v ≠ .alias) : resolve whole v = v := by
  cases v <;> first | rfl | exact absurd rfl h

theorem take_drop_take (b : List Nat) (off k L : Nat) (h : off + k ≤ L) :
    (b.drop off).take k = ((b.take L).drop off).take k := by
  rw [List.drop_take, List.take_take]
  congr 1
  omega

theorem overlay_take (b w : List Nat) (off L : Nat) (h1 : off + w.length ≤ L) (h2 : L ≤ b.length) :
    (overlay b off w).take L = overlay (b.take L) off w := by
  have hA : (b.take off ++ w).length = off + w.length := by simp; omega
  unfold overlay
  rw [List.take_append, hA, List.take_of_length_le (l := b.take off ++ w) (by omega)]
  rw [List.take_take, show min off L = off by omega, List.drop_take]

/-- Two runs of one item over buffers that agree on the struct's `L` bytes agree on those bytes,
for an argument that is not the target. -/
theorem packOne_sim (t : Tab) (L : Nat) (code : Code) (hl : Laid t.table L code) (pre1 pre2 b1 b2 : List Nat)
    (off : Nat) (v : SV) (hv : v ≠ .alias) (hoff : off + code.size ≤ L) (h1 : L ≤ b1.length)
    (h2 : L ≤ b2.length) (heq : b1.take L = b2.take L) :
    (packOne code pre1 b1 off v).map (·.take L) = (packOne code pre2 b2 off v).map (·.take L) := by
  obtain ⟨hmem, hnx, hsp, hsz, _⟩ := hl
  obtain ⟨hnone, hwid, _⟩ := width_tables t code.fmtdef hmem
  have hres : (b1.drop off).take code.size = (b2.drop off).take code.size := by
    rw [take_drop_take b1 off code.size L hoff, take_drop_take b2 off code.size L hoff, heq]
  have hrl : ((b1.drop off).take code.size).length = code.size := by simp; omega
  unfold packOne
  simp only [resolve_ne _ v hv]
  split
  · rw [hres]
    cases hw : packS code v ((b2.drop off).take code.size) with
    | error e => rfl
    | ok w =>
      have := packS_len code v _ w (by rw [← hres]; exact hrl) hw
      simp only [bind, Except.bind, pure, Except.pure, Except.map]
      rw [overlay_take b1 w off L (by omega) h1, overlay_take b2 w off L (by omega) h2, heq]
  · split
    · rw [hres]
      cases hw : packP code v ((b2.drop off).take code.size) with
      | error e => rfl
      | ok w =>
        have := packP_len code v _ w (by rw [← hres]; exact hrl) hw
        simp only [bind, Except.bind, pure, Except.pure, Except.map]
        rw [overlay_take b1 w off L (by omega) h1, overlay_take b2 w off L (by omega) h2, heq]
    · rename_i hs hp
      cases hw : packCall code.fmtdef v with
      | error e => rfl
      | ok w =>
        have hpw := runPack_width _ _ _ (packCall_ok _ _ _ hw)
        have hne : code.fmtdef.pack ≠ .none := by
          intro hn
          rcases hnone hn with h3 | h3 | h3
          · exact hnx h3
          · exact hs h3
          · exact hp h3
        rw [hwid hne] at hpw
        simp only [Option.some.injEq] at hpw
        have hcs := hsz (by rintro (h3 | h3) <;> contradiction)
        simp only [bind, Except.bind]
        split
        · rfl
        · simp only [pure, Except.pure, Except.map]
          rw [overlay_take b1 w off L (by omega) h1, overlay_take b2 w off L (by omega) h2, heq]

/-- `Except.map` of a pair function, for stating the simulation on the buffer part. -/
def takeFst (L : Nat) (r : List Nat × List SV) : List Nat × List SV := (r.1.take L, r.2)

theorem packRepeat_sim (t : Tab) (L : Nat) (code : Code) (hl : Laid t.table L code) (pre1 pre2 : List Nat) :
    ∀ (j off : Nat) (b1 b2 : List Nat) (args : List SV), (∀ v ∈ args, v ≠ .alias) →
      off + j * code.size ≤ L → L ≤ b1.length → L ≤ b2.length → b1.take L = b2.take L →
      (packRepeat code pre1 j off b1 args).map (takeFst L) = (packRepeat code pre2 j off b2 args).map (takeFst L) := by
  intro j
  induction j with
  | zero => intro off b1 b2 args _ _ _ _ heq; simp [packRepeat, Except.map, takeFst, heq]
  | succ j ih =>
    intro off b1 b2 args hna hj h1 h2 heq
    cases args with
    | nil => rfl
    | cons v rest =>
      have hv : v ≠ .alias := hna v (by simp)
      have hone := packOne_sim t L code hl pre1 pre2 b1 b2 off v hv (by rw [Nat.succ_mul] at hj; omega) h1 h2 heq
      simp only [packRepeat]
      cases hp1 : packOne code pre1 b1 off v with
      | error e1 =>
        cases hp2 : packOne code pre2 b2 off v with
        | error e2 =>
          rw [hp1, hp2] at hone
          simp only [Except.map, Except.error.injEq] at hone
          subst hone; rfl
        | ok w2 => rw [hp1, hp2] at hone; cases hone
      | ok w1 =>
        cases hp2 : packOne code pre2 b2 off v with
        | error e2 => rw [hp1, hp2] at hone; cases hone
        | ok w2 =>
          rw [hp1, hp2] at hone
          simp only [Except.map, Except.ok.injEq] at hone
          have l1 := (packOne_props t L code hl pre1 b1 w1 off v (by rw [Nat.succ_mul] at hj; omega) h1 hp1).1
          have l2 := (packOne_props t L code hl pre2 b2 w2 off v (by rw [Nat.succ_mul] at hj; omega) h2 hp2).1
          simp only [bind, Except.bind]
          exact ih (off + code.size) w1 w2 rest (fun x hx => hna x (by simp [hx]))
            (by rw [Nat.succ_mul] at hj; omega) (by omega) (by omega) hone

theorem packRepeat_sub (code : Code) (pre : List Nat) : ∀ (j off : Nat) (b : List Nat) (args : List SV)
    (r : List Nat × List SV), packRepeat code pre j off b args = .ok r → ∀ v ∈ r.2, v ∈ args := by
  intro j
  induction j with
  | zero => intro off b args r h v hv; simp only [packRepeat, Except.ok.injEq] at h; subst h; exact hv
  | succ j ih =>
    intro off b args r h v hv
    cases args with
    | nil => simp [packRepeat] at h
    | cons a rest =>
      simp only [packRepeat] at h
      obtain ⟨b', _, h2⟩ := bind_ok h
      exact List.mem_cons_of_mem _ (ih _ _ _ _ h2 v hv)

theorem fold_sim (t : Tab) (L : Nat) (pre1 pre2 : List Nat) :
    ∀ (codes : List Code) (b1 b2 : List Nat) (args : List SV), (∀ c ∈ codes, Laid t.table L c) →
      (∀ v ∈ args, v ≠ .alias) → L ≤ b1.length → L ≤ b2.length → b1.take L = b2.take L →
      (codes.foldlM (init := (b1, args))
          (fun acc code => packRepeat code pre1 code.repeat_ code.offset acc.1 acc.2)).map (takeFst L) =
        (codes.foldlM (init := (b2, args))
          (fun acc code => packRepeat code pre2 code.repeat_ code.offset acc.1 acc.2)).map (takeFst L) := by
  intro codes
  induction codes with
  | nil =>
    intro b1 b2 args _ _ _ _ heq
    simp [Except.map, takeFst, heq, pure, Except.pure]
  | cons c cs ih =>
    intro b1 b2 args hc hna h1 h2 heq
    have hlc := hc c (by simp)
    have hrep := packRepeat_sim t L c hlc pre1 pre2 c.repeat_ c.offset b1 b2 args hna
      (by have := hlc.2.2.2.2; omega) h1 h2 heq
    simp only [List.foldlM_cons]
    cases hp1 : packRepeat c pre1 c.repeat_ c.offset b1 args with
    | error e1 =>
      cases hp2 : packRepeat c pre2 c.repeat_ c.offset b2 args with
      | error e2 =>
        rw [hp1, hp2] at hrep
        simp only [Except.map, Except.error.injEq] at hrep
        subst hrep; rfl
      | ok r2 => rw [hp1, hp2] at hrep; cases hrep
    | ok r1 =>
      cases hp2 : packRepeat c pre2 c.repeat_ c.offset b2 args with
      | error e2 => rw [hp1, hp2] at hrep; cases hrep
      | ok r2 =>
        rw [hp1, hp2] at hrep
        simp only [Except.map, Except.ok.injEq, takeFst, Prod.mk.injEq] at hrep
        have l1 := (packRepeat_props t L c hlc pre1 c.repeat_ c.offset b1 args r1
          (by have := hlc.2.2.2.2; omega) h1 hp1).1
        have l2 := (packRepeat_props t L c hlc pre2 c.repeat_ c.offset b2 args r2
          (by have := hlc.2.2.2.2; omega) h2 hp2).1
        simp only [bind, Except.bind]
        obtain ⟨r1b, r1a⟩ := r1
        obtain ⟨r2b, r2a⟩ := r2
        simp only at hrep l1 l2
        obtain ⟨hb, ha⟩ := hrep
        subst ha
        exact ih r1b r2b r1a (fun x hx => hc x (by simp [hx]))
          (fun v hv => hna v (packRepeat_sub c pre1 _ _ _ _ _ hp1 v hv)) (by omega) (by omega) hb

/-- `pack_into` puts exactly `pack`'s bytes at the offset: for arguments that are not the target
buffer itself, a successful `pack_into(fmt, buf, o, *v)` leaves at `buf[o:o+size]` what
`pack(fmt, *v)` returns (both are `s_pack_internal`, over the target region and over zeros). A
`pack_into` that wrote the field shifted, reversed, or with the wrong values fails this. -/
def PackIntoMatchesPack : Prop :=
  ∀ (fmt : List Nat) (s : SObj), prepareS fmt = .ok s →
    ∀ (buf : List Nat) (o : Nat) (args : List SV) (out : List Nat), args.length = s.sLen →
      (∀ v ∈ args, v ≠ .alias) → packIntoBody s buf o args = .ok out →
      structPack s args = .ok ((out.drop o).take s.sSize)

theorem packIntoMatchesPack_proven : PackIntoMatchesPack := by
  intro fmt s hs buf o args out hn hna h
  have hlaid := prepareS_laid fmt s hs
  unfold packIntoBody at h
  simp only [show ¬ ((o : Int) < 0) by omega, if_false, pure, Except.pure, bind, Except.bind] at h
  by_cases hlen : (buf.length : Int) - (o : Int) < (s.sSize : Int)
  · simp [hlen, throw, throwThe, MonadExceptOf.throw] at h
  simp only [hlen, if_false, Int.toNat_natCast] at h
  cases ht : sPackInternal s (buf.take o) (buf.drop o) args with
  | error e => rw [ht] at h; cases h
  | ok tail =>
    rw [ht] at h
    simp only [Except.ok.injEq] at h
    subst h
    have hto : (buf.take o).length = o := by simp; omega
    have hdrop : (buf.take o ++ tail).drop o = tail := by
      rw [List.drop_append, List.drop_eq_nil_of_le (by omega), hto, Nat.sub_self, List.drop_zero, List.nil_append]
    rw [hdrop, packValues_proven s args hn]
    have hb : s.sSize ≤ (buf.drop o).length := by simp; omega
    -- both runs clear the first s_size bytes, so they agree on them
    have hsim := fold_sim (whichtable (asciiChars fmt)).1 s.sSize (buf.take o) [] s.codes
      (List.replicate s.sSize 0 ++ (buf.drop o).drop s.sSize)
      (List.replicate s.sSize 0 ++ (List.replicate s.sSize 0).drop s.sSize)
      args hlaid hna (by simp; try omega) (by simp) (by simp)
    unfold sPackInternal at ht ⊢
    obtain ⟨r1, hr1, h1⟩ := bind_ok ht
    simp only [pure, Except.pure, Except.ok.injEq] at h1
    subst h1
    rw [hr1] at hsim
    cases hr2 : s.codes.foldlM (init := (List.replicate s.sSize 0 ++ (List.replicate s.sSize 0).drop s.sSize, args))
        (fun acc code => packRepeat code [] code.repeat_ code.offset acc.1 acc.2) with
    | error e => rw [hr2] at hsim; cases hsim
    | ok r2 =>
      rw [hr2] at hsim
      simp only [Except.map, Except.ok.injEq, takeFst, Prod.mk.injEq] at hsim
      have hl2 := (fold_props (whichtable (asciiChars fmt)).1 s.sSize [] s.codes _ r2 hlaid (by simp) hr2).1
      simp only [List.drop_replicate, Nat.sub_self, List.replicate_zero, List.append_nil, List.length_replicate] at hl2
      simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq]
      rw [hr2]
      simp only [Except.ok.injEq]
      have h3 : r2.1.take s.sSize = r2.1 := List.take_of_length_le (by omega)
      first
        | exact (hsim.1.trans h3).symm
        | exact hsim.1.trans h3
        | (rw [hsim.1, h3])

/-! ### The size `prepare_s` stores for an `s`/`p` code -/

theorem scan2_ok : ∀ (ds : List Char) (acc : Nat) (c : Char) (r : List Char), (∀ d ∈ ds, isDigit d = true) →
    isDigit c = false → scanDigits2 acc (ds ++ c :: r) = (digVal acc ds, some c, r)
  | [], acc, c, r, _, hc => by simp [scanDigits2, hc, digVal]
  | d :: ds, acc, c, r, hd, hc => by
    have hdd : isDigit d = true := hd d (by simp)
    simp only [List.cons_append, scanDigits2, hdd, if_true]
    have := scan2_ok ds (acc * 10 + digit d) c r (fun x hx => hd x (by simp [hx])) hc
    rw [this]
    simp [digVal]

def spOk (t : Tab) (c : Char) : Bool :=
  match getentry [c] t.table with
  | .ok e => e.format == [c] && e.size == 1 && e.alignment == 0
  | .error _ => false

theorem sp_tables : ∀ t : Tab, ∀ c ∈ ['s', 'p'], spOk t c = true := by
  intro t
  cases t <;> decide +kernel

theorem sp_entry (t : Tab) (c : Char) (hc : c ∈ ['s', 'p']) :
    ∃ e, getentry [c] t.table = .ok e ∧ e.format = [c] ∧ e.size = 1 ∧ e.alignment = 0 := by
  have h := sp_tables t c hc
  unfold spOk at h
  split at h
  · rename_i e he
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨e, he, h.1.1, h.1.2, h.2⟩
  · cases h

theorem sp_passes (t : Tab) (c : Char) (hc : c ∈ ['s', 'p']) (d : Char) (ds : List Char)
    (hd : ∀ x ∈ d :: ds, isDigit x = true) (hv : digVal 0 (d :: ds) ≤ maxN) :
    ∃ e, e.format = [c] ∧
      pass1 t.table ((d :: ds ++ [c]).length + 1) (d :: ds ++ [c]) {} =
        .ok { size := digVal 0 (d :: ds), len := 1, ncodes := 1 } ∧
      pass2 t.table ((d :: ds ++ [c]).length + 1) (d :: ds ++ [c]) ([], 0) =
        ([⟨e, 0, digVal 0 (d :: ds), 1⟩], digVal 0 (d :: ds)) := by
  obtain ⟨e, hg, hf, hsz, hal⟩ := sp_entry t c hc
  have hcs : c = 's' ∨ c = 'p' := by simpa using hc
  have hcd : isDigit c = false := by rcases hcs with rfl | rfl <;> decide
  have hdd : isDigit d = true := hd d (by simp)
  have hsp : isSpace d = false := digit_not_space d hdd
  have hN : digVal 0 (d :: ds) = digVal (digit d) ds := by simp [digVal]
  have hlen : entryLen t.table [c] = 1 := by simp [entryLen, hg, hf]
  have hal0 : align 0 e = some 0 := by simp [align, hal]
  have hs1 := scan_ok ds (digit d) [c] (some c) (fun x hx => hd x (by simp [hx]))
    (by rw [← hN]; exact hv) ⟨hcd, rfl⟩
  have hs2 := scan2_ok ds (digit d) c [] (fun x hx => hd x (by simp [hx])) hcd
  refine ⟨e, hf, ?_, ?_⟩
  · rw [show (d :: ds ++ [c]).length + 1 = (ds.length + 2) + 1 by simp]
    simp only [List.cons_append, pass1, hsp, hdd, if_true, Bool.false_eq_true, if_false]
    rw [hs1]
    simp only [List.drop, List.drop_one, List.tail_cons, hlen]
    have hitem : pass1Item t.table {} (digVal (digit d) ds) c [] =
        .ok { size := digVal (digit d) ds, len := 1, ncodes := 1 } := by
      unfold pass1Item
      have hnm : ¬ ((0 : Nat) = maxN) := by simp [maxN]
      have hnn : ¬ (digVal (digit d) ds > (maxN - 0) / e.size) := by rw [hsz]; omega
      have hle : digVal (digit d) ds ≤ maxN := by rw [← hN]; exact hv
      simp [hg, hcs, hnm, hal0, hnn, bind, Except.bind, pure, Except.pure, hsz, Nat.zero_add, Nat.mul_one, hle]
    rw [hitem, ← hN]
    rfl
  · rw [show (d :: ds ++ [c]).length + 1 = (ds.length + 2) + 1 by simp]
    simp only [List.cons_append, pass2, hsp, hdd, if_true, Bool.false_eq_true, if_false]
    rw [hs2]
    simp only [hlen]
    have hitem : pass2Item t.table ([], 0) (digVal (digit d) ds) c [] =
        ([⟨e, 0, digVal (digit d) ds, 1⟩], digVal (digit d) ds) := by
      unfold pass2Item
      simp [hg, hcs, hal0]
    rw [hitem, ← hN]
    rfl

/-- `prepare_s` stores an `s` or `p` field once, at offset 0 of a one-item format, with its whole
count as its size, for every count that fits in `Py_ssize_t` and every prefix (`codes->size = num`,
1765): `Struct('4s').unpack(b'abcd') == (b'abcd',)`. A pass that stored size 1 for every `s`/`p`
field fails this. -/
def SPCount : Prop :=
  ∀ p ∈ [[], ['<'], ['>'], ['!'], ['='], ['@']], ∀ c ∈ ['s', 'p'], ∀ ds : List Char, ds ≠ [] →
    (∀ d ∈ ds, isDigit d = true) → digVal 0 ds ≤ maxN →
    ∃ s, prepareS ((p ++ ds ++ [c]).map Char.toNat) = .ok s ∧
      s.codes.map (fun x => (x.offset, x.size, x.repeat_)) = [(0, digVal 0 ds, 1)] ∧
      s.sSize = digVal 0 ds ∧ s.sLen = 1

theorem spCount_proven : SPCount := by
  intro p hp c hc ds hne hd hv
  obtain ⟨d, ds', rfl⟩ : ∃ d ds', ds = d :: ds' := by
    cases ds with
    | nil => exact absurd rfl hne
    | cons d ds' => exact ⟨d, ds', rfl⟩
  have hdd : isDigit d = true := hd d (by simp)
  have hdr := digit_range d hdd
  have hcs : c = 's' ∨ c = 'p' := by simpa using hc
  have hasc : ∀ x ∈ p ++ d :: ds' ++ [c], x.toNat < 128 ∧ x.toNat ≠ 0 := by
    intro x hx
    simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
    rcases hx with (hx | hx | hx) | hx
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hx <;> subst hx <;> decide
    · subst hx; omega
    · have := digit_range x (hd x (by simp [hx])); omega
    · subst hx; rcases hcs with rfl | rfl <;> decide
  have hall : ((p ++ d :: ds' ++ [c]).map Char.toNat).all (· < 128) = true := by
    simp only [List.all_map, List.all_eq_true, Function.comp, decide_eq_true_eq]
    exact fun x hx => (hasc x hx).1
  have hz : 0 ∉ (p ++ d :: ds' ++ [c]).map Char.toNat := by
    simp only [List.mem_map, not_exists, not_and]
    exact fun x hx h0 => (hasc x hx).2 h0
  have hasc' : asciiChars ((p ++ d :: ds' ++ [c]).map Char.toNat) = p ++ d :: ds' ++ [c] := by
    have hcomp : (Char.ofNat ∘ Char.toNat) = id := funext Char.ofNat_toNat
    simp [asciiChars, List.map_map, hcomp]
  have hnp : d ≠ '<' ∧ d ≠ '>' ∧ d ≠ '!' ∧ d ≠ '=' ∧ d ≠ '@' := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> subst h <;> simp at hdr
  have hw : ∃ t : Tab, whichtable (p ++ d :: ds' ++ [c]) = (t, d :: ds' ++ [c]) := by
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨.native, ?_⟩
      simp only [List.nil_append, List.cons_append]
      unfold whichtable
      split <;> simp_all
    all_goals first
      | exact ⟨.little, rfl⟩
      | exact ⟨.big, rfl⟩
      | exact ⟨.native, rfl⟩
  obtain ⟨t, ht⟩ := hw
  obtain ⟨e, _, h1, h2⟩ := sp_passes t c hc d ds' hd hv
  refine ⟨⟨[⟨e, 0, digVal 0 (d :: ds'), 1⟩], digVal 0 (d :: ds'), 1, (p ++ d :: ds' ++ [c]).map Char.toNat⟩,
    ?_, rfl, rfl, rfl⟩
  unfold prepareS
  rw [hasc', ht]
  simp only [hall, Bool.not_true, Bool.false_eq_true, if_false, hz]
  rw [h1]
  simp only
  rw [if_neg (by simp [maxN]), h2]

/-! ### Whitespace between items -/

/-- No format of a table is a proper prefix of another, and every format starts with a character that
is not a digit, not `Py_ISSPACE`, not a byte-order prefix, ASCII and not NUL. -/
def tableShape (tbl : List FormatDef) : Bool :=
  tbl.all (fun e1 => tbl.all (fun e2 => !e1.format.isPrefixOf e2.format || e1.format == e2.format)) &&
  tbl.all (fun e => e.format.all (fun x => !isDigit x && !isSpace x &&
    !(x == '<' || x == '>' || x == '!' || x == '=' || x == '@') && decide (x.toNat < 128) &&
    decide (x.toNat ≠ 0)) && e.format != [])

theorem tables_shape : ∀ t : Tab, tableShape t.table = true := by
  intro t
  cases t <;> decide +kernel

theorem shape_prefix {tbl : List FormatDef} (h : tableShape tbl = true) {e1 e2 : FormatDef}
    (h1 : e1 ∈ tbl) (h2 : e2 ∈ tbl) (hp : e1.format <+: e2.format) : e1.format = e2.format := by
  simp only [tableShape, Bool.and_eq_true, List.all_eq_true] at h
  have := h.1 e1 h1 e2 h2
  simp only [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at this
  rcases this with h3 | h3
  · rw [List.isPrefixOf_iff_prefix.mpr hp] at h3; cases h3
  · exact h3

theorem shape_char {tbl : List FormatDef} (h : tableShape tbl = true) {e : FormatDef} (he : e ∈ tbl)
    {x : Char} (hx : x ∈ e.format) :
    isDigit x = false ∧ isSpace x = false ∧ x ≠ '<' ∧ x ≠ '>' ∧ x ≠ '!' ∧ x ≠ '=' ∧ x ≠ '@' ∧
      x.toNat < 128 ∧ x.toNat ≠ 0 := by
  simp only [tableShape, Bool.and_eq_true, List.all_eq_true] at h
  have := (h.2 e he).1 x hx
  simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne,
    decide_eq_true_eq, ne_eq] at this
  obtain ⟨⟨⟨⟨h1, h2⟩, ⟨⟨⟨⟨h3, h4⟩, h5⟩, h6⟩, h7⟩⟩, h8⟩, h9⟩ := this
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem shape_ne {tbl : List FormatDef} (h : tableShape tbl = true) {e : FormatDef} (he : e ∈ tbl) :
    e.format ≠ [] := by
  simp only [tableShape, Bool.and_eq_true, List.all_eq_true] at h
  have := (h.2 e he).2
  simpa using this

/-- `getentry` at a whole format of the table, followed by anything, finds an entry with that format. -/
theorem getentry_fmt (tbl0 : List FormatDef) (h : tableShape tbl0 = true) (e : FormatDef) (he : e ∈ tbl0)
    (r : List Char) : ∀ tbl : List FormatDef, (∀ x ∈ tbl, x ∈ tbl0) → e ∈ tbl →
      ∃ e', getentry (e.format ++ r) tbl = .ok e' ∧ getentry e.format tbl = .ok e' ∧ e'.format = e.format
  | [], _, hm => by cases hm
  | x :: xs, hsub, hm => by
    have hx0 : x ∈ tbl0 := hsub x (by simp)
    by_cases hxp : x.format <+: e.format
    · have h1 : formatEqual x e.format = true := List.isPrefixOf_iff_prefix.mpr hxp
      have h2 : formatEqual x (e.format ++ r) = true :=
        List.isPrefixOf_iff_prefix.mpr (hxp.trans (List.prefix_append _ _))
      exact ⟨x, by simp [getentry, h2], by simp [getentry, h1], shape_prefix h hx0 he hxp⟩
    · have h1 : formatEqual x e.format = false := by
        cases hh : formatEqual x e.format
        · rfl
        · exact absurd (List.isPrefixOf_iff_prefix.mp hh) hxp
      have h2 : formatEqual x (e.format ++ r) = false := by
        cases hh : formatEqual x (e.format ++ r)
        · rfl
        · have hp := List.isPrefixOf_iff_prefix.mp hh
          rcases List.prefix_or_prefix_of_prefix hp (List.prefix_append e.format r) with h3 | h3
          · exact absurd h3 hxp
          · exact absurd ((shape_prefix h he hx0 h3) ▸ List.prefix_refl _) hxp
      have hm' : e ∈ xs := by
        rcases List.mem_cons.mp hm with h3 | h3
        · subst h3; exact absurd (List.prefix_refl _) hxp
        · exact h3
      obtain ⟨e', a, b, c⟩ := getentry_fmt tbl0 h e he r xs (fun y hy => hsub y (by simp [hy])) hm'
      exact ⟨e', by simp [getentry, h2, a], by simp [getentry, h1, b], c⟩

theorem pass1Item_congr (tbl : List FormatDef) (st : Pass1) (num : Nat) (c : Char) (r r' : List Char)
    (h : getentry (c :: r) tbl = getentry (c :: r') tbl) :
    pass1Item tbl st num c r = pass1Item tbl st num c r' := by
  unfold pass1Item
  rw [h]

theorem pass2Item_congr (tbl : List FormatDef) (acc : List Code × Nat) (num : Nat) (c : Char) (r r' : List Char)
    (h : getentry (c :: r) tbl = getentry (c :: r') tbl) :
    pass2Item tbl acc num c r = pass2Item tbl acc num c r' := by
  unfold pass2Item
  rw [h]

/-- An item: a run of digits, then the whole format of an entry of the table. -/
def IsItem (tbl : List FormatDef) (it : List Char) : Prop :=
  ∃ ds e, it = ds ++ e.format ∧ e ∈ tbl ∧ ∀ d ∈ ds, isDigit d = true

/-- Runs of `Py_ISSPACE` characters are skipped by the first pass (1673-1674). -/
theorem pass1_spaces (tbl : List FormatDef) (s : List Char) (st : Pass1) :
    ∀ (w : List Char) (f : Nat), (∀ x ∈ w, isSpace x = true) → pass1 tbl (f + w.length) (w ++ s) st = pass1 tbl f s st
  | [], f, _ => rfl
  | x :: w, f, hw => by
    have hx : isSpace x = true := hw x (by simp)
    rw [show f + (x :: w).length = (f + w.length) + 1 by simp; omega]
    simp only [List.cons_append, pass1, hx, if_true]
    exact pass1_spaces tbl s st w f (fun y hy => hw y (by simp [hy]))

/-- ... and by the second (1748-1749). -/
theorem pass2_spaces (tbl : List FormatDef) (s : List Char) (acc : List Code × Nat) :
    ∀ (w : List Char) (f : Nat), (∀ x ∈ w, isSpace x = true) → pass2 tbl (f + w.length) (w ++ s) acc = pass2 tbl f s acc
  | [], f, _ => rfl
  | x :: w, f, hw => by
    have hx : isSpace x = true := hw x (by simp)
    rw [show f + (x :: w).length = (f + w.length) + 1 by simp; omega]
    simp only [List.cons_append, pass2, hx, if_true]
    exact pass2_spaces tbl s acc w f (fun y hy => hw y (by simp [hy]))

theorem bind_pure_py {α : Type} (x : Py α) : (x >>= fun a => (pure a : Py α)) = x := by
  cases x <;> rfl

/-- One item costs the first pass one unit of fuel, and what it does does not depend on what follows. -/
theorem pass1_item (tbl : List FormatDef) (h : tableShape tbl = true) (it : List Char) (hi : IsItem tbl it)
    (f : Nat) (s : List Char) (st : Pass1) :
    pass1 tbl (f + 1) (it ++ s) st = (pass1 tbl 2 it st >>= fun st' => pass1 tbl f s st') := by
  obtain ⟨ds, e, rfl, he, hd⟩ := hi
  have gen : ∀ (f : Nat) (s : List Char), pass1 tbl (f + 1) (ds ++ e.format ++ s) st =
      ((match ds with
        | [] => pass1Item tbl st 1 (e.format.headD ' ') (e.format.tail)
        | d :: ds' => if digVal (digit d) ds' ≤ maxN then
            pass1Item tbl st (digVal (digit d) ds') (e.format.headD ' ') (e.format.tail)
            else .error overflowErr) >>= fun st' => pass1 tbl f s st') := by
    intro f s
    obtain ⟨e', hg1, hg2, hf⟩ := getentry_fmt tbl h e he s tbl (fun _ hy => hy) he
    obtain ⟨c, cs, hcs⟩ : ∃ c cs, e.format = c :: cs := by
      cases hh : e.format with
      | nil => exact absurd hh (shape_ne h he)
      | cons c cs => exact ⟨c, cs, rfl⟩
    have hc := shape_char h he (x := c) (by simp [hcs])
    rw [hcs] at hg1 hg2 hf ⊢
    have hlen : entryLen tbl (c :: (cs ++ s)) = cs.length + 1 := by
      simp only [entryLen, List.cons_append] at hg1 ⊢
      rw [hg1]; simp [hf]
    have hcong : pass1Item tbl st 1 c (cs ++ s) = pass1Item tbl st 1 c cs := by
      apply pass1Item_congr; simpa using hg1.trans hg2.symm
    cases ds with
    | nil =>
      simp only [List.nil_append, List.cons_append, pass1, hc.2.1, hc.1, Bool.false_eq_true, if_false,
        List.headD_cons, List.tail_cons]
      rw [hlen, hcong]
      congr 1
      funext st'
      simp
    | cons d ds' =>
      have hdd : isDigit d = true := hd d (by simp)
      have hsp : isSpace d = false := digit_not_space d hdd
      simp only [List.cons_append, List.append_assoc, pass1, hsp, hdd, if_true, Bool.false_eq_true,
        if_false, List.headD_cons, List.tail_cons]
      by_cases hv : digVal (digit d) ds' ≤ maxN
      · rw [scan_ok ds' (digit d) (c :: (cs ++ s)) (some c) (fun x hx => hd x (by simp [hx])) hv ⟨hc.1, rfl⟩]
        simp only [List.drop_one, List.tail_cons, if_pos hv]
        rw [hlen]
        have hcong' : pass1Item tbl st (digVal (digit d) ds') c (cs ++ s) =
            pass1Item tbl st (digVal (digit d) ds') c cs := by
          apply pass1Item_congr; simpa using hg1.trans hg2.symm
        rw [hcong']
        congr 1
        funext st'
        simp
      · rw [scan_ovf ds' (digit d) (c :: (cs ++ s)) (fun x hx => hd x (by simp [hx])) (by omega)
          (by have := digit_le d hdd; simp [maxN]; omega)]
        simp only [if_neg hv]
        rfl
  rw [gen f s]
  have g1 := gen 1 []
  simp only [List.append_nil] at g1
  rw [show (1 + 1) = 2 from rfl] at g1
  rw [g1]
  rw [show (pass1 tbl 1 [] : Pass1 → Py Pass1) = pure from rfl, bind_pure_py]

/-- One item, in the second pass, at the same cost. -/
theorem pass2_item (tbl : List FormatDef) (h : tableShape tbl = true) (it : List Char) (hi : IsItem tbl it)
    (f : Nat) (s : List Char) (acc : List Code × Nat) :
    pass2 tbl (f + 1) (it ++ s) acc = pass2 tbl f s (pass2 tbl 2 it acc) := by
  obtain ⟨ds, e, rfl, he, hd⟩ := hi
  have gen : ∀ (f : Nat) (s : List Char), pass2 tbl (f + 1) (ds ++ e.format ++ s) acc =
      pass2 tbl f s (match ds with
        | [] => pass2Item tbl acc 1 (e.format.headD ' ') (e.format.tail)
        | d :: ds' => pass2Item tbl acc (digVal (digit d) ds') (e.format.headD ' ') (e.format.tail)) := by
    intro f s
    obtain ⟨e', hg1, hg2, hf⟩ := getentry_fmt tbl h e he s tbl (fun _ hy => hy) he
    obtain ⟨c, cs, hcs⟩ : ∃ c cs, e.format = c :: cs := by
      cases hh : e.format with
      | nil => exact absurd hh (shape_ne h he)
      | cons c cs => exact ⟨c, cs, rfl⟩
    have hc := shape_char h he (x := c) (by simp [hcs])
    rw [hcs] at hg1 hg2 hf ⊢
    have hlen : entryLen tbl (c :: (cs ++ s)) = cs.length + 1 := by
      simp only [entryLen, List.cons_append] at hg1 ⊢
      rw [hg1]; simp [hf]
    have hcong : ∀ num, pass2Item tbl acc num c (cs ++ s) = pass2Item tbl acc num c cs := by
      intro num; apply pass2Item_congr; simpa using hg1.trans hg2.symm
    cases ds with
    | nil =>
      simp only [List.nil_append, List.cons_append, pass2, hc.2.1, hc.1, Bool.false_eq_true, if_false,
        List.headD_cons, List.tail_cons]
      rw [hlen, hcong]
      simp
    | cons d ds' =>
      have hdd : isDigit d = true := hd d (by simp)
      have hsp : isSpace d = false := digit_not_space d hdd
      simp only [List.cons_append, List.append_assoc, pass2, hsp, hdd, if_true, Bool.false_eq_true,
        if_false, List.headD_cons, List.tail_cons]
      rw [scan2_ok ds' (digit d) c (cs ++ s) (fun x hx => hd x (by simp [hx])) hc.1]
      simp only
      rw [hlen, hcong]
      simp
  rw [gen f s]
  have g1 := gen 1 []
  simp only [List.append_nil] at g1
  rw [show (1 + 1) = 2 from rfl] at g1
  rw [g1]
  rfl

/-- The first pass over a list of items: each item at a time, from the state the last one left. -/
def fold1 (tbl : List FormatDef) : Pass1 → List (List Char) → Py Pass1
  | st, [] => pure st
  | st, it :: its => pass1 tbl 2 it st >>= fun st' => fold1 tbl st' its

def fold2 (tbl : List FormatDef) : List Code × Nat → List (List Char) → List Code × Nat
  | acc, [] => acc
  | acc, it :: its => fold2 tbl (pass2 tbl 2 it acc) its

/-- Items, each followed by its run of whitespace. -/
def inter (items ws : List (List Char)) : List Char := (List.zipWith (· ++ ·) items ws).flatten

def wsum (ws : List (List Char)) : Nat := (ws.map List.length).sum

theorem pass1_inter (tbl : List FormatDef) (h : tableShape tbl = true) :
    ∀ (items ws : List (List Char)), ws.length = items.length → (∀ it ∈ items, IsItem tbl it) →
      (∀ w ∈ ws, ∀ x ∈ w, isSpace x = true) → ∀ (f : Nat) (st : Pass1),
      pass1 tbl (f + 1 + items.length + wsum ws) (inter items ws) st = fold1 tbl st items
  | [], [], _, _, _, f, st => rfl
  | [], _ :: _, hl, _, _, _, _ => by simp at hl
  | _ :: _, [], hl, _, _, _, _ => by simp at hl
  | it :: its, w :: ws, hl, hi, hw, f, st => by
    simp only [inter, List.zipWith_cons_cons, List.flatten_cons, List.append_assoc, wsum, List.map_cons,
      List.sum_cons, List.length_cons]
    rw [show f + 1 + (its.length + 1) + (w.length + (ws.map List.length).sum) =
      ((f + 1 + its.length + wsum ws) + w.length) + 1 by simp [wsum]; omega]
    rw [pass1_item tbl h it (hi it (by simp)), fold1]
    congr 1
    funext st'
    rw [pass1_spaces tbl _ st' w _ (hw w (by simp))]
    exact pass1_inter tbl h its ws (by simpa using hl) (fun y hy => hi y (by simp [hy]))
      (fun y hy => hw y (by simp [hy])) f st'

theorem pass2_inter (tbl : List FormatDef) (h : tableShape tbl = true) :
    ∀ (items ws : List (List Char)), ws.length = items.length → (∀ it ∈ items, IsItem tbl it) →
      (∀ w ∈ ws, ∀ x ∈ w, isSpace x = true) → ∀ (f : Nat) (acc : List Code × Nat),
      pass2 tbl (f + 1 + items.length + wsum ws) (inter items ws) acc = fold2 tbl acc items
  | [], [], _, _, _, f, acc => rfl
  | [], _ :: _, hl, _, _, _, _ => by simp at hl
  | _ :: _, [], hl, _, _, _, _ => by simp at hl
  | it :: its, w :: ws, hl, hi, hw, f, acc => by
    simp only [inter, List.zipWith_cons_cons, List.flatten_cons, List.append_assoc, wsum, List.map_cons,
      List.sum_cons, List.length_cons]
    rw [show f + 1 + (its.length + 1) + (w.length + (ws.map List.length).sum) =
      ((f + 1 + its.length + wsum ws) + w.length) + 1 by simp [wsum]; omega]
    rw [pass2_item tbl h it (hi it (by simp)), fold2]
    rw [pass2_spaces tbl _ _ w _ (hw w (by simp))]
    exact pass2_inter tbl h its ws (by simpa using hl) (fun y hy => hi y (by simp [hy]))
      (fun y hy => hw y (by simp [hy])) f _

theorem inter_length (tbl : List FormatDef) (h : tableShape tbl = true) :
    ∀ (items ws : List (List Char)), ws.length = items.length → (∀ it ∈ items, IsItem tbl it) →
      items.length + wsum ws ≤ (inter items ws).length
  | [], [], _, _ => by simp [inter, wsum]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
  | it :: its, w :: ws, hl, hi => by
    have ih := inter_length tbl h its ws (by simpa using hl) (fun y hy => hi y (by simp [hy]))
    obtain ⟨ds, e, rfl, he, _⟩ := hi it (by simp)
    have hne := shape_ne h he
    have : 1 ≤ e.format.length := by cases hh : e.format <;> simp_all
    simp only [inter, wsum, List.zipWith_cons_cons, List.flatten_cons, List.length_append, List.map_cons,
      List.sum_cons, List.length_cons] at ih ⊢
    omega

theorem inter_mem : ∀ (items ws : List (List Char)) (x : Char), x ∈ inter items ws →
    (∃ it ∈ items, x ∈ it) ∨ (∃ w ∈ ws, x ∈ w)
  | [], _, x, hx => by simp [inter] at hx
  | _ :: _, [], x, hx => by simp [inter] at hx
  | it :: its, w :: ws, x, hx => by
    simp only [inter, List.zipWith_cons_cons, List.flatten_cons, List.mem_append] at hx
    rcases hx with (hx | hx) | hx
    · exact .inl ⟨it, by simp, hx⟩
    · exact .inr ⟨w, by simp, hx⟩
    · rcases inter_mem its ws x hx with ⟨y, hy, hxy⟩ | ⟨y, hy, hxy⟩
      · exact .inl ⟨y, by simp [hy], hxy⟩
      · exact .inr ⟨y, by simp [hy], hxy⟩

theorem inter_nil : ∀ items : List (List Char), inter items (List.replicate items.length []) = items.flatten
  | [] => rfl
  | it :: its => by
    have := inter_nil its
    simp only [inter] at this ⊢
    simp [List.replicate_succ, this]

theorem space_char (x : Char) (h : isSpace x = true) :
    x ≠ '<' ∧ x ≠ '>' ∧ x ≠ '!' ∧ x ≠ '=' ∧ x ≠ '@' ∧ x.toNat < 128 ∧ x.toNat ≠ 0 := by
  simp only [isSpace, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with ((((h1 | h1) | h1) | h1) | h1) | h1 <;> subst h1 <;> decide

theorem digit_char (x : Char) (h : isDigit x = true) :
    x ≠ '<' ∧ x ≠ '>' ∧ x ≠ '!' ∧ x ≠ '=' ∧ x ≠ '@' ∧ x.toNat < 128 ∧ x.toNat ≠ 0 := by
  have hr := digit_range x h
  refine ⟨?_, ?_, ?_, ?_, ?_, by omega, by omega⟩ <;> intro h1 <;> subst h1 <;> simp at hr

theorem whichtable_native (X : List Char)
    (h : ∀ x ∈ X, x ≠ '<' ∧ x ≠ '>' ∧ x ≠ '!' ∧ x ≠ '=' ∧ x ≠ '@') : whichtable X = (.native, X) := by
  cases X with
  | nil => rfl
  | cons x r =>
    have hx := h x (by simp)
    obtain ⟨h1, h2, h3, h4, h5⟩ := hx
    unfold whichtable
    split <;> simp_all

/-- The result of `prepare_s` for a list of items, read item by item. -/
def canon (t : Tab) (items : List (List Char)) : Py (List Code × Nat × Nat) :=
  match fold1 t.table {} items with
  | .error e => .error e
  | .ok st =>
    if st.ncodes + 1 > maxN / 32 then .error (.named "MemoryError" "")
    else
      let (codes, size) := fold2 t.table ([], 0) items
      .ok (codes, size, st.len)

/-- What a `Struct` exposes apart from its format string: codes, `s_size`, `s_len`. -/
def sView (s : SObj) : List Code × Nat × Nat := (s.codes, s.sSize, s.sLen)

theorem prepareS_inter (p : List Char) (hp : p ∈ [[], ['<'], ['>'], ['!'], ['='], ['@']])
    (items : List (List Char)) (w0 : List Char) (ws : List (List Char))
    (hi : ∀ it ∈ items, IsItem (whichtable p).1.table it) (h0 : ∀ x ∈ w0, isSpace x = true)
    (hw : ∀ w ∈ ws, ∀ x ∈ w, isSpace x = true) (hl : ws.length = items.length) :
    sView <$> prepareS ((p ++ w0 ++ inter items ws).map Char.toNat) = canon (whichtable p).1 items := by
  have hsh := tables_shape (whichtable p).1
  have good : ∀ x ∈ w0 ++ inter items ws,
      x ≠ '<' ∧ x ≠ '>' ∧ x ≠ '!' ∧ x ≠ '=' ∧ x ≠ '@' ∧ x.toNat < 128 ∧ x.toNat ≠ 0 := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact space_char x (h0 x hx)
    · rcases inter_mem items ws x hx with ⟨it, hit, hxi⟩ | ⟨w, hw', hxw⟩
      · obtain ⟨ds, e, rfl, he, hd⟩ := hi it hit
        rcases List.mem_append.mp hxi with hxd | hxe
        · exact digit_char x (hd x hxd)
        · exact (shape_char hsh he hxe).2.2
      · exact space_char x (hw w hw' x hxw)
  have hgood : ∀ x ∈ p ++ w0 ++ inter items ws, x.toNat < 128 ∧ x.toNat ≠ 0 := by
    intro x hx
    rw [List.append_assoc] at hx
    rcases List.mem_append.mp hx with hx | hx
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hx <;> subst hx <;> decide
    · exact (good x hx).2.2.2.2.2
  have hall : ((p ++ w0 ++ inter items ws).map Char.toNat).all (· < 128) = true := by
    simp only [List.all_map, List.all_eq_true, Function.comp, decide_eq_true_eq]
    exact fun x hx => (hgood x hx).1
  have hz : 0 ∉ (p ++ w0 ++ inter items ws).map Char.toNat := by
    simp only [List.mem_map, not_exists, not_and]
    exact fun x hx h0 => (hgood x hx).2 h0
  have hasc : asciiChars ((p ++ w0 ++ inter items ws).map Char.toNat) = p ++ w0 ++ inter items ws := by
    have hcomp : (Char.ofNat ∘ Char.toNat) = id := funext Char.ofNat_toNat
    simp [asciiChars, List.map_map, hcomp]
  have hwt : whichtable (p ++ w0 ++ inter items ws) = ((whichtable p).1, w0 ++ inter items ws) := by
    rw [List.append_assoc]
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [List.nil_append, whichtable_native _ (fun x hx => by
        obtain ⟨a, b, c, d, e, _⟩ := good x hx; exact ⟨a, b, c, d, e⟩)]
      rfl
    all_goals rfl
  have hlen := inter_length _ hsh items ws hl hi
  have hfuel : (w0 ++ inter items ws).length + 1 =
      ((inter items ws).length - items.length - wsum ws) + 1 + items.length + wsum ws + w0.length := by
    simp only [List.length_append]; omega
  have hp1 := pass1_spaces (whichtable p).1.table (inter items ws) {} w0
    (((inter items ws).length - items.length - wsum ws) + 1 + items.length + wsum ws) h0
  rw [pass1_inter _ hsh items ws hl hi hw] at hp1
  have hp2 := pass2_spaces (whichtable p).1.table (inter items ws) ([], 0) w0
    (((inter items ws).length - items.length - wsum ws) + 1 + items.length + wsum ws) h0
  rw [pass2_inter _ hsh items ws hl hi hw] at hp2
  unfold prepareS
  rw [hasc, hwt]
  simp only [hall, Bool.not_true, Bool.false_eq_true, if_false, hz]
  rw [hfuel, hp1, hp2]
  unfold canon
  cases fold1 (whichtable p).1.table {} items with
  | error e => rfl
  | ok st =>
    simp only
    split
    · rfl
    · cases fold2 (whichtable p).1.table ([], 0) items
      rfl

/-- `Py_ISSPACE` characters between items are skipped by both passes of `prepare_s` (1673-1674,
1748-1749): a run of them after the byte-order prefix, and one after each item, change no code, no
offset, `s_size` or `s_len`, and no refusal. All six characters `Py_ISSPACE` accepts (space, `\t`,
`\n`, `\r`, `\v`, `\f`) are covered: `calcsize('i i') == calcsize('\ti\x0bi\x0c\r\n') == 8`.

An item is a run of digits, possibly empty, then the whole format of an entry of the table the prefix
selects (`Zf` and `Zd` are two characters). That is the precondition of the documented rule
("Whitespace characters between formats are ignored; a count and its format must not contain
whitespace though"): whitespace inside an item, between `Z` and its `f`, or before the prefix is a bad
char. Counts of any size are included, so overflow refusals are compared too. A `prepare_s` that
refused whitespace, or counted it as an item or a byte, fails this. -/
def WhitespaceSkip : Prop :=
  ∀ p ∈ [[], ['<'], ['>'], ['!'], ['='], ['@']], ∀ (items : List (List Char)) (w0 : List Char)
    (ws : List (List Char)), (∀ it ∈ items, IsItem (whichtable p).1.table it) →
    (∀ x ∈ w0, isSpace x = true) → (∀ w ∈ ws, ∀ x ∈ w, isSpace x = true) → ws.length = items.length →
    sView <$> prepareS ((p ++ w0 ++ inter items ws).map Char.toNat) =
      sView <$> prepareS ((p ++ items.flatten).map Char.toNat)

theorem whitespaceSkip_proven : WhitespaceSkip := by
  intro p hp items w0 ws hi h0 hw hl
  rw [prepareS_inter p hp items w0 ws hi h0 hw hl]
  have := prepareS_inter p hp items [] (List.replicate items.length []) hi (by simp)
    (by simp) (by simp)
  rw [inter_nil, List.append_nil] at this
  exact this.symm

end PyLean.TextLibs.Struct
