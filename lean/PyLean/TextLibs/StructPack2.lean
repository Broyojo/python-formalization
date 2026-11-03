import PyLean.TextLibs.StructPack

/-!
Third review pass of `Modules/_struct.c`: the size `prepare_s` stores for an `s`/`p` code,
`Struct.pack` as `s_pack_internal` on zeros, and `pack_into` writing what `pack` returns.
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

end PyLean.TextLibs.Struct
