import PyLean.TextLibs.StructMore

/-!
`s_pack_internal`, `Struct_pack_impl` and `Struct_pack_into_impl` (`Modules/_struct.c:2331-2537`):
every pack routine writes its entry's size, `prepare_s` lays every code out inside `s_size`, so
`pack` returns `s_size` bytes and `pack_into` changes nothing outside its field; the `'p'` branch;
the refusals and rebase of `pack_into`; and the late read of an argument that is the target itself.
-/

namespace PyLean.TextLibs.Struct

open PyLean PyLean.TextLibs

set_option linter.unusedSimpArgs false

/-! ### Every pack routine writes its entry's size -/

theorem bind_ok {α β : Type} {x : Py α} {f : α → Py β} {w : β} (h : (x >>= f) = .ok w) :
    ∃ a, x = .ok a ∧ f a = .ok w := by
  cases hx : x with
  | error e => rw [hx] at h; cases h
  | ok a => rw [hx] at h; exact ⟨a, rfl, h⟩

theorem ordered_length (le : Bool) (n v : Nat) : (ordered le n v).length = n := by
  cases le <;> simp [ordered, leBytes_length]

/-- The width each pack routine writes: `sizeof` of the C type, or the entry's size where the model
writes that (the standard loops, and the native routines whose C type has the entry's size, which
`width_tables` checks). -/
def packWidth (e : FormatDef) : Option Nat :=
  match e.pack with
  | .none => none
  | .npChar | .npBool | .bpBool => some 1
  | .npHalffloat | .bpHalffloat | .lpHalffloat => some 2
  | .npFloat | .bpFloat | .lpFloat => some 4
  | .npLong | .npUlong | .npSsizeT | .npSizeT | .npLonglong | .npUlonglong | .npVoidP
  | .npDouble | .bpDouble | .lpDouble | .bpLonglong | .bpUlonglong | .lpLonglong | .lpUlonglong
  | .npFloatComplex | .bpFloatComplex | .lpFloatComplex => some 8
  | .npDoubleComplex | .bpDoubleComplex | .lpDoubleComplex => some 16
  | .bpInt | .bpUint | .lpInt | .lpUint | .npByte | .npUbyte | .npShort | .npUshort | .npInt | .npUint =>
    some e.size

theorem twos_len (s : Nat) (x : Int) : (twos s x).length = s := leBytes_length _ _

theorem runPack_width (e : FormatDef) (v : SV) (w : List Nat) (h : runPack e v = .ok w) :
    some w.length = packWidth e := by
  cases hp : e.pack <;> simp only [runPack, hp, packHalffloat, packFloatStd, packDoubleStd, packFCStd,
      packDCStd, packIntStd, packUintStd, packLonglongStd, packUlonglongStd, npSigned, npUnsigned] at h <;>
    simp only [packWidth, hp]
  all_goals
    repeat' (first
      | (cases h; done)
      | (obtain ⟨_, _, h⟩ := bind_ok h)
      | (simp only [bind, Except.bind] at h)
      | (split at h)
      | (simp only [throw, throwThe, MonadExceptOf.throw, pure, Except.pure] at h))
  all_goals first
    | (cases h; done)
    | (simp only [Except.ok.injEq] at h; subst h
       simp [twos_len, ordered_length, lpLoop_length, bpLoop_length, leBytes_length])
    | (injection h with h; subst h
       simp [twos_len, ordered_length, lpLoop_length, bpLoop_length, leBytes_length])

/-- In every table, an entry with a pack routine has the width that routine writes as its size, and
the entries without one are `x`, `s` and `p`. -/
theorem width_tables : ∀ t : Tab, ∀ e ∈ t.table,
    (e.pack = .none → e.format = ['x'] ∨ e.format = ['s'] ∨ e.format = ['p']) ∧
    (e.pack ≠ .none → packWidth e = some e.size) ∧
    (e.code = 's' → e.format = ['s']) ∧ (e.code = 'p' → e.format = ['p']) ∧
    (e.code = 'x' → e.format = ['x']) := by
  intro t
  cases t <;> decide +kernel

theorem packCall_ok (e : FormatDef) (v : SV) (w : List Nat) (h : packCall e v = .ok w) :
    runPack e v = .ok w := by
  unfold packCall at h
  split at h
  · cases h
  · exact h

/-! ### `prepare_s` lays every code out inside `s_size` -/

/-- What `prepare_s` guarantees of a code of a struct of size `L`: an entry of the table that is not
`x`; an `s` or `p` field once, with its count as its size; any other code with its entry's size; and
all its repeats ending by `L`. -/
def Laid (tbl : List FormatDef) (L : Nat) (c : Code) : Prop :=
  c.fmtdef ∈ tbl ∧ c.fmtdef.format ≠ ['x'] ∧
  ((c.fmtdef.format = ['s'] ∨ c.fmtdef.format = ['p']) → c.repeat_ = 1) ∧
  (¬(c.fmtdef.format = ['s'] ∨ c.fmtdef.format = ['p']) → c.size = c.fmtdef.size) ∧
  c.offset + c.repeat_ * c.size ≤ L

theorem align_ge (size : Nat) (e : FormatDef) : size ≤ (align size e).getD size := by
  unfold align
  by_cases h : e.alignment ≠ 0 ∧ size > 0
  · rw [if_pos h]
    simp only
    split <;> simp
  · rw [if_neg h]; simp

theorem laid_mono {tbl : List FormatDef} {L L' : Nat} {c : Code} (h : Laid tbl L c) (hl : L ≤ L') :
    Laid tbl L' c := ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, by have := h.2.2.2.2; omega⟩

theorem pass2_laid (t : Tab) : ∀ (fuel : Nat) (s : List Char) (acc : List Code × Nat),
    (∀ c ∈ acc.1, Laid t.table acc.2 c) →
    acc.2 ≤ (pass2 t.table fuel s acc).2 ∧
    ∀ c ∈ (pass2 t.table fuel s acc).1, Laid t.table (pass2 t.table fuel s acc).2 c := by
  intro fuel
  induction fuel with
  | zero => intro s acc h; exact ⟨Nat.le_refl _, h⟩
  | succ fuel ih =>
    intro s acc h
    have hitem : ∀ acc num c r, (∀ x ∈ acc.1, Laid t.table acc.2 x) →
        acc.2 ≤ (pass2Item t.table acc num c r).2 ∧
        ∀ x ∈ (pass2Item t.table acc num c r).1, Laid t.table (pass2Item t.table acc num c r).2 x := by
      intro acc num c r ha
      obtain ⟨codes, size⟩ := acc
      simp only at ha
      unfold pass2Item
      cases hg : getentry (c :: r) t.table with
      | error _ => exact ⟨Nat.le_refl _, ha⟩
      | ok e =>
        obtain ⟨he, hfe⟩ := getentry_mem hg
        obtain ⟨_, _, hne⟩ := table_sizes t e he
        have hcode : e.code = c := code_of_equal hfe hne
        obtain ⟨_, _, hs, hp, hx⟩ := width_tables t e he
        have hga := align_ge size e
        simp only
        generalize (align size e).getD size = sz at hga ⊢
        by_cases hsp : c = 's' ∨ c = 'p'
        · rw [if_pos hsp]
          have hf : e.format = ['s'] ∨ e.format = ['p'] := by
            rcases hsp with h | h
            · exact Or.inl (hs (hcode.trans h))
            · exact Or.inr (hp (hcode.trans h))
          refine ⟨by simp; omega, fun x hx => ?_⟩
          simp only [List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | hx
          · exact laid_mono (ha x hx) (by simp; omega)
          · subst hx
            refine ⟨he, ?_, fun _ => rfl, fun h => absurd hf h, by simp⟩
            rcases hf with h | h <;> rw [h] <;> decide
        · rw [if_neg hsp]
          by_cases hxc : c = 'x'
          · rw [if_pos hxc]
            exact ⟨by simp; omega, fun x hx => laid_mono (ha x hx) (by simp; omega)⟩
          · rw [if_neg hxc]
            have hnf : ¬(e.format = ['s'] ∨ e.format = ['p']) := by
              intro hf; apply hsp
              rcases hf with h | h
              · left; rw [← hcode]; simp [FormatDef.code, h]
              · right; rw [← hcode]; simp [FormatDef.code, h]
            have hnx : e.format ≠ ['x'] := by
              intro h; apply hxc; rw [← hcode]; simp [FormatDef.code, h]
            by_cases hn : num ≠ 0
            · rw [if_pos hn]
              refine ⟨by simp; omega, fun x hx => ?_⟩
              simp only [List.mem_append, List.mem_singleton] at hx
              rcases hx with hx | hx
              · exact laid_mono (ha x hx) (by simp; omega)
              · subst hx
                refine ⟨he, hnx, fun h => absurd h hnf, fun _ => rfl, ?_⟩
                simp only
                rw [Nat.mul_comm]
                exact Nat.le_refl _
            · rw [if_neg hn]
              exact ⟨by simp; omega, fun x hx => laid_mono (ha x hx) (by simp; omega)⟩
    match s with
    | [] => exact ⟨Nat.le_refl _, h⟩
    | c :: s =>
      unfold pass2
      split
      · exact ih _ _ h
      · split
        · split
          · exact ⟨Nat.le_refl _, h⟩
          · obtain ⟨h1, h2⟩ := hitem _ _ _ _ h
            obtain ⟨h3, h4⟩ := ih _ _ h2
            exact ⟨Nat.le_trans h1 h3, h4⟩
        · obtain ⟨h1, h2⟩ := hitem _ _ _ _ h
          obtain ⟨h3, h4⟩ := ih _ _ h2
          exact ⟨Nat.le_trans h1 h3, h4⟩

theorem prepareS_laid (fmt : List Nat) (s : SObj) (h : prepareS fmt = .ok s) :
    ∀ c ∈ s.codes, Laid (whichtable (asciiChars fmt)).1.table s.sSize c := by
  unfold prepareS at h
  split at h
  · cases h
  split at h
  · cases h
  cases hw : whichtable (asciiChars fmt) with
  | mk t f =>
    rw [hw] at h
    simp only at h
    split at h
    · cases h
    · split at h
      · cases h
      · cases hp : pass2 t.table (f.length + 1) f ([], 0) with
        | mk codes size =>
          rw [hp] at h
          cases h
          intro c hc
          have := (pass2_laid t (f.length + 1) f ([], 0) (by simp)).2 c (by rw [hp]; exact hc)
          simpa [hp] using this

/-! ### Packing stays inside the struct's region -/

theorem overlay_props (buf w : List Nat) (i L : Nat) (h1 : i + w.length ≤ L) (h2 : L ≤ buf.length) :
    (overlay buf i w).length = buf.length ∧ (overlay buf i w).drop L = buf.drop L := by
  have ht : (buf.take i).length = i := by simp; omega
  refine ⟨?_, ?_⟩
  · simp only [overlay, List.length_append, List.length_take, List.length_drop]; omega
  · unfold overlay
    rw [List.append_assoc, List.drop_append, List.drop_append]
    have e1 : (buf.take i).drop L = [] := List.drop_eq_nil_of_le (by omega)
    have e2 : w.drop (L - (buf.take i).length) = [] := List.drop_eq_nil_of_le (by rw [ht]; omega)
    rw [e1, e2, ht, List.nil_append, List.nil_append, List.drop_drop]
    congr 1
    omega

theorem packS_len (code : Code) (v : SV) (res w : List Nat) (hr : res.length = code.size)
    (h : packS code v res = .ok w) : w.length = code.size := by
  unfold packS at h
  cases v with
  | bytes p | bytearray p =>
    simp only [Except.ok.injEq] at h
    subst h
    simp only [List.length_append, List.length_take, List.length_drop, hr]
    split <;> omega
  | _ => simp at h

theorem packP_len (code : Code) (v : SV) (res w : List Nat) (hr : res.length = code.size)
    (h : packP code v res = .ok w) : w.length = code.size := by
  unfold packP at h
  cases v with
  | bytes p | bytearray p =>
    simp only at h
    by_cases hn : (if code.size = 0 then 0 else if p.length > code.size - 1 then code.size - 1 else p.length) > 0
    · rw [if_pos hn] at h
      simp only [Except.ok.injEq] at h
      subst h
      simp only [List.length_set, List.length_append, List.length_take, List.length_drop, hr]
      revert hn
      split
      · omega
      · split <;> intro hn <;> omega
    · rw [if_neg hn] at h
      simp only [Except.ok.injEq] at h
      subst h
      exact hr
  | _ => simp at h

theorem packOne_props (t : Tab) (L : Nat) (code : Code) (hl : Laid t.table L code) (pre buf buf' : List Nat)
    (off : Nat) (v : SV) (hoff : off + code.size ≤ L) (hL : L ≤ buf.length)
    (h : packOne code pre buf off v = .ok buf') : buf'.length = buf.length ∧ buf'.drop L = buf.drop L := by
  obtain ⟨hmem, hnx, hsp, hsz, _⟩ := hl
  obtain ⟨hnone, hwid, _⟩ := width_tables t code.fmtdef hmem
  have hres : ((buf.drop off).take code.size).length = code.size := by simp; omega
  unfold packOne at h
  simp only at h
  split at h
  · obtain ⟨w, hw, h2⟩ := bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h2
    subst h2
    have := packS_len code _ _ w hres hw
    exact overlay_props buf w off L (by omega) hL
  · split at h
    · obtain ⟨w, hw, h2⟩ := bind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h2
      subst h2
      have := packP_len code _ _ w hres hw
      exact overlay_props buf w off L (by omega) hL
    · rename_i hs hp
      obtain ⟨w, hw, h2⟩ := bind_ok h
      have hrun := packCall_ok _ _ _ hw
      have hpw := runPack_width _ _ _ hrun
      have hne : code.fmtdef.pack ≠ .none := by
        intro hn
        rcases hnone hn with h3 | h3 | h3
        · exact hnx h3
        · exact hs h3
        · exact hp h3
      rw [hwid hne] at hpw
      simp only [Option.some.injEq] at hpw
      have hcs := hsz (by rintro (h3 | h3) <;> contradiction)
      split at h2
      · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h2
      · simp only [pure, Except.pure, Except.ok.injEq, bind, Except.bind] at h2
        subst h2
        exact overlay_props buf w off L (by omega) hL

theorem packRepeat_props (t : Tab) (L : Nat) (code : Code) (hl : Laid t.table L code) (pre : List Nat) :
    ∀ (j off : Nat) (buf : List Nat) (args : List SV) (r : List Nat × List SV),
      off + j * code.size ≤ L → L ≤ buf.length → packRepeat code pre j off buf args = .ok r →
      r.1.length = buf.length ∧ r.1.drop L = buf.drop L := by
  intro j
  induction j with
  | zero => intro off buf args r _ _ h; simp only [packRepeat, Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩
  | succ j ih =>
    intro off buf args r hj hL h
    unfold packRepeat at h
    split at h
    · cases h
    · rename_i v rest
      obtain ⟨b1, hb1, h2⟩ := bind_ok h
      obtain ⟨l1, d1⟩ := packOne_props t L code hl pre buf b1 off v (by rw [Nat.succ_mul] at hj; omega) hL hb1
      obtain ⟨l2, d2⟩ := ih (off + code.size) b1 rest r (by rw [Nat.succ_mul] at hj; omega) (by omega) h2
      exact ⟨l2.trans l1, d2.trans d1⟩

theorem fold_props (t : Tab) (L : Nat) (pre : List Nat) :
    ∀ (codes : List Code) (acc r : List Nat × List SV), (∀ c ∈ codes, Laid t.table L c) →
      L ≤ acc.1.length →
      codes.foldlM (init := acc) (fun acc code => packRepeat code pre code.repeat_ code.offset acc.1 acc.2)
        = .ok r →
      r.1.length = acc.1.length ∧ r.1.drop L = acc.1.drop L := by
  intro codes
  induction codes with
  | nil => intro acc r _ _ h; simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩
  | cons c cs ih =>
    intro acc r hc hL h
    simp only [List.foldlM_cons] at h
    obtain ⟨r1, hr1, h2⟩ := bind_ok h
    have hlc := hc c (by simp)
    obtain ⟨l1, d1⟩ := packRepeat_props t L c hlc pre c.repeat_ c.offset acc.1 acc.2 r1
      (by have := hlc.2.2.2.2; omega) hL hr1
    obtain ⟨l2, d2⟩ := ih r1 r (fun x hx => hc x (by simp [hx])) (by omega) h2
    exact ⟨l2.trans l1, d2.trans d1⟩

/-- `s_pack_internal` on a struct `prepare_s` made, over a region of at least `s_size` bytes, keeps
the region's length and every byte from `s_size` on. -/
theorem sPack_props (fmt : List Nat) (s : SObj) (hs : prepareS fmt = .ok s) (pre buf out : List Nat)
    (args : List SV) (hb : s.sSize ≤ buf.length) (h : sPackInternal s pre buf args = .ok out) :
    out.length = buf.length ∧ out.drop s.sSize = buf.drop s.sSize := by
  unfold sPackInternal at h
  obtain ⟨r, hr, h2⟩ := bind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h2
  subst h2
  have hcl1 : (List.replicate s.sSize 0 ++ buf.drop s.sSize).length = buf.length := by simp; omega
  have hcl2 : (List.replicate s.sSize 0 ++ buf.drop s.sSize).drop s.sSize = buf.drop s.sSize := by
    rw [List.drop_append]; simp
  obtain ⟨l, d⟩ := fold_props (whichtable (asciiChars fmt)).1 s.sSize pre s.codes _ r
    (prepareS_laid fmt s hs) (by rw [hcl1]; exact hb) hr
  exact ⟨l.trans hcl1, d.trans hcl2⟩

/-- `pack` on a struct of an accepted format returns exactly `s_size` bytes whenever it succeeds
(`PyBytesWriter_FinishWithSize(writer, self->s_size)`, 2458, over a buffer `s_pack_internal` filled
without writing past it). A `pack` returning `b''` or a short buffer fails this. -/
def PackLength : Prop :=
  ∀ (fmt : List Nat) (s : SObj) (args : List SV) (out : List Nat), prepareS fmt = .ok s →
    structPack s args = .ok out → out.length = s.sSize

theorem packLength_proven : PackLength := by
  intro fmt s args out hs h
  unfold structPack at h
  split at h
  · cases h
  · have := (sPack_props fmt s hs [] _ out args (by simp) h).1
    simpa using this

theorem cacheStruct_prep (f : FmtArg) (s : SObj) (h : cacheStruct f = .ok s) : ∃ fmt, prepareS fmt = .ok s := by
  cases f with
  | str c => exact ⟨c, h⟩
  | bytes b => exact ⟨decodeSurrogate b, h⟩
  | other t hh => cases hh <;> simp [cacheStruct, structInit, setFormat] at h
  | hashRaises t e => cases e <;> simp [cacheStruct] at h

/-- Where `pack_into` writes, at a non-negative offset: the buffer keeps its length, the bytes before
the offset and every byte from `offset + s_size` on. -/
theorem packIntoBody_props (fmt : List Nat) (s : SObj) (hs : prepareS fmt = .ok s) (buf out : List Nat)
    (o : Nat) (args : List SV) (h : packIntoBody s buf o args = .ok out) :
    out.length = buf.length ∧ out.take o = buf.take o ∧ out.drop (o + s.sSize) = buf.drop (o + s.sSize) := by
  unfold packIntoBody at h
  simp only [show ¬ ((o : Int) < 0) by omega, if_false, pure, Except.pure, bind, Except.bind] at h
  by_cases hlen : (buf.length : Int) - (o : Int) < (s.sSize : Int)
  · simp [hlen, throw, throwThe, MonadExceptOf.throw] at h
  · simp only [hlen, if_false, Int.toNat_natCast] at h
    cases ht : sPackInternal s (buf.take o) (buf.drop o) args with
    | error e => rw [ht] at h; cases h
    | ok tail =>
      rw [ht] at h
      simp only [Except.ok.injEq] at h
      subst h
      have hb : s.sSize ≤ (buf.drop o).length := by simp; omega
      obtain ⟨l, d⟩ := sPack_props fmt s hs _ _ tail args hb ht
      have hto : (buf.take o).length = o := by simp; omega
      refine ⟨?_, ?_, ?_⟩
      · simp only [List.length_append, hto, l, List.length_drop]; omega
      · rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
      · rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append, hto,
          show o + s.sSize - o = s.sSize by omega, d, List.drop_drop]

theorem packIntoStaysInside_proven : PackIntoStaysInside := by
  intro f s buf out o args hc h
  obtain ⟨fmt, hs⟩ := cacheStruct_prep f s hc
  simp only [modPackInto, hc, bind, Except.bind, structPackInto] at h
  by_cases ho : (o : Int) ≤ longMax
  · have ha : ssizeArg (o : Int) = .ok (o : Int) := by
      unfold ssizeArg; rw [if_neg (by simp only [longMin] at *; omega)]
    rw [ha] at h
    simp only at h
    by_cases hn : args.length ≠ s.sLen
    · simp [hn, throw, throwThe, MonadExceptOf.throw] at h
    · simp only [hn, if_false] at h
      exact (packIntoBody_props fmt s hs buf out o args h).2.2
  · have ha : ssizeArg (o : Int) = .error (.overflowError "Python int too large to convert to C ssize_t") := by
      unfold ssizeArg; rw [if_pos (by omega)]
    rw [ha] at h
    cases h

/-! ### `pack_into`: refusals, rebase, where the bytes land -/

/-- `Struct_pack_into_impl` past its count check, for a struct of an accepted format and a buffer
whose length fits in `Py_ssize_t`: a negative offset that leaves less than `size` bytes (2497-2503),
one before the buffer (2506-2512), and a buffer too short from a non-negative offset (2518-2531) are
refused with the source's messages; a negative offset counts from the end (2514); and a success keeps
the buffer's length, the bytes before the offset, and every byte from `offset + size` on. -/
def PackIntoLaws : Prop :=
  ∀ (fmt : List Nat) (s : SObj), prepareS fmt = .ok s → ∀ (buf : List Nat) (args : List SV),
    (∀ off : Int, off < 0 → off + s.sSize > 0 →
      packIntoBody s buf off args =
        .error (structErr s!"no space to pack {(s.sSize : Int)} bytes at offset {off}")) ∧
    (∀ off : Int, off < 0 → off + s.sSize ≤ 0 → off + buf.length < 0 →
      packIntoBody s buf off args =
        .error (structErr s!"offset {off} out of range for {(buf.length : Int)}-byte buffer")) ∧
    (∀ off : Int, 0 ≤ off → (buf.length : Int) - off < s.sSize →
      packIntoBody s buf off args = .error (structErr s!"pack_into requires a buffer of at least {(s.sSize : Int) + off} bytes for \
      packing {(s.sSize : Int)} bytes at offset {off} (actual buffer size is {(buf.length : Int)})")) ∧
    (∀ k : Nat, 0 < k → k ≤ buf.length → s.sSize ≤ k →
      packIntoBody s buf (-(k : Int)) args = packIntoBody s buf ((buf.length : Int) - k) args) ∧
    (∀ (o : Nat) (out : List Nat), packIntoBody s buf o args = .ok out →
      out.length = buf.length ∧ out.take o = buf.take o ∧ out.drop (o + s.sSize) = buf.drop (o + s.sSize))

theorem packIntoLaws_proven : PackIntoLaws := by
  intro fmt s hs buf args
  refine ⟨fun off h1 h2 => ?_, fun off h1 h2 h3 => ?_, fun off h1 h2 => ?_, fun k hk0 hk hsz => ?_,
    fun o out h => packIntoBody_props fmt s hs buf out o args h⟩
  · simp [packIntoBody, h1, h2, bind, Except.bind]
  · have n2 : ¬ (off + (s.sSize : Int) > 0) := by omega
    simp [packIntoBody, h1, n2, h3, bind, Except.bind]
  · have n1 : ¬ off < 0 := by omega
    simp [packIntoBody, n1, h2, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  · have n1 : -(k : Int) < 0 := by omega
    have n2 : ¬ (-(k : Int) + (s.sSize : Int) > 0) := by omega
    have n3 : ¬ (-(k : Int) + (buf.length : Int) < 0) := by omega
    have n4 : ¬ ((buf.length : Int) - (k : Int) < 0) := by omega
    simp only [packIntoBody, n1, n2, n3, n4, if_true, if_false, bind, Except.bind, pure, Except.pure]
    rw [show -(k : Int) + (buf.length : Int) = (buf.length : Int) - k by omega]

/-! ### The `'p'` branch -/

/-- A `'p'` field of size `n` holds, from the zeros the `memset` left, the count
`min(len, n - 1, 255)` in its first byte and then the first `min(len, n - 1)` bytes of the value, NUL
padded; a zero-sized field writes nothing (2370-2400). A count byte written for `0p`, or the length
not capped at 255, fails this. -/
def PackPField : Prop :=
  ∀ (code : Code) (d : List Nat), code.size ≥ 0 →
    packP code (.bytes d) (List.replicate code.size 0) = .ok
      (if code.size = 0 then []
       else (if min d.length (code.size - 1) = 0 then 0 else min (min d.length (code.size - 1)) 255) ::
         (d.take (min d.length (code.size - 1)) ++ List.replicate (code.size - 1 - min d.length (code.size - 1)) 0))

theorem packPField_proven : PackPField := by
  intro code d _
  unfold packP
  simp only
  generalize code.size = n
  rcases n with _ | m
  · simp
  · have hk : (if m + 1 = 0 then 0 else if d.length > m + 1 - 1 then m + 1 - 1 else d.length) = min d.length m := by
      simp only [Nat.add_sub_cancel, Nat.succ_ne_zero, if_false, Nat.min_def]
      split <;> split <;> omega
    rw [hk]
    simp only [Nat.add_sub_cancel, Nat.add_one_ne_zero, if_false]
    generalize hkk : min d.length m = k
    have hk1 : k ≤ m := by omega
    have hk2 : k ≤ d.length := by omega
    by_cases hk0 : k > 0
    · have hk00 : (k = 0) = False := by simp; omega
      simp only [if_pos hk0, hk00, if_false]
      simp only [List.replicate_succ, List.take_succ_cons, List.take_zero, List.drop_succ_cons,
        List.drop_replicate, List.cons_append, List.nil_append, List.set_cons_zero, Except.ok.injEq,
        List.cons.injEq]
      refine ⟨?_, ?_⟩
      · by_cases hb : k > 255
        · rw [if_pos hb]; simp only [Nat.min_def]; rw [if_neg (by omega)]
        · rw [if_neg hb]; simp only [Nat.min_def]; rw [if_pos (by omega)]
      · rw [show 1 + k = k + 1 by omega, List.drop_succ_cons, List.drop_replicate]
    · have : k = 0 := by omega
      subst this
      rw [if_neg (by omega), if_pos rfl]
      simp [List.replicate_succ]

/-! ### Packing the items: offsets and repeats -/

/-- Pack the items at the given positions, consuming one argument each. -/
def writeItems (pre : List Nat) : List (Code × Nat) → List Nat → List SV → Py (List Nat × List SV)
  | [], b, a => .ok (b, a)
  | (c, o) :: rest, b, a =>
    match a with
    | [] => .error (.named "SystemError" "args exhausted")
    | v :: vs => do writeItems pre rest (← packOne c pre b o v) vs

theorem packRepeat_eq (c : Code) (pre : List Nat) : ∀ (j off : Nat) (b : List Nat) (a : List SV),
    packRepeat c pre j off b a = writeItems pre (reps c j off) b a := by
  intro j
  induction j with
  | zero => intro off b a; rfl
  | succ j ih =>
    intro off b a
    cases a with
    | nil => rfl
    | cons v vs =>
      simp only [packRepeat, reps, writeItems]
      cases packOne c pre b off v with
      | error e => rfl
      | ok b' => simp only [bind, Except.bind]; exact ih _ _ _

theorem writeItems_append (pre : List Nat) : ∀ (xs ys : List (Code × Nat)) (b : List Nat) (a : List SV),
    writeItems pre (xs ++ ys) b a = (do let r ← writeItems pre xs b a; writeItems pre ys r.1 r.2) := by
  intro xs
  induction xs with
  | nil => intro ys b a; rfl
  | cons x xs ih =>
    intro ys b a
    obtain ⟨c, o⟩ := x
    cases a with
    | nil => rfl
    | cons v vs =>
      simp only [List.cons_append, writeItems]
      cases packOne c pre b o v with
      | error e => rfl
      | ok b' => simp only [bind, Except.bind]; exact ih ys b' vs

theorem foldPack_eq (pre : List Nat) : ∀ (codes : List Code) (acc : List Nat × List SV),
    codes.foldlM (init := acc) (fun acc code => packRepeat code pre code.repeat_ code.offset acc.1 acc.2)
      = writeItems pre (codes.flatMap (fun c => reps c c.repeat_ c.offset)) acc.1 acc.2 := by
  intro codes
  induction codes with
  | nil => intro acc; rfl
  | cons c cs ih =>
    intro acc
    rw [List.foldlM_cons, List.flatMap_cons, writeItems_append, packRepeat_eq]
    cases writeItems pre (reps c c.repeat_ c.offset) acc.1 acc.2 with
    | error e => rfl
    | ok r => simp only [bind, Except.bind]; exact ih r

/-- `s_pack_internal` clears the struct's `s_size` bytes and then packs every item in order: each code
`repeat` times at `offset + j * size`, consuming one argument per item, and reading each argument only
when its item is packed (2340-2410). A pack that wrote every field at offset 0, or skipped the
`memset`, fails this. -/
def PackItems : Prop :=
  ∀ (s : SObj) (pre buf : List Nat) (args : List SV),
    sPackInternal s pre buf args =
      (do let r ← writeItems pre (itemPos s) (List.replicate s.sSize 0 ++ buf.drop s.sSize) args
          return r.1)

theorem packItems_proven : PackItems := by
  intro s pre buf args
  unfold sPackInternal itemPos
  simp only [foldPack_eq]

/-! ### An argument that is the target itself -/

/-- `pack_into(fmt, ba, 0, ba)` writes what `pack_into(fmt, ba, 0, bytes(ba))` writes. False: the
argument is read after the `memset` at 2340, so `pack_into('4s', ba, 0, ba)` writes zeros
(python/cpython#158761, closed). -/
def PackIntoAliasCopy : Prop :=
  ∀ (cps : List Nat) (s : SObj) (buf : List Nat), structInit (.str cps) = .ok s →
    structPackInto s buf 0 [.alias] = structPackInto s buf 0 [.bytearray buf]

theorem packIntoAliasCopy_refuted : ¬PackIntoAliasCopy := by
  intro h
  have := h [52, 115] (sOf (.str [52, 115])) [1, 2, 3, 4] (by decide +kernel)
  revert this
  decide +kernel

/-! ### `__sizeof__` -/

def sizeofOk (p : List Char) (a b : FormatDef) : Bool :=
  match prepareS ((p ++ a.format ++ b.format).map Char.toNat) with
  | .ok s => sSizeof s == 96 + 32 * ((if a.code = 'x' then 0 else 1) + (if b.code = 'x' then 0 else 1))
  | .error _ => false

/-- `Struct.__sizeof__` counts the object, the terminating code and one 32-byte `formatcode` per code
`prepare_s` made, so for every two-item format it is `96 + 32 * (number of items that are not x)`
(2546-2553). A `__sizeof__` that ignored the codes, or counted `x`, fails this. -/
def SizeofPairs : Prop :=
  ∀ p ∈ [[], ['<'], ['>'], ['!'], ['='], ['@']], ∀ a ∈ (whichtable p).1.table, ∀ b ∈ (whichtable p).1.table,
    ∃ s, prepareS ((p ++ a.format ++ b.format).map Char.toNat) = .ok s ∧
      sSizeof s = 96 + 32 * ((if a.code = 'x' then 0 else 1) + (if b.code = 'x' then 0 else 1))

theorem sizeof_check : ∀ p ∈ [[], ['<'], ['>'], ['!'], ['='], ['@']], ∀ a ∈ (whichtable p).1.table,
    ∀ b ∈ (whichtable p).1.table, sizeofOk p a b = true := by
  decide +kernel

theorem sizeofPairs_proven : SizeofPairs := by
  intro p hp a ha b hb
  have h := sizeof_check p hp a ha b hb
  unfold sizeofOk at h
  split at h
  · rename_i s hs
    simp only [beq_iff_eq] at h
    exact ⟨s, hs, h⟩
  · cases h

end PyLean.TextLibs.Struct
