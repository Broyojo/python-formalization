import PyLean.TextLibs.StructCache

/-!
`Struct.unpack`, `unpack_from`, `iter_unpack` and the iterator's `__length_hint__`
(`Modules/_struct.c:2105-2318`), by their results, with a `__buffer__` that can call `__init__`.
-/

namespace PyLean.TextLibs.Struct

open PyLean PyLean.TextLibs

set_option linter.unusedSimpArgs false

/-! ### `iter_unpack` divides by the size `__buffer__` left -/

/-- `iter_unpack` does not divide by zero, whatever its buffer's `__buffer__` does. False: the zero
test (2291) runs before `PyObject_GetBuffer` (2303), and a `__buffer__` that installs `'0s'` makes
the `%` at 2307 divide by zero (SIGFPE; python/cpython#158695, closed unread). -/
def IterUnpackNoCrash : Prop :=
  ∀ (f : FmtArg) (s : SObj) (b : BufArg), structInit f = .ok s → structIterUnpackA s b ≠ .error MEMORY

theorem iterUnpackNoCrash_refuted : ¬IterUnpackNoCrash := by
  intro h
  exact h (.str [98]) (sOf (.str [98])) (.reinit (List.replicate 8 0) (sOf (.str [48, 115])))
    (by decide +kernel) (by decide +kernel)

/-! ### `unpack` returns one value per item -/

/-- Entries without an unpack routine are only `x`, `s` and `p`. -/
theorem unpack_tables : ∀ t : Tab, ∀ e ∈ t.table, e.unpack = .none →
    e.format = ['x'] ∨ e.format = ['s'] ∨ e.format = ['p'] := by
  intro t
  cases t <;> decide +kernel

/-- What `prepare_s` stores in a code: an entry of the table that is not `x`. -/
def GoodCode (tbl : List FormatDef) (c : Code) : Prop := c.fmtdef ∈ tbl ∧ c.fmtdef.format ≠ ['x']

theorem pass2_good (t : Tab) : ∀ (fuel : Nat) (s : List Char) (acc : List Code × Nat),
    (∀ c ∈ acc.1, GoodCode t.table c) → ∀ c ∈ (pass2 t.table fuel s acc).1, GoodCode t.table c := by
  intro fuel
  induction fuel with
  | zero => intro s acc h; exact h
  | succ fuel ih =>
    intro s acc h
    have hitem : ∀ acc num c r, (∀ x ∈ acc.1, GoodCode t.table x) →
        ∀ x ∈ (pass2Item t.table acc num c r).1, GoodCode t.table x := by
      intro acc num c r ha x hx
      obtain ⟨codes, size⟩ := acc
      unfold pass2Item at hx
      cases hg : getentry (c :: r) t.table with
      | error _ => rw [hg] at hx; exact ha x hx
      | ok e =>
        obtain ⟨he, hfe⟩ := getentry_mem hg
        obtain ⟨_, _, hne⟩ := table_sizes t e he
        have hcode : e.code = c := code_of_equal hfe hne
        have hnx : c ≠ 'x' → e.format ≠ ['x'] := by
          intro hc hf; apply hc; rw [← hcode]; simp [FormatDef.code, hf]
        rw [hg] at hx
        simp only at hx
        split at hx
        · simp only [List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | hx
          · exact ha x hx
          · subst hx
            refine ⟨he, hnx ?_⟩
            rename_i hsp; rcases hsp with h | h <;> rw [h] <;> decide
        · split at hx
          · exact ha x hx
          · split at hx
            · simp only [List.mem_append, List.mem_singleton] at hx
              rcases hx with hx | hx
              · exact ha x hx
              · subst hx
                rename_i hx' _
                exact ⟨he, hnx hx'⟩
            · exact ha x hx
    match s with
    | [] => exact h
    | c :: s =>
      unfold pass2
      split
      · exact ih _ _ h
      · split
        · split
          · exact h
          · exact ih _ _ (hitem _ _ _ _ h)
        · exact ih _ _ (hitem _ _ _ _ h)

theorem prepareS_good (fmt : List Nat) (s : SObj) (h : prepareS fmt = .ok s) :
    ∀ c ∈ s.codes, GoodCode (whichtable (asciiChars fmt)).1.table c := by
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
          have := pass2_good t (f.length + 1) f ([], 0) (by simp) c (by rw [hp]; exact hc)
          simpa using this

theorem runUnpack_ok (e : FormatDef) (p : List Nat) (h : e.unpack ≠ .none) : ∃ v, runUnpack e p = .ok v := by
  unfold runUnpack
  cases hu : e.unpack <;> simp_all

theorem unpackOne_ok (tbl : List FormatDef) (t : Tab) (ht : tbl = t.table) (c : Code) (hc : GoodCode tbl c)
    (res : List Nat) : ∃ v, unpackOne c res = .ok v := by
  by_cases hs : c.fmtdef.format = ['s']
  · simp only [unpackOne, hs, if_true]; exact ⟨_, rfl⟩
  by_cases hp : c.fmtdef.format = ['p']
  · simp only [unpackOne, hs, hp, if_true, if_false]; exact ⟨_, rfl⟩
  simp only [unpackOne, hs, hp, if_false]
  apply runUnpack_ok
  intro hn
  subst ht
  rcases unpack_tables t c.fmtdef hc.1 hn with h | h | h
  · exact hc.2 h
  · exact hs h
  · exact hp h

theorem unpackRepeat_len (code : Code) (buf : List Nat) (hok : ∀ res, ∃ v, unpackOne code res = .ok v) :
    ∀ (j off : Nat), ∃ l, unpackRepeat code buf j off = .ok l ∧ l.length = j := by
  intro j
  induction j with
  | zero => intro off; exact ⟨[], rfl, rfl⟩
  | succ j ih =>
    intro off
    obtain ⟨v, hv⟩ := hok (buf.drop off)
    obtain ⟨l, hl, hlen⟩ := ih (off + code.size)
    refine ⟨v :: l, ?_, by simp [hlen]⟩
    simp [unpackRepeat, hv, hl, bind, Except.bind, pure, Except.pure]

theorem foldl_len (codes : List Code) (buf : List Nat)
    (hok : ∀ c ∈ codes, ∀ res, ∃ v, unpackOne c res = .ok v) :
    ∀ acc : List SV, ∃ l, codes.foldlM (init := acc) (fun acc code => do
        return acc ++ (← unpackRepeat code buf code.repeat_ code.offset)) = (.ok l : Py (List SV)) ∧
      l.length = acc.length + sumRepeat codes := by
  induction codes with
  | nil => intro acc; exact ⟨acc, rfl, by simp [sumRepeat]⟩
  | cons c cs ih =>
    intro acc
    obtain ⟨l, hl, hlen⟩ := unpackRepeat_len c buf (hok c (by simp)) c.repeat_ c.offset
    obtain ⟨l2, hl2, hlen2⟩ := ih (fun x hx => hok x (by simp [hx])) (acc ++ l)
    refine ⟨l2, ?_, ?_⟩
    · simp only [List.foldlM_cons, hl, bind, Except.bind, pure, Except.pure]
      exact hl2
    · rw [hlen2]
      simp [sumRepeat, hlen]
      omega

/-- For every accepted `str` format and every buffer of the struct's size, `unpack` succeeds and
returns exactly `s_len` values, one per item of the format (`s_unpack_internal`, 2038-2081, walks
every code `repeat` times). An `unpack` that returned `()` or dropped an item fails this. With a
`__buffer__` that calls `__init__`, the size and codes are the new ones (`structUnpackA`). -/
def UnpackLength : Prop :=
  ∀ (cps : List Nat) (s : SObj), structInit (.str cps) = .ok s →
    ∀ buf : List Nat, buf.length = s.sSize → ∃ l, structUnpack s buf = .ok l ∧ l.length = s.sLen

theorem unpackLength_proven : UnpackLength := by
  intro cps s h buf hl
  obtain ⟨st, _, _, hlen, _, _⟩ := prepareSAgree_proven cps s h
  have hg := prepareS_good cps s h
  have hok : ∀ c ∈ s.codes, ∀ res, ∃ v, unpackOne c res = .ok v :=
    fun c hc res => unpackOne_ok _ _ rfl c (hg c hc) res
  obtain ⟨l, hl2, hlen2⟩ := foldl_len s.codes buf hok []
  refine ⟨l, ?_, ?_⟩
  · simp only [structUnpack, hl, ne_eq, not_true_eq_false, if_false, sUnpackInternal]
    exact hl2
  · rw [hlen2, hlen]; simp

/-! ### `unpack_from` -/

/-- `unpack_from`: a non-negative offset with room for the struct reads the buffer from there (the
same as `unpack_from` of the tail at offset 0), and its three refusals carry the source's messages: a negative offset that
leaves less than `size` bytes (2143-2149), one before the start of the buffer (2151-2157), and a
buffer too short from a non-negative offset (2161-2171). An `unpack_from` that ignored the offset
fails the first part. -/
def UnpackFromLaws : Prop :=
  ∀ (s : SObj) (buf : List Nat), (buf.length : Int) ≤ longMax → (s.sSize : Int) ≤ longMax →
    (∀ off : Nat, off + s.sSize ≤ buf.length →
      structUnpackFrom s buf off = sUnpackInternal s (buf.drop off) ∧
      structUnpackFrom s (buf.drop off) 0 = sUnpackInternal s (buf.drop off)) ∧
    (∀ off : Int, longMin ≤ off → off < 0 → off + s.sSize > 0 →
      structUnpackFrom s buf off =
        .error (structErr s!"not enough data to unpack {(s.sSize : Int)} bytes at offset {off}")) ∧
    (∀ off : Int, longMin ≤ off → off < 0 → off + s.sSize ≤ 0 → off + buf.length < 0 →
      structUnpackFrom s buf off =
        .error (structErr s!"offset {off} out of range for {(buf.length : Int)}-byte buffer")) ∧
    (∀ off : Int, 0 ≤ off → off ≤ longMax → (buf.length : Int) - off < s.sSize →
      structUnpackFrom s buf off = .error (structErr
        s!"unpack_from requires a buffer of at least {(s.sSize : Int) + off} bytes for unpacking {(s.sSize : Int)} bytes at offset {off} (actual buffer size is {(buf.length : Int)})"))

theorem unpackFromLaws_proven : UnpackFromLaws := by
  intro s buf hb hs
  have hl : longMax = 9223372036854775807 := rfl
  have hm : longMin = -9223372036854775808 := rfl
  have harg : ∀ o : Int, longMin ≤ o → o ≤ longMax → ssizeArg o = .ok o := by
    intro o h1 h2; unfold ssizeArg; rw [if_neg (by omega)]
  refine ⟨fun off hoff => ?_, fun off h1 h2 h3 => ?_, fun off h1 h2 h3 h4 => ?_, fun off h1 h2 h3 => ?_⟩
  · have a1 := harg (off : Int) (by omega) (by omega)
    have a2 := harg 0 (by omega) (by omega)
    have n1 : ¬ ((off : Int) < 0) := by omega
    have n2 : ¬ ((0 : Int) < 0) := by omega
    have e1 : ((buf.drop off).length : Int) - 0 = (buf.length : Int) - (off : Int) := by
      simp only [List.length_drop]; omega
    have e2 : (0 : Int).toNat = 0 := rfl
    have e3 : (off : Int).toNat = off := by omega
    have n4 : ¬ ((buf.length : Int) - (off : Int) < s.sSize) := by omega
    simp only [structUnpackFrom, a1, a2, n1, n2, e1, e2, e3, n4, bind, Except.bind, pure, Except.pure, if_false,
      List.drop_zero, Int.add_zero]
    trivial
  · have a1 := harg off h1 (by omega)
    simp [structUnpackFrom, a1, h2, h3, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
  · have a1 := harg off h1 (by omega)
    have n3 : ¬ (off + (s.sSize : Int) > 0) := by omega
    simp [structUnpackFrom, a1, h2, n3, h4, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
  · have a1 := harg off (by omega) h2
    have n1 : ¬ off < 0 := by omega
    simp [structUnpackFrom, a1, n1, h3, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw]

/-! ### The iterator's length hint -/

/-- `__length_hint__` is the number of tuples the iterator still yields, on a struct left alone, and
`0` once `next()` has raised `StopIteration` (`so == NULL`, 2216-2217). A hint of a constant, or one
that ignored exhaustion, fails this. -/
def IterLenLaws : Prop :=
  (∀ (s : SObj) (buf : List Nat) (index fuel : Nat) (l : List (List SV)), 0 < s.sSize →
    (buf.length - index) % s.sSize = 0 → index ≤ buf.length →
    iterDrive s fuel { buf, index } = .ok l → iterLenU s { buf, index } = .ok l.length) ∧
  (∀ (s : SObj) (it : UIter), (iterNextU s it).2 = .ok none → iterLenU s (iterNextU s it).1 = .ok 0)

theorem iterLenLaws_proven : IterLenLaws := by
  refine ⟨fun s buf index fuel l hs hm hi h => ?_, fun s it h => ?_⟩
  · rw [iterDriveAgrees_proven s buf fuel index hs hm hi] at h
    have hlen := iterLoop_length s buf hs fuel index l h
    simp only [iterLenU, Bool.not_true, Bool.false_eq_true, if_false, Nat.ne_of_gt hs, if_false]
    rw [hlen]
    have hd : buf.length - index = s.sSize * ((buf.length - index) / s.sSize) := by
      have := Nat.div_add_mod (buf.length - index) s.sSize
      omega
    generalize (buf.length - index) / s.sSize = k at hd
    rw [hd]
    congr 1
    have e : s.sSize * k + s.sSize - 1 = (s.sSize - 1) + s.sSize * k := by omega
    rw [e, Nat.add_mul_div_left _ _ hs, Nat.div_eq_of_lt (by omega)]
    omega
  · cases hlive : it.live
    · simp [iterNextU, hlive, iterLenU]
    · by_cases hx : it.index ≥ it.buf.length
      · simp [iterNextU, hlive, hx, iterLenU]
      · by_cases hy : it.index + s.sSize > it.buf.length
        · simp [iterNextU, hlive, hx, hy] at h
        · simp only [iterNextU, hlive, hx, hy, Bool.not_true, Bool.false_eq_true, if_false] at h
          split at h <;> simp at h

end PyLean.TextLibs.Struct
