import PyLean.BytesObj.Mem.Effects

/-!
Exact statements of what five functions of `Objects/memoryobject.c` accept and refuse:
`get_native_fmtchar` and `get_native_fmtstr` against `struct`'s native table, the
`err_format` exits of `unpack_single` and `pack_single`, the re-checks of `pack_single`
after the item's own callback, the key refusals of `memory_ass_sub`, and the
`NotImplemented` of `memory_richcompare` for an operand without a buffer.
-/

namespace PyLean.BytesObj.Mem

open PyLean

/-! ## The native format table -/

/-- `struct`'s native table on this build (x86-64 Linux, LP64), written out: every format text
`memoryview.cast` accepts after an optional `@`, with the item size `struct.calcsize` gives it.
It is data, not the model's `fmtSize`: the sizes were read from `struct.calcsize` on 3.15.2. -/
def nativeFormats : List (List Char × Int) :=
  [(['c'], 1), (['b'], 1), (['B'], 1), (['h'], 2), (['H'], 2), (['i'], 4), (['I'], 4),
   (['l'], 8), (['L'], 8), (['q'], 8), (['Q'], 8), (['n'], 8), (['N'], 8),
   (['f'], 4), (['d'], 8), (['e'], 2), (['?'], 1), (['P'], 8),
   (['Z', 'f'], 8), (['Z', 'd'], 16)]

/-- A C string as the characters before its terminating NUL: what `strcmp` and `strlen` see. -/
def cstr (s : List Char) : List Char := s.takeWhile (fun c => c != '\x00')

/-- `strcmp(s, t) == 0`, position by position. -/
def Spells : List Char → List Char → Prop
  | s, [] => cc s 0 = '\x00'
  | s, x :: t => cc s 0 = x ∧ Spells (s.drop 1) t

theorem cc_drop (s : List Char) (n i : Nat) : cc (s.drop n) i = cc s (n + i) := by
  simp [cc, List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem cstr_eq_iff (t : List Char) (ht : '\x00' ∉ t) (s : List Char) : cstr s = t ↔ Spells s t := by
  induction t generalizing s with
  | nil =>
    cases s with
    | nil => simp [cstr, Spells, cc]
    | cons y u =>
      by_cases hy : y = '\x00'
      · subst hy; simp [cstr, Spells, cc]
      · simp [cstr, Spells, cc, hy]
  | cons x t ih =>
    have hx : x ≠ '\x00' := fun h => ht (h ▸ List.mem_cons_self ..)
    have ht' : '\x00' ∉ t := fun h => ht (List.mem_cons_of_mem _ h)
    cases s with
    | nil => simp [cstr, Spells, cc, Ne.symm hx]
    | cons y u =>
      by_cases hy : y = '\x00'
      · subst hy; simp [cstr, Spells, cc, Ne.symm hx]
      · have e1 : cstr (y :: u) = y :: cstr u := by unfold cstr; simp [List.takeWhile_cons, hy]
        have e2 : Spells (y :: u) (x :: t) ↔ y = x ∧ Spells u t := by simp [Spells, cc]
        rw [e1, e2, List.cons.injEq, ih ht' u]

/-- The 18 one-character entries of the table. -/
def nativeChars : List Char :=
  ['c', 'b', 'B', 'h', 'H', 'i', 'I', 'l', 'L', 'q', 'Q', 'n', 'N', 'f', 'd', 'e', '?', 'P']

theorem fmtSize_pos_chars (x : Char) (h : fmtSize x > 0) : x ∈ nativeChars := by
  unfold fmtSize at h
  split at h <;> simp_all [nativeChars]

theorem fmtSize_pos_mem (x : Char) (h : fmtSize x > 0) : ([x], fmtSize x) ∈ nativeFormats := by
  have hx := fmtSize_pos_chars x h
  simp only [nativeChars, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;> decide

theorem fmtSize_pos_code (x : Char) (h : fmtSize x > 0) : codeText x = [x] := by
  have h1 : x ≠ zfCode := by rintro rfl; exact absurd h (by decide)
  have h2 : x ≠ zdCode := by rintro rfl; exact absurd h (by decide)
  simp [codeText, h1, h2]

theorem codeText_one (c x : Char) (h : codeText c = [x]) : c = x := by
  unfold codeText at h
  by_cases h1 : c = zfCode <;> by_cases h2 : c = zdCode <;> simp_all

theorem codeText_zf (c : Char) (h : codeText c = ['Z', 'f']) : c = zfCode := by
  unfold codeText at h
  have hzd : zdCode ≠ zfCode := by decide
  by_cases h1 : c = zfCode
  · exact h1
  · by_cases h2 : c = zdCode
    · subst h2; simp [hzd] at h
    · simp [h1, h2] at h

theorem codeText_zd (c : Char) (h : codeText c = ['Z', 'd']) : c = zdCode := by
  unfold codeText at h
  by_cases h1 : c = zfCode
  · subst h1; simp at h
  · by_cases h2 : c = zdCode
    · exact h2
    · simp [h1, h2] at h

theorem cc_tail (s : List Char) (i : Nat) : cc s.tail i = cc s (i + 1) := by
  rw [← List.drop_one, cc_drop, Nat.add_comm]

/-- `get_native_fmtchar`, memoryobject.c:1203-1241, exactly: it accepts a format when the C string,
after one optional `@`, is an entry of `struct`'s native table (`Zf` and `Zd`, new in 3.15, included),
and then returns that entry's size and the entry itself (`codeText`). Nothing else is accepted, so not
`x`, `@@B`, `Z`, `Zfx` or the empty string. The C string is what precedes the first NUL, so
`B\0xyz` is `B` (the refutation `castWholeFormat_refuted`). No hypothesis. -/
def NativeFmtcharSpec : Prop :=
  ∀ (fmt : List Char) (c : Char) (size : Int),
    getNativeFmtchar fmt = some (c, size) ↔
      ∃ t, (t, size) ∈ nativeFormats ∧ codeText c = t ∧ (cstr fmt = t ∨ cstr fmt = '@' :: t)

/-- `get_native_fmtstr`, memoryobject.c:1243-1297, exactly: it accepts the same strings, and what it
returns is the C string itself, `@` kept, so `m.cast('@B').format` is `'@B'` and
`m.cast('@Zd').format` is `'@Zd'`. No hypothesis. -/
def NativeFmtstrSpec : Prop :=
  ∀ (fmt r : List Char),
    getNativeFmtstr fmt = some r ↔
      r = cstr fmt ∧ ∃ t size, (t, size) ∈ nativeFormats ∧ (r = t ∨ r = '@' :: t)

/-- The `(c, size)` branch of `get_native_fmtchar` after the `@`, on the format `f`. -/
theorem fmtchar_branch (f : List Char) (c : Char) (size : Int)
    (h : (if cc f 0 = 'Z' then
        if cc f 1 = 'f' ∧ cc f 2 = '\x00' then some (zfCode, (8 : Int))
        else if cc f 1 = 'd' ∧ cc f 2 = '\x00' then some (zdCode, 16) else none
      else if fmtSize (cc f 0) > 0 ∧ cc f 1 = '\x00' then some (cc f 0, fmtSize (cc f 0)) else none) =
      some (c, size)) :
    ∃ t, (t, size) ∈ nativeFormats ∧ codeText c = t ∧ cstr f = t := by
  by_cases hz : cc f 0 = 'Z'
  · rw [if_pos hz] at h
    by_cases hf : cc f 1 = 'f' ∧ cc f 2 = '\x00'
    · rw [if_pos hf] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨['Z', 'f'], by simp [nativeFormats], by simp [codeText], ?_⟩
      rw [cstr_eq_iff _ (by decide)]
      simp [Spells, cc_drop, cc_tail, hz, hf.1, hf.2]
    · rw [if_neg hf] at h
      by_cases hd : cc f 1 = 'd' ∧ cc f 2 = '\x00'
      · rw [if_pos hd] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨['Z', 'd'], by simp [nativeFormats], by simp [codeText, show zdCode ≠ zfCode by decide], ?_⟩
        rw [cstr_eq_iff _ (by decide)]
        simp [Spells, cc_drop, cc_tail, hz, hd.1, hd.2]
      · rw [if_neg hd] at h
        simp at h
  · rw [if_neg hz] at h
    by_cases hs : fmtSize (cc f 0) > 0 ∧ cc f 1 = '\x00'
    · rw [if_pos hs] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hnz : cc f 0 ≠ '\x00' := by intro e; rw [e] at hs; exact absurd hs.1 (by decide)
      refine ⟨[cc f 0], fmtSize_pos_mem _ hs.1, fmtSize_pos_code _ hs.1, ?_⟩
      rw [cstr_eq_iff _ (by simp [Ne.symm hnz])]
      simp [Spells, cc_drop, cc_tail, hs.2]
    · rw [if_neg hs] at h
      simp at h

theorem cstr_at (fmt : List Char) (h0 : cc fmt 0 = '@') : cstr fmt = '@' :: cstr (fmt.drop 1) := by
  cases fmt with
  | nil => simp [cc] at h0
  | cons y u =>
    simp only [cc, List.getD_cons_zero] at h0
    subst h0
    unfold cstr
    simp [List.takeWhile_cons]

theorem cstr_ne_at (fmt t : List Char) (h0 : cc fmt 0 ≠ '@') : cstr fmt ≠ '@' :: t := by
  cases fmt with
  | nil => simp [cstr]
  | cons y u =>
    simp only [cc, List.getD_cons_zero] at h0
    unfold cstr
    by_cases hy : y = '\x00'
    · simp [List.takeWhile_cons, hy]
    · simp [List.takeWhile_cons, hy, h0]

theorem nativeFmtcharSpec_proven : NativeFmtcharSpec := by
  intro fmt c size
  constructor
  · intro h
    unfold getNativeFmtchar at h
    by_cases h0 : cc fmt 0 = '@'
    · simp only [h0, ↓reduceIte] at h
      obtain ⟨t, hm, hc, hs⟩ := fmtchar_branch _ _ _ h
      exact ⟨t, hm, hc, Or.inr (by rw [cstr_at fmt h0, hs])⟩
    · simp only [h0, ↓reduceIte] at h
      obtain ⟨t, hm, hc, hs⟩ := fmtchar_branch _ _ _ h
      exact ⟨t, hm, hc, Or.inl hs⟩
  · rintro ⟨t, hm, hc, hs⟩
    simp only [nativeFormats, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals
      rw [cstr_eq_iff _ (by decide), cstr_eq_iff _ (by decide)] at hs
      simp only [Spells, cc_drop, cc_tail, Nat.reduceAdd, List.drop_one] at hs
      first
        | obtain rfl := codeText_one _ _ hc
        | obtain rfl := codeText_zf _ hc
        | obtain rfl := codeText_zd _ hc
      rcases hs with h | h <;>
        simp [getNativeFmtchar, cc_drop, cc_tail, h, fmtSize]

theorem nativeChar_pos (x : Char) (h : nativeChar x = true) : fmtSize x > 0 := (fmtSize_pos_iff x).2 h

/-- The branch of `get_native_fmtstr` after the `@`, on the format `f`; `mk` puts the `@` back. -/
theorem fmtstr_branch (f : List Char) (mk : List Char → List Char) (r : List Char)
    (h : (if cc f 0 = '\x00' then none
      else if cc f 0 = 'Z' then
        if cc f 1 = '\x00' ∨ cc f 2 ≠ '\x00' then none
        else if cc f 1 = 'f' ∨ cc f 1 = 'd' then some (mk ['Z', cc f 1])
        else none
      else if cc f 1 ≠ '\x00' then none
      else if nativeChar (cc f 0) then some (mk [cc f 0])
      else none) = some r) :
    ∃ t size, (t, size) ∈ nativeFormats ∧ r = mk t ∧ cstr f = t := by
  by_cases h0 : cc f 0 = '\x00'
  · rw [if_pos h0] at h; simp at h
  rw [if_neg h0] at h
  by_cases hz : cc f 0 = 'Z'
  · rw [if_pos hz] at h
    by_cases h1 : cc f 1 = '\x00' ∨ cc f 2 ≠ '\x00'
    · rw [if_pos h1] at h; simp at h
    rw [if_neg h1] at h
    have h2 : cc f 2 = '\x00' := Classical.byContradiction fun hc => h1 (Or.inr hc)
    by_cases hfd : cc f 1 = 'f' ∨ cc f 1 = 'd'
    · rw [if_pos hfd] at h
      simp only [Option.some.injEq] at h
      subst h
      rcases hfd with hf | hd
      · refine ⟨['Z', 'f'], 8, by simp [nativeFormats], by rw [hf], ?_⟩
        rw [cstr_eq_iff _ (by decide)]
        simp [Spells, cc_drop, cc_tail, hz, hf, h2]
      · refine ⟨['Z', 'd'], 16, by simp [nativeFormats], by rw [hd], ?_⟩
        rw [cstr_eq_iff _ (by decide)]
        simp [Spells, cc_drop, cc_tail, hz, hd, h2]
    · rw [if_neg hfd] at h; simp at h
  · rw [if_neg hz] at h
    by_cases h1 : cc f 1 ≠ '\x00'
    · rw [if_pos h1] at h; simp at h
    rw [if_neg h1] at h
    by_cases hn : nativeChar (cc f 0) = true
    · rw [if_pos hn] at h
      simp only [Option.some.injEq] at h
      subst h
      have hp := nativeChar_pos _ hn
      refine ⟨[cc f 0], fmtSize (cc f 0), fmtSize_pos_mem _ hp, rfl, ?_⟩
      rw [cstr_eq_iff _ (by simp [Ne.symm h0])]
      simp only [Spells, cc_drop, cc_tail, Nat.reduceAdd, List.drop_one, true_and]
      exact Classical.not_not.mp h1
    · rw [if_neg hn] at h; simp at h

theorem nativeFmtstrSpec_proven : NativeFmtstrSpec := by
  intro fmt r
  constructor
  · intro h
    unfold getNativeFmtstr at h
    by_cases h0 : cc fmt 0 = '@'
    · simp only [h0, ↓reduceIte] at h
      obtain ⟨t, size, hm, hr, hs⟩ := fmtstr_branch (fmt.drop 1) (fun l => '@' :: l) r h
      refine ⟨by rw [cstr_at fmt h0, hs, hr], t, size, hm, Or.inr hr⟩
    · simp only [h0, ↓reduceIte] at h
      obtain ⟨t, size, hm, hr, hs⟩ := fmtstr_branch fmt id r h
      exact ⟨by rw [hs, hr]; rfl, t, size, hm, Or.inl hr⟩
  · rintro ⟨hr, t, size, hm, ht⟩
    subst hr
    simp only [nativeFormats, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals
      rcases ht with ht | ht <;>
      · rw [ht]
        have hs := ht
        rw [cstr_eq_iff _ (by decide)] at hs
        simp only [Spells, cc_drop, cc_tail, Nat.reduceAdd, List.drop_one] at hs
        simp [getNativeFmtstr, cc_drop, cc_tail, hs, nativeChar]

/-- `m.cast(format)` keeps the format text it was given: on every cast that `Cast1DSpec` describes,
the new view's `format` is the C string of `format`, `@` included. -/
def CastKeepsFormat : Prop :=
  ∀ (st : St) (self : Nat) (format : List Char) (c : Char) (size : Int),
    self < st.mvs.length → (st.mv self).mbuf < st.mbufs.length →
    baseInaccessible st self = false → (st.mv self).flags.restricted = false →
    (st.mv self).flags.isC = true →
    ((st.mv self).view.ndim = 1 ∨ ¬ HasZero (st.mv self).view) →
    (∀ ch ∈ format, ch.toNat < 128) →
    getNativeFmtchar format = some (c, size) →
    (srcIsByte (st.mv self).view = true ∨ isByteFormat c = true) →
    (st.mv self).view.len.tmod size = 0 →
    let r := memoryviewCast self format none st
    r.1 = .ok st.mvs.length ∧ (r.2.mv st.mvs.length).view.format = some (cstr format)

theorem castKeepsFormat_proven : CastKeepsFormat := by
  intro st self format c size h1 h2 h3 h4 h5 h6 h7 hf h9 h10
  have hsome := (nativeFormatAgree_proven format).1
  rw [hf] at hsome
  obtain ⟨fstr, hs⟩ := Option.isSome_iff_exists.mp hsome.symm
  have hcs := ((nativeFmtstrSpec_proven format fstr).1 hs).1
  obtain ⟨ok, hv, -⟩ := cast1DSpec_proven st self format c size fstr h1 h2 h3 h4 h5 h6 h7 hf hs h9 h10
  refine ⟨ok, ?_⟩
  rw [hv, ← hcs]
  rfl

end PyLean.BytesObj.Mem
