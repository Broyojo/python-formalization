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

/-! ## `err_format` of `unpack_single` and `pack_single` -/

/-- The formats the `switch` of `unpack_single` (:1825-1881) and of `pack_single` (:1941-2090)
convert: a first character among the eighteen of `nativeChars`, or `Z` followed by `f` or `d`. -/
def Converted (fmt : List Char) : Prop :=
  cc fmt 0 ∈ nativeChars ∨ (cc fmt 0 = 'Z' ∧ (cc fmt 1 = 'f' ∨ cc fmt 1 = 'd'))

/-- The `NotImplementedError` of `err_format`, :1908-1911 and :2098-2101. -/
def unsupportedFormat (fmt : List Char) : PyExc :=
  notImplError ("memoryview: format " ++ fmtText fmt ++ " not supported")

theorem unsupported_eq (fmt : List Char) :
    notImplError s!"memoryview: format {fmtText fmt} not supported" = unsupportedFormat fmt := by
  simp [unsupportedFormat, toString]

theorem not_converted (fmt : List Char) (h : ¬ Converted fmt) :
    cc fmt 0 ∉ nativeChars ∧ (cc fmt 0 = 'Z' → cc fmt 1 ≠ 'f' ∧ cc fmt 1 ≠ 'd') := by
  refine ⟨fun hm => h (Or.inl hm), fun hz => ⟨fun hf => h (Or.inr ⟨hz, Or.inl hf⟩),
    fun hd => h (Or.inr ⟨hz, Or.inr hd⟩)⟩⟩

theorem unpackRaw_unsupported (m : Mem) (ptr : Int) (fmt : List Char) (h : ¬ Converted fmt) :
    unpackRaw m ptr fmt = .error (unsupportedFormat fmt) := by
  obtain ⟨h1, h2⟩ := not_converted fmt h
  unfold unpackRaw
  split
  all_goals first
    | (exfalso; simp_all [nativeChars]; done)
    | (rw [unsupported_eq])
    | skip
  -- the `Z` arm
  rename_i hz
  have := h2 hz
  split
  · exact absurd ‹cc fmt 1 = 'f'› this.1
  · exact absurd ‹cc fmt 1 = 'd'› this.2
  · rfl

theorem unpackRaw_converted (m : Mem) (ptr : Int) (fmt : List Char) (h : Converted fmt) :
    ∃ x, unpackRaw m ptr fmt = .ok x := by
  unfold unpackRaw
  split
  all_goals first
    | exact ⟨_, rfl⟩
    | skip
  · rename_i hz
    rcases h with hm | ⟨-, hfd⟩
    · rw [hz] at hm; exact absurd hm (by decide)
    · split
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
      · rcases hfd with hf | hd <;> simp_all
  · rcases h with hm | ⟨hz, -⟩
    · simp only [nativeChars, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm <;>
        simp_all
    · simp_all

/-- `unpack_single`, :1804-1912, by format: the re-check `CHECK_RELEASED_AGAIN` (:1817) comes first,
then every format outside the `switch`, such as the `w` of `memoryview(array.array('w', 'ab'))`,
raises `NotImplementedError("memoryview: format w not supported")` (`err_format`, :1908-1911), and
every format in it gives an item. Nothing changes. No hypothesis. -/
def UnpackFormats : Prop :=
  ∀ (st : St) (self : Nat) (ptr : Int) (fmt : List Char),
    (baseInaccessible st self = true → unpackSingle self ptr fmt st = (.error releasedError, st)) ∧
    (baseInaccessible st self = false → ¬ Converted fmt →
      unpackSingle self ptr fmt st = (.error (unsupportedFormat fmt), st)) ∧
    (baseInaccessible st self = false → Converted fmt → ∃ x, unpackSingle self ptr fmt st = (.ok x, st))

theorem unpackFormats_proven : UnpackFormats := by
  intro st self ptr fmt
  refine ⟨fun h => ?_, fun h hc => ?_, fun h hc => ?_⟩
  · simp only [unpackSingle, M.bind_app, checkReleased_err _ _ h]
  · simp only [unpackSingle, M.bind_app, checkReleased_ok _ _ h, M.get, M.lift,
      unpackRaw_unsupported _ _ _ hc]
  · obtain ⟨x, hx⟩ := unpackRaw_converted st.mem ptr fmt hc
    exact ⟨x, by simp only [unpackSingle, M.bind_app, checkReleased_ok _ _ h, M.get, M.lift, hx]⟩

/-- `m[i]` on a live 1-D view whose format `adjust_fmt` lets through but `unpack_single` does not
convert, at an index `ptr_from_index` accepts, raises the `NotImplementedError` of `err_format`:
`memoryview(array.array('w', 'ab'))[0]` (`memory_item`, :2533-2559). -/
def ItemUnsupported : Prop :=
  ∀ (st : St) (self : Nat) (index p : Int) (fmt : List Char),
    baseInaccessible st self = false → adjustFmt (st.mv self).view = .ok fmt → ¬ Converted fmt →
    (st.mv self).view.ndim = 1 → ptrFromIndex st.mem (st.mv self).view index = .ok p →
    memoryItem self index st = (.error (unsupportedFormat fmt), st)

theorem itemUnsupported_proven : ItemUnsupported := by
  intro st self index p fmt h hf hc h1 hp
  simp only [memoryItem, M.bind_app, checkReleased_ok _ _ h, M.get, M.lift, hf, h1, hp,
    Nat.one_ne_zero, ↓reduceIte, unpackSingle, unpackRaw_unsupported _ _ _ hc]

/-- The format of an `array.array('w')` passes `adjust_fmt` and is not converted. -/
theorem w_unsupported (v : Buf) (h : v.format = some ['w']) :
    adjustFmt v = .ok ['w'] ∧ ¬ Converted ['w'] := by
  refine ⟨by simp [adjustFmt, h, cc], ?_⟩
  simp [Converted, nativeChars, cc]

theorem packSingle_unsupported (self : Nat) (ptr : Int) (item : Obj) (fmt : List Char) (st : St)
    (h : ¬ Converted fmt) : packSingle self ptr item fmt st = (.error (unsupportedFormat fmt), st) := by
  obtain ⟨h1, h2⟩ := not_converted fmt h
  unfold packSingle
  generalize cc fmt 0 = x at h1 h2 ⊢
  split
  all_goals first
    | (exfalso; simp [nativeChars] at h1; done)
    | skip
  · have := h2 rfl
    generalize cc fmt 1 = y at this ⊢
    split
    · exact absurd rfl this.2
    · exact absurd rfl this.1
    · simp only [M.throw_app, unsupported_eq]
  · simp only [M.throw_app, unsupported_eq]

/-- `pack_single`, :1923-2102, on a format outside its `switch`: `NotImplementedError("memoryview: format
w not supported")` (`err_format`, :2098-2101) before anything is converted, so whatever the item, no
`__index__`, `__float__` or `__bool__` runs and nothing changes. Through `memory_ass_sub` (:2758-2771):
`m[i] = x` on a writable 1-D view of such a format, at a valid index, raises it, as
`memoryview(array.array('w', 'ab'))[0] = 'c'` does. Hypotheses: for the second part, the checks
`memory_ass_sub` makes first pass (live, format accepted, writable, 1-D), `i` is a `Py_ssize_t`,
and `ptr_from_index` accepts it. -/
def PackUnsupported : Prop :=
  ∀ (st : St) (self : Nat) (item : Obj) (fmt : List Char), ¬ Converted fmt →
    (∀ ptr : Int, packSingle self ptr item fmt st = (.error (unsupportedFormat fmt), st)) ∧
    (∀ (n p : Int), baseInaccessible st self = false → adjustFmt (st.mv self).view = .ok fmt →
      (st.mv self).view.readonly = false → (st.mv self).view.ndim = 1 →
      ssizeMin ≤ n ∧ n ≤ ssizeMax → ptrFromIndex st.mem (st.mv self).view n = .ok p →
      memoryAssSub self (.one (.obj (.int n))) (some item) st = (.error (unsupportedFormat fmt), st))

theorem packUnsupported_proven : PackUnsupported := by
  intro st self item fmt hc
  refine ⟨fun ptr => packSingle_unsupported self ptr item fmt st hc, fun n p h hf hro h1 hn hp => ?_⟩
  have hk : keyAsSsize (.int n) n = .ok n := by simp [keyAsSsize, hn]
  simp only [memoryAssSub, M.bind_app, checkReleased_ok _ _ h, M.get, M.lift, hf, hro, h1,
    Bool.false_eq_true, ↓reduceIte, Nat.one_ne_zero, Obj.isIndex, Nat.lt_irrefl, numberIndex, M.pure_app,
    hk, hp, packSingle_unsupported self p item fmt st hc]

/-! ## `pack_single`: the re-checks after the item's own callback -/

/-- `pack_single`, :1923-2102, when the item's own conversion callback does `m.release()` on the view
being written and then returns normally (gh-92888): each arm that converts through Python code
re-checks with `CHECK_RELEASED_INT_AGAIN` after the conversion and before anything is written, so
`m[0] = x` raises `ValueError("operation forbidden on released memoryview object")`, the release has
happened, and the store is unchanged. The order is pinned both ways: a conversion error comes first
(`2**70` in any integer format, `-1` in an unsigned one, a negative `__len__`), but the range check
of `b`, `h`, `i` (:1950-1957) and the overflow of `PyFloat_Pack2` (:2029) come after the re-check, so
`__index__` returning 200 into format `b`, or `__float__` returning `1e300` into `e`, still reports
the release. Integer formats run `__index__`, `f`, `d`, `e`, `Zf`, `Zd` run `__float__`, `?` runs
`__bool__` or `__len__`. Hypotheses: `self` is a view of the state, with no exports, so the
callback's `release()` succeeds (a refused release is the `BufferError` the callback swallows). -/
def PackItemReleases : Prop :=
  ∀ (st : St) (self : Nat) (ptr : Int), self < st.mvs.length → (st.mv self).exports = 0 →
    let st1 := (memoryRelease self st).2
    (∀ c ∈ ['b', 'h', 'i', 'l', 'q', 'n'], ∀ n : Int,
      packSingle self ptr (.index (.val n) (some self)) [c] st =
        (.error (if -2 ^ 63 ≤ n ∧ n < 2 ^ 63 then releasedError else valueErrorInt [c]), st1)) ∧
    (∀ c ∈ ['B', 'H', 'I', 'L', 'Q', 'N'], ∀ n : Int,
      packSingle self ptr (.index (.val n) (some self)) [c] st =
        (.error (if 0 ≤ n ∧ n < 2 ^ 64 then releasedError else valueErrorInt [c]), st1)) ∧
    (∀ fmt ∈ [['f'], ['d'], ['e'], ['Z', 'f'], ['Z', 'd']], ∀ bits : Nat,
      packSingle self ptr (.floatLike (.val bits) (some self)) fmt st = (.error releasedError, st1)) ∧
    (∀ b : Bool, packSingle self ptr (.boolLike (.val b) (some self)) ['?'] st = (.error releasedError, st1)) ∧
    (∀ n : Int, packSingle self ptr (.lenLike (.val n) (some self)) ['?'] st =
      (.error (if n < 0 then .valueError "__len__() should return >= 0" else releasedError), st1)) ∧
    st1.mem = st.mem

theorem fire_release (st : St) (self : Nat) (h : (st.mv self).exports = 0) :
    fire (some self) st = (.ok (), (memoryRelease self st).2) := by
  rw [fire_self st self h]
  exact Prod.ext (memoryRelease_ok self st) rfl

theorem packItemReleases_proven : PackItemReleases := by
  intro st self ptr hs he
  dsimp only
  have hf := fire_release st self he
  have hin := memoryRelease_inaccessible self st hs
  have hrel := checkReleased_err _ _ hin
  have hidx : ∀ n, numberIndex (.index (.val n) (some self)) st = (.ok n, (memoryRelease self st).2) :=
    fun n => numberIndex_val n (some self) st _ hf
  refine ⟨?_, ?_, ?_, ?_, ?_, (memoryRelease_mono self st).mem⟩
  · intro c hc n
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    by_cases hr : -2 ^ 63 ≤ n ∧ n < 2 ^ 63
    · have h1 : asLong n = .ok n := asLong_ok n (by omega)
      have h2 : longAsSsize n = .ok n := longAsSsize_ok n (by omega)
      rw [if_pos hr]
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [packSingle, cc, List.getD_cons_zero, M.bind_app, M.mapErr, pylongAsLd, pylongAsLld,
          pylongAsZd, hidx, lift_apply, h1, h2, hrel]
    · have h1 := asLong_err n (by omega)
      have h2 := longAsSsize_err n (by omega)
      rw [if_neg hr]
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [packSingle, cc, List.getD_cons_zero, M.bind_app, M.mapErr, pylongAsLd, pylongAsLld,
          pylongAsZd, hidx, lift_apply, h1, h2, fixErrorInt_overflow]
  · intro c hc n
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    by_cases hr : 0 ≤ n ∧ n < 2 ^ 64
    · have h1 : asUnsignedLong n = .ok n := asUnsignedLong_ok n (by omega)
      rw [if_pos hr]
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [packSingle, cc, List.getD_cons_zero, M.bind_app, M.mapErr, pylongAsLu, pylongAsLlu,
          pylongAsZu, hidx, lift_apply, h1, hrel]
    · obtain ⟨m, h1⟩ := asUnsignedLong_err n (by omega)
      rw [if_neg hr]
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [packSingle, cc, List.getD_cons_zero, M.bind_app, M.mapErr, pylongAsLu, pylongAsLlu,
          pylongAsZu, hidx, lift_apply, h1, fixErrorInt_overflow]
  · intro fmt hfm bits
    have hd : floatAsDouble (.floatLike (.val bits) (some self)) st = (.ok bits, (memoryRelease self st).2) := by
      simp only [floatAsDouble, M.bind_app, hf]; rfl
    have hc : complexAsC (.floatLike (.val bits) (some self)) st = (.ok (bits, 0), (memoryRelease self st).2) := by
      simp only [complexAsC, M.bind_app, hd]; rfl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hfm
    rcases hfm with rfl | rfl | rfl | rfl | rfl <;>
      simp only [packSingle, cc, List.getD_cons_zero, List.getD_cons_succ, M.bind_app, M.mapErr, hd, hc, hrel]
  · intro b
    have hb : isTrue (.boolLike (.val b) (some self)) st = (.ok b, (memoryRelease self st).2) := by
      simp only [isTrue, M.bind_app, hf]; rfl
    simp only [packSingle, cc, List.getD_cons_zero, M.bind_app, hb, hrel]
  · intro n
    by_cases hn : n < 0
    · have hb : isTrue (.lenLike (.val n) (some self)) st =
          (.error (.valueError "__len__() should return >= 0"), (memoryRelease self st).2) := by
        simp only [isTrue, M.bind_app, hf, Ret.get, M.pure_app, hn, ↓reduceIte, M.throw_app]
      rw [if_pos hn]
      simp only [packSingle, cc, List.getD_cons_zero, M.bind_app, hb]
    · have hb : isTrue (.lenLike (.val n) (some self)) st = (.ok (n != 0), (memoryRelease self st).2) := by
        simp only [isTrue, M.bind_app, hf, Ret.get, M.pure_app, hn, ↓reduceIte]
      rw [if_neg hn]
      simp only [packSingle, cc, List.getD_cons_zero, M.bind_app, hb, hrel]

/-- `pack_single` on `Zf` and `Zd` (:2036-2058) when `PyComplex_AsCComplex` fails: what fails is
`PyFloat_AsDouble`, inside it, and `err_occurred` hands it to `fix_error_int`, so a `__float__` that
raises a `ValueError` gives `ValueError("memoryview: invalid value for format 'Zd'")`, one that raises
anything outside `TypeError`, `ValueError` and `OverflowError` passes it on unchanged (a `KeyError`
stays a `KeyError`), a `__float__` returning a non-float and a `str` item give
`TypeError("memoryview: invalid type for format 'Zd'")`, and a raising `__index__` behaves as in the
float formats. Nothing is written and the callback's release, if any, stays. No hypothesis. -/
def PackComplexFailures : Prop :=
  ∀ (self : Nat) (ptr : Int) (r : Option Nat) (e : PyExc) (t : String) (s : List Char) (st st' : St),
    fire r st = (.ok (), st') →
    (∀ fmt ∈ [['Z', 'f'], ['Z', 'd']],
      packSingle self ptr (.floatLike (.raises e) r) fmt st = (.error (fixErrorInt fmt e), st') ∧
      packSingle self ptr (.floatLike (.wrong t) r) fmt st = (.error (typeErrorInt fmt), st') ∧
      packSingle self ptr (.index (.raises e) r) fmt st = (.error (fixErrorInt fmt e), st') ∧
      packSingle self ptr (.str s) fmt st = (.error (typeErrorInt fmt), st)) ∧
    st'.mem = st.mem

theorem packComplexFailures_proven : PackComplexFailures := by
  intro self ptr r e t s st st' h
  refine ⟨fun fmt hfm => ?_, fire_mem r st st' h⟩
  have i1 : complexAsC (.floatLike (.raises e) r) st = (.error e, st') := by
    simp only [complexAsC, M.bind_app, floatAsDouble_raises e r st st' h]
  have i2 : complexAsC (.floatLike (.wrong t) r) st = (.error (floatWrong t), st') := by
    simp only [complexAsC, M.bind_app, floatAsDouble_wrong t r st st' h]
  have i3 : complexAsC (.index (.raises e) r) st = (.error e, st') := by
    simp only [complexAsC, floatAsDouble, M.bind_app, h, Ret.get, M.throw_app]
  have i4 : complexAsC (.str s) st = (.error (.typeError "must be real number, not str"), st) := rfl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfm
  rcases hfm with rfl | rfl <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [packSingle, cc, List.getD_cons_zero, List.getD_cons_succ, M.bind_app, M.mapErr, i1, i2, i3, i4,
      floatWrong, fixErrorInt_type]

/-! ## `memory_ass_sub`: the keys it refuses -/

/-- The three key refusals of `memory_ass_sub` (:2722-2823) that `AssSubRules` leaves out, once the
earlier checks pass (live, format accepted, writable, a value, not 0-dim). On a view of two or more
dimensions, a single index is `NotImplementedError("sub-views are not implemented")` (:2760-2764),
raised before `PyNumber_AsSsize_t`, so the key's `__index__` never runs; a single slice is
`NotImplementedError("memoryview slice assignments are currently restricted to ndim = 1")`
(:2812-2818), raised before anything looks at the value or the slice. On a view of any dimension, a
key that is neither an index nor a slice nor a tuple, such as `1.5`, `'a'` or `None`, is
`TypeError("memoryview: invalid slice key")` (:2821). The state is unchanged in each, whatever the key's
or the value's callbacks would do, so storing row 0 for `m[i] = x` on a 2-D view is excluded. -/
def AssSubKeyRefusals : Prop :=
  ∀ (st : St) (self : Nat) (value : Obj) (fmt : List Char), baseInaccessible st self = false →
    let v := (st.mv self).view
    adjustFmt v = .ok fmt → v.readonly = false → v.ndim ≠ 0 →
    (∀ o : Obj, o.isIndex = false →
      memoryAssSub self (.one (.obj o)) (some value) st =
        (.error (.typeError "memoryview: invalid slice key"), st)) ∧
    (1 < v.ndim → ∀ o : Obj, o.isIndex = true →
      memoryAssSub self (.one (.obj o)) (some value) st =
        (.error (notImplError "sub-views are not implemented"), st)) ∧
    (1 < v.ndim → ∀ s rel fail,
      memoryAssSub self (.one (.slice s rel fail)) (some value) st =
        (.error (notImplError "memoryview slice assignments are currently restricted to ndim = 1"), st))

theorem assSubKeyRefusals_proven : AssSubKeyRefusals := by
  intro st self value fmt hl
  dsimp only
  intro hf hro h0
  have e := checkReleased_ok st self hl
  refine ⟨fun o ho => ?_, fun h1 o ho => ?_, fun h1 s rel fail => ?_⟩
  · simp [memoryAssSub, M.bind_app, e, M.get, M.lift, hf, hro, h0, ho, M.throw_app]
  · simp [memoryAssSub, M.bind_app, e, M.get, M.lift, hf, hro, h0, ho, h1, M.throw_app]
  · have h1' : (st.mv self).view.ndim ≠ 1 := by omega
    simp [memoryAssSub, M.bind_app, e, M.get, M.lift, hf, hro, h0, h1', M.throw_app]

/-! ## `memory_richcompare`: an operand without a buffer -/

/-- An object with no `bf_getbuffer` in this model: everything but a memoryview, `bytes` and an exporter. -/
def NoBuffer : Obj → Prop
  | .view _ | .bytes _ | .exporter _ _ => False
  | _ => True

/-- `memory_richcompare`, :3201-3326, when the other operand gives no buffer: `PyObject_GetBuffer`
fails, `PyErr_Clear` drops the error and the result is `NotImplemented` (:3253-3257), so
`memoryview(b'a').__eq__(5)` is `NotImplemented` and `==` falls back to identity. This holds for an
int, a str, None, a list and every other object without a buffer, with nothing changed, and for an
exporter whose `__buffer__` raises, returns a non-memoryview, or gives more than 64 dimensions: the
exception is not raised, and only the callback's release stays. Hypotheses: `==` or `!=` (other
operators are `NotImplemented` at :3212-3213 already), and a live `v`, since a released `v` compares
by identity first (:3216-3219). -/
def CompareNoBuffer : Prop :=
  ∀ (st : St) (v : Nat) (op : CmpOp), op ≠ .other → baseInaccessible st v = false →
    (∀ w : Obj, NoBuffer w → memoryRichcompare v w op st = (.ok none, st)) ∧
    (∀ (r : Option Nat) (e : PyExc) (t : String) (st' : St), fire r st = (.ok (), st') →
      memoryRichcompare v (.exporter (.raises e) r) op st = (.ok none, st') ∧
      memoryRichcompare v (.exporter (.wrong t) r) op st = (.ok none, st') ∧
      ∀ b : Buf, b.ndim > 64 → memoryRichcompare v (.exporter (.val b) r) op st = (.ok none, st'))

/-- `memory_richcompare` when `PyObject_GetBuffer(w)` fails: `NotImplemented`, the error cleared. -/
theorem richcompare_getbuf_fails (st st' : St) (v : Nat) (op : CmpOp) (x : Ret Buf) (r : Option Nat)
    (e : PyExc) (hop : op ≠ .other) (hl : baseInaccessible st v = false)
    (hg : getBufferFull (.exporter x r) st = (.error e, st')) :
    memoryRichcompare v (.exporter x r) op st = (.ok none, st') := by
  have hm : (some <$> getBufferFull (.exporter x r) : M (Option Buf)) st = (.error e, st') := by
    show (getBufferFull (.exporter x r) >>= fun a => pure (some a)) st = _
    rw [M.bind_app, hg]
  have tc : (tryCatch (some <$> getBufferFull (.exporter x r))
      (fun _ => pure Option.none) : M (Option Buf)) st = (.ok none, st') := by
    simp [tryCatch, MonadExcept.tryCatch, hm]
    rfl
  have hq : ((Obj.exporter x r == Obj.view v) && selfEqualFormat (st.mv v).view.format) = false := by
    simp
  have he : memoryRichEqual v (.exporter x r) st = (.ok none, st') := by
    simp only [memoryRichEqual, M.bind_app, M.get, hl, Bool.false_eq_true, ↓reduceIte, hq, tc]
    rfl
  simp only [memoryRichcompare, hop, ↓reduceIte, M.bind_app, he]
  rfl

theorem compareNoBuffer_proven : CompareNoBuffer := by
  intro st v op hop hl
  refine ⟨fun w hw => ?_, fun r e t st' h => ⟨?_, ?_, fun b hb => ?_⟩⟩
  · cases w <;> simp_all [NoBuffer, memoryRichcompare, memoryRichEqual, M.bind_app, M.get, M.pure_app]
  · exact richcompare_getbuf_fails st st' v op _ r e hop hl
      (bufferFailures_proven r e t 0 st st' h).2.2.2.2.1
  · exact richcompare_getbuf_fails st st' v op _ r _ hop hl
      (bufferFailures_proven r e t 0 st st' h).2.2.2.2.2.1
  · refine richcompare_getbuf_fails st st' v op _ r
      (.valueError "memoryview: number of dimensions must not exceed 64") hop hl ?_
    simp only [getBufferFull, M.bind_app, h, Ret.get, M.pure_app, hb, ↓reduceIte, M.throw_app]

end PyLean.BytesObj.Mem
