import PyLean.PyIO.StringProps

/-!
`StringIO(value, newline)` followed by `read()` and `newlines`, in both twins
(`Lib/_pyio.py:2090-2153`, :2309-2315, :2597-2627, :2732-2733, :2747-2761;
`Modules/_io/stringio.c:684-792`, :327-355, :1037-1046).
-/

namespace PyLean.PyIO

open PyLean

/-- What a legal `newline` makes of the initial value when it is written: `'\n'`
becomes `newline` when that starts with `'\r'` (_pyio.py:2288-2290 with
`_writetranslate`, stringio.c:747-749 with `writenl`), and nothing else changes. -/
def storeOf : Option (List Nat) → List Nat → List Nat
  | some (13 :: r), v => replaceLf (13 :: r) v
  | _, v => v

/-- What `read()` returns for that stored text: universal newlines with translation
for `newline=None` (`\r\n` and `\r` become `\n`), the text itself otherwise. -/
def readOf : Option (List Nat) → List Nat → List Nat
  | none, v => translateNl v
  | some nl, v => storeOf (some nl) v

/-- `_pyio.StringIO(v, nl)` right after construction: the UTF-8 of the stored text in
the `BytesIO`, rewound, no decoder yet. -/
def pyAfterInit (v : List Nat) (nl : Option (List Nat)) : TState :=
  { b := ⟨utf8Enc (storeOf nl v), 0, false, 0, true⟩, decoded := [], used := 0, snapshot := none,
    telling := true, decoder := none, b2c := (0, 1)
    readuniversal := nl.isNone || nl = some []
    readtranslate := nl.isNone
    readnl := nl
    writetranslate := nl ≠ some [] && nl.isSome
    writenl := match nl with
      | some [] | none => [10]
      | some n => n }

theorem py_init (v : List Nat) (nl : Option (List Nat)) (hl : LegalNewline nl)
    (hb : (utf8Enc (storeOf nl v)).length < memLimit) :
    TP.init (some v) nl = .ok (pyAfterInit v nl) := by
  have hw : ∀ x : List Nat, (utf8Enc x).length < memLimit →
      P.write ⟨[], 0, false, 0, true⟩ (utf8Enc x) =
        (if utf8Enc x = [] then ⟨[], 0, false, 0, true⟩
         else ⟨utf8Enc x, (utf8Enc x).length, false, 0, true⟩, .ok (.int (utf8Enc x).length)) := by
    intro x hx
    rw [P_write_end _ _ rfl rfl rfl (by simpa using hx)]
    simp
  have hrep : ∀ n w, (if w.contains 10 = true then replaceLf n w else w) = replaceLf n w :=
    fun n w => if_contains_replace n w
  have hrep2 : ∀ n w, (if 10 ∈ w then replaceLf n w else w) = replaceLf n w := by
    intro n w
    by_cases h : 10 ∈ w
    · simp [h]
    · simp only [h, ite_false]; exact (replaceLf_no_lf n w (by simpa using h)).symm
  by_cases he : utf8Enc (storeOf nl v) = [] <;>
  rcases hl with rfl | rfl | rfl | rfl | rfl <;>
    simp only [storeOf] at hb he <;>
    simp [TP.init, TP.init.build, TP.write, bInit, hrep2] <;>
    rw [hw _ hb] <;>
    simp [he, TP.seek, TP.seekCookie, TP.flush, TP.unpack, P.seek, TP.setDecoded, pyAfterInit, storeOf]

theorem translateNl_length_le : ∀ (n : Nat) (v : List Nat), v.length ≤ n → (translateNl v).length ≤ v.length := by
  intro n
  induction n with
  | zero => intro v h; have : v = [] := List.eq_nil_of_length_eq_zero (by omega); subst this; simp [translateNl]
  | succ n ih =>
    intro v h
    match v with
    | [] => simp [translateNl]
    | c :: t =>
      have iht := ih t (by simp at h; omega)
      by_cases h13 : c = 13
      · subst h13
        cases t with
        | nil => simp [translateNl]
        | cons d r =>
          by_cases h10 : d = 10
          · subst h10
            have := ih r (by simp at h; omega)
            rw [translateNl.eq_2]; simp; omega
          · rw [translateNl.eq_3 _ (by intro r' e; simp at e; exact h10 e.1)]; simp at iht ⊢; omega
      · rw [translateNl.eq_4 _ _ (by intro r' e; exact absurd e h13) h13]; simp; omega

theorem resizeCheck_ok (n : Nat) (h : 4 * (n + 2) < memLimit) : SC.resizeCheck n = .ok () := by
  have hmax : memLimit ≤ ssizeMax := by decide
  have : memLimit ≤ (2 ^ 64 - 1) / 4 := by decide
  unfold SC.resizeCheck
  have d1 : ¬ (((n + 1 : Nat) : Int) > ssizeMax) := by omega
  have d2 : ¬ (n + 1 + 1 > (2 ^ 64 - 1) / 4) := by omega
  have d3 : ¬ (4 * (n + 1 + 1) ≥ memLimit) := by omega
  simp only [d1, d2, d3, ite_false]

/-- What C's `newlines` reports: the kinds the decoder recorded while writing, for the
universal modes (stringio.c:1037-1046), `None` otherwise. -/
def cNewlinesOf (nl : Option (List Nat)) (v : List Nat) : Val :=
  if nl = none ∨ nl = some [] then newlinesVal (nlKinds v) else .none

theorem c_init_read (v : List Nat) (nl : Option (List Nat)) (hl : LegalNewline nl)
    (hb : 8 * v.length + 16 < memLimit) :
    runSC (some v) nl [.newlines, .read none, .newlines] =
      .ok [.ok (cNewlinesOf nl v), .ok (.str (readOf nl v)), .ok (cNewlinesOf nl v)] := by
  have ht := translateNl_length_le v.length v (Nat.le_refl _)
  have hr : ∀ n : List Nat, n.length ≤ 2 → (replaceLf n v).length ≤ 2 * v.length :=
    fun n hn => replaceLf_length_le n v hn
  have hz : ssizeMin ≤ 0 := by decide
  have hmax : memLimit ≤ ssizeMax := by decide
  by_cases he : v = []
  · subst he
    rcases hl with rfl | rfl | rfl | rfl | rfl <;>
      simp [runSC, runSC.runOps', SC.init, SC.step, cNewlinesOf, readOf, storeOf, slice, optSsize,
        InSsize, hz, nlKinds, newlinesVal, utf8Enc, replaceLf, translateNl] <;> decide
  · have hlen : 0 < v.length := List.length_pos_iff.mpr he
    have hlim : ∀ D : List Nat, D.length ≤ 2 * v.length →
        SC.resizeCheck D.length = .ok () ∧ ¬ (ssizeMax - (D.length : Int) < 0) :=
      fun D hD => ⟨resizeCheck_ok D.length (by omega), by omega⟩
    have hrl : ∀ n w, (if w.contains 10 = true then replaceLf n w else w) = replaceLf n w :=
      fun n w => if_contains_replace n w
    have htk : ∀ l : List Nat, List.take (if (l.length : Int) < 0 then 0 else (l.length : Int)).toNat l = l := by
      intro l; have : ¬ ((l.length : Int) < 0) := by omega
      simp [this]
    have htk2 : ∀ n : Nat, (if (n : Int) < 0 then (0 : Int) else (n : Int)).toNat = n := by
      intro n; have : ¬ ((n : Int) < 0) := by omega
      simp [this]
    rcases hl with rfl | rfl | rfl | rfl | rfl
    · obtain ⟨hrc, c1⟩ := hlim (translateNl v) (by omega)
      simp +decide [runSC, runSC.runOps', SC.init, SC.step, SC.writeStr, cNewlinesOf, readOf, storeOf, slice,
        optSsize, InSsize, hz, hlen, writeAt, hrc, c1, NlKinds.union, newlinesVal, pure, Except.pure, bind, Except.bind, htk, htk2, isSurrogate, hrl]
      all_goals (congr 1; rw [if_neg (by omega)]; simp)
    · obtain ⟨hrc, c1⟩ := hlim v (by omega)
      simp +decide [runSC, runSC.runOps', SC.init, SC.step, SC.writeStr, cNewlinesOf, readOf, storeOf, slice,
        optSsize, InSsize, hz, hlen, writeAt, hrc, c1, NlKinds.union, newlinesVal, pure, Except.pure, bind, Except.bind, utf8Enc, utf8Enc1, htk, htk2, isSurrogate, hrl]
      all_goals (congr 1; rw [if_neg (by omega)]; simp)
    · obtain ⟨hrc, c1⟩ := hlim v (by omega)
      simp +decide [runSC, runSC.runOps', SC.init, SC.step, SC.writeStr, cNewlinesOf, readOf, storeOf, slice,
        optSsize, InSsize, hz, hlen, writeAt, hrc, c1, NlKinds.union, newlinesVal, pure, Except.pure, bind, Except.bind, utf8Enc, utf8Enc1, htk, htk2, isSurrogate, hrl]
      all_goals (congr 1; rw [if_neg (by omega)]; simp)
    · obtain ⟨hrc, c1⟩ := hlim (replaceLf [13] v) (hr _ (by decide))
      simp +decide [runSC, runSC.runOps', SC.init, SC.step, SC.writeStr, cNewlinesOf, readOf, storeOf, slice,
        optSsize, InSsize, hz, hlen, writeAt, hrc, c1, NlKinds.union, newlinesVal, pure, Except.pure, bind, Except.bind, utf8Enc, utf8Enc1, htk, htk2, isSurrogate, hrl]
      all_goals (congr 1; rw [if_neg (by omega)]; simp)
    · obtain ⟨hrc, c1⟩ := hlim (replaceLf [13, 10] v) (hr _ (by decide))
      simp +decide [runSC, runSC.runOps', SC.init, SC.step, SC.writeStr, cNewlinesOf, readOf, storeOf, slice,
        optSsize, InSsize, hz, hlen, writeAt, hrc, c1, NlKinds.union, newlinesVal, pure, Except.pure, bind, Except.bind, utf8Enc, utf8Enc1, htk, htk2, isSurrogate, hrl]
      all_goals (congr 1; rw [if_neg (by omega)]; simp)

/-- What `_pyio`'s `newlines` reports after the first `read()`: the kinds the wrapping
`IncrementalNewlineDecoder` saw, for the universal modes; the plain decoder of the other
modes has no `newlines` attribute (bugs/pyio-stringio-pyio-newlines-attributeerror.yaml). -/
def pyNewlinesAfter (nl : Option (List Nat)) (v : List Nat) : Py Val :=
  if nl = none ∨ nl = some [] then .ok (newlinesVal (nlKinds v))
  else .error (.named "AttributeError" "'IncrementalDecoder' object has no attribute 'newlines'")

theorem py_init_read (v : List Nat) (nl : Option (List Nat)) (hl : LegalNewline nl)
    (hv : ValidStr (storeOf nl v)) (hb : (utf8Enc (storeOf nl v)).length < memLimit) :
    runSPy (some v) nl [.newlines, .read none, .newlines] =
      .ok [.ok .none, .ok (.str (readOf nl v)), pyNewlinesAfter nl v] := by
  unfold runSPy
  rw [py_init v nl hl hb]
  have hd := utf8Dec_enc true (storeOf nl v) hv
  have hu : ∀ k : NlKinds, Dec.none0.union k = k := by
    intro k; cases k; simp [Dec.none0, NlKinds.union]
  by_cases he : utf8Enc (storeOf nl v) = []
  · have hs : storeOf nl v = [] := (utf8Enc_eq_nil _).mp he
    rcases hl with rfl | rfl | rfl | rfl | rfl <;>
      simp only [storeOf] at hs hd <;>
      simp [runOps, TP.step, TP.newlines, pyAfterInit, TP.read, TP.getDecoder, P.readRaw,
        TP.getDecodedChars, Dec.decode, he, hs, hd, readOf, storeOf, pyNewlinesAfter, hu, nlKinds,
        newlinesVal, translateNl, bind, Except.bind, pure, Except.pure, utf8Enc_nil] <;> simp_all [replaceLf_eq_nil, utf8Enc_nil] <;> decide
  · have hpos : ¬ (utf8Enc (storeOf nl v)).length ≤ 0 := by
      intro h; exact he (List.eq_nil_of_length_eq_zero (by omega))
    rcases hl with rfl | rfl | rfl | rfl | rfl <;>
      simp only [storeOf] at hd hpos he <;>
      simp [runOps, TP.step, TP.newlines, pyAfterInit, TP.read, TP.getDecoder, P.readRaw,
        TP.getDecodedChars, Dec.decode, hpos, hd, readOf, storeOf, pyNewlinesAfter, hu, slice,
        bind, Except.bind, pure, Except.pure]

/-- `StringIO(v, newline)` for every legal `newline` and every `str` `v` below the
allocation bound, then `newlines`, `read()`, `newlines`. Both twins' `read()` return the
initial value as the newline mode stores and reads it: `newline=None` translates `\r\n`
and `\r` to `\n`, `'\r'` and `'\r\n'` turn each `\n` into that ending, `''` and `'\n'`
leave it as it is. So the constructor rewinds (`seek(0)`, _pyio.py:2761), `_configure`
sets the translation fields (:2128-2143), `_get_decoder` wraps the decoder in an
`IncrementalNewlineDecoder` with `translate` for the universal modes (:2309-2315), and
`read()` decodes the whole rest (:2608-2619). `newlines`: C reports the kinds of the
initial value as soon as it is written (its decoder runs on write), `None` for the other
modes; `_pyio` reports `None` until the first read creates the decoder, then the same kinds
for the universal modes, and `AttributeError` for the others. -/
def StringIOInitRead : Prop := ∀ (v : List Nat) (nl : Option (List Nat)),
  ValidStr v → LegalNewline nl → 8 * v.length + 16 < memLimit →
  runSC (some v) nl [.newlines, .read none, .newlines] =
      .ok [.ok (cNewlinesOf nl v), .ok (.str (readOf nl v)), .ok (cNewlinesOf nl v)] ∧
  runSPy (some v) nl [.newlines, .read none, .newlines] =
      .ok [.ok .none, .ok (.str (readOf nl v)), pyNewlinesAfter nl v]

theorem stringIOInitRead_proven : StringIOInitRead := by
  intro v nl hv hl hb
  refine ⟨c_init_read v nl hl hb, py_init_read v nl hl ?_ ?_⟩
  · rcases hl with rfl | rfl | rfl | rfl | rfl <;> simp only [storeOf] <;>
      first | exact hv | exact replaceLf_valid _ _ (by decide) hv
  · have h1 := utf8Enc_length_le (storeOf nl v)
    have h2 : (storeOf nl v).length ≤ 2 * v.length := by
      rcases hl with rfl | rfl | rfl | rfl | rfl <;> simp only [storeOf] <;>
        first | omega | exact replaceLf_length_le _ _ (by decide)
    omega

/-- For the universal newline modes, `io.StringIO(v, newline).newlines` and
`_pyio.StringIO(v, newline).newlines` agree right after construction. -/
def StringIONewlinesTwins : Prop := ∀ (v : List Nat) (nl : Option (List Nat)),
  ValidStr v → (nl = none ∨ nl = some []) → 8 * v.length + 16 < memLimit →
  runSC (some v) nl [.newlines] = runSPy (some v) nl [.newlines]

/-- `StringIO('a\n').newlines`: C `'\n'` (the decoder saw the initial value when it was
written, stringio.c:199-200, :1037-1046), `_pyio` `None` (no decoder before the first
read, _pyio.py:2732-2733). -/
theorem stringIONewlinesTwins_refuted : ¬StringIONewlinesTwins := by
  intro h
  have := h [97, 10] none (by decide) (Or.inl rfl) (by decide)
  revert this
  decide

end PyLean.PyIO
