import PyLean.Datetime.FmtTwinsProps

/-!
The scan of `_wrap_strftime` (Lib/_pydatetime.py:217-295), one directive at a time: what
each `%` escape is replaced by before `time.strftime` sees the format.
-/

namespace PyLean.Datetime

open PyLean

/-- `_wrap_strftime`'s scan (:227-292) step by step, for every object, tzinfo environment,
remaining format and fuel (`wrapStrftimePy` starts with the format's length, and every step
consumes at least one character): a character other than `%` is copied; `%f` is the six
digits of `microsecond` (0 for a date); `%z` and `%:z` are `_format_offset(utcoffset(), '')`
and `(..., ':')` (`""` for a date; the text is pinned by `FormatOffsetText`), and an
exception of `utcoffset()` propagates; `%Z` is `tzname()` with every `%` doubled (`""` for
None or a date); `%:` followed by another character is kept as three characters; a trailing
`%` is kept and a trailing `%:` is dropped; when the year is below 1000 and the C library
needs the normalization, `%Y` and `%G` are the four-digit year and ISO year, `%C` the
two-digit century and `%F` `YYYY-MM-DD`, and otherwise these, `%%` and every other directive
are kept for `time.strftime`. The `%%` clause means `%%f` is not a microsecond field. -/
def WrapScanDirectives : Prop :=
  ∀ (env : TzEnv) (obj : StrfObj) (tt0 gyear mon day : Int) (norm : Bool) (n : Nat)
    (rest : List Char) (c : Char),
    let sc := wrapScanPy env obj tt0 gyear mon day norm
    (c ≠ '%' → sc (n + 1) (c :: rest) = (c :: ·) <$> sc n rest) ∧
    sc (n + 1) ['%'] = .ok ['%'] ∧
    sc (n + 1) ['%', ':'] = .ok [] ∧
    (0 ≤ obj.microsecond → obj.microsecond < 1000000 →
      sc (n + 1) ('%' :: 'f' :: rest) = (d6 obj.microsecond.toNat ++ ·) <$> sc n rest) ∧
    sc (n + 1) ('%' :: 'f' :: rest) = (padInt 6 obj.microsecond ++ ·) <$> sc n rest ∧
    sc (n + 1) ('%' :: 'z' :: rest) = (do let z ← obj.zreplacePy env []; let r ← sc n rest; return z ++ r) ∧
    sc (n + 1) ('%' :: ':' :: 'z' :: rest) =
      (do let z ← obj.zreplacePy env [':']; let r ← sc n rest; return z ++ r) ∧
    sc (n + 1) ('%' :: 'Z' :: rest) = (do let z ← obj.ZreplacePy env; let r ← sc n rest; return z ++ r) ∧
    (c ≠ 'z' → sc (n + 1) ('%' :: ':' :: c :: rest) = (['%', ':', c] ++ ·) <$> sc n rest) ∧
    sc (n + 1) ('%' :: '%' :: rest) = (['%', '%'] ++ ·) <$> sc n rest ∧
    (tt0 < 1000 → norm = true →
      sc (n + 1) ('%' :: 'Y' :: rest) = (padInt 4 tt0 ++ ·) <$> sc n rest ∧
      sc (n + 1) ('%' :: 'G' :: rest) = (padInt 4 gyear ++ ·) <$> sc n rest ∧
      sc (n + 1) ('%' :: 'C' :: rest) = (padInt 2 (tt0 / 100) ++ ·) <$> sc n rest ∧
      sc (n + 1) ('%' :: 'F' :: rest) =
        (padInt 4 tt0 ++ ['-'] ++ padInt 2 mon ++ ['-'] ++ padInt 2 day ++ ·) <$> sc n rest) ∧
    ((¬ (tt0 < 1000 ∧ norm = true) ∨ c ∉ ['Y', 'G', 'F', 'C']) → c ∉ ['f', 'z', ':', 'Z'] →
      sc (n + 1) ('%' :: c :: rest) = (['%', c] ++ ·) <$> sc n rest) ∧
    (∀ (t : TM) (s : String), t.tznamePy env = .ok (some s) →
      wrapScanPy env (.time t) tt0 gyear mon day norm (n + 1) ('%' :: 'Z' :: rest) =
        (escapePercent s.toList ++ ·) <$> wrapScanPy env (.time t) tt0 gyear mon day norm n rest) ∧
    (wrapScanPy env .date tt0 gyear mon day norm (n + 1) ('%' :: 'z' :: rest) =
        wrapScanPy env .date tt0 gyear mon day norm n rest ∧
      wrapScanPy env .date tt0 gyear mon day norm (n + 1) ('%' :: 'Z' :: rest) =
        wrapScanPy env .date tt0 gyear mon day norm n rest)

theorem map_ok_eq {α β : Type} (f : α → β) (x : Py α) : (do let r ← x; return f r) = f <$> x := by
  cases x <;> rfl

theorem wrapScanDirectives_proven : WrapScanDirectives := by
  intro env obj tt0 gyear mon day norm n rest c
  simp only
  refine ⟨fun hc => ?_, ?_, ?_, fun h0 h1 => ?_, ?_, rfl, rfl, rfl, fun hc => ?_, ?_, fun ht hn => ?_,
    fun hy hc => ?_, fun t s hs => ?_, ?_⟩
  · simp only [wrapScanPy, hc, ne_eq, not_false_eq_true, ↓reduceIte]; exact map_ok_eq _ _
  · cases n <;> rfl
  · cases n <;> rfl
  · simp only [wrapScanPy, ne_eq, not_true_eq_false, ↓reduceIte, padInt_d6 _ h0 h1]; exact map_ok_eq _ _
  · simp only [wrapScanPy, ne_eq, not_true_eq_false, ↓reduceIte]; exact map_ok_eq _ _
  · simp only [wrapScanPy, ne_eq, not_true_eq_false, ↓reduceIte, hc, show (':' : Char) ≠ 'f' by decide,
      show (':' : Char) ≠ 'z' by decide]
    exact map_ok_eq _ _
  · simp only [wrapScanPy, ne_eq, not_true_eq_false, ↓reduceIte]
    simp (config := { decide := true }) only [↓reduceIte]
    exact map_ok_eq _ _
  · subst hn
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp (config := { decide := true }) [wrapScanPy, ht] <;> exact map_ok_eq _ _
  · have : c ≠ 'f' ∧ c ≠ 'z' ∧ c ≠ ':' ∧ c ≠ 'Z' := by simpa using hc
    obtain ⟨h1, h2, h3, h4⟩ := this
    simp only [wrapScanPy, ne_eq, not_true_eq_false, ↓reduceIte, h1, h2, h3, h4]
    rw [if_neg (by
      rintro ⟨hm, ht, hn⟩
      rcases hy with hy | hy
      · exact hy ⟨ht, hn⟩
      · exact hy (by simp at hm ⊢; exact hm))]
    exact map_ok_eq _ _
  · simp [wrapScanPy, StrfObj.ZreplacePy, hs, bind, Except.bind, pure, Except.pure]
    cases wrapScanPy env (.time t) tt0 gyear mon day norm n rest <;> rfl
  · constructor <;> simp [wrapScanPy, StrfObj.zreplacePy, StrfObj.ZreplacePy, bind, Except.bind, pure,
      Except.pure] <;> cases wrapScanPy env .date tt0 gyear mon day norm n rest <;> rfl

end PyLean.Datetime
