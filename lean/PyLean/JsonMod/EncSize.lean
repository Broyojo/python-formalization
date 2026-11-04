import PyLean.JsonMod.EncTwins

/-!
The allocation of the C escapes, Modules/_json.c:162-419: `ascii_escape_size` and
`escape_size` compute `output_size`, `PyUnicode_New(output_size, maxchar)` allocates a
`str` of exactly that length, and the fill loops write into it with `output[chars++]`.

The buffer is modelled as the units written so far. A write at `chars >= output_size` is past
the allocation (a heap overflow), and a result with fewer units than `output_size` leaves
uninitialised memory in the returned `str`; both are `none`, which is no Python outcome. A
unit is stored truncated to the width of the output's kind (`Py_UCS1`, `Py_UCS2`,
`Py_UCS4`). `escape_unicode_and_size` reads the input with the output's kind
(`kind = PyUnicode_KIND(rval)`, :320); a read with a kind other than the input's is `none`.

The input `str` is canonical (its kind is the smallest that holds its largest code point,
`_PyUnicode_CheckConsistency`), a type invariant. `PyUnicode_New` failing with
`MemoryError` is out of scope.

So the size functions are pinned by what the fill loops write: a size that is wrong for one
character makes the result `none`.
-/

namespace PyLean.JsonMod

open PyLean

/-- `PY_SSIZE_T_MAX` as a `Nat`. -/
def ssizeMaxN : Nat := 2 ^ 63 - 1

/-- The kind `PyUnicode_New(size, maxchar)` chooses: bytes per code point. -/
def ucsKind (maxchar : Nat) : Nat :=
  if maxchar < 256 then 1 else if maxchar < 65536 then 2 else 4

/-- `PyUnicode_MAX_CHAR_VALUE(pystr)`: the largest code point of the string's kind
(0x7f for an ASCII string). -/
def maxCharValue (s : PStr) : Nat :=
  if s.all (· < 128) then 0x7f
  else if s.all (· < 256) then 0xff
  else if s.all (· < 65536) then 0xffff
  else 0x10ffff

/-- `PyUnicode_KIND(pystr)` of a canonical string. -/
def strKind (s : PStr) : Nat := ucsKind (maxCharValue s)

/-- `output[chars++] = c` into a buffer of `size` units of `width` bytes. -/
def bufPut (size width : Nat) (buf : List Nat) (c : Nat) : Option (List Nat) :=
  if buf.length < size then some (buf ++ [c % 2 ^ (8 * width)]) else none

/-- Several `output[chars++] = ...` in a row. -/
def bufPuts (size width : Nat) : List Nat → List Nat → Option (List Nat)
  | buf, [] => some buf
  | buf, c :: cs => (bufPut size width buf c).bind (fun b => bufPuts size width b cs)

/-- The `str` the function returns: `size` units, all written. -/
def bufFinish (size : Nat) (buf : List Nat) : Option PStr :=
  if buf.length = size then some buf else none

/-- The size loop of `ascii_escape_size` (:168-188) and `escape_size` (:285-304), for the
per-character `d`: `OverflowError` when `output_size > PY_SSIZE_T_MAX - d`. -/
def escSizeLoop (d : Nat → Nat) : Nat → PStr → Except PyExc Nat
  | acc, [] => .ok acc
  | acc, c :: cs =>
    if acc > ssizeMaxN - d c then .error (.overflowError "string is too long to escape")
    else escSizeLoop d (acc + d c) cs

/-- `ascii_escape_size`, :162-191. -/
def cAsciiEscapeSize (s : PStr) : Except PyExc Nat := escSizeLoop asciiEscD 2 s

/-- `escape_size`, :279-307. -/
def cEscapeSize (s : PStr) : Except PyExc Nat := escSizeLoop escD 2 s

/-- One iteration of the fill loop of `ascii_escape_unicode_and_size`, :208-215: an `S_CHAR`
as it is, otherwise `ascii_escape_unichar` (`cAsciiEscapeChar` is the units it writes, from
its `output[chars++] = '\\'` on). -/
def asciiStep (size : Nat) (buf : List Nat) (c : Nat) : Option (List Nat) :=
  if sChar c then bufPut size (ucsKind 127) buf c
  else bufPuts size (ucsKind 127) buf (cAsciiEscapeChar c)

/-- `ascii_escape_unicode_and_size`, :194-222: `PyUnicode_New(output_size, 127)` (1-byte
kind), the opening quote, the loop, the closing quote. -/
def cAsciiEscapeAndSize (s : PStr) (outSize : Nat) : Option PStr :=
  (bufPut outSize (ucsKind 127) [] 34).bind fun buf =>
  (s.foldlM (asciiStep outSize) buf).bind fun buf =>
  (bufPut outSize (ucsKind 127) buf 34).bind (bufFinish outSize)

/-- One iteration of `ENCODE_OUTPUT`, :324-347, writing with `kind`. -/
def escStep (size kind : Nat) (buf : List Nat) (c : Nat) : Option (List Nat) :=
  bufPuts size kind buf (cEscapeChar c)

/-- `escape_unicode_and_size`, :310-368: `PyUnicode_New(output_size, maxchar)`, then
`kind = PyUnicode_KIND(rval)` (:320) for both the reads and the writes of `ENCODE_OUTPUT`
(:322-349); `inKind` is the kind of the input. -/
def cEscapeAndSize (s : PStr) (inKind maxchar outSize : Nat) : Option PStr :=
  let kind := ucsKind maxchar
  if kind ≠ inKind then none
  else
    (bufPut outSize kind [] 34).bind fun buf =>
    (s.foldlM (escStep outSize kind) buf).bind fun buf =>
    (bufPut outSize kind buf 34).bind (bufFinish outSize)

/-- `ascii_escape_unicode`, :225-238. -/
def cAsciiEscapeUnicode (s : PStr) : Option (Except PyExc PStr) :=
  match cAsciiEscapeSize s with
  | .error e => some (.error e)
  | .ok n => (cAsciiEscapeAndSize s n).map .ok

/-- `escape_unicode`, :371-385. -/
def cEscapeUnicode (s : PStr) : Option (Except PyExc PStr) :=
  match cEscapeSize s with
  | .error e => some (.error e)
  | .ok n => (cEscapeAndSize s (strKind s) (maxCharValue s) n).map .ok

/-- `write_escaped_ascii`, :241-276, returning what it writes: the direct path on
`output_size == input_chars + 2`, otherwise `ascii_escape_unicode_and_size`. -/
def cWriteEscapedAscii (s : PStr) : Option (Except PyExc PStr) :=
  match cAsciiEscapeSize s with
  | .error e => some (.error e)
  | .ok n =>
    if n = s.length + 2 then some (.ok ([34] ++ s ++ [34]))
    else (cAsciiEscapeAndSize s n).map .ok

/-- `write_escaped_unicode`, :388-419. -/
def cWriteEscapedUnicode (s : PStr) : Option (Except PyExc PStr) :=
  match cEscapeSize s with
  | .error e => some (.error e)
  | .ok n =>
    if n = s.length + 2 then some (.ok ([34] ++ s ++ [34]))
    else (cEscapeAndSize s (strKind s) (maxCharValue s) n).map .ok

/-! ### Proofs -/

theorem escSizeLoop_eq (d : Nat → Nat) (hd : ∀ c, d c ≤ 12) :
    ∀ (s : PStr) (acc : Nat), acc ≤ ssizeMaxN →
    escSizeLoop d acc s = if acc + (s.map d).sum ≤ ssizeMaxN then .ok (acc + (s.map d).sum)
      else .error (.overflowError "string is too long to escape") := by
  intro s
  induction s with
  | nil => intro acc h; simp [escSizeLoop, h]
  | cons c t ih =>
    intro acc h
    have hc := hd c
    have hM : 12 ≤ ssizeMaxN := by simp [ssizeMaxN]
    simp only [escSizeLoop, List.map_cons, List.sum_cons]
    by_cases h1 : acc > ssizeMaxN - d c
    · have : ¬ (acc + (d c + (t.map d).sum) ≤ ssizeMaxN) := by omega
      simp [h1, this]
    · simp only [h1, ↓reduceIte]
      rw [ih (acc + d c) (by omega)]
      have e : acc + d c + (t.map d).sum = acc + (d c + (t.map d).sum) := by omega
      rw [e]

theorem asciiEscD_le (c : Nat) : asciiEscD c ≤ 12 := by
  unfold asciiEscD; split <;> (try split) <;> (try split) <;> omega

theorem escD_le (c : Nat) : escD c ≤ 12 := by
  unfold escD; split <;> (try split) <;> omega

theorem bufPuts_append (size width : Nat) :
    ∀ (u v buf : List Nat), bufPuts size width buf (u ++ v) =
      (bufPuts size width buf u).bind (fun b => bufPuts size width b v) := by
  intro u
  induction u with
  | nil => intro v buf; simp [bufPuts]
  | cons c t ih =>
    intro v buf
    simp only [List.cons_append, bufPuts]
    cases bufPut size width buf c with
    | none => rfl
    | some b => simp only [Option.bind_some]; exact ih v b

theorem fold_puts (size width : Nat) (step : List Nat → Nat → Option (List Nat)) (units : Nat → PStr)
    (h : ∀ buf c, step buf c = bufPuts size width buf (units c)) :
    ∀ (s buf : List Nat), s.foldlM step buf = bufPuts size width buf (s.flatMap units) := by
  intro s
  induction s with
  | nil => intro buf; simp [bufPuts]
  | cons c t ih =>
    intro buf
    simp only [List.foldlM_cons, h, List.flatMap_cons, bufPuts_append]
    cases bufPuts size width buf (units c) with
    | none => rfl
    | some b => simp only [Option.bind_eq_bind, Option.bind_some]; exact ih b

theorem bufPut_puts (size width : Nat) (buf : List Nat) (c : Nat) :
    bufPut size width buf c = bufPuts size width buf [c] := by
  simp only [bufPuts]; cases bufPut size width buf c <;> rfl

theorem bufPuts_ok (size width : Nat) :
    ∀ (u buf : List Nat), buf.length + u.length ≤ size → (∀ x ∈ u, x < 2 ^ (8 * width)) →
    bufPuts size width buf u = some (buf ++ u) := by
  intro u
  induction u with
  | nil => intro buf _ _; simp [bufPuts]
  | cons c t ih =>
    intro buf h hu
    have hc : c < 2 ^ (8 * width) := hu c (by simp)
    simp only [List.length_cons] at h
    simp only [bufPuts, bufPut, show buf.length < size by omega, ↓reduceIte, Option.bind_some,
      Nat.mod_eq_of_lt hc]
    rw [ih (buf ++ [c]) (by simp; omega) (fun x hx => hu x (by simp [hx]))]
    simp

/-- Writing past the end fails. -/
theorem bufPuts_none (size width : Nat) :
    ∀ (u buf : List Nat), buf.length ≤ size → size < buf.length + u.length →
    bufPuts size width buf u = none := by
  intro u
  induction u with
  | nil => intro buf h0 h; simp at h; omega
  | cons c t ih =>
    intro buf h0 h
    simp only [bufPuts, bufPut]
    split
    · simp only [Option.bind_some]
      exact ih _ (by simp; omega) (by simp at h ⊢; omega)
    · rfl

/-- A buffer of `size` filled with `u`: exactly `u` when `u` has `size` units that fit their
width, nothing otherwise. -/
theorem fill_eq (size width : Nat) (u : List Nat) (hu : ∀ x ∈ u, x < 2 ^ (8 * width)) :
    (bufPuts size width [] u).bind (bufFinish size) = if u.length = size then some u else none := by
  by_cases h : u.length ≤ size
  · rw [bufPuts_ok size width u [] (by simpa using h) hu]
    simp only [List.nil_append, Option.bind_some, bufFinish]
  · rw [bufPuts_none size width u [] (by simp) (by simp; omega)]
    simp only [Option.bind_none]
    split
    · omega
    · rfl

/-- The units the ASCII fill loop writes for `c`. -/
def asciiUnits (c : Nat) : PStr := if sChar c then [c] else cAsciiEscapeChar c

theorem cAsciiEscape_units (s : PStr) : cAsciiEscape s = [34] ++ s.flatMap asciiUnits ++ [34] := rfl

theorem asciiStep_eq (size : Nat) (buf : List Nat) (c : Nat) :
    asciiStep size buf c = bufPuts size (ucsKind 127) buf (asciiUnits c) := by
  unfold asciiStep asciiUnits
  split
  · exact bufPut_puts _ _ _ _
  · rfl

theorem cAsciiEscapeAndSize_eq (s : PStr) (n : Nat) :
    cAsciiEscapeAndSize s n = (bufPuts n (ucsKind 127) [] (cAsciiEscape s)).bind (bufFinish n) := by
  unfold cAsciiEscapeAndSize
  simp only [fold_puts n _ _ asciiUnits (asciiStep_eq n)]
  rw [cAsciiEscape_units, bufPuts_append, bufPuts_append, bufPut_puts]
  cases bufPuts n (ucsKind 127) [] [34] with
  | none => rfl
  | some b =>
    simp only [Option.bind_some]
    cases bufPuts n (ucsKind 127) b (s.flatMap asciiUnits) with
    | none => rfl
    | some b2 =>
      simp only [Option.bind_some, bufPut_puts]

theorem cEscapeAndSize_eq (s : PStr) (inKind maxchar n : Nat) :
    cEscapeAndSize s inKind maxchar n = if ucsKind maxchar ≠ inKind then none
      else (bufPuts n (ucsKind maxchar) [] (cEscape s)).bind (bufFinish n) := by
  unfold cEscapeAndSize
  dsimp only
  split
  · rfl
  · simp only [fold_puts n (ucsKind maxchar) (escStep n (ucsKind maxchar)) cEscapeChar (fun _ _ => rfl)]
    rw [cEscape, bufPuts_append, bufPuts_append, bufPut_puts]
    cases bufPuts n (ucsKind maxchar) [] [34] with
    | none => rfl
    | some b =>
      simp only [Option.bind_some]
      cases bufPuts n (ucsKind maxchar) b (s.flatMap cEscapeChar) with
      | none => rfl
      | some b2 =>
        simp only [Option.bind_some, bufPut_puts]

theorem cU_len (v : Nat) : (cU v).length = 5 := rfl

theorem asciiUnits_len (c : Nat) : (asciiUnits c).length = asciiEscD c := by
  unfold asciiUnits asciiEscD cAsciiEscapeChar
  by_cases h : sChar c = true
  · simp [h]
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    by_cases h92 : c = 92
    · simp [h92]
    by_cases h34 : c = 34
    · simp [h34]
    by_cases h8 : c = 8
    · simp [h8]
    by_cases h12 : c = 12
    · simp [h12]
    by_cases h10 : c = 10
    · simp [h10]
    by_cases h13 : c = 13
    · simp [h13]
    by_cases h9 : c = 9
    · simp [h9]
    simp only [h92, h34, h8, h12, h10, h13, h9, ↓reduceIte, or_self]
    by_cases hb : c ≥ 0x10000
    · simp [hb, cU_len]
    · simp [hb, cU_len]

theorem hexCp_and_lt (x : Nat) : hexCp (x &&& 0xf) < 128 := by
  have : x &&& 0xf < 16 := by rw [and_0xf]; omega
  unfold hexCp; split <;> omega

theorem cU_all (v : Nat) : (cU v).all (· < 128) = true := by
  simp [cU, hexCp_and_lt]

theorem asciiUnits_all (c : Nat) : (asciiUnits c).all (· < 128) = true := by
  unfold asciiUnits
  split
  · rename_i h
    simp only [sChar, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h
    simp; omega
  · unfold cAsciiEscapeChar
    simp only [List.all_cons]
    repeat' split
    all_goals simp [List.all_append, cU_all]

theorem cAsciiEscape_all (s : PStr) : ∀ x ∈ cAsciiEscape s, x < 128 := by
  intro x hx
  rw [cAsciiEscape_units] at hx
  simp only [List.mem_append, List.mem_singleton, List.mem_flatMap] at hx
  rcases hx with (rfl | ⟨c, _, hc⟩) | rfl
  · omega
  · have := List.all_eq_true.mp (asciiUnits_all c) x hc
    simpa using this
  · omega

/-- `ascii_escape_size` counts exactly what the fill loop writes. -/
theorem asciiEscapeSize_eq_length (s : PStr) : asciiEscapeSize s = (cAsciiEscape s).length := by
  have h : (s.flatMap asciiUnits).length = (s.map asciiEscD).sum := by
    rw [List.length_flatMap]; congr 1; apply List.map_congr_left; intro c _; exact asciiUnits_len c
  rw [cAsciiEscape_units]
  simp only [asciiEscapeSize, List.length_append, List.length_singleton, h]
  omega

/-- `ascii_escape_unicode_and_size` with output size `n`: the escaped text exactly when `n` is
its length. -/
theorem cAsciiEscapeAndSize_spec (s : PStr) (n : Nat) :
    cAsciiEscapeAndSize s n = if n = asciiEscapeSize s then some (cAsciiEscape s) else none := by
  rw [cAsciiEscapeAndSize_eq, fill_eq n _ _ (fun x hx => by
    have := cAsciiEscape_all s x hx; simp [ucsKind]; omega), asciiEscapeSize_eq_length]
  by_cases h : n = (cAsciiEscape s).length
  · simp [h]
  · simp only [h, ↓reduceIte]
    split
    · omega
    · rfl

/-! #### The unicode escape -/

theorem cEscapeChar_len (c : Nat) : (cEscapeChar c).length = escD c := by
  unfold cEscapeChar escD
  by_cases h92 : c = 92
  · simp [h92]
  by_cases h34 : c = 34
  · simp [h34]
  by_cases h8 : c = 8
  · simp [h8]
  by_cases h12 : c = 12
  · simp [h12]
  by_cases h10 : c = 10
  · simp [h10]
  by_cases h13 : c = 13
  · simp [h13]
  by_cases h9 : c = 9
  · simp [h9]
  simp only [h92, h34, h8, h12, h10, h13, h9, ↓reduceIte, or_self]
  by_cases h1f : c ≤ 0x1f <;> simp [h1f]

theorem escapeSize_eq_length (s : PStr) : escapeSize s = (cEscape s).length := by
  have h : (s.flatMap cEscapeChar).length = (s.map escD).sum := by
    rw [List.length_flatMap]; congr 1; apply List.map_congr_left; intro c _; exact cEscapeChar_len c
  simp only [escapeSize, cEscape, List.length_append, List.length_singleton, h]
  omega

/-- Each unit `ENCODE_OUTPUT` writes for `c` is `c` itself or ASCII. -/
theorem cEscapeChar_all (c : Nat) : (cEscapeChar c).all (fun x => x == c || decide (x < 128)) = true := by
  unfold cEscapeChar
  repeat' split
  all_goals simp [hexCp_and_lt]

/-- A code point of `s` fits in a unit of `s`'s own kind. -/
theorem mem_lt_kind {s : PStr} (hs : strOk s = true) {c : Nat} (hc : c ∈ s) :
    c < 2 ^ (8 * strKind s) := by
  have hcp : c ≤ 0x10FFFF := by
    have := List.all_eq_true.mp hs c hc
    simpa [cpOk] using this
  unfold strKind maxCharValue
  split
  · rename_i h; have := List.all_eq_true.mp h c hc; simp at this; simp [ucsKind]; omega
  · split
    · rename_i _ h; have := List.all_eq_true.mp h c hc; simp at this; simp [ucsKind]; omega
    · split
      · rename_i _ _ h; have := List.all_eq_true.mp h c hc; simp at this; simp [ucsKind]; omega
      · simp [ucsKind]; omega

theorem strKind_pos (s : PStr) : 1 ≤ strKind s := by
  unfold strKind ucsKind; split <;> (try split) <;> omega

theorem cEscape_fits {s : PStr} (hs : strOk s = true) : ∀ x ∈ cEscape s, x < 2 ^ (8 * strKind s) := by
  have h128 : 128 ≤ 2 ^ (8 * strKind s) :=
    calc 128 ≤ 2 ^ 8 := by decide
      _ ≤ 2 ^ (8 * strKind s) := Nat.pow_le_pow_right (by decide) (by have := strKind_pos s; omega)
  intro x hx
  simp only [cEscape, List.mem_append, List.mem_singleton, List.mem_flatMap] at hx
  rcases hx with (rfl | ⟨c, hcs, hc⟩) | rfl
  · omega
  · have := List.all_eq_true.mp (cEscapeChar_all c) x hc
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    rcases this with rfl | h
    · exact mem_lt_kind hs hcs
    · omega
  · omega

/-- `escape_unicode_and_size` as `escape_unicode` calls it, with output size `n`: the escaped
text exactly when `n` is its length. -/
theorem cEscapeAndSize_spec (s : PStr) (hs : strOk s = true) (n : Nat) :
    cEscapeAndSize s (strKind s) (maxCharValue s) n = if n = escapeSize s then some (cEscape s) else none := by
  rw [cEscapeAndSize_eq]
  simp only [show ucsKind (maxCharValue s) = strKind s from rfl, ne_eq, not_true_eq_false, ↓reduceIte]
  rw [fill_eq n _ _ (cEscape_fits hs), escapeSize_eq_length]
  by_cases h : n = (cEscape s).length
  · simp [h]
  · simp only [h, ↓reduceIte]
    split
    · omega
    · rfl

/-! #### The property -/

theorem cAsciiEscapeSize_eq (s : PStr) : cAsciiEscapeSize s =
    if asciiEscapeSize s ≤ ssizeMaxN then .ok (asciiEscapeSize s)
    else .error (.overflowError "string is too long to escape") := by
  unfold cAsciiEscapeSize
  rw [escSizeLoop_eq asciiEscD asciiEscD_le s 2 (by simp [ssizeMaxN])]
  rfl

theorem cEscapeSize_eq (s : PStr) : cEscapeSize s =
    if escapeSize s ≤ ssizeMaxN then .ok (escapeSize s)
    else .error (.overflowError "string is too long to escape") := by
  unfold cEscapeSize
  rw [escSizeLoop_eq escD escD_le s 2 (by simp [ssizeMaxN])]
  rfl

/-- The size `ascii_escape_size` and `escape_size` compute is the length of what the fill
loops write (`asciiEscapeSize s = (cAsciiEscape s).length`, `escapeSize s = (cEscape s).length`);
`ascii_escape_unicode_and_size` and `escape_unicode_and_size` give the escaped text exactly
when the size they are given is that length (a smaller one overflows the buffer, a larger one
leaves units unwritten); so `ascii_escape_unicode`, `escape_unicode` and both `write_escaped_*`
return the escaped text, or `OverflowError` when the size passes `PY_SSIZE_T_MAX`. For every
`str` (code points at most 0x10FFFF, a type invariant). -/
def EscapeSize : Prop :=
  ∀ s : PStr, strOk s = true →
    asciiEscapeSize s = (cAsciiEscape s).length ∧
    escapeSize s = (cEscape s).length ∧
    (∀ n, cAsciiEscapeAndSize s n = if n = asciiEscapeSize s then some (cAsciiEscape s) else none) ∧
    (∀ n, cEscapeAndSize s (strKind s) (maxCharValue s) n =
      if n = escapeSize s then some (cEscape s) else none) ∧
    cAsciiEscapeUnicode s = some (if asciiEscapeSize s ≤ ssizeMaxN then .ok (cAsciiEscape s)
      else .error (.overflowError "string is too long to escape")) ∧
    cEscapeUnicode s = some (if escapeSize s ≤ ssizeMaxN then .ok (cEscape s)
      else .error (.overflowError "string is too long to escape")) ∧
    cWriteEscapedAscii s = some (if asciiEscapeSize s ≤ ssizeMaxN then .ok (writeEscapedAscii s)
      else .error (.overflowError "string is too long to escape")) ∧
    cWriteEscapedUnicode s = some (if escapeSize s ≤ ssizeMaxN then .ok (writeEscapedUnicode s)
      else .error (.overflowError "string is too long to escape"))

theorem escapeSize_proven : EscapeSize := by
  intro s hs
  refine ⟨asciiEscapeSize_eq_length s, escapeSize_eq_length s, cAsciiEscapeAndSize_spec s,
    cEscapeAndSize_spec s hs, ?_, ?_, ?_, ?_⟩
  · unfold cAsciiEscapeUnicode
    rw [cAsciiEscapeSize_eq]
    by_cases hle : asciiEscapeSize s ≤ ssizeMaxN
    · simp [hle, cAsciiEscapeAndSize_spec]
    · simp [hle]
  · unfold cEscapeUnicode
    rw [cEscapeSize_eq]
    by_cases hle : escapeSize s ≤ ssizeMaxN
    · simp [hle, cEscapeAndSize_spec s hs]
    · simp [hle]
  · unfold cWriteEscapedAscii
    rw [cAsciiEscapeSize_eq]
    by_cases hle : asciiEscapeSize s ≤ ssizeMaxN
    · simp only [hle, ↓reduceIte, writeEscapedAscii]
      by_cases h2 : asciiEscapeSize s = s.length + 2
      · simp [h2]
      · simp [h2, cAsciiEscapeAndSize_spec]
    · simp [hle]
  · unfold cWriteEscapedUnicode
    rw [cEscapeSize_eq]
    by_cases hle : escapeSize s ≤ ssizeMaxN
    · simp only [hle, ↓reduceIte, writeEscapedUnicode]
      by_cases h2 : escapeSize s = s.length + 2
      · simp [h2]
      · simp [h2, cEscapeAndSize_spec s hs]
    · simp [hle]

end PyLean.JsonMod
