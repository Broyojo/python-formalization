import PyLean.TextLibs.EmailHeaders

/-!
Refuted properties of `Lib/email/_header_value_parser.py` (CPython 3.15.2). Each statement is
quantified over every input and every `_ew.decode` that raises nothing `get_encoded_word`
would not catch; each refutation evaluates the model on one input, with `_ew.decode` raising
`ValueError` for every argument (`cfgCaught`) or, where an encoded word must decode, returning
what CPython's `_ew.decode` returns for it (`cfgQ`). `bugs/textlibs-email-*.yaml` hold the
reproducers.

The header parsers are the `value_parser`s of `email.headerregistry`, whose contract is "The
parser should not, insofar as practical, raise any errors. Defects should be added to the list
instead." (Lib/email/headerregistry.py:169-174); `parse_message_id` and the `parse_content_*`
functions turn every `HeaderParseError` of the `get_*` functions into a defect.
-/

namespace PyLean.TextLibs.Email

open PyLean.UnicodeObj

/-- `r` is a value, not a raised exception. Fuel exhaustion counts as a value: it is not a
Python outcome, and the statements below are about what CPython does. -/
def noRaise {α : Type} : EPy α → Bool
  | .ok _ => true
  | .error .fuel => true
  | .error _ => false

/-- The exception `r` raised, if any. -/
def errOf {α : Type} : EPy α → Option EExc
  | .ok _ => none
  | .error e => some e

/-- `_ew.decode` raises nothing that `get_encoded_word` does not catch (`ValueError`,
`KeyError`). -/
def DecSafe (cfg : Cfg) : Prop := ∀ s c m, cfg.dec s ≠ .raise c m

/-- `_ew.decode` raising `ValueError` for every argument. -/
def cfgCaught : Cfg := { dec := fun _ => .caught }

theorem cfgCaught_safe : DecSafe cfgCaught := by
  intro s c m h
  cases h

/-! ## `parse_message_id` and `parse_message_ids` -/

/-- For every header value, `parse_message_id` returns a token list (with defects) and raises
nothing: it catches the `HeaderParseError` of `get_msg_id` and falls back to `get_unstructured`
(_header_value_parser.py:2182-2189). -/
def MessageIdNoRaise : Prop :=
  ∀ (cfg : Cfg) (n : Nat) (v : Str), DecSafe cfg → noRaise (parseMessageId cfg n v) = true

/-- The same for `parse_message_ids` (In-Reply-To, References), which catches the
`HeaderParseError` of `get_msg_id` the same way (:2213-2221). -/
def MessageIdsNoRaise : Prop :=
  ∀ (cfg : Cfg) (n : Nat) (v : Str), DecSafe cfg → noRaise (parseMessageIds cfg n v) = true

/-- `<a@[ x]>`: the id-right is not a dot-atom-text, so `get_msg_id` tries
`get_no_fold_literal`, whose `get_dtext(' x]>')` calls `_get_ptext_to_endchars` on a value
starting with a space. The fragment before the first space is empty, the `for` loop never
binds `pos`, and its `else` clause raises `UnboundLocalError`, which neither `get_msg_id` nor
`parse_message_id` catches. -/
theorem messageId_unbound :
    errOf (parseMessageId cfgCaught 100 (S "<a@[ x]>")) = some unboundPos := by
  decide +kernel

theorem messageIds_unbound :
    errOf (parseMessageIds cfgCaught 100 (S "<a@[ x]>")) = some unboundPos := by
  decide +kernel

theorem messageIdNoRaise_refuted : ¬ MessageIdNoRaise := by
  intro h
  have h1 := h cfgCaught 100 (S "<a@[ x]>") cfgCaught_safe
  have h2 : noRaise (parseMessageId cfgCaught 100 (S "<a@[ x]>")) = false := by decide +kernel
  rw [h2] at h1
  exact Bool.false_ne_true h1

theorem messageIdsNoRaise_refuted : ¬ MessageIdsNoRaise := by
  intro h
  have h1 := h cfgCaught 100 (S "<a@[ x]>") cfgCaught_safe
  have h2 : noRaise (parseMessageIds cfgCaught 100 (S "<a@[ x]>")) = false := by decide +kernel
  rw [h2] at h1
  exact Bool.false_ne_true h1

/-! ## `parse_content_type_header` and `parse_content_disposition_header` -/

/-- For every header value, `parse_content_type_header` returns a token list and raises
nothing: a value that is not a valid parameter list is recovered by `parse_mime_parameters`,
which catches the `HeaderParseError` of `get_parameter` and keeps the text as an invalid
parameter (_header_value_parser.py:2650-2671). -/
def ContentHeadersNoRaise : Prop :=
  ∀ (cfg : Cfg) (n : Nat) (v : Str), DecSafe cfg → noRaise (parseContentTypeHeader cfg n v) = true

/-- The same for `parse_content_disposition_header`, which hands its parameters to
`parse_mime_parameters` the same way (:2785-2786). -/
def ContentDispositionNoRaise : Prop :=
  ∀ (cfg : Cfg) (n : Nat) (v : Str), DecSafe cfg →
    noRaise (parseContentDispositionHeader cfg n v) = true

/-- `text/plain; a*`: `get_parameter` reads the attribute `a`, finds `*`, fails to read a
section (`get_section` raises `HeaderParseError`, which it ignores), takes the `*` as the
extended-parameter marker and is left with an empty value; `if value[0] != '='`
(:2525) then raises `IndexError`. -/
theorem contentType_star :
    errOf (parseContentTypeHeader cfgCaught 100 (S "text/plain; a*")) = some strIndexError := by
  decide +kernel

theorem contentDisposition_star :
    errOf (parseContentDispositionHeader cfgCaught 100 (S "attachment; filename*")) =
      some strIndexError := by
  decide +kernel

theorem contentHeadersNoRaise_refuted : ¬ ContentHeadersNoRaise := by
  intro h
  have h1 := h cfgCaught 100 (S "text/plain; a*") cfgCaught_safe
  have h2 : noRaise (parseContentTypeHeader cfgCaught 100 (S "text/plain; a*")) = false := by
    decide +kernel
  rw [h2] at h1
  exact Bool.false_ne_true h1

theorem contentDispositionNoRaise_refuted : ¬ ContentDispositionNoRaise := by
  intro h
  have h1 := h cfgCaught 100 (S "attachment; filename*") cfgCaught_safe
  have h2 : noRaise (parseContentDispositionHeader cfgCaught 100 (S "attachment; filename*")) =
      false := by
    decide +kernel
  rw [h2] at h1
  exact Bool.false_ne_true h1

/-! ## `get_section` -/

/-- `r` is a value or a `HeaderParseError` (`EExc.fuel` again is not a Python outcome). -/
def onlyHpe {α : Type} : EPy α → Bool
  | .ok _ => true
  | .error e => e.isHpe || e == .fuel

/-- For every value, `get_section` returns a section or raises `HeaderParseError`, the only
exception its caller `get_parameter` catches (:2513-2518): the section number is
`'*' 1*digit`, and a value that is not one is "Expected section number ...". -/
def SectionOnlyHpe : Prop := ∀ (cfg : Cfg) (v : Str), onlyHpe (getSection cfg v) = true

/-- `*²`: `'²'.isdigit()` is true, so the digit loop takes it, and `int('²')` raises
`ValueError: invalid literal for int() with base 10: '²'` (:2457-2467). -/
theorem section_superscript :
    errOf (getSection cfgCaught [42, 0xB2]) =
      some (.valueError (S "invalid literal for int() with base 10: '" ++ [0xB2] ++ S "'")) := by
  decide +kernel

/-- The same `ValueError` from a whole Content-Type value. -/
theorem contentType_superscript :
    errOf (parseContentTypeHeader cfgCaught 100 (S "text/plain; a*" ++ [0xB2] ++ S "=x")) =
      some (.valueError (S "invalid literal for int() with base 10: '" ++ [0xB2] ++ S "'")) := by
  decide +kernel

theorem sectionOnlyHpe_refuted : ¬ SectionOnlyHpe := by
  intro h
  have h1 := h cfgCaught [42, 0xB2]
  have h2 : onlyHpe (getSection cfgCaught [42, 0xB2]) = false := by decide +kernel
  rw [h2] at h1
  exact Bool.false_ne_true h1

/-! ## `parse_mime_version` -/

/-- For every header value, `parse_mime_version` returns a `MIMEVersion` token and raises
nothing: a value that is not `major.minor` gets defects ("Expected MIME major version number
but found ...", :2253-2256). -/
def MimeVersionNoRaise : Prop :=
  ∀ (cfg : Cfg) (n : Nat) (v : Str), noRaise (parseMimeVersion cfg n v) = true

/-- `²`: `digits.isdigit()` holds (:2253), so `int(digits)` runs and raises `ValueError`. -/
theorem mimeVersion_superscript :
    errOf (parseMimeVersion cfgCaught 100 [0xB2]) =
      some (.valueError (S "invalid literal for int() with base 10: '" ++ [0xB2] ++ S "'")) := by
  decide +kernel

theorem mimeVersionNoRaise_refuted : ¬ MimeVersionNoRaise := by
  intro h
  have h1 := h cfgCaught 100 [0xB2]
  have h2 : noRaise (parseMimeVersion cfgCaught 100 [0xB2]) = false := by decide +kernel
  rw [h2] at h1
  exact Bool.false_ne_true h1

/-! ## `DisplayName.display_name` and `DisplayName.value` -/

/-- `display_name` of the display name `get_display_name` returned, as a Python outcome;
`true` when `get_display_name` raised. -/
def dnTotal : EPy (Tok × Str) → Bool
  | .ok (dn, _) => noRaise (displayName dn)
  | .error _ => true

/-- `value` of the display name `get_display_name` returned. -/
def dnValueTotal : EPy (Tok × Str) → Bool
  | .ok (dn, _) => noRaise dn.value
  | .error _ => true

/-- For every value `get_display_name` parses, the display name's `display_name` (the phrase
without its leading and trailing CFWS, :585-601) is a string; the address headers read it for
every group and mailbox (Lib/email/headerregistry.py:343-347). -/
def DisplayNameTotal : Prop :=
  ∀ (cfg : Cfg) (n : Nat) (v : Str), dnTotal (getDisplayName cfg n v) = true

/-- For every value `get_display_name` parses, the display name's `value` (:604-624: the
phrase's value, or the quoted `display_name` when the phrase has a defect or a quoted string)
is a string. -/
def DisplayNameValueTotal : Prop :=
  ∀ (cfg : Cfg) (n : Nat) (v : Str), dnValueTotal (getDisplayName cfg n v) = true

/-- `(c)`: the phrase is a lone CFWS token (`get_word` finds nothing after the comment, and the
loop of `get_phrase` takes the comment as CFWS). `display_name` pops it, leaving an empty list,
and `res[-1]` (:595) raises `IndexError`; `value` quotes the name (the phrase has a defect) and
calls `display_name`. -/
theorem displayName_comment :
    (match getDisplayName cfgCaught 100 (S "(c)") with
     | .ok (dn, _) => (errOf (displayName dn), errOf dn.value)
     | .error _ => (none, none)) = (some listIndexError, some listIndexError) := by
  decide +kernel

theorem displayNameTotal_refuted : ¬ DisplayNameTotal := by
  intro h
  have h1 := h cfgCaught 100 (S "(c)")
  have h2 : dnTotal (getDisplayName cfgCaught 100 (S "(c)")) = false := by decide +kernel
  rw [h2] at h1
  exact Bool.false_ne_true h1

/-- `value` raises on `(c)` on its own account: the phrase has a defect, so `value` takes the
quoting branch (:606-607, :612) and calls `display_name` (:622). -/
theorem displayNameValueTotal_refuted : ¬ DisplayNameValueTotal := by
  intro h
  have h1 := h cfgCaught 100 (S "(c)")
  have h2 : dnValueTotal (getDisplayName cfgCaught 100 (S "(c)")) = false := by decide +kernel
  rw [h2] at h1
  exact Bool.false_ne_true h1

/-! ## `str()` of a quoted string -/

/-- `str()` of the quoted string parsed from `v`, parsed again, is a whole quoted string with
the same `value`. -/
def qsReparse (cfg : Cfg) (n : Nat) (v : Str) : Bool :=
  match getQuotedString cfg n v with
  | .ok (q, _) =>
    match getQuotedString cfg n q.str, q.value with
    | .ok (q', rest), .ok val =>
      rest.isEmpty && (match q'.value with
        | .ok val' => val' == val
        | .error _ => false)
    | .error .fuel, _ => true
    | .error _, _ => false
    | .ok _, .error _ => true
  | .error _ => true

/-- `str()` of a parse tree is "a 'canonical' representation of the RFC-compliant form of the
substring that produced the parsed subtree, including minimal use of quoted pair quoting"
(module docstring, :46-49): for every value `get_quoted_string` parses, parsing its `str()`
again gives the same quoted string, with the same `value`. -/
def QuotedStringCanonical : Prop :=
  ∀ (cfg : Cfg) (n : Nat) (v : Str), DecSafe cfg → qsReparse cfg n v = true

/-- `_ew.decode` as CPython runs it on `=?utf-8?q?a?=`: `('a', 'utf-8', '', [])`; `ValueError`
elsewhere. -/
def cfgQ : Cfg :=
  { dec := fun s => if s == S "=?utf-8?q?a?=" then .ok (S "a") (S "utf-8") [] [] else .caught }

theorem cfgQ_safe : DecSafe cfgQ := by
  intro s c m h
  simp only [cfgQ] at h
  split at h <;> cases h

/-- `"\=?utf-8?q?a?="`: the quoted pair `\=` keeps `get_bare_quoted_string` from seeing an
encoded word (its test is `value[:2] == '=?'`, :1261), so the value is the literal
`=?utf-8?q?a?=`. `str()` writes it back as `"=?utf-8?q?a?="` (`make_quoted_pairs` only escapes
`\` and `"`), and that text parses as an encoded word inside a quoted string, whose value is
`a`. -/
theorem quotedString_reparse :
    (match getQuotedString cfgQ 100 (S "\"\\=?utf-8?q?a?=\"") with
     | .ok (q, _) => (q.str, q.value.toOption,
        (match getQuotedString cfgQ 100 q.str with
         | .ok (q', _) => q'.value.toOption
         | .error _ => none))
     | .error _ => ([], none, none)) =
    (S "\"=?utf-8?q?a?=\"", some (S "=?utf-8?q?a?="), some (S "a")) := by
  decide +kernel

theorem quotedStringCanonical_refuted : ¬ QuotedStringCanonical := by
  intro h
  have h1 := h cfgQ 100 (S "\"\\=?utf-8?q?a?=\"") cfgQ_safe
  have h2 : qsReparse cfgQ 100 (S "\"\\=?utf-8?q?a?=\"") = false := by decide +kernel
  rw [h2] at h1
  exact Bool.false_ne_true h1

end PyLean.TextLibs.Email
