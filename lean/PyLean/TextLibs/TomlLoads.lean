import PyLean.TextLibs.TomlScen

/-!
`loads` itself: its argument check, the CRLF normalisation, top-level blank and comment lines,
and the two statement errors; `skip_comment` and `skip_until`.
-/

namespace PyLean.TextLibs.Toml

/-! ## CRLF, _parser.py:154-161 -/

theorem crlf_cons {c : Nat} (h : c ≠ 13) (t : Str) : crlf (c :: t) = c :: crlf t := by
  conv => lhs; unfold crlf
  split
  · rename_i heq; simp at heq; exact absurd heq.1 h
  · rename_i heq; simp at heq; obtain ⟨rfl, rfl⟩ := heq; rfl
  · simp at *

theorem crlf_append {a : Str} (h : 13 ∉ a) (b : Str) : crlf (a ++ b) = a ++ crlf b := by
  induction a with
  | nil => rfl
  | cons c r ih =>
    have hc : c ≠ 13 := fun e => h (by simp [e])
    have hr : 13 ∉ r := fun m => h (by simp [m])
    rw [List.cons_append, crlf_cons hc, ih hr]; rfl

/-- `s` with each character paired with a flag: a newline whose flag is set is written as CRLF. -/
def withCR : Str → List Bool → Str
  | [], _ => []
  | c :: r, [] => c :: withCR r []
  | c :: r, b :: bs => if c = 10 ∧ b = true then 13 :: 10 :: withCR r bs else c :: withCR r bs

theorem crlf_withCR : ∀ (s : Str) (bs : List Bool), 13 ∉ s → crlf (withCR s bs) = s
  | [], _, _ => rfl
  | c :: r, [], h => by
    have hc : c ≠ 13 := fun e => h (by simp [e])
    rw [withCR, crlf_cons hc, crlf_withCR r [] (fun m => h (by simp [m]))]
  | c :: r, b :: bs, h => by
    have hc : c ≠ 13 := fun e => h (by simp [e])
    have ih := crlf_withCR r bs (fun m => h (by simp [m]))
    unfold withCR
    split
    · next hcb => rw [hcb.1]; simp only [crlf]; rw [ih]
    · rw [crlf_cons hc, ih]

/-- `loads`'s argument, TOML 1.1 ("Newline means LF (0x0A) or CRLF (0x0D 0x0A)") and the docs
of `loads` ("Load TOML from a str object"): (1) for every text without CR and every choice of
which newlines are written as CRLF, `loads` gives exactly what it gives on the LF text (the
same dict or the same error, at the same position of the normalised document); (2) a CR not
followed by a newline is kept, so `loads('\r' + t)` raises "Invalid statement" at 0; (3) an
argument whose `replace` raises `AttributeError` or `TypeError` (not a `str`) raises
`TypeError("Expected str object, not '<qualname>'")`. (2) and (3) with at least four and one
frames left. -/
def LoadsInput : Prop :=
  (∀ (pf : ParseFloat) (maxK maxD : Nat) (tz : TzCache) (fr : Nat) (s : Str) (bs : List Bool), 13 ∉ s →
    loads pf maxK maxD tz fr (.str (withCR s bs)) = loads pf maxK maxD tz fr (.str s)) ∧
  (∀ (pf : ParseFloat) (maxK maxD : Nat) (tz : TzCache) (fr : Nat) (t : Str), 4 ≤ fr → t.head? ≠ some 10 →
    loads pf maxK maxD tz fr (.str (13 :: t)) = .error (tdeS "Invalid statement" (13 :: crlf t) 0)) ∧
  (∀ (pf : ParseFloat) (maxK maxD : Nat) (tz : TzCache) (fr : Nat) (q : String), 1 ≤ fr →
    loads pf maxK maxD tz fr (.other q) = .error (.typeError s!"Expected str object, not '{q}'"))

theorem loadsInput_proven : LoadsInput := by
  refine ⟨?_, ?_, ?_⟩
  · intro pf maxK maxD tz fr s bs h
    simp only [loads, crlf_withCR s bs h, crlf_id s h]
  · intro pf maxK maxD tz fr t hfr ht
    have hc : crlf (13 :: t) = 13 :: crlf t := by
      cases t with
      | nil => rfl
      | cons d r =>
        have hd : d ≠ 10 := fun e => ht (by simp [e])
        conv => lhs; unfold crlf
        split
        · rename_i heq; simp at heq; exact absurd heq.1 hd
        · rename_i heq; simp at heq; obtain ⟨rfl, rfl⟩ := heq; rfl
        · simp at *
    have hg : (13 :: crlf t)[0]? = some 13 := rfl
    have hs0 : skipChars (13 :: crlf t) 0 tomlWs = 0 := skipChars_at hg (by decide)
    simp only [loads, need_ok (show 1 ≤ fr by omega), hc, need_ok (show 3 ≤ fr - 1 by omega)]
    simp only [List.length_cons, mainLoop, hs0, hg, show ((13 : Nat) == 10) = false from rfl,
      show keyInitial 13 = false from rfl, show ((13 : Nat) == 91) = false from rfl,
      show ((13 : Nat) != 35) = true from rfl, Bool.false_eq_true, ite_false, ite_true, bind, Except.bind]
  · intro pf maxK maxD tz fr q hfr
    simp [loads, need_ok hfr]

/-! ## Comments, _parser.py:329-360 -/

/-- Comments, TOML 1.1 "Comment" ("Control characters other than tab (U+0000 to U+0008, U+000A
to U+001F, U+007F) are not permitted in comments"; a comment runs to the end of the line):
`skip_comment` at `#` followed by allowed characters returns the position of the newline that
ends them, or the end of the document when none does (`skip_until` with `error_on_eof=False`);
at a forbidden character before the newline (or the end) it raises "Found invalid character"
there; at anything but `#` it returns its argument. -/
def CommentRules : Prop :=
  (∀ (src : Str) (pos : Nat) (t rest : Str), (∀ x ∈ t, illegalBasic x = false) →
    (rest = [] ∨ rest.head? = some 10) → src.drop pos = 35 :: t ++ rest →
    skipComment src pos = .ok (pos + 1 + t.length)) ∧
  (∀ (src : Str) (pos c : Nat) (t1 t2 rest : Str), (∀ x ∈ t1, illegalBasic x = false) → illegalBasic c = true →
    c ≠ 10 → 10 ∉ t2 → (rest = [] ∨ rest.head? = some 10) → src.drop pos = 35 :: t1 ++ c :: t2 ++ rest →
    skipComment src pos = .error (tde (S "Found invalid character " ++ reprS [c]) src (pos + 1 + t1.length))) ∧
  (∀ (src : Str) (pos : Nat), src[pos]? ≠ some 35 → skipComment src pos = .ok pos)

theorem commentRules_proven : CommentRules := by
  refine ⟨?_, ?_, ?_⟩
  · intro src pos t rest ht hrest h
    have hg := getElem?_of_drop h
    have h1 : src.drop (pos + 1) = t ++ rest := by simpa using drop_succ_of_drop h
    have hn10 : 10 ∉ t := fun m => absurd (ht 10 m) (by decide)
    have hsl : sl src (pos + 1) (pos + 1 + t.length) = t := sl_of_drop h1
    rcases hrest with rfl | hr
    · have hfind : findSub [10] (src.drop (pos + 1)) = none := by
        rw [h1]; simpa using findSub_single_none hn10
      have hlen : src.length = pos + 1 + t.length := by
        have := congrArg List.length h; simp at this; omega
      simp only [skipComment, hg, show (some 35 == some 35) = true from rfl, ite_true, skipUntil, hfind,
        Bool.false_eq_true, ite_false, hlen, hsl, firstIdx_none ht]
    · obtain ⟨r, rfl⟩ : ∃ r, rest = 10 :: r := by
        cases rest with
        | nil => simp at hr
        | cons d r => simp at hr; exact ⟨r, by rw [hr]⟩
      have hfind : findSub [10] (src.drop (pos + 1)) = some t.length := by rw [h1]; exact findSub_single hn10
      simp only [skipComment, hg, show (some 35 == some 35) = true from rfl, ite_true, skipUntil, hfind, hsl,
        firstIdx_none ht]
  · intro src pos c t1 t2 rest ht1 hc hc10 ht2 hrest h
    have hg := getElem?_of_drop h
    have h1 : src.drop (pos + 1) = (t1 ++ c :: t2) ++ rest := by simpa using drop_succ_of_drop h
    have hn10 : 10 ∉ t1 ++ c :: t2 := by
      simp only [List.mem_append, List.mem_cons, not_or]
      exact ⟨fun m => absurd (ht1 10 m) (by decide), fun e => hc10 e.symm, ht2⟩
    have hsl : sl src (pos + 1) (pos + 1 + (t1 ++ c :: t2).length) = t1 ++ c :: t2 := sl_of_drop h1
    have hfi : firstIdx illegalBasic (t1 ++ c :: t2) = some t1.length := firstIdx_append ht1 hc
    have hgc : src.getD (pos + 1 + t1.length) 0 = c := by
      have : src.drop (pos + 1 + t1.length) = c :: (t2 ++ rest) :=
        drop_add_of_drop (a := t1) (by simpa using h1)
      simp [List.getD, getElem?_of_drop this]
    rcases hrest with rfl | hr
    · have hfind : findSub [10] (src.drop (pos + 1)) = none := by
        rw [h1]; simpa using findSub_single_none hn10
      have hlen : src.length = pos + 1 + (t1 ++ c :: t2).length := by
        have := congrArg List.length h; simp at this ⊢; omega
      simp only [skipComment, hg, show (some 35 == some 35) = true from rfl, ite_true, skipUntil, hfind,
        Bool.false_eq_true, ite_false, hlen, hsl, hfi, hgc]
    · obtain ⟨r, rfl⟩ : ∃ r, rest = 10 :: r := by
        cases rest with
        | nil => simp at hr
        | cons d r => simp at hr; exact ⟨r, by rw [hr]⟩
      have hfind : findSub [10] (src.drop (pos + 1)) = some (t1 ++ c :: t2).length := by
        rw [h1]; exact findSub_single hn10
      simp only [skipComment, hg, show (some 35 == some 35) = true from rfl, ite_true, skipUntil, hfind, hsl,
        hfi, hgc]
  · intro src pos h
    have : (src[pos]? == some 35) = false := by
      cases hs : src[pos]? with
      | none => rfl
      | some d => rw [hs] at h; simpa using h
    simp [skipComment, this]

/-! ## Top-level lines, _parser.py:169-217 -/

/-- A line of spaces and tabs, then an optional comment, then a newline. -/
structure TopLine where
  w : Str
  cmt : Option Str

def TopLine.enc (l : TopLine) : Str :=
  l.w ++ (match l.cmt with
    | none => []
    | some t => 35 :: t) ++ [10]

def TopLine.ok (l : TopLine) : Prop := allWs l.w ∧ ∀ t, l.cmt = some t → ∀ x ∈ t, illegalBasic x = false

def topEnc (ls : List TopLine) : Str := ls.flatMap TopLine.enc

theorem topLine_no13 (l : TopLine) (h : l.ok) : 13 ∉ l.enc := by
  obtain ⟨hw, ht⟩ := h
  have := allWs_no13 hw
  cases hc : l.cmt with
  | none => simp [TopLine.enc, hc]; exact this
  | some t =>
    have h13 : 13 ∉ t := fun m => absurd (ht t hc 13 m) (by decide)
    simp [TopLine.enc, hc]; exact ⟨this, h13⟩

theorem topEnc_no13 : ∀ (ls : List TopLine), (∀ l ∈ ls, l.ok) → 13 ∉ topEnc ls
  | [], _ => by simp [topEnc]
  | l :: ls, h => by
    have h1 := topLine_no13 l (h l (by simp))
    have h2 := topEnc_no13 ls (fun x hx => h x (by simp [hx]))
    simp only [topEnc, List.flatMap_cons, List.mem_append, not_or] at h2 ⊢
    exact ⟨h1, h2⟩

/-- The statement loop skips blank and comment lines, one round each. -/
theorem mainLoop_top {cfg : Cfg} {src : Str} {R : Nat} (hR : 3 ≤ R) :
    ∀ (ls : List TopLine) (pos fuel : Nat) (out : Out) (header : Key) (rest : Str), (∀ l ∈ ls, l.ok) →
      src.drop pos = topEnc ls ++ rest →
      mainLoop cfg src R (fuel + ls.length) pos out header =
        mainLoop cfg src R fuel (pos + (topEnc ls).length) out header
  | [], pos, fuel, out, header, rest, _, _ => by simp [topEnc]
  | l :: ls, pos, fuel, out, header, rest, hok, h => by
    obtain ⟨hw, hcm⟩ := hok l (by simp)
    have hls : ∀ x ∈ ls, x.ok := fun x hx => hok x (by simp [hx])
    have hlen : (topEnc (l :: ls)).length = l.enc.length + (topEnc ls).length := by simp [topEnc]
    rw [show fuel + (l :: ls).length = (fuel + ls.length) + 1 by simp; omega]
    cases hc : l.cmt with
    | none =>
      have h0 : src.drop pos = l.w ++ 10 :: (topEnc ls ++ rest) := by
        rw [h]; simp [topEnc, TopLine.enc, hc]
      have hs : skipChars src pos tomlWs = pos + l.w.length :=
        skipChars_of_drop h0 hw (by intro x hx; simp at hx; subst hx; decide)
      have hd1 : src.drop (pos + l.w.length) = 10 :: (topEnc ls ++ rest) := drop_add_of_drop h0
      have hg := getElem?_of_drop hd1
      have ih := mainLoop_top (cfg := cfg) hR ls (pos + l.w.length + 1) fuel out header rest hls
        (drop_succ_of_drop hd1)
      simp only [mainLoop, hs, hg, show ((10 : Nat) == 10) = true from rfl, ite_true]
      rw [ih, hlen]; congr 1; simp [TopLine.enc, hc]; omega
    | some t =>
      have ht := hcm t hc
      have h0 : src.drop pos = l.w ++ 35 :: (t ++ 10 :: (topEnc ls ++ rest)) := by
        rw [h]; simp [topEnc, TopLine.enc, hc]
      have hs : skipChars src pos tomlWs = pos + l.w.length :=
        skipChars_of_drop h0 hw (by intro x hx; simp at hx; subst hx; decide)
      have hd1 : src.drop (pos + l.w.length) = 35 :: t ++ (10 :: (topEnc ls ++ rest)) := by
        simpa using drop_add_of_drop h0
      have hg := getElem?_of_drop hd1
      have hcom := commentRules_proven.1 src (pos + l.w.length) t (10 :: (topEnc ls ++ rest)) ht
        (Or.inr rfl) hd1
      have hd2 : src.drop (pos + l.w.length + 1 + t.length) = 10 :: (topEnc ls ++ rest) := by
        have := drop_add_of_drop (a := 35 :: t) (by simpa using hd1)
        have e : pos + l.w.length + (35 :: t).length = pos + l.w.length + 1 + t.length := by simp; omega
        rw [e] at this; exact this
      have hg2 := getElem?_of_drop hd2
      have ih := mainLoop_top (cfg := cfg) hR ls (pos + l.w.length + 1 + t.length + 1) fuel out header rest hls
        (drop_succ_of_drop hd2)
      simp only [mainLoop, hs, hg, show ((35 : Nat) == 10) = false from rfl, show keyInitial 35 = false from rfl,
        show ((35 : Nat) == 91) = false from rfl, show ((35 : Nat) != 35) = false from rfl, Bool.false_eq_true,
        ite_false, bind, Except.bind, pure, Except.pure, need_skipComment hR, hcom, hg2,
        show ((10 : Nat) != 10) = false from rfl]
      rw [ih, hlen]; congr 1; simp [TopLine.enc, hc]; omega

/-- A key/value line followed by spaces or tabs and then a character that is not a newline or
`#`: "Expected newline or end of document after a statement" there. -/
theorem mainLoop_kv_trailing {cfg : Cfg} {src : Str} {R f pos p q c d : Nat} {out out' : Out} {header : Key}
    (hc : src[pos]? = some c) (hkey : keyInitial c = true) (hws : tomlWs c = false) (h10 : c ≠ 10)
    (hrule : keyValueRule cfg src (R - 1) pos out header = .ok (p, out')) (hR : 3 ≤ R)
    (hsk : skipChars src p tomlWs = q) (hq : src[q]? = some d) (hd35 : d ≠ 35) (hd10 : d ≠ 10) :
    mainLoop cfg src R (f + 1) pos out header =
      .error (tdeS "Expected newline or end of document after a statement" src q) := by
  have hs0 : skipChars src pos tomlWs = pos := skipChars_at hc hws
  have hb : (c == 10) = false := by simp [h10]
  have hcm : skipComment src q = .ok q := commentRules_proven.2.2 src q (by rw [hq]; simpa using hd35)
  have hd : (d != 10) = true := by simpa using hd10
  simp only [mainLoop, hs0, hc, hb, Bool.false_eq_true, ite_false, hkey, ite_true, need_ok (show 1 ≤ R by omega),
    hrule, bind, Except.bind, pure, Except.pure, hsk, need_skipComment hR, hcm, hq, hd]

/-- Top-level lines, TOML 1.1 ("Whitespace means tab or space"; "A hash symbol marks the rest of
the line as a comment"; "There must be a newline (or EOF) after a key/value pair"): for every
run of blank and comment lines `L`, with at least four frames left and `3 * depth + 14` for each
value: (1) `loads(L + D)` for a document `D` of `DocRoundTrip` returns the same dict as `D` alone
(comment-only documents give `{}`); (2) `L` then spaces or tabs then a character that starts no
statement (not a newline, `#`, `[`, CR or a key character) raises "Invalid statement" at that
character; (3) `L`, one `key = value` line, spaces or tabs, then a character other than a newline,
`#`, CR or `"` raises "Expected newline or end of document after a statement" at that character. -/
def TopLevel : Prop :=
  ∀ (pf : ParseFloat) (maxK maxD : Nat) (tz : TzCache) (fr : Nat) (ls : List TopLine), (∀ l ∈ ls, l.ok) → 4 ≤ fr →
    (∀ kvs : List Line, (∀ l ∈ kvs, l.ok) → (kvs.map (·.k.val)).Nodup → (∀ l ∈ kvs, 3 * l.v.depth + 14 ≤ fr) →
      loads pf maxK maxD tz fr (.str (topEnc ls ++ docEnc kvs)) = .ok (kvs.map (fun l => (l.k.val, l.v.val)))) ∧
    (∀ (w : Str) (c : Nat) (t : Str), allWs w → c ≠ 10 → c ≠ 35 → c ≠ 91 → c ≠ 13 → keyInitial c = false →
      tomlWs c = false →
      loads pf maxK maxD tz fr (.str (topEnc ls ++ w ++ c :: t)) =
        .error (tdeS "Invalid statement" (topEnc ls ++ w ++ c :: crlf t) ((topEnc ls).length + w.length))) ∧
    (∀ (l : Line) (w : Str) (c : Nat) (t : Str), l.ok → allWs w → c ≠ 10 → c ≠ 35 → c ≠ 13 → c ≠ 34 →
      tomlWs c = false → 3 * l.v.depth + 14 ≤ fr →
      loads pf maxK maxD tz fr (.str (topEnc ls ++ l.enc ++ w ++ c :: t)) =
        .error (tdeS "Expected newline or end of document after a statement"
          (topEnc ls ++ l.enc ++ w ++ c :: crlf t) ((topEnc ls).length + l.enc.length + w.length)))

theorem topLevel_proven : TopLevel := by
  intro pf maxK maxD tz fr ls hls hfr
  have htop13 := topEnc_no13 ls hls
  have htoplen : ls.length ≤ (topEnc ls).length := by
    clear hls htop13
    induction ls with
    | nil => simp [topEnc]
    | cons l t ih => simp [topEnc, TopLine.enc] at ih ⊢; omega
  refine ⟨?_, ?_, ?_⟩
  · intro kvs hok hnd hdep
    have h13 : 13 ∉ topEnc ls ++ docEnc kvs := by
      simp only [List.mem_append, not_or]; exact ⟨htop13, docEnc_no13 kvs hok⟩
    rw [loads_eq pf maxK maxD tz fr _ h13 hfr]
    have hkvlen : kvs.length ≤ (docEnc kvs).length := by
      clear hok hnd hdep h13
      induction kvs with
      | nil => simp [docEnc]
      | cons l t ih =>
        have hl : l.enc.length ≥ 1 := by simp [Line.enc]; omega
        by_cases ht : t = []
        · subst ht; simp [docEnc]; omega
        · have := ih; rw [docEnc_cons l t ht]; simp; omega
    obtain ⟨f, hf⟩ : ∃ f, (topEnc ls ++ docEnc kvs).length + 1 = f + ls.length ∧ kvs.length < f := by
      refine ⟨(topEnc ls ++ docEnc kvs).length + 1 - ls.length, ?_, ?_⟩ <;> simp <;> omega
    rw [hf.1, mainLoop_top (by omega) ls 0 f Out.init [] (docEnc kvs) hls (by simp)]
    by_cases hkv : kvs = []
    · subst hkv
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by have := hf.2; simp at this; omega⟩
      have hend : (topEnc ls ++ docEnc [])[(topEnc ls).length]? = none := by simp [docEnc]
      have hs : skipChars (topEnc ls ++ docEnc []) (topEnc ls).length tomlWs = (topEnc ls).length :=
        skipChars_stop (fun x hx => by simp [docEnc] at hx)
      simp [mainLoop, hs, hend, Out.init]
    · have := doc_loop pf maxK maxD tz (topEnc ls ++ docEnc kvs) (fr - 1) kvs (0 + (topEnc ls).length) f Out.init
        hkv hok hnd (by intro l _; rfl) (by simp) hf.2 (fun l hl => by have := hdep l hl; omega)
      simpa [Out.init] using this
  · intro w c t hw hc10 hc35 hc91 hc13 hki hcws
    have hw13 := allWs_no13 hw
    have hcr : crlf (topEnc ls ++ w ++ c :: t) = topEnc ls ++ w ++ c :: crlf t := by
      rw [List.append_assoc, crlf_append htop13, crlf_append hw13, crlf_cons hc13]; simp
    generalize hsrc : topEnc ls ++ w ++ c :: crlf t = src
    simp only [loads, need_ok (show 1 ≤ fr by omega), hcr, hsrc, need_ok (show 3 ≤ fr - 1 by omega)]
    have hlen : ls.length ≤ src.length := by rw [← hsrc]; simp; omega
    obtain ⟨f, hf⟩ : ∃ f, src.length + 1 = (f + 1) + ls.length := ⟨src.length - ls.length, by omega⟩
    rw [hf, mainLoop_top (by omega) ls 0 (f + 1) Out.init [] (w ++ c :: crlf t) hls (by rw [← hsrc, List.drop_zero]; simp [List.append_assoc])]
    have hd : src.drop (0 + (topEnc ls).length) = w ++ c :: crlf t := by rw [← hsrc]; simp
    have hs : skipChars src (0 + (topEnc ls).length) tomlWs = 0 + (topEnc ls).length + w.length :=
      skipChars_of_drop hd hw (by intro x hx; simp at hx; subst hx; exact hcws)
    have hg : src[0 + (topEnc ls).length + w.length]? = some c := getElem?_of_drop (by simpa using drop_add_of_drop hd)
    have hc35' : (c != 35) = true := by simpa using hc35
    simp only [mainLoop, hs, hg, show (c == 10) = false by simpa using hc10, hki,
      show (c == 91) = false by simpa using hc91, hc35', Bool.false_eq_true, ite_false, ite_true, bind, Except.bind]
    congr 2; omega
  · intro l w c t hl hw hc10 hc35 hc13 hc34 hcws hdep
    obtain ⟨hk, hw1, hw2, hv⟩ := hl
    have hw13 := allWs_no13 hw
    have hl13 := line_no13 l ⟨hk, hw1, hw2, hv⟩
    have hcr : crlf (topEnc ls ++ l.enc ++ w ++ c :: t) = topEnc ls ++ l.enc ++ w ++ c :: crlf t := by
      rw [List.append_assoc, List.append_assoc, crlf_append htop13, crlf_append hl13, crlf_append hw13,
        crlf_cons hc13]
      simp
    generalize hsrc : topEnc ls ++ l.enc ++ w ++ c :: crlf t = src
    simp only [loads, need_ok (show 1 ≤ fr by omega), hcr, hsrc, need_ok (show 3 ≤ fr - 1 by omega)]
    have hlen : ls.length ≤ src.length := by rw [← hsrc]; simp; omega
    obtain ⟨f, hf⟩ : ∃ f, src.length + 1 = (f + 1) + ls.length := ⟨src.length - ls.length, by omega⟩
    rw [hf, mainLoop_top (by omega) ls 0 (f + 1) Out.init [] (l.enc ++ w ++ c :: crlf t) hls
      (by rw [← hsrc, List.drop_zero]; simp [List.append_assoc])]
    -- the key/value line
    generalize hP : 0 + (topEnc ls).length = P
    have hd : src.drop P = l.enc ++ (w ++ c :: crlf t) := by rw [← hP, ← hsrc]; simp
    have hvpos : src.drop (P + l.k.enc.length + l.w1.length + 1 + l.w2.length) = l.v.enc ++ (w ++ c :: crlf t) := by
      have := drop_add_of_drop (a := l.k.enc ++ l.w1 ++ 61 :: l.w2) (by simpa [Line.enc] using hd)
      have e : P + (l.k.enc ++ l.w1 ++ 61 :: l.w2).length = P + l.k.enc.length + l.w1.length + 1 + l.w2.length := by
        simp; omega
      rw [e] at this; exact this
    have hrest34 : ∀ x, (w ++ c :: crlf t).head? = some x → x ≠ 34 := by
      intro x hx
      cases w with
      | nil => simp at hx; omega
      | cons y ys => simp at hx; subst hx; have := hw y (by simp); revert this; simp [tomlWs]; omega
    have hvlen : l.v.enc.length ≤ src.length := by
      have := congrArg List.length hd; simp [Line.enc] at this; omega
    have hneed := SV.need_le l.v
    have hvp := SV.parse (mkCfg pf maxK maxD tz) src l.v (fr - 1 - 1 - 1 - 1) _ (vFuel src - 1) _ hv hrest34 hvpos
      (by unfold vFuel; omega) (by omega)
    have hkv := pkv (r := fr - 1 - 1 - 1) (by omega) hk hw1 hw2 (fun x hx => ((SV.head_props l.v _).2 x hx).2.2.2)
      (by simpa [Line.enc] using hd) hvp
    rw [show vFuel src - 1 + 1 = vFuel src by unfold vFuel; omega] at hkv
    have hpend : P + l.k.enc.length + l.w1.length + 1 + l.w2.length + l.v.enc.length = P + l.enc.length := by
      simp [Line.enc]; omega
    rw [hpend] at hkv
    have hrule := kvr_one (R := fr - 1 - 1) (out := Out.init) (by omega) hkv rfl
    obtain ⟨c0, t0, hke, hki, hcws0, hc100⟩ := keyInitial_head l.k hk
    have hc0 : src[P]? = some c0 := getElem?_of_drop (r := t0 ++ l.w1 ++ 61 :: l.w2 ++ l.v.enc ++ (w ++ c :: crlf t))
      (by rw [hd]; simp [Line.enc, hke])
    have hd2 : src.drop (P + l.enc.length) = w ++ c :: crlf t := drop_add_of_drop hd
    have hsk : skipChars src (P + l.enc.length) tomlWs = P + l.enc.length + w.length :=
      skipChars_of_drop hd2 hw (by intro x hx; simp at hx; subst hx; exact hcws)
    have hq : src[P + l.enc.length + w.length]? = some c := getElem?_of_drop (by simpa using drop_add_of_drop hd2)
    rw [mainLoop_kv_trailing hc0 hki hcws0 hc100 hrule (by omega) hsk hq hc35 hc10, ← hP]
    simp

end PyLean.TextLibs.Toml
