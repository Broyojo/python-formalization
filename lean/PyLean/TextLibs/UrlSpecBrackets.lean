import PyLean.TextLibs.UrlSpecNetloc

/-!
Which bracketed hosts `urlsplit` accepts, stated positively: `_check_bracketed_host` accepts
exactly the IPvFuture literals of its regular expression (written out) and the addresses
`ipaddress.ip_address` reads as IPv6, and refuses an IPv4 address; `_check_bracketed_netloc`
accepts exactly a host part (after the last `@`) that starts with `[`, has nothing but a `:` port
after the matching `]`, and holds an accepted host. And where `_splitparams` cuts a path.
-/

namespace PyLean.TextLibs.Url

open PyLean

set_option linter.unusedSimpArgs false

/-! ## Helpers -/

theorem dropWhile_prefix (p : Nat → Bool) (a b : Str) (ha : ∀ c ∈ a, p c = true)
    (hb : ∀ x t, b = x :: t → p x = false) : (a ++ b).dropWhile p = b := by
  induction a with
  | nil =>
    cases b with
    | nil => rfl
    | cons x t => simp [List.dropWhile_cons, hb x t rfl]
  | cons c r ih =>
    simp only [List.cons_append, List.dropWhile_cons, ha c List.mem_cons_self, ite_true]
    exact ih (fun x hx => ha x (List.mem_cons_of_mem _ hx))

/-- `part c s` read as `takeWhile`/`dropWhile`. -/
theorem part_take_drop (c : Nat) : ∀ s : Str,
    (part c s).1 = s.takeWhile (· != c) ∧ (part c s).2.getD [] = (s.dropWhile (· != c)).drop 1
  | [] => by simp [part]
  | x :: r => by
    rw [part_cons]
    by_cases hx : x = c
    · subst hx; simp
    · have ih := part_take_drop c r
      rw [if_neg hx]
      have hb : (x != c) = true := by simpa using hx
      simp only [List.takeWhile_cons, List.dropWhile_cons, hb, ite_true]
      exact ⟨congrArg (x :: ·) ih.1, ih.2⟩

theorem afterAt_exists (n : Str) : ∃ hi, AfterAt n hi := by
  rcases hr : rpart 64 n with ⟨_ | ui, hi⟩
  · exact ⟨hi, Or.inl (by have := rpart_none hr; exact ⟨this.2, this.1⟩)⟩
  · have := rpart_some hr
    exact ⟨hi, Or.inr ⟨ui, this.1, this.2⟩⟩

theorem afterAt_unique (n hi hi' : Str) (h : AfterAt n hi) (h' : AfterAt n hi') : hi = hi' := by
  rw [← afterAt_rpart n hi h, ← afterAt_rpart n hi' h']

/-! ## `_check_bracketed_host` -/

/-- The characters of `[a-fA-F0-9]`. -/
def hexChars : Str := cs "0123456789abcdefABCDEF"

set_option maxRecDepth 20000 in
theorem hexChars_lt : ∀ c ∈ hexChars, c < 128 := by decide

set_option maxRecDepth 20000 in
theorem isHex_iff (c : Nat) : isHex c = true ↔ c ∈ hexChars := by
  by_cases hc : c < 128
  · have key : ∀ c < 128, (isHex c = true ↔ c ∈ hexChars) := by decide
    exact key c hc
  · constructor
    · intro h; simp [isHex, isAsciiDigit] at h; omega
    · intro h; exact absurd (hexChars_lt c h) hc

/-- A match of `\A[vV][a-fA-F0-9]+\..+\z` (:548): `v` or `V`, hex digits, a `.`, and at least one
character other than a newline (`.` does not match `\n` without `re.DOTALL`). -/
def IPvFutureForm (h : Str) : Prop :=
  ∃ c hex t, h = c :: (hex ++ 46 :: t) ∧ (c = 118 ∨ c = 86) ∧ hex ≠ [] ∧ (∀ d ∈ hex, d ∈ hexChars) ∧
    t ≠ [] ∧ 10 ∉ t

theorem ipvFutureOk_iff (h : Str) : ipvFutureOk h = true ↔ IPvFutureForm h := by
  cases h with
  | nil =>
    simp only [ipvFutureOk, Bool.false_eq_true, false_iff]
    rintro ⟨c, hex, t, he, _⟩; cases he
  | cons c r =>
    constructor
    · intro hok
      simp only [ipvFutureOk, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hok
      obtain ⟨hc, hm⟩ := hok
      have hsplit : r = r.takeWhile isHex ++ r.dropWhile isHex := (List.takeWhile_append_dropWhile).symm
      generalize hd : r.dropWhile isHex = D at hm hsplit
      rcases D with _ | ⟨x, t⟩
      · simp at hm
      · by_cases hx : x = 46
        · subst hx
          simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true,
            bne_iff_ne, ne_eq] at hm
          obtain ⟨⟨hhex, ht⟩, hnl⟩ := hm
          refine ⟨c, r.takeWhile isHex, t, congrArg (c :: ·) hsplit, hc, hhex, ?_, ht, fun m => hnl 10 m rfl⟩
          intro d hd'
          exact (isHex_iff d).1 (mem_takeWhile_p hd')
        · simp [hx] at hm
    · rintro ⟨c', hex, t, he, hc, hhex, hall, ht, hnl⟩
      simp only [List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have hall' : ∀ d ∈ hex, isHex d = true := fun d hd => (isHex_iff d).2 (hall d hd)
      have h46 : ∀ x t', (46 :: t) = x :: t' → isHex x = false := by
        intro x t' e; cases e; decide
      simp only [ipvFutureOk, takeWhile_prefix isHex hex _ hall' h46, dropWhile_prefix isHex hex _ hall' h46]
      have hhe : hex.isEmpty = false := by cases hex <;> simp_all
      have hte : t.isEmpty = false := by cases t <;> simp_all
      have hta : t.all (· != 10) = true := by
        simp only [List.all_eq_true, bne_iff_ne, ne_eq]
        intro x hx e; subst e; exact hnl hx
      rcases hc with rfl | rfl <;> simp [hhe, hte, hta]

/-- A host starting with `v` or `V` (it is checked as IPvFuture). -/
def VStart (h : Str) : Prop := h.take 1 = [118] ∨ h.take 1 = [86]

instance (h : Str) : Decidable (VStart h) := by unfold VStart; infer_instance

/-- A bracketed host `_check_bracketed_host` accepts: an IPvFuture literal, or (not starting with
`v`/`V`) a host `ipaddress.ip_address` reads as an IPv6 address (the oracle `ipk` answers
`some false`). -/
def HostOk (ipk : Str → Option Bool) (h : Str) : Prop :=
  (VStart h ∧ IPvFutureForm h) ∨ (¬VStart h ∧ ipk h = some false)

theorem checkBracketedHost_iff (ipk : Str → Option Bool) (h : Str) :
    checkBracketedHost ipk h = .ok () ↔ HostOk ipk h := by
  unfold checkBracketedHost HostOk
  by_cases hv : VStart h
  · have hv' : (h.take 1 == [118] || h.take 1 == [86]) = true := by
      rcases hv with e | e <;> simp [e]
    rw [if_pos hv']
    split
    · next hok => simp [hv, (ipvFutureOk_iff h).1 hok]
    · next hok =>
      simp only [reduceCtorEq, false_iff, not_or, not_and, Decidable.not_not]
      exact ⟨fun _ hf => hok ((ipvFutureOk_iff h).2 hf), fun hn => absurd hv hn⟩
  · have hv' : (h.take 1 == [118] || h.take 1 == [86]) = false := by
      simp only [VStart, not_or] at hv
      simp [hv.1, hv.2]
    rw [if_neg (by simp [hv'])]
    rcases hk : ipk h with _ | _ | _ <;> simp [hv]

/-! ## `_check_bracketed_netloc` -/

/-- What `_check_bracketed_netloc` accepts, for the host part `hi` after the last `@`: without `[`,
the host before the first `:` is accepted by `_check_bracketed_host`; with `[`, the part starts
with it, what follows the first `]` (if any) is empty or starts with `:`, and the host between
them is accepted. -/
def BracketOk (ipk : Str → Option Bool) (hi : Str) : Prop :=
  (91 ∉ hi → HostOk ipk (hi.takeWhile (· != 58))) ∧
  (91 ∈ hi → ∃ y, hi = 91 :: y ∧
    (((y.dropWhile (· != 93)).drop 1) = [] ∨ ((y.dropWhile (· != 93)).drop 1).take 1 = [58]) ∧
    HostOk ipk (y.takeWhile (· != 93)))

theorem checkBracketedNetloc_iff (ipk : Str → Option Bool) (n hi : Str) (hn : AfterAt n hi) :
    checkBracketedNetloc ipk n = .ok () ↔ BracketOk ipk hi := by
  unfold checkBracketedNetloc BracketOk
  simp only [afterAt_rpart n hi hn]
  rcases part_cases 91 hi with ⟨before, br, hp, he, hb91⟩ | ⟨hp, h91⟩
  · rw [hp]
    simp only
    have h91 : 91 ∈ hi := by rw [he]; simp
    by_cases hbe : before = []
    · subst hbe
      simp only [List.nil_append] at he
      subst he
      simp only [List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ite_false]
      obtain ⟨h1, h2⟩ := part_take_drop 93 br
      generalize hP : part 93 br = P at h1 h2
      obtain ⟨hname, port⟩ := P
      simp only at h1 h2 ⊢
      rw [h2, h1]
      constructor
      · intro hok
        split at hok
        · cases hok
        · next hc =>
          refine ⟨fun hn => absurd List.mem_cons_self hn, fun _ => ⟨br, rfl, ?_, (checkBracketedHost_iff _ _).1 hok⟩⟩
          simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, bne_iff_ne, ne_eq,
            not_and, Decidable.not_not] at hc
          by_cases hz : (br.dropWhile (· != 93)).drop 1 = []
          · exact Or.inl hz
          · exact Or.inr (hc hz)
      · rintro ⟨_, hy⟩
        obtain ⟨y, hye, hz, hok⟩ := hy List.mem_cons_self
        simp only [List.cons.injEq, true_and] at hye
        subst hye
        rw [if_neg]
        · exact (checkBracketedHost_iff _ _).2 hok
        · simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, bne_iff_ne, ne_eq,
            not_and, Decidable.not_not]
          intro hne
          rcases hz with hz | hz
          · exact absurd hz hne
          · exact hz
    · have hbe' : before.isEmpty = false := by cases before <;> simp_all
      simp only [hbe', Bool.not_false, ite_true, reduceCtorEq, false_iff, not_and]
      intro _ hy
      obtain ⟨y, hye, _⟩ := hy h91
      exfalso
      rw [he] at hye
      cases before with
      | nil => exact hbe rfl
      | cons b r =>
        simp only [List.cons_append, List.cons.injEq] at hye
        exact hb91 (hye.1 ▸ List.mem_cons_self)
  · rw [hp]
    simp only
    rw [(part_take_drop 58 hi).1, checkBracketedHost_iff]
    constructor
    · intro hok; exact ⟨fun _ => hok, fun h => absurd h h91⟩
    · intro h; exact h.1 h91

/-- The errors `_check_bracketed_netloc` raises itself: data before the `[` and data between the
`]` and the port's `:`. -/
theorem checkBracketedNetloc_errors (ipk : Str → Option Bool) (n hi : Str) (hn : AfterAt n hi) :
    (∀ x y, hi = x ++ 91 :: y → 91 ∉ x → x ≠ [] →
      checkBracketedNetloc ipk n = .error (.valueError "Invalid IPv6 URL")) ∧
    (∀ h z, hi = 91 :: (h ++ 93 :: z) → 93 ∉ h → z ≠ [] → z.take 1 ≠ [58] →
      checkBracketedNetloc ipk n = .error (.valueError "Invalid IPv6 URL")) := by
  unfold checkBracketedNetloc
  simp only [afterAt_rpart n hi hn]
  constructor
  · intro x y he h91 hx
    subst he
    rw [part_prefix 91 x y h91]
    have : x.isEmpty = false := by cases x <;> simp_all
    simp [this]
  · intro h z he h93 hz hz58
    subst he
    rw [show (91 :: (h ++ 93 :: z)) = [] ++ 91 :: (h ++ 93 :: z) from rfl, part_prefix 91 [] _ (by simp)]
    have : z.isEmpty = false := by cases z <;> simp_all
    simp [part_prefix 93 h z h93, this, hz58]

/-- For every host `h` and every outcome of `ipaddress.ip_address(h)` (the oracle `ipk`):
`_check_bracketed_host` accepts `h` exactly when it is an IPvFuture literal per the regular
expression of :548 (when it starts with `v` or `V`) or an IPv6 address (otherwise), and raises the
`ValueError`s 'IPvFuture address is invalid' and 'An IPv4 address cannot be in brackets' and
`ip_address`'s own. For every netloc, `_check_bracketed_netloc` accepts it exactly when its part
after the last `@` is `BracketOk` (starts with `[` when it has one, only a `:` port after the
`]`, and an accepted host), and raises 'Invalid IPv6 URL' for data before the `[` and for data
between the `]` and the `:`. Source: the comments at :526-529 and :544-545 (RFC 3986 section
3.2.2: `IP-literal = "[" ( IPv6address / IPvFuture ) "]"`, `IPvFuture = "v" 1*HEXDIG "." 1*(...)`),
and the docs of `urlsplit` ("ValueError ... if the netloc contains invalid IPv6 or IPvFuture
brackets"). -/
def BracketSpec : Prop :=
  ∀ ipk : Str → Option Bool,
    (∀ h, checkBracketedHost ipk h = .ok () ↔ HostOk ipk h) ∧
    (∀ h, VStart h → ¬IPvFutureForm h →
      checkBracketedHost ipk h = .error (.valueError "IPvFuture address is invalid")) ∧
    (∀ h, ¬VStart h → ipk h = some true →
      checkBracketedHost ipk h = .error (.valueError "An IPv4 address cannot be in brackets")) ∧
    (∀ h, ¬VStart h → ipk h = none → (checkBracketedHost ipk h).raises "ValueError") ∧
    (∀ n hi, AfterAt n hi →
      (checkBracketedNetloc ipk n = .ok () ↔ BracketOk ipk hi) ∧
      (∀ x y, hi = x ++ 91 :: y → 91 ∉ x → x ≠ [] →
        checkBracketedNetloc ipk n = .error (.valueError "Invalid IPv6 URL")) ∧
      (∀ h z, hi = 91 :: (h ++ 93 :: z) → 93 ∉ h → z ≠ [] → z.take 1 ≠ [58] →
        checkBracketedNetloc ipk n = .error (.valueError "Invalid IPv6 URL")))

theorem bracketSpec_proven : BracketSpec := by
  intro ipk
  refine ⟨checkBracketedHost_iff ipk, ?_, ?_, ?_, ?_⟩
  · intro h hv hf
    have hv' : (h.take 1 == [118] || h.take 1 == [86]) = true := by
      rcases hv with e | e <;> simp [e]
    unfold checkBracketedHost
    rw [if_pos hv', if_neg (fun hok => hf ((ipvFutureOk_iff h).1 hok))]
  · intro h hv hk
    have hv' : (h.take 1 == [118] || h.take 1 == [86]) = false := by
      simp only [VStart, not_or] at hv
      simp [hv.1, hv.2]
    unfold checkBracketedHost
    rw [if_neg (by simp [hv']), hk]
  · intro h hv hk
    have hv' : (h.take 1 == [118] || h.take 1 == [86]) = false := by
      simp only [VStart, not_or] at hv
      simp [hv.1, hv.2]
    unfold checkBracketedHost
    rw [if_neg (by simp [hv']), hk]
    exact ⟨_, rfl, rfl⟩
  · intro n hi hn
    exact ⟨checkBracketedNetloc_iff ipk n hi hn, (checkBracketedNetloc_errors ipk n hi hn).1,
      (checkBracketedNetloc_errors ipk n hi hn).2⟩

/-! ## `_splitparams` -/

/-- For every path and both values of `missing_as_none`, `_splitparams` cuts at the first `;`
after the last `/` (when the path has a `/`): the parameters are what follows that `;`; without
such a `;` it returns the path and `None` (`missing_as_none=True`) or `''`. Without a `/`, it cuts
at the first `;`, and without either it returns `url[:-1], url` (`find` gives `-1`).
Source: the docs of `urlparse` ("parameters for last path element"), RFC 2396 section 3.3
(`path_segments = segment *( "/" segment )`, `segment = *pchar *( ";" param )`) and the body,
:492-499. -/
def SplitparamsSpec : Prop :=
  ∀ (url : Str) (mn : Bool),
    (∀ a b, url = a ++ 47 :: b → 47 ∉ b →
      (59 ∉ b → splitparamsMn url mn = (url, if mn then none else some [])) ∧
      (∀ c d, b = c ++ 59 :: d → 59 ∉ c → splitparamsMn url mn = (a ++ 47 :: c, some d))) ∧
    (47 ∉ url → ∀ c d, url = c ++ 59 :: d → 59 ∉ c → splitparamsMn url mn = (c, some d)) ∧
    (47 ∉ url → 59 ∉ url → splitparamsMn url mn = (url.dropLast, some url))

theorem findIdx_none_of (c : Nat) : ∀ (l : Str), c ∉ l → l.findIdx? (· == c) = none
  | [], _ => rfl
  | x :: r, h => by
    have hx : x ≠ c := fun e => h (e ▸ List.mem_cons_self)
    simp only [List.findIdx?_cons, beq_iff_eq, hx, Bool.false_eq_true, ite_false]
    rw [findIdx_none_of c r (fun m => h (List.mem_cons_of_mem _ m))]
    rfl

theorem splitparamsSpec_proven : SplitparamsSpec := by
  intro url mn
  refine ⟨?_, ?_, ?_⟩
  · intro a b hu h47
    have hc : url.contains 47 = true := by subst hu; simp
    have hr : rfindSlash url = a.length := by
      subst hu; simp [rfindSlash, rpart_of 47 a b h47]
    have hd : url.drop a.length = 47 :: b := by subst hu; simp
    refine ⟨?_, ?_⟩
    · intro h59
      unfold splitparamsMn
      rw [if_pos hc, hr, hd]
      have : (47 :: b).findIdx? (· == 59) = none := findIdx_none_of 59 _ (by simp [h59])
      rw [this]
    · intro c d hb h59
      unfold splitparamsMn
      rw [if_pos hc, hr, hd]
      have : (47 :: b).findIdx? (· == 59) = some (c.length + 1) := by
        rw [hb, show (47 :: (c ++ 59 :: d)) = (47 :: c) ++ 59 :: d from rfl,
          findIdx_prefix (47 :: c) d 59 (by simp [h59])]
        simp
      rw [this]
      subst hu; subst hb
      simp only [Prod.mk.injEq, Option.some.injEq]
      have e1 : a ++ 47 :: (c ++ 59 :: d) = (a ++ 47 :: c) ++ 59 :: d := by simp
      have e2 : a ++ 47 :: (c ++ 59 :: d) = (a ++ 47 :: c ++ [59]) ++ d := by simp
      have l1 : a.length + (c.length + 1) = (a ++ 47 :: c).length := by
        simp only [List.length_append, List.length_cons]
      have l2 : a.length + (c.length + 1) + 1 = (a ++ 47 :: c ++ [59]).length := by
        simp only [List.length_append, List.length_cons, List.length_nil]
      constructor
      · rw [l1, e1]; exact List.take_left' rfl
      · rw [l2, e2]; exact List.drop_left' rfl
  · intro h47 c d hu h59
    have hc : url.contains 47 = false := by simpa using h47
    unfold splitparamsMn
    rw [if_neg (by simp [h47])]
    subst hu
    rw [findIdx_prefix c d 59 h59]
    simp
  · intro h47 h59
    have hc : url.contains 47 = false := by simpa using h47
    unfold splitparamsMn
    rw [if_neg (by simp [h47]), findIdx_none_of 59 url h59]
    simp [List.dropLast_eq_take]

end PyLean.TextLibs.Url
