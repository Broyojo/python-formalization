import PyLean.CoreLibs.Coll.UserString

/-!
Properties of `UserString`: agreement with `str` on `str` arguments, what each sibling does
with a `UserString` argument, what happens to `self.__class__`, and the remaining special
methods.
-/

set_option linter.unusedSimpArgs false

namespace PyLean.CoreLibs.Coll

open PyLean PyLean.StrSearch
open PyLean.RangeSlice (Slice)

/-- `Except.map` of a `<$>`. -/
theorem map_plain_us (u : US) (r : Py Seq) :
    (URes.us <$> wrapIn u r).map URes.plain = URes.str <$> r := by
  cases r <;> rfl

/-- `UserString` simulates `str`. For every call in the table (all the search, split, strip,
pad, case, predicate, `%`, `format`, `join`, comparison, subscript and conversion methods), with
`str` arguments, the result of the `UserString` method is the result of the `str` method,
exception included, once a `UserString` result is read as its `data`. Doc/library/collections.rst:
"Class that simulates a string object." The argument condition is the type invariant
of the `str` side: the case of a `UserString` argument is `UserStringUnwrapSiblings`. -/
def UserStringSimulatesStr : Prop :=
  ∀ (ops : UniOps) (c : SCall) (u : US), c.allStr = true →
    (usCall ops c u).map URes.plain = strCall ops c u.data

theorem unwrap_str {a : SArg} (h : a.isStr = true) : unwrap a = a := by
  cases a <;> simp_all [SArg.isStr, unwrap]

theorem userStringSimulatesStr_proven : UserStringSimulatesStr := by
  intro ops c u h
  cases c with
  | case f => rfl
  | pred f => rfl
  | center w fill => exact map_plain_us u _
  | ljust w fill => exact map_plain_us u _
  | rjust w fill => exact map_plain_us u _
  | zfill w => exact map_plain_us u _
  | expandtabs t => exact map_plain_us u _
  | count a st en =>
    simp only [usCall, strCall, usCount, unwrap_str (a := a) h]
    cases strCountA u.data a st en <;> rfl
  | find a st en fwd =>
    simp only [usCall, strCall, usFind, unwrap_str (a := a) h]
    cases strFindA u.data a st en fwd <;> rfl
  | index a st en fwd =>
    simp only [usCall, strCall, usIndex, unwrap_str (a := a) h]
    cases strIndexA u.data a st en fwd <;> rfl
  | startswith a st en =>
    simp only [usCall, strCall, usStartswith]
    cases strStartswithA u.data a st en <;> rfl
  | endswith a st en =>
    simp only [usCall, strCall, usEndswith]
    cases strEndswithA u.data a st en <;> rfl
  | removeprefix a =>
    simp only [usCall, strCall, usRemoveprefix, unwrap_str (a := a) h]
    exact map_plain_us u _
  | removesuffix a =>
    simp only [usCall, strCall, usRemovesuffix, unwrap_str (a := a) h]
    exact map_plain_us u _
  | partition a =>
    simp only [usCall, strCall, usPartition]
    cases strPartitionA u.data a <;> rfl
  | rpartition a =>
    simp only [usCall, strCall, usRPartition]
    cases strRPartitionA u.data a <;> rfl
  | replace o n c =>
    have ho : o.isStr = true := by simp_all [SCall.allStr]
    have hn : n.isStr = true := by simp_all [SCall.allStr]
    simp only [usCall, strCall, usReplace, unwrap_str ho, unwrap_str hn]
    exact map_plain_us u _
  | split sep m =>
    simp only [usCall, strCall, usSplit]
    cases strSplitA u.data sep m <;> rfl
  | rsplit sep m =>
    simp only [usCall, strCall, usRSplit]
    cases strRSplitA u.data sep m <;> rfl
  | splitlines keep => rfl
  | strip chars t => exact map_plain_us u _
  | join items =>
    simp only [usCall, strCall, usJoin]
    cases strJoin u.data items <;> rfl
  | contains a =>
    simp only [usCall, strCall, usContains, unwrap_str (a := a) h]
    cases strContains u.data a <;> rfl
  | rich op a =>
    simp only [usCall, strCall, usRich, unwrap_str (a := a) h]
    cases strRich op u.data a <;> rfl
  | mul n => exact map_plain_us u _
  | getitem i => exact map_plain_us u _
  | getslice s => exact map_plain_us u _
  | format args =>
    simp only [usCall, strCall, usFormat]
    cases ops.format u.data args <;> rfl
  | formatMap m =>
    simp only [usCall, strCall, usFormatMap]
    cases ops.formatMap u.data m <;> rfl
  | mod args => exact map_plain_us u _
  | translate t => exact map_plain_us u _
  | encode enc err =>
    simp only [usCall, strCall, usEncode, Option.getD_some]
    cases ops.encode u.data enc err <;> rfl
  | len => rfl
  | hash => rfl
  | repr => rfl
  | toInt =>
    simp only [usCall, strCall]
    cases ops.toInt u.data <;> rfl
  | toFloat =>
    simp only [usCall, strCall]
    cases ops.toFloat u.data <;> rfl
  | toComplex =>
    simp only [usCall, strCall]
    cases ops.toComplex u.data <;> rfl

/-- The sibling test: passing a `UserString` wherever a `str` is accepted gives the same
result as passing the `str`. `count`, `find`, `index`, `rfind`, `rindex`, `replace`,
`removeprefix`, `removesuffix`, `__contains__`, `__eq__`, `__lt__`, ... all unwrap their argument
and pass. `startswith`, `endswith` (fixed on main by gh-159868), `partition`, `rpartition`, `split`,
`rsplit`, `strip`, `lstrip`, `rstrip`, `center`, `ljust`, `rjust` and `join` do not. -/
def UserStringUnwrapSiblings : Prop :=
  ∀ (ops : UniOps) (c : SCall) (u : US), c.allStr = true → usCall ops c.wrap u = usCall ops c u

/-- Any `UniOps`, for refutations that do not touch it. -/
def trivialOps : UniOps where
  case _ s := s
  pred _ _ := false
  encode s _ _ := .ok s
  format s _ := .ok s
  formatMap s _ := .ok s
  mod s _ := .ok s
  modUser s _ := .ok s
  translate s _ := .ok s
  hash _ := 0
  repr _ := ""
  toInt _ := .ok 0
  toFloat _ := .ok ""
  toComplex _ := .ok ""

theorem userStringUnwrapSiblings_refuted : ¬ UserStringUnwrapSiblings := by
  intro h
  have := h trivialOps (.partition (.str [97])) ⟨"UserString", [97]⟩ rfl
  simp [usCall, SCall.wrap, usPartition, strPartitionA, needStr, SArg.wrap, SArg.ty, Functor.map,
    Except.map, bind, Except.bind] at this
  have h2 : strPartition [97] [97] = .ok ([], [97], []) := by decide
  simp [h2] at this

/-- The calls whose method body unwraps. -/
def SCall.unwraps : SCall → Bool
  | .count .. | .find .. | .index .. | .removeprefix _ | .removesuffix _ | .replace ..
  | .contains _ | .rich .. => true
  | _ => false

/-- The narrowed statement: for the methods that have the `isinstance` test, a `UserString`
argument is the same as its `str`, exception included. -/
def UserStringUnwrapNarrow : Prop :=
  ∀ (ops : UniOps) (c : SCall) (u : US), c.unwraps = true → c.allStr = true →
    usCall ops c.wrap u = usCall ops c u

theorem unwrap_wrap (a : SArg) : unwrap a.wrap = unwrap a := by
  cases a <;> rfl

theorem userStringUnwrapNarrow_proven : UserStringUnwrapNarrow := by
  intro ops c u h _
  cases c <;> simp [SCall.unwraps] at h <;>
    simp [SCall.wrap, usCall, usCount, usFind, usIndex, usRemoveprefix, usRemovesuffix, usReplace,
      usContains, usRich, unwrap_wrap]

/-- `self.__class__` survives exactly the listed methods, in particular in subclasses:
case mapping, padding, `strip`, `replace`, `removeprefix`, `*`, `%`, subscripts, `translate`
return a `UserString` of the receiver's class, and `format`, `format_map`, `join`,
`partition`, `split` and the predicates and searches return the plain type `str` gives
(the open question of python/cpython#76022, recorded here as behaviour). -/
def UserStringResultClass : Prop :=
  ∀ (ops : UniOps) (c : SCall) (u : US) (r : URes), usCall ops c u = .ok r →
    (c.keepsClass = true → ∃ d, r = .us ⟨u.cls, d⟩) ∧
    (c.keepsClass = false → ∀ v, r ≠ .us v)

theorem map_ok_us {r : Py US} {x : URes} (h : URes.us <$> r = .ok x) (u : US)
    (hc : ∀ v, r = .ok v → v.cls = u.cls) : ∃ d, x = .us ⟨u.cls, d⟩ := by
  cases hr : r with
  | error e => simp [hr, Functor.map, Except.map] at h
  | ok v =>
    simp only [hr, Functor.map, Except.map, Except.ok.injEq] at h
    have := hc v hr
    subst h
    exact ⟨v.data, by cases v; simp_all⟩

theorem wrapIn_cls {u : US} {r : Py Seq} {v : US} (h : wrapIn u r = .ok v) : v.cls = u.cls := by
  cases r with
  | error e => simp [wrapIn, Except.map] at h
  | ok d =>
    simp only [wrapIn, Except.map, Except.ok.injEq] at h
    rw [← h]

theorem map_ok_notUs {β : Type} {f : β → URes} (hf : ∀ b v, f b ≠ .us v) {r : Py β} {x : URes}
    (h : f <$> r = .ok x) (v : US) : x ≠ .us v := by
  cases r with
  | error e => simp [Functor.map, Except.map] at h
  | ok b =>
    simp only [Functor.map, Except.map, Except.ok.injEq] at h
    rw [← h]
    exact hf b v

theorem userStringResultClass_proven : UserStringResultClass := by
  intro ops c u r h
  constructor
  · intro hk
    cases c <;> simp [SCall.keepsClass] at hk
    case case f =>
      simp only [usCall, Except.ok.injEq] at h
      exact ⟨_, h.symm⟩
    all_goals
      exact map_ok_us h u (fun v hv => wrapIn_cls hv)
  · intro hk v
    cases c <;> simp [SCall.keepsClass] at hk <;> simp only [usCall] at h
    all_goals
      first
      | (simp only [Except.ok.injEq] at h; rw [← h]; simp)
      | exact map_ok_notUs (by intro b w; simp) h v

/-- `str.replace` has accepted `count` as a keyword since 3.13 (Doc/library/stdtypes.rst, "Changed in
version 3.13: count is now supported as a keyword argument."), so a program written for `str`
expects `u.replace(old, new, count=n)` to work on a `UserString`. The parameter there
is named `maxsplit` (:1558), and the call raises `TypeError`. -/
def UserStringReplaceCountKeyword : Prop :=
  ∀ (u : US) (o n : Seq) (c : Int),
    (usReplaceKw u (.str o) (.str n) "count" c).map (·.data) = strReplaceKw u.data (.str o) (.str n) "count" c

theorem userStringReplaceCountKeyword_refuted : ¬ UserStringReplaceCountKeyword := by
  intro h
  have := h ⟨"UserString", []⟩ [] [] 0
  simp [usReplaceKw, strReplaceKw, strReplaceA, needArg, bind, Except.bind, Except.map] at this
  have h2 : strReplace [] [] [] 0 = .ok [] := by decide
  simp [h2] at this

/-- `format(s, spec)` on a `str` applies the format mini-language; `format(u, spec)`, and so
`f"{u:>5}"`, should do the same on a class that simulates `str`. It raises `TypeError`, as
`UserString` has no `__format__`. Stated for the spec `">w"`, whose `str` meaning is `rjust`. -/
def UserStringFormatSpec : Prop :=
  ∀ (u : US) (w : Nat), usDunderFormat u (">" ++ toString w) = strRjust u.data w

theorem userStringFormatSpec_refuted : ¬ UserStringFormatSpec := by
  intro h
  have := h ⟨"UserString", []⟩ 0
  have h2 : strRjust [] 0 = .ok [] := by decide
  have h3 : (">" ++ toString 0 : String).isEmpty = false := by decide
  simp [usDunderFormat, h2, h3] at this

/-! ### Comparison and hash -/

theorem seqCmp_self (s : Seq) : seqCmp s s = .eq := by
  induction s with
  | nil => rfl
  | cons a t ih => simp [seqCmp, ih]

theorem seqCmp_eq_iff (s t : Seq) : seqCmp s t = .eq ↔ s = t := by
  induction s generalizing t with
  | nil => cases t <;> simp [seqCmp]
  | cons a s ih =>
    cases t with
    | nil => simp [seqCmp]
    | cons b t =>
      simp only [seqCmp, List.cons.injEq]
      by_cases h1 : a < b
      · have : a ≠ b := by omega
        simp [h1, this]
      · by_cases h2 : a > b
        · have : a ≠ b := by omega
          simp [h1, h2, this]
        · have : a = b := by omega
          simp [h1, h2, this, ih]

theorem seqCmp_swap (s t : Seq) : seqCmp t s = (seqCmp s t).swap := by
  induction s generalizing t with
  | nil => cases t <;> rfl
  | cons a s ih =>
    cases t with
    | nil => rfl
    | cons b t =>
      simp only [seqCmp]
      by_cases h1 : a < b
      · have h2 : ¬ b < a := by omega
        simp [h1, h2, Ordering.swap]
      · by_cases h2 : b < a
        · simp [h1, h2, Ordering.swap]
        · simp [h1, h2, ih]

/-- Rich comparison of a `UserString` with a `UserString` or a `str` is the total order of `str`:
exactly one of `<`, `==`, `>` holds, `<=` and `>=` are the weak forms, and `==` is equality
of contents, so equal objects have equal hashes (`__hash__`, :1388-1389, the invariant every hash
table relies on, across `UserString` and `str`). -/
def UserStringOrderHash : Prop :=
  ∀ (ops : UniOps) (u : US) (t : Seq) (a : SArg), (a = .str t ∨ a = .user t) →
    ∃ lt eq gt, usRich .lt u a = .ok lt ∧ usRich .eq u a = .ok eq ∧ usRich .gt u a = .ok gt ∧
      ((lt && eq) = false ∧ (lt && gt) = false ∧ (eq && gt) = false ∧ (lt || eq || gt) = true) ∧
      usRich .le u a = .ok (lt || eq) ∧ usRich .ge u a = .ok (gt || eq) ∧
      (eq = true ↔ u.data = t) ∧ (eq = true → ops.hash u.data = ops.hash t)

theorem userStringOrderHash_proven : UserStringOrderHash := by
  intro ops u t a ha
  have hun : unwrap a = .str t := by rcases ha with h | h <;> subst h <;> rfl
  have hE := seqCmp_eq_iff u.data t
  refine ⟨SOp.test .lt (seqCmp u.data t), SOp.test .eq (seqCmp u.data t), SOp.test .gt (seqCmp u.data t),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [usRich, hun, strRich]
  · simp [usRich, hun, strRich]
  · simp [usRich, hun, strRich]
  · cases seqCmp u.data t <;> simp [SOp.test]
  · simp only [usRich, hun, strRich]
    cases seqCmp u.data t <;> rfl
  · simp only [usRich, hun, strRich]
    cases seqCmp u.data t <;> rfl
  · rw [← hE]
    cases seqCmp u.data t <;> simp [SOp.test]
  · intro h
    have : u.data = t := hE.mp (by revert h; cases seqCmp u.data t <;> simp [SOp.test])
    rw [this]

/-! ### Construction and arithmetic -/

/-- `UserString(x)` holds `x`, `UserString(u)` holds the same text, anything else holds `str(x)`
(`__init__`, :1365-1371); `__getnewargs__`, `__str__` return the data, so
a pickle or `copy` round trip gives the same object; `int(u)`, `float(u)`, `complex(u)` are the
conversions of the data. Concatenation adds lengths and keeps the class, and takes the same
`str(other)` on both sides (:1430-1440). `__rmod__` formats `str(template)` with the object and keeps
the class (:1450-1451), and `encode(None, None)` means the defaults (:1478-1481). -/
def UserStringConstructAdd : Prop :=
  ∀ (ops : UniOps) (u : US) (cls : String) (a : SArg) (t : Seq),
    usNew cls (.str u.data) = ⟨cls, u.data⟩ ∧
    usNew cls (.user u.data) = ⟨cls, u.data⟩ ∧
    usNew u.cls (.str (usGetnewargs u)) = u ∧
    usNew u.cls (.str (usStr u)) = u ∧
    usRmod ops u t = (ops.modUser t u.data).map (fun d => ⟨u.cls, d⟩) ∧
    usEncode ops u none none = ops.encode u.data "utf-8" "strict" ∧
    ((usAdd u a).data = u.data ++ (usNew cls a).data) ∧
    ((usRadd u a).data = (usNew cls a).data ++ u.data) ∧
    (usAdd u a).cls = u.cls ∧ (usRadd u a).cls = u.cls ∧
    usCall ops .toInt u = URes.int <$> ops.toInt u.data ∧
    usCall ops .toFloat u = URes.text <$> ops.toFloat u.data ∧
    usCall ops .toComplex u = URes.text <$> ops.toComplex u.data

theorem userStringConstructAdd_proven : UserStringConstructAdd := by
  intro ops u cls a t
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩ <;> cases a <;> rfl

theorem sum_rep (m k : Nat) : (List.replicate m k).sum = m * k := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [List.replicate_succ, List.sum_cons, ih, Nat.succ_mul]
    omega

/-- `str * n` on a `UserString`: `u * n` (and `n * u`, the same function) has length `n * len(u)`
for `n >= 0` in range when that fits, and `u * n` is empty for `n <= 0` of `Py_ssize_t` size. -/
def UserStringMul : Prop :=
  ∀ (u : US) (n : Int), ssizeMin ≤ n → n ≤ ssizeMax →
    (n ≤ 0 → usMul u n = .ok ⟨u.cls, []⟩) ∧
    (0 < n → n * u.data.length ≤ ssizeMax →
      ∃ v, usMul u n = .ok v ∧ v.cls = u.cls ∧ (v.data.length : Int) = n * u.data.length)

theorem userStringMul_proven : UserStringMul := by
  intro u n h1 h2
  have hr : ¬ (n < ssizeMin ∨ n > ssizeMax) := by omega
  constructor
  · intro hn
    simp [usMul, wrapIn, strRepeat, hr, hn, bind, Except.bind, pure, Except.pure, Except.map]
  · intro hn hfit
    have hn0 : ¬ n ≤ 0 := by omega
    by_cases he : u.data.length = 0
    · refine ⟨⟨u.cls, []⟩, ?_, rfl, ?_⟩
      · simp [usMul, wrapIn, strRepeat, hr, hn0, he, bind, Except.bind, pure, Except.pure, Except.map]
      · simp [he]
    · have hf : ¬ n * u.data.length > ssizeMax := by omega
      refine ⟨⟨u.cls, (List.replicate n.toNat u.data).flatten⟩, ?_, rfl, ?_⟩
      · simp [usMul, wrapIn, strRepeat, hr, hn0, he, hf, bind, Except.bind, pure, Except.pure, Except.map]
      · simp only [List.length_flatten, List.map_replicate]
        rw [sum_rep, Int.natCast_mul]
        have : ((n.toNat : Nat) : Int) = n := by omega
        rw [this]

end PyLean.CoreLibs.Coll
