import PyLean.Bytecode.Ceval

/-!
Argument binding in `Python/ceval.c` (CPython 3.15.2): `initialize_locals` (lines 1738-1984), its
keyword loop (lines 1803-1903), the unexpected keyword error, `positional_only_passed_as_keyword`
(lines 1674-1735) and `too_many_positional` (lines 1616-1671), for every code object, function,
keyword list, runtime and object model. A keyword that is not an exact `str` (a `str` subclass
instance from a `**` mapping) is compared with `PyObject_RichCompareBool`, the `KwHooks.eq` of the
object model, which may run its `__eq__`, raise, or say true for other text.
-/

namespace PyLean.Bytecode

/-- **The slot a keyword names** (lines 1815-1835): an exact `str` is found by its text, with no
Python code run and nothing changed; any other keyword object goes through
`PyObject_RichCompareBool(keyword, varname, Py_EQ)` (line 1832) against
`co_varnames[co_posonlyargcount:total_args]` in order: an error is the result (`kw_fail`,
lines 1836-1838), the first true comparison is the slot, whatever the texts. -/
def FindKwSlotRules : Prop :=
  ∀ (hk : KwHooks) (co : Code) (rt : Rt),
    (∀ s, findKwSlot hk co (.str s) rt =
      .ok ((List.range' co.posonlyargcount (co.argcount + co.kwonlyargcount - co.posonlyargcount)).find?
        fun j => co.localsplusnames.getD j "" == s) rt) ∧
    (∀ k, (∀ s, k ≠ .str s) → findKwSlot hk co k rt =
      kwSlotSlow hk co k (List.range' co.posonlyargcount
        (co.argcount + co.kwonlyargcount - co.posonlyargcount)) rt) ∧
    (∀ k, kwSlotSlow hk co k [] rt = .ok none rt) ∧
    (∀ k j js,
      (∀ y rt', hk.eq k (.str (co.localsplusnames.getD j "")) rt = .error y rt' →
        kwSlotSlow hk co k (j :: js) rt = .error y rt') ∧
      (∀ rt', hk.eq k (.str (co.localsplusnames.getD j "")) rt = .ok true rt' →
        kwSlotSlow hk co k (j :: js) rt = .ok (some j) rt') ∧
      (∀ rt', hk.eq k (.str (co.localsplusnames.getD j "")) rt = .ok false rt' →
        kwSlotSlow hk co k (j :: js) rt = kwSlotSlow hk co k js rt'))

theorem findKwSlotRules_proven : FindKwSlotRules := by
  intro hk co rt
  refine ⟨fun s => rfl, fun k hk' => ?_, fun k => rfl, fun k j js => ⟨fun y rt' he => ?_,
    fun rt' he => ?_, fun rt' he => ?_⟩⟩
  · cases k <;> first | rfl | exact absurd rfl (hk' _)
  · simp only [kwSlotSlow, bind, EStateM.bind, he]
  · simp only [kwSlotSlow, bind, EStateM.bind, he, if_true, pure, EStateM.pure]
  · simp only [kwSlotSlow, bind, EStateM.bind, he, Bool.false_eq_true, if_false]

/-- **The keyword loop** (`initialize_locals`, lines 1803-1903), one keyword `k = v` at a time,
for every object model, code object, function, `**kwargs` dict, keyword list and runtime: a keyword
that is not a `str` is "Q() keywords must be strings"; otherwise its slot is looked up
(`findKwSlot`), whose error is the result; a slot already set is "Q() got multiple values for
argument '%S'" (`kw_found`, lines 1894-1901, `'%S'` being `PyObject_Str` of the keyword) and an
empty one takes `v`. A keyword naming no parameter goes into `**kwargs` when there is one
(`PyDict_SetItem` with the keyword object); with no `**kwargs`, `positional_only_passed_as_keyword`
runs first when there are positional-only parameters, and its error is the one raised; otherwise
the unexpected keyword error is. -/
def BindKeywordsRules : Prop :=
  ∀ (hk : KwHooks) (co : Code) (funcv : Val) (kwdict : Val) (kwnames : List Val) (k v : Val)
    (rest : List (Val × Val)) (fast : Array Val) (rt : Rt),
    (kwText rt k = none → ∀ func, getFunc funcv rt = .ok func rt → ∀ y rt',
      typeError (α := Unit) s!"{func.qualname}() keywords must be strings" rt = .error y rt' →
      bindKeywords hk co funcv kwdict kwnames ((k, v) :: rest) fast rt = .error y rt') ∧
    (∀ s, kwText rt k = some s →
      (∀ y rt', findKwSlot hk co k rt = .error y rt' →
        bindKeywords hk co funcv kwdict kwnames ((k, v) :: rest) fast rt = .error y rt') ∧
      (∀ j rt1, findKwSlot hk co k rt = .ok (some j) rt1 → fast.getD j .null ≠ .null →
        ∀ func, getFunc funcv rt1 = .ok func rt1 → ∀ y rt',
        (do let shown ← fmtKw hk k
            typeError (α := Unit) s!"{func.qualname}() got multiple values for argument '{shown}'") rt1
          = .error y rt' →
        bindKeywords hk co funcv kwdict kwnames ((k, v) :: rest) fast rt = .error y rt') ∧
      (∀ j rt1, findKwSlot hk co k rt = .ok (some j) rt1 → fast.getD j .null = .null →
        bindKeywords hk co funcv kwdict kwnames ((k, v) :: rest) fast rt =
          bindKeywords hk co funcv kwdict kwnames rest (fast.setIfInBounds j v) rt1) ∧
      (∀ rt1, findKwSlot hk co k rt = .ok none rt1 → kwdict = .null → co.posonlyargcount ≠ 0 →
        ∀ func, getFunc funcv rt1 = .ok func rt1 →
        ∀ y rt', posonlyPassedAsKeyword hk co kwnames func.qualname rt1 = .error y rt' →
        bindKeywords hk co funcv kwdict kwnames ((k, v) :: rest) fast rt = .error y rt') ∧
      (∀ rt1 rt2 func, findKwSlot hk co k rt = .ok none rt1 → kwdict = .null →
        getFunc funcv rt1 = .ok func rt1 →
        (co.posonlyargcount = 0 ∧ rt2 = rt1 ∨
          posonlyPassedAsKeyword hk co kwnames func.qualname rt1 = .ok () rt2) →
        ∀ func2, getFunc funcv rt2 = .ok func2 rt2 → ∀ y rt',
        unexpectedKeyword (α := Unit) hk co func2.qualname k rt2 = .error y rt' →
        bindKeywords hk co funcv kwdict kwnames ((k, v) :: rest) fast rt = .error y rt') ∧
      (∀ rt1, findKwSlot hk co k rt = .ok none rt1 → kwdict ≠ .null →
        bindKeywords hk co funcv kwdict kwnames ((k, v) :: rest) fast rt =
          (do (match k with
               | .str s => dictSetStr kwdict s v
               | k => hk.setItem kwdict k v)
              bindKeywords hk co funcv kwdict kwnames rest fast) rt1))

theorem bindKeywordsRules_proven : BindKeywordsRules := by
  intro hk co funcv kwdict kwnames k v rest fast rt
  refine ⟨fun hn func hg y rt' ht => ?_, fun s hs => ⟨fun y rt' he => ?_,
    fun j rt1 hf hset func hg y rt' ht => ?_, fun j rt1 hf hset => ?_,
    fun rt1 hf hd hp func hg y rt' hpe => ?_, fun rt1 rt2 func hf hd hg hp func2 hg2 y rt' hu => ?_,
    fun rt1 hf hd => ?_⟩⟩
  · simp only [bindKeywords, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, hn,
      Option.isNone_none, if_true, hg, ht]
  all_goals
    have hs' : (kwText rt k).isNone = false := by simp [hs]
    simp only [bindKeywords, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, hs',
      Bool.false_eq_true, if_false, pure, EStateM.pure]
  · simp only [he]
  · have hb : (fast.getD j .null != .null) = true := by simpa using hset
    simp only [hf, hb, if_true, EStateM.bind, hg]
    simp only [bind, EStateM.bind] at ht
    cases h2 : fmtKw hk k rt1 with
    | ok shown r2 => simp only [h2] at ht ⊢; simp only [ht]
    | error e2 r2 => simp only [h2] at ht ⊢; cases ht; rfl
  · have hb : (fast.getD j .null != .null) = false := by simpa using hset
    simp only [hf, hb, Bool.false_eq_true, if_false, EStateM.bind]
  · have hb : (co.posonlyargcount != 0) = true := by simpa using hp
    simp only [hf, hd, beq_self_eq_true, if_true, hb, EStateM.bind, hg, hpe]
  · rcases hp with ⟨hp, hr⟩ | hp
    · subst hr
      have hb : (co.posonlyargcount != 0) = false := by simpa using hp
      simp only [hf, hd, beq_self_eq_true, if_true, hb, Bool.false_eq_true, if_false, EStateM.bind,
        pure, EStateM.pure, hg2, hu]
    · by_cases hz : co.posonlyargcount = 0
      · have hb : (co.posonlyargcount != 0) = false := by simpa using hz
        simp only [posonlyPassedAsKeyword, posonlyConflicts, hz, List.range_zero, List.map_nil,
          bind, EStateM.bind, pure, EStateM.pure, List.isEmpty_nil, Bool.not_true,
          Bool.false_eq_true, if_false] at hp
        cases hp
        simp only [hf, hd, beq_self_eq_true, if_true, hb, Bool.false_eq_true, if_false, EStateM.bind,
          pure, EStateM.pure, hg2, hu]
      · have hb : (co.posonlyargcount != 0) = true := by simpa using hz
        simp only [hf, hd, beq_self_eq_true, if_true, hb, EStateM.bind, hg, hp, hg2, hu]
  · have hb : (kwdict == .null) = false := by simpa using hd
    simp only [hf, hb, Bool.false_eq_true, if_false, EStateM.bind]
    cases k <;> rfl

/-- **`positional_only_passed_as_keyword`** (lines 1674-1735), for every object model, code
object, keyword list and runtime: for each positional-only name in order and each keyword in
order, an exact `str` keyword counts when its text is the name (the pointer test of line 1688, or
`PyObject_RichCompareBool` of two exact `str`), and any other keyword object when
`PyObject_RichCompareBool(posonly_name, kwname, Py_EQ)` (line 1697, which runs a subclass's
reflected `__eq__`) is true, whose error is the result (`cmp < 0`, `goto fail`, lines 1704-1706);
the keywords counted are joined with `", "` (their `str` data, `PyUnicode_Join`) into
"Q() got some positional-only arguments passed as keyword arguments: 'A, B'", and with none it
returns 0. For a keyword list of exact `str` the counted keywords are the text matches, name by
name, with no Python code run. -/
def PosonlyKeywordRules : Prop :=
  ∀ (hk : KwHooks) (co : Code) (kwnames : List Val) (q : String) (rt : Rt),
    (∀ n s rest, posonlyHits hk n (.str s :: rest) rt =
      (do let tl ← posonlyHits hk n rest; pure (if s == n then Val.str s :: tl else tl)) rt) ∧
    (∀ n kw rest, (∀ s, kw ≠ .str s) → posonlyHits hk n (kw :: rest) rt =
      (do let hit ← hk.eq (.str n) kw
          let tl ← posonlyHits hk n rest
          pure (if hit then kw :: tl else tl)) rt) ∧
    (∀ y rt1, posonlyConflicts hk kwnames
        ((List.range co.posonlyargcount).map fun i => co.localsplusnames.getD i "") rt = .error y rt1 →
      posonlyPassedAsKeyword hk co kwnames q rt = .error y rt1) ∧
    (∀ rt1, posonlyConflicts hk kwnames
        ((List.range co.posonlyargcount).map fun i => co.localsplusnames.getD i "") rt = .ok [] rt1 →
      posonlyPassedAsKeyword hk co kwnames q rt = .ok () rt1) ∧
    (∀ cs rt1, cs ≠ [] → posonlyConflicts hk kwnames
        ((List.range co.posonlyargcount).map fun i => co.localsplusnames.getD i "") rt = .ok cs rt1 →
      posonlyPassedAsKeyword hk co kwnames q rt =
        typeError s!"{q}() got some positional-only arguments passed as keyword arguments: '{joinStrs ", " (cs.map fun c => (kwText rt1 c).getD "")}'" rt1) ∧
    (∀ names : List String, ∀ ss : List String, kwnames = ss.map Val.str →
      posonlyConflicts hk kwnames names rt =
        .ok (names.flatMap fun n => (ss.filter (· == n)).map Val.str) rt)

theorem posonlyHits_str (hk : KwHooks) (n : String) (ss : List String) (rt : Rt) :
    posonlyHits hk n (ss.map Val.str) rt = .ok ((ss.filter (· == n)).map Val.str) rt := by
  induction ss with
  | nil => rfl
  | cons s rest ih =>
    simp only [List.map_cons, posonlyHits, bind, EStateM.bind, pure, EStateM.pure, ih]
    by_cases h : s = n
    · subst h; simp
    · have : (s == n) = false := by simpa using h
      simp [this]

theorem posonlyConflicts_str (hk : KwHooks) (ss : List String) (rt : Rt) :
    ∀ names : List String, posonlyConflicts hk (ss.map Val.str) names rt =
      .ok (names.flatMap fun n => (ss.filter (· == n)).map Val.str) rt := by
  intro names
  induction names with
  | nil => rfl
  | cons n ns ih =>
    simp only [posonlyConflicts, bind, EStateM.bind, posonlyHits_str, ih, pure, EStateM.pure,
      List.flatMap_cons]

theorem posonlyKeywordRules_proven : PosonlyKeywordRules := by
  intro hk co kwnames q rt
  refine ⟨fun n s rest => rfl, fun n kw rest hkw => ?_, fun y rt1 h => ?_, fun rt1 h => ?_,
    fun cs rt1 hc h => ?_, fun names ss hk' => ?_⟩
  · cases kw <;> first | rfl | exact absurd rfl (hkw _)
  · simp only [posonlyPassedAsKeyword, bind, EStateM.bind, h]
  · simp only [posonlyPassedAsKeyword, bind, EStateM.bind, h, List.isEmpty_nil, Bool.not_true,
      Bool.false_eq_true, if_false, pure, EStateM.pure]
  · have he : cs.isEmpty = false := by cases cs with | nil => exact absurd rfl hc | cons _ _ => rfl
    simp only [posonlyPassedAsKeyword, bind, EStateM.bind, h, he, Bool.not_false, if_true, get,
      getThe, MonadStateOf.get, EStateM.get]
  · subst hk'; exact posonlyConflicts_str hk ss rt names


/-- One step of the candidate loop goes on with the suggestion it had or with this item, which is
not the name. -/
theorem suggestLoop_step (name item : String) (rest : List String) (sug : Option String) (sd : Nat) :
    ∃ X Y, (X = sug ∨ (X = some item ∧ item ≠ name)) ∧
      PyLean.TypeObj.suggestLoop name (item :: rest) sug sd = PyLean.TypeObj.suggestLoop name rest X Y := by
  conv => enter [1, X, 1, Y, 2, 1]; unfold PyLean.TypeObj.suggestLoop
  by_cases hne : item = name
  · simp only [hne, beq_self_eq_true, if_true]
    exact ⟨_, _, Or.inl rfl, rfl⟩
  · have hb : (item == name) = false := by simpa using hne
    simp only [hb, Bool.false_eq_true, if_false]
    repeat' split
    all_goals first | exact ⟨_, _, Or.inl rfl, rfl⟩ | exact ⟨_, _, Or.inr ⟨rfl, hne⟩, rfl⟩

/-- The candidate loop keeps an item of the list, never the name itself. -/
theorem suggestLoop_mem (name : String) :
    ∀ (dir : List String) (sug : Option String) (sd : Nat) (s : String),
      PyLean.TypeObj.suggestLoop name dir sug sd = some s → sug = some s ∨ (s ∈ dir ∧ s ≠ name)
  | [], sug, sd, s, h => by simp [PyLean.TypeObj.suggestLoop] at h; exact Or.inl h
  | item :: rest, sug, sd, s, h => by
    obtain ⟨X, Y, hX, he⟩ := suggestLoop_step name item rest sug sd
    rw [he] at h
    rcases suggestLoop_mem name rest X Y s h with h1 | ⟨h1, h2⟩
    · rcases hX with hX | ⟨hX, hn⟩
      · exact Or.inl (by rw [← hX]; exact h1)
      · rw [hX] at h1; cases h1; exact Or.inr ⟨List.mem_cons_self, hn⟩
    · exact Or.inr ⟨List.mem_cons_of_mem _ h1, h2⟩

/-- **The unexpected keyword error** (lines 1851-1876), for every object model, code object,
keyword and runtime: `"Q() got an unexpected keyword argument 'K'"`, with `". Did you mean 'S'?"`
exactly when `_Py_CalculateSuggestions` finds `S` among the names that may be passed by keyword
(only tried when there are any); a suggestion is always such a name, never a positional-only one
and never the keyword itself. For a keyword object that is not an exact `str`, the suggestion is
made from its `str` data and the keyword is shown by `PyObject_Str` (`'%S'`), whose error is the
result. -/
def UnexpectedKeywordRules : Prop :=
  ∀ (hk : KwHooks) (co : Code) (q k : String) (rt : Rt),
    (kwSuggestion co k = if co.argcount + co.kwonlyargcount > co.posonlyargcount then
      PyLean.TypeObj.calcSuggestion (possibleKeywords co) k else none) ∧
    (kwSuggestion co k = none → unexpectedKeyword (α := Unit) hk co q (.str k) rt =
      typeError s!"{q}() got an unexpected keyword argument '{k}'" rt) ∧
    (∀ s, kwSuggestion co k = some s → unexpectedKeyword (α := Unit) hk co q (.str k) rt =
      typeError s!"{q}() got an unexpected keyword argument '{k}'. Did you mean '{s}'?" rt) ∧
    (∀ s, kwSuggestion co k = some s → s ≠ k ∧ ∃ j, co.posonlyargcount ≤ j ∧ j < co.argcount + co.kwonlyargcount ∧
      co.localsplusnames.getD j "" = s) ∧
    (∀ kw : Val, (∀ s, kw ≠ .str s) → kwText rt kw = some k →
      (∀ y rt', hk.str kw rt = .error y rt' → unexpectedKeyword (α := Unit) hk co q kw rt = .error y rt') ∧
      (∀ shown rt', hk.str kw rt = .ok shown rt' →
        unexpectedKeyword (α := Unit) hk co q kw rt =
          (match kwSuggestion co k with
           | some sug => typeError s!"{q}() got an unexpected keyword argument '{shown}'. Did you mean '{sug}'?"
           | none => typeError s!"{q}() got an unexpected keyword argument '{shown}'") rt'))

theorem unexpectedKeywordRules_proven : UnexpectedKeywordRules := by
  intro hk co q k rt
  refine ⟨rfl, fun h => ?_, fun s h => ?_, fun s h => ?_, fun kw hkw ht => ⟨fun y rt' he => ?_,
    fun shown rt' he => ?_⟩⟩
  · simp only [unexpectedKeyword, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
      kwText, Option.getD_some, fmtKw, pure, EStateM.pure, h]
  · simp only [unexpectedKeyword, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
      kwText, Option.getD_some, fmtKw, pure, EStateM.pure, h]
  · simp only [kwSuggestion] at h
    split at h
    · simp only [PyLean.TypeObj.calcSuggestion] at h
      split at h
      · cases h
      · rcases suggestLoop_mem k _ none 0 s h with h1 | ⟨h1, h2⟩
        · cases h1
        · refine ⟨h2, ?_⟩
          simp only [possibleKeywords, List.mem_map, List.mem_range'_1] at h1
          obtain ⟨j, ⟨hj1, hj2⟩, hj⟩ := h1
          exact ⟨j, hj1, by omega, hj⟩
    · cases h
  · have hf : fmtKw hk kw = hk.str kw := by cases kw <;> first | rfl | exact absurd rfl (hkw _)
    simp only [unexpectedKeyword, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
      hf, he]
  · have hf : fmtKw hk kw = hk.str kw := by cases kw <;> first | rfl | exact absurd rfl (hkw _)
    simp only [unexpectedKeyword, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
      hf, he, ht, Option.getD_some]
    cases kwSuggestion co k <;> rfl

/-- **`too_many_positional`** (lines 1616-1671), for every code object, count, defaults tuple and
frame: the keyword-only arguments already given are counted over
`localsplus[co_argcount:co_argcount + co_kwonlyargcount]` (lines 1627-1632); with defaults the
signature is "from ATLEAST to N" with `atleast = co_argcount - defcount` a signed `Py_ssize_t` and
"arguments" plural, else "N" with the plural when `N != 1` (lines 1633-1642); with keyword-only
arguments given, " positional argument(s) (and K keyword-only argument(s))" follows the count
(lines 1645-1660); and the verb is "was" only for one positional and no keyword-only argument
(lines 1661-1668). -/
def TooManyPositionalMsg : Prop :=
  ∀ (co : Code) (gvn : Nat) (defaults : Val) (fast : Array Val) (q : String) (rt : Rt) (defs : Array Val),
    tupleItems defaults rt = .ok defs rt →
    ∀ K, K = ((List.range' co.argcount co.kwonlyargcount).filter fun i => fast.getD i .null != .null).length →
    tooManyPositional (α := Unit) co gvn defaults fast q rt =
      typeError s!"{q}() takes {if defs.size ≠ 0 then s!"from {(co.argcount : Int) - defs.size} to {co.argcount}" else s!"{co.argcount}"} positional argument{if defs.size ≠ 0 ∨ co.argcount ≠ 1 then "s" else ""} but {gvn}{if K ≠ 0 then s!" positional argument{if gvn ≠ 1 then "s" else ""} (and {K} keyword-only argument{if K ≠ 1 then "s" else ""})" else ""} {if gvn = 1 ∧ K = 0 then "was" else "were"} given" rt

theorem tooManyPositionalMsg_proven : TooManyPositionalMsg := by
  intro co gvn defaults fast q rt defs ht K hK
  subst hK
  simp only [tooManyPositional, bind, EStateM.bind, ht]
  by_cases hd : defs.size = 0 <;>
    by_cases hz : ((List.range' co.argcount co.kwonlyargcount).filter
      fun i => fast.getD i .null != .null).length = 0 <;>
    simp only [hd, hz, bne_iff_ne, ne_eq, not_true_eq_false, not_false_eq_true, decide_false,
      decide_true, if_true, if_false, ite_true, ite_false, true_or, false_or, Bool.false_eq_true,
      Bool.and_true, Bool.and_false, beq_iff_eq, and_true, and_false, Bool.true_and, decide_eq_true_eq,
      beq_self_eq_true, Bool.and_eq_true] <;>
    rfl

section Init
variable (hk : KwHooks) (co : Code) (func : FuncObj) (fast0 : Array Val) (args : List Val)
  (kwargs : List (Val × Val))

/-- The frame after the positional copy (lines 1763-1773): `localsplus[j] = args[j]` for
`j < n`, `n = min(argcount, co_argcount)`. -/
def posFill : Array Val :=
  (List.range (if args.length > co.argcount then co.argcount else args.length)).foldl
    (fun f j => f.setIfInBounds j (args.getD j .null)) fast0

end Init

/-- **`initialize_locals`** (lines 1738-1984), for every object model, code object, function,
frame, arguments and keywords. With no `*args` and no `**kwargs`: the positional arguments are
copied first (`posFill`), then the keyword loop runs on that frame and its error is the result
even when there are too many positional arguments (the count is checked only after it, lines
1905-1910); too many positional arguments is then `too_many_positional` on the frame the keywords
left; too few takes `m = co_argcount - defcount` as a signed `Py_ssize_t` (lines 1912-1940):
the missing ones below `m` are `missing_arguments`, else defaults `i` from `max(n - m, 0)` fill
the empty slots `m + i`; exactly `co_argcount` uses no default. With `*args`, the extra positional
arguments are packed into a tuple at `localsplus[total_args]` before the keyword loop (lines
1775-1794) and too many is no error. -/
def InitializeLocalsRules : Prop :=
  ∀ (hk : KwHooks) (co : Code) (funcv : Val) (fast0 : Array Val) (args : List Val)
    (kwargs : List (Val × Val)) (rt : Rt),
    flagSet co.flags coVarkeywords = false →
    (flagSet co.flags coVarargs = false →
      (∀ y rt', bindKeywords hk co funcv .null (kwargs.map (·.1)) kwargs (posFill co fast0 args) rt = .error y rt' →
        initializeLocals hk co funcv fast0 args kwargs rt = .error y rt') ∧
      (∀ fast1 rt1, bindKeywords hk co funcv .null (kwargs.map (·.1)) kwargs (posFill co fast0 args) rt = .ok fast1 rt1 →
        ∀ func, getFunc funcv rt1 = .ok func rt1 →
        (args.length > co.argcount → ∀ y rt',
          tooManyPositional (α := Unit) co args.length func.defaults fast1 func.qualname rt1 = .error y rt' →
          initializeLocals hk co funcv fast0 args kwargs rt = .error y rt') ∧
        (args.length = co.argcount → co.kwonlyargcount = 0 →
          initializeLocals hk co funcv fast0 args kwargs rt = .ok fast1 rt1) ∧
        (args.length < co.argcount → co.kwonlyargcount = 0 → ∀ defs, tupleItems func.defaults rt1 = .ok defs rt1 →
          let m : Int := (co.argcount : Int) - defs.size
          let missing := ((List.range' args.length (m.toNat - args.length)).filter
            fun i => fast1.getD i .null == .null).length
          (missing ≠ 0 → ∀ y rt',
            missingArguments (α := Unit) co (some defs.size) fast1 func.qualname rt1 = .error y rt' →
            initializeLocals hk co funcv fast0 args kwargs rt = .error y rt') ∧
          (missing = 0 →
            let i0 : Nat := if (args.length : Int) > m then ((args.length : Int) - m).toNat else 0
            initializeLocals hk co funcv fast0 args kwargs rt =
              .ok ((List.range' i0 (defs.size - i0)).foldl
                (fun f (i : Nat) => if f.getD (m + (i : Int)).toNat .null == .null
                  then f.setIfInBounds (m + (i : Int)).toNat (defs.getD i .null) else f) fast1) rt1)))) ∧
    (flagSet co.flags coVarargs = true → ∀ u rt0,
      mkTuple (args.drop (if args.length > co.argcount then co.argcount else args.length)) rt = .ok u rt0 →
      (∀ y rt', bindKeywords hk co funcv .null (kwargs.map (·.1)) kwargs
          ((posFill co fast0 args).setIfInBounds (co.argcount + co.kwonlyargcount) u) rt0 = .error y rt' →
        initializeLocals hk co funcv fast0 args kwargs rt = .error y rt') ∧
      (args.length ≥ co.argcount → co.kwonlyargcount = 0 → ∀ fast1 rt1,
        bindKeywords hk co funcv .null (kwargs.map (·.1)) kwargs
          ((posFill co fast0 args).setIfInBounds (co.argcount + co.kwonlyargcount) u) rt0 = .ok fast1 rt1 →
        ∀ func, getFunc funcv rt1 = .ok func rt1 →
        initializeLocals hk co funcv fast0 args kwargs rt = .ok fast1 rt1))

theorem initializeLocalsRules_proven : InitializeLocalsRules := by
  intro hk co funcv fast0 args kwargs rt hvk
  refine ⟨fun hva => ⟨?_, ?_⟩, fun hva u rt0 hu => ⟨?_, ?_⟩⟩
  · intro y rt' hb
    simp only [posFill] at hb
    simp only [initializeLocals, hvk, hva, Bool.false_eq_true, if_false, if_true,
      bind, EStateM.bind, pure, EStateM.pure, hb]
  · intro fast1 rt1 hb func hg
    simp only [posFill] at hb
    refine ⟨?_, ?_, ?_⟩
    · intro hgt y rt' ht
      have hc : (decide (args.length > co.argcount) && !false) = true := by simp [hgt]
      simp only [initializeLocals, hvk, hva, Bool.false_eq_true, if_false, if_true,
        bind, EStateM.bind, pure, EStateM.pure, hb, hg, hc, ht]
    · intro heq hk0
      have h1 : ¬ args.length > co.argcount := by omega
      have h2 : ¬ args.length < co.argcount := by omega
      have hk' : ¬ co.kwonlyargcount > 0 := by omega
      rw [if_neg h1] at hb
      simp only [initializeLocals, hvk, hva, Bool.false_eq_true, if_false, if_true, ite_false, ite_true,
        bind, EStateM.bind, pure, EStateM.pure, h1, decide_false, Bool.false_and, h2, hk', hb, hg]
    · intro hlt hk0 defs hdefs
      intro m missing
      have h1 : ¬ args.length > co.argcount := by omega
      rw [if_neg h1] at hb
      refine ⟨?_, ?_⟩
      · intro hm y rt' hma
        simp only [initializeLocals, hvk, hva, Bool.false_eq_true, if_false, if_true,
          bind, EStateM.bind, pure, EStateM.pure, hb, hg, h1, decide_false, Bool.false_and, hlt,
          decide_true, hdefs]
        have hm' : (missing != 0) = true := by simpa using hm
        simp only [missing, m] at hm'
        simp only [hm', if_true, EStateM.bind, hma]
      · intro hm i0
        simp only [initializeLocals, hvk, hva, Bool.false_eq_true, if_false, if_true,
          bind, EStateM.bind, pure, EStateM.pure, hb, hg, h1, decide_false, Bool.false_and, hlt,
          decide_true, hdefs]
        have hm' : (missing != 0) = false := by simpa using hm
        simp only [missing, m] at hm'
        have hk' : ¬ co.kwonlyargcount > 0 := by omega
        simp only [hm', Bool.false_eq_true, if_false, hk', decide_false, i0, m, EStateM.bind,
          EStateM.pure]
  · intro y rt' hb
    simp only [posFill] at hb
    simp only [initializeLocals, hvk, hva, Bool.false_eq_true, if_false, if_true,
      bind, EStateM.bind, pure, EStateM.pure, hu, hb]
  · intro hge hk0 fast1 rt1 hb func hg
    simp only [posFill] at hb
    have h2 : ¬ args.length < co.argcount := by omega
    have hk' : ¬ co.kwonlyargcount > 0 := by omega
    simp only [initializeLocals, hvk, hva, Bool.false_eq_true, if_false, if_true, ite_false, ite_true,
      bind, EStateM.bind, pure, EStateM.pure, hu, hb, hg, h2, decide_false, Bool.not_true, Bool.and_false,
      hk']

end PyLean.Bytecode
