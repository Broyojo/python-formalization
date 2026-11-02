import PyLean.TextLibs.EtreeDiff

/-!
Properties of the ElementPath model (`EtreePath.lean`).

ElementPath raises `SyntaxError` for paths it rejects ("invalid path", "invalid predicate",
"invalid descendant", "prefix ... not found in prefix map", ...). Three kinds of invalid path
escape that: a step whose token type is not in `ops` raises `KeyError`, an unterminated predicate
leaves `None` in the selector list, which `iterfind` then calls (`TypeError`), and a path with no
tokens makes `iterfind` return `None` instead of an iterator. Bug
`textlibs-etree-elementpath-errors`.

The C accelerator's fast path (`checkpath` false, no `namespaces`) agrees with ElementPath on
plain tag names (`plainTagTwins_proven`).
-/

namespace PyLean.TextLibs.Etree

open PyLean
open PyLean.UnicodeObj (isSpace)

/-! ## Invalid paths -/

/-- `iterfind` hands back an iterator or raises `SyntaxError`. -/
def iterOk : Py IterOut → Bool
  | .ok (.gen _) => true
  | .error (.named "SyntaxError" _) => true
  | _ => false

/-- No path makes `iterfind` raise `KeyError`: every token that can start a step is in `ops` or
is rejected with `SyntaxError`. -/
def ElementPathNoKeyError : Prop := ∀ (path : S) (ns : List (S × S)), iterOk (iterfindPath path ns) = true

/-- `e.findall(")")` raises `KeyError: ')'`. -/
theorem elementPathNoKeyError_refuted : ¬ ElementPathNoKeyError := by
  intro h
  have := h (lit ")") []
  revert this
  decide

/-- The same for the unterminated predicate `a[`: `prepare_predicate` returns `None`, which
`iterfind` calls. -/
def ElementPathNoNoneStep : Prop :=
  ∀ (path : S) (ns : List (S × S)), iterfindPath path ns ≠ .error (.typeError "'NoneType' object is not callable")

theorem elementPathNoNoneStep_refuted : ¬ ElementPathNoNoneStep := by
  intro h
  exact h (lit "a[") [] (by decide)

/-- `iterfind` returns an iterator for every path it does not reject (the docs: "Returns an
iterable yielding all matching elements in document order"). -/
def ElementPathIterable : Prop := ∀ (path : S) (ns : List (S × S)), iterfindPath path ns ≠ .ok .none

/-- `e.iterfind("")` returns `None`; `findall("")` then raises `TypeError` in the Python twin. -/
theorem elementPathIterable_refuted : ¬ ElementPathIterable := by
  intro h
  exact h [] [] (by decide)

/-! ## Plain tags: the C fast path against ElementPath -/

/-- A character a plain tag name may hold: a tag character of the tokenizer that is not one of
`.*:{}` or a quote. -/
def isPlainChar (x : Nat) : Bool := isTagChar x && !(lit ".*:{}'\"").contains x

/-- A nonempty name of plain characters (`a`, `item-2`, `é`). -/
def PlainTag (p : S) : Prop := p ≠ [] ∧ ∀ x ∈ p, isPlainChar x = true

theorem lt_of_contains (x : Nat) (l : List Nat) (h : l.contains x = true) (hs : ∀ y ∈ l, y < 128) : x < 128 :=
  hs x (List.mem_of_elem_eq_true h)

theorem plain_lt (x : Nat) (h : ¬ x < 128) : isOpChar x = false := by
  cases hop : isOpChar x
  · rfl
  · exact absurd (lt_of_contains x _ hop (by decide)) h

theorem op_small : ∀ x < 128, isOpChar x = true → isPlainChar x = false := by decide

theorem op_not_plain (x : Nat) (hx : isPlainChar x = true) : isOpChar x = false := by
  by_cases h : x < 128
  · cases hop : isOpChar x
    · rfl
    · rw [op_small x h hop] at hx; exact absurd hx (by decide)
  · exact plain_lt x h

theorem plain_ne (x : Nat) (hx : isPlainChar x = true) (c : Nat) (hc : isPlainChar c = false) : x ≠ c := by
  intro h; subst h; rw [hc] at hx; exact absurd hx (by decide)

theorem matchOp_plain (x : Nat) (rest : S) (hx : isPlainChar x = true) : matchOp (x :: rest) = none := by
  have h1 := plain_ne x hx (ch '\'') (by decide)
  have h2 := plain_ne x hx (ch '"') (by decide)
  have h3 := plain_ne x hx (ch ':') (by decide)
  have h4 := plain_ne x hx (ch '/') (by decide)
  have h5 := plain_ne x hx (ch '.') (by decide)
  have h6 := plain_ne x hx (ch '(') (by decide)
  have h7 := plain_ne x hx (ch '!') (by decide)
  have hop := op_not_plain x hx
  unfold matchOp
  cases rest <;> simp [h1, h2, h3, h4, h5, h6, h7, hop]

theorem tagChar_of_plain (x : Nat) (hx : isPlainChar x = true) : isTagChar x = true := by
  unfold isPlainChar at hx; simp only [Bool.and_eq_true] at hx; exact hx.1

theorem tagRun_plain (l : S) (h : ∀ x ∈ l, isPlainChar x = true) : tagRun l = (l, []) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    unfold tagRun
    rw [tagChar_of_plain x (h x (by simp)), ih (fun y hy => h y (by simp [hy]))]
    rfl

theorem tokenize_plain (p : S) (hp : PlainTag p) : tokenize p = [([], p)] := by
  obtain ⟨hne, hall⟩ := hp
  match p, hne with
  | x :: xs, _ =>
    have hx := hall x (by simp)
    unfold tokenize
    simp only [List.length_cons]
    unfold tokenizeF
    rw [matchOp_plain x xs hx]
    have hb : x ≠ ch '{' := plain_ne x hx (ch '{') (by decide)
    simp only [matchTag, hb, if_false, ite_false, tagRun_plain (x :: xs) hall]
    cases xs <;> rfl

theorem colon_not_mem (p : S) (hall : ∀ x ∈ p, isPlainChar x = true) : ch ':' ∉ p := by
  intro h; have := hall _ h; revert this; decide

theorem iterfind_plain (p : S) (hp : PlainTag p) : iterfindPath p [] = .ok (.gen [.child p]) := by
  obtain ⟨hne, hall⟩ := hp
  have hlast : p.getLast? ≠ some (ch '/') := by
    intro h
    have := hall _ (List.mem_of_getLast? h)
    revert this; decide
  have hhead : p.head? ≠ some (ch '/') := by
    intro h
    have := hall _ (List.mem_of_head? h)
    revert this; decide
  have hhead2 : p.head? ≠ some (ch '{') := by
    intro h
    have := hall _ (List.mem_of_head? h)
    revert this; decide
  have hwild : isWildcard p = false := by
    unfold isWildcard
    have h3 : (p.take 3 == lit "{*}") = false := by
      match p, hne with
      | x :: xs, _ =>
        have : x ≠ 123 := plain_ne x (hall x (by simp)) 123 (by decide)
        show ((x :: xs.take 2) == [123, 42, 125]) = false
        simp [this]
    have h2 : (p.length ≥ 2 && p.drop (p.length - 2) == lit "}*") = false := by
      by_cases hl : p.length ≥ 2
      · have hstar : ch '*' ∉ p := by intro h; have := hall _ h; revert this; decide
        simp only [hl, decide_true, Bool.true_and, beq_eq_false_iff_ne, ne_eq]
        intro h
        apply hstar
        have : ch '*' ∈ p.drop (p.length - 2) := by rw [h]; simp [lit, ch]
        exact List.mem_of_mem_drop this
      · simp [hl]
    rw [h3, h2]; rfl
  have hstrip : stripEmptyNs p = p := by
    match p, hne with
    | x :: xs, _ =>
      have : x ≠ 123 := plain_ne x (hall x (by simp)) 123 (by decide)
      have hb : ((x :: xs.take 1) == [123, 125]) = false := by simp [this]
      show (if ((x :: xs.take 1) == [123, 125]) = true then _ else _) = _
      rw [hb]; rfl
  unfold iterfindPath
  simp only [hlast, if_false, hhead]
  unfold xpathTokenizer
  rw [tokenize_plain p ⟨hne, hall⟩]
  simp only [nsToks, if_true]
  rw [if_pos ⟨hne, hhead2⟩, if_neg (colon_not_mem p hall)]
  simp only [Stream.cons, Stream.next, compileLoop, applyOp, if_true, prepareChild, hwild, hstrip]
  rfl

theorem checkScan_plain (l : S) (hall : ∀ x ∈ l, isPlainChar x = true) : checkScan true l = false := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hx := hall x (by simp)
    unfold checkScan
    have h1 : x ≠ ch '{' := plain_ne x hx _ (by decide)
    have h2 : x ≠ ch '}' := plain_ne x hx _ (by decide)
    have h3 : isPathChar x = false := by
      cases h : isPathChar x
      · rfl
      · exfalso
        have hs : x < 128 := lt_of_contains x _ h (by decide)
        have : ∀ y < 128, isPathChar y = true → isPlainChar y = false := by decide
        rw [this x hs h] at hx
        exact absurd hx (by decide)
    simp only [h1, h2, h3, if_false, Bool.and_false]
    exact ih (fun y hy => hall y (by simp [hy]))

theorem checkpath_plain (p : S) (hp : PlainTag p) : checkpath p = false := by
  obtain ⟨hne, hall⟩ := hp
  unfold checkpath
  match p, hne with
  | x :: rest, _ =>
    have h1 : x ≠ ch '{' := plain_ne x (hall x (by simp)) _ (by decide)
    match rest with
    | [] => exact checkScan_plain _ hall
    | [_] => exact checkScan_plain _ hall
    | _ :: _ :: _ => simp only [h1, false_and, if_false]; exact checkScan_plain _ hall

/-- For every tree and every plain tag name, `Element.findall`, `find` and `findtext` without
`namespaces` give the same result through the C fast path and through ElementPath (the
pure-Python twin). -/
def PlainTagTwins : Prop :=
  ∀ (root : Elem) (p : S) (dflt : Option S), PlainTag p →
    findallC root p none = findallPy root p [] ∧ findC root p none = findPy root p [] ∧
    findtextC root p dflt none = findtextPy root p dflt []

theorem find_head (l : List Elem) (p : S) : l.find? (·.tag == p) = (l.filter (·.tag == p)).head? := by
  induction l with
  | nil => rfl
  | cons e es ih =>
    cases h : (e.tag == p)
    · simp only [List.find?, List.filter, h]; exact ih
    · simp only [List.find?, List.filter, h, List.head?_cons]

theorem plainTagTwins_proven : PlainTagTwins := by
  intro root p dflt hp
  have hc := checkpath_plain p hp
  have hi := iterfind_plain p hp
  unfold findallC findC findtextC findallPy findPy findtextPy
  simp only [hc, Option.isSome_none, Bool.or_false, if_false, Bool.false_eq_true, hi, runSels, runSel,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, Option.map_some]
  refine ⟨?_, ?_, ?_⟩
  · first | rfl | trivial
  · rw [find_head]
    cases root.kids.filter (·.tag == p) <;> first | rfl | trivial
  · rw [find_head]
    cases root.kids.filter (·.tag == p) <;> first | rfl | trivial

end PyLean.TextLibs.Etree
