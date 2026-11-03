import PyLean.TextLibs.UrlSpecCoerce

/-!
`parse_qsl` and `urlencode` beyond their default options: the separator check, `None` input,
`max_num_fields`, `strict_parsing` and `keep_blank_values` field by field, and how fields
compose; `urlencode`'s refusal of non-sequences, `doseq`, `quote_via`, and `str()` of other objects.
-/

namespace PyLean.TextLibs.Url

open PyLean
open PyLean.UnicodeObj (ErrHandler)

set_option linter.unusedSimpArgs false

/-! ## `parse_qsl` -/

/-- A `separator` `parse_qsl` accepts: a non-empty `str` or `bytes` (:931). -/
def SepOk : Arg → Prop
  | .str s => s ≠ []
  | .bytes b false => b ≠ []
  | _ => False

/-- `unquote_plus(s, encoding=encoding, errors=errors)` as `parse_qsl` calls it on `str`. -/
def uqOf (o : QslOpts) (x : Str) : Py Str := unquotePlus (.str x) o.encoding o.errors

theorem splitOn_one_app (d : Nat) (b : Str) : ∀ a : Str,
    splitOn [d] (a ++ d :: b) = splitOn [d] a ++ splitOn [d] b
  | [] => by rw [List.nil_append, splitOn_one_hit, splitOn_nil]; rfl
  | c :: a => by
    by_cases hc : c = d
    · subst c
      rw [List.cons_append, splitOn_one_hit, splitOn_one_hit, splitOn_one_app d b a]
      rfl
    · rw [List.cons_append, splitOn_one_miss d c _ hc, splitOn_one_miss d c _ hc, splitOn_one_app d b a]
      have hne := splitOn_ne_nil [d] a
      generalize splitOn [d] a = l at hne ⊢
      cases l with
      | nil => exact absurd rfl hne
      | cons x t => rfl

theorem qslLoop_app (o : QslOpts) (unq : Str → Py Str) : ∀ (l1 l2 : List Str),
    qslLoop o unq (l1 ++ l2) = (do let x ← qslLoop o unq l1; let y ← qslLoop o unq l2; pure (x ++ y))
  | [], l2 => by
    show qslLoop o unq l2 = (pure [] >>= fun x => qslLoop o unq l2 >>= fun y => pure (x ++ y))
    rw [pure_bind]; simp
  | nv :: r, l2 => by
    simp only [List.cons_append, qslLoop]
    rw [qslLoop_app o unq r l2]
    by_cases h1 : (!List.isEmpty nv || o.strict) = true <;>
    by_cases h2 : ((part 61 nv).snd.isNone && o.strict) = true <;>
    by_cases h3 : (!List.isEmpty ((part 61 nv).snd.getD []) || o.keepBlank) = true <;>
    simp only [h1, h2, h3, ite_true, ite_false, Bool.false_eq_true, bind_assoc, pure_bind,
      List.append_assoc] <;> rfl

/-- The loop reads only `strict_parsing` and `keep_blank_values`. -/
theorem qslLoop_opts (o o' : QslOpts) (unq : Str → Py Str) (hs : o.strict = o'.strict)
    (hk : o.keepBlank = o'.keepBlank) : ∀ l, qslLoop o unq l = qslLoop o' unq l
  | [] => rfl
  | nv :: r => by
    simp only [qslLoop, hs, hk, qslLoop_opts o o' unq hs hk r]

/-- `parse_qsl` on a non-empty `str` with a `str` separator and no `max_num_fields`. -/
theorem parseQsl_str (q sd : Str) (o : QslOpts) (hq : q ≠ []) (hs : sd ≠ []) (ho : o.sep = .str sd)
    (hm : o.maxNum = none) :
    parseQsl (.str q) o = qslLoop o (uqOf o) (splitOn sd q) := by
  unfold parseQsl
  have hsep : (match o.sep with
      | .str s => !s.isEmpty
      | .bytes b false => !b.isEmpty
      | _ => false) = true := by
    rw [ho]; simp [List.isEmpty_iff, hs]
  have hqe : q.isEmpty = false := by cases q <;> simp_all
  have hse : sd.isEmpty = false := by cases sd <;> simp_all
  simp only [hsep, Bool.not_true, Bool.false_eq_true, ite_false, ho, bind, Except.bind, pure, Except.pure,
    hqe, hm, hse, Bool.not_false]
  rfl

/-- For every query string and every option of `parse_qsl`: a `separator` that is not a
non-empty `str` or `bytes` raises `ValueError('Separator must be of type string or bytes.')`;
`None` and `''` give `[]`; with `max_num_fields`, more fields than it (one more than the
separators) raise `ValueError('Max number of fields exceeded')`, and otherwise it changes
nothing. With a one-character separator, the fields of `a + sep + b` (both non-empty) are those of
`a` then those of `b`, `a`'s errors first; and one field (non-empty, without the separator) is,
when it has `=`, the unquoted name before the first `=` and value after it, dropped when the
value is empty and `keep_blank_values` is false; without `=` it raises `ValueError` under
`strict_parsing`, gives the unquoted field and `''` under `keep_blank_values`, and is dropped
otherwise. Names and values are unquoted by `unquote_plus` with `encoding` and `errors`.
Source: the docstring of `parse_qsl` (`keep_blank_values`: "blank values are to be ignored and
treated as if they were not included"; `strict_parsing`: "errors raise a ValueError exception";
`max_num_fields`: "throws a ValueError if there are more than n fields read"; `separator`), and
the docs ("Changed in version 3.10: ... separator ... only allow a single separator key"). -/
def QslSpec : Prop :=
  (∀ (qs : Arg) (o : QslOpts), ¬SepOk o.sep →
    parseQsl qs o = .error (.valueError "Separator must be of type string or bytes.")) ∧
  (∀ o : QslOpts, SepOk o.sep → parseQsl .none o = .ok [] ∧ (∀ s, o.sep = .str s → parseQsl (.str []) o = .ok [])) ∧
  (∀ (q sd : Str) (o : QslOpts) (m : Int), q ≠ [] → sd ≠ [] → o.sep = .str sd → o.maxNum = some m →
    (m < ((1 + countSub sd q : Nat) : Int) →
      parseQsl (.str q) o = .error (.valueError "Max number of fields exceeded")) ∧
    (¬ m < ((1 + countSub sd q : Nat) : Int) → parseQsl (.str q) o = parseQsl (.str q) { o with maxNum := none })) ∧
  (∀ (a b : Str) (d : Nat) (o : QslOpts), a ≠ [] → b ≠ [] → o.sep = .str [d] → o.maxNum = none →
    parseQsl (.str (a ++ d :: b)) o =
      (do let x ← parseQsl (.str a) o; let y ← parseQsl (.str b) o; pure (x ++ y))) ∧
  (∀ (f : Str) (d : Nat) (o : QslOpts), f ≠ [] → d ∉ f → o.sep = .str [d] → o.maxNum = none →
    (∀ n v, f = n ++ 61 :: v → 61 ∉ n →
      parseQsl (.str f) o = if v = [] ∧ o.keepBlank = false then .ok []
        else (do let x ← uqOf o n; let y ← uqOf o v; pure [(x, y)])) ∧
    (61 ∉ f → parseQsl (.str f) o =
      if o.strict = true then .error (.valueError "~bad query field")
      else if o.keepBlank = true then (do let x ← uqOf o f; let y ← uqOf o []; pure [(x, y)])
      else .ok []))

theorem qslSpec_proven : QslSpec := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro qs o hs
    obtain ⟨kb, st, en, er, mx, sp⟩ := o
    simp only at hs
    rcases sp with _ | s | ⟨b, _ | _⟩
    · rfl
    · have : s = [] := by simpa [SepOk] using hs
      subst this; rfl
    · have : b = [] := by simpa [SepOk] using hs
      subst this; rfl
    · rfl
  · intro o hs
    obtain ⟨kb, st, en, er, mx, sp⟩ := o
    simp only at hs
    rcases sp with _ | s | ⟨b, _ | _⟩
    · exact absurd hs (by simp [SepOk])
    · obtain ⟨c, s', rfl⟩ : ∃ c s', s = c :: s' := by
        cases s with
        | nil => exact absurd rfl hs
        | cons c s' => exact ⟨c, s', rfl⟩
      exact ⟨rfl, fun _ _ => rfl⟩
    · obtain ⟨c, s', rfl⟩ : ∃ c s', b = c :: s' := by
        cases b with
        | nil => exact absurd rfl hs
        | cons c s' => exact ⟨c, s', rfl⟩
      exact ⟨rfl, fun _ h => by cases h⟩
    · exact absurd hs (by simp [SepOk])
  · intro q sd o m hq hsd ho hm
    obtain ⟨kb, st, en, er, mx, sp⟩ := o
    simp only at ho hm
    subst ho hm
    have hqe : q.isEmpty = false := by cases q <;> simp_all
    have hse : sd.isEmpty = false := by cases sd <;> simp_all
    constructor
    · intro hlt
      simp only [parseQsl, hse, hqe, Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_false, bind,
        Except.bind, pure, Except.pure, hlt, ite_true]
      rfl
    · intro hge
      simp only [parseQsl, hse, hqe, Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_false, bind,
        Except.bind, pure, Except.pure, hge]
      apply qslLoop_opts <;> rfl
  · intro a b d o ha hb ho hm
    rw [parseQsl_str _ [d] o (by simp) (by simp) ho hm, parseQsl_str a [d] o ha (by simp) ho hm,
      parseQsl_str b [d] o hb (by simp) ho hm, splitOn_one_app d b a, qslLoop_app]
  · intro f d o hf hd ho hm
    rw [parseQsl_str f [d] o hf (by simp) ho hm, splitOn_one_none d f hd]
    have hfe : f.isEmpty = false := by cases f <;> simp_all
    refine ⟨?_, ?_⟩
    · intro n v he h61
      subst he
      simp only [qslLoop, hfe, Bool.not_false, Bool.true_or, ite_true, part_prefix 61 n v h61,
        Option.isNone_some, Bool.false_eq_true, Bool.false_and, ite_false, Option.getD_some, bind,
        Except.bind, pure, Except.pure, List.append_nil]
      by_cases hv : v = [] ∧ o.keepBlank = false
      · obtain ⟨rfl, hk⟩ := hv
        simp [hk]
      · rw [if_neg hv]
        have : (!v.isEmpty || o.keepBlank) = true := by
          simp only [not_and, Bool.not_eq_false] at hv
          cases v with
          | nil => simp [hv rfl]
          | cons _ _ => simp
        rw [if_pos this]
    · intro h61
      simp only [qslLoop, hfe, Bool.not_false, Bool.true_or, ite_true, part_absent 61 f h61,
        Option.isNone_none, Bool.true_and, Option.getD_none, List.isEmpty_nil, Bool.not_true, Bool.false_or,
        bind, Except.bind, pure, Except.pure]
      cases hs : o.strict
      · simp only [Bool.false_eq_true, ite_false]
        cases hk : o.keepBlank
        · rfl
        · simp only [ite_true, uqOf]
          cases unquotePlus (.str f) o.encoding o.errors with
          | error e => rfl
          | ok x =>
            simp only
            cases unquotePlus (.str []) o.encoding o.errors with
            | error e => rfl
            | ok y => rfl
      · rfl

/-! ## `urlencode` -/

/-- `quote_via`: `quote_plus` or `quote`. -/
def viaFn : QuoteVia → (Arg → Arg → Option Enc → Option ErrHandler → Py Str)
  | .plus => quotePlus
  | .plain => quote

/-- `doseq` on the pairs: a value with a length becomes one pair per element. -/
def expandSeq : List (List QV) → List (List QV)
  | [] => []
  | [k, .obj _ (some items)] :: r => items.map (fun e => [k, e]) ++ expandSeq r
  | kv :: r => kv :: expandSeq r

/-- One pair of `urlencode`'s loops, :1159-1199. -/
def encHere (o : EncOpts) (kv : List QV) : Py (List Str) := do
  let (k, v) ← match kv with
    | [k, v] => pure (k, v)
    | l => throw (unpackErr 2 l.length)
  let k ← quoteQV o k
  if !o.doseq then do
    let v ← quoteQV o v
    pure [k ++ [61] ++ v]
  else
    match v with
    | .obj _ (some items) => items.mapM (fun e => do
        let e ← quoteQV o e
        pure (k ++ [61] ++ e))
    | v => do
      let v ← quoteQV o v
      pure [k ++ [61] ++ v]

theorem encodeLoop_cons (o : EncOpts) (kv : List QV) (r : List (List QV)) :
    encodeLoop o (kv :: r) = (encHere o kv >>= fun h => encodeLoop o r >>= fun t => pure (h ++ t)) := by
  rcases kv with _ | ⟨k, _ | ⟨v, _ | ⟨w, z⟩⟩⟩
  · rfl
  · rfl
  · rcases v with s | b | ⟨t, _ | items⟩ <;> cases hd : o.doseq <;>
      simp only [encodeLoop, encHere, hd, bind_assoc, pure_bind, Bool.not_false, Bool.not_true, ite_true,
        ite_false, Bool.false_eq_true]
  · rfl

theorem encodeLoop_app (o : EncOpts) : ∀ (l1 l2 : List (List QV)),
    encodeLoop o (l1 ++ l2) = (do let x ← encodeLoop o l1; let y ← encodeLoop o l2; pure (x ++ y))
  | [], l2 => by
    show encodeLoop o l2 = (pure [] >>= fun x => encodeLoop o l2 >>= fun y => pure (x ++ y))
    rw [pure_bind]; simp
  | kv :: r, l2 => by
    rw [List.cons_append, encodeLoop_cons, encodeLoop_cons, encodeLoop_app o r l2]
    simp only [bind_assoc, pure_bind, List.append_assoc]

theorem quoteQV_doseq (o : EncOpts) (b : Bool) (v : QV) : quoteQV { o with doseq := b } v = quoteQV o v := by
  cases v <;> rfl

/-- The pairs, with a key `quote_via` accepts wherever the value is an empty sequence. -/
def KeysOk (o : EncOpts) : List (List QV) → Prop
  | [] => True
  | [k, .obj _ (some [])] :: r => (∃ y, quoteQV o k = .ok y) ∧ KeysOk o r
  | _ :: r => KeysOk o r

theorem items_eq (o : EncOpts) (k : QV) (k' : Str) (hk' : quoteQV o k = pure k') : ∀ items : List QV,
    items.mapM (fun e => do let e ← quoteQV o e; pure (k' ++ [61] ++ e)) =
      encodeLoop { o with doseq := false } (items.map (fun e => [k, e]))
  | [] => rfl
  | e :: t => by
    rw [List.mapM_cons, List.map_cons, encodeLoop_cons, ← items_eq o k k' hk' t]
    simp only [encHere, quoteQV_doseq, hk', pure_bind, bind_assoc, Bool.not_false, reduceIte,
      List.singleton_append]

theorem pyOk_pure {α : Type} (x : α) : (Except.ok x : Py α) = pure x := rfl

theorem encodeLoop_doseq (o : EncOpts) : ∀ l : List (List QV), KeysOk o l →
    encodeLoop { o with doseq := true } l = encodeLoop { o with doseq := false } (expandSeq l)
  | [], _ => rfl
  | [] :: r, _ => rfl
  | [_] :: r, _ => rfl
  | (_ :: _ :: _ :: _) :: r, _ => by simp only [expandSeq]; rfl
  | [k, .str s] :: r, hk => by
    have ih := encodeLoop_doseq o r hk
    simp only [expandSeq, encodeLoop_cons, encHere, quoteQV_doseq, ih, pure_bind, Bool.not_true,
      Bool.not_false, Bool.false_eq_true, reduceIte]
  | [k, .bytes b] :: r, hk => by
    have ih := encodeLoop_doseq o r hk
    simp only [expandSeq, encodeLoop_cons, encHere, quoteQV_doseq, ih, pure_bind, Bool.not_true,
      Bool.not_false, Bool.false_eq_true, reduceIte]
  | [k, .obj t none] :: r, hk => by
    have ih := encodeLoop_doseq o r hk
    simp only [expandSeq, encodeLoop_cons, encHere, quoteQV_doseq, ih, pure_bind, Bool.not_true,
      Bool.not_false, Bool.false_eq_true, reduceIte]
  | [k, .obj t (some items)] :: r, hk => by
    have hr : KeysOk o r := by cases items <;> first | exact hk.2 | exact hk
    have ih := encodeLoop_doseq o r hr
    simp only [expandSeq]
    rw [encodeLoop_app, encodeLoop_cons, ← ih]
    simp only [encHere, quoteQV_doseq, pure_bind, Bool.not_true, Bool.false_eq_true, reduceIte]
    rcases hq : quoteQV o k with x | k'
    · cases items with
      | nil => obtain ⟨y, hy⟩ := hk.1; rw [hq] at hy; cases hy
      | cons e t' =>
        rw [List.map_cons, encodeLoop_cons]
        simp only [encHere, quoteQV_doseq, hq, pure_bind]
        rfl
    · rw [pyOk_pure, pure_bind, items_eq o k k' (by rw [hq]; rfl) items]

theorem encodeLoop_pairs (o : EncOpts) (ho : o.doseq = false) : ∀ l : List (List QV), (∀ kv ∈ l, kv.length = 2) →
    encodeLoop o l = l.mapM (fun (kv : List QV) => (do
      let a ← quoteQV o (kv.getD 0 default)
      let b ← quoteQV o (kv.getD 1 default)
      pure (a ++ [61] ++ b) : Py Str))
  | [], _ => rfl
  | kv :: r, hl => by
    have ih := encodeLoop_pairs o ho r (fun x hx => hl x (List.mem_cons_of_mem _ hx))
    match kv, hl kv List.mem_cons_self with
    | [k, v], _ =>
      rw [encodeLoop_cons, ih, List.mapM_cons]
      simp only [encHere, ho, pure_bind, bind_assoc, Bool.not_false, reduceIte, List.getD_cons_zero,
        List.getD_cons_succ, List.singleton_append]

theorem urlencode_seq (elems : List (Bool × List QV)) (o : EncOpts) (h : ∀ e ∈ elems, e.1 = true) :
    urlencode (.seq elems) o = (encodeLoop o (elems.map Prod.snd) >>= fun l => pure (joinWith [38] l)) := by
  cases elems with
  | nil => rfl
  | cons e r =>
    obtain ⟨b, l⟩ := e
    have : b = true := h _ List.mem_cons_self
    subst this
    rfl

/-- For every query and every option of `urlencode`: an object without `len` and a sequence whose
first element is not a tuple raise `TypeError('not a valid non-string sequence or mapping
object')`; a mapping encodes as the sequence of its items. Each key and value goes through
`quote_via` (`quote_plus` or `quote`) with `safe`: a `bytes` one without `encoding` and
`errors`, a `str` one with them, and any other object as `str(v)`; without `doseq`, a sequence of
pairs gives `quote_via(k) + '=' + quote_via(v)` joined by `&`. With `doseq`, every value with a
length gives one pair per element: the result is that of the expanded pairs without `doseq`
(when a key's value is an empty sequence, that key is still quoted, so its error is raised).
Source: the docstring of `urlencode` ("If any values in the query arg are sequences and doseq is
true, each sequence element is converted to a separate parameter"; "The safe, encoding, and
errors parameters are passed down to the function specified by quote_via (encoding and errors
only if a component is a str)"). -/
def UrlencodeSpec : Prop :=
  (∀ o : EncOpts, urlencode .noLen o = .error (.typeError "not a valid non-string sequence or mapping object")) ∧
  (∀ (l : List QV) (r : List (Bool × List QV)) (o : EncOpts),
    urlencode (.seq ((false, l) :: r)) o = .error (.typeError "not a valid non-string sequence or mapping object")) ∧
  (∀ (items : List (QV × QV)) (o : EncOpts),
    urlencode (.mapping items) o = urlencode (.seq (items.map (fun p => (true, [p.1, p.2])))) o) ∧
  (∀ (o : EncOpts) (b : Str), quoteQV o (.bytes b) = viaFn o.via (.bytes b false) o.safe none none) ∧
  (∀ (o : EncOpts) (s : Str), quoteQV o (.str s) = viaFn o.via (.str s) o.safe o.encoding o.errors) ∧
  (∀ (o : EncOpts) (t : Str) (its : Option (List QV)), quoteQV o (.obj t its) = quoteQV o (.str t)) ∧
  (∀ (elems : List (Bool × List QV)) (o : EncOpts), o.doseq = false → (∀ e ∈ elems, e.1 = true ∧ e.2.length = 2) →
    urlencode (.seq elems) o = ((elems.map Prod.snd).mapM (fun (kv : List QV) => do
      let a ← quoteQV o (kv.getD 0 default)
      let b ← quoteQV o (kv.getD 1 default)
      pure (a ++ [61] ++ b)) >>= fun l => pure (joinWith [38] l))) ∧
  (∀ (elems : List (Bool × List QV)) (o : EncOpts), (∀ e ∈ elems, e.1 = true) → KeysOk o (elems.map Prod.snd) →
    urlencode (.seq elems) { o with doseq := true } =
      urlencode (.seq ((expandSeq (elems.map Prod.snd)).map (fun kv => (true, kv)))) { o with doseq := false }) ∧
  (∀ (k : QV) (t : Str) (r : List (Bool × List QV)) (o : EncOpts) (e : PyExc), quoteQV o k = .error e →
    urlencode (.seq ((true, [k, .obj t (some [])]) :: r)) { o with doseq := true } = .error e)

theorem urlencodeSpec_proven : UrlencodeSpec := by
  refine ⟨fun o => rfl, fun l r o => rfl, ?_, fun o b => ?_, fun o s => ?_, fun o t its => rfl, ?_, ?_, ?_⟩
  · intro items o
    unfold urlencode
    cases items with
    | nil => rfl
    | cons p r => simp [bind, Except.bind, pure, Except.pure, List.map_map, Function.comp_def]
  · cases h : o.via <;> simp [quoteQV, callVia, viaFn, h]
  · cases h : o.via <;> simp [quoteQV, callVia, viaFn, h, QV.text]
  · intro elems o ho h
    rw [urlencode_seq elems o (fun e he => (h e he).1),
      encodeLoop_pairs o ho _ (fun kv hkv => by
        simp only [List.mem_map] at hkv
        obtain ⟨e, he, rfl⟩ := hkv
        exact (h e he).2)]
  · intro elems o h hk
    rw [urlencode_seq elems _ h, urlencode_seq _ _ (by simp), encodeLoop_doseq o _ hk]
    simp [Function.comp_def]
  · intro k t r o e hq
    unfold urlencode
    simp [encodeLoop, quoteQV_doseq, hq, bind, Except.bind, pure, Except.pure]

end PyLean.TextLibs.Url
