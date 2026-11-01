import PyLean.CoreLibs.CollAbc.Builtins

/-!
`Sequence` and `MutableSequence` mixins against `list`, over an abstract element type with
abstract identity and `__eq__`, which may raise.
-/

namespace PyLean.CoreLibs.CollAbc

open PyLean

theorem listGet_nat {α : Type} (xs : List α) (k : Nat) :
    listGet xs k = match xs[k]? with
      | some v => .ok v
      | none => .error (.indexError "list index out of range") := by
  have h0 : ¬ ((k : Int) < 0) := by omega
  simp only [listGet, h0, ite_false, false_or]
  by_cases h : k < xs.length
  · have h1 : ¬ ((k : Int) ≥ (xs.length : Int)) := by omega
    simp only [h1, ite_false, Int.toNat_natCast]
    rfl
  · have h1 : (k : Int) ≥ (xs.length : Int) := by omega
    have h2 : xs[k]? = none := by simp; omega
    simp only [h1, ite_true, h2]

theorem drop_step {α : Type} (xs : List α) (k : Nat) :
    match xs[k]? with
    | none => xs.drop k = []
    | some v => xs.drop k = v :: xs.drop (k + 1) := by
  by_cases h : k < xs.length
  · have : xs[k]? = some xs[k] := by simp [h]
    rw [this]
    exact List.drop_eq_getElem_cons h
  · have : xs[k]? = none := by simp; omega
    rw [this]
    simp; omega

theorem iterFrom_list {α : Type} (xs : List α) : ∀ (fuel k : Nat), 0 < fuel →
    xs.length < k + fuel → (listSeq xs).iterFrom fuel (k : Int) = .ok (xs.drop k)
  | 0, k, h0, h => absurd h0 (by omega)
  | fuel + 1, k, _, h => by
    have hd := drop_step xs k
    simp only [Seq.iterFrom, listSeq, listGet_nat]
    cases hk : xs[k]? with
    | none =>
      simp only [hk] at hd
      simp [isIndexError, hd]
    | some v =>
      simp only [hk] at hd
      have hlt : k < xs.length := (List.getElem?_eq_some_iff.mp hk).1
      have ih := iterFrom_list xs fuel (k + 1) (by omega) (by omega)
      have e : ((k : Int) + 1) = ((k + 1 : Nat) : Int) := by omega
      simp only [listSeq] at ih
      simp only [e, ih, hd, bind, Except.bind, pure, Except.pure]

theorem containsFrom_list {α : Type} (xs : List α) (E : EqOps α) (value : α) :
    ∀ (fuel k : Nat), 0 < fuel → xs.length < k + fuel →
    (listSeq xs).containsFrom E value fuel (k : Int) = listContains E value (xs.drop k)
  | 0, k, h0, h => absurd h0 (by omega)
  | fuel + 1, k, _, h => by
    have hd := drop_step xs k
    simp only [Seq.containsFrom, listSeq, listGet_nat]
    cases hk : xs[k]? with
    | none =>
      simp only [hk] at hd
      simp [isIndexError, hd, listContains]
    | some v =>
      simp only [hk] at hd
      have hlt : k < xs.length := (List.getElem?_eq_some_iff.mp hk).1
      have ih := containsFrom_list xs E value fuel (k + 1) (by omega) (by omega)
      have e : ((k : Int) + 1) = ((k + 1 : Nat) : Int) := by omega
      simp only [listSeq] at ih
      simp only [e, ih, hd, listContains]

theorem countFrom_list {α : Type} (xs : List α) (E : EqOps α) (value : α) :
    ∀ (fuel k : Nat), 0 < fuel → xs.length < k + fuel →
    (listSeq xs).countFrom E value fuel (k : Int) = listCount E value (xs.drop k)
  | 0, k, h0, h => absurd h0 (by omega)
  | fuel + 1, k, _, h => by
    have hd := drop_step xs k
    simp only [Seq.countFrom, listSeq, listGet_nat]
    cases hk : xs[k]? with
    | none =>
      simp only [hk] at hd
      simp [isIndexError, hd, listCount]
    | some v =>
      simp only [hk] at hd
      have hlt : k < xs.length := (List.getElem?_eq_some_iff.mp hk).1
      have ih := countFrom_list xs E value fuel (k + 1) (by omega) (by omega)
      have e : ((k : Int) + 1) = ((k + 1 : Nat) : Int) := by omega
      simp only [listSeq] at ih
      simp only [e, ih, hd, listCount]

theorem reversedFrom_list {α : Type} (xs : List α) : ∀ n : Nat, n ≤ xs.length →
    (listSeq xs).reversedFrom n = .ok (xs.take n).reverse
  | 0, _ => by simp [Seq.reversedFrom]
  | n + 1, h => by
    have hn : n < xs.length := by omega
    have ih := reversedFrom_list xs n (by omega)
    have hg : xs[n]? = some xs[n] := by simp [hn]
    simp only [Seq.reversedFrom, ih]
    have h2 : (listSeq xs).getitem (n : Int) = .ok xs[n] := by
      simp [listSeq, listGet_nat, hg]
    simp only [h2, List.take_add_one, hg, Option.toList_some, List.reverse_append,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
    rfl

/-- `Sequence.__iter__`, `__contains__`, `count`, `__reversed__` applied to a sequence with
`list`'s `__getitem__` and `__len__` behave exactly like `list`'s own, including the order of the
`==` calls and which exception escapes from a raising `__eq__`. `Sequence` docs; `fuel` is the
model's loop budget and any `fuel > len(xs)` is enough. -/
def SeqMixinsMatchList : Prop :=
  ∀ (α : Type) (E : EqOps α) (xs : List α) (value : α) (fuel : Nat), xs.length < fuel →
    (listSeq xs).iterFrom fuel 0 = .ok xs ∧
    (listSeq xs).containsFrom E value fuel 0 = listContains E value xs ∧
    (listSeq xs).countFrom E value fuel 0 = listCount E value xs ∧
    (listSeq xs).reversed = .ok xs.reverse

theorem seqMixinsMatchList_proven : SeqMixinsMatchList := by
  intro α E xs value fuel h
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using iterFrom_list xs fuel 0 (by omega) (by omega)
  · simpa using containsFrom_list xs E value fuel 0 (by omega) (by omega)
  · simpa using countFrom_list xs E value fuel 0 (by omega) (by omega)
  · have := reversedFrom_list xs xs.length (by omega)
    simpa [Seq.reversed, listSeq, bind, Except.bind] using this

/-- The outcome of `Sequence.index` and `list.index` agree: the same index, or the same
exception out of `__eq__`, and not-found (`ValueError`, with a different message) on both sides. -/
def indexAgree : Py Int → Py (Option Int) → Prop
  | .ok i, .ok (some j) => i = j
  | .error (.valueError ""), .ok none => True
  | .error e, .error e' => e = e'
  | _, _ => False

theorem indexLoop_agree {α : Type} (xs : List α) (E : EqOps α) (value : α) (stop : Option Int)
    (stop' : Int)
    (hstop : ∀ k : Nat, k < xs.length →
      ((stop.isNone = true ∨ (k : Int) < stop.getD 0) ↔ (k : Int) < stop')) :
    ∀ (fuel k : Nat), xs.length < k + (fuel + 1) →
    indexAgree ((listSeq xs).indexLoop E value stop (fuel + 1) (k : Int))
      (listIndexLoop E value xs stop' (fuel + 1) (k : Int))
  | fuel, k, h => by
    have toNat_k : ((k : Int)).toNat = k := by omega
    simp only [Seq.indexLoop, listIndexLoop, listSeq, listGet_nat, toNat_k]
    by_cases hlen : k < xs.length
    · have hg : xs[k]? = some xs[k] := by simp [hlen]
      have hs := hstop k hlen
      simp only [hg]
      by_cases hc : (k : Int) < stop'
      · rw [if_pos (hs.mpr hc), if_pos hc]
        cases hsame : E.same xs[k] value with
        | error e => simp only [bind, Except.bind, indexAgree]
        | ok b =>
          cases b with
          | true => simp only [bind, Except.bind, pure, Except.pure, ite_true, indexAgree]
          | false =>
            cases fuel with
            | zero => omega
            | succ fuel =>
              have ih := indexLoop_agree xs E value stop stop' hstop fuel (k + 1) (by omega)
              have e : ((k : Int) + 1) = ((k + 1 : Nat) : Int) := by omega
              simp only [listSeq] at ih
              simp only [bind, Except.bind, Bool.false_eq_true, ite_false, e]
              exact ih
      · rw [if_neg (fun x => hc (hs.mp x)), if_neg hc]
        simp only [indexAgree]
    · have hg : xs[k]? = none := by simp; omega
      simp only [hg]
      by_cases hc : (k : Int) < stop' <;>
        by_cases hc' : (stop.isNone = true ∨ (k : Int) < stop.getD 0) <;>
        simp only [hc, hc', ite_true, ite_false, indexAgree, isIndexError]

/-- `Sequence.index(value, start, stop)` agrees with `list.index(value, start, stop)` for every
pair of `int` bounds, negative, out of range or huge, with the default `stop=None` being
`list.index`'s `sys.maxsize`. Type invariant: `len(xs) <= sys.maxsize`. -/
def SeqIndexMatchesList : Prop :=
  ∀ (α : Type) (E : EqOps α) (xs : List α) (value : α) (start : Int) (stop : Option Int)
    (fuel : Nat), xs.length < fuel → (xs.length : Int) ≤ ssizeMax →
    indexAgree ((listSeq xs).index E value start stop fuel)
      (listIndex E xs value start (stop.getD ssizeMax) fuel)

/-- `stop` after the source's normalisation of a negative value. -/
def seqStop (n : Int) : Option Int → Option Int
  | some t => if t < 0 then some (t + n) else some t
  | none => none

def listStop (n s : Int) : Int := if s < 0 then max (s + n) 0 else s

theorem seqIndex_eq {α : Type} (s : Seq α) (n : Nat) (hn : s.len = .ok n) (E : EqOps α) (value : α)
    (start : Int) (stop : Option Int) (fuel : Nat) :
    s.index E value start stop fuel = s.indexLoop E value (seqStop n stop) fuel
      (if start < 0 then max ((n : Int) + start) 0 else start) := by
  by_cases h : start < 0 <;> cases stop <;>
    simp only [Seq.index, seqStop, hn, h, ite_true, ite_false, bind, Except.bind, pure, Except.pure]
  all_goals (rename_i t; by_cases ht : t < 0 <;>
    simp only [ht, ite_true, ite_false, bind, Except.bind, pure, Except.pure])

theorem seqIndexMatchesList_proven : SeqIndexMatchesList := by
  intro α E xs value start stop fuel hf hmax
  cases fuel with
  | zero => omega
  | succ fuel =>
    have h0 : ¬ ssizeMax < 0 := by unfold ssizeMax; omega
    obtain ⟨k, hk⟩ : ∃ k : Nat,
        (if start < 0 then max ((xs.length : Int) + start) 0 else start) = (k : Int) :=
      ⟨_, (Int.toNat_of_nonneg (by split <;> omega)).symm⟩
    have hL : listIndex E xs value start (stop.getD ssizeMax) (fuel + 1) =
        listIndexLoop E value xs (listStop xs.length (stop.getD ssizeMax)) (fuel + 1) (k : Int) := by
      rw [← hk]
      simp only [listIndex, listStop]
      have : (if start < 0 then max (start + (xs.length : Int)) 0 else start) =
          (if start < 0 then max ((xs.length : Int) + start) 0 else start) := by
        split <;> omega
      rw [this]
    rw [hL, seqIndex_eq (listSeq xs) xs.length rfl, hk]
    refine indexLoop_agree xs E value _ _ ?_ fuel k (by omega)
    intro j hj
    cases stop with
    | none =>
      simp only [seqStop, listStop, Option.getD_none, Option.isNone_none, true_or, h0, ite_false,
        true_iff]
      unfold ssizeMax at *
      omega
    | some t =>
      by_cases ht : t < 0 <;>
        simp only [seqStop, listStop, Option.getD_some, ht, ite_true, ite_false, Option.isNone_some,
          Bool.false_eq_true, false_or] <;>
        omega

/-! ### MutableSequence -/

/-- The mixin and the builtin have the same result, or both raise `IndexError`. -/
def sameOrIndexError {α : Type} (a b : Py α) : Prop :=
  a = b ∨ (a.raises "IndexError" ∧ b.raises "IndexError")

theorem listGet_in {α : Type} (xs : List α) (i : Int)
    (j : Int) (hj : j = if i < 0 then i + xs.length else i) :
    listGet xs i = if j < 0 ∨ j ≥ xs.length then .error (.indexError "list index out of range")
      else match xs[j.toNat]? with
        | some v => .ok v
        | none => .error (.indexError "list index out of range") := by
  subst hj; rfl

/-- `MutableSequence.pop(index)` on `list` primitives has `list.pop`'s result, for every `index`,
with `IndexError` on both sides for an empty list or an index out of range. The messages differ:
the mixin reports what `self[index]` reported. `MutableSequence.pop` docstring. -/
def MSeqPopMatchesList : Prop :=
  ∀ (α : Type) (xs : List α) (i : Int), sameOrIndexError (listMSeq.pop xs i) (listPop xs i)

theorem mseqPopMatchesList_proven : MSeqPopMatchesList := by
  intro α xs i
  simp only [sameOrIndexError, MSeq.pop, listMSeq, bind, Except.bind, pure, Except.pure,
    listPop, listGet, listDel]
  by_cases hc : (if i < 0 then i + (xs.length : Int) else i) < 0 ∨
      (if i < 0 then i + (xs.length : Int) else i) ≥ (xs.length : Int)
  · right
    constructor
    · simp only [hc, ite_true]; exact ⟨_, rfl, rfl⟩
    · by_cases he : xs.isEmpty <;> simp only [he, ite_true, ite_false, hc]
      all_goals exact ⟨_, rfl, rfl⟩
  · have hne : xs.isEmpty = false := by
      cases xs with
      | nil =>
        exfalso; apply hc
        simp only [List.length_nil]
        by_cases h : i < 0 <;> simp only [h, ite_true, ite_false] <;> omega
      | cons a as => rfl
    left
    simp only [hc, ite_false, hne, Bool.false_eq_true]
    generalize (if i < 0 then i + (xs.length : Int) else i) = j at hc
    have hlt : j.toNat < xs.length := by omega
    have hs : xs[j.toNat]? = some xs[j.toNat] := by simp [hlt]
    rw [hs]

theorem pop_empty {α : Type} (i : Int) :
    (listMSeq (α := α)).pop [] i = .error (.indexError "list index out of range") := by
  simp only [MSeq.pop, listMSeq, listGet, bind, Except.bind]
  simp

theorem pop_last {α : Type} (a : α) (as : List α) :
    ∃ v, (listMSeq (α := α)).pop (a :: as) = .ok (v, (a :: as).dropLast) := by
  have hlen : ((a :: as).length : Int) ≠ 0 := by simp; omega
  have h1 : (-1 : Int) < 0 := by omega
  have h2 : ¬ ((-1 + ((a :: as).length : Int)) < 0 ∨
      (-1 + ((a :: as).length : Int)) ≥ ((a :: as).length : Int)) := by
    simp only [List.length_cons]; omega
  have ht : (-1 + ((a :: as).length : Int)).toNat = as.length := by
    simp only [List.length_cons]; omega
  refine ⟨(a :: as)[as.length]'(by simp), ?_⟩
  simp only [MSeq.pop, listMSeq, listGet, listDel, h1, ite_true, h2, ite_false, ht, bind, Except.bind,
    pure, Except.pure]
  have hidx : (a :: as)[as.length]? = some ((a :: as)[as.length]'(by simp)) := by simp
  rw [hidx]
  have : (a :: as).eraseIdx as.length = (a :: as).dropLast := by
    rw [List.dropLast_eq_take]
    simp only [List.length_cons, Nat.add_sub_cancel]
    rw [List.eraseIdx_eq_take_drop_succ]
    simp
  simp [this]

theorem clear_list {α : Type} : ∀ (fuel : Nat) (s : List α), s.length < fuel →
    (listMSeq (α := α)).clear fuel s = .ok []
  | 0, s, h => by omega
  | fuel + 1, [], h => by
    simp [MSeq.clear, pop_empty, isIndexError]
  | fuel + 1, a :: as, h => by
    obtain ⟨v, hv⟩ := pop_last a as
    simp only [MSeq.clear, hv]
    exact clear_list fuel _ (by simp at h ⊢; omega)

theorem listInsert_len {α : Type} (xs : List α) (v : α) :
    listInsert xs (xs.length : Int) v = xs ++ [v] := by
  have h3 : (if (xs.length : Int) < 0 then max ((xs.length : Int) + xs.length) 0
      else min (xs.length : Int) xs.length).toNat = xs.length := by
    split <;> omega
  simp only [listInsert]
  rw [h3]
  simp

theorem append_list {α : Type} (xs : List α) (v : α) :
    (listMSeq (α := α)).append xs v = .ok (xs ++ [v]) := by
  simp only [MSeq.append, listMSeq, bind, Except.bind, pure, Except.pure]
  rw [listInsert_len]

theorem extendList_list {α : Type} (s vs : List α) :
    (listMSeq (α := α)).extendList s vs = .ok (s ++ vs) := by
  induction vs generalizing s with
  | nil => simp [MSeq.extendList]
  | cons v vs ih =>
    simp only [MSeq.extendList, append_list, bind, Except.bind, ih]
    simp

/-- `append`, `extend`, `__iadd__` (also with `values is self`, which must not loop) and `clear`
on `list` primitives give `list`'s results. `MutableSequence` docs. -/
def MSeqGrowMatchesList : Prop :=
  ∀ (α : Type) (xs vs : List α) (v : α) (fuel : Nat), xs.length < fuel →
    listMSeq.append xs v = .ok (xs ++ [v]) ∧
    listMSeq.extend xs (some vs) fuel = .ok (xs ++ vs) ∧
    listMSeq.extend xs none fuel = .ok (xs ++ xs) ∧
    listMSeq.clear fuel xs = .ok []

theorem mseqGrowMatchesList_proven : MSeqGrowMatchesList := by
  intro α xs vs v fuel h
  refine ⟨?_, ?_, ?_, clear_list fuel xs h⟩
  · exact append_list xs v
  · simp [MSeq.extend, extendList_list]
  · have hi : (listMSeq.view xs).iterFrom fuel 0 = .ok xs := by
      simpa [listSeq, MSeq.view, listMSeq] using iterFrom_list xs fuel 0 (by omega) (by omega)
    simp [MSeq.extend, hi, bind, Except.bind, extendList_list]

/-! ### `reverse` and `remove` -/

/-- The list after `i` swaps of `MutableSequence.reverse`. -/
def RevInv {α : Type} (xs s : List α) (i : Nat) : Prop :=
  s.length = xs.length ∧ ∀ j, j < xs.length →
    s[j]? = if j < i ∨ xs.length - i ≤ j then xs[xs.length - 1 - j]? else xs[j]?

theorem listGet_set_nat {α : Type} (s : List α) (j : Nat) (h : j < s.length) :
    listGet s j = .ok s[j] := by
  rw [listGet_nat]
  simp [h]

theorem listSetItem_nat {α : Type} (s : List α) (j : Nat) (h : j < s.length) (v : α) :
    listSetItem s j v = .ok (s.set j v) := by
  have h1 : ¬ ((j : Int) < 0) := by omega
  have h2 : ¬ ((j : Int) ≥ (s.length : Int)) := by omega
  simp only [listSetItem, h1, ite_false, false_or, h2, Int.toNat_natCast]

theorem swap_step {α : Type} (xs s : List α) (i : Nat) (hi : i < xs.length / 2)
    (hinv : RevInv xs s i) : ∃ s', (listMSeq (α := α)).swap xs.length s i = .ok s' ∧
      RevInv xs s' (i + 1) := by
  obtain ⟨hlen, hj⟩ := hinv
  have hn : 2 * i + 1 < xs.length := by omega
  let m := xs.length - 1 - i
  have hm : m < xs.length := by omega
  have hmi : (xs.length : Int) - (i : Int) - 1 = (m : Int) := by omega
  have hi' : i < s.length := by omega
  have hm' : m < s.length := by omega
  have hset : m < (s.set i s[m]).length := by simp; omega
  refine ⟨(s.set i s[m]).set m s[i], ?_, ?_⟩
  · simp only [MSeq.swap, listMSeq, hmi, bind, Except.bind, listGet_set_nat s m hm',
      listGet_set_nat s i hi', listSetItem_nat s i hi', listSetItem_nat _ m hset]
  · refine ⟨by simp [hlen], ?_⟩
    intro j hjl
    have him : i ≠ m := by omega
    have hvi : s[i]? = xs[i]? := by rw [hj i (by omega), if_neg (by omega)]
    have hvm : s[m]? = xs[m]? := by rw [hj m hm, if_neg (by omega)]
    have gi : some s[i] = xs[i]? := by rw [← hvi]; simp [hi']
    have gm : some s[m] = xs[m]? := by rw [← hvm]; simp [hm']
    simp only [List.getElem?_set, List.length_set]
    by_cases h1 : m = j
    · subst h1
      have e : xs.length - 1 - m = i := by omega
      rw [if_pos rfl, if_pos hm', if_pos (Or.inr (by omega)), e]
      exact gi
    · rw [if_neg h1]
      by_cases h2 : i = j
      · subst h2
        rw [if_pos rfl, if_pos hi', if_pos (Or.inl (by omega))]
        exact gm
      · rw [if_neg h2, hj j hjl]
        by_cases c : j < i ∨ xs.length - i ≤ j
        · rw [if_pos c, if_pos (by omega)]
        · rw [if_neg c, if_neg (by omega)]

theorem swapLoop_rev {α : Type} (xs : List α) : ∀ (k i : Nat) (s : List α),
    k + i = xs.length / 2 → RevInv xs s i →
    (listMSeq (α := α)).swapLoop xs.length k i s = .ok xs.reverse
  | 0, i, s, h, hinv => by
    obtain ⟨hlen, hj⟩ := hinv
    have : s = xs.reverse := by
      apply List.ext_getElem?
      intro j
      by_cases hjl : j < xs.length
      · rw [hj j hjl, List.getElem?_reverse hjl]
        by_cases c : j < i ∨ xs.length - i ≤ j
        · rw [if_pos c]
        · have e : xs.length - 1 - j = j := by omega
          rw [if_neg c, e]
      · have h1 : s[j]? = none := by simp; omega
        have h2 : xs.reverse[j]? = none := by simp; omega
        rw [h1, h2]
    simp [MSeq.swapLoop, this]
  | k + 1, i, s, h, hinv => by
    obtain ⟨s', h1, h2⟩ := swap_step xs s i (by omega) hinv
    simp only [MSeq.swapLoop, h1, bind, Except.bind]
    exact swapLoop_rev xs k (i + 1) s' (by omega) h2

/-- `MutableSequence.reverse` on `list` primitives reverses the list in place, for every length,
even and odd, including the fixed middle element. Docstring: "reverse *IN PLACE*". -/
def MSeqReverseMatchesList : Prop :=
  ∀ (α : Type) (xs : List α), listMSeq.reverse xs = .ok xs.reverse

theorem mseqReverseMatchesList_proven : MSeqReverseMatchesList := by
  intro α xs
  simp only [MSeq.reverse, listMSeq, bind, Except.bind]
  refine swapLoop_rev xs (xs.length / 2) 0 xs (by omega) ⟨rfl, ?_⟩
  intro j hjl
  rw [if_neg (by omega)]

/-- The outcomes of `MutableSequence.remove` and `list.remove` agree: the same list, the same
exception out of `__eq__`, or not-found on both sides. -/
def removeAgree {α : Type} : Py (List α) → Py (Option (List α)) → Prop
  | .ok a, .ok (some b) => a = b
  | .error (.valueError ""), .ok none => True
  | .error e, .error e' => e = e'
  | _, _ => False

/-- How the index loop and `listRemove` on `xs.drop k` relate. -/
def RemoveRel {α : Type} (xs : List α) (k : Nat) (r : Py Int) (l : Py (Option (List α))) : Prop :=
  (∃ (j : Nat) (ys : List α), r = .ok (j : Int) ∧ l = .ok (some ys) ∧ j < xs.length ∧
      xs.eraseIdx j = xs.take k ++ ys) ∨
  (r = .error (.valueError "") ∧ l = .ok none) ∨
  (∃ e, r = .error e ∧ l = .error e)

theorem remove_loop {α : Type} (xs : List α) (E : EqOps α) (value : α) :
    ∀ (fuel k : Nat), xs.length < k + (fuel + 1) →
    RemoveRel xs k ((listSeq xs).indexLoop E value none (fuel + 1) (k : Int))
      (listRemove E value (xs.drop k))
  | fuel, k, h => by
    have hd := drop_step xs k
    simp only [Seq.indexLoop, listSeq, listGet_nat, Option.isNone_none, true_or, ite_true]
    cases hk : xs[k]? with
    | none =>
      simp only [hk] at hd
      exact Or.inr (Or.inl (by simp [isIndexError, hd, listRemove]))
    | some v =>
      simp only [hk] at hd
      have hlt : k < xs.length := (List.getElem?_eq_some_iff.mp hk).1
      rw [hd]
      simp only [listRemove, bind, Except.bind, pure, Except.pure]
      cases hsame : E.same v value with
      | error e => exact Or.inr (Or.inr ⟨e, rfl, rfl⟩)
      | ok b =>
        cases b with
        | true =>
          simp only [ite_true]
          exact Or.inl ⟨k, _, rfl, rfl, hlt, List.eraseIdx_eq_take_drop_succ ..⟩
        | false =>
          cases fuel with
          | zero => omega
          | succ fuel =>
            have ih := remove_loop xs E value fuel (k + 1) (by omega)
            have e : ((k : Int) + 1) = ((k + 1 : Nat) : Int) := by omega
            simp only [listSeq] at ih
            simp only [Bool.false_eq_true, ite_false, e]
            have htake : xs.take (k + 1) = xs.take k ++ [v] := by
              rw [List.take_add_one, hk]; rfl
            rcases ih with ⟨j, ys, hr, hl, h1, h2⟩ | ⟨hr, hl⟩ | ⟨e, hr, hl⟩
            · refine Or.inl ⟨j, v :: ys, hr, by rw [hl], h1, ?_⟩
              rw [h2, htake]; simp
            · exact Or.inr (Or.inl ⟨hr, by rw [hl]⟩)
            · exact Or.inr (Or.inr ⟨e, hr, by rw [hl]⟩)

theorem listDel_nat {α : Type} (s : List α) (j : Nat) (h : j < s.length) :
    listDel s j = .ok (s.eraseIdx j) := by
  have h1 : ¬ ((j : Int) < 0) := by omega
  have h2 : ¬ ((j : Int) ≥ (s.length : Int)) := by omega
  simp only [listDel, h1, ite_false, false_or, h2, Int.toNat_natCast]

/-- `MutableSequence.remove` on `list` primitives removes the first element comparing equal, like
`list.remove`; both raise `ValueError` when there is none, with different messages, and an
exception out of `__eq__` escapes from the same comparison. Docstring; `fuel > len(xs)`. -/
def MSeqRemoveMatchesList : Prop :=
  ∀ (α : Type) (E : EqOps α) (xs : List α) (value : α) (fuel : Nat), xs.length < fuel →
    removeAgree (listMSeq.remove E xs value fuel) (listRemove E value xs)

theorem mseqRemoveMatchesList_proven : MSeqRemoveMatchesList := by
  intro α E xs value fuel hf
  cases fuel with
  | zero => omega
  | succ fuel =>
    have h := remove_loop xs E value fuel 0 (by omega)
    simp only [Int.natCast_zero, List.drop_zero, List.take_zero, List.nil_append] at h
    have hv : (listMSeq.view xs) = listSeq xs := rfl
    have hidx : (listSeq xs).index E value 0 none (fuel + 1) =
        (listSeq xs).indexLoop E value none (fuel + 1) 0 := by
      rw [seqIndex_eq (listSeq xs) xs.length rfl]
      simp [seqStop]
    simp only [MSeq.remove, hv, hidx, bind, Except.bind]
    rcases h with ⟨j, ys, hr, hl, h1, h2⟩ | ⟨hr, hl⟩ | ⟨e, hr, hl⟩
    · have hr' : (listSeq xs).indexLoop E value none (fuel + 1) 0 = .ok (j : Int) := hr
      rw [hr', hl]
      simp [listMSeq, listDel_nat xs j h1, removeAgree, h2, bind, Except.bind]
    · have hr' : (listSeq xs).indexLoop E value none (fuel + 1) 0 = .error (.valueError "") := hr
      rw [hr', hl]
      simp only [removeAgree]
    · have hr' : (listSeq xs).indexLoop E value none (fuel + 1) 0 = .error e := hr
      rw [hr', hl]
      cases e <;> simp only [removeAgree]

end PyLean.CoreLibs.CollAbc
