import PyLean.BytesObj.Bytes.Ctor
import PyLean.BytesObj.Bytes.FormatProps2
import PyLean.StrSearch.Basic

/-!
Properties of the `bytes` methods.
-/

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

/-! ## isascii -/

/-- `isascii` is true exactly for byte strings with no byte above 127
(`stringlib_find_max_char` returns at most 127 only then). -/
def IsAsciiSpec : Prop := ∀ s : Seq, (∀ c ∈ s, c < 256) → bytesIsAscii s = s.all (· < 128)

theorem isAsciiSpec_proven : IsAsciiSpec := by
  intro s hs
  unfold bytesIsAscii maxCharValue isAscii
  cases h : s.all (· < 128) with
  | true => simp
  | false =>
    have hk : kindOf s = 1 := kindOf_of_all hs
    simp [hk]

/-! ## The search plumbing -/

theorem clamp_id (v : Int) (h1 : ssizeMin ≤ v) (h2 : v ≤ ssizeMax) : clampSsize v = v := by
  simp only [clampSsize, Int.max_def, Int.min_def]
  repeat' split
  all_goals omega

theorem clamp_byte (c : Nat) (hc : c < 256) : clampSsize (c : Int) = c := by
  apply clamp_id
  · rw [show ssizeMin = -9223372036854775808 by decide]; omega
  · rw [show ssizeMax = 9223372036854775807 by decide]; omega

theorem parse_byte (c : Nat) (hc : c < 256) : parseFindsByte (.byte (c : Int)) = .ok [c] := by
  have h : ¬ ((c : Int) < 0 ∨ (c : Int) > 255) := by omega
  simp [parseFindsByte, clamp_byte c hc, h]

theorem parse_buf (b : Seq) : parseFindsByte (.buf b) = .ok b := rfl

/-- An int argument of `find`, `rfind`, `index`, `rindex`, `count` means the one-byte
string: for every byte value and all bounds the result is the same; ints outside
`range(256)` raise `ValueError`, also when they do not fit `Py_ssize_t`, and an object
that is neither a buffer nor an index raises `TypeError`. `index` is `find` with a
`ValueError` for -1. -/
def FindByteArg : Prop :=
  (∀ (s : Seq) (c : Nat) (st en : Option Int) (fwd : Bool), c < 256 →
    bytesFindObj s (.int c) st en fwd = bytesFindObj s (.bytes [c]) st en fwd ∧
    bytesIndexObj s (.int c) st en fwd = bytesIndexObj s (.bytes [c]) st en fwd ∧
    bytesCountObj s (.int c) st en = bytesCountObj s (.bytes [c]) st en) ∧
  (∀ (s : Seq) (v : Int) (st en : Option Int) (fwd : Bool), v < 0 ∨ v > 255 →
    bytesFindObj s (.int v) st en fwd = .error (.valueError "byte must be in range(0, 256)")) ∧
  (∀ (s p : Seq) (st en : Option Int) (fwd : Bool), ∀ r,
    bytesFindObj s (.bytes p) st en fwd = .ok r →
    bytesIndexObj s (.bytes p) st en fwd =
      if r = -1 then .error (.valueError "subsection not found") else .ok r) ∧
  (∀ (s : Seq) (st en : Option Int) (fwd : Bool),
    ∃ m, bytesFindObj s (.str []) st en fwd = .error (.typeError m))

theorem clamp_out (v : Int) (h : v < 0 ∨ v > 255) : clampSsize v < 0 ∨ clampSsize v > 255 := by
  have h1 : ssizeMin < 0 := by decide
  have h2 : (255 : Int) < ssizeMax := by decide
  unfold clampSsize
  rcases h with h | h
  · left
    simp only [Int.max_def, Int.min_def]
    repeat' split
    all_goals omega
  · right
    simp only [Int.max_def, Int.min_def]
    repeat' split
    all_goals omega

theorem findByteArg_proven : FindByteArg := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s c st en fwd hc
    have h0 := parse_byte c hc
    refine ⟨?_, ?_, ?_⟩
    · simp [bytesFindObj, parseFindsByteObj, Obj.buffer?, Obj.index?, bind, Except.bind, bytesFind,
        bytesFindInternal, h0, parse_buf]
    · simp [bytesIndexObj, parseFindsByteObj, Obj.buffer?, Obj.index?, bind, Except.bind, bytesIndex,
        bytesFindInternal, h0, parse_buf]
    · simp [bytesCountObj, parseFindsByteObj, Obj.buffer?, Obj.index?, bind, Except.bind, bytesCount,
        h0, parse_buf]
  · intro s v st en fwd h
    have := clamp_out v h
    simp [bytesFindObj, parseFindsByteObj, Obj.buffer?, Obj.index?, bind, Except.bind, bytesFind,
      bytesFindInternal, parseFindsByte, this]
  · intro s p st en fwd r h
    simp only [bytesFindObj, parseFindsByteObj, Obj.buffer?, bind, Except.bind] at h
    simp only [bytesIndexObj, parseFindsByteObj, Obj.buffer?, bind, Except.bind, bytesIndex]
    simp only [bytesFind] at h
    rw [h]
    by_cases hr : r = -1
    · simp [hr]; rfl
    · simp [hr, pure, Except.pure]
  · intro s st en fwd
    exact ⟨_, by simp [bytesFindObj, parseFindsByteObj, Obj.buffer?, Obj.index?, bind, Except.bind]; rfl⟩

theorem findL_single (c : Nat) (s : Seq) : (findL [c] s).isSome = true ↔ c ∈ s := by
  induction s with
  | nil => simp [findL]
  | cons d ds ih =>
    by_cases h : c = d
    · subst h
      simp [findL, List.isPrefixOf]
    · have h2 : (([c] : Seq).isPrefixOf (d :: ds)) = false := by simp [List.isPrefixOf, h]
      simp [findL, h2, ih, h]

theorem find_single (s : Seq) (c : Nat) : decide (stringlibFind s [c] 0 ≥ 0) = decide (c ∈ s) := by
  have h3 := findL_single c s
  unfold stringlibFind fastsearch
  simp only [List.length_cons, List.length_nil]
  cases hf : findL [c] s with
  | none =>
    have : c ∉ s := by rw [← h3, hf]; simp
    by_cases hs : s.length < 0 + 1 <;> simp [this, hf, hs, optIdx]
  | some i =>
    have hm : c ∈ s := by rw [← h3, hf]; simp
    have hs : ¬ (s.length < 0 + 1) := by
      have := List.length_pos_of_mem hm
      omega
    simp only [hm, hf, hs, decide_true, optIdx]
    simp

theorem clamp_out2 (v : Int) (h : v < 0 ∨ v ≥ 256) : clampSsize v < 0 ∨ clampSsize v ≥ 256 := by
  have h1 : ssizeMin < 0 := by decide
  have h2 : (256 : Int) < ssizeMax := by decide
  unfold clampSsize
  rcases h with h | h
  · left
    simp only [Int.max_def, Int.min_def]
    repeat' split
    all_goals omega
  · right
    simp only [Int.max_def, Int.min_def]
    repeat' split
    all_goals omega

/-- `x in b`: an int in `range(256)` is byte membership and the same as `bytes([x]) in b`,
any other int is a `ValueError`; an object that is no index is searched as a buffer, an
empty one being found everywhere. -/
def ContainsSpec : Prop :=
  (∀ (s : Seq) (c : Nat), c < 256 → bytesContains s (.int c) = .ok (decide (c ∈ s)) ∧
    bytesContains s (.int c) = bytesContains s (.bytes [c])) ∧
  (∀ (s : Seq) (v : Int), v < 0 ∨ v ≥ 256 →
    bytesContains s (.int v) = .error (.valueError "byte must be in range(0, 256)")) ∧
  (∀ s : Seq, bytesContains s (.bytes []) = .ok true)

theorem containsSpec_proven : ContainsSpec := by
  refine ⟨?_, ?_, ?_⟩
  · intro s c hc
    have hA : bytesContains s (.int c) = .ok (decide (c ∈ s)) := by
      have h : ¬ ((c : Int) < 0 ∨ (c : Int) ≥ 256) := by omega
      simp [bytesContains, Obj.index?, clamp_byte c hc, h]
    refine ⟨hA, ?_⟩
    rw [hA]
    have hB : bytesContains s (.bytes [c]) = .ok (decide (stringlibFind s [c] 0 ≥ 0)) := by
      simp [bytesContains, Obj.index?, getBuffer, Obj.buffer?]
    rw [hB, find_single]
  · intro s v h
    have := clamp_out2 v h
    simp [bytesContains, Obj.index?, this]
  · intro s
    simp [bytesContains, Obj.index?, getBuffer, Obj.buffer?, stringlibFind]

/-- `startswith`/`endswith` with a tuple is "any item matches", stopping at a match,
so an invalid item after the match is not looked at; a non-buffer, non-tuple argument
gets the method's message. -/
def TailmatchTuple : Prop :=
  (∀ (s : Seq) (ps : List Seq) (st en : Int) (dir : Bool),
    bytesTailmatchObj s "startswith" (.tuple (ps.map .bytes)) st en dir =
      .ok (ps.any (fun p => bytesTailmatch s p st en dir))) ∧
  (∀ (s p : Seq) (st en : Int) (dir : Bool), bytesTailmatch s p st en dir = true →
    bytesTailmatchObj s "startswith" (.tuple [.bytes p, .int 0]) st en dir = .ok true) ∧
  (∀ (s : Seq) (st en : Int) (dir : Bool) (v : Int),
    bytesTailmatchObj s "endswith" (.int v) st en dir =
      .error (.typeError "endswith first arg must be bytes or a tuple of bytes, not int"))

theorem tailLoop_bytes (s : Seq) (st en : Int) (dir : Bool) (ps : List Seq) :
    bytesTailmatchObj.loop s st en dir (ps.map .bytes) =
      .ok (ps.any (fun p => bytesTailmatch s p st en dir)) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, bytesTailmatchObj.loop, tailItem, getBuffer, Obj.buffer?, List.any_cons]
    cases h : bytesTailmatch s p st en dir <;> simp [ih]

theorem tailmatchTuple_proven : TailmatchTuple := by
  refine ⟨?_, ?_, ?_⟩
  · intro s ps st en dir
    simp [bytesTailmatchObj, tailLoop_bytes]
  · intro s p st en dir h
    simp [bytesTailmatchObj, bytesTailmatchObj.loop, tailItem, getBuffer, Obj.buffer?, h]
  · intro s st en dir v
    simp [bytesTailmatchObj, tailItem, getBuffer, Obj.buffer?, Obj.typeName]
    decide

/-! ## `_PyBytes_Find` -/

theorem occ_take_last {hay p : Seq} {j : Nat} (hp : p ≠ [])
    (h : Occ hay p j) (hj : j + p.length ≤ hay.length - 1) : Occ (hay.take (hay.length - 1)) p j := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨by simp; omega, ?_⟩
  rw [← h2]
  apply List.ext_getElem
  · simp; omega
  · intro i hi hi2
    simp at hi hi2 ⊢

theorem occ_of_take {hay p : Seq} {j k : Nat} (h : Occ (hay.take k) p j) : Occ hay p j := by
  obtain ⟨h1, h2⟩ := h
  simp at h1
  refine ⟨by omega, ?_⟩
  rw [← h2]
  apply List.ext_getElem
  · simp; omega
  · intro i hi hi2
    simp at hi hi2 ⊢

/-- `_PyBytes_Find` is `stringlib_find`, for every haystack and needle and any offset
`≥ 0` (a documented precondition: the callers pass a position): searching one byte less
and comparing the last alignment by hand changes nothing. `_PyBytes_ReverseFind` is
`stringlib_rfind` by definition. -/
def PrivateFindAgrees : Prop :=
  ∀ (hay needle : Seq) (off : Int), 0 ≤ off →
    privateBytesFind hay needle off = stringlibFind hay needle off ∧
    privateBytesRFind hay needle off = stringlibRFind hay needle off

theorem privateFindAgrees_proven : PrivateFindAgrees := by
  intro hay needle off hoff
  refine ⟨?_, rfl⟩
  unfold privateBytesFind
  by_cases hm : needle.length = 0
  · simp [hm, stringlibFind]
  have hne : needle ≠ [] := by intro e; simp [e] at hm
  by_cases hl : needle.length > hay.length
  · have : stringlibFind hay needle off = -1 := by
      simp [stringlibFind, hm, fastsearch, show hay.length < needle.length by omega]
    simp [hm, hl, this]
  simp only [hm, if_false, hl]
  have hlen : needle.length ≤ hay.length := by omega
  generalize hinit : hay.take (hay.length - 1) = init
  have hstart : stringlibFind hay needle off =
      (match findL needle hay with | some i => (i : Int) + off | none => -1) := by
    have h1 : ¬ (hay.length < needle.length) := by omega
    cases hf : findL needle hay <;> simp [stringlibFind, hm, fastsearch, h1, hf, optIdx]
  have hinitlen : init.length = hay.length - 1 := by rw [← hinit]; simp
  have hT : ∀ {j}, Occ hay needle j → j + needle.length ≤ hay.length - 1 → Occ init needle j := by
    intro j ho hj
    rw [← hinit]
    exact occ_take_last hne ho hj
  have hU : ∀ {j}, Occ init needle j → Occ hay needle j := by
    intro j ho
    rw [← hinit] at ho
    exact occ_of_take ho
  have hres : stringlibFind init needle off =
      (match (if init.length < needle.length then none else findL needle init) with
       | some i => (i : Int) + off | none => -1) := by
    by_cases h1 : init.length < needle.length
    · simp [stringlibFind, hm, fastsearch, h1, optIdx]
    · cases hf : findL needle init <;> simp [stringlibFind, hm, fastsearch, h1, hf, optIdx]
  rw [hstart, hres]
  cases hfi : (if init.length < needle.length then none else findL needle init) with
  | none =>
    have hno : ∀ j, ¬ Occ init needle j := by
      intro j
      by_cases h1 : init.length < needle.length
      · exact not_occ_of_long h1 j
      · simp only [h1, if_false] at hfi
        exact findL_eq_none.mp hfi j
    simp only [if_true]
    by_cases hc : (hay.drop (hay.length - needle.length)).take needle.length = needle
    · have hocc : Occ hay needle (hay.length - needle.length) := ⟨by omega, hc⟩
      have : findL needle hay = some (hay.length - needle.length) := by
        rw [findL_eq_some]
        refine ⟨hocc, fun j hj ho => hno j (hT ho (by omega))⟩
      simp [this, hc, Int.add_comm]
    · have : findL needle hay = none := by
        rw [findL_eq_none]
        intro j ho
        by_cases hj : j + needle.length ≤ hay.length - 1
        · exact hno j (hT ho hj)
        · have e : j = hay.length - needle.length := by have := ho.1; omega
          exact hc (e ▸ ho.2)
      simp [this, hc]
  | some i =>
    have hocc : Occ init needle i ∧ ∀ j < i, ¬ Occ init needle j := by
      by_cases h1 : init.length < needle.length
      · simp [h1] at hfi
      · simp only [h1, if_false] at hfi
        exact findL_eq_some.mp hfi
    have : findL needle hay = some i := by
      rw [findL_eq_some]
      refine ⟨hU hocc.1, fun j hj ho => hocc.2 j hj (hT ho ?_)⟩
      have := hocc.1.1
      omega
    have hne1 : ¬ ((i : Int) + off = -1) := by omega
    simp [this, hne1]

end PyLean.BytesObj.Bytes
