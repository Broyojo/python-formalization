import PyLean.UnicodeObj.ObjectJoin
import PyLean.UnicodeObj.ObjectWriterProps

/-!
Properties of `str.join`.
-/

namespace PyLean.UnicodeObj

open PyLean

/-- A `str`, exact or not. -/
def JItem.isStr : JItem → Bool
  | .other _ => false
  | _ => true

/-- The length the pre-pass adds up, from index `i`. -/
def joinSize (seplen : Nat) : Nat → List JItem → Nat
  | _, [] => 0
  | i, x :: t => x.text.length + (if i != 0 then seplen else 0) + joinSize seplen (i + 1) t

theorem strMax_need (s : Str) : strMaxValue s = capNeed (maxCharOf s) := by
  rw [need_eq]
  unfold strMaxValue canonicalKind
  cases kindOfMax (maxCharOf s) <;> rfl

/-- The largest `strMaxValue` of the items. -/
def joinCap : List JItem → Nat
  | [] => 0
  | x :: t => max (strMaxValue x.text) (joinCap t)

/-- One round of the pre-pass on a `str`. -/
def jstep (seplen i : Nat) (s : Str) (p : JPass) : JPass :=
  { sz := p.sz + (s.length + (if i != 0 then seplen else 0))
    maxchar := max p.maxchar (strMaxValue s)
    useMemcpy := p.useMemcpy && (match p.last with | some w => w == (canonicalKind s).width | none => true)
    last := some (canonicalKind s).width }

theorem prepass_step (seplen i : Nat) (x : JItem) (t : List JItem) (p : JPass) (hx : x.isStr = true) :
    joinPrepass seplen i (x :: t) p =
      if ((x.text.length + (if i != 0 then seplen else 0) : Nat) : Int) > ssizeMax - p.sz then
        .error (.overflowError "join() result is too long for a Python string")
      else joinPrepass seplen (i + 1) t (jstep seplen i x.text p) := by
  cases x with
  | other n => simp [JItem.isStr] at hx
  | exact s => rfl
  | sub s => rfl

/-- The pre-pass on strings that fit: what it finds. -/
theorem prepass_ok (seplen : Nat) : ∀ (items : List JItem) (i : Nat) (p : JPass),
    (∀ x ∈ items, x.isStr = true) → (p.sz + joinSize seplen i items : Int) ≤ ssizeMax →
    ∃ q, joinPrepass seplen i items p = .ok q ∧ q.maxchar = max p.maxchar (joinCap items) := by
  intro items
  induction items with
  | nil =>
    intro i p _ _
    exact ⟨p, rfl, by simp [joinCap]⟩
  | cons x t ih =>
    intro i p hs hf
    simp only [joinSize] at hf
    rw [prepass_step _ _ _ _ _ (hs x List.mem_cons_self), if_neg (by omega)]
    obtain ⟨q, h1, h2⟩ := ih (i + 1) (jstep seplen i x.text p)
      (fun y hy => hs y (List.mem_cons_of_mem _ hy)) (by
        simp only [jstep]
        omega)
    refine ⟨q, h1, ?_⟩
    rw [h2]
    simp only [jstep, joinCap]
    omega

/-- The text of what comes after the first item. -/
theorem copy_rest {sep : Str} {seplen : Nat} (hn : sep.length = seplen) :
    ∀ (items : List JItem) (i : Nat), i ≠ 0 →
      joinCopy sep seplen i items = items.flatMap fun x => sep ++ x.text := by
  intro items
  induction items with
  | nil => intro _ _; rfl
  | cons x t ih =>
    intro i hi
    have e : (if (i != 0 && seplen != 0) = true then sep else []) = sep := by
      by_cases hs : seplen = 0
      · have : sep = [] := List.eq_nil_of_length_eq_zero (by omega)
        simp [this]
      · simp [hi, hs]
    simp only [joinCopy, e, List.flatMap_cons, List.append_assoc]
    rw [ih (i + 1) (by omega)]

theorem intercalate_flat (sep : Str) (x : Str) (l : List Str) :
    sep.intercalate (x :: l) = x ++ l.flatMap (fun y => sep ++ y) := by
  induction l generalizing x with
  | nil => simp
  | cons y t ih =>
    rw [List.intercalate_cons_cons, ih y]
    simp [List.flatMap_cons, List.append_assoc]

theorem copy_all {sep : Str} {seplen : Nat} (hn : sep.length = seplen) (x : JItem) (t : List JItem) :
    joinCopy sep seplen 0 (x :: t) = sep.intercalate ((x :: t).map JItem.text) := by
  simp only [joinCopy, List.map_cons]
  rw [intercalate_flat, copy_rest hn t 1 (by omega)]
  simp [List.flatMap_map]

theorem cap_ge (s : Str) : 127 ≤ strMaxValue s := by
  rw [strMax_need]
  have := need_value (maxCharOf s)
  omega

/-- The capacity of what `joinCopy` writes after the first item. -/
theorem rest_need (sep : Str) : ∀ t : List JItem, t ≠ [] →
    capNeed (maxCharOf (t.flatMap fun x => sep ++ x.text)) = max (strMaxValue sep) (joinCap t) := by
  intro t
  induction t with
  | nil => intro h; exact absurd rfl h
  | cons x r ih =>
    intro _
    simp only [List.flatMap_cons, List.append_assoc, joinCap]
    rw [maxCharOf_append, maxCharOf_append, capNeed_max, capNeed_max, ← strMax_need, ← strMax_need]
    cases r with
    | nil =>
      have h1 := cap_ge sep
      have h2 := cap_ge x.text
      have e : capNeed (maxCharOf []) = 127 := need_empty
      simp only [List.flatMap_nil, joinCap]
      rw [e]
      omega
    | cons y u =>
      rw [ih (by simp)]
      omega

/-- The kind of a result. -/
theorem join_kind (sep : Str) (x : JItem) (t : List JItem) (ht : t ≠ []) :
    kindOfMax (max (strMaxValue sep) (joinCap (x :: t))) =
      canonicalKind (sep.intercalate ((x :: t).map JItem.text)) := by
  have hf : (t.map JItem.text).flatMap (fun y => sep ++ y) = t.flatMap fun z => sep ++ z.text := by
    simp [List.flatMap_map]
  have e : max (strMaxValue sep) (joinCap (x :: t)) =
      capNeed (maxCharOf (sep.intercalate ((x :: t).map JItem.text))) := by
    simp only [List.map_cons]
    rw [intercalate_flat, hf, maxCharOf_append, capNeed_max, ← strMax_need, rest_need sep t ht]
    simp only [joinCap]
    omega
  rw [e, kind_need]
  rfl

theorem join_one_kind (s : Str) : kindOfMax (max 0 (strMaxValue s)) = canonicalKind s := by
  have : max 0 (strMaxValue s) = capNeed (maxCharOf s) := by
    rw [strMax_need]
    omega
  rw [this, kind_need]
  rfl

/-- `sep.join(items)`, for every list of strings that fits: the items with the separator between
them, and the canonical kind. The separator counts for the kind only if it is written, so one item
of a subclass stays narrow under a wide separator, and no item gives `''`. One exact `str` is
returned itself, with any separator, even one that is not a `str`. `NULL` is a space. A list that
does not fit is `JoinErrors`, so this leaves nothing out. -/
def JoinSpec : Prop :=
  (∀ (sep : JSep) (s : Str), joinArray sep [.exact s] = .ok .itself) ∧
  (∀ (sep : JSep), ∃ m, joinArray sep [] = .ok (.fresh [] (canonicalKind []) m)) ∧
  (∀ (sep : JSep) (s : Str), (s.length : Int) ≤ ssizeMax →
    ∃ m, joinArray sep [.sub s] = .ok (.fresh s (canonicalKind s) m)) ∧
  (∀ (sep : Str) (items : List JItem), 2 ≤ items.length → (∀ x ∈ items, x.isStr = true) →
    (joinSize sep.length 0 items : Int) ≤ ssizeMax →
    (∃ m, joinArray (.str sep) items =
      .ok (.fresh (sep.intercalate (items.map JItem.text))
        (canonicalKind (sep.intercalate (items.map JItem.text))) m))) ∧
  (∀ (items : List JItem), 2 ≤ items.length → (∀ x ∈ items, x.isStr = true) →
    (joinSize 1 0 items : Int) ≤ ssizeMax →
    (∃ m, joinArray .null items =
      .ok (.fresh ([32].intercalate (items.map JItem.text))
        (canonicalKind ([32].intercalate (items.map JItem.text))) m)))

/-- `joinArray` on one instance of a subclass, or one thing that is not a `str`. -/
theorem join_sub (sep : JSep) (s : Str) :
    joinArray sep [.sub s] =
      match joinPrepass 0 0 [.sub s] { sz := 0, maxchar := 0, useMemcpy := true, last := none } with
      | .error e => .error e
      | .ok p => .ok (.fresh (joinCopy [] 0 0 [.sub s]) (kindOfMax p.maxchar) p.useMemcpy) := rfl

theorem join_other (sep : JSep) (tp : String) :
    joinArray sep [.other tp] =
      match joinPrepass 0 0 [.other tp] { sz := 0, maxchar := 0, useMemcpy := true, last := none } with
      | .error e => .error e
      | .ok p => .ok (.fresh (joinCopy [] 0 0 [.other tp]) (kindOfMax p.maxchar) p.useMemcpy) := rfl

/-- `joinArray` on two or more items. -/
theorem join_many (sep : JSep) (x y : JItem) (t : List JItem) :
    joinArray sep (x :: y :: t) =
      match sep with
      | .null =>
        match joinPrepass 1 0 (x :: y :: t) { sz := 0, maxchar := 32, useMemcpy := true, last := some 1 } with
        | .error e => .error e
        | .ok p => .ok (.fresh (joinCopy [32] 1 0 (x :: y :: t)) (kindOfMax p.maxchar) p.useMemcpy)
      | .other tp => .error (.typeError s!"separator: expected str instance, {tpName80 tp} found")
      | .str s =>
        match joinPrepass s.length 0 (x :: y :: t)
            { sz := 0, maxchar := strMaxValue s, useMemcpy := true, last := some (canonicalKind s).width } with
        | .error e => .error e
        | .ok p => .ok (.fresh (joinCopy s s.length 0 (x :: y :: t)) (kindOfMax p.maxchar) p.useMemcpy) := by
  cases x <;> rfl

theorem joinSpec_proven : JoinSpec := by
  refine ⟨fun _ _ => rfl, fun _ => ⟨true, rfl⟩, ?_, ?_, ?_⟩
  · intro sep s hs
    obtain ⟨q, h1, h2⟩ := prepass_ok 0 [.sub s] 0
      { sz := 0, maxchar := 0, useMemcpy := true, last := none } (by simp [JItem.isStr]) (by
        simp [joinSize, JItem.text]
        omega)
    refine ⟨q.useMemcpy, ?_⟩
    rw [join_sub, h1]
    simp only [h2, joinCap, JItem.text]
    have e : max 0 (max (strMaxValue s) 0) = max 0 (strMaxValue s) := by omega
    rw [e, join_one_kind]
    simp [joinCopy, JItem.text]
  · intro sep items hl hs hf
    cases items with
    | nil => simp at hl
    | cons x t =>
      cases t with
      | nil => simp at hl
      | cons y r =>
        obtain ⟨q, h1, h2⟩ := prepass_ok sep.length (x :: y :: r) 0
          { sz := 0, maxchar := strMaxValue sep, useMemcpy := true,
            last := some (canonicalKind sep).width } hs (by simpa using hf)
        refine ⟨q.useMemcpy, ?_⟩
        rw [join_many]
        simp only [h1, h2]
        rw [copy_all rfl, join_kind sep x (y :: r) (by simp)]
  · intro items hl hs hf
    cases items with
    | nil => simp at hl
    | cons x t =>
      cases t with
      | nil => simp at hl
      | cons y r =>
        obtain ⟨q, h1, h2⟩ := prepass_ok 1 (x :: y :: r) 0
          { sz := 0, maxchar := 32, useMemcpy := true, last := some 1 } hs (by simpa using hf)
        refine ⟨q.useMemcpy, ?_⟩
        rw [join_many]
        simp only [h1, h2]
        rw [copy_all (sep := [32]) (seplen := 1) rfl]
        have e : max 32 (joinCap (x :: y :: r)) = max (strMaxValue [32]) (joinCap (x :: y :: r)) := by
          have h3 : strMaxValue [32] = 127 := by decide
          have h4 : 127 ≤ joinCap (x :: y :: r) := by
            simp only [joinCap]
            have := cap_ge x.text
            omega
          rw [h3]
          omega
        rw [e, join_kind [32] x (y :: r) (by simp)]

/-- The pre-pass on the first item that is not a `str`. -/
theorem prepass_item (seplen : Nat) (tp : String) (post : List JItem) :
    ∀ (pre : List JItem) (i : Nat) (p : JPass), (∀ x ∈ pre, x.isStr = true) →
      (p.sz + joinSize seplen i pre : Int) ≤ ssizeMax →
      joinPrepass seplen i (pre ++ .other tp :: post) p =
        .error (.typeError
          s!"sequence item {i + pre.length}: expected str instance, {tpName80 tp} found") := by
  intro pre
  induction pre with
  | nil =>
    intro i p _ _
    simp [joinPrepass]
  | cons x t ih =>
    intro i p hs hf
    have hi : i + (x :: t).length = (i + 1) + t.length := by
      simp only [List.length_cons]
      omega
    simp only [joinSize] at hf
    rw [hi, List.cons_append, prepass_step _ _ _ _ _ (hs x List.mem_cons_self), if_neg (by omega)]
    exact ih (i + 1) (jstep seplen i x.text p) (fun y hy => hs y (List.mem_cons_of_mem _ hy)) (by
      simp only [jstep]
      omega)

/-- The pre-pass on a list too long for `Py_ssize_t`. -/
theorem prepass_over (seplen : Nat) : ∀ (items : List JItem) (i : Nat) (p : JPass),
    (∀ x ∈ items, x.isStr = true) → (p.sz : Int) ≤ ssizeMax →
    (p.sz + joinSize seplen i items : Int) > ssizeMax →
    joinPrepass seplen i items p =
      .error (.overflowError "join() result is too long for a Python string") := by
  intro items
  induction items with
  | nil =>
    intro i p _ hp hf
    simp only [joinSize] at hf
    omega
  | cons x t ih =>
    intro i p hs hp hf
    simp only [joinSize] at hf
    rw [prepass_step _ _ _ _ _ (hs x List.mem_cons_self)]
    by_cases hc : ((x.text.length + (if i != 0 then seplen else 0) : Nat) : Int) > ssizeMax - p.sz
    · rw [if_pos hc]
    · rw [if_neg hc]
      exact ih (i + 1) (jstep seplen i x.text p) (fun y hy => hs y (List.mem_cons_of_mem _ hy))
        (by
          simp only [jstep]
          omega) (by
          simp only [jstep]
          omega)

/-- The failures, with their exact exceptions and in the order the C checks them. With two or more
items the separator is checked before any item; with one item it is not looked at. The first item
that is not a `str` is named by its index, and an overflow before it wins. A result too long for
`Py_ssize_t` raises instead of wrapping. `%.80s` cuts the type name. -/
def JoinErrors : Prop :=
  (∀ (tp : String) (items : List JItem), 2 ≤ items.length → joinArray (.other tp) items =
    .error (.typeError s!"separator: expected str instance, {tpName80 tp} found")) ∧
  (∀ (sep : JSep) (tp : String), joinArray sep [.other tp] =
    .error (.typeError s!"sequence item {0 + ([] : List JItem).length}: expected str instance, {tpName80 tp} found")) ∧
  (∀ (sep : Str) (pre : List JItem) (tp : String) (post : List JItem),
    2 ≤ (pre ++ .other tp :: post).length → (∀ x ∈ pre, x.isStr = true) →
    (joinSize sep.length 0 pre : Int) ≤ ssizeMax →
    joinArray (.str sep) (pre ++ .other tp :: post) =
      .error (.typeError s!"sequence item {0 + pre.length}: expected str instance, {tpName80 tp} found")) ∧
  (∀ (sep : Str) (items : List JItem), 2 ≤ items.length → (∀ x ∈ items, x.isStr = true) →
    (joinSize sep.length 0 items : Int) > ssizeMax →
    joinArray (.str sep) items =
      .error (.overflowError "join() result is too long for a Python string"))

theorem ssize_nonneg : (0 : Int) ≤ ssizeMax := by decide

theorem joinErrors_proven : JoinErrors := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro tp items hl
    cases items with
    | nil => simp at hl
    | cons x t =>
      cases t with
      | nil => simp at hl
      | cons y r => rw [join_many]
  · intro sep tp
    have := prepass_item 0 tp [] [] 0 { sz := 0, maxchar := 0, useMemcpy := true, last := none }
      (by simp) (by simp [joinSize]; exact ssize_nonneg)
    rw [List.nil_append] at this
    rw [join_other, this]
  · intro sep pre tp post hl hs hf
    obtain ⟨x, y, r, he⟩ : ∃ x y r, pre ++ .other tp :: post = x :: y :: r := by
      cases hq : pre ++ .other tp :: post with
      | nil => rw [hq] at hl; simp at hl
      | cons x t =>
        cases t with
        | nil => rw [hq] at hl; simp at hl
        | cons y r => exact ⟨x, y, r, rfl⟩
    have := prepass_item sep.length tp post pre 0
      { sz := 0, maxchar := strMaxValue sep, useMemcpy := true,
        last := some (canonicalKind sep).width } hs (by simpa using hf)
    rw [he] at this ⊢
    rw [join_many]
    simp only [this]
  · intro sep items hl hs hf
    cases items with
    | nil => simp at hl
    | cons x t =>
      cases t with
      | nil => simp at hl
      | cons y r =>
        have := prepass_over sep.length (x :: y :: r) 0
          { sz := 0, maxchar := strMaxValue sep, useMemcpy := true,
            last := some (canonicalKind sep).width } hs (by simpa using ssize_nonneg)
          (by simpa using hf)
        rw [join_many]
        simp only [this]

theorem iterList_ok (items : List JItem) : iterList (items.map .ok) = .ok items := by
  induction items with
  | nil => rfl
  | cons x t ih =>
    simp only [List.map_cons, iterList, ih]
    rfl

theorem iterList_err (e : PyExc) (post : List (Py JItem)) (pre : List JItem) :
    iterList (pre.map .ok ++ .error e :: post) = .error e := by
  induction pre with
  | nil => rfl
  | cons x t ih =>
    simp only [List.map_cons, List.cons_append, iterList, ih]
    rfl

/-- `PySequence_Fast` in `join`. An iterator gives what a list of its items gives. The first
exception from `next` is what is raised, a `TypeError` included. A `TypeError` from `__iter__` is
replaced by "can only join an iterable", and any other exception from it is kept. -/
def JoinSequence : Prop :=
  (∀ (sep : JSep) (items : List JItem),
    pyUnicodeJoin sep (.iter (items.map .ok)) = pyUnicodeJoin sep (.array items)) ∧
  (∀ (sep : JSep) (pre : List JItem) (e : PyExc) (post : List (Py JItem)),
    pyUnicodeJoin sep (.iter (pre.map .ok ++ .error e :: post)) = .error e) ∧
  (∀ (sep : JSep) (m : String), pyUnicodeJoin sep (.getIterFails (.typeError m)) =
    .error (.typeError "can only join an iterable")) ∧
  (∀ (sep : JSep) (e : PyExc), (∀ m, e ≠ .typeError m) →
    pyUnicodeJoin sep (.getIterFails e) = .error e)

theorem joinSequence_proven : JoinSequence := by
  refine ⟨?_, ?_, fun _ _ => rfl, ?_⟩
  · intro sep items
    simp only [pyUnicodeJoin, sequenceFast, iterList_ok]
  · intro sep pre e post
    simp only [pyUnicodeJoin, sequenceFast, iterList_err]
    rfl
  · intro sep e h
    cases e with
    | typeError m => exact absurd rfl (h m)
    | _ => rfl

theorem pass_mono (seplen : Nat) : ∀ (items : List JItem) (i : Nat) (p q : JPass),
    joinPrepass seplen i items p = .ok q → q.useMemcpy = true → p.useMemcpy = true := by
  intro items
  induction items with
  | nil =>
    intro i p q h hq
    simp only [joinPrepass, Except.ok.injEq] at h
    rw [h]
    exact hq
  | cons x t ih =>
    intro i p q h hq
    cases hs : x.isStr with
    | false =>
      cases x with
      | other n => simp [joinPrepass] at h
      | exact s => simp [JItem.isStr] at hs
      | sub s => simp [JItem.isStr] at hs
    | true =>
      rw [prepass_step _ _ _ _ _ hs] at h
      by_cases hc : ((x.text.length + (if i != 0 then seplen else 0) : Nat) : Int) > ssizeMax - p.sz
      · rw [if_pos hc] at h
        simp at h
      · rw [if_neg hc] at h
        have := ih _ _ _ h hq
        simp only [jstep, Bool.and_eq_true] at this
        exact this.1

theorem width_cap (s : Str) : (kindOfMax (strMaxValue s)).width = (canonicalKind s).width := by
  rw [strMax_need, kind_need]
  rfl

theorem width_max {a b w : Nat} (ha : (kindOfMax a).width = w) (hb : (kindOfMax b).width = w) :
    (kindOfMax (max a b)).width = w := by
  by_cases h : a ≤ b
  · rw [Nat.max_eq_right h]
    exact hb
  · rw [Nat.max_eq_left (by omega)]
    exact ha

/-- What `use_memcpy` says when it stays true. -/
theorem memcpy_pass (seplen : Nat) : ∀ (items : List JItem) (i : Nat) (p q : JPass) (w : Nat),
    p.last = some w → (kindOfMax p.maxchar).width = w → joinPrepass seplen i items p = .ok q →
    q.useMemcpy = true →
    (∀ x ∈ items, (canonicalKind x.text).width = w) ∧ (kindOfMax q.maxchar).width = w := by
  intro items
  induction items with
  | nil =>
    intro i p q w _ hm h _
    simp only [joinPrepass, Except.ok.injEq] at h
    subst h
    exact ⟨by simp, hm⟩
  | cons x t ih =>
    intro i p q w hl hm h hq
    cases hs : x.isStr with
    | false =>
      cases x with
      | other n => simp [joinPrepass] at h
      | exact s => simp [JItem.isStr] at hs
      | sub s => simp [JItem.isStr] at hs
    | true =>
      rw [prepass_step _ _ _ _ _ hs] at h
      by_cases hc : ((x.text.length + (if i != 0 then seplen else 0) : Nat) : Int) > ssizeMax - p.sz
      · rw [if_pos hc] at h
        simp at h
      · rw [if_neg hc] at h
        have hu := pass_mono seplen t _ _ _ h hq
        simp only [jstep, Bool.and_eq_true, hl, beq_iff_eq] at hu
        have hw : w = (canonicalKind x.text).width := hu.2
        have hmax : (kindOfMax (jstep seplen i x.text p).maxchar).width = w :=
          width_max hm (by rw [width_cap, hw])
        obtain ⟨a, b⟩ := ih (i + 1) (jstep seplen i x.text p) q w (by simp only [jstep]; rw [hw]) hmax h hq
        refine ⟨?_, b⟩
        intro y hy
        rcases List.mem_cons.1 hy with rfl | hy
        · exact hw.symm
        · exact a y hy

/-- Why the `memcpy` path is valid. It copies `kind * len` bytes from each part into the result, so
every part must have the byte width of the result. `ascii` and `latin-1` are different kinds of the
same width, which the comparison of `PyUnicode_KIND` allows. A pre-pass that ignored the kinds
fails this. -/
def JoinMemcpySafe : Prop :=
  ∀ (sep : Str) (items : List JItem) (t : Str) (k : Kind), 2 ≤ items.length →
    joinArray (.str sep) items = .ok (.fresh t k true) →
    (canonicalKind sep).width = k.width ∧ ∀ x ∈ items, (canonicalKind x.text).width = k.width

theorem joinMemcpySafe_proven : JoinMemcpySafe := by
  intro sep items t k hl h
  cases items with
  | nil => simp at hl
  | cons x r =>
    cases r with
    | nil => simp at hl
    | cons y u =>
      rw [join_many] at h
      simp only at h
      cases hp : joinPrepass sep.length 0 (x :: y :: u)
          { sz := 0, maxchar := strMaxValue sep, useMemcpy := true,
            last := some (canonicalKind sep).width } with
      | error e =>
        rw [hp] at h
        simp at h
      | ok q =>
        rw [hp] at h
        simp only [Except.ok.injEq, JOut.fresh.injEq] at h
        obtain ⟨_, hk, hm⟩ := h
        obtain ⟨a, b⟩ := memcpy_pass sep.length _ 0 _ q (canonicalKind sep).width rfl (width_cap sep) hp hm
        rw [← hk, b]
        exact ⟨rfl, a⟩

end PyLean.UnicodeObj
