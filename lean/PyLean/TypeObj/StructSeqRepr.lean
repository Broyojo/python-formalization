import PyLean.TypeObj.StructSeqC

/-!
# `structseq_repr`: what it writes (Objects/structseq.c:273-339, CPython 3.15.2)

`ReprShape`: for every type and object, `repr(s)` is exactly
`tp_name(m0=repr(v0), m1=repr(v1), ...)` over the `Py_SIZE` visible items, where `m_i` is
`tp_members[i].name`, or else the first failure in that order: `tp_name` or a member name that is
not UTF-8, an item's `__repr__` raising, or `SystemError` when the visible fields outnumber the
members. `tp_name` is written whole (3.15 has no truncation), and the loop never reads
`tp_members` past its sentinel.

`ReprLabelsMatchAttrs`, refuted: the label written before item `i` names the attribute that reads
item `i`, as in `namedtuple`. `tp_members` skips unnamed fields, so after an unnamed visible field
every label is shifted.
-/

namespace PyLean.TypeObj.StructSeq

open PyLean PyLean.UnicodeObj

variable {α : Type}

/-- The first failure of a list of steps, or their texts concatenated. -/
def catAll : List (CRes Str) → CRes Str
  | [] => .ok []
  | r :: rs => do
    let s ← r
    let t ← catAll rs
    .ok (s ++ t)

def CRes.map {β γ : Type} (f : β → γ) : CRes β → CRes γ
  | .ok a => .ok (f a)
  | .exc e => .exc e
  | .nullNoExc => .nullNoExc
  | .ub w => .ub w

/-- What `repr()` of an item gives: `<NULL>` for a `NULL` slot, junk is dereferenced. -/
def itemText (rep : α → Py Str) : Slot α → CRes Str
  | .null => .ok (lit "<NULL>")
  | .val a => CRes.ofPy (rep a)
  | .junk => .ub "structseq_repr: junk item"

/-- `name=repr(value)` for visible field `i`, labelled with `tp_members[i].name`. -/
def fieldText (t : CType) (o : CObj α) (rep : α → Py Str) (i : Nat) : CRes Str :=
  if h : i < t.members.length then do
    let nm ← CRes.ofPy (utf8Decode t.members[i].name .strict)
    let s ← pssGetItem o i
    let r ← itemText rep s
    .ok (nm ++ [chEq] ++ r)
  else .exc (systemError s!"~In structseq_repr(), member {i} name is NULL for type {t.nameStr}")

/-- `", "` before every field but the first. -/
def sepOf (i : Nat) : Str := if i = 0 then [] else [chComma, chSpace]

/-- The specification: `tp_name(` the fields, separated by `", "`, `)`. -/
def reprSpec (t : CType) (o : CObj α) (rep : α → Py Str) : CRes Str :=
  match utf8Decode t.name .strict with
  | .error e => .exc e
  | .ok nm =>
    (catAll ((List.range o.size).map fun i => (fieldText t o rep i).map (sepOf i ++ ·))).map
      (fun body => nm ++ [chLParen] ++ body ++ [chRParen])

/-- C strings: the bytes of a member name stop before the NUL. -/
def MemberNamesCStr (t : CType) : Prop := ∀ m ∈ t.members, ∀ c ∈ m.name, c ≠ 0

/-- For every type whose member names are C strings (their bytes before the NUL), every object
and every behaviour of the items' `__repr__`, `structseq_repr` returns exactly `reprSpec`; in
particular it never reads `tp_members` past the sentinel. -/
def ReprShape : Prop :=
  ∀ (α : Type) (t : CType) (o : CObj α) (rep : α → Py Str), MemberNamesCStr t →
    structseqRepr t o rep = reprSpec t o rep ∧
    structseqRepr t o rep ≠ .ub "structseq_repr: tp_members past the sentinel"

/-! ### The writer, as text -/

/-- `c` is the writer outcome of a step whose text outcome is `d`, starting from text `base`. -/
def TextRel : CRes UWriter → Str → CRes Str → Prop
  | c, base, .ok s => ∃ w', c = .ok w' ∧ w'.text = base ++ s
  | c, _, .exc e => c = .exc e
  | c, _, .nullNoExc => c = .nullNoExc
  | c, _, .ub x => c = .ub x

theorem textRel_bind {c : CRes UWriter} {base : Str} {d : CRes Str} (h : TextRel c base d)
    {f : UWriter → CRes UWriter} {g : Str → CRes Str}
    (hf : ∀ w s, w.text = base ++ s → TextRel (f w) w.text (g s)) :
    TextRel (c >>= f) base (d >>= fun s => (g s).map (s ++ ·)) := by
  cases d with
  | ok s =>
    obtain ⟨w', rfl, hw⟩ := h
    have := hf w' s hw
    simp only [CRes.bind_ok]
    rw [hw] at this
    cases hg : g s with
    | ok r =>
      rw [hg] at this
      obtain ⟨w'', h1, h2⟩ := this
      exact ⟨w'', h1, by rw [h2]; simp [List.append_assoc]⟩
    | exc e => rw [hg] at this; exact this
    | nullNoExc => rw [hg] at this; exact this
    | ub x => rw [hg] at this; exact this
  | exc e => simp only [TextRel] at h; subst h; rfl
  | nullNoExc => simp only [TextRel] at h; subst h; rfl
  | ub x => simp only [TextRel] at h; subst h; rfl

theorem textRel_ok (w : UWriter) : TextRel (.ok w) w.text (.ok []) := ⟨w, rfl, by simp⟩

theorem wop_rel (w : UWriter) (op : WOp) : TextRel (wop w op) w.text (CRes.ofPy (opText op)) := by
  have h := applyOp_agrees w op
  unfold wop
  cases ht : opText op with
  | ok s =>
    rw [ht] at h
    obtain ⟨h1, n, h2⟩ := h
    cases happ : applyOp w op with
    | mk w' r =>
      rw [happ] at h1 h2
      simp only at h1 h2
      subst h2
      exact ⟨w', rfl, h1⟩
  | error e =>
    rw [ht] at h
    obtain ⟨_, h2⟩ := h
    cases happ : applyOp w op with
    | mk w' r =>
      rw [happ] at h2
      simp only at h2
      subst h2
      rfl

theorem char_text (c : Nat) (hc : c ≤ maxUnicode) : opText (.char c) = .ok [c] := by
  simp only [opText]
  rw [if_neg (by omega)]

theorem takeWhile_ne0 (b : List Nat) (hb : ∀ c ∈ b, c ≠ 0) : b.takeWhile (· != 0) = b := by
  induction b with
  | nil => rfl
  | cons x xs ih =>
    have hx : (x != 0) = true := by simpa using hb x (by simp)
    simp only [List.takeWhile, hx]
    rw [ih (fun c hc => hb c (by simp [hc]))]

theorem utf8_text (b : Bytes) (hb : ∀ c ∈ b, c ≠ 0) : opText (.utf8 b (-1)) = utf8Decode b .strict := by
  simp only [opText, sizedBytes]
  rw [if_pos (by omega), takeWhile_ne0 b hb]

theorem utf8_len_text (b : Bytes) : opText (.utf8 b b.length) = utf8Decode b .strict := by
  simp only [opText, sizedBytes]
  rw [if_neg (by omega)]
  simp

theorem wop_char (w : UWriter) (c : Nat) (hc : c ≤ maxUnicode) :
    ∃ w', wop w (.char c) = .ok w' ∧ w'.text = w.text ++ [c] := by
  have := wop_rel w (.char c)
  rw [char_text c hc] at this
  exact this

/-- Relabel the base of a successful relation. -/
theorem textRel_ofPy_ok {c : CRes UWriter} {base : Str} {r : Py Str} (h : TextRel c base (CRes.ofPy r)) :
    TextRel c base (CRes.ofPy r) := h

theorem writeReprSlot_rel (rep : α → Py Str) (w : UWriter) (s : Slot α) :
    TextRel (writeReprSlot rep w s) w.text (itemText rep s) := by
  cases s with
  | null => exact ⟨_, rfl, writeAscii_text w _⟩
  | val a =>
    simp only [writeReprSlot, itemText]
    cases rep a with
    | ok s => exact ⟨_, rfl, writeText_text w s⟩
    | error e => rfl
  | junk => rfl

theorem pssGetItem_nat (o : CObj α) (i : Nat) :
    pssGetItem o (i : Int) = readSlot o.slots i "PyStructSequence_GetItem: past the block" := by
  unfold pssGetItem
  rw [if_neg (by omega)]
  rfl

theorem memberName_lt (ms : List Member) (i : Nat) (h : i < ms.length) (w : String) :
    memberName ms (i : Int) w = .ok (.name ms[i].name) := by
  simp [memberName, h]

theorem memberName_eq (ms : List Member) (w : String) :
    memberName ms (ms.length : Int) w = .ok .null := by
  simp [memberName]

theorem catAll_cons (r : CRes Str) (rs : List (CRes Str)) :
    catAll (r :: rs) = (r >>= fun s => (catAll rs).map (s ++ ·)) := by
  cases r <;> simp [catAll] <;> rename_i s <;> cases catAll rs <;> rfl

theorem bind_map_eq {β : Type} (d : CRes β) (g : β → CRes Str) :
    (d >>= fun s => g s) = d.bind g := rfl

theorem reprSep_ok (i : Nat) (w : UWriter) : ∃ w1, reprSep i w = .ok w1 ∧ w1.text = w.text ++ sepOf i := by
  unfold reprSep sepOf
  by_cases hi : i > 0
  · rw [if_pos hi, if_neg (by omega)]
    obtain ⟨w1, h1, t1⟩ := wop_char w chComma (by decide)
    obtain ⟨w2, h2, t2⟩ := wop_char w1 chSpace (by decide)
    refine ⟨w2, ?_, ?_⟩
    · show (wop w (.char chComma)).bind (fun w => wop w (.char chSpace)) = .ok w2
      rw [h1]; exact h2
    · rw [t2, t1]; simp
  · rw [if_neg hi, if_pos (by omega)]
    exact ⟨w, rfl, by simp⟩

/-- The name, `=`, the item. -/
theorem reprNameValue_rel (o : CObj α) (rep : α → Py Str) (i : Nat) (b : Bytes) (hb : ∀ c ∈ b, c ≠ 0)
    (w : UWriter) :
    TextRel (reprNameValue o rep i b w) w.text (do
      let nm ← CRes.ofPy (utf8Decode b .strict)
      let s ← pssGetItem o i
      let r ← itemText rep s
      .ok (nm ++ [chEq] ++ r)) := by
  have h1 := wop_rel w (.utf8 b (-1))
  rw [utf8_text b hb] at h1
  unfold reprNameValue
  cases hd : utf8Decode b .strict with
  | error e =>
    rw [hd] at h1
    simp only [CRes.ofPy, TextRel] at h1 ⊢
    rw [h1]; rfl
  | ok nm =>
    rw [hd] at h1
    obtain ⟨w2, e2, t2⟩ := h1
    obtain ⟨w3, e3, t3⟩ := wop_char w2 chEq (by decide)
    simp only [CRes.ofPy, CRes.bind_ok]
    rw [e2]
    show TextRel ((wop w2 (.char chEq)).bind fun w => (pssGetItem o i).bind fun v => writeReprSlot rep w v) _ _
    rw [e3]
    simp only [CRes.bind]
    rw [pssGetItem_nat]
    unfold readSlot
    by_cases hi : i < o.slots.length
    · rw [dif_pos hi]
      simp only [CRes.bind_ok]
      have h4 := writeReprSlot_rel rep w3 o.slots[i]
      cases hit : itemText rep o.slots[i] with
      | ok r =>
        rw [hit] at h4
        obtain ⟨w4, e4, t4⟩ := h4
        refine ⟨w4, e4, ?_⟩
        rw [t4, t3, t2]; simp [List.append_assoc]
      | exc e => rw [hit] at h4; exact h4
      | nullNoExc => rw [hit] at h4; exact h4
      | ub x => rw [hit] at h4; exact h4
    · rw [dif_neg hi]
      rfl

/-- One field: the separator, the label, `=`, the item. -/
theorem reprField_rel (t : CType) (ht : MemberNamesCStr t) (o : CObj α) (rep : α → Py Str)
    (i : Nat) (hi : i ≤ t.members.length) (w : UWriter) :
    TextRel (reprField t o rep i w) w.text ((fieldText t o rep i).map (sepOf i ++ ·)) := by
  obtain ⟨w1, e1, t1⟩ := reprSep_ok i w
  unfold reprField
  rw [e1]
  simp only [CRes.bind_ok]
  unfold fieldText
  by_cases hl : i < t.members.length
  · rw [memberName_lt _ _ hl, dif_pos hl]
    simp only [CRes.bind_ok]
    have hb : ∀ c ∈ t.members[i].name, c ≠ 0 := ht _ (List.getElem_mem hl)
    have h := reprNameValue_rel o rep i _ hb w1
    rw [t1] at h
    revert h
    generalize (do
      let nm ← CRes.ofPy (utf8Decode t.members[i].name .strict)
      let s ← pssGetItem o i
      let r ← itemText rep s
      CRes.ok (nm ++ [chEq] ++ r) : CRes Str) = d
    intro h
    cases d with
    | ok s =>
      obtain ⟨w', e', t'⟩ := h
      exact ⟨w', e', by rw [t']; simp [CRes.map, List.append_assoc]⟩
    | exc e => exact h
    | nullNoExc => exact h
    | ub x => exact h
  · have he : i = t.members.length := by omega
    rw [dif_neg hl]
    subst he
    rw [memberName_eq]
    rfl

/-- The loop from field `i`, for `i ≤ #members`: fields past the members are never reached. -/
theorem reprLoop_rel (t : CType) (ht : MemberNamesCStr t) (o : CObj α) (rep : α → Py Str) :
    ∀ (fuel i : Nat) (w : UWriter), i ≤ t.members.length →
      TextRel (reprLoop t o rep fuel i w) w.text
        (catAll ((List.range' i fuel).map fun j => (fieldText t o rep j).map (sepOf j ++ ·))) := by
  intro fuel
  induction fuel with
  | zero => intro i w _; exact ⟨w, rfl, by simp [catAll]⟩
  | succ fuel ih =>
    intro i w hi
    have hf := reprField_rel t ht o rep i hi w
    simp only [reprLoop, List.range'_succ, List.map_cons, catAll_cons]
    by_cases hl : i < t.members.length
    · have hrest : ∀ w', TextRel (reprLoop t o rep fuel (i + 1) w') w'.text
          (catAll ((List.range' (i + 1) fuel).map fun j => (fieldText t o rep j).map (sepOf j ++ ·))) :=
        fun w' => ih (i + 1) w' (by omega)
      exact textRel_bind hf (fun w' _ _ => hrest w')
    · -- field `i` is the sentinel: it fails, and nothing after it runs
      have he : i = t.members.length := by omega
      have hft : fieldText t o rep i = .exc (systemError s!"~In structseq_repr(), member {i} name is NULL for type {t.nameStr}") := by
        unfold fieldText; rw [dif_neg hl]
      rw [hft] at hf ⊢
      simp only [CRes.map, TextRel] at hf
      simp only [CRes.map, CRes.bind_exc, TextRel]
      show (reprField t o rep i w).bind _ = _
      rw [hf]; rfl

theorem finish_fst (w : UWriter) : w.finish.1 = w.text := by
  unfold UWriter.finish
  split
  · simp_all
  · rename_i h; split <;> simp [h]
  · simp_all

theorem reprShape_eq (t : CType) (ht : MemberNamesCStr t) (o : CObj α) (rep : α → Py Str) :
    structseqRepr t o rep = reprSpec t o rep := by
  have hc : writerCreate ((t.name.length : Int) + 1 + (o.size : Int) * 5 + 1) = .ok { cap := 127 } := by
    unfold writerCreate
    rw [if_neg (by omega), if_pos (by omega)]
  unfold structseqRepr reprSpec
  rw [hc]
  simp only [CRes.ofPy, CRes.bind_ok]
  have h1 := wop_rel { cap := 127 } (.utf8 t.name t.name.length)
  rw [utf8_len_text] at h1
  cases hd : utf8Decode t.name .strict with
  | error e =>
    rw [hd] at h1
    simp only [CRes.ofPy, TextRel] at h1
    rw [h1]; rfl
  | ok nm =>
    rw [hd] at h1
    obtain ⟨w1, e1, t1⟩ := h1
    rw [e1]
    simp only [CRes.bind_ok]
    obtain ⟨w2, e2, t2⟩ := wop_char w1 chLParen (by decide)
    rw [e2]
    simp only [CRes.bind_ok]
    have h3 := reprLoop_rel t ht o rep o.size 0 w2 (Nat.zero_le _)
    rw [← List.range_eq_range'] at h3
    revert h3
    generalize catAll ((List.range o.size).map fun j => (fieldText t o rep j).map (sepOf j ++ ·)) = d
    intro h3
    cases d with
    | ok body =>
      obtain ⟨w3, e3, t3⟩ := h3
      rw [e3]
      simp only [CRes.bind_ok]
      obtain ⟨w4, e4, t4⟩ := wop_char w3 chRParen (by decide)
      rw [e4]
      simp only [CRes.bind_ok, CRes.map, finish_fst, t4, t3, t2, t1]
      simp
    | exc e => simp only [TextRel] at h3; rw [h3]; rfl
    | nullNoExc => simp only [TextRel] at h3; rw [h3]; rfl
    | ub x => simp only [TextRel] at h3; rw [h3]; rfl

def sentinelTag : String := "structseq_repr: tp_members past the sentinel"

theorem map_ne_tag {f : Str → Str} {d : CRes Str} (h : d ≠ .ub sentinelTag) : d.map f ≠ .ub sentinelTag := by
  cases d <;> simp_all [CRes.map]

theorem fieldText_ne (t : CType) (o : CObj α) (rep : α → Py Str) (i : Nat) :
    fieldText t o rep i ≠ .ub sentinelTag := by
  unfold fieldText
  split
  · cases utf8Decode _ .strict with
    | error e => simp [CRes.ofPy]
    | ok nm =>
      simp only [CRes.ofPy, CRes.bind_ok]
      rw [pssGetItem_nat]
      unfold readSlot
      split
      · simp only [CRes.bind_ok]
        rename_i hi
        cases o.slots[i] with
        | null => simp [itemText]
        | val a =>
          simp only [itemText, CRes.ofPy]
          cases rep a <;> simp
        | junk => simp [itemText, sentinelTag]
      · simp [sentinelTag]
  · simp

theorem catAll_ne (l : List (CRes Str)) (h : ∀ d ∈ l, d ≠ .ub sentinelTag) : catAll l ≠ .ub sentinelTag := by
  induction l with
  | nil => simp [catAll]
  | cons d ds ih =>
    rw [catAll_cons]
    have hd := h d (by simp)
    have hr := ih (fun x hx => h x (by simp [hx]))
    cases d with
    | ok s => simp only [CRes.bind_ok]; exact map_ne_tag hr
    | exc e => simp
    | nullNoExc => simp
    | ub x => simp only [CRes.bind_ub]; exact hd

theorem reprShape_proven : ReprShape := by
  intro α t o rep ht
  refine ⟨reprShape_eq t ht o rep, ?_⟩
  rw [reprShape_eq t ht o rep]
  unfold reprSpec
  split
  · simp
  · apply map_ne_tag
    apply catAll_ne
    intro d hd
    simp only [List.mem_map, List.mem_range] at hd
    obtain ⟨i, _, rfl⟩ := hd
    exact map_ne_tag (fieldText_ne t o rep i)

end PyLean.TypeObj.StructSeq
