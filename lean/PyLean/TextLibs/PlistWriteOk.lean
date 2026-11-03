import PyLean.TextLibs.PlistSpec

/-! `dumps(fmt=FMT_BINARY)` succeeds on every supported object graph. -/

namespace PyLean.TextLibs.Plist

open PyLean PyLean.TextLibs

/-- What the writer accepts: ints in -2**63..2**64-1, UIDs in 0..2**64-1, strs without lone
surrogates, no datetimes (not covered) and no other types; dicts whose keys are all `str`
(or `skipkeys`); and references to cells of the heap. -/
def Supported (H : WHeap) (cfg : WCfg) : Prop :=
  ∀ c, c < H.length → match H.getD c .none with
    | .int v => -2 ^ 63 ≤ v ∧ v < 2 ^ 64
    | .uid d => 0 ≤ d ∧ d < 2 ^ 64
    | .str s => ∀ ch ∈ s, UnicodeObj.isSurrogate ch = false
    | .date _ _ => False
    | .other _ _ => False
    | .list xs => ∀ x ∈ xs, x < H.length
    | .tuple xs => ∀ x ∈ xs, x < H.length
    | .dict items => (∀ q ∈ items, q.1 < H.length ∧ q.2 < H.length) ∧
        (cfg.skipkeys = true ∨ ∀ q ∈ items, (keyStr H q.1).isSome = true)
    | .fdict items => (∀ q ∈ items, q.1 < H.length ∧ q.2 < H.length) ∧
        (cfg.skipkeys = true ∨ ∀ q ∈ items, (keyStr H q.1).isSome = true)
    | _ => True

/-- The cells of the heap not numbered yet. -/
def notSeen (H : WHeap) (st : WState) : Nat :=
  ((List.range H.length).filter (fun c => (lookupW H st c).isNone)).length

theorem filter_len_le (p q : Nat → Bool) (h : ∀ x, q x = true → p x = true) :
    ∀ l : List Nat, (l.filter q).length ≤ (l.filter p).length
  | [] => by simp
  | a :: l => by
    have ih := filter_len_le p q h l
    by_cases hq : q a = true
    · simp [List.filter_cons, hq, h a hq]; omega
    · by_cases hp : p a = true
      · simp [List.filter_cons, hq, hp]; omega
      · simp [List.filter_cons, hq, hp]; omega

theorem filter_len_lt (p q : Nat → Bool) (h : ∀ x, q x = true → p x = true) (c : Nat)
    (hp : p c = true) (hq : q c = false) : ∀ l : List Nat, c ∈ l →
      (l.filter q).length < (l.filter p).length
  | [], hc => by simp at hc
  | a :: l, hc => by
    have hle := filter_len_le p q h l
    simp at hc
    rcases hc with rfl | hc
    · simp [List.filter_cons, hp, hq]; omega
    · have ih := filter_len_lt p q h c hp hq l hc
      by_cases hqa : q a = true
      · simp [List.filter_cons, hqa, h a hqa]; omega
      · by_cases hpa : p a = true
        · simp [List.filter_cons, hqa, hpa]; omega
        · simp [List.filter_cons, hqa, hpa]; omega

theorem notSeen_ext {H : WHeap} {st st' : WState} (h : WExt st st') : notSeen H st' ≤ notSeen H st := by
  apply filter_len_le
  intro x hx
  cases hl : lookupW H st x with
  | none => rfl
  | some i => rw [lookup_ext h x i hl] at hx; cases hx

theorem notSeen_lt {H : WHeap} {st st' : WState} (h : WExt st st') (c : Nat) (hc : c < H.length)
    (h1 : lookupW H st c = none) (h2 : (lookupW H st' c).isSome = true) : notSeen H st' < notSeen H st := by
  apply filter_len_lt _ _ _ c (by simp [h1]) (by simpa using h2) _ (by simp [hc])
  intro x hx
  cases hl : lookupW H st x with
  | none => rfl
  | some i => rw [lookup_ext h x i hl] at hx; cases hx

/-- The objects numbered are cells of the heap. -/
def InHeap (H : WHeap) (st : WState) : Prop := ∀ c ∈ st.objlist, c < H.length

theorem dictItems_ok (H : WHeap) (cfg : WCfg) (items : List (Nat × Nat))
    (h : cfg.skipkeys = true ∨ ∀ q ∈ items, (keyStr H q.1).isSome = true) :
    ∃ kept, writtenItems H cfg items = .ok kept ∧ (∀ q ∈ kept, q ∈ items) := by
  have hk : ∀ its : List (Nat × Nat), (cfg.skipkeys = true ∨ ∀ q ∈ its, (keyStr H q.1).isSome = true) →
      ∃ kept, keptItems H cfg.skipkeys its = .ok kept ∧ ∀ q ∈ kept, q ∈ its := by
    intro its
    induction its with
    | nil => intro _; exact ⟨[], rfl, by simp⟩
    | cons q its ih =>
      intro hq
      obtain ⟨kept, h1, h2⟩ := ih (hq.imp id (fun h x hx => h x (by simp [hx])))
      rcases q with ⟨k, v⟩
      simp only [keptItems]
      by_cases hn : (keyStr H k).isNone = true
      · rw [if_pos hn]
        rcases hq with hs | hs
        · rw [if_pos hs]; exact ⟨kept, h1, fun x hx => by simp [h2 x hx]⟩
        · have := hs (k, v) (by simp); simp_all
      · rw [if_neg hn]
        refine ⟨(k, v) :: kept, by simp [h1, bind, Except.bind, pure, Except.pure], ?_⟩
        intro x hx; simp at hx; rcases hx with rfl | hx
        · simp
        · simp [h2 x hx]
  unfold writtenItems dictItems
  by_cases hs : cfg.sortKeys = true
  · by_cases hsk : cfg.skipkeys = true
    · obtain ⟨kept, h1, h2⟩ := hk (sortItems H (items.filter fun (k, _) => (keyStr H k).isSome)) (Or.inl hsk)
      rw [hsk] at h1
      refine ⟨kept, by simp only [hs, hsk, ↓reduceIte, bind, Except.bind]; exact h1, fun q hq => ?_⟩
      have := h2 q hq
      have hm := (List.mergeSort_perm _ _).mem_iff.mp this
      exact (List.mem_filter.mp hm).1
    · have hall : ∀ q ∈ items, (keyStr H q.1).isSome = true := by
        rcases h with h | h
        · exact absurd h hsk
        · exact h
      have hany : items.any (fun (k, _) => (keyStr H k).isNone) = false := by
        simp only [List.any_eq_false]
        intro q hq
        rcases q with ⟨k, v⟩
        have := hall (k, v) hq
        simp only at this ⊢
        cases hk : keyStr H k <;> simp_all
      obtain ⟨kept, h1, h2⟩ := hk (sortItems H items) (Or.inr (fun q hq =>
        hall q ((List.mergeSort_perm _ _).mem_iff.mp hq)))
      have hsk' : cfg.skipkeys = false := by simpa using hsk
      rw [hsk'] at h1
      refine ⟨kept, by simp only [hs, hsk', hany, Bool.false_eq_true, ↓reduceIte, bind, Except.bind]; exact h1, fun q hq =>
        (List.mergeSort_perm _ _).mem_iff.mp (h2 q hq)⟩
  · obtain ⟨kept, h1, h2⟩ := hk items h
    have hs' : cfg.sortKeys = false := by simpa using hs
    exact ⟨kept, by simp only [hs', Bool.false_eq_true, ↓reduceIte, bind, Except.bind]; exact h1, h2⟩


theorem wloop_ok (H : WHeap) (cfg : WCfg) (r : Nat)
    (IH : ∀ c st, WInv H st → InHeap H st → c < H.length → notSeen H st + 2 ≤ r →
      ∃ st', flattenR H cfg r c st = .ok st' ∧ InHeap H st') :
    ∀ xs st, WInv H st → InHeap H st → (∀ x ∈ xs, x < H.length) → notSeen H st + 2 ≤ r →
      ∃ st', wloop (fun x st => flattenR H cfg r x st) xs st = .ok st' ∧ InHeap H st'
  | [], st, _, hh, _, _ => ⟨st, rfl, hh⟩
  | x :: xs, st, hI, hh, hx, hr => by
    obtain ⟨st1, h1, hh1⟩ := IH x st hI hh (hx x (by simp)) hr
    obtain ⟨hI1, he1, _, _⟩ := flatten_spec H cfg r x st st1 hI h1
    obtain ⟨st', h', hh'⟩ := wloop_ok H cfg r IH xs st1 hI1 hh1 (fun y hy => hx y (by simp [hy]))
      (by have := notSeen_ext (H := H) he1; omega)
    exact ⟨st', by simp only [wloop, h1, bind, Except.bind]; exact h', hh'⟩

theorem written_split (H : WHeap) (cfg : WCfg) (items kept : List (Nat × Nat))
    (h : writtenItems H cfg items = .ok kept) :
    ∃ its, dictItems H cfg items = .ok its ∧ keptItems H cfg.skipkeys its = .ok kept := by
  unfold writtenItems at h
  simp only [bind, Except.bind] at h
  cases hd : dictItems H cfg items with
  | error e => rw [hd] at h; cases h
  | ok its => rw [hd] at h; exact ⟨its, rfl, h⟩

theorem flatten_ok (H : WHeap) (cfg : WCfg) (hS : Supported H cfg) :
    ∀ r c st, WInv H st → InHeap H st → c < H.length → notSeen H st + 2 ≤ r →
      ∃ st', flattenR H cfg r c st = .ok st' ∧ InHeap H st'
  | 0, _, _, _, _, _, h => by omega
  | r + 1, c, st, hI, hh, hc, hr => by
    simp only [flattenR]
    rw [seen_eq]
    cases hl : lookupW H st c with
    | some i => exact ⟨st, by simp, hh⟩
    | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨hI2, he2, hl2⟩ := winv_append H st c hI hl
      generalize hst2 : (if isScalar H c = true then
          (⟨st.objlist ++ [c], st.objtable ++ [(c, st.objlist.length)], st.objidtable⟩ : WState)
        else ⟨st.objlist ++ [c], st.objtable, st.objidtable ++ [(objId H c, st.objlist.length)]⟩) = st2
        at hI2 he2 hl2
      have hst2' : st2.objlist = st.objlist ++ [c] := by rw [← hst2]; split <;> rfl
      have hh2 : InHeap H st2 := by
        intro x hx; rw [hst2'] at hx; simp at hx; rcases hx with hx | rfl
        · exact hh x hx
        · exact hc
      have hns : notSeen H st2 + 1 ≤ notSeen H st := notSeen_lt he2 c hc hl (by rw [hl2]; rfl)
      have hh' : (if (scalarType (H.getD c .none)).isSome = true then
          (⟨st.objlist ++ [c], st.objtable ++ [(c, st.objlist.length)], st.objidtable⟩ : WState)
        else ⟨st.objlist ++ [c], st.objtable, st.objidtable ++ [(objId H c, st.objlist.length)]⟩) = st2 := by
        rw [← hst2]; rfl
      rw [hh']
      have IH := flatten_ok H cfg hS r
      have hSc := hS c hc
      cases ho : H.getD c .none with
      | dict items | fdict items =>
        rw [ho] at hSc
        obtain ⟨hin, hkey⟩ := hSc
        obtain ⟨kept, hk, hsub⟩ := dictItems_ok H cfg items hkey
        obtain ⟨its, hd, hkp⟩ := written_split H cfg items kept hk
        obtain ⟨r', rfl⟩ : ∃ j, r = j + 1 := ⟨r - 1, by omega⟩
        obtain ⟨st', h', hh''⟩ := wloop_ok H cfg (r' + 1) IH (kept.map (·.1) ++ kept.map (·.2)) st2 hI2 hh2 (by
          intro x hx; simp at hx
          rcases hx with ⟨b, hb⟩ | ⟨a, ha⟩
          · exact (hin _ (hsub _ hb)).1
          · exact (hin _ (hsub _ ha)).2) (by omega)
        refine ⟨st', ?_, hh''⟩
        simp only [dictItemsR, call, hd, hkp, bind, Except.bind]
        exact h'
      | list xs | tuple xs =>
        rw [ho] at hSc
        obtain ⟨st', h', hh''⟩ := wloop_ok H cfg r IH xs st2 hI2 hh2 hSc (by omega)
        exact ⟨st', h', hh''⟩
      | _ => exact ⟨st2, rfl, hh2⟩


theorem getrefnum_of_lookup (k : Nat) (H : WHeap) (st : WState) (c n : Nat) (h : lookupW H st c = some n) :
    getrefnumR (k + 1) H st c = .ok n := by
  unfold lookupW isScalar at h
  simp only [getrefnumR, call]
  split at h <;> simp_all

theorem mapM_ok {α : Type} (f : α → Py Nat) :
    ∀ l : List α, (∀ x ∈ l, ∃ n, f x = .ok n) → ∃ rs, l.mapM f = .ok rs
  | [], _ => ⟨[], rfl⟩
  | x :: l, h => by
    obtain ⟨n, hn⟩ := h x (by simp)
    obtain ⟨rs, hrs⟩ := mapM_ok f l (fun y hy => h y (by simp [hy]))
    exact ⟨n :: rs, by simp [List.mapM_cons, hn, hrs, bind, Except.bind, pure, Except.pure]⟩

theorem mapM_ne_error {α : Type} (f : α → Py Nat) (l : List α) (h : ∀ x ∈ l, ∃ n, f x = .ok n)
    (e : PyExc) : l.mapM f ≠ .error e := by
  obtain ⟨rs, hrs⟩ := mapM_ok f l h
  rw [hrs]; intro h'; cases h'

theorem writeInt_ok (v : Int) (h1 : -2 ^ 63 ≤ v) (h2 : v < 2 ^ 64) : ∃ b, writeInt v = .ok b := by
  unfold writeInt
  by_cases h0 : v < 0
  · rw [if_pos h0, if_pos h1]; exact ⟨_, rfl⟩
  · rw [if_neg h0]
    by_cases a : v < 2 ^ 8
    · rw [if_pos a]; exact ⟨_, rfl⟩
    · rw [if_neg a]
      by_cases b : v < 2 ^ 16
      · rw [if_pos b]; exact ⟨_, rfl⟩
      · rw [if_neg b]
        by_cases c : v < 2 ^ 32
        · rw [if_pos c]; exact ⟨_, rfl⟩
        · rw [if_neg c]
          by_cases d : v < 2 ^ 63
          · rw [if_pos d]; exact ⟨_, rfl⟩
          · rw [if_neg d, if_pos h2]; exact ⟨_, rfl⟩

theorem writeObject_ok (k : Nat) (H : WHeap) (cfg : WCfg) (rs : Nat) (st : WState) (c : Nat)
    (hS : Supported H cfg) (hc : c < H.length) (hl : (lookupW H st c).isSome = true)
    (hcd : ChildrenDone H cfg st c) : ∃ out, writeObjectR (k + 2) H cfg rs st c = .ok out := by
  obtain ⟨n, hn⟩ : ∃ n, lookupW H st c = some n := by
    cases h : lookupW H st c with
    | none => rw [h] at hl; cases hl
    | some n => exact ⟨n, rfl⟩
  have hlook : ∀ x, (lookupW H st x).isSome = true → ∃ m, getrefnumR (k + 1) H st x = .ok m := by
    intro x hx
    cases h : lookupW H st x with
    | none => rw [h] at hx; cases hx
    | some m => exact ⟨m, getrefnum_of_lookup k H st x m h⟩
  have hSc := hS c hc
  unfold ChildrenDone at hcd
  simp only [writeObjectR, call, getrefnum_of_lookup k H st c n hn, bind, Except.bind]
  cases ho : H.getD c .none <;> rw [ho] at hSc hcd <;> (try simp only at hcd) <;> (try simp only)
  · exact ⟨_, rfl⟩
  · rename_i b; cases b <;> exact ⟨_, rfl⟩
  · rename_i v
    obtain ⟨b, hb⟩ := writeInt_ok v hSc.1 hSc.2
    exact ⟨_, by rw [hb]; rfl⟩
  · exact ⟨_, rfl⟩
  · rename_i s
    cases ha : UnicodeObj.ucs1Encode s 128 .strict (fun _ => none) with
    | ok t => simp [writeSizeR, call, pure, Except.pure]
    | error e =>
      have hsp := ascii_encode_spec s
      rw [ha] at hsp
      have hu : UnicodeObj.utf16EncodeFull s 1 .strict (fun _ => none) =
          .ok (s.flatMap (UnicodeObj.utf16Char false)) := by
        unfold UnicodeObj.utf16EncodeFull
        rw [UnicodeObj.encodeWide_plain _ _ _ _ _ _ s s hSc _ _ _ (by omega)]
        simp
      simp only [hsp, ↓reduceIte, hu]
      simp [writeSizeR, call, pure, Except.pure]
  · simp [writeSizeR, call, pure, Except.pure]
  · simp [writeSizeR, call, pure, Except.pure]
  · exact hSc.elim
  · rename_i d
    have h0 : ¬ d < 0 := by omega
    rw [if_neg h0]
    by_cases a : d < 2 ^ 8
    · rw [if_pos a]; exact ⟨_, rfl⟩
    · rw [if_neg a]
      by_cases b : d < 2 ^ 16
      · rw [if_pos b]; exact ⟨_, rfl⟩
      · rw [if_neg b]
        by_cases cc : d < 2 ^ 32
        · rw [if_pos cc]; exact ⟨_, rfl⟩
        · rw [if_neg cc, if_pos hSc.2]; exact ⟨_, rfl⟩
  · rename_i xs
    obtain ⟨refs, hr⟩ := mapM_ok _ xs (fun x hx => hlook x (hcd x hx))
    simp [hr, writeSizeR, call, pure, Except.pure]
  · rename_i xs
    obtain ⟨refs, hr⟩ := mapM_ok _ xs (fun x hx => hlook x (hcd x hx))
    simp [hr, writeSizeR, call, pure, Except.pure]
  · rename_i items
    obtain ⟨kept, hk, _⟩ := dictItems_ok H cfg items hSc.2
    obtain ⟨its, hd, hkp⟩ := written_split H cfg items kept hk
    have hq := hcd kept hk
    simp only [dictItemsR, call, hd, hkp, bind, Except.bind]
    obtain ⟨kr, hkr⟩ := mapM_ok (fun x : Nat × Nat => getrefnumR (k + 1) H st x.fst) kept
      (fun q hq' => hlook q.1 (hq _ hq').1)
    obtain ⟨vr, hvr⟩ := mapM_ok (fun x : Nat × Nat => getrefnumR (k + 1) H st x.snd) kept
      (fun q hq' => hlook q.2 (hq _ hq').2)
    simp [hkr, hvr, writeSizeR, call, pure, Except.pure]
  · rename_i items
    obtain ⟨kept, hk, _⟩ := dictItems_ok H cfg items hSc.2
    obtain ⟨its, hd, hkp⟩ := written_split H cfg items kept hk
    have hq := hcd kept hk
    simp only [dictItemsR, call, hd, hkp, bind, Except.bind]
    obtain ⟨kr, hkr⟩ := mapM_ok (fun x : Nat × Nat => getrefnumR (k + 1) H st x.fst) kept
      (fun q hq' => hlook q.1 (hq _ hq').1)
    obtain ⟨vr, hvr⟩ := mapM_ok (fun x : Nat × Nat => getrefnumR (k + 1) H st x.snd) kept
      (fun q hq' => hlook q.2 (hq _ hq').2)
    simp [hkr, hvr, writeSizeR, call, pure, Except.pure]
  · exact hSc.elim


theorem writeAll_ok (k : Nat) (H : WHeap) (cfg : WCfg) (rs : Nat) (st : WState)
    (h : ∀ c ∈ st.objlist, ∃ out, writeObjectR (k + 2) H cfg rs st c = .ok out) :
    ∀ cs offs out, (∀ c ∈ cs, c ∈ st.objlist) →
      ∃ res, writeAll (k + 2) H cfg rs st cs offs out = .ok res
  | [], offs, out, _ => ⟨_, rfl⟩
  | c :: cs, offs, out, hc => by
    obtain ⟨o, ho⟩ := h c (hc c (by simp))
    rcases o with ⟨ref, b⟩
    obtain ⟨res, hres⟩ := writeAll_ok k H cfg rs st h cs (offs.set ref (8 + out.length)) (out ++ b)
      (fun x hx => hc x (by simp [hx]))
    exact ⟨res, by simp only [writeAll, ho, bind, Except.bind]; exact hres⟩

/-- `dumps(value, fmt=FMT_BINARY)` returns bytes for every supported object graph whose cells
the value refers to, with `len(heap) + 8` frames. -/
def WriteSucceeds : Prop :=
  ∀ (xmlw : XmlWrite) (H : WHeap) (root : Nat) (cfg : WCfg) (r : Nat),
    Supported H cfg → root < H.length → H.length + 8 ≤ r →
    ∃ b, dumpsR xmlw r H root .binary cfg = .ok b

theorem writeSucceeds_proven : WriteSucceeds := by
  intro xmlw H root cfg r hS hroot hr
  obtain ⟨k, rfl⟩ : ∃ j, r = j + 6 := ⟨r - 6, by omega⟩
  obtain ⟨st, hf, hh⟩ := flatten_ok H cfg hS (k + 3) root WState.init (winv_init H)
    (by simp [InHeap, WState.init]) hroot (by
      have : notSeen H WState.init ≤ H.length := by
        unfold notSeen; exact Nat.le_trans (List.length_filter_le _ _) (by simp)
      omega)
  obtain ⟨hI, _, hlr, hnew⟩ := flatten_spec H cfg (k + 3) root WState.init st (winv_init H) hf
  have hobj : ∀ c ∈ st.objlist, ∃ out,
      writeObjectR (k + 1 + 2) H cfg (countToSize st.objlist.length) st c = .ok out := by
    intro c hc
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
    have hci : st.objlist[i]? = some st.objlist[i] := List.getElem?_eq_getElem hi
    exact writeObject_ok (k + 1) H cfg _ st _ hS (hh _ hc) (by rw [hI.2.2 i _ hci]; rfl)
      (hnew i _ (by simp [WState.init]) hci)
  obtain ⟨res, hres⟩ := writeAll_ok (k + 1) H cfg (countToSize st.objlist.length) st hobj st.objlist
    (List.replicate st.objlist.length 0) [] (fun c hc => hc)
  rcases res with ⟨offsets, body⟩
  obtain ⟨top, htop⟩ : ∃ t, lookupW H st root = some t := by
    cases h : lookupW H st root with
    | none => rw [h] at hlr; cases hlr
    | some t => exact ⟨t, rfl⟩
  simp only [show k + 1 + 2 = k + 3 from rfl] at hres
  simp only [dumpsR, dumpR, binaryWriteR, call, bind, Except.bind, ↓reduceIte, hf, countToSizeR,
    pure, Except.pure, hres, getrefnum_of_lookup (k + 2) H st root top htop]
  simp

end PyLean.TextLibs.Plist
