import PyLean.TextLibs.PlistModel

/-!
`plistlib.loads` on arbitrary bytes in the binary format: with enough frames left, it returns or
raises `InvalidFileException`, and nothing else (`LoadsBinaryInvalidOnly`). The frames needed do
not depend on the references: `_read_object` stores a container in `self._objects` before reading
its elements (:619, :634), so a chain of nested calls visits each slot at most once, cycles
included, and the depth is bounded by the number of objects.
-/

namespace PyLean.TextLibs.Plist

open PyLean PyLean.TextLibs

/-! ## Undefined slots -/

/-- The number of `_undefined` slots. -/
def undef : List (Option Obj) → Nat
  | [] => 0
  | none :: t => undef t + 1
  | some _ :: t => undef t

theorem undef_set_some_le : ∀ (l : List (Option Obj)) (i : Nat) (o : Obj),
    undef (l.set i (some o)) ≤ undef l
  | [], _, _ => by simp [undef]
  | a :: t, 0, o => by cases a <;> simp [undef]
  | a :: t, i + 1, o => by
    have := undef_set_some_le t i o
    cases a <;> simp [undef] <;> omega

theorem undef_set_none : ∀ (l : List (Option Obj)) (i : Nat) (o : Obj), l[i]? = some none →
    undef (l.set i (some o)) + 1 = undef l
  | [], _, _, h => by simp at h
  | a :: t, 0, o, h => by
    simp at h
    subst h
    simp [undef]
  | a :: t, i + 1, o, h => by
    simp at h
    have := undef_set_none t i o h
    cases a <;> simp [undef] <;> omega

theorem undef_le_length : ∀ (l : List (Option Obj)), undef l ≤ l.length
  | [] => by simp [undef]
  | a :: t => by
    have := undef_le_length t
    cases a <;> simp [undef] <;> omega

theorem undef_replicate (n : Nat) : undef (List.replicate n none) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, undef, ih]

theorem put_objs_length (st : PState) (ref : Nat) (o : Obj) :
    (st.put ref o).objs.length = st.objs.length := by
  simp [PState.put]

theorem put_slot (st : PState) (ref : Nat) (o : Obj) (h : ref < st.objs.length) :
    (st.put ref o).objs[ref]? = some (some o) := by
  simp [PState.put, h]

/-! ## Safe computations: success, or an exception `parse` catches -/

def Safe {α : Type} (x : Py α) : Prop := ∀ e, x = .error e → parseCatches e = true

theorem safe_ok {α : Type} (a : α) : Safe (.ok a : Py α) := by
  intro e h; cases h

theorem safe_bind {α β : Type} (x : Py α) (f : α → Py β) (hx : Safe x)
    (hf : ∀ a, x = .ok a → Safe (f a)) : Safe (x >>= f) := by
  intro e h
  cases hx' : x with
  | error e' =>
    rw [hx'] at h
    cases h
    exact hx _ hx'
  | ok a =>
    rw [hx'] at h
    exact hf a hx' e h

theorem safe_invalid {α : Type} (r : Nat) (h : 1 ≤ r) : Safe (raiseInvalid r : Py α) := by
  intro e he
  obtain ⟨r, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  simp [raiseInvalid, call] at he
  subst he
  rfl

theorem safe_seek (f : FP) (n : Nat) : Safe (f.seek n) := by
  intro e he
  unfold FP.seek at he
  split at he
  · cases he; rfl
  · cases he

theorem safe_err {α : Type} (e : PyExc) (h : parseCatches e = true) : Safe (.error e : Py α) := by
  intro x hx; cases hx; exact h

theorem safe_unpackReal (b : List Nat) (four : Bool) : Safe (unpackReal b four) := by
  cases four <;> unfold unpackReal <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> split
  all_goals first | exact safe_ok _ | (apply safe_err; rfl)

theorem safe_longFromDouble (x : Binary64.F64) : Safe (longFromDouble x) := by
  unfold longFromDouble
  split
  · (apply safe_err; rfl)
  · split
    · (apply safe_err; rfl)
    · exact safe_ok _

theorem safe_usToDeltaC (x : Int) : Safe (Datetime.usToDeltaC x) := by
  unfold Datetime.usToDeltaC
  dsimp only
  apply safe_bind
  · unfold Datetime.asCInt
    split
    · exact safe_ok _
    · (apply safe_err; rfl)
  · intro d _
    apply safe_bind
    · unfold Datetime.checkDeltaDayRange
      split
      · exact safe_ok _
      · (apply safe_err; rfl)
    · intro _ _
      exact safe_ok _

theorem safe_accumSeconds (f : Binary64.F64) : Safe (accumSeconds f) := by
  unfold accumSeconds
  generalize modf f = p
  rcases p with ⟨frac1, int1⟩
  try dsimp only
  apply safe_bind _ _ (safe_longFromDouble _)
  intro x1 _
  try dsimp only
  split
  · exact safe_ok _
  · generalize modf _ = q
    rcases q with ⟨frac2, int2⟩
    try dsimp only
    apply safe_bind _ _ (safe_longFromDouble _)
    intro _ _
    exact safe_ok _

theorem safe_deltaFromSeconds (f : Binary64.F64) : Safe (deltaFromSeconds f) := by
  unfold deltaFromSeconds
  apply safe_bind _ _ (safe_accumSeconds _)
  intro p _
  rcases p with ⟨x, leftover⟩
  dsimp only
  split
  · exact safe_usToDeltaC _
  · exact safe_usToDeltaC _

theorem safe_epochPlus (td : Datetime.Delta) : Safe (epochPlus td) := by
  unfold epochPlus
  dsimp only
  split
  · split
    · exact safe_ok _
    · split
      · (apply safe_err; rfl)
      · exact safe_ok _
  · exact safe_ok _

theorem safe_uidR (r : Nat) (h : 1 ≤ r) (d : Int) : Safe (uidR r d) := by
  intro e he
  obtain ⟨r, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  simp only [uidR, call] at he
  split at he
  · cases he; rfl
  · split at he
    · cases he; rfl
    · cases he

theorem safe_getSizeR (r : Nat) (h : 1 ≤ r) (fp : FP) (t : Nat) : Safe (getSizeR r fp t) := by
  intro e he
  obtain ⟨r, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  simp only [getSizeR, call] at he
  split at he
  · split at he
    · cases he; rfl
    · split at he
      · cases he; rfl
      · cases he
  · cases he

/-! ## `_read`: the fuel suffices -/

theorem readLoop_safe (r : Nat) (hr : 1 ≤ r) (size : Nat) :
    ∀ fuel fp cursize data, cursize ≤ size → (cursize = 0 → size = 0) → size - cursize < fuel →
      Safe (readLoop r size fuel fp cursize data)
  | 0, _, _, _, _, _, hf => by omega
  | fuel + 1, fp, cursize, data, h1, h0, hf => by
    unfold readLoop
    split
    · exact safe_invalid r hr
    · split
      · exact safe_ok _
      · rename_i _ hne
        have hc : 0 < cursize := by
          rcases Nat.eq_zero_or_pos cursize with h | h
          · exact absurd (h.trans (h0 h).symm) hne
          · exact h
        exact readLoop_safe r hr size fuel _ _ _ (by omega) (by omega) (by omega)

theorem safe_readR (r : Nat) (hr : 2 ≤ r) (fp : FP) (size : Nat) : Safe (readR r fp size) := by
  obtain ⟨r, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  simp only [readR, call]
  exact readLoop_safe r (by omega) size _ _ _ _ (by simp [minReadBuf]; omega)
    (by intro h; simp [minReadBuf] at h; omega) (by omega)

theorem safe_readIntsR (r : Nat) (hr : 3 ≤ r) (fp : FP) (n size : Nat) :
    Safe (readIntsR r fp n size) := by
  obtain ⟨r, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  simp only [readIntsR, call]
  apply safe_bind _ _ (safe_readR r (by omega) _ _)
  intro p _
  split
  · exact safe_ok _
  · split
    · exact safe_invalid r (by omega)
    · obtain ⟨r', hr'⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
      subst hr'
      exact safe_ok _

theorem safe_readRefsR (r : Nat) (hr : 4 ≤ r) (cfg : PCfg) (fp : FP) (n : Nat) :
    Safe (readRefsR r cfg fp n) := by
  obtain ⟨r, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  simp only [readRefsR, call]
  exact safe_readIntsR r (by omega) _ _ _

/-! ## The strict decoders: the fuel suffices, and they raise `UnicodeDecodeError` -/

/-- A step that consumes at least one byte, and no more than are left, for each character. -/
def StepOk (step : List Nat → UnicodeObj.DStep) : Prop :=
  ∀ rest, match step rest with
    | .char _ n => 1 ≤ n ∧ n ≤ rest.length
    | .multi _ n => 1 ≤ n ∧ n ≤ rest.length
    | .stop => True
    | .raise _ => False
    | .fail _ _ _ => True

theorem decodeDriver_safe (step : List Nat → UnicodeObj.DStep) (hs : StepOk step) (enc : String)
    (code : UnicodeObj.EncCode) (input : List Nat) :
    ∀ fuel pos rest out, rest.length < fuel →
      Safe (UnicodeObj.decodeDriver step .strict enc code input fuel pos rest out)
  | 0, _, _, _, h => by omega
  | fuel + 1, pos, rest, out, h => by
    have hr := hs rest
    unfold UnicodeObj.decodeDriver
    split
    · rename_i c n he
      rw [he] at hr
      exact decodeDriver_safe step hs enc code input fuel _ _ _ (by simp; omega)
    · rename_i w n he
      rw [he] at hr
      exact decodeDriver_safe step hs enc code input fuel _ _ _ (by simp; omega)
    · exact safe_ok _
    · rename_i e he
      rw [he] at hr
      exact hr.elim
    · rename_i reason s e he
      intro x hx
      simp only [UnicodeObj.decodeHandlerCall] at hx
      cases hx
      unfold UnicodeObj.decodeError
      split <;> rfl

theorem stepAscii_ok : StepOk UnicodeObj.stepAscii := by
  intro rest
  cases rest with
  | nil => simp [UnicodeObj.stepAscii]
  | cons c t =>
    by_cases h : c < 128 <;> simp [UnicodeObj.stepAscii, h]

theorem step16_ok (le : Bool) : StepOk (UnicodeObj.step16 le false) := by
  intro rest
  match rest with
  | [] => simp [UnicodeObj.step16]
  | [_] => simp [UnicodeObj.step16]
  | a :: b :: t =>
    by_cases h1 : (!UnicodeObj.isSurrogate (UnicodeObj.unit16 le a b)) = true
    · simp [UnicodeObj.step16, h1]
    · by_cases h2 : (!UnicodeObj.isHighSurrogate (UnicodeObj.unit16 le a b)) = true
      · simp [UnicodeObj.step16, h1, h2]
      · match t with
        | [] => simp [UnicodeObj.step16, h1, h2]
        | [_] => simp [UnicodeObj.step16, h1, h2]
        | c :: d :: t' =>
          by_cases h3 : (!UnicodeObj.isLowSurrogate (UnicodeObj.unit16 le c d)) = true
          · simp [UnicodeObj.step16, h1, h2, h3]
          · simp [UnicodeObj.step16, h1, h2, h3]
            try omega

theorem bom16_one (b : List Nat) : UnicodeObj.bom16 1 b = (1, 0) := by
  unfold UnicodeObj.bom16
  split <;> simp

theorem safe_asciiDecode (d : List Nat) : Safe (UnicodeObj.asciiDecode d .strict) := by
  unfold UnicodeObj.asciiDecode
  apply safe_bind _ _ (decodeDriver_safe _ stepAscii_ok _ _ _ _ _ _ _ (by omega))
  intro _ _
  exact safe_ok _

theorem safe_utf16be (d : List Nat) : Safe (UnicodeObj.utf16DecodeFull d 1 .strict true) := by
  unfold UnicodeObj.utf16DecodeFull
  rw [bom16_one]
  dsimp only
  split
  · exact safe_ok _
  · exact decodeDriver_safe _ (step16_ok _) _ _ _ _ _ _ _ (by simp)


/-! ## `_read_object` -/

theorem lt_of_getElem?_some {α : Type} {l : List α} {i : Nat} {a : α} (h : l[i]? = some a) :
    i < l.length := by
  rcases Nat.lt_or_ge i l.length with h' | h'
  · exact h'
  · rw [List.getElem?_eq_none_iff.mpr h'] at h; cases h

/-- What `_read_object(ref)` leaves behind when it returns: as many slots, no more undefined ones,
and slot `ref` defined; when it raises, an exception `parse` catches. -/
def ROk (ref : Nat) (st : PState) : Py PState → Prop
  | .ok st' => st'.objs.length = st.objs.length ∧ undef st'.objs ≤ undef st.objs ∧
      ∃ o, st'.objs[ref]? = some (some o)
  | .error e => parseCatches e = true

theorem rok_err {ref : Nat} {st : PState} (e : PyExc) (h : parseCatches e = true) :
    ROk ref st (.error e) := h

theorem rok_bind {α : Type} {ref : Nat} {st : PState} (x : Py α) (f : α → Py PState) (hx : Safe x)
    (hf : ∀ a, x = .ok a → ROk ref st (f a)) : ROk ref st (x >>= f) := by
  cases h : x with
  | error e => exact hx e h
  | ok a => exact hf a h

theorem rok_invalid {ref : Nat} {st : PState} (k : Nat) (hk : 1 ≤ k) : ROk ref st (raiseInvalid k) := by
  cases h : (raiseInvalid k : Py PState) with
  | error e => exact safe_invalid k hk e h
  | ok a =>
    obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp [raiseInvalid, call] at h

theorem rok_leaf {ref : Nat} {st : PState} (hs : st.objs[ref]? = some none) (fp : FP) (o : Obj) :
    ROk ref st (.ok ({ st with fp := fp }.put ref o)) := by
  have hlt := lt_of_getElem?_some hs
  refine ⟨by simp [PState.put], ?_, o, ?_⟩
  · have := undef_set_none st.objs ref o hs
    simp only [PState.put]
    omega
  · simp [PState.put, hlt]

theorem rok_weaken {ref : Nat} {s0 s1 : PState} (res : Py PState) (h : ROk ref s1 res)
    (hl : s1.objs.length = s0.objs.length) (hu : undef s1.objs ≤ undef s0.objs) : ROk ref s0 res := by
  cases res with
  | error e => exact h
  | ok s2 =>
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨h1.trans hl, Nat.le_trans h2 hu, h3⟩

theorem put_undef_le (st : PState) (ref : Nat) (o : Obj) :
    undef (st.put ref o).objs ≤ undef st.objs := undef_set_some_le _ _ _

theorem arrLoop_ok (rd : Nat → PState → Py PState) (ref U : Nat)
    (hrd : ∀ x st, undef st.objs ≤ U → ROk x st (rd x st)) :
    ∀ (xs acc : List Nat) (st : PState), undef st.objs ≤ U → (∃ o, st.objs[ref]? = some (some o)) →
      ROk ref st (arrLoop rd ref acc xs st)
  | [], acc, st, hu, hd => by
    simp only [arrLoop]
    exact ⟨rfl, Nat.le_refl _, hd⟩
  | x :: xs, acc, st, hu, hd => by
    simp only [arrLoop]
    apply rok_bind _ _ (fun e he => by have := hrd x st hu; rw [he] at this; exact this)
    intro st1 h1
    have h := hrd x st hu
    rw [h1] at h
    obtain ⟨hl, hu1, _⟩ := h
    obtain ⟨o, ho⟩ := hd
    have hlt : ref < st1.objs.length := by rw [hl]; exact lt_of_getElem?_some ho
    have ih := arrLoop_ok rd ref U hrd xs (acc ++ [x]) (st1.put ref (.arr (acc ++ [x])))
      (Nat.le_trans (put_undef_le _ _ _) (by omega)) ⟨_, put_slot _ _ _ hlt⟩
    exact rok_weaken _ ih (by rw [put_objs_length, hl]) (Nat.le_trans (put_undef_le _ _ _) hu1)

/-- As `ROk`, but the loop of a dict may also raise the `TypeError` of an unhashable key. -/
def DOk (ref : Nat) (st : PState) : Py PState → Prop
  | .ok st' => st'.objs.length = st.objs.length ∧ undef st'.objs ≤ undef st.objs ∧
      ∃ o, st'.objs[ref]? = some (some o)
  | .error e => parseCatches e = true ∨ isInst e "TypeError" = true

theorem dictLoop_ok (rd : Nat → PState → Py PState) (ref U : Nat)
    (hrd : ∀ x st, undef st.objs ≤ U → ROk x st (rd x st)) :
    ∀ (ps : List (Nat × Nat)) (items : List (Nat × Nat)) (st : PState), undef st.objs ≤ U →
      (∃ o, st.objs[ref]? = some (some o)) → DOk ref st (dictLoop rd ref items ps st)
  | [], items, st, hu, hd => by
    simp only [dictLoop]
    exact ⟨rfl, Nat.le_refl _, hd⟩
  | (k, o) :: ps, items, st, hu, hd => by
    simp only [dictLoop]
    have h := hrd o st hu
    cases h1 : rd o st with
    | error e => rw [h1] at h; exact Or.inl h
    | ok st1 =>
      rw [h1] at h
      obtain ⟨hl1, hu1, _⟩ := h
      simp only [bind, Except.bind]
      have h' := hrd k st1 (by omega)
      cases h2 : rd k st1 with
      | error e => rw [h2] at h'; exact Or.inl h'
      | ok st2 =>
        rw [h2] at h'
        obtain ⟨hl2, hu2, ko, hko⟩ := h'
        simp only
        have hg : st2.objs.getD k none = some ko := by
          simp [List.getD_eq_getElem?_getD, hko]
        rw [hg]
        simp only
        split
        · exact Or.inr rfl
        · obtain ⟨o0, ho0⟩ := hd
          have hlt : ref < st2.objs.length := by
            rw [hl2, hl1]; exact lt_of_getElem?_some ho0
          have ih := dictLoop_ok rd ref U hrd ps (dictSet st2.objs k o items)
            (st2.put ref (.dict (dictSet st2.objs k o items)))
            (Nat.le_trans (put_undef_le _ _ _) (by omega)) ⟨_, put_slot _ _ _ hlt⟩
          revert ih
          generalize dictLoop rd ref _ ps _ = res
          cases res with
          | error e => exact id
          | ok s3 =>
            intro ⟨a, b, c⟩
            refine ⟨?_, ?_, c⟩
            · rw [a, put_objs_length, hl2, hl1]
            · exact Nat.le_trans b (Nat.le_trans (put_undef_le _ _ _) (by omega))

theorem parseCatches_not_type (e : PyExc) (h : parseCatches e = true) :
    isInst e "TypeError" = false := by
  cases e <;> simp_all [parseCatches, isInst, excMro]
  all_goals (split at h <;> simp_all)
  all_goals (rintro rfl; simp at h)

theorem rok_ite {ref : Nat} {st : PState} (c : Prop) [Decidable c] (a b : Py PState)
    (ha : c → ROk ref st a) (hb : ¬c → ROk ref st b) : ROk ref st (if c then a else b) := by
  by_cases h : c
  · rw [if_pos h]; exact ha h
  · rw [if_neg h]; exact hb h

theorem put_undef_eq (st : PState) (fp : FP) (ref : Nat) (o : Obj) (hs : st.objs[ref]? = some none) :
    undef ((({ fp := fp, objs := st.objs } : PState).put ref o).objs) + 1 = undef st.objs :=
  undef_set_none st.objs ref o hs

theorem put_slot' (st : PState) (fp : FP) (ref : Nat) (o : Obj) (hs : st.objs[ref]? = some none) :
    (({ fp := fp, objs := st.objs } : PState).put ref o).objs[ref]? = some (some o) := by
  simp [PState.put, lt_of_getElem?_some hs]

theorem put_len' (st : PState) (fp : FP) (ref : Nat) (o : Obj) :
    (({ fp := fp, objs := st.objs } : PState).put ref o).objs.length = st.objs.length := by
  simp [PState.put]

theorem rok_arr (cfg : PCfg) (k ref : Nat) (st : PState) (hs : st.objs[ref]? = some none)
    (hrd : ∀ x (st' : PState), undef st'.objs ≤ undef st.objs - 1 → ROk x st' (readObj cfg k x st'))
    (refs : List Nat) (fp : FP) :
    ROk ref st (arrLoop (fun x st => readObj cfg k x st) ref [] refs
      (({ fp := fp, objs := st.objs } : PState).put ref (.arr []))) := by
  have hu := put_undef_eq st fp ref (.arr []) hs
  exact rok_weaken _ (arrLoop_ok _ ref (undef st.objs - 1) hrd refs []
    (({ fp := fp, objs := st.objs } : PState).put ref (.arr [])) (by omega)
    ⟨_, put_slot' st fp ref _ hs⟩) (put_len' _ _ _ _) (by omega)

theorem dok_dict (cfg : PCfg) (k ref : Nat) (st : PState) (hs : st.objs[ref]? = some none)
    (hrd : ∀ x (st' : PState), undef st'.objs ≤ undef st.objs - 1 → ROk x st' (readObj cfg k x st'))
    (ps : List (Nat × Nat)) (fp : FP) :
    DOk ref st (dictLoop (fun x st => readObj cfg k x st) ref [] ps
      (({ fp := fp, objs := st.objs } : PState).put ref (.dict []))) := by
  have hu := put_undef_eq st fp ref (.dict []) hs
  have h := dictLoop_ok _ ref (undef st.objs - 1) hrd ps []
    (({ fp := fp, objs := st.objs } : PState).put ref (.dict [])) (by omega) ⟨_, put_slot' st fp ref _ hs⟩
  cases hres : dictLoop (fun x st => readObj cfg k x st) ref [] ps
      (({ fp := fp, objs := st.objs } : PState).put ref (.dict [])) with
  | error e => rw [hres] at h; exact h
  | ok s =>
    rw [hres] at h
    obtain ⟨a, b, c⟩ := h
    exact ⟨a.trans (put_len' _ _ _ _), Nat.le_trans b (by omega), c⟩

theorem rok_dict_ok (cfg : PCfg) (k ref : Nat) (st : PState) (hs : st.objs[ref]? = some none)
    (hrd : ∀ x (st' : PState), undef st'.objs ≤ undef st.objs - 1 → ROk x st' (readObj cfg k x st'))
    {ps : List (Nat × Nat)} {fp : FP} {s : PState}
    (heq : dictLoop (fun x st => readObj cfg k x st) ref [] ps
      (({ fp := fp, objs := st.objs } : PState).put ref (.dict [])) = .ok s) : ROk ref st (.ok s) := by
  have h := dok_dict cfg k ref st hs hrd ps fp
  rw [heq] at h
  exact h

theorem rok_dict_err (cfg : PCfg) (k ref : Nat) (st : PState) (hs : st.objs[ref]? = some none)
    (hrd : ∀ x (st' : PState), undef st'.objs ≤ undef st.objs - 1 → ROk x st' (readObj cfg k x st'))
    {ps : List (Nat × Nat)} {fp : FP} {e : PyExc}
    (heq : dictLoop (fun x st => readObj cfg k x st) ref [] ps
      (({ fp := fp, objs := st.objs } : PState).put ref (.dict [])) = .error e)
    (hT : ¬ isInst e "TypeError" = true) : ROk ref st (.error e) := by
  have h := dok_dict cfg k ref st hs hrd ps fp
  rw [heq] at h
  rcases h with h | h
  · exact h
  · exact absurd h hT

/-- Discharges the `Safe` side of `rok_bind` for the calls `_read_object` makes. -/
macro "safe_tac" : tactic => `(tactic| first
  | exact safe_unpackReal _ _
  | exact safe_deltaFromSeconds _
  | exact safe_epochPlus _
  | exact safe_getSizeR _ (by omega) _ _
  | exact safe_readR _ (by omega) _ _
  | exact safe_asciiDecode _
  | exact safe_utf16be _
  | exact safe_uidR _ (by omega) _
  | exact safe_readRefsR _ (by omega) _ _ _)

theorem readObj_ok (cfg : PCfg) :
    ∀ (k ref : Nat) (st : PState), undef st.objs + 5 ≤ k → ROk ref st (readObj cfg k ref st)
  | 0, _, _, h => by omega
  | k + 1, ref, st, h => by
    match hs : st.objs[ref]? with
    | none =>
      simp only [readObj, hs]
      exact rok_err _ rfl
    | some (some o) =>
      simp only [readObj, hs]
      exact ⟨rfl, Nat.le_refl _, o, hs⟩
    | some none =>
      have hu1 := undef_set_none st.objs ref .none hs
      have hrd : ∀ x (st' : PState), undef st'.objs ≤ undef st.objs - 1 →
          ROk x st' (readObj cfg k x st') :=
        fun x st' hu => readObj_ok cfg k x st' (by omega)
      simp only [readObj, hs]
      apply rok_bind _ _ (safe_seek _ _)
      intro fp _
      split
      · exact rok_err _ rfl
      · unfold readToken catchTypeError
        repeat' (first
          | exact rok_leaf hs _ _
          | exact rok_invalid k (by omega)
          | exact rok_arr cfg k ref st hs hrd _ _
          | exact rok_dict_ok cfg k ref st hs hrd ‹_›
          | exact rok_dict_err cfg k ref st hs hrd ‹_› ‹_›
          | (refine rok_ite _ _ _ (fun _ => ?_) (fun _ => ?_))
          | (refine rok_bind _ _ ?_ (fun _ _ => ?_); safe_tac)
          | (intro _; skip)
          | split
          | dsimp only)
        done

end PyLean.TextLibs.Plist

namespace PyLean.TextLibs.Plist

open PyLean PyLean.TextLibs

/-! ## Reads never return more than the buffer holds -/

theorem FP.read_buf (f : FP) (n : Nat) : (f.read n).2.buf = f.buf := rfl

theorem FP.read_len (f : FP) (n : Nat) :
    (f.read n).1.length + (f.buf.length - (f.read n).2.pos) = f.buf.length - f.pos := by
  simp only [FP.read, List.length_take, List.length_drop]
  omega

theorem readLoop_len (r size : Nat) (B : List Nat) :
    ∀ fuel (fp : FP) cursize data d fp', fp.buf = B → data.length + (B.length - fp.pos) ≤ B.length →
      readLoop r size fuel fp cursize data = .ok (d, fp') → d.length = size ∧ d.length ≤ B.length
  | 0, _, _, _, _, _, _, _, h => by simp [readLoop] at h
  | fuel + 1, fp, cursize, data, d, fp', hb, hl, h => by
    unfold readLoop at h
    split at h
    · obtain ⟨r, rfl⟩ : ∃ j, r = j + 1 := by
        cases r with
        | zero => simp [raiseInvalid, call] at h
        | succ j => exact ⟨j, rfl⟩
      simp [raiseInvalid, call] at h
    · rename_i hc
      split at h
      · rename_i he
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have : data.length = cursize := by simpa using hc
        omega
      · have hr := FP.read_len fp (min cursize (size - cursize))
        have hb2 := FP.read_buf fp (min cursize (size - cursize))
        dsimp only at h
        generalize hq : fp.read (min cursize (size - cursize)) = q at h hr hb2
        rcases q with ⟨dd, fp2⟩
        dsimp only at h hr hb2
        refine readLoop_len r size B fuel fp2 _ _ d fp' (by rw [hb2, hb]) ?_ h
        rw [hb] at hr
        simp only [List.length_append]
        omega

theorem readR_len (r : Nat) (fp : FP) (size : Nat) (d : List Nat) (fp' : FP)
    (h : readR r fp size = .ok (d, fp')) : d.length = size ∧ d.length ≤ fp.buf.length := by
  cases r with
  | zero => simp [readR, call] at h
  | succ r =>
    simp only [readR, call] at h
    have hr := FP.read_len fp (min size minReadBuf)
    exact readLoop_len r size fp.buf _ _ _ _ d fp' (FP.read_buf _ _) (by omega) h

theorem readIntsR_len (r : Nat) (fp : FP) (n size : Nat) (o : List Nat) (fp' : FP)
    (h : readIntsR r fp n size = .ok (o, fp')) : n ≤ fp.buf.length := by
  cases r with
  | zero => simp [readIntsR, call] at h
  | succ r =>
    simp only [readIntsR, call] at h
    cases hd : readR r fp (size * n) with
    | error e => rw [hd] at h; simp [bind, Except.bind] at h
    | ok p =>
      rcases p with ⟨data, fp1⟩
      have ⟨h1, h2⟩ := readR_len r fp (size * n) data fp1 hd
      rw [hd] at h
      simp only [bind, Except.bind] at h
      have hs : 1 ≤ size := by
        rcases Nat.eq_zero_or_pos size with h0 | h0
        · subst h0
          simp [binaryFormat] at h
          cases r with
          | zero => simp [raiseInvalid, call] at h
          | succ r => simp [raiseInvalid, call] at h
        · exact h0
      have : n ≤ size * n := Nat.le_mul_of_pos_left n hs
      omega

/-! ## `parse`, `load`, `loads` -/

theorem seek_buf (f f' : FP) (n : Nat) (h : f.seek n = .ok f') : f'.buf = f.buf := by
  unfold FP.seek at h
  split at h
  · cases h
  · cases h; rfl

theorem safe_readObj (cfg : PCfg) (k ref : Nat) (st : PState) (h : undef st.objs + 5 ≤ k) :
    Safe (readObj cfg k ref st) := by
  intro e he
  have := readObj_ok cfg k ref st h
  rw [he] at this
  exact this

theorem safe_parseBody (k : Nat) (aware : Bool) (buf : List Nat) (hk : buf.length + 5 ≤ k) :
    Safe (parseBody k aware buf) := by
  unfold parseBody
  dsimp only
  split
  · exact safe_invalid k (by omega)
  · apply safe_bind _ _ (safe_seek _ _)
    intro fp hfp
    apply safe_bind _ _ (safe_readIntsR k (by omega) _ _ _)
    intro p hp
    rcases p with ⟨offsets, fp2⟩
    have hn := readIntsR_len k _ _ _ _ _ hp
    rw [seek_buf _ _ _ hfp, FP.read_buf] at hn
    apply safe_bind
    · exact safe_readObj _ _ _ _ (by simp only [undef_replicate]; simp only [FP.seekEnd] at hn ⊢; omega)
    · intro _ _
      exact safe_ok _

theorem parseR_invalid (r : Nat) (aware : Bool) (buf : List Nat) (hr : buf.length + 6 ≤ r) :
    ∀ e, parseR r aware buf = .error e → e = invalidFile := by
  intro e he
  obtain ⟨r, rfl⟩ : ∃ j, r = j + 1 := ⟨r - 1, by omega⟩
  simp only [parseR, call] at he
  split at he
  · cases he
  · rename_i e' he'
    have hc := safe_parseBody r aware buf (by omega) e' he'
    simp only [hc, ↓reduceIte] at he
    obtain ⟨r, rfl⟩ : ∃ j, r = j + 1 := ⟨r - 1, by omega⟩
    simp [raiseInvalid, call] at he
    exact he.symm

theorem header_take (buf : List Nat) : (FP.read ⟨buf, 0⟩ 32).1 = buf.take 32 := by
  simp only [FP.read, List.drop_zero, Nat.sub_zero]
  rcases Nat.le_total 32 buf.length with h | h
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right h, List.take_of_length_le h, List.take_of_length_le (Nat.le_refl _)]

/-- With `len(data) + 8` frames left, `loads(data)` in the binary format (`fmt=FMT_BINARY`, or
`fmt=None` and `data` does not look like XML) returns or raises `InvalidFileException`, for every
`data`, whatever its trailer, offsets and references say, cyclic ones included. -/
def LoadsBinaryInvalidOnly : Prop :=
  ∀ (xml : XmlParse) (buf : List Nat) (fmt : Fmt) (aware : Bool) (r : Nat),
    buf.length + 8 ≤ r → (fmt = .binary ∨ (fmt = .none ∧ isFmtXml (buf.take 32) = false)) →
    ∀ e, loadsR xml r (.bytes buf) fmt aware = .error e → e = invalidFile

theorem loadsBinaryInvalidOnly_proven : LoadsBinaryInvalidOnly := by
  intro xml buf fmt aware r hr hfmt e he
  obtain ⟨r, rfl⟩ : ∃ j, r = j + 3 := ⟨r - 3, by omega⟩
  rcases hfmt with rfl | ⟨rfl, hx⟩
  · simp only [loadsR, loadR, call, bind, Except.bind, ↓reduceIte, Bool.false_eq_true] at he
    exact parseR_invalid (r + 1) aware buf (by omega) e he
  · simp only [loadsR, loadR, call, bind, Except.bind, header_take, hx, ↓reduceIte,
      Bool.false_eq_true] at he
    by_cases hb : isFmtBinary (buf.take 32) = true
    · simp only [hb, ↓reduceIte, Bool.false_eq_true] at he
      exact parseR_invalid (r + 1) aware buf (by omega) e he
    · simp [hb, raiseInvalid, call] at he
      exact he.symm

end PyLean.TextLibs.Plist
