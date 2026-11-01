import PyLean.Pickle.Enc

/-!
The refutation witness for `DumpsTwinsAgree`, a list of 1001 `None`s, evaluated
by lemmas: the first 1000 items produce the same output-layer calls in both
picklers, and only the last one differs. (`decide +kernel` overflows the
kernel's stack on this size.)
-/

namespace PyLean.Pickle

open PyLean

/-- The calls for item `i < 1000` of a list of `None`s, most recent first. -/
def itemEv (i : Nat) : List Event :=
  (if (i + 1) % 1000 = 0 then [.w [oAPPENDS]] else []) ++ [.w [oNONE], .boundary] ++
    (if i % 1000 = 0 then [.w [oMARK]] else [])

theorem batchLen_first (i : Nat) (hi : i < 1000) : batchLen 1001 i = 1000 := by
  simp only [batchLen, batchSize]; omega

theorem py_step (i : Nat) (hi : i < 1000) (xs : List PV) (st : EncSt) :
    pyAppends 2 1001 i (.none :: xs) st =
      pyAppends 2 1001 (i + 1) xs { st with ev := itemEv i ++ st.ev } := by
  have hbl := batchLen_first i hi
  have h3 : ¬ (i + 1 = 1001) := by omega
  simp only [pyAppends, pyBatchStep, optWr, hbl, batchSize, itemEv, pySave]
  by_cases h1 : i % 1000 = 0 <;> by_cases h2 : (i + 1) % 1000 = 0 <;>
    simp only [h1, h2, h3, or_false, reduceCtorEq, if_true, if_false, ne_eq, not_false_eq_true, and_true,
      Nat.reduceEqDiff] <;> rfl

theorem c_step (i : Nat) (hi : i < 1000) (xs : List PV) (st : EncSt) :
    cAppends 2 1001 i (.none :: xs) st =
      cAppends 2 1001 (i + 1) xs { st with ev := itemEv i ++ st.ev } := by
  have h3 : ¬ (i + 1 = 1001) := by omega
  simp only [cAppends, cBatchStep, optWr, batchSize, itemEv, cSave]
  by_cases h1 : i % 1000 = 0 <;> by_cases h2 : (i + 1) % 1000 = 0 <;>
    simp only [h1, h2, h3, or_false, reduceCtorEq, if_true, if_false, Nat.reduceEqDiff] <;> rfl

def advEv (e : List Event) : Nat → Nat → List Event
  | 0, _ => e
  | k + 1, i => advEv (itemEv i ++ e) k (i + 1)

theorem py_adv (k : Nat) : ∀ (i m : Nat) (st : EncSt), i + k ≤ 1000 →
    pyAppends 2 1001 i (List.replicate (k + m) .none) st =
      pyAppends 2 1001 (i + k) (List.replicate m .none) { st with ev := advEv st.ev k i } := by
  induction k with
  | zero => intro i m st _; simp [advEv]
  | succ k ih =>
    intro i m st h
    rw [show k + 1 + m = (k + m) + 1 by omega, List.replicate_succ, py_step i (by omega), ih (i + 1) m _ (by omega)]
    simp only [advEv, show i + 1 + k = i + (k + 1) by omega]

theorem c_adv (k : Nat) : ∀ (i m : Nat) (st : EncSt), i + k ≤ 1000 →
    cAppends 2 1001 i (List.replicate (k + m) .none) st =
      cAppends 2 1001 (i + k) (List.replicate m .none) { st with ev := advEv st.ev k i } := by
  induction k with
  | zero => intro i m st _; simp [advEv]
  | succ k ih =>
    intro i m st h
    rw [show k + 1 + m = (k + m) + 1 by omega, List.replicate_succ, c_step i (by omega), ih (i + 1) m _ (by omega)]
    simp only [advEv, show i + 1 + k = i + (k + 1) by omega]

/-- Plain output-layer calls: no framing. -/
def Plain : Event → Prop
  | .w _ | .boundary => True
  | _ => False

def conc : List Event → Bytes
  | [] => []
  | .w d :: r => d ++ conc r
  | _ :: r => conc r

theorem pyFold_plain (evs : List Event) (h : ∀ e ∈ evs, Plain e) (o : Bytes) :
    evs.foldl PyFramer.step ⟨o, none⟩ = ⟨o ++ conc evs, none⟩ := by
  induction evs generalizing o with
  | nil => simp [conc]
  | cons e r ih =>
    have hr : ∀ e ∈ r, Plain e := fun x hx => h x (List.mem_cons_of_mem _ hx)
    have he := h e List.mem_cons_self
    cases e <;> simp_all [Plain, conc, PyFramer.step]

theorem cFold_plain (evs : List Event) (h : ∀ e ∈ evs, Plain e) (o : Bytes) :
    evs.foldl CFramer.step ⟨o, none, false⟩ = ⟨o ++ conc evs, none, false⟩ := by
  induction evs generalizing o with
  | nil => simp [conc]
  | cons e r ih =>
    have hr : ∀ e ∈ r, Plain e := fun x hx => h x (List.mem_cons_of_mem _ hx)
    have he := h e List.mem_cons_self
    cases e <;> simp_all [Plain, conc, CFramer.step, CFramer.write]

theorem conc_append (a b : List Event) : conc (a ++ b) = conc a ++ conc b := by
  induction a with
  | nil => rfl
  | cons e r ih => cases e <;> simp [conc, ih]

theorem advEv_plain (k : Nat) : ∀ (i : Nat) (e : List Event), (∀ x ∈ e, Plain x) →
    ∀ x ∈ advEv e k i, Plain x := by
  induction k with
  | zero => intro i e h; exact h
  | succ k ih =>
    intro i e h
    apply ih
    intro x hx
    simp only [itemEv, List.mem_append] at hx
    rcases hx with ((hx | hx) | hx) | hx
    · split at hx <;> simp at hx; subst hx; trivial
    · simp at hx; rcases hx with rfl | rfl <;> trivial
    · split at hx <;> simp at hx; subst hx; trivial
    · exact h x hx

def noneList (n : Nat) : PV := .list (.u 0) (List.replicate n .none)

def headEv : List Event := [.w [oBINPUT, 0], .w [oEMPTY_LIST], .boundary, .w [oPROTO, 2]]
def headMemo : List (Oid × Nat) := [(.u 0, 0)]
def midEv : List Event := advEv headEv 1000 0

theorem advEv_eq_midEv : advEv headEv 1000 0 = midEv := by unfold midEv; rfl

theorem midEv_plain : ∀ x ∈ midEv, Plain x := by
  apply advEv_plain
  intro x hx
  simp [headEv] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> trivial

theorem bind_run {m : EncM Unit} {k : Unit → EncM Unit} {s s' : EncSt} (h : m s = .ok ((), s')) :
    (m >>= k) s = k () s' := by
  show (StateT.bind m k) s = _
  simp only [StateT.bind, bind, Except.bind, h]

theorem pyBody_list (xs : List PV) : pyBody 2 (.list (.u 0) xs) {} =
    (pyAppends 2 xs.length 0 xs >>= fun _ => do wr [oSTOP]; emit .finish)
      { memo := headMemo, ev := headEv } := by
  simp only [pyBody, pySave]
  rfl

theorem cBody_list (xs : List PV) (hxs : xs.length ≠ 0) : cBody 2 (.list (.u 0) xs) {} =
    (cAppends 2 xs.length 0 xs >>= fun _ => do wr [oSTOP]; emit .finish)
      { memo := headMemo, ev := headEv } := by
  simp only [cBody, cSave, cListWith, hxs, ne_eq, not_false_eq_true]
  rfl

theorem py_last (st : EncSt) : pyAppends 2 1001 1000 [.none] st =
    .ok ((), { st with ev := [.w [oAPPEND], .w [oNONE], .boundary] ++ st.ev }) := rfl

theorem c_last (st : EncSt) : cAppends 2 1001 1000 [.none] st =
    .ok ((), { st with ev := [.w [oAPPENDS], .w [oNONE], .boundary, .w [oMARK]] ++ st.ev }) := rfl

theorem pyBody_witness : pyBody 2 (noneList 1001) {} = .ok ((),
    { memo := headMemo, ev := [.finish, .w [oSTOP], .w [oAPPEND], .w [oNONE], .boundary] ++ midEv }) := by
  have h1 := py_adv 1000 0 1 { memo := headMemo, ev := headEv } (by omega)
  rw [show (1000 + 1 : Nat) = 1001 from rfl, show (0 + 1000 : Nat) = 1000 from rfl] at h1
  simp only [advEv_eq_midEv] at h1
  have h2 : pyAppends 2 1001 0 (List.replicate 1001 .none) { memo := headMemo, ev := headEv } =
      .ok ((), { memo := headMemo, ev := [.w [oAPPEND], .w [oNONE], .boundary] ++ midEv }) := by
    rw [h1, List.replicate_one, py_last]
  unfold noneList
  rw [pyBody_list, List.length_replicate, bind_run h2]
  rfl

theorem cBody_witness : cBody 2 (noneList 1001) {} = .ok ((),
    { memo := headMemo, ev := [.finish, .w [oSTOP], .w [oAPPENDS], .w [oNONE], .boundary, .w [oMARK]] ++ midEv }) := by
  have h1 := c_adv 1000 0 1 { memo := headMemo, ev := headEv } (by omega)
  rw [show (1000 + 1 : Nat) = 1001 from rfl, show (0 + 1000 : Nat) = 1000 from rfl] at h1
  simp only [advEv_eq_midEv] at h1
  have h2 : cAppends 2 1001 0 (List.replicate 1001 .none) { memo := headMemo, ev := headEv } =
      .ok ((), { memo := headMemo, ev := [.w [oAPPENDS], .w [oNONE], .boundary, .w [oMARK]] ++ midEv }) := by
    rw [h1, List.replicate_one, c_last]
  unfold noneList
  rw [cBody_list _ (by rw [List.length_replicate]; decide), List.length_replicate, bind_run h2]
  rfl

theorem pyDumps_of_run {x : PV} {st : EncSt} (h : pyBody 2 x {} = .ok ((), st)) :
    pyDumps x 2 = .ok (pyFrame st.ev.reverse) := by
  have hp : pyProtocol 2 = .ok 2 := rfl
  unfold pyDumps
  simp only [hp, bind, Except.bind, StateT.run, h, pure, Except.pure]

theorem cDumps_of_run {x : PV} {st : EncSt} (h : cBody 2 x {} = .ok ((), st)) :
    cDumps x 2 = .ok (cFrame st.ev.reverse) := by
  have hp : cProtocol 2 = .ok 2 := rfl
  unfold cDumps
  simp only [hp, bind, Except.bind, StateT.run, h, pure, Except.pure]

theorem pyFrame_tail (P : Bytes) (l : List Event) (hl : midEv.reverse.foldl PyFramer.step {} = ⟨P, none⟩) :
    pyFrame (midEv.reverse ++ l) = (l.foldl PyFramer.step ⟨P, none⟩).out := by
  unfold pyFrame
  rw [List.foldl_append, hl]

theorem cFrame_tail (P : Bytes) (l : List Event) (hl : midEv.reverse.foldl CFramer.step {} = ⟨P, none, false⟩) :
    cFrame (midEv.reverse ++ l) = (l.foldl CFramer.step ⟨P, none, false⟩).buf := by
  unfold cFrame
  rw [List.foldl_append, hl]

theorem pyTail_eval (P : Bytes) :
    (([.boundary, .w [oNONE], .w [oAPPEND], .w [oSTOP], .finish] : List Event).foldl PyFramer.step ⟨P, none⟩).out =
      P ++ [oNONE, oAPPEND, oSTOP] := by
  simp [PyFramer.step]

theorem cTail_eval (P : Bytes) :
    (([.w [oMARK], .boundary, .w [oNONE], .w [oAPPENDS], .w [oSTOP], .finish] : List Event).foldl
      CFramer.step ⟨P, none, false⟩).buf = P ++ [oMARK, oNONE, oAPPENDS, oSTOP] := by
  simp [CFramer.step, CFramer.write, CFramer.commit]

theorem pyDumps_witness : pyDumps (noneList 1001) 2 = .ok (conc midEv.reverse ++ [oNONE, oAPPEND, oSTOP]) := by
  have hfold : midEv.reverse.foldl PyFramer.step {} = ⟨conc midEv.reverse, none⟩ := by
    have h := pyFold_plain midEv.reverse (fun x hx => midEv_plain x (List.mem_reverse.mp hx)) []
    rw [List.nil_append] at h
    exact h
  rw [pyDumps_of_run pyBody_witness]
  have hrev : (([.finish, .w [oSTOP], .w [oAPPEND], .w [oNONE], .boundary] : List Event) ++ midEv).reverse =
      midEv.reverse ++ [.boundary, .w [oNONE], .w [oAPPEND], .w [oSTOP], .finish] := by
    rw [List.reverse_append]; rfl
  dsimp only
  rw [hrev, pyFrame_tail _ _ hfold, pyTail_eval]

theorem cDumps_witness : cDumps (noneList 1001) 2 =
    .ok (conc midEv.reverse ++ [oMARK, oNONE, oAPPENDS, oSTOP]) := by
  have hfold : midEv.reverse.foldl CFramer.step {} = ⟨conc midEv.reverse, none, false⟩ := by
    have h := cFold_plain midEv.reverse (fun x hx => midEv_plain x (List.mem_reverse.mp hx)) []
    rw [List.nil_append] at h
    exact h
  rw [cDumps_of_run cBody_witness]
  have hrev : (([.finish, .w [oSTOP], .w [oAPPENDS], .w [oNONE], .boundary, .w [oMARK]] : List Event) ++ midEv).reverse =
      midEv.reverse ++ [.w [oMARK], .boundary, .w [oNONE], .w [oAPPENDS], .w [oSTOP], .finish] := by
    rw [List.reverse_append]; rfl
  dsimp only
  rw [hrev, cFrame_tail _ _ hfold, cTail_eval]

end PyLean.Pickle
