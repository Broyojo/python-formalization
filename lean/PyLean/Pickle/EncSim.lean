import PyLean.Pickle.EncProps
import PyLean.Pickle.SaveLongProps
import PyLean.Pickle.IntLineProps

/-!
Simulation between the two picklers: from related states they make the same
output-layer calls up to how a write is split, and keep the same memo.
-/

namespace PyLean.Pickle

open PyLean

/-- An output-layer call as a token stream: writes are byte by byte, so the
split of a write into several calls disappears. -/
inductive Tok where
  | b (x : UInt8)
  | bnd
  | lg (h p : Bytes)
  deriving DecidableEq

def tok : Event → List Tok
  | .w d => d.map .b
  | .boundary => [.bnd]
  | .large h p => [.lg h p]
  | _ => []

/-- Calls in the order they were made, from a most-recent-first list. -/
def flat : List Event → List Tok
  | [] => []
  | e :: r => flat r ++ tok e

/-- Only `save`'s own calls: no `start`, no `finish`. -/
def Clean : Event → Prop
  | .w _ | .boundary | .large _ _ => True
  | _ => False

/-- Related pickler states above a common base of earlier calls. -/
def Rel (base : List Event) (s s' : EncSt) : Prop :=
  s.memo = s'.memo ∧ ∃ a b, s.ev = a ++ base ∧ s'.ev = b ++ base ∧ flat a = flat b ∧
    (∀ e ∈ a, Clean e) ∧ (∀ e ∈ b, Clean e)

def Out (base : List Event) : Except PyExc (Unit × EncSt) → Except PyExc (Unit × EncSt) → Prop
  | .ok r, .ok r' => Rel base r.2 r'.2
  | .error _, .error _ => True
  | _, _ => False

def Sim (base : List Event) (m n : EncM Unit) : Prop :=
  ∀ s s', Rel base s s' → Out base (m s) (n s')

variable {base : List Event}

theorem sim_pure : Sim base (pure ()) (pure ()) := fun _ _ h => h

theorem sim_bind {m n k l : EncM Unit} (h1 : Sim base m n) (h2 : Sim base k l) :
    Sim base (m >>= fun _ => k) (n >>= fun _ => l) := by
  intro s s' hr
  have := h1 s s' hr
  show Out base (Except.bind (m s) _) (Except.bind (n s') _)
  cases hm : m s with
  | error e =>
    cases hn : n s' with
    | error e' => exact trivial
    | ok r => rw [hm, hn] at this; exact this.elim
  | ok r =>
    cases hn : n s' with
    | error e' => rw [hm, hn] at this; exact this.elim
    | ok r' =>
      rw [hm, hn] at this
      exact h2 r.2 r'.2 this

theorem rel_cons {s s' : EncSt} (hr : Rel base s s') (e : Event) (he : Clean e) :
    Rel base { s with ev := e :: s.ev } { s' with ev := e :: s'.ev } := by
  obtain ⟨hm, a, b, ha, hb, hf, hca, hcb⟩ := hr
  refine ⟨hm, e :: a, e :: b, by simp [ha], by simp [hb], by simp [flat, hf], ?_, ?_⟩
  · intro x hx; rcases List.mem_cons.mp hx with rfl | hx
    · exact he
    · exact hca x hx
  · intro x hx; rcases List.mem_cons.mp hx with rfl | hx
    · exact he
    · exact hcb x hx

theorem sim_emit (e : Event) (he : Clean e) : Sim base (emit e) (emit e) :=
  fun _ _ hr => rel_cons hr e he

theorem sim_wr (d : Bytes) : Sim base (wr d) (wr d) := sim_emit _ trivial

/-- One write on the left, two on the right. -/
theorem sim_wr2 (d e : Bytes) : Sim base (wr (d ++ e)) (wr d >>= fun _ => wr e) := by
  intro s s' hr
  obtain ⟨hm, a, b, ha, hb, hf, hca, hcb⟩ := hr
  refine ⟨hm, .w (d ++ e) :: a, .w e :: .w d :: b, by simp [wr, emit, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, ha], ?_, ?_, ?_, ?_⟩
  · show Event.w e :: Event.w d :: s'.ev = _
    simp [hb]
  · simp [flat, hf, tok, List.map_append]
  · intro x hx; rcases List.mem_cons.mp hx with rfl | hx
    · trivial
    · exact hca x hx
  · intro x hx; rcases List.mem_cons.mp hx with rfl | hx
    · trivial
    · rcases List.mem_cons.mp hx with rfl | hx
      · trivial
      · exact hcb x hx

theorem sim_memo (o : Oid) {f g : Option Nat → EncM Unit} (h : ∀ v, Sim base (f v) (g v)) :
    Sim base (memoLookup o >>= f) (memoLookup o >>= g) := by
  intro s s' hr
  have hm : s.memo = s'.memo := hr.1
  have := h (s'.memo.lookup o) s s' hr
  show Out base (f (s.memo.lookup o) s) (g (s'.memo.lookup o) s')
  rw [hm]
  exact this

theorem sim_lift {a b : Py Bytes} (h : SameOutcome a b) {f g : Bytes → EncM Unit}
    (hk : ∀ v, Sim base (f v) (g v)) : Sim base (liftPy a >>= f) (liftPy b >>= g) := by
  intro s s' hr
  cases a with
  | error e =>
    cases b with
    | error e' => exact trivial
    | ok v => exact h.elim
  | ok v =>
    cases b with
    | error e' => exact h.elim
    | ok v' =>
      have hv : v = v' := h
      subst hv
      exact hk v s s' hr

theorem sameOutcome_get (p i : Nat) : SameOutcome (pyGet p i) (cGet p i) := by
  unfold pyGet cGet packU32
  by_cases h0 : p = 0
  · subst h0; simp [SameOutcome]
  · have h1 : p ≥ 1 := by omega
    simp only [h1, h0, ge_iff_le, if_true, if_false, ↓reduceIte]
    by_cases h2 : i < 256
    · simp [h2, SameOutcome]
    · by_cases h3 : i ≤ 4294967295
      · simp [h2, h3, SameOutcome, Functor.map, Except.map]
      · simp [h2, h3, SameOutcome, Functor.map, Except.map, picklingError]

theorem sameOutcome_put (p i : Nat) : SameOutcome (pyPut p i) (cPut p i) := by
  unfold pyPut cPut packU32
  by_cases h4 : p ≥ 4
  · simp [h4, SameOutcome]
  by_cases h0 : p = 0
  · subst h0; simp [SameOutcome]
  · have h1 : p ≥ 1 := by omega
    simp only [h4, h1, h0, ge_iff_le, if_true, if_false, ↓reduceIte]
    by_cases h2 : i < 256
    · simp [h2, SameOutcome]
    · by_cases h3 : i ≤ 4294967295
      · simp [h2, h3, SameOutcome, Functor.map, Except.map]
      · simp [h2, h3, SameOutcome, Functor.map, Except.map, picklingError]

theorem sim_get (p i : Nat) :
    Sim base (liftPy (pyGet p i) >>= wr) (liftPy (cGet p i) >>= wr) :=
  sim_lift (sameOutcome_get p i) (fun v => sim_wr v)

/-- `memoize`: the C code sets the memo first, which does not matter. -/
theorem sim_memoize (p : Nat) (o : Oid) : Sim base (pyMemoize p o) (cMemoPut p o) := by
  intro s s' hr
  have hm : s.memo = s'.memo := hr.1
  have hs := sameOutcome_put p s'.memo.length
  have e1 : pyMemoize p o s = (liftPy (pyPut p s.memo.length) >>= fun b =>
      (wr b >>= fun _ => memoSet o s.memo.length)) s := rfl
  have e2 : cMemoPut p o s' = (liftPy (cPut p s'.memo.length) >>= wr)
      { s' with memo := (o, s'.memo.length) :: s'.memo } := rfl
  rw [e1, e2, hm]
  cases ha : pyPut p s'.memo.length with
  | error e =>
    rw [ha] at hs
    cases hb : cPut p s'.memo.length with
    | error e' => exact trivial
    | ok v => rw [hb] at hs; exact hs.elim
  | ok v =>
    rw [ha] at hs
    cases hb : cPut p s'.memo.length with
    | error e' => rw [hb] at hs; exact hs.elim
    | ok v' =>
      rw [hb] at hs
      have hv : v = v' := hs
      subst hv
      have := rel_cons hr (.w v) trivial
      obtain ⟨_, h2⟩ := this
      refine ⟨?_, h2⟩
      show (o, s'.memo.length) :: s.memo = (o, s'.memo.length) :: s'.memo
      rw [hm]

theorem rue_eq_c (s : List Nat) : rueEncode (pyStrEscape s) = cRawUnicodeEscape s := by
  unfold rueEncode pyStrEscape cRawUnicodeEscape
  rw [List.flatMap_assoc]
  congr 1
  funext c
  by_cases h1 : c = 0x5c
  · subst h1; decide
  by_cases h2 : c = 0
  · subst h2; decide
  by_cases h3 : c = 0x0a
  · subst h3; decide
  by_cases h4 : c = 0x0d
  · subst h4; decide
  by_cases h5 : c = 0x1a
  · subst h5; decide
  simp only [h1, h2, h3, h4, h5, if_false, List.flatMap_cons, List.flatMap_nil, List.append_nil, rueChar,
    or_false, ↓reduceIte]

/-- The header-and-payload part of `save_str`, protocol >= 1. -/
theorem sim_strdata (p : Nat) (data : Bytes) : Sim base (pyStrData p data) (cStrData p data) := by
  unfold pyStrData cStrData
  dsimp only
  generalize hn : data.length = n
  by_cases h1 : n ≤ 0xff ∧ p ≥ 4
  · rw [if_pos h1, if_pos h1]
    have : ¬ (data.length ≥ frameSizeTarget) := by simp only [frameSizeTarget]; omega
    show Sim base _ (cWriteBytes _ data)
    unfold cWriteBytes
    rw [if_neg this]
    exact sim_wr2 _ _
  rw [if_neg h1, if_neg h1]
  by_cases h2 : n > 0xffffffff ∧ p ≥ 4
  · have h3 : ¬ n ≤ 0xffffffff := by omega
    rw [if_pos h2, if_neg h3, if_pos h2.2]
    show Sim base _ (cWriteBytes _ data)
    unfold cWriteBytes
    rw [if_pos (by simp only [frameSizeTarget]; omega)]
    exact sim_emit _ trivial
  rw [if_neg h2]
  by_cases h3 : n ≤ 0xffffffff
  · rw [if_pos h3]
    have hpk : packU32 n = .ok (leBytes n 4) := by unfold packU32; rw [if_pos h3]
    rw [hpk]
    show Sim base _ (cWriteBytes _ data)
    unfold cWriteBytes
    by_cases h4 : n ≥ frameSizeTarget
    · rw [if_pos h4, if_pos (by omega)]
      exact sim_emit _ trivial
    · rw [if_neg h4, if_neg (by omega)]
      exact sim_wr2 (oBINUNICODE :: leBytes n 4) data
  · have hp4 : ¬ p ≥ 4 := fun h => h2 ⟨by omega, h⟩
    have hpk : packU32 n = .error (structError "'I' format requires 0 <= number <= 4294967295") := by
      unfold packU32; rw [if_neg h3]
    rw [hpk, if_neg h3, if_neg hp4]
    split <;> exact fun _ _ _ => trivial

theorem flat_append (l a : List Event) : flat (l ++ a) = flat a ++ flat l := by
  induction l with
  | nil => simp [flat]
  | cons e r ih => simp [flat, ih, List.append_assoc]

theorem rel_ext {s s' : EncSt} (hr : Rel base s s') (l r : List Event) (hf : flat l = flat r)
    (hl : ∀ e ∈ l, Clean e) (hc : ∀ e ∈ r, Clean e) {t t' : EncSt} (ht : t = { memo := s.memo, ev := l ++ s.ev })
    (ht' : t' = { memo := s'.memo, ev := r ++ s'.ev }) : Rel base t t' := by
  obtain ⟨hm, a, b, ha, hb, hfl, hca, hcb⟩ := hr
  subst ht ht'
  refine ⟨hm, l ++ a, r ++ b, by simp [ha], by simp [hb], by simp [flat_append, hf, hfl], ?_, ?_⟩
  · intro e he; rcases List.mem_append.mp he with he | he
    · exact hl e he
    · exact hca e he
  · intro e he; rcases List.mem_append.mp he with he | he
    · exact hc e he
    · exact hcb e he

theorem sim_wr5 (a b c d e : Bytes) :
    Sim base (wr (a ++ (b ++ c)) >>= fun _ => wr (d ++ e))
      (wr a >>= fun _ => wr b >>= fun _ => wr c >>= fun _ => wr d >>= fun _ => wr e) := by
  intro s s' hr
  exact rel_ext hr [.w (d ++ e), .w (a ++ (b ++ c))] [.w e, .w d, .w c, .w b, .w a]
    (by simp [flat, tok, List.map_append])
    (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> trivial)
    (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl <;> trivial)
    rfl rfl

theorem sim_wr3 (a b c : Bytes) :
    Sim base (wr (a ++ (b ++ c))) (wr a >>= fun _ => wr b >>= fun _ => wr c) := by
  intro s s' hr
  obtain ⟨hm, x, y, hx, hy, hf, hcx, hcy⟩ := hr
  refine ⟨hm, .w (a ++ (b ++ c)) :: x, .w c :: .w b :: .w a :: y, ?_, ?_, ?_, ?_, ?_⟩
  · show Event.w _ :: s.ev = _
    simp [hx]
  · show Event.w c :: Event.w b :: Event.w a :: s'.ev = _
    simp [hy]
  · simp [flat, hf, tok, List.map_append]
  · intro e he; rcases List.mem_cons.mp he with rfl | he
    · trivial
    · exact hcx e he
  · intro e he
    simp only [List.mem_cons] at he
    rcases he with rfl | rfl | rfl | he
    · trivial
    · trivial
    · trivial
    · exact hcy e he

theorem sim_strbody (p : Nat) (s : List Nat) : Sim base (pyStrBody p s) (cStrBody p s) := by
  unfold pyStrBody cStrBody
  by_cases h : p ≥ 1
  · rw [if_pos h, if_pos h]
    exact sim_strdata p _
  · rw [if_neg h, if_neg h, rue_eq_c]
    exact sim_wr3 [oUNICODE] (cRawUnicodeEscape s) [nl]

theorem sim_str (p : Nat) (o : Oid) (s : List Nat) : Sim base (pySaveStr p o s) (cSaveStr p o s) :=
  sim_bind (sim_strbody p s) (sim_memoize p o)

theorem sim_get_or {p : Nat} {f g : EncM Unit} (h : Sim base f g) (v : Option Nat) :
    Sim base (match v with
      | some i => liftPy (pyGet p i) >>= wr
      | none => f)
    (match v with
      | some i => liftPy (cGet p i) >>= wr
      | none => g) := by
  cases v with
  | some i => exact sim_get p i
  | none => exact h

theorem sim_strobj (p : Nat) (o : Oid) (s : List Nat) :
    Sim base (pySaveStrObj p o s) (cSaveStrObj p o s) :=
  sim_bind (sim_emit _ trivial) (sim_memo o (sim_get_or (sim_str p o s)))

theorem sim_globalref (p : Nat) (g : Glob) : Sim base (pyGlobalRef p g) (cGlobalRef p g) := by
  unfold pyGlobalRef cGlobalRef
  by_cases h : p ≥ 4
  · rw [if_pos h, if_pos h]
    exact sim_bind (sim_strobj p _ _) (sim_bind (sim_strobj p _ _) (sim_wr _))
  · rw [if_neg h, if_neg h]
    exact sim_wr5 [oGLOBAL] (ascii (globModuleOut p g)) [nl] (ascii g.name) [nl]

theorem sim_global (p : Nat) (g : Glob) : Sim base (pySaveGlobal p g) (cSaveGlobal p g) :=
  sim_bind (sim_emit _ trivial) (sim_memo _ (sim_get_or (sim_bind (sim_globalref p g) (sim_memoize p _))))

theorem sim_bytesdata (p : Nat) (b : Bytes) : Sim base (pySaveBytesData p b) (cSaveBytesData p b) := by
  unfold pySaveBytesData cSaveBytesData
  dsimp only
  generalize hn : b.length = n
  by_cases h1 : n ≤ 0xff
  · rw [if_pos h1, if_pos h1]
    have : ¬ (b.length ≥ frameSizeTarget) := by simp only [frameSizeTarget]; omega
    show Sim base _ (cWriteBytes _ b)
    unfold cWriteBytes
    rw [if_neg this]
    exact sim_wr2 _ _
  rw [if_neg h1, if_neg h1]
  by_cases h2 : n > 0xffffffff ∧ p ≥ 4
  · have h3 : ¬ n ≤ 0xffffffff := by omega
    rw [if_pos h2, if_neg h3, if_pos h2.2]
    show Sim base _ (cWriteBytes _ b)
    unfold cWriteBytes
    rw [if_pos (by simp only [frameSizeTarget]; omega)]
    exact sim_emit _ trivial
  rw [if_neg h2]
  by_cases h3 : n ≤ 0xffffffff
  · rw [if_pos h3]
    have hpk : packU32 n = .ok (leBytes n 4) := by unfold packU32; rw [if_pos h3]
    rw [hpk]
    show Sim base _ (cWriteBytes _ b)
    unfold cWriteBytes
    by_cases h4 : n ≥ frameSizeTarget
    · rw [if_pos h4, if_pos (by omega)]
      exact sim_emit _ trivial
    · rw [if_neg h4, if_neg (by omega)]
      exact sim_wr2 (oBINBYTES :: leBytes n 4) b
  · have hp4 : ¬ p ≥ 4 := fun h => h2 ⟨by omega, h⟩
    have hpk : packU32 n = .error (structError "'I' format requires 0 <= number <= 4294967295") := by
      unfold packU32; rw [if_neg h3]
    rw [hpk, if_neg h3, if_neg hp4]
    split <;> exact fun _ _ _ => trivial

theorem cPops_run (n : Nat) (s : EncSt) :
    cPops n s = .ok ((), { memo := s.memo, ev := List.replicate n (.w [oPOP]) ++ s.ev }) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    show cPops n { s with ev := .w [oPOP] :: s.ev } = _
    rw [ih]
    simp [List.replicate_succ', List.append_assoc]

theorem flat_replicate (n : Nat) : flat (List.replicate n (.w [oPOP])) =
    (List.replicate n oPOP).map .b := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, flat, ih, List.replicate_succ']
    simp [tok]

theorem clean_replicate (n : Nat) : ∀ e ∈ List.replicate n (Event.w [oPOP]), Clean e := by
  intro e he
  rw [List.eq_of_mem_replicate he]
  trivial

/-- `POP`s then get: one write in Python, `n + 1` in C. -/
theorem sim_pops (p i n : Nat) :
    Sim base (liftPy (pyGet p i) >>= fun b => wr (List.replicate n oPOP ++ b))
      (cPops n >>= fun _ => liftPy (cGet p i) >>= wr) := by
  intro s s' hr
  have hs := sameOutcome_get p i
  have e2 : (cPops n >>= fun _ => liftPy (cGet p i) >>= wr) s' =
      (liftPy (cGet p i) >>= wr) { memo := s'.memo, ev := List.replicate n (.w [oPOP]) ++ s'.ev } := by
    show Except.bind (cPops n s') _ = _
    rw [cPops_run]
    rfl
  rw [e2]
  cases ha : pyGet p i with
  | error e =>
    rw [ha] at hs
    cases hb : cGet p i with
    | error e' => exact trivial
    | ok v => rw [hb] at hs; exact hs.elim
  | ok v =>
    rw [ha] at hs
    cases hb : cGet p i with
    | error e' => rw [hb] at hs; exact hs.elim
    | ok v' =>
      rw [hb] at hs
      have hv : v = v' := hs
      subst hv
      exact rel_ext hr [.w (List.replicate n oPOP ++ v)] (.w v :: List.replicate n (.w [oPOP]))
        (by simp [flat, tok, flat_replicate, List.map_append])
        (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; subst hx; trivial)
        (by intro x hx; rcases List.mem_cons.mp hx with rfl | hx
            · trivial
            · exact clean_replicate n x hx)
        rfl rfl

/-- One opcode then get: one write in Python, two in C. -/
theorem sim_op_get (p i : Nat) (op : UInt8) :
    Sim base (liftPy (pyGet p i) >>= fun b => wr (op :: b))
      (wr [op] >>= fun _ => liftPy (cGet p i) >>= wr) := by
  intro s s' hr
  have hs := sameOutcome_get p i
  have e2 : (wr [op] >>= fun _ => liftPy (cGet p i) >>= wr) s' =
      (liftPy (cGet p i) >>= wr) { memo := s'.memo, ev := [.w [op]] ++ s'.ev } := rfl
  rw [e2]
  cases ha : pyGet p i with
  | error e =>
    rw [ha] at hs
    cases hb : cGet p i with
    | error e' => exact trivial
    | ok v => rw [hb] at hs; exact hs.elim
  | ok v =>
    rw [ha] at hs
    cases hb : cGet p i with
    | error e' => rw [hb] at hs; exact hs.elim
    | ok v' =>
      rw [hb] at hs
      have hv : v = v' := hs
      subst hv
      exact rel_ext hr [.w (op :: v)] [.w v, .w [op]] (by simp [flat, tok])
        (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; subst hx; trivial)
        (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
            rcases hx with rfl | rfl <;> trivial)
        rfl rfl

theorem sim_tuplewith (p n : Nat) (o : Oid) {e e' : EncM Unit} (he : Sim base e e') :
    Sim base (pyTupleWith p o n e) (cTupleWith p o n e') := by
  unfold pyTupleWith cTupleWith
  by_cases h0 : n = 0
  · rw [if_pos h0, if_pos h0]
    by_cases hp : p = 0
    · subst hp; simp only [ge_iff_le, Nat.le_zero_eq, Nat.succ_ne_zero, ↓reduceIte, ne_eq, not_true_eq_false]
      exact sim_wr _
    · rw [if_pos (by omega), if_pos hp]
      exact sim_wr _
  rw [if_neg h0, if_neg h0]
  by_cases h3 : n ≤ 3 ∧ p ≥ 2
  · rw [if_pos h3, if_pos h3]
    refine sim_bind he (sim_memo o ?_)
    intro v
    cases v with
    | some i => exact sim_pops p i n
    | none => exact sim_bind (sim_wr _) (sim_memoize p o)
  · rw [if_neg h3, if_neg h3]
    refine sim_bind (sim_wr _) (sim_bind he (sim_memo o ?_))
    intro v
    cases v with
    | some i =>
      show Sim base (if p ≥ 1 then (liftPy (pyGet p i) >>= fun b => wr (oPOP_MARK :: b))
          else (liftPy (pyGet p i) >>= fun b => wr (List.replicate (n + 1) oPOP ++ b)))
        (cPopMark p n >>= fun _ => liftPy (cGet p i) >>= wr)
      unfold cPopMark
      by_cases hp : p = 0
      · rw [if_neg (by omega), if_neg (by simp [hp])]
        exact sim_pops p i (n + 1)
      · rw [if_pos (by omega), if_pos hp]
        exact sim_op_get p i oPOP_MARK
    | none => exact sim_bind (sim_wr _) (sim_memoize p o)

theorem sim_tupleobj (p n : Nat) (o : Oid) {e e' : EncM Unit} (he : Sim base e e') :
    Sim base (pyTupleObj p o n e) (cTupleObj p o n e') :=
  sim_bind (sim_emit _ trivial) (sim_memo o (sim_get_or (sim_tuplewith p n o he)))

theorem sim_reduce (p : Nat) (o : Oid) (g : Glob) {a a' : EncM Unit} (ha : Sim base a a') :
    Sim base (pyReduceWith p o g a) (cReduceWith p o g a') := by
  refine sim_bind (sim_global p g) (sim_bind ha (sim_bind (sim_wr _) (sim_memo o ?_)))
  intro v
  cases v with
  | some i => exact sim_op_get p i oPOP
  | none => exact sim_memoize p o

theorem sim_bytesobj (p : Nat) (o : Oid) (b : Bytes) :
    Sim base (pySaveBytesObj p o b) (cSaveBytesObj p o b) := by
  refine sim_bind (sim_emit _ trivial) (sim_memo o (sim_get_or ?_))
  by_cases h : p < 3
  · rw [if_pos h, if_pos h]
    by_cases hb : b = []
    · subst hb
      simp only [↓reduceIte, List.length_nil]
      exact sim_reduce p o .bytes (sim_tupleobj p 0 _ sim_pure)
    · have hl : ¬ b.length = 0 := by simpa using hb
      rw [if_neg hb, if_neg hl]
      exact sim_reduce p o .codecsEncode (sim_tupleobj p 2 _ (sim_bind (sim_strobj p _ _) (sim_strobj p _ _)))
  · rw [if_neg h, if_neg h]
    exact sim_bind (sim_bytesdata p b) (sim_memoize p o)

theorem sim_bytearraydata (b : Bytes) :
    Sim base (pySaveBytearrayData b) (cWriteBytes (oBYTEARRAY8 :: leBytes b.length 8) b) := by
  unfold pySaveBytearrayData cWriteBytes
  dsimp only
  split
  · exact sim_emit _ trivial
  · exact sim_wr2 (oBYTEARRAY8 :: leBytes b.length 8) b

theorem sim_bytearrayobj (p : Nat) (o : Oid) (b : Bytes) :
    Sim base (pySaveBytearrayObj p o b) (cSaveBytearrayObj p o b) := by
  refine sim_bind (sim_emit _ trivial) (sim_memo o (sim_get_or ?_))
  by_cases h : p < 5
  · rw [if_pos h, if_pos h]
    by_cases hb : b = []
    · subst hb
      simp only [↓reduceIte, List.length_nil]
      exact sim_reduce p o .bytearray (sim_tupleobj p 0 _ sim_pure)
    · have hl : ¬ b.length = 0 := by simpa using hb
      rw [if_neg hb, if_neg hl]
      exact sim_reduce p o .bytearray (sim_tupleobj p 1 _ (sim_bytesobj p _ b))
  · rw [if_neg h, if_neg h]
    exact sim_bind (sim_bytearraydata b) (sim_memoize p o)

theorem batchLen_ne_one (n i : Nat) (hi : i < n) (h : n % 1000 ≠ 1) : batchLen n i ≠ 1 := by
  simp only [batchLen, batchSize]; omega

theorem batchLen_one : batchLen 1 0 = 1 := rfl

mutual
/-- Every int in `x` passes the C size check of `save_long`. -/
def IntsOk : PV → Prop
  | .int i => bitLength i.natAbs / 8 + 1 ≤ 0x7fffffff
  | .tuple _ xs | .list _ xs | .set _ xs | .frozenset _ xs => IntsOkList xs
  | .dict _ kvs => IntsOkPairs kvs
  | _ => True
def IntsOkList : List PV → Prop
  | [] => True
  | x :: xs => IntsOk x ∧ IntsOkList xs
def IntsOkPairs : List (PV × PV) → Prop
  | [] => True
  | (k, v) :: kvs => IntsOk k ∧ IntsOk v ∧ IntsOkPairs kvs
end

theorem sim_opt {c c' : Prop} [Decidable c] [Decidable c'] (h : c ↔ c') (d : Bytes) :
    Sim base (optWr c d) (optWr c' d) := by
  unfold optWr
  by_cases hc : c
  · rw [if_pos hc, if_pos (h.mp hc)]; exact sim_wr d
  · rw [if_neg hc, if_neg (fun x => hc (h.mpr x))]; exact sim_pure

theorem sim_emptyop (p : Nat) (e o : UInt8) : Sim base (pyEmptyOp p e o) (cEmptyOp p e o) := by
  unfold pyEmptyOp cEmptyOp
  by_cases h : p = 0
  · rw [if_neg (by omega), if_neg (by simp [h])]; exact sim_wr _
  · rw [if_pos (by omega), if_pos h]; exact sim_wr _

theorem sim_batchStep (p n i : Nat) (hc : p = 0 ∨ n ≤ 1 ∨ n % 1000 ≠ 1) (hi : i < n)
    {it it' : EncM Unit} (h : Sim base it it') (one many : UInt8) :
    Sim base (pyBatchStep p n i it one many) (cBatchStep p n i it' one many) := by
  unfold pyBatchStep cBatchStep
  by_cases h0 : p = 0
  · rw [if_pos h0, if_pos h0]; exact sim_bind h (sim_wr _)
  rw [if_neg h0, if_neg h0]
  by_cases h1 : n = 1
  · subst h1
    have hi0 : i = 0 := by omega
    subst hi0
    rw [if_pos rfl]
    have e1 : optWr (0 % batchSize = 0 ∧ batchLen 1 0 ≠ 1) [oMARK] = pure () := by
      unfold optWr; rw [if_neg (by simp [batchLen_one])]
    have e2 : optWr ((0 + 1) % batchSize = 0 ∨ 0 + 1 = 1) [if batchLen 1 0 ≠ 1 then many else one] =
        wr [one] := by
      unfold optWr; rw [if_pos (Or.inr rfl), if_neg (by simp [batchLen_one])]
    rw [e1, e2, pure_bind]
    exact sim_bind h (sim_wr _)
  · rw [if_neg h1]
    have hbl := batchLen_ne_one n i hi (by omega)
    have e2 : (if batchLen n i ≠ 1 then many else one) = many := if_pos hbl
    rw [e2]
    exact sim_bind (sim_opt (by simp [hbl]) _) (sim_bind h (sim_opt Iff.rfl _))

theorem sim_addStep (n i : Nat) {it it' : EncM Unit} (h : Sim base it it') :
    Sim base (addStep n i it) (addStep n i it') :=
  sim_bind (sim_opt Iff.rfl _) (sim_bind h (sim_opt Iff.rfl _))

theorem sim_listwith (p n : Nat) (o : Oid) {it it' : EncM Unit} (h : Sim base it it')
    (hz : n = 0 → Sim base it (pure ())) : Sim base (pyListWith p o it) (cListWith p o n it') := by
  unfold pyListWith cListWith
  refine sim_bind (sim_emptyop p _ _) (sim_bind (sim_memoize p o) ?_)
  by_cases hn : n = 0
  · rw [if_neg (by simpa using hn)]; exact hz hn
  · rw [if_pos hn]; exact h

mutual
theorem simSave (base : List Event) (p : Nat) (hp : p ≤ 5) :
    (x : PV) → BatchOk p x → IntsOk x → Sim base (pySave p x) (cSave p x)
  | .none, _, _ => by
    rw [pySave, cSave]; exact sim_bind (sim_emit _ trivial) (sim_wr _)
  | .bool b, _, _ => by
    rw [pySave, cSave]
    exact sim_bind (sim_emit _ trivial) (by split <;> exact sim_wr _)
  | .int i, _, hi => by
    rw [pySave, cSave, ← saveLongTwinsAgreeSized_proven p i hp hi]
    exact sim_bind (sim_emit _ trivial) (sim_lift (by
      cases cSaveLong p i <;> simp [SameOutcome]) (fun v => sim_wr v))
  | .str o s, _, _ => by rw [pySave, cSave]; exact sim_strobj p o s
  | .bytes o b, _, _ => by rw [pySave, cSave]; exact sim_bytesobj p o b
  | .bytearray o b, _, _ => by rw [pySave, cSave]; exact sim_bytearrayobj p o b
  | .tuple o xs, h1, h2 => by
    rw [pySave, cSave]
    exact sim_tupleobj p xs.length o (simElems base p hp xs (by simpa [BatchOk] using h1) (by simpa [IntsOk] using h2))
  | .list o xs, h1, h2 => by
    rw [pySave, cSave]
    rw [BatchOk] at h1
    rw [IntsOk] at h2
    have h3 := h1.1
    refine sim_bind (sim_emit _ trivial) (sim_memo o (sim_get_or ?_))
    refine sim_listwith p xs.length o
      (simAppends base p hp xs.length (by omega) xs 0 (by omega) h1.2 h2) ?_
    intro hn
    have hx : xs = [] := List.length_eq_zero_iff.mp hn
    subst hx
    rw [pyAppends]
    exact sim_pure
  | .dict o kvs, h1, h2 => by
    rw [pySave, cSave]
    rw [BatchOk] at h1
    rw [IntsOk] at h2
    have h3 := h1.1
    refine sim_bind (sim_emit _ trivial) (sim_memo o (sim_get_or ?_))
    refine sim_bind (sim_emptyop p _ _) (sim_bind (sim_memoize p o) ?_)
    by_cases hn : kvs.length = 0
    · have hx : kvs = [] := List.length_eq_zero_iff.mp hn
      subst hx
      rw [pySetitems]
      exact sim_pure
    · rw [if_pos hn]
      exact simSetitems base p hp kvs.length (by omega) (by omega) (by omega) kvs 0 (by omega) h1.2 h2
  | .set o xs, h1, h2 => by
    rw [pySave, cSave]
    rw [BatchOk] at h1
    rw [IntsOk] at h2
    have h3 := h1.1
    refine sim_bind (sim_emit _ trivial) (sim_memo o (sim_get_or ?_))
    by_cases h4 : p < 4
    · rw [if_pos h4, if_pos h4]
      rw [if_neg (by omega)] at h3
      refine sim_reduce p o .set (sim_tupleobj p 1 _ (sim_bind (sim_emit _ trivial) ?_))
      refine sim_listwith p xs.length _
        (simAppends base p hp xs.length (by omega) xs 0 (by omega) h1.2 h2) ?_
      intro hn
      have hx : xs = [] := List.length_eq_zero_iff.mp hn
      subst hx
      rw [pyAppends]
      exact sim_pure
    · rw [if_neg h4, if_neg h4]
      rw [if_pos (by omega)] at h3
      refine sim_bind (sim_wr _) (sim_bind (sim_memoize p o) ?_)
      by_cases hn : xs.length = 0
      · have hx : xs = [] := List.length_eq_zero_iff.mp hn
        subst hx
        rw [pyAdditems]
        exact sim_pure
      · rw [if_pos hn]
        exact simAdditems base p hp xs.length (by omega) xs 0 (by omega) h1.2 h2
  | .frozenset o xs, h1, h2 => by
    rw [pySave, cSave]
    rw [BatchOk] at h1
    rw [IntsOk] at h2
    have h3 := h1.1
    refine sim_bind (sim_emit _ trivial) (sim_memo o (sim_get_or ?_))
    by_cases h4 : p < 4
    · rw [if_pos h4, if_pos h4]
      have h5 := h3 h4
      refine sim_reduce p o .frozenset (sim_tupleobj p 1 _ (sim_bind (sim_emit _ trivial) ?_))
      refine sim_listwith p xs.length _
        (simAppends base p hp xs.length (by omega) xs 0 (by omega) h1.2 h2) ?_
      intro hn
      have hx : xs = [] := List.length_eq_zero_iff.mp hn
      subst hx
      rw [pyAppends]
      exact sim_pure
    · rw [if_neg h4, if_neg h4]
      refine sim_bind (sim_wr _) (sim_bind (simElems base p hp xs h1.2 h2) (sim_memo o ?_))
      intro v
      cases v with
      | some i => exact sim_op_get p i oPOP_MARK
      | none => exact sim_bind (sim_wr _) (sim_memoize p o)

theorem simElems (base : List Event) (p : Nat) (hp : p ≤ 5) :
    (xs : List PV) → BatchOkList p xs → IntsOkList xs → Sim base (pySaveElems p xs) (cSaveElems p xs)
  | [], _, _ => by rw [pySaveElems, cSaveElems]; exact sim_pure
  | x :: xs, h1, h2 => by
    rw [pySaveElems, cSaveElems]
    exact sim_bind (simSave base p hp x h1.1 h2.1) (simElems base p hp xs h1.2 h2.2)

theorem simAppends (base : List Event) (p : Nat) (hp : p ≤ 5) (n : Nat)
    (hc : p = 0 ∨ n ≤ 1 ∨ n % 1000 ≠ 1) :
    (xs : List PV) → (i : Nat) → i + xs.length = n → BatchOkList p xs → IntsOkList xs →
      Sim base (pyAppends p n i xs) (cAppends p n i xs)
  | [], _, _, _, _ => by rw [pyAppends, cAppends]; exact sim_pure
  | x :: xs, i, hl, h1, h2 => by
    simp only [List.length_cons] at hl
    rw [pyAppends, cAppends]
    exact sim_bind (sim_batchStep p n i hc (by omega) (simSave base p hp x h1.1 h2.1) _ _)
      (simAppends base p hp n hc xs (i + 1) (by omega) h1.2 h2.2)

theorem simSetitems (base : List Event) (p : Nat) (hp : p ≤ 5) (n : Nat)
    (hc : p = 0 ∨ n ≤ 1 ∨ n % 1000 ≠ 1) (hn0 : n ≠ 0) (hc2 : p = 0 ∨ n ≤ 1 ∨ n % 1000 ≠ 0) :
    (kvs : List (PV × PV)) → (i : Nat) → i + kvs.length = n → BatchOkPairs p kvs → IntsOkPairs kvs →
      Sim base (pySetitems p n i kvs) (cSetitems p n i kvs)
  | [], _, _, _, _ => by
    rw [pySetitems, cSetitems, if_neg (by simp only [batchSize]; omega)]
    exact sim_pure
  | (k, v) :: kvs, i, hl, h1, h2 => by
    simp only [List.length_cons] at hl
    rw [pySetitems, cSetitems]
    exact sim_bind (sim_batchStep p n i hc (by omega)
        (sim_bind (simSave base p hp k h1.1 h2.1) (simSave base p hp v h1.2.1 h2.2.1)) _ _)
      (simSetitems base p hp n hc hn0 hc2 kvs (i + 1) (by omega) h1.2.2 h2.2.2)

theorem simAdditems (base : List Event) (p : Nat) (hp : p ≤ 5) (n : Nat)
    (hc : n % 1000 ≠ 0) :
    (xs : List PV) → (i : Nat) → i + xs.length = n → BatchOkList p xs → IntsOkList xs →
      Sim base (pyAdditems p n i xs) (cAdditems p n i xs)
  | [], _, _, _, _ => by
    rw [pyAdditems, cAdditems, if_neg (by simp only [batchSize]; omega)]
    exact sim_pure
  | x :: xs, i, hl, h1, h2 => by
    simp only [List.length_cons] at hl
    rw [pyAdditems, cAdditems]
    exact sim_bind (sim_addStep n i (simSave base p hp x h1.1 h2.1))
      (simAdditems base p hp n hc xs (i + 1) (by omega) h1.2 h2.2)
end

end PyLean.Pickle
