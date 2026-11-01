import PyLean.JsonMod.DecFuel

/-!
`strict`: "If strict is false (true is the default), then control characters
will be allowed inside strings. Control characters in this context are those
with character codes in the 0-31 range" (`JSONDecoder.__init__`,
decoder.py:322-325). `strict=True` differs from `strict=False` only by an
"Invalid control character" error at such a character, in both twins.
-/

namespace PyLean.JsonMod

open PyLean

/-- `strict=True` gives the same outcome as `strict=False`, or an invalid
control character error at a control character. -/
def SRel {α : Type} (s : PStr) (msg : Nat → String) (a b : DR α) : Prop :=
  a = b ∨ ∃ (q ch : Nat), s[q]? = some ch ∧ ch < 32 ∧ a = .error (.jde (msg ch) (q : Int))

theorem SRel.rfl' {α : Type} {s : PStr} {msg : Nat → String} (a : DR α) : SRel s msg a a := Or.inl rfl

theorem SRel.ite {α : Type} {s : PStr} {msg : Nat → String} (c : Prop) [Decidable c] {a b a' b' : DR α}
    (h1 : c → SRel s msg a a') (h2 : ¬c → SRel s msg b b') :
    SRel s msg (if c then a else b) (if c then a' else b') := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte]; exact h1 hc
  · simp only [hc, ↓reduceIte]; exact h2 hc

/-! ### `py_scanstring` -/

theorem pyLoop_srel (s : PStr) (b : Int) : ∀ (f e : Nat) (acc : PStr),
    SRel s ctrlMsgPy (pyScanLoop s true b f e acc) (pyScanLoop s false b f e acc) := by
  intro f
  induction f with
  | zero => intro e acc; exact Or.inl rfl
  | succ f ih =>
    intro e acc
    simp only [pyScanLoop]
    cases hf : findTerm (s.drop e) with
    | none => exact Or.inl rfl
    | some k =>
      obtain ⟨hk, hterm, _⟩ := findTerm_spec _ k hf
      simp only [List.length_drop] at hk
      rw [getD_drop] at hterm
      have hs0 := getElem?_of_lt s (show e + k < s.length by omega)
      dsimp only
      generalize hc0 : s.getD (e + k) 0 = c0 at hs0 hterm
      refine SRel.ite _ (fun _ => Or.inl rfl) (fun h34 => ?_)
      by_cases h92 : c0 = 92
      rotate_left
      · simp only [ne_eq, h92, not_false_eq_true, ↓reduceIte, Bool.false_eq_true, eq_self]
        right
        refine ⟨e + k, c0, hs0, ?_, ?_⟩
        · simp [isTerm] at hterm; omega
        · rw [show ((e + k + 1 : Nat) : Int) - 1 = ((e + k : Nat) : Int) by omega]
      · simp only [ne_eq, h92, not_true_eq_false, ↓reduceIte]
        cases hesc : s[e + k + 1]? with
        | none => exact Or.inl rfl
        | some esc =>
          simp only
          refine SRel.ite _ (fun _ => ?_) (fun _ => ?_)
          · cases backslash esc with
            | none => exact Or.inl rfl
            | some ch => exact ih _ _
          · cases decodeUXXXX s (e + k + 1) with
            | error err => exact Or.inl rfl
            | ok uni =>
              simp only
              refine SRel.ite _ (fun _ => ?_) (fun _ => ih _ _)
              cases decodeUXXXX s (e + k + 1 + 5 + 1) with
              | error err => exact Or.inl rfl
              | ok uni2 =>
                simp only
                exact SRel.ite _ (fun _ => ih _ _) (fun _ => ih _ _)

/-- `strict` only enters the pure-Python scanner through `py_scanstring`. -/
theorem pyStr_srel (s : PStr) (e : Int) :
    SRel s ctrlMsgPy (pyScanstring s e true) (pyScanstring s e false) :=
  pyLoop_srel s (e - 1) _ _ _

theorem pyScanNumber_strict (cfg : DCfg) (a b : Bool) (s : PStr) (idx : Int) (c : Nat) :
    pyScanNumber { cfg with strict := a } s idx c = pyScanNumber { cfg with strict := b } s idx c := rfl

theorem pyMkObj_strict (cfg : DCfg) (a b : Bool) (p : List (PStr × JVal)) :
    pyMkObj { cfg with strict := a } p = pyMkObj { cfg with strict := b } p := rfl

theorem py_srel (cfg : DCfg) (s : PStr) : ∀ n : Nat,
    (∀ idx : Int, SRel s ctrlMsgPy (pyScanOnce { cfg with strict := true } s n idx)
      (pyScanOnce { cfg with strict := false } s n idx)) ∧
    (∀ (e : Int) (acc : List JVal), SRel s ctrlMsgPy (pyArrLoop { cfg with strict := true } s n e acc)
      (pyArrLoop { cfg with strict := false } s n e acc)) ∧
    (∀ (e : Int) (acc : List (PStr × JVal)), SRel s ctrlMsgPy (pyObjLoop { cfg with strict := true } s n e acc)
      (pyObjLoop { cfg with strict := false } s n e acc)) := by
  intro n
  induction n with
  | zero => exact ⟨fun _ => Or.inl rfl, fun _ _ => Or.inl rfl, fun _ _ => Or.inl rfl⟩
  | succ n ih =>
    obtain ⟨ihS, ihA, ihO⟩ := ih
    refine ⟨fun idx => ?_, fun e acc => ?_, fun e acc => ?_⟩
    · simp only [pyScanOnce]
      cases hi : pyIndex s idx with
      | none => exact Or.inl rfl
      | some c =>
        simp only
        refine SRel.ite _ (fun _ => ?_) (fun _ => ?_)
        · rcases pyStr_srel s (idx + 1) with h | ⟨q, ch, h1, h2, h3⟩
          · rw [h]
            exact Or.inl rfl
          · rw [h3]
            exact Or.inr ⟨q, ch, h1, h2, rfl⟩
        · refine SRel.ite _ (fun _ => ?_) (fun _ => ?_)
          · refine SRel.ite _ (fun _ => ?_) (fun _ => ihO _ _)
            generalize (if inWsSlice (pySlice s (idx + 1) (idx + 1 + 1)) = true then
                (wsEndPy s (idx + 1), pySlice s (wsEndPy s (idx + 1)) (wsEndPy s (idx + 1) + 1))
              else (idx + 1, pySlice s (idx + 1) (idx + 1 + 1))) = p
            obtain ⟨e', nc⟩ := p
            simp only
            refine SRel.ite _ (fun _ => Or.inl rfl) (fun _ => ?_)
            exact SRel.ite _ (fun _ => Or.inl rfl) (fun _ => ihO _ _)
          · refine SRel.ite _ (fun _ => ?_) (fun _ => ?_)
            · generalize (if inWsSlice (pySlice s (idx + 1) (idx + 1 + 1)) = true then
                  (wsEndPy s (idx + 1 + 1), pySlice s (wsEndPy s (idx + 1 + 1)) (wsEndPy s (idx + 1 + 1) + 1))
                else (idx + 1, pySlice s (idx + 1) (idx + 1 + 1))) = p
              obtain ⟨e', nc⟩ := p
              simp only
              exact SRel.ite _ (fun _ => Or.inl rfl) (fun _ => ihA _ _)
            · refine SRel.ite _ (fun _ => Or.inl rfl) (fun _ => ?_)
              refine SRel.ite _ (fun _ => Or.inl rfl) (fun _ => ?_)
              refine SRel.ite _ (fun _ => Or.inl rfl) (fun _ => ?_)
              exact Or.inl rfl
    · simp only [pyArrLoop]
      rcases ihS e with h | ⟨q, ch, h1, h2, h3⟩
      · rw [h]
        cases hr : pyScanOnce { cfg with strict := false } s n e with
        | error x => cases x <;> exact Or.inl rfl
        | ok r =>
          obtain ⟨v, e'⟩ := r
          simp only
          cases pyArrAfter s e' with
          | close i => exact Or.inl rfl
          | err x => exact Or.inl rfl
          | next i => exact ihA _ _
      · rw [h3]
        exact Or.inr ⟨q, ch, h1, h2, rfl⟩
    · simp only [pyObjLoop]
      rcases pyStr_srel s e with h | ⟨q, ch, h1, h2, h3⟩
      · simp only [h]
        cases hr : pyScanstring s e false with
        | error x => exact Or.inl rfl
        | ok r =>
          obtain ⟨key, e'⟩ := r
          simp only
          cases pyObjColon s e' with
          | error x => exact Or.inl rfl
          | ok e2 =>
            simp only
            rcases ihS e2 with h4 | ⟨q, ch, h1, h2, h3⟩
            · rw [h4]
              cases hv : pyScanOnce { cfg with strict := false } s n e2 with
              | error x => cases x <;> exact Or.inl rfl
              | ok r2 =>
                obtain ⟨v, e3⟩ := r2
                simp only
                cases pyObjAfter s e3 with
                | close i => exact Or.inl rfl
                | err x => exact Or.inl rfl
                | next i => exact ihO _ _
            · rw [h3]
              exact Or.inr ⟨q, ch, h1, h2, rfl⟩
      · simp only [h3]
        exact Or.inr ⟨q, ch, h1, h2, rfl⟩

/-! ### `scanstring_unicode` -/

theorem cFind_strict_rel : ∀ t : PStr,
    cFind true t = cFind false t ∨ ∃ k, cFind true t = .ctrl k ∧ t.getD k 0 < 32
  | [] => Or.inl rfl
  | d :: t => by
    by_cases h1 : d = 34 ∨ d = 92
    · left; simp [cFind, h1]
    · by_cases h2 : d ≤ 31
      · right
        exact ⟨0, by simp [cFind, h1, h2], by simp; omega⟩
      · have h3 : ∀ b : Bool, cFind b (d :: t) = (match cFind b t with
            | .found k => .found (k + 1) | .ctrl k => .ctrl (k + 1) | .eof => .eof) := by
          intro b
          simp only [cFind, h1, ↓reduceIte, h2, false_and]
          cases cFind b t <;> rfl
        rw [h3 true, h3 false]
        rcases cFind_strict_rel t with h | ⟨k, h, hk⟩
        · left; rw [h]
        · right
          refine ⟨k + 1, by rw [h], by simpa using hk⟩

theorem cFind_ctrl_lt : ∀ (strict : Bool) (t : PStr) (k : Nat), cFind strict t = .ctrl k → k < t.length
  | _, [], _, h => by simp [cFind] at h
  | strict, d :: t, k, h => by
    simp only [cFind] at h
    split at h
    · cases h
    · split at h
      · cases h; simp
      · cases hf : cFind strict t with
        | found k' => rw [hf] at h; cases h
        | ctrl k' =>
          rw [hf] at h
          simp only [CFind.ctrl.injEq] at h
          have := cFind_ctrl_lt strict t k' hf
          simp; omega
        | eof => rw [hf] at h; cases h

theorem cLoop_srel (s : PStr) (b : Nat) : ∀ (g e : Nat) (acc : Option PStr),
    SRel s (fun _ => "Invalid control character at") (cScanLoop s true b g e acc) (cScanLoop s false b g e acc) := by
  intro g
  induction g with
  | zero => intro e acc; exact Or.inl rfl
  | succ g ih =>
    intro e acc
    simp only [cScanLoop]
    rcases cFind_strict_rel (s.drop e) with h | ⟨k, h, hk⟩
    · rw [h]
      cases hf : cFind false (s.drop e) with
      | ctrl k => exact absurd hf (cFind_false_ne_ctrl _ k)
      | eof => exact Or.inl rfl
      | found k =>
        dsimp only
        refine SRel.ite _ (fun _ => Or.inl rfl) (fun _ => ?_)
        refine SRel.ite _ (fun _ => Or.inl rfl) (fun _ => ?_)
        refine SRel.ite _ (fun _ => Or.inl rfl) (fun _ => ?_)
        refine SRel.ite _ (fun _ => ?_) (fun _ => ?_)
        · cases backslash _ with
          | none => exact Or.inl rfl
          | some ch => exact ih _ _
        · refine SRel.ite _ (fun _ => Or.inl rfl) (fun _ => ?_)
          cases hex4 _ _ with
          | none => exact Or.inl rfl
          | some c =>
            simp only
            refine SRel.ite _ (fun _ => ?_) (fun _ => ih _ _)
            cases hex4 _ _ with
            | none => exact Or.inl rfl
            | some c2 =>
              simp only
              exact SRel.ite _ (fun _ => ih _ _) (fun _ => ih _ _)
    · rw [h]
      right
      rw [getD_drop] at hk
      have hlt : e + k < s.length := by
        have := cFind_ctrl_lt _ _ _ h
        simp only [List.length_drop] at this
        omega
      exact ⟨e + k, s.getD (e + k) 0, getElem?_of_lt s hlt, hk, rfl⟩

theorem cStr_srel (s : PStr) (e : Nat) :
    SRel s (fun _ => "Invalid control character at") (cScanstring s e true) (cScanstring s e false) := by
  unfold cScanstring
  exact SRel.ite _ (fun _ => Or.inl rfl) (fun _ => cLoop_srel s (e - 1) _ _ _)

theorem c_srel (cfg : DCfg) (s : PStr) : ∀ n : Nat,
    (∀ idx : Nat, SRel s (fun _ => "Invalid control character at")
      (cScanOnce { cfg with strict := true } s n idx) (cScanOnce { cfg with strict := false } s n idx)) ∧
    (∀ (e : Nat) (acc : List JVal), SRel s (fun _ => "Invalid control character at")
      (cArrLoop { cfg with strict := true } s n e acc) (cArrLoop { cfg with strict := false } s n e acc)) ∧
    (∀ (q : Nat) (acc : List (PStr × JVal)), SRel s (fun _ => "Invalid control character at")
      (cObjBody { cfg with strict := true } s n q acc) (cObjBody { cfg with strict := false } s n q acc)) := by
  intro n
  induction n with
  | zero => exact ⟨fun _ => Or.inl rfl, fun _ _ => Or.inl rfl, fun _ _ => Or.inl rfl⟩
  | succ n ih =>
    obtain ⟨ihS, ihA, ihO⟩ := ih
    refine ⟨fun idx => ?_, fun e acc => ?_, fun q acc => ?_⟩
    · simp only [cScanOnce]
      refine SRel.ite _ (fun _ => Or.inl rfl) (fun _ => ?_)
      refine SRel.ite _ (fun _ => ?_) (fun _ => ?_)
      · rcases cStr_srel s (idx + 1) with h | ⟨q, ch, h1, h2, h3⟩
        · rw [h]
          exact Or.inl rfl
        · rw [h3]
          exact Or.inr ⟨q, ch, h1, h2, rfl⟩
      · refine SRel.ite _ (fun _ => ?_) (fun _ => ?_)
        · refine SRel.ite _ (fun _ => ?_) (fun _ => Or.inl rfl)
          exact SRel.ite _ (fun _ => Or.inl rfl) (fun _ => ihO _ _)
        · refine SRel.ite _ (fun _ => ?_) (fun _ => ?_)
          · exact SRel.ite _ (fun _ => ihA _ _) (fun _ => Or.inl rfl)
          · refine SRel.ite _ (fun _ => Or.inl rfl) (fun _ => ?_)
            refine SRel.ite _ (fun _ => Or.inl rfl) (fun _ => ?_)
            refine SRel.ite _ (fun _ => Or.inl rfl) (fun _ => ?_)
            refine SRel.ite _ (fun _ => Or.inl rfl) (fun _ => ?_)
            refine SRel.ite _ (fun _ => Or.inl rfl) (fun _ => ?_)
            refine SRel.ite _ (fun _ => Or.inl rfl) (fun _ => ?_)
            exact Or.inl rfl
    · simp only [cArrLoop]
      rcases ihS e with h | ⟨q, ch, h1, h2, h3⟩
      · rw [h]
        cases hr : cScanOnce { cfg with strict := false } s n e with
        | error x => exact Or.inl rfl
        | ok r =>
          obtain ⟨v, e'⟩ := r
          simp only
          cases cArrAfter s e' with
          | close i => exact Or.inl rfl
          | err x => exact Or.inl rfl
          | next i => exact ihA _ _
      · rw [h3]
        exact Or.inr ⟨q, ch, h1, h2, rfl⟩
    · simp only [cObjBody]
      rcases cStr_srel s (q + 1) with h | ⟨q', ch, h1, h2, h3⟩
      · simp only [h]
        cases hr : cScanstring s (q + 1) false with
        | error x => exact Or.inl rfl
        | ok r =>
          obtain ⟨key, e'⟩ := r
          simp only
          refine SRel.ite _ (fun _ => Or.inl rfl) (fun _ => ?_)
          rcases ihS (wsEnd s (wsEnd s e' + 1)) with h4 | ⟨q', ch, h1, h2, h3⟩
          · rw [h4]
            cases hv : cScanOnce { cfg with strict := false } s n (wsEnd s (wsEnd s e' + 1)) with
            | error x => exact Or.inl rfl
            | ok r2 =>
              obtain ⟨v, e3⟩ := r2
              simp only
              have hadd : cAddPair { cfg with strict := true } acc key v =
                  cAddPair { cfg with strict := false } acc key v := rfl
              rw [hadd]
              cases cObjAfter s e3 with
              | close i => exact Or.inl rfl
              | err x => exact Or.inl rfl
              | next i =>
                simp only
                exact SRel.ite _ (fun _ => Or.inl rfl) (fun _ => ihO _ _)
          · rw [h3]
            exact Or.inr ⟨q', ch, h1, h2, rfl⟩
      · simp only [h3]
        exact Or.inr ⟨q', ch, h1, h2, rfl⟩

theorem decodeWith_srel {s : PStr} {msg : Nat → String} {r1 r2 : PStr → Int → DR (JVal × Int)}
    (h : SRel s msg (r1 s (wsEnd s 0 : Nat)) (r2 s (wsEnd s 0 : Nat))) :
    SRel s msg (decodeWith r1 s) (decodeWith r2 s) := by
  unfold decodeWith
  rcases h with h | ⟨q, ch, h1, h2, h3⟩
  · rw [h]; exact Or.inl rfl
  · rw [h3]; exact Or.inr ⟨q, ch, h1, h2, rfl⟩

theorem stopToJde_srel {α : Type} {s : PStr} {msg : Nat → String} {a b : DR α} (h : SRel s msg a b) :
    SRel s msg (stopToJde a) (stopToJde b) := by
  rcases h with rfl | ⟨q, ch, h1, h2, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨q, ch, h1, h2, rfl⟩

/-- For every document, `strict=True` and `strict=False` give the same result,
except that `strict=True` may raise "Invalid control character" at a character
in the range 0-31, in both twins (`JSONDecoder.__init__`, decoder.py:322-325). -/
def StrictOnlyControl : Prop :=
  ∀ (cfg : DCfg) (s : PStr),
    SRel s ctrlMsgPy (loadsPy { cfg with strict := true } s) (loadsPy { cfg with strict := false } s) ∧
    SRel s (fun _ => "Invalid control character at")
      (loadsC { cfg with strict := true } s) (loadsC { cfg with strict := false } s)

theorem strictOnlyControl_proven : StrictOnlyControl := by
  intro cfg s
  constructor
  · apply decodeWith_srel
    exact stopToJde_srel ((py_srel cfg s (docFuel s)).1 _)
  · apply decodeWith_srel
    simp only [rawDecodeC]
    refine SRel.ite _ (fun _ => Or.inl rfl) (fun _ => ?_)
    refine SRel.ite _ (fun _ => Or.inl rfl) (fun _ => ?_)
    rcases stopToJde_srel ((c_srel cfg s (docFuel s)).1 (((wsEnd s 0 : Nat) : Int).toNat)) with h | ⟨q, ch, h1, h2, h3⟩
    · rw [h]
      exact Or.inl rfl
    · rw [h3]
      exact Or.inr ⟨q, ch, h1, h2, rfl⟩

end PyLean.JsonMod
