import PyLean.JsonMod.DecProps

/-!
The fuel the decoder models are given is always enough: `PyExc.modelFuel` is
never the outcome of `raw_decode` or `loads`, so the twin agreement theorems are
about real Python outcomes. Every two nested calls of the C scanner consume a
character.
-/

namespace PyLean.JsonMod

open PyLean

/-- Not out of fuel, and a value ends after `e`. -/
def Good {α : Type} (e : Nat) (r : DR (α × Nat)) : Prop :=
  r ≠ fuelOut ∧ ∀ (v : α) (k : Nat), r = .ok (v, k) → e < k

theorem Good.err {α : Type} {e : Nat} {x : DErr} (h : x ≠ .exc .modelFuel) : Good (α := α) e (.error x) := by
  refine ⟨?_, fun _ _ h => by cases h⟩
  intro h'
  exact h (Except.error.inj h')

theorem Good.ok' {α : Type} {e k : Nat} (v : α) (h : e < k) : Good e (.ok (v, k)) :=
  ⟨by simp [fuelOut], fun _ _ h' => by cases h'; exact h⟩

theorem Good.mono {α : Type} {e e' : Nat} {r : DR (α × Nat)} (h : Good e' r) (he : e ≤ e') : Good e r :=
  ⟨h.1, fun v k hr => by have := h.2 v k hr; omega⟩

theorem cFind_found_lt : ∀ (strict : Bool) (t : PStr) (k : Nat), cFind strict t = .found k → k < t.length
  | _, [], _, h => by simp [cFind] at h
  | strict, d :: t, k, h => by
    simp only [cFind] at h
    split at h
    · cases h; simp
    · split at h
      · cases h
      · cases hf : cFind strict t with
        | found k' =>
          rw [hf] at h
          simp only [CFind.found.injEq] at h
          have := cFind_found_lt strict t k' hf
          simp; omega
        | ctrl k' => rw [hf] at h; cases h
        | eof => rw [hf] at h; cases h

theorem scanLoop_good (s : PStr) (strict : Bool) (b : Nat) :
    ∀ (g e : Nat) (acc : Option PStr), s.length + 1 - e ≤ g → e ≤ s.length →
      Good e (cScanLoop s strict b g e acc) := by
  intro g
  induction g with
  | zero => intro e acc h1 h2; omega
  | succ g ih =>
    intro e acc h1 h2
    have step : ∀ (e' : Nat) (acc' : Option PStr), e < e' → e' ≤ s.length →
        Good e (cScanLoop s strict b g e' acc') :=
      fun e' acc' h3 h4 => (ih e' acc' (by omega) h4).mono (by omega)
    simp only [cScanLoop]
    cases hf : cFind strict (s.drop e) with
    | ctrl k => exact Good.err (by simp)
    | eof => exact Good.err (by simp)
    | found k =>
      have hk := cFind_found_lt _ _ _ hf
      simp only [List.length_drop] at hk
      dsimp only
      split
      · exact Good.ok' _ (by omega)
      · split
        · exact Good.ok' _ (by omega)
        · split
          · exact Good.err (by simp)
          · rename_i hne
            split
            · split
              · exact Good.err (by simp)
              · exact step _ _ (by omega) (by omega)
            · split
              · exact Good.err (by simp)
              · rename_i hend
                split
                · exact Good.err (by simp)
                · split
                  · rename_i hp
                    split
                    · exact Good.err (by simp)
                    · split
                      · exact step _ _ (by omega) (by omega)
                      · exact step _ _ (by omega) (by omega)
                  · exact step _ _ (by omega) (by omega)

theorem scanstring_good (s : PStr) (e : Nat) (strict : Bool) : Good e (cScanstring s e strict) := by
  unfold cScanstring
  split
  · exact Good.err (by simp)
  · exact scanLoop_good s strict (e - 1) (s.length + 1) e none (by omega) (by omega)

theorem parseInt_map_good (cfg : DCfg) (t : PStr) (e k : Nat) (h : e < k) :
    Good e ((parseInt cfg t).map (fun x => (x, k))) := by
  unfold parseInt
  split
  · exact Good.ok' _ h
  · cases hp : pyIntOfText t with
    | ok n => exact Good.ok' _ h
    | error x =>
      apply Good.err
      intro hx
      simp only [DErr.exc.injEq] at hx
      subst hx
      unfold pyIntOfText at hp
      dsimp only at hp
      split at hp
      · split at hp
        · cases hp
        · cases hp
      · split at hp
        · cases hp
        · cases hp

theorem reInt_pos {t ip : PStr} (h : reInt t = some ip) : 1 ≤ ip.length := by
  cases t with
  | nil => simp [reInt] at h
  | cons c r =>
    rw [reInt_cons] at h
    split at h
    · cases h; simp
    · split at h
      · cases h; simp
      · cases h

theorem numberRe_pos {t i fr ex : PStr} (h : numberRe t = some (i, fr, ex)) : 1 ≤ i.length := by
  unfold numberRe at h
  generalize reSign t = p at h
  obtain ⟨sign, t1⟩ := p
  simp only at h
  cases hi : reInt t1 with
  | none => rw [hi] at h; cases h
  | some ip =>
    rw [hi] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -, -⟩ := h
    have := reInt_pos hi
    simp; omega

theorem matchNumber_good (cfg : DCfg) (s : PStr) (idx : Nat) (h : idx < s.length) :
    Good idx (cMatchNumber cfg s idx) := by
  rcases matchNumber_twin cfg s idx h with ⟨_, h2⟩ | ⟨i, fr, ex, h1, h2⟩
  · rw [h2]; exact Good.err (by simp)
  · have := numberRe_pos h1
    rw [h2]
    split
    · exact Good.ok' _ (by omega)
    · exact parseInt_map_good _ _ _ _ (by omega)

theorem cArrAfter_close' {s : PStr} {e : Nat} {i : Int} (h : cArrAfter s e = .close i) :
    ∃ m : Nat, i = m ∧ e < m := by
  unfold cArrAfter at h
  dsimp only at h
  have := wsEnd_ge s e
  split at h
  · cases h; exact ⟨_, rfl, by omega⟩
  · split at h
    · cases h
    · split at h <;> cases h

theorem cArrAfter_next' {s : PStr} {e : Nat} {i : Int} (h : cArrAfter s e = .next i) :
    ∃ m : Nat, i = m ∧ e < m ∧ e < s.length := by
  unfold cArrAfter at h
  dsimp only at h
  have h1 := wsEnd_ge s e
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i hc
      split at h
      · cases h
      · cases h
        have h2 := wsEnd_ge s (wsEnd s e + 1)
        exact ⟨_, rfl, by omega, by omega⟩

theorem cObjAfter_close' {s : PStr} {e : Nat} {i : Int} (h : cObjAfter s e = .close i) :
    ∃ m : Nat, i = m ∧ e < m := by
  unfold cObjAfter at h
  dsimp only at h
  have := wsEnd_ge s e
  split at h
  · cases h; exact ⟨_, rfl, by omega⟩
  · split at h
    · cases h
    · split at h <;> cases h

theorem cObjAfter_next' {s : PStr} {e : Nat} {i : Int} (h : cObjAfter s e = .next i) :
    ∃ m : Nat, i = m ∧ e < m := by
  unfold cObjAfter at h
  dsimp only at h
  have h1 := wsEnd_ge s e
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · cases h
        have h2 := wsEnd_ge s (wsEnd s e + 1)
        exact ⟨_, rfl, by omega⟩

theorem cConst_good (name : String) (idx : Nat) (h : 1 ≤ (cs name).length) : Good idx (cConst name idx) :=
  Good.ok' _ (by omega)

/-- The C scanner never runs out of fuel when it has `2 * (len - idx) + 3`. -/
theorem nofuel (cfg : DCfg) (s : PStr) : ∀ n : Nat,
    (∀ idx : Nat, 2 * (s.length - idx) + 3 ≤ n → Good idx (cScanOnce cfg s n idx)) ∧
    (∀ (e : Nat) (acc : List JVal), 2 * (s.length - e) + 4 ≤ n → Good e (cArrLoop cfg s n e acc)) ∧
    (∀ (q : Nat) (acc : List (PStr × JVal)), 2 * (s.length - q) + 4 ≤ n →
      Good q (cObjBody cfg s n q acc)) := by
  intro n
  induction n with
  | zero =>
    refine ⟨fun idx h => ?_, fun e acc h => ?_, fun q acc h => ?_⟩ <;> omega
  | succ n ih =>
    obtain ⟨ihS, ihA, ihO⟩ := ih
    refine ⟨fun idx h => ?_, fun e acc h => ?_, fun q acc h => ?_⟩
    · simp only [cScanOnce]
      split
      · exact Good.err (by simp)
      · rename_i hl
        have hlt : idx < s.length := by omega
        have hw := wsEnd_ge s (idx + 1)
        split
        · have := scanstring_good s (idx + 1) cfg.strict
          cases hr : cScanstring s (idx + 1) cfg.strict with
          | error x =>
            rw [hr] at this
            refine Good.err (fun hx => this.1 ?_)
            subst hx; rfl
          | ok r =>
            obtain ⟨v, k⟩ := r
            rw [hr] at this
            have := this.2 v k rfl
            exact Good.ok' _ (by omega)
        · split
          · split
            · split
              · exact Good.err (by simp)
              · exact (ihO _ _ (by omega)).mono (by omega)
            · exact Good.ok' _ (by omega)
          · split
            · split
              · exact (ihA _ _ (by omega)).mono (by omega)
              · exact Good.ok' _ (by omega)
            · split
              · exact Good.ok' _ (by omega)
              · split
                · exact Good.ok' _ (by omega)
                · split
                  · exact Good.ok' _ (by omega)
                  · split
                    · exact cConst_good _ _ (by decide)
                    · split
                      · exact cConst_good _ _ (by decide)
                      · split
                        · exact cConst_good _ _ (by decide)
                        · exact matchNumber_good cfg s idx hlt
    · simp only [cArrLoop]
      have hS := ihS e (by omega)
      cases hr : cScanOnce cfg s n e with
      | error x =>
        refine Good.err (fun hx => hS.1 ?_)
        rw [hr, hx]; rfl
      | ok r =>
        obtain ⟨v, k⟩ := r
        have hk := hS.2 v k hr
        dsimp only
        cases ha : cArrAfter s k with
        | close i =>
          obtain ⟨m, rfl, hm⟩ := cArrAfter_close' ha
          exact Good.ok' _ (by simp; omega)
        | err x =>
          apply Good.err
          intro hx
          subst hx
          unfold cArrAfter at ha
          dsimp only at ha
          split at ha
          · cases ha
          · split at ha
            · cases ha
            · split at ha <;> cases ha
        | next i =>
          obtain ⟨m, rfl, hm, hl⟩ := cArrAfter_next' ha
          simp only [Int.toNat_natCast]
          exact (ihA m _ (by omega)).mono (by omega)
    · simp only [cObjBody]
      have hsg := scanstring_good s (q + 1) cfg.strict
      cases hr : cScanstring s (q + 1) cfg.strict with
      | error x =>
        refine Good.err (fun hx => hsg.1 ?_)
        rw [hr, hx]; rfl
      | ok r =>
        obtain ⟨key, k⟩ := r
        have hk := hsg.2 key k hr
        dsimp only
        have hw := wsEnd_ge s k
        split
        · exact Good.err (by simp)
        · rename_i hcol
          have hw2 := wsEnd_ge s (wsEnd s k + 1)
          have hS := ihS (wsEnd s (wsEnd s k + 1)) (by omega)
          cases hv : cScanOnce cfg s n (wsEnd s (wsEnd s k + 1)) with
          | error x =>
            refine Good.err (fun hx => hS.1 ?_)
            rw [hv, hx]; rfl
          | ok r2 =>
            obtain ⟨v, k2⟩ := r2
            have hk2 := hS.2 v k2 hv
            dsimp only
            cases ha : cObjAfter s k2 with
            | close i =>
              obtain ⟨m, rfl, hm⟩ := cObjAfter_close' ha
              exact Good.ok' _ (by simp; omega)
            | err x =>
              apply Good.err
              intro hx
              subst hx
              unfold cObjAfter at ha
              dsimp only at ha
              split at ha
              · cases ha
              · split at ha
                · cases ha
                · split at ha <;> cases ha
            | next i =>
              obtain ⟨m, rfl, hm⟩ := cObjAfter_next' ha
              simp only [Int.toNat_natCast]
              split
              · exact Good.err (by simp)
              · rename_i hq
                exact (ihO m _ (by omega)).mono (by omega)

/-- `cScanOnce` with the document's fuel never runs out. -/
theorem docFuel_good (cfg : DCfg) (s : PStr) (idx : Nat) : Good idx (cScanOnce cfg s (docFuel s) idx) :=
  (nofuel cfg s (docFuel s)).1 idx (by simp only [docFuel]; omega)

/-- `raw_decode(s, idx)`, for `0 <= idx <= sys.maxsize`, and `json.loads(s)`
(`len(s) <= sys.maxsize`) always end with a value or a Python exception in both
twins: the models never run out of fuel, and in particular neither Python
function hangs. (`RecursionError` on deep nesting is out of scope.) -/
def DecodeTerminates : Prop :=
  ∀ (cfg : DCfg) (s : PStr) (idx : Int), 0 ≤ idx → idx ≤ ssizeMax →
    rawDecodePy cfg s idx ≠ fuelOut ∧ rawDecodeC cfg s idx ≠ fuelOut

theorem decodeTerminates_proven : DecodeTerminates := by
  intro cfg s idx h0 h1
  obtain ⟨n, rfl⟩ : ∃ n : Nat, idx = n := ⟨idx.toNat, by omega⟩
  have hg := docFuel_good cfg s n
  have hc : rawDecodeC cfg s (n : Int) ≠ fuelOut := by
    have hr : ¬ ((n : Int) < ssizeMin ∨ (n : Int) > ssizeMax) := by
      simp only [ssizeMin, ssizeMax] at h1 ⊢; omega
    have hn : ¬ ((n : Int) < 0) := by omega
    simp only [rawDecodeC, hr, hn, ↓reduceIte, Int.toNat_natCast]
    cases hs : cScanOnce cfg s (docFuel s) n with
    | ok r => obtain ⟨v, k⟩ := r; simp [stopToJde, fuelOut]
    | error x =>
      intro h
      cases x with
      | stop i => simp [stopToJde, fuelOut] at h
      | jde m p => simp [stopToJde, fuelOut] at h
      | exc e =>
        simp [stopToJde, fuelOut] at h
        subst h
        exact hg.1 hs
  refine ⟨?_, hc⟩
  rcases rawDecodeTwinsInRange_proven cfg s n h0 h1 with h | ⟨_, _, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩
  · rw [h]; exact hc
  · rw [h]; simp [fuelOut]
  · rw [h]; simp [fuelOut]

end PyLean.JsonMod
