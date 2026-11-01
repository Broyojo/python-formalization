import PyLean.JsonMod.RoundTripTop
import PyLean.JsonMod.Strict

/-!
Documented behaviour: control characters in string literals, `ensure_ascii`,
and int literals under the 4300-digit limit.
-/

namespace PyLean.JsonMod

open PyLean

/-- `loads` when the C scanner raises at index 0. -/
theorem loads_of_scan_err (dcfg : DCfg) (d : PStr) (x : DErr)
    (hscan : cScanOnce dcfg d (docFuel d) 0 = .error x) (hw0 : wsEnd d 0 = 0) :
    (∃ e, loadsC dcfg d = .error e) ∧ (∃ e, loadsPy dcfg d = .error e) := by
  have hraw : ∃ e, rawDecodeC dcfg d ((0 : Nat) : Int) = .error e := by
    have hr : ¬ (((0 : Nat) : Int) < ssizeMin ∨ ((0 : Nat) : Int) > ssizeMax) := by
      simp only [ssizeMin, ssizeMax]; omega
    have hn : ¬ (((0 : Nat) : Int) < 0) := by omega
    simp only [rawDecodeC, hr, hn, ↓reduceIte, Int.toNat_natCast, hscan]
    cases x <;> exact ⟨_, rfl⟩
  obtain ⟨e, he⟩ := hraw
  have hpy : ∃ e, rawDecodePy dcfg d ((0 : Nat) : Int) = .error e := by
    have h0 : ((0 : Nat) : Int) ≤ ssizeMax := by simp only [ssizeMax]; omega
    rcases raw_nat_twin dcfg d 0 h0 with h | ⟨_, _, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩
    · exact ⟨e, by rw [h, he]⟩
    · exact ⟨_, h⟩
    · exact ⟨_, h⟩
  obtain ⟨e2, he2⟩ := hpy
  constructor
  · refine ⟨e, ?_⟩
    unfold loadsC decodeWith
    rw [hw0, he]
  · refine ⟨e2, ?_⟩
    unfold loadsPy decodeWith
    rw [hw0, he2]

/-- `loads` when the C scanner raises an exception other than
`JSONDecodeError` at index 0. -/
theorem loads_of_scan_exc (dcfg : DCfg) (d : PStr) (x : PyExc)
    (hscan : cScanOnce dcfg d (docFuel d) 0 = .error (.exc x)) (hw0 : wsEnd d 0 = 0) :
    loadsC dcfg d = .error (.exc x) ∧ loadsPy dcfg d = .error (.exc x) := by
  have hraw : rawDecodeC dcfg d ((0 : Nat) : Int) = .error (.exc x) := by
    have hr : ¬ (((0 : Nat) : Int) < ssizeMin ∨ ((0 : Nat) : Int) > ssizeMax) := by
      simp only [ssizeMin, ssizeMax]; omega
    have hn : ¬ (((0 : Nat) : Int) < 0) := by omega
    simp only [rawDecodeC, hr, hn, ↓reduceIte, Int.toNat_natCast, hscan]
    rfl
  have hpy : rawDecodePy dcfg d ((0 : Nat) : Int) = .error (.exc x) := by
    have h0 : ((0 : Nat) : Int) ≤ ssizeMax := by simp only [ssizeMax]; omega
    rcases raw_nat_twin dcfg d 0 h0 with h | ⟨_, _, _, _, h, _⟩ | ⟨_, _, _, _, h, _⟩
    · rw [h, hraw]
    · rw [hraw] at h; cases h
    · rw [hraw] at h; cases h
  constructor
  · unfold loadsC decodeWith
    rw [hw0, hraw]
  · unfold loadsPy decodeWith
    rw [hw0, hpy]

/-! ### `strict` on one string literal -/

/-- `py_scanstring` over text without quotes or backslashes. -/
theorem loopRaw (s : PStr) (strict : Bool) (b : Int) : ∀ (t : PStr) (f e : Nat) (a rest : PStr),
    t.length + 1 ≤ f → (∀ c ∈ t, c ≠ 34 ∧ c ≠ 92 ∧ (strict = true → 32 ≤ c)) →
    s.drop e = t ++ 34 :: rest →
    pyScanLoop s strict b f e a = .ok (a ++ t, ((e + t.length + 1 : Nat) : Int)) := by
  intro t
  induction t with
  | nil =>
    intro f e a rest hf _ hs
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
    simp only [List.nil_append] at hs
    obtain ⟨_, h0, _⟩ := char_at hs
    have hft : findTerm (s.drop e) = some 0 := by rw [hs]; simp [findTerm, isTerm]
    simp [pyScanLoop, hft, List.getD_eq_getElem?_getD, h0]
  | cons c t' ih =>
    intro f e a rest hf hok hs
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
    have hf' : t'.length + 1 ≤ f := by simpa using hf
    have hok' : ∀ d ∈ t', d ≠ 34 ∧ d ≠ 92 ∧ (strict = true → 32 ≤ d) := fun d hd => hok d (by simp [hd])
    obtain ⟨h34, h92, hctl⟩ := hok c (by simp)
    have hs' : s.drop e = c :: (t' ++ 34 :: rest) := by rw [hs]; rfl
    obtain ⟨_, h0, _⟩ := char_at hs'
    have hd : s.drop (e + 1) = t' ++ 34 :: rest := by
      rw [← List.drop_drop, hs']; rfl
    by_cases h32 : c < 32
    · have hns : strict = false := by
        cases strict with
        | false => rfl
        | true => have := hctl rfl; omega
      subst hns
      have hft : findTerm (s.drop e) = some 0 := by
        rw [hs']
        simp [findTerm, isTerm, h32]
      have hstep : pyScanLoop s false b (f + 1) e a = pyScanLoop s false b f (e + 1) (a ++ [c]) := by
        simp [pyScanLoop, hft, List.getD_eq_getElem?_getD, h0, h34, h92]
      rw [hstep, ih f (e + 1) _ rest hf' hok' hd]
      exact ok_congr (by simp) (by simp only [List.length_cons]; omega)
    · have ht : isTerm c = false := by simp [isTerm, h34, h92, h32]
      rw [pyScanLoop_absorb s strict b f e c a h0 ht, ih (f + 1) (e + 1) _ rest (by omega) hok' hd]
      exact ok_congr (by simp) (by simp only [List.length_cons]; omega)

theorem cScan_raw (s : PStr) (strict : Bool) (t rest : PStr)
    (hok : ∀ c ∈ t, c ≠ 34 ∧ c ≠ 92 ∧ (strict = true → 32 ≤ c)) (hs : s.drop 1 = t ++ 34 :: rest) :
    cScanstring s 1 strict = .ok (t, t.length + 2) := by
  have hl : 1 ≤ s.length := by
    have h := congrArg List.length hs
    simp only [List.length_drop, List.length_append, List.length_cons] at h
    omega
  have hlen : t.length + 1 ≤ s.length + 1 := by
    have h := congrArg List.length hs
    simp only [List.length_drop, List.length_append, List.length_cons] at h
    omega
  have hpy : pyScanstring s ((1 : Nat) : Int) strict = .ok (t, ((t.length + 2 : Nat) : Int)) := by
    unfold pyScanstring
    rw [clampPos_nat hl, loopRaw s strict _ t _ 1 [] rest hlen hok hs]
    exact ok_congr (by simp) (by omega)
  rcases scanstring_rel s strict 1 hl with ⟨v, k, _, h3, h4⟩ | ⟨pe, ce, h3, _, _⟩
  · rw [hpy] at h3
    simp only [Except.ok.injEq, Prod.mk.injEq] at h3
    obtain ⟨rfl, h5⟩ := h3
    have : k = t.length + 2 := by omega
    rw [h4, this]
  · rw [hpy] at h3; cases h3

theorem cFind_ctrl_exists : ∀ (t rest : PStr), (∀ c ∈ t, c ≠ 34 ∧ c ≠ 92) → (∃ c ∈ t, c < 32) →
    ∃ k, cFind true (t ++ rest) = .ctrl k
  | [], _, _, ⟨_, h, _⟩ => by simp at h
  | c :: t, rest, h, ⟨d, hd, hd2⟩ => by
    obtain ⟨h34, h92⟩ := h c (by simp)
    by_cases h31 : c ≤ 31
    · exact ⟨0, by simp [cFind, h34, h92, h31]⟩
    · have hne : ∃ c' ∈ t, c' < 32 := by
        simp only [List.mem_cons] at hd
        rcases hd with rfl | hd
        · omega
        · exact ⟨d, hd, hd2⟩
      obtain ⟨k, hk⟩ := cFind_ctrl_exists t rest (fun x hx => h x (by simp [hx])) hne
      refine ⟨k + 1, ?_⟩
      simp [cFind, h34, h92, h31, hk]

/-- `strict` on a string literal without quotes or backslashes (documented,
decoder.py:334-337): with `strict=False` every such literal is accepted and
gives its characters back, control characters included; with `strict=True` it
is accepted exactly when it has no character in the range 0-31. In both twins. -/
def StrictLiteral : Prop :=
  ∀ (cfg : DCfg) (t : PStr), (∀ c ∈ t, c ≠ 34 ∧ c ≠ 92) →
    (loadsPy { cfg with strict := false } (34 :: t ++ [34]) = .ok (.str t) ∧
     loadsC { cfg with strict := false } (34 :: t ++ [34]) = .ok (.str t)) ∧
    ((∀ c ∈ t, 32 ≤ c) →
      loadsPy { cfg with strict := true } (34 :: t ++ [34]) = .ok (.str t) ∧
      loadsC { cfg with strict := true } (34 :: t ++ [34]) = .ok (.str t)) ∧
    ((∃ c ∈ t, c < 32) →
      (∃ e, loadsPy { cfg with strict := true } (34 :: t ++ [34]) = .error e) ∧
      (∃ e, loadsC { cfg with strict := true } (34 :: t ++ [34]) = .error e))

theorem docFuel_succ (d : PStr) : ∃ n, docFuel d = n + 1 := ⟨4 * d.length + 7, rfl⟩

theorem strictLiteral_proven : StrictLiteral := by
  intro cfg t ht
  generalize hd : 34 :: t ++ [34] = d
  have hs0 : d.drop 0 = 34 :: (t ++ [34]) := by rw [← hd]; rfl
  have hs1 : d.drop 1 = t ++ 34 :: [] := by rw [← hd]; rfl
  have hlen : d.length = t.length + 2 := by rw [← hd]; simp
  have hw0 : wsEnd d 0 = 0 := by simp [wsEnd, hs0, wsLen, isWs]
  have run : ∀ b : Bool, (∀ c ∈ t, c ≠ 34 ∧ c ≠ 92 ∧ (b = true → 32 ≤ c)) →
      loadsC { cfg with strict := b } d = .ok (.str t) ∧
      loadsPy { cfg with strict := b } d = .ok (.str t) := by
    intro b hb
    obtain ⟨n, hn⟩ := docFuel_succ d
    have hscan := scanOnce_str { cfg with strict := b } n (p := 0) hs0 (cScan_raw d b t [] hb hs1)
    apply loads_of_scan _ d _ _ hw0
    rw [hn, hscan, hlen]
  refine ⟨?_, ?_, ?_⟩
  · have h := run false (fun c hc => ⟨(ht c hc).1, (ht c hc).2, by simp⟩)
    exact ⟨h.2, h.1⟩
  · intro h32
    have h := run true (fun c hc => ⟨(ht c hc).1, (ht c hc).2, fun _ => h32 c hc⟩)
    exact ⟨h.2, h.1⟩
  · intro hctl
    obtain ⟨k, hk⟩ := cFind_ctrl_exists t [34] ht hctl
    obtain ⟨n, hn⟩ := docFuel_succ d
    have hl1 : 1 ≤ d.length := by omega
    have hc : cScanstring d 1 true = .error (.jde "Invalid control character at" ((1 + k : Nat) : Int)) := by
      unfold cScanstring
      have hnl : ¬ d.length < 1 := by omega
      simp only [hnl, ↓reduceIte, Nat.add_one_sub_one, cScanLoop, hs1]
      rw [hk]
    have hs : cScanOnce { cfg with strict := true } d (docFuel d) 0 =
        .error (.jde "Invalid control character at" ((1 + k : Nat) : Int)) := by
      obtain ⟨_, _, h3⟩ := char_at hs0
      have hl : ¬ 0 ≥ d.length := by omega
      rw [hn]
      simp only [cScanOnce, hl, ↓reduceIte, h3, hc]
    have := loads_of_scan_err { cfg with strict := true } d _ hs hw0
    exact ⟨this.2, this.1⟩

/-! ### `ensure_ascii` -/

/-- Only ASCII code points. -/
def isAscii (t : PStr) : Bool := t.all (· < 128)

theorem isAscii_append {a b : PStr} (ha : isAscii a = true) (hb : isAscii b = true) : isAscii (a ++ b) = true := by
  simp only [isAscii, List.all_append, Bool.and_eq_true] at *
  exact ⟨ha, hb⟩

theorem isAscii_rep {t : PStr} (h : isAscii t = true) : ∀ k, isAscii (rep t k) = true
  | 0 => rfl
  | k + 1 => isAscii_append h (isAscii_rep h k)

theorem isAscii_nl {t : PStr} (h : isAscii t = true) (k : Nat) : isAscii (cNewlineIndent t k) = true :=
  isAscii_append (by decide) (isAscii_rep h k)

theorem hexCp_lt {n : Nat} (h : n < 16) : hexCp n < 128 := by
  unfold hexCp; split <;> omega

theorem uEsc_ascii (n : Nat) : isAscii (uEsc n) = true := by
  have h1 := hexCp_lt (n := n / 4096 % 16) (Nat.mod_lt _ (by decide))
  have h2 := hexCp_lt (n := n / 256 % 16) (Nat.mod_lt _ (by decide))
  have h3 := hexCp_lt (n := n / 16 % 16) (Nat.mod_lt _ (by decide))
  have h4 := hexCp_lt (n := n % 16) (Nat.mod_lt _ (by decide))
  simp [isAscii, uEsc, h1, h2, h3, h4]

theorem backslash_arg {x y : Nat} (hb : backslash x = some y) : x ≤ 116 := by
  unfold backslash at hb
  repeat' (first | (split at hb) | omega | cases hb)

theorem escA_ascii (c : Nat) (hc : c ≤ 0x10FFFF) : isAscii (escA c) = true := by
  cases escA_form c hc with
  | plain h _ hp => rw [h]; simp [isAscii]; omega
  | short x y h _ hb _ =>
    have := backslash_arg hb
    rw [h]; simp [isAscii]; omega
  | u h _ => rw [h]; exact uEsc_ascii c
  | pair n m h => rw [h]; exact isAscii_append (uEsc_ascii n) (uEsc_ascii m)

theorem cStrEnc_ascii {cfg : ECfg} (ha : cfg.ensureAscii = true) {t : PStr} (hok : strOk t = true) :
    isAscii (cStrEnc cfg t) = true := by
  rw [← strEnc_twins cfg t hok]
  simp only [pyStrEnc, ha, ↓reduceIte, pyEncA, List.cons_append]
  simp only [isAscii, List.all_cons, List.all_append, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨by decide, ?_, by decide⟩
  apply List.all_eq_true.mpr
  intro x hx
  obtain ⟨c, hc, hx2⟩ := List.mem_flatMap.mp hx
  have := List.all_eq_true.mp (escA_ascii c (cps_of_strOk hok c hc)) x hx2
  exact this

theorem intRepr_ascii {n : Int} {t : PStr} (h : intRepr n = .ok t) : isAscii t = true := by
  obtain ⟨ds, hd, rfl, _⟩ := intRepr_view h
  have hds : isAscii ds = true := by
    apply List.all_eq_true.mpr
    intro c hc
    have := hd.dig c hc
    simp only [isDigit, Bool.and_eq_true, decide_eq_true_eq] at this
    simp; omega
  split
  · exact isAscii_append (a := [45]) (by decide) hds
  · exact hds

theorem encList_ascii (cfg : ECfg) (f lvl : Nat) (seen : List Nat) (sep : PStr) (hsep : isAscii sep = true)
    (ih : ∀ lvl' seen' v t, v.ok = true → cEnc cfg f lvl' seen' v = .ok t → isAscii t = true) :
    ∀ (xs : List EVal) (i : Nat) (b : PStr), EVal.okList xs = true →
      cEncList cfg f lvl seen sep i xs = .ok b → isAscii b = true := by
  intro xs
  induction xs with
  | nil =>
    intro i b _ h
    simp only [cEncList, Except.ok.injEq] at h
    subst h; rfl
  | cons x xs ihx =>
    intro i b hok h
    simp only [EVal.okList, Bool.and_eq_true] at hok
    obtain ⟨t, b1, h1, h2, h3⟩ := cEncList_cons h
    subst h3
    refine isAscii_append (isAscii_append ?_ (ih lvl seen x t hok.1 h1)) (ihx (i + 1) b1 hok.2 h2)
    split
    · exact hsep
    · rfl

theorem encItems_ascii (cfg : ECfg) (hc : cfg.customEnc = none) (ha : cfg.ensureAscii = true)
    (hk : isAscii cfg.keySep = true)
    (f lvl : Nat) (seen : List Nat) (sep : PStr) (hsep : isAscii sep = true) (hpre : isAscii (firstPre cfg lvl) = true)
    (ih : ∀ lvl' seen' v t, v.ok = true → cEnc cfg f lvl' seen' v = .ok t → isAscii t = true) :
    ∀ (items : List (EKey × EVal)) (first : Bool) (b : PStr) (fst : Bool), EVal.okItems items = true →
      cEncItems cfg f lvl seen sep first items = .ok (b, fst) → isAscii b = true := by
  intro items
  induction items with
  | nil =>
    intro first b fst _ h
    simp only [cEncItems, Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.1]; rfl
  | cons p items ihx =>
    obtain ⟨k, x⟩ := p
    intro first b fst hok h
    simp only [EVal.okItems, Bool.and_eq_true] at hok
    simp only [cEncItems, cEncStr_std hc] at h
    cases hkk : cKeyStr cfg k with
    | error e => rw [hkk] at h; cases h
    | ok o =>
      rw [hkk] at h
      cases o with
      | none => exact ihx first b fst hok.2 h
      | some ks =>
        simp only at h
        cases h1 : cEnc cfg f lvl seen x with
        | error e => rw [h1] at h; cases h
        | ok t =>
          rw [h1] at h
          simp only at h
          cases h2 : cEncItems cfg f lvl seen sep false items with
          | error e => rw [h2] at h; cases h
          | ok r =>
            obtain ⟨b', fst'⟩ := r
            rw [h2] at h
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have hk' := keyStr_ok hok.1.1 hkk
            refine isAscii_append (isAscii_append (isAscii_append (isAscii_append ?_ (cStrEnc_ascii ha hk'))
              hk) (ih lvl seen x t hok.1.2 h1)) (ihx false b' fst' hok.2 h2)
            split
            · unfold firstPre at hpre
              cases hi : cfg.indent <;> simp only [hi] at hpre ⊢ <;> exact hpre
            · exact hsep

theorem enc_ascii (cfg : ECfg) (hO : cfg.Ok) (ha : cfg.ensureAscii = true) (hs : isAscii cfg.itemSep = true)
    (hk : isAscii cfg.keySep = true) (hi : ∀ i, cfg.indent = some i → isAscii i = true) :
    ∀ (f lvl : Nat) (seen : List Nat) (v : EVal) (t : PStr), v.ok = true →
      cEnc cfg f lvl seen v = .ok t → isAscii t = true := by
  intro f
  induction f with
  | zero => intro lvl seen v t _ h; simp [cEnc] at h
  | succ f ih =>
    intro lvl seen v t hok he
    have hsepi : ∀ ind lvl', cfg.indent = some ind → isAscii (cSepIndent cfg ind lvl') = true :=
      fun ind lvl' h => isAscii_append hs (isAscii_nl (hi ind h) lvl')
    have hfp : ∀ lvl', isAscii (firstPre cfg lvl') = true := by
      intro lvl'
      unfold firstPre
      split
      · rename_i ind h; exact isAscii_nl (hi ind h) _
      · rfl
    cases v with
    | none =>
      simp only [cEnc, Except.ok.injEq] at he
      subst he; decide
    | bool b =>
      cases b
      · simp only [cEnc, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at he
        subst he; decide
      · simp only [cEnc, ↓reduceIte, Except.ok.injEq] at he
        subst he; decide
    | int n =>
      simp only [cEnc] at he
      exact intRepr_ascii he
    | str x =>
      simp only [cEnc, cEncStr_std hO.cst, Except.ok.injEq] at he
      subst he
      exact cStrEnc_ascii ha hok
    | flt b r =>
      simp only [cEnc] at he
      have := cEncodeFloat_ok hok he
      simpa [isAscii, fltOk] using this
    | back k => simp only [cEnc] at he; cases he
    | other n tn =>
      simp only [cEnc] at he
      split at he
      · cases he
      · cases hd : cfg.dflt n tn with
        | error e => rw [hd] at he; cases he
        | ok v' =>
          rw [hd] at he
          exact ih lvl (n :: seen) v' t (hO.dfl n tn v' hd) he
    | list xs =>
      simp only [cEnc] at he
      split at he
      · simp only [Except.ok.injEq] at he
        subst he; decide
      · cases hind : cfg.indent with
        | none =>
          simp only [hind] at he
          cases hb : cEncList cfg f lvl seen cfg.itemSep 0 xs with
          | error e => rw [hb] at he; cases he
          | ok body =>
            rw [hb] at he
            simp only [Except.ok.injEq] at he
            subst he
            have := encList_ascii cfg f lvl seen cfg.itemSep hs ih xs 0 body hok hb
            exact isAscii_append (isAscii_append (isAscii_append (isAscii_append (a := [91]) (by decide) rfl)
              this) rfl) (by decide)
        | some ind =>
          simp only [hind] at he
          cases hb : cEncList cfg f (lvl + 1) seen (cSepIndent cfg ind (lvl + 1)) 0 xs with
          | error e => rw [hb] at he; cases he
          | ok body =>
            rw [hb] at he
            simp only [Except.ok.injEq] at he
            subst he
            have := encList_ascii cfg f (lvl + 1) seen _ (hsepi ind _ hind) ih xs 0 body hok hb
            exact isAscii_append (isAscii_append (isAscii_append (isAscii_append (a := [91]) (by decide)
              (isAscii_nl (hi ind hind) _)) this) (isAscii_nl (hi ind hind) _)) (by decide)
    | dict kvs =>
      have hkvs : EVal.okItems kvs = true := hok
      simp only [cEnc] at he
      split at he
      · simp only [Except.ok.injEq] at he
        subst he; decide
      · cases hsort : (if cfg.sortKeys then sortItems kvs else Except.ok kvs) with
        | error e =>
          cases hind : cfg.indent <;> simp only [hind, hsort] at he <;> cases he
        | ok items =>
          have hok2 : EVal.okItems items = true := by
            rw [← hkvs]
            by_cases hsk : cfg.sortKeys = true
            · simp only [hsk, ↓reduceIte] at hsort; exact sortItems_ok hsort
            · simp only [hsk, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at hsort; rw [hsort]
          cases hind : cfg.indent with
          | none =>
            simp only [hind, hsort] at he
            cases hb : cEncItems cfg f lvl seen cfg.itemSep true items with
            | error e => rw [hb] at he; cases he
            | ok r =>
              obtain ⟨body, first⟩ := r
              rw [hb] at he
              simp only [Except.ok.injEq] at he
              subst he
              have := encItems_ascii cfg hO.cst ha hk f lvl seen cfg.itemSep hs (hfp lvl) ih items true body first hok2 hb
              exact isAscii_append (isAscii_append (isAscii_append (a := [123]) (by decide) this) rfl) (by decide)
          | some ind =>
            simp only [hind, hsort] at he
            cases hb : cEncItems cfg f (lvl + 1) seen (cSepIndent cfg ind (lvl + 1)) true items with
            | error e => rw [hb] at he; cases he
            | ok r =>
              obtain ⟨body, first⟩ := r
              rw [hb] at he
              simp only [Except.ok.injEq] at he
              subst he
              have := encItems_ascii cfg hO.cst ha hk f (lvl + 1) seen _ (hsepi ind _ hind) (hfp _) ih items true body first hok2 hb
              refine isAscii_append (isAscii_append (isAscii_append (a := [123]) (by decide) this) ?_) (by decide)
              split
              · exact isAscii_nl (hi ind hind) _
              · rfl

/-- `ensure_ascii` (`JSONEncoder.__init__`, encoder.py:114-115: "the output is
guaranteed to be str objects with all incoming non-ASCII and non-printable
characters escaped"): with `ensure_ascii=True`, every code point of the output
of either encoder is ASCII, unless `indent` or a separator itself is not, for
every value and every `default` (type invariants `ECfg.Ok`, `EVal.ok`). -/
def EnsureAsciiOutput : Prop :=
  ∀ (cfg : ECfg) (v : EVal) (d : PStr), cfg.Ok → cfg.ensureAscii = true → isAscii cfg.itemSep = true →
    isAscii cfg.keySep = true → (∀ i, cfg.indent = some i → isAscii i = true) → v.ok = true →
    (dumpsPy cfg v = .ok d ∨ dumpsC cfg v = .ok d) → ∀ c ∈ d, c < 128

theorem ensureAsciiOutput_proven : EnsureAsciiOutput := by
  intro cfg v d hO ha hs hk hi hok he c hc
  have he' : dumpsC cfg v = .ok d := by
    rcases he with h | h
    · rw [← dumpsTwins_proven cfg v hO hok]; exact h
    · exact h
  rw [dumpsC_eq cfg hO.cst] at he'
  have := List.all_eq_true.mp (enc_ascii cfg hO ha hs hk hi _ 0 [] v d hok he') c hc
  simpa using this

/-! ### Int literals -/

theorem scanOnce_num (cfg : DCfg) (n : Nat) {s : PStr} {p c : Nat} {R : PStr} (hs : s.drop p = c :: R)
    (h : (c = 45 ∧ ∃ d R', R = d :: R' ∧ isDigit d = true) ∨ isDigit c = true) :
    cScanOnce cfg s (n + 1) p = cMatchNumber cfg s p := by
  obtain ⟨hlt, _, hg⟩ := char_at hs
  have hnot : c ≠ 34 ∧ c ≠ 123 ∧ c ≠ 91 ∧ c ≠ 110 ∧ c ≠ 116 ∧ c ≠ 102 ∧ c ≠ 78 ∧ c ≠ 73 := by
    rcases h with ⟨rfl, _⟩ | h
    · decide
    · simp [isDigit] at h
      omega
  have hm : ¬ (c = 45 ∧ litAt s p "-Infinity" = true) := by
    rintro ⟨rfl, hl⟩
    rcases h with ⟨-, d, R', rfl, hdig⟩ | h
    · have h9 := (lit_twin' s p "-Infinity" 9 (by decide) (by decide)).mpr hl
      rw [pySlice_nat, hs] at h9
      simp [cs] at h9
      simp [h9.1, isDigit] at hdig
    · revert h; decide
  have hl : ¬ p ≥ s.length := by omega
  simp only [cScanOnce, hl, ↓reduceIte, hg, hnot.1, hnot.2.1, hnot.2.2.1, hnot.2.2.2.1,
    hnot.2.2.2.2.1, hnot.2.2.2.2.2.1, hnot.2.2.2.2.2.2.1, hnot.2.2.2.2.2.2.2, false_and, hm]

/-- `PyLong_FromString`'s error for too many digits. -/
def tooManyDigits (k : Nat) : PyExc :=
  .valueError s!"Exceeds the limit (4300 digits) for integer string conversion: value has {k} digits; use sys.set_int_max_str_digits() to increase the limit"

/-- A JSON int literal (optional `-`, no leading zeros) with the default
`parse_int`: `loads` returns its value when it has at most 4300 digits, and
raises the `ValueError` of `int()` otherwise, in both twins. -/
def IntLiteral : Prop :=
  ∀ (cfg : DCfg) (neg : Bool) (ds : PStr), cfg.parseIntFn = none → (∀ c ∈ ds, isDigit c = true) →
    (ds = [48] ∨ ∃ d r, ds = d :: r ∧ 49 ≤ d ∧ d ≤ 57) →
    (ds.length ≤ maxStrDigits →
      loadsPy cfg (if neg then 45 :: ds else ds) = .ok (.int (if neg then -(decVal ds : Int) else decVal ds)) ∧
      loadsC cfg (if neg then 45 :: ds else ds) = .ok (.int (if neg then -(decVal ds : Int) else decVal ds))) ∧
    (maxStrDigits < ds.length →
      loadsPy cfg (if neg then 45 :: ds else ds) = .error (.exc (tooManyDigits ds.length)) ∧
      loadsC cfg (if neg then 45 :: ds else ds) = .error (.exc (tooManyDigits ds.length)))

theorem intLiteral_proven : IntLiteral := by
  intro cfg neg ds hint hdig hhead
  have hd : DigSpec (decVal ds) ds := by
    refine ⟨hdig, rfl, ?_⟩
    rcases hhead with rfl | h
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr h
  obtain ⟨d0, r0, hds, hd0⟩ : ∃ d r, ds = d :: r ∧ isDigit d = true := by
    rcases hhead with rfl | ⟨d, r, rfl, _, _⟩
    · exact ⟨48, [], rfl, rfl⟩
    · exact ⟨d, r, rfl, hdig d (by simp)⟩
  have h450 : d0 ≠ 45 := by
    intro e; subst e; revert hd0; decide
  generalize hT : (if neg then 45 :: ds else ds) = T
  have hre : numberRe T = some (T, [], []) := by
    have hstop : Delim [] := Or.inl rfl
    cases neg with
    | true =>
      simp only [↓reduceIte] at hT
      subst hT
      simpa using numberRe_signed (rest := []) hd hstop
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hT
      subst hT
      have h45 : ∀ r, ds ≠ 45 :: r := by
        intro r e
        rw [hds] at e
        simp only [List.cons.injEq] at e
        exact h450 e.1
      simpa using numberRe_digits (rest := []) hd hstop h45
  obtain ⟨c, R, hcr, hstart⟩ : ∃ c R, T = c :: R ∧
      ((c = 45 ∧ ∃ d R', R = d :: R' ∧ isDigit d = true) ∨ isDigit c = true) := by
    cases neg with
    | true =>
      simp only [↓reduceIte] at hT
      exact ⟨45, ds, hT.symm, Or.inl ⟨rfl, d0, r0, hds, hd0⟩⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hT
      exact ⟨d0, r0, by rw [← hT, hds], Or.inr hd0⟩
  have hw0 : wsEnd T 0 = 0 := by
    have : isWs c = false := by
      rcases hstart with ⟨rfl, _⟩ | h
      · rfl
      · simp only [isDigit, Bool.and_eq_true, decide_eq_true_eq] at h
        simp only [isWs, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
        omega
    rw [hcr]
    simp [wsEnd, wsLen, this]
  have hs0 : T.drop 0 = c :: R := by simp [hcr]
  have hlt : 0 < T.length := by rw [hcr]; simp
  have hstep : cScanOnce cfg T (docFuel T) 0 = cMatchNumber cfg T 0 := by
    obtain ⟨n, hn⟩ := docFuel_succ T
    rw [hn]
    exact scanOnce_num cfg n hs0 hstart
  have hnum : cMatchNumber cfg T 0 = (parseInt cfg T).map (·, 0 + (T.length + 0 + 0)) := by
    rcases matchNumber_twin cfg T 0 hlt with ⟨h1, _⟩ | ⟨i, fr, ex, h1, h2⟩
    · simp only [List.drop_zero] at h1
      rw [hre] at h1; cases h1
    · simp only [List.drop_zero] at h1
      rw [hre] at h1
      simp only [Option.some.injEq, Prod.mk.injEq] at h1
      obtain ⟨rfl, rfl, rfl⟩ := h1
      rw [h2]
      simp
  have hparse : pyIntOfText T = (if ds.length > maxStrDigits then .error (tooManyDigits ds.length)
      else .ok (if neg then -(decVal ds : Int) else decVal ds)) := by
    cases neg with
    | true =>
      simp only [↓reduceIte] at hT
      subst hT
      rfl
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hT ⊢
      subst hT
      rw [hds]
      simp [pyIntOfText, h450, tooManyDigits]
  simp only [parseInt, hint, Bool.false_eq_true, ↓reduceIte, hparse] at hnum
  constructor
  · intro hl
    have hn : ¬ ds.length > maxStrDigits := by omega
    simp only [hn, ↓reduceIte, Except.map] at hnum
    obtain ⟨h1, h2⟩ := loads_of_scan cfg T (.int (if neg then -(decVal ds : Int) else decVal ds))
      (by rw [hstep, hnum]; simp) hw0
    exact ⟨h2, h1⟩
  · intro hl
    have hn : ds.length > maxStrDigits := hl
    simp only [hn, ↓reduceIte, Except.map] at hnum
    obtain ⟨h1, h2⟩ := loads_of_scan_exc cfg T _ (by rw [hstep, hnum]) hw0
    exact ⟨h2, h1⟩

end PyLean.JsonMod
