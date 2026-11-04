import PyLean.Datetime.DtProps

/-!
`datetime` comparison across time zones, `astimezone` to a `timezone`, and `tzinfo.fromutc`
for a constant offset.
-/

namespace PyLean.Datetime

open PyLean

theorem dt_memcmp (a b : DT) (ha : a.Valid) (hb : b.Valid) :
    memcmpBytes (dtData a) (dtData b) = cmpTuple a.base b.base := by
  have pa := validDate_pos _ _ _ ha.1
  have pb := validDate_pos _ _ _ hb.1
  obtain ⟨_, a1, a2, a3, a4, a5, a6, a7, a8, _⟩ := ha
  obtain ⟨_, b1, b2, b3, b4, b5, b6, b7, b8, _⟩ := hb
  show memcmpBytes ((a.y / 256).toNat :: (a.y % 256).toNat :: a.m.toNat :: a.d.toNat :: a.h.toNat :: a.mi.toNat ::
      a.s.toNat :: [(a.us / 65536).toNat, (a.us / 256 % 256).toNat, (a.us % 256).toNat])
    ((b.y / 256).toNat :: (b.y % 256).toNat :: b.m.toNat :: b.d.toNat :: b.h.toNat :: b.mi.toNat ::
      b.s.toNat :: [(b.us / 65536).toNat, (b.us / 256 % 256).toNat, (b.us % 256).toNat]) = _
  unfold DT.base
  rw [mc_year _ _ (by omega) (by omega), mc_field _ _ (by omega) (by omega), mc_field _ _ (by omega) (by omega),
    mc_field _ _ a1 b1, mc_field _ _ a3 b3, mc_field _ _ a5 b5, mc_us _ _ a7 b7 (by omega) (by omega),
    cmpTuple_cons a.y b.y [a.m, a.d, a.h, a.mi, a.s, a.us] [b.m, b.d, b.h, b.mi, b.s, b.us] rfl,
    cmpTuple_cons a.m b.m [a.d, a.h, a.mi, a.s, a.us] [b.d, b.h, b.mi, b.s, b.us] rfl,
    cmpTuple_cons a.d b.d [a.h, a.mi, a.s, a.us] [b.h, b.mi, b.s, b.us] rfl,
    cmpTuple_cons a.h b.h [a.mi, a.s, a.us] [b.mi, b.s, b.us] rfl,
    cmpTuple_cons a.mi b.mi [a.s, a.us] [b.s, b.us] rfl,
    cmpTuple_cons a.s b.s [a.us] [b.us] rfl, cmpTuple_cons a.us b.us [] [] rfl, cmpTuple_nil]

theorem offEq_comm (a b : Option Delta) : offEq a b = offEq b a := by
  cases a <;> cases b <;> simp [offEq]
  rename_i x y
  simp [BEq.comm]

/-- The Python sign of a difference and the C one agree. -/
theorem diff_signs (s : Delta) (hv0 : 0 ≤ s.seconds) (hv1 : 0 ≤ s.us) :
    let p : Int := if s.days < 0 then -1 else if s.bool then 1 else 0
    let d : Int := if s.days = 0 then (if s.seconds = 0 ∧ s.us = 0 then 0 else 1) else s.days
    (p < 0 ↔ d < 0) ∧ (p = 0 ↔ d = 0) := by
  intro p d
  by_cases h0 : s.days < 0
  · have hp : p = -1 := by simp [p, h0]
    have hne : ¬ s.days = 0 := by omega
    have hd : d = s.days := by simp [d, hne]
    rw [hp, hd]; omega
  · by_cases h1 : s.days = 0
    · by_cases h2 : s.seconds = 0 ∧ s.us = 0
      · have hp : p = 0 := by simp [p, h1, h2, Delta.bool]
        have hd : d = 0 := by simp [d, h1, h2]
        rw [hp, hd]; omega
      · have hb : s.bool = true := by
          simp only [Delta.bool, bne_iff_ne, Bool.or_eq_true]
          omega
        have hp : p = 1 := by simp [p, h0, hb]
        have hd : d = 1 := by simp [d, h1, h2]
        rw [hp, hd]; omega
    · have hb : s.bool = true := by
        simp only [Delta.bool, bne_iff_ne, Bool.or_eq_true]
        omega
      have hp : p = 1 := by simp [p, h0, hb]
      have hd : d = s.days := by simp [d, h1]
      rw [hp, hd]; omega

theorem diffToBool_congr (x y : Int) (op : CmpOp) (h1 : x < 0 ↔ y < 0) (h2 : x = 0 ↔ y = 0) :
    diffToBool x op = diffToBool y op := by
  cases op <;> simp only [diffToBool] <;> congr 1 <;> simp only [eq_iff_iff] <;> omega

/-- `datetime` comparison: the two implementations agree for every `tzinfo` whose
`utcoffset` does not raise on the operands with `fold` flipped. That hypothesis is
needed because `datetime._cmp` asks for the flipped offsets up front
(_pydatetime.py:2311-2318, PEP 495), while C asks only once the operands are otherwise
equal (pep495_eq_exception, :6560-6586): a method raising there is an exception in one twin only. -/
def DatetimeCompareTwins : Prop :=
  ∀ (env : TzEnv) (op : CmpOp) (a b : DT), env.Valid → a.Valid → b.Valid →
    (∃ o, a.flipFold.utcoffsetPy env = .ok o) → (∃ o, b.flipFold.utcoffsetPy env = .ok o) →
    SameOutcome (dtRichPy env op a b) (dtRichC env op a b)

theorem datetimeCompareBase (env : TzEnv) (op : CmpOp) (a b : DT) (ha : a.Valid) (hb : b.Valid)
    (hs : sameTz a.tz b.tz = true) : SameOutcome (dtRichPy env op a b) (dtRichC env op a b) := by
  have hm := dt_memcmp a b ha hb
  have hc : dtCmpPy env a b true = .ok (cmpTuple a.base b.base) ∧
      dtCmpPy env a b false = .ok (cmpTuple a.base b.base) := by
    simp [dtCmpPy, hs, bind, Except.bind, pure, Except.pure]
  have hr : dtRichC env op a b = .ok (diffToBool (cmpTuple a.base b.base) op) := by
    simp [dtRichC, hs, hm, bind, Except.bind, pure, Except.pure]
  rw [hr]
  generalize cmpTuple a.base b.base = c at hc
  by_cases h0 : c = 0 <;>
    cases op <;> simp [dtRichPy, hc.1, hc.2, h0, bind, Except.bind, pure, Except.pure, SameOutcome, diffToBool]

theorem diffToBool_eqne (x y : Int) (op : CmpOp) (hop : op = .eq ∨ op = .ne) (h : x = 0 ↔ y = 0) :
    diffToBool x op = diffToBool y op := by
  rcases hop with rfl | rfl <;> simp only [diffToBool] <;> congr 1 <;> simp only [eq_iff_iff] <;> omega

theorem offEq_some_none (x : Delta) : offEq (some x) none = false := rfl
theorem offEq_none_some (x : Delta) : offEq none (some x) = false := rfl

/-- The equality operators once the four offsets are known. -/
theorem datetimeCompare_eqne (env : TzEnv) (a b : DT) (henv : env.Valid) (ha : a.Valid) (hb : b.Valid)
    (hs : sameTz a.tz b.tz = false) (o1 o2 f1 f2 : Option Delta)
    (h1 : a.utcoffsetC env = .ok o1) (h2 : b.utcoffsetC env = .ok o2)
    (h3 : a.flipFold.utcoffsetC env = .ok f1) (h4 : b.flipFold.utcoffsetC env = .ok f2)
    (op : CmpOp) (hop : op = .eq ∨ op = .ne) :
    SameOutcome (dtRichPy env op a b) (dtRichC env op a b) := by
  have hax : OptTzOk a.tz := ha.2.2.2.2.2.2.2.2.2.2
  have hbx : OptTzOk b.tz := hb.2.2.2.2.2.2.2.2.2.2
  have p1 : a.utcoffsetPy env = .ok o1 := by rw [dt_utcoffset_twin env henv a hax]; exact h1
  have p2 : b.utcoffsetPy env = .ok o2 := by rw [dt_utcoffset_twin env henv b hbx]; exact h2
  have p3 : a.flipFold.utcoffsetPy env = .ok f1 := by
    rw [dt_utcoffset_twin env henv a.flipFold hax]; exact h3
  have p4 : b.flipFold.utcoffsetPy env = .ok f2 := by
    rw [dt_utcoffset_twin env henv b.flipFold hbx]; exact h4
  have hpep : pep495EqExceptionC env a b o1 o2 = .ok (!offEq o1 f1 || !offEq o2 f2) := by
    unfold pep495EqExceptionC getFlipFoldOffsetC
    rw [h3]
    dsimp only [bind, Except.bind]
    rw [offEq_comm f1 o1]
    cases e1 : offEq o1 f1
    · simp [pure, Except.pure]
    · simp [h4, offEq_comm f2 o2, pure, Except.pure]
  have hPy : ∀ c : Int, dtCmpPy env a b true = .ok c → dtRichPy env op a b = .ok (diffToBool c op) := by
    intro c hc
    rcases hop with rfl | rfl <;> by_cases h0 : c = 0 <;>
      simp [dtRichPy, hc, h0, bind, Except.bind, pure, Except.pure, diffToBool]
  have hm := dt_memcmp a b ha hb
  cases he : offEq o1 o2 with
  | true =>
    generalize hcd : cmpTuple a.base b.base = c at hm
    have eC : dtRichC env op a b = .ok (diffToBool
        (if c = 0 ∧ (!offEq o1 f1 || !offEq o2 f2) = true then 1 else c) op) := by
      rcases hop with rfl | rfl <;> by_cases hc : c = 0 <;>
        simp [dtRichC, hs, h1, h2, he, hm, hpep, hc, bind, Except.bind, pure, Except.pure] <;>
        (try (cases hb1 : offEq o1 f1 <;> cases hb2 : offEq o2 f2 <;> simp [hb1, hb2, diffToBool, hc]))
    have eP : dtCmpPy env a b true = .ok
        (if (!offEq o1 f1 || !offEq o2 f2) = true then 2 else c) := by
      cases hb1 : offEq o1 f1 <;> cases hb2 : offEq o2 f2 <;>
        simp [dtCmpPy, hs, p1, p2, p3, p4, he, hb1, hb2, hcd, bind, Except.bind, pure, Except.pure]
    rw [hPy _ eP, eC]
    show diffToBool _ op = diffToBool _ op
    apply diffToBool_eqne _ _ _ hop
    cases hb1 : offEq o1 f1 <;> cases hb2 : offEq o2 f2 <;> by_cases hc : c = 0 <;> simp [hc]
  | false =>
    cases o1 with
    | none =>
      have eC : dtRichC env op a b = .ok (diffToBool 1 op) := by
        have hn : ¬ ((none : Option Delta).isSome = true ∧ o2.isSome = true) := by simp
        rcases hop with rfl | rfl <;>
          simp [dtRichC, hs, h1, h2, he, bind, Except.bind, pure, Except.pure, diffToBool]
      have eP : dtCmpPy env a b true = .ok 2 := by
        cases hb1 : offEq none f1 <;> cases hb2 : offEq o2 f2 <;>
          simp [dtCmpPy, hs, p1, p2, p3, p4, he, hb1, hb2, bind, Except.bind, pure, Except.pure]
      rw [hPy _ eP, eC]
      show diffToBool _ op = diffToBool _ op
      exact diffToBool_eqne _ _ _ hop (by omega)
    | some x =>
      cases o2 with
      | none =>
        have eC : dtRichC env op a b = .ok (diffToBool 1 op) := by
          rcases hop with rfl | rfl <;>
            simp [dtRichC, hs, h1, h2, he, bind, Except.bind, pure, Except.pure, diffToBool]
        have eP : dtCmpPy env a b true = .ok 2 := by
          cases hb1 : offEq (some x) f1 <;> cases hb2 : offEq none f2 <;>
            simp [dtCmpPy, hs, p1, p2, p3, p4, he, hb1, hb2, bind, Except.bind, pure, Except.pure]
        rw [hPy _ eP, eC]
        show diffToBool _ op = diffToBool _ op
        exact diffToBool_eqne _ _ _ hop (by omega)
      | some y =>
        obtain ⟨e1, e2⟩ := dtSub_aware env a b henv ha hb x y hs p1 p2
        generalize a.totalUs - b.totalUs + (y.toUs - x.toUs) = T at e1 e2
        have nn0 : 0 ≤ (canon T).seconds := by simp only [canon]; omega
        have nn1 : 0 ≤ (canon T).us := by simp only [canon]; omega
        obtain ⟨s1, s2⟩ := diff_signs (canon T) nn0 nn1
        generalize hP : (if (canon T).days < 0 then (-1 : Int) else if (canon T).bool then 1 else 0) = P at s1 s2
        generalize hD : (if (canon T).days = 0 then (if (canon T).seconds = 0 ∧ (canon T).us = 0 then (0 : Int) else 1)
          else (canon T).days) = D at s1 s2
        generalize hq : (!offEq (some x) f1 || !offEq (some y) f2) = q at hpep
        have eC0 : dtRichC env op a b = (do
            let diff ← if (op = .eq ∨ op = .ne) ∧ D = 0 then do
                if ← pep495EqExceptionC env a b (some x) (some y) then pure 1 else pure D
              else pure D
            return diffToBool diff op) := by
          subst hD
          simp only [dtRichC, hs, h1, h2, he, e2, bind, Except.bind, Bool.false_eq_true, ite_false,
            Option.isSome_some, and_self, ite_true]
        have eC : dtRichC env op a b = .ok (diffToBool (if D = 0 ∧ q = true then 1 else D) op) := by
          rw [eC0]
          rcases hop with rfl | rfl <;> cases q <;> by_cases hc : D = 0 <;>
            simp [hc, hpep, bind, Except.bind, pure, Except.pure]
        have eP : dtCmpPy env a b true = .ok (if q = true then 2 else P) := by
          rw [← hq]
          subst hP
          cases hb1 : offEq (some x) f1 <;> cases hb2 : offEq (some y) f2 <;>
            simp [dtCmpPy, hs, p1, p2, p3, p4, he, hb1, hb2, e1, bind, Except.bind, pure, Except.pure] <;>
            (try (split <;> simp_all))
        rw [hPy _ eP, eC]
        show diffToBool _ op = diffToBool _ op
        apply diffToBool_eqne _ _ _ hop
        cases q <;> by_cases hc : D = 0 <;> simp [hc] <;> omega

/-- The ordering operators: no `fold` flip is involved. -/
theorem datetimeCompare_order (env : TzEnv) (a b : DT) (henv : env.Valid) (ha : a.Valid) (hb : b.Valid)
    (hs : sameTz a.tz b.tz = false) (o1 o2 : Option Delta)
    (h1 : a.utcoffsetC env = .ok o1) (h2 : b.utcoffsetC env = .ok o2)
    (op : CmpOp) (hop : op ≠ .eq ∧ op ≠ .ne) :
    SameOutcome (dtRichPy env op a b) (dtRichC env op a b) := by
  have hax : OptTzOk a.tz := ha.2.2.2.2.2.2.2.2.2.2
  have hbx : OptTzOk b.tz := hb.2.2.2.2.2.2.2.2.2.2
  have p1 : a.utcoffsetPy env = .ok o1 := by rw [dt_utcoffset_twin env henv a hax]; exact h1
  have p2 : b.utcoffsetPy env = .ok o2 := by rw [dt_utcoffset_twin env henv b hbx]; exact h2
  have hPy : ∀ c : Py Int, dtCmpPy env a b false = c →
      dtRichPy env op a b = (do return diffToBool (← c) op) := by
    intro c hc
    subst hc
    cases op
    all_goals first
      | exact absurd rfl hop.1
      | exact absurd rfl hop.2
      | rfl
  have hne : (op = .eq ∨ op = .ne) = False := by
    simp [hop.1, hop.2]
  have hm := dt_memcmp a b ha hb
  cases he : offEq o1 o2 with
  | true =>
    have eC : dtRichC env op a b = .ok (diffToBool (cmpTuple a.base b.base) op) := by
      simp [dtRichC, hs, h1, h2, he, hm, hne, bind, Except.bind, pure, Except.pure]
    have eP : dtCmpPy env a b false = .ok (cmpTuple a.base b.base) := by
      simp [dtCmpPy, hs, p1, p2, he, bind, Except.bind, pure, Except.pure]
    rw [hPy _ eP, eC]
    rfl
  | false =>
    have aux : ¬(o1.isSome = true ∧ o2.isSome = true) →
        (o1.isNone = true ∨ o2.isNone = true) ∧
        ∃ e, dtRichC env op a b = .error e ∧ e.className = "TypeError" := by
      intro hn
      refine ⟨?_, ?_⟩
      · cases o1 <;> cases o2 <;> simp_all
      · refine ⟨.typeError "can't compare offset-naive and offset-aware datetimes", ?_, rfl⟩
        cases op
        all_goals first
          | exact absurd rfl hop.1
          | exact absurd rfl hop.2
          | simp [dtRichC, hs, h1, h2, he, hn, bind, Except.bind, pure, Except.pure, throw, throwThe,
              MonadExceptOf.throw]
    cases o1 with
    | none =>
      obtain ⟨hn, e, ee, ec⟩ := aux (by simp)
      have eP : dtCmpPy env a b false = .error (.typeError "cannot compare naive and aware datetimes") := by
        simp [dtCmpPy, hs, p1, p2, he, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
      rw [hPy _ eP, ee]
      simp only [bind, Except.bind, SameOutcome]
      rw [ec]; rfl
    | some x =>
      cases o2 with
      | none =>
        obtain ⟨hn, e, ee, ec⟩ := aux (by simp)
        have eP : dtCmpPy env a b false = .error (.typeError "cannot compare naive and aware datetimes") := by
          simp [dtCmpPy, hs, p1, p2, he, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
        rw [hPy _ eP, ee]
        simp only [bind, Except.bind, SameOutcome]
        rw [ec]; rfl
      | some y =>
        obtain ⟨e1, e2⟩ := dtSub_aware env a b henv ha hb x y hs p1 p2
        generalize a.totalUs - b.totalUs + (y.toUs - x.toUs) = T at e1 e2
        have nn0 : 0 ≤ (canon T).seconds := by simp only [canon]; omega
        have nn1 : 0 ≤ (canon T).us := by simp only [canon]; omega
        obtain ⟨s1, s2⟩ := diff_signs (canon T) nn0 nn1
        have eC : dtRichC env op a b = .ok (diffToBool (if (canon T).days = 0 then
            (if (canon T).seconds = 0 ∧ (canon T).us = 0 then (0 : Int) else 1) else (canon T).days) op) := by
          simp [dtRichC, hs, h1, h2, he, e2, hne, bind, Except.bind, pure, Except.pure]
        have eP : dtCmpPy env a b false = .ok
            (if (canon T).days < 0 then (-1 : Int) else if (canon T).bool then 1 else 0) := by
          simp only [dtCmpPy, hs, p1, p2, he, e1, bind, Except.bind, pure, Except.pure]
          simp only [Bool.false_eq_true, ite_false, Option.isNone_some, false_or]
          split <;> rfl
        rw [hPy _ eP, eC]
        exact diffToBool_congr _ _ op s1 s2

theorem datetimeCompareTwins_proven : DatetimeCompareTwins := by
  intro env op a b henv ha hb ⟨f1, hf1⟩ ⟨f2, hf2⟩
  have hax : OptTzOk a.tz := ha.2.2.2.2.2.2.2.2.2.2
  have hbx : OptTzOk b.tz := hb.2.2.2.2.2.2.2.2.2.2
  by_cases hs : sameTz a.tz b.tz = true
  · exact datetimeCompareBase env op a b ha hb hs
  have hs' : sameTz a.tz b.tz = false := by simpa using hs
  have tw1 := dt_utcoffset_twin env henv a hax
  have tw2 := dt_utcoffset_twin env henv b hbx
  have tw3 := dt_utcoffset_twin env henv a.flipFold hax
  have tw4 := dt_utcoffset_twin env henv b.flipFold hbx
  cases h1 : a.utcoffsetC env with
  | error e =>
    have ep : a.utcoffsetPy env = .error e := by rw [tw1]; exact h1
    have c : ∀ al, dtCmpPy env a b al = .error e := by
      intro al; simp [dtCmpPy, hs', ep, bind, Except.bind]
    have eC : dtRichC env op a b = .error e := by simp [dtRichC, hs', h1, bind, Except.bind]
    rw [eC]
    cases op <;> simp [dtRichPy, c, bind, Except.bind, SameOutcome]
  | ok o1 =>
    cases h2 : b.utcoffsetC env with
    | error e =>
      have ep1 : a.utcoffsetPy env = .ok o1 := by rw [tw1]; exact h1
      have ep : b.utcoffsetPy env = .error e := by rw [tw2]; exact h2
      have c : ∀ al, dtCmpPy env a b al = .error e := by
        intro al; simp [dtCmpPy, hs', ep1, ep, bind, Except.bind]
      have eC : dtRichC env op a b = .error e := by simp [dtRichC, hs', h1, h2, bind, Except.bind]
      rw [eC]
      cases op <;> simp [dtRichPy, c, bind, Except.bind, SameOutcome]
    | ok o2 =>
      by_cases hop : op = .eq ∨ op = .ne
      · have h3 : a.flipFold.utcoffsetC env = .ok f1 := by rw [← tw3]; exact hf1
        cases f1 with
        | _ =>
        have h4 : b.flipFold.utcoffsetC env = .ok f2 := by rw [← tw4]; exact hf2
        exact datetimeCompare_eqne env a b henv ha hb hs' o1 o2 _ _ h1 h2 h3 h4 op hop
      · exact datetimeCompare_order env a b henv ha hb hs' o1 o2 h1 h2 op (by
          constructor <;> (intro hh; exact hop (by simp [hh])))

end PyLean.Datetime
