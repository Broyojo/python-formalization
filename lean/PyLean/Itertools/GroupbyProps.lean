import PyLean.Itertools.GroupbyTee

/-!
`groupby`: the C object (one shared state, `currgrouper` invalidating old
groups) simulates the doc's two kinds of generator frames, for every
interleaving of `next()` on the groupby object and on any group it returned.
-/

namespace PyLean.Itertools

open PyLean

variable {α κ : Type} [Inhabited α] [Inhabited κ] [DecidableEq κ]

theorem getD_snoc {α : Type} (pre : List α) (x d : α) : (pre ++ [x]).getD pre.length d = x := by
  simp [List.getD_eq_getElem?_getD]

theorem set_snoc {α : Type} (pre : List α) (x y : α) : (pre ++ [x]).set pre.length y = pre ++ [y] := by
  simp

/-- How the C state matches the live group's generator frame. -/
def GbActive (g : CGroupby α κ) (d : DocGroupby α κ) (T : κ) : GenPc → Prop
  | .fresh => g.currvalue = some d.currValue ∧ g.currkey = some d.currKey ∧ d.currKey = T ∧
      d.exhausted = false
  | .suspended => g.currvalue = none ∧ g.currkey = none ∧ d.currKey = T ∧ d.exhausted = false
  | .done =>
    (g.currvalue = some d.currValue ∧ g.currkey = some d.currKey ∧ d.currKey ≠ T ∧ d.exhausted = false) ∨
    (g.currkey = none ∧ g.currvalue = none ∧ d.exhausted = true ∧ d.currKey = T ∧ g.it = [])

/-- The simulation relation: not started, a group is live, or finished. -/
def GbRel (g : CGroupby α κ) (d : DocGroupby α κ) : Prop :=
  g.it = d.it ∧ g.groupers = d.groups.map Prod.fst ∧
  ((d.outer = .fresh ∧ d.groups = [] ∧ g.tgtkey = none ∧ g.currkey = none ∧ g.currvalue = none ∧
      g.currgrouper = none ∧ d.exhausted = false) ∨
   (∃ T pre pc, d.groups = pre ++ [(T, pc)] ∧ (∀ x ∈ pre, x.2 = GenPc.done) ∧ d.outer = .suspended ∧
      d.targetKey = T ∧ g.tgtkey = some T ∧ g.currgrouper = some pre.length ∧ GbActive g d T pc) ∨
   (d.outer = .done ∧ (∀ x ∈ d.groups, x.2 = GenPc.done) ∧ g.currgrouper = none ∧ g.it = [] ∧
      (g.currkey = none ∨ ∃ T, g.currkey = some T ∧ g.tgtkey = some T)))

/-! ## One `next()` of the doc's `_grouper` frame -/

theorem grouper_done (key : α → κ) (d : DocGroupby α κ) (j : Nat)
    (h : (d.groups.getD j (default, GenPc.done)).2 = GenPc.done) : docGrouperNext key d j = (none, d) := by
  simp only [docGrouperNext]
  cases hg : d.groups.getD j (default, GenPc.done) with
  | mk t pc => rw [hg] at h; simp only at h; subst h; rfl

theorem grouper_fresh (key : α → κ) (d : DocGroupby α κ) (pre : List (κ × GenPc)) (T : κ)
    (h : d.groups = pre ++ [(T, GenPc.fresh)]) :
    docGrouperNext key d pre.length =
      (some d.currValue, { d with groups := pre ++ [(T, GenPc.suspended)] }) := by
  simp [docGrouperNext, h, getD_snoc]

theorem grouper_nil (key : α → κ) (d : DocGroupby α κ) (pre : List (κ × GenPc)) (T : κ)
    (h : d.groups = pre ++ [(T, GenPc.suspended)]) (hit : d.it = []) :
    docGrouperNext key d pre.length =
      (none, { d with exhausted := true, groups := pre ++ [(T, GenPc.done)] }) := by
  simp [docGrouperNext, h, getD_snoc, hit]

theorem grouper_same (key : α → κ) (d : DocGroupby α κ) (pre : List (κ × GenPc)) (T : κ) (v : α) (rest : List α)
    (h : d.groups = pre ++ [(T, GenPc.suspended)]) (hit : d.it = v :: rest) (hv : key v = T) :
    docGrouperNext key d pre.length =
      (some v, { d with it := rest, currValue := v, currKey := key v }) := by
  simp [docGrouperNext, h, getD_snoc, hit, hv]

theorem grouper_new (key : α → κ) (d : DocGroupby α κ) (pre : List (κ × GenPc)) (T : κ) (v : α) (rest : List α)
    (h : d.groups = pre ++ [(T, GenPc.suspended)]) (hit : d.it = v :: rest) (hv : key v ≠ T) :
    docGrouperNext key d pre.length =
      (none, { d with it := rest, currValue := v, currKey := key v, groups := pre ++ [(T, GenPc.done)] }) := by
  simp [docGrouperNext, h, getD_snoc, hit, hv]

/-- The input is exhausted or a boundary is reached, in lockstep: `cGroupbySkip`
drops the rest of the group, `for _ in curr_group: pass` runs the frame out. -/
theorem exhaust_rel (key : α → κ) (T : κ) (pre : List (κ × GenPc)) :
    ∀ (fuelC fuelD : Nat) (g : CGroupby α κ) (d : DocGroupby α κ), g.it = d.it → g.it.length < fuelC →
      g.it.length < fuelD → d.groups = pre ++ [(T, GenPc.suspended)] → g.tgtkey = some T →
      (g.currkey = none ∨ g.currkey = some T) → d.exhausted = false → d.currKey = T →
      (cGroupbySkip key fuelC g).2.it = (docExhaustGroup key d pre.length fuelD).it ∧
      (cGroupbySkip key fuelC g).2.groupers = g.groupers ∧
      (cGroupbySkip key fuelC g).2.tgtkey = some T ∧
      (cGroupbySkip key fuelC g).2.currgrouper = g.currgrouper ∧
      (docExhaustGroup key d pre.length fuelD).groups = pre ++ [(T, GenPc.done)] ∧
      (docExhaustGroup key d pre.length fuelD).outer = d.outer ∧
      (docExhaustGroup key d pre.length fuelD).targetKey = d.targetKey ∧
      (((cGroupbySkip key fuelC g).1 = true ∧
          (cGroupbySkip key fuelC g).2.currvalue = some (docExhaustGroup key d pre.length fuelD).currValue ∧
          (cGroupbySkip key fuelC g).2.currkey = some (docExhaustGroup key d pre.length fuelD).currKey ∧
          (docExhaustGroup key d pre.length fuelD).currKey ≠ T ∧
          (docExhaustGroup key d pre.length fuelD).exhausted = false) ∨
       ((cGroupbySkip key fuelC g).1 = false ∧ (docExhaustGroup key d pre.length fuelD).exhausted = true ∧
          (docExhaustGroup key d pre.length fuelD).currKey = T ∧ (cGroupbySkip key fuelC g).2.it = [] ∧
          ((cGroupbySkip key fuelC g).2.currkey = none ∨ (cGroupbySkip key fuelC g).2.currkey = some T)))
  | 0, _, _, _, _, h, _, _, _, _, _, _ => by simp at h
  | _ + 1, 0, _, _, _, _, h, _, _, _, _, _ => by simp at h
  | fuelC + 1, fuelD + 1, g, d, hit, hfc, hfd, hgr, htg, hck, hex, hkey => by
    have hadv : gbAdvance g.currkey g.tgtkey = true := by
      rcases hck with h | h <;> simp [h, htg, gbAdvance]
    cases hxs : g.it with
    | nil =>
      have hd : d.it = [] := by rw [← hit, hxs]
      have hcS : cGroupbySkip key (fuelC + 1) g = (false, g) := by
        simp [cGroupbySkip, hadv, cGroupbyStep, hxs]
      have hdE : docExhaustGroup key d pre.length (fuelD + 1) =
          { d with exhausted := true, groups := pre ++ [(T, GenPc.done)] } := by
        simp [docExhaustGroup, grouper_nil key d pre T hgr hd]
      rw [hcS, hdE]
      exact ⟨by simp [hxs, hd], rfl, htg, rfl, rfl, rfl, rfl, Or.inr ⟨rfl, rfl, hkey, hxs, hck⟩⟩
    | cons v rest =>
      have hd : d.it = v :: rest := by rw [← hit, hxs]
      have hrest : rest.length < fuelC := by rw [hxs] at hfc; simp at hfc; omega
      have hrestD : rest.length < fuelD := by rw [hxs] at hfd; simp at hfd; omega
      have hcS : cGroupbySkip key (fuelC + 1) g =
          cGroupbySkip key fuelC { g with it := rest, currvalue := some v, currkey := some (key v) } := by
        simp [cGroupbySkip, hadv, cGroupbyStep, hxs]
      by_cases hv : key v = T
      · have hdE : docExhaustGroup key d pre.length (fuelD + 1) =
            docExhaustGroup key { d with it := rest, currValue := v, currKey := key v } pre.length fuelD := by
          simp [docExhaustGroup, grouper_same key d pre T v rest hgr hd hv]
        rw [hcS, hdE]
        exact exhaust_rel key T pre fuelC fuelD _ _ rfl hrest hrestD hgr htg (Or.inr (by simp [hv])) hex hv
      · have hdE : docExhaustGroup key d pre.length (fuelD + 1) =
            { d with it := rest, currValue := v, currKey := key v, groups := pre ++ [(T, GenPc.done)] } := by
          simp [docExhaustGroup, grouper_new key d pre T v rest hgr hd hv]
        cases fuelC with
        | zero => simp at hrest
        | succ f =>
          have hne : (T == key v) = false := by
            simp only [beq_eq_false_iff_ne]; exact fun h => hv h.symm
          have hcS2 : cGroupbySkip key (f + 1) { g with it := rest, currvalue := some v, currkey := some (key v) } =
              (true, { g with it := rest, currvalue := some v, currkey := some (key v) }) := by
            simp [cGroupbySkip, gbAdvance, htg, hne]
          rw [hcS, hcS2, hdE]
          exact ⟨rfl, rfl, htg, rfl, rfl, rfl, rfl, Or.inl ⟨rfl, rfl, rfl, hv, hex⟩⟩

/-! ## `next()` on a group -/

theorem gr_getD (pre : List (κ × GenPc)) (T : κ) (pc : GenPc) :
    ((pre ++ [(T, pc)]).map Prod.fst).getD pre.length default = T := by
  simp [List.getD_eq_getElem?_getD]

theorem pcOf_mem (groups : List (κ × GenPc)) (j : Nat) (hj : j < groups.length)
    (h : ∀ x ∈ groups, x.2 = GenPc.done) : (groups.getD j (default, GenPc.done)).2 = GenPc.done := by
  apply h
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

theorem cGrouperNext_stop (key : α → κ) (g : CGroupby α κ) (j : Nat) (h : g.currgrouper ≠ some j) :
    cGrouperNext key g j = (none, g) := by
  simp [cGrouperNext, h]

theorem cGrouperNext_pending (key : α → κ) (g : CGroupby α κ) (j : Nat) (T k : κ) (v : α)
    (hc : g.currgrouper = some j) (hv : g.currvalue = some v) (hT : g.groupers.getD j default = T)
    (hk : g.currkey = some k) :
    cGrouperNext key g j =
      if T == k then (some v, { g with currvalue := none, currkey := none }) else (none, g) := by
  simp only [cGrouperNext, hc, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hv, Option.isNone_some,
    hT, hk, Option.getD_some]

theorem cGrouperNext_nil (key : α → κ) (g : CGroupby α κ) (j : Nat)
    (hc : g.currgrouper = some j) (hv : g.currvalue = none) (hit : g.it = []) :
    cGrouperNext key g j = (none, g) := by
  simp only [cGrouperNext, hc, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hv, Option.isNone_none,
    cGroupbyStep, hit]

theorem cGrouperNext_cons (key : α → κ) (g : CGroupby α κ) (j : Nat) (T : κ) (v : α) (rest : List α)
    (hc : g.currgrouper = some j) (hv : g.currvalue = none) (hit : g.it = v :: rest)
    (hT : g.groupers.getD j default = T) :
    cGrouperNext key g j =
      if T == key v then (some v, { g with it := rest, currvalue := none, currkey := none })
      else (none, { g with it := rest, currvalue := some v, currkey := some (key v) }) := by
  simp only [cGrouperNext, hc, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hv, Option.isNone_none,
    cGroupbyStep, hit, hT, Option.getD_some]

theorem grouperNext_rel (key : α → κ) (g : CGroupby α κ) (d : DocGroupby α κ) (h : GbRel g d) (j : Nat)
    (hj : j < d.groups.length) :
    (cGrouperNext key g j).1 = (docGrouperNext key d j).1 ∧
      GbRel (cGrouperNext key g j).2 (docGrouperNext key d j).2 := by
  obtain ⟨hit, hgl, hph⟩ := h
  rcases hph with ⟨_, hg0, _⟩ | ⟨T, pre, pc, hgr, hpre, hou, htk, htg, hcg, hact⟩ | ⟨hou, hall, hcg, hgit, hck⟩
  · simp [hg0] at hj
  · by_cases hjp : j = pre.length
    · subst hjp
      have hc : g.currgrouper = some pre.length := hcg
      have hT : g.groupers.getD pre.length default = T := by rw [hgl, hgr, gr_getD]
      cases pc with
      | fresh =>
        obtain ⟨h1, h2, h3, h4⟩ := hact
        have hc1 : cGrouperNext key g pre.length =
            (some d.currValue, { g with currvalue := none, currkey := none }) := by
          rw [cGrouperNext_pending key g pre.length T d.currKey d.currValue hc h1 hT h2, h3]; simp
        rw [hc1, grouper_fresh key d pre T hgr]
        refine ⟨rfl, hit, by simp [hgl, hgr], Or.inr (Or.inl ⟨T, pre, .suspended, rfl, hpre, hou, htk, htg,
          hcg, rfl, rfl, h3, h4⟩)⟩
      | suspended =>
        obtain ⟨h1, h2, h3, h4⟩ := hact
        cases hxs : g.it with
        | nil =>
          have hd : d.it = [] := by rw [← hit, hxs]
          have hc1 := cGrouperNext_nil key g pre.length hc h1 hxs
          rw [hc1, grouper_nil key d pre T hgr hd]
          exact ⟨rfl, hit, by simp [hgl, hgr], Or.inr (Or.inl ⟨T, pre, .done, rfl, hpre, hou, htk, htg,
            hcg, Or.inr ⟨h2, h1, rfl, h3, hxs⟩⟩)⟩
        | cons v rest =>
          have hd : d.it = v :: rest := by rw [← hit, hxs]
          by_cases hv : key v = T
          · have hc1 : cGrouperNext key g pre.length =
                (some v, { g with it := rest, currvalue := none, currkey := none }) := by
              rw [cGrouperNext_cons key g pre.length T v rest hc h1 hxs hT, hv]; simp
            rw [hc1, grouper_same key d pre T v rest hgr hd hv]
            exact ⟨rfl, rfl, hgl, Or.inr (Or.inl ⟨T, pre, .suspended, hgr, hpre, hou, htk, htg, hcg,
              rfl, rfl, hv, h4⟩)⟩
          · have hne : (T == key v) = false := by
              simp only [beq_eq_false_iff_ne]; exact fun h => hv h.symm
            have hc1 : cGrouperNext key g pre.length =
                (none, { g with it := rest, currvalue := some v, currkey := some (key v) }) := by
              rw [cGrouperNext_cons key g pre.length T v rest hc h1 hxs hT, hne]; simp
            rw [hc1, grouper_new key d pre T v rest hgr hd hv]
            exact ⟨rfl, rfl, by simp [hgl, hgr], Or.inr (Or.inl ⟨T, pre, .done, rfl, hpre, hou, htk, htg,
              hcg, Or.inl ⟨rfl, rfl, hv, h4⟩⟩)⟩
      | done =>
        have hd := grouper_done key d pre.length (by rw [hgr, getD_snoc])
        have hrel : GbRel g d := ⟨hit, hgl, Or.inr (Or.inl ⟨T, pre, .done, hgr, hpre, hou, htk, htg, hcg, hact⟩)⟩
        rcases hact with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4, h5⟩
        · have hne : (T == d.currKey) = false := by
            simp only [beq_eq_false_iff_ne]; exact fun h => h3 h.symm
          have hc1 : cGrouperNext key g pre.length = (none, g) := by
            rw [cGrouperNext_pending key g pre.length T d.currKey d.currValue hc h1 hT h2, hne]; simp
          rw [hc1, hd]
          exact ⟨rfl, hrel⟩
        · have hc1 := cGrouperNext_nil key g pre.length hc h2 h5
          rw [hc1, hd]
          exact ⟨rfl, hrel⟩
    · have hjl : j < pre.length := by rw [hgr] at hj; simp at hj; omega
      have hc1 := cGrouperNext_stop key g j (by rw [hcg]; simp; omega)
      have hd : docGrouperNext key d j = (none, d) := by
        apply grouper_done
        rw [hgr, show (pre ++ [(T, pc)]).getD j (default, GenPc.done) = pre.getD j (default, GenPc.done) by
          simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hjl]]
        exact pcOf_mem pre j hjl hpre
      rw [hc1, hd]
      exact ⟨rfl, hit, hgl, Or.inr (Or.inl ⟨T, pre, pc, hgr, hpre, hou, htk, htg, hcg, hact⟩)⟩
  · have hc1 := cGrouperNext_stop key g j (by rw [hcg]; simp)
    rw [hc1, grouper_done key d j (pcOf_mem _ j hj hall)]
    exact ⟨rfl, hit, hgl, Or.inr (Or.inr ⟨hou, hall, hcg, hgit, hck⟩)⟩

/-! ## `next()` on the groupby object -/

/-- The end of `groupby_next` after the loop's `break`. -/
def gbNew (g : CGroupby α κ) : Option κ × CGroupby α κ :=
  (some (g.currkey.getD default),
    { g with tgtkey := some (g.currkey.getD default), groupers := g.groupers ++ [g.currkey.getD default],
             currgrouper := some g.groupers.length })

theorem cGroupbyNext_true (key : α → κ) (g g' : CGroupby α κ)
    (h : cGroupbySkip key (g.it.length + 1) { g with currgrouper := none } = (true, g')) :
    cGroupbyNext key g = gbNew g' := by
  simp [cGroupbyNext, h, gbNew, cGrouperCreate]

theorem cGroupbyNext_false (key : α → κ) (g g' : CGroupby α κ)
    (h : cGroupbySkip key (g.it.length + 1) { g with currgrouper := none } = (false, g')) :
    cGroupbyNext key g = (none, g') := by
  simp [cGroupbyNext, h]

/-- A new group starts: the C state and `docGroupbyLoopHead` agree. -/
theorem finish_new (g : CGroupby α κ) (d : DocGroupby α κ) (pre : List (κ × GenPc))
    (hit : g.it = d.it) (hgl : g.groupers = d.groups.map Prod.fst) (hpre : ∀ x ∈ pre, x.2 = GenPc.done)
    (hgr : d.groups = pre) (hcv : g.currvalue = some d.currValue) (hck : g.currkey = some d.currKey)
    (hex : d.exhausted = false) :
    (gbNew g).1 = (docGroupbyLoopHead d).1 ∧ GbRel (gbNew g).2 (docGroupbyLoopHead d).2 := by
  simp only [gbNew, docGroupbyLoopHead, hex, Bool.false_eq_true, ↓reduceIte, hck, Option.getD_some]
  refine ⟨by simp, hit, by simp [hgl], Or.inr (Or.inl ⟨d.currKey, pre, .fresh, by simp [hgr], hpre, rfl, rfl,
    rfl, ?_, hcv, rfl, rfl, rfl⟩)⟩
  simp [hgl, hgr]

theorem docLoopHead_exh (d : DocGroupby α κ) (h : d.exhausted = true) :
    docGroupbyLoopHead d = (none, { d with outer := .done }) := by
  simp [docGroupbyLoopHead, h]

theorem allDone_snoc (pre : List (κ × GenPc)) (T : κ) (hpre : ∀ x ∈ pre, x.2 = GenPc.done) :
    ∀ x ∈ pre ++ [(T, GenPc.done)], x.2 = GenPc.done := by
  intro x hx
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with h | h
  · exact hpre x h
  · subst h; rfl

/-- After the current frame has been run out by the outer generator. -/
theorem after_exhaust (key : α → κ) (g g' : CGroupby α κ) (d d' : DocGroupby α κ) (flag : Bool) (T : κ)
    (pre : List (κ × GenPc)) (hpre : ∀ x ∈ pre, x.2 = GenPc.done)
    (hskip : cGroupbySkip key (g.it.length + 1) { g with currgrouper := none } = (flag, g'))
    (hit : g'.it = d'.it) (hgl : g'.groupers = g.groupers) (hgl0 : g.groupers = d.groups.map Prod.fst)
    (hgr0 : d.groups.map Prod.fst = (pre ++ [(T, GenPc.done)]).map Prod.fst)
    (htg : g'.tgtkey = some T) (hcg : g'.currgrouper = none) (hgr : d'.groups = pre ++ [(T, GenPc.done)])
    (hres : (flag = true ∧ g'.currvalue = some d'.currValue ∧ g'.currkey = some d'.currKey ∧
          d'.exhausted = false) ∨
       (flag = false ∧ d'.exhausted = true ∧ g'.it = [] ∧ (g'.currkey = none ∨ g'.currkey = some T))) :
    (cGroupbyNext key g).1 = (docGroupbyLoopHead d').1 ∧
      GbRel (cGroupbyNext key g).2 (docGroupbyLoopHead d').2 := by
  rcases hres with ⟨rfl, h1, h2, h3⟩ | ⟨rfl, h1, h2, h3⟩
  · rw [cGroupbyNext_true key g g' hskip]
    exact finish_new g' d' _ hit (by rw [hgl, hgl0, hgr0, hgr]) (allDone_snoc pre T hpre) hgr h1 h2 h3
  · rw [cGroupbyNext_false key g g' hskip, docLoopHead_exh d' h1]
    refine ⟨rfl, hit, by simp only; rw [hgl, hgl0, hgr0, hgr], Or.inr (Or.inr ⟨rfl, ?_, hcg, h2, ?_⟩)⟩
    · simp only; rw [hgr]; exact allDone_snoc pre T hpre
    · rcases h3 with h | h
      · exact Or.inl h
      · exact Or.inr ⟨T, h, htg⟩

theorem groupbyNext_rel (key : α → κ) (g : CGroupby α κ) (d : DocGroupby α κ) (h : GbRel g d) :
    (cGroupbyNext key g).1 = (docGroupbyNext key d).1 ∧
      GbRel (cGroupbyNext key g).2 (docGroupbyNext key d).2 := by
  obtain ⟨hit, hgl, hph⟩ := h
  rcases hph with ⟨hou, hg0, h1, h2, h3, h4, h5⟩ | ⟨T, pre, pc, hgr, hpre, hou, htk, htg, hcg, hact⟩ |
    ⟨hou, hall, hcg, hgit, hck⟩
  · -- first call
    cases hxs : g.it with
    | nil =>
      have hd : d.it = [] := by rw [← hit, hxs]
      have hs : cGroupbySkip key (g.it.length + 1) { g with currgrouper := none } =
          (false, { g with currgrouper := none }) := by
        simp [cGroupbySkip, gbAdvance, h2, cGroupbyStep, hxs]
      rw [cGroupbyNext_false key g _ hs]
      simp only [docGroupbyNext, hou, hd]
      exact ⟨by simp, by simp [hxs], hgl, Or.inr (Or.inr ⟨rfl, by simp [hg0], rfl, hxs, Or.inl h2⟩)⟩
    | cons v rest =>
      have hd : d.it = v :: rest := by rw [← hit, hxs]
      have hs : cGroupbySkip key (g.it.length + 1) { g with currgrouper := none } =
          (true, { g with currgrouper := none, it := rest, currvalue := some v, currkey := some (key v) }) := by
        rw [hxs]
        simp [cGroupbySkip, gbAdvance, h2, h1, cGroupbyStep, hxs]
      rw [cGroupbyNext_true key g _ hs]
      simp only [docGroupbyNext, hou, hd]
      exact finish_new _ { d with it := rest, currValue := v, currKey := key v } [] rfl (by simp [hgl, hg0])
        (by simp) (by simp [hg0]) rfl rfl h5
  · -- a group is live
    have hglen : d.groups.length - 1 = pre.length := by rw [hgr]; simp
    cases pc with
    | fresh =>
      obtain ⟨h1, h2, h3, h4⟩ := hact
      have hdfresh : (d.currKey == d.targetKey) = true := by simp [h3, htk]
      have hdN : docGroupbyNext key d = docGroupbyLoopHead
          (docExhaustGroup key { d with groups := pre ++ [(T, GenPc.suspended)] } pre.length (d.it.length + 1)) := by
        simp [docGroupbyNext, hou, hdfresh, hglen, docExhaustGroup, grouper_fresh key d pre T hgr]
      have hex := exhaust_rel key T pre (g.it.length + 1) (d.it.length + 1) { g with currgrouper := none }
        { d with groups := pre ++ [(T, GenPc.suspended)] } hit (by simp) (by simp [hit]) rfl htg
        (Or.inr (by rw [show g.currkey = some T by rw [h2, h3]])) h4 h3
      rw [hdN]
      obtain ⟨e1, e2, e3, e4, e5, _, _, e6⟩ := hex
      exact after_exhaust key g _ d _ _ T pre hpre rfl e1 e2 hgl (by rw [hgr]; simp) e3 e4 e5
        (by rcases e6 with ⟨a, b, c, _, e⟩ | ⟨a, b, _, c, e⟩
            · exact Or.inl ⟨a, b, c, e⟩
            · exact Or.inr ⟨a, b, c, e⟩)
    | suspended =>
      obtain ⟨h1, h2, h3, h4⟩ := hact
      have hdsus : (d.currKey == d.targetKey) = true := by simp [h3, htk]
      have hdN : docGroupbyNext key d = docGroupbyLoopHead
          (docExhaustGroup key d pre.length (d.it.length + 2)) := by
        simp [docGroupbyNext, hou, hdsus, hglen]
      have hex := exhaust_rel key T pre (g.it.length + 1) (d.it.length + 2) { g with currgrouper := none }
        d hit (by simp) (by simp [hit]) hgr htg (Or.inl h2) h4 h3
      rw [hdN]
      obtain ⟨e1, e2, e3, e4, e5, _, _, e6⟩ := hex
      exact after_exhaust key g _ d _ _ T pre hpre rfl e1 e2 hgl (by rw [hgr]; simp) e3 e4 e5
        (by rcases e6 with ⟨a, b, c, _, e⟩ | ⟨a, b, _, c, e⟩
            · exact Or.inl ⟨a, b, c, e⟩
            · exact Or.inr ⟨a, b, c, e⟩)
    | done =>
      have hne0 := grouper_done key d pre.length (by rw [hgr, getD_snoc])
      rcases hact with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4, h5⟩
      · have hne : (T == d.currKey) = false := by
          simp only [beq_eq_false_iff_ne]; exact fun h => h3 h.symm
        have hk : (d.currKey == d.targetKey) = false := by
          simp only [beq_eq_false_iff_ne, htk]; exact h3
        have hdN : docGroupbyNext key d = docGroupbyLoopHead d := by
          simp [docGroupbyNext, hou, hk]
        have hs : cGroupbySkip key (g.it.length + 1) { g with currgrouper := none } =
            (true, { g with currgrouper := none }) := by
          simp [cGroupbySkip, gbAdvance, h2, htg, hne]
        rw [hdN, cGroupbyNext_true key g _ hs]
        exact finish_new _ d _ hit hgl (allDone_snoc pre T hpre) hgr h1 h2 h4
      · have hk : (d.currKey == d.targetKey) = true := by simp [h4, htk]
        have hE : docExhaustGroup key d pre.length (d.it.length + 2) = d := by
          simp [docExhaustGroup, hne0]
        have hdN : docGroupbyNext key d = docGroupbyLoopHead d := by
          simp [docGroupbyNext, hou, hk, hglen, hE]
        have hs : cGroupbySkip key (g.it.length + 1) { g with currgrouper := none } =
            (false, { g with currgrouper := none }) := by
          simp [cGroupbySkip, gbAdvance, h1, cGroupbyStep, h5]
        rw [hdN, docLoopHead_exh d h3, cGroupbyNext_false key g _ hs]
        exact ⟨rfl, hit, hgl, Or.inr (Or.inr ⟨rfl, by simp only; rw [hgr]; exact allDone_snoc pre T hpre,
          rfl, h5, Or.inl h1⟩)⟩
  · -- finished
    have hadv : gbAdvance g.currkey g.tgtkey = true := by
      rcases hck with h | ⟨T, h1, h2⟩
      · simp [gbAdvance, h]
      · simp [gbAdvance, h1, h2]
    have hs : cGroupbySkip key (g.it.length + 1) { g with currgrouper := none } =
        (false, { g with currgrouper := none }) := by
      simp [cGroupbySkip, hadv, cGroupbyStep, hgit]
    rw [cGroupbyNext_false key g _ hs]
    simp only [docGroupbyNext, hou]
    exact ⟨by simp, hit, hgl, Or.inr (Or.inr ⟨hou, hall, rfl, hgit, hck⟩)⟩

/-! ## Interleavings -/

/-- The public operations: no direct `_grouper` calls. -/
def GbOp.isPublic : GbOp κ → Bool
  | .direct _ => false
  | _ => true

theorem groupbyOps_eq (key : α → κ) : ∀ (ops : List (GbOp κ)) (g : CGroupby α κ) (d : DocGroupby α κ),
    GbRel g d → (∀ op ∈ ops, op.isPublic = true) → cGroupbyOps key g ops = docGroupbyOps key d ops
  | [], _, _, _, _ => rfl
  | .outer :: ops, g, d, h, hp => by
    have hs := groupbyNext_rel key g d h
    simp only [cGroupbyOps, docGroupbyOps]
    rw [hs.1, groupbyOps_eq key ops _ _ hs.2 (fun op hop => hp op (by simp [hop]))]
  | .group j :: ops, g, d, h, hp => by
    have hlen : g.groupers.length = d.groups.length := by rw [h.2.1]; simp
    simp only [cGroupbyOps, docGroupbyOps, hlen]
    by_cases hj : j < d.groups.length
    · have hs := grouperNext_rel key g d h j hj
      simp only [hj, ↓reduceIte]
      rw [hs.1, groupbyOps_eq key ops _ _ hs.2 (fun op hop => hp op (by simp [hop]))]
    · simp only [hj, ↓reduceIte]
      exact groupbyOps_eq key ops g d h (fun op hop => hp op (by simp [hop]))
  | .direct k :: ops, _, _, _, hp => by
    have := hp (.direct k) (by simp)
    simp [GbOp.isPublic] at this

/-- For every key function, input and interleaving of `next()` on the groupby
object and on any group it returned (including groups already advanced past),
the C object answers exactly as the doc's generators, over any element and
key type; a non-iterable input raises in both. Keys compare by decidable
equality. This is the statement for the model without failing calls, which
ignores `Obj.iter`'s exception; `GroupbyDocAgreeR` in `GroupbyRaising.lean` is the
one for the full model. -/
def GroupbyDocAgree : Prop :=
  ∀ (α κ : Type) [Inhabited α] [Inhabited κ] [DecidableEq κ] (key : α → κ) (o : Obj α)
    (ops : List (GbOp κ)), (∀ op ∈ ops, op.isPublic = true) → cGroupby key o ops = docGroupby key o ops

theorem groupbyDocAgree_proven : GroupbyDocAgree := by
  intro α κ _ _ _ key o ops hp
  cases o with
  | notIterable ty => rfl
  | iter l err =>
    simp only [cGroupby, cGroupbyNew, docGroupby, getIter]
    exact congrArg Except.ok
      (groupbyOps_eq key ops _ _ ⟨rfl, rfl, Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩ hp)

/-- A groupby over an input that cannot be iterated fails in the constructor. -/
def GroupbyCtorError : Prop :=
  ∀ (α κ : Type) (ty : String),
    (cGroupbyNew (.notIterable ty) : Py (CGroupby α κ)) = .error (.typeError s!"'{ty}' object is not iterable")

theorem groupbyCtorError_proven : GroupbyCtorError := fun _ _ _ => rfl

end PyLean.Itertools
