import PyLean.DictSet.SetHooks

/-!
The generic branch of `set_intersection` (`Objects/setobject.c:1756-1790`) for an honest key
protocol: the result holds exactly the items of the iterable that the set holds, although the loop
may stop early, once the result has caught up with the set (:1772-1775); a pigeonhole step shows
that nothing is lost by stopping.
-/

namespace PyLean.DictSet

open PyLean

section InterIter
variable {K : Type} [DecidableEq K] {P : Proto K (SetObj K)} {hf : K → Int} {eqv : K → K → Bool}

/-- What the generic loop keeps: the result is well formed and in focus, with `so` as its one peer,
and holds exactly the keys seen so far that `so` holds, no more of them than were seen. -/
structure InterInv (hf : K → Int) (eqv : K → K → Bool) (so : SetObj K) (id : Nat) (done : List K)
    (s : SetObj K) : Prop where
  wf : SetWF hf eqv s
  ident : s.ident = id
  peers : s.peers = [so.toSetBody]
  keys : ∀ y, (setKeys s).any (eqv · y) = (done.any (eqv · y) && (setKeys so).any (eqv · y))
  used : s.used ≤ done.length

omit [DecidableEq K] in
theorem any_congr_eqv (H : HonestSet P hf eqv) (l : List K) {x y : K} (h : eqv x y = true) :
    l.any (eqv · x) = l.any (eqv · y) := by
  cases hx : l.any (eqv · x) with
  | true =>
    obtain ⟨k, hk, hkx⟩ := List.any_eq_true.mp hx
    exact (List.any_eq_true.mpr ⟨k, hk, H.trans k x y hkx h⟩).symm
  | false =>
    cases hy : l.any (eqv · y) with
    | false => rfl
    | true =>
      obtain ⟨k, hk, hky⟩ := List.any_eq_true.mp hy
      have : eqv k x = true := H.trans k y x hky (by rw [H.symm]; exact h)
      have h2 := List.any_eq_false.mp hx k hk
      simp [this] at h2

omit [DecidableEq K] in
theorem setKeys_pairwise {s : SetObj K} (w : SetWF hf eqv s) :
    (setKeys s).Pairwise (fun a b => eqv a b = false) := by
  unfold setKeys
  exact List.pairwise_map.mpr (entries_pairwise w.toSetCore)

/-- A result whose keys `so` all holds, as large as `so`, holds every key of `so`. -/
theorem caught_up (H : HonestSet P hf eqv) {s so : SetObj K} (w : SetWF hf eqv s)
    (wso : SetWF hf eqv so)
    (hsub : ∀ y, (setKeys s).any (eqv · y) = true → (setKeys so).any (eqv · y) = true)
    (hge : so.used ≤ s.used) :
    ∀ y, (setKeys so).any (eqv · y) = true → (setKeys s).any (eqv · y) = true := by
  intro y hy
  cases hs : (setKeys s).any (eqv · y) with
  | true => rfl
  | false =>
    exfalso
    let m := (setKeys so).filter fun w => !eqv w y
    obtain ⟨w0, hw0, hw0y⟩ := List.any_eq_true.mp hy
    have hlt : m.length < (setKeys so).length := by
      apply List.length_filter_lt_length_iff_exists.mpr
      exact ⟨w0, hw0, by simp [hw0y]⟩
    have hall : (setKeys s).all (fun k => m.any (eqv · k)) = true := by
      apply List.all_eq_true.mpr
      intro k hk
      have hkk : (setKeys s).any (eqv · k) = true := List.any_eq_true.mpr ⟨k, hk, H.refl k⟩
      obtain ⟨w1, hw1, hw1k⟩ := List.any_eq_true.mp (hsub k hkk)
      apply List.any_eq_true.mpr
      refine ⟨w1, List.mem_filter.mpr ⟨hw1, ?_⟩, hw1k⟩
      cases hq : eqv w1 y with
      | false => rfl
      | true =>
        have hky : eqv k y = true := H.trans k w1 y (by rw [H.symm]; exact hw1k) hq
        have := List.any_eq_false.mp hs k hk
        simp [hky] at this
    have hp := pigeon H (setKeys s) m (setKeys_pairwise w) ((setKeys_pairwise wso).filter _) hall
    have e1 := setKeys_length w
    have e2 := setKeys_length wso
    omega

theorem inter_live {so s : SetObj K} {id : Nat} (hid : id ≠ so.ident) (hident : s.ident = id)
    (hpeers : s.peers = [so.toSetBody]) : s.live so.ident = so.toSetBody := by
  apply live_peer (by rw [hident]; exact hid)
  rw [hpeers]
  simp [List.find?]

theorem inter_onSet (H : HonestSet P hf eqv) {so s : SetObj K} {id : Nat} (wso : SetWF hf eqv so)
    (hid : id ≠ so.ident) (hident : s.ident = id) (hpeers : s.peers = [so.toSetBody]) (x : K) :
    onSet so.ident (setContainsEntry P x (hf x)) s = (.ok ((setKeys so).any (eqv · x)), s) := by
  apply onSet_contains H wso x (by rw [hident]; exact hid) (by rw [hpeers]; simp)
  · intro b hb _
    rw [hpeers] at hb
    simpa using hb
  · intro b hb
    rw [hpeers] at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    subst hb
    rw [hident]
    exact fun h => hid h.symm

/-- One turn of the generic loop, for an honest protocol. -/
theorem inter_step (H : HonestSet P hf eqv) {so s : SetObj K} {id : Nat} {done : List K}
    (wso : SetWF hf eqv so) (hid : id ≠ so.ident) (hi : InterInv hf eqv so id done s) (x : K) :
    (∃ s', SetTooBig (s.used + 1) ∧ interIterStep P so.ident x s = (.error memoryError, s')) ∨
    ∃ s', InterInv hf eqv so id (done ++ [x]) s' ∧
      interIterStep P so.ident x s =
        (.ok (decide (s'.used ≥ so.used) && (setKeys so).any (eqv · x)), s') := by
  have hon := inter_onSet (P := P) H wso hid hi.ident hi.peers x
  have hlive := inter_live hid hi.ident hi.peers
  have hdone : ∀ y, (done ++ [x]).any (eqv · y) = (done.any (eqv · y) || eqv x y) := by
    intro y
    simp
  cases hso : (setKeys so).any (eqv · x) with
  | false =>
    right
    refine ⟨s, ⟨hi.wf, hi.ident, hi.peers, fun y => ?_, by simp; have := hi.used; omega⟩, ?_⟩
    · rw [hi.keys y, hdone y]
      cases hxy : eqv x y with
      | false => simp
      | true =>
        have : (setKeys so).any (eqv · y) = false := by
          rw [← any_congr_eqv H (setKeys so) hxy]
          exact hso
        simp [this]
    · simp [interIterStep, M.bind_run, H.hash_ok, hon, hso]
  | true =>
    rcases setAddEntry_spec H hi.wf x with ⟨h1, h2⟩ | ⟨h1, h3⟩
    · right
      refine ⟨s, ⟨hi.wf, hi.ident, hi.peers, fun y => ?_, by simp; have := hi.used; omega⟩, ?_⟩
      · rw [hi.keys y, hdone y]
        cases hxy : eqv x y with
        | false => simp
        | true =>
          have e1 : (setKeys so).any (eqv · y) = true := by
            rw [← any_congr_eqv H (setKeys so) hxy]
            exact hso
          have e2 : (setKeys s).any (eqv · y) = true := by
            rw [← any_congr_eqv H (setKeys s) hxy]
            exact h1
          rw [hi.keys y] at e2
          rw [e2]
          simp [hxy, e1]
      · by_cases hc : s.used ≥ so.used <;>
          simp [interIterStep, M.bind_run, H.hash_ok, hon, hso, h2, M.get_run, hlive, hc]
    · rcases h3 with ⟨hb, s', h3⟩ | ⟨s', a, b, c, d, e⟩
      · left
        exact ⟨s', hb, by simp [interIterStep, M.bind_run, H.hash_ok, hon, hso, h3]⟩
      · right
        have hk' : (setKeys s').Perm (x :: setKeys s) := by
          simpa [setKeys] using c.map Prod.fst
        have hu : s'.used = s.used + 1 := by
          have e1 := setKeys_length b
          have e2 := setKeys_length hi.wf
          have e3 := hk'.length_eq
          simp only [List.length_cons] at e3
          omega
        have hlive' := inter_live hid (e.trans hi.ident) (d.trans hi.peers)
        refine ⟨s', ⟨b, e.trans hi.ident, d.trans hi.peers, fun y => ?_, ?_⟩, ?_⟩
        · rw [hk'.any_eq, List.any_cons, hi.keys y, hdone y]
          cases hxy : eqv x y with
          | false => simp
          | true =>
            have e1 : (setKeys so).any (eqv · y) = true := by
              rw [← any_congr_eqv H (setKeys so) hxy]
              exact hso
            simp [e1]
        · simp only [List.length_append, List.length_cons, List.length_nil]
          have := hi.used
          omega
        · by_cases hc : s'.used ≥ so.used <;>
            simp [interIterStep, M.bind_run, H.hash_ok, hon, hso, a, M.get_run, hlive', hc]

theorem forIter_pure_cons (body : K → SM K Bool) (x : K) (rest : List (SM K (Option K)))
    (s : SetObj K) :
    forIter body (pure (some x) :: rest) s =
      match body x s with
      | (.ok true, s') => (.ok true, s')
      | (.ok false, s') => forIter body rest s'
      | (.error e, s') => (.error e, s') := by
  simp only [forIter, M.bind_run, M.pure_run]
  rcases body x s with ⟨r, s'⟩
  cases r with
  | error e => rfl
  | ok b => cases b <;> rfl

/-- The generic loop over items handed over as they are. -/
theorem inter_loop (H : HonestSet P hf eqv) {so : SetObj K} {id : Nat} (wso : SetWF hf eqv so)
    (hid : id ≠ so.ident) :
    ∀ (rest done : List K) (s : SetObj K), InterInv hf eqv so id done s →
      (∃ s' n, n ≤ done.length + rest.length ∧ SetTooBig n ∧
        forIter (interIterStep P so.ident) (rest.map (fun x => pure (some x))) s =
          (.error memoryError, s')) ∨
      ∃ b s', forIter (interIterStep P so.ident) (rest.map (fun x => pure (some x))) s = (.ok b, s') ∧
        SetWF hf eqv s' ∧ s'.ident = id ∧ s'.peers = [so.toSetBody] ∧
        ∀ y, (setKeys s').any (eqv · y) = ((done ++ rest).any (eqv · y) && (setKeys so).any (eqv · y)) := by
  intro rest
  induction rest with
  | nil =>
    intro done s hi
    right
    exact ⟨false, s, rfl, hi.wf, hi.ident, hi.peers, fun y => by simpa using hi.keys y⟩
  | cons x rest ih =>
    intro done s hi
    rw [List.map_cons, forIter_pure_cons]
    rcases inter_step (P := P) H wso hid hi x with ⟨s', hb, h⟩ | ⟨s', hi', h⟩
    · left
      refine ⟨s', s.used + 1, ?_, hb, by rw [h]⟩
      have := hi.used
      simp only [List.length_cons]
      omega
    · rw [h]
      cases hb : (decide (s'.used ≥ so.used) && (setKeys so).any (eqv · x)) with
      | true =>
        right
        refine ⟨true, s', rfl, hi'.wf, hi'.ident, hi'.peers, fun y => ?_⟩
        have hge : so.used ≤ s'.used := by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
          exact hb.1
        have hsub : ∀ y, (setKeys s').any (eqv · y) = true → (setKeys so).any (eqv · y) = true := by
          intro y hy
          rw [hi'.keys y] at hy
          simp only [Bool.and_eq_true] at hy
          exact hy.2
        have hcu := caught_up H hi'.wf wso hsub hge
        cases hsy : (setKeys so).any (eqv · y) with
        | false =>
          rw [hi'.keys y, hsy]
          simp
        | true =>
          have h1 := hcu y hsy
          have h2 : (done ++ [x]).any (eqv · y) = true := by
            rw [hi'.keys y, hsy, Bool.and_true] at h1
            exact h1
          obtain ⟨z, hz, hzy⟩ := List.any_eq_true.mp h2
          have h3 : (done ++ x :: rest).any (eqv · y) = true := by
            apply List.any_eq_true.mpr
            refine ⟨z, ?_, hzy⟩
            simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil,
              or_false] at hz ⊢
            rcases hz with hz | hz
            · exact Or.inl hz
            · exact Or.inr (Or.inl hz)
          rw [hcu y hsy, h3]
          simp [hsy]
      | false =>
        rcases ih (done ++ [x]) s' hi' with ⟨s2, n, a, b, c⟩ | ⟨b, s2, a, c, d, e, f⟩
        · left
          refine ⟨s2, n, ?_, b, c⟩
          simp only [List.length_append, List.length_cons, List.length_nil] at a ⊢
          omega
        · right
          refine ⟨b, s2, a, c, d, e, fun y => ?_⟩
          rw [f y, List.append_assoc]
          rfl

end InterIter

/-- `set_intersection` with an iterable that is not a set, for an honest key protocol, from a
well-formed set: either an add runs out of memory, for a result `PyMem_NEW` cannot hold, or the
result is a new well-formed set that holds exactly the items `so` holds, although the loop stops
once the result has caught up with `so` (:1772-1775), and `so` is unchanged. -/
def SetInterIterRefines : Prop :=
  ∀ (K : Type) [DecidableEq K] (P : Proto K (SetObj K)) (hf : K → Int) (eqv : K → K → Bool),
    HonestSet P hf eqv → ∀ (so : SetObj K) (items : List K) (id : Nat),
      SetWF hf eqv so → so.peers = [] → id ≠ so.ident →
      (∃ s n, n ≤ items.length ∧ SetTooBig n ∧
        setIntersection P (.iter { items := items }) id so = (.error memoryError, s)) ∨
      ∃ r, setIntersection P (.iter { items := items }) id so = (.ok r, so) ∧ SetWF hf eqv r ∧
        ∀ y, (setKeys r).any (eqv · y) = (items.any (eqv · y) && (setKeys so).any (eqv · y))
theorem setInterIterRefines_proven : SetInterIterRefines := by
  intro K _ P hf eqv H so items id wso hps hid
  obtain ⟨wr0, her0⟩ := newBasetype_wf hf eqv so.toSetBody id (so.toSetBody :: so.peers)
  have hi0 : InterInv hf eqv so id []
      { newBasetype so.toSetBody id with peers := so.toSetBody :: so.peers } :=
    { wf := wr0, ident := rfl, peers := by simp [hps]
      keys := fun y => by simp [setKeys, her0]
      used := by simp [newBasetype] }
  have hrun := (setIntersectionBranches_proven K P id so so (ReIter.ofIterable { items := [] })).2.2.1
    (.iter { items := items }) (fun s => nofun) (fun s it' => nofun)
  have hloop : setInterIter P so.ident (SetArg.iter ({ items := items } : Iterable K)).toReIter
      { newBasetype so.toSetBody id with peers := so.toSetBody :: so.peers } =
      forIter (interIterStep P so.ident) (items.map (fun x => pure (some x)))
        { newBasetype so.toSetBody id with peers := so.toSetBody :: so.peers } := by
    simp only [setInterIter, SetArg.toReIter, ReIter.ofIterable, M.bind_run, M.pure_run,
      List.append_nil]
  have hso : ({ toSetBody := so.toSetBody, peers := [] } : SetObj K) = so := by
    rw [← hps]
  rcases inter_loop (P := P) H wso hid items [] _ hi0 with ⟨s, n, a, b, c⟩ | ⟨bv, s, a, b, c, d, e⟩
  · left
    have h1 : (setIntersection P (.iter { items := items }) id so).1 = .error memoryError := by
      rw [hrun]
      simp only [onResult, hloop, c]
    refine ⟨(setIntersection P (.iter { items := items }) id so).2, n, by simpa using a, b, ?_⟩
    exact Prod.ext h1 rfl
  · right
    refine ⟨{ s with peers := [] }, ?_,
      { toSetCore := b.toSetCore.of_fields rfl rfl rfl rfl, load := b.load },
      fun y => by
        have h := e y
        simp only [List.nil_append] at h
        exact h⟩
    rw [hrun]
    simp only [onResult, hloop, a, d, hso]

end PyLean.DictSet
