import PyLean.CoreLibs.Coll.ODictMore
import PyLean.CoreLibs.Coll.CounterProps3

/-!
`OrderedDict.update` (and `__init__`, `copy`, `fromkeys`, `|`, `|=`, `__ror__`) keep the invariant,
the keys coming in first-seen order after the existing ones.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace PyLean.CoreLibs.Coll

open PyLean

variable {κ ν : Type} [DecidableEq κ]

/-- A loop whose every step is `od[key x] = v` for some `v`: the invariant holds after, with the new keys
appended in first-seen order. -/
theorem setLoop_inv (K : KOps κ) {α : Type} (f : OD κ ν → α → Py (OD κ ν)) (key : α → κ) :
    ∀ (xs : List α) (o : OD κ ν) (L : List (Nat × κ)), ODInv o L → (∀ x ∈ xs, K.hash (key x) = .ok ()) →
      (∀ o, ∀ x ∈ xs, ∃ v, f o x = odSet K o (key x) v) →
      ∃ o' L', loopS f o xs = (o', none) ∧ ODInv o' L' ∧ L'.map (·.2) = firstSeen (L.map (·.2)) (xs.map key)
  | [], o, L, I, _, _ => ⟨o, L, rfl, I, rfl⟩
  | x :: xs, o, L, I, hh, hf => by
    obtain ⟨v, hfx⟩ := hf o x (by simp)
    obtain ⟨o1, h1, I1, _⟩ := odSetInv_proven κ ν K o L (key x) v I (hh x (by simp))
    obtain ⟨o', L', h2, I', hL'⟩ := setLoop_inv K f key xs o1 _ I1 (fun y hy => hh y (by simp [hy]))
      (fun o y hy => hf o y (by simp [hy]))
    refine ⟨o', L', ?_, I', ?_⟩
    · simp only [loopS, hfx, h1]; exact h2
    · rw [hL']
      simp only [List.map_cons, firstSeen, List.foldl_cons]
      congr 1
      by_cases hk : key x ∈ L.map (·.2) <;> simp [hk]

theorem loopS_map {σ α β : Type} (f : σ → β → Py σ) (g : α → β) :
    ∀ (xs : List α) (s : σ), loopS f s (xs.map g) = loopS (fun s x => f s (g x)) s xs
  | [], _ => rfl
  | x :: xs, s => by
    simp only [List.map_cons, loopS]
    cases f s (g x) with
    | ok s' => exact loopS_map f g xs s'
    | error e => rfl

/-- **`update`, `__init__`, `fromkeys` and `copy` add keys in first-seen order.** For every instance
with list `L` and every iterable of hashable pairs (or keys) that does not raise: `od.update(pairs)`
keeps the invariant with the keys of `L` and then the new keys in first-seen order; `OrderedDict(pairs)`
is the update of a new instance; `OrderedDict.fromkeys(xs, v)` has the keys of `xs` in first-seen
order; `od.copy()` (and so `od | other`, whose left half it is) has `od`'s keys in `od`'s order.

Source: Doc/library/collections.rst ('remembers the order entries were added'); Lib/collections/__init__.py:113-117,
:303-314, :329-334; Lib/_collections_abc.py:965-984. -/
def ODUpdateOrder : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] (K : KOps κ) (o : OD κ ν) (L : List (Nat × κ)) (ps : List (κ × ν)) (xs : List κ)
    (v : ν), ODInv o L → (∀ p ∈ ps, K.hash p.1 = .ok ()) → (∀ k ∈ xs, K.hash k = .ok ()) →
    (∃ o' L', odUpdate K o (.pairs (.ok (FIt.ofList (ps.map .ok)))) = (o', none) ∧ ODInv o' L' ∧
      L'.map (·.2) = firstSeen (L.map (·.2)) (ps.map (·.1))) ∧
    (∃ o' L', odFromkeys K (.ok (FIt.ofList xs)) v = .ok o' ∧ ODInv o' L' ∧ L'.map (·.2) = firstSeen [] xs) ∧
    ((∀ k ∈ L.map (·.2), K.hash k = .ok ()) →
      ∃ o' L', odCopy K o = .ok o' ∧ ODInv o' L' ∧ L'.map (·.2) = L.map (·.2))

theorem firstSeen_nodup : ∀ (xs : List κ), xs.Nodup → firstSeen [] xs = xs := by
  intro xs hxs
  suffices h : ∀ (acc ys : List κ), (acc ++ ys).Nodup → firstSeen acc ys = acc ++ ys by simpa using h [] xs (by simpa)
  intro acc ys
  induction ys generalizing acc with
  | nil => intro _; simp [firstSeen]
  | cons y ys ih =>
    intro h
    have hy : y ∉ acc := fun hm => by
      rw [List.nodup_append] at h; exact h.2.2 y hm y (by simp) rfl
    simp only [firstSeen, List.foldl_cons, hy, if_false]
    have := ih (acc ++ [y]) (by simpa using h)
    simpa [firstSeen] using this

theorem odUpdateOrder_proven : ODUpdateOrder := by
  intro κ ν _ K o L ps xs v I hps hxs
  refine ⟨?_, ?_, fun hL => ?_⟩
  · obtain ⟨o', L', h, I', hL'⟩ := setLoop_inv K (fun o (q : κ × ν) => odSet K o q.1 q.2) (·.1) ps o L I hps
      (fun o q _ => ⟨q.2, rfl⟩)
    refine ⟨o', L', ?_, I', hL'⟩
    show forIt (fun o (p : Py (κ × ν)) => do let (k, v) ← p; odSet K o k v) o
      (FIt.ofList (ps.map (Except.ok (ε := PyExc)))) = _
    simp only [forIt, FIt.ofList]
    rw [loopS_map]
    have : loopS (fun o (q : κ × ν) => (do let (k, v) ← (Except.ok q : Py (κ × ν)); odSet K o k v)) o ps =
        loopS (fun o (q : κ × ν) => odSet K o q.1 q.2) o ps := rfl
    rw [this, h]
  · obtain ⟨o', L', h, I', hL'⟩ := setLoop_inv K (fun o k => odSet K o k v) id xs OD.new [] odInv_new hxs
      (fun o k _ => ⟨v, rfl⟩)
    refine ⟨o', L', ?_, I', by simpa using hL'⟩
    show Out.toPy (forIt _ OD.new (FIt.ofList xs)) = _
    simp only [forIt, FIt.ofList, h, Out.toPy]
  · have hval : ∀ k ∈ L.map (·.2), ∃ w, D.get? o.d k = some w := fun k hk =>
      Option.isSome_iff_exists.1 (by have := I.mem k; unfold D.mem at this; rw [this]; simpa using hk)
    have hk := keysList_inv I
    let g : κ → Py ν := fun k => match D.get? o.d k with
      | some w => .ok w
      | none => .error (.keyError "~key")
    obtain ⟨o', L', h, I', hL'⟩ := setLoop_inv K (fun o' k => do let w ← g k; odSet K o' k w) id (L.map (·.2))
      OD.new [] odInv_new hL (fun o' k hk' => by
        obtain ⟨w, hw⟩ := hval k hk'
        exact ⟨w, by simp [g, hw]⟩)
    refine ⟨o', L', ?_, I', ?_⟩
    · show Out.toPy (forIt (fun o' k => do let w ← g k; odSet K o' k w) OD.new (FIt.ofList o.keysList)) = _
      rw [hk]
      simp only [forIt, FIt.ofList, h, Out.toPy]
    · rw [hL']; simpa using firstSeen_nodup _ I.keys

end PyLean.CoreLibs.Coll
