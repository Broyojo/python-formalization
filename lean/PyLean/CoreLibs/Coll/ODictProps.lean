import PyLean.CoreLibs.Coll.ODictG
import PyLean.CoreLibs.Coll.CounterProps2

/-!
The list invariant of the pure-Python `OrderedDict` (`ODictG.lean`): the links reachable from the
root form a chain whose order is the abstract list `L` of `(link id, key)`, `self.__map` sends each key
to its link, and the dict holds exactly those keys. Every mutator keeps it, with the order changed as
the docs say.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace PyLean.CoreLibs.Coll

open PyLean

variable {κ ν : Type} [DecidableEq κ]

/-- The id after `L` (`n` when `L` is empty). -/
def nxt : List (Nat × κ) → Nat → Nat
  | [], n => n
  | (j, _) :: _, _ => j

/-- The id of the last link of `L` (`p` when `L` is empty). -/
def lastOf (p : Nat) (L : List (Nat × κ)) : Nat := (L.getLast?.map (·.1)).getD p

/-- The links of `L`, in order, each pointing back to its predecessor (`p` for the first) and forward
to its successor (`n` after the last). -/
def Chain (h : Nat → OLink κ) : Nat → List (Nat × κ) → Nat → Prop
  | _, [], _ => True
  | p, (i, k) :: t, n => h i = ⟨some k, some p, some (nxt t n)⟩ ∧ Chain h i t n

/-- The update of one link, as `OD.setLink` does it. -/
def upd (h : Nat → OLink κ) (i : Nat) (f : OLink κ → OLink κ) : Nat → OLink κ :=
  fun j => if j = i then f (h j) else h j

theorem lastOf_cons (p p' : Nat) (q : Nat × κ) (t : List (Nat × κ)) : lastOf p (q :: t) = lastOf p' (q :: t) := by
  have : (q :: t).getLast? = some ((q :: t).getLast (by simp)) := List.getLast?_eq_getLast _
  simp [lastOf, this]

theorem lastOf_mem {p : Nat} {L : List (Nat × κ)} (hL : L ≠ []) : lastOf p L ∈ L.map (·.1) := by
  have : L.getLast? = some (L.getLast hL) := List.getLast?_eq_getLast _
  simp only [lastOf, this, Option.map_some, Option.getD_some]
  exact List.mem_map_of_mem (List.getLast_mem hL)

theorem chain_frame {h h' : Nat → OLink κ} :
    ∀ (L : List (Nat × κ)) (p n : Nat), (∀ x ∈ L.map (·.1), h' x = h x) → Chain h p L n → Chain h' p L n
  | [], _, _, _, _ => trivial
  | (i, k) :: t, p, n, hf, ⟨h1, h2⟩ => by
    refine ⟨by rw [hf i (by simp), h1], chain_frame t i n (fun x hx => hf x (by simp [hx])) h2⟩

theorem chain_append (h : Nat → OLink κ) :
    ∀ (A B : List (Nat × κ)) (p n : Nat), Chain h p (A ++ B) n ↔ Chain h p A (nxt B n) ∧ Chain h (lastOf p A) B n
  | [], B, p, n => by simp [Chain, lastOf]
  | (i, k) :: t, B, p, n => by
    have ih := chain_append h t B i n
    cases t with
    | nil =>
      show (h i = ⟨some k, some p, some (nxt B n)⟩ ∧ Chain h i B n) ↔
        ((h i = ⟨some k, some p, some (nxt B n)⟩ ∧ True) ∧ Chain h i B n)
      simp
    | cons q t' =>
      simp only [List.cons_append, Chain] at ih ⊢
      have hl : lastOf p ((i, k) :: q :: t') = lastOf i (q :: t') := by
        rw [lastOf_cons p i]; simp [lastOf, List.getLast?_cons_cons]
      rw [hl]
      constructor
      · rintro ⟨h1, h2⟩
        rw [ih] at h2
        exact ⟨⟨by simpa [nxt] using h1, h2.1⟩, h2.2⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨by simpa [nxt] using h1, ih.2 ⟨h2, h3⟩⟩

/-- Redirect the `next` of the last link of a chain. -/
theorem chain_retarget {h h' : Nat → OLink κ} :
    ∀ (L : List (Nat × κ)) (p n m : Nat), (L.map (·.1)).Nodup → Chain h p L n →
      (∀ x ∈ L.map (·.1), x ≠ lastOf p L → h' x = h x) →
      (L ≠ [] → h' (lastOf p L) = { h (lastOf p L) with next := some m }) → Chain h' p L m
  | [], _, _, _, _, _, _, _ => trivial
  | [(i, k)], p, n, m, _, ⟨h1, _⟩, _, hl => by
    have := hl (by simp)
    simp only [lastOf, List.getLast?_singleton, Option.map_some, Option.getD_some] at this
    refine ⟨?_, trivial⟩
    rw [this, h1]; rfl
  | (i, k) :: q :: t, p, n, m, hnd, ⟨h1, h2⟩, hf, hl => by
    have hlast : lastOf p ((i, k) :: q :: t) = lastOf i (q :: t) := by
      rw [lastOf_cons p i]; simp [lastOf, List.getLast?_cons_cons]
    have hi : i ≠ lastOf i (q :: t) := by
      intro he
      have hmem : lastOf i (q :: t) ∈ (q :: t).map (·.1) := lastOf_mem (by simp)
      rw [← he] at hmem
      exact (List.nodup_cons.1 hnd).1 (by simpa using hmem)
    refine ⟨?_, chain_retarget (q :: t) i n m (List.nodup_cons.1 hnd).2 h2 ?_ ?_⟩
    · rw [hf i (by simp) (by rw [hlast]; exact hi), h1]; rfl
    · intro x hx hne; exact hf x (by simp at hx ⊢; exact Or.inr hx) (by rw [hlast]; exact hne)
    · intro _; rw [← hlast]; exact hl (by simp)

/-- The keys of a chain ending at the root, walking `next` from its first link. -/
theorem walk_chain (o : OD κ ν) :
    ∀ (L : List (Nat × κ)) (p fuel : Nat), (∀ x ∈ L.map (·.1), x ≠ 0) → L.length < fuel → Chain o.heap p L 0 →
      o.walk fuel (nxt L 0) = L.map (·.2)
  | [], _, fuel, _, _, _ => by cases fuel <;> simp [OD.walk, nxt]
  | (i, k) :: t, p, fuel + 1, hz, hlen, ⟨h1, h2⟩ => by
    have hi : i ≠ 0 := hz i (by simp)
    show o.walk (fuel + 1) i = _
    simp only [OD.walk, hi, if_false, OD.link, h1, List.map_cons]
    rw [walk_chain o t i fuel (fun x hx => hz x (by simp [hx])) (by simp at hlen; omega) h2]

/-- **The list invariant.** `L` lists the live links, by id and key, in list order: they form a
chain from the root back to the root, the root points at the first and the last, ids are distinct,
non-zero and below the next fresh id, `self.__map` sends each key of `L` to its link, and the dict
holds exactly the keys of `L`, each once. -/
structure ODInv (o : OD κ ν) (L : List (Nat × κ)) : Prop where
  chain : Chain o.heap 0 L 0
  root : o.heap 0 = ⟨none, some (lastOf 0 L), some (nxt L 0)⟩
  ids : (L.map (·.1)).Nodup
  keys : (L.map (·.2)).Nodup
  pos : ∀ x ∈ L.map (·.1), 0 < x ∧ x < o.next
  len : L.length < o.next
  map : ∀ k, D.get? o.map k = (L.find? (·.2 = k)).map (·.1)
  mem : ∀ k, D.mem o.d k = decide (k ∈ L.map (·.2))
  wfd : D.WF o.d

/-- **Iteration follows the links.** Under the invariant, `list(od)` is the keys of `L` in order. -/
theorem keysList_inv {o : OD κ ν} {L : List (Nat × κ)} (I : ODInv o L) : o.keysList = L.map (·.2) := by
  unfold OD.keysList
  rw [show (o.link 0).next = some (nxt L 0) by simp [OD.link, I.root]]
  exact walk_chain o L 0 o.next (fun x hx => Nat.pos_iff_ne_zero.1 (I.pos x hx).1) I.len I.chain

theorem odInv_new : ODInv (OD.new : OD κ ν) [] := by
  refine ⟨trivial, rfl, by simp, by simp, by simp, by simp [OD.new], fun k => rfl, fun k => rfl, D.WF_nil⟩

end PyLean.CoreLibs.Coll
