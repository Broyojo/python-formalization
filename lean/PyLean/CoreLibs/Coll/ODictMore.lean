import PyLean.CoreLibs.Coll.ODictDel

/-!
`OrderedDict.popitem` and `setdefault` keep the list invariant; iteration, `__eq__`, `__reduce__` and
`__repr__` follow the link order.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace PyLean.CoreLibs.Coll

open PyLean

variable {κ ν : Type} [DecidableEq κ]

/-- The invariant only reads the live links and the root. -/
theorem odInv_frame {o o' : OD κ ν} {L : List (Nat × κ)} (I : ODInv o L) (i : Nat) (hd : o'.d = o.d)
    (hm : o'.map = o.map) (hn : o'.next = o.next) (hh : ∀ x, x ≠ i → o'.heap x = o.heap x)
    (hiL : i ∉ L.map (·.1)) (hi0 : i ≠ 0) : ODInv o' L := by
  refine ⟨chain_frame L 0 0 (fun x hx => hh x (fun e => hiL (e ▸ hx))) I.chain, by rw [hh 0 (Ne.symm hi0)]; exact I.root,
    I.ids, I.keys, fun x hx => by rw [hn]; exact I.pos x hx, by rw [hn]; exact I.len,
    fun k => by rw [hm]; exact I.map k, fun k => by rw [hd]; exact I.mem k, by rw [hd]; exact I.wfd,
    by rw [hm]; exact I.wfm⟩

/-- **`popitem` removes the last (or first) item and keeps the invariant.** For every instance with
list `A ++ [(i, key)]`, `od.popitem()` returns `(key, od[key])` and leaves `A`; for a list
`(i, key) :: B`, `od.popitem(last=False)` returns the first item and leaves `B`; an empty one raises
`KeyError('dictionary is empty')`.

Source: docstring, Lib/collections/__init__.py:172-175 ('Pairs are returned in LIFO order if last is
true or FIFO order if false'). -/
def ODPopitemInv : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] (rk : κ → String) (o : OD κ ν),
    (∀ (A : List (Nat × κ)) (i : Nat) (key : κ), ODInv o (A ++ [(i, key)]) →
      ∃ v o', odPopitem rk o true = .ok ((key, v), o') ∧ D.get? o.d key = some v ∧ ODInv o' A) ∧
    (∀ (B : List (Nat × κ)) (i : Nat) (key : κ), ODInv o ((i, key) :: B) →
      ∃ v o', odPopitem rk o false = .ok ((key, v), o') ∧ D.get? o.d key = some v ∧ ODInv o' B) ∧
    (ODInv o [] → ∀ last, odPopitem rk o last = .error (keyErrorStr "dictionary is empty"))

theorem odPopitemInv_proven : ODPopitemInv := by
  intro κ ν _ rk o
  refine ⟨fun A i key I => ?_, fun B i key I => ?_, fun I last => ?_⟩
  · have hm : D.mem o.d key = true := by rw [I.mem key]; simp
    obtain ⟨v, hv⟩ : ∃ v, D.get? o.d key = some v := Option.isSome_iff_exists.1 hm
    have hne : o.d.isEmpty = false := by
      cases hd : o.d with
      | nil => rw [hd] at hv; simp [D.get?] at hv
      | cons a t => rfl
    have I' : ODInv o (A ++ (i, key) :: []) := I
    have hch := I.chain
    rw [chain_append] at hch
    have hi : o.heap i = ⟨some key, some (lastOf 0 A), some 0⟩ :=
      (show o.heap i = ⟨some key, some (lastOf 0 A), some (nxt ([] : List (Nat × κ)) 0)⟩ ∧ True from hch.2).1
    have hi0 : i ≠ 0 := Nat.pos_iff_ne_zero.1 (I.pos i (by simp)).1
    have hroot : (o.heap 0).prev = some i := by rw [I.root]; simp [lastOf]
    have hiA : i ∉ A.map (·.1) := by
      have h := I.ids
      rw [List.map_append, List.nodup_append] at h
      exact fun hm => h.2.2 i hm i (by simp) rfl
    have hlpi : lastOf 0 A ≠ i := by
      by_cases hA : A = []
      · subst hA; exact Ne.symm hi0
      · intro he; exact hiA (he ▸ lastOf_mem hA)
    have hcore := del_core (K := ⟨fun _ => .ok (), fun _ => ""⟩) o A [] i key I'
    simp only [List.append_nil] at hcore
    refine ⟨v, { ((o.setNext (lastOf 0 A) 0).setPrev 0 (lastOf 0 A)) with map := D.del o.map key, d := D.del o.d key },
      ?_, hv, ?_⟩
    · simp only [odPopitem, hne, Bool.false_eq_true, if_false, if_true, OD.link, hroot, Option.getD_some, hi,
        OD.setPrev, OD.setNext, setLink_heap, hlpi, Ne.symm hlpi, hi0, Ne.symm hi0, setLink_d, hv]
      try rfl
    · refine odInv_frame hcore i rfl rfl rfl ?_ (by simpa using hiA) hi0
      intro x hxi
      have hp : (({ o with d := D.del o.d key, map := D.del o.map key } : OD κ ν).heap i).prev = some (lastOf 0 A) := by
        show (o.heap i).prev = _; rw [hi]
      have hn : (({ o with d := D.del o.d key, map := D.del o.map key } : OD κ ν).heap i).next = some 0 := by
        show (o.heap i).next = _; rw [hi]
      rw [dropLink_heap _ i (lastOf 0 A) 0 hp hn x hxi]
      simp only [OD.setPrev, OD.setNext, setLink_heap]
      all_goals (by_cases h0 : x = 0 <;> by_cases hl : x = lastOf 0 A <;> simp [h0, hl])
  · have hm : D.mem o.d key = true := by rw [I.mem key]; simp
    obtain ⟨v, hv⟩ : ∃ v, D.get? o.d key = some v := Option.isSome_iff_exists.1 hm
    have hne : o.d.isEmpty = false := by
      cases hd : o.d with
      | nil => rw [hd] at hv; simp [D.get?] at hv
      | cons a t => rfl
    have I' : ODInv o ([] ++ (i, key) :: B) := I
    have hi : o.heap i = ⟨some key, some 0, some (nxt B 0)⟩ :=
      (show o.heap i = ⟨some key, some 0, some (nxt B 0)⟩ ∧ Chain o.heap i B 0 from I.chain).1
    have hi0 : i ≠ 0 := Nat.pos_iff_ne_zero.1 (I.pos i (by simp)).1
    have hroot : (o.heap 0).next = some i := by rw [I.root]; rfl
    have hiB : i ∉ B.map (·.1) := (List.nodup_cons.1 (by simpa using I.ids)).1
    have hlni : nxt B 0 ≠ i := by
      by_cases hB : B = []
      · subst hB; exact Ne.symm hi0
      · intro he; exact hiB (he ▸ nxt_mem 0 hB)
    have hcore := del_core (K := ⟨fun _ => .ok (), fun _ => ""⟩) o [] B i key I'
    simp only [List.nil_append] at hcore
    refine ⟨v, { ((o.setNext 0 (nxt B 0)).setPrev (nxt B 0) 0) with map := D.del o.map key, d := D.del o.d key },
      ?_, hv, ?_⟩
    · simp only [odPopitem, hne, Bool.false_eq_true, if_false, OD.link, hroot, Option.getD_some, hi,
        OD.setPrev, OD.setNext, setLink_heap, hlni, Ne.symm hlni, hi0, Ne.symm hi0, setLink_d, hv]
      try rfl
    · refine odInv_frame hcore i rfl rfl rfl ?_ hiB hi0
      intro x hxi
      have hp : (({ o with d := D.del o.d key, map := D.del o.map key } : OD κ ν).heap i).prev = some 0 := by
        show (o.heap i).prev = _; rw [hi]
      have hn : (({ o with d := D.del o.d key, map := D.del o.map key } : OD κ ν).heap i).next = some (nxt B 0) := by
        show (o.heap i).next = _; rw [hi]
      rw [dropLink_heap _ i 0 (nxt B 0) hp hn x hxi]
      simp only [OD.setPrev, OD.setNext, setLink_heap]
      all_goals (by_cases h0 : x = 0 <;> by_cases hl : x = nxt B 0 <;> simp [h0, hl])
  · have hd : o.d = [] := by
      cases hd : o.d with
      | nil => rfl
      | cons a t =>
        have := I.mem a.1
        unfold D.mem at this
        rw [hd] at this
        simp [D.get?] at this
    simp [odPopitem, hd]

/-- **`setdefault` returns the stored value or stores the default at the end.** For every hashable
key: a present key returns its value and leaves the list; an absent one stores the default, gets a
new link at the end, and returns the default.

Source: docstring, Lib/collections/__init__.py:268-271. -/
def ODSetdefaultInv : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] (K : KOps κ) (o : OD κ ν) (L : List (Nat × κ)) (key : κ) (dflt : ν),
    ODInv o L → K.hash key = .ok () →
    (key ∈ L.map (·.2) → ∃ v, D.get? o.d key = some v ∧ odSetdefault K o key dflt = .ok (v, o)) ∧
    (key ∉ L.map (·.2) → ∃ o', odSetdefault K o key dflt = .ok (dflt, o') ∧ ODInv o' (L ++ [(o.next, key)]) ∧
      D.get? o'.d key = some dflt)

theorem odSetdefaultInv_proven : ODSetdefaultInv := by
  intro κ ν _ K o L key dflt I hk
  refine ⟨fun hin => ?_, fun hin => ?_⟩
  · have hm : D.mem o.d key = true := by rw [I.mem key]; simp [hin]
    obtain ⟨v, hv⟩ : ∃ v, D.get? o.d key = some v := Option.isSome_iff_exists.1 hm
    exact ⟨v, hv, by simp [odSetdefault, dMem_ok o.d hk, hm, hv]⟩
  · have hm : D.mem o.d key = false := by rw [I.mem key]; simp [hin]
    obtain ⟨o', h1, h2, h3⟩ := odSetInv_proven κ ν K o L key dflt I hk
    rw [if_neg hin] at h2
    exact ⟨o', by simp [odSetdefault, dMem_ok o.d hk, hm, h1], h2, h3⟩

/-- **Iteration, `__reduce__`, `__repr__` and `==` follow the links.** For every instance with
list `L`: `list(od)` is the keys of `L` in order; the items `__reduce__` hands to pickle and those
`repr` prints are `L`'s keys with their values in that order; `od == other` for another
`OrderedDict` is `dict.__eq__` and then the keys in the same order (so two instances with equal
items in different orders are unequal), and for a plain dict it is `dict.__eq__` alone, order
ignored.

Source: Lib/collections/__init__.py:146-153, :278-301, :316-324; docstring of `__eq__` ('order-sensitive
... order-insensitive'). -/
def ODOrderViews : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] [DecidableEq ν] (o p : OD κ ν) (L M : List (Nat × κ)) (veq : ν → ν → Py Bool)
    (d : D κ ν) (cls : String) (rk : κ → Py String) (rv : ν → Py String),
    ODInv o L → ODInv p M →
    o.keysList = L.map (·.2) ∧
    (odReduce cls o).2 = (L.map (·.2)).filterMap (fun k => (D.get? o.d k).map (k, ·)) ∧
    (o.d ≠ [] → odRepr rk rv cls o =
      (do let s ← reprDict rk rv ((L.map (·.2)).filterMap (fun k => (D.get? o.d k).map (k, ·)))
          pure (cls ++ "(" ++ s ++ ")"))) ∧
    odEq veq o (.dict d) = dictEq veq o.d d ∧
    (dictEq veq o.d p.d = .ok true → L.map (·.2) ≠ M.map (·.2) → L.length = M.length →
      odEq veq o (.od p) = .ok false)

theorem zip_all_eq_false {l m : List κ} (h : l ≠ m) (hl : l.length = m.length) :
    (l.zip m).all (fun q => decide (q.1 = q.2)) = false := by
  induction l generalizing m with
  | nil => cases m <;> simp_all
  | cons a t ih =>
    cases m with
    | nil => simp at hl
    | cons b u =>
      simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_false_iff, decide_eq_false_iff_not]
      by_cases hab : a = b
      · subst hab
        right
        exact ih (fun e => h (by rw [e])) (by simpa using hl)
      · left; exact hab

theorem odOrderViews_proven : ODOrderViews := by
  intro κ ν _ _ o p L M veq d cls rk rv I J
  have hk := keysList_inv I
  have hk' := keysList_inv J
  refine ⟨hk, by simp [odReduce, hk], fun hne => ?_, rfl, fun he hne hlen => ?_⟩
  · have : o.d.isEmpty = false := by cases h : o.d <;> simp_all
    simp [odRepr, this, hk]
  · simp only [odEq, he, ok_bind, if_true, hk, hk']
    rw [zip_all_eq_false hne (by simpa using hlen)]
    rfl

end PyLean.CoreLibs.Coll
