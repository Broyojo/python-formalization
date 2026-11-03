import PyLean.TextLibs.PlistRoundTrip

namespace PyLean.TextLibs.Plist

open PyLean PyLean.TextLibs

/-- What the round trip needs of the value written: no datetimes (not covered), floats are 64-bit
patterns, `str`s hold code points, and the `str` keys of a dict are pairwise different (the type
invariants of `float`, `str` and `dict`). -/
def HeapWf (H : WHeap) : Prop :=
  (∀ c us off, H.getD c .none ≠ .date us off) ∧
  (∀ c bits, H.getD c .none = .float bits → bits < 2 ^ 64) ∧
  (∀ c s, H.getD c .none = .str s → UnicodeObj.Str.Valid s) ∧
  (∀ c items, H.getD c .none = .dict items → KeysDistinct H items) ∧
  (∀ c items, H.getD c .none = .fdict items → KeysDistinct H items)

/-- The object `o` read back matches the object `w` written, when the elements read back match
the elements written by `R` (a list for a list or tuple; for a dict, the items `_write_object`
keeps, in its order). -/
def Match (H : WHeap) (cfg : WCfg) (R : Nat → Nat → Prop) (o : Obj) (w : WObj) : Prop :=
  match w, o with
  | .none, .none => True
  | .bool a, .bool b => a = b
  | .int a, .int b => a = b
  | .float a, .real b => b = a ∨ Binary64.F64.eq (Binary64.F64.ofBits a) (Binary64.F64.ofBits b) = true
  | .str a, .str b => a = b
  | .bytes a, .data b => a = b
  | .bytearray a, .data b => a = b
  | .uid a, .uid b => a = b
  | .list xs, .arr rs => Forall2 (fun x r => R r x) xs rs
  | .tuple xs, .arr rs => Forall2 (fun x r => R r x) xs rs
  | .dict items, .dict ps => ∃ kept, writtenItems H cfg items = .ok kept ∧
      Forall2 (fun q p => R p.1 q.1 ∧ R p.2 q.2) kept ps
  | .fdict items, .dict ps => ∃ kept, writtenItems H cfg items = .ok kept ∧
      Forall2 (fun q p => R p.1 q.1 ∧ R p.2 q.2) kept ps
  | _, _ => False

/-- The loaded object graph is the written one: a relation between loaded slots and written
cells relates the roots, each related pair matches, and identity is kept: two related
containers (or other objects tracked by `id()`) are the same loaded object exactly when they are
the same written object (shared lists come back shared, equal but distinct ones distinct, and a list
that contains itself contains its loaded self). -/
def Bisim (H : WHeap) (cfg : WCfg) (root : Nat) (res : Res) : Prop :=
  ∃ R : Nat → Nat → Prop, R res.root root ∧
    (∀ i c, R i c → ∃ o, res.objs[i]? = some (some o) ∧ Match H cfg R o (H.getD c .none)) ∧
    (∀ i c i' c', R i c → R i' c' → isScalar H c = false → isScalar H c' = false →
      (i = i' ↔ objId H c = objId H c'))

theorem objId_cell (H : WHeap) (c d : Nat) (h : objId H c = .cell d) : d = c := by
  unfold objId at h; split at h <;> (try split at h) <;> simp_all

theorem objId_none (H : WHeap) (c : Nat) (h : objId H c = .noneObj) : H.getD c .none = .none := by
  unfold objId at h; split at h
  · assumption
  · cases h
  · cases h

theorem objId_tuple (H : WHeap) (c : Nat) (h : objId H c = .emptyTuple) : H.getD c .none = .tuple [] := by
  unfold objId at h; split at h
  · cases h
  · assumption
  · cases h

theorem forall2_mono {α β : Type} {P Q : α → β → Prop} (h : ∀ a b, P a b → Q a b) :
    ∀ {l : List α} {m : List β}, Forall2 P l m → Forall2 Q l m
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h1 t => .cons (h _ _ h1) (forall2_mono h t)

theorem forall2_mem {α β : Type} {P : α → β → Prop} :
    ∀ {l : List α} {m : List β}, Forall2 P l m → ∀ b ∈ m, ∃ a ∈ l, P a b
  | [], [], .nil, _, hb => by simp at hb
  | a :: l, b' :: m, .cons h1 t, b, hb => by
    simp at hb
    rcases hb with rfl | hb
    · exact ⟨a, by simp, h1⟩
    · obtain ⟨x, hx, hp⟩ := forall2_mem t b hb
      exact ⟨x, by simp [hx], hp⟩

theorem forall2_map {α β γ : Type} {P : α → β → Prop} (f : β → γ) (g : α → γ)
    (h : ∀ a b, P a b → f b = g a) : ∀ {l : List α} {m : List β}, Forall2 P l m → m.map f = l.map g
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h1 t => by simp [h _ _ h1, forall2_map f g h t]

end PyLean.TextLibs.Plist
