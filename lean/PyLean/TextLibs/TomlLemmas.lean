import PyLean.TextLibs.TomlModel

/-! Position and slicing lemmas for the `tomllib` model. -/

namespace PyLean.TextLibs.Toml

theorem getElem?_of_drop {src : Str} {pos c : Nat} {r : Str} (h : src.drop pos = c :: r) :
    src[pos]? = some c := by
  have : (src.drop pos)[0]? = some c := by rw [h]; rfl
  simpa [List.getElem?_drop] using this

theorem getElem?_of_drop_nil {src : Str} {pos : Nat} (h : src.drop pos = []) : src[pos]? = none := by
  have : (src.drop pos)[0]? = none := by rw [h]; rfl
  simpa [List.getElem?_drop] using this

theorem drop_add_of_drop {src : Str} {pos : Nat} {a r : Str} (h : src.drop pos = a ++ r) :
    src.drop (pos + a.length) = r := by
  have : (src.drop pos).drop a.length = r := by rw [h]; simp
  simpa [List.drop_drop, Nat.add_comm] using this

theorem drop_succ_of_drop {src : Str} {pos c : Nat} {r : Str} (h : src.drop pos = c :: r) :
    src.drop (pos + 1) = r := drop_add_of_drop (a := [c]) h

theorem sl_of_drop {src : Str} {pos : Nat} {a r : Str} (h : src.drop pos = a ++ r) :
    sl src pos (pos + a.length) = a := by
  simp [sl, h]

theorem sl_self (src : Str) (pos : Nat) : sl src pos pos = [] := by simp [sl]

theorem sl_snoc {src : Str} {start pos c : Nat} {r : Str} (hs : start ≤ pos) (h : src.drop pos = c :: r) :
    sl src start (pos + 1) = sl src start pos ++ [c] := by
  have hc := getElem?_of_drop h
  unfold sl
  rw [show pos + 1 - start = (pos - start) + 1 by omega, List.take_add_one]
  congr
  rw [List.getElem?_drop, show start + (pos - start) = pos by omega, hc]
  rfl

theorem takeWhile_append_stop {p : Nat → Bool} {a r : Str} (ha : ∀ x ∈ a, p x = true)
    (hr : ∀ x, r.head? = some x → p x = false) : (a ++ r).takeWhile p = a := by
  induction a with
  | nil =>
    cases r with
    | nil => rfl
    | cons x t => simp [List.takeWhile_cons, hr x rfl]
  | cons y t ih =>
    have hy := ha y (by simp)
    simp [List.takeWhile_cons, hy, ih (fun x hx => ha x (by simp [hx]))]

theorem skipChars_of_drop {src : Str} {pos : Nat} {p : Nat → Bool} {a r : Str}
    (h : src.drop pos = a ++ r) (ha : ∀ x ∈ a, p x = true) (hr : ∀ x, r.head? = some x → p x = false) :
    skipChars src pos p = pos + a.length := by
  simp [skipChars, h, takeWhile_append_stop ha hr]

theorem skipChars_stop {src : Str} {pos : Nat} {p : Nat → Bool}
    (hr : ∀ x, (src.drop pos).head? = some x → p x = false) : skipChars src pos p = pos := by
  have := skipChars_of_drop (src := src) (pos := pos) (a := []) (r := src.drop pos) (p := p) (by simp)
    (by simp) hr
  simpa using this

theorem startsAt_of_drop {src : Str} {pos : Nat} {p r : Str} (h : src.drop pos = p ++ r) :
    startsAt src pos p = true := by
  simp [startsAt, h]

theorem firstIdx_none {p : Nat → Bool} : ∀ {s : Str}, (∀ x ∈ s, p x = false) → firstIdx p s = none
  | [], _ => rfl
  | c :: r, h => by
    have := h c (by simp)
    simp [firstIdx, this, firstIdx_none (s := r) (fun x hx => h x (by simp [hx]))]

theorem firstIdx_append {p : Nat → Bool} {a : Str} {c : Nat} {r : Str} (ha : ∀ x ∈ a, p x = false)
    (hc : p c = true) : firstIdx p (a ++ c :: r) = some a.length := by
  induction a with
  | nil => simp [firstIdx, hc]
  | cons y t ih =>
    have hy := ha y (by simp)
    simp [firstIdx, hy, ih (fun x hx => ha x (by simp [hx]))]

theorem findSub_single_none {c : Nat} : ∀ {s : Str}, c ∉ s → findSub [c] s = none
  | [], _ => rfl
  | x :: r, h => by
    have hx : x ≠ c := fun e => h (by simp [e])
    have hr : c ∉ r := fun m => h (by simp [m])
    simp [findSub, List.isPrefixOf, hx, findSub_single_none hr, Ne.symm hx]

theorem findSub_single {c : Nat} {a r : Str} (ha : c ∉ a) : findSub [c] (a ++ c :: r) = some a.length := by
  induction a with
  | nil => simp [findSub, List.isPrefixOf]
  | cons y t ih =>
    have hy : y ≠ c := fun e => ha (by simp [e])
    have ht : c ∉ t := fun m => ha (by simp [m])
    simp [findSub, List.isPrefixOf, hy, ih ht, Ne.symm hy]

end PyLean.TextLibs.Toml
