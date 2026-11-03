import PyLean.UnicodeObj.CodecsModule
import PyLean.UnicodeObj.CodecsErrBase

/-!
Properties of the codec registry: what `codecs.lookup` promises, what it raises when a search
function changes the registry under it, the generic and the text encode/decode paths, and the
error handler registry.
-/

namespace PyLean.UnicodeObj.Codecs

open PyLean PyLean.UnicodeObj

/-! ## lookup -/

/-- The answer of a search path that no search function changes: the first answer that is not
`None`, which must be a 4-tuple. -/
def firstAnswer (W : World) (v : Str) (encoding : String) : List Val → Py Val
  | [] => .error (lookupErr s!"unknown encoding: {encoding}")
  | f :: fs =>
    match (W.call f [.str v]).2 with
    | .error e => .error e
    | .ok .none => firstAnswer W v encoding fs
    | .ok res =>
      match res with
      | .tuple _ items _ =>
        if items.length = 4 then .ok res
        else .error (.typeError "codec search functions must return 4-tuples")
      | _ => .error (.typeError "codec search functions must return 4-tuples")

theorem runOps_nil (W : World) (st : Reg) : runOps W st [] = st := rfl

theorem searchLoop_pure (W : World) (v : Str) (encoding : String) (st : Reg)
    (hW : ∀ f args, (W.call f args).1 = []) :
    ∀ (k fuel i : Nat), i + k = st.path.length → k < fuel →
      searchLoop W v encoding st.path.length fuel i st = (st, firstAnswer W v encoding (st.path.drop i))
  | 0, fuel + 1, i, hk, _ => by
    simp only [searchLoop]
    rw [if_pos (by omega)]
    have : st.path.drop i = [] := by simp; omega
    rw [this]; rfl
  | k + 1, fuel + 1, i, hk, hf => by
    have hget : st.path[i]? = some (st.path[i]'(by omega)) := List.getElem?_eq_getElem (by omega)
    have hdrop : st.path.drop i = st.path[i]'(by omega) :: st.path.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by omega)]
    have h1 := hW (st.path[i]'(by omega)) [.str v]
    rcases hc : W.call (st.path[i]'(by omega)) [.str v] with ⟨ops, r⟩
    rw [hc] at h1
    simp only at h1
    subst h1
    have hc' : W.1 (st.path[i]'(by omega)) [.str v] = ([], r) := hc
    simp only [searchLoop]
    rw [if_neg (by omega), hget, hdrop]
    simp only [firstAnswer, hc', runOps_nil]
    cases r with
    | error e => rfl
    | ok res =>
      cases res with
      | none => exact searchLoop_pure W v encoding st hW k fuel (i + 1) (by omega) (by omega)
      | tuple id items exact => simp only; split <;> rfl
      | _ => rfl

theorem dictSet_lookup (d : List (Str × Val)) (k : Str) (v : Val) : (dictSet d k v).lookup k = some v := by
  unfold dictSet
  split
  · rename_i h
    induction d with
    | nil => simp at h
    | cons e es ih =>
      simp only [List.map_cons, List.lookup]
      cases hb : e.1 == k
      · have hk : (k == e.1) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq] at hb ⊢; exact fun x => hb x.symm
        simp only [Bool.false_eq_true, if_false, hk]
        apply ih
        simpa [List.any_cons, hb] using h
      · simp
  · rename_i h
    induction d with
    | nil => simp [List.lookup]
    | cons e es ih =>
      have hb : (e.1 == k) = false := by
        cases hx : e.1 == k
        · rfl
        · exact absurd (by simp [List.any_cons, hx]) h
      have hk : (k == e.1) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq] at hb ⊢; exact fun x => hb x.symm
      simp only [List.cons_append, List.lookup, hk]
      apply ih
      intro x; apply h; simp [List.any_cons, x]

/-- **codecs.lookup does what its documentation says** (codecs.rst, `lookup`): "This function
first normalizes the encoding: all ASCII letters are converted to lower case, spaces are
replaced with hyphens. Then encoding is looked up in the registry's cache. If not found, the
list of registered search functions is scanned. If no CodecInfo object is found, a LookupError
is raised. Otherwise, the CodecInfo object is stored in the cache and returned to the caller."
For every registry and every name: a cached name is answered from the cache without calling
anything; when no search function changes the registry, the answer is the first search
function's that is not `None` (a 4-tuple, or `TypeError`), and the `LookupError` names the
encoding as given; and after any successful lookup, every name with the same normalization is
answered from the cache with the same object. -/
def LookupDoc : Prop :=
  ∀ (W : World) (st : Reg) (enc : List Nat) (v : Str), normalizestring enc = .ok v →
    (∀ r, st.cache.lookup v = some r → pyCodecLookup W st enc = (st, .ok r)) ∧
    (st.cache.lookup v = none → st.path ≠ [] → (∀ f args, (W.call f args).1 = []) →
      pyCodecLookup W st enc =
        match firstAnswer W v (toLeanString ((utf8Decode enc .strict).toOption.getD [])) st.path with
        | .ok r => ({ st with cache := dictSet st.cache v r }, .ok r)
        | .error e => (st, .error e)) ∧
    (∀ st' r, pyCodecLookup W st enc = (st', .ok r) →
      ∀ enc', normalizestring enc' = .ok v → pyCodecLookup W st' enc' = (st', .ok r))

theorem lookupDoc_proven : LookupDoc := by
  intro W st enc v hv
  refine ⟨fun r hr => by simp [pyCodecLookup, hv, hr], fun hmiss hne hW => ?_, fun st' r hl enc' hv' => ?_⟩
  · simp only [pyCodecLookup, hv, hmiss]
    have hlen : st.path.length ≠ 0 := by simpa using hne
    simp only [hlen, if_false]
    rw [searchLoop_pure W v _ st hW st.path.length (st.path.length + 1) 0 (by omega) (by omega)]
    simp only [List.drop_zero]
    cases firstAnswer W v _ st.path <;> rfl
  · simp only [pyCodecLookup, hv] at hl
    cases hc : st.cache.lookup v with
    | some r0 =>
      rw [hc] at hl
      simp only [Prod.mk.injEq, Except.ok.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      simp [pyCodecLookup, hv', hc]
    | none =>
      rw [hc] at hl
      simp only at hl
      by_cases hl0 : st.path.length = 0
      · simp [hl0] at hl
      · simp only [hl0, if_false] at hl
        generalize searchLoop W v (toLeanString ((utf8Decode enc .strict).toOption.getD []))
          st.path.length (st.path.length + 1) 0 st = res at hl
        rcases res with ⟨st1, r1⟩
        cases r1 with
        | error e => simp at hl
        | ok res =>
          simp only [Prod.mk.injEq, Except.ok.injEq] at hl
          obtain ⟨rfl, rfl⟩ := hl
          simp [pyCodecLookup, hv', dictSet_lookup]

/-! ## What lookup raises -/

theorem searchLoop_err (W : World) (v : Str) (encoding : String) (len : Nat) :
    ∀ (fuel i : Nat) (st st' : Reg) (x : PyExc), len - i < fuel →
      searchLoop W v encoding len fuel i st = (st', .error x) →
      x = lookupErr s!"unknown encoding: {encoding}" ∨ x = .indexError "list index out of range" ∨
      x = .typeError "codec search functions must return 4-tuples" ∨
      ∃ f args, (W.call f args).2 = .error x
  | 0, _, _, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | fuel + 1, i, st, st', x, hf, h => by
    simp only [searchLoop] at h
    split at h
    · simp only [Prod.mk.injEq, Except.error.injEq] at h; left; exact h.2.symm
    · split at h
      · simp only [Prod.mk.injEq, Except.error.injEq] at h; right; left; exact h.2.symm
      · rename_i func _
        rcases hc : W.call func [.str v] with ⟨ops, r⟩
        have hc' : W.1 func [.str v] = (ops, r) := hc
        simp only [hc'] at h
        cases r with
        | error e =>
          simp only [Prod.mk.injEq, Except.error.injEq] at h
          right; right; right; exact ⟨func, [.str v], by rw [hc, ← h.2]⟩
        | ok res =>
          cases res with
          | none => exact searchLoop_err W v encoding len fuel (i + 1) _ st' x (by omega) h
          | tuple id items exact =>
            simp only at h
            split at h
            · cases h
            · simp only [Prod.mk.injEq, Except.error.injEq] at h; right; right; left; exact h.2.symm
          | _ => simp only [Prod.mk.injEq, Except.error.injEq] at h; right; right; left; exact h.2.symm

/-- **codecs.lookup raises a LookupError when it finds no codec.** codecs.rst (`lookup`): "If no
CodecInfo object is found, a LookupError is raised." For every registry, name and search
functions (which may change the registry while it is being scanned), a failed lookup raises an
exception whose class is below `LookupError` (the exceptions here are the builtin `LookupError`
and `IndexError`, whose MROs are fixed), the `TypeError`
for a search function's bad answer, or what a search function raised. When a search function
unregisters search functions during the scan, the saved length (codecs.c:165) outlives the list
and the error is the `IndexError` of `PyList_GetItemRef`, a subclass of `LookupError`
(`unregWorld_lookup`). -/
def LookupRaisesLookupError : Prop :=
  ∀ (H : Hier) (W : World) (st : Reg) (enc : List Nat) (v : Str) (st' : Reg) (x : PyExc),
    HierOk H → normalizestring enc = .ok v → pyCodecLookup W st enc = (st', .error x) →
    H.sub x.className "LookupError" = true ∨ x = .typeError "codec search functions must return 4-tuples" ∨
      ∃ f args, (W.call f args).2 = .error x

theorem lookupRaisesLookupError_proven : LookupRaisesLookupError := by
  intro H W st enc v st' x hH hv hl
  have hL : H.sub "LookupError" "LookupError" = true := by
    rw [hH.builtin (by decide)]; decide
  have hI : H.sub "IndexError" "LookupError" = true := by
    rw [hH.builtin (by decide)]; decide
  simp only [pyCodecLookup, hv] at hl
  split at hl
  · cases hl
  · split at hl
    · simp only [Prod.mk.injEq, Except.error.injEq] at hl
      left; rw [← hl.2]; exact hL
    · generalize hs : searchLoop W v (toLeanString ((utf8Decode enc .strict).toOption.getD []))
        st.path.length (st.path.length + 1) 0 st = res at hl
      rcases res with ⟨st1, r1⟩
      cases r1 with
      | ok res => simp at hl
      | error e =>
        simp only [Prod.mk.injEq, Except.error.injEq] at hl
        obtain ⟨_, rfl⟩ := hl
        rcases searchLoop_err W v _ st.path.length (st.path.length + 1) 0 st st1 e (by omega) hs with
          h | h | h | h
        · left; rw [h]; exact hL
        · left; rw [h]; exact hI
        · right; left; exact h
        · right; right; exact h

/-- Two search functions; the first unregisters both and finds nothing. -/
def unregWorld : World where
  call f _ :=
    match f with
    | .obj 1 _ => ([.unregister (.obj 1 "function"), .unregister (.obj 2 "function")], .ok .none)
    | _ => ([], .ok .none)
  getattr _ _ := .ok none
  truth _ := .ok true
  callable _ := true

def unregReg : Reg := { path := [.obj 1 "function", .obj 2 "function"], cache := [], errors := [] }

/-- The scan reads past the shortened list: `IndexError`. -/
theorem unregWorld_lookup :
    (pyCodecLookup unregWorld unregReg (lit "x")).2 = .error (.indexError "list index out of range") := by
  rfl

end PyLean.UnicodeObj.Codecs
