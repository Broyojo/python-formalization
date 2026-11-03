import PyLean.Datetime.ZoneCacheIdProps

/-!
# Keys equal by value: the fallible cache mirrors agree (CPython 3.15.2)

Keys whose `==` compares a value `v k` (the text of a `str`) and never raises, and whose
`hash()` is a function of that value: separate `str` objects with equal text are equal keys.
C's strong cache keeps the key object of the first call, Python's `OrderedDict` the latest
(`pop` then `__setitem__`), so the twins' entries differ as objects; they agree by value and
by the instance they hold. A state of either twin is a state of `ZoneCache.lean` over values,
with `ι x` the current instance for value `x`.
-/

namespace PyLean.Datetime.Zone

open PyLean

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section equiv

variable {K V : Type} [DecidableEq K] [DecidableEq V]

def vals (v : K → V) (l : List (K × Inst K)) : List V := l.map fun e => v e.1

/-- Every entry holds the current instance for its key's value. -/
def Good (v : K → V) (ι : V → Option (Inst K)) (l : List (K × Inst K)) : Prop :=
  ∀ e ∈ l, ι (v e.1) = some e.2

def updO (ι : V → Option (Inst K)) (x : V) (i : Inst K) : V → Option (Inst K) :=
  fun y => if y = x then some i else ι y

theorem find_v_some (v : K → V) (l : List (K × Inst K)) (x : V) (e : K × Inst K)
    (h : l.find? (fun e => decide (v e.1 = x)) = some e) : e ∈ l ∧ v e.1 = x := by
  refine ⟨List.mem_of_find?_eq_some h, ?_⟩
  have := List.find?_some h
  simpa using this

theorem find_v_none (v : K → V) (l : List (K × Inst K)) (x : V) :
    l.find? (fun e => decide (v e.1 = x)) = none ↔ x ∉ vals v l := by
  rw [List.find?_eq_none]
  simp only [vals, List.mem_map, decide_eq_true_eq, not_exists, not_and]

theorem erase_find_v (v : K → V) (x : V) : ∀ (l : List (K × Inst K)) (e : K × Inst K),
    l.find? (fun e => decide (v e.1 = x)) = some e → vals v (l.erase e) = (vals v l).erase x := by
  intro l
  induction l with
  | nil => intro e h; simp at h
  | cons a l ih =>
    intro e h
    by_cases ha : v a.1 = x
    · have : a = e := by simpa [List.find?_cons, ha] using h
      subst this
      simp [vals, ha]
    · have h' : l.find? (fun e => decide (v e.1 = x)) = some e := by
        simpa [List.find?_cons, ha] using h
      have hne : a ≠ e := fun hae => ha (hae ▸ (find_v_some v l x e h').2)
      have hb : ¬ (a == e) = true := by simp [hne]
      have hb2 : ¬ (v a.1 == x) = true := by simp [ha]
      simp only [List.erase_cons, hb, Bool.false_eq_true, ite_false, vals, List.map_cons, hb2]
      exact congrArg _ (ih e h')

/-- Removing the entry a lookup finds (or nothing). -/
def remv (v : K → V) (l : List (K × Inst K)) (x : V) : List (K × Inst K) :=
  match l.find? (fun e => decide (v e.1 = x)) with
  | some e => l.erase e
  | none => l

theorem remv_spec (v : K → V) (l : List (K × Inst K)) (x : V) :
    vals v (remv v l x) = (vals v l).erase x ∧ ∀ e ∈ remv v l x, e ∈ l := by
  unfold remv
  split
  · rename_i e he
    exact ⟨erase_find_v v x l e he, fun _ h => List.mem_of_mem_erase h⟩
  · rename_i he
    have : x ∉ vals v l := (find_v_none v l x).mp he
    exact ⟨(List.erase_of_not_mem this).symm, fun _ h => h⟩

section ops
variable (o : KeyOps K) (v : K → V) (hv : V → Int)
  (hE : ∀ a b, o.eq a b = .ok (decide (v a = v b))) (hH : ∀ a, o.hash a = .ok (hv (v a)))
include hE hH

theorem probe_v (key : K) : ∀ l : List (K × Inst K),
    dictProbe o key (hv (v key)) l = .ok (l.find? (fun e => decide (v e.1 = v key))) := by
  intro l
  induction l with
  | nil => rfl
  | cons e l ih =>
    by_cases h1 : e.1 = key
    · have : v e.1 = v key := by rw [h1]
      simp [dictProbe, h1, List.find?_cons]
    · by_cases h2 : v e.1 = v key
      · have hh : hashIs o e.1 (hv (v key)) = true := by simp [hashIs, hH, h2]
        simp [dictProbe, h1, hh, hE, h2, List.find?_cons]
      · have hstep : dictProbe o key (hv (v key)) (e :: l) = dictProbe o key (hv (v key)) l := by
          simp only [dictProbe, h1, ite_false, hE, h2, decide_false]
          split <;> rfl
        rw [hstep, ih]
        simp [List.find?_cons, h2]

theorem dictFind_v (key : K) (l : List (K × Inst K)) :
    dictFind o l key = .ok (l.find? (fun e => decide (v e.1 = v key))) := by
  simp only [dictFind, hH]
  exact probe_v o v hv hE hH key l

theorem findStrongC_v (key : K) : ∀ l : List (K × Inst K),
    findStrongC o key l = .ok (l.find? (fun e => decide (v e.1 = v key))) := by
  intro l
  induction l with
  | nil => rfl
  | cons e l ih =>
    by_cases h1 : key = e.1
    · have : v e.1 = v key := by rw [h1]
      simp [findStrongC, richEqBool, h1, List.find?_cons]
    · by_cases h2 : v e.1 = v key
      · have : richEqBool o key e.1 = .ok true := by
          simp [richEqBool, h1, hE, h2]
        simp [findStrongC, this, List.find?_cons, h2]
      · have : richEqBool o key e.1 = .ok false := by
          have h2' : ¬ v key = v e.1 := fun x => h2 x.symm
          simp [richEqBool, h1, hE, h2']
        simp only [findStrongC, this]
        rw [ih]
        simp [List.find?_cons, h2]

theorem wvdGet_v (key : K) (l : List (K × Inst K)) :
    wvdGet o l key = .ok ((l.find? (fun e => decide (v e.1 = v key))).map Prod.snd) := by
  simp only [wvdGet, dictFind_v o v hv hE hH]

theorem dictPop_v (key : K) (l : List (K × Inst K)) :
    dictPop o l key =
      .ok ((l.find? (fun e => decide (v e.1 = v key))).map Prod.snd, remv v l (v key)) := by
  rw [dictPop, dictFind_v o v hv hE hH]
  unfold remv
  cases l.find? (fun e => decide (v e.1 = v key)) <;> rfl

theorem wvdPop_v (key : K) (l : List (K × Inst K)) : wvdPop o l key = .ok (remv v l (v key)) := by
  cases l with
  | nil => rfl
  | cons a l => simp only [wvdPop, dictPop_v o v hv hE hH]

theorem dictSet_none (key : K) (i : Inst K) (l : List (K × Inst K)) (hn : v key ∉ vals v l) :
    dictSet o l key i = .ok (l ++ [(key, i)]) := by
  simp only [dictSet, dictFind_v o v hv hE hH, (find_v_none v l (v key)).mpr hn]

theorem wvdSetdefault_none (key : K) (i : Inst K) (l : List (K × Inst K)) (hn : v key ∉ vals v l) :
    wvdSetdefault o l key i = .ok (i, l ++ [(key, i)]) := by
  simp only [wvdSetdefault, dictFind_v o v hv hE hH, (find_v_none v l (v key)).mpr hn,
    dictSet_none o v hv hE hH key i l hn]

/-- A base-class state with no foreign objects. -/
def mkZ (s W : List (K × Inst K)) (n : Nat) : ZCls K := ⟨true, s, some W, [], n, []⟩

def trim8 {α : Type} (l : List α) : List α := if l.length > 8 then l.tail else l

theorem py_get_hit (ps W : List (K × Inst K)) (n : Nat) (k : K) (w : K × Inst K)
    (hw : W.find? (fun e => decide (v e.1 = v k)) = some w)
    (hval : ∀ e, ps.find? (fun e => decide (v e.1 = v k)) = some e → e.2 = w.2)
    (hn : v k ∉ vals v (remv v ps (v k))) :
    stepErrPy o (mkZ ps W n) (.get k) = (mkZ (trim8 (remv v ps (v k) ++ [(k, w.2)])) W n, .ok (some w.2)) := by
  have hv' : ((ps.find? (fun e => decide (v e.1 = v k))).map Prod.snd).getD w.2 = w.2 := by
    cases h : ps.find? (fun e => decide (v e.1 = v k)) with
    | none => rfl
    | some e => simp [hval e h]
  simp only [stepErrPy, newErrPy, mkZ, getWeakPy, Option.getD_some, wvdGet_v o v hv hE hH, hw,
    Option.map_some, setWeakPy, dictPop_v o v hv hE hH, hv', dictSet_none o v hv hE hH k _ _ hn,
    trim8, Except.map]

theorem py_get_fail (ps W : List (K × Inst K)) (n : Nat) (k : K)
    (hw : W.find? (fun e => decide (v e.1 = v k)) = none) (hl : o.loads k = false) :
    stepErrPy o (mkZ ps W n) (.get k) = (mkZ ps W n, .error notFound) := by
  simp only [stepErrPy, newErrPy, mkZ, getWeakPy, Option.getD_some, wvdGet_v o v hv hE hH, hw,
    Option.map_none, hl, Bool.not_false, ite_true, Except.map]

theorem py_get_new (ps W : List (K × Inst K)) (n : Nat) (k : K)
    (hw : W.find? (fun e => decide (v e.1 = v k)) = none) (hl : o.loads k = true)
    (hp : v k ∉ vals v ps) :
    stepErrPy o (mkZ ps W n) (.get k) =
      (mkZ (trim8 (ps ++ [(k, (k, n))])) (W ++ [(k, (k, n))]) (n + 1), .ok (some (k, n))) := by
  have hwn : v k ∉ vals v W := (find_v_none v W (v k)).mp hw
  have hpn := (find_v_none v ps (v k)).mpr hp
  have hr : remv v ps (v k) = ps := by simp [remv, hpn]
  simp only [stepErrPy, newErrPy, mkZ, getWeakPy, Option.getD_some, wvdGet_v o v hv hE hH, hw,
    Option.map_none, hl, Bool.not_true, Bool.false_eq_true, ite_false,
    wvdSetdefault_none o v hv hE hH k _ W hwn, Except.map, setWeakPy, dictPop_v o v hv hE hH, hpn,
    hr, Option.getD_none, dictSet_none o v hv hE hH k _ _ hp, trim8]

theorem c_get_strong (cs W : List (K × Inst K)) (n : Nat) (k : K) (e : K × Inst K)
    (he : cs.find? (fun e => decide (v e.1 = v k)) = some e) :
    stepErrC o (mkZ cs W n) (.get k) = (mkZ (e :: cs.erase e) W n, .ok (some e.2)) := by
  simp only [stepErrC, newErrC, zoneFromStrongC, mkZ, Bool.not_true, Bool.false_eq_true, ite_false,
    findStrongC_v o v hv hE hH, he, Except.map]

theorem c_get_weak (cs W : List (K × Inst K)) (n : Nat) (k : K) (w : K × Inst K)
    (hc : cs.find? (fun e => decide (v e.1 = v k)) = none)
    (hw : W.find? (fun e => decide (v e.1 = v k)) = some w) :
    stepErrC o (mkZ cs W n) (.get k) = (mkZ (((k, w.2) :: cs).take 8) W n, .ok (some w.2)) := by
  simp only [stepErrC, newErrC, zoneFromStrongC, mkZ, Bool.not_true, Bool.false_eq_true, ite_false,
    findStrongC_v o v hv hE hH, hc, getWeakC, ite_true, Option.getD_some, wvdGet_v o v hv hE hH, hw,
    Option.map_some, List.not_mem_nil, updateStrongC, Except.map]

theorem c_get_fail (cs W : List (K × Inst K)) (n : Nat) (k : K)
    (hc : cs.find? (fun e => decide (v e.1 = v k)) = none)
    (hw : W.find? (fun e => decide (v e.1 = v k)) = none) (hl : o.loads k = false) :
    stepErrC o (mkZ cs W n) (.get k) = (mkZ cs W n, .error notFound) := by
  simp only [stepErrC, newErrC, zoneFromStrongC, mkZ, Bool.not_true, Bool.false_eq_true, ite_false,
    findStrongC_v o v hv hE hH, hc, getWeakC, ite_true, Option.getD_some, wvdGet_v o v hv hE hH, hw,
    Option.map_none, hl, Bool.not_false, Except.map]

theorem c_get_new (cs W : List (K × Inst K)) (n : Nat) (k : K)
    (hc : cs.find? (fun e => decide (v e.1 = v k)) = none)
    (hw : W.find? (fun e => decide (v e.1 = v k)) = none) (hl : o.loads k = true) :
    stepErrC o (mkZ cs W n) (.get k) =
      (mkZ (((k, (k, n)) :: cs).take 8) (W ++ [(k, (k, n))]) (n + 1), .ok (some (k, n))) := by
  have hwn : v k ∉ vals v W := (find_v_none v W (v k)).mp hw
  simp only [stepErrC, newErrC, zoneFromStrongC, mkZ, Bool.not_true, Bool.false_eq_true, ite_false,
    findStrongC_v o v hv hE hH, hc, getWeakC, ite_true, Option.getD_some, wvdGet_v o v hv hE hH, hw,
    Option.map_none, hl, wvdSetdefault_none o v hv hE hH k _ W hwn, List.not_mem_nil,
    updateStrongC, Except.map]

theorem c_clearKeys_cons (cs W : List (K × Inst K)) (n : Nat) (cw : Option (List (K × Inst K)))
    (err : Option PyExc) (k : K) (ks : List K) :
    clearKeysC o W err ⟨true, cs, cw, [], n, []⟩ (k :: ks) =
      clearKeysC o (remv v W (v k)) err ⟨true, remv v cs (v k), cw, [], n, []⟩ ks := by
  have hej : ejectC o ⟨true, cs, cw, [], n, []⟩ k = .ok (remv v cs (v k)) := by
    simp only [ejectC, Bool.not_true, Bool.false_eq_true, ite_false, findStrongC_v o v hv hE hH]
    unfold remv
    cases cs.find? (fun e => decide (v e.1 = v k)) <;> rfl
  simp only [clearKeysC, hej, wvdPop_v o v hv hE hH]

theorem py_clearKeys_cons (ps W : List (K × Inst K)) (n : Nat) (err : Option PyExc) (k : K)
    (ks : List K) :
    clearKeysPy o err (mkZ ps W n) (k :: ks) =
      clearKeysPy o err (mkZ (remv v ps (v k)) (remv v W (v k)) n) ks := by
  simp only [clearKeysPy, mkZ, getWeakPy, Option.getD_some, wvdPop_v o v hv hE hH, setWeakPy,
    dictPop_v o v hv hE hH]

end ops

theorem good_sub (v : K → V) (ι : V → Option (Inst K)) (l l' : List (K × Inst K)) (h : Good v ι l)
    (hs : ∀ e ∈ l', e ∈ l) : Good v ι l' := fun e he => h e (hs e he)

theorem good_find (v : K → V) (ι : V → Option (Inst K)) (l : List (K × Inst K)) (x : V)
    (e : K × Inst K) (h : Good v ι l) (hf : l.find? (fun e => decide (v e.1 = x)) = some e) :
    ι x = some e.2 := by
  obtain ⟨hm, hx⟩ := find_v_some v l x e hf
  rw [← hx]; exact h e hm

theorem mem_vals (v : K → V) (l : List (K × Inst K)) (x : V) :
    x ∈ vals v l ↔ ∃ e ∈ l, v e.1 = x := by simp [vals]

theorem find_of_mem (v : K → V) (l : List (K × Inst K)) (x : V) (h : x ∈ vals v l) :
    ∃ e, l.find? (fun e => decide (v e.1 = x)) = some e := by
  cases hf : l.find? (fun e => decide (v e.1 = x)) with
  | none => exact absurd h ((find_v_none v l x).mp hf)
  | some e => exact ⟨e, rfl⟩

theorem vals_trim8 (v : K → V) (l : List (K × Inst K)) : vals v (trim8 l) = trim8 (vals v l) := by
  unfold trim8 vals
  simp only [List.length_map]
  split
  · cases l <;> rfl
  · rfl

theorem vals_append (v : K → V) (l l' : List (K × Inst K)) :
    vals v (l ++ l') = vals v l ++ vals v l' := by simp [vals]

theorem trim8_mem {α : Type} (l : List α) (a : α) (h : a ∈ trim8 l) : a ∈ l := by
  unfold trim8 at h
  split at h
  · exact List.mem_of_mem_tail h
  · exact h

theorem eraseP_inst (v : K → V) (i : Inst K) (x : V) : ∀ W : List (K × Inst K),
    (∀ e ∈ W, (e.2 = i ↔ v e.1 = x)) →
    vals v (W.eraseP (fun e => decide (e.2 = i))) = (vals v W).erase x := by
  intro W
  induction W with
  | nil => intro _; rfl
  | cons a W ih =>
    intro h
    by_cases ha : a.2 = i
    · have hx : v a.1 = x := (h a List.mem_cons_self).mp ha
      simp [List.eraseP_cons, ha, vals, hx]
    · have hx : ¬ v a.1 = x := fun e => ha ((h a List.mem_cons_self).mpr e)
      have hb : ¬ (v a.1 == x) = true := by simp [hx]
      simp only [List.eraseP_cons, ha, decide_false, Bool.cond_false, vals, List.map_cons,
        List.erase_cons, hb, Bool.false_eq_true, ite_false]
      exact congrArg _ (ih fun e he => h e (List.mem_cons_of_mem _ he))

theorem cinv_next (L : V → Bool) (sp sc : CacheSt V) (h : CInv sp sc) (op : CacheOp V) :
    CInv ((stepPy L sp op).getD sp) ((stepC L sc op).getD sc) ∧
      (stepPy L sp op).isSome = (stepC L sc op).isSome := by
  have hs := step_inv L sp sc h op
  cases hp : stepPy L sp op <;> cases hc : stepC L sc op <;> rw [hp, hc] at hs
  · exact ⟨h, rfl⟩
  · exact hs.elim
  · exact hs.elim
  · exact ⟨hs, rfl⟩

/-- The two twins' base-class states, by value. -/
structure SimE (v : K → V) (ι : V → Option (Inst K)) (sp sc : CacheSt V)
    (W ps cs : List (K × Inst K)) (n : Nat) : Prop where
  inv : CInv sp sc
  wv : vals v W = sp.weak
  wg : Good v ι W
  pv : vals v ps = sp.strong
  pg : Good v ι ps
  cv : vals v cs = sc.strong
  cg : Good v ι cs
  inj : ∀ a ∈ sp.weak, ∀ b ∈ sp.weak, ι a = ι b → a = b
  fresh : ∀ a ∈ sp.weak, ∀ i, ι a = some i → i.2 < n

def SimStep (o : KeyOps K) (v : K → V) (ι : V → Option (Inst K)) (sp sc : CacheSt V)
    (W ps cs : List (K × Inst K)) (n : Nat) (op : ZOp K) : Prop :=
  (stepErrC o (mkZ cs W n) op).2 = (stepErrPy o (mkZ ps W n) op).2 ∧
  ∃ ι' sp' sc' W' ps' cs' n', (stepErrPy o (mkZ ps W n) op).1 = mkZ ps' W' n' ∧
    (stepErrC o (mkZ cs W n) op).1 = mkZ cs' W' n' ∧ SimE v ι' sp' sc' W' ps' cs' n'

section sim
variable (o : KeyOps K) (v : K → V) (hv : V → Int)
  (hE : ∀ a b, o.eq a b = .ok (decide (v a = v b))) (hH : ∀ a, o.hash a = .ok (hv (v a)))
include hE hH

theorem sim_get (ι : V → Option (Inst K)) (sp sc : CacheSt V) (W ps cs : List (K × Inst K))
    (n : Nat) (h : SimE v ι sp sc W ps cs n) (k : K) : SimStep o v ι sp sc W ps cs n (.get k) := by
  unfold SimStep
  let L : V → Bool := fun _ => o.loads k
  have hmc : ∀ y, y ∈ sc.strong ↔ y ∈ sp.strong := fun y => by rw [h.inv.strong, List.mem_reverse]
  have hnd : (vals v ps).Nodup := by rw [h.pv]; exact h.inv.nodup
  obtain ⟨hci, -⟩ := cinv_next L sp sc h.inv (.get (v k))
  cases hw : W.find? (fun e => decide (v e.1 = v k)) with
  | some w =>
    have hxw : v k ∈ sp.weak := by rw [← h.wv]; exact (mem_vals v W _).mpr ⟨w, (find_v_some v W _ w hw)⟩
    have hiw := good_find v ι W (v k) w h.wg hw
    have hval : ∀ e, ps.find? (fun e => decide (v e.1 = v k)) = some e → e.2 = w.2 := fun e he => by
      have := good_find v ι ps (v k) e h.pg he; rw [hiw] at this; exact (Option.some.inj this).symm
    have hrn : v k ∉ vals v (remv v ps (v k)) := by
      rw [(remv_spec v ps (v k)).1]; exact hnd.not_mem_erase
    have hpy := py_get_hit o v hv hE hH ps W n k w hw hval hrn
    have hstp : stepPy L sp (.get (v k)) =
        some ⟨trim8 (sp.strong.erase (v k) ++ [v k]), sp.weak⟩ := by
      simp [stepPy, newPy, hxw, trim8]
    rw [hstp] at hci
    cases hc : cs.find? (fun e => decide (v e.1 = v k)) with
    | some e =>
      have hie := good_find v ι cs (v k) e h.cg hc
      have he2 : e.2 = w.2 := by rw [hiw] at hie; exact (Option.some.inj hie).symm
      have hxs : v k ∈ sc.strong := by
        rw [← h.cv]; exact (mem_vals v cs _).mpr ⟨e, (find_v_some v cs _ e hc)⟩
      have hstc : stepC L sc (.get (v k)) = some ⟨v k :: sc.strong.erase (v k), sc.weak⟩ := by
        simp [stepC, newC, hxs]
      rw [hstc] at hci
      simp only [Option.getD_some] at hci
      rw [hpy, c_get_strong o v hv hE hH cs W n k e hc]
      refine ⟨by simp [he2], ι, _, _, W, _, _, n, rfl, rfl, ⟨hci, h.wv, h.wg, ?_, ?_, ?_, ?_, h.inj, h.fresh⟩⟩
      · simp only [vals_trim8, vals_append, (remv_spec v ps (v k)).1, h.pv]; rfl
      · intro x hx
        rcases List.mem_append.mp (trim8_mem _ x hx) with hx | hx
        · exact h.pg x ((remv_spec v ps (v k)).2 x hx)
        · simp at hx; subst hx; exact hiw
      · have h1 := erase_find_v v (v k) cs e hc
        have h2 := (find_v_some v cs _ e hc).2
        have hcv := h.cv
        simp only [vals] at h1 hcv ⊢
        rw [List.map_cons, h1, h2, hcv]
      · intro x hx
        rcases List.mem_cons.mp hx with hx | hx
        · rw [hx]; exact h.cg _ (find_v_some v cs _ e hc).1
        · exact h.cg x (List.mem_of_mem_erase hx)
    | none =>
      have hxs : v k ∉ sc.strong := by rw [← h.cv]; exact (find_v_none v cs _).mp hc
      have hstc : stepC L sc (.get (v k)) = some ⟨(v k :: sc.strong).take 8, sc.weak⟩ := by
        have hxw' : v k ∈ sc.weak := by rw [h.inv.weak]; exact hxw
        simp [stepC, newC, hxs, hxw']
      rw [hstc] at hci
      simp only [Option.getD_some] at hci
      rw [hpy, c_get_weak o v hv hE hH cs W n k w hc hw]
      refine ⟨rfl, ι, _, _, W, _, _, n, rfl, rfl, ⟨hci, h.wv, h.wg, ?_, ?_, ?_, ?_, h.inj, h.fresh⟩⟩
      · simp only [vals_trim8, vals_append, (remv_spec v ps (v k)).1, h.pv]; rfl
      · intro x hx
        rcases List.mem_append.mp (trim8_mem _ x hx) with hx | hx
        · exact h.pg x ((remv_spec v ps (v k)).2 x hx)
        · simp at hx; subst hx; exact hiw
      · have hcv := h.cv
        simp only [vals] at hcv ⊢
        rw [List.map_take, List.map_cons, hcv]
      · intro x hx
        rcases List.mem_cons.mp (List.mem_of_mem_take hx) with hx | hx
        · subst hx; exact hiw
        · exact h.cg x hx
  | none =>
    have hxw : v k ∉ sp.weak := by rw [← h.wv]; exact (find_v_none v W _).mp hw
    have hxp : v k ∉ sp.strong := fun hm => hxw (h.inv.sub _ hm)
    have hxs : v k ∉ sc.strong := fun hm => hxp ((hmc _).mp hm)
    have hp : v k ∉ vals v ps := by rw [h.pv]; exact hxp
    have hc : cs.find? (fun e => decide (v e.1 = v k)) = none :=
      (find_v_none v cs _).mpr (by rw [h.cv]; exact hxs)
    cases hl : o.loads k with
    | false =>
      rw [py_get_fail o v hv hE hH ps W n k hw hl, c_get_fail o v hv hE hH cs W n k hc hw hl]
      exact ⟨rfl, ι, sp, sc, W, ps, cs, n, rfl, rfl, h⟩
    | true =>
      have hxw' : v k ∉ sc.weak := by rw [h.inv.weak]; exact hxw
      have hstp : stepPy L sp (.get (v k)) =
          some ⟨trim8 (sp.strong ++ [v k]), sp.weak ++ [v k]⟩ := by
        simp [stepPy, newPy, hxw, L, hl, trim8, List.erase_of_not_mem hxp]
      have hstc : stepC L sc (.get (v k)) = some ⟨(v k :: sc.strong).take 8, sc.weak ++ [v k]⟩ := by
        simp [stepC, newC, hxs, hxw', L, hl]
      rw [hstp, hstc] at hci
      simp only [Option.getD_some] at hci
      rw [py_get_new o v hv hE hH ps W n k hw hl hp, c_get_new o v hv hE hH cs W n k hc hw hl]
      have hgood : ∀ l : List (K × Inst K), Good v ι l → v k ∉ vals v l →
          Good v (updO ι (v k) (k, n)) l := fun l hg hn e he => by
        have : v e.1 ≠ v k := fun x => hn ((mem_vals v l _).mpr ⟨e, he, x⟩)
        simp [updO, this, hg e he]
      have hnew : ∀ e ∈ [(k, (k, n))], (updO ι (v k) (k, n)) (v e.1) = some e.2 := by simp [updO]
      have hwn : v k ∉ vals v W := by rw [h.wv]; exact hxw
      have hcn : v k ∉ vals v cs := by rw [h.cv]; exact hxs
      refine ⟨rfl, updO ι (v k) (k, n), _, _, W ++ [(k, (k, n))], _, _, n + 1, rfl, rfl,
        ⟨hci, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
      · rw [vals_append, h.wv]; rfl
      · intro e he
        rcases List.mem_append.mp he with he | he
        · exact hgood W h.wg hwn e he
        · exact hnew e he
      · simp only [vals_trim8, vals_append, h.pv]; rfl
      · intro e he
        rcases List.mem_append.mp (trim8_mem _ e he) with he | he
        · exact hgood ps h.pg hp e he
        · exact hnew e he
      · have hcv := h.cv
        simp only [vals] at hcv ⊢
        rw [List.map_take, List.map_cons, hcv]
      · intro e he
        rcases List.mem_cons.mp (List.mem_of_mem_take he) with he | he
        · subst he; simp [updO]
        · exact hgood cs h.cg hcn e he
      · intro a ha b hb hab
        simp only [List.mem_append, List.mem_singleton] at ha hb
        by_cases hak : a = v k <;> by_cases hbk : b = v k
        · rw [hak, hbk]
        · exfalso
          rcases hb with hb | hb
          · simp only [updO, hak, hbk, ite_true, ite_false] at hab
            have := h.fresh b hb (k, n) hab.symm; simp at this
          · exact hbk hb
        · exfalso
          rcases ha with ha | ha
          · simp only [updO, hak, hbk, ite_true, ite_false] at hab
            have := h.fresh a ha (k, n) hab; simp at this
          · exact hak ha
        · rcases ha with ha | ha
          · rcases hb with hb | hb
            · simp only [updO, hak, hbk, ite_false] at hab; exact h.inj a ha b hb hab
            · exact absurd hb hbk
          · exact absurd ha hak
      · intro a ha i hi
        simp only [List.mem_append, List.mem_singleton] at ha
        by_cases hak : a = v k
        · simp only [updO, hak, ite_true] at hi; cases hi; simp
        · simp only [updO, hak, ite_false] at hi
          rcases ha with ha | ha
          · have := h.fresh a ha i hi; omega
          · exact absurd ha hak

theorem sim_clearKeys (err : Option PyExc) : ∀ (ks : List K) (ι : V → Option (Inst K))
    (sp sc : CacheSt V) (W ps cs : List (K × Inst K)) (n : Nat) (cw : Option (List (K × Inst K))),
    SimE v ι sp sc W ps cs n →
    (clearKeysC o W err ⟨true, cs, cw, [], n, []⟩ ks).2 = (clearKeysPy o err (mkZ ps W n) ks).2 ∧
    ∃ sp' sc' W' ps' cs', (clearKeysPy o err (mkZ ps W n) ks).1 = mkZ ps' W' n ∧
      (clearKeysC o W err ⟨true, cs, cw, [], n, []⟩ ks).1 = mkZ cs' W' n ∧
      SimE v ι sp' sc' W' ps' cs' n := by
  intro ks
  induction ks with
  | nil => intro ι sp sc W ps cs n cw h; exact ⟨rfl, sp, sc, W, ps, cs, rfl, rfl, h⟩
  | cons k ks ih =>
    intro ι sp sc W ps cs n cw h
    rw [c_clearKeys_cons o v hv hE hH, py_clearKeys_cons o v hv hE hH]
    have hci := clearKeys_inv [v k] sp sc h.inv
    simp only [List.foldl_cons, List.foldl_nil] at hci
    apply ih
    refine ⟨hci, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [(remv_spec v W (v k)).1, h.wv]
    · exact good_sub v ι W _ h.wg (remv_spec v W (v k)).2
    · rw [(remv_spec v ps (v k)).1, h.pv]
    · exact good_sub v ι ps _ h.pg (remv_spec v ps (v k)).2
    · rw [(remv_spec v cs (v k)).1, h.cv]
    · exact good_sub v ι cs _ h.cg (remv_spec v cs (v k)).2
    · intro a ha b hb hab
      exact h.inj a (List.mem_of_mem_erase ha) b (List.mem_of_mem_erase hb) hab
    · intro a ha i hi; exact h.fresh a (List.mem_of_mem_erase ha) i hi

theorem sim_drop (ι : V → Option (Inst K)) (sp sc : CacheSt V) (W ps cs : List (K × Inst K))
    (n : Nat) (h : SimE v ι sp sc W ps cs n) (k : K) : SimStep o v ι sp sc W ps cs n (.drop k) := by
  have hmc : ∀ y, y ∈ sc.strong ↔ y ∈ sp.strong := fun y => by rw [h.inv.strong, List.mem_reverse]
  unfold SimStep
  have h0 : dropIn ps ([] : List (K × Inst K)) k = [] := by simp [dropIn]
  have hpy : stepErrPy o (mkZ ps W n) (.drop k) = (mkZ ps (dropIn ps W k) n, .ok none) := by
    simp only [stepErrPy, mkZ, Option.map_some, h0]
  have hc : stepErrC o (mkZ cs W n) (.drop k) = (mkZ cs (dropIn cs W k) n, .ok none) := by
    simp [stepErrC, mkZ]
  rw [hpy, hc]
  cases hf : W.find? (fun e => decide (e.1 = k)) with
  | none =>
    have e1 : dropIn ps W k = W := by simp [dropIn, hf]
    have e2 : dropIn cs W k = W := by simp [dropIn, hf]
    rw [e1, e2]; exact ⟨rfl, ι, sp, sc, W, ps, cs, n, rfl, rfl, h⟩
  | some p =>
    obtain ⟨k', i⟩ := p
    have hm : (k', i) ∈ W := List.mem_of_find?_eq_some hf
    have hk : k' = k := by simpa using List.find?_some hf
    subst hk
    have hi : ι (v k') = some i := h.wg _ hm
    have hxw : v k' ∈ sp.weak := by rw [← h.wv]; exact (mem_vals v W _).mpr ⟨_, hm, rfl⟩
    have hiff : ∀ e ∈ W, (e.2 = i ↔ v e.1 = v k') := fun e he => by
      have hg := h.wg e he
      constructor
      · intro hei
        have hew : v e.1 ∈ sp.weak := by rw [← h.wv]; exact (mem_vals v W _).mpr ⟨e, he, rfl⟩
        exact h.inj _ hew _ hxw (by rw [hg, hi, hei])
      · intro hx; rw [hx, hi] at hg; exact (Option.some.inj hg).symm
    have hany : ∀ (l : List (K × Inst K)) (s : List V), vals v l = s → Good v ι l →
        (∀ y ∈ s, y ∈ sp.weak) → l.any (fun e => decide (e.2 = i)) = decide (v k' ∈ s) := by
      intro l s hls hg hsub
      rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_iff]
      constructor
      · rintro ⟨e, he, hei⟩
        have hys : v e.1 ∈ s := by rw [← hls]; exact (mem_vals v l _).mpr ⟨e, he, rfl⟩
        have := h.inj _ (hsub _ hys) _ hxw (by rw [hg e he, hi]; simp at hei; rw [hei])
        rw [← this]; exact hys
      · intro hs
        rw [← hls] at hs
        obtain ⟨e, he, hx⟩ := (mem_vals v l _).mp hs
        refine ⟨e, he, ?_⟩
        have := hg e he; rw [hx, hi] at this; simp [(Option.some.inj this).symm]
    have hap := hany ps sp.strong h.pv h.pg (fun y hy => h.inv.sub y hy)
    have hac := hany cs sc.strong h.cv h.cg (fun y hy => h.inv.sub y ((hmc y).mp hy))
    have e1 : dropIn ps W k' = if v k' ∈ sp.strong then W else W.eraseP (fun e => decide (e.2 = i)) := by
      simp only [dropIn, hf, hap]; split <;> simp_all
    have e2 : dropIn cs W k' = if v k' ∈ sp.strong then W else W.eraseP (fun e => decide (e.2 = i)) := by
      simp only [dropIn, hf, hac, hmc]; split <;> simp_all
    rw [e1, e2]
    obtain ⟨hci, -⟩ := cinv_next (fun _ => true) sp sc h.inv (.drop (v k'))
    have hs1 : (stepPy (fun _ => true) sp (.drop (v k'))).getD sp =
        ⟨sp.strong, if v k' ∈ sp.strong then sp.weak else sp.weak.erase (v k')⟩ := rfl
    have hs2 : (stepC (fun _ => true) sc (.drop (v k'))).getD sc =
        ⟨sc.strong, if v k' ∈ sp.strong then sc.weak else sc.weak.erase (v k')⟩ := by
      simp only [stepC, Option.getD_some, hmc]
    rw [hs1, hs2] at hci
    refine ⟨rfl, ι, _, _, _, ps, cs, n, rfl, rfl, ⟨hci, ?_, ?_, h.pv, h.pg, h.cv, h.cg, ?_, ?_⟩⟩
    · split
      · exact h.wv
      · rw [eraseP_inst v i (v k') W hiff, h.wv]
    · split
      · exact h.wg
      · exact good_sub v ι W _ h.wg (fun e he => List.mem_of_mem_eraseP he)
    · intro a ha b hb hab
      simp only at ha hb
      split at ha <;> split at hb <;> simp_all
      all_goals first
        | exact h.inj a ha b hb hab
        | exact h.inj a (List.mem_of_mem_erase ha) b (List.mem_of_mem_erase hb) hab
    · intro a ha j hj
      simp only at ha
      split at ha
      · exact h.fresh a ha j hj
      · exact h.fresh a (List.mem_of_mem_erase ha) j hj

theorem sim_step (ι : V → Option (Inst K)) (sp sc : CacheSt V) (W ps cs : List (K × Inst K))
    (n : Nat) (h : SimE v ι sp sc W ps cs n) (op : ZOp K) (hop : op.isDel = false) :
    SimStep o v ι sp sc W ps cs n op := by
  cases op with
  | get k => exact sim_get o v hv hE hH ι sp sc W ps cs n h k
  | clear =>
    have hp : stepErrPy o (mkZ ps W n) .clear = (mkZ [] [] n, .ok none) := by
      simp [stepErrPy, clearErrPy, setWeakPy, mkZ]
    have hc : stepErrC o (mkZ cs W n) .clear = (mkZ [] [] n, .ok none) := by
      simp [stepErrC, clearErrC, getWeakC, mkZ]
    unfold SimStep
    rw [hp, hc]
    refine ⟨rfl, ι, ⟨[], []⟩, ⟨[], []⟩, [], [], [], n, rfl, rfl,
      ⟨⟨rfl, rfl, List.nodup_nil, by simp, by simp⟩, rfl, by simp [Good], rfl, by simp [Good], rfl,
        by simp [Good], by simp, by simp⟩⟩
  | clearKeys ks err =>
    have hp : stepErrPy o (mkZ ps W n) (.clearKeys ks err) = clearKeysPy o err (mkZ ps W n) ks := rfl
    have hc : stepErrC o (mkZ cs W n) (.clearKeys ks err) =
        clearKeysC o W err ⟨true, cs, some W, [], n, []⟩ ks := by
      simp [stepErrC, clearErrC, getWeakC, mkZ]
    unfold SimStep
    rw [hp, hc]
    obtain ⟨e1, sp', sc', W', ps', cs', h1, h2, h3⟩ :=
      sim_clearKeys o v hv hE hH err ks ι sp sc W ps cs n (some W) h
    exact ⟨e1, ι, sp', sc', W', ps', cs', n, h1, h2, h3⟩
  | drop k => exact sim_drop o v hv hE hH ι sp sc W ps cs n h k
  | delWeak => simp [ZOp.isDel] at hop
  | setWeak d => simp [ZOp.isDel] at hop

theorem sim_run : ∀ (ops : List (ZOp K)) (ι : V → Option (Inst K)) (sp sc : CacheSt V)
    (W ps cs : List (K × Inst K)) (n : Nat), SimE v ι sp sc W ps cs n →
    ops.all (fun op => !op.isDel) = true →
    (runErrC o (mkZ cs W n) ops).2 = (runErrPy o (mkZ ps W n) ops).2 ∧
    ∃ ι' sp' sc' W' ps' cs' n', (runErrPy o (mkZ ps W n) ops).1 = mkZ ps' W' n' ∧
      (runErrC o (mkZ cs W n) ops).1 = mkZ cs' W' n' ∧ SimE v ι' sp' sc' W' ps' cs' n' := by
  intro ops
  induction ops with
  | nil => intro ι sp sc W ps cs n h _; exact ⟨rfl, ι, sp, sc, W, ps, cs, n, rfl, rfl, h⟩
  | cons op ops ih =>
    intro ι sp sc W ps cs n h hall
    simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at hall
    obtain ⟨er, ι', sp', sc', W', ps', cs', n', hp, hc, h'⟩ :=
      sim_step o v hv hE hH ι sp sc W ps cs n h op hall.1
    obtain ⟨er2, rest⟩ := ih ι' sp' sc' W' ps' cs' n' h' hall.2
    simp only [runErrPy, runErrC]
    rw [show stepErrPy o (mkZ ps W n) op = ((stepErrPy o (mkZ ps W n) op).1,
        (stepErrPy o (mkZ ps W n) op).2) from rfl,
      show stepErrC o (mkZ cs W n) op = ((stepErrC o (mkZ cs W n) op).1,
        (stepErrC o (mkZ cs W n) op).2) from rfl, hp, hc, er]
    simp only [er2, true_and]
    exact rest

end sim

theorem good_map (v : K → V) (ι : V → Option (Inst K)) : ∀ l : List (K × Inst K), Good v ι l →
    l.map (fun e => (v e.1, e.2)) = (vals v l).filterMap (fun x => (ι x).map fun i => (x, i)) := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons e l ih =>
    intro hg
    have he := hg e List.mem_cons_self
    simp only [List.map_cons, vals, List.filterMap_cons, he, Option.map_some]
    exact congrArg _ (ih fun x hx => hg x (List.mem_cons_of_mem _ hx))

end equiv

/-- The base-class caches with the fallible-key mirrors, for keys whose `==` compares a value
`v k` and never raises, and whose `hash()` is a function of that value (separate `str` objects
with equal text are equal keys; such `__eq__` cannot re-enter): every run of `ZoneInfo(key)`,
`clear_cache()`, `clear_cache(only_keys=...)` whose iterator may raise after any prefix, and
collections gives the same outcome in both twins (the same instance for each `ZoneInfo(key)`,
the same exception for each failure), and the strong caches hold the same key values with the
same instances in recency order (C newest first, Python oldest first), never more than 8. The
stored key objects may differ: C keeps the first equal key, Python the latest. -/
def CacheTwinsEquiv : Prop :=
  ∀ (K V : Type) [DecidableEq K] [DecidableEq V] (o : KeyOps K) (v : K → V) (hv : V → Int),
    (∀ a b, o.eq a b = .ok (decide (v a = v b))) → (∀ a, o.hash a = .ok (hv (v a))) →
    ∀ ops : List (ZOp K), ops.all (fun op => !op.isDel) = true →
      (runErrC o freshBase ops).2 = (runErrPy o freshBase ops).2 ∧
      (runErrC o freshBase ops).1.strong.map (fun e => (v e.1, e.2)) =
        ((runErrPy o freshBase ops).1.strong.map (fun e => (v e.1, e.2))).reverse ∧
      (runErrPy o freshBase ops).1.strong.length ≤ 8

theorem cacheTwinsEquiv_proven : CacheTwinsEquiv := by
  intro K V _ _ o v hv hE hH ops hall
  have h0 : SimE v (fun _ => none) ⟨[], []⟩ ⟨[], []⟩ [] [] [] 0 :=
    ⟨⟨rfl, rfl, List.nodup_nil, by simp, by simp⟩, rfl, by simp [Good], rfl, by simp [Good], rfl,
      by simp [Good], by simp, by simp⟩
  have hf : (freshBase : ZCls K) = mkZ [] [] 0 := rfl
  rw [hf]
  obtain ⟨er, ι', sp', sc', W', ps', cs', n', hp, hc, h'⟩ := sim_run o v hv hE hH ops _ _ _ _ _ _ _ h0 hall
  refine ⟨er, ?_, ?_⟩
  · rw [hp, hc]
    simp only [mkZ]
    rw [good_map v ι' cs' h'.cg, good_map v ι' ps' h'.pg, h'.cv, h'.pv, h'.inv.strong,
      List.filterMap_reverse]
  · rw [hp]
    simp only [mkZ]
    have := h'.inv.len
    rw [← h'.pv] at this
    simpa [vals] using this

end PyLean.Datetime.Zone
