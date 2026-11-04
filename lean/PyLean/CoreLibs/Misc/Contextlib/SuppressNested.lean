import PyLean.CoreLibs.Misc.Contextlib.SuppressProps

/-!
`suppress` on nested exception groups, with plain exception classes and the builtin `derive`: the
group that leaves the `with` holds exactly the leaves that no matching node is above, in order.
-/

namespace PyLean.CoreLibs.Misc.Contextlib

open PyLean

/-- Every member of a group was made before the group: `BaseExceptionGroup.__new__` takes a
sequence of existing exceptions and `excs` is read-only afterwards (Objects/exceptions.c:1347), so
an exception is never its own member, directly or not. -/
def MembersBefore (h : Heap) : Prop :=
  ∀ e cs, (h.get e).children = some cs → ∀ c ∈ cs, c < e

/-- The leaves of `e`, in order. -/
def leaves (h : Heap) : Nat → ExcId → List ExcId
  | 0, _ => []
  | n + 1, e =>
    match (h.get e).children with
    | none => [e]
    | some cs => cs.flatMap (leaves h n)

/-- The leaves of `e` that no node matching `ms` is above, in order: what `suppress` must keep. -/
def kept (h : Heap) (ms : List Cls) : Nat → ExcId → List ExcId
  | 0, _ => []
  | n + 1, e =>
    if matchBy h ms e then []
    else
      match (h.get e).children with
      | none => [e]
      | some cs => cs.flatMap (kept h ms n)

/-- `h'` extends `h`: the objects of `h` are unchanged and more may follow. -/
def Ext (h h' : Heap) : Prop := h.length ≤ h'.length ∧ ∀ i < h.length, h'.get i = h.get i

theorem Ext.refl (h : Heap) : Ext h h := ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem Ext.trans {a b c : Heap} (h1 : Ext a b) (h2 : Ext b c) : Ext a c :=
  ⟨Nat.le_trans h1.1 h2.1, fun i hi => (h2.2 i (Nat.lt_of_lt_of_le hi h1.1)).trans (h1.2 i hi)⟩

theorem flatMap_congr' {α β : Type} (l : List α) (f g : α → List β) (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.flatMap_cons]
    rw [h a (by simp), ih (fun x hx => h x (by simp [hx]))]

theorem leaves_ext {h h' : Heap} (hm : MembersBefore h) (he : Ext h h') :
    ∀ n c, c < h.length → leaves h' n c = leaves h n c := by
  intro n
  induction n with
  | zero => intro c _; rfl
  | succ k ih =>
    intro c hc
    simp only [leaves, he.2 c hc]
    split
    · rfl
    · rename_i cs hcs
      exact flatMap_congr' cs _ _ (fun x hx => ih x (Nat.lt_trans (hm c cs hcs x hx) hc))

theorem kept_ext {h h' : Heap} (ms : List Cls) (hm : MembersBefore h) (he : Ext h h') :
    ∀ n c, c < h.length → kept h' ms n c = kept h ms n c := by
  intro n
  induction n with
  | zero => intro c _; rfl
  | succ k ih =>
    intro c hc
    simp only [kept, matchBy, he.2 c hc]
    by_cases hmc : ms.any (subOf (h.get c).cls) = true
    · simp [hmc]
    · simp only [hmc, Bool.false_eq_true, if_false]
      cases hcs : (h.get c).children with
      | none => rfl
      | some cs =>
        show cs.flatMap (kept h' ms k) = cs.flatMap (kept h ms k)
        exact flatMap_congr' cs _ _ (fun x hx => ih x (Nat.lt_trans (hm c cs hcs x hx) hc))

theorem leaves_fuel {h : Heap} (hm : MembersBefore h) :
    ∀ n m c, c < n → c < m → leaves h n c = leaves h m c := by
  intro n
  induction n with
  | zero => intro m c hc; exact absurd hc (Nat.not_lt_zero _)
  | succ k ih =>
    intro m c hc hm'
    cases m with
    | zero => exact absurd hm' (Nat.not_lt_zero _)
    | succ j =>
      simp only [leaves]
      split
      · rfl
      · rename_i cs hcs
        exact flatMap_congr' cs _ _ (fun x hx =>
          ih j x (Nat.lt_of_lt_of_le (hm c cs hcs x hx) (Nat.le_of_lt_succ hc))
            (Nat.lt_of_lt_of_le (hm c cs hcs x hx) (Nat.le_of_lt_succ hm')))

theorem kept_fuel {h : Heap} (ms : List Cls) (hm : MembersBefore h) :
    ∀ n m c, c < n → c < m → kept h ms n c = kept h ms m c := by
  intro n
  induction n with
  | zero => intro m c hc; exact absurd hc (Nat.not_lt_zero _)
  | succ k ih =>
    intro m c hc hm'
    cases m with
    | zero => exact absurd hm' (Nat.not_lt_zero _)
    | succ j =>
      simp only [kept]
      split
      · rfl
      · split
        · rfl
        · rename_i cs hcs
          exact flatMap_congr' cs _ _ (fun x hx =>
            ih j x (Nat.lt_of_lt_of_le (hm c cs hcs x hx) (Nat.le_of_lt_succ hc))
              (Nat.lt_of_lt_of_le (hm c cs hcs x hx) (Nat.le_of_lt_succ hm')))

theorem leaves_children {h h' : Heap} (hc : ∀ i, (h'.get i).children = (h.get i).children) :
    ∀ n c, leaves h' n c = leaves h n c := by
  intro n
  induction n with
  | zero => intro c; rfl
  | succ k ih =>
    intro c
    simp only [leaves, hc c]
    split
    · rfl
    · exact flatMap_congr' _ _ _ (fun x _ => ih x)

theorem get_modify_ne (h : Heap) (a i : ExcId) (f : ExcObj → ExcObj) (hne : a ≠ i) :
    (h.modify a f).get i = h.get i := by
  simp only [Heap.modify, Heap.get]
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne hne, ← List.getD_eq_getElem?_getD]

theorem get_beyond (h : Heap) (i : ExcId) (hi : h.length ≤ i) : h.get i = default := by
  simp [Heap.get, List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

/-- `exceptiongroup_subset` with the builtin `derive` on a non-empty list: a new group, the next
object of the heap, with the members given and the message, cause and traceback of `orig`. -/
theorem subsetM_builtin {σ : Type} (handled : Option ExcId) (s : St σ) (orig : ExcId)
    (excs : List ExcId) (hne : excs ≠ []) (horig : orig < s.h.length) :
    ∃ s', subsetM builtinDerive handled s orig excs = (s', .ok (some s.h.length)) ∧
      s'.g = s.g ∧ s'.h.length = s.h.length + 1 ∧ (∀ i < s.h.length, s'.h.get i = s.h.get i) ∧
      (s'.h.get s.h.length).children = some excs ∧ (s'.h.get s.h.length).msg = (s.h.get orig).msg ∧
      (s'.h.get s.h.length).cause = (s.h.get orig).cause ∧
      (s'.h.get s.h.length).tb = (s.h.get orig).tb := by
  have hcs : excs.isEmpty = false := by
    cases excs with
    | nil => exact absurd rfl hne
    | cons _ _ => rfl
  let o : ExcObj :=
    { cls := deriveCls s.h excs, msg := (s.h.get orig).msg, children := some excs }
  let h0 := (s.h.alloc o).1
  have hlen0 : h0.length = s.h.length + 1 := by simp [h0, Heap.alloc]
  have hget0 : h0.get s.h.length = o := get_alloc_last s.h o
  have hold0 : ∀ i < s.h.length, h0.get i = s.h.get i := fun i hi => get_alloc_lt s.h o i hi
  have hbeg : h0.isInst s.h.length "BaseExceptionGroup" = true := by
    have hc : (deriveCls s.h excs).contains "BaseExceptionGroup" = true := by
      unfold deriveCls
      split <;> decide
    simp only [Heap.isInst, hget0, o]
    exact hc
  have horig0 : h0.get orig = s.h.get orig := hold0 orig horig
  let h1 := match (h0.get orig).tb with
    | some t => h0.setTb s.h.length (some t)
    | none => h0
  let h2 := (h1.setContext s.h.length (h0.get orig).context).modify s.h.length
    (fun x => { x with cause := (h0.get orig).cause })
  have hk : subsetM builtinDerive handled s orig excs = ({ s with h := h2 }, .ok (some s.h.length)) := by
    simp only [subsetM, hcs, builtinDerive, Bool.false_eq_true, if_false]
    show (if (({ s with h := h0 } : St σ)).h.isInst s.h.length "BaseExceptionGroup" = true then _ else _) = _
    rw [if_pos hbeg]
    rfl
  have hl1 : h1.length = s.h.length + 1 := by
    simp only [h1]
    split <;> simp [Heap.setTb, length_modify, hlen0]
  have hl2 : h2.length = s.h.length + 1 := by
    simp only [h2, length_modify, length_setContext, hl1]
  have hlt1 : s.h.length < h1.length := by rw [hl1]; exact Nat.lt_succ_self _
  have hold1 : ∀ i < s.h.length, h1.get i = s.h.get i := by
    intro i hi
    simp only [h1]
    split
    · simp only [Heap.setTb]
      rw [get_modify_ne _ _ _ _ (Nat.ne_of_gt hi)]
      exact hold0 i hi
    · exact hold0 i hi
  have hnew1 : h1.get s.h.length =
      { o with tb := match (h0.get orig).tb with
        | some t => some t
        | none => o.tb } := by
    simp only [h1]
    split
    · rename_i t ht
      simp only [Heap.setTb]
      rw [get_modify_self _ _ _ (by rw [hlen0]; exact Nat.lt_succ_self _), hget0]
    · rw [hget0]
  have hnew2 : h2.get s.h.length =
      { (h1.setContext s.h.length (h0.get orig).context).get s.h.length with
        cause := (h0.get orig).cause } := by
    simp only [h2]
    rw [get_modify_self _ _ _ (by rw [length_setContext]; exact hlt1)]
  have hsc := setContext_same h1 s.h.length (h0.get orig).context s.h.length
  refine ⟨{ s with h := h2 }, hk, rfl, hl2, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    show h2.get i = s.h.get i
    simp only [h2]
    rw [get_modify_ne _ _ _ _ (Nat.ne_of_gt hi)]
    simp only [Heap.setContext]
    rw [get_modify_ne _ _ _ _ (Nat.ne_of_gt hi)]
    exact hold1 i hi
  · show (h2.get s.h.length).children = some excs
    rw [hnew2]
    show ((h1.setContext s.h.length (h0.get orig).context).get s.h.length).children = some excs
    rw [hsc.1, hnew1]
  · show (h2.get s.h.length).msg = (s.h.get orig).msg
    rw [hnew2]
    show ((h1.setContext s.h.length (h0.get orig).context).get s.h.length).msg = _
    rw [hsc.2.1, hnew1]
  · show (h2.get s.h.length).cause = (s.h.get orig).cause
    rw [hnew2, horig0]
  · show (h2.get s.h.length).tb = (s.h.get orig).tb
    rw [hnew2]
    show ((h1.setContext s.h.length (h0.get orig).context).get s.h.length).tb = _
    rw [hsc.2.2.2.1, hnew1, horig0]
    cases (s.h.get orig).tb <;> rfl

/-- What `subsetM_builtin` gives keeps the heap an extension with members made before. -/
theorem subsetM_builtin_ext {σ : Type} {s s' : St σ} {excs : List ExcId}
    (hlen : s'.h.length = s.h.length + 1) (hold : ∀ i < s.h.length, s'.h.get i = s.h.get i)
    (hch : (s'.h.get s.h.length).children = some excs) (hb : ∀ x ∈ excs, x < s.h.length)
    (hm : MembersBefore s.h) : Ext s.h s'.h ∧ MembersBefore s'.h := by
  refine ⟨⟨by rw [hlen]; exact Nat.le_succ _, hold⟩, ?_⟩
  intro e cs hcs c hc
  rcases Nat.lt_or_ge e s.h.length with he | he
  · rw [hold e he] at hcs
    exact hm e cs hcs c hc
  · rcases Nat.lt_or_ge e (s.h.length + 1) with he' | he'
    · have : e = s.h.length := Nat.le_antisymm (Nat.le_of_lt_succ he') he
      subst this
      rw [hch] at hcs
      cases hcs
      exact hb c hc
    · rw [get_beyond s'.h e (by rw [hlen]; exact he')] at hcs
      cases hcs

/-- The main lemma: on a heap whose groups have members made before them, `splitRec` with the
builtin `derive` succeeds, extends the heap, and its rest is `none` exactly when `kept` is empty,
otherwise an object whose leaves are `kept`: `e` itself for an unmatched leaf, else a new group
with `e`'s message, cause and traceback. -/
theorem splitRec_builtin {σ : Type} (ms : List Cls) (handled : Option ExcId) :
    ∀ (n : Nat) (s : St σ) (e : ExcId), MembersBefore s.h → e < s.h.length → e < n →
      ∃ s' m r, splitRec ms builtinDerive handled n s e = some (s', .ok (m, r)) ∧
        Ext s.h s'.h ∧ MembersBefore s'.h ∧ s'.g = s.g ∧
        (∀ x, m = some x → x < s'.h.length) ∧
        (r = none ↔ kept s.h ms n e = []) ∧
        (∀ x, r = some x → x < s'.h.length ∧ leaves s'.h (x + 1) x = kept s.h ms n e ∧
          ((x = e ∧ (s.h.get e).children = none) ∨
           (s.h.length ≤ x ∧ (s'.h.get x).msg = (s.h.get e).msg ∧
            (s'.h.get x).cause = (s.h.get e).cause ∧ (s'.h.get x).tb = (s.h.get e).tb))) := by
  intro n
  induction n with
  | zero => intro s e _ _ he; exact absurd he (Nat.not_lt_zero _)
  | succ k ih =>
    intro s e hm hel hek
    rw [splitRec]
    by_cases hmat : matchBy s.h ms e = true
    · refine ⟨s, some e, none, by simp [hmat], Ext.refl _, hm, rfl, ?_, ?_, ?_⟩
      · intro x hx; cases hx; exact hel
      · simp [kept, hmat]
      · intro x hx; cases hx
    · have hmat' : matchBy s.h ms e = false := by simpa using hmat
      simp only [hmat', Bool.false_eq_true, if_false]
      cases hch : (s.h.get e).children with
      | none =>
        refine ⟨s, none, some e, rfl, Ext.refl _, hm, rfl, ?_, ?_, ?_⟩
        · intro x hx; cases hx
        · simp [kept, hmat', hch]
        · intro x hx
          cases hx
          refine ⟨hel, ?_, .inl ⟨rfl, rfl⟩⟩
          simp [leaves, kept, hmat', hch]
      | some cs =>
        simp only
        -- the loop over the members
        have hfold : ∀ (l : List ExcId) (s1 : St σ) (ml rl done : List ExcId),
            (∀ c ∈ l, c < e) → Ext s.h s1.h → MembersBefore s1.h → s1.g = s.g →
            (∀ x ∈ ml, x < s1.h.length) →
            (∀ x ∈ rl, x < s1.h.length ∧ leaves s1.h (x + 1) x ≠ []) →
            rl.flatMap (fun x => leaves s1.h (x + 1) x) = done.flatMap (kept s.h ms k) →
            ∃ s2 ml' rl', l.foldl (splitStep (splitRec ms builtinDerive handled k))
                (some (s1, .ok (ml, rl))) = some (s2, .ok (ml', rl')) ∧
              Ext s.h s2.h ∧ MembersBefore s2.h ∧ s2.g = s.g ∧ (∀ x ∈ ml', x < s2.h.length) ∧
              (∀ x ∈ rl', x < s2.h.length ∧ leaves s2.h (x + 1) x ≠ []) ∧
              rl'.flatMap (fun x => leaves s2.h (x + 1) x) = (done ++ l).flatMap (kept s.h ms k) := by
          intro l
          induction l with
          | nil =>
            intro s1 ml rl done _ h1 h2 h3 h4 h5 h6
            exact ⟨s1, ml, rl, rfl, h1, h2, h3, h4, h5, by simpa using h6⟩
          | cons c rest ihl =>
            intro s1 ml rl done hb h1 h2 h3 h4 h5 h6
            have hce : c < e := hb c (by simp)
            have hcl : c < s1.h.length := Nat.lt_of_lt_of_le (Nat.lt_trans hce hel) h1.1
            obtain ⟨s3, m, r, hrec, he3, hm3, hg3, hmb, hiff, hr⟩ :=
              ih s1 c h2 hcl (Nat.lt_of_lt_of_le hce (Nat.le_of_lt_succ hek))
            have hstep : splitStep (splitRec ms builtinDerive handled k) (some (s1, .ok (ml, rl))) c =
                some (s3, .ok (ml ++ m.toList, rl ++ r.toList)) := by
              simp [splitStep, hrec]
            simp only [List.foldl_cons]
            rw [hstep]
            have hkc : kept s1.h ms k c = kept s.h ms k c := kept_ext ms hm h1 k c (Nat.lt_trans hce hel)
            rw [show done ++ c :: rest = done ++ [c] ++ rest by simp]
            apply ihl s3 _ _ (done ++ [c]) (fun x hx => hb x (by simp [hx])) (h1.trans he3) hm3
              (hg3.trans h3)
            · intro x hx
              simp only [List.mem_append] at hx
              rcases hx with hx | hx
              · exact Nat.lt_of_lt_of_le (h4 x hx) he3.1
              · cases m with
                | none => cases hx
                | some y => simp at hx; subst hx; exact hmb _ rfl
            · intro x hx
              simp only [List.mem_append] at hx
              rcases hx with hx | hx
              · obtain ⟨hxl, hxn⟩ := h5 x hx
                refine ⟨Nat.lt_of_lt_of_le hxl he3.1, ?_⟩
                rw [leaves_ext h2 he3 _ x hxl]
                exact hxn
              · cases r with
                | none => cases hx
                | some y =>
                  simp at hx
                  subst hx
                  obtain ⟨hyl, hyk, _⟩ := hr x rfl
                  refine ⟨hyl, ?_⟩
                  rw [hyk]
                  intro hk
                  exact absurd (hiff.2 hk) (by simp)
            · rw [List.flatMap_append, List.flatMap_append]
              have hold : rl.flatMap (fun x => leaves s3.h (x + 1) x) =
                  rl.flatMap (fun x => leaves s1.h (x + 1) x) :=
                flatMap_congr' rl _ _ (fun x hx => leaves_ext h2 he3 _ x (h5 x hx).1)
              rw [hold, h6]
              congr 1
              simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
              cases r with
              | none =>
                simp only [Option.toList_none, List.flatMap_nil]
                rw [← hkc]
                exact (hiff.1 rfl).symm
              | some y =>
                obtain ⟨_, hyk, _⟩ := hr y rfl
                simp [hyk, hkc]
        have hcsb : ∀ c ∈ cs, c < e := fun c hc => hm e cs hch c hc
        obtain ⟨s2, ml, rl, hf, he2, hm2, hg2, hml, hrl, heq⟩ :=
          hfold cs s [] [] [] hcsb (Ext.refl _) hm rfl (by simp) (by simp) (by simp)
        rw [hf]
        simp only [List.nil_append] at heq
        have hel2 : e < s2.h.length := Nat.lt_of_lt_of_le hel he2.1
        -- the match subset
        obtain ⟨s4, m4, hsub4, he4, hm4, hg4, hml4⟩ : ∃ s4 m4, subsetM builtinDerive handled s2 e ml =
            (s4, .ok m4) ∧ Ext s2.h s4.h ∧ MembersBefore s4.h ∧ s4.g = s2.g ∧
            (∀ x, m4 = some x → x < s4.h.length) := by
          by_cases hmn : ml = []
          · subst hmn
            exact ⟨s2, none, by simp [subsetM], Ext.refl _, hm2, rfl, fun x hx => by cases hx⟩
          · obtain ⟨s4, hk4, hg, hlen, hold, hch4, _, _, _⟩ := subsetM_builtin handled s2 e ml hmn hel2
            obtain ⟨hx4, hm4⟩ := subsetM_builtin_ext hlen hold hch4 hml hm2
            exact ⟨s4, some s2.h.length, hk4, hx4, hm4, hg,
              fun x hx => by cases hx; rw [hlen]; exact Nat.lt_succ_self _⟩
        by_cases hrn : rl = []
        · subst hrn
          have hsub5 : subsetM builtinDerive handled s4 e [] = (s4, .ok none) := by simp [subsetM]
          refine ⟨s4, m4, none, ?_, he2.trans he4, hm4, hg4.trans hg2, hml4, ?_, ?_⟩
          · simp [hsub4, hsub5]
          · have hkeq : kept s.h ms (k + 1) e = cs.flatMap (kept s.h ms k) := by
              simp [kept, hmat', hch]
            rw [hkeq, ← heq]
            simp
          · intro x hx; cases hx
        · obtain ⟨s5, hk5, hg5, hlen5, hold5, hch5, hmsg5, hcause5, htb5⟩ :=
            subsetM_builtin handled s4 e rl hrn (Nat.lt_of_lt_of_le hel2 he4.1)
          have hrlb : ∀ x ∈ rl, x < s4.h.length := fun x hx => Nat.lt_of_lt_of_le (hrl x hx).1 he4.1
          obtain ⟨he5, hm5⟩ := subsetM_builtin_ext hlen5 hold5 hch5 hrlb hm4
          have hkeq : kept s.h ms (k + 1) e = cs.flatMap (kept s.h ms k) := by
            simp [kept, hmat', hch]
          have hleaves : leaves s5.h (s4.h.length + 1) s4.h.length =
              rl.flatMap (fun x => leaves s2.h (x + 1) x) := by
            simp only [leaves, hch5]
            apply flatMap_congr'
            intro y hy
            rw [leaves_fuel hm5 s4.h.length (y + 1) y (hrlb y hy) (Nat.lt_succ_self y)]
            exact leaves_ext hm2 (he4.trans he5) (y + 1) y (hrl y hy).1
          have hne : rl.flatMap (fun x => leaves s2.h (x + 1) x) ≠ [] := by
            obtain ⟨y, ys, hyy⟩ : ∃ y ys, rl = y :: ys := by
              cases rl with
              | nil => exact absurd rfl hrn
              | cons y ys => exact ⟨y, ys, rfl⟩
            have hy := (hrl y (by simp [hyy])).2
            intro h0
            apply hy
            rw [hyy, List.flatMap_cons] at h0
            exact (List.append_eq_nil_iff.mp h0).1
          have hold24 := he2.trans he4
          refine ⟨s5, m4, some s4.h.length, ?_, hold24.trans he5, hm5, hg5.trans (hg4.trans hg2), ?_, ?_, ?_⟩
          · simp [hsub4, hk5]
          · intro x hx; exact Nat.lt_of_lt_of_le (hml4 x hx) he5.1
          · rw [hkeq, ← heq]
            simp [hne]
          · intro x hx
            cases hx
            refine ⟨by rw [hlen5]; exact Nat.lt_succ_self _, by rw [hleaves, heq, hkeq],
              .inr ⟨hold24.1, ?_, ?_, ?_⟩⟩
            · rw [hmsg5, hold24.2 e hel]
            · rw [hcause5, hold24.2 e hel]
            · rw [htb5, hold24.2 e hel]

theorem matcherClasses_plain {σ : Type} : ∀ (cls : List Cls),
    (∀ c ∈ cls, c.contains "BaseException" = true) →
    matcherClasses (σ := σ) (cls.map SupItem.cls) = some cls
  | [], _ => rfl
  | c :: rest, h => by
    simp only [List.map_cons, matcherClasses, h c (by simp), if_true]
    rw [matcherClasses_plain rest (fun c' hc' => h c' (by simp [hc']))]
    rfl

/-- `suppress` on a nested exception group, as documented: "suppressed exceptions are removed from
the group. Any exceptions of the group which are not suppressed are re-raised in a new group which
is created using the original group's derive() method". For exception classes and the builtin
`derive`, and a group that is not itself suppressed: when every leaf is under a matching node, the
group is suppressed; otherwise a new group is raised whose leaves are exactly the others, in
order, with the message, cause and traceback of the original, and every object that existed keeps
its class, message, members, cause and traceback. `MembersBefore` is the invariant that groups are
made from existing exceptions. -/
def SuppressNested : Prop :=
  ∀ (σ : Type) (cls : List Cls) (s : St σ) (handled : Option ExcId) (e : ExcId) (cs : List ExcId),
    MembersBefore s.h → (∀ c ∈ cls, c.contains "BaseException" = true) →
    (s.h.get e).children = some cs → s.h.isInst e "BaseExceptionGroup" = true →
    cls.any (subOf (s.h.get e).cls) = false →
    let r := suppressExit (cls.map SupItem.cls) builtinDerive s handled
      (some (Derived.cls (s.h.get e).cls)) (some e)
    (kept s.h cls (e + 1) e = [] → ∃ s', r = .ok (s', .ok (some true))) ∧
    (kept s.h cls (e + 1) e ≠ [] → ∃ s' x, r = .ok (s', .error x) ∧ x ≠ e ∧
      leaves s'.h (x + 1) x = kept s.h cls (e + 1) e ∧
      (s'.h.get x).msg = (s.h.get e).msg ∧ (s'.h.get x).cause = (s.h.get e).cause ∧
      (s'.h.get x).tb = (s.h.get e).tb ∧ (∀ i < s.h.length, SameData (s'.h.get i) (s.h.get i)))

theorem suppressNested_proven : SuppressNested := by
  intro σ cls s handled e cs hm hcls hch hbeg hnm r
  have hel : e < s.h.length := isInst_lt hbeg
  have hbegc : subOf (s.h.get e).cls clsBEG = true := by
    simp only [Heap.isInst] at hbeg
    simpa [subOf, clsBEG] using hbeg
  obtain ⟨s', m, rr, hsplit, hext, _, _, _, hiff, hrr⟩ :=
    splitRec_builtin cls handled (s.h.length + 1) s e hm hel (Nat.lt_succ_of_lt hel)
  have hkf : kept s.h cls (s.h.length + 1) e = kept s.h cls (e + 1) e :=
    kept_fuel cls hm _ _ e (Nat.lt_succ_of_lt hel) (Nat.lt_succ_self e)
  have hr : r = (match rr with
      | none => .ok (s', .ok (some true))
      | some x => .ok ({ s' with h := s'.h.raiseCtx x handled }, .error x)) := by
    simp only [r, suppressExit, issubTuple_plain, hnm, issubItem, hbegc, egSplit, hbeg,
      Bool.not_true, Bool.false_eq_true, if_false, matcherClasses_plain cls hcls, hsplit]
    cases rr <;> rfl
  refine ⟨?_, ?_⟩
  · intro hk
    have : rr = none := hiff.2 (by rw [hkf]; exact hk)
    subst this
    exact ⟨s', hr⟩
  · intro hk
    cases rr with
    | none => exact absurd (by rw [← hkf]; exact hiff.1 rfl) hk
    | some x =>
      obtain ⟨hxl, hxk, hcase⟩ := hrr x rfl
      have hnew : s.h.length ≤ x ∧ (s'.h.get x).msg = (s.h.get e).msg ∧
          (s'.h.get x).cause = (s.h.get e).cause ∧ (s'.h.get x).tb = (s.h.get e).tb := by
        rcases hcase with ⟨_, hc⟩ | hc
        · rw [hch] at hc; cases hc
        · exact hc
      obtain ⟨hlx, hmsg, hcause, htb⟩ := hnew
      let H := s'.h.raiseCtx x handled
      have hsame := raiseCtx_same s'.h x handled
      refine ⟨{ s' with h := H }, x, by rw [hr], Nat.ne_of_gt (Nat.lt_of_lt_of_le hel hlx), ?_,
        ?_, ?_, ?_, ?_⟩
      · show leaves H (x + 1) x = _
        rw [leaves_children (fun i => (hsame i).1), hxk, hkf]
      · show (H.get x).msg = _
        rw [(hsame x).2.1, hmsg]
      · show (H.get x).cause = _
        rw [(hsame x).2.2.1, hcause]
      · show (H.get x).tb = _
        rw [(hsame x).2.2.2.1, htb]
      · intro i hi
        show SameData (H.get i) (s.h.get i)
        have := hsame i
        rw [hext.2 i hi] at this
        exact this

end PyLean.CoreLibs.Misc.Contextlib
