import PyLean.BytesObj.Mem.Tuple

/-!
`v == w` for two different views, of any dimension, against `v.tolist() == w.tolist()`. The walks
`cmp_base` and `cmp_rec` are compared with the nested lists `tolist` builds, the fast `switch`
with the `struct` path, and the check `equiv_shape` with the shapes the lists show.
-/

namespace PyLean.BytesObj.Mem

open PyLean

mutual
  /-- `==` on two results of `tolist`: lists are equal if they have the same length and their
  items are equal, and a list never equals a scalar. -/
  def treeEq : Tree → Tree → Bool
    | .leaf a, .leaf b => itemEq a b
    | .node l, .node r => treeListEq l r
    | _, _ => false
  def treeListEq : List Tree → List Tree → Bool
    | [], [] => true
    | a :: as, b :: bs => treeEq a b && treeListEq as bs
    | _, _ => false
end

theorem treeListEq_length (l r : List Tree) (h : treeListEq l r = true) : l.length = r.length := by
  induction l generalizing r with
  | nil =>
    cases r with
    | nil => rfl
    | cons _ _ => simp [treeListEq] at h
  | cons a as ih =>
    cases r with
    | nil => simp [treeListEq] at h
    | cons b bs =>
      simp only [treeListEq, Bool.and_eq_true] at h
      simp [ih bs h.2]

/-- `cmp_base`, :3040-3058, for an item comparison with the meaning `itemEq`. -/
theorem cmpBase_spec (m : Mem) (fmt : Char) (unp : Option (Unpacker × Unpacker)) (g h : Int → Item)
    (he : ∀ p q, unpackCmp m p q fmt unp = .ok (itemEq (g p) (h q)))
    (ps qs : Int) (psub qsub : Option (List Int)) (n : Nat) (p q : Int) :
    cmpBase m fmt unp ps qs psub qsub n p q =
      .ok (treeListEq ((walk ps n p).map fun a => .leaf (g (adjustPtr m a psub 0)))
        ((walk qs n q).map fun a => .leaf (h (adjustPtr m a qsub 0)))) := by
  induction n generalizing p q with
  | zero => rfl
  | succ n ih =>
    simp only [cmpBase, he, walk, List.map_cons, treeListEq, treeEq, bind, Except.bind]
    cases hE : itemEq (g (adjustPtr m p psub 0)) (h (adjustPtr m q qsub 0)) with
    | false => rfl
    | true => simpa using ih (p + ps) (q + qs)

/-- The loop of `cmp_rec`, :3084-3093. -/
theorem cmpLoop_spec (ps qs : Int) (body : Int → Int → Py Bool) (F G : Int → Tree)
    (hb : ∀ p q, body p q = .ok (treeEq (F p) (G q))) (n : Nat) (p q : Int) :
    cmpLoop ps qs body n p q = .ok (treeListEq ((walk ps n p).map F) ((walk qs n q).map G)) := by
  induction n generalizing p q with
  | zero => rfl
  | succ n ih =>
    simp only [cmpLoop, hb, walk, List.map_cons, treeListEq, bind, Except.bind]
    cases hE : treeEq (F p) (G q) with
    | false => rfl
    | true => simpa using ih (p + ps) (q + qs)

/-- `cmp_rec`, :3062-3096, on shapes that `equiv_shape` accepts. -/
theorem cmpRec_spec (m : Mem) (fmt : Char) (unp : Option (Unpacker × Unpacker)) (g h : Int → Item)
    (he : ∀ p q, unpackCmp m p q fmt unp = .ok (itemEq (g p) (h q))) (sh sh' : List Int)
    (hne : sh ≠ []) (hlen : sh.length = sh'.length) (hs : shapeLoop sh sh' = true)
    (pst qst : List Int) (psub qsub : Option (List Int)) (p q : Int) :
    cmpRec m fmt unp sh pst psub qst qsub p q =
      .ok (treeEq (treeOf m g sh pst psub p) (treeOf m h sh' qst qsub q)) := by
  induction sh generalizing sh' pst qst psub qsub p q with
  | nil => exact absurd rfl hne
  | cons n xs ih =>
    match sh', hlen, hs with
    | n' :: xs', hlen, hs =>
      simp only [shapeLoop] at hs
      have hnn : n = n' := by
        by_cases hc : n = n'
        · exact hc
        · simp [hc] at hs
      subst hnn
      match xs, xs', hlen, hs, ih with
      | [], [], _, _, _ =>
        simp only [cmpRec, treeOf, treeEq]
        exact cmpBase_spec m fmt unp g h he _ _ _ _ _ _ _
      | x :: xs, x' :: xs', hlen, hs, ih =>
        simp only [cmpRec, treeOf, treeEq]
        by_cases hz : n.toNat = 0
        · rw [hz]
          rfl
        · have hn0 : n ≠ 0 := by
            intro e
            rw [e] at hz
            exact hz rfl
          have htail : shapeLoop (x :: xs) (x' :: xs') = true := by
            simpa [hn0] using hs
          exact cmpLoop_spec _ _ _
            (fun p' => treeOf m g (x :: xs) (pst.drop 1) (subTail psub) (adjustPtr m p' psub 0))
            (fun q' => treeOf m h (x' :: xs') (qst.drop 1) (subTail qsub) (adjustPtr m q' qsub 0))
            (fun p' q' => ih (x' :: xs') (by simp) (by simpa using hlen) htail _ _ _ _ _ _) _ _ _

/-- A shape `equiv_shape` refuses is a different nested list, when the number of dimensions is
the same. -/
theorem tree_ne_of_shape (m : Mem) (g h : Int → Item) (sh sh' : List Int) (hne : sh ≠ [])
    (hlen : sh.length = sh'.length) (hn : ∀ x ∈ sh, 0 ≤ x) (hn' : ∀ x ∈ sh', 0 ≤ x)
    (hs : shapeLoop sh sh' = false) (pst qst : List Int) (psub qsub : Option (List Int)) (p q : Int) :
    treeEq (treeOf m g sh pst psub p) (treeOf m h sh' qst qsub q) = false := by
  induction sh generalizing sh' pst qst psub qsub p q with
  | nil => exact absurd rfl hne
  | cons n xs ih =>
    match sh', hlen, hs, hn' with
    | n' :: xs', hlen, hs, hn' =>
      have h0 : 0 ≤ n := hn n (by simp)
      have h0' : 0 ≤ n' := hn' n' (by simp)
      simp only [shapeLoop] at hs
      have long : n ≠ n' → ∀ (F G : Int → Tree) (a b c d : Int),
          treeListEq ((walk a n.toNat b).map F) ((walk c n'.toNat d).map G) = false := by
        intro hc F G a b c d
        cases hE : treeListEq ((walk a n.toNat b).map F) ((walk c n'.toNat d).map G) with
        | false => rfl
        | true =>
          have := treeListEq_length _ _ hE
          simp only [List.length_map, walk_length] at this
          omega
      match xs, xs', hlen, hs, ih with
      | [], [], _, hs, _ =>
        have hc : n ≠ n' := by
          intro e
          subst e
          simp [shapeLoop] at hs
        simp only [treeOf, treeEq]
        exact long hc _ _ _ _ _ _
      | x :: xs, x' :: xs', hlen, hs, ih =>
        simp only [treeOf, treeEq]
        by_cases hc : n = n'
        · subst hc
          have hz : n ≠ 0 := by
            intro e
            simp [e] at hs
          obtain ⟨k, hk⟩ : ∃ k, n.toNat = k + 1 := ⟨n.toNat - 1, by omega⟩
          rw [hk]
          simp only [walk, List.map_cons, treeListEq]
          rw [ih (x' :: xs') (by simp) (by simpa using hlen) (fun y hy => hn y (by simp [hy]))
            (fun y hy => hn' y (by simp [hy])) (by simpa [hz] using hs)]
          rfl
        · exact long hc _ _ _ _ _ _

/-! ## From memory to `==` -/

/-- A live view of one native format with its arrays: what `tolist` works on. The itemsize is
the format's, and the format is a C string, both type invariants of a buffer. -/
structure NativeView (st : St) (i : Nat) (c : Char) (sh strs : List Int) : Prop where
  live : baseInaccessible st i = false
  fmt : getNativeFmtchar ((st.mv i).view.format.getD []) = some (c, (st.mv i).view.itemsize)
  cstr : '\x00' ∉ (st.mv i).view.format.getD []
  rank : sh.length = (st.mv i).view.ndim
  shape : sh ≠ [] → (st.mv i).view.shape = some sh
  strides : sh ≠ [] → (st.mv i).view.strides = some strs
  nonneg : ∀ x ∈ sh, 0 ≤ x

/-- A format `get_native_fmtchar` accepts is one character, with or without `@`. -/
theorem native_shape (f : List Char) (c : Char) (s : Int) (h : getNativeFmtchar f = some (c, s))
    (hz : '\x00' ∉ f) : (f = [c] ∨ f = ['@', c]) ∧ fmtSize c = s ∧ nativeChar c = true := by
  have hn := nativeChar_of_fmtchar _ _ _ h
  unfold getNativeFmtchar at h
  dsimp only at h
  split at h
  · rename_i hat
    match f, hat, hz with
    | [], hat, _ => simp [cc] at hat
    | a :: rest, hat, hz =>
      simp only [cc, List.getD_cons_zero] at hat
      subst hat
      simp only [List.drop_succ_cons, List.drop_zero] at h
      split at h
      · rename_i hc
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        match rest, hc, hz with
        | [], hc, _ => simp [cc, fmtSize] at hc
        | [b], _, _ => exact ⟨Or.inr rfl, rfl, hn⟩
        | b :: d :: r, hc, hz =>
          have : d = '\x00' := by simpa [cc] using hc.2
          subst this
          simp at hz
      · simp at h
  · split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      match f, hc, hz with
      | [], hc, _ => simp [cc, fmtSize] at hc
      | [b], _, _ => exact ⟨Or.inl rfl, rfl, hn⟩
      | b :: d :: r, hc, hz =>
        have : d = '\x00' := by simpa [cc] using hc.2
        subst this
        simp at hz
    · simp at h

theorem adjustFmt_native (v : Buf) (c : Char) (hn : nativeChar c = true)
    (h : v.format.getD [] = [c] ∨ v.format.getD [] = ['@', c]) : adjustFmt v = .ok [c] := by
  have h0 : c ≠ '\x00' := by
    intro e
    rw [e] at hn
    exact absurd hn (by decide)
  have h1 : c ≠ '@' := by
    intro e
    rw [e] at hn
    exact absurd hn (by decide)
  unfold adjustFmt
  dsimp only
  rcases h with h | h <;> rw [h] <;> simp [cc, h0, h1]

macro "ni_tac" : tactic => `(tactic| first
  | (simp [unpackRaw, cc, structItem, rdS, rdU, rdBytes_length, unpackToBool, decLE_one]; done)
  | (simp [unpackRaw, cc, structItem, rdS, rdU, rdBytes, decLE, unpackToBool]; done))

/-- One native code, compiled by `Struct` and read by `unpack_single`, is one item. -/
theorem native_item (c : Char) (h : nativeChar c = true) :
    ∃ (k : Nat), k = (fmtSize c).toNat ∧ c ≠ 's' ∧ c ≠ 'p' ∧
      structGetUnpacker [c] (fmtSize c) = .ok ⟨⟨false, [(c, 1, k, 0)], k⟩, fmtSize c⟩ ∧
      structGetUnpacker ['@', c] (fmtSize c) = .ok ⟨⟨false, [(c, 1, k, 0)], k⟩, fmtSize c⟩ ∧
      ∀ m p, unpackRaw m p [c] = .ok (structItem false c (rdBytes m p k)) := by
  unfold nativeChar at h
  split at h
  all_goals first
    | exact ⟨1, rfl, by decide, by decide, rfl, rfl, fun m p => by ni_tac⟩
    | exact ⟨2, rfl, by decide, by decide, rfl, rfl, fun m p => by ni_tac⟩
    | exact ⟨4, rfl, by decide, by decide, rfl, rfl, fun m p => by ni_tac⟩
    | exact ⟨8, rfl, by decide, by decide, rfl, rfl, fun m p => by ni_tac⟩
    | (simp at h)

/-- The item comparison, fast or through `struct`, is `==` of the items `tolist` shows. -/
def itemOf (m : Mem) (c : Char) (p : Int) : Item := structItem false c (rdBytes m p (fmtSize c).toNat)

theorem struct_cmp (m : Mem) (cv cw : Char) (kv kw : Nat) (hkv : kv = (fmtSize cv).toNat)
    (hkw : kw = (fmtSize cw).toNat) (hv : cv ≠ 's' ∧ cv ≠ 'p') (hw : cw ≠ 's' ∧ cw ≠ 'p') (p q : Int) :
    structUnpackCmp m p q ⟨⟨false, [(cv, 1, kv, 0)], kv⟩, fmtSize cv⟩ ⟨⟨false, [(cw, 1, kw, 0)], kw⟩, fmtSize cw⟩ =
      .ok (itemEq (itemOf m cv p) (itemOf m cw q)) := by
  subst hkv hkw
  simp only [structUnpackCmp, structUnpackSingle_native m _ cv _ _ rfl hv,
    structUnpackSingle_native m _ cw _ _ rfl hw, bind, Except.bind, pure, Except.pure, structResultEq,
    itemOf]

theorem fast_cmp (m : Mem) (c : Char) (h : nativeChar c = true) (p q : Int) :
    unpackCmp m p q c none = .ok (itemEq (itemOf m c p) (itemOf m c q)) := by
  obtain ⟨k, hk, h1, h2, h3, -, -⟩ := native_item c h
  obtain ⟨u, hu, e⟩ := cmpFastStruct_proven m p q c h
  rw [h3] at hu
  simp only [Except.ok.injEq] at hu
  subst hu
  rw [unpackCmp_none, e]
  exact struct_cmp m c c k k hk hk ⟨h1, h2⟩ ⟨h1, h2⟩ p q

/-- The result of `tolist`: a scalar for 0 dimensions, a nested list otherwise. -/
def viewTree (m : Mem) (c : Char) (b : Buf) (sh strs : List Int) : Tree :=
  if sh = [] then .leaf (itemOf m c b.buf) else treeOf m (itemOf m c) sh strs b.suboffsets b.buf

theorem tolist_viewTree (st : St) (i : Nat) (c : Char) (sh strs : List Int) (h : NativeView st i c sh strs) :
    memoryviewTolist i st = (.ok (viewTree st.mem c (st.mv i).view sh strs), st) := by
  obtain ⟨hf, hs, hn⟩ := native_shape _ _ _ h.fmt h.cstr
  have ha := adjustFmt_native _ c hn hf
  obtain ⟨k, hk, -, -, -, -, hu⟩ := native_item c hn
  have hg : ∀ p, unpackRaw st.mem p [c] = .ok (itemOf st.mem c p) := fun p => by
    rw [hu, hk]
    rfl
  unfold viewTree
  by_cases he : sh = []
  · rw [if_pos he]
    have h0 : (st.mv i).view.ndim = 0 := by
      rw [← h.rank, he]
      rfl
    simp only [memoryviewTolist, M.bind_app, checkReleased_ok _ _ h.live, M.get, M.lift, ha, h0, ↓reduceIte,
      unpackSingle_live _ _ _ _ h.live, hg, M.pure_app]
  · rw [if_neg he]
    exact memoryviewTolist_eq st i c sh strs _ h.live ha hg (h.shape he) (h.strides he) he h.rank

/-- The two cases of `equiv_shape` on views of the same `ndim`. -/
theorem equivShape_views (st : St) (v w : Nat) (cv cw : Char) (shv shw stv stw : List Int)
    (hv : NativeView st v cv shv stv) (hw : NativeView st w cw shw stw)
    (hnd : (st.mv v).view.ndim = (st.mv w).view.ndim) :
    equivShape (st.mv v).view (st.mv w).view = shapeLoop shv shw := by
  unfold equivShape
  rw [hnd]
  simp only [beq_self_eq_true, Bool.true_and]
  by_cases he : shv = []
  · subst he
    have h0 : (st.mv w).view.ndim = 0 := by
      rw [← hnd, ← hv.rank]
      rfl
    simp [h0, shapeLoop]
  · have hne : shw ≠ [] := by
      intro e
      subst e
      apply he
      apply List.length_eq_zero_iff.1
      rw [hv.rank, hnd, ← hw.rank]
      rfl
    rw [hv.shape he, hw.shape hne, ← hnd, ← hv.rank]
    simp only [Option.getD_some, List.take_length]

/-- The walk `memory_richcompare` picks by `ndim`, on an item comparison that is `==`. -/
theorem run_spec (st : St) (v w : Nat) (cv cw : Char) (shv shw stv stw : List Int) (fmt : Char)
    (unp : Option (Unpacker × Unpacker))
    (hv : NativeView st v cv shv stv) (hw : NativeView st w cw shw stw)
    (hnd : (st.mv v).view.ndim = (st.mv w).view.ndim)
    (hs : shapeLoop shv shw = true)
    (he : ∀ p q, unpackCmp st.mem p q fmt unp = .ok (itemEq (itemOf st.mem cv p) (itemOf st.mem cw q))) :
    (if (st.mv v).view.ndim = 0 then unpackCmp st.mem (st.mv v).view.buf (st.mv w).view.buf fmt unp
     else if (st.mv v).view.ndim = 1 then
       cmpBase st.mem fmt unp (((st.mv v).view.strides.getD []).getD 0 0) (((st.mv w).view.strides.getD []).getD 0 0)
         (st.mv v).view.suboffsets (st.mv w).view.suboffsets (((st.mv v).view.shape.getD []).getD 0 0).toNat
         (st.mv v).view.buf (st.mv w).view.buf
     else
       cmpRec st.mem fmt unp ((st.mv v).view.shape.getD []) ((st.mv v).view.strides.getD [])
         (st.mv v).view.suboffsets ((st.mv w).view.strides.getD []) (st.mv w).view.suboffsets
         (st.mv v).view.buf (st.mv w).view.buf) =
    .ok (treeEq (viewTree st.mem cv (st.mv v).view shv stv) (viewTree st.mem cw (st.mv w).view shw stw)) := by
  have hlen : shv.length = shw.length := by rw [hv.rank, hnd, hw.rank]
  unfold viewTree
  by_cases he0 : shv = []
  · have he1 : shw = [] := by
      subst he0
      exact List.length_eq_zero_iff.1 hlen.symm
    have h0 : (st.mv v).view.ndim = 0 := by
      rw [← hv.rank, he0]
      rfl
    rw [if_pos h0, if_pos he0, if_pos he1]
    simp only [he, treeEq]
  · have hne1 : shw ≠ [] := by
      intro e
      subst e
      exact he0 (List.length_eq_zero_iff.1 hlen)
    rw [if_neg he0, if_neg hne1, hv.shape he0, hv.strides he0, hw.strides hne1]
    have hn0 : ¬ (st.mv v).view.ndim = 0 := by
      rw [← hv.rank]
      intro e
      exact he0 (List.length_eq_zero_iff.1 e)
    rw [if_neg hn0]
    simp only [Option.getD_some]
    by_cases h1 : (st.mv v).view.ndim = 1
    · rw [if_pos h1]
      rw [h1] at hnd
      have l1 : shv.length = 1 := by rw [hv.rank, h1]
      have l2 : shw.length = 1 := by rw [← hlen, l1]
      obtain ⟨n, rfl⟩ := List.length_eq_one_iff.1 l1
      obtain ⟨n', rfl⟩ := List.length_eq_one_iff.1 l2
      have hnn : n = n' := by
        by_cases hc : n = n'
        · exact hc
        · simp [shapeLoop, hc] at hs
      subst hnn
      simp only [treeOf, treeEq, List.getD_cons_zero]
      exact cmpBase_spec st.mem fmt unp _ _ he _ _ _ _ _ _ _
    · rw [if_neg h1]
      exact cmpRec_spec st.mem fmt unp _ _ he shv shw he0 hlen hs _ _ _ _ _ _

theorem compareBufs_views (st : St) (v w : Nat) (cv cw : Char) (shv shw stv stw : List Int)
    (hv : NativeView st v cv shv stv) (hw : NativeView st w cw shw stw)
    (hnd : (st.mv v).view.ndim = (st.mv w).view.ndim) (hns : cv = cw ∨ st.noStruct = false) :
    compareBufs st.mem st.noStruct (st.mv v).view (st.mv w).view =
      .ok (treeEq (viewTree st.mem cv (st.mv v).view shv stv) (viewTree st.mem cw (st.mv w).view shw stw)) := by
  have hlen : shv.length = shw.length := by rw [hv.rank, hnd, hw.rank]
  have hes := equivShape_views st v w cv cw shv shw stv stw hv hw hnd
  obtain ⟨hfv, hsv, hnv⟩ := native_shape _ _ _ hv.fmt hv.cstr
  obtain ⟨hfw, hsw, hnw⟩ := native_shape _ _ _ hw.fmt hw.cstr
  cases hloop : shapeLoop shv shw with
  | false =>
    have hne : shv ≠ [] := by
      intro e
      rw [e] at hloop
      simp [shapeLoop] at hloop
    have hne' : shw ≠ [] := by
      intro e
      subst e
      exact hne (List.length_eq_zero_iff.1 hlen)
    have ht := tree_ne_of_shape st.mem (itemOf st.mem cv) (itemOf st.mem cw) shv shw hne hlen hv.nonneg
      hw.nonneg hloop stv stw (st.mv v).view.suboffsets (st.mv w).view.suboffsets
      (st.mv v).view.buf (st.mv w).view.buf
    unfold viewTree
    rw [if_neg hne, if_neg hne', ht]
    simp only [compareBufs, hes, hloop, Bool.not_false, ↓reduceIte]
  | true =>
    have hcv : cv ≠ '_' := by
      intro e
      rw [e] at hnv
      exact absurd hnv (by decide)
    have hcw : cw ≠ '_' := by
      intro e
      rw [e] at hnw
      exact absurd hnw (by decide)
    obtain ⟨kv, hkv, s1, s2, u1, u2, -⟩ := native_item cv hnv
    obtain ⟨kw, hkw, s3, s4, u3, u4, -⟩ := native_item cw hnw
    have up1 : ∀ h : st.noStruct = false, unpackerOf st.noStruct ((st.mv v).view.format.getD []) (st.mv v).view.itemsize =
        .ok ⟨⟨false, [(cv, 1, kv, 0)], kv⟩, fmtSize cv⟩ := by
      intro h0
      rw [unpackerOf, if_neg (by simp [h0]), ← hsv]
      rcases hfv with h | h <;> rw [h]
      · exact u1
      · exact u2
    have up2 : ∀ h : st.noStruct = false, unpackerOf st.noStruct ((st.mv w).view.format.getD []) (st.mv w).view.itemsize =
        .ok ⟨⟨false, [(cw, 1, kw, 0)], kw⟩, fmtSize cw⟩ := by
      intro h0
      rw [unpackerOf, if_neg (by simp [h0]), ← hsw]
      rcases hfw with h | h <;> rw [h]
      · exact u3
      · exact u4
    simp only [compareBufs, hes, hloop, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hv.fmt, hw.fmt]
    by_cases hc : cv = cw
    · subst hc
      simp only [hcv, or_self, ne_eq, not_true_eq_false, ↓reduceIte]
      exact run_spec st v w cv cv shv shw stv stw cv none hv hw hnd hloop (fun p q => fast_cmp st.mem cv hnv p q)
    · have hn0 : st.noStruct = false := hns.resolve_left hc
      simp only [hc, ne_eq, not_false_eq_true, or_true, ↓reduceIte, up1 hn0, up2 hn0]
      refine run_spec st v w cv cw shv shw stv stw '_' _ hv hw hnd hloop (fun p q => ?_)
      exact struct_cmp st.mem cv cw kv kw hkv hkw ⟨s1, s2⟩ ⟨s3, s4⟩ p q

/-- `v == w` is `v.tolist() == w.tolist()` for two live views of native formats, of any dimension,
shape, strides and suboffsets, equal or different formats, floats included: `cmp_base` and
`cmp_rec` compare what `tolist` shows, the `switch` and `struct` paths agree, and a shape
`equiv_shape` refuses is a list of a different shape. With a different `ndim` they are not equal,
though the lists can be: `(0,)` and `(0, 3)` both give `[]` (Doc/library/stdtypes.rst, "their
shapes are equivalent"). Hypotheses: `NativeView`, which is `tolist` succeeding; for two different
formats, `struct` can be imported (`CmpImportFails` is the other case). -/
def CmpIsTolist : Prop :=
  ∀ (st : St) (v w : Nat) (cv cw : Char) (shv shw stv stw : List Int),
    NativeView st v cv shv stv → NativeView st w cw shw stw → (cv = cw ∨ st.noStruct = false) →
    ∃ tv tw, memoryviewTolist v st = (.ok tv, st) ∧ memoryviewTolist w st = (.ok tw, st) ∧
      memoryRichcompare v (.view w) .eq st =
        (.ok (some ((st.mv v).view.ndim == (st.mv w).view.ndim && treeEq tv tw)), st)

theorem cmpIsTolist_proven : CmpIsTolist := by
  intro st v w cv cw shv shw stv stw hv hw hns
  refine ⟨_, _, tolist_viewTree st v cv shv stv hv, tolist_viewTree st w cw shw stw hw, ?_⟩
  have e : compareBufs st.mem st.noStruct (st.mv v).view (st.mv w).view =
      .ok ((st.mv v).view.ndim == (st.mv w).view.ndim &&
        treeEq (viewTree st.mem cv (st.mv v).view shv stv) (viewTree st.mem cw (st.mv w).view shw stw)) := by
    by_cases hnd : (st.mv v).view.ndim = (st.mv w).view.ndim
    · rw [compareBufs_views st v w cv cw shv shw stv stw hv hw hnd hns]
      simp [hnd]
    · have : equivShape (st.mv v).view (st.mv w).view = false := by
        simp [equivShape, hnd]
      simp [compareBufs, this, hnd]
  simp only [memoryRichcompare, memoryRichEqual, M.bind_app, M.get, hv.live, Bool.false_eq_true, ↓reduceIte,
    reduceCtorEq, hw.live, M.lift, e, M.pure_app, Option.map_some]

/-! ## Formats that are not native -/

/-- `cmp_base`, for any item comparison: every pair of items, until the first unequal one. -/
theorem cmpBase_all (m : Mem) (fmt : Char) (unp : Option (Unpacker × Unpacker)) (e : Int → Int → Bool)
    (he : ∀ p q, unpackCmp m p q fmt unp = .ok (e p q))
    (ps qs : Int) (psub qsub : Option (List Int)) (n : Nat) (p q : Int) :
    cmpBase m fmt unp ps qs psub qsub n p q =
      .ok (((walk ps n p).zip (walk qs n q)).all fun x =>
        e (adjustPtr m x.1 psub 0) (adjustPtr m x.2 qsub 0)) := by
  induction n generalizing p q with
  | zero => rfl
  | succ n ih =>
    simp only [cmpBase, he, walk, List.zip_cons_cons, List.all_cons, bind, Except.bind]
    cases hE : e (adjustPtr m p psub 0) (adjustPtr m q qsub 0) with
    | false => rfl
    | true => simpa using ih (p + ps) (q + qs)

/-- The values `struct.unpack_from` gives for one item. -/
def unpackAt (m : Mem) (u : Unpacker) (p : Int) : List Item :=
  u.fmt.codes.flatMap (unpackCode u.fmt.big (rdBytes m p u.itemsize.toNat))

/-- `memory_richcompare` on 1-D views when a format is not native, as `<i` or `2B`, or the two
differ: `get_native_fmtchar` fails, so both go through `struct` (@3.14.7:3140-3158), and `v == w` is true
exactly when each pair of unpacked items agrees under `struct_unpack_cmp`, @3.14.7:2931-2956, which
compares one-value tuples by that value and longer tuples as tuples. Hypotheses: the case; both
formats compile, and each fits its itemsize, otherwise `unpack_from` raises. -/
def CmpNonNative : Prop :=
  ∀ (m : Mem) (vv ww : Buf) (up uq : Unpacker) (n : Int),
    vv.ndim = 1 → ww.ndim = 1 → vv.shape = some [n] → ww.shape = some [n] →
    (getNativeFmtchar (vv.format.getD []) = none ∨ getNativeFmtchar (ww.format.getD []) = none) →
    structGetUnpacker (vv.format.getD []) vv.itemsize = .ok up →
    structGetUnpacker (ww.format.getD []) ww.itemsize = .ok uq →
    up.fmt.size ≤ up.itemsize.toNat → uq.fmt.size ≤ uq.itemsize.toNat →
    compareBufs m false vv ww = .ok
      (((walk ((vv.strides.getD []).getD 0 0) n.toNat vv.buf).zip
        (walk ((ww.strides.getD []).getD 0 0) n.toNat ww.buf)).all fun x =>
          structResultEq (unpackAt m up (adjustPtr m x.1 vv.suboffsets 0))
            (unpackAt m uq (adjustPtr m x.2 ww.suboffsets 0)))

theorem structUnpackSingle_fits (m : Mem) (u : Unpacker) (p : Int) (h : u.fmt.size ≤ u.itemsize.toNat) :
    structUnpackSingle m p u = .ok (unpackAt m u p) := by
  simp only [structUnpackSingle, structUnpackFrom, rdBytes_length, unpackAt]
  rw [if_neg (by omega)]

theorem cmpNonNative_proven : CmpNonNative := by
  intro m vv ww up uq n h1 h2 h3 h4 hn hu hw hsu hsw
  have hs : equivShape vv ww = true := by
    simp [equivShape, h1, h2, h3, h4, shapeLoop]
  have hm : ∀ p q, unpackCmp m p q '_' (some (up, uq)) =
      .ok (structResultEq (unpackAt m up p) (unpackAt m uq q)) := by
    intro p q
    simp only [unpackCmp, structUnpackCmp, structUnpackSingle_fits m _ _ hsu,
      structUnpackSingle_fits m _ _ hsw, bind, Except.bind, pure, Except.pure]
  rcases hn with h | h
  · simp only [compareBufs, hs, Bool.not_true, Bool.false_eq_true, ↓reduceIte, h, eq_self, true_or, unpackerOf,
      hu, hw, h1, Nat.one_ne_zero, h3, Option.getD_some, List.getD_cons_zero]
    exact cmpBase_all m '_' _ _ hm _ _ _ _ _ _ _
  · simp only [compareBufs, hs, Bool.not_true, Bool.false_eq_true, ↓reduceIte, h, eq_self, true_or, or_true,
      unpackerOf, hu, hw, h1, Nat.one_ne_zero, h3, Option.getD_some, List.getD_cons_zero]
    exact cmpBase_all m '_' _ _ hm _ _ _ _ _ _ _

/-! ## `import struct` fails -/

/-- `fix_struct_error_int`, @3.14.7:2917-2928: anything from `struct` itself means "not equal" and is
cleared; `ImportError`, `MemoryError` and their subclasses are real errors and pass through. -/
def FixStructRules : Prop :=
  ∀ (msg : String),
    fixStructError (structError msg) = .ok false ∧
    fixStructError (.valueError msg) = .ok false ∧
    fixStructError importStruct = .error importStruct ∧
    fixStructError (.named "ImportError" msg) = .error (.named "ImportError" msg) ∧
    fixStructError (.named "ModuleNotFoundError" msg) = .error (.named "ModuleNotFoundError" msg) ∧
    fixStructError (.named "ISub" msg) = .error (.named "ISub" msg) ∧
    fixStructError (.named "MemoryError" msg) = .error (.named "MemoryError" msg) ∧
    fixStructError (.named "MSub" msg) = .error (.named "MSub" msg)

theorem fixStructRules_proven : FixStructRules := by
  intro msg
  simp [fixStructError, structError, importStruct, excMatches, PyExc.className, excBases]

/-- `memory_richcompare` with `sys.modules['struct'] = None`, @3.14.7:3144-3158: two views of the same native
format take the `switch` and never import `struct`, so `==` is unchanged; when the formats differ or
one is not native, `struct_get_unpacker` fails, @3.14.7:2084-2086, and `fix_struct_error_int` lets the
`ModuleNotFoundError` out of `==`, where a bad format would be "not equal". Hypotheses: the shapes
pass `equiv_shape`, the case. -/
def CmpImportFails : Prop :=
  ∀ (m : Mem) (vv ww : Buf), equivShape vv ww = true →
    (getNativeFmtchar (vv.format.getD []) = none ∨ getNativeFmtchar (ww.format.getD []) = none →
      compareBufs m true vv ww = .error importStruct) ∧
    (∀ c c' s s', getNativeFmtchar (vv.format.getD []) = some (c, s) →
      getNativeFmtchar (ww.format.getD []) = some (c', s') →
      (c ≠ c' → compareBufs m true vv ww = .error importStruct) ∧
      (c = c' → nativeChar c = true → compareBufs m true vv ww = compareBufs m false vv ww))

theorem cmpImportFails_proven : CmpImportFails := by
  intro m vv ww hs
  refine ⟨fun h => ?_, fun c c' s s' h1 h2 => ⟨fun hc => ?_, fun hc hn => ?_⟩⟩
  · rcases h with h | h
    · simp [compareBufs, hs, h, unpackerOf, fixStructError, importStruct, excMatches, PyExc.className, excBases]
    · simp [compareBufs, hs, h, unpackerOf, fixStructError, importStruct, excMatches, PyExc.className, excBases]
  · simp [compareBufs, hs, h1, h2, hc, unpackerOf, fixStructError, importStruct, excMatches, PyExc.className, excBases]
  · subst hc
    have h_ : c ≠ '_' := by
      intro e
      rw [e] at hn
      exact absurd hn (by decide)
    simp [compareBufs, hs, h1, h2, h_]

/-! ## `equiv_format`, `equiv_shape`, `equiv_structure`, `adjust_fmt` -/

/-- The same shape up to and including the first dimension of length 0, or everywhere. -/
def ShapeEquiv (a b : List Int) : Prop :=
  ∃ i, i ≤ a.length ∧ a.take i = b.take i ∧ (∀ x ∈ a.take i, x ≠ 0) ∧
    (i = a.length ∨ (a.getD i 1 = 0 ∧ b.getD i 1 = 0))

theorem shapeLoop_iff (a b : List Int) (h : a.length = b.length) :
    shapeLoop a b = true ↔ ShapeEquiv a b := by
  induction a generalizing b with
  | nil =>
    have : b = [] := List.length_eq_zero_iff.1 h.symm
    subst this
    exact ⟨fun _ => ⟨0, by simp, by simp, by simp, Or.inl rfl⟩, fun _ => rfl⟩
  | cons x xs ih =>
    match b, h with
    | y :: ys, h =>
      have hl : xs.length = ys.length := by simpa using h
      simp only [shapeLoop]
      by_cases hc : x = y
      · subst hc
        by_cases h0 : x = 0
        · subst h0
          constructor
          · intro _
            exact ⟨0, by simp, by simp, by simp, Or.inr (by simp)⟩
          · intro _
            simp
        · simp only [ne_eq, not_true_eq_false, ↓reduceIte, h0, ih ys hl]
          constructor
          · rintro ⟨i, h1, h2, h3, h4⟩
            refine ⟨i + 1, by simp; omega, by simp [h2], ?_, ?_⟩
            · intro z hz
              simp only [List.take_succ_cons, List.mem_cons] at hz
              rcases hz with rfl | hz
              · exact h0
              · exact h3 z hz
            · rcases h4 with h4 | h4
              · exact Or.inl (by simp [h4])
              · exact Or.inr (by simpa using h4)
          · rintro ⟨i, h1, h2, h3, h4⟩
            cases i with
            | zero =>
              rcases h4 with h4 | h4
              · simp at h4
              · exact absurd (by simpa using h4.1) h0
            | succ i =>
              refine ⟨i, by simp at h1; omega, by simpa using h2, ?_, ?_⟩
              · intro z hz
                exact h3 z (by simp [hz])
              · rcases h4 with h4 | h4
                · exact Or.inl (by simpa using h4)
                · exact Or.inr (by simpa using h4)
      · simp only [ne_eq, hc, not_false_eq_true, ↓reduceIte, reduceCtorEq, false_iff]
        rintro ⟨i, h1, h2, h3, h4⟩
        cases i with
        | zero =>
          rcases h4 with h4 | h4
          · simp at h4
          · exact hc (by simp at h4; omega)
        | succ i =>
          simp only [List.take_succ_cons, List.cons.injEq] at h2
          exact hc h2.1

/-- `equiv_structure`, @3.14.7:327-339, with `equiv_format`, @3.14.7:287-305, and `equiv_shape`, @3.14.7:307-323: the
assignment `dest[...] = src` goes ahead exactly if the formats are the same apart from a leading
`@`, the item sizes are equal, the dimensions are equal, and the shapes are equal up to the first
dimension of length 0, past which they can differ. Otherwise `ValueError`. Hypothesis: the shape
arrays have `ndim` entries, a type invariant. -/
def EquivRules : Prop :=
  ∀ (d s : Buf), (d.shape.getD []).length = d.ndim → (s.shape.getD []).length = s.ndim →
    let ok := stripAt (d.format.getD []) = stripAt (s.format.getD []) ∧ d.itemsize = s.itemsize ∧
      d.ndim = s.ndim ∧ ShapeEquiv (d.shape.getD []) (s.shape.getD [])
    (ok → equivStructure d s = .ok ()) ∧
    (¬ ok → equivStructure d s =
      .error (.valueError "memoryview assignment: lvalue and rvalue have different structures"))

theorem equivRules_proven : EquivRules := by
  intro d s h1 h2
  dsimp only
  have hb : (equivFormat d s && equivShape d s) = true ↔
      (stripAt (d.format.getD []) = stripAt (s.format.getD []) ∧ d.itemsize = s.itemsize ∧
        d.ndim = s.ndim ∧ ShapeEquiv (d.shape.getD []) (s.shape.getD [])) := by
    simp only [equivFormat, equivShape, Bool.and_eq_true, beq_iff_eq]
    rw [← h1, List.take_length]
    constructor
    · rintro ⟨⟨a, b⟩, c, e⟩
      exact ⟨a, b, c, (shapeLoop_iff _ _ (by omega)).1 e⟩
    · rintro ⟨a, b, c, e⟩
      exact ⟨⟨a, b⟩, c, (shapeLoop_iff _ _ (by omega)).2 e⟩
  constructor
  · intro h
    have hf : equivFormat d s = true ∧ equivShape d s = true := by simpa using hb.2 h
    simp [equivStructure, hf.1, hf.2]
  · intro h
    unfold equivStructure
    rw [if_pos]
    cases hf : equivFormat d s with
    | false => rfl
    | true =>
      cases hs : equivShape d s with
      | false => rfl
      | true =>
        exact absurd (hb.1 (by simp [hf, hs])) h

/-- `copy_single`, @3.14.7:404-432: `m[s] = x` re-checks the view after the Python code that got `x`'s
buffer (`CHECK_RELEASED_INT_AGAIN`, @3.14.7:407), and refuses a source of another structure, in that
order, writing nothing. Hypothesis: the view or the structures are as the case says. -/
def CopySingleRefuses : Prop :=
  ∀ (st : St) (self : Nat) (dest src : Buf),
    (baseInaccessible st self = true → copySingle self dest src st = (.error releasedError, st)) ∧
    (baseInaccessible st self = false → equivFormat dest src = false →
      copySingle self dest src st =
        (.error (.valueError "memoryview assignment: lvalue and rvalue have different structures"), st))

theorem copySingleRefuses_proven : CopySingleRefuses := by
  intro st self dest src
  constructor
  · intro h
    simp only [copySingle, M.bind_app, checkReleased_err _ _ h]
  · intro h1 h2
    simp [copySingle, M.bind_app, checkReleased_ok _ _ h1, M.lift, equivStructure, h2]

/-- `adjust_fmt`, @3.14.7:2152-2164: the format after an optional `@` must be one character, which it
returns, and anything else raises `NotImplementedError` naming the whole format. Formats are C
strings here. Hypothesis: no NUL in the format, a type invariant. -/
def AdjustFmtRules : Prop :=
  ∀ (v : Buf), '\x00' ∉ v.format.getD [] →
    let f := v.format.getD []
    let body := if f.head? = some '@' then f.drop 1 else f
    (body.length = 1 → adjustFmt v = .ok body) ∧
    (body.length ≠ 1 → adjustFmt v = .error (notImplError s!"memoryview: unsupported format {fmtText f}"))

theorem adjustFmtRules_proven : AdjustFmtRules := by
  intro v hz
  dsimp only
  generalize hf : v.format.getD [] = f at hz ⊢
  have hb : (if cc f 0 = '@' then f.drop 1 else f) = (if f.head? = some '@' then f.drop 1 else f) := by
    cases f with
    | nil => simp [cc]
    | cons a as => simp [cc]
  have hn : ∀ (b : List Char), '\x00' ∉ b →
      ((cc b 0 ≠ '\x00' ∧ cc b 1 = '\x00') ↔ b.length = 1) := by
    intro b hb0
    match b, hb0 with
    | [], _ => simp [cc]
    | [x], hb0 => simpa [cc] using fun e : x = '\x00' => hb0 (by simp [e])
    | x :: y :: r, hb0 =>
      have hy : y ≠ '\x00' := fun e => hb0 (by simp [e])
      simp [cc, hy]
  have hsub : '\x00' ∉ (if f.head? = some '@' then f.drop 1 else f) := by
    split
    · exact fun h => hz (List.mem_of_mem_drop h)
    · exact hz
  have hc := hn _ hsub
  unfold adjustFmt
  simp only [hf, hb]
  constructor
  · intro h
    rw [if_pos (hc.2 h)]
  · intro h
    rw [if_neg (fun e => h (hc.1 e))]

end PyLean.BytesObj.Mem
