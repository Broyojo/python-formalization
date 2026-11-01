import PyLean.TextLibs.ReCharset2

/-!
The compression of `_optimize_charset`: runs, the bitmap, and the two-level `BIGCHARSET`. Each form
answers what the charmap answers, and `CharsetPreserved` puts the steps together.
-/

namespace PyLean.TextLibs.Re

open PyLean

set_option linter.unusedSimpArgs false

/-! ### Runs -/

theorem cm_bang (cm : Array Bool) (q : Nat) (h : q < cm.size) : cm[q]! = cmAt cm q := by
  simp [cmAt, Array.getD_eq_getD_getElem?, h]

theorem cmFind_some (cm : Array Bool) (v : Bool) : ∀ (fuel q p : Nat), cmFind cm v fuel q = some p →
    q ≤ p ∧ p < cm.size ∧ cmAt cm p = v ∧ ∀ x, q ≤ x → x < p → cmAt cm x = !v := by
  intro fuel
  induction fuel with
  | zero => intro q p h; simp [cmFind] at h
  | succ fuel ih =>
    intro q p h
    simp only [cmFind] at h
    by_cases h1 : q ≥ cm.size
    · simp [h1] at h
    · simp only [h1, if_false] at h
      have hq : q < cm.size := by omega
      by_cases h2 : (cm[q]! == v) = true
      · simp only [h2, if_true, Option.some.injEq] at h
        subst h
        rw [cm_bang cm q hq] at h2
        exact ⟨Nat.le_refl _, hq, by simpa using h2, fun x h3 h4 => by omega⟩
      · simp only [h2, Bool.false_eq_true, if_false] at h
        obtain ⟨h3, h4, h5, h6⟩ := ih (q + 1) p h
        rw [cm_bang cm q hq] at h2
        refine ⟨by omega, h4, h5, fun x h7 h8 => ?_⟩
        by_cases h9 : x = q
        · subst h9
          cases hc : cmAt cm x <;> cases v <;> simp_all
        · exact h6 x (by omega) h8

theorem cmFind_none (cm : Array Bool) (v : Bool) : ∀ (fuel q : Nat), cm.size ≤ q + fuel →
    cmFind cm v fuel q = none → ∀ x, q ≤ x → x < cm.size → cmAt cm x = !v := by
  intro fuel
  induction fuel with
  | zero => intro q h _ x h1 h2; omega
  | succ fuel ih =>
    intro q h1 h x h2 h3
    simp only [cmFind] at h
    have hq : q < cm.size := by omega
    simp only [show ¬(q ≥ cm.size) by omega, if_false] at h
    by_cases h4 : (cm[q]! == v) = true
    · simp [h4] at h
    · simp only [h4, Bool.false_eq_true, if_false] at h
      by_cases h5 : x = q
      · subst h5
        rw [cm_bang cm x hq] at h4
        cases hc : cmAt cm x <;> cases v <;> simp_all
      · exact ih (q + 1) (by omega) h x (by omega) h3

/-- The runs so far hold the map below `q`. -/
def RunsOk (cm : Array Bool) (runs : List (Nat × Nat)) (q : Nat) : Prop :=
  (∀ r ∈ runs, r.1 < r.2) ∧
  ∀ x, x < q → (cmAt cm x = true ↔ ∃ r ∈ runs, r.1 ≤ x ∧ x < r.2)

/-- `# compress character map`: the runs are the map. -/
theorem cmRuns_spec (cm : Array Bool) : ∀ (fuel : Nat) (runs out : List (Nat × Nat)) (q : Nat),
    1 ≤ fuel → q ≤ cm.size → runs.length + fuel = 3 → (∀ r ∈ runs, r.2 ≤ q) → RunsOk cm runs q →
    cmRuns cm fuel runs q = some out →
    (∀ r ∈ out, r.1 < r.2 ∧ r.2 ≤ cm.size) ∧
      ∀ x, x < cm.size → (cmAt cm x = true ↔ ∃ r ∈ out, r.1 ≤ x ∧ x < r.2) := by
  intro fuel
  induction fuel with
  | zero => intro runs out q h; omega
  | succ fuel ih =>
    intro runs out q _ hq hlen hle hok h
    simp only [cmRuns] at h
    cases h1 : cmFind cm true cm.size q with
    | none =>
      rw [h1] at h
      simp only [Option.some.injEq] at h
      subst h
      have h2 := cmFind_none cm true _ q (by omega) h1
      refine ⟨fun r hr => ⟨hok.1 r hr, by have := hle r hr; omega⟩, fun x hx => ?_⟩
      by_cases h3 : x < q
      · exact hok.2 x h3
      · have h4 := h2 x (by omega) hx
        constructor
        · intro h5
          rw [h4] at h5
          cases h5
        · rintro ⟨r, h5, h6, h7⟩
          have := hle r h5
          omega
    | some p =>
      rw [h1] at h
      obtain ⟨h2, h3, h4, h5⟩ := cmFind_some cm true _ q p h1
      simp only at h
      by_cases h6 : runs.length ≥ 2
      · simp [h6] at h
      · simp only [h6, if_false] at h
        cases h7 : cmFind cm false cm.size p with
        | none =>
          rw [h7] at h
          simp only [Option.some.injEq] at h
          subst h
          have h8 := cmFind_none cm false _ p (by omega) h7
          refine ⟨fun r hr => ?_, fun x hx => ?_⟩
          · simp only [List.mem_append, List.mem_singleton] at hr
            rcases hr with hr | rfl
            · exact ⟨hok.1 r hr, by have := hle r hr; omega⟩
            · exact ⟨h3, Nat.le_refl _⟩
          · by_cases h9 : x < q
            · have h10 := hok.2 x h9
              constructor
              · intro h11
                obtain ⟨r, h12, h13⟩ := h10.1 h11
                exact ⟨r, by simp [h12], h13⟩
              · rintro ⟨r, h12, h13⟩
                simp only [List.mem_append, List.mem_singleton] at h12
                rcases h12 with h12 | rfl
                · exact h10.2 ⟨r, h12, h13⟩
                · simp only at h13
                  omega
            · by_cases h11 : x < p
              · have h12 := h5 x (by omega) h11
                simp only [Bool.not_true] at h12
                constructor
                · intro h13
                  rw [h12] at h13
                  cases h13
                · rintro ⟨r, h13, h14⟩
                  simp only [List.mem_append, List.mem_singleton] at h13
                  rcases h13 with h13 | rfl
                  · have := hle r h13
                    omega
                  · simp only at h14
                    omega
              · have h12 := h8 x (by omega) hx
                constructor
                · intro _
                  exact ⟨(p, cm.size), by simp, by simpa using by omega, hx⟩
                · intro _
                  simpa using h12
        | some q2 =>
          rw [h7] at h
          simp only at h
          obtain ⟨h8, h9, h10, h11⟩ := cmFind_some cm false _ p q2 h7
          have hpq : p < q2 := by
            by_cases hc : p = q2
            · subst hc
              rw [h4] at h10
              cases h10
            · omega
          refine ih (runs ++ [(p, q2)]) out q2 (by omega) (by omega) (by simp; omega) ?_ ⟨?_, ?_⟩ h
          · intro r hr
            simp only [List.mem_append, List.mem_singleton] at hr
            rcases hr with hr | rfl
            · have := hle r hr
              omega
            · exact Nat.le_refl _
          · intro r hr
            simp only [List.mem_append, List.mem_singleton] at hr
            rcases hr with hr | rfl
            · exact hok.1 r hr
            · exact hpq
          · intro x hx
            by_cases h12 : x < q
            · have h13 := hok.2 x h12
              constructor
              · intro h14
                obtain ⟨r, h15, h16⟩ := h13.1 h14
                exact ⟨r, by simp [h15], h16⟩
              · rintro ⟨r, h15, h16⟩
                simp only [List.mem_append, List.mem_singleton] at h15
                rcases h15 with h15 | rfl
                · exact h13.2 ⟨r, h15, h16⟩
                · simp only at h16
                  omega
            · by_cases h13 : x < p
              · have h14 := h5 x (by omega) h13
                simp only [Bool.not_true] at h14
                constructor
                · intro h15
                  rw [h14] at h15
                  cases h15
                · rintro ⟨r, h15, h16⟩
                  simp only [List.mem_append, List.mem_singleton] at h15
                  rcases h15 with h15 | rfl
                  · have := hle r h15
                    omega
                  · simp only at h16
                    omega
              · have h14 := h11 x (by omega) hx
                simp only [Bool.not_false] at h14
                constructor
                · intro _
                  exact ⟨(p, q2), by simp, by simpa using by omega, hx⟩
                · intro _
                  exact h14

def runItem (r : Nat × Nat) : CItem :=
  if r.2 - r.1 == 1 then .lit r.1 else .rng r.1 (r.2 - 1)

theorem runItem_hit (flags c : Nat) (r : Nat × Nat) (h : r.1 < r.2) :
    siHit flags (runItem r) c = (decide (r.1 ≤ c) && decide (c < r.2)) := by
  unfold runItem
  by_cases h1 : r.2 - r.1 = 1
  · have : (r.2 - r.1 == 1) = true := by simpa using h1
    simp only [this, if_true, siHit]
    by_cases h2 : c = r.1
    · subst h2
      have h3 : r.1 < r.2 := h
      simp [h3]
    · have h3 : (c == r.1) = false := by simpa using h2
      have h4 : ¬(r.1 ≤ c ∧ c < r.2) := by omega
      have h5 : (decide (r.1 ≤ c) && decide (c < r.2)) = false := by
        simpa using fun h => not_and.1 h4 h
      rw [h3, h5]
  · have : (r.2 - r.1 == 1) = false := by simpa using h1
    simp only [this, Bool.false_eq_true, if_false, siHit]
    have e : decide (c ≤ r.2 - 1) = decide (c < r.2) := by
      apply decide_eq_decide.2
      omega
    rw [e]

theorem runs_any (flags c : Nat) (runs : List (Nat × Nat)) (h : ∀ r ∈ runs, r.1 < r.2) :
    (runs.map runItem).any (siHit flags · c) = true ↔ ∃ r ∈ runs, r.1 ≤ c ∧ c < r.2 := by
  simp only [List.any_map, List.any_eq_true, Function.comp]
  constructor
  · rintro ⟨r, h1, h2⟩
    rw [runItem_hit flags c r (h r h1)] at h2
    exact ⟨r, h1, by simpa using h2⟩
  · rintro ⟨r, h1, h2⟩
    exact ⟨r, h1, by rw [runItem_hit flags c r (h r h1)]; simpa using h2⟩

theorem runs_plain (runs : List (Nat × Nat)) : ∀ x ∈ runs.map runItem, Plain x := by
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨r, _, rfl⟩ := hx
  unfold runItem
  split <;> trivial

/-! ### The bitmap -/

theorem chunkWords_length (n : Nat) (hn : 0 < n) (w : List Nat → Nat) : ∀ (k fuel : Nat) (s : List Nat),
    s.length = k * n → k ≤ fuel → (chunkWords n w fuel s).length = k := by
  intro k
  induction k with
  | zero =>
    intro fuel s h _
    have : s = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
    subst this
    cases fuel <;> rfl
  | succ k ih =>
    intro fuel s h hf
    obtain ⟨g, rfl⟩ : ∃ g, fuel = g + 1 := ⟨fuel - 1, by omega⟩
    have hk : s.length = n + k * n := by rw [h, Nat.add_mul, Nat.one_mul, Nat.add_comm]
    match s, hk with
    | [], hk =>
      simp only [List.length_nil] at hk
      omega
    | x :: t, hk =>
      show (w ((x :: t).take n) :: chunkWords n w g ((x :: t).drop n)).length = _
      rw [List.length_cons, ih g _ (by simp only [List.length_drop]; omega) (by omega)]

theorem mkBitmap_length (k : Nat) (bits : List Bool) (h : bits.length = k * 32) :
    (mkBitmap bits).length = k := by
  rw [mkBitmap_eq]
  apply chunkWords_length 32 (by decide) _ k
  · simpa using h
  · simp only [List.length_map]
    omega

theorem getD_bool_toList (cm : Array Bool) (i : Nat) : cm.toList.getD i false = cmAt cm i := by
  simp [cmAt, List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?]

theorem bitmap_hit (flags c : Nat) (cm : Array Bool) (h : cm.size = 256) :
    siHit flags (.charset (mkBitmap cm.toList)) c = cmAt cm c := by
  simp only [siHit]
  by_cases h1 : c < 256
  · have := bitmapLaw_proven cm.toList c (by simpa [h] using h1)
    simp only [decide_eq_true h1, Bool.true_and]
    rw [this, getD_bool_toList]
  · have h2 : cmAt cm c = false := cmAt_of_size cm c (by omega)
    simp [h1, h2]

/-! ### `BIGCHARSET` -/

theorem lookup_mem {b : List Bool} {v : Nat} : ∀ (comps : List (List Bool × Nat)),
    comps.lookup b = some v → (b, v) ∈ comps := by
  intro comps
  induction comps with
  | nil => intro h; simp at h
  | cons x r ih =>
    intro h
    obtain ⟨k, w⟩ := x
    simp only [List.lookup_cons] at h
    by_cases hk : (b == k) = true
    · simp only [hk, Option.some.injEq] at h
      subst h
      have : b = k := by simpa using hk
      simp [this]
    · simp only [hk] at h
      exact List.mem_cons_of_mem _ (ih h)

/-- A chunk of `data`. -/
def chunkAt (l : List Bool) (i : Nat) : List Bool := (l.drop (i * 256)).take 256

theorem chunkAt_append (data extra : List Bool) (b block : Nat) (h : data.length = block * 256)
    (hb : b < block) : chunkAt (data ++ extra) b = chunkAt data b := by
  unfold chunkAt
  have h1 : (b + 1) * 256 ≤ block * 256 := Nat.mul_le_mul_right 256 hb
  have h2 : b * 256 + 256 ≤ data.length := by
    rw [Nat.add_mul] at h1
    omega
  have h3 : b * 256 ≤ data.length := Nat.le_trans (Nat.le_add_right _ _) h2
  have h4 : 256 ≤ (data.drop (b * 256)).length := by
    rw [List.length_drop]
    exact Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact h2)
  rw [List.drop_append_of_le_length h3, List.take_append_of_le_length h4]

theorem chunkAt_new (data extra : List Bool) (block : Nat) (h : data.length = block * 256)
    (he : extra.length = 256) : chunkAt (data ++ extra) block = extra := by
  unfold chunkAt
  rw [← h, List.drop_left, List.take_of_length_le (by omega)]

/-- The state of `go2` after `h` chunks. -/
structure GoInv (bits : List Bool) (h : Nat) (rest : List Bool) (comps : List (List Bool × Nat))
    (mapping : List Nat) (block : Nat) (data : List Bool) : Prop where
  rest : rest = bits.drop (h * 256)
  mlen : mapping.length = h
  dlen : data.length = block * 256
  ble : block ≤ h
  maps : ∀ j, j < h → mapping.reverse.getD j 0 < block ∧
    chunkAt data (mapping.reverse.getD j 0) = chunkAt bits j
  comps : ∀ c b, (c, b) ∈ comps → b < block ∧ chunkAt data b = c

theorem rev_getD_new (mapping : List Nat) (b j : Nat) (hj : j = mapping.length) :
    (b :: mapping).reverse.getD j 0 = b := by
  subst hj
  rw [List.reverse_cons]
  have := getD_app_self mapping.reverse b
  rwa [List.length_reverse] at this

theorem rev_getD_old (mapping : List Nat) (b j : Nat) (hj : j < mapping.length) :
    (b :: mapping).reverse.getD j 0 = mapping.reverse.getD j 0 := by
  rw [List.reverse_cons, getD_app_left _ _ _ (by simpa using hj)]

theorem go2_spec (bits : List Bool) (hb : bits.length = 65536) : ∀ (i h : Nat) (rest : List Bool)
    (comps : List (List Bool × Nat)) (mapping : List Nat) (block : Nat) (data : List Bool),
    i + h = 256 → GoInv bits h rest comps mapping block data →
    ∃ (block' : Nat) (m : List Nat) (d : List Bool), bigCharset.go2 i rest comps mapping block data = (block', m, d) ∧
      m.length = 256 ∧ d.length = block' * 256 ∧ block' ≤ 256 ∧
      ∀ j, j < 256 → m.getD j 0 < block' ∧ chunkAt d (m.getD j 0) = chunkAt bits j := by
  intro i
  induction i with
  | zero =>
    intro h rest comps mapping block data hs hg
    have h256 : h = 256 := by omega
    subst h256
    refine ⟨block, mapping.reverse, data, rfl, by simp [hg.mlen], hg.dlen, hg.ble, hg.maps⟩
  | succ i ih =>
    intro h rest comps mapping block data hs hg
    have hchunk : rest.take 256 = chunkAt bits h := by
      rw [hg.rest]
      rfl
    have hlen : (chunkAt bits h).length = 256 := by
      simp only [chunkAt, List.length_take, List.length_drop, hb]
      omega
    have hdrop : rest.drop 256 = bits.drop ((h + 1) * 256) := by
      rw [hg.rest, List.drop_drop, Nat.add_mul, Nat.one_mul, Nat.add_comm]
    cases hl : comps.lookup (rest.take 256) with
    | some b =>
      have hm := hg.comps _ _ (lookup_mem comps hl)
      have e : bigCharset.go2 (i + 1) rest comps mapping block data =
          bigCharset.go2 i (rest.drop 256) comps (b :: mapping) block data := by
        simp [bigCharset.go2, hl]
      rw [e]
      apply ih (h + 1) _ _ _ _ _ (by omega)
      refine ⟨hdrop, by simp [hg.mlen], hg.dlen, by have := hg.ble; omega, fun j hj => ?_, hg.comps⟩
      by_cases hjh : j = h
      · subst hjh
        rw [rev_getD_new _ _ _ hg.mlen.symm]
        exact ⟨hm.1, by rw [hm.2, hchunk]⟩
      · rw [rev_getD_old _ _ _ (by rw [hg.mlen]; omega)]
        exact hg.maps j (by omega)
    | none =>
      have e : bigCharset.go2 (i + 1) rest comps mapping block data =
          bigCharset.go2 i (rest.drop 256) ((rest.take 256, block) :: comps) (block :: mapping)
            (block + 1) (data ++ rest.take 256) := by
        simp [bigCharset.go2, hl]
      rw [e]
      apply ih (h + 1) _ _ _ _ _ (by omega)
      have hchunk' : (rest.take 256).length = 256 := by rw [hchunk, hlen]
      refine ⟨hdrop, by simp [hg.mlen], ?_, by have := hg.ble; omega, fun j hj => ?_, fun c b hcb => ?_⟩
      · rw [List.length_append, hg.dlen, hchunk', Nat.add_mul, Nat.one_mul]
      · by_cases hjh : j = h
        · subst hjh
          rw [rev_getD_new _ _ _ hg.mlen.symm, chunkAt_new _ _ _ hg.dlen hchunk', hchunk]
          exact ⟨by omega, rfl⟩
        · rw [rev_getD_old _ _ _ (by rw [hg.mlen]; omega)]
          obtain ⟨h1, h2⟩ := hg.maps j (by omega)
          exact ⟨by omega, by rw [chunkAt_append _ _ _ _ hg.dlen h1, h2]⟩
      · simp only [List.mem_cons, Prod.mk.injEq] at hcb
        rcases hcb with ⟨rfl, rfl⟩ | hcb
        · exact ⟨by omega, chunkAt_new _ _ _ hg.dlen hchunk'⟩
        · obtain ⟨h1, h2⟩ := hg.comps c b hcb
          exact ⟨by omega, by rw [chunkAt_append _ _ _ _ hg.dlen h1, h2]⟩

theorem getD_bool_take (l : List Bool) (n k : Nat) (h : k < n) : (l.take n).getD k false = l.getD k false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, h]

theorem getD_bool_drop (l : List Bool) (n k : Nat) : (l.drop n).getD k false = l.getD (n + k) false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem chunk_getD (l : List Bool) (i k : Nat) (h : k < 256) :
    (chunkAt l i).getD k false = l.getD (i * 256 + k) false := by
  unfold chunkAt
  rw [getD_bool_take _ _ _ h, getD_bool_drop]

theorem bytes_len (m : List Nat) (hm : m.length = 256) : (bytesToCodes m).length = 64 := by
  rw [bytesToCodes_eq]
  exact chunkWords_length 4 (by decide) _ 64 _ _ hm (by omega)

/-- What `bigCharset` builds, and that it answers what the map answers. -/
theorem big_spec (flags : Nat) (cm : Array Bool) (h : cm.size = 65536) :
    ItemWf (.big (bigCharset cm)) ∧ ∀ c, siHit flags (.big (bigCharset cm)) c = cmAt cm c := by
  have hb : cm.toList.length = 65536 := by simpa using h
  obtain ⟨block, m, d, h1, h2, h3, h4, h5⟩ := go2_spec cm.toList hb 256 0 cm.toList [] [] 0 []
    rfl ⟨by simp, rfl, rfl, Nat.le_refl _, fun j hj => by omega, fun c b hcb => by simp at hcb⟩
  have e : bigCharset cm = block :: bytesToCodes m ++ mkBitmap d := by
    simp only [bigCharset, h1]
  have hml : (mkBitmap d).length = block * 8 := by
    apply mkBitmap_length
    rw [h3] <;> omega
  have hbytes : ∀ x ∈ m, x < 256 := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    have := (h5 j (by omega)).1
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at this
    omega
  have hbl := bytes_len m h2
  rw [e]
  generalize hD : block :: bytesToCodes m ++ mkBitmap d = D
  have hlen : D.length = 65 + block * 8 := by
    rw [← hD]
    simp only [List.length_cons, List.length_append, hbl, hml] <;> omega
  have hhead : D.headD 0 = block := by
    rw [← hD]
    rfl
  have hmap : ∀ i, i < 64 → D.getD (1 + i) 0 = (bytesToCodes m).getD i 0 := by
    intro i hi
    rw [← hD, Nat.add_comm, List.cons_append, List.getD_cons_succ]
    exact getD_app_left _ _ _ (by omega)
  have hbit : ∀ i, D.getD (1 + 64 + i) 0 = (mkBitmap d).getD i 0 := by
    intro i
    rw [← hD, show 1 + 64 + i = (64 + i) + 1 by omega, List.cons_append, List.getD_cons_succ]
    have := getD_app_right (bytesToCodes m) (mkBitmap d) i
    rwa [hbl] at this
  /- The block of a character. -/
  have hblock : ∀ ch, ch < 0x10000 →
      (D.getD (1 + ch / 256 / 4) 0 / 256 ^ (ch / 256 % 4)) % 256 = m.getD (ch / 256) 0 := by
    intro ch hc
    have h6 : ch / 256 < 256 := by omega
    rw [hmap _ (by omega)]
    exact bytesToCodesLaw_proven m (ch / 256) hbytes (by omega)
  refine ⟨⟨by omega, by rw [hhead]; exact hlen, fun ch hc => ?_⟩, fun c => ?_⟩
  · rw [hblock ch hc, hlen]
    have h6 := (h5 (ch / 256) (by omega)).1
    have h7 : (m.getD (ch / 256) 0 + 1) * 256 ≤ block * 256 := Nat.mul_le_mul_right 256 h6
    rw [Nat.add_mul, Nat.one_mul] at h7
    have h8 : ch % 256 < 256 := Nat.mod_lt _ (by decide)
    omega
  · simp only [siHit, bigHit]
    by_cases hc : c < 0x10000
    · simp only [hc, if_true]
      rw [hblock c hc, hbit]
      obtain ⟨h6, h7⟩ := h5 (c / 256) (by omega)
      generalize hB : m.getD (c / 256) 0 = B at h6 h7
      have h8 : c % 256 < 256 := Nat.mod_lt _ (by decide)
      have h9 : (B + 1) * 256 ≤ block * 256 := Nat.mul_le_mul_right 256 h6
      rw [Nat.add_mul, Nat.one_mul] at h9
      have hmod : c % 32 = (B * 256 + c % 256) % 32 := by omega
      rw [hmod, bitmapLaw_proven d _ (by omega), ← chunk_getD d B _ h8, h7, chunk_getD _ _ _ h8,
        getD_bool_toList]
      congr 1
      omega
    · have h6 : cmAt cm c = false := cmAt_of_size cm c (by omega)
      simp [hc, h6]

/-! ### The whole of `_optimize_charset` -/

/-- A list of the parser's items: `NEGATE` comes first, if at all. -/
def NegHead (items : List SetItem) : Prop := ∀ it ∈ items.drop 1, it ≠ .negate

theorem plain_ne (x : CItem) (h : Plain x) : x ≠ .neg := by
  intro h1
  subst h1
  exact h

theorem plain_wf (x : CItem) (h : Plain x) : ItemWf x := by
  cases x <;> first | trivial | exact h.elim

/-- The result of the loop, whichever form the map compressed to. `mid` answers what the map does. -/
theorem final_hit (flags c : Nat) (st : OSt) (mid : List CItem) (neg : Bool)
    (hout : st.out = if neg then [.neg] else []) (hmid : mid.any (siHit flags · c) = cmAt st.cm c)
    (hm : ∀ x ∈ mid, x ≠ .neg) (ht : ∀ x ∈ st.tail, Plain x) :
    hitList flags true (st.out ++ mid ++ st.tail) c = if neg then !stHit flags st c else stHit flags st c := by
  have hX : ∀ x ∈ mid ++ st.tail, x ≠ .neg := by
    intro x hx
    simp only [List.mem_append] at hx
    rcases hx with hx | hx
    · exact hm x hx
    · exact plain_ne x (ht x hx)
  have hany : (mid ++ st.tail).any (siHit flags · c) = stHit flags st c := by
    rw [List.any_append, hmid]
    rfl
  rw [hout, List.append_assoc]
  cases neg with
  | true =>
    show hitList flags false (mid ++ st.tail) c = _
    rw [hitList_plain flags c _ _ hX, hany]
    cases stHit flags st c <;> rfl
  | false =>
    show hitList flags true (mid ++ st.tail) c = _
    rw [hitList_plain flags c _ _ hX, hany]
    cases stHit flags st c <;> rfl

theorem empty_stHit (flags c : Nat) (out : List CItem) :
    stHit flags ({ out } : OSt) c = false := by
  have : cmAt (Array.replicate 256 false) c = false := by
    simp only [cmAt, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> rfl
  simpa [stHit] using this

/-- `optimizeCharset` over a list of the parser's items, from either start. -/
theorem optimize_hit (flags c : Nat) (charset rr : List CItem) (neg : Bool)
    (hloop : optLoop none charset {} = optLoop none rr { out := if neg then [.neg] else [] })
    (hr : ∀ x ∈ rr, Plain x) (hbase : hitList flags true charset c =
      if neg then !rr.any (siHit flags · c) else rr.any (siHit flags · c))
    (hwf : ∀ x ∈ charset, ItemWf x) :
    hitList flags true (optimizeCharset charset none).1 c =
        (if neg then !rr.any (siHit flags · c) else rr.any (siHit flags · c)) ∧
      ∀ x ∈ (optimizeCharset charset none).1, ItemWf x := by
  have h0 := optLoop_none flags rr { out := if neg then [.neg] else [] } hr (.inl (by simp)) (by simp)
  have hneg : ∀ x ∈ (if neg then [CItem.neg] else []), ItemWf x := by
    intro x hx
    cases neg with
    | true =>
      simp only [if_true, List.mem_singleton] at hx
      subst hx
      trivial
    | false => simp at hx
  unfold optimizeCharset
  rw [hloop]
  cases h1 : optLoop none rr { out := if neg then [.neg] else [] } with
  | inl out =>
    rw [h1] at h0
    obtain ⟨h2, h3⟩ := h0
    have h4 := h3 c
    rw [empty_stHit, Bool.false_or] at h4
    cases neg with
    | true =>
      simp only [h2, h4]
      simp [hitList, ItemWf]
    | false =>
      simp only [h2, h4]
      simp [hitList, ItemWf]
  | inr st =>
    rw [h1] at h0
    obtain ⟨h2, h3, h4, h5⟩ := h0
    have h6 := h5 c
    rw [empty_stHit, Bool.false_or] at h6
    have hout : st.out = if neg then [.neg] else [] := h2
    rw [← h6] at hbase ⊢
    have hmemwf : ∀ (mid : List CItem), (∀ x ∈ mid, ItemWf x) →
        ∀ x ∈ st.out ++ mid ++ st.tail, ItemWf x := by
      intro mid hm x hx
      simp only [List.mem_append] at hx
      rcases hx with (hx | hx) | hx
      · rw [hout] at hx
        exact hneg x hx
      · exact hm x hx
      · exact plain_wf x (h4 x hx)
    cases hr2 : cmRuns st.cm 3 [] 0 with
    | some runs =>
      obtain ⟨h7, h8⟩ := cmRuns_spec st.cm 3 [] runs 0 (by decide) (by omega) rfl (by simp)
        ⟨by simp, fun x hx => by omega⟩ hr2
      have h7' : ∀ r ∈ runs, r.1 < r.2 := fun r hr => (h7 r hr).1
      have hmid : (runs.map runItem).any (siHit flags · c) = cmAt st.cm c := by
        by_cases hc : c < st.cm.size
        · have h9 := h8 c hc
          have h10 := runs_any flags c runs h7'
          cases h11 : cmAt st.cm c with
          | true => exact h10.2 (h9.1 h11)
          | false =>
            cases h12 : (runs.map runItem).any (siHit flags · c) with
            | false => rfl
            | true =>
              rw [h9.2 (h10.1 h12)] at h11
              cases h11
        · have h9 : cmAt st.cm c = false := cmAt_of_size _ _ (by omega)
          rw [h9]
          cases h12 : (runs.map runItem).any (siHit flags · c) with
          | false => rfl
          | true =>
            obtain ⟨r, h13, h14⟩ := (runs_any flags c runs h7').1 h12
            have := (h7 r h13).2
            omega
      have hfin := final_hit flags c st (runs.map runItem) neg hout hmid
        (fun x hx => plain_ne x (runs_plain runs x hx)) h4
      have hw2 := hmemwf (runs.map runItem) (fun x hx => plain_wf x (runs_plain runs x hx))
      have hmap : (runs.map fun r => if r.2 - r.1 == 1 then CItem.lit r.1 else .rng r.1 (r.2 - 1)) =
          runs.map runItem := rfl
      simp only [hr2, hmap]
      by_cases hc : st.cased = true ∨ (st.out ++ runs.map runItem ++ st.tail).length < charset.length
      · simp only [if_pos hc]
        exact ⟨hfin, hw2⟩
      · simp only [if_neg hc]
        exact ⟨hbase, hwf⟩
    | none =>
      by_cases h256 : st.cm.size = 256
      · have hb : (st.cm.size == 256) = true := by simpa using h256
        simp only [hr2, hb, if_true]
        have hany : ([CItem.charset (mkBitmap st.cm.toList)]).any (siHit flags · c) = cmAt st.cm c := by
          simp only [List.any_cons, List.any_nil, Bool.or_false]
          exact bitmap_hit flags c st.cm h256
        refine ⟨final_hit flags c st _ neg hout hany (by simp) h4, hmemwf _ ?_⟩
        intro x hx
        simp only [List.mem_singleton] at hx
        subst hx
        exact mkBitmap_length 8 _ (by simp [h256])
      · have hz : st.cm.size = 65536 := by
          rcases h3 with h7 | h7
          · exact absurd h7 h256
          · exact h7
        have hb : (st.cm.size == 256) = false := by simpa using h256
        simp only [hr2, hb, Bool.false_eq_true, if_false]
        obtain ⟨h7, h8⟩ := big_spec flags st.cm hz
        have hany : ([CItem.big (bigCharset st.cm)]).any (siHit flags · c) = cmAt st.cm c := by
          simp only [List.any_cons, List.any_nil, Bool.or_false]
          exact h8 c
        refine ⟨final_hit flags c st _ neg hout hany (by simp) h4, hmemwf _ ?_⟩
        intro x hx
        simp only [List.mem_singleton] at hx
        subst hx
        exact h7

theorem item_of_setItem (flags c : Nat) (h : hasFlag flags FLAG_IGNORECASE = false) (it : SetItem) :
    siHit flags (ofSetItem it) c = itemHit flags it c := by
  cases it with
  | literal a => simp [ofSetItem, siHit, itemHit, litEq, h]
  | range a b => simp [ofSetItem, siHit, itemHit, h]
  | category k => rfl
  | negate => rfl

theorem plain_of (it : SetItem) (h : it ≠ .negate) : Plain (ofSetItem it) := by
  cases it with
  | literal _ => trivial
  | range _ _ => trivial
  | category _ => trivial
  | negate => exact absurd rfl h

/-- `_optimize_charset`, with `_compile_charset`: `SRE(charset)` on the compiled words answers what
the unoptimized set says, for every set and every character, through the literal, range, bitmap
and `BIGCHARSET` forms and both `[\s\S]` shortcuts, whose results `IN` compiles to `FAILURE` and
`ANY_ALL` and `hitList` reads the same.

The hypotheses: `IGNORECASE` is off (`textlibs-re-charset-preserved-ignorecase` is the other case),
and `NEGATE` comes first, which the parser guarantees. -/
def CharsetPreserved : Prop :=
  ∀ (e : Env) (flags ch set fuel : Nat) (items : List SetItem),
    hasFlag flags FLAG_IGNORECASE = false → NegHead items →
    (optimizeCharset (items.map ofSetItem) none).1.length + 1 ≤ fuel →
    Slice e set (compileCharset (optimizeCharset (items.map ofSetItem) none).1 flags) →
    sreCharset e ch fuel set true = setHit flags items ch

theorem charsetPreserved_proven : CharsetPreserved := by
  intro e flags ch set fuel items hi hneg hf hs
  rw [compileCharset_eq] at hs
  have hany : ∀ r : List SetItem,
      (r.map ofSetItem).any (siHit flags · ch) = r.any (itemHit flags · ch) := by
    intro r
    induction r with
    | nil => rfl
    | cons x t ih =>
      simp only [List.map_cons, List.any_cons, ih, item_of_setItem flags ch hi]
  /- The set without its `NEGATE`, and whether it had one. -/
  have key : ∀ (neg : Bool) (r : List SetItem), (∀ it ∈ r, it ≠ .negate) →
      optLoop none (items.map ofSetItem) {} = optLoop none (r.map ofSetItem) { out := if neg then [.neg] else [] } →
      hitList flags true (items.map ofSetItem) ch =
        (if neg then !(r.map ofSetItem).any (siHit flags · ch) else (r.map ofSetItem).any (siHit flags · ch)) →
      (∀ x ∈ items.map ofSetItem, ItemWf x) →
      setHit flags items ch =
        (if neg then !(r.map ofSetItem).any (siHit flags · ch) else (r.map ofSetItem).any (siHit flags · ch)) →
      sreCharset e ch fuel set true = setHit flags items ch := by
    intro neg r hr hl hb hw hset
    have hplain : ∀ x ∈ r.map ofSetItem, Plain x := by
      intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨it, h1, rfl⟩ := hx
      exact plain_of it (hr it h1)
    obtain ⟨h1, h2⟩ := optimize_hit flags ch _ _ neg hl hplain hb hw
    rw [charset_list e flags ch _ fuel set true h2 hf hs, h1, hset]
  match items, hneg with
  | [], _ =>
    apply key false [] (by simp) rfl (by simp [hitList]) (by simp)
    simp [setHit]
  | .negate :: r, hneg =>
    have hr : ∀ it ∈ r, it ≠ .negate := by simpa [NegHead] using hneg
    have hrp : ∀ x ∈ r.map ofSetItem, x ≠ .neg := by
      intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨it, h1, rfl⟩ := hx
      exact plain_ne _ (plain_of it (hr it h1))
    apply key true r hr rfl
    · show hitList flags false (r.map ofSetItem) ch = _
      rw [hitList_plain flags ch _ _ hrp]
      cases (r.map ofSetItem).any (siHit flags · ch) <;> rfl
    · intro x hx
      simp only [List.map_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · trivial
      · simp only [List.mem_map] at hx
        obtain ⟨it, h1, rfl⟩ := hx
        exact plain_wf _ (plain_of it (hr it h1))
    · rw [hany]
      simp [setHit, itemHit]
  | x :: r, hneg =>
    by_cases hx : x = .negate
    · subst hx
      have hr : ∀ it ∈ r, it ≠ .negate := by simpa [NegHead] using hneg
      have hrp : ∀ y ∈ r.map ofSetItem, y ≠ .neg := by
        intro y hy
        simp only [List.mem_map] at hy
        obtain ⟨it, h1, rfl⟩ := hy
        exact plain_ne _ (plain_of it (hr it h1))
      apply key true r hr rfl
      · show hitList flags false (r.map ofSetItem) ch = _
        rw [hitList_plain flags ch _ _ hrp]
        cases (r.map ofSetItem).any (siHit flags · ch) <;> rfl
      · intro y hy
        simp only [List.map_cons, List.mem_cons] at hy
        rcases hy with rfl | hy
        · trivial
        · simp only [List.mem_map] at hy
          obtain ⟨it, h1, rfl⟩ := hy
          exact plain_wf _ (plain_of it (hr it h1))
      · rw [hany]
        simp [setHit, itemHit]
    · have hr : ∀ it ∈ x :: r, it ≠ .negate := by
        intro it hit
        simp only [List.mem_cons] at hit
        rcases hit with rfl | hit
        · exact hx
        · have : ∀ it ∈ r, it ≠ .negate := by simpa [NegHead] using hneg
          exact this it hit
      have hrp : ∀ y ∈ (x :: r).map ofSetItem, y ≠ .neg := by
        intro y hy
        simp only [List.mem_map] at hy
        obtain ⟨it, h1, rfl⟩ := hy
        exact plain_ne _ (plain_of it (hr it h1))
      apply key false (x :: r) hr rfl
      · rw [hitList_plain flags ch _ _ hrp]
        cases ((x :: r).map ofSetItem).any (siHit flags · ch) <;> rfl
      · intro y hy
        simp only [List.mem_map] at hy
        obtain ⟨it, h1, rfl⟩ := hy
        exact plain_wf _ (plain_of it (hr it h1))
      · have hno : (x :: r).contains .negate = false := by
          cases h : (x :: r).contains .negate with
          | false => rfl
          | true =>
            have := List.contains_iff_mem.1 h
            exact absurd rfl (hr _ this)
        rw [hany]
        simp only [setHit, hno, Bool.false_eq_true, if_false]

/-- The same under `IGNORECASE`: the set tests the lower-cased character when `_optimize_charset`
says it is cased, and the map holds lower-cased members and their `_EXTRA_CASES`. -/
def CharsetPreservedIgnorecase : Prop :=
  ∀ (e : Env) (flags ch set fuel : Nat) (items : List SetItem) (cf : CaseFns),
    caseFor flags = some cf → NegHead items →
    (optimizeCharset (items.map ofSetItem) (some cf)).1.length + 1 ≤ fuel →
    Slice e set (compileCharset (optimizeCharset (items.map ofSetItem) (some cf)).1 flags) →
    sreCharset e (if (optimizeCharset (items.map ofSetItem) (some cf)).2 then cf.tolower ch else ch)
      fuel set true = setHit flags items ch

end PyLean.TextLibs.Re
