import PyLean.TextLibs.PlistRoundTrip4

namespace PyLean.TextLibs.Plist

open PyLean PyLean.TextLibs

theorem lookup_id_iff {H : WHeap} {st : WState} (hI : WInv H st) {c c' i i' : Nat}
    (hs1 : isScalar H c = false) (hs2 : isScalar H c' = false)
    (h1 : lookupW H st c = some i) (h2 : lookupW H st c' = some i') : i = i' ↔ objId H c = objId H c' := by
  constructor
  · rintro rfl
    obtain ⟨d, hd, hm⟩ := lookup_sound hI h1
    obtain ⟨d', hd', hm'⟩ := lookup_sound hI h2
    rw [hd] at hd'; cases hd'
    rcases hm with ⟨h, _⟩ | ⟨_, e1, _⟩
    · rw [hs1] at h; cases h
    rcases hm' with ⟨h, _⟩ | ⟨_, e2, _⟩
    · rw [hs2] at h; cases h
    rw [← e1, ← e2]
  · intro he
    unfold lookupW at h1 h2
    rw [if_neg (by simp [hs1])] at h1
    rw [if_neg (by simp [hs2])] at h2
    unfold idLookup at h1 h2
    rw [he] at h1
    rw [h1] at h2; cases h2; rfl

theorem isFmtXml_bplist (rest : List Nat) : isFmtXml ((bplistHeader ++ rest).take 32) = false := by
  simp [isFmtXml, bplistHeader, asciiBytes, encodeAscii, List.isPrefixOf]

theorem isFmtBinary_bplist (rest : List Nat) : isFmtBinary ((bplistHeader ++ rest).take 32) = true := by
  simp [isFmtBinary, bplistHeader, asciiBytes]

theorem trailer_ofBytes (oS rS n top tbl : Nat) (hn : n < 2 ^ 64) (ht : top < 2 ^ 64) (hb : tbl < 2 ^ 64) :
    Trailer.ofBytes ([0, 0, 0, 0, 0, 0, oS, rS] ++ beBytes n 8 ++ beBytes top 8 ++ beBytes tbl 8) =
      ⟨oS, rS, n, top, tbl⟩ := by
  have l1 := beBytes_length n 8
  have l2 := beBytes_length top 8
  have l3 := beBytes_length tbl 8
  simp only [Trailer.ofBytes, List.append_assoc]
  congr 1
  · rw [List.drop_left' (by simp), List.take_left' l1, beVal_beBytes 8 n (by omega)]
  · rw [show 16 = 8 + 8 from rfl, ← List.drop_drop, List.drop_left' (by simp), List.drop_left' l1,
      List.take_left' l2, beVal_beBytes 8 top (by omega)]
  · rw [show 24 = 8 + 8 + 8 from rfl, ← List.drop_drop, ← List.drop_drop, List.drop_left' (by simp),
      List.drop_left' l1, List.drop_left' l2, List.take_of_length_le (by omega), beVal_beBytes 8 tbl (by omega)]

/-- `BinaryRoundTrip`: for every object graph without datetimes, `loads` reads back what
`dumps(fmt=FMT_BINARY)` wrote. -/
def BinaryRoundTrip : Prop :=
  ∀ (xml : XmlParse) (xmlw : XmlWrite) (H : WHeap) (root : Nat) (cfg : WCfg) (r1 r2 : Nat) (b : List Nat),
    HeapWf H → dumpsR xmlw r1 H root .binary cfg = .ok b → b.length < 2 ^ 63 → b.length + 8 ≤ r2 →
    ∃ res, loadsR xml r2 (.bytes b) .none cfg.awareDatetime = .ok res ∧ Bisim H cfg root res

theorem binaryRoundTrip_proven : BinaryRoundTrip := by
  intro xml xmlw H root cfg r1 r2 b hwf hd hbl hr2
  obtain ⟨k, hk⟩ := dumps_binary xmlw r1 H root cfg b hd
  obtain ⟨⟨st, kk, offsets, body, top, hflat, hall, htop, hb⟩⟩ := written_of H cfg root b k hk
  obtain ⟨hI, _, _, _⟩ := flatten_spec H cfg kk root WState.init st (winv_init H) hflat
  obtain ⟨encs, os, h1, h2, h3, h4, _, h6, h7⟩ := writeAll_spec kk H cfg _ st hI hwf.1 st.objlist 0
    (List.replicate st.objlist.length 0) [] offsets body (by simp) hall
  simp only [List.drop_zero, List.length_replicate, List.length_nil, Nat.zero_add] at h1 h2 h3 h4 h6 h7
  have h6' : ∀ k, k < st.objlist.length → offsets[k]? = some (8 + (encs.take k).flatten.length) := by
    intro k hk; have := h6 k hk hk; simpa using this
  have hT := written_tab H cfg b hwf st offsets body top hb hbl encs os hI h1 h2 (by simpa using h3) h6'
    (fun k hk => h7 k hk) h4
  have h3' : body = encs.flatten := by simpa using h3
  -- sizes
  have hne : ∀ e ∈ encs, e ≠ [] := by
    intro e he
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem he
    have := (h7 k (by omega)).1
    rw [getD_lt _ _ hk] at this
    obtain ⟨tok, tail, ht⟩ := canon_cons _ _ _ this
    rw [ht]; simp
  have hbody : body.length + 40 ≤ b.length := by
    have := congrArg List.length hb; simp [bplistHeader, asciiBytes, beBytes_length] at this; omega
  have hn : st.objlist.length ≤ body.length := by
    have := length_le_flatten encs hne; rw [← h3'] at this; omega
  have htopn : top < st.objlist.length := lookup_lt hI htop
  let n := st.objlist.length
  let tbl := 8 + body.length
  let trl := [0, 0, 0, 0, 0, 0, countToSize tbl, countToSize n] ++ beBytes n 8 ++ beBytes top 8 ++ beBytes tbl 8
  have htrl : trl.length = 32 := by simp [trl, beBytes_length]
  have hbx : b = (bplistHeader ++ body ++ packRefs (countToSize tbl) offsets) ++ trl := by
    rw [hb]; try simp [trl, List.append_assoc]
  have hbx2 : b = bplistHeader ++ (body ++ packRefs (countToSize tbl) offsets ++ trl) := by
    rw [hbx]; simp [List.append_assoc]
  have hdtrl : b.drop (b.length - 32) = trl := by
    rw [hbx]
    have : (bplistHeader ++ body ++ packRefs (countToSize tbl) offsets ++ trl).length - 32 =
        (bplistHeader ++ body ++ packRefs (countToSize tbl) offsets).length := by
      simp only [List.length_append, htrl]; omega
    rw [this, List.drop_left]
  have hdtbl : b.drop tbl = packRefs (countToSize tbl) offsets ++ trl := by
    rw [hbx, List.append_assoc]
    have : tbl = (bplistHeader ++ body).length := by simp [tbl, bplistHeader, asciiBytes]; omega
    rw [this, List.drop_left]
  have hoffs : ∀ x ∈ offsets, x < 256 ^ countToSize tbl := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    have h6k := h6' k (by omega)
    rw [List.getElem?_eq_getElem hk] at h6k
    simp only [Option.some.injEq] at h6k
    rw [h6k]
    have hl : (encs.take k).flatten.length < body.length := by
      rw [h3', take_drop_flatten encs k, flatten_drop encs k (by omega)]
      have hk' : encs.getD k [] ≠ [] := hne _ (by rw [getD_lt _ _ (by omega)]; simp)
      cases hh : encs.getD k [] with
      | nil => exact absurd hh hk'
      | cons _ _ => simp
    have := countToSize_lt tbl (by omega)
    omega
  -- the reader
  let T : Tab := ⟨os, b, offsets, countToSize n⟩
  obtain ⟨r, rfl⟩ : ∃ r, r2 = r + 3 := ⟨r2 - 3, by omega⟩
  let st0 : PState := ⟨⟨b, tbl + countToSize tbl * offsets.length⟩, List.replicate n none⟩
  have hg0 : Good T [] st0 := by
    refine ⟨by simp [st0, T, h2, n], rfl, ?_, by simp⟩
    intro j o hj
    simp [st0, List.getElem?_replicate] at hj
  obtain ⟨st', hro, hg', _, hdef, _⟩ := readObj_tab T hT cfg.awareDatetime r top st0 [] hg0 (by simpa [T, h2] using htopn)
    (by simp only [st0, undef_replicate]; omega)
  have hparse : parseBody r cfg.awareDatetime b = .ok ⟨st'.objs, top⟩ := by
    unfold parseBody
    simp only [FP.seekEnd]
    have hr32 := read_prefix b (b.length - 32) trl [] (by rw [hdtrl]; simp)
    rw [htrl] at hr32
    simp only [hr32]
    simp only [htrl, ne_eq, not_true_eq_false, ↓reduceIte]
    rw [trailer_ofBytes _ _ _ _ _ (by omega) (by omega) (by omega)]
    simp only [FP.seek, bind, Except.bind]
    rw [if_neg (by omega)]
    simp only
    rw [show n = offsets.length by omega, readIntsR_pack r (by omega) b tbl (countToSize tbl)
      (countToSize_bin _) offsets trl hoffs hdtbl]
    simp only
    have hcfg : (⟨offsets, countToSize offsets.length, cfg.awareDatetime⟩ : PCfg) = cfgOf T cfg.awareDatetime := by
      simp [cfgOf, T, n, h4]
    rw [hcfg]
    have hst0 : (⟨⟨b, tbl + countToSize tbl * offsets.length⟩, List.replicate offsets.length none⟩ : PState) = st0 := by
      simp [st0, n, h4]
    rw [hst0, hro]
  refine ⟨⟨st'.objs, top⟩, ?_, ?_⟩
  · simp only [loadsR, loadR, call, bind, Except.bind]
    rw [header_take, hbx2, isFmtXml_bplist, isFmtBinary_bplist, ← hbx2]
    simp only [Bool.false_eq_true, ↓reduceIte, parseR, call]
    rw [hparse]
  · refine ⟨fun i c => lookupW H st c = some i ∧ Defined st' i, ⟨htop, hdef⟩, ?_, ?_⟩
    rotate_left
    · intro i c i' c' ⟨h1, _⟩ ⟨h2, _⟩ hs1 hs2
      exact lookup_id_iff hI hs1 hs2 h1 h2
    intro i c ⟨hl, hdi⟩
    obtain ⟨o, ho⟩ := hdi
    refine ⟨o, ho, ?_⟩
    obtain ⟨hos, hch⟩ := hg'.2.2.1 i o ho (by simp)
    obtain ⟨c', hc', hm⟩ := lookup_sound hI hl
    have hil := lt_of_getElem?_some hc'
    have hrel := (h7 i hil).2
    rw [List.getD_eq_getElem?_getD, hc', List.getD_eq_getElem?_getD, show os[i]? = some o from hos] at hrel
    simp only [Option.getD_some] at hrel
    exact match_of_lookup H cfg st _ (Defined st') (fun r x h1 h2 => ⟨h1, h2⟩) hwf.1 c' c o hrel hch hm

end PyLean.TextLibs.Plist
