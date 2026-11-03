import PyLean.TextLibs.UrlSpecQuery

/-!
`urlparse` and `urldefrag` on ASCII `bytes`: the `bytes` path (`_decode_args`, then
`_encode_result` on the result) gives the `str` path's fields as a `bytes` result, for every
`allow_fragments` and `missing_as_none`, errors included.
-/

namespace PyLean.TextLibs.Url

open PyLean

set_option linter.unusedSimpArgs false

theorem fill_some_ascii (mn : Bool) (x : Option Str) (h : ∀ s, x = some s → ∀ c ∈ s, c < 128) :
    ∀ s, fillMissing mn x = some s → ∀ c ∈ s, c < 128 := by
  intro s hs c hc
  unfold fillMissing at hs
  split at hs
  · exact h s hs c hc
  · cases x with
    | none => simp at hs; subst hs; simp at hc
    | some t => simp at hs; subst hs; exact h _ rfl c hc

theorem pathParams_sub (s : Option Str) (p : Str) :
    (∀ c ∈ (pathParams s p).1, c ∈ p) ∧ (∀ y, (pathParams s p).2 = some y → ∀ c ∈ y, c ∈ p) := by
  have hr := paramsOf_rebuild s p
  have he : pathParams s p = paramsOf s p := rfl
  rw [he]
  constructor
  · intro c hc; rw [← hr]; exact List.mem_append_left _ hc
  · intro y hy c hc; rw [← hr, hy]; simp [opt, hc]

theorem schemeWith_none (s : Option Str) : schemeWith s none = s := by cases s <;> rfl

theorem parseRes_ascii (x : Str) (frag mn : Bool) (hx : ∀ c ∈ x, c < 128) :
    AsciiFields (parseRes x none frag mn).fields := by
  have hs := splitPure_ascii x frag hx
  have g : ∀ f, f ∈ [(splitPure x frag).1, (splitPure x frag).2.1, some (splitPure x frag).2.2.1,
      (splitPure x frag).2.2.2.1, (splitPure x frag).2.2.2.2] → ∀ s, f = some s → ∀ c ∈ s, c < 128 := hs
  have hp : ∀ c ∈ (splitPure x frag).2.2.1, c < 128 := g _ (by simp) _ rfl
  obtain ⟨h1, h2⟩ := pathParams_sub (splitPure x frag).1 (splitPure x frag).2.2.1
  intro f hf
  simp only [parseRes, schemeWith_none, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact fill_some_ascii mn _ (g _ (by simp))
  · exact fill_some_ascii mn _ (g _ (by simp))
  · intro s hs c hc; simp at hs; subst hs; exact hp c (h1 c hc)
  · exact fill_some_ascii mn _ (fun y hy c hc => hp c (h2 y hy c hc))
  · exact fill_some_ascii mn _ (g _ (by simp))
  · exact fill_some_ascii mn _ (g _ (by simp))

theorem allLt_app {a b : Str} (ha : ∀ c ∈ a, c < 128) (hb : ∀ c ∈ b, c < 128) : ∀ c ∈ a ++ b, c < 128 := by
  intro c hc
  rcases List.mem_append.1 hc with h | h
  · exact ha c h
  · exact hb c h

theorem allLt_lit (l : Str) (h : l.all (· < 128) = true) : ∀ c ∈ l, c < 128 := by
  intro c hc
  have := List.all_eq_true.1 h c hc
  simpa using this

theorem allLt_opt (d : Nat) (hd : d < 128) (x : Option Str) (h : ∀ t, x = some t → ∀ c ∈ t, c < 128) :
    ∀ c ∈ opt d x, c < 128 := by
  cases x with
  | none => simp [opt]
  | some t =>
    intro c hc
    simp only [opt, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact hd
    · exact h t rfl c hc

theorem unsplitPure_ascii (s n : Option Str) (p : Str) (q f : Option Str)
    (h : ∀ y ∈ [s, n, some p, q, f], ∀ t, y = some t → ∀ c ∈ t, c < 128) :
    ∀ c ∈ unsplitPure s n p q f, c < 128 := by
  have hs : ∀ t, s = some t → ∀ c ∈ t, c < 128 := h s (by simp)
  have hn : ∀ t, n = some t → ∀ c ∈ t, c < 128 := h n (by simp)
  have hp : ∀ c ∈ p, c < 128 := h (some p) (by simp) p rfl
  have hq : ∀ t, q = some t → ∀ c ∈ t, c < 128 := h q (by simp)
  have hf : ∀ t, f = some t → ∀ c ∈ t, c < 128 := h f (by simp)
  obtain ⟨_, _, h3, h4, h5, _⟩ := unsplitSpec_proven
  have hpre : ∀ c ∈ (match s with | some (c :: x) => (c :: x) ++ [58] | _ => []), c < 128 := by
    rcases s with _ | _ | ⟨d, x⟩
    · simp
    · simp
    · exact allLt_app (hs _ rfl) (allLt_lit _ rfl)
  have hq' := allLt_opt 63 (by omega) q hq
  have hf' := allLt_opt 35 (by omega) f hf
  cases n with
  | some m =>
    rw [h3]
    refine allLt_app (allLt_app (allLt_app (allLt_app (allLt_app hpre (allLt_lit _ rfl)) (hn m rfl)) ?_) hq') hf'
    split
    · intro c hc
      simp only [List.mem_cons] at hc
      rcases hc with rfl | hc
      · omega
      · exact hp c hc
    · exact hp
  | none =>
    by_cases hp2 : p.take 2 = [47, 47]
    · rw [h4 s p q f hp2]
      exact allLt_app (allLt_app (allLt_app (allLt_app hpre (allLt_lit _ rfl)) hp) hq') hf'
    · rw [h5 s p q f hp2]
      exact allLt_app (allLt_app (allLt_app hpre hp) hq') hf'

theorem defragRes_ascii (x : Str) (mn : Bool) (hx : ∀ c ∈ x, c < 128) :
    AsciiFields (defragRes x mn).fields := by
  have g := splitPure_ascii x true hx
  intro f hf
  simp only [defragRes, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · intro s hs
    simp only [Option.some.injEq] at hs
    subst hs
    apply unsplitPure_ascii
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl
    · exact g _ (by simp)
    · exact g _ (by simp)
    · exact g _ (by simp)
    · exact g _ (by simp)
    · intro t ht; cases ht
  · exact fill_some_ascii mn _ (g _ (by simp))

theorem coerce_one_bytes (x : Str) (hx : ∀ c ∈ x, c < 128) :
    coerceArgs [.bytes x false] = .ok ([some (.s x)], true) := by
  cases x with
  | nil => rfl
  | cons c r =>
    rw [(coerceSpec_proven).2.2.1 [.bytes (c :: r) false] ⟨_, List.mem_cons_self, rfl⟩
      (by intro a ha _; simp at ha; subst ha; rfl)
      (by intro a ha b ba hab; simp at ha; subst ha; cases hab; exact hx)]
    rfl

/-- For every ASCII `bytes` URL, every `allow_fragments` and `missing_as_none`: `urlparse` and
`urldefrag` on it give exactly what they give on the decoded `str`, as a `bytes` result (the same
fields, `_keep_empty` kept), and raise the same errors. Source: (a), the `bytes` path against the
`str` path; the docs' "Parsing ASCII Encoded Bytes" ("these functions ... also accept bytes ...
the result ... will contain bytes"). -/
def ParseBytesTwin : Prop :=
  ∀ (nfkc : Str → Str) (ipk : Str → Option Bool) (x : Str) (frag mn : Bool), (∀ c ∈ x, c < 128) →
    urlparse nfkc ipk (.bytes x false) .none frag mn =
      (urlparse nfkc ipk (.str x) .none frag mn).map (fun r => { r with isBytes := true }) ∧
    urldefrag nfkc ipk (.bytes x false) mn =
      (urldefrag nfkc ipk (.str x) mn).map (fun r => { r with isBytes := true })

theorem parseBytesTwin_proven : ParseBytesTwin := by
  intro nfkc ipk x frag mn hx
  constructor
  · have es := urlparse_eq nfkc ipk x none frag mn
    simp only [toArgStr] at es
    rw [es]
    unfold urlparse urlparseCore
    simp only [decodeArgs_ascii x hx, bind, Except.bind, List.headD_cons, Option.getD_some,
      List.getD_cons_succ, List.getD_cons_zero]
    have hc := urlsplitCore_eq nfkc ipk x none frag
    simp only [Option.map_none] at hc
    rw [hc]
    cases netlocChk nfkc ipk (splitPure x frag).2.1 with
    | error e => rfl
    | ok v =>
      have ha := parseRes_ascii x frag mn hx
      have hm := mkRes_ascii true (parseRes x none frag mn).fields mn ha
      simp only [Except.map]
      simp only [parseRes, schemeWith_none] at hm ⊢
      unfold pathParams at hm
      exact hm
  · rw [urldefrag_eq]
    unfold urldefrag
    simp only [coerce_one_bytes x hx, bind, Except.bind, List.headD_cons, pure, Except.pure]
    by_cases h35 : 35 ∈ x
    · rw [if_pos (by simpa using h35), if_pos h35]
      have hc := urlsplitCore_eq nfkc ipk x none true
      simp only [Option.map_none] at hc
      rw [hc]
      cases netlocChk nfkc ipk (splitPure x true).2.1 with
      | error e => rfl
      | ok v =>
        simp only [Except.map, schemeWith_none]
        have hl := urlunsplitCore_lift (splitPure x true).1 (splitPure x true).2.1 (splitPure x true).2.2.1
          (splitPure x true).2.2.2.1 none
        simp only [lift, Option.map_none] at hl
        rw [hl]
        have hm := mkRes_ascii true (defragRes x mn).fields mn (defragRes_ascii x mn hx)
        simp only [defragRes] at hm ⊢
        have hf : (if (!mn && (splitPure x true).2.2.2.2.isNone) = true then some []
            else (splitPure x true).2.2.2.2) = fillMissing mn (splitPure x true).2.2.2.2 := by
          cases mn <;> cases (splitPure x true).2.2.2.2 <;> rfl
        simp only [hf]
        exact hm
    · rw [if_neg (by simpa using h35), if_neg h35]
      have hm := mkRes_ascii true [some x, fillMissing mn none] mn (by
        intro f hf
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl
        · intro s hs; cases hs; exact hx
        · exact fill_some_ascii mn _ (fun t ht => by cases ht))
      have hf : (if (!mn && (none : Option Str).isNone) = true then some [] else none) = fillMissing mn none := by
        cases mn <;> rfl
      simp only [Except.map, defragNoHash, hf]
      exact hm

end PyLean.TextLibs.Url
