import PyLean.TypeObj.ExcOsStrC
import PyLean.TypeObj.ExcPropsBase

/-!
Properties of `OSError_str`, `Objects/exceptions.c:2346-2390`: the format branches, on the
interpreter's version (`osErrorStr`, over every `rt`) and on the C-pointer version
(`OsStrC.osErrorStrC`), and the use-after-free of 3.15.2.
-/

namespace PyLean.TypeObj

/-! ## The interpreter's `OSError_str` -/

/-- **`OSError.__str__` picks its format from the members.** With `filename` set it is
`[Errno e] s: f`, followed by ` -> f2` when `filename2` is set, where `e` and `s` are `str` of
`errno` and `strerror` (`None` when NULL) and `f`, `f2` are `repr`s; without `filename` but
with `errno` and `strerror` it is `[Errno e] s`; otherwise it is `BaseException_str`. The
conversions run in that order, each in the world the previous one left, on the values the
members had at the start, and the first one that raises is the result. Quantified over every
`rt`, so the methods may run any code. -/
def OsErrorStrFormats : Prop :=
  ∀ (rt : Rt) (self : Val) (w : World),
    let d := excDataOf w self
    let eno := orNone (memGet d "errno")
    let se := orNone (memGet d "strerror")
    (∀ (fn f2 : Val) (a b c e : String) (w1 w2 w3 w4 : World),
      memGet d "filename" = some fn → memGet d "filename2" = some f2 →
      rt.str eno w = .ok a w1 → rt.str se w1 = .ok b w2 → rt.repr fn w2 = .ok c w3 →
      rt.repr f2 w3 = .ok e w4 →
      osErrorStr rt self w = .ok (.str s!"[Errno {a}] {b}: {c} -> {e}") w4) ∧
    (∀ (fn : Val) (a b c : String) (w1 w2 w3 : World),
      memGet d "filename" = some fn → memGet d "filename2" = none →
      rt.str eno w = .ok a w1 → rt.str se w1 = .ok b w2 → rt.repr fn w2 = .ok c w3 →
      osErrorStr rt self w = .ok (.str s!"[Errno {a}] {b}: {c}") w3) ∧
    (∀ (fn : Val) (er : PyErr) (w1 : World),
      memGet d "filename" = some fn → rt.str eno w = .err er w1 →
      osErrorStr rt self w = .err er w1) ∧
    (∀ (x y : Val) (a b : String) (w1 w2 : World),
      memGet d "filename" = none → memGet d "errno" = some x → memGet d "strerror" = some y →
      rt.str x w = .ok a w1 → rt.str y w1 = .ok b w2 →
      osErrorStr rt self w = .ok (.str s!"[Errno {a}] {b}") w2) ∧
    (memGet d "filename" = none → (memGet d "errno" = none ∨ memGet d "strerror" = none) →
      osErrorStr rt self w = baseExceptionStr rt self w)

theorem osErrorStrFormats_proven : OsErrorStrFormats := by
  intro rt self w d eno se
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro fn f2 a b c e w1 w2 w3 w4 hf hf2 h1 h2 h3 h4
    simp only [osErrorStr, M.bind_app, getW_app]
    simp only [d] at hf hf2
    simp [hf, hf2, eno, se, d] at h1 h2 h3 h4 ⊢
    simp [h1, h2, h3, h4]
  · intro fn a b c w1 w2 w3 hf hf2 h1 h2 h3
    simp only [osErrorStr, M.bind_app, getW_app]
    simp only [d] at hf hf2
    simp [hf, hf2, eno, se, d] at h1 h2 h3 ⊢
    simp [h1, h2, h3]
  · intro fn er w1 hf h1
    simp only [osErrorStr, M.bind_app, getW_app]
    simp only [d] at hf
    simp [hf, eno, d] at h1 ⊢
    simp [h1]
  · intro x y a b w1 w2 hf hx hy h1 h2
    simp only [osErrorStr, M.bind_app, getW_app]
    simp only [d] at hf hx hy
    simp [hf, hx, hy, h1, h2]
  · intro hf hn
    simp only [d] at hf hn
    simp only [osErrorStr, M.bind_app, getW_app, hf]
    rcases hn with hn | hn <;> simp [hn]

/-! ## The C version, with reference counts -/

namespace OsStrC

/-- What a conversion of `a` returns when the method runs nothing: `none` for a freed object. -/
def methRes (str : Bool) (s : St) (a : Nat) : Option (Option String) :=
  if a == 0 then some (some "None") else (find s a).map fun o => (if str then o.str else o.repr).result

def asCR (r : Option String) (s : St) : CR String :=
  match r with
  | some x => .ok x s
  | none => .raise s

/-- Every `__str__` and `__repr__` on the heap assigns nothing. -/
def pureSt (s : St) : Bool := s.objs.all fun p => p.2.str.acts.isEmpty && p.2.repr.acts.isEmpty

theorem inc_dec_objs (a : Nat) (objs : List (Nat × CObj)) (h : ∀ p ∈ objs, 1 ≤ p.2.rc) :
    (objs.filterMap (stepAt a incO)).filterMap (stepAt a decO) = objs := by
  induction objs with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨k, ⟨rc, st, rp⟩⟩ := p
    have hp : 1 ≤ rc := h _ (List.mem_cons_self ..)
    have ih' := ih fun q hq => h q (List.mem_cons_of_mem _ hq)
    by_cases ha : k = a
    · subst ha
      have hn : ¬ (rc + 1 ≤ 1) := by omega
      simp [List.filterMap_cons, stepAt, incO, decO, hn, ih']
    · have hb : (k == a) = false := by simpa using ha
      simp [List.filterMap_cons, stepAt, hb, ih']

theorem decref_incref (a : Nat) (s : St) (h : ∀ p ∈ s.objs, 1 ≤ p.2.rc) :
    decref a (incref a s) = s := by
  unfold decref incref
  by_cases ha : a == 0
  · simp [ha]
  · simp only [ha, Bool.false_eq_true, if_false, mapObj, inc_dec_objs a s.objs h]

theorem wf_rc {s : St} (h : wf s = true) : ∀ p ∈ s.objs, 1 ≤ p.2.rc := by
  intro p hp
  simp only [wf, Bool.and_eq_true, List.all_eq_true] at h
  have := h.1.2 p hp
  simp at this
  exact this.2

theorem find_mem {s : St} {a : Nat} {o : CObj} (h : find s a = some o) : (a, o) ∈ s.objs := by
  simp only [find, Option.map_eq_some_iff] at h
  obtain ⟨p, hp, rfl⟩ := h
  have hm := List.mem_of_find?_eq_some hp
  have hk := List.find?_some hp
  simp at hk
  rw [← hk]
  exact hm

theorem conv_pure {s : St} {str : Bool} {a : Nat} {r : Option String} (hw : wf s = true)
    (hp : pureSt s = true) (hr : methRes str s a = some r) : conv str a s = asCR r s := by
  unfold methRes at hr
  unfold conv
  by_cases ha : a == 0
  · simp [ha] at hr
    subst hr
    simp [ha, asCR]
  · simp only [ha, if_false, Bool.false_eq_true] at hr ⊢
    cases hf : find s a with
    | none => simp [hf] at hr
    | some o =>
      simp only [hf, Option.map_some, Option.some.injEq] at hr
      have hm := find_mem hf
      simp only [pureSt, List.all_eq_true] at hp
      have hpo := hp _ hm
      simp only [Bool.and_eq_true, List.isEmpty_iff] at hpo
      have hacts : (if str = true then o.str else o.repr).acts = [] := by
        cases str <;> simp [hpo.1, hpo.2]
      simp only [hacts, List.foldl_nil, decref_incref a s (wf_rc hw)]
      rw [hr]
      cases r <;> rfl

/-- **The four branches of 3.15.2's `OSError_str`.** In a reachable state where no `__str__`
or `__repr__` assigns a member, the result is `[Errno e] s: f -> f2` with both filenames,
`[Errno e] s: f` with only the first, `[Errno e] s` with no filename but `errno` and
`strerror`, and `BaseException_str` otherwise; a `str(errno)` that raises is the result. The
hypotheses are the reachability invariant `wf` and the case the statement is about (pure
methods): the next statement is about the methods that are not. -/
def OsErrorStrBranches : Prop :=
  ∀ s : St, wf s = true → pureSt s = true →
    (∀ fn f2 a b c d, s.filename = some fn → s.filename2 = some f2 →
      methRes true s (orNoneC s.errno) = some (some a) →
      methRes true s (orNoneC s.strerror) = some (some b) →
      methRes false s fn = some (some c) → methRes false s f2 = some (some d) →
      osErrorStrC s = .ok s!"[Errno {a}] {b}: {c} -> {d}" s) ∧
    (∀ fn a b c, s.filename = some fn → s.filename2 = none →
      methRes true s (orNoneC s.errno) = some (some a) →
      methRes true s (orNoneC s.strerror) = some (some b) →
      methRes false s fn = some (some c) →
      osErrorStrC s = .ok s!"[Errno {a}] {b}: {c}" s) ∧
    (∀ fn, s.filename = some fn → methRes true s (orNoneC s.errno) = some none →
      osErrorStrC s = .raise s) ∧
    (∀ x y a b, s.filename = none → s.errno = some x → s.strerror = some y →
      methRes true s x = some (some a) → methRes true s y = some (some b) →
      osErrorStrC s = .ok s!"[Errno {a}] {b}" s) ∧
    (s.filename = none → (s.errno = none ∨ s.strerror = none) → osErrorStrC s = baseStr s)

theorem osErrorStrBranches_proven : OsErrorStrBranches := by
  intro s hw hp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro fn f2 a b c d hf hf2 h1 h2 h3 h4
    simp only [osErrorStrC, hf, hf2, conv_pure hw hp h1, asCR, CR.bind, conv_pure hw hp h2,
      conv_pure hw hp h3, conv_pure hw hp h4]
  · intro fn a b c hf hf2 h1 h2 h3
    simp only [osErrorStrC, hf, hf2, conv_pure hw hp h1, asCR, CR.bind, conv_pure hw hp h2,
      conv_pure hw hp h3]
  · intro fn hf h1
    unfold osErrorStrC
    rw [hf]
    cases hf2 : s.filename2 <;> simp only [conv_pure hw hp h1, asCR, CR.bind]
  · intro x y a b hf hx hy h1 h2
    simp only [osErrorStrC, hf, hx, hy, conv_pure hw hp h1, asCR, CR.bind, conv_pure hw hp h2]
  · intro hf hn
    unfold osErrorStrC
    rw [hf]
    rcases hn with hn | hn <;> simp [hn]

/-- **`OSError_str` does not crash**: from every reachable state, whatever the `__str__` and
`__repr__` of the members do among the member assignments of `Act`, no conversion reads a freed
object. FALSE on 3.15.2: the members are borrowed (`:2372-2388`), so an `errno` whose
`__str__` sets `e.filename = None` frees the filename object, and the `%R` that follows reads
it. -/
def OsErrorStrNoCrash : Prop :=
  ∀ s : St, wf s = true → (osErrorStrC s).isUb = false

/-- `e = OSError(Errno(), "s", FN())` after `del FN`: `errno` is object 1, held by the member
and the args tuple, whose `__str__` runs `e.filename = None` and returns `"1"`; `strerror` is
the str `"s"`; `filename` is the `FN()` instance, held only by the member (`oserror_init` cut
args to two, `:2153-2162`). The reproducer of `typeobj-exc-oserror-str-borrowed-free`. -/
def uafState : St :=
  { objs := [(1, ⟨2, { acts := [.setNone .filename], result := some "1" }, { result := some "e" }⟩),
             (2, ⟨2, { result := some "s" }, { result := some "'s'" }⟩),
             (3, ⟨1, { result := some "fn" }, { result := some "fn" }⟩)]
    errno := some 1, strerror := some 2, filename := some 3, args := [1, 2] }

theorem uafState_wf : wf uafState = true := by decide +kernel

theorem uafState_ub : (osErrorStrC uafState).isUb = true := by decide +kernel

theorem osErrorStrNoCrash_refuted : ¬OsErrorStrNoCrash := by
  intro h
  have := h uafState uafState_wf
  rw [uafState_ub] at this
  exact Bool.noConfusion this

/-- **The fix removes this crash.** With the strong references of gh-160822, the same state
formats as `[Errno 1] s: fn`, which is what main prints for the reproducer. -/
def OsErrorStrFixedOnUaf : Prop :=
  ∃ s', osErrorStrFixed uafState = .ok "[Errno 1] s: fn" s'

theorem osErrorStrFixedOnUaf_proven : OsErrorStrFixedOnUaf := ⟨_, rfl⟩

/-- **The fixed `OSError_str` never reads a freed object**, from every reachable state and for
every `Act`-method. Open: it needs an invariant that the counts cover the members, the args and
the pinned references through every `runAct`, which is not written yet. -/
def OsErrorStrFixedNoCrash : Prop :=
  ∀ s : St, wf s = true → (osErrorStrFixed s).isUb = false

end OsStrC

end PyLean.TypeObj
