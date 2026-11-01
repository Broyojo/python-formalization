import PyLean.CoreLibs.Coll.Namedtuple
import PyLean.CoreLibs.Coll.ChainMapProps

/-!
Properties of `namedtuple`. The Unicode facts are hypotheses on `U : UniId`, so a property
holds for the real database as soon as it holds for all `U` with those facts; the refutations
use `UFi`, which agrees with CPython on the three strings it is applied to.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace PyLean.CoreLibs.Coll

open PyLean

/-- `str.isidentifier` and NFKC on `T`, `ﬁ` (U+FB01) and `fi`. -/
def UFi : UniId where
  isidentifier s := s == "T" || s == "ﬁ" || s == "fi"
  nfkc s := if s = "ﬁ" then "fi" else s

/-! ### Names -/

theorem posName_toList (i : Nat) : (posName i).toList = '_' :: Nat.toDigits 10 i := by
  simp [posName, Nat.toString_eq_repr, Nat.toList_repr]

theorem posName_inj {a b : Nat} (h : posName a = posName b) : a = b := by
  have h1 : (posName a).toList = (posName b).toList := by rw [h]
  simp only [posName_toList, List.cons.injEq, true_and] at h1
  have := Nat.ofDigitChars_ten_toDigits (n := a)
  rw [h1, Nat.ofDigitChars_ten_toDigits] at this
  exact this.symm

theorem startsUnderscore_posName (i : Nat) : startsUnderscore (posName i) = true := by
  simp [startsUnderscore, posName_toList]

theorem kw_noUnderscore : ∀ k ∈ kwlist, startsUnderscore k = false := by decide

theorem iskeyword_posName (i : Nat) : iskeyword (posName i) = false := by
  cases h : iskeyword (posName i) with
  | false => rfl
  | true =>
    have hm : posName i ∈ kwlist := by simpa [iskeyword] using h
    have := kw_noUnderscore _ hm
    rw [startsUnderscore_posName] at this
    simp at this

theorem kw_consts : iskeyword "None" = true ∧ iskeyword "True" = true ∧ iskeyword "False" = true := by
  decide

theorem cls_ne_posName (i : Nat) : "_cls" ≠ posName i := by
  intro h
  have h1 : ("_cls").toList = (posName i).toList := by rw [h]
  rw [posName_toList] at h1
  have h2 : ("_cls").toList = ['_', 'c', 'l', 's'] := by decide
  rw [h2] at h1
  simp only [List.cons.injEq, true_and] at h1
  have hm : 'c' ∈ Nat.toDigits 10 i := by rw [← h1]; simp
  have := Nat.isDigit_of_mem_toDigits (by decide) (by decide) hm
  revert this
  decide

theorem cls_underscore : startsUnderscore "_cls" = true := by decide

/-! ### `rename` -/

/-- A name that passes the `rename` test. -/
def Kept (U : UniId) (n : String) : Prop :=
  U.isidentifier n = true ∧ iskeyword n = false ∧ startsUnderscore n = false

theorem kept_of_good {U : UniId} {seen : List String} {n : String}
    (h : (!U.isidentifier n || iskeyword n || startsUnderscore n || seen.contains n) = false) :
    Kept U n ∧ n ∉ seen := by
  simp only [Bool.or_eq_false_iff, Bool.not_eq_false', List.contains_eq_mem,
    decide_eq_false_iff_not] at h
  exact ⟨⟨h.1.1.1, h.1.1.2, h.1.2⟩, h.2⟩

theorem renameLoop_length (U : UniId) (seen : List String) (i : Nat) (l : List String) :
    (renameLoop U seen i l).length = l.length := by
  induction l generalizing seen i with
  | nil => rfl
  | cons a t ih => simp [renameLoop, ih]

theorem renameLoop_mem (U : UniId) (seen : List String) (i : Nat) (l : List String) :
    ∀ r ∈ renameLoop U seen i l, (∃ j, j ≥ i ∧ r = posName j) ∨ (r ∈ l ∧ r ∉ seen ∧ Kept U r) := by
  induction l generalizing seen i with
  | nil => simp [renameLoop]
  | cons a t ih =>
    intro r hr
    simp only [renameLoop, List.mem_cons] at hr
    rcases hr with hr | hr
    · by_cases hb : (!U.isidentifier a || iskeyword a || startsUnderscore a || seen.contains a) = true
      · simp only [hb, if_true] at hr
        exact Or.inl ⟨i, Nat.le_refl _, hr⟩
      · have hb' : (!U.isidentifier a || iskeyword a || startsUnderscore a || seen.contains a) = false := by
          simpa using hb
        simp only [hb, if_false] at hr
        subst hr
        have := kept_of_good hb'
        exact Or.inr ⟨by simp, this.2, this.1⟩
    · rcases ih (a :: seen) (i + 1) r hr with ⟨j, hj, e⟩ | ⟨h1, h2, h3⟩
      · exact Or.inl ⟨j, by omega, e⟩
      · simp only [List.mem_cons, not_or] at h2
        exact Or.inr ⟨List.mem_cons_of_mem _ h1, h2.2, h3⟩

theorem renameLoop_nodup (U : UniId) (seen : List String) (i : Nat) (l : List String) :
    (renameLoop U seen i l).Nodup := by
  induction l generalizing seen i with
  | nil => simp [renameLoop]
  | cons a t ih =>
    simp only [renameLoop, List.nodup_cons]
    refine ⟨?_, ih _ _⟩
    intro hm
    by_cases hb : (!U.isidentifier a || iskeyword a || startsUnderscore a || seen.contains a) = true
    · rw [if_pos hb] at hm
      rcases renameLoop_mem U (a :: seen) (i + 1) t _ hm with ⟨j, hj, e⟩ | ⟨_, _, h3⟩
      · have := posName_inj e
        omega
      · have := h3.2.2
        rw [startsUnderscore_posName] at this
        simp at this
    · rw [if_neg hb] at hm
      have hb' : (!U.isidentifier a || iskeyword a || startsUnderscore a || seen.contains a) = false := by
        simpa using hb
      rcases renameLoop_mem U (a :: seen) (i + 1) t _ hm with ⟨j, hj, e⟩ | ⟨_, h2, _⟩
      · have := (kept_of_good hb').1.2.2
        rw [e, startsUnderscore_posName] at this
        simp at this
      · simp at h2

theorem renameLoop_get (U : UniId) (seen : List String) (i : Nat) (l : List String) :
    ∀ (k : Nat) (h1 : k < (renameLoop U seen i l).length) (h2 : k < l.length),
      (renameLoop U seen i l)[k] = l[k] ∨ (renameLoop U seen i l)[k] = posName (i + k) := by
  induction l generalizing seen i with
  | nil => intro k _ h2; simp at h2
  | cons a t ih =>
    intro k h1 h2
    cases k with
    | zero =>
      simp only [renameLoop, List.getElem_cons_zero, Nat.add_zero]
      split
      · exact Or.inr rfl
      · exact Or.inl rfl
    | succ m =>
      simp only [renameLoop, List.getElem_cons_succ]
      have h3 : m < t.length := by simpa using h2
      have h4 : m < (renameLoop U (a :: seen) (i + 1) t).length := by
        rw [renameLoop_length]; exact h3
      rcases ih (a :: seen) (i + 1) m h4 h3 with h | h
      · exact Or.inl h
      · right
        rw [h]
        congr 1
        omega

/-! ### The checks -/

theorem checkNames_iff (U : UniId) (l : List String) :
    checkNames U l = .ok () ↔ ∀ n ∈ l, U.isidentifier n = true ∧ iskeyword n = false := by
  induction l with
  | nil => simp [checkNames]
  | cons a t ih =>
    simp only [checkNames, List.mem_cons, forall_eq_or_imp]
    cases h1 : U.isidentifier a with
    | false => simp
    | true =>
      cases h2 : iskeyword a with
      | true => simp
      | false => simpa using ih

theorem checkSeen_iff (rename : Bool) (seen l : List String) :
    checkSeen rename seen l = .ok () ↔
      (rename = false → ∀ n ∈ l, startsUnderscore n = false) ∧ l.Nodup ∧ ∀ n ∈ l, n ∉ seen := by
  induction l generalizing seen with
  | nil => simp [checkSeen]
  | cons a t ih =>
    by_cases h1 : (startsUnderscore a && !rename) = true
    · simp only [Bool.and_eq_true, Bool.not_eq_true'] at h1
      simp [checkSeen, h1.1, h1.2]
    · by_cases h2 : seen.contains a = true
      · have : a ∈ seen := by simpa using h2
        simp [checkSeen, h1, h2, this]
      · have ha : a ∉ seen := by simpa using h2
        have hstep : checkSeen rename seen (a :: t) = checkSeen rename (a :: seen) t := by
          simp only [checkSeen, if_neg h1, if_neg h2]
        rw [hstep, ih]
        constructor
        · rintro ⟨h3, h4, h5⟩
          refine ⟨?_, ?_, ?_⟩
          · intro hr n hn
            rcases List.mem_cons.mp hn with e | e
            · subst e
              subst hr
              simpa using h1
            · exact h3 hr n e
          · refine List.nodup_cons.mpr ⟨?_, h4⟩
            intro hm
            exact h5 a hm (by simp)
          · intro n hn
            rcases List.mem_cons.mp hn with e | e
            · subst e; exact ha
            · intro hs
              exact h5 n e (List.mem_cons_of_mem _ hs)
        · rintro ⟨h3, h4, h5⟩
          have h6 := List.nodup_cons.mp h4
          refine ⟨fun hr n hn => h3 hr n (List.mem_cons_of_mem _ hn), h6.2, ?_⟩
          intro n hn hs
          rcases List.mem_cons.mp hs with e | e
          · subst e; exact h6.1 hn
          · exact h5 n (List.mem_cons_of_mem _ hn) e

theorem firstDup_none {seen l : List String} (h : l.Nodup) (hd : ∀ n ∈ l, n ∉ seen) :
    firstDup seen l = none := by
  induction l generalizing seen with
  | nil => rfl
  | cons a t ih =>
    simp only [List.nodup_cons] at h
    have ha : ¬ seen.contains a = true := by simpa using hd a (by simp)
    simp only [firstDup, ha, if_false]
    apply ih h.2
    intro n hn
    simp only [List.mem_cons, not_or]
    exact ⟨fun e => h.1 (e ▸ hn), hd n (List.mem_cons_of_mem _ hn)⟩

theorem find_none {l : List String} (h : ∀ n ∈ l, iskeyword n = false) :
    l.find? (fun a => a = "None" ∨ a = "True" ∨ a = "False") = none := by
  rw [List.find?_eq_none]
  intro a ha
  have := h a ha
  simp only [decide_eq_true_eq, not_or]
  obtain ⟨k1, k2, k3⟩ := kw_consts
  refine ⟨?_, ?_, ?_⟩ <;> (intro e; subst e; simp_all)

theorem map_id_of {U : UniId} {l : List String} (h : ∀ n ∈ l, U.nfkc n = n) : l.map U.nfkc = l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.map_cons, h a (by simp)]
    rw [ih (fun n hn => h n (List.mem_cons_of_mem _ hn))]

theorem compile_ok {U : UniId} {l : List String} (hf : ∀ n ∈ l, U.nfkc n = n)
    (hk : ∀ n ∈ l, iskeyword n = false) (hn : l.Nodup) (hc : "_cls" ∉ l) :
    compileNew U l = .ok l := by
  unfold compileNew
  simp only [map_id_of hf]
  rw [find_none hk, firstDup_none hn]
  intro n hm
  simp only [List.mem_singleton]
  exact fun e => hc (e ▸ hm)

/-- A successful run in terms of its three checks. -/
theorem namedtuple_ok {ν : Type} {U : UniId} {tn : String} {fn : FieldNames} {r : Bool} {d : List ν}
    {names : List String}
    (hn : names = (if r then renameLoop U [] 0 (fieldList fn) else fieldList fn))
    (h1 : checkNames U (tn :: names) = .ok ()) (h2 : checkSeen r [] names = .ok ())
    (h3 : d.length ≤ names.length) {args : List String} (h4 : compileNew U names = .ok args) :
    namedtuple U tn fn r (some d) = .ok {
      typename := tn, fields := names, args, defaults := d,
      fieldDefaults := fieldDefaultsOf names d,
      doc := tn ++ "(" ++ argListOf names ++ ")",
      newDoc := "Create new instance of " ++ tn ++ "(" ++ argListOf names ++ ")" } := by
  have h5 : ¬ d.length > names.length := by omega
  simp only [namedtuple, ← hn, h1, h2, h4, Option.getD_some, h5, if_false, bind, Except.bind, pure,
    Except.pure]

/-- The result of a successful run: it passed the checks, its parameters are the normalised
fields, and the fields have no repeat. -/
theorem namedtuple_inv {ν : Type} {U : UniId} {tn : String} {fn : FieldNames} {r : Bool}
    {d : Option (List ν)} {T : NT ν} (h : namedtuple U tn fn r d = .ok T) :
    checkNames U (tn :: T.fields) = .ok () ∧ checkSeen r [] T.fields = .ok () ∧
    T.args = T.fields.map U.nfkc ∧ T.defaults = d.getD [] ∧
    T.fieldDefaults = fieldDefaultsOf T.fields T.defaults ∧
    T.fields = (if r then renameLoop U [] 0 (fieldList fn) else fieldList fn) := by
  have hcomp : ∀ (U : UniId) (l a : List String), compileNew U l = .ok a → a = l.map U.nfkc := by
    intro U l a hc
    unfold compileNew at hc
    simp only at hc
    split at hc
    · simp at hc
    · split at hc
      · simp at hc
      · simpa using hc.symm
  have hthrow : ∀ (e : PyExc) (α : Type), (throw e : Except PyExc α) = .error e := fun _ _ => rfl
  unfold namedtuple at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  generalize hN : (if r = true then renameLoop U [] 0 (fieldList fn) else fieldList fn) = names at h
  cases hc1 : checkNames U (tn :: names) with
  | error e => simp [hc1] at h
  | ok u1 =>
    cases hc2 : checkSeen r [] names with
    | error e => simp [hc1, hc2] at h
    | ok u2 =>
      by_cases hd : (d.getD []).length > names.length
      · simp [hc1, hc2, hd, hthrow] at h
      · cases hc3 : compileNew U names with
        | error e => simp [hc1, hc2, hd, hc3] at h
        | ok args =>
          simp only [hc1, hc2, hd, hc3, if_false, Except.ok.injEq] at h
          subst h
          exact ⟨hc1, hc2, hcomp _ _ _ hc3, rfl, rfl, rfl⟩

/-- `namedtuple('T', ['ﬁ'], defaults=[])` as computed. -/
def fiT : NT Nat := {
  typename := "T", fields := ["\ufb01"], args := ["fi"], defaults := [],
  fieldDefaults := fieldDefaultsOf ["\ufb01"] [],
  doc := "T" ++ "(" ++ argListOf ["\ufb01"] ++ ")",
  newDoc := "Create new instance of " ++ "T" ++ "(" ++ argListOf ["\ufb01"] ++ ")" }

theorem fi_class : namedtuple UFi "T" (.list ["\ufb01"]) false (some []) = .ok fiT :=
  namedtuple_ok (fn := .list ["\ufb01"]) (r := false) (names := ["\ufb01"]) rfl (by decide) (by decide)
    (by simp) (by decide)

/-! ### Refuted: `rename=True` promises a class -/

/-- Doc/library/collections.rst, `namedtuple`: "If rename is true, invalid fieldnames are
automatically replaced with positional names", so for a valid `typename` there is no list of names
that makes `namedtuple(..., rename=True)` fail. False: `['ﬁ', 'fi']` pass every check, being
distinct strings, and the compiler then normalises both to `fi`: `SyntaxError`. -/
def NamedtupleRenameTotal : Prop :=
  ∀ (U : UniId) (tn : String) (names : List String), U.isidentifier tn = true → iskeyword tn = false →
    ∃ T : NT Nat, namedtuple U tn (.list names) true none = .ok T

theorem namedtupleRenameTotal_refuted : ¬ NamedtupleRenameTotal := by
  intro h
  obtain ⟨T, hT⟩ := h UFi "T" ["ﬁ", "fi"] (by decide) (by decide)
  have : (namedtuple (ν := Nat) UFi "T" (.list ["ﬁ", "fi"]) true none).toBool = false := by decide
  rw [hT] at this
  simp [Except.toBool] at this

/-- The narrowed statement, on names NFKC leaves alone: `rename=True` always gives a class, each
field is the name given or `_i`, with `_fields` free of repeats and `__new__` having exactly
those parameters. The hypotheses on `posName` are facts about ASCII names. -/
def NamedtupleRenameNarrow : Prop :=
  ∀ (U : UniId) (tn : String) (names : List String) (d : List Nat),
    U.isidentifier tn = true → iskeyword tn = false →
    (∀ i, U.isidentifier (posName i) = true) → (∀ i, U.nfkc (posName i) = posName i) →
    (∀ n ∈ names, U.nfkc n = n) → d.length ≤ names.length →
    ∃ T : NT Nat, namedtuple U tn (.list names) true (some d) = .ok T ∧
      T.fields.length = names.length ∧ T.args = T.fields ∧ T.fields.Nodup ∧
      ∀ (i : Nat) (h1 : i < T.fields.length) (h2 : i < names.length),
        T.fields[i] = names[i] ∨ T.fields[i] = posName i

theorem namedtupleRenameNarrow_proven : NamedtupleRenameNarrow := by
  intro U tn names d ht hk hp1 hp2 hf hd
  let R := renameLoop U [] 0 names
  have hlen : R.length = names.length := renameLoop_length ..
  have hnd : R.Nodup := renameLoop_nodup ..
  have hmem := renameLoop_mem U [] 0 names
  have hid : ∀ r ∈ R, U.isidentifier r = true ∧ iskeyword r = false := by
    intro r hr
    rcases hmem r hr with ⟨j, _, e⟩ | ⟨_, _, h3⟩
    · rw [e]; exact ⟨hp1 j, iskeyword_posName j⟩
    · exact ⟨h3.1, h3.2.1⟩
  have hfix : ∀ r ∈ R, U.nfkc r = r := by
    intro r hr
    rcases hmem r hr with ⟨j, _, e⟩ | ⟨h1, _, _⟩
    · rw [e]; exact hp2 j
    · exact hf r h1
  have hcls : "_cls" ∉ R := by
    intro hm
    rcases hmem _ hm with ⟨j, _, e⟩ | ⟨_, _, h3⟩
    · exact cls_ne_posName j e
    · have := h3.2.2
      rw [cls_underscore] at this
      simp at this
  have h1 : checkNames U (tn :: R) = .ok () := by
    rw [checkNames_iff]
    intro n hn
    rcases List.mem_cons.mp hn with e | e
    · subst e; exact ⟨ht, hk⟩
    · exact hid n e
  have h2 : checkSeen true [] R = .ok () := by
    rw [checkSeen_iff]
    exact ⟨by simp, hnd, by simp⟩
  have h4 : compileNew U R = .ok R := compile_ok hfix (fun n hn => (hid n hn).2) hnd hcls
  refine ⟨_, namedtuple_ok (fn := .list names) (r := true) (names := R) rfl h1 h2 (by omega) h4, hlen, rfl,
    hnd, ?_⟩
  intro i h3 h4
  have := renameLoop_get U [] 0 names i h3 h4
  simpa using this

/-- Without `rename`, on names NFKC leaves alone, `namedtuple` succeeds exactly on valid input:
the type name and fields are identifiers and not keywords, no field starts with `_`, no field
repeats. Docs: "Any valid Python identifier may be used for a fieldname except for names starting
with an underscore. Valid identifiers consist of letters, digits, and underscores but do not
start with a digit or underscore and cannot be a keyword". -/
def NamedtupleValidation : Prop :=
  ∀ (U : UniId) (tn : String) (names : List String) (d : List Nat),
    (∀ n ∈ names, U.nfkc n = n) → d.length ≤ names.length →
    ((∃ T : NT Nat, namedtuple U tn (.list names) false (some d) = .ok T ∧ T.fields = names ∧ T.args = names) ↔
      (∀ n ∈ tn :: names, U.isidentifier n = true ∧ iskeyword n = false) ∧
      (∀ n ∈ names, startsUnderscore n = false) ∧ names.Nodup)

theorem namedtupleValidation_proven : NamedtupleValidation := by
  intro U tn names d hf hd
  constructor
  · rintro ⟨T, hT, h1, _⟩
    obtain ⟨hc1, hc2, _⟩ := namedtuple_inv hT
    rw [h1] at hc1 hc2
    have := (checkSeen_iff false [] names).mp hc2
    exact ⟨(checkNames_iff U _).mp hc1, this.1 rfl, this.2.1⟩
  · rintro ⟨h1, h2, h3⟩
    have hc1 : checkNames U (tn :: names) = .ok () := (checkNames_iff U _).mpr h1
    have hc2 : checkSeen false [] names = .ok () :=
      (checkSeen_iff false [] names).mpr ⟨fun _ => h2, h3, by simp⟩
    have hcls : "_cls" ∉ names := by
      intro hm
      have := h2 _ hm
      rw [cls_underscore] at this
      simp at this
    have h4 : compileNew U names = .ok names :=
      compile_ok hf (fun n hn => (h1 n (List.mem_cons_of_mem _ hn)).2) h3 hcls
    exact ⟨_, namedtuple_ok (fn := .list names) (r := false) (names := names) rfl hc1 hc2 hd h4, rfl, rfl⟩

/-! ### Instances -/

theorem zip_WF {ν : Type} {F : List String} {vals : List ν} (hn : F.Nodup) (hl : vals.length = F.length) :
    D.keys (F.zip vals) = F := by
  unfold D.keys
  exact List.map_fst_zip (by omega)

theorem get?_zip_cons {ν : Type} (kw : D String ν) (a : String) (v : ν) :
    D.get? ((a, v) :: kw) a = some v := by simp [D.get?_cons]

theorem fill_asdict {ν : Type} (d : List ν) (n : Nat) :
    ∀ (F : List String) (vals : List ν) (kw : D String ν) (i : Nat),
      vals.length = F.length → (∀ (p : String × ν), p ∈ F.zip vals → D.get? kw p.1 = some p.2) →
      fillRest kw d n i F = .ok vals := by
  intro F
  induction F with
  | nil =>
    intro vals kw i hl _
    cases vals with
    | nil => rfl
    | cons _ _ => simp at hl
  | cons a t ih =>
    intro vals kw i hl h
    cases vals with
    | nil => simp at hl
    | cons v vs =>
      have hv := h (a, v) (by simp)
      simp only at hv
      have hr := ih vs kw (i + 1) (by simpa using hl) (fun p hp => h p (by simp [hp]))
      simp [fillRest, hv, hr, bind, Except.bind, pure, Except.pure]

theorem checkKw_ok {ν : Type} (args : List String) (kw : D String ν) (h : ∀ p ∈ kw, p.1 ∈ args) :
    checkKw args 0 kw = .ok () := by
  induction kw with
  | nil => rfl
  | cons p t ih =>
    have hp := h p (by simp)
    have ht := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    simp [checkKw, hp, ht]

theorem call_kw {ν : Type} {T : NT ν} {vals : List ν}
    (hargs : T.args = T.fields) (hn : T.fields.Nodup) (hl : vals.length = T.fields.length) :
    ntCall T [] (ntAsdict T vals) = .ok vals := by
  have hk := zip_WF hn hl
  have hwf : D.WF (T.fields.zip vals) := by unfold D.WF; rw [hk]; exact hn
  have hkw : ntAsdict T vals = T.fields.zip vals := update_nil_WF hwf
  have hc : checkKw T.args 0 (T.fields.zip vals) = .ok () := by
    apply checkKw_ok
    intro p hp
    rw [hargs, ← hk]
    exact D.mem_keys_of_mem hp
  have hf : fillRest (T.fields.zip vals) T.defaults T.args.length 0 T.args = .ok vals := by
    rw [hargs]
    apply fill_asdict _ _ _ _ _ _ hl
    intro p hp
    exact D.get?_of_mem_pair hwf (x := p.1) (v := p.2) hp
  simp [ntCall, hkw, hc, hf, bind, Except.bind, pure, Except.pure]

/-- The class docstring, :375-379: `d = p._asdict()` then `Point(**d)` "convert from a dictionary"
gives back `p`. False: `__new__` has the normalised parameter names and `_asdict` the raw
field names, and keywords at run time are not normalised. -/
def NamedtupleAsdictRoundTrip : Prop :=
  ∀ (U : UniId) (tn : String) (names : List String) (r : Bool) (d : Option (List Nat)) (T : NT Nat)
    (vals : List Nat), namedtuple U tn (.list names) r d = .ok T → vals.length = T.fields.length →
    ntCall T [] (ntAsdict T vals) = .ok vals

theorem namedtupleAsdictRoundTrip_refuted : ¬ NamedtupleAsdictRoundTrip := by
  intro h
  have := h UFi "T" ["\ufb01"] false (some []) fiT [0] fi_class rfl
  have h2 : (ntCall fiT [] (ntAsdict fiT [0])).toBool = false := by decide +kernel
  rw [this] at h2
  simp [Except.toBool] at h2

/-- The narrowed statement: when NFKC leaves the fields alone, `T(**p._asdict()) == p`, for
every `rename`, `defaults` and tuple. -/
def NamedtupleAsdictNarrow : Prop :=
  ∀ (U : UniId) (tn : String) (names : List String) (r : Bool) (d : Option (List Nat)) (T : NT Nat)
    (vals : List Nat), namedtuple U tn (.list names) r d = .ok T → vals.length = T.fields.length →
    (∀ n ∈ T.fields, U.nfkc n = n) → ntCall T [] (ntAsdict T vals) = .ok vals

theorem namedtupleAsdictNarrow_proven : NamedtupleAsdictNarrow := by
  intro U tn names r d T vals hT hl hf
  obtain ⟨_, hc2, ha, _⟩ := namedtuple_inv hT
  have hn := ((checkSeen_iff r [] T.fields).mp hc2).2.1
  exact call_kw (by rw [ha, map_id_of hf]) hn hl

/-- `p.field` in source reaches every field. False for the same reason: attributes are stored
under the raw name and source identifiers are normalised, so `p.ﬁ` is an `AttributeError`
on a field `namedtuple` accepted. -/
def NamedtupleSourceAttribute : Prop :=
  ∀ (U : UniId) (tn : String) (names : List String) (d : Option (List Nat)) (T : NT Nat) (vals : List Nat)
    (f : String),
    namedtuple U tn (.list names) false d = .ok T → vals.length = T.fields.length → f ∈ T.fields →
    ntSourceAttr U T vals f = ntGetattr T vals f

theorem namedtupleSourceAttribute_refuted : ¬ NamedtupleSourceAttribute := by
  intro h
  have := h UFi "T" ["\ufb01"] (some []) fiT [0] "\ufb01" fi_class rfl (by simp [fiT])
  have h2 : ntSourceAttr UFi fiT [0] "\ufb01" = ntGetattr fiT [0] "\ufb01" → False := by decide +kernel
  exact h2 this

theorem replLoop_empty {ν : Type} : ∀ (F : List String) (vals : List ν), vals.length = F.length →
    replLoop [] F vals = (vals, [])
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: t, v :: vs, h => by
    have := replLoop_empty t vs (by simpa using h)
    simp [replLoop, D.get?, this]

theorem replLoop_one {ν : Type} (f : String) (x : ν) :
    ∀ (F : List String) (vals : List ν), vals.length = F.length → F.Nodup → f ∈ F →
      replLoop [(f, x)] F vals = ((F.zip vals).map (fun p => if p.1 = f then x else p.2), [])
  | [], _, _, _, hm => by simp at hm
  | _ :: _, [], h, _, _ => by simp at h
  | a :: t, v :: vs, h, hn, hm => by
    simp only [List.nodup_cons] at hn
    have hl : vs.length = t.length := by simpa using h
    by_cases e : f = a
    · subst e
      have hz : (t.zip vs).map (fun p => if p.1 = f then x else p.2) = vs := by
        have hne : ∀ p ∈ t.zip vs, p.1 ≠ f := by
          intro p hp e2
          apply hn.1
          rw [← e2]
          exact (List.of_mem_zip hp).1
        have : (t.zip vs).map (fun p => if p.1 = f then x else p.2) = (t.zip vs).map Prod.snd :=
          List.map_congr_left (fun p hp => by simp [hne p hp])
        rw [this]
        exact List.map_snd_zip (by omega)
      simp [replLoop, D.get?_cons, D.del, replLoop_empty t vs hl, hz]
    · have hm' : f ∈ t := by
        rcases List.mem_cons.mp hm with h2 | h2
        · exact absurd h2 e
        · exact h2
      have hne : ¬ a = f := fun h2 => e h2.symm
      have hne2 : ¬ f = a := e
      have hr := replLoop_one f x t vs hl hn.2 hm'
      simp [replLoop, D.get?_cons, hne2, hr, hne]

theorem replLoop_miss {ν : Type} (f : String) (x : ν) :
    ∀ (F : List String) (vals : List ν), vals.length = F.length → f ∉ F →
      replLoop [(f, x)] F vals = (vals, [(f, x)])
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: t, v :: vs, h, hm => by
    simp only [List.mem_cons, not_or] at hm
    have hr := replLoop_miss f x t vs (by simpa using h) hm.2
    have hne : ¬ f = a := hm.1
    simp [replLoop, D.get?_cons, hne, hr]

/-- The generated instance methods on every class `namedtuple` returns and every tuple of the
right length: `_make` gives back the items and refuses a wrong length, `_replace()` is the
identity, `_replace(f=x)` changes that field and no other, and an unknown name is a
`TypeError`. `getattr(p, _fields[i]) == p[i]`, `_asdict` keeps the field order. -/
def NamedtupleInstanceMethods : Prop :=
  ∀ (U : UniId) (tn : String) (names : List String) (r : Bool) (d : Option (List Nat)) (T : NT Nat)
    (vals : List Nat) (f : String) (x : Nat),
    namedtuple U tn (.list names) r d = .ok T → vals.length = T.fields.length →
    ntMake T vals = .ok vals ∧
    (∀ l : List Nat, l.length ≠ T.fields.length →
      ntMake T l = .error (.typeError s!"Expected {T.fields.length} arguments, got {l.length}")) ∧
    ntReplace T vals [] = .ok vals ∧
    (f ∈ T.fields →
      ntReplace T vals [(f, x)] = .ok ((T.fields.zip vals).map (fun p => if p.1 = f then x else p.2))) ∧
    (f ∉ T.fields → ntReplace T vals [(f, x)] =
      .error (.typeError ("Got unexpected field names: [" ++ pyStrRepr f ++ "]"))) ∧
    (∀ p ∈ T.fields.zip vals, ntGetattr T vals p.1 = some p.2) ∧
    D.keys (ntAsdict T vals) = T.fields

theorem namedtupleInstanceMethods_proven : NamedtupleInstanceMethods := by
  intro U tn names r d T vals f x hT hl
  obtain ⟨_, hc2, _⟩ := namedtuple_inv hT
  have hn := ((checkSeen_iff r [] T.fields).mp hc2).2.1
  have hmk : ntMake T vals = .ok vals := by simp [ntMake, hl]
  have hk := zip_WF hn hl
  have hwf : D.WF (T.fields.zip vals) := by unfold D.WF; rw [hk]; exact hn
  refine ⟨hmk, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro l h
    simp [ntMake, h]
  · simp [ntReplace, replLoop_empty T.fields vals hl, hmk, bind, Except.bind, pure, Except.pure]
  · intro hm
    have hlz : ((T.fields.zip vals).map (fun p => if p.1 = f then x else p.2)).length = T.fields.length := by
      simp; omega
    have h2 : ntMake T ((T.fields.zip vals).map (fun p => if p.1 = f then x else p.2)) =
        .ok ((T.fields.zip vals).map (fun p => if p.1 = f then x else p.2)) := by
      simp only [ntMake, hlz, ne_eq, not_true_eq_false, if_false]
    simp only [ntReplace, replLoop_one f x T.fields vals hl hn hm, bind, Except.bind, h2, pure,
      Except.pure]
    simp
  · intro hm
    simp only [ntReplace, replLoop_miss f x T.fields vals hl hm, bind, Except.bind, hmk]
    simp
    rfl
  · intro p hp
    exact D.get?_of_mem_pair hwf (x := p.1) (v := p.2) hp
  · have : ntAsdict T vals = T.fields.zip vals := update_nil_WF hwf
    rw [this, hk]

theorem fill_defaults (d : List Nat) (n : Nat) :
    ∀ (rest : List String) (i : Nat), i + rest.length = n → i + d.length ≥ n →
      fillRest [] d n i rest = .ok (d.drop (i + d.length - n)) := by
  intro rest
  induction rest with
  | nil =>
    intro i h1 _
    simp only [List.length_nil, Nat.add_zero] at h1
    subst h1
    simp [fillRest]
  | cons a t ih =>
    intro i h1 h2
    simp only [List.length_cons] at h1
    have hlt : i + d.length - n < d.length := by omega
    have hr := ih (i + 1) (by omega) (by omega)
    have e : i + 1 + d.length - n = i + d.length - n + 1 := by omega
    rw [e] at hr
    have hg : d[i + d.length - n]? = some d[i + d.length - n] := List.getElem?_eq_getElem hlt
    simp only [fillRest, D.get?_nil, h2, if_true, hg, hr, bind, Except.bind, pure, Except.pure]
    rw [List.drop_eq_getElem_cons hlt]

theorem map_fst_zip_take {α β : Type} : ∀ (a : List α) (b : List β), (a.zip b).map Prod.fst = a.take b.length
  | [], _ => by simp
  | _ :: _, [] => by simp
  | x :: t, y :: s => by
    simp [map_fst_zip_take t s]

/-- `defaults` belong to the rightmost parameters (docs: "Since fields with a default value must come
after any fields without a default, the defaults are applied to the rightmost parameters"):
`T(*pos)` with `pos` covering the fields without a default fills the rest from `defaults`
in order, and `_field_defaults` has exactly the last `len(defaults)` fields, in order. -/
def NamedtupleDefaults : Prop :=
  ∀ (U : UniId) (tn : String) (names : List String) (r : Bool) (d : List Nat) (T : NT Nat)
    (pos : List Nat), namedtuple U tn (.list names) r (some d) = .ok T →
    (pos.length ≤ T.fields.length → T.fields.length ≤ pos.length + d.length →
      ntCall T pos [] = .ok (pos ++ d.drop (pos.length + d.length - T.fields.length))) ∧
    D.keys T.fieldDefaults = T.fields.drop (T.fields.length - d.length)

theorem namedtupleDefaults_proven : NamedtupleDefaults := by
  intro U tn names r d T pos hT
  obtain ⟨_, hc2, ha, hdf, hfd, _⟩ := namedtuple_inv hT
  have hn := ((checkSeen_iff r [] T.fields).mp hc2).2.1
  have hd : T.defaults = d := by simpa using hdf
  have hlen : T.args.length = T.fields.length := by rw [ha]; simp
  constructor
  · intro h1 h2
    have hf := fill_defaults d T.fields.length (T.args.drop pos.length) pos.length
      (by simp; omega) (by omega)
    have hp : ¬ pos.length > T.fields.length := by omega
    simp only [ntCall, hp, if_false, checkKw, hd, hlen, hf, bind, Except.bind, pure, Except.pure]
  · have hkeys : D.keys (T.fields.reverse.zip d.reverse).reverse =
        T.fields.drop (T.fields.length - d.length) := by
      unfold D.keys
      simp only [List.map_reverse, map_fst_zip_take, List.length_reverse]
      rw [List.take_reverse]
      simp
    have hw : D.WF (T.fields.reverse.zip d.reverse).reverse := by
      unfold D.WF
      rw [hkeys]
      exact hn.sublist (List.drop_sublist _ _)
    rw [hfd, hd]
    unfold fieldDefaultsOf
    rw [update_nil_WF hw]
    exact hkeys

end PyLean.CoreLibs.Coll
