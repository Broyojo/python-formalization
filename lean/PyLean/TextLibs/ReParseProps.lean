import PyLean.TextLibs.ReProps

/-!
Laws that exercise the rest of `Lib/re/_parser.py`: the group state, the tokenizer, `getwidth`,
the factoring in `_parse_sub`, `_parse_flags`, and the main loop on plain text.
-/

namespace PyLean.TextLibs.Re

open PyLean

set_option linter.unusedSimpArgs false

/-- A Python string literal as code points. -/
def strOf (s : String) : List Nat := s.toList.map Char.toNat

/-! ### Group state -/

/-- `opengroup` returns the next group number, grows `groups` by one and records the name, and
`closegroup` makes the group referable, the only way `checkgroup` turns true. -/
def GroupLifecycle : Prop :=
  ∀ (st st' : PSt) (name : Option (List Nat)) (gid : Nat) (w : Nat × Nat),
    opengroupPure st name = .ok (gid, st') →
      gid = st.groupwidths.length ∧ st'.groupwidths.length = gid + 1 ∧
      checkgroup st' gid = false ∧ checkgroup (closegroupPure st' gid w) gid = true ∧
      (∀ n, name = some n → st'.groupdict.lookup n = some gid)

theorem lookup_snoc' (n : List Nat) (g : Nat) : ∀ l : List (List Nat × Nat), (l.lookup n).isSome = false →
    (l ++ [(n, g)]).lookup n = some g := by
  intro l
  induction l with
  | nil => intro _; simp [List.lookup]
  | cons p ps ih =>
    intro h
    obtain ⟨k, v⟩ := p
    by_cases he : n = k
    · subst he
      simp [List.lookup] at h
    · have hb : (n == k) = false := by simpa using he
      simp only [List.lookup, hb, List.cons_append] at h ⊢
      exact ih h

theorem groupLifecycle_proven : GroupLifecycle := by
  intro st st' name gid w h
  have base : ∀ s : PSt, s.groupwidths = st.groupwidths ++ [none] →
      checkgroup s st.groupwidths.length = false ∧
      checkgroup (closegroupPure s st.groupwidths.length w) st.groupwidths.length = true := by
    intro s hs
    constructor
    · simp [checkgroup, hs]
    · simp [checkgroup, closegroupPure, hs]
  unfold opengroupPure at h
  dsimp only at h
  by_cases hm : (st.groupwidths ++ [none]).length > MAXGROUPS
  · rw [if_pos hm] at h
    cases h
  rw [if_neg hm] at h
  cases name with
  | none =>
    dsimp only at h
    cases h
    obtain ⟨h1, h2⟩ := base { st with groupwidths := st.groupwidths ++ [none] } rfl
    exact ⟨rfl, by simp, h1, h2, fun _ hn => by cases hn⟩
  | some n =>
    dsimp only at h
    by_cases hn : (st.groupdict.lookup n).isSome = true
    · rw [if_pos hn] at h
      cases h
    rw [if_neg hn] at h
    cases h
    obtain ⟨h1, h2⟩ := base
      { st with groupwidths := st.groupwidths ++ [none],
                groupdict := st.groupdict ++ [(n, st.groupwidths.length)] } rfl
    refine ⟨rfl, by simp, h1, h2, ?_⟩
    intro m hm'
    cases hm'
    exact lookup_snoc' _ _ _ (Bool.eq_false_iff.2 hn)

/-- Outside a lookbehind any group may be referred to. Inside one, an open group or a group opened
in the same lookbehind is refused. -/
def LookbehindLaw : Prop :=
  ∀ (st : PSt) (gid lb : Nat),
    (st.lookbehindgroups = none → lookbehindError st gid = none) ∧
    (st.lookbehindgroups = some lb → (lookbehindError st gid = none ↔ checkgroup st gid = true ∧ gid < lb))

theorem lookbehindLaw_proven : LookbehindLaw := by
  intro st gid lb
  constructor
  · intro h
    simp [lookbehindError, h]
  · intro h
    simp only [lookbehindError, h]
    by_cases h1 : checkgroup st gid = true
    · by_cases h2 : gid ≥ lb
      · simp [h1, h2] <;> omega
      · simp [h1, h2] <;> omega
    · simp [h1]

/-! ### Tokenizer -/

/-- `Tokenizer.seek(i)` puts `tell()` at `i` when there is a token there. -/
def SeekTell : Prop :=
  ∀ (t t' : Tk) (i : Nat), t.seek (i : Int) = .ok t' → t'.next.isSome = true → t'.tell = i

theorem seekTell_proven : SeekTell := by
  intro t t' i h hn
  have := tellAfterAdv_proven { t with index := (i : Int).toNat } t' h hn
  simpa using this

/-- `Tokenizer.error` reports the position `tell() - offset`. -/
def ErrorPosition : Prop :=
  ∀ (t : Tk) (msg : String) (off : Int), t.istext = true →
    t.err msg off = reError msg t.s (t.tell - off)

theorem errorPosition_proven : ErrorPosition := by
  intro t msg off h
  simp [Tk.err, h]

/-- `Tokenizer.match(c)` consumes the token exactly when it is `c`. -/
def MatchLaw : Prop :=
  ∀ (st : PSt) (c : Nat), st.tk.next ≠ some [c] → (smatch c).run st = .ok (false, st)

theorem matchLaw_proven : MatchLaw := by
  intro st c h
  have hb : (st.tk.next == some [c]) = false := by simpa using h
  simp [smatch, peek, hb, StateT.run, bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure, get,
    getThe, MonadStateOf.get, StateT.get, liftM, monadLift]

/-- `Tokenizer.getwhile(n, set)` reads at most `n` characters, all in `set`, without erroring on a
pattern with no backslash left. -/
def GetwhileBound : Prop :=
  ∀ (n : Nat) (set : Nat → Bool) (st st' : PSt) (r : List Nat),
    (getwhile n set).run st = .ok (r, st') → r.length ≤ n ∧ ∀ c ∈ r, set c = true

theorem getwhileBound_proven : GetwhileBound := by
  intro n
  induction n with
  | zero =>
    intro set st st' r h
    simp only [getwhile, StateT.run, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    simp
  | succ n ih =>
    intro set st st' r h
    rw [getwhile] at h
    simp only [peek, bind, StateT.bind, StateT.run, get, getThe, MonadStateOf.get, StateT.get, pure,
      StateT.pure, Except.bind, Except.pure] at h
    have stop : (Except.ok ([], st) : Py (List Nat × PSt)) = .ok (r, st') →
        r.length ≤ n + 1 ∧ ∀ c ∈ r, set c = true := by
      intro he
      simp only [Except.ok.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, _⟩ := he
      simp
    cases hn : st.tk.next with
    | none =>
      rw [hn] at h
      exact stop h
    | some t =>
      rw [hn] at h
      match t, h with
      | [], h => exact stop h
      | _ :: _ :: _, h => exact stop h
      | [c], h =>
        simp only at h
        by_cases hc : set c = true
        · rw [if_pos hc] at h
          cases hs : (sget) st with
          | error e => simp [hs, bind, StateT.bind, Except.bind] at h
          | ok v =>
            obtain ⟨u, st2⟩ := v
            simp only [hs, bind, StateT.bind, Except.bind] at h
            cases hg : (getwhile n set) st2 with
            | error e => simp [hg] at h
            | ok v2 =>
              obtain ⟨rest, st3⟩ := v2
              simp only [hg, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, _⟩ := h
              obtain ⟨h1, h2⟩ := ih set st2 _ _ hg
              refine ⟨by rw [List.length_cons]; omega, ?_⟩
              intro x hx
              rcases List.mem_cons.1 hx with rfl | hx
              · exact hc
              · exact h2 x hx
        · rw [if_neg hc] at h
          exact stop h

/-- `checkgroupname` accepts exactly the identifiers. -/
def GroupNameLaw : Prop :=
  ∀ (name : List Nat) (st : PSt),
    ((checkgroupname name).run st = .ok ((), st) ∨ isIdentifier name = false) ∧
    (isIdentifier name = false → (checkgroupname name).run st = .error (reErrorR "bad character in group name"))

theorem groupNameLaw_proven : GroupNameLaw := by
  intro name st
  by_cases h : isIdentifier name = true
  · refine ⟨.inl ?_, fun h2 => by simp [h] at h2⟩
    show checkgroupname name st = _
    unfold checkgroupname
    rw [h]
    rfl
  · have hf : isIdentifier name = false := by simpa using h
    refine ⟨.inr hf, fun _ => ?_⟩
    show checkgroupname name st = _
    unfold checkgroupname
    rw [hf]
    rfl

/-! ### `getwidth` -/

/-- `lo ≤ hi`, or `hi` already at the ceiling that `min(hi, MAXWIDTH)` applies. -/
def WLe (w : Nat × Nat) : Prop := w.1 ≤ w.2 ∨ MAXWIDTH ≤ w.2

theorem clamp_ok (w : Nat × Nat) (h : WLe w) : (clampW w).1 ≤ (clampW w).2 := by
  simp only [clampW, WLe, Nat.min_def] at h ⊢
  split <;> split <;> omega

mutual
  /-- The shape the parser produces: repeats have `min <= max`, and branches have alternatives. -/
  def WFNode : Node → Prop
    | .grouprefExists _ y n => WFList y ∧ (match n with
        | some l => WFList l
        | none => True)
    | .branch alts => alts ≠ [] ∧ WFAlts alts
    | .subpattern _ _ _ p | .atomic p | .assert_ _ p | .assertNot _ p => WFList p
    | .repeat_ _ lo hi p => lo ≤ hi ∧ hi ≤ MAXREPEAT ∧ WFList p
    | _ => True

  def WFList : List Node → Prop
    | [] => True
    | n :: ns => WFNode n ∧ WFList ns

  def WFAlts : List (List Node) → Prop
    | [] => True
    | a :: as => WFList a ∧ WFAlts as
end

/-- Well-formed group widths. -/
def GWOk (gw : List (Option (Nat × Nat))) : Prop := ∀ g v, gw.getD g none = some v → v.1 ≤ v.2

theorem wle_add (a b c d : Nat) (h : WLe (a, b)) (hc : c ≤ d) : WLe (a + c, b + d) := by
  simp only [WLe] at h ⊢
  omega

theorem wf_gex {g : Nat} {y : List Node} {n : Option (List Node)} (h : WFNode (.grouprefExists g y n)) :
    WFList y ∧ (∀ l, n = some l → WFList l) := by
  cases n with
  | none =>
    simp only [WFNode] at h
    exact ⟨h.1, fun _ hl => by cases hl⟩
  | some m =>
    simp only [WFNode] at h
    refine ⟨h.1, fun l hl => ?_⟩
    cases hl
    exact h.2

mutual
  theorem width_node (gw : List (Option (Nat × Nat))) (hg : GWOk gw) :
      ∀ (n : Node) (lo hi : Nat), WFNode n → WLe (lo, hi) → WLe (widthNode gw n lo hi)
    | .branch alts, lo, hi, hw, h => by
      simp only [WFNode] at hw
      have := width_alts gw hg alts hw.1 hw.2
      simp only [widthNode]
      exact wle_add _ _ _ _ h this
    | .atomic p, lo, hi, hw, h => by
      simp only [WFNode] at hw
      simp only [widthNode]
      exact wle_add _ _ _ _ h (clamp_ok _ (width_list gw hg p hw))
    | .subpattern _ _ _ p, lo, hi, hw, h => by
      simp only [WFNode] at hw
      simp only [widthNode]
      exact wle_add _ _ _ _ h (clamp_ok _ (width_list gw hg p hw))
    | .repeat_ _ mn mx p, lo, hi, hw, h => by
      simp only [WFNode] at hw
      obtain ⟨h1, _, h3⟩ := hw
      have hc := clamp_ok _ (width_list gw hg p h3)
      simp only [widthNode]
      generalize clampW (widthList gw p) = w at hc
      obtain ⟨i, j⟩ := w
      simp only at hc ⊢
      by_cases hm : mx = MAXREPEAT ∧ j ≠ 0
      · rw [if_pos hm]
        right
        simp only [MAXWIDTH]
        omega
      · rw [if_neg hm]
        have : i * mn ≤ j * mx := Nat.mul_le_mul hc h1
        exact wle_add _ _ _ _ h this
    | .literal _, lo, hi, _, h | .notLiteral _, lo, hi, _, h | .any, lo, hi, _, h
    | .in_ _, lo, hi, _, h => by
      simp only [widthNode]
      exact wle_add _ _ _ _ h (Nat.le_refl _)
    | .groupref g, lo, hi, _, h => by
      simp only [widthNode]
      cases hv : gw.getD g none with
      | none => simpa using h
      | some v =>
        simp only [Option.getD_some]
        exact wle_add _ _ _ _ h (hg g v hv)
    | .grouprefExists _ yes none, lo, hi, hw, h => by
      have hw' := wf_gex hw
      have hy := clamp_ok _ (width_list gw hg yes hw'.1)
      simp only [widthNode]
      exact wle_add _ _ 0 _ h (Nat.zero_le _)
    | .grouprefExists _ yes (some l), lo, hi, hw, h => by
      have hw' := wf_gex hw
      have hy := clamp_ok _ (width_list gw hg yes hw'.1)
      have hn := clamp_ok _ (width_list gw hg l (hw'.2 l rfl))
      simp only [widthNode]
      apply wle_add _ _ _ _ h
      exact Nat.le_trans (Nat.min_le_left _ _) (Nat.le_trans hy (Nat.le_max_left _ _))
    | .at_ _, lo, hi, _, h | .failure, lo, hi, _, h => by
      simpa only [widthNode] using h
    | .assert_ _ _, lo, hi, _, h | .assertNot _ _, lo, hi, _, h => by
      simpa only [widthNode] using h

  theorem width_list (gw : List (Option (Nat × Nat))) (hg : GWOk gw) :
      ∀ l : List Node, WFList l → WLe (widthList gw l)
    | [], _ => by simp [widthList, WLe]
    | n :: ns, hw => by
      simp only [WFList] at hw
      have := width_node gw hg n _ _ hw.1 (width_list gw hg ns hw.2)
      simp only [widthList]
      exact this

  theorem width_alts (gw : List (Option (Nat × Nat))) (hg : GWOk gw) :
      ∀ alts : List (List Node), alts ≠ [] → WFAlts alts → (widthAlts gw alts).1 ≤ (widthAlts gw alts).2
    | [], h, _ => absurd rfl h
    | a :: r, _, hw => by
      simp only [WFAlts] at hw
      have h1 := clamp_ok _ (width_list gw hg a hw.1)
      simp only [widthAlts]
      generalize clampW (widthList gw a) = w at h1
      generalize widthAlts gw r = w2
      obtain ⟨l, h⟩ := w
      obtain ⟨i, j⟩ := w2
      simp only at h1 ⊢
      exact Nat.le_trans (Nat.min_le_right _ _) (Nat.le_trans h1 (Nat.le_max_right _ _))
end

/-- For every tree of the shape the parser produces, `getwidth` returns `lo <= hi`. -/
def WidthOrdered : Prop :=
  ∀ (gw : List (Option (Nat × Nat))) (p : List Node), GWOk gw → WFList p →
    (getwidth gw p).1 ≤ (getwidth gw p).2

theorem widthOrdered_proven : WidthOrdered :=
  fun gw p hg hp => clamp_ok _ (width_list gw hg p hp)

/-! ### `_parse_sub` -/

theorem atomEq_eq : ∀ a b : Node, atomEq a b = true → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [atomEq]

/-- Moving a common prefix out of a branch keeps every alternative: each one is still the prefix
followed by what stays in the branch. -/
def PrefixFactor : Prop :=
  ∀ (fuel : Nat) (items : List (List Node)) (acc : List Node),
    (factorPrefix fuel items acc).1.map ((factorPrefix fuel items acc).2 ++ ·) = items.map (acc ++ ·)

theorem prefixFactor_proven : PrefixFactor := by
  intro fuel
  induction fuel with
  | zero => intro _ _; rfl
  | succ fuel ih =>
    intro items acc
    match items with
    | [] => rfl
    | [] :: rest => rfl
    | (pfx :: t) :: rest =>
      have e : factorPrefix (fuel + 1) ((pfx :: t) :: rest) acc =
          if ((pfx :: t) :: rest).all (fun it => match it with
              | h :: _ => atomEq pfx h
              | [] => false) then
            factorPrefix fuel (((pfx :: t) :: rest).map (·.drop 1)) (acc ++ [pfx])
          else (((pfx :: t) :: rest), acc) := rfl
      rw [e]
      by_cases hall : ((pfx :: t) :: rest).all (fun it => match it with
          | h :: _ => atomEq pfx h
          | [] => false) = true
      · rw [if_pos hall, ih]
        rw [List.map_map]
        apply List.map_congr_left
        intro it hit
        have hh := List.all_eq_true.1 hall it hit
        match it, hh with
        | h :: tl, hh =>
          have : pfx = h := atomEq_eq _ _ hh
          subst this
          simp
      · rw [if_neg hall]

/-- A branch of single characters and sets becomes one set that holds all of them. -/
def BranchSetLaw : Prop :=
  ∀ (items : List (List Node)) (acc set : List SetItem), branchSet items acc = some set →
    (∀ x ∈ acc, x ∈ set) ∧
    ∀ it ∈ items, (∃ c, it = [.literal c] ∧ SetItem.literal c ∈ set) ∨
      (∃ av, it = [.in_ av] ∧ ∀ x ∈ av, x ∈ set)

theorem branchSetLaw_proven : BranchSetLaw := by
  intro items
  induction items with
  | nil =>
    intro acc set h
    simp only [branchSet, Option.some.injEq] at h
    subst h
    exact ⟨fun _ h => h, fun _ h => by cases h⟩
  | cons it rest ih =>
    intro acc set h
    match it, h with
    | [.literal c], h =>
      simp only [branchSet] at h
      obtain ⟨h1, h2⟩ := ih _ _ h
      refine ⟨fun x hx => h1 x (by simp [hx]), ?_⟩
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact .inl ⟨c, rfl, h1 _ (by simp)⟩
      · exact h2 y hy
    | [.in_ av], h =>
      simp only [branchSet] at h
      split at h
      · cases h
      · obtain ⟨h1, h2⟩ := ih _ _ h
        refine ⟨fun x hx => h1 x (by simp [hx]), ?_⟩
        intro y hy
        rcases List.mem_cons.1 hy with rfl | hy
        · exact .inr ⟨av, rfl, fun x hx => h1 x (by simp [hx])⟩
        · exact h2 y hy

/-! ### `_parse_flags` -/

/-- `(?a-b:...)` never turns a flag both on and off or turns off a global flag, and the flag
combinations the source refuses are refused, each with its message. -/
def FlagLaws : Prop :=
  (∀ (add del : Nat) (st st' : PSt) (r : Nat × Nat),
    (flagsCheck add del).run st = .ok (some r, st') → r.1 &&& r.2 = 0 ∧ r.2 &&& GLOBAL_FLAGS = 0) ∧
  errOf (parse true (strOf "(?i-i:a)") 0) =
    some (reError "bad inline flags: flag turned on and off" (strOf "(?i-i:a)") 5) ∧
  errOf (parse true (strOf "(?au:a)") 0) =
    some (reError "bad inline flags: flags 'a', 'u' and 'L' are incompatible" (strOf "(?au:a)") 4) ∧
  errOf (parse true (strOf "(?-a:a)") 0) =
    some (reError "bad inline flags: cannot turn off flags 'a', 'u' and 'L'" (strOf "(?-a:a)") 4) ∧
  errOf (parse true (strOf "(?L:a)") 0) =
    some (reError "bad inline flags: cannot use 'L' flag with a str pattern" (strOf "(?L:a)") 3)

theorem pErr_run {α : Type} (msg : String) (off : Int) (st : PSt) :
    ∃ e, (pErr msg off : P α) st = .error e := ⟨_, rfl⟩

theorem flagLaws_proven : FlagLaws := by
  refine ⟨?_, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
  intro add del st st' r h
  unfold flagsCheck at h
  by_cases h1 : (del &&& GLOBAL_FLAGS) ≠ 0
  · rw [if_pos h1] at h
    obtain ⟨e, he⟩ := pErr_run (α := Option (Nat × Nat)) "bad inline flags: cannot turn off global flag" 1 st
    simp only [StateT.run, he] at h
    cases h
  rw [if_neg h1] at h
  by_cases h2 : (add &&& del) ≠ 0
  · rw [if_pos h2] at h
    obtain ⟨e, he⟩ := pErr_run (α := Option (Nat × Nat)) "bad inline flags: flag turned on and off" 1 st
    simp only [StateT.run, he] at h
    cases h
  rw [if_neg h2] at h
  simp only [StateT.run, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq,
    Option.some.injEq] at h
  obtain ⟨rfl, _⟩ := h
  exact ⟨by simpa using h2, by simpa using h1⟩

/-! ### The main loop on plain text -/

/-- The tokenizer sits at `rest`: `next` holds its head, and the unread text is its tail. -/
def PlainInv (st : PSt) : List Nat → Prop
  | [] => st.tk.next = none
  | c :: r => st.tk.next = some [c] ∧ st.tk.s.drop st.tk.index = r

theorem sget_plain (st : PSt) (c : Nat) (r : List Nat) (h : PlainInv st (c :: r))
    (hr : ∀ x ∈ r, x ≠ 92) :
    ∃ st2, sget st = .ok (some [c], st2) ∧ PlainInv st2 r ∧
      st2.flags = st.flags ∧ st2.groupwidths = st.groupwidths ∧ st2.groupdict = st.groupdict ∧
      st2.grouprefpos = st.grouprefpos := by
  obtain ⟨h1, h2⟩ := h
  have hh : st.tk.s[st.tk.index]? = r.head? := by rw [← h2, List.head?_drop]
  match r, hr, h2, hh with
  | [], _, h2, hh =>
    refine ⟨{ st with tk := { st.tk with next := none } }, ?_, rfl, rfl, rfl, rfl, rfl⟩
    have hadv : st.tk.adv = .ok { st.tk with next := none } := by
      unfold Tk.adv
      rw [hh]
      rfl
    simp only [sget, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, liftM, monadLift,
      MonadLift.monadLift, StateT.lift, Except.bind, hadv, set, StateT.set, pure, StateT.pure, Except.pure, h1]
  | d :: r', hr, h2, hh =>
    have hd : d ≠ 92 := hr d (by simp)
    refine ⟨{ st with tk := { st.tk with index := st.tk.index + 1, next := some [d] } }, ?_, ?_, rfl, rfl, rfl, rfl⟩
    · have hadv : st.tk.adv = .ok { st.tk with index := st.tk.index + 1, next := some [d] } := by
        unfold Tk.adv
        rw [hh]
        simp [hd]
      simp only [sget, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, liftM, monadLift,
        MonadLift.monadLift, StateT.lift, Except.bind, hadv, set, StateT.set, pure, StateT.pure, Except.pure, h1]
    · refine ⟨rfl, ?_⟩
      show st.tk.s.drop (st.tk.index + 1) = r'
      rw [← List.drop_drop, h2]
      rfl

theorem unpack_lits (l : List Nat) : unpackGroups (l.map Node.literal) = l.map Node.literal := by
  induction l with
  | nil => rfl
  | cons c cs ih => simpa [unpackGroups] using ih

theorem seq_plain (nested : Nat) (first : Bool) : ∀ (rest : List Nat) (f : Nat) (pre : List Nat) (st : PSt),
    (∀ x ∈ rest, isSpecial x = false) → rest.length < f → PlainInv st rest →
    ∃ st', parseSeq f false nested first (pre.map .literal) st =
        .ok ((pre ++ rest).map .literal, st') ∧ st'.tk.next = none ∧ st'.flags = st.flags ∧
        st'.groupwidths = st.groupwidths ∧ st'.groupdict = st.groupdict ∧ st'.grouprefpos = st.grouprefpos := by
  intro rest
  induction rest with
  | nil =>
    intro f pre st _ hf h
    match f, hf with
    | g + 1, _ =>
      refine ⟨st, ?_, h, rfl, rfl, rfl, rfl⟩
      rw [parseSeq]
      simp only [peek, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure,
        Except.bind, Except.pure]
      have : st.tk.next = none := h
      rw [this]
      simp [unpack_lits]
      rfl
  | cons c r ih =>
    intro f pre st hall hf h
    match f, hf with
    | g + 1, hf =>
      have hc : isSpecial c = false := hall c (by simp)
      have hr : ∀ x ∈ r, x ≠ 92 := by
        intro x hx he
        have := hall x (by simp [hx])
        subst he
        simp [isSpecial] at this
      obtain ⟨st2, hs, hi, e1, e2, e3, e4⟩ := sget_plain st c r h hr
      obtain ⟨st3, h3, h4, e5, e6, e7, e8⟩ := ih g (pre ++ [c]) st2
        (fun x hx => hall x (by simp [hx])) (by simp at hf; omega) hi
      refine ⟨st3, ?_, h4, e5.trans e1, e6.trans e2, e7.trans e3, e8.trans e4⟩
      have hn : st.tk.next = some [c] := h.1
      have h124 : c ≠ 124 := by intro he; subst he; simp [isSpecial] at hc
      have h41 : c ≠ 41 := by intro he; subst he; simp [isSpecial] at hc
      have h92 : c ≠ 92 := by intro he; subst he; simp [isSpecial] at hc
      have happ : (pre ++ c :: r) = (pre ++ [c]) ++ r := by simp
      rw [happ, parseSeq]
      simp only [peek, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure,
        Except.bind, Except.pure, hn]
      simpa [hs, h124, h41, h92, hc, List.map_append, StateT.bind, bind, Except.bind] using h3

/-- A `str` pattern with no special character parses to its literal characters: the group state
stays empty, nothing is factored, and `fix_flags` adds `UNICODE`. Holds for every length, through
`_parse_sub`, the main loop of `_parse`, `Tokenizer.get`, `Tokenizer.__next` and `parse`. -/
def ParsePlain : Prop :=
  ∀ s : List Nat, (∀ x ∈ s, isSpecial x = false) →
    ∃ q, parse true s 0 = .ok q ∧ q.p = s.map .literal ∧ q.groups = 1 ∧ q.flags = FLAG_UNICODE

theorem sub_plain (s : List Nat) (st : PSt) (f : Nat) (hf : s.length + 2 < f)
    (hs : ∀ x ∈ s, isSpecial x = false) (hi : PlainInv st s) :
    ∃ st', parseSub f false 0 st = .ok (s.map .literal, st') ∧ st'.tk.next = none ∧ st'.flags = st.flags ∧
      st'.groupwidths = st.groupwidths ∧ st'.groupdict = st.groupdict ∧ st'.grouprefpos = st.grouprefpos := by
  match f, hf with
  | g + 2, hf =>
    obtain ⟨st', h1, h2, e1, e2, e3, e4⟩ := seq_plain 1 true s g [] st hs (by omega) hi
    refine ⟨st', ?_, h2, e1, e2, e3, e4⟩
    rw [parseSub, parseAlts]
    have hm : (smatch 124) st' = .ok (false, st') := by
      have := matchLaw_proven st' 124 (by rw [h2]; simp)
      exact this
    have h1' : parseSeq g false 1 true [] st = .ok (s.map .literal, st') := by simpa using h1
    simp [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, finishSub, hm, h1']

theorem parsePlain_proven : ParsePlain := by
  intro s hs
  have hadv : ∃ t, Tk.adv ⟨true, s, 0, none⟩ = .ok t ∧ t.istext = true ∧
      PlainInv { tk := t, flags := 0 } s := by
    match s, hs with
    | [], _ => exact ⟨_, rfl, rfl, rfl⟩
    | c :: r, hs =>
      have h92 : c ≠ 92 := by
        intro he
        have := hs c (by simp)
        subst he
        simp [isSpecial] at this
      refine ⟨⟨true, c :: r, 1, some [c]⟩, ?_, rfl, rfl, ?_⟩
      · simp [Tk.adv, h92]
      · simp
  obtain ⟨t, h1, _, h3⟩ := hadv
  obtain ⟨st', h4, h5, e1, e2, e3, e4⟩ :=
    sub_plain s { tk := t, flags := 0 } (4 * s.length + 16) (by omega) hs h3
  have hfl : fixFlags true 0 = .ok FLAG_UNICODE := by decide
  refine ⟨⟨s.map .literal, FLAG_UNICODE, 1, [], [none]⟩, ?_, rfl, rfl, rfl⟩
  have h4' : parseSub (4 * s.length + 16) (decide ((0 &&& FLAG_VERBOSE) ≠ 0)) 0
      { tk := t, flags := 0, maxDigits := 4300 } = .ok (s.map .literal, st') := h4
  simp only [parse, h1, bind, Except.bind, StateT.run, h4', e1, hfl, h5, Option.isSome_none,
    Bool.false_eq_true, if_false, e4]
  simp [e2, e3, forIn, pure, Except.pure]

/-- `Tokenizer.getuntil(term)` on plain text returns what comes before the terminator and leaves
the tokenizer after it. -/
def GetuntilLaw : Prop :=
  ∀ (term : Nat) (name : String) (r rest acc : List Nat) (st : PSt) (f : Nat),
    term ∉ r → r.length < f → (∀ x ∈ r ++ term :: rest, x ≠ 92) →
    PlainInv st (r ++ term :: rest) → acc ++ r ≠ [] →
    ∃ st', (getuntil term name f acc).run st = .ok (acc ++ r, st') ∧ PlainInv st' rest

theorem getuntilLaw_proven : GetuntilLaw := by
  intro term name r
  induction r with
  | nil =>
    intro rest acc st f _ hf hall hi hne
    match f, hf with
    | g + 1, _ =>
      obtain ⟨st2, hs, h2, _⟩ := sget_plain st term rest hi
        (fun x hx => hall x (by simp [hx]))
      refine ⟨st2, ?_, h2⟩
      have hacc : acc.isEmpty = false := by simpa using hne
      show getuntil term name (g + 1) acc st = _
      rw [getuntil]
      simp [bind, StateT.bind, Except.bind, hs, hacc, pure, StateT.pure, Except.pure]
  | cons c r ih =>
    intro rest acc st f hterm hf hall hi hne
    match f, hf with
    | g + 1, hf =>
      have hc : c ≠ term := by
        intro he
        apply hterm
        simp [he]
      have hnt : term ∉ r := fun h => hterm (by simp [h])
      obtain ⟨st2, hs, h2, _⟩ := sget_plain st c (r ++ term :: rest) hi
        (fun x hx => hall x (by simp [hx]))
      obtain ⟨st3, h3, h4⟩ := ih rest (acc ++ [c]) st2 g hnt (by simp at hf; omega)
        (fun x hx => hall x (by simp [hx])) h2 (by simp)
      refine ⟨st3, ?_, h4⟩
      show getuntil term name (g + 1) acc st = _
      rw [getuntil]
      have e : acc ++ c :: r = acc ++ [c] ++ r := by simp
      rw [e]
      have h3' : getuntil term name g (acc ++ [c]) st2 = .ok (acc ++ [c] ++ r, st3) := h3
      simpa [bind, StateT.bind, Except.bind, hs, hc] using h3'

/-- The template tokenizer sits at `rest`, with `index` at the end when `rest` is empty. -/
def TInv (t : Tk) : List Nat → Prop
  | [] => t.next = none ∧ t.s.drop t.index = []
  | c :: r => t.next = some [c] ∧ t.s.drop t.index = r

theorem tget_end (st : TSt) (h : TInv st.tk []) : tget st = .ok (none, st) := by
  obtain ⟨h1, h2⟩ := h
  have hh : st.tk.s[st.tk.index]? = none := by
    have : (st.tk.s.drop st.tk.index).head? = none := by rw [h2]; rfl
    rwa [List.head?_drop] at this
  have hadv : st.tk.adv = .ok st.tk := by
    unfold Tk.adv
    rw [hh]
    cases htk : st.tk
    simp_all
  simp only [tget, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, liftM, monadLift,
    MonadLift.monadLift, StateT.lift, Except.bind, hadv, set, StateT.set, pure, StateT.pure, Except.pure, h1]

theorem tget_step (st : TSt) (c : Nat) (r : List Nat) (h : TInv st.tk (c :: r)) (hr : ∀ x ∈ r, x ≠ 92) :
    ∃ t2 : Tk, tget st = .ok (some [c], { st with tk := t2 }) ∧ TInv t2 r := by
  obtain ⟨h1, h2⟩ := h
  have hh : st.tk.s[st.tk.index]? = r.head? := by rw [← h2, List.head?_drop]
  match r, hr, h2, hh with
  | [], _, h2, hh =>
    refine ⟨{ st.tk with next := none }, ?_, rfl, h2⟩
    have hadv : st.tk.adv = .ok { st.tk with next := none } := by
      unfold Tk.adv
      rw [hh]
      rfl
    simp only [tget, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, liftM, monadLift,
      MonadLift.monadLift, StateT.lift, Except.bind, hadv, set, StateT.set, pure, StateT.pure, Except.pure, h1]
  | d :: r', hr, h2, hh =>
    have hd : d ≠ 92 := hr d (by simp)
    refine ⟨{ st.tk with index := st.tk.index + 1, next := some [d] }, ?_, rfl, ?_⟩
    · have hadv : st.tk.adv = .ok { st.tk with index := st.tk.index + 1, next := some [d] } := by
        unfold Tk.adv
        rw [hh]
        simp [hd]
      simp only [tget, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, liftM, monadLift,
        MonadLift.monadLift, StateT.lift, Except.bind, hadv, set, StateT.set, pure, StateT.pure, Except.pure, h1]
    · show st.tk.s.drop (st.tk.index + 1) = r'
      rw [← List.drop_drop, h2]
      rfl

theorem template_loop (g : Nat) (gi : List (List Nat × Nat)) : ∀ (rest : List Nat) (f : Nat) (st : TSt),
    (∀ x ∈ rest, x ≠ 92) → rest.length < f → TInv st.tk rest →
    ∃ st', templateLoop g gi f st = .ok ((), st') ∧ st'.result = st.result ∧ st'.literal = st.literal ++ rest := by
  intro rest
  induction rest with
  | nil =>
    intro f st _ hf h
    match f, hf with
    | k + 1, _ =>
      refine ⟨st, ?_, rfl, by simp⟩
      rw [templateLoop]
      simp [bind, StateT.bind, Except.bind, tget_end st h, pure, StateT.pure, Except.pure]
  | cons c r ih =>
    intro f st hall hf h
    match f, hf with
    | k + 1, hf =>
      have hc : c ≠ 92 := hall c (by simp)
      obtain ⟨t2, ht, hi⟩ := tget_step st c r h (fun x hx => hall x (by simp [hx]))
      obtain ⟨st', h3, h4, h5⟩ := ih k { st with tk := t2, literal := st.literal ++ [c] }
        (fun x hx => hall x (by simp [hx])) (by simp at hf; omega) hi
      refine ⟨st', ?_, h4, by simpa using h5⟩
      rw [templateLoop]
      simpa [bind, StateT.bind, Except.bind, ht, hc, lappend, modify, modifyGet, MonadStateOf.modifyGet,
        StateT.modifyGet, pure, StateT.pure, Except.pure] using h3

/-- A replacement with no backslash is that literal text, whatever the pattern's groups are. -/
def TemplatePlain : Prop :=
  ∀ (s : List Nat) (g : Nat) (gi : List (List Nat × Nat)), (∀ x ∈ s, x ≠ 92) →
    parseTemplate true s g gi = .ok [.lit s]

theorem templatePlain_proven : TemplatePlain := by
  intro s g gi hs
  have hadv : ∃ t, Tk.adv ⟨true, s, 0, none⟩ = .ok t ∧ TInv t s := by
    match s, hs with
    | [], _ => exact ⟨_, rfl, rfl, rfl⟩
    | c :: r, hs =>
      have h92 : c ≠ 92 := hs c (by simp)
      refine ⟨⟨true, c :: r, 1, some [c]⟩, ?_, rfl, by simp⟩
      simp [Tk.adv, h92]
  obtain ⟨t, h1, h2⟩ := hadv
  obtain ⟨st', h3, h4, h5⟩ := template_loop g gi s (s.length + 2) { tk := t } hs (by omega) h2
  simp only [parseTemplate, h1, bind, Except.bind, StateT.run, StateT.bind, h3, addLiteral, modify,
    modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure, Except.pure, h4, h5]
  simp

end PyLean.TextLibs.Re
