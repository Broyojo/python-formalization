import PyLean.Ipaddress.Parse6Spec

/-!
The refusals of `_BaseV6._ip_int_from_string`, Lib/ipaddress.py:1648-1760 (CPython 3.15.2):
which inputs raise which `AddressValueError`, in the order the checks run.
-/

namespace PyLean.Ipaddress

open PyLean

/-- The indices `i` in `range(1, len(parts) - 1)` with `parts[i] == ''`, in order: the positions
the loop at :1702-1708 visits and finds empty. -/
def innerEmpty (parts : List (List Char)) : List Nat :=
  ((parts.drop 1).take (parts.length - 2)).zipIdx.filterMap fun pi =>
    if pi.1.isEmpty then some (pi.2 + 1) else none

/-- The loop at :1702-1708 keeps the first empty index and raises at a second one. -/
theorem skipScan_eq (parts : List (List Char)) :
    skipScan parts = ((innerEmpty parts).head?, decide (2 ≤ (innerEmpty parts).length)) := by
  unfold skipScan innerEmpty
  generalize ((parts.drop 1).take (parts.length - 2)).zipIdx = l
  have H : ∀ (sk : Option Nat) (two : Bool),
      l.foldl (fun (sk, two) (p, i) =>
        if p.isEmpty then (if sk.isSome then (sk, true) else (some (i + 1), two)) else (sk, two))
        (sk, two) =
      ((match sk with
        | some x => some x
        | none => (l.filterMap fun pi => if pi.1.isEmpty then some (pi.2 + 1) else none).head?),
       two || decide ((if sk.isSome then 1 else 2) ≤
         (l.filterMap fun pi => if pi.1.isEmpty then some (pi.2 + 1) else none).length)) := by
    induction l with
    | nil => intro sk two; cases sk <;> simp
    | cons pi l ih =>
      intro sk two
      obtain ⟨p, i⟩ := pi
      by_cases hp : p.isEmpty = true
      · cases sk with
        | some x =>
          simp only [List.foldl_cons, List.filterMap_cons, hp, ↓reduceIte, Option.isSome_some]
          rw [ih]
          simp
        | none =>
          simp only [List.foldl_cons, List.filterMap_cons, hp, ↓reduceIte, Option.isSome_none,
            Bool.false_eq_true]
          rw [ih]
          simp <;> omega
      · have hp' : p.isEmpty = false := by simpa using hp
        simp only [List.foldl_cons, List.filterMap_cons, hp', Bool.false_eq_true, ↓reduceIte]
        rw [ih]
  exact H none false

theorem parseHextets_first (pre post : List (List Char)) (p : List Char) (e : HexErr)
    (hpre : ∀ q ∈ pre, ∃ v, parseHextet q = .ok v) (hp : parseHextet p = .error e) :
    parseHextets (pre ++ p :: post) = .error (p, e) := by
  induction pre with
  | nil => simp [parseHextets, hp]
  | cons q qs ih =>
    obtain ⟨v, hv⟩ := hpre q (by simp)
    simp [parseHextets, hv, ih (fun r hr => hpre r (by simp [hr])), Except.map]

theorem bind_className {α β : Type} {x : Py α} {f : α → Py β} {c : String}
    (hx : ∀ e, x = .error e → e.className = c) (hf : ∀ a e, f a = .error e → e.className = c) :
    ∀ e, (x >>= f) = .error e → e.className = c := by
  intro e h
  cases hx' : x with
  | error e' =>
    rw [hx'] at h
    simp only [bind, Except.bind, Except.error.injEq] at h
    subst h; exact hx _ hx'
  | ok a =>
    rw [hx'] at h
    exact hf a e h

theorem ipv6Suffix_className (s : List Char) (parts : List (List Char)) :
    ∀ e, ipv6Suffix s parts = .error e → e.className = "AddressValueError" := by
  intro e h
  unfold ipv6Suffix at h
  split at h
  · split at h
    · simp only [throw, throwThe, MonadExceptOf.throw, Except.error.injEq] at h
      subst h; rfl
    · cases h
  · cases h

theorem ipv6Hextets_className (s : List Char) (parts : List (List Char)) (hi lo sk : Nat) :
    ∀ e, ipv6Hextets s parts hi lo sk = .error e → e.className = "AddressValueError" := by
  intro e h
  unfold ipv6Hextets at h
  split at h
  · simp only [throw, throwThe, MonadExceptOf.throw, Except.error.injEq] at h
    subst h; rfl
  · cases h

/-- `s` passes the checks before the layout (non-empty, at most 45 characters, at least 3 parts,
:1662-1681) and the IPv4-suffix step (:1684-1690) leaves the parts `Q`. -/
def Staged (s : List Char) (Q : List (List Char)) : Prop :=
  s ≠ [] ∧ s.length ≤ 45 ∧ 3 ≤ (splitMax ':' 9 s).length ∧ ipv6Suffix s (splitMax ':' 9 s) = .ok Q

theorem staged_eq (s : List Char) (Q : List (List Char)) (h : Staged s Q) :
    ipIntFromString6 s = (ipv6Layout s Q >>= fun t => ipv6Hextets s Q t.1 t.2.1 t.2.2) := by
  obtain ⟨h0, h45, h3, hq⟩ := h
  have he : s.isEmpty = false := by cases s <;> simp_all
  have h45' : ¬ s.length > 45 := by omega
  have h3' : ¬ (splitMax ':' 9 s).length < 3 := by omega
  unfold ipIntFromString6
  simp only [he, h45', h3', Bool.false_eq_true, ↓reduceIte, hq, bind, Except.bind]

theorem prefix_eq (s : List Char) (h0 : s ≠ []) (h45 : s.length ≤ 45) (h3 : 3 ≤ (splitMax ':' 9 s).length) :
    ipIntFromString6 s = (ipv6Suffix s (splitMax ':' 9 s) >>= fun parts =>
      ipv6Layout s parts >>= fun t => ipv6Hextets s parts t.1 t.2.1 t.2.2) := by
  have he : s.isEmpty = false := by cases s <;> simp_all
  have h45' : ¬ s.length > 45 := by omega
  have h3' : ¬ (splitMax ':' 9 s).length < 3 := by omega
  unfold ipIntFromString6
  simp only [he, h45', h3', Bool.false_eq_true, ↓reduceIte, bind, Except.bind]

theorem suffix_plain (s : List Char) (P : List (List Char)) (hd : '.' ∉ P.getLast!) :
    ipv6Suffix s P = .ok P := by
  unfold ipv6Suffix; rw [if_neg hd]; rfl

theorem suffix_v4 (s : List Char) (P : List (List Char)) (v : Nat) (hd : '.' ∈ P.getLast!)
    (hv : ipv4Init (.str P.getLast!) = .ok v) :
    ipv6Suffix s P = .ok (P.dropLast ++ [hexStr (v / 65536 % 65536), hexStr (v % 65536)]) := by
  unfold ipv6Suffix; rw [if_pos hd, hv]; rfl

theorem suffix_err (s : List Char) (P : List (List Char)) (e : PyExc) (hd : '.' ∈ P.getLast!)
    (hv : ipv4Init (.str P.getLast!) = .error e) :
    ipv6Suffix s P = .error (avErr (do let r ← reprPlain s; if e.message.startsWith "~" then none else
      some (e.message ++ " in " ++ r))) := by
  unfold ipv6Suffix; rw [if_pos hd, hv]; rfl

/-- `parts_hi` and `parts_lo` with `::` at index `k`, :1714-1725. -/
def layoutHi (Q : List (List Char)) (k : Nat) : Nat := if Q.head!.isEmpty then k - 1 else k
def layoutLo (Q : List (List Char)) (k : Nat) : Nat :=
  if Q.getLast!.isEmpty then Q.length - k - 2 else Q.length - k - 1

theorem layout_skip (s : List Char) (Q : List (List Char)) (k : Nat) (h9 : ¬ Q.length > 9)
    (hk : innerEmpty Q = [k]) :
    ipv6Layout s Q =
      if Q.head!.isEmpty = true ∧ layoutHi Q k ≠ 0 then .error (avMsg "Leading ':' only permitted as part of '::' in " s)
      else if Q.getLast!.isEmpty = true ∧ layoutLo Q k ≠ 0 then
        .error (avMsg "Trailing ':' only permitted as part of '::' in " s)
      else if 8 < layoutHi Q k + layoutLo Q k + 1 then
        .error (avMsg "Expected at most 7 other parts with '::' in " s)
      else .ok (layoutHi Q k, layoutLo Q k, 8 - (layoutHi Q k + layoutLo Q k)) := by
  unfold ipv6Layout layoutHi layoutLo
  rw [skipScan_eq, hk]
  simp only [h9, ↓reduceIte, List.head?_cons, List.length_cons, List.length_nil, bind, Except.bind,
    pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  simp only [Nat.zero_add, Nat.reduceLeDiff, decide_false, Bool.false_eq_true, ↓reduceIte]
  repeat' split
  all_goals rfl

theorem layout_noskip (s : List Char) (Q : List (List Char)) (h9 : ¬ Q.length > 9)
    (hk : innerEmpty Q = []) :
    ipv6Layout s Q =
      if Q.length ≠ 8 then .error (avMsg "Exactly 8 parts expected without '::' in " s)
      else if Q.head!.isEmpty = true then .error (avMsg "Leading ':' only permitted as part of '::' in " s)
      else if Q.getLast!.isEmpty = true then .error (avMsg "Trailing ':' only permitted as part of '::' in " s)
      else .ok (Q.length, 0, 0) := by
  unfold ipv6Layout
  rw [skipScan_eq, hk]
  simp only [h9, ↓reduceIte, List.head?_nil, List.length_nil, bind, Except.bind,
    pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  simp only [Nat.reduceLeDiff, decide_false, Bool.false_eq_true, ↓reduceIte]
  repeat' split
  all_goals rfl

theorem ite_err_cls {α : Type} {c : Prop} [Decidable c] {x : PyExc} {y : Py α} {e : PyExc}
    {C : String} (h : (if c then .error x else y) = .error e) (hx : x.className = C)
    (hy : y = .error e → e.className = C) : e.className = C := by
  by_cases hc : c
  · rw [if_pos hc] at h; cases h; exact hx
  · rw [if_neg hc] at h; exact hy h

theorem ipv6Layout_className (s : List Char) (parts : List (List Char)) :
    ∀ e, ipv6Layout s parts = .error e → e.className = "AddressValueError" := by
  intro e h
  by_cases h9 : parts.length > 9
  · unfold ipv6Layout at h
    simp only [h9, ↓reduceIte] at h
    cases h; rfl
  by_cases h2 : 2 ≤ (innerEmpty parts).length
  · unfold ipv6Layout at h
    rw [skipScan_eq] at h
    simp only [h9, ↓reduceIte, decide_eq_true h2] at h
    cases h; rfl
  cases hk : innerEmpty parts with
  | nil =>
    rw [layout_noskip s parts h9 hk] at h
    exact ite_err_cls h rfl fun h => ite_err_cls h rfl fun h => ite_err_cls h rfl fun h => by cases h
  | cons k t =>
    have ht : t = [] := by
      rw [hk] at h2; cases t with
      | nil => rfl
      | cons _ _ => simp at h2
    subst ht
    rw [layout_skip s parts k h9 hk] at h
    exact ite_err_cls h rfl fun h => ite_err_cls h rfl fun h => ite_err_cls h rfl fun h => by cases h

/-- `_ip_int_from_string` raises only `AddressValueError`: `ip_address` relies on that to try
IPv4 then IPv6 (:41-49). -/
theorem ipIntFromString6_class (s : List Char) :
    (∃ n, ipIntFromString6 s = .ok n) ∨ ∃ m, ipIntFromString6 s = .error (.named "AddressValueError" m) := by
  have hc : ∀ e, ipIntFromString6 s = .error e → e.className = "AddressValueError" := by
    intro e h
    unfold ipIntFromString6 at h
    by_cases c1 : s.isEmpty = true
    · simp only [c1, ↓reduceIte] at h
      simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind, Except.error.injEq] at h
      subst h; rfl
    by_cases c2 : s.length > 45
    · simp only [c1, c2, ↓reduceIte, Bool.false_eq_true] at h
      simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind, Except.error.injEq] at h
      subst h; try rfl
    by_cases c3 : (splitMax ':' 9 s).length < 3
    · simp only [c1, c2, c3, ↓reduceIte, Bool.false_eq_true] at h
      simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind, Except.error.injEq] at h
      subst h; rfl
    simp only [c1, c2, c3, ↓reduceIte, Bool.false_eq_true] at h
    refine bind_className (ipv6Suffix_className s _) (fun parts e h => ?_) e h
    exact bind_className (ipv6Layout_className s parts) (fun t e h => by
      obtain ⟨hi, lo, sk⟩ := t
      exact ipv6Hextets_className s parts hi lo sk e h) e h
  cases h : ipIntFromString6 s with
  | ok n => exact Or.inl ⟨n, rfl⟩
  | error e =>
    right
    have := hc e h
    cases e <;> simp [PyExc.className] at this
    subst this
    exact ⟨_, rfl⟩

/-- `_BaseV6._ip_int_from_string`, ipaddress.py:1648-1760, docstring "Raises: AddressValueError:
if ip_str isn't a valid IPv6 Address": every refusal, in the order of the checks, with its message
(`avMsg pre s` is `pre + repr(s)` where `reprPlain` renders it). `Q` is the list of parts after the
IPv4-suffix step (`Staged`), which conjuncts 5 and 6 describe; `innerEmpty Q` lists the empty parts
strictly inside it (where `::` is); `layoutHi`/`layoutLo` are `parts_hi`/`parts_lo` (:1714-1725),
and the conditions are the source's, in its order. -/
def V6ParseRefusals : Prop :=
  (∀ s, (∃ n, ipIntFromString6 s = .ok n) ∨ ∃ m, ipIntFromString6 s = .error (.named "AddressValueError" m)) ∧
  ipIntFromString6 [] = .error (.named "AddressValueError" "Address cannot be empty") ∧
  (∀ s, 45 < s.length → s.length ≤ 100 →
    ipIntFromString6 s = .error (avMsg "At most 45 characters expected in " s)) ∧
  (∀ s, s ≠ [] → s.length ≤ 45 → (splitMax ':' 9 s).length < 3 →
    ipIntFromString6 s = .error (avMsg "At least 3 parts expected in " s)) ∧
  (∀ s P, '.' ∉ P.getLast! → ipv6Suffix s P = .ok P) ∧
  (∀ s P v, '.' ∈ P.getLast! → ipv4Init (.str P.getLast!) = .ok v →
    ipv6Suffix s P = .ok (P.dropLast ++ [hexStr (v / 65536 % 65536), hexStr (v % 65536)])) ∧
  (∀ s e, s ≠ [] → s.length ≤ 45 → 3 ≤ (splitMax ':' 9 s).length → '.' ∈ (splitMax ':' 9 s).getLast! →
    ipv4Init (.str (splitMax ':' 9 s).getLast!) = .error e →
    ipIntFromString6 s = .error (avErr (do let r ← reprPlain s; if e.message.startsWith "~" then none else
      some (e.message ++ " in " ++ r)))) ∧
  (∀ s Q, Staged s Q → 9 < Q.length →
    ipIntFromString6 s = .error (avMsg "At most 8 colons permitted in " s)) ∧
  (∀ s Q, Staged s Q → Q.length ≤ 9 → 2 ≤ (innerEmpty Q).length →
    ipIntFromString6 s = .error (avMsg "At most one '::' permitted in " s)) ∧
  (∀ s Q k, Staged s Q → Q.length ≤ 9 → innerEmpty Q = [k] →
    (Q.head!.isEmpty = true ∧ layoutHi Q k ≠ 0) →
    ipIntFromString6 s = .error (avMsg "Leading ':' only permitted as part of '::' in " s)) ∧
  (∀ s Q k, Staged s Q → Q.length ≤ 9 → innerEmpty Q = [k] →
    ¬ (Q.head!.isEmpty = true ∧ layoutHi Q k ≠ 0) → (Q.getLast!.isEmpty = true ∧ layoutLo Q k ≠ 0) →
    ipIntFromString6 s = .error (avMsg "Trailing ':' only permitted as part of '::' in " s)) ∧
  (∀ s Q k, Staged s Q → Q.length ≤ 9 → innerEmpty Q = [k] →
    ¬ (Q.head!.isEmpty = true ∧ layoutHi Q k ≠ 0) → ¬ (Q.getLast!.isEmpty = true ∧ layoutLo Q k ≠ 0) →
    8 < layoutHi Q k + layoutLo Q k + 1 →
    ipIntFromString6 s = .error (avMsg "Expected at most 7 other parts with '::' in " s)) ∧
  (∀ s Q, Staged s Q → Q.length ≤ 9 → innerEmpty Q = [] → Q.length ≠ 8 →
    ipIntFromString6 s = .error (avMsg "Exactly 8 parts expected without '::' in " s)) ∧
  (∀ s Q, Staged s Q → innerEmpty Q = [] → Q.length = 8 → Q.head!.isEmpty = true →
    ipIntFromString6 s = .error (avMsg "Leading ':' only permitted as part of '::' in " s)) ∧
  (∀ s Q, Staged s Q → innerEmpty Q = [] → Q.length = 8 → Q.head!.isEmpty = false →
    Q.getLast!.isEmpty = true →
    ipIntFromString6 s = .error (avMsg "Trailing ':' only permitted as part of '::' in " s)) ∧
  (∀ s Q pre p post e, Staged s Q → innerEmpty Q = [] → Q.length = 8 → Q.head!.isEmpty = false →
    Q.getLast!.isEmpty = false → Q = pre ++ p :: post → (∀ q ∈ pre, ∃ v, parseHextet q = .ok v) →
    parseHextet p = .error e →
    ipIntFromString6 s = .error (avErr (do let m ← hexMsg p e; let r ← reprPlain s; pure (m ++ " in " ++ r)))) ∧
  (∀ s Q k pre p post e, Staged s Q → Q.length ≤ 9 → innerEmpty Q = [k] →
    ¬ (Q.head!.isEmpty = true ∧ layoutHi Q k ≠ 0) → ¬ (Q.getLast!.isEmpty = true ∧ layoutLo Q k ≠ 0) →
    ¬ 8 < layoutHi Q k + layoutLo Q k + 1 →
    Q.take (layoutHi Q k) ++ Q.drop (Q.length - layoutLo Q k) = pre ++ p :: post →
    (∀ q ∈ pre, ∃ v, parseHextet q = .ok v) → parseHextet p = .error e →
    ipIntFromString6 s = .error (avErr (do let m ← hexMsg p e; let r ← reprPlain s; pure (m ++ " in " ++ r))))

theorem v6ParseRefusals_proven : V6ParseRefusals := by
  refine ⟨ipIntFromString6_class, rfl, fun s h1 h2 => ?_, fun s h0 h45 h3 => ?_,
    fun s P hd => suffix_plain s P hd, fun s P v hd hv => suffix_v4 s P v hd hv,
    fun s e h0 h45 h3 hd hv => ?_,
    fun s Q hs h9 => ?_, fun s Q hs h9 h2 => ?_, fun s Q k hs h9 hk hc => ?_,
    fun s Q k hs h9 hk hc1 hc2 => ?_, fun s Q k hs h9 hk hc1 hc2 h8 => ?_,
    fun s Q hs h9 hk h8 => ?_, fun s Q hs hk h8 hh => ?_, fun s Q hs hk h8 hh hl => ?_,
    fun s Q pre p post e hs hk h8 hh hl hq hpre hp => ?_,
    fun s Q k pre p post e hs h9 hk hc1 hc2 h8 hq hpre hp => ?_⟩
  · have he : s.isEmpty = false := by cases s <;> simp_all
    have h1' : s.length > 45 := h1
    have h100 : ¬ s.length > 100 := by omega
    unfold ipIntFromString6
    simp only [he, h1', h100, Bool.false_eq_true, ↓reduceIte]
    rfl
  · have he : s.isEmpty = false := by cases s <;> simp_all
    have h45' : ¬ s.length > 45 := by omega
    unfold ipIntFromString6
    simp only [he, h45', h3, Bool.false_eq_true, ↓reduceIte]
    rfl
  · rw [prefix_eq s h0 h45 h3, suffix_err s _ e hd hv]
    rfl
  · rw [staged_eq s Q hs]
    have h9' : Q.length > 9 := h9
    unfold ipv6Layout
    simp only [h9', ↓reduceIte]
    rfl
  · rw [staged_eq s Q hs]
    have h9' : ¬ Q.length > 9 := by omega
    have h2' : decide (2 ≤ (innerEmpty Q).length) = true := decide_eq_true h2
    unfold ipv6Layout
    rw [skipScan_eq]
    simp only [h9', ↓reduceIte, h2']
    rfl
  · rw [staged_eq s Q hs, layout_skip s Q k (by omega) hk, if_pos hc]
    rfl
  · rw [staged_eq s Q hs, layout_skip s Q k (by omega) hk, if_neg hc1, if_pos hc2]
    rfl
  · rw [staged_eq s Q hs, layout_skip s Q k (by omega) hk, if_neg hc1, if_neg hc2, if_pos h8]
    rfl
  · rw [staged_eq s Q hs, layout_noskip s Q (by omega) hk, if_pos h8]
    rfl
  · rw [staged_eq s Q hs, layout_noskip s Q (by omega) hk, if_neg (by omega), if_pos hh]
    rfl
  · rw [staged_eq s Q hs, layout_noskip s Q (by omega) hk, if_neg (by omega), if_neg (by rw [hh]; decide),
      if_pos hl]
    rfl
  · rw [staged_eq s Q hs, layout_noskip s Q (by omega) hk, if_neg (by omega), if_neg (by rw [hh]; decide),
      if_neg (by rw [hl]; decide)]
    simp only [bind, Except.bind, ipv6Hextets, List.drop_eq_nil_of_le (Nat.le_refl _), Nat.sub_zero,
      List.drop_length, List.append_nil]
    rw [h8, show List.take 8 Q = Q by rw [← h8]; exact List.take_length, hq,
      parseHextets_first pre post p e hpre hp]
    rfl
  · rw [staged_eq s Q hs, layout_skip s Q k (by omega) hk, if_neg hc1, if_neg hc2, if_neg h8]
    simp only [bind, Except.bind, ipv6Hextets]
    rw [hq, parseHextets_first pre post p e hpre hp]
    rfl

end PyLean.Ipaddress
