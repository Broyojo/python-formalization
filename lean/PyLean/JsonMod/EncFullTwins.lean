import PyLean.JsonMod.EncFull

/-!
The two full encoders agree on exact containers with exact-`str` separators when neither hits
its recursion limit: the same text, or the same exception with corresponding notes (same kind,
same type, same index; a dict item's note names the original key in C and its converted text
in Python).
-/

namespace PyLean.JsonMod

open PyLean

def XKey.okx : XKey → Bool
  | .str s => strOk s
  | .flt _ r => fltOk r
  | .obj t _ => decide (truncName 100 t.tpName = t.name)
  | _ => true

mutual
/-- Exact containers only, every string a Python `str` (code points at most 0x10FFFF), ASCII
`float.__repr__`, and object keys whose `tp_name` (cut to 100 bytes) is their `__name__`. -/
def XVal.okx : XVal → Bool
  | .str s => strOk s
  | .flt _ r => fltOk r
  | .seq _ xs => XVal.okxList xs
  | .map _ kvs => XVal.okxItems kvs
  | .seqSub .. => false
  | .mapSub .. => false
  | _ => true
def XVal.okxList : List XVal → Bool
  | [] => true
  | x :: xs => x.okx && XVal.okxList xs
def XVal.okxItems : List (XKey × XVal) → Bool
  | [] => true
  | (k, x) :: xs => k.okx && x.okx && XVal.okxItems xs
end

/-- No custom `encoder`, exact-`str` separators, and `default` returns such values. -/
structure XCfg.Okx (cfg : XCfg) : Prop where
  cst : cfg.customEnc = none
  isep : cfg.itemSep.exact = true
  ksep : cfg.keySep.exact = true
  dfl : ∀ n t v', cfg.dflt n t = .ok v' → v'.okx = true

def IsRecCX {α : Type} (r : Except XErr α) : Prop := ∃ ns, r = .error (recEncC, ns)
def IsRecPyX {α : Type} (r : Except XErr α) : Prop := ∃ ns, r = .error (recEncPy, ns)

/-- Corresponding notes. -/
def NoteRel (cfg : XCfg) : Note → Note → Prop
  | .item t i, .item t' i' => t = t' ∧ i = i'
  | .obj t, .obj t' => t = t'
  | .key t (.orig k), .key t' (.conv s) => t = t' ∧ cKeyX cfg k = .ok (some s)
  | _, _ => False

/-- Corresponding note lists. -/
def NotesRel (cfg : XCfg) : List Note → List Note → Prop
  | [], [] => True
  | a :: as, b :: bs => NoteRel cfg a b ∧ NotesRel cfg as bs
  | _, _ => False

theorem NotesRel.snoc {cfg : XCfg} : ∀ {as bs : List Note}, NotesRel cfg as bs → ∀ {a b : Note},
    NoteRel cfg a b → NotesRel cfg (as ++ [a]) (bs ++ [b])
  | [], [], _, _, _, h => ⟨h, trivial⟩
  | _ :: _, _ :: _, ⟨h1, h2⟩, _, _, h => ⟨h1, NotesRel.snoc h2 h⟩
  | [], _ :: _, h, _, _, _ => h.elim
  | _ :: _, [], h, _, _, _ => h.elim

/-- Related outcomes: values related by `R`, or the same exception with corresponding notes, or
one of the two is its model's `RecursionError`. -/
def XRelW (cfg : XCfg) {α β : Type} (R : α → β → Prop) (rc : Except XErr α) (rp : Except XErr β) : Prop :=
  (∃ a b, rc = .ok a ∧ rp = .ok b ∧ R a b) ∨
  (∃ e nsC nsP, rc = .error (e, nsC) ∧ rp = .error (e, nsP) ∧ NotesRel cfg nsC nsP) ∨
  IsRecCX rc ∨ IsRecPyX rp

theorem XRelW.ok {cfg : XCfg} {α : Type} (a : α) : XRelW cfg Eq (.ok a) (.ok a) := Or.inl ⟨a, a, rfl, rfl, rfl⟩

theorem XRelW.err {cfg : XCfg} {α β : Type} {R : α → β → Prop} (e : PyExc) :
    XRelW cfg R (.error (xe e)) (.error (xe e)) :=
  Or.inr (Or.inl ⟨e, [], [], rfl, rfl, trivial⟩)

theorem XRelW.recC {cfg : XCfg} {α β : Type} {R : α → β → Prop} {rc : Except XErr α} {rp : Except XErr β}
    (h : IsRecCX rc) : XRelW cfg R rc rp := Or.inr (Or.inr (Or.inl h))

theorem XRelW.recPy {cfg : XCfg} {α β : Type} {R : α → β → Prop} {rc : Except XErr α} {rp : Except XErr β}
    (h : IsRecPyX rp) : XRelW cfg R rc rp := Or.inr (Or.inr (Or.inr h))

theorem IsRecCX.enter0 {α : Type} {c w : Nat} (h : c < w + 1) (k : (c' : Nat) → c' < c → Except XErr α) :
    IsRecCX (cEnterX c w k) :=
  ⟨[], by simp [cEnterX, xe, show ¬ (w + 1 ≤ c) by omega]⟩

theorem IsRecPyX.call0 {α : Type} (k : (b' : Nat) → b' < 0 → Except XErr α) : IsRecPyX (pyCallX 0 k) :=
  ⟨[], rfl⟩

theorem XRelW.addNote {cfg : XCfg} {α : Type} {rc rp : Except XErr α} (h : XRelW cfg Eq rc rp)
    {n1 n2 : Note} (hn : NoteRel cfg n1 n2) : XRelW cfg Eq (addNote n1 rc) (addNote n2 rp) := by
  rcases h with ⟨a, b, rfl, rfl, rfl⟩ | ⟨e, nsC, nsP, rfl, rfl, hf⟩ | ⟨ns, rfl⟩ | ⟨ns, rfl⟩
  · exact XRelW.ok a
  · exact Or.inr (Or.inl ⟨e, nsC ++ [n1], nsP ++ [n2], rfl, rfl, NotesRel.snoc hf hn⟩)
  · exact XRelW.recC ⟨ns ++ [n1], rfl⟩
  · exact XRelW.recPy ⟨ns ++ [n2], rfl⟩

/-- Errors pass through a `match` that propagates them, with a note added on both sides. -/
theorem XRelW.bindN {cfg : XCfg} {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop}
    {rc : Except XErr α} {rp : Except XErr β} (h : XRelW cfg R rc rp)
    (fc : XErr → Except XErr γ) (fp : XErr → Except XErr δ)
    (hf : ∀ e nsC nsP, NotesRel cfg nsC nsP → XRelW cfg S (fc (e, nsC)) (fp (e, nsP)))
    (hfc : ∀ ns, IsRecCX (fc (recEncC, ns))) (hfp : ∀ ns, IsRecPyX (fp (recEncPy, ns)))
    (kc : α → Except XErr γ) (kp : β → Except XErr δ) (hk : ∀ a b, R a b → XRelW cfg S (kc a) (kp b)) :
    XRelW cfg S (match rc with | .error e => fc e | .ok a => kc a)
      (match rp with | .error e => fp e | .ok b => kp b) := by
  rcases h with ⟨a, b, rfl, rfl, hr⟩ | ⟨e, nsC, nsP, rfl, rfl, hn⟩ | ⟨ns, rfl⟩ | ⟨ns, rfl⟩
  · exact hk a b hr
  · exact hf e nsC nsP hn
  · exact XRelW.recC (hfc ns)
  · exact XRelW.recPy (hfp ns)

/-! ### Leaves -/

theorem cWriteStringX_std {cfg : XCfg} (h : cfg.customEnc = none) (s : PStr) :
    cWriteStringX cfg s = .ok (cStrEnc cfg.toE s) := by
  simp [cWriteStringX, h, cFastEncode_eq]

theorem strLeaf {cfg : XCfg} (hO : cfg.Okx) (b : Nat) (s : PStr) (hs : strOk s = true) :
    XRelW cfg Eq (liftE (cWriteStringX cfg s)) (pyEncStrX cfg b s) := by
  rw [cWriteStringX_std hO.cst]
  simp only [liftE, pyEncStrX]
  cases b with
  | zero => exact XRelW.recPy ⟨[], rfl⟩
  | succ b =>
    simp only [pyCallX]
    rw [← strEnc_twins cfg.toE s hs]
    split
    · cases b with
      | zero => exact XRelW.recPy ⟨[], rfl⟩
      | succ b => exact XRelW.ok _
    · exact XRelW.ok _

theorem liftE_rel {cfg : XCfg} {α : Type} (r : Except PyExc α) : XRelW cfg Eq (liftE r) (liftE r) := by
  cases r with
  | ok a => exact XRelW.ok a
  | error e => exact XRelW.err e

theorem fltLeaf {cfg : XCfg} (b bits : Nat) (r : PStr) :
    XRelW cfg Eq (liftE (cEncodeFloat cfg.toE bits r)) (pyFloatX cfg b bits r) := by
  simp only [pyFloatX]
  cases b with
  | zero => exact XRelW.recPy ⟨[], rfl⟩
  | succ b => simp only [pyCallX, floatStr_twins]; exact liftE_rel _

theorem keyRel {cfg : XCfg} (b : Nat) (k : XKey) (hk : k.okx = true) :
    pyKeyX cfg b k = liftE (cKeyX cfg k) ∨ IsRecPyX (pyKeyX cfg b k) := by
  cases k with
  | str s => left; rfl
  | int n => left; rfl
  | bool bb => cases bb <;> left <;> rfl
  | none => left; rfl
  | flt bits r =>
    cases b with
    | zero => right; exact ⟨[], rfl⟩
    | succ b =>
      left
      simp only [pyKeyX, pyFloatX, pyCallX, cKeyX, floatStr_twins]
      cases cEncodeFloat cfg.toE bits r <;> rfl
  | obj t o =>
    left
    simp only [XKey.okx, decide_eq_true_eq] at hk
    simp only [pyKeyX, cKeyX, hk]
    split <;> rfl

theorem cKeyX_strOk {cfg : XCfg} {k : XKey} {ks : PStr} (hk : k.okx = true)
    (h : cKeyX cfg k = .ok (some ks)) : strOk ks = true := by
  have := keyStr_ok (cfg := cfg.toE) (k := k.toE) (ks := ks)
  cases k with
  | obj t o =>
    simp only [cKeyX] at h
    split at h <;> cases h
  | str s => simp [cKeyX] at h; subst h; simpa [XKey.okx] using hk
  | flt bits r =>
    simp only [cKeyX] at h
    exact this (by simpa [XKey.okx, XKey.toE, EKey.ok] using hk) (by simpa [cKeyStr, XKey.toE] using h)
  | int n => exact this rfl (by simpa [cKeyStr, XKey.toE, cKeyX] using h)
  | bool bb => exact this rfl (by cases bb <;> simpa [cKeyStr, XKey.toE, cKeyX] using h)
  | none => exact this rfl (by simpa [cKeyStr, XKey.toE, cKeyX] using h)

/-! ### Loops -/

/-- What the loops need of the items: C's `encoder_listencode_obj` and Python's dispatch inside
the `try` are related. -/
def ItemSim (cfg : XCfg) (c b : Nat) : Prop :=
  ∀ lvl seen anc x, (∀ a ∈ anc, XVal.okx a = true) → x.okx = true →
    XRelW cfg Eq (cObjX cfg c lvl seen anc x) (pyItemX cfg b lvl seen anc x)

theorem seqLoop {cfg : XCfg} {c b : Nat} (H : ItemSim cfg c b) (lvl : Nat) (seen : List Nat)
    (anc : List XVal) (hanc : ∀ a ∈ anc, XVal.okx a = true) (t : PyType) (sep buf0 : PStr) :
    ∀ (xs : List XVal) (i : Nat), XVal.okxList xs = true → i ≠ 0 →
    XRelW cfg Eq (cSeqItemsX cfg c lvl seen anc t (.ok sep) i xs) (pyListItemsX cfg b lvl seen anc t buf0 sep i xs) := by
  intro xs
  induction xs with
  | nil => intro i _ _; simp only [cSeqItemsX, pyListItemsX]; exact XRelW.ok _
  | cons x xs ih =>
    intro i hx hi
    simp only [XVal.okxList, Bool.and_eq_true] at hx
    simp only [cSeqItemsX, pyListItemsX, hi, ne_eq, not_false_eq_true, ↓reduceIte]
    have h1 := H lvl seen anc x hanc hx.1
    generalize cObjX cfg c lvl seen anc x = X at h1 ⊢
    generalize pyItemX cfg b lvl seen anc x = Y at h1 ⊢
    rcases h1 with ⟨a, _, rfl, rfl, rfl⟩ | ⟨e, nsC, nsP, rfl, rfl, hn⟩ | ⟨ns, rfl⟩ | ⟨ns, rfl⟩
    · simp only
      have h2 := ih (i + 1) hx.2 (by omega)
      generalize cSeqItemsX cfg c lvl seen anc t (.ok sep) (i + 1) xs = X2 at h2 ⊢
      generalize pyListItemsX cfg b lvl seen anc t buf0 sep (i + 1) xs = Y2 at h2 ⊢
      rcases h2 with ⟨r, _, rfl, rfl, rfl⟩ | ⟨e, nsC, nsP, rfl, rfl, hn⟩ | ⟨ns, rfl⟩ | ⟨ns, rfl⟩
      · exact XRelW.ok _
      · exact Or.inr (Or.inl ⟨e, nsC, nsP, rfl, rfl, hn⟩)
      · exact XRelW.recC ⟨ns, rfl⟩
      · exact XRelW.recPy ⟨ns, rfl⟩
    · exact Or.inr (Or.inl ⟨e, _, _, rfl, rfl, NotesRel.snoc hn ⟨rfl, rfl⟩⟩)
    · exact XRelW.recC ⟨ns ++ [_], rfl⟩
    · exact XRelW.recPy ⟨ns ++ [_], rfl⟩

/-- The first item: Python writes the opening bracket with it. -/
theorem seqLoop0 {cfg : XCfg} {c b : Nat} (H : ItemSim cfg c b) (lvl : Nat) (seen : List Nat)
    (anc : List XVal) (hanc : ∀ a ∈ anc, XVal.okx a = true) (t : PyType) (sep buf0 : PStr)
    (x : XVal) (xs : List XVal) (hx : XVal.okxList (x :: xs) = true) :
    XRelW cfg (fun tc tp => tp = buf0 ++ tc) (cSeqItemsX cfg c lvl seen anc t (.ok sep) 0 (x :: xs))
      (pyListItemsX cfg b lvl seen anc t buf0 sep 0 (x :: xs)) := by
  simp only [XVal.okxList, Bool.and_eq_true] at hx
  simp only [cSeqItemsX, pyListItemsX, ne_eq, not_true_eq_false, ↓reduceIte]
  have h1 := H lvl seen anc x hanc hx.1
  generalize cObjX cfg c lvl seen anc x = X at h1 ⊢
  generalize pyItemX cfg b lvl seen anc x = Y at h1 ⊢
  rcases h1 with ⟨a, _, rfl, rfl, rfl⟩ | ⟨e, nsC, nsP, rfl, rfl, hn⟩ | ⟨ns, rfl⟩ | ⟨ns, rfl⟩
  · simp only
    have h2 := seqLoop H lvl seen anc hanc t sep buf0 xs 1 hx.2 (by omega)
    generalize cSeqItemsX cfg c lvl seen anc t (.ok sep) (0 + 1) xs = X2 at h2 ⊢
    generalize pyListItemsX cfg b lvl seen anc t buf0 sep (0 + 1) xs = Y2 at h2 ⊢
    rcases h2 with ⟨r, _, rfl, rfl, rfl⟩ | ⟨e, nsC, nsP, rfl, rfl, hn⟩ | ⟨ns, rfl⟩ | ⟨ns, rfl⟩
    · exact Or.inl ⟨_, _, rfl, rfl, by simp⟩
    · exact Or.inr (Or.inl ⟨e, nsC, nsP, rfl, rfl, hn⟩)
    · exact XRelW.recC ⟨ns, rfl⟩
    · exact XRelW.recPy ⟨ns, rfl⟩
  · exact Or.inr (Or.inl ⟨e, _, _, rfl, rfl, NotesRel.snoc hn ⟨rfl, rfl⟩⟩)
  · exact XRelW.recC ⟨ns ++ [_], rfl⟩
  · exact XRelW.recPy ⟨ns ++ [_], rfl⟩

/-- The items of an exact dict: 2-tuples with keys and values that satisfy the invariants. -/
def ItemsOk (its : List (ItemShape × XKey × XVal)) : Prop :=
  ∀ p ∈ its, (match p.1 with | .tup => True | _ => False) ∧ p.2.1.okx = true ∧ p.2.2.okx = true

theorem mapLoop {cfg : XCfg} (hO : cfg.Okx) {c b : Nat} (H : ItemSim cfg c b) (lvl : Nat) (seen : List Nat)
    (anc : List XVal) (hanc : ∀ a ∈ anc, XVal.okx a = true) (t : PyType) (sep nl : PStr) :
    ∀ (its : List (ItemShape × XKey × XVal)) (first : Bool), ItemsOk its →
    XRelW cfg Eq (cMapItemsX cfg c lvl seen anc t (.ok sep) nl first its)
      (pyDictItemsX cfg b lvl seen anc t nl sep first its) := by
  intro its
  induction its with
  | nil => intro first _; simp only [cMapItemsX, pyDictItemsX]; exact XRelW.ok _
  | cons p rest ih =>
    intro first hok
    obtain ⟨sh, k, x⟩ := p
    have hp := hok (sh, k, x) (by simp)
    have hrest : ItemsOk rest := fun q hq => hok q (by simp [hq])
    obtain ⟨hsh, hk, hx⟩ := hp
    cases sh with
    | lst => exact hsh.elim
    | bad e => exact hsh.elim
    | tup =>
      simp only [cMapItemsX, pyDictItemsX, cNoteKey]
      rcases keyRel (cfg := cfg) b k hk with hkr | hkr
      · rw [hkr]
        cases hc : cKeyX cfg k with
        | error e => exact XRelW.err e
        | ok o =>
          cases o with
          | none => exact ih first hrest
          | some ks =>
            simp only [liftE]
            obtain ⟨pre, hpre, hpre'⟩ : ∃ pre, (if first = true then (Except.ok nl : Except PyExc PStr) else .ok sep) = .ok pre ∧
                pre = (if first = true then nl else sep) := ⟨_, by cases first <;> rfl, rfl⟩
            rw [hpre]
            simp only
            have hks := cKeyX_strOk hk hc
            rw [cWriteStringX_std hO.cst]
            simp only [writeStrObj, hO.ksep, ↓reduceIte]
            have hstr := strLeaf hO b ks hks
            rw [cWriteStringX_std hO.cst] at hstr
            simp only [liftE] at hstr
            generalize pyEncStrX cfg b ks = Z at hstr ⊢
            rcases hstr with ⟨a, _, h1, rfl, rfl⟩ | ⟨e, _, _, h1, _, _⟩ | ⟨ns, h1⟩ | ⟨ns, rfl⟩
            · cases h1
              have h1 := H lvl seen anc x hanc hx
              generalize cObjX cfg c lvl seen anc x = X at h1 ⊢
              generalize pyItemX cfg b lvl seen anc x = Y at h1 ⊢
              rcases h1 with ⟨a, _, rfl, rfl, rfl⟩ | ⟨e, nsC, nsP, rfl, rfl, hn⟩ | ⟨ns, rfl⟩ | ⟨ns, rfl⟩
              · have h2 := ih false hrest
                generalize cMapItemsX cfg c lvl seen anc t (.ok sep) nl false rest = X2 at h2 ⊢
                generalize pyDictItemsX cfg b lvl seen anc t nl sep false rest = Y2 at h2 ⊢
                rcases h2 with ⟨r, _, rfl, rfl, rfl⟩ | ⟨e, nsC, nsP, rfl, rfl, hn⟩ | ⟨ns, rfl⟩ | ⟨ns, rfl⟩
                · subst hpre'; exact XRelW.ok _
                · exact Or.inr (Or.inl ⟨e, nsC, nsP, rfl, rfl, hn⟩)
                · exact XRelW.recC ⟨ns, rfl⟩
                · exact XRelW.recPy ⟨ns, rfl⟩
              · exact Or.inr (Or.inl ⟨e, _, _, rfl, rfl, NotesRel.snoc hn
                  (show NoteRel cfg (.key t (.orig k)) (.key t (.conv ks)) from ⟨rfl, hc⟩)⟩)
              · exact XRelW.recC ⟨ns ++ [_], rfl⟩
              · exact XRelW.recPy ⟨ns ++ [_], rfl⟩
            · cases h1
            · cases h1
            · exact XRelW.recPy ⟨ns, rfl⟩
      · obtain ⟨ns, hns⟩ := hkr
        rw [hns]
        exact XRelW.recPy ⟨ns, rfl⟩

/-! ### Containers and the induction on the stack room -/

theorem mem_xInsert (p : XKey × XVal) : ∀ (l : List (XKey × XVal)) (q : XKey × XVal),
    q ∈ xInsert p l → q = p ∨ q ∈ l
  | [], q, h => by simp [xInsert] at h; exact Or.inl h
  | r :: l, q, h => by
    simp only [xInsert] at h
    split at h
    · simpa using h
    · simp only [List.mem_cons] at h
      rcases h with h | h
      · exact Or.inr (by simp [h])
      · rcases mem_xInsert p l q h with h | h
        · exact Or.inl h
        · exact Or.inr (by simp [h])

theorem mem_foldr_xInsert : ∀ (kvs : List (XKey × XVal)) (q : XKey × XVal), q ∈ kvs.foldr xInsert [] → q ∈ kvs
  | [], q, h => by simp at h
  | p :: l, q, h => by
    simp only [List.foldr_cons] at h
    rcases mem_xInsert p _ q h with h | h
    · simp [h]
    · exact List.mem_cons_of_mem _ (mem_foldr_xInsert l q h)

theorem xSortItems_mem {kvs l : List (XKey × XVal)} (h : xSortItems kvs = .ok l) :
    ∀ q ∈ l, q ∈ kvs := by
  unfold xSortItems at h
  split at h
  · cases h; intro q hq; simp at hq
  · cases h; exact fun q hq => hq
  · split at h
    · cases h; exact mem_foldr_xInsert _
    · cases h

theorem okxItems_mem : ∀ {kvs : List (XKey × XVal)}, XVal.okxItems kvs = true →
    ∀ q ∈ kvs, q.1.okx = true ∧ q.2.okx = true
  | [], _, q, hq => by simp at hq
  | (k, x) :: l, h, q, hq => by
    simp only [XVal.okxItems, Bool.and_eq_true] at h
    simp only [List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact ⟨h.1.1, h.1.2⟩
    · exact okxItems_mem h.2 q hq

theorem cExactItems_ok {cfg : XCfg} {kvs : List (XKey × XVal)} {its : List (ItemShape × XKey × XVal)}
    (hk : XVal.okxItems kvs = true) (h : cExactItems cfg kvs = .ok its) : ItemsOk its := by
  unfold cExactItems at h
  split at h
  · cases hs : xSortItems kvs with
    | error e => rw [hs] at h; cases h
    | ok l =>
      rw [hs] at h
      simp only [Except.map, Except.ok.injEq] at h
      subst h
      intro p hp
      simp only [List.mem_map] at hp
      obtain ⟨⟨k, x⟩, hm, rfl⟩ := hp
      have := okxItems_mem hk (k, x) (xSortItems_mem hs _ hm)
      exact ⟨trivial, this.1, this.2⟩
  · simp only [Except.ok.injEq] at h
    subst h
    intro p hp
    simp only [List.mem_map] at hp
    obtain ⟨⟨k, x⟩, hm, rfl⟩ := hp
    have := okxItems_mem hk (k, x) hm
    exact ⟨trivial, this.1, this.2⟩

/-- `SimAt cfg c`: with stack room `c`, C's `encoder_listencode_obj` and the body of Python's
`_iterencode` are related, for every frame budget. -/
def SimAt (cfg : XCfg) (c : Nat) : Prop :=
  ∀ b lvl seen anc v, (∀ a ∈ anc, XVal.okx a = true) → v.okx = true →
    XRelW cfg Eq (cObjX cfg c lvl seen anc v) (pyIterX cfg b lvl seen anc v)

theorem itemSim_of {cfg : XCfg} {c : Nat} (h : SimAt cfg c) (b : Nat) : ItemSim cfg c b := by
  intro lvl seen anc x hanc hx
  cases x with
  | other n t =>
    simp only [pyItemX]
    cases b with
    | zero => exact XRelW.recPy ⟨[], rfl⟩
    | succ b => simp only [pyCallX]; exact h b lvl seen anc _ hanc hx
  | _ => simp only [pyItemX]; exact h b lvl seen anc _ hanc hx

theorem contSim {cfg : XCfg} (hO : cfg.Okx) {c : Nat} (h : SimAt cfg c) (b lvl : Nat) (seen : List Nat)
    (anc : List XVal) (hanc : ∀ a ∈ anc, XVal.okx a = true) (cyc : Bool) (a : XVal) (ha : a.okx = true) :
    XRelW cfg Eq (cContX cfg c lvl seen anc cyc a) (pyContX cfg b lvl seen anc cyc a) := by
  have H := itemSim_of h b
  have hanc' : ∀ y ∈ a :: anc, XVal.okx y = true := by
    intro y hy
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact ha
    · exact hanc y hy
  cases a with
  | seq t xs =>
    simp only [cContX, pyContX, cSeqPart, pyListPart]
    cases xs with
    | nil => exact XRelW.ok _
    | cons x xs =>
      simp only [List.length_cons, Nat.add_one_ne_zero, ↓reduceIte, List.isEmpty_cons, Bool.not_false,
        Bool.not_true, Bool.false_eq_true]
      by_cases hc : cfg.checkCircular = true ∧ cyc = true
      · simp only [hc, and_self, ↓reduceIte]; exact XRelW.err _
      simp only [hc, ↓reduceIte]
      cases hi : cfg.indent with
      | some ind =>
        simp only
        have h0 := seqLoop0 H (lvl + 1) seen _ hanc' t (cfg.itemSep.raw ++ cNewlineIndent ind (lvl + 1))
          ([91] ++ [10] ++ rep ind (lvl + 1)) x xs ha
        rw [show cfg.itemSep.raw ++ [10] ++ rep ind (lvl + 1) = cfg.itemSep.raw ++ cNewlineIndent ind (lvl + 1) by
          simp [cNewlineIndent]]
        generalize cSeqItemsX cfg c (lvl + 1) seen (XVal.seq t (x :: xs) :: anc) t
          (.ok (cfg.itemSep.raw ++ cNewlineIndent ind (lvl + 1))) 0 (x :: xs) = X at h0 ⊢
        generalize pyListItemsX cfg b (lvl + 1) seen (XVal.seq t (x :: xs) :: anc) t ([91] ++ [10] ++ rep ind (lvl + 1))
          (cfg.itemSep.raw ++ cNewlineIndent ind (lvl + 1)) 0 (x :: xs) = Y at h0 ⊢
        rcases h0 with ⟨r, _, rfl, rfl, rfl⟩ | ⟨e, nsC, nsP, rfl, rfl, hn⟩ | ⟨ns, rfl⟩ | ⟨ns, rfl⟩
        · exact Or.inl ⟨_, _, rfl, rfl, by simp [cNewlineIndent]⟩
        · exact Or.inr (Or.inl ⟨e, nsC, nsP, rfl, rfl, hn⟩)
        · exact XRelW.recC ⟨ns, rfl⟩
        · exact XRelW.recPy ⟨ns, rfl⟩
      | none =>
        simp only [writeStrObj, hO.isep, ↓reduceIte]
        have h0 := seqLoop0 H lvl seen _ hanc' t cfg.itemSep.raw [91] x xs ha
        generalize cSeqItemsX cfg c lvl seen (XVal.seq t (x :: xs) :: anc) t (.ok cfg.itemSep.raw) 0 (x :: xs) = X at h0 ⊢
        generalize pyListItemsX cfg b lvl seen (XVal.seq t (x :: xs) :: anc) t [91] cfg.itemSep.raw 0 (x :: xs) = Y at h0 ⊢
        rcases h0 with ⟨r, _, rfl, rfl, rfl⟩ | ⟨e, nsC, nsP, rfl, rfl, hn⟩ | ⟨ns, rfl⟩ | ⟨ns, rfl⟩
        · exact Or.inl ⟨_, _, rfl, rfl, by simp⟩
        · exact Or.inr (Or.inl ⟨e, nsC, nsP, rfl, rfl, hn⟩)
        · exact XRelW.recC ⟨ns, rfl⟩
        · exact XRelW.recPy ⟨ns, rfl⟩
  | map t kvs =>
    simp only [cContX, pyContX, pyExactItems]
    unfold cMapPart pyDictPart
    cases kvs with
    | nil => simp only [List.length_nil, decide_true, ↓reduceIte, List.isEmpty_nil, Bool.not_true, Bool.not_false]; exact XRelW.ok _
    | cons p kvs =>
      simp only [List.length_cons, Nat.add_one_ne_zero, decide_false, Bool.false_eq_true, ↓reduceIte,
        List.isEmpty_cons, Bool.not_false, Bool.not_true]
      by_cases hc : cfg.checkCircular = true ∧ cyc = true
      · simp only [hc, and_self, ↓reduceIte]; exact XRelW.err _
      simp only [hc, ↓reduceIte]
      cases hI : cExactItems cfg (p :: kvs) with
      | error e => exact XRelW.err e
      | ok its =>
        have hok := cExactItems_ok ha hI
        simp only [Except.map]
        cases hi : cfg.indent with
        | some ind =>
          simp only
          have h0 := mapLoop hO H (lvl + 1) seen _ hanc' t (cfg.itemSep.raw ++ cNewlineIndent ind (lvl + 1))
            (cNewlineIndent ind (lvl + 1)) its true hok
          rw [show cfg.itemSep.raw ++ [10] ++ rep ind (lvl + 1) = cfg.itemSep.raw ++ cNewlineIndent ind (lvl + 1) by
            simp [cNewlineIndent], show [10] ++ rep ind (lvl + 1) = cNewlineIndent ind (lvl + 1) from rfl]
          generalize cMapItemsX cfg c (lvl + 1) seen (XVal.map t (p :: kvs) :: anc) t
            (.ok (cfg.itemSep.raw ++ cNewlineIndent ind (lvl + 1))) (cNewlineIndent ind (lvl + 1)) true its = X at h0 ⊢
          generalize pyDictItemsX cfg b (lvl + 1) seen (XVal.map t (p :: kvs) :: anc) t (cNewlineIndent ind (lvl + 1))
            (cfg.itemSep.raw ++ cNewlineIndent ind (lvl + 1)) true its = Y at h0 ⊢
          rcases h0 with ⟨⟨r, f⟩, _, rfl, rfl, rfl⟩ | ⟨e, nsC, nsP, rfl, rfl, hn⟩ | ⟨ns, rfl⟩ | ⟨ns, rfl⟩
          · exact Or.inl ⟨_, _, rfl, rfl, by cases f <;> simp [cNewlineIndent]⟩
          · exact Or.inr (Or.inl ⟨e, nsC, nsP, rfl, rfl, hn⟩)
          · exact XRelW.recC ⟨ns, rfl⟩
          · exact XRelW.recPy ⟨ns, rfl⟩
        | none =>
          simp only [writeStrObj, hO.isep, ↓reduceIte]
          have h0 := mapLoop hO H lvl seen _ hanc' t cfg.itemSep.raw [] its true hok
          generalize cMapItemsX cfg c lvl seen (XVal.map t (p :: kvs) :: anc) t (.ok cfg.itemSep.raw) [] true its = X at h0 ⊢
          generalize pyDictItemsX cfg b lvl seen (XVal.map t (p :: kvs) :: anc) t [] cfg.itemSep.raw true its = Y at h0 ⊢
          rcases h0 with ⟨⟨r, f⟩, _, rfl, rfl, rfl⟩ | ⟨e, nsC, nsP, rfl, rfl, hn⟩ | ⟨ns, rfl⟩ | ⟨ns, rfl⟩
          · exact XRelW.ok _
          · exact Or.inr (Or.inl ⟨e, nsC, nsP, rfl, rfl, hn⟩)
          · exact XRelW.recC ⟨ns, rfl⟩
          · exact XRelW.recPy ⟨ns, rfl⟩
  | seqSub => simp [XVal.okx] at ha
  | mapSub => simp [XVal.okx] at ha
  | _ => simp only [cContX, pyContX]; exact XRelW.err _

theorem simStep {cfg : XCfg} (hO : cfg.Okx) (c : Nat) (ih : ∀ c', c' < c → SimAt cfg c') : SimAt cfg c := by
  intro b lvl seen anc v hanc hv
  -- the containers: `_Py_EnterRecursiveCall` and a generator frame
  have cont : ∀ (cyc : Bool) (a : XVal) (w : Nat), a.okx = true →
      XRelW cfg Eq (cEnterX c w (fun c' _ => cContX cfg c' lvl seen anc cyc a))
        (pyCallX b (fun b' _ => pyContX cfg b' lvl seen anc cyc a)) := by
    intro cyc a w ha
    by_cases hw : w + 1 ≤ c
    · cases b with
      | zero => exact XRelW.recPy ⟨[], rfl⟩
      | succ b =>
        simp only [cEnterX, hw, ↓reduceDIte, pyCallX]
        exact contSim hO (ih _ (by omega)) b lvl seen anc hanc cyc a ha
    · exact XRelW.recC (IsRecCX.enter0 (by omega) _)
  cases v with
  | none => simp only [cObjX, pyIterX]; exact XRelW.ok _
  | bool bb => cases bb <;> simp only [cObjX, pyIterX] <;> exact XRelW.ok _
  | str s => simp only [cObjX, pyIterX]; exact strLeaf hO b s hv
  | int n => simp only [cObjX, pyIterX]; exact liftE_rel _
  | flt bits r => simp only [cObjX, pyIterX]; exact fltLeaf b bits r
  | seq t xs => simp only [cObjX, pyIterX]; exact cont false _ _ hv
  | map t kvs => simp only [cObjX, pyIterX]; exact cont false _ _ hv
  | seqSub => simp [XVal.okx] at hv
  | mapSub => simp [XVal.okx] at hv
  | back k =>
    simp only [cObjX, pyIterX]
    cases ha : anc[k]? with
    | none => exact XRelW.err _
    | some a => exact cont true a _ (hanc a (List.mem_of_getElem? ha))
  | other n t =>
    simp only [cObjX, pyIterX]
    by_cases hc : cfg.checkCircular = true ∧ n ∈ seen
    · simp only [hc, and_self, ↓reduceIte]; exact XRelW.err _
    simp only [hc, ↓reduceIte]
    cases b with
    | zero => exact XRelW.recPy ⟨[], rfl⟩
    | succ b =>
      simp only [pyCallX]
      cases hd : cfg.dflt n t with
      | error e => exact XRelW.err e
      | ok v' =>
        simp only [liftE]
        by_cases hw : cfg.stk .dflt + 1 ≤ c
        · simp only [cEnterX, hw, ↓reduceDIte]
          exact XRelW.addNote (ih _ (by omega) b lvl (n :: seen) anc v' hanc (hO.dfl n t v' hd))
            (show NoteRel cfg (.obj t) (.obj t) from rfl)
        · exact XRelW.recC (IsRecCX.enter0 (by omega) _)

theorem simX {cfg : XCfg} (hO : cfg.Okx) : ∀ c, SimAt cfg c := by
  intro c
  induction c using Nat.strongRecOn with
  | ind c ih => exact simStep hO c ih

end PyLean.JsonMod
