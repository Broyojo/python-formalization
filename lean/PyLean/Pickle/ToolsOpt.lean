import PyLean.Pickle.ToolsDis

/-!
The output of `pickletools.optimize` (`Lib/pickletools.py:2356-2418`) on every
stream with the pickler's memo discipline, stated without the dict and counters of
the source: each opcode's kind, the keys a GET uses, and each kept PUT's rank among
the kept PUTs.
-/

namespace PyLean.Pickle

open PyLean

/-- The kind of an opcode for `optimize`: the tests of its first loop in their
order, `:2366-2387` (`'PUT' in name`, `MEMOIZE`, `'FRAME' in name`, `'GET' in name`,
`PROTO`). -/
inductive OKind where
  | put (k : Int)
  | memoize
  | frame
  | get (k : Int)
  | proto (v : Int)
  | other
  deriving DecidableEq

def okind (op : GenOp) : OKind :=
  if hasSub op.info.name "PUT" then .put (memoKey op.arg)
  else if op.info.name = "MEMOIZE" then .memoize
  else if hasSub op.info.name "FRAME" then .frame
  else if hasSub op.info.name "GET" then .get (memoKey op.arg)
  else if op.info.name = "PROTO" then .proto (memoKey op.arg)
  else .other

/-- What `optimize` keeps of each opcode after the header, `n` being the number of
memo opcodes before it: a PUT of its key, a MEMOIZE as a PUT of `n`, a GET of its
key, or the opcode's own bytes; FRAME is dropped. -/
def classify (n : Nat) : List GenOp → List OptOp
  | [] => []
  | op :: r =>
    match okind op with
    | .put k => .put k :: classify (n + 1) r
    | .memoize => .put n :: classify (n + 1) r
    | .frame => classify n r
    | .get k => .get k :: classify n r
    | _ => .raw (op.pos.getD 0) (op.endPos.getD 0) :: classify n r

/-- The opcodes after a leading `PROTO`, which becomes the header. -/
def bodyOps : List GenOp → List GenOp
  | [] => []
  | op :: r =>
    match okind op with
    | .proto _ => r
    | _ => op :: r

theorem bodyOps_cons (op : GenOp) (r : List GenOp) :
    bodyOps (op :: r) = match okind op with
      | .proto _ => r
      | _ => op :: r := rfl

/-- `protoheader`: the bytes of a leading `PROTO`. -/
def headerOf (p : Bytes) : List GenOp → Bytes
  | [] => []
  | op :: _ =>
    match okind op with
    | .proto _ => slice p 0 (op.endPos.getD 0)
    | _ => []

theorem headerOf_cons (p : Bytes) (op : GenOp) (r : List GenOp) :
    headerOf p (op :: r) = match okind op with
      | .proto _ => slice p 0 (op.endPos.getD 0)
      | _ => [] := rfl

/-- `proto`: the largest `PROTO` argument and GET protocol, from 0. -/
def protoStep (m : Int) (op : GenOp) : Int :=
  match okind op with
  | .get _ => max m op.info.proto
  | .proto v => max m v
  | _ => m

def putKeys : List OptOp → List Int
  | [] => []
  | .put k :: r => k :: putKeys r
  | _ :: r => putKeys r

def getKeys : List OptOp → List Int
  | [] => []
  | .get k :: r => k :: getKeys r
  | _ :: r => getKeys r

/-- Every GET reads a key some earlier memo opcode stored (`seen`). -/
def GetsAfterPuts : List Int → List OptOp → Prop
  | _, [] => True
  | seen, .put k :: r => GetsAfterPuts (k :: seen) r
  | seen, .get k :: r => k ∈ seen ∧ GetsAfterPuts seen r
  | seen, .raw _ _ :: r => GetsAfterPuts seen r

def optOps (ops : List GenOp) : List OptOp := classify 0 (bodyOps ops)

/-- The pickler's memo discipline: no two memo opcodes store the same key, and every
GET reads a key an earlier memo opcode stored. -/
def MemoWF (ops : List GenOp) : Prop :=
  (putKeys (optOps ops)).Nodup ∧ GetsAfterPuts [] (optOps ops)

/-- The writes of the second loop: a PUT whose key some GET uses becomes
`pickler.put(i)`, and a GET `pickler.get(i)`, `i` being the rank of the key among the
kept PUTs (`kept`); an unused PUT is dropped; other opcodes are copied, those over
`_FRAME_SIZE_TARGET` outside any frame. -/
def emitSpec (proto : Nat) (p : Bytes) (used : Int → Bool) (kept : List Int) :
    List OptOp → Py (List Event)
  | [] => .ok []
  | .put k :: r =>
    if used k then do
      let d ← pyPut proto (kept.idxOf k)
      let rest ← emitSpec proto p used kept r
      return [.boundary, .w d] ++ rest
    else emitSpec proto p used kept r
  | .get k :: r => do
    let d ← pyGet proto (kept.idxOf k)
    let rest ← emitSpec proto p used kept r
    return [.boundary, .w d] ++ rest
  | .raw a b :: r => do
    let rest ← emitSpec proto p used kept r
    return (if (slice p a b).length > frameSizeTarget then [.large [] (slice p a b)]
      else [.boundary, .w (slice p a b)]) ++ rest

/-- The output of `optimize`: the header, then the kept opcodes, framed by the
pickler's `_Framer` from protocol 4. -/
def optimizeSpec (p : Bytes) (ops : List GenOp) : Py Bytes := do
  let pr ← pyProtocol (ops.foldl protoStep 0)
  let c := optOps ops
  let used := fun k => (getKeys c).contains k
  let evs ← emitSpec pr p used ((putKeys c).filter used) c
  return headerOf p ops ++ pyFrame ((if pr ≥ 4 then [.start] else []) ++ evs ++ [.finish])

/-- `optimize` (`Lib/pickletools.py:2356-2418`) on every stream `genops` accepts whose
memo opcodes follow the pickler's discipline (`MemoWF`, true of every pickle
`pickle.dumps` writes): its output is the header, every opcode except FRAME and the
PUTs no GET uses, each kept PUT and each GET renumbered to the rank of its key among
the kept PUTs, written by the pickler at the stream's protocol, and framed again
from protocol 4. A GET of a key no earlier PUT stored is outside the hypothesis; see
`OptimizeGetNone`. -/
def OptimizeExact : Prop :=
  ∀ (p : Bytes) (ops : List GenOp), genops true p = .ok ops → MemoWF ops →
    optimize p = optimizeSpec p ops

/-! ## The first loop -/

theorem optStep_eq (p : Bytes) (s : OptSt) (op : GenOp) :
    optStep p s op =
      match okind op with
      | .put k => { s with oldids := addId s.oldids k, ops := .put k :: s.ops }
      | .memoize => { s with oldids := addId s.oldids (s.oldids.length : Int),
                             ops := .put (s.oldids.length : Int) :: s.ops }
      | .frame => s
      | .get k => { s with proto := max s.proto op.info.proto, newids := addNew s.newids k,
                           ops := .get k :: s.ops }
      | .proto v =>
        if op.pos.getD 0 = 0 then
          { s with proto := max s.proto v, header := slice p (op.pos.getD 0) (op.endPos.getD 0) }
        else { s with proto := max s.proto v, ops := .raw (op.pos.getD 0) (op.endPos.getD 0) :: s.ops }
      | .other => { s with ops := .raw (op.pos.getD 0) (op.endPos.getD 0) :: s.ops } := by
  unfold optStep okind
  dsimp only
  by_cases h1 : hasSub op.info.name "PUT" = true
  · rw [if_pos h1, if_pos h1]
  rw [if_neg h1, if_neg h1]
  by_cases h2 : op.info.name = "MEMOIZE"
  · rw [if_pos h2, if_pos h2]
  rw [if_neg h2, if_neg h2]
  by_cases h3 : hasSub op.info.name "FRAME" = true
  · rw [if_pos h3, if_pos h3]
  rw [if_neg h3, if_neg h3]
  by_cases h4 : hasSub op.info.name "GET" = true
  · rw [if_pos h4, if_pos h4]
  rw [if_neg h4, if_neg h4]
  by_cases h5 : op.info.name = "PROTO"
  · rw [if_pos h5, if_pos h5]
    dsimp only
    by_cases h6 : op.pos.getD 0 = 0
    · rw [if_pos h6, if_pos h6]
      rfl
    · rw [if_neg h6, if_neg h6]
  rw [if_neg h5, if_neg h5]

def newidStep (N : List (Int × Option Nat)) (op : GenOp) : List (Int × Option Nat) :=
  match okind op with
  | .get k => addNew N k
  | _ => N

theorem optStep_proto (p : Bytes) (s : OptSt) (op : GenOp) :
    (optStep p s op).proto = protoStep s.proto op := by
  rw [optStep_eq]
  unfold protoStep
  cases okind op with
  | proto v => dsimp only; split <;> rfl
  | _ => rfl

theorem optStep_newids (p : Bytes) (s : OptSt) (op : GenOp) :
    (optStep p s op).newids = newidStep s.newids op := by
  rw [optStep_eq]
  unfold newidStep
  cases okind op with
  | proto v => dsimp only; split <;> rfl
  | _ => rfl

theorem fold_proto (p : Bytes) :
    ∀ (ops : List GenOp) (s : OptSt), (ops.foldl (optStep p) s).proto = ops.foldl protoStep s.proto := by
  intro ops
  induction ops with
  | nil => intro s; rfl
  | cons op r ih => intro s; rw [List.foldl_cons, List.foldl_cons, ih, optStep_proto]

theorem fold_newids (p : Bytes) :
    ∀ (ops : List GenOp) (s : OptSt), (ops.foldl (optStep p) s).newids = ops.foldl newidStep s.newids := by
  intro ops
  induction ops with
  | nil => intro s; rfl
  | cons op r ih => intro s; rw [List.foldl_cons, List.foldl_cons, ih, optStep_newids]

/-- The keys of the GETs among `ops`. -/
def gkeys (ops : List GenOp) : List Int :=
  ops.filterMap fun op => match okind op with
    | .get k => some k
    | _ => none

theorem lookup_cons_int {β : Type} (k a : Int) (b : β) (l : List (Int × β)) :
    ((k, b) :: l).lookup a = if a = k then some b else l.lookup a := by
  rw [List.lookup_cons]
  by_cases h : a = k
  · subst h; simp
  · rw [show (a == k) = false from by simpa using h]
    simp [h]

theorem addNew_lookup (N : List (Int × Option Nat)) (k a : Int) :
    (addNew N k).lookup a = if a = k ∧ N.lookup a = none then some none else N.lookup a := by
  unfold addNew
  by_cases hk : (N.lookup k).isSome = true
  · rw [if_pos hk]
    by_cases ha : a = k
    · subst ha
      have : N.lookup a ≠ none := by intro e; rw [e] at hk; cases hk
      simp [this]
    · simp [ha]
  · rw [if_neg hk, lookup_cons_int]
    have hn : N.lookup k = none := by
      cases h : N.lookup k with
      | none => rfl
      | some v => rw [h] at hk; exact absurd rfl hk
    by_cases ha : a = k
    · subst ha; simp [hn]
    · simp [ha]

theorem newids_lookup :
    ∀ (ops : List GenOp) (N : List (Int × Option Nat)) (a : Int),
      (ops.foldl newidStep N).lookup a =
        if a ∈ gkeys ops ∧ N.lookup a = none then some none else N.lookup a := by
  intro ops
  induction ops with
  | nil => intro N a; simp [gkeys]
  | cons op r ih =>
    intro N a
    rw [List.foldl_cons, ih]
    unfold newidStep gkeys
    rw [List.filterMap_cons]
    cases hk : okind op with
    | get k =>
      dsimp only
      rw [addNew_lookup]
      by_cases ha : a = k
      · subst ha
        by_cases hn : N.lookup a = none
        · simp [hn]
        · simp [hn]
      · simp only [ha, false_and, if_false, List.mem_cons, false_or]
    | put k => rfl
    | memoize => rfl
    | frame => rfl
    | proto v => rfl
    | other => rfl

theorem getKeys_classify :
    ∀ (ops : List GenOp) (n : Nat), getKeys (classify n ops) = gkeys ops := by
  intro ops
  induction ops with
  | nil => intro n; rfl
  | cons op r ih =>
    intro n
    unfold classify gkeys
    rw [List.filterMap_cons]
    cases hk : okind op with
    | put k => simp only [getKeys]; exact ih _
    | memoize => simp only [getKeys]; exact ih _
    | frame => exact ih _
    | get k => simp only [getKeys]; rw [ih]; rfl
    | proto v => simp only [getKeys]; exact ih _
    | other => simp only [getKeys]; exact ih _

theorem gkeys_body (ops : List GenOp) : gkeys (bodyOps ops) = gkeys ops := by
  cases ops with
  | nil => rfl
  | cons op r =>
    rw [bodyOps_cons]
    cases hk : okind op with
    | proto v =>
      dsimp only
      unfold gkeys
      rw [List.filterMap_cons, hk]
    | put k => rfl
    | memoize => rfl
    | frame => rfl
    | get k => rfl
    | other => rfl

/-- No opcode is a `PROTO` at position 0. -/
def NoP0 (ops : List GenOp) : Prop := ∀ op ∈ ops, ∀ v, okind op = .proto v → op.pos.getD 0 ≠ 0

theorem addId_new (ids : List Int) (k : Int) (h : k ∉ ids) : addId ids k = k :: ids := by
  unfold addId
  rw [if_neg (by simpa using h)]

theorem nodup_shift (l r : List Int) (k : Int) (h : (l ++ k :: r).Nodup) : ((k :: l) ++ r).Nodup := by
  have hp : (l ++ k :: r).Perm (k :: (l ++ r)) := List.perm_middle
  exact hp.nodup_iff.mp h

theorem not_mem_of_nodup (l r : List Int) (k : Int) (h : (l ++ k :: r).Nodup) : k ∉ l := by
  intro hk
  have := (List.nodup_append.mp h).2.2 k hk k List.mem_cons_self
  exact this rfl

theorem fold_ops (p : Bytes) :
    ∀ (ops : List GenOp) (s : OptSt), NoP0 ops →
      (s.oldids ++ putKeys (classify s.oldids.length ops)).Nodup →
      (ops.foldl (optStep p) s).ops = (classify s.oldids.length ops).reverse ++ s.ops ∧
      (ops.foldl (optStep p) s).header = s.header := by
  intro ops
  induction ops with
  | nil => intro s _ _; simp [classify]
  | cons op r ih =>
    intro s hp hn
    have hr : NoP0 r := fun o ho => hp o (List.mem_cons_of_mem _ ho)
    rw [List.foldl_cons, optStep_eq]
    unfold classify at hn ⊢
    cases hk : okind op with
    | put k =>
      rw [hk] at hn
      dsimp only at hn ⊢
      simp only [putKeys] at hn
      have hnew := not_mem_of_nodup _ _ _ hn
      rw [addId_new _ _ hnew]
      have := ih { s with oldids := k :: s.oldids, ops := .put k :: s.ops } hr (by
        simpa using nodup_shift _ _ _ hn)
      simp only [List.length_cons] at this
      rw [this.1, this.2]
      simp
    | memoize =>
      rw [hk] at hn
      dsimp only at hn ⊢
      simp only [putKeys] at hn
      have hnew := not_mem_of_nodup _ _ _ hn
      rw [addId_new _ _ hnew]
      have := ih { s with oldids := (s.oldids.length : Int) :: s.oldids,
                          ops := .put (s.oldids.length : Int) :: s.ops } hr (by
        simpa using nodup_shift _ _ _ hn)
      simp only [List.length_cons] at this
      rw [this.1, this.2]
      simp
    | frame =>
      rw [hk] at hn
      dsimp only at hn ⊢
      exact ih s hr hn
    | get k =>
      rw [hk] at hn
      dsimp only at hn ⊢
      simp only [putKeys] at hn
      have := ih { s with proto := max s.proto op.info.proto, newids := addNew s.newids k,
                          ops := .get k :: s.ops } hr hn
      rw [this.1, this.2]
      simp
    | proto v =>
      rw [hk] at hn
      dsimp only at hn ⊢
      simp only [putKeys] at hn
      rw [if_neg (hp op List.mem_cons_self v hk)]
      have := ih { s with proto := max s.proto v,
                          ops := .raw (op.pos.getD 0) (op.endPos.getD 0) :: s.ops } hr hn
      rw [this.1, this.2]
      simp
    | other =>
      rw [hk] at hn
      dsimp only at hn ⊢
      simp only [putKeys] at hn
      have := ih { s with ops := .raw (op.pos.getD 0) (op.endPos.getD 0) :: s.ops } hr hn
      rw [this.1, this.2]
      simp

theorem chain_pos : ∀ (p : Nat) (ops : List GenOp) (e : Nat), OpsChain p ops e →
    ∀ o ∈ ops, ∃ q, o.pos = some q ∧ p ≤ q := by
  intro p ops
  induction ops generalizing p with
  | nil => intro e h; exact h.elim
  | cons op r ih =>
    intro e h o ho
    cases r with
    | nil =>
      obtain ⟨h1, _⟩ := h
      rcases List.mem_singleton.mp ho with rfl
      exact ⟨p, h1, Nat.le_refl _⟩
    | cons o' r' =>
      obtain ⟨m, h1, _, _, h4, h5⟩ := h
      rcases List.mem_cons.mp ho with e' | e'
      · subst e'; exact ⟨p, h1, Nat.le_refl _⟩
      · obtain ⟨q, hq, hle⟩ := ih m e h5 o e'
        exact ⟨q, hq, by omega⟩

theorem chain_tail (ops : List GenOp) (e : Nat) (h : OpsChain 0 ops e) :
    ∃ op0 rest, ops = op0 :: rest ∧ op0.pos = some 0 ∧ ∀ o ∈ rest, o.pos.getD 0 ≠ 0 := by
  cases ops with
  | nil => exact h.elim
  | cons op0 rest =>
    refine ⟨op0, rest, rfl, ?_, ?_⟩
    · cases rest with
      | nil => exact h.1
      | cons o r => obtain ⟨m, h1, _⟩ := h; exact h1
    · intro o ho
      cases rest with
      | nil => cases ho
      | cons o' r' =>
        obtain ⟨m, _, _, _, h4, h5⟩ := h
        obtain ⟨q, hq, hle⟩ := chain_pos m _ e h5 o ho
        rw [hq]
        simp only [Option.getD_some]
        omega

/-- What the first loop of `optimize` leaves. -/
theorem firstLoop (p : Bytes) (ops : List GenOp) (e : Nat) (hc : OpsChain 0 ops e)
    (hnd : (putKeys (optOps ops)).Nodup) :
    (ops.foldl (optStep p) {}).ops.reverse = optOps ops ∧
    (ops.foldl (optStep p) {}).header = headerOf p ops ∧
    (ops.foldl (optStep p) {}).proto = ops.foldl protoStep 0 ∧
    ∀ a, (ops.foldl (optStep p) {}).newids.lookup a =
      if a ∈ getKeys (optOps ops) then some none else none := by
  obtain ⟨op0, rest, rfl, h0, hrest⟩ := chain_tail ops e hc
  have hlk : ∀ a, ((op0 :: rest).foldl (optStep p) {}).newids.lookup a =
      if a ∈ getKeys (optOps (op0 :: rest)) then some none else none := by
    intro a
    rw [fold_newids, newids_lookup]
    unfold optOps
    rw [getKeys_classify, gkeys_body]
    simp
  have hpr := fold_proto p (op0 :: rest) {}
  refine ⟨?_, ?_, hpr, hlk⟩ <;>
  · cases hk : okind op0 with
    | proto v =>
      have hb : optOps (op0 :: rest) = classify 0 rest := by
        unfold optOps; rw [bodyOps_cons, hk]
      have hh : headerOf p (op0 :: rest) = slice p 0 (op0.endPos.getD 0) := by
        rw [headerOf_cons, hk]
      rw [hb] at hnd
      rw [List.foldl_cons, optStep_eq, hk]
      dsimp only
      rw [h0]
      simp only [Option.getD_some, if_true]
      have hr : NoP0 rest := fun o ho _ _ => hrest o ho
      have := fold_ops p rest { proto := max 0 v, header := slice p 0 (op0.endPos.getD 0) } hr
        (by simpa using hnd)
      simp only [List.length_nil] at this
      first
        | (rw [hb, this.1]; simp)
        | (rw [hh, this.2])
    | _ =>
      have hb : optOps (op0 :: rest) = classify 0 (op0 :: rest) := by
        unfold optOps; rw [bodyOps_cons, hk]
      have hh : headerOf p (op0 :: rest) = [] := by
        rw [headerOf_cons, hk]
      rw [hb] at hnd
      have hr : NoP0 (op0 :: rest) := by
        intro o ho v hv
        rcases List.mem_cons.mp ho with e' | e'
        · subst e'; rw [hk] at hv; cases hv
        · exact hrest o e'
      have := fold_ops p (op0 :: rest) {} hr (by simpa using hnd)
      simp only [List.length_nil] at this
      first
        | (rw [hb, this.1]; simp)
        | (rw [hh, this.2])

/-! ## The second loop -/

def evRes (r : Py OptOut) : Py (List Event) :=
  match r with
  | .ok o => .ok o.ev
  | .error e => .error e

def evSpec (r : Py (List Event)) (base : List Event) : Py (List Event) :=
  match r with
  | .ok evs => .ok (evs.reverse ++ base)
  | .error e => .error e

theorem evSpec_cons (r : Py (List Event)) (pre base : List Event) :
    evSpec (do let rest ← r; return pre ++ rest) base = evSpec r (pre.reverse ++ base) := by
  cases r with
  | error e => rfl
  | ok evs => simp [evSpec, bind, Except.bind, pure, Except.pure, List.reverse_append]

theorem putKeys_append (a b : List OptOp) : putKeys (a ++ b) = putKeys a ++ putKeys b := by
  induction a with
  | nil => rfl
  | cons o r ih => cases o <;> simp [putKeys, ih]

theorem getKeys_append (a b : List OptOp) : getKeys (a ++ b) = getKeys a ++ getKeys b := by
  induction a with
  | nil => rfl
  | cons o r ih => cases o <;> simp [getKeys, ih]

theorem gap_append :
    ∀ (done todo : List OptOp) (seen : List Int), GetsAfterPuts seen (done ++ todo) →
      GetsAfterPuts ((putKeys done).reverse ++ seen) todo := by
  intro done
  induction done with
  | nil => intro todo seen h; simpa [putKeys] using h
  | cons o r ih =>
    intro todo seen h
    cases o with
    | put k =>
      have := ih todo (k :: seen) h
      simpa [putKeys] using this
    | get k => exact ih todo seen h.2
    | raw a b => exact ih todo seen h

/-- The value `newids` holds for key `a` once the opcodes `done` are written. -/
def expLookup (used : Int → Bool) (kept : List Int) (done : List OptOp) (a : Int) :
    Option (Option Nat) :=
  if a ∈ putKeys done ∧ used a = true then some (some (kept.idxOf a))
  else if used a = true then some none else none

theorem secondLoop (proto : Nat) (p : Bytes) (c : List OptOp) (hnd : (putKeys c).Nodup) :
    ∀ (todo done : List OptOp) (st : OptOut), c = done ++ todo →
      GetsAfterPuts (putKeys done).reverse todo →
      st.idx = ((putKeys done).filter (fun k => (getKeys c).contains k)).length →
      (∀ a, st.newids.lookup a =
        expLookup (fun k => (getKeys c).contains k)
          ((putKeys c).filter (fun k => (getKeys c).contains k)) done a) →
      evRes (todo.foldlM (optEmit proto p) st) =
        evSpec (emitSpec proto p (fun k => (getKeys c).contains k)
          ((putKeys c).filter (fun k => (getKeys c).contains k)) todo) st.ev := by
  generalize hU : (fun k => (getKeys c).contains k) = used
  have hused : ∀ k, used k = true ↔ k ∈ getKeys c := by
    intro k; rw [← hU]; simp
  generalize hK : (putKeys c).filter used = kept
  intro todo
  induction todo with
  | nil => intro done st _ _ _ _; rfl
  | cons o r ih =>
    intro done st hc hg hidx hlk
    rw [List.foldlM_cons]
    cases o with
    | put k =>
      have hc' : c = (done ++ [.put k]) ++ r := by simp [hc]
      have hpk : putKeys c = putKeys done ++ k :: putKeys r := by
        rw [hc, putKeys_append]; rfl
      have hnot : k ∉ putKeys done := by
        rw [hpk] at hnd; exact not_mem_of_nodup _ _ _ hnd
      have hg2 : GetsAfterPuts (k :: (putKeys done).reverse) r := hg
      have hg' : GetsAfterPuts (putKeys (done ++ [.put k])).reverse r := by
        rw [putKeys_append]; simpa [putKeys] using hg2
      have hmem : ∀ a, a ∈ putKeys (done ++ [.put k]) ↔ a ∈ putKeys done ∨ a = k := by
        intro a; rw [putKeys_append]; simp [putKeys]
      have hk := hlk k
      unfold expLookup at hk
      simp only [hnot, false_and, if_false] at hk
      by_cases hu : used k = true
      · rw [if_pos hu] at hk
        have hidx' : st.idx = kept.idxOf k := by
          rw [← hK, hpk, List.filter_append, List.filter_cons, if_pos hu, List.idxOf_append,
            if_neg (fun hm => hnot (List.mem_filter.mp hm).1), List.idxOf_cons_self, hidx]
          simp
        simp only [optEmit, hk, Option.isNone_some, Bool.false_eq_true, if_false]
        unfold emitSpec
        rw [if_pos hu, ← hidx']
        cases hput : pyPut proto st.idx with
        | error e => rfl
        | ok d =>
          simp only [bind, Except.bind]
          rw [ih (done ++ [.put k]) _ hc' hg']
          · cases emitSpec proto p used kept r with
            | error e => rfl
            | ok evs => simp [evSpec, optWrite, pure, Except.pure, List.reverse_append]
          · simp [optWrite, putKeys_append, putKeys, List.filter_append, hu, hidx]
          · intro a
            simp only [optWrite, lookup_cons_int]
            unfold expLookup
            by_cases ha : a = k
            · subst ha
              simp [hmem, hu, hidx']
            · rw [if_neg ha, hlk a]
              unfold expLookup
              simp [hmem, ha]
      · rw [if_neg hu] at hk
        simp only [optEmit, hk, Option.isNone_none, if_true, bind, Except.bind]
        unfold emitSpec
        rw [if_neg hu]
        rw [ih (done ++ [.put k]) st hc' hg']
        · simp [putKeys_append, putKeys, List.filter_append, hu, hidx]
        · intro a
          rw [hlk a]
          unfold expLookup
          by_cases ha : a = k
          · subst ha; simp [hu]
          · simp [hmem, ha]
    | get k =>
      have hc' : c = (done ++ [.get k]) ++ r := by simp [hc]
      have hg2 : k ∈ (putKeys done).reverse ∧ GetsAfterPuts (putKeys done).reverse r := hg
      have hin : k ∈ putKeys done := by simpa using hg2.1
      have hu : used k = true := by
        rw [hused, hc, getKeys_append]; simp [getKeys]
      have hk := hlk k
      unfold expLookup at hk
      rw [if_pos ⟨hin, hu⟩] at hk
      have hpk : putKeys (done ++ [.get k]) = putKeys done := by
        rw [putKeys_append]; simp [putKeys]
      have hg' : GetsAfterPuts (putKeys (done ++ [.get k])).reverse r := by
        rw [hpk]; exact hg2.2
      simp only [optEmit, hk, Option.join_some, optGet]
      unfold emitSpec
      cases hget : pyGet proto (kept.idxOf k) with
      | error e => rfl
      | ok d =>
        simp only [bind, Except.bind]
        rw [ih (done ++ [.get k]) _ hc' hg']
        · cases emitSpec proto p used kept r with
          | error e => rfl
          | ok evs => simp [evSpec, optWrite, pure, Except.pure, List.reverse_append]
        · simp only [optWrite]; rw [hpk]; exact hidx
        · intro a
          simp only [optWrite]
          rw [hlk a]
          unfold expLookup
          rw [hpk]
    | raw a b =>
      have hc' : c = (done ++ [.raw a b]) ++ r := by simp [hc]
      have hpk : putKeys (done ++ [.raw a b]) = putKeys done := by
        rw [putKeys_append]; simp [putKeys]
      have hg2 : GetsAfterPuts (putKeys done).reverse r := hg
      have hg' : GetsAfterPuts (putKeys (done ++ [.raw a b])).reverse r := by
        rw [hpk]; exact hg2
      have hlk' : ∀ x, st.newids.lookup x = expLookup used kept (done ++ [.raw a b]) x := by
        intro x
        rw [hlk x]
        unfold expLookup
        rw [hpk]
      unfold emitSpec
      simp only [optEmit]
      by_cases hl : (slice p a b).length > frameSizeTarget
      · have hl' : ((p.drop a).take (b - a)).length > frameSizeTarget := hl
        rw [if_pos hl']
        simp only [bind, Except.bind]
        rw [ih (done ++ [.raw a b]) _ hc' hg' (by rw [hpk]; exact hidx) hlk']
        cases emitSpec proto p used kept r with
        | error e => rfl
        | ok evs =>
          rw [if_pos hl]
          simp [evSpec, pure, Except.pure, slice]
      · have hl' : ¬ ((p.drop a).take (b - a)).length > frameSizeTarget := hl
        rw [if_neg hl']
        simp only [bind, Except.bind]
        rw [ih (done ++ [.raw a b]) _ hc' hg' (by simp only [optWrite]; rw [hpk]; exact hidx) hlk']
        cases emitSpec proto p used kept r with
        | error e => rfl
        | ok evs =>
          rw [if_neg hl]
          simp [evSpec, pure, Except.pure, slice, optWrite]

theorem optimizeExact_proven : OptimizeExact := by
  intro p ops hg ⟨hnd, hgap⟩
  obtain ⟨e, hc, _⟩ := genopsWellFormed_proven p ops hg
  obtain ⟨h1, h2, h3, h4⟩ := firstLoop p ops e hc hnd
  generalize hs : ops.foldl (optStep p) {} = s at h1 h2 h3 h4
  unfold optimize optimizeSpec
  simp only [bind, Except.bind, hg, hs, h3]
  cases hpr : pyProtocol (ops.foldl protoStep 0) with
  | error x => rfl
  | ok pr =>
    dsimp only
    have hl := secondLoop pr p (optOps ops) hnd (optOps ops) [] { newids := s.newids }
      (by simp) (by simpa [putKeys] using hgap) (by simp [putKeys]) (by
        intro a
        rw [h4 a]
        unfold expLookup
        simp [putKeys])
    rw [h1] at *
    generalize hfo : (optOps ops).foldlM (optEmit pr p) ({ newids := s.newids } : OptOut) = fo at hl
    generalize hes : emitSpec pr p (fun k => (getKeys (optOps ops)).contains k)
      ((putKeys (optOps ops)).filter (fun k => (getKeys (optOps ops)).contains k)) (optOps ops) = es at hl
    cases fo with
    | error x =>
      cases es with
      | error y => simp only [evRes, evSpec] at hl; injection hl with hl; rw [hl]
      | ok evs => simp [evRes, evSpec] at hl
    | ok out =>
      cases es with
      | error y => simp [evRes, evSpec] at hl
      | ok evs =>
        simp only [evRes, evSpec] at hl
        injection hl with hl
        simp only [List.append_nil] at hl
        simp only [pure, Except.pure]
        rw [hl, h2, List.reverse_reverse]

/-- A GET of a key no PUT stored, outside `MemoWF`: `newids[arg]` stays `None`, so
`pickler.get(None)` raises `TypeError` from `None < 256` at protocol 1 and up
(`Lib/pickle.py:555`), and at protocol 0 writes `repr(None)` as the key
(`b'gNone\n'`). Probed on 3.15.2: `optimize(b'\x80\x02h\x00.')` and
`optimize(b'g0\n.')`. -/
def OptimizeGetNone : Prop :=
  optimize [0x80, 0x02, 0x68, 0x00, 0x2e] =
    .error (.typeError "'<' not supported between instances of 'NoneType' and 'int'") ∧
  optimize [0x67, 0x30, 0x0a, 0x2e] = .ok [0x67, 0x4e, 0x6f, 0x6e, 0x65, 0x0a, 0x2e]

theorem optimizeGetNone_proven : OptimizeGetNone := by
  constructor <;> decide +kernel

end PyLean.Pickle
