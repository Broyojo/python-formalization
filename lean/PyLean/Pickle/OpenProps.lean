import PyLean.Pickle.EncFrame
import PyLean.Pickle.DecProps

/-!
Statements of the properties that stay open, with the definitions they need.
-/

namespace PyLean.Pickle

open PyLean

mutual
/-- The plain value as `dvJson` shows the decoded object. -/
def pvJson : PV → Lean.Json
  | .none => mk "none" Lean.Json.null
  | .bool b => mk "bool" (Lean.toJson b)
  | .int i => mk "int" (Lean.toJson (hexInt i))
  | .str _ s => mk "str" (Lean.toJson s)
  | .bytes _ b => mk "bytes" (bytesJson b)
  | .bytearray _ b => mk "bytearray" (bytesJson b)
  | .tuple _ xs => mk "tuple" (Lean.Json.arr (pvJsonList xs).toArray)
  | .list _ xs => mk "list" (Lean.Json.arr (pvJsonList xs).toArray)
  | .set _ xs => mk "set" (Lean.Json.arr (sortJson (pvJsonList xs)).toArray)
  | .frozenset _ xs => mk "frozenset" (Lean.Json.arr (sortJson (pvJsonList xs)).toArray)
  | .dict _ kvs => mk "dict" (Lean.Json.arr (pvJsonPairs kvs).toArray)
def pvJsonList : List PV → List Lean.Json
  | [] => []
  | x :: xs => pvJson x :: pvJsonList xs
def pvJsonPairs : List (PV × PV) → List Lean.Json
  | [] => []
  | (k, v) :: kvs => Lean.Json.arr #[pvJson k, pvJson v] :: pvJsonPairs kvs
end

mutual
/-- The hashable part of plain values as decoded values, `none` for lists,
dicts, sets and bytearrays. -/
def hashDV : PV → Option DV
  | .none => some .none
  | .bool b => some (.bool b)
  | .int i => some (.int i)
  | .str _ s => some (.str s)
  | .bytes _ b => some (.bytes b)
  | .tuple _ xs => (.tuple ·) <$> hashDVList xs
  | .frozenset _ xs => (.frozenset ·) <$> hashDVList xs
  | _ => none
def hashDVList : List PV → Option (List DV)
  | [] => some []
  | x :: xs => do return (← hashDV x) :: (← hashDVList xs)
end

/-- Pairwise different as Python values, all hashable: dict keys and set
elements. -/
def DistinctKeys (xs : List PV) : Prop :=
  ∃ ds, hashDVList xs = some ds ∧ ds.Pairwise (fun a b => pyEq a b = false)

mutual
/-- All nodes of `x`, itself first. -/
def nodes : PV → List PV
  | .tuple o xs => .tuple o xs :: nodesList xs
  | .list o xs => .list o xs :: nodesList xs
  | .set o xs => .set o xs :: nodesList xs
  | .frozenset o xs => .frozenset o xs :: nodesList xs
  | .dict o kvs => .dict o kvs :: nodesPairs kvs
  | x => [x]
def nodesList : List PV → List PV
  | [] => []
  | x :: xs => nodes x ++ nodesList xs
def nodesPairs : List (PV × PV) → List PV
  | [] => []
  | (k, v) :: kvs => nodes k ++ nodes v ++ nodesPairs kvs
end

def oidOf : PV → Option Oid
  | .str o _ | .bytes o _ | .bytearray o _ | .tuple o _ | .list o _ | .dict o _ | .set o _
  | .frozenset o _ => some o
  | _ => none

/-- User object ids only: the picklers' own `tmp`, `glob` and `latin1` ids do
not label user objects, and a cached character carries its own value. -/
def UserOid : PV → Prop
  | .str (.u _) _ | .bytes (.u _) _ | .bytearray (.u _) _ | .tuple (.u _) _ | .list (.u _) _
  | .dict (.u _) _ | .set (.u _) _ | .frozenset (.u _) _ => True
  | .str (.str1 c) s => s = [c] ∧ c < 256
  | .bytes (.bytes1 b) s => s.map (·.toNat) = [b]
  | .none | .bool _ | .int _ => True
  | _ => False

/-- The type invariants of a plain value. -/
def WellFormed (x : PV) : Prop :=
  (∀ a ∈ nodes x, ∀ b ∈ nodes x, oidOf a = oidOf b → oidOf a ≠ none → a = b) ∧
  (∀ a ∈ nodes x, UserOid a) ∧
  (∀ o kvs, .dict o kvs ∈ nodes x → DistinctKeys (kvs.map (·.1))) ∧
  (∀ o xs, .set o xs ∈ nodes x → DistinctKeys xs) ∧
  (∀ o xs, .frozenset o xs ∈ nodes x → DistinctKeys xs) ∧
  (∀ o s, .str o s ∈ nodes x → ∀ c ∈ s, c < 0x110000)

/-- `loads(dumps(x, p)) == x` for both encoders, both decoders, every protocol. -/
def RoundTrip : Prop :=
  ∀ (x : PV) (p : Nat) (b : Bytes), p ≤ 5 → WellFormed x →
    (cDumps x p = .ok b ∨ pyDumps x p = .ok b) →
    resolved (cLoads b) = .ok (pvJson x) ∧ resolved (pyLoads b) = .ok (pvJson x)

mutual
/-- `x` needs no length field beyond 4 bytes before protocol 4. -/
def SizeOk (p : Nat) : PV → Prop
  | .str _ s => p < 4 → (utf8Enc s).length ≤ 0xffffffff
  | .bytes _ b | .bytearray _ b => p < 4 → (utf8Enc (b.map (·.toNat))).length ≤ 0xffffffff
  | .tuple _ xs | .list _ xs | .set _ xs | .frozenset _ xs => SizeOkList p xs
  | .dict _ kvs => SizeOkPairs p kvs
  | _ => True
def SizeOkList (p : Nat) : List PV → Prop
  | [] => True
  | x :: xs => SizeOk p x ∧ SizeOkList p xs
def SizeOkPairs (p : Nat) : List (PV × PV) → Prop
  | [] => True
  | (k, v) :: kvs => SizeOk p k ∧ SizeOk p v ∧ SizeOkPairs p kvs
end

/-- Exact agreement, exception included, below the sizes where the twins raise
different classes. A bound on the node count keeps memo indices below 2**32
(each node memoizes at most a few objects). -/
def DumpsTwinsExactSized : Prop :=
  ∀ (x : PV) (protocol : Int), longMin ≤ protocol → protocol ≤ longMax →
    BatchOk (effProto protocol) x → IntsOk x → SizeOk (effProto protocol) x →
    (nodes x).length * 16 + 64 < 2 ^ 32 →
    cDumps x protocol = pyDumps x protocol

end PyLean.Pickle
