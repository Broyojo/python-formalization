import PyLean.CoreLibs.Misc.Weakref.Deepcopy
import PyLean.CoreLibs.Misc.Weakref.PropsWvd

/-!
`__deepcopy__` of the two dictionaries. `copy.deepcopy` keeps the shape of the object graph: an
object reached twice is copied once, and a reference to an object that is being copied points at its
copy (Lib/copy.py docstring: "Python's deep copy operation avoids these problems by ... keeping a
memo dictionary of objects already copied during the current copying pass"). Both `__deepcopy__`
methods build `new` without recording it in `memo`, so a key or value that refers back to the
dictionary meets a second copy of it.
-/

namespace PyLean.CoreLibs.Misc.Weakref

open PyLean

/-- `deepcopy` keeps references consistent with `memo`: after a deep copy from an empty memo, every
instance `b` that was copied has, as its attribute, the copy of the original attribute. -/
def DeepcopyKeepsSharing : Prop :=
  ∀ (ops : KOps Nat) (q : ROps) (w : World) (s : DS) (x f : Nat) (s' : DS) (y : Nat),
    s.memo = [] → deep ops q w f s x = .ok (s', y) →
    ∀ b fld, s.get b = some (.box fld) → (dGet s'.memo b).isSome →
      s'.get (img s'.memo b) = some (.box (img s'.memo fld))

/-- Keys compared by identity, hashed by id. -/
def idOps : KOps Nat := ⟨fun k => .ok k, fun _ _ => .ok false, fun _ => "B"⟩

def idQ : ROps := ⟨fun k => .ok k, fun a b => .ok (a == b)⟩

/-- `d = WeakValueDictionary(); k = B(d); d[k] = v; deepcopy(d)`: object 0 is `d`, 1 the key whose
attribute is `d`, 2 the value. -/
def wvdSelfRef : DS :=
  { heap := [(0, .wvd { data := [(1, 1, ⟨2, true, 1⟩)], eager := true }), (1, .box 0), (2, .atom)],
    next := 3, memo := [] }

/-- `d = WeakKeyDictionary(); d[k] = B(d); deepcopy(d)`: object 0 is `d`, 1 the key, 2 the value
whose attribute is `d`. -/
def wkdSelfRef : DS :=
  { heap := [(0, .wkd { data := [(⟨0, 1, 1, true⟩, 2)], eager := true, nextRid := 1 }), (1, .atom),
      (2, .box 0)], next := 3, memo := [] }

/-- Refuted by `WeakValueDictionary.__deepcopy__`: the copied key's attribute is a second copy of
the dictionary (object 5), not the copy that `deepcopy` returns (object 3). -/
theorem deepcopyKeepsSharing_wvd_refuted : ¬ DeepcopyKeepsSharing := by
  intro h
  have hr : deep idOps idQ [] 10 wvdSelfRef 0 = .ok (_, 3) := rfl
  have := h idOps idQ [] wvdSelfRef 0 10 _ 3 rfl hr 1 0 rfl rfl
  revert this
  decide

/-- Refuted by `WeakKeyDictionary.__deepcopy__` in the same way, through a value. -/
theorem deepcopyKeepsSharing_wkd_refuted : ¬ DeepcopyKeepsSharing := by
  intro h
  have hr : deep idOps idQ [] 10 wkdSelfRef 0 = .ok (_, 3) := rfl
  have := h idOps idQ [] wkdSelfRef 0 10 _ 3 rfl hr 2 0 rfl rfl
  revert this
  decide

/-- The deep copy loops otherwise: `self.__class__()` raising ends `__deepcopy__` with its
exception; an exception from deep-copying a key (or a value) ends it too; with keys that copy as
themselves `WeakValueDictionary.__deepcopy__` gives the items of `copy()`, and with values that copy
as themselves `WeakKeyDictionary.__deepcopy__` gives those of its `copy()`. -/
def DeepcopyLoops : Prop :=
  ∀ (K M V : Type) [DecidableEq K] (ops : KOps K) (q : ROps) (w : World) (d : WVD K) (e : WKD V)
    (m : M) (err : PyExc),
    WVD.deepcopy ops (fun m k => .ok (m, k)) (.error err) w d m = .error err ∧
    WKD.deepcopy q (fun m v => .ok (m, v)) (.error err) w e m = .error err ∧
    (∀ k o rest, WVD.liveItems w d = (k, o) :: rest →
      WVD.deepcopy ops (fun (_ : M) _ => .error err) (.ok WVD.empty) w d m = .error err) ∧
    (∀ k v rest, WKD.liveItems w e = (k, v) :: rest →
      WKD.deepcopy q (fun (_ : M) _ => .error err) (.ok WKD.empty) w e m = .error err) ∧
    (WVD.deepcopy ops (fun m k => .ok (m, k)) (.ok WVD.empty) w d m).map (·.2) = WVD.copy ops w d ∧
    (WKD.deepcopy q (fun m v => .ok (m, v)) (.ok WKD.empty) w e m).map (·.2) = WKD.copy q w e

theorem deepcopyLoops_proven : DeepcopyLoops := by
  intro K M V _ ops q w d e m err
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro k o rest h
    simp [WVD.deepcopy, h, WVD.dcLoop]
  · intro k v rest h
    simp [WKD.deepcopy, h, WKD.dcLoop]
  · simp only [WVD.deepcopy, WVD.copy]
    generalize WVD.liveItems w d = l
    generalize (WVD.empty : WVD K) = n
    induction l generalizing n with
    | nil => rfl
    | cons p rest ih =>
      obtain ⟨k, o⟩ := p
      simp only [WVD.dcLoop, WVD.setAll]
      cases WVD.setitem ops n k o with
      | error _ => rfl
      | ok n' => exact ih n'
  · simp only [WKD.deepcopy, WKD.copy]
    generalize WKD.liveItems w e = l
    generalize (WKD.empty : WKD V) = n
    induction l generalizing n with
    | nil => rfl
    | cons p rest ih =>
      obtain ⟨k, v⟩ := p
      simp only [WKD.dcLoop, WKD.setAll]
      cases WKD.setitem q w n k v with
      | error _ => rfl
      | ok n' => exact ih n'

end PyLean.CoreLibs.Misc.Weakref
