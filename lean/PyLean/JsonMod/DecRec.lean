import PyLean.JsonMod.DecFuel

/-!
Recursion limits in the two decoders of CPython 3.15.2.

**C.** `scan_once_unicode` calls `_Py_EnterRecursiveCall` before `_parse_object_unicode`
(Modules/_json.c:1132-1137) and `_parse_array_unicode` (:1140-1145). In 3.15 that check is
stack based (`_Py_MakeRecCheck`, Include/internal/pycore_ceval.h:211-236): it fails when the
machine stack pointer passes the soft limit, and `_Py_CheckRecursiveCall` (Python/ceval.c:298-336)
raises `RecursionError("Stack overflow (used %d kB)%s")` with the `where` string. The stack room
is abstracted as the number `c` of nested arrays and objects it holds (a parameter: it depends
on the platform, the thread's stack size and what is already on the stack).
`sys.getrecursionlimit()` plays no part.

**Python.** Each Python call pushes a frame, and `_Py_CheckRecursiveCallPy` (Python/ceval.c:1026-1045)
raises `RecursionError("maximum recursion depth exceeded")` when none is left. The frames of
the pure-Python decoder are `scan_once` and `_scan_once` (Lib/json/scanner.py:29-71), `JSONObject`,
`JSONArray`, `py_scanstring` and `_decode_uXXXX` (Lib/json/decoder.py). `p` is the number of
frames left when `raw_decode` calls `self.scan_once` (decoder.py:374): the recursion limit minus
the depth of the caller. The callbacks are the abstract functions of `DCfg`; that they run with
the same outcome at every depth is a scope limit (a Python hook near the limit could raise
`RecursionError` itself).

**The error's frame.** Raising `JSONDecodeError(msg, doc, pos)` runs `JSONDecodeError.__init__`
(Lib/json/decoder.py:31-41), a Python frame, so it needs one frame left where it is raised
(`chargeJde`); at none, `RecursionError('maximum recursion depth exceeded')` is raised instead.
C: `raise_errmsg` calls the class with `PyObject_CallFunction(JSONDecodeError, "zOn", ...)`
(Modules/_json.c:432), and `raw_decode` turns C's `StopIteration` into `JSONDecodeError('Expecting
value')` in its own frame (decoder.py:374-377); the C scanner takes no Python frame, so both happen
with the `p` frames left at the `scan_once` call. Python: `JSONObject`, `JSONArray`, `py_scanstring`
and `_decode_uXXXX` raise in their own frames, with what is left after them.

`cScanOnceR` and the rest are `cScanOnce` and the rest (DecC.lean, DecPy.lean) with these checks;
the unbounded models are what they compute when the checks pass (`bridgeC`, `bridgePy`).
-/

namespace PyLean.JsonMod

open PyLean

/-- `RecursionError` of `_Py_CheckRecursiveCall` in `scan_once_unicode`; the stack use in kB
is not modelled. -/
def recC (what : String) : DErr :=
  .exc (.named "RecursionError" s!"~Stack overflow (used N kB) while decoding a JSON {what} from a unicode string")

/-- `RecursionError` of `_Py_CheckRecursiveCallPy`. -/
def recPy : DErr := .exc (.named "RecursionError" "maximum recursion depth exceeded")

/-- A `JSONDecodeError` raised where `b` frames are left: its `__init__` needs one. -/
def chargeJde {α : Type} (b : Nat) (r : DR α) : DR α :=
  match b, r with
  | 0, .error (.jde _ _) => .error recPy
  | _, r => r

theorem chargeJde_succ {α : Type} (b : Nat) (r : DR α) : chargeJde (b + 1) r = r := by
  cases r <;> rfl

@[simp] theorem chargeJde_ok {α : Type} (b : Nat) (a : α) : chargeJde b (.ok a : DR α) = .ok a := by
  cases b <;> rfl

@[simp] theorem chargeJde_exc {α : Type} (b : Nat) (e : PyExc) :
    chargeJde b (.error (.exc e) : DR α) = .error (.exc e) := by
  cases b <;> rfl

@[simp] theorem chargeJde_stop {α : Type} (b : Nat) (i : Int) :
    chargeJde b (.error (.stop i) : DR α) = .error (.stop i) := by
  cases b <;> rfl

@[simp] theorem chargeJde_zero_jde {α : Type} (m : String) (i : Int) :
    chargeJde 0 (.error (.jde m i) : DR α) = .error recPy := rfl

theorem chargeJde_cases {α : Type} (b : Nat) (r : DR α) :
    chargeJde b r = r ∨ (b = 0 ∧ chargeJde b r = .error recPy) := by
  cases b with
  | succ b => exact Or.inl (chargeJde_succ b r)
  | zero =>
    cases r with
    | ok a => exact Or.inl rfl
    | error e => cases e <;> first | exact Or.inl rfl | exact Or.inr ⟨rfl, rfl⟩

/-! ### C -/

/-- `if (_Py_EnterRecursiveCall(where)) return NULL;` with room `b`: the body `k` runs with
one level less. -/
def cEnter {α : Type} (b : Nat) (what : String) (k : Nat → DR α) : DR α :=
  match b with
  | 0 => .error (recC what)
  | b + 1 => k b

mutual
/-- `scan_once_unicode`, :1099-1205, with `b` nested arrays or objects of stack room. -/
def cScanOnceR (cfg : DCfg) (s : PStr) : Nat → Nat → Nat → DR (JVal × Nat)
  | _, 0, _ => fuelOut
  | b, n + 1, idx =>
    if idx ≥ s.length then .error (.stop idx)
    else
      let c := s.getD idx 0
      if c = 34 then
        match cScanstring s (idx + 1) cfg.strict with
        | .ok (v, e) => .ok (.str v, e)
        | .error err => .error err
      else if c = 123 then
        -- `_Py_EnterRecursiveCall`, :1132-1134
        cEnter b "object" fun b =>
          let idx := wsEnd s (idx + 1)
          if idx ≥ s.length ∨ s.getD idx 0 ≠ 125 then
            if idx ≥ s.length ∨ s.getD idx 0 ≠ 34 then
              .error (.jde "Expecting property name enclosed in double quotes" idx)
            else cObjBodyR cfg s b n idx []
          else (cFinish cfg []).map (·, idx + 1)
      else if c = 91 then
        -- `_Py_EnterRecursiveCall`, :1140-1142
        cEnter b "array" fun b =>
          let idx := wsEnd s (idx + 1)
          if idx ≥ s.length ∨ s.getD idx 0 ≠ 93 then cArrLoopR cfg s b n idx []
          else (mkArr cfg []).map (·, idx + 1)
      else if c = 110 ∧ litAt s idx "null" then .ok (.null, idx + 4)
      else if c = 116 ∧ litAt s idx "true" then .ok (.bool true, idx + 4)
      else if c = 102 ∧ litAt s idx "false" then .ok (.bool false, idx + 5)
      else if c = 78 ∧ litAt s idx "NaN" then cConst cfg "NaN" idx
      else if c = 73 ∧ litAt s idx "Infinity" then cConst cfg "Infinity" idx
      else if c = 45 ∧ litAt s idx "-Infinity" then cConst cfg "-Infinity" idx
      else cMatchNumber cfg s idx

/-- `cArrLoop` with stack room `b`. -/
def cArrLoopR (cfg : DCfg) (s : PStr) : Nat → Nat → Nat → List JVal → DR (JVal × Nat)
  | _, 0, _, _ => fuelOut
  | b, n + 1, idx, acc =>
    match cScanOnceR cfg s b n idx with
    | .error err => .error err
    | .ok (v, next) =>
      match cArrAfter s next with
      | .close i => (mkArr cfg (acc ++ [v])).map (·, i.toNat)
      | .err err => .error err
      | .next i => cArrLoopR cfg s b n i.toNat (acc ++ [v])

/-- `cObjBody` with stack room `b`. -/
def cObjBodyR (cfg : DCfg) (s : PStr) : Nat → Nat → Nat → List (PStr × JVal) → DR (JVal × Nat)
  | _, 0, _, _ => fuelOut
  | b, n + 1, idx, acc =>
    match cScanstring s (idx + 1) cfg.strict with
    | .error err => .error err
    | .ok (key, next) =>
      let idx := wsEnd s next
      if idx ≥ s.length ∨ s.getD idx 0 ≠ 58 then .error (.jde "Expecting ':' delimiter" idx)
      else
        let idx := wsEnd s (idx + 1)
        match cScanOnceR cfg s b n idx with
        | .error err => .error err
        | .ok (v, next) =>
          let acc := cAddPair cfg acc key v
          match cObjAfter s next with
          | .close i => (cFinish cfg acc).map (·, i.toNat)
          | .err err => .error err
          | .next i =>
            if i.toNat ≥ s.length ∨ s.getD i.toNat 0 ≠ 34 then
              .error (.jde "Expecting property name enclosed in double quotes" i.toNat)
            else cObjBodyR cfg s b n i.toNat acc
end

/-- `raw_decode` with the C scanner, stack room `c` and `p` Python frames left at the `scan_once`
call: every `JSONDecodeError` of the scan (`raise_errmsg`, :422-440) and the `'Expecting value'`
that `raw_decode` makes of its `StopIteration` need one of them. -/
def rawDecodeCR (cfg : DCfg) (c p : Nat) (s : PStr) (idx : Int) : DR (JVal × Int) :=
  if idx < ssizeMin ∨ idx > ssizeMax then
    .error (.exc (.overflowError "Python int too large to convert to C ssize_t"))
  else if idx < 0 then .error (.exc (.valueError "idx cannot be negative"))
  else
    match chargeJde p (stopToJde (cScanOnceR cfg s c (docFuel s) idx.toNat)) with
    | .ok (v, e) => .ok (v, (e : Int))
    | .error err => .error err

/-- `json.loads(s)` with the C scanner, stack room `c` and `p` frames left at the `scan_once` call
(`'Extra data'` is raised in `decode`'s frame, one further out). -/
def loadsCR (cfg : DCfg) (c p : Nat) (s : PStr) : DR JVal := decodeWith (rawDecodeCR cfg c p) s

/-! ### Python -/

/-- A Python call with `b` frames left: `RecursionError` when there is none, otherwise the
callee runs with one frame less. -/
def pyCall {α : Type} (b : Nat) (k : Nat → DR α) : DR α :=
  match b with
  | 0 => .error recPy
  | b + 1 => k b

/-- `pyScanLoop` with `b` frames left: each `_decode_uXXXX` call needs one. -/
def pyScanLoopR (s : PStr) (strict : Bool) (begin : Int) (b : Nat) : Nat → Nat → PStr → DR (PStr × Int)
  | 0, _, _ => fuelOut
  | f + 1, e, acc =>
    match findTerm (s.drop e) with
    | none => .error (.jde "Unterminated string starting at" begin)
    | some k =>
      let term := s.getD (e + k) 0
      let acc := acc ++ (s.drop e).take k
      let e := e + k + 1
      if term = 34 then .ok (acc, (e : Int))
      else if term ≠ 92 then
        if strict then .error (.jde (ctrlMsgPy term) ((e : Int) - 1))
        else pyScanLoopR s strict begin b f e (acc ++ [term])
      else
        match s[e]? with
        | none => .error (.jde "Unterminated string starting at" begin)
        | some esc =>
          if esc ≠ 117 then
            match backslash esc with
            | none => .error (.jde (escMsgPy esc) e)
            | some ch => pyScanLoopR s strict begin b f (e + 1) (acc ++ [ch])
          else
            match pyCall b (fun b => chargeJde b (decodeUXXXX s e)) with
            | .error err => .error err
            | .ok uni =>
              let e := e + 5
              if 0xd800 ≤ uni ∧ uni ≤ 0xdbff ∧ (s.drop e).take 2 = [92, 117] then
                match pyCall b (fun b => chargeJde b (decodeUXXXX s (e + 1))) with
                | .error err => .error err
                | .ok uni2 =>
                  if 0xdc00 ≤ uni2 ∧ uni2 ≤ 0xdfff then
                    pyScanLoopR s strict begin b f (e + 6) (acc ++ [joinSurrogates uni uni2])
                  else pyScanLoopR s strict begin b f e (acc ++ [uni])
              else pyScanLoopR s strict begin b f e (acc ++ [uni])

/-- `py_scanstring` with `b` frames left after its own; its errors are raised in its frame. -/
def pyScanstringR (s : PStr) (e : Int) (strict : Bool) (b : Nat) : DR (PStr × Int) :=
  chargeJde b (pyScanLoopR s strict (e - 1) b (s.length + 1) (clampPos s e) [])

mutual
/-- `_scan_once` with `b` frames left after its own: `parse_string`, `parse_object` and
`parse_array` are calls. -/
def pyScanOnceR (cfg : DCfg) (s : PStr) : Nat → Nat → Int → DR (JVal × Int)
  | _, 0, _ => fuelOut
  | b, n + 1, idx =>
    match pyIndex s idx with
    | none => .error (.stop idx)
    | some c =>
      if c = 34 then
        pyCall b fun b =>
          match pyScanstringR s (idx + 1) cfg.strict b with
          | .ok (v, e) => .ok (.str v, e)
          | .error err => .error err
      else if c = 123 then
        -- `JSONObject`, raising in its frame
        pyCall b fun b => chargeJde b <|
          let e := idx + 1
          let nc := pySlice s e (e + 1)
          if nc ≠ [34] then
            let (e, nc) : Int × PStr :=
              if inWsSlice nc then (wsEndPy s e, pySlice s (wsEndPy s e) (wsEndPy s e + 1)) else (e, nc)
            if nc = [125] then (pyMkObj cfg []).map (·, e + 1)
            else if nc ≠ [34] then .error (.jde "Expecting property name enclosed in double quotes" e)
            else pyObjLoopR cfg s b n (e + 1) []
          else pyObjLoopR cfg s b n (e + 1) []
      else if c = 91 then
        -- `JSONArray`, raising in its frame
        pyCall b fun b => chargeJde b <|
          let e := idx + 1
          let nc := pySlice s e (e + 1)
          let (e, nc) : Int × PStr :=
            if inWsSlice nc then (wsEndPy s (e + 1), pySlice s (wsEndPy s (e + 1)) (wsEndPy s (e + 1) + 1))
            else (e, nc)
          if nc = [93] then (mkArr cfg []).map (·, e + 1)
          else pyArrLoopR cfg s b n e []
      else if c = 110 ∧ pySlice s idx (idx + 4) = cs "null" then .ok (.null, idx + 4)
      else if c = 116 ∧ pySlice s idx (idx + 4) = cs "true" then .ok (.bool true, idx + 4)
      else if c = 102 ∧ pySlice s idx (idx + 5) = cs "false" then .ok (.bool false, idx + 5)
      else pyScanNumber cfg s idx c

/-- `pyArrLoop` (the loop of `JSONArray`) with `b` frames left after `JSONArray`'s. -/
def pyArrLoopR (cfg : DCfg) (s : PStr) : Nat → Nat → Int → List JVal → DR (JVal × Int)
  | _, 0, _, _ => fuelOut
  | b, n + 1, e, acc =>
    match pyCall b (fun b => pyScanOnceR cfg s b n e) with
    | .error (.stop i) => .error (.jde "Expecting value" i)
    | .error err => .error err
    | .ok (v, e) =>
      match pyArrAfter s e with
      | .close e => (mkArr cfg (acc ++ [v])).map (·, e)
      | .err err => .error err
      | .next e => pyArrLoopR cfg s b n e (acc ++ [v])

/-- `pyObjLoop` (the loop of `JSONObject`) with `b` frames left after `JSONObject`'s. -/
def pyObjLoopR (cfg : DCfg) (s : PStr) : Nat → Nat → Int → List (PStr × JVal) → DR (JVal × Int)
  | _, 0, _, _ => fuelOut
  | b, n + 1, e, pairs =>
    match pyCall b (fun b => pyScanstringR s e cfg.strict b) with
    | .error err => .error err
    | .ok (key, e) =>
      match pyObjColon s e with
      | .error err => .error err
      | .ok e =>
        match pyCall b (fun b => pyScanOnceR cfg s b n e) with
        | .error (.stop i) => .error (.jde "Expecting value" i)
        | .error err => .error err
        | .ok (v, e) =>
          match pyObjAfter s e with
          | .close e => (pyMkObj cfg (pairs ++ [(key, v)])).map (·, e)
          | .err err => .error err
          | .next e => pyObjLoopR cfg s b n e (pairs ++ [(key, v)])
end

/-- `JSONDecoder.raw_decode(s, idx)` with `p` frames left when it calls `self.scan_once`, which
calls `_scan_once` (scanner.py:67-71). -/
def rawDecodePyR (cfg : DCfg) (p : Nat) (s : PStr) (idx : Int) : DR (JVal × Int) :=
  stopToJde (match p with
    | 0 => .error recPy
    | 1 => .error recPy
    | p + 2 => pyScanOnceR cfg s p (docFuel s) idx)

/-- `json.loads(s)` in pure Python with `p` frames left at the `scan_once` call. -/
def loadsPyR (cfg : DCfg) (p : Nat) (s : PStr) : DR JVal := decodeWith (rawDecodePyR cfg p) s

/-! ### Bridges to the unbounded models -/

/-- The bounded result `x` is the unbounded `y` or a `RecursionError` the bounded model
raised itself, and it is `y` when the room `b` covers the fuel `f`. -/
def RelB {α : Type} (isRec : DR α → Prop) (f b : Nat) (x y : DR α) : Prop :=
  (x = y ∨ isRec x) ∧ (f ≤ b → x = y)

def IsRecC {α : Type} (r : DR α) : Prop := r = .error (recC "object") ∨ r = .error (recC "array")

def IsRecPy {α : Type} (r : DR α) : Prop := r = .error recPy

theorem RelB.refl {α : Type} {P : DR α → Prop} {f b : Nat} (x : DR α) : RelB P f b x x :=
  ⟨Or.inl rfl, fun _ => rfl⟩

theorem RelB.succ {α : Type} {P : DR α → Prop} {f b : Nat} {x y : DR α} (h : RelB P f b x y) :
    RelB P (f + 1) (b + 1) x y :=
  ⟨h.1, fun hf => h.2 (by omega)⟩

theorem RelB.weak {α : Type} {P : DR α → Prop} {f b : Nat} {x y : DR α} (h : RelB P f b x y) :
    RelB P (f + 1) b x y :=
  ⟨h.1, fun hf => h.2 (by omega)⟩

theorem RelB.ite {α : Type} {P : DR α → Prop} {f b : Nat} {x1 y1 x2 y2 : DR α} (c : Prop) [Decidable c]
    (h1 : RelB P f b x1 y1) (h2 : RelB P f b x2 y2) :
    RelB P f b (if c then x1 else x2) (if c then y1 else y2) := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte]; exact h1
  · simp only [hc, ↓reduceIte]; exact h2

theorem RelB.rec0 {α : Type} {P : DR α → Prop} {f : Nat} {x y : DR α} (h : P x) :
    RelB P (f + 1) 0 x y :=
  ⟨Or.inr h, fun hf => by omega⟩

theorem bridgeC (cfg : DCfg) (s : PStr) : ∀ n : Nat,
    (∀ b idx, RelB IsRecC n b (cScanOnceR cfg s b n idx) (cScanOnce cfg s n idx)) ∧
    (∀ b e acc, RelB IsRecC n b (cArrLoopR cfg s b n e acc) (cArrLoop cfg s n e acc)) ∧
    (∀ b q acc, RelB IsRecC n b (cObjBodyR cfg s b n q acc) (cObjBody cfg s n q acc)) := by
  intro n
  induction n with
  | zero =>
    refine ⟨fun b idx => ?_, fun b e acc => ?_, fun b q acc => ?_⟩ <;>
      simp only [cScanOnceR, cScanOnce, cArrLoopR, cArrLoop, cObjBodyR, cObjBody] <;> exact RelB.refl _
  | succ n ih =>
    obtain ⟨ihS, ihA, ihO⟩ := ih
    refine ⟨fun b idx => ?_, fun b e acc => ?_, fun b q acc => ?_⟩
    · simp only [cScanOnceR, cScanOnce]
      by_cases h1 : idx ≥ s.length
      · simp only [h1, ↓reduceIte]; exact RelB.refl _
      simp only [h1, ↓reduceIte]
      by_cases h2 : s.getD idx 0 = 34
      · simp only [h2, ↓reduceIte]; exact RelB.refl _
      simp only [h2, ↓reduceIte]
      by_cases h3 : s.getD idx 0 = 123
      · simp only [h3, ↓reduceIte]
        cases b with
        | zero => exact RelB.rec0 (Or.inl rfl)
        | succ b =>
          simp only [cEnter]
          by_cases h4 : wsEnd s (idx + 1) ≥ s.length ∨ s.getD (wsEnd s (idx + 1)) 0 ≠ 125
          · simp only [h4, ↓reduceIte]
            by_cases h5 : wsEnd s (idx + 1) ≥ s.length ∨ s.getD (wsEnd s (idx + 1)) 0 ≠ 34
            · simp only [h5, ↓reduceIte]; exact RelB.refl _
            · simp only [h5, ↓reduceIte]; exact (ihO b _ []).succ
          · simp only [h4, ↓reduceIte]; exact RelB.refl _
      simp only [h3, ↓reduceIte]
      by_cases h6 : s.getD idx 0 = 91
      · simp only [h6, ↓reduceIte]
        cases b with
        | zero => exact RelB.rec0 (Or.inr rfl)
        | succ b =>
          simp only [cEnter]
          by_cases h7 : wsEnd s (idx + 1) ≥ s.length ∨ s.getD (wsEnd s (idx + 1)) 0 ≠ 93
          · simp only [h7, ↓reduceIte]; exact (ihA b _ []).succ
          · simp only [h7, ↓reduceIte]; exact RelB.refl _
      simp only [h6, ↓reduceIte]
      exact RelB.refl _
    · simp only [cArrLoopR, cArrLoop]
      have hS := ihS b e
      generalize cScanOnceR cfg s b n e = x at hS ⊢
      generalize cScanOnce cfg s n e = y at hS ⊢
      rcases hS with ⟨h1 | h1, h2⟩
      · subst h1
        cases x with
        | error x => exact RelB.refl _
        | ok p =>
          obtain ⟨v, next⟩ := p
          simp only
          cases cArrAfter s next with
          | close i => exact RelB.refl _
          | err x => exact RelB.refl _
          | next i => exact (ihA b _ _).weak
      · refine ⟨Or.inr ?_, fun hf => ?_⟩
        · rcases h1 with rfl | rfl <;> simp [IsRecC]
        · have hxy := h2 (by omega)
          subst hxy
          cases x with
          | error x => rfl
          | ok p =>
            obtain ⟨v, next⟩ := p
            simp only
            cases cArrAfter s next with
            | close i => rfl
            | err x => rfl
            | next i => exact (ihA b _ _).2 (by omega)
    · simp only [cObjBodyR, cObjBody]
      cases cScanstring s (q + 1) cfg.strict with
      | error x => exact RelB.refl _
      | ok r =>
        obtain ⟨key, next⟩ := r
        simp only
        by_cases h1 : wsEnd s next ≥ s.length ∨ s.getD (wsEnd s next) 0 ≠ 58
        · simp only [h1, ↓reduceIte]; exact RelB.refl _
        simp only [h1, ↓reduceIte]
        have hS := ihS b (wsEnd s (wsEnd s next + 1))
        generalize cScanOnceR cfg s b n (wsEnd s (wsEnd s next + 1)) = x at hS ⊢
        generalize cScanOnce cfg s n (wsEnd s (wsEnd s next + 1)) = y at hS ⊢
        rcases hS with ⟨h1 | h1, h2⟩
        · subst h1
          cases x with
          | error x => exact RelB.refl _
          | ok p =>
            obtain ⟨v, next2⟩ := p
            simp only
            cases cObjAfter s next2 with
            | close i => exact RelB.refl _
            | err x => exact RelB.refl _
            | next i =>
              simp only
              by_cases h2 : i.toNat ≥ s.length ∨ s.getD i.toNat 0 ≠ 34
              · simp only [h2, ↓reduceIte]; exact RelB.refl _
              · simp only [h2, ↓reduceIte]; exact (ihO b _ _).weak
        · refine ⟨Or.inr ?_, fun hf => ?_⟩
          · rcases h1 with rfl | rfl <;> simp [IsRecC]
          · have hxy := h2 (by omega)
            subst hxy
            cases x with
            | error x => rfl
            | ok p =>
              obtain ⟨v, next2⟩ := p
              simp only
              cases cObjAfter s next2 with
              | close i => rfl
              | err x => rfl
              | next i =>
                simp only
                by_cases h3 : i.toNat ≥ s.length ∨ s.getD i.toNat 0 ≠ 34
                · simp only [h3, ↓reduceIte]
                · simp only [h3, ↓reduceIte]; exact (ihO b _ _).2 (by omega)

/-- `py_scanstring` with `b` frames left is the unbounded one, or `RecursionError` when it has
no frame for `_decode_uXXXX` or for its `JSONDecodeError`. -/
theorem bridgeScanLoop (s : PStr) (strict : Bool) (begin : Int) (b : Nat) : ∀ (f e : Nat) (acc : PStr),
    pyScanLoopR s strict begin b f e acc = pyScanLoop s strict begin f e acc ∨
    (b ≤ 1 ∧ pyScanLoopR s strict begin b f e acc = .error recPy) := by
  intro f
  induction f with
  | zero => intro e acc; left; simp [pyScanLoopR, pyScanLoop]
  | succ f ih =>
    intro e acc
    simp only [pyScanLoopR, pyScanLoop]
    cases findTerm (s.drop e) with
    | none => left; rfl
    | some k =>
      simp only
      by_cases h1 : s.getD (e + k) 0 = 34
      · left; simp only [h1, ↓reduceIte]
      simp only [h1, ↓reduceIte]
      by_cases h2 : s.getD (e + k) 0 ≠ 92
      · simp only [h2, ↓reduceIte, ne_eq, not_false_eq_true]
        cases strict
        · simp only [Bool.false_eq_true, ↓reduceIte]; exact ih _ _
        · left; rfl
      simp only [h2, ↓reduceIte]
      cases s[e + k + 1]? with
      | none => left; rfl
      | some esc =>
        simp only
        by_cases h3 : esc ≠ 117
        · simp only [h3, ↓reduceIte, ne_eq, not_false_eq_true]
          cases backslash esc with
          | none => left; rfl
          | some ch => simp only; exact ih _ _
        simp only [h3, ↓reduceIte]
        cases b with
        | zero => right; exact ⟨by omega, rfl⟩
        | succ b =>
          simp only [pyCall]
          rcases chargeJde_cases b (decodeUXXXX s (e + k + 1)) with hc | ⟨hb0, hc⟩
          rotate_left
          · rw [hc]; right; exact ⟨by omega, rfl⟩
          rw [hc]
          cases decodeUXXXX s (e + k + 1) with
          | error x => left; rfl
          | ok uni =>
            simp only
            by_cases h4 : 0xd800 ≤ uni ∧ uni ≤ 0xdbff ∧ (s.drop (e + k + 1 + 5)).take 2 = [92, 117]
            · simp only [h4, and_self, ↓reduceIte]
              rcases chargeJde_cases b (decodeUXXXX s (e + k + 1 + 5 + 1)) with hc2 | ⟨hb0, hc2⟩
              rotate_left
              · rw [hc2]; right; exact ⟨by omega, rfl⟩
              rw [hc2]
              cases decodeUXXXX s (e + k + 1 + 5 + 1) with
              | error x => left; rfl
              | ok uni2 =>
                simp only
                by_cases h5 : 0xdc00 ≤ uni2 ∧ uni2 ≤ 0xdfff
                · simp only [h5, and_self, ↓reduceIte]
                  exact ih _ _
                · simp only [h5, ↓reduceIte]
                  exact ih _ _
            · simp only [h4, ↓reduceIte]
              exact ih _ _

theorem bridgeScanstring (s : PStr) (e : Int) (strict : Bool) (b : Nat) :
    RelB IsRecPy 2 b (pyScanstringR s e strict b) (pyScanstring s e strict) := by
  unfold pyScanstringR pyScanstring
  rcases chargeJde_cases b (pyScanLoopR s strict (e - 1) b (s.length + 1) (clampPos s e) []) with hc | ⟨hb0, hc⟩
  · rw [hc]
    rcases bridgeScanLoop s strict (e - 1) b (s.length + 1) (clampPos s e) [] with h | ⟨h0, h⟩
    · rw [h]; exact RelB.refl _
    · exact ⟨Or.inr h, fun hb => by omega⟩
  · rw [hc]; exact ⟨Or.inr rfl, fun hb => by omega⟩

/-- A frame's `chargeJde` keeps the relation when the fuel needs two frames. -/
theorem RelB.charge {α : Type} {f b : Nat} {x y : DR α} (h : RelB IsRecPy (f + 2) (b + 1) x y) :
    RelB IsRecPy (f + 2) (b + 1) (chargeJde b x) y := by
  rcases chargeJde_cases b x with hc | ⟨hb0, hc⟩
  · rw [hc]; exact h
  · rw [hc]; exact ⟨Or.inr rfl, fun hf => by omega⟩

theorem bridgePy (cfg : DCfg) (s : PStr) : ∀ n : Nat,
    (∀ b idx, RelB IsRecPy (n + 2) b (pyScanOnceR cfg s b n idx) (pyScanOnce cfg s n idx)) ∧
    (∀ b e acc, RelB IsRecPy (n + 2) b (pyArrLoopR cfg s b n e acc) (pyArrLoop cfg s n e acc)) ∧
    (∀ b e acc, RelB IsRecPy (n + 2) b (pyObjLoopR cfg s b n e acc) (pyObjLoop cfg s n e acc)) := by
  intro n
  induction n with
  | zero =>
    refine ⟨fun b idx => ?_, fun b e acc => ?_, fun b q acc => ?_⟩ <;>
      simp only [pyScanOnceR, pyScanOnce, pyArrLoopR, pyArrLoop, pyObjLoopR, pyObjLoop] <;> exact RelB.refl _
  | succ n ih =>
    obtain ⟨ihS, ihA, ihO⟩ := ih
    refine ⟨fun b idx => ?_, fun b e acc => ?_, fun b q acc => ?_⟩
    · simp only [pyScanOnceR, pyScanOnce]
      cases pyIndex s idx with
      | none => exact RelB.refl _
      | some c =>
        simp only
        by_cases h2 : c = 34
        · simp only [h2, ↓reduceIte]
          cases b with
          | zero => exact RelB.rec0 rfl
          | succ b =>
            simp only [pyCall]
            have hs := bridgeScanstring s (idx + 1) cfg.strict b
            generalize pyScanstringR s (idx + 1) cfg.strict b = x at hs ⊢
            generalize pyScanstring s (idx + 1) cfg.strict = y at hs ⊢
            rcases hs with ⟨h1 | h1, h3⟩
            · subst h1; exact RelB.refl _
            · refine ⟨Or.inr (by rw [h1]; rfl), fun hf => ?_⟩
              have hxy := h3 (by omega)
              subst hxy; rfl
        simp only [h2, ↓reduceIte]
        by_cases h3 : c = 123
        · simp only [h3, ↓reduceIte]
          cases b with
          | zero => exact RelB.rec0 rfl
          | succ b =>
            simp only [pyCall]
            exact RelB.charge (RelB.ite _ (RelB.ite _ (RelB.refl _) (RelB.ite _ (RelB.refl _) (ihO b _ []).succ))
              (ihO b _ []).succ)
        simp only [h3, ↓reduceIte]
        by_cases h4 : c = 91
        · simp only [h4, ↓reduceIte]
          cases b with
          | zero => exact RelB.rec0 rfl
          | succ b =>
            simp only [pyCall]
            exact RelB.charge (RelB.ite _ (RelB.refl _) (ihA b _ []).succ)
        simp only [h4, ↓reduceIte]
        exact RelB.refl _
    · simp only [pyArrLoopR, pyArrLoop]
      cases b with
      | zero => exact RelB.rec0 rfl
      | succ b =>
        simp only [pyCall]
        have hS := ihS b e
        generalize pyScanOnceR cfg s b n e = x at hS ⊢
        generalize pyScanOnce cfg s n e = y at hS ⊢
        rcases hS with ⟨h1 | h1, h2⟩
        · subst h1
          cases x with
          | error x => cases x <;> exact RelB.refl _
          | ok p =>
            obtain ⟨v, e2⟩ := p
            simp only
            cases pyArrAfter s e2 with
            | close i => exact RelB.refl _
            | err x => exact RelB.refl _
            | next i => exact (ihA (b + 1) _ _).weak
        · refine ⟨Or.inr (by rw [h1]; rfl), fun hf => ?_⟩
          have hxy := h2 (by omega)
          subst hxy
          cases x with
          | error x => cases x <;> rfl
          | ok p =>
            obtain ⟨v, e2⟩ := p
            simp only
            cases pyArrAfter s e2 with
            | close i => rfl
            | err x => rfl
            | next i => exact (ihA (b + 1) _ _).2 (by omega)
    · simp only [pyObjLoopR, pyObjLoop]
      cases b with
      | zero => exact RelB.rec0 rfl
      | succ b =>
        simp only [pyCall]
        have hs := bridgeScanstring s q cfg.strict b
        generalize pyScanstringR s q cfg.strict b = x at hs ⊢
        generalize pyScanstring s q cfg.strict = y at hs ⊢
        have cont : ∀ r : DR (PStr × Int), RelB IsRecPy (n + 1 + 2) (b + 1)
            (match r with
              | .error err => .error err
              | .ok (key, e) =>
                match pyObjColon s e with
                | .error err => .error err
                | .ok e =>
                  match pyScanOnceR cfg s b n e with
                  | .error (.stop i) => .error (.jde "Expecting value" i)
                  | .error err => .error err
                  | .ok (v, e) =>
                    match pyObjAfter s e with
                    | .close e => (pyMkObj cfg (acc ++ [(key, v)])).map (·, e)
                    | .err err => .error err
                    | .next e => pyObjLoopR cfg s (b + 1) n e (acc ++ [(key, v)]))
            (match r with
              | .error err => .error err
              | .ok (key, e) =>
                match pyObjColon s e with
                | .error err => .error err
                | .ok e =>
                  match pyScanOnce cfg s n e with
                  | .error (.stop i) => .error (.jde "Expecting value" i)
                  | .error err => .error err
                  | .ok (v, e) =>
                    match pyObjAfter s e with
                    | .close e => (pyMkObj cfg (acc ++ [(key, v)])).map (·, e)
                    | .err err => .error err
                    | .next e => pyObjLoop cfg s n e (acc ++ [(key, v)])) := by
          intro r
          cases r with
          | error x => exact RelB.refl _
          | ok p =>
            obtain ⟨key, e⟩ := p
            simp only
            cases pyObjColon s e with
            | error x => exact RelB.refl _
            | ok e =>
              simp only
              have hS := ihS b e
              generalize pyScanOnceR cfg s b n e = x at hS ⊢
              generalize pyScanOnce cfg s n e = y at hS ⊢
              rcases hS with ⟨h1 | h1, h2⟩
              · subst h1
                cases x with
                | error x => cases x <;> exact RelB.refl _
                | ok p =>
                  obtain ⟨v, e2⟩ := p
                  simp only
                  cases pyObjAfter s e2 with
                  | close i => exact RelB.refl _
                  | err x => exact RelB.refl _
                  | next i => exact (ihO (b + 1) _ _).weak
              · refine ⟨Or.inr (by rw [h1]; rfl), fun hf => ?_⟩
                have hxy := h2 (by omega)
                subst hxy
                cases x with
                | error x => cases x <;> rfl
                | ok p =>
                  obtain ⟨v, e2⟩ := p
                  simp only
                  cases pyObjAfter s e2 with
                  | close i => rfl
                  | err x => rfl
                  | next i => exact (ihO (b + 1) _ _).2 (by omega)
        rcases hs with ⟨h1 | h1, h3⟩
        · subst h1; exact cont x
        · refine ⟨Or.inr (by rw [h1]; rfl), fun hf => ?_⟩
          have hxy := h3 (by omega)
          subst hxy
          exact (cont x).2 hf

end PyLean.JsonMod
