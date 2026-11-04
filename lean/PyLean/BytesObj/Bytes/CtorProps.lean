import PyLean.BytesObj.Bytes.BasicProps4
import PyLean.BytesObj.Bytes.Hex

/-!
`bytes_new_impl` arm by arm, its subtype arm, `bytes.__bytes__`, and the subclass branch of
`bytes_fromhex_impl`.
-/

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

set_option linter.unusedSimpArgs false

/-- The arms of `bytes_new_impl` (bytesobject.c:2881-2949) in their order: `encoding` or `errors`
without an argument (:2881-2889, encoding named first); an encoding with a non-str (:2892-2896); errors
without an encoding (:2898-2903); `__bytes__` returning bytes, or anything else, which is the
TypeError naming both types (:2907-2919); an int, through `PyNumber_AsSsize_t(x, OverflowError)`
(:2928-2945) and `_PyBytes_FromSize` (:97-114): outside `Py_ssize_t` it cannot fit, past
`PY_SSIZE_T_MAX - PyBytesObject_SIZE` the string is too large, past what `malloc` gives it is a
`MemoryError`, a negative count is a ValueError, and otherwise it is that many zero bytes. And an
encoding with an `errors` the codec knows: latin-1 copies the code points of a text below 256 for
every handler. -/
def BytesNewArms : Prop :=
  (∀ (e : String) (r : Option String), bytesNew none (some e) r =
    .error (.typeError "encoding without a string argument")) ∧
  (∀ r : String, bytesNew none none (some r) = .error (.typeError "errors without a string argument")) ∧
  (∀ (x : Obj) (e : String) (r : Option String), (∀ cs, x ≠ .str cs) →
    bytesNew (some x) (some e) r = .error (.typeError "encoding without a string argument")) ∧
  (∀ (cs : Seq) (r : String), bytesNew (some (.str cs)) none (some r) =
    .error (.typeError "string argument without an encoding")) ∧
  (∀ (x : Obj) (r : String), (∀ cs, x ≠ .str cs) → bytesNew (some x) none (some r) =
    .error (.typeError "errors without a string argument")) ∧
  (∀ s : Seq, bytesNew (some (.dunder (.bytes s))) none none = .ok s) ∧
  (∀ r : Obj, (∀ s, r ≠ .bytes s) → bytesNew (some (.dunder r)) none none =
    .error (.typeError s!"BDun.__bytes__() must return a bytes, not {r.typeName}")) ∧
  (∀ n : Int, (n < ssizeMin ∨ n > ssizeMax) → bytesNew (some (.int n)) none none =
    .error (.overflowError "cannot fit 'int' into an index-sized integer")) ∧
  (∀ n : Int, ssizeMax - 33 < n → n ≤ ssizeMax → bytesNew (some (.int n)) none none =
    .error (.overflowError "byte string is too large")) ∧
  (∀ n : Int, 0 < n → n ≤ ssizeMax - 33 → 2 ^ 47 ≤ n + 33 → bytesNew (some (.int n)) none none =
    .error memoryError) ∧
  (∀ n : Int, ssizeMin ≤ n → n < 0 → bytesNew (some (.int n)) none none =
    .error (.valueError "negative count")) ∧
  (∀ n : Int, 0 ≤ n → n + 33 < 2 ^ 47 → bytesNew (some (.int n)) none none = .ok (List.replicate n.toNat 0)) ∧
  (∀ (s : Seq) (r : String) (h : UnicodeObj.ErrHandler), (∀ c ∈ s, c < 256) → errHandlerOf (some r) = some h →
    bytesNew (some (.str s)) (some "latin-1") (some r) = .ok s)

theorem bytesNewArms_proven : BytesNewArms := by
  have hmax := ssizeMax_val
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e r; simp [bytesNew]
  · intro r; simp [bytesNew]
  · intro x e r h
    cases x <;> simp [bytesNew]
    exact absurd rfl (h _)
  · intro cs r; simp [bytesNew]
  · intro x r h
    cases x <;> simp [bytesNew]
    exact absurd rfl (h _)
  · intro s; simp [bytesNew]
  · intro r h
    cases r <;> first
      | exact absurd rfl (h _)
      | (simp [bytesNew, bytesDunderWrong, Obj.typeName]; try rfl)
  · intro n h
    have h' : ¬ (ssizeMin ≤ n ∧ n ≤ ssizeMax) := by omega
    simp [bytesNew, Obj.index?, countOf, h', Obj.typeName]
    rfl
  · intro n h1 h2
    have h3 : ssizeMin ≤ n ∧ n ≤ ssizeMax := by simp only [ssizeMin, hmax] at *; omega
    have h4 : ¬ n < 0 := by omega
    have h5 : ¬ n = 0 := by omega
    have h6 : n > ssizeMax - bytesObjectSize := by rw [objsize_val]; omega
    simp [bytesNew, Obj.index?, countOf, h3, h4, bytesFromSize, bytesSizeCheck, h5, h6]
  · intro n h1 h2 h3
    have h3' : ssizeMin ≤ n ∧ n ≤ ssizeMax := by simp only [ssizeMin, hmax] at *; omega
    have h4 : ¬ n < 0 := by omega
    have h5 : ¬ n = 0 := by omega
    have h6 : ¬ n > ssizeMax - bytesObjectSize := by rw [objsize_val]; omega
    have h7 : mallocFails (bytesObjectSize + n) = true := by
      simp [mallocFails, objsize_val]; omega
    simp [bytesNew, Obj.index?, countOf, h3', h4, bytesFromSize, bytesSizeCheck, h5, h6, h7]
  · intro n h1 h2
    have h3 : ssizeMin ≤ n ∧ n ≤ ssizeMax := by simp only [ssizeMin, hmax] at *; omega
    simp [bytesNew, Obj.index?, countOf, h3, h2]
  · intro n h1 h2
    have h3 : ssizeMin ≤ n ∧ n ≤ ssizeMax := by simp only [ssizeMin, hmax] at *; omega
    have h4 : ¬ n < 0 := by omega
    simp [bytesNew, Obj.index?, countOf, h3, h4, bytesFromSize, bytesSizeCheck_ok n h1 h2]
  · intro s r h hs hr
    have := UnicodeObj.latin1RoundTrip_proven s h (fun _ => none) hs
    simp only [UnicodeObj.latin1Decode] at this
    simp [bytesNew, unicodeEncode, sc_latin1, hr, this]

/-- The subtype arm and the class of the results: `bytes.__new__(T, ...)` for a subclass `T` gives
an instance of `T` with the contents the arms give for `bytes` (`bytes_subtype_new`); `__bytes__` of
any instance is an exact bytes with the same contents (:1832-1837); `T.fromhex(s)` is an instance of `T`
with the bytes `bytes.fromhex(s)` gives (:2621-2623), and an exact bytes for `bytes` itself. -/
def BytesNewSubtype : Prop :=
  (∀ (T : String) (x : Option Obj) (e r : Option String), T ≠ "bytes" →
    bytesNewType T x e r = (bytesNew x e r).map (fun b => (T, b))) ∧
  (∀ (x : Option Obj) (e r : Option String),
    bytesNewType "bytes" x e r = (bytesNew x e r).map (fun b => ("bytes", b))) ∧
  (∀ (cls : String) (s : Seq), bytesDunderBytes cls s = ("bytes", s)) ∧
  (∀ (T : String) (o : Obj), T ≠ "bytes" → bytesFromHexType T o = (bytesFromHex o).map (fun b => (T, b))) ∧
  (∀ o : Obj, bytesFromHexType "bytes" o = (bytesFromHex o).map (fun b => ("bytes", b)))

theorem bytesNewSubtype_proven : BytesNewSubtype := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro T x e r hT
    unfold bytesNewType
    cases bytesNew x e r <;> simp [hT, bytesSubtypeNew, Except.map]
  · intro x e r
    unfold bytesNewType
    cases bytesNew x e r <;> simp [Except.map]
  · intro cls s
    unfold bytesDunderBytes
    split <;> simp_all
  · intro T o hT
    unfold bytesFromHexType bytesFromHexT
    cases bytesFromHex o <;> simp [hT, plainSubCall, bytesNewType, bytesNew, bytesSubtypeNew, Except.map]
  · intro o
    unfold bytesFromHexType bytesFromHexT
    cases bytesFromHex o <;> simp [Except.map]

/-- The subclass branch of `bytes_fromhex_impl` (bytesobject.c:2621-2623) runs user code: for any
`type(result)`, the result is what that call gives, an exception included (a subclass whose
`__init__` takes other arguments makes `T.fromhex('00')` a TypeError) or any object (a `__new__` that
returns an int); the call is made only after the parse succeeded, so a parse error comes first and no
user code runs; for `bytes` itself no call is made. -/
def FromHexCallback : Prop :=
  (∀ {α : Type} (inj : Seq → α) (f : Seq → Py α) (o : Obj) (r : Seq), bytesFromHex o = .ok r →
    bytesFromHexT inj (some f) o = f r) ∧
  (∀ {α : Type} (inj : Seq → α) (f : Seq → Py α) (o : Obj) (e : PyExc), bytesFromHex o = .error e →
    bytesFromHexT inj (some f) o = .error e) ∧
  (∀ {α : Type} (inj : Seq → α) (o : Obj), bytesFromHexT inj none o = (bytesFromHex o).map inj) ∧
  (∀ (o : Obj) (r : Seq) (e : PyExc), bytesFromHex o = .ok r →
    bytesFromHexT (fun r => Obj.bytes r) (some (fun _ => .error e)) o = .error e) ∧
  (∀ (o : Obj) (r : Seq) (x : Obj), bytesFromHex o = .ok r →
    bytesFromHexT (fun r => Obj.bytes r) (some (fun _ => .ok x)) o = .ok x)

theorem fromHexCallback_proven : FromHexCallback := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro α inj f o r h; simp [bytesFromHexT, h]
  · intro α inj f o e h; simp [bytesFromHexT, h]
  · intro α inj o; unfold bytesFromHexT; cases bytesFromHex o <;> rfl
  · intro o r e h; simp [bytesFromHexT, h]
  · intro o r x h; simp [bytesFromHexT, h]

/-- `__getnewargs__` (bytesobject.c:2775-2780) is a 1-tuple holding an exact bytes with the contents,
whatever the class of `self`; it is what `copyreg.__newobj__` passes back to `cls.__new__`, which for
a subclass that keeps `bytes.__new__` rebuilds an instance of `cls` with the same contents (the pickle
round trip). -/
def GetnewargsPickle : Prop :=
  ∀ (cls : String) (s : Seq), ∃ a, bytesGetnewargs s = .tuple [a] ∧ a.typeName = "bytes" ∧
    a.buffer? = some s ∧ bytesNewType cls (some a) none none = .ok (if cls ≠ "bytes" then cls else "bytes", s)

theorem getnewargsPickle_proven : GetnewargsPickle := by
  intro cls s
  refine ⟨.bytes s, rfl, rfl, rfl, ?_⟩
  by_cases h : cls ≠ "bytes" <;> simp [bytesNewType, bytesNew, bytesSubtypeNew, h]

end PyLean.BytesObj.Bytes
