import PyLean.TypeObj.Call
import PyLean.TypeObj.ExcProps

/-!
The other half of properties that say "if this succeeds, the result is right". Such a property
holds of a function that always raises, so on its own it pins nothing. Each statement here says
when the function does succeed, or exactly how it fails, so the pair determines the behaviour.
-/

namespace PyLean.TypeObj

/-- **Exception `__init__`s accept these arguments.** With no keywords, or only the keywords each
type defines, `StopIteration`, `SystemExit`, `ImportError`, `NameError` and `AttributeError`
initialise: they do not raise. `typeobj-exc-stopiteration-value` and its neighbours say what
results. -/
def ExcInitAccepts : Prop :=
  (∀ (a : Addr) (args : List Val) (w : World),
    ∃ w', stopIterationInit (.obj a) args [] w = .ok () w') ∧
  (∀ (a : Addr) (args : List Val) (w : World),
    ∃ w', systemExitInit (.obj a) args [] w = .ok () w') ∧
  (∀ (a : Addr) (args : List Val) (n : Val) (w : World),
    ∃ w', nameErrorInit (.obj a) args [("name", n)] w = .ok () w') ∧
  (∀ (a : Addr) (args : List Val) (n o : Val) (w : World),
    ∃ w', attributeErrorInit (.obj a) args [("name", n), ("obj", o)] w = .ok () w') ∧
  (∀ (a : Addr) (args : List Val) (w : World),
    ∃ w', importErrorInit (.obj a) args [] w = .ok () w')

theorem excInitAccepts_proven : ExcInitAccepts := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a args w
    simp only [stopIterationInit, baseExceptionInit, argNoKeywords, M.bind_app, getW_app]
    simp [excUpdate_app]
  · intro a args w
    simp only [systemExitInit, baseExceptionInit, argNoKeywords, M.bind_app, getW_app]
    cases args with
    | nil => simp [excUpdate_app]
    | cons x xs => cases xs <;> simp [excUpdate_app]
  · intro a args n w
    simp only [nameErrorInit, baseExceptionInit, argNoKeywords, argKeywordOnly, M.bind_app,
      getW_app]
    simp [excUpdate_app, NameDict.get?]
  · intro a args n o w
    simp only [attributeErrorInit, baseExceptionInit, argNoKeywords, argKeywordOnly, M.bind_app,
      getW_app]
    simp [excUpdate_app, NameDict.get?]
  · intro a args w
    simp only [importErrorInit, baseExceptionInit, argNoKeywords, argKeywordOnly, M.bind_app,
      getW_app]
    cases args with
    | nil => simp [excUpdate_app, NameDict.get?]
    | cons x xs => cases xs <;> simp [excUpdate_app, NameDict.get?]

/-- **`__cause__` and `__context__` take `None` or an exception, and nothing else.** A value that
is neither is the exact `TypeError`; `None` or an exception is accepted, and the neighbouring
entries say what is stored. -/
def ExcChainSetAccepts : Prop :=
  ∀ (a : Addr) (v : Val) (w : World),
    ((v.is .none = true ∨ excInstanceCheck w v = true) →
      (∃ w', baseExceptionCauseSet (.obj a) (some v) w = .ok () w') ∧
      (∃ w', baseExceptionContextSet (.obj a) (some v) w = .ok () w')) ∧
    (v.is .none = false → excInstanceCheck w v = false →
      baseExceptionCauseSet (.obj a) (some v) w =
        (typeErr "exception cause must be None or derive from BaseException" : M Unit) w ∧
      baseExceptionContextSet (.obj a) (some v) w =
        (typeErr "exception context must be None or derive from BaseException" : M Unit) w)

theorem excChainSetAccepts_proven : ExcChainSetAccepts := by
  intro a v w
  constructor
  · intro h
    by_cases h0 : v.is .none = true
    · simp [baseExceptionCauseSet, baseExceptionContextSet, h0, pyExceptionSetCause,
        pyExceptionSetContext, excUpdate_app]
    · have h1 : excInstanceCheck w v = true := by simpa [h0] using h
      simp [baseExceptionCauseSet, baseExceptionContextSet, h0, h1, pyExceptionSetCause,
        pyExceptionSetContext, excUpdate_app]
  · intro h0 h1
    simp [baseExceptionCauseSet, baseExceptionContextSet, h0, h1]

/-- **`__hash__ = None` is written exactly when it should be.** With `tp_hash` NULL and no
`__hash__` in the dict, `type_ready_set_hash` succeeds; with `tp_hash` set it leaves the world
alone. `typeobj-hash-none-eq` says what the first case writes. -/
def TypeReadySetHashAccepts : Prop :=
  ∀ (t : Addr) (w : World),
    ((slotOf w t .tp_hash).isSome = true → typeReadySetHash t w = .ok () w) ∧
    (∃ w', typeReadySetHash t w = .ok () w')

theorem typeReadySetHashAccepts_proven : TypeReadySetHashAccepts := by
  intro t w
  constructor
  · intro h
    have hn : ¬ ((slotOf w t .tp_hash).isNone && !NameDict.contains (tdata w t).dict "__hash__") = true := by
      cases hs : slotOf w t .tp_hash <;> simp_all
    simp only [typeReadySetHash, M.bind_app, getW_app]
    rw [if_neg hn]
    rfl
  · by_cases h : ((slotOf w t .tp_hash).isNone && !NameDict.contains (tdata w t).dict "__hash__") = true
    · simp only [typeReadySetHash, M.bind_app, getW_app, h, if_true]
      exact ⟨_, rfl⟩
    · simp only [typeReadySetHash, M.bind_app, getW_app]
      rw [if_neg h]
      exact ⟨_, rfl⟩

/-- **`best_base` accepts a chain and rejects a conflict.** One acceptable base wins alone. Two
bases whose solid bases are unrelated are the exact layout conflict, whichever comes first, and a
base that forbids subclassing is the exact `TypeError` text. With `typeobj-best-base`, which says a
result dominates every base, this fixes the outcome both ways. -/
def BestBaseDecides : Prop :=
  ∀ (w : World) (a b : Addr) (x y : Val),
    (asType w x = some a → (tdata w a).baseType = true →
      bestBaseLoop w [x] none none = .ok a) ∧
    (asType w x = some a → (tdata w a).baseType = false →
      bestBaseLoop w [x] none none =
        .error s!"type '{trunc 100 (tpName w a)}' is not an acceptable base type") ∧
    (asType w x = some a → asType w y = some b → (tdata w a).baseType = true →
      (tdata w b).baseType = true →
      isSubtype w (solidBase w a) (solidBase w b) = false →
      isSubtype w (solidBase w b) (solidBase w a) = false →
      bestBaseLoop w [x, y] none none = .error "multiple bases have instance lay-out conflict")

theorem bestBaseDecides_proven : BestBaseDecides := by
  intro w a b x y
  refine ⟨?_, ?_, ?_⟩
  · intro h1 h2
    simp [bestBaseLoop, h1, h2]
  · intro h1 h2
    simp [bestBaseLoop, h1, h2]
  · intro h1 h2 h3 h4 h5 h6
    simp [bestBaseLoop, h1, h2, h3, h4, h5, h6]

end PyLean.TypeObj
