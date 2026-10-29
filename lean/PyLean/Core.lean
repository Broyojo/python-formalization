/-!
Shared vocabulary for CPython models.

* A Python exception is a value of `PyExc`; a model function returns `Py α`.
* Python `int` is Lean `Int` (or `Nat` where the source guarantees `>= 0`).
  There is no wraparound in pure-Python code; C code that narrows to
  `Py_ssize_t` must model that narrowing explicitly with `ssize`.
* Loops are written with explicit fuel. Running out of fuel is reported as
  `PyExc.modelFuel`, which never corresponds to Python behaviour, so properties
  quantify over inputs where the source loop terminates.
-/

namespace PyLean

/-- Exception classes that models raise. The message is compared exactly
by the differential tester, so models copy the source's format string. -/
inductive PyExc where
  | valueError (msg : String)
  | typeError (msg : String)
  | indexError (msg : String)
  | keyError (msg : String)
  | overflowError (msg : String)
  | zeroDivisionError (msg : String)
  | assertionError (msg : String)
  | stopIteration
  /-- A module-defined exception class, e.g. `ipaddress.NetmaskValueError`. -/
  | named (cls : String) (msg : String)
  /-- Not a Python exception: the model's loop fuel ran out. -/
  | modelFuel
  deriving Repr, DecidableEq, Inhabited

/-- Name of the Python exception class, as `type(e).__name__` prints it. -/
def PyExc.className : PyExc → String
  | .valueError _ => "ValueError"
  | .typeError _ => "TypeError"
  | .indexError _ => "IndexError"
  | .keyError _ => "KeyError"
  | .overflowError _ => "OverflowError"
  | .zeroDivisionError _ => "ZeroDivisionError"
  | .assertionError _ => "AssertionError"
  | .stopIteration => "StopIteration"
  | .named cls _ => cls
  | .modelFuel => "<model fuel exhausted>"

def PyExc.message : PyExc → String
  | .valueError m | .typeError m | .indexError m | .keyError m
  | .overflowError m | .zeroDivisionError m | .assertionError m | .named _ m => m
  | .stopIteration | .modelFuel => ""

/-- Result of evaluating Python code: a value or a raised exception. -/
abbrev Py (α : Type) := Except PyExc α

instance {α : Type} [DecidableEq α] : DecidableEq (Py α)
  | .ok a, .ok b => if h : a = b then .isTrue (h ▸ rfl) else .isFalse (fun e => h (Except.ok.inj e))
  | .error a, .error b => if h : a = b then .isTrue (h ▸ rfl) else .isFalse (fun e => h (Except.error.inj e))
  | .ok _, .error _ => .isFalse (fun e => nomatch e)
  | .error _, .ok _ => .isFalse (fun e => nomatch e)

/-- `True` when the computation raised an exception of the given class. -/
def Py.raises {α : Type} (r : Py α) (cls : String) : Prop :=
  ∃ e, r = .error e ∧ e.className = cls

/-- `int.bit_length()` on a non-negative int. -/
def bitLength (n : Nat) : Nat := if n = 0 then 0 else Nat.log2 n + 1

/-- Python `~a & b` for `a b >= 0`. Since `b` has no bits at or above
`bit_length(b)`, complementing `a` within that width is exact. -/
def notAnd (a b : Nat) : Nat := ((2 ^ bitLength b - 1) ^^^ a) &&& b

/-- `Py_ssize_t` on a 64-bit build. -/
def ssizeMin : Int := -(2 ^ 63)
def ssizeMax : Int := 2 ^ 63 - 1

end PyLean
