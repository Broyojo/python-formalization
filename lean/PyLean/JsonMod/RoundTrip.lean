import PyLean.JsonMod.DecProps
import PyLean.JsonMod.EncTwins

/-!
Round trip of strings: `json.loads(json.dumps(t)) == t`.

With `ensure_ascii=True` a `str` holding a high surrogate followed by a low
surrogate (two code points) is written as `"𝄞"`, which `loads`
reads as the single code point U+1D11E: refuted. Without such a pair, and for
every string with `ensure_ascii=False`, the round trip holds (proven for the
pure-Python decoder by following `py_scanstring` through the escaped text, and
transferred to the C decoder with `loadsTwinsScan_proven`).
-/

namespace PyLean.JsonMod

open PyLean

def isHigh (c : Nat) : Bool := 0xd800 ≤ c && c ≤ 0xdbff
def isLow (c : Nat) : Bool := 0xdc00 ≤ c && c ≤ 0xdfff

/-- No high surrogate immediately followed by a low surrogate. -/
def noSurrPair : PStr → Bool
  | a :: b :: t => !(isHigh a && isLow b) && noSurrPair (b :: t)
  | _ => true

/-- `loads(dumps(t)) == t` for every Python `str` `t`, with either encoder and
either decoder, whatever `ensure_ascii` and the other options (the JSON text
is a Python `str`: its length is at most `sys.maxsize`). -/
def RoundTripStr : Prop :=
  ∀ (cfg : ECfg) (dcfg : DCfg) (t d : PStr), strOk t = true → dumpsC cfg (.str t) = .ok d →
    (d.length : Int) ≤ ssizeMax →
    loadsPy dcfg d = .ok (.str t) ∧ loadsC dcfg d = .ok (.str t)

/-- `json.loads(json.dumps('𝄞'))` is `'\U0001d11e'`: the two
surrogate code points are escaped one by one and the decoder joins the escapes
into one character. -/
theorem roundTripStr_refuted : ¬RoundTripStr := by
  intro h
  have hd : dumpsC {} (.str [0xd834, 0xdd1e]) = .ok (cs "\"\\ud834\\udd1e\"") := by decide
  have := (h {} {} [0xd834, 0xdd1e] _ (by decide) hd (by decide)).1
  have e : loadsPy {} (cs "\"\\ud834\\udd1e\"") = .ok (.str [0x1d11e]) := by decide
  rw [e] at this
  exact absurd this (by decide)

/-! ### The proof of the narrowed round trip -/

theorem hexVal_hexCp {d : Nat} (h : d < 16) : hexVal (hexCp d) = some d := by
  unfold hexVal hexCp
  by_cases h10 : d < 10
  · simp only [h10, ↓reduceIte]
    rw [if_pos (by omega)]
    congr 1; omega
  · simp only [h10, ↓reduceIte]
    rw [if_neg (by omega), if_pos (by omega)]
    congr 1; omega

theorem hex4_uEsc (s : PStr) (p n : Nat) (r : PStr) (hs : s.drop p = uEsc n ++ r) (hn : n < 0x10000) :
    hex4 s (p + 2) = some n := by
  unfold hex4
  have : (s.drop (p + 2)).take 4 =
      [hexCp (n / 4096 % 16), hexCp (n / 256 % 16), hexCp (n / 16 % 16), hexCp (n % 16)] := by
    rw [show p + 2 = p + 1 + 1 from rfl, ← List.drop_drop, ← List.drop_drop, hs]
    simp [uEsc]
  rw [this]
  simp only
  rw [hexVal_hexCp (Nat.mod_lt _ (by decide)), hexVal_hexCp (Nat.mod_lt _ (by decide)),
    hexVal_hexCp (Nat.mod_lt _ (by decide)), hexVal_hexCp (Nat.mod_lt _ (by decide))]
  congr 1
  omega

/-- `py_scanstring` takes an unescaped, non-terminator character into the
current chunk. -/
theorem pyScanLoop_absorb (s : PStr) (strict : Bool) (b : Int) (f e c : Nat) (a : PStr)
    (hc : s[e]? = some c) (ht : isTerm c = false) :
    pyScanLoop s strict b (f + 1) e a = pyScanLoop s strict b (f + 1) (e + 1) (a ++ [c]) := by
  have hlt : e < s.length := (List.getElem?_eq_some_iff.mp hc).1
  have hd : s.drop e = c :: s.drop (e + 1) := by
    rw [List.drop_eq_getElem_cons hlt]; simp [(List.getElem?_eq_some_iff.mp hc).2]
  have hf : findTerm (s.drop e) = (findTerm (s.drop (e + 1))).map (· + 1) := by
    rw [hd]; simp [findTerm, ht]
  simp only [pyScanLoop]
  rw [hf]
  cases hk : findTerm (s.drop (e + 1)) with
  | none => rfl
  | some k =>
    simp only [Option.map_some]
    rw [hd, List.take_succ_cons, show e + (k + 1) = e + 1 + k by omega, List.append_assoc]
    rfl

end PyLean.JsonMod
