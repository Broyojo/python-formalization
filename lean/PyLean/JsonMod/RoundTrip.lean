import PyLean.JsonMod.DecProps
import PyLean.JsonMod.EncTwins

/-!
Round trip of strings: `json.loads(json.dumps(t)) == t`.

With `ensure_ascii=True` a `str` holding a high surrogate followed by a low
surrogate (two code points) is written as `"𝄞"`, which `loads`
reads as the single code point U+1D11E: refuted. Without such a pair, and for
every string with `ensure_ascii=False`, the round trip holds (`json-roundtrip`,
`RoundTripTop.lean`). This file has the steps of `py_scanstring` on escaped text.
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
  have e : loadsPy {} (cs "\"\\ud834\\udd1e\"") = .ok (.str [0x1d11e]) := by decide +kernel
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
  show some (((n / 4096 % 16 * 16 + n / 256 % 16) * 16 + n / 16 % 16) * 16 + n % 16) = some n
  have a1 : n / 4096 % 16 = n / 4096 := by omega
  have a2 : n / 4096 * 16 + n / 256 % 16 = n / 256 := by omega
  have a3 : n / 256 * 16 + n / 16 % 16 = n / 16 := by omega
  have a4 : n / 16 * 16 + n % 16 = n := by omega
  rw [a1, a2, a3, a4]

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
    rw [hd, List.take_succ_cons, show e + (k + 1) = e + 1 + k by omega,
      show a ++ c :: (s.drop (e + 1)).take k = a ++ [c] ++ (s.drop (e + 1)).take k by simp]

theorem ok_congr {a b : PStr} {p q : Nat} (h1 : a = b) (h2 : p = q) :
    (.ok (a, (p : Int)) : DR (PStr × Int)) = .ok (b, (q : Int)) := by
  subst h1; subst h2; rfl

theorem uEsc_length (n : Nat) : (uEsc n).length = 6 := rfl

theorem join_ge (n m : Nat) : 0x10000 ≤ joinSurrogates n m := by
  unfold joinSurrogates; exact Nat.le_add_right _ _

/-- A `\X` escape of `py_scanstring`. -/
theorem loop_short (s : PStr) (strict : Bool) (b : Int) (f e x y : Nat) (a R : PStr)
    (hs : s.drop e = [92, x] ++ R) (hx : x ≠ 117) (hb : backslash x = some y) :
    pyScanLoop s strict b (f + 1) e a = pyScanLoop s strict b f (e + 2) (a ++ [y]) := by
  have hf : findTerm (s.drop e) = some 0 := by rw [hs]; simp [findTerm, isTerm]
  have h0 : s[e]? = some 92 := by
    have := congrArg (fun l => l[0]?) hs; simpa [List.getElem?_drop] using this
  have h1 : s[e + 1]? = some x := by
    have := congrArg (fun l => l[1]?) hs; simpa [List.getElem?_drop] using this
  simp [pyScanLoop, hf, List.getD_eq_getElem?_getD, h0, h1, hx, hb]

theorem uEsc_nth (n : Nat) (R : PStr) (s : PStr) (e : Nat) (hs : s.drop e = uEsc n ++ R) :
    s[e]? = some 92 ∧ s[e + 1]? = some 117 := by
  constructor
  · have := congrArg (fun l => l[0]?) hs; simpa [List.getElem?_drop, uEsc] using this
  · have := congrArg (fun l => l[1]?) hs; simpa [List.getElem?_drop, uEsc] using this

theorem drop_six {s : PStr} {e n : Nat} {R : PStr} (hs : s.drop e = uEsc n ++ R) : s.drop (e + 6) = R := by
  rw [← List.drop_drop, hs]
  simp [uEsc]

/-- A `\uXXXX` escape that is not joined with a following one. -/
theorem loop_u (s : PStr) (strict : Bool) (b : Int) (f e n : Nat) (a R : PStr)
    (hs : s.drop e = uEsc n ++ R) (hn : n < 0x10000)
    (hno : isHigh n = false ∨ R.take 2 ≠ [92, 117]) :
    pyScanLoop s strict b (f + 1) e a = pyScanLoop s strict b f (e + 6) (a ++ [n]) := by
  have hf : findTerm (s.drop e) = some 0 := by rw [hs]; simp [findTerm, isTerm, uEsc]
  obtain ⟨h0, h1⟩ := uEsc_nth n R s e hs
  have hx := hex4_uEsc s e n R hs hn
  have hd := drop_six hs
  have hc : ¬ (0xd800 ≤ n ∧ n ≤ 0xdbff ∧ (s.drop (e + 6)).take 2 = [92, 117]) := by
    rintro ⟨h2, h3, h4⟩
    rcases hno with h | h
    · simp [isHigh] at h; omega
    · rw [hd] at h4; exact h h4
  have e6 : e + 0 + 1 + 5 = e + 6 := by omega
  have e2 : e + 0 + 1 + 1 = e + 2 := by omega
  simp only [pyScanLoop, decodeUXXXX, hf, List.getD_eq_getElem?_getD]
  simp [h0, h1, e2, hx, e6, hc]

/-- Two `\uXXXX` escapes of a high and a low surrogate are joined. -/
theorem loop_pair (s : PStr) (strict : Bool) (b : Int) (f e n m : Nat) (a R : PStr)
    (hs : s.drop e = uEsc n ++ uEsc m ++ R) (hn : n < 0x10000) (hm : m < 0x10000)
    (hh : isHigh n = true) (hl : isLow m = true) :
    pyScanLoop s strict b (f + 1) e a = pyScanLoop s strict b f (e + 12) (a ++ [joinSurrogates n m]) := by
  have hs' : s.drop e = uEsc n ++ (uEsc m ++ R) := by rw [hs, List.append_assoc]
  have hf : findTerm (s.drop e) = some 0 := by rw [hs']; simp [findTerm, isTerm, uEsc]
  obtain ⟨h0, h1⟩ := uEsc_nth n _ s e hs'
  have hx := hex4_uEsc s e n _ hs' hn
  have hd := drop_six hs'
  have hx2 := hex4_uEsc s (e + 6) m R hd hm
  have ht : (s.drop (e + 6)).take 2 = [92, 117] := by rw [hd]; simp [uEsc]
  simp only [isHigh, isLow, Bool.and_eq_true, decide_eq_true_eq] at hh hl
  have e6 : e + 0 + 1 + 5 = e + 6 := by omega
  have e2 : e + 0 + 1 + 1 = e + 2 := by omega
  have e12 : e + 6 + 6 = e + 12 := by omega
  have e8 : e + 6 + 1 + 1 = e + 6 + 2 := rfl
  simp only [pyScanLoop, decodeUXXXX, hf, List.getD_eq_getElem?_getD]
  simp [h0, h1, e2, hx, e6, ht, hh, e8, hx2, hl, e12]

/-- The escape of one character with `ensure_ascii=True`. -/
def escA (c : Nat) : PStr :=
  if c = 92 ∨ c = 34 ∨ ¬(32 ≤ c ∧ c ≤ 126) then pyAsciiReplace c else [c]

/-- The escape of one character with `ensure_ascii=False`. -/
def escN (c : Nat) : PStr :=
  if c < 32 ∨ c = 92 ∨ c = 34 then (escDct c).getD [] else [c]

/-- What `py_scanstring` reads back with `ensure_ascii=True`: an escaped high
surrogate and an escaped low surrogate become one character. -/
def mergeSurr : PStr → PStr
  | [] => []
  | [a] => [a]
  | a :: b :: t =>
    if isHigh a = true ∧ isLow b = true then joinSurrogates a b :: mergeSurr t
    else a :: mergeSurr (b :: t)

/-- The ways one `ensure_ascii=True` escape starts. -/
inductive EscAForm (c : Nat) : Prop where
  | plain (h : escA c = [c]) (ht : isTerm c = false) (hp : c ≤ 126)
  | short (x y : Nat) (h : escA c = [92, x]) (hx : x ≠ 117) (hb : backslash x = some y) (hy : y = c)
  | u (h : escA c = uEsc c) (hn : c < 0x10000)
  | pair (n m : Nat) (h : escA c = uEsc n ++ uEsc m) (hn : n < 0x10000) (hm : m < 0x10000)
      (hh : isHigh n = true) (hl : isLow m = true) (hj : joinSurrogates n m = c)

theorem escA_form (c : Nat) (hc : c ≤ 0x10FFFF) : EscAForm c := by
  by_cases h92 : c = 92
  · subst h92; exact .short 92 92 (by decide) (by decide) (by decide) rfl
  by_cases h34 : c = 34
  · subst h34; exact .short 34 34 (by decide) (by decide) (by decide) rfl
  by_cases hp : 32 ≤ c ∧ c ≤ 126
  · refine .plain (by simp [escA, h92, h34, hp]) ?_ hp.2
    simp [isTerm, h92, h34]; omega
  have he : escA c = pyAsciiReplace c := by simp [escA, hp]
  by_cases h8 : c = 8
  · subst h8; exact .short 98 8 (by decide) (by decide) (by decide) rfl
  by_cases h12 : c = 12
  · subst h12; exact .short 102 12 (by decide) (by decide) (by decide) rfl
  by_cases h10 : c = 10
  · subst h10; exact .short 110 10 (by decide) (by decide) (by decide) rfl
  by_cases h13 : c = 13
  · subst h13; exact .short 114 13 (by decide) (by decide) (by decide) rfl
  by_cases h9 : c = 9
  · subst h9; exact .short 116 9 (by decide) (by decide) (by decide) rfl
  have hr : pyAsciiReplace c = if c < 32 then uEsc c else
      (if c < 0x10000 then uEsc c else
        uEsc (0xd800 ||| (((c - 0x10000) >>> 10) &&& 0x3ff)) ++ uEsc (0xdc00 ||| ((c - 0x10000) &&& 0x3ff))) := by
    by_cases h32 : c < 32 <;> simp [pyAsciiReplace, escDct, h92, h34, h8, h12, h10, h13, h9, h32]
  rw [hr] at he
  by_cases h32 : c < 32
  · simp only [h32, ↓reduceIte] at he
    exact .u he (by omega)
  simp only [h32, ↓reduceIte] at he
  by_cases hbmp : c < 0x10000
  · simp only [hbmp, ↓reduceIte] at he
    exact .u he hbmp
  simp only [hbmp, ↓reduceIte, Nat.shiftRight_eq_div_pow, and_3ff] at he
  have e1 : (c - 0x10000) / 2 ^ 10 % 1024 < 1024 := Nat.mod_lt _ (by decide)
  have e2 : (c - 0x10000) % 1024 < 1024 := Nat.mod_lt _ (by decide)
  rw [or_d800 e1, or_dc00 e2] at he
  simp only [Nat.reducePow] at he e1
  refine .pair _ _ he (by omega) (by omega) ?_ ?_ ?_
  · simp [isHigh]; omega
  · simp [isLow]; omega
  · have key : ∀ q r : Nat, joinSurrogates (0xd800 + q) (0xdc00 + r) = 0x10000 + (q * 1024 + r) := by
      intro q r
      unfold joinSurrogates
      rw [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]
    rw [key]
    omega

end PyLean.JsonMod
