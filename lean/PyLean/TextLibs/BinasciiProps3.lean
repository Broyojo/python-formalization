import PyLean.TextLibs.BinasciiProps2

/-!
`hexlify` with a separator, uu, `b16` and the URL-safe alphabet, and what the argument conversions
do when they fail.
-/

namespace PyLean.TextLibs.Binascii

open PyLean

set_option linter.unusedSimpArgs false

/-! ### `hexlify` with a separator -/

theorem b2aHex_append (a b : List Nat) : b2aHex (a ++ b) = b2aHex a ++ b2aHex b := by
  induction a with
  | nil => rfl
  | cons x r ih => simp [b2aHex, ih]

theorem filter_hex {c : Nat} (hc : ∀ v, v < 16 → hexDigit v ≠ c) : ∀ l : List Nat,
    (∀ x ∈ l, x < 256) → (b2aHex l).filter (· != c) = b2aHex l := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons x r ih =>
    intro hb
    have h : x < 256 := hb x (by simp)
    have h1 := hc (x / 16) (by omega)
    have h2 := hc (x % 16) (by omega)
    simp [b2aHex, List.filter_cons, h1, h2, ih (fun y hy => hb y (by simp [hy]))]

theorem hexLeft_filter {c k : Nat} (hc : ∀ v, v < 16 → hexDigit v ≠ c) : ∀ (n : Nat) (l : List Nat),
    (∀ x ∈ l, x < 256) → (hexLeft c k n l).filter (· != c) = b2aHex l := by
  intro n
  induction n with
  | zero => intro l h; exact filter_hex hc l h
  | succ n ih =>
    intro l h
    have hd := ih (l.drop k) (fun x hx => h x (List.mem_of_mem_drop hx))
    have ht := filter_hex hc (l.take k) (fun x hx => h x (List.mem_of_mem_take hx))
    simp only [hexLeft, List.filter_append, ht, hd, List.filter_cons, bne_self_eq_false,
      Bool.false_eq_true, if_false, List.filter_nil, List.nil_append, List.append_nil]
    rw [← b2aHex_append, List.take_append_drop]

theorem hexRight_filter {c k : Nat} (hc : ∀ v, v < 16 → hexDigit v ≠ c) : ∀ (n : Nat) (l : List Nat),
    (∀ x ∈ l, x < 256) → (hexRight c k n l).filter (· != c) = b2aHex l := by
  intro n
  induction n with
  | zero => intro l h; exact filter_hex hc l h
  | succ n ih =>
    intro l h
    have hd := ih (l.take (l.length - k)) (fun x hx => h x (List.mem_of_mem_take hx))
    have ht := filter_hex hc (l.drop (l.length - k)) (fun x hx => h x (List.mem_of_mem_drop hx))
    simp only [hexRight, List.filter_append, ht, hd, List.filter_cons, bne_self_eq_false,
      Bool.false_eq_true, if_false, List.filter_nil, List.nil_append, List.append_nil]
    rw [← b2aHex_append, List.take_append_drop]

theorem hexLeft_length (c k : Nat) : ∀ (n : Nat) (l : List Nat), n * k ≤ l.length →
    (hexLeft c k n l).length = 2 * l.length + n := by
  intro n
  induction n with
  | zero => intro l _; simp [hexLeft, b2aHex_length]
  | succ n ih =>
    intro l h
    rw [Nat.succ_mul] at h
    have hd := ih (l.drop k) (by rw [List.length_drop]; omega)
    simp only [hexLeft, List.length_append, hd, b2aHex_length, List.length_take, List.length_drop,
      List.length_cons, List.length_nil]
    omega

theorem hexRight_length (c k : Nat) : ∀ (n : Nat) (l : List Nat), n * k ≤ l.length →
    (hexRight c k n l).length = 2 * l.length + n := by
  intro n
  induction n with
  | zero => intro l _; simp [hexRight, b2aHex_length]
  | succ n ih =>
    intro l h
    rw [Nat.succ_mul] at h
    have hd := ih (l.take (l.length - k)) (by rw [List.length_take]; omega)
    simp only [hexRight, List.length_append, hd, b2aHex_length, List.length_take, List.length_drop,
      List.length_cons, List.length_nil]
    omega

/-- `hexlify(data, sep, group)` with a real group: taking the separators out gives plain hexadecimal,
`(n - 1) / |group|` of them are inserted, and the sign of `group` picks the end the groups count
from. The hypotheses are that `data` holds bytes and that `sep` is not itself a hex digit, without
which removing it would remove digits too. -/
def HexSepLaw : Prop :=
  ∀ (data : List Nat) (c : Nat) (g : Int), (∀ x ∈ data, x < 256) → (∀ v, v < 16 → hexDigit v ≠ c) →
    g ≠ 0 → g.natAbs < data.length →
    ∃ out, strhexBytes data (.bytes [c]) g = .ok out ∧
      out.filter (· != c) = b2aHex data ∧
      out.length = 2 * data.length + (data.length - 1) / g.natAbs ∧
      (g < 0 → ∃ rest, out = b2aHex (data.take g.natAbs) ++ [c] ++ rest) ∧
      (0 < g → ∃ rest, out = rest ++ [c] ++ b2aHex (data.drop (data.length - g.natAbs)))

theorem hexSepLaw_proven : HexSepLaw := by
  intro data c g hb hc h0 hk
  have hkpos : 0 < g.natAbs := by omega
  have hchunk : (data.length - 1) / g.natAbs * g.natAbs ≤ data.length :=
    Nat.le_trans (Nat.div_mul_le_self _ _) (by omega)
  have hone : 1 ≤ (data.length - 1) / g.natAbs := by
    rw [Nat.le_div_iff_mul_le hkpos]
    omega
  have hn : ¬(g = 0 ∨ g.natAbs ≥ data.length) := by omega
  by_cases hneg : g < 0
  · refine ⟨hexLeft c g.natAbs ((data.length - 1) / g.natAbs) data, ?_, hexLeft_filter hc _ _ hb,
      hexLeft_length _ _ _ _ hchunk, fun _ => ?_, fun h => absurd h (by omega)⟩
    · simp [strhexBytes, strhexSep, hn, hneg, bind, Except.bind, pure, Except.pure]
    · obtain ⟨m, hm⟩ : ∃ m, (data.length - 1) / g.natAbs = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hone).symm⟩
      rw [hm]
      exact ⟨_, rfl⟩
  · refine ⟨hexRight c g.natAbs ((data.length - 1) / g.natAbs) data, ?_, hexRight_filter hc _ _ hb,
      hexRight_length _ _ _ _ hchunk, fun h => absurd h hneg, fun _ => ?_⟩
    · simp [strhexBytes, strhexSep, hn, hneg, bind, Except.bind, pure, Except.pure]
    · obtain ⟨m, hm⟩ : ∃ m, (data.length - 1) / g.natAbs = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hone).symm⟩
      rw [hm]
      exact ⟨_, rfl⟩

/-- No separator is inserted without a `sep`, for `bytes_per_sep = 0`, or for a group at least as long
as the data; `hexlify` is then the plain one, whose `unhexlify` round trip is proved. -/
def HexNoSep : Prop :=
  ∀ (data : List Nat) (sep : SepArg) (c : Nat) (g : Int),
    strhexBytes data .absent g = .ok (b2aHex data) ∧
    (sep = .bytes [c] → g = 0 → strhexBytes data sep g = .ok (b2aHex data)) ∧
    (sep = .bytes [c] → g.natAbs ≥ data.length → strhexBytes data sep g = .ok (b2aHex data))

theorem hexNoSep_proven : HexNoSep := by
  intro data sep c g
  refine ⟨rfl, fun h h2 => ?_, fun h h2 => ?_⟩ <;>
    subst h <;> simp [strhexBytes, strhexSep, *, bind, Except.bind, pure, Except.pure]

/-- What `sep` may be, in the order of the checks: the length comes first and may raise, then the
type. With `hexlify` returning `bytes`, a non-ASCII `bytes` or Latin-1 `str` separator passes, which
`bytes.hex` would refuse. -/
def HexSepChecks : Prop :=
  ∀ (e : PyExc) (c : Nat) (l : List Nat),
    strhexSep (.lenRaises e) = .error e ∧
    strhexSep (.seqlen 1) = .error (.typeError "sep must be str or bytes.") ∧
    strhexSep (.bytes [c]) = .ok (some c) ∧
    (l.length ≠ 1 → strhexSep (.bytes l) = .error (.valueError "sep must be length 1.") ∧
      strhexSep (.str l) = .error (.valueError "sep must be length 1.")) ∧
    (c < 256 → strhexSep (.str [c]) = .ok (some c)) ∧
    (256 ≤ c → strhexSep (.str [c]) = .error (.valueError "sep must be ASCII."))

theorem hexSepChecks_proven : HexSepChecks := by
  intro e c l
  refine ⟨rfl, rfl, rfl, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · match l, h with
    | [], _ => exact ⟨rfl, rfl⟩
    | [x], h => exact absurd rfl h
    | _ :: _ :: _, _ => exact ⟨rfl, rfl⟩
  · simp [strhexSep, h]
  · have : ¬(c < 256) := by omega
    simp [strhexSep, this]

/-! ### uu -/

theorem uu_char (bt : Bool) (v : Nat) (h : v < 64) :
    let c := uuChar bt v
    c ≠ 10 ∧ c ≠ 13 ∧ ¬(c < 32 ∨ c > 96) ∧ (c - 32) % 64 = v := by
  cases bt <;> by_cases h0 : v = 0 <;> simp [uuChar, h0] <;> omega

/-- One encoded character in the decoder's loop. -/
theorem a2bUu_step (f n left bits v : Nat) (bt : Bool) (rest : List Nat) (hn : n ≠ 0) (hv : v < 64) :
    a2bUuLoop (f + 1) n left bits (uuChar bt v :: rest) =
      if bits + 6 ≥ 8 then
        match a2bUuLoop f (n - 1) ((left * 64 + v) % 2 ^ (bits + 6 - 8)) (bits + 6 - 8) rest with
        | .error e => .error e
        | .ok (out, r) => .ok ((left * 64 + v) / 2 ^ (bits + 6 - 8) % 256 :: out, r)
      else a2bUuLoop f n (left * 64 + v) (bits + 6) rest := by
  obtain ⟨h1, h2, h3, h4⟩ := uu_char bt v hv
  simp only [a2bUuLoop, hn, if_false]
  rw [if_neg (by omega), if_neg h3, h4]
  dsimp only
  by_cases h5 : bits + 6 ≥ 8
  · simp only [if_pos h5, List.drop_succ_cons, List.drop_zero]
    cases a2bUuLoop f (n - 1) ((left * 64 + v) % 2 ^ (bits + 6 - 8)) (bits + 6 - 8) rest with
    | error e => rfl
    | ok x => rfl
  · simp only [if_neg h5, List.drop_succ_cons, List.drop_zero]

theorem a2bUu_0 (f n v : Nat) (bt : Bool) (rest : List Nat) (hn : n ≠ 0) (hv : v < 64) :
    a2bUuLoop (f + 1) n 0 0 (uuChar bt v :: rest) = a2bUuLoop f n v 6 rest := by
  rw [a2bUu_step _ _ _ _ _ _ _ hn hv]
  simp

theorem a2bUu_6 (f n left v : Nat) (bt : Bool) (rest : List Nat) (hn : n ≠ 0) (hv : v < 64) :
    a2bUuLoop (f + 1) n left 6 (uuChar bt v :: rest) =
      match a2bUuLoop f (n - 1) ((left * 64 + v) % 16) 4 rest with
      | .error e => .error e
      | .ok (out, r) => .ok ((left * 64 + v) / 16 % 256 :: out, r) := by
  rw [a2bUu_step _ _ _ _ _ _ _ hn hv]
  simp

theorem a2bUu_4 (f n left v : Nat) (bt : Bool) (rest : List Nat) (hn : n ≠ 0) (hv : v < 64) :
    a2bUuLoop (f + 1) n left 4 (uuChar bt v :: rest) =
      match a2bUuLoop f (n - 1) ((left * 64 + v) % 4) 2 rest with
      | .error e => .error e
      | .ok (out, r) => .ok ((left * 64 + v) / 4 % 256 :: out, r) := by
  rw [a2bUu_step _ _ _ _ _ _ _ hn hv]
  simp

theorem a2bUu_2 (f n left v : Nat) (bt : Bool) (rest : List Nat) (hn : n ≠ 0) (hv : v < 64) :
    a2bUuLoop (f + 1) n left 2 (uuChar bt v :: rest) =
      match a2bUuLoop f (n - 1) 0 0 rest with
      | .error e => .error e
      | .ok (out, r) => .ok ((left * 64 + v) % 256 :: out, r) := by
  rw [a2bUu_step _ _ _ _ _ _ _ hn hv]
  simp [Nat.mod_one]

theorem a2bUu_done (f left bits : Nat) (rest : List Nat) :
    a2bUuLoop (f + 1) 0 left bits rest = .ok ([], rest) := by
  simp [a2bUuLoop]

/-- Three bytes come back from four characters. -/
theorem a2bUu_group (f n a b c : Nat) (bt : Bool) (rest : List Nat) (hn : n ≥ 3) (ha : a < 256)
    (hb : b < 256) (hc : c < 256) :
    a2bUuLoop (f + 4) n 0 0 (uuChar bt (a / 4) :: uuChar bt (a % 4 * 16 + b / 16) ::
        uuChar bt (b % 16 * 4 + c / 64) :: uuChar bt (c % 64) :: rest) =
      match a2bUuLoop f (n - 3) 0 0 rest with
      | .error e => .error e
      | .ok (out, r) => .ok (a :: b :: c :: out, r) := by
  have e1 : (a / 4 * 64 + (a % 4 * 16 + b / 16)) / 16 % 256 = a := by omega
  have e2 : (a / 4 * 64 + (a % 4 * 16 + b / 16)) % 16 = b / 16 := by omega
  have e3 : (b / 16 * 64 + (b % 16 * 4 + c / 64)) / 4 % 256 = b := by omega
  have e4 : (b / 16 * 64 + (b % 16 * 4 + c / 64)) % 4 = c / 64 := by omega
  have e5 : (c / 64 * 64 + c % 64) % 256 = c := by omega
  rw [a2bUu_0 _ _ _ _ _ (by omega) (by omega), a2bUu_6 _ _ _ _ _ _ (by omega) (by omega)]
  rw [e1, e2]
  rw [a2bUu_4 _ _ _ _ _ _ (by omega) (by omega)]
  rw [e3, e4]
  rw [a2bUu_2 _ _ _ _ _ _ (by omega) (by omega)]
  rw [e5, show n - 1 - 1 - 1 = n - 3 by omega]
  cases a2bUuLoop f (n - 3) 0 0 rest with
  | error e => rfl
  | ok v => rfl

theorem b2aUu_three (bt : Bool) (f a b c : Nat) (r : List Nat) (left : Nat) (ha : a < 256)
    (hb : b < 256) (hc : c < 256) :
    b2aUuLoop bt (f + 3) (a :: b :: c :: r) left 0 =
      uuChar bt (a / 4) :: uuChar bt (a % 4 * 16 + b / 16) :: uuChar bt (b % 16 * 4 + c / 64) ::
        uuChar bt (c % 64) :: b2aUuLoop bt f r (L c (L b (L a left))) 0 := by
  have h1 := L_low1 left a ha
  have h2 := L_low2 _ b a h1 hb
  have h3 := L_low3 _ c _ h2 hc
  have e1 : L a left / 4 % 64 = a / 4 := by omega
  have e2 : L b (L a left) / 16 % 64 = a % 4 * 16 + b / 16 := by omega
  have e3 : L c (L b (L a left)) / 64 % 64 = b % 16 * 4 + c / 64 := by omega
  have e4 : L c (L b (L a left)) / 1 % 64 = c % 64 := by omega
  have hp : b2aUuLoop bt (f + 3) (a :: b :: c :: r) left 0 =
      uuChar bt (L a left / 4 % 64) :: uuChar bt (L b (L a left) / 16 % 64) ::
        uuChar bt (L c (L b (L a left)) / 64 % 64) :: uuChar bt (L c (L b (L a left)) / 1 % 64) ::
        b2aUuLoop bt f r (L c (L b (L a left))) 0 := by
    simp [b2aUuLoop, uuDrain, L]
  rw [hp, e1, e2, e3, e4]

theorem uu_go (bt : Bool) : ∀ (m : Nat) (d : List Nat), d.length ≤ m → (∀ x ∈ d, x < 256) →
    ∀ (left f : Nat) (tail : List Nat), 2 * d.length + 2 ≤ f → uuTrailingOk tail = true →
    ∃ r, a2bUuLoop f d.length 0 0 (b2aUuLoop bt (d.length + 3) d left 0 ++ tail) = .ok (d, r) ∧
      uuTrailingOk r = true := by
  intro m
  induction m with
  | zero =>
    intro d hl _ left f tail hf ht
    have : d = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp at hf; omega⟩
    exact ⟨tail, by simp [b2aUuLoop, a2bUu_done], ht⟩
  | succ m ih =>
    intro d hl hb left f tail hf ht
    have hz : ∀ b : Bool, uuTrailingOk (uuChar b 0 :: uuChar b 0 :: tail) = true := by
      intro b
      cases b <;> simpa [uuTrailingOk, uuChar] using ht
    have hz1 : ∀ b : Bool, uuTrailingOk (uuChar b 0 :: tail) = true := by
      intro b
      cases b <;> simpa [uuTrailingOk, uuChar] using ht
    match d, hl, hb, hf with
    | [], _, _, hf =>
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp at hf; omega⟩
      exact ⟨tail, by simp [b2aUuLoop, a2bUu_done], ht⟩
    | [a], _, hb, hf =>
      have ha : a < 256 := hb a (by simp)
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 3 := ⟨f - 3, by simp at hf; omega⟩
      have he : b2aUuLoop bt ([a].length + 3) [a] left 0 ++ tail =
          uuChar bt (a / 4) :: uuChar bt (a % 4 * 16) :: uuChar bt 0 :: uuChar bt 0 :: tail := by
        have h1 := L_low1 left a ha
        have hp : b2aUuLoop bt 4 [a] left 0 =
            [uuChar bt (L a left / 4 % 64), uuChar bt (L 0 (L a left) / 16 % 64),
             uuChar bt (L 0 (L 0 (L a left)) / 64 % 64), uuChar bt (L 0 (L 0 (L a left)) / 1 % 64)] := by
          simp [b2aUuLoop, uuDrain, L]
        have e1 : L a left / 4 % 64 = a / 4 := by omega
        have e2 : L 0 (L a left) / 16 % 64 = a % 4 * 16 := by
          have := L_low2 _ 0 a h1 (by omega)
          omega
        have e3 : L 0 (L 0 (L a left)) / 64 % 64 = 0 := by
          have h2 := L_low2 _ 0 a h1 (by omega)
          have h3 := L_low3 _ 0 _ h2 (by omega)
          omega
        have e4 : L 0 (L 0 (L a left)) / 1 % 64 = 0 := by
          have h2 := L_low2 _ 0 a h1 (by omega)
          have h3 := L_low3 _ 0 _ h2 (by omega)
          omega
        show b2aUuLoop bt 4 [a] left 0 ++ tail = _
        rw [hp, e1, e2, e3, e4]
        rfl
      rw [he]
      show ∃ r, a2bUuLoop (g + 3) 1 0 0 _ = _ ∧ _
      rw [a2bUu_0 _ _ _ _ _ (by omega) (by omega), a2bUu_6 _ _ _ _ _ _ (by omega) (by omega)]
      refine ⟨uuChar bt 0 :: uuChar bt 0 :: tail, ?_, hz bt⟩
      rw [a2bUu_done, show (a / 4 * 64 + a % 4 * 16) / 16 % 256 = a by omega]
    | [a, b], _, hb, hf =>
      have ha : a < 256 := hb a (by simp)
      have hb' : b < 256 := hb b (by simp)
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 4 := ⟨f - 4, by simp at hf; omega⟩
      have he : b2aUuLoop bt ([a, b].length + 3) [a, b] left 0 ++ tail =
          uuChar bt (a / 4) :: uuChar bt (a % 4 * 16 + b / 16) :: uuChar bt (b % 16 * 4) ::
            uuChar bt 0 :: tail := by
        have h1 := L_low1 left a ha
        have h2 := L_low2 _ b a h1 hb'
        have h3 := L_low3 _ 0 _ h2 (by omega)
        have hp : b2aUuLoop bt 5 [a, b] left 0 =
            [uuChar bt (L a left / 4 % 64), uuChar bt (L b (L a left) / 16 % 64),
             uuChar bt (L 0 (L b (L a left)) / 64 % 64), uuChar bt (L 0 (L b (L a left)) / 1 % 64)] := by
          simp [b2aUuLoop, uuDrain, L]
        have e1 : L a left / 4 % 64 = a / 4 := by omega
        have e2 : L b (L a left) / 16 % 64 = a % 4 * 16 + b / 16 := by omega
        have e3 : L 0 (L b (L a left)) / 64 % 64 = b % 16 * 4 := by omega
        have e4 : L 0 (L b (L a left)) / 1 % 64 = 0 := by omega
        show b2aUuLoop bt 5 [a, b] left 0 ++ tail = _
        rw [hp, e1, e2, e3, e4]
        rfl
      rw [he]
      show ∃ r, a2bUuLoop (g + 4) 2 0 0 _ = _ ∧ _
      rw [a2bUu_0 _ _ _ _ _ (by omega) (by omega), a2bUu_6 _ _ _ _ _ _ (by omega) (by omega),
        a2bUu_4 _ _ _ _ _ _ (by omega) (by omega)]
      refine ⟨uuChar bt 0 :: tail, ?_, hz1 bt⟩
      rw [a2bUu_done, show (a / 4 * 64 + (a % 4 * 16 + b / 16)) % 16 = b / 16 by omega,
        show (a / 4 * 64 + (a % 4 * 16 + b / 16)) / 16 % 256 = a by omega,
        show (b / 16 * 64 + b % 16 * 4) / 4 % 256 = b by omega]
    | a :: b :: c :: r, hl, hb, hf =>
      have ha : a < 256 := hb a (by simp)
      have hb' : b < 256 := hb b (by simp)
      have hc : c < 256 := hb c (by simp)
      simp only [List.length_cons] at hf hl ⊢
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 4 := ⟨f - 4, by omega⟩
      obtain ⟨t, h1, h2⟩ := ih r (by omega) (fun x hx => hb x (by simp [hx]))
        (L c (L b (L a left))) g tail (by omega) ht
      refine ⟨t, ?_, h2⟩
      rw [show r.length + 1 + 1 + 1 + 3 = (r.length + 3) + 3 by omega,
        b2aUu_three bt _ a b c r left ha hb' hc]
      simp only [List.cons_append]
      rw [a2bUu_group g _ a b c bt _ (by omega) ha hb' hc,
        show r.length + 1 + 1 + 1 - 3 = r.length by omega, h1]

/-- `a2b_uu(b2a_uu(d, backtick=b)) == d` for all the data `b2a_uu` accepts, which is at most 45 bytes.
Both the space and the backtick spelling of zero come back. -/
def UuRoundTrip : Prop :=
  ∀ (d out : List Nat) (bt : Bool), (∀ x ∈ d, x < 256) → b2aUu d bt = .ok out → a2bUuBytes out = .ok d

theorem uuRoundTrip_proven : UuRoundTrip := by
  intro d out bt hb h
  unfold b2aUu at h
  split at h
  · cases h
  · rename_i hl
    simp only [Except.ok.injEq] at h
    subst h
    obtain ⟨r, h1, h2⟩ := uu_go bt d.length d (Nat.le_refl _) hb 0 (2 * d.length + 2) [10] (by omega)
      (by simp [uuTrailingOk])
    have hfirst : ((if (bt && d.isEmpty) = true then 96 else 32 + d.length) + 256 - 32) % 64 = d.length := by
      split
      · rename_i he
        have : d = [] := by simpa using (Bool.and_eq_true_iff.1 he).2
        subst this
        rfl
      · omega
    simp only [a2bUuBytes, List.cons_append]
    rw [hfirst, h1]
    simp [h2]

/-- The other half of `b2a_uu`: more than 45 bytes is an error, whatever the data. -/
def UuLimit : Prop :=
  ∀ (d : List Nat) (bt : Bool), d.length > 45 → b2aUu d bt = .error (err "At most 45 bytes at once")

theorem uuLimit_proven : UuLimit := by
  intro d bt h
  simp [b2aUu, h]

/-! ### `b16` -/

theorem upper_hex : ∀ v, v < 16 →
    digitValue (if 97 ≤ hexDigit v ∧ hexDigit v ≤ 122 then hexDigit v - 32 else hexDigit v) = v ∧
    ("0123456789ABCDEF".toList.map Char.toNat).contains
      (if 97 ≤ hexDigit v ∧ hexDigit v ≤ 122 then hexDigit v - 32 else hexDigit v) = true := by
  decide

/-- `b16decode(b16encode(d)) == d`, and only upper case digits are produced, so the default
`casefold=False` accepts the output. -/
def B16RoundTrip : Prop :=
  ∀ d : List Nat, (∀ x ∈ d, x < 256) → b16decode (.bytes (b16encode d)) false = .ok d

theorem b16RoundTrip_proven : B16RoundTrip := by
  intro d hd
  have hloop : ∀ d : List Nat, (∀ x ∈ d, x < 256) →
      a2bHexLoop (upper (b2aHex d)) = .ok d ∧
      (upper (b2aHex d)).any (fun c => !(("0123456789ABCDEF".toList.map Char.toNat).contains c)) = false := by
    intro d
    induction d with
    | nil => intro _; exact ⟨rfl, rfl⟩
    | cons b r ih =>
      intro hb
      have h : b < 256 := hb b (by simp)
      obtain ⟨t1, t2⟩ := upper_hex (b / 16) (by omega)
      obtain ⟨u1, u2⟩ := upper_hex (b % 16) (by omega)
      obtain ⟨i1, i2⟩ := ih (fun x hx => hb x (by simp [hx]))
      constructor
      · simp only [b2aHex, upper, List.map_cons, a2bHexLoop]
        rw [t1, u1, if_neg (by omega)]
        have := i1
        simp only [upper] at this
        rw [this]
        simp only [bind, Except.bind, pure, Except.pure]
        rw [show b / 16 * 16 + b % 16 = b by omega]
      · simp only [b2aHex, upper, List.map_cons, List.any_cons, t2, u2, Bool.not_true, Bool.false_or]
        exact i2
  obtain ⟨h1, h2⟩ := hloop d hd
  simp only [b16decode, b16encode, bytesFromDecodeData, bind, Except.bind, pure, Except.pure]
  simp only [Bool.false_eq_true, if_false, h2]
  simp only [a2bHex, asciiBuffer, bind, Except.bind, a2bHexBytes]
  rw [if_neg (by simp [upper, b2aHex_length])]
  exact h1

/-! ### The URL-safe alphabet -/

theorem b2aChar_ne (v : Nat) : b2aChar v ≠ 45 ∧ b2aChar v ≠ 95 := by
  unfold b2aChar
  repeat' split
  all_goals omega

theorem b2aDrain_ok (left : Nat) : ∀ (f bits : Nat), ∀ c ∈ (b2aDrain left f bits).1, c ≠ 45 ∧ c ≠ 95 := by
  intro f
  induction f with
  | zero => intro bits c h; simp [b2aDrain] at h
  | succ f ih =>
    intro bits c h
    simp only [b2aDrain] at h
    split at h
    · simp only [List.mem_cons] at h
      rcases h with h | h
      · rw [h]
        exact b2aChar_ne _
      · exact ih _ c h
    · simp at h

theorem b2aLoop_ok : ∀ (d : List Nat) (left bits : Nat), ∀ c ∈ (b2aLoop d left bits).1, c ≠ 45 ∧ c ≠ 95 := by
  intro d
  induction d with
  | nil => intro _ _ c h; simp [b2aLoop] at h
  | cons b r ih =>
    intro left bits c h
    simp only [b2aLoop, List.mem_append] at h
    rcases h with h | h
    · exact b2aDrain_ok _ _ _ c h
    · exact ih _ _ c h

theorem b2a_no_dash (d : List Nat) : ∀ c ∈ b2aBase64 d false, c ≠ 45 ∧ c ≠ 95 := by
  intro c h
  simp only [b2aBase64, Bool.false_eq_true, if_false, List.append_nil, List.mem_append] at h
  rcases h with h | h
  · exact b2aLoop_ok _ _ _ c h
  · split at h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h
      · rw [h]
        exact b2aChar_ne _
      · subst h
        decide
      · subst h
        decide
    · split at h
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with h | h
        · rw [h]
          exact b2aChar_ne _
        · subst h
          decide
      · simp at h

/-- One character of `translate`. -/
def tr (frm to : List Nat) (c : Nat) : Nat :=
  (((frm.zip to).reverse.find? (·.1 == c)).map (·.2)).getD c

theorem tr_back (x : Nat) (h1 : x ≠ 45) (h2 : x ≠ 95) :
    tr dashUnderscore plusSlash (tr plusSlash dashUnderscore x) = x := by
  have e1 : (plusSlash.zip dashUnderscore).reverse = [(47, 95), (43, 45)] := by decide
  have e2 : (dashUnderscore.zip plusSlash).reverse = [(95, 47), (45, 43)] := by decide
  by_cases h3 : x = 47
  · subst h3
    decide
  · by_cases h4 : x = 43
    · subst h4
      decide
    · have a1 : (47 == x) = false := beq_false_of_ne (Ne.symm h3)
      have a2 : (43 == x) = false := beq_false_of_ne (Ne.symm h4)
      have a3 : (95 == x) = false := beq_false_of_ne (Ne.symm h2)
      have a4 : (45 == x) = false := beq_false_of_ne (Ne.symm h1)
      have f1 : tr plusSlash dashUnderscore x = x := by
        simp only [tr, e1, List.find?_cons, a1, a2, List.find?_nil]
        rfl
      have f2 : tr dashUnderscore plusSlash x = x := by
        simp only [tr, e2, List.find?_cons, a3, a4, List.find?_nil]
        rfl
      rw [f1, f2]

theorem translate_back (s : List Nat) (h : ∀ c ∈ s, c ≠ 45 ∧ c ≠ 95) :
    translate dashUnderscore plusSlash (translate plusSlash dashUnderscore s) = s := by
  induction s with
  | nil => rfl
  | cons c r ih =>
    have hc := h c (by simp)
    have hr := ih (fun x hx => h x (by simp [hx]))
    have e : translate dashUnderscore plusSlash (translate plusSlash dashUnderscore (c :: r)) =
        tr dashUnderscore plusSlash (tr plusSlash dashUnderscore c) ::
          translate dashUnderscore plusSlash (translate plusSlash dashUnderscore r) := rfl
    rw [e, tr_back c hc.1 hc.2, hr]

/-- `urlsafe_b64decode(urlsafe_b64encode(d)) == d`. -/
def UrlsafeRoundTrip : Prop :=
  ∀ d : List Nat, (∀ x ∈ d, x < 256) → urlsafeDecode (.bytes (urlsafeEncode d)) = .ok d

theorem urlsafeRoundTrip_proven : UrlsafeRoundTrip := by
  intro d hd
  have h := base64RoundTrip_proven false d hd
  simp only [urlsafeDecode, urlsafeEncode, bytesFromDecodeData, bind, Except.bind, b64decode, a2bBase64,
    asciiBuffer]
  rw [translate_back _ (b2a_no_dash d)]
  exact h

/-! ### When a conversion fails -/

/-- The two buffer conversions of `binascii` differ. A `__buffer__` that raises passes through `y*`,
while `ascii_buffer_converter` replaces it with `TypeError`, and the decoders take an ASCII `str`,
which the encoders refuse. -/
def BufferConversions : Prop :=
  ∀ (t : String) (e : PyExc) (s : List Nat),
    bufData (.raises t e) = .error e ∧
    asciiBuffer (.raises t e) =
      .error (.typeError s!"argument should be bytes, buffer or ASCII string, not '{t}'") ∧
    asciiBuffer (.notBuffer t) =
      .error (.typeError s!"argument should be bytes, buffer or ASCII string, not '{t}'") ∧
    bufData (.notBuffer t) = .error (.typeError s!"a bytes-like object is required, not '{t}'") ∧
    bufData (.str s) = .error (.typeError "a bytes-like object is required, not 'str'")

theorem bufferConversions_proven : BufferConversions := by
  intro t e s
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- `_bytes_from_decode_data` only replaces a `TypeError` from `memoryview`: anything else raised by
`__buffer__` comes through. -/
def DecodeDataFails : Prop :=
  ∀ (t : String) (m : String) (e : PyExc), (∀ x, e ≠ .typeError x) →
    bytesFromDecodeData (.raises t (.typeError m)) =
      .error (.typeError s!"argument should be a bytes-like object or ASCII string, not '{t}'") ∧
    bytesFromDecodeData (.notBuffer t) =
      .error (.typeError s!"argument should be a bytes-like object or ASCII string, not '{t}'") ∧
    bytesFromDecodeData (.raises t e) = .error e

theorem decodeDataFails_proven : DecodeDataFails := by
  intro t m e h
  refine ⟨rfl, rfl, ?_⟩
  cases e with
  | typeError x => exact absurd rfl (h x)
  | _ => rfl

/-- The `bool` keywords run `__bool__`, after the data has been converted: a raising one passes
through, and it is not reached when the data fails. -/
def FlagOrder : Prop :=
  ∀ (d : Data) (e e2 : PyExc) (b : List Nat),
    (bufData d = .ok b → b2aBase64A d (.error e) = .error e ∧ b2aUuA d (.error e) = .error e) ∧
    (asciiBuffer d = .ok b → a2bBase64A d (.error e) = .error e) ∧
    (bufData d = .error e2 → b2aBase64A d (.error e) = .error e2 ∧ b2aUuA d (.error e) = .error e2)

theorem flagOrder_proven : FlagOrder := by
  intro d e e2 b
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · simp [b2aBase64A, b2aUuA, h, bind, Except.bind]
  · simp [a2bBase64A, h, bind, Except.bind]
  · simp [b2aBase64A, b2aUuA, h, bind, Except.bind]

end PyLean.TextLibs.Binascii
