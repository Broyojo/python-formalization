import PyLean.TextLibs.BinasciiProps
import PyLean.TextLibs.BinasciiRest

/-!
Properties of the rest of `Modules/binascii.c` and `Lib/base64.py`. The round trips of uu, qp,
base32 and the 85-based codecs hold on CPython over 200000 random inputs (see the registry
notes); those not yet proven stay `.open`.
-/

namespace PyLean.TextLibs.Binascii

open PyLean

set_option linter.unusedSimpArgs false

/-- An ASCII `str` and the equal `bytes` decode alike; any other `str` raises `ValueError`. -/
def AsciiBuffer : Prop :=
  ∀ s : List Nat,
    (s.all (· < 128) = true → asciiBuffer (.str s) = asciiBuffer (.bytes s)) ∧
    (s.all (· < 128) = false → asciiBuffer (.str s) =
      .error (.valueError "string argument should contain only ASCII characters"))

theorem asciiBuffer_proven : AsciiBuffer := by
  intro s
  constructor <;> intro h <;> simp [asciiBuffer, h]

/-- `crc_hqx` is incremental: `crc_hqx(a + b, c) == crc_hqx(b, crc_hqx(a, c))`. -/
def CrcIncremental : Prop :=
  ∀ (a b : List Nat) (c : Int), crcHqx (a ++ b) c = crcHqx b (crcHqx a c)

theorem crcEntry_lt (i : Nat) : crctabHqx.getD i 0 < 65536 := by
  have hall : ∀ v ∈ crctabHqx, v < 65536 := by decide +kernel
  rw [List.getD_eq_getElem?_getD]
  cases h : crctabHqx[i]? with
  | none => simp
  | some v =>
    simp only [Option.getD_some]
    exact hall v (List.mem_of_getElem? h)

theorem crcStep_lt (cr b : Nat) : crcStep cr b < 65536 := by
  unfold crcStep
  exact Nat.xor_lt_two_pow (n := 16) (by omega) (crcEntry_lt _)

theorem crcFold_lt (d : List Nat) : ∀ c, c < 65536 → d.foldl crcStep c < 65536 := by
  induction d with
  | nil => intro c h; exact h
  | cons b bs ih =>
    intro c _
    exact ih _ (crcStep_lt c b)

theorem crcIncremental_proven : CrcIncremental := by
  intro a b c
  have hmask : ∀ x : Nat, x < 65536 → ((x : Int) % 2 ^ 32).toNat % 65536 = x := by
    intro x hx
    have : (x : Int) % 2 ^ 32 = x := Int.emod_eq_of_lt (by omega) (by omega)
    rw [this]
    simp only [Int.toNat_natCast]
    exact Nat.mod_eq_of_lt hx
  have hlow : ((c % 2 ^ 32).toNat % 65536) < 65536 := Nat.mod_lt _ (by decide)
  simp only [crcHqx, List.foldl_append]
  rw [hmask _ (crcFold_lt a _ hlow)]

/-- The bitwise CRC-CCITT (polynomial `0x1021`) of a byte, MSB first. -/
def crcBit (crc : Nat) : (i : Nat) → Nat
  | 0 => crc
  | i + 1 =>
    let c := crc * 2
    crcBit (if c ≥ 65536 then (c - 65536) ^^^ 0x1021 else c) i

/-- `crctab_hqx` is the table of the CCITT polynomial: every entry is the bitwise CRC of its
index, so a corrupted table entry would be caught. -/
def CrcTableIsCcitt : Prop :=
  crctabHqx.length = 256 ∧ ∀ i < 256, crctabHqx.getD i 0 = crcBit (i * 256) 8

theorem crcTableIsCcitt_proven : CrcTableIsCcitt := by
  unfold CrcTableIsCcitt
  decide +kernel

/-- `to_hex` writes two hex digits that decode back to the byte. -/
def ToHexInverse : Prop :=
  ∀ ch < 256, (toHex ch).all isHexChar = true ∧ (toHex ch).length = 2 ∧
    digitValue ((toHex ch).getD 0 0) * 16 + digitValue ((toHex ch).getD 1 0) = ch

theorem toHexInverse_proven : ToHexInverse := by
  unfold ToHexInverse
  decide +kernel

/-- `a2b_qp` leaves text without `=` unchanged (with `header=False`). -/
def A2bQpPlain : Prop :=
  ∀ d : List Nat, (∀ c ∈ d, c ≠ 61) → a2bQp (.bytes d) false = .ok d

theorem a2bQpPlain_proven : A2bQpPlain := by
  intro d hd
  have hloop : ∀ (fuel : Nat) (d : List Nat), d.length < fuel → (∀ c ∈ d, c ≠ 61) →
      a2bQpLoop false fuel d = d := by
    intro fuel
    induction fuel with
    | zero => intro d h; omega
    | succ fuel ih =>
      intro d hl hd
      match d, hl, hd with
      | [], _, _ => rfl
      | c :: r, hl, hd =>
        have hc : c ≠ 61 := hd c (by simp)
        have hr := ih r (by simp at hl; omega) (fun x hx => hd x (by simp [hx]))
        simp [a2bQpLoop, hc, hr]
  simp only [a2bQp, asciiBuffer, bind, Except.bind, pure, Except.pure]
  rw [hloop _ _ (by omega) hd]

/-- Split at `\n`. -/
def linesOf : List Nat → List (List Nat)
  | [] => [[]]
  | 10 :: r => [] :: linesOf r
  | c :: r =>
    match linesOf r with
    | l :: ls => (c :: l) :: ls
    | [] => [[c]]

/-- `b2a_qp` keeps every line of its output to `MAXLINESIZE`, 76 characters, the limit its own
source names and RFC 2045 requires. -/
def QpLineLimit : Prop :=
  ∀ (d : List Nat) (o : QpOpts), ∀ l ∈ linesOf (b2aQp d o), (l.filter (· != 13)).length ≤ MAXLINESIZE

theorem qpLineLimit_refuted : ¬QpLineLimit := by
  intro h
  have := h (List.replicate 74 97 ++ [32, 10]) ⟨false, true, false⟩
    (List.replicate 74 97 ++ [61, 50, 48]) (by decide +kernel)
  revert this
  decide +kernel

/-! ### `base64.py` -/

/-- The `standard_` names round-trip like `b64encode`. -/
def StandardRoundTrip : Prop :=
  ∀ (d out : List Nat), (∀ x ∈ d, x < 256) → standardB64encode d = .ok out →
    standardB64decode (.bytes out) = .ok d

theorem standardRoundTrip_proven : StandardRoundTrip := by
  intro d out hd h
  exact b64ModuleRoundTrip_proven false d out hd h

/-- `_input_type_check` accepts exactly one-dimensional views of single-byte formats. -/
def InputTypeCheck : Prop :=
  ∀ (f : String) (n : Nat) (c : String),
    (inputTypeCheck (.view f n c)).toBool = ((f == "c" || f == "b" || f == "B") && n == 1)

theorem inputTypeCheck_proven : InputTypeCheck := by
  intro f n c
  by_cases h : (f == "c" || f == "b" || f == "B") = true
  · by_cases hn : n = 1
    · simp [inputTypeCheck, h, hn, Except.toBool]
    · simp [inputTypeCheck, h, hn, Except.toBool]
  · have h' : (f == "c" || f == "b" || f == "B") = false := by simpa using h
    simp [inputTypeCheck, h', Except.toBool]

/-- `main` runs the function of the last `-e`, `-d` or `-u`, encoding by default, and `-h` stops. -/
def MainLastFlagWins : Prop :=
  ∀ (fl : List Char) (f : Option Bool),
    (mainSelect (fl ++ ['e']) f = some true ∨ 'h' ∈ fl) ∧
    (mainSelect (fl ++ ['d']) f = some false ∨ 'h' ∈ fl)

theorem mainLastFlagWins_proven : MainLastFlagWins := by
  intro fl
  induction fl with
  | nil => intro f; exact ⟨.inl rfl, .inl rfl⟩
  | cons c cs ih =>
    intro f
    unfold mainSelect
    by_cases hh : c = 'h'
    · subst hh
      simp
    · by_cases he : c = 'e'
      · subst he
        have := ih (some true)
        simpa using this
      · have := ih (some false)
        have hh' : 'h' ≠ c := Ne.symm hh
        simp [mainSelect, hh, he, hh']
        exact this

end PyLean.TextLibs.Binascii
