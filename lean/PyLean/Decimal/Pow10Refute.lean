import PyLean.Decimal.DivisionProps

/-!
`_is_less_than_pow10a_use_str` (new in 3.15) answers `q < 10**a` wrongly when the rounded
`1 + a * _LOG_10_BASE_2_HI` lands on the integer just above `a * log2(10)`. Its comment's
claim, "If z > log2(10) and q.bit_length() >= 1 + a*z, then q > 10**a", holds for the real
product, but Python compares with the product rounded to a double.

The smallest such `a` is 355861594 (exhaustive over `a <= 4*10**9`, scratch search recorded
in `bugs/decimal-pydecimal-pow10-float-misfire.yaml`): `355861594 * log2(10)` is
`1182146627 + 1.56e-8`, and `1 + 355861594 * _LOG_10_BASE_2_HI` rounds to exactly
`1182146628.0`. Every `q` with `2**1182146627 <= q < 10**355861594` has bit length
1182146628 and fewer than 355861595 digits, and the helper calls it too large.

The counterexample quotient is `10^355861603 // 1000000001`, the integer part of
`Decimal('1E+355861594') / Decimal('1.000000001')`.
-/

namespace PyLean.Decimal

open PyLean

theorem pow10_lo_false :
    intLtF 1182146628 (Binary64.F64.mul (Binary64.F64.ofInt ((355861594 : Nat) : Int)) log10Base2Lo) = false := by
  decide +kernel

theorem pow10_hi_true :
    intGeF 1182146628 (Binary64.F64.add Binary64.F64.one
        (Binary64.F64.mul (Binary64.F64.ofInt ((355861594 : Nat) : Int)) log10Base2Hi)) = true := by
  decide +kernel

theorem pow10_fa_finite : (Binary64.F64.ofInt ((355861594 : Nat) : Int)).isInf = false := by
  decide +kernel

/-- At `a = 355861594`, every `q` of bit length 1182146628 is called too large. -/
theorem pow10_hi_fires (q : Nat) (hb : bitLen q = 1182146628) :
    isLessThanPow10aUseStr q 355861594 = .ok (false, false) := by
  unfold isLessThanPow10aUseStr
  simp only
  rw [hb, pow10_fa_finite, pow10_lo_false, pow10_hi_true]
  rfl

/-! ### Certified bounds on `2^n / 10^k`

`10^355861603` has about 1.18e9 bits, past what the kernel will hold as a numeral, so the
two inequalities below are proven by interval arithmetic on 128-bit mantissas: `CertLo k m a`
says `10^k ≥ 2^m · a / 2^128`, `CertHi k m b` says `10^k ≤ 2^m · b / 2^128`, and they are
built up from `10 = 2^4 · (5·2^125) / 2^128` by squaring and multiplying, rounding the
mantissa down (`CertLo`) or up (`CertHi`) at each step. Every step's side condition is a
comparison of numbers below 2^257. -/

@[irreducible] def CertLo (k m a : Nat) : Prop := 2 ^ m * a ≤ 10 ^ k * 2 ^ 128
@[irreducible] def CertHi (k m b : Nat) : Prop := 10 ^ k * 2 ^ 128 ≤ 2 ^ m * b

theorem certLo_mul {k1 m1 a1 k2 m2 a2 k m a : Nat} (h1 : CertLo k1 m1 a1) (h2 : CertLo k2 m2 a2)
    (hk : k1 + k2 = k) (hm : m1 + m2 = m) (h : a * 2 ^ 128 ≤ a1 * a2) : CertLo k m a := by
  subst hk hm
  unfold CertLo at *
  have hp : 0 < 2 ^ 128 := Nat.pow_pos (by decide)
  apply Nat.le_of_mul_le_mul_right _ hp
  calc 2 ^ (m1 + m2) * a * 2 ^ 128 = 2 ^ m1 * 2 ^ m2 * (a * 2 ^ 128) := by
        rw [Nat.pow_add, Nat.mul_assoc]
    _ ≤ 2 ^ m1 * 2 ^ m2 * (a1 * a2) := Nat.mul_le_mul_left _ h
    _ = (2 ^ m1 * a1) * (2 ^ m2 * a2) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ (10 ^ k1 * 2 ^ 128) * (10 ^ k2 * 2 ^ 128) := Nat.mul_le_mul h1 h2
    _ = 10 ^ (k1 + k2) * 2 ^ 128 * 2 ^ 128 := by
        rw [Nat.pow_add]; simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem certHi_mul {k1 m1 b1 k2 m2 b2 k m b : Nat} (h1 : CertHi k1 m1 b1) (h2 : CertHi k2 m2 b2)
    (hk : k1 + k2 = k) (hm : m1 + m2 = m) (h : b1 * b2 ≤ b * 2 ^ 128) : CertHi k m b := by
  subst hk hm
  unfold CertHi at *
  have hp : 0 < 2 ^ 128 := Nat.pow_pos (by decide)
  apply Nat.le_of_mul_le_mul_right _ hp
  calc 10 ^ (k1 + k2) * 2 ^ 128 * 2 ^ 128 = (10 ^ k1 * 2 ^ 128) * (10 ^ k2 * 2 ^ 128) := by
        rw [Nat.pow_add]; simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ (2 ^ m1 * b1) * (2 ^ m2 * b2) := Nat.mul_le_mul h1 h2
    _ = 2 ^ m1 * 2 ^ m2 * (b1 * b2) := by
        simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ 2 ^ m1 * 2 ^ m2 * (b * 2 ^ 128) := Nat.mul_le_mul_left _ h
    _ = 2 ^ (m1 + m2) * b * 2 ^ 128 := by
        rw [Nat.pow_add]; simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem two_pow_succ_mul (m a : Nat) : 2 ^ (m + 1) * a = 2 ^ m * (2 * a) := by
  rw [Nat.pow_succ, Nat.mul_comm (2 ^ m) 2, Nat.mul_assoc, Nat.mul_left_comm]

theorem certLo_unshift {k m m' a a' : Nat} (h : CertLo k m a) (hm : m' + 1 = m) (ha : 2 * a = a') :
    CertLo k m' a' := by
  subst hm ha
  unfold CertLo at *
  rw [← two_pow_succ_mul]
  exact h

theorem certHi_unshift {k m m' b b' : Nat} (h : CertHi k m b) (hm : m' + 1 = m) (hb : 2 * b = b') :
    CertHi k m' b' := by
  subst hm hb
  unfold CertHi at *
  rw [← two_pow_succ_mul]
  exact h

theorem certLo_final {K m a N M d : Nat} (h : CertLo K m a) (hm : N + d = m)
    (hc : M * 2 ^ 128 ≤ 2 ^ d * a) : 2 ^ N * M ≤ 10 ^ K := by
  subst hm
  unfold CertLo at h
  have hp : 0 < 2 ^ 128 := Nat.pow_pos (by decide)
  apply Nat.le_of_mul_le_mul_right _ hp
  calc 2 ^ N * M * 2 ^ 128 = 2 ^ N * (M * 2 ^ 128) := Nat.mul_assoc _ _ _
    _ ≤ 2 ^ N * (2 ^ d * a) := Nat.mul_le_mul_left _ hc
    _ = 2 ^ (N + d) * a := by rw [Nat.pow_add, Nat.mul_assoc]
    _ ≤ 10 ^ K * 2 ^ 128 := h

theorem certHi_final {K m b N M d : Nat} (h : CertHi K m b) (hm : N + d = m)
    (hc : 2 ^ d * b < M * 2 ^ 128) : 10 ^ K < 2 ^ N * M := by
  subst hm
  unfold CertHi at h
  apply Nat.lt_of_mul_lt_mul_right (a := 2 ^ 128)
  calc 10 ^ K * 2 ^ 128 ≤ 2 ^ (N + d) * b := h
    _ = 2 ^ N * (2 ^ d * b) := by rw [Nat.pow_add, Nat.mul_assoc]
    _ < 2 ^ N * (M * 2 ^ 128) := Nat.mul_lt_mul_of_pos_left hc (Nat.pow_pos (by decide))
    _ = 2 ^ N * M * 2 ^ 128 := (Nat.mul_assoc _ _ _).symm

theorem pow10_cert_lo : 2 ^ 1182146627 * 1000000001 ≤ 10 ^ 355861603 := by
  have l1 : CertLo 1 4 212676479325586539664609129644855132160 := by unfold CertLo; decide
  have l2 : CertLo 2 8 132922799578491587290380706028034457600 := certLo_mul l1 l1 rfl rfl (by decide)
  have l3 : CertLo 2 7 265845599156983174580761412056068915200 := certLo_unshift l2 rfl rfl
  have l4 : CertLo 4 14 207691874341393105141219853168803840000 := certLo_mul l3 l3 rfl rfl (by decide)
  have l5 : CertLo 5 18 129807421463370690713262408230502400000 := certLo_mul l4 l1 rfl rfl (by decide)
  have l6 : CertLo 5 17 259614842926741381426524816461004800000 := certLo_unshift l5 rfl rfl
  have l7 : CertLo 10 34 198070406285660843983859875840000000000 := certLo_mul l6 l6 rfl rfl (by decide)
  have l8 : CertLo 20 68 115292150460684697600000000000000000000 := certLo_mul l7 l7 rfl rfl (by decide)
  have l9 : CertLo 20 67 230584300921369395200000000000000000000 := certLo_unshift l8 rfl rfl
  have l10 : CertLo 21 71 144115188075855872000000000000000000000 := certLo_mul l9 l1 rfl rfl (by decide)
  have l11 : CertLo 21 70 288230376151711744000000000000000000000 := certLo_unshift l10 rfl rfl
  have l12 : CertLo 42 140 244140625000000000000000000000000000000 := certLo_mul l11 l11 rfl rfl (by decide)
  have l13 : CertLo 84 280 175162308040602133865466197911239516410 := certLo_mul l12 l12 rfl rfl (by decide)
  have l14 : CertLo 168 560 90165806814313825983973933227508139041 := certLo_mul l13 l13 rfl rfl (by decide)
  have l15 : CertLo 168 559 180331613628627651967947866455016278082 := certLo_unshift l14 rfl rfl
  have l16 : CertLo 169 563 112707258517892282479967416534385173801 := certLo_mul l15 l1 rfl rfl (by decide)
  have l17 : CertLo 169 562 225414517035784564959934833068770347602 := certLo_unshift l16 rfl rfl
  have l18 : CertLo 338 1124 149322178960515020638414327155810747136 := certLo_mul l17 l17 rfl rfl (by decide)
  have l19 : CertLo 338 1123 298644357921030041276828654311621494272 := certLo_unshift l18 rfl rfl
  have l20 : CertLo 339 1127 186652723700643775798017908944763433920 := certLo_mul l19 l1 rfl rfl (by decide)
  have l21 : CertLo 678 2254 102383322356998443835244950704729869730 := certLo_mul l20 l20 rfl rfl (by decide)
  have l22 : CertLo 678 2253 204766644713996887670489901409459739460 := certLo_unshift l21 rfl rfl
  have l23 : CertLo 1356 4506 123219369745274348119219197929906801684 := certLo_mul l22 l22 rfl rfl (by decide)
  have l24 : CertLo 1356 4505 246438739490548696238438395859813603368 := certLo_unshift l23 rfl rfl
  have l25 : CertLo 1357 4509 154024212181592935149023997412383502105 := certLo_mul l24 l1 rfl rfl (by decide)
  have l26 : CertLo 1357 4508 308048424363185870298047994824767004210 := certLo_unshift l25 rfl rfl
  have l27 : CertLo 2714 9016 278867907882776574634073210811051957269 := certLo_mul l26 l26 rfl rfl (by decide)
  have l28 : CertLo 2715 9020 174292442426735359146295756756907473293 := certLo_mul l27 l1 rfl rfl (by decide)
  have l29 : CertLo 5430 18040 89272493787886694634810681920458300186 := certLo_mul l28 l28 rfl rfl (by decide)
  have l30 : CertLo 5430 18039 178544987575773389269621363840916600372 := certLo_unshift l29 rfl rfl
  have l31 : CertLo 10860 36078 93681940903625229952834771944590615679 := certLo_mul l30 l30 rfl rfl (by decide)
  have l32 : CertLo 10860 36077 187363881807250459905669543889181231358 := certLo_unshift l31 rfl rfl
  have l33 : CertLo 21720 72154 103164981845908289003661943603398982149 := certLo_mul l32 l32 rfl rfl (by decide)
  have l34 : CertLo 21720 72153 206329963691816578007323887206797964298 := certLo_unshift l33 rfl rfl
  have l35 : CertLo 43440 144306 125108022206033320067251456023865807866 := certLo_mul l34 l34 rfl rfl (by decide)
  have l36 : CertLo 43440 144305 250216044412066640134502912047731615732 := certLo_unshift l35 rfl rfl
  have l37 : CertLo 86880 288610 183988578214420746010250932491266220789 := certLo_mul l36 l36 rfl rfl (by decide)
  have l38 : CertLo 173760 577220 99481490092106887847826058549354872207 := certLo_mul l37 l37 rfl rfl (by decide)
  have l39 : CertLo 173760 577219 198962980184213775695652117098709744414 := certLo_unshift l38 rfl rfl
  have l40 : CertLo 347520 1154438 116333584493319794950488727069929251697 := certLo_mul l39 l39 rfl rfl (by decide)
  have l41 : CertLo 347520 1154437 232667168986639589900977454139858503394 := certLo_unshift l40 rfl rfl
  have l42 : CertLo 347521 1154441 145416980616649743688110908837411564621 := certLo_mul l41 l1 rfl rfl (by decide)
  have l43 : CertLo 347521 1154440 290833961233299487376221817674823129242 := certLo_unshift l42 rfl rfl
  have l44 : CertLo 695042 2308880 248571190367630096241289165620596054019 := certLo_mul l43 l43 rfl rfl (by decide)
  have l45 : CertLo 1390084 4617760 181577544672293880048491403959805141423 := certLo_mul l44 l44 rfl rfl (by decide)
  have l46 : CertLo 2780168 9235520 96891311258803062128752039558460073235 := certLo_mul l45 l45 rfl rfl (by decide)
  have l47 : CertLo 2780168 9235519 193782622517606124257504079116920146470 := certLo_unshift l46 rfl rfl
  have l48 : CertLo 5560336 18471038 110354542110393359802605984560731595390 := certLo_mul l47 l47 rfl rfl (by decide)
  have l49 : CertLo 5560336 18471037 220709084220786719605211969121463190780 := certLo_unshift l48 rfl rfl
  have l50 : CertLo 5560337 18471041 137943177637991699753257480700914494237 := certLo_mul l49 l1 rfl rfl (by decide)
  have l51 : CertLo 5560337 18471040 275886355275983399506514961401828988474 := certLo_unshift l50 rfl rfl
  have l52 : CertLo 11120674 36942080 223676829675839086833148032435327304545 := certLo_mul l51 l51 rfl rfl (by decide)
  have l53 : CertLo 11120675 36942084 139798018547399429270717520272079565340 := certLo_mul l52 l1 rfl rfl (by decide)
  have l54 : CertLo 11120675 36942083 279596037094798858541435040544159130680 := certLo_unshift l53 rfl rfl
  have l55 : CertLo 22241350 73884166 229732573763597775854980380061247279927 := certLo_mul l54 l54 rfl rfl (by decide)
  have l56 : CertLo 44482700 147768332 155097826330534387092552823132641429427 := certLo_mul l55 l55 rfl rfl (by decide)
  have l57 : CertLo 44482700 147768331 310195652661068774185105646265282858854 := certLo_unshift l56 rfl rfl
  have l58 : CertLo 88965400 295536662 282769112606362538365522258111824879412 := certLo_mul l57 l57 rfl rfl (by decide)
  have l59 : CertLo 177930800 591073324 234976533658493515816337965121189704614 := certLo_mul l58 l58 rfl rfl (by decide)
  have l60 : CertLo 177930801 591073328 146860333536558447385211228200743565383 := certLo_mul l59 l1 rfl rfl (by decide)
  have l61 : CertLo 177930801 591073327 293720667073116894770422456401487130766 := certLo_unshift l60 rfl rfl
  have l62 : CertLo 355861602 1182146654 253530122781593488423844034271829930101 := certLo_mul l61 l61 rfl rfl (by decide)
  have l63 : CertLo 355861603 1182146658 158456326738495930264902521419893706313 := certLo_mul l62 l1 rfl rfl (by decide)
  have l64 : CertLo 355861603 1182146657 316912653476991860529805042839787412626 := certLo_unshift l63 rfl rfl
  exact certLo_final (d := 30) l64 rfl (by decide)

theorem pow10_cert_hi : 10 ^ 355861603 < 2 ^ 1182146628 * 1000000001 := by
  have u1 : CertHi 1 4 212676479325586539664609129644855132160 := by unfold CertHi; decide
  have u2 : CertHi 2 8 132922799578491587290380706028034457600 := certHi_mul u1 u1 rfl rfl (by decide)
  have u3 : CertHi 2 7 265845599156983174580761412056068915200 := certHi_unshift u2 rfl rfl
  have u4 : CertHi 4 14 207691874341393105141219853168803840000 := certHi_mul u3 u3 rfl rfl (by decide)
  have u5 : CertHi 5 18 129807421463370690713262408230502400000 := certHi_mul u4 u1 rfl rfl (by decide)
  have u6 : CertHi 5 17 259614842926741381426524816461004800000 := certHi_unshift u5 rfl rfl
  have u7 : CertHi 10 34 198070406285660843983859875840000000000 := certHi_mul u6 u6 rfl rfl (by decide)
  have u8 : CertHi 20 68 115292150460684697600000000000000000000 := certHi_mul u7 u7 rfl rfl (by decide)
  have u9 : CertHi 20 67 230584300921369395200000000000000000000 := certHi_unshift u8 rfl rfl
  have u10 : CertHi 21 71 144115188075855872000000000000000000000 := certHi_mul u9 u1 rfl rfl (by decide)
  have u11 : CertHi 21 70 288230376151711744000000000000000000000 := certHi_unshift u10 rfl rfl
  have u12 : CertHi 42 140 244140625000000000000000000000000000000 := certHi_mul u11 u11 rfl rfl (by decide)
  have u13 : CertHi 84 280 175162308040602133865466197911239516411 := certHi_mul u12 u12 rfl rfl (by decide)
  have u14 : CertHi 168 560 90165806814313825983973933227508139043 := certHi_mul u13 u13 rfl rfl (by decide)
  have u15 : CertHi 168 559 180331613628627651967947866455016278086 := certHi_unshift u14 rfl rfl
  have u16 : CertHi 169 563 112707258517892282479967416534385173804 := certHi_mul u15 u1 rfl rfl (by decide)
  have u17 : CertHi 169 562 225414517035784564959934833068770347608 := certHi_unshift u16 rfl rfl
  have u18 : CertHi 338 1124 149322178960515020638414327155810747145 := certHi_mul u17 u17 rfl rfl (by decide)
  have u19 : CertHi 338 1123 298644357921030041276828654311621494290 := certHi_unshift u18 rfl rfl
  have u20 : CertHi 339 1127 186652723700643775798017908944763433932 := certHi_mul u19 u1 rfl rfl (by decide)
  have u21 : CertHi 678 2254 102383322356998443835244950704729869744 := certHi_mul u20 u20 rfl rfl (by decide)
  have u22 : CertHi 678 2253 204766644713996887670489901409459739488 := certHi_unshift u21 rfl rfl
  have u23 : CertHi 1356 4506 123219369745274348119219197929906801718 := certHi_mul u22 u22 rfl rfl (by decide)
  have u24 : CertHi 1356 4505 246438739490548696238438395859813603436 := certHi_unshift u23 rfl rfl
  have u25 : CertHi 1357 4509 154024212181592935149023997412383502148 := certHi_mul u24 u1 rfl rfl (by decide)
  have u26 : CertHi 1357 4508 308048424363185870298047994824767004296 := certHi_unshift u25 rfl rfl
  have u27 : CertHi 2714 9016 278867907882776574634073210811051957426 := certHi_mul u26 u26 rfl rfl (by decide)
  have u28 : CertHi 2715 9020 174292442426735359146295756756907473392 := certHi_mul u27 u1 rfl rfl (by decide)
  have u29 : CertHi 5430 18040 89272493787886694634810681920458300289 := certHi_mul u28 u28 rfl rfl (by decide)
  have u30 : CertHi 5430 18039 178544987575773389269621363840916600578 := certHi_unshift u29 rfl rfl
  have u31 : CertHi 10860 36078 93681940903625229952834771944590615896 := certHi_mul u30 u30 rfl rfl (by decide)
  have u32 : CertHi 10860 36077 187363881807250459905669543889181231792 := certHi_unshift u31 rfl rfl
  have u33 : CertHi 21720 72154 103164981845908289003661943603398982628 := certHi_mul u32 u32 rfl rfl (by decide)
  have u34 : CertHi 21720 72153 206329963691816578007323887206797965256 := certHi_unshift u33 rfl rfl
  have u35 : CertHi 43440 144306 125108022206033320067251456023865809029 := certHi_mul u34 u34 rfl rfl (by decide)
  have u36 : CertHi 43440 144305 250216044412066640134502912047731618058 := certHi_unshift u35 rfl rfl
  have u37 : CertHi 86880 288610 183988578214420746010250932491266224210 := certHi_mul u36 u36 rfl rfl (by decide)
  have u38 : CertHi 173760 577220 99481490092106887847826058549354875908 := certHi_mul u37 u37 rfl rfl (by decide)
  have u39 : CertHi 173760 577219 198962980184213775695652117098709751816 := certHi_unshift u38 rfl rfl
  have u40 : CertHi 347520 1154438 116333584493319794950488727069929260354 := certHi_mul u39 u39 rfl rfl (by decide)
  have u41 : CertHi 347520 1154437 232667168986639589900977454139858520708 := certHi_unshift u40 rfl rfl
  have u42 : CertHi 347521 1154441 145416980616649743688110908837411575443 := certHi_mul u41 u1 rfl rfl (by decide)
  have u43 : CertHi 347521 1154440 290833961233299487376221817674823150886 := certHi_unshift u42 rfl rfl
  have u44 : CertHi 695042 2308880 248571190367630096241289165620596091017 := certHi_mul u43 u43 rfl rfl (by decide)
  have u45 : CertHi 1390084 4617760 181577544672293880048491403959805195477 := certHi_mul u44 u44 rfl rfl (by decide)
  have u46 : CertHi 2780168 9235520 96891311258803062128752039558460130923 := certHi_mul u45 u45 rfl rfl (by decide)
  have u47 : CertHi 2780168 9235519 193782622517606124257504079116920261846 := certHi_unshift u46 rfl rfl
  have u48 : CertHi 5560336 18471038 110354542110393359802605984560731726798 := certHi_mul u47 u47 rfl rfl (by decide)
  have u49 : CertHi 5560336 18471037 220709084220786719605211969121463453596 := certHi_unshift u48 rfl rfl
  have u50 : CertHi 5560337 18471041 137943177637991699753257480700914658498 := certHi_mul u49 u1 rfl rfl (by decide)
  have u51 : CertHi 5560337 18471040 275886355275983399506514961401829316996 := certHi_unshift u50 rfl rfl
  have u52 : CertHi 11120674 36942080 223676829675839086833148032435327837249 := certHi_mul u51 u51 rfl rfl (by decide)
  have u53 : CertHi 11120675 36942084 139798018547399429270717520272079898281 := certHi_mul u52 u1 rfl rfl (by decide)
  have u54 : CertHi 11120675 36942083 279596037094798858541435040544159796562 := certHi_unshift u53 rfl rfl
  have u55 : CertHi 22241350 73884166 229732573763597775854980380061248374184 := certHi_mul u54 u54 rfl rfl (by decide)
  have u56 : CertHi 44482700 147768332 155097826330534387092552823132642906944 := certHi_mul u55 u55 rfl rfl (by decide)
  have u57 : CertHi 44482700 147768331 310195652661068774185105646265285813888 := certHi_unshift u56 rfl rfl
  have u58 : CertHi 88965400 295536662 282769112606362538365522258111830266931 := certHi_mul u57 u57 rfl rfl (by decide)
  have u59 : CertHi 177930800 591073324 234976533658493515816337965121198658496 := certHi_mul u58 u58 rfl rfl (by decide)
  have u60 : CertHi 177930801 591073328 146860333536558447385211228200749161560 := certHi_mul u59 u1 rfl rfl (by decide)
  have u61 : CertHi 177930801 591073327 293720667073116894770422456401498323120 := certHi_unshift u60 rfl rfl
  have u62 : CertHi 355861602 1182146654 253530122781593488423844034271849251854 := certHi_mul u61 u61 rfl rfl (by decide)
  have u63 : CertHi 355861603 1182146658 158456326738495930264902521419905782409 := certHi_mul u62 u1 rfl rfl (by decide)
  have u64 : CertHi 355861603 1182146657 316912653476991860529805042839811564818 := certHi_unshift u63 rfl rfl
  exact certHi_final (d := 29) u64 rfl (by decide)

/-- The quotient of the counterexample, `10^355861603 // 1000000001`, has bit length
1182146628 and fewer digits than 355861595. -/
theorem pow10_quot_bounds :
    2 ^ 1182146627 ≤ 10 ^ 355861603 / 1000000001 ∧ 10 ^ 355861603 / 1000000001 < 2 ^ 1182146628 ∧
      10 ^ 355861603 / 1000000001 < 10 ^ 355861594 := by
  have h9 : (0 : Nat) < 1000000001 := by decide
  refine ⟨(Nat.le_div_iff_mul_le h9).mpr pow10_cert_lo, (Nat.div_lt_iff_lt_mul h9).mpr pow10_cert_hi, ?_⟩
  rw [Nat.div_lt_iff_lt_mul h9, show 355861603 = 355861594 + 9 from rfl, Nat.pow_add]
  exact Nat.mul_lt_mul_of_pos_left (show 10 ^ 9 < 1000000001 by decide) (Nat.pow_pos (by decide))

theorem pow10_quot_bitLen : bitLen (10 ^ 355861603 / 1000000001) = 1182146628 := by
  obtain ⟨h1, h2, _⟩ := pow10_quot_bounds
  have hpos : 10 ^ 355861603 / 1000000001 ≠ 0 :=
    Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.pow_pos (by decide)) h1)
  have hle := (Nat.le_log2 hpos).mpr h1
  have hlt := (Nat.log2_lt hpos).mpr h2
  unfold bitLen
  rw [if_neg hpos]
  omega

/-- `_is_less_than_pow10a_use_str(q, a)` returns `q < 10**a` as its first item, for every
`q` and `a >= 1`: its docstring, "Try to efficiently check len(str(q)) <= a, or
equivalently q < 10**a ... Return (len(str(q)) <= a, None) or (len(str(q)) <= a, str(q))"
(_pydecimal.py:471-476). The outcomes that raise (the str limit, OverflowError for an
astronomically large `a`) are not constrained. -/
def Pow10Correct : Prop :=
  ∀ q a : Nat, 0 < a → ∀ v s, isLessThanPow10aUseStr q a = .ok (v, s) → (v = true ↔ q < 10 ^ a)

theorem pow10Correct_refuted : ¬ Pow10Correct := by
  intro h
  have := h _ _ (by decide) _ _ (pow10_hi_fires _ pow10_quot_bitLen)
  exact absurd (this.mpr pow10_quot_bounds.2.2) (by decide)

/-! ### `_divide` -/

/-- The context of the counterexample: prec 355861594, nothing trapped (Emin, Emax and
clamp are not read by `_divide`). -/
def pow10Ctx : Ctx := { prec := 355861594, traps := [] }

theorem pow10_scaled : scaled 1 355861594 1000000001 (-9) = (10 ^ 355861603, 1000000001) := by
  unfold scaled
  rw [if_pos (by decide), show ((355861594 : Int) - -9).toNat = 355861603 by decide, Nat.one_mul]

/-- `_divide` signals DivisionImpossible whenever the helper says the quotient is too
large, stated over variables so that no big numeral reaches the kernel's evaluator. -/
theorem divideD_misfire (c : Ctx) (sa sb : Bool) (ca cb : Nat) (ea eb : Int) (X Y : Nat) (s : Bool)
    (ha : ca ≠ 0) (hd1 : ¬ (adjustedD ca ea - adjustedD cb eb ≤ -2))
    (hd2 : adjustedD ca ea - adjustedD cb eb ≤ c.prec)
    (hl1 : ¬ numDigits ca > maxStrDigits) (hl2 : ¬ numDigits cb > maxStrDigits)
    (hs : scaled ca ea cb eb = (X, Y)) (hp : isLessThanPow10aUseStr (X / Y) c.prec = .ok (false, s))
    (ht : Signal.invalidOperation ∉ c.traps) :
    (divideD c (.fin sa ca ea) (.fin sb cb eb)).run [] =
      .ok ((.nan false false 0, .nan false false 0), [.invalidOperation]) := by
  have hw1 : workRep (.fin sa ca ea) = .ok (sa, ca, ea) := by simp [workRep, intLimit, hl1, pure, Except.pure, bind, Except.bind]
  have hw2 : workRep (.fin sb cb eb) = .ok (sb, cb, eb) := by simp [workRep, intLimit, hl2, pure, Except.pure, bind, Except.bind]
  simp only [divideD, decBool, isZero_fin sa ca ea ha, isinfinity, expOf, Dec.adjusted, Dec.neg,
    Bool.not_false, Bool.not_true, ne_eq, not_true_eq_false, decide_false, Bool.false_or,
    ↓reduceIte, decide_eq_true_eq, hd1, hd2, hs]
  simp [StateT.run, bind, StateT.bind, Except.bind, liftPy, hw1, hw2, hp, invalid, raiseSig, ht, pure,
    StateT.pure, Except.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, Functor.map,
    Except.map]

theorem pow10_divide_run :
    (divideD pow10Ctx (.fin false 1 355861594) (.fin false 1000000001 (-9))).run [] =
      .ok ((.nan false false 0, .nan false false 0), [.invalidOperation]) :=
  divideD_misfire pow10Ctx false false 1 1000000001 355861594 (-9) _ _ false (by decide) (by decide)
    (by decide) (by decide) (by decide) pow10_scaled (pow10_hi_fires _ pow10_quot_bitLen) (by decide)

/-- `_divide` of `Decimal('1E+355861594')` by `Decimal('1.000000001')` at prec 355861594:
the integer quotient `10^355861603 // 1000000001` has 355861594 digits, so `divide-integer`
fits, but `_divide` returns NaN with InvalidOperation (DivisionImpossible). -/
theorem divideCorrect_refuted : ¬ DivideCorrect := by
  intro h
  have key : ∀ (c : Ctx) (ca cb : Nat) (ea eb : Int) (X Y P : Nat), ca ≠ 0 → cb ≠ 0 →
      scaled ca ea cb eb = (X, Y) → c.prec = P → X / Y < 10 ^ P →
      (divideD c (.fin false ca ea) (.fin false cb eb)).run [] =
        .ok ((.nan false false 0, .nan false false 0), [.invalidOperation]) → False := by
    intro c ca cb ea eb X Y P ha hb hs hP hlt hrun
    have := h c false ca ea false cb eb [] _ _ _ ha hb hrun
    simp only [hs, hP] at this
    rcases this with ⟨_, hq, _⟩ | ⟨hle, _⟩
    · cases hq
    · exact absurd hlt (Nat.not_lt.mpr hle)
  exact key pow10Ctx 1 1000000001 355861594 (-9) _ _ 355861594 (by decide) (by decide) pow10_scaled rfl
    pow10_quot_bounds.2.2 pow10_divide_run

end PyLean.Decimal
