import PyLean.Core

/-!
SHA-512 (FIPS 180-4), the hash `Random.seed` applies to `str`, `bytes` and
`bytearray` seeds (`Lib/random.py:167`, through `_sha2.sha512`). Bytes are `Nat`s
below 256. The constants are the first 64 bits of the fractional parts of the
cube roots (`K`) and square roots (`H0`) of the first primes, FIPS 180-4 §4.2.3
and §5.3.5.
-/

namespace PyLean.CoreLibs.Rand.Sha512

/-- FIPS 180-4 §4.2.3. -/
def K : Array UInt64 := #[
  0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
  0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
  0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
  0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
  0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
  0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
  0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
  0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
  0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
  0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
  0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
  0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
  0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
  0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
  0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
  0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
  0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
  0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
  0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
  0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817
]

/-- FIPS 180-4 §5.3.5. -/
def H0 : List UInt64 := [
  0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
  0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179
]

/-- `ROTR^n(x)`. -/
@[inline] def rotr (x : UInt64) (n : UInt64) : UInt64 := (x >>> n) ||| (x <<< (64 - n))

@[inline] def Ch (x y z : UInt64) : UInt64 := (x &&& y) ^^^ ((~~~x) &&& z)
@[inline] def Maj (x y z : UInt64) : UInt64 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)
@[inline] def bigS0 (x : UInt64) : UInt64 := rotr x 28 ^^^ rotr x 34 ^^^ rotr x 39
@[inline] def bigS1 (x : UInt64) : UInt64 := rotr x 14 ^^^ rotr x 18 ^^^ rotr x 41
@[inline] def smallS0 (x : UInt64) : UInt64 := rotr x 1 ^^^ rotr x 8 ^^^ (x >>> 7)
@[inline] def smallS1 (x : UInt64) : UInt64 := rotr x 19 ^^^ rotr x 61 ^^^ (x >>> 6)

/-- Padding, FIPS 180-4 §5.1.2: `1` bit, zeros, 128-bit big-endian length. -/
def pad (msg : List Nat) : List Nat :=
  let l := msg.length
  let z := (112 + 128 - (l + 1) % 128) % 128
  let bits := 8 * l
  msg ++ [0x80] ++ List.replicate z 0
    ++ (List.range 16).map fun i => (bits >>> (8 * (15 - i))) % 256

/-- Big-endian word from eight bytes. -/
def beWord (bs : List Nat) : UInt64 :=
  (bs.foldl (fun acc b => acc * 256 + b) 0).toUInt64

/-- The sixteen message words of a 128-byte block. -/
def blockWords (block : List Nat) : Array UInt64 :=
  ((List.range 16).map fun i => beWord ((block.drop (8 * i)).take 8)).toArray

/-- The message schedule, FIPS 180-4 §6.4.2 step 1. -/
def schedule (w0 : Array UInt64) : Array UInt64 :=
  (List.range 64).foldl (fun w i =>
    let t := i + 16
    w.push (smallS1 (w.getD (t - 2) 0) + w.getD (t - 7) 0 + smallS0 (w.getD (t - 15) 0)
      + w.getD (t - 16) 0)) w0

/-- The 80 rounds and the feed-forward, FIPS 180-4 §6.4.2 steps 2-4. -/
def compress (h : List UInt64) (block : List Nat) : List UInt64 :=
  let w := schedule (blockWords block)
  let step (st : List UInt64) (t : Nat) : List UInt64 :=
    match st with
    | [a, b, c, d, e, f, g, hh] =>
      let t1 := hh + bigS1 e + Ch e f g + K.getD t 0 + w.getD t 0
      let t2 := bigS0 a + Maj a b c
      [t1 + t2, a, b, c, d + t1, e, f, g]
    | st => st
  let final := (List.range 80).foldl step h
  List.zipWith (· + ·) h final

/-- Process the padded message block by block. -/
def blocks : Nat → List UInt64 → List Nat → List UInt64
  | 0, h, _ => h
  | n + 1, h, msg => blocks n (compress h (msg.take 128)) (msg.drop 128)

/-- `sha512(msg).digest()`. -/
def digest (msg : List Nat) : List Nat :=
  let p := pad msg
  let h := blocks (p.length / 128) H0 p
  h.flatMap fun w => (List.range 8).map fun i => (w.toNat >>> (8 * (7 - i))) % 256

/-- FIPS 180-4 example: SHA-512("abc"). The first eight bytes, in the kernel. -/
theorem digest_abc :
    (digest [0x61, 0x62, 0x63]).take 8 = [0xdd, 0xaf, 0x35, 0xa1, 0x93, 0x61, 0x7a, 0xba] := by
  decide +kernel

end PyLean.CoreLibs.Rand.Sha512
