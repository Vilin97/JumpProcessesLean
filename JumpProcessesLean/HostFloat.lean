import JumpProcessesLean.Core

/-!
# Host floating point and a fast generator

`hostArithmetic` instantiates the generic algorithms at Lean's native `Float`. Its logical
definitions follow Lean's binary64 model; compiled code calls the host's IEEE operations.
`Xoshiro` is xoshiro256++ (Blackman–Vigna), seeded through SplitMix64. Uniforms are the top
53 bits of a word. Exponentials are drawn by a 256-layer ziggurat (Marsaglia–Tsang), the method
of Julia's `randexp`: 98% of draws cost one word, a multiplication and a comparison; the others
make one tail or wedge attempt with two more words and, if it is rejected, return `-log V` of
the second. Each branch returns an exact `Exp(1)` sample in real arithmetic, so the mixture is
`Exp(1)`. Like SplitMix64 in `FloatLibBackend`, it is an executable source only: no theorem
claims that its outputs are independent uniforms or exponentials.
-/

namespace JumpProcessesLean

/-- Integer to float avoiding the runtime's `Float.ofScientific` path, which builds `2^53`
with GMP on every call. Below `2^53` the direct conversion is exact. The test is a shift: a
literal `2^53` would be rebuilt from a string at every call. -/
@[inline] def natToFloat (n : Nat) : Float :=
  if n >>> 53 = 0 then n.toUInt64.toFloat else Float.ofNat n

@[inline] def hostArithmetic : Arithmetic Float where
  zero := 0
  one := 1
  add := (· + ·)
  sub := (· - ·)
  mul := (· * ·)
  div := (· / ·)
  lt a b := decide (a < b)
  le a b := decide (a ≤ b)
  finite := Float.isFinite
  ofNat := natToFloat

/-! Float constants are top-level definitions: the compiler initializes each once.
A literal inside an inlined function would be rebuilt through `Float.ofScientific` at
every use. -/

/-- `0` as a float. -/
def floatZero : Float := 0
/-- `1` as a float. -/
def floatOne : Float := 1
/-- `1/2` as a float. -/
def floatHalf : Float := 0.5
/-- `2^-53`. -/
def twoPowNeg53 : Float := 1.1102230246251565e-16
/-- `2^-52`, the binary64 machine epsilon. -/
def twoPowNeg52 : Float := 2.220446049250313e-16

structure Xoshiro where
  s0 : UInt64
  s1 : UInt64
  s2 : UInt64
  s3 : UInt64
  deriving Inhabited, BEq, Repr

namespace Xoshiro

@[inline] def rotl (x k : UInt64) : UInt64 := (x <<< k) ||| (x >>> (64 - k))

/-- One xoshiro256++ step. -/
@[inline] def next (s : Xoshiro) : UInt64 × Xoshiro :=
  let result := rotl (s.s0 + s.s3) 23 + s.s0
  let t := s.s1 <<< 17
  let s2 := s.s2 ^^^ s.s0
  let s3 := s.s3 ^^^ s.s1
  let s1 := s.s1 ^^^ s2
  let s0 := s.s0 ^^^ s3
  (result, ⟨s0, s1, s2 ^^^ t, rotl s3 45⟩)

@[inline] def splitMix (s : UInt64) : UInt64 × UInt64 :=
  let s := s + 0x9e3779b97f4a7c15
  let z := (s ^^^ (s >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb
  (z ^^^ (z >>> 31), s)

def seed (x : UInt64) : Xoshiro :=
  let (a, x) := splitMix x
  let (b, x) := splitMix x
  let (c, x) := splitMix x
  let (d, _) := splitMix x
  ⟨a, b, c, d⟩

/-- A uniform draw on the grid `k / 2^53` of `[0,1)`. -/
@[inline] def uniform (s : Xoshiro) : Float × Xoshiro :=
  let (w, s) := s.next
  ((w >>> 11).toFloat * twoPowNeg53, s)

/-- `-log V` for the uniform `V = (k + 1/2) / 2^52` of a word's top 52 bits `k`, which is never
`0` or `1`. -/
@[inline] def negLogWord (w : UInt64) : Float :=
  -(Float.log (((w >>> 12).toFloat + floatHalf) * twoPowNeg52))

/-- Ziggurat layer widths `X[0..256]` for the exponential distribution (256 layers, Marsaglia
and Tsang): `X[1] = R = 7.697…`, `X[0] = V / exp(-R)`, `X[256] = 0`. -/
def zigX : FloatArray := ⟨#[
    Float.ofBits 0x402164ec94bf5dc1, Float.ofBits 0x401ec9d9297ebb83, Float.ofBits 0x401bc39e51da71fc,
    Float.ofBits 0x4019e9dc0d487b85, Float.ofBits 0x4018939fe6f2ed19, Float.ofBits 0x40178750d6eac62f,
    Float.ofBits 0x4016aa676d4bbf72, Float.ofBits 0x4015ee7ae17313d2, Float.ofBits 0x40154ad83ccf73f6,
    Float.ofBits 0x4014b9d7cd4751d1, Float.ofBits 0x4014379766e41362, Float.ofBits 0x4013c14ec7c8b861,
    Float.ofBits 0x401354ee27ccf75e, Float.ofBits 0x4012f0e38a4411f0, Float.ofBits 0x401293f5ae49aaa5,
    Float.ofBits 0x40123d2bb659919f, Float.ofBits 0x4011ebbca0c9fa7c, Float.ofBits 0x40119f03bcb3c2d6,
    Float.ofBits 0x401156786775442a, Float.ofBits 0x401111a8034392a6, Float.ofBits 0x4010d031785d48a0,
    Float.ofBits 0x401091c1cdcba54e, Float.ofBits 0x401056118bf58eef, Float.ofBits 0x40101ce2b362ec2e,
    Float.ofBits 0x400fcbfe43f6c6e5, Float.ofBits 0x400f626e9791f7a7, Float.ofBits 0x400efcc26750ea4a,
    Float.ofBits 0x400e9aaf2af383c1, Float.ofBits 0x400e3bf26e190960, Float.ofBits 0x400de050af4ef19f,
    Float.ofBits 0x400d87946fec3bec, Float.ofBits 0x400d318d6b2738c5, Float.ofBits 0x400cde0fecf2a97f,
    Float.ofBits 0x400c8cf442c8c8f4, Float.ofBits 0x400c3e1641c2e0a7, Float.ofBits 0x400bf154de4bef77,
    Float.ofBits 0x400ba691d276da5e, Float.ofBits 0x400b5db15091ea0f, Float.ofBits 0x400b1699c003b60a,
    Float.ofBits 0x400ad13382d845c4, Float.ofBits 0x400a8d68c2ad86ea, Float.ofBits 0x400a4b2543e84c3b,
    Float.ofBits 0x400a0a563e49f178, Float.ofBits 0x4009caea3a24d9ea, Float.ofBits 0x40098cd0f18d1ad8,
    Float.ofBits 0x40094ffb34fc2a0e, Float.ofBits 0x4009145ad2f37544, Float.ofBits 0x4008d9e2823b3695,
    Float.ofBits 0x4008a085ce695bab, Float.ofBits 0x4008683906687342, Float.ofBits 0x400830f12cc0bec3,
    Float.ofBits 0x4007faa3e96e1412, Float.ofBits 0x4007c5477d1476d3, Float.ofBits 0x400790d2b56b71f9,
    Float.ofBits 0x40075d3ce2bd71c3, Float.ofBits 0x40072a7dce5cd218, Float.ofBits 0x4006f88db1f42507,
    Float.ofBits 0x4006c7652f9a7b1e, Float.ofBits 0x400696fd4a9748ee, Float.ofBits 0x4006674f60c3f432,
    Float.ofBits 0x40063855247b2e94, Float.ofBits 0x40060a0897081879, Float.ofBits 0x4005dc640388bd9e,
    Float.ofBits 0x4005af61fa38e107, Float.ofBits 0x400582fd4c1b4461, Float.ofBits 0x4005573106f8a75a,
    Float.ofBits 0x40052bf871acaab2, Float.ofBits 0x4005014f08b99508, Float.ofBits 0x4004d7307b1cb127,
    Float.ofBits 0x4004ad98a75da14c, Float.ofBits 0x4004848398d39432, Float.ofBits 0x40045bed851bc92c,
    Float.ofBits 0x400433d2c9bd42f8, Float.ofBits 0x40040c2fe9f5eead, Float.ofBits 0x4003e5018cadded0,
    Float.ofBits 0x4003be447a8d8b83, Float.ofBits 0x400397f59c345143, Float.ofBits 0x40037211f88ca856,
    Float.ofBits 0x40034c96b33bc965, Float.ofBits 0x400327810b2aa7d0, Float.ofBits 0x400302ce59265965,
    Float.ofBits 0x4002de7c0e962d70, Float.ofBits 0x4002ba87b445db51, Float.ofBits 0x400296eee942532b,
    Float.ofBits 0x400273af61c7daa6, Float.ofBits 0x400250c6e6403bba, Float.ofBits 0x40022e33524fe550,
    Float.ofBits 0x40020bf293f0f4a2, Float.ofBits 0x4001ea02aa9b3370, Float.ofBits 0x4001c861a6782a5a,
    Float.ofBits 0x4001a70da7a27820, Float.ofBits 0x40018604dd6fae9e, Float.ofBits 0x4001654585c404c1,
    Float.ofBits 0x400144cdec6f3a2b, Float.ofBits 0x4001249c6a92154a, Float.ofBits 0x400104af660befce,
    Float.ofBits 0x4000e50550efcfb7, Float.ofBits 0x4000c59ca900946f, Float.ofBits 0x4000a673f733c819,
    Float.ofBits 0x40008789cf3aad0f, Float.ofBits 0x400068dccf1126db, Float.ofBits 0x40004a6b9e9224a3,
    Float.ofBits 0x40002c34ef11391b, Float.ofBits 0x40000e377af911d4, Float.ofBits 0x3fffe0e40add09d8,
    Float.ofBits 0x3fffa5c6b3efe1e5, Float.ofBits 0x3fff6b1498515ed0, Float.ofBits 0x3fff30cb6ea0bc7f,
    Float.ofBits 0x3ffef6e8fc5b9168, Float.ofBits 0x3ffebd6b154a7678, Float.ofBits 0x3ffe844f9af4237f,
    Float.ofBits 0x3ffe4b947c16a452, Float.ofBits 0x3ffe1337b426509c, Float.ofBits 0x3ffddb374ad2357f,
    Float.ofBits 0x3ffda391538da50a, Float.ofBits 0x3ffd6c43ed1ea3ff, Float.ofBits 0x3ffd354d4130f2ad,
    Float.ofBits 0x3ffcfeab83ed7180, Float.ofBits 0x3ffcc85cf395a56c, Float.ofBits 0x3ffc925fd82323fb,
    Float.ofBits 0x3ffc5cb282eab1a4, Float.ofBits 0x3ffc27534e42e02d, Float.ofBits 0x3ffbf2409d2dfd85,
    Float.ofBits 0x3ffbbd78db072610, Float.ofBits 0x3ffb88fa7b324fb6, Float.ofBits 0x3ffb54c3f8cf2542,
    Float.ofBits 0x3ffb20d3d66e8bb5, Float.ofBits 0x3ffaed289dcaacff, Float.ofBits 0x3ffab9c0df81657a,
    Float.ofBits 0x3ffa869b32d0f30f, Float.ofBits 0x3ffa53b63556c690, Float.ofBits 0x3ffa21108ad0592d,
    Float.ofBits 0x3ff9eea8dcdde951, Float.ofBits 0x3ff9bc7ddac7035d, Float.ofBits 0x3ff98a8e3940bbf4,
    Float.ofBits 0x3ff958d8b235828a, Float.ofBits 0x3ff9275c048e73e1, Float.ofBits 0x3ff8f616f3fe1513,
    Float.ofBits 0x3ff8c50848cc6094, Float.ofBits 0x3ff8942ecfa40f54, Float.ofBits 0x3ff86389596108e7,
    Float.ofBits 0x3ff83316badfe62a, Float.ofBits 0x3ff802d5ccce7277, Float.ofBits 0x3ff7d2c56b7d17f7,
    Float.ofBits 0x3ff7a2e476b1240a, Float.ofBits 0x3ff77331d177d130, Float.ofBits 0x3ff743ac61fa041c,
    Float.ofBits 0x3ff714531150a9fb, Float.ofBits 0x3ff6e524cb59a608, Float.ofBits 0x3ff6b6207e8d3cdf,
    Float.ofBits 0x3ff687451bd3ebee, Float.ofBits 0x3ff65891965c9b8c, Float.ofBits 0x3ff62a04e3731a2e,
    Float.ofBits 0x3ff5fb9dfa56cf26, Float.ofBits 0x3ff5cd5bd4119335, Float.ofBits 0x3ff59f3d6b4e9cf9,
    Float.ofBits 0x3ff57141bc316f27, Float.ofBits 0x3ff54367c42cb5f8, Float.ofBits 0x3ff515ae81d900fb,
    Float.ofBits 0x3ff4e814f4cb45ea, Float.ofBits 0x3ff4ba9a1d6b18a4, Float.ofBits 0x3ff48d3cfcc883c4,
    Float.ofBits 0x3ff45ffc94716ca7, Float.ofBits 0x3ff432d7e6466cd0, Float.ofBits 0x3ff405cdf44f09c4,
    Float.ofBits 0x3ff3d8ddc08d336d, Float.ofBits 0x3ff3ac064ccfeffc, Float.ofBits 0x3ff37f469a851af0,
    Float.ofBits 0x3ff3529daa8a1ba1, Float.ofBits 0x3ff3260a7cfb7611, Float.ofBits 0x3ff2f98c11031721,
    Float.ofBits 0x3ff2cd2164a53b5d, Float.ofBits 0x3ff2a0c9748bcdaa, Float.ofBits 0x3ff274833bd0189f,
    Float.ofBits 0x3ff2484db3c2a329, Float.ofBits 0x3ff21c27d3b10e05, Float.ofBits 0x3ff1f01090a9c4e2,
    Float.ofBits 0x3ff1c406dd3d5283, Float.ofBits 0x3ff19809a93d2396, Float.ofBits 0x3ff16c17e1777ffb,
    Float.ofBits 0x3ff140306f707dbe, Float.ofBits 0x3ff114523917ac15, Float.ofBits 0x3ff0e87c207a2f66,
    Float.ofBits 0x3ff0bcad03710137, Float.ofBits 0x3ff090e3bb4b0072, Float.ofBits 0x3ff0651f1c7276f8,
    Float.ofBits 0x3ff0395df60db162, Float.ofBits 0x3ff00d9f119a3cd9, Float.ofBits 0x3fefc3c26504a9a1,
    Float.ofBits 0x3fef6c462b57feb5, Float.ofBits 0x3fef14c6e20294a0, Float.ofBits 0x3feebd41e5e21b62,
    Float.ofBits 0x3fee65b483cf1044, Float.ofBits 0x3fee0e1bf77c31fe, Float.ofBits 0x3fedb6756a429057,
    Float.ofBits 0x3fed5ebdf1d86b8d, Float.ofBits 0x3fed06f28ef0e6fb, Float.ofBits 0x3fecaf102bc25adb,
    Float.ofBits 0x3fec57139a70d29f, Float.ofBits 0x3febfef99359fe99, Float.ofBits 0x3feba6beb33f8f89,
    Float.ofBits 0x3feb4e5f794c979b, Float.ofBits 0x3feaf5d844f224c9, Float.ofBits 0x3fea9d255396d261,
    Float.ofBits 0x3fea4442be14884a, Float.ofBits 0x3fe9eb2c75ff03bf, Float.ofBits 0x3fe991de42ad1338,
    Float.ofBits 0x3fe93853bdfda244, Float.ofBits 0x3fe8de8850d0c52a, Float.ofBits 0x3fe884772f2be1ec,
    Float.ofBits 0x3fe82a1b53fed599, Float.ofBits 0x3fe7cf6f7c7e8172, Float.ofBits 0x3fe7746e23077973,
    Float.ofBits 0x3fe71911797990bb, Float.ofBits 0x3fe6bd5362faa944, Float.ofBits 0x3fe6612d6d0c68e0,
    Float.ofBits 0x3fe60498c7dd2ecf, Float.ofBits 0x3fe5a78e3db8befd, Float.ofBits 0x3fe54a0629786f4d,
    Float.ofBits 0x3fe4ebf86bcd0b93, Float.ofBits 0x3fe48d5c5f35e712, Float.ofBits 0x3fe42e28ca706748,
    Float.ofBits 0x3fe3ce53d12162a0, Float.ofBits 0x3fe36dd2e26d8202, Float.ofBits 0x3fe30c9aa526da4b,
    Float.ofBits 0x3fe2aa9ee123680b, Float.ofBits 0x3fe247d26538ff2e, Float.ofBits 0x3fe1e426e93e49e7,
    Float.ofBits 0x3fe17f8ceb4bdfa0, Float.ofBits 0x3fe119f38749f5af, Float.ofBits 0x3fe0b348479b80fc,
    Float.ofBits 0x3fe04b76ed6a7558, Float.ofBits 0x3fdfc4d25d683209, Float.ofBits 0x3fdef00ccf5f4faa,
    Float.ofBits 0x3fde186678f1735a, Float.ofBits 0x3fdd3da24df17c36, Float.ofBits 0x3fdc5f7bd78c3f89,
    Float.ofBits 0x3fdb7da5dddda3c4, Float.ofBits 0x3fda97c8be5d5204, Float.ofBits 0x3fd9ad80552237d2,
    Float.ofBits 0x3fd8be5954d3606f, Float.ofBits 0x3fd7c9cdda17d019, Float.ofBits 0x3fd6cf40f0a72bbd,
    Float.ofBits 0x3fd5cdf89d024ac3, Float.ofBits 0x3fd4c515c60bfe22, Float.ofBits 0x3fd3b388fe3d6eca,
    Float.ofBits 0x3fd2980290da2633, Float.ofBits 0x3fd170db24d6f670, Float.ofBits 0x3fd03bf049c65c3c,
    Float.ofBits 0x3fcdecd8b76dbd98, Float.ofBits 0x3fcb38d1ef79b7cc, Float.ofBits 0x3fc85090fbc27a80,
    Float.ofBits 0x3fc522e6e54a2a74, Float.ofBits 0x3fc19335a95b8dba, Float.ofBits 0x3fbad6b2495b4d2c,
    Float.ofBits 0x3fb0589d8b5d411b, Float.ofBits 0x0000000000000000]⟩

/-- `F[i] = exp(-X[i])`. -/
def zigF : FloatArray := ⟨#[
    Float.ofBits 0x3f25e5d3f59d055c, Float.ofBits 0x3f3dc31c329f0b4b, Float.ofBits 0x3f4fb20af78dfcb9,
    Float.ofBits 0x3f592bb5540c3e25, Float.ofBits 0x3f61946ba8e1a324, Float.ofBits 0x3f66d888f3a1feff,
    Float.ofBits 0x3f6c58b381cd4b11, Float.ofBits 0x3f71073d69574043, Float.ofBits 0x3f73fa97cee322fd,
    Float.ofBits 0x3f77049f37ec3620, Float.ofBits 0x3f7a23e9d4974836, Float.ofBits 0x3f7d5751fa745dc5,
    Float.ofBits 0x3f804ef2295fd7f9, Float.ofBits 0x3f81fb69edb37671, Float.ofBits 0x3f83b0b8c1516f62,
    Float.ofBits 0x3f856e930be416cb, Float.ofBits 0x3f8734b6e6aa74f5, Float.ofBits 0x3f8902ea688fa7bd,
    Float.ofBits 0x3f8ad8fa5542c92d, Float.ofBits 0x3f8cb6b9146e2757, Float.ofBits 0x3f8e9bfdde89c7ce,
    Float.ofBits 0x3f904452091e02f0, Float.ofBits 0x3f913e4554725f5f, Float.ofBits 0x3f923bc9e1b93a32,
    Float.ofBits 0x3f933cd225315d84, Float.ofBits 0x3f944151ce87f0be, Float.ofBits 0x3f95493da6ab0251,
    Float.ofBits 0x3f96548b72a24077, Float.ofBits 0x3f976331da87fc96, Float.ofBits 0x3f98752853ec9967,
    Float.ofBits 0x3f998a670f132a48, Float.ofBits 0x3f9aa2e6e6924e9b, Float.ofBits 0x3f9bbea150fa5870,
    Float.ofBits 0x3f9cdd9054331b0c, Float.ofBits 0x3f9dffae7a517468, Float.ofBits 0x3f9f24f6c7af9890,
    Float.ofBits 0x3fa026b2590dfaee, Float.ofBits 0x3fa0bc7a0c7cd651, Float.ofBits 0x3fa153d09f19b3a1,
    Float.ofBits 0x3fa1ecb45ff312d4, Float.ofBits 0x3fa28723c956c00c, Float.ofBits 0x3fa3231d7e3f14ae,
    Float.ofBits 0x3fa3c0a047ff18ff, Float.ofBits 0x3fa45fab14266b19, Float.ofBits 0x3fa5003cf296c5eb,
    Float.ofBits 0x3fa5a25513c5d2ca, Float.ofBits 0x3fa645f2c726a041, Float.ofBits 0x3fa6eb1579b6af52,
    Float.ofBits 0x3fa791bcb4ab089e, Float.ofBits 0x3fa839e81c3a396b, Float.ofBits 0x3fa8e3976e80776d,
    Float.ofBits 0x3fa98eca827b7c4c, Float.ofBits 0x3faa3b81471bf138, Float.ofBits 0x3faae9bbc26a8084,
    Float.ofBits 0x3fab997a10bed985, Float.ofBits 0x3fac4abc640721e9, Float.ofBits 0x3facfd83031e794a,
    Float.ofBits 0x3fadb1ce49315810, Float.ofBits 0x3fae679ea52eb2e5, Float.ofBits 0x3faf1ef49944e834,
    Float.ofBits 0x3fafd7d0ba699676, Float.ofBits 0x3fb04919d7f5c817, Float.ofBits 0x3fb0a70f19871b3b,
    Float.ofBits 0x3fb105c88756ca50, Float.ofBits 0x3fb165468f755392, Float.ofBits 0x3fb1c589a86fa340,
    Float.ofBits 0x3fb22692512c9d8c, Float.ofBits 0x3fb2886110ce0570, Float.ofBits 0x3fb2eaf676948dd1,
    Float.ofBits 0x3fb34e5319c6e718, Float.ofBits 0x3fb3b277999b9f9e, Float.ofBits 0x3fb417649d25b10e,
    Float.ofBits 0x3fb47d1ad343985c, Float.ofBits 0x3fb4e39af290d929, Float.ofBits 0x3fb54ae5b959d036,
    Float.ofBits 0x3fb5b2fbed91bb3e, Float.ofBits 0x3fb61bde5ccadef7, Float.ofBits 0x3fb6858ddc30b620,
    Float.ofBits 0x3fb6f00b488416b6, Float.ofBits 0x3fb75b5786193c1e, Float.ofBits 0x3fb7c77380d7a6f3,
    Float.ofBits 0x3fb834602c3bc4ba, Float.ofBits 0x3fb8a21e835a533b, Float.ofBits 0x3fb910af88e574b9,
    Float.ofBits 0x3fb9801447336b70, Float.ofBits 0x3fb9f04dd046f428, Float.ofBits 0x3fba615d3dd938b7,
    Float.ofBits 0x3fbad343b1655465, Float.ofBits 0x3fbb460254356548, Float.ofBits 0x3fbbb99a5771268f,
    Float.ofBits 0x3fbc2e0cf42e10af, Float.ofBits 0x3fbca35b6b80fd57, Float.ofBits 0x3fbd198706914dd7,
    Float.ofBits 0x3fbd909116ad9398, Float.ofBits 0x3fbe087af561bafb, Float.ofBits 0x3fbe8146048eb9cc,
    Float.ofBits 0x3fbefaf3ae83c33c, Float.ofBits 0x3fbf758566190414, Float.ofBits 0x3fbff0fca6cbea8d,
    Float.ofBits 0x3fc036ad7a6e7f04, Float.ofBits 0x3fc07550eeb7a5be, Float.ofBits 0x3fc0b4697b54b62f,
    Float.ofBits 0x3fc0f3f7efec1720, Float.ofBits 0x3fc133fd20c9712f, Float.ofBits 0x3fc17479e6f0ae78,
    Float.ofBits 0x3fc1b56f2031d666, Float.ofBits 0x3fc1f6ddaf3dca65, Float.ofBits 0x3fc238c67bbbe878,
    Float.ofBits 0x3fc27b2a72609940, Float.ofBits 0x3fc2be0a8504cf34, Float.ofBits 0x3fc30167aabe7d6e,
    Float.ofBits 0x3fc34542dffa0caf, Float.ofBits 0x3fc3899d2694d5c9, Float.ofBits 0x3fc3ce7785f8a905,
    Float.ofBits 0x3fc413d30b386a9a, Float.ofBits 0x3fc459b0c92dccc6, Float.ofBits 0x3fc4a011d8983096,
    Float.ofBits 0x3fc4e6f7583cb6fa, Float.ofBits 0x3fc52e626d078c49, Float.ofBits 0x3fc57654422e78f5,
    Float.ofBits 0x3fc5bece0954c2b6, Float.ofBits 0x3fc607d0fab06a31, Float.ofBits 0x3fc6515e5530d1ac,
    Float.ofBits 0x3fc69b775ea6da28, Float.ofBits 0x3fc6e61d63ee84ea, Float.ofBits 0x3fc73151b91a2839,
    Float.ofBits 0x3fc77d15b99f46fe, Float.ofBits 0x3fc7c96ac8851bae, Float.ofBits 0x3fc816525094e7e6,
    Float.ofBits 0x3fc863cdc48c1af9, Float.ofBits 0x3fc8b1de9f5062d5, Float.ofBits 0x3fc900866425bb79,
    Float.ofBits 0x3fc94fc69ee692a1, Float.ofBits 0x3fc99fa0e43e1623, Float.ofBits 0x3fc9f016d1e4c512,
    Float.ofBits 0x3fca412a0edf5cbc, Float.ofBits 0x3fca92dc4bc03c49, Float.ofBits 0x3fcae52f42eb5b0b,
    Float.ofBits 0x3fcb3824b8dcef3e, Float.ofBits 0x3fcb8bbe7c72e4a5, Float.ofBits 0x3fcbdffe67394435,
    Float.ofBits 0x3fcc34e65db9afee, Float.ofBits 0x3fcc8a784fce1801, Float.ofBits 0x3fcce0b638f6d09f,
    Float.ofBits 0x3fcd37a220b431fd, Float.ofBits 0x3fcd8f3e1ae3eeb8, Float.ofBits 0x3fcde78c48224f39,
    Float.ofBits 0x3fce408ed62f83a7, Float.ofBits 0x3fce9a48005940f2, Float.ofBits 0x3fcef4ba0fe8e09b,
    Float.ofBits 0x3fcf4fe75c963e7e, Float.ofBits 0x3fcfabd24cff9354, Float.ofBits 0x3fd0043eab93476a,
    Float.ofBits 0x3fd032f580797c2c, Float.ofBits 0x3fd0620ef05d90d2, Float.ofBits 0x3fd0918c4ee93e13,
    Float.ofBits 0x3fd0c16ef88f5333, Float.ofBits 0x3fd0f1b852d9a66c, Float.ofBits 0x3fd12269ccba9fba,
    Float.ofBits 0x3fd15384dee291ef, Float.ofBits 0x3fd1850b0c191982, Float.ofBits 0x3fd1b6fde19abc5a,
    Float.ofBits 0x3fd1e95ef77b09db, Float.ofBits 0x3fd21c2ff10b7eff, Float.ofBits 0x3fd24f727d4776fd,
    Float.ofBits 0x3fd2832857457629, Float.ofBits 0x3fd2b75346ae2262, Float.ofBits 0x3fd2ebf520394270,
    Float.ofBits 0x3fd3210fc6312435, Float.ofBits 0x3fd356a528fcd0dd, Float.ofBits 0x3fd38cb747b17def,
    Float.ofBits 0x3fd3c34830abb285, Float.ofBits 0x3fd3fa5a0230a14e, Float.ofBits 0x3fd431eeeb1841e2,
    Float.ofBits 0x3fd46a092b80beef, Float.ofBits 0x3fd4a2ab158bdad3, Float.ofBits 0x3fd4dbd70e26f91d,
    Float.ofBits 0x3fd5158f8dde89f5, Float.ofBits 0x3fd54fd721bda3e7, Float.ofBits 0x3fd58ab06c3aa9ef,
    Float.ofBits 0x3fd5c61e2631ee6c, Float.ofBits 0x3fd602231fef5876, Float.ofBits 0x3fd63ec2424827e4,
    Float.ofBits 0x3fd67bfe8fc60d9f, Float.ofBits 0x3fd6b9db25e4e99c, Float.ofBits 0x3fd6f85b3e649e9d,
    Float.ofBits 0x3fd7378230b08dea, Float.ofBits 0x3fd77753735e72e3, Float.ofBits 0x3fd7b7d29dc6801e,
    Float.ofBits 0x3fd7f90369b6ce59, Float.ofBits 0x3fd83ae9b5446138, Float.ofBits 0x3fd87d8984bc3f8c,
    Float.ofBits 0x3fd8c0e704b75d39, Float.ofBits 0x3fd905068c545d04, Float.ofBits 0x3fd949ec9f9a8110,
    Float.ofBits 0x3fd98f9df2097ba8, Float.ofBits 0x3fd9d61f695a3792, Float.ofBits 0x3fda1d76207521f4,
    Float.ofBits 0x3fda65a76aa30140, Float.ofBits 0x3fdaaeb8d6fdf6e5, Float.ofBits 0x3fdaf8b03428ef5f,
    Float.ofBits 0x3fdb43939454806f, Float.ofBits 0x3fdb8f6951990b88, Float.ofBits 0x3fdbdc3812aeeeb5,
    Float.ofBits 0x3fdc2a06d00ea583, Float.ofBits 0x3fdc78dcd983fb60, Float.ofBits 0x3fdcc8c1dc40e092,
    Float.ofBits 0x3fdd19bde97e1a0b, Float.ofBits 0x3fdd6bd97db9ed7a, Float.ofBits 0x3fddbf1d88a7210c,
    Float.ofBits 0x3fde139375e137fc, Float.ofBits 0x3fde6945367dd351, Float.ofBits 0x3fdec03d4b969d90,
    Float.ofBits 0x3fdf1886d1eb424d, Float.ofBits 0x3fdf722d8ebfc5fa, Float.ofBits 0x3fdfcd3dfe214576,
    Float.ofBits 0x3fe014e2b160f324, Float.ofBits 0x3fe043e8ebd26548, Float.ofBits 0x3fe073b931ee3b7d,
    Float.ofBits 0x3fe0a45b8854d02a, Float.ofBits 0x3fe0d5d8812b1e2b, Float.ofBits 0x3fe108394a1cc38c,
    Float.ofBits 0x3fe13b87bc33169c, Float.ofBits 0x3fe16fce6dce6fee, Float.ofBits 0x3fe1a518c71e3b25,
    Float.ofBits 0x3fe1db7319877b89, Float.ofBits 0x3fe212eaba813ec8, Float.ofBits 0x3fe24b8e228c50a3,
    Float.ofBits 0x3fe2856d111132bd, Float.ofBits 0x3fe2c098b61f4f24, Float.ofBits 0x3fe2fd23e345da5e,
    Float.ofBits 0x3fe33b23450e6318, Float.ofBits 0x3fe37aada708ddd9, Float.ofBits 0x3fe3bbdc44e1d114,
    Float.ofBits 0x3fe3fecb2bb18b7f, Float.ofBits 0x3fe44399afa8e125, Float.ofBits 0x3fe48a6afb8ee069,
    Float.ofBits 0x3fe4d366c151f8ae, Float.ofBits 0x3fe51eba1578899a, Float.ofBits 0x3fe56c9882da8773,
    Float.ofBits 0x3fe5bd3d694cac75, Float.ofBits 0x3fe610edc1a7af66, Float.ofBits 0x3fe667fa6d4f5c06,
    Float.ofBits 0x3fe6c2c3498418c6, Float.ofBits 0x3fe721bb5ba94b63, Float.ofBits 0x3fe7856e9b09d47e,
    Float.ofBits 0x3fe7ee8a2d243126, Float.ofBits 0x3fe85de87806c5b8, Float.ofBits 0x3fe8d4a376d3d22f,
    Float.ofBits 0x3fe95431c455aa39, Float.ofBits 0x3fe9de9715556d9b, Float.ofBits 0x3fea76baa562fae7,
    Float.ofBits 0x3feb210f0ee67f2a, Float.ofBits 0x3febe5007beb7b27, Float.ofBits 0x3fecd0a65081fff0,
    Float.ofBits 0x3fee0545e5881137, Float.ofBits 0x3ff0000000000000]⟩

set_option maxRecDepth 8192 in
theorem zigX_size : zigX.size = 257 := by rfl

/-- The slow path of the exponential ziggurat after a draw at `x` in layer `i`, with two further
words `w2`, `w3`: layer 0 returns the tail `R + Exp(1)` from `w2`; another layer returns `x` if
the uniform of `w2` falls under the density in the layer's wedge, and otherwise the inverse
transform of `w3`. -/
def zigSlow (i : Nat) (x : Float) (w2 w3 : UInt64) : Float :=
  if i = 0 then zigX.get! 1 + negLogWord w2
  else
    let v := (w2 >>> 11).toFloat * twoPowNeg53
    if zigF.get! (i + 1) + (zigF.get! i - zigF.get! (i + 1)) * v < Float.exp (-x) then x
    else negLogWord w3

theorem pow_numBits_gt : 256 < 2 ^ System.Platform.numBits := by
  rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> decide

/-- The layer index `w &&& 255` as a machine word, and its successor, are table indices. -/
theorem layer_toNat (w : UInt64) : (w &&& 255).toUSize.toNat ≤ 255 ∧
    ((w &&& 255).toUSize + 1).toNat = (w &&& 255).toUSize.toNat + 1 := by
  have h1 : (w &&& 255).toUSize.toNat ≤ 255 := by
    rw [UInt64.toNat_toUSize]
    exact Nat.le_trans (Nat.mod_le _ _) (by rw [UInt64.toNat_and]; exact Nat.and_le_right)
  refine ⟨h1, ?_⟩
  have h3 : (1 : USize).toNat = 1 := by
    rcases USize.size_eq with h | h <;> simp [USize.toNat_ofNat, h]
  have := pow_numBits_gt
  rw [USize.toNat_add, h3]
  exact Nat.mod_eq_of_lt (by show _ < 2 ^ System.Platform.numBits; omega)

/-- An exponential draw by the 256-layer ziggurat: the word's low 8 bits choose the layer and
its top 52 bits the position `x` in the layer's rectangle; when `x` lies under the next layer's
width the draw ends there (98% of draws), otherwise `zigSlow` takes two more words. Each state
word is selected separately, so that a caller's continuation receives the state as four machine
words rather than a structure built on both branches. -/
@[inline] def exponential (s : Xoshiro) : Float × Xoshiro :=
  let (w, s1) := s.next
  let i := (w &&& 255).toUSize
  have h0 : i.toNat < zigX.size := by
    show (w &&& 255).toUSize.toNat < zigX.size
    rw [zigX_size]; have := (layer_toNat w).1; omega
  have h1 : (i + 1).toNat < zigX.size := by
    show ((w &&& 255).toUSize + 1).toNat < zigX.size
    rw [zigX_size, (layer_toNat w).2]; have := (layer_toNat w).1; omega
  let x := ((w >>> 12).toFloat + floatHalf) * twoPowNeg52 * zigX.uget i h0
  let fast := decide (x < zigX.uget (i + 1) h1)
  let e := if fast then x else zigSlow i.toNat x s1.next.1 s1.next.2.next.1
  let t0 := if fast then s1.s0 else s1.next.2.next.2.s0
  let t1 := if fast then s1.s1 else s1.next.2.next.2.s1
  let t2 := if fast then s1.s2 else s1.next.2.next.2.s2
  let t3 := if fast then s1.s3 else s1.next.2.next.2.s3
  (e, ⟨t0, t1, t2, t3⟩)

end Xoshiro

def hostSource : RandomSource Float Xoshiro where
  uniform s := .ok s.uniform
  exponential s := .ok s.exponential

end JumpProcessesLean
