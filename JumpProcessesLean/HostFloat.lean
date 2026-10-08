import JumpProcessesLean.Core

/-!
# Host floating point and a fast generator

`hostArithmetic` instantiates the generic algorithms at Lean's native `Float`. Its logical
definitions follow Lean's binary64 model; compiled code calls the host's IEEE operations.
`Xoshiro` is xoshiro256++ (Blackman–Vigna), seeded through SplitMix64. Like SplitMix64 in
`FloatLibBackend`, it is an executable source only: no theorem claims that its outputs are
independent uniforms.
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

/-- `-log V` for `V = (k + 1/2) / 2^52`, which never takes the values `0` or `1`. -/
@[inline] def exponential (s : Xoshiro) : Float × Xoshiro :=
  let (w, s) := s.next
  let v := ((w >>> 12).toFloat + floatHalf) * twoPowNeg52
  (-(Float.log v), s)

end Xoshiro

def hostSource : RandomSource Float Xoshiro where
  uniform s := .ok s.uniform
  exponential s := .ok s.exponential

end JumpProcessesLean
