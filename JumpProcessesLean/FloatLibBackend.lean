import JumpProcessesLean.Core
import FloatLib.Floats.Formats.BinaryInterchange.Configured.NativeDispatch
import FloatLib.Floats.Formats.BinaryInterchange.Configured.Instances
import FloatLib.Floats.Formats.BinaryInterchange.Configured.Transcendentals
import FloatLib.Floats.ExecFloat.Proof.Arithmetic

namespace JumpProcessesLean

open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange

abbrev Binary64 := ExecFloat.Binary (exponentBits := 11) (fractionBits := 52)

def binary64Arithmetic : Arithmetic Binary64 where
  zero := 0
  one := 1
  add := (· + ·)
  sub := (· - ·)
  mul := (· * ·)
  div := (· / ·)
  lt a b := decide (a < b)
  le a b := decide (a ≤ b)
  finite := ExecFloat.Binary.isFinite
  ofNat n := ExecFloat.Binary.ofModel (Model.roundRatQ _ (n : Rat))

/-- SplitMix64 is only an executable source; the ideal-source probability proofs do not
claim independent randomness from a finite seed. All sampling arithmetic uses FloatLib. -/
def splitMix64 (s : UInt64) : UInt64 × UInt64 :=
  let s := s + 0x9e3779b97f4a7c15
  let z := (s ^^^ (s >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb
  (z ^^^ (z >>> 31), s)

def binary64Uniform (s : UInt64) : Binary64 × UInt64 :=
  let (word, s) := splitMix64 s
  -- 52 random bits in the significand produce an exact point in [0,1).
  let bits := (word >>> 12).toNat + 0x3ff0000000000000
  (ExecFloat.Binary.ofNatBits bits - 1, s)

/-- Cache FloatLib's generated constants once, including its argument-reduction data. -/
def binary64LogConfig : Model.Transcendentals.Config :=
  Model.Transcendentals.Config.forFormat FloatFormat.binary64

def binary64Log (u : Binary64) : Binary64 :=
  ExecFloat.Binary.ofModel (Model.logWith binary64LogConfig (ExecFloat.Binary.toModel u))

/-- Configuration reuse changes execution cost, not the FloatLib result. -/
theorem binary64Log_eq_builtin (u : Binary64) : binary64Log u = ExecFloat.Binary.log u := rfl

/-- Open-interval input prevents log(0) and log(1). Rejected endpoints consume a new word. -/
def binary64Exponential : Nat → UInt64 → Except Error (Binary64 × UInt64)
  | 0, _ => .error .exhaustedRandomness
  | fuel + 1, s =>
    let (u, s) := binary64Uniform s
    if u == 0 then binary64Exponential fuel s
    else .ok (-binary64Log u, s)

def binary64Source : RandomSource Binary64 UInt64 where
  uniform s := .ok (binary64Uniform s)
  exponential s := binary64Exponential 1024 s

/-- Optional certified logarithm path: failure is propagated, never silently approximated. -/
def binary64CertifiedExponential : Nat → UInt64 → Except Error (Binary64 × UInt64)
  | 0, _ => .error .exhaustedRandomness
  | fuel + 1, s =>
    let (u, s) := binary64Uniform s
    if u == 0 then binary64CertifiedExponential fuel s
    else match ExecFloat.Binary.Certified.log u with
      | none => .error .transcendentalFailure
      | some l => .ok (-l, s)

def binary64CertifiedSource : RandomSource Binary64 UInt64 where
  uniform s := .ok (binary64Uniform s)
  exponential s := binary64CertifiedExponential 1024 s

/-- Every executable add uses FloatLib's proved nearest-even specification. -/
theorem binary64_add_eq_spec (a b : Binary64) :
    binary64Arithmetic.add a b = ExecFloat.Spec.add a b :=
  ExecFloat.Proof.add_eq_spec a b

theorem binary64_div_eq_spec (a b : Binary64) :
    binary64Arithmetic.div a b = ExecFloat.Spec.div a b :=
  ExecFloat.Proof.div_eq_spec a b

end JumpProcessesLean
