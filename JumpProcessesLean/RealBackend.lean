import JumpProcessesLean.Core
import Mathlib.Basic.Real.Basic

namespace JumpProcessesLean

/-- Real-valued interpretation of the very same arithmetic-parameterized algorithms. -/
noncomputable def realArithmetic : Arithmetic ℝ where
  zero := 0
  one := 1
  add := (· + ·)
  sub := (· - ·)
  mul := (· * ·)
  div := (· / ·)
  lt a b := decide (a < b)
  le a b := decide (a ≤ b)
  finite _ := true
  ofNat := Nat.cast

end JumpProcessesLean
