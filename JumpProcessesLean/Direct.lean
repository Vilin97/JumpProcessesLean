import JumpProcessesLean.Core

namespace JumpProcessesLean

/-- Direct SSA: cumulative propensity selection and one total-rate exponential clock. -/
def direct {α R : Type} [Inhabited α] (op : Arithmetic α) (src : RandomSource α R)
    (rates : Array α) (now : α) (rng : R) : Except Error (Option (Event α) × R) := do
  checkRates op rates
  if !op.finite now then throw .invalidTime
  let total := sumRates op rates
  if !op.finite total then throw (.invalidRate rates.size)
  if !op.lt op.zero total then return (none, rng)
  let (e, rng) ← drawExponential op src rng
  let (u, rng) ← drawUniform op src rng
  let reaction ← weightedIndex op rates (op.mul u total)
  let time := op.add now (op.div e total)
  if !(op.finite time && op.lt now time) then throw .invalidTime
  return (some ⟨time, reaction⟩, rng)

end JumpProcessesLean

