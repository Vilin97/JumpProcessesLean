import JumpProcessesLean.Core

namespace JumpProcessesLean

structure RateBounds (α : Type) where
  lower : Array α
  upper : Array α

def checkBoundsAux {α : Type} (op : Arithmetic α) : List α → List α → List α → Nat → Except Error Unit
  | [], [], [], _ => .ok ()
  | a :: rates, lo :: lower, hi :: upper, i =>
    if validRate op lo && validRate op hi && op.le lo a && op.le a hi then
      checkBoundsAux op rates lower upper (i + 1)
    else .error (.invalidBounds i)
  | _, _, _, _ => .error .invalidShape

def checkBounds {α : Type} [Inhabited α] (op : Arithmetic α)
    (rates : Array α) (bounds : RateBounds α) : Except Error Unit := do
  checkRates op rates
  if bounds.lower.size != rates.size || bounds.upper.size != rates.size then
    throw .invalidShape
  checkBoundsAux op rates.toList bounds.lower.toList bounds.upper.toList 0

/-- The lower-bound shortcut is valid only with checked enclosing rate bounds. -/
def rssaAccept {α : Type} (op : Arithmetic α) (lower actual threshold : α) : Bool :=
  (op.lt op.zero lower && op.le threshold lower) ||
    (op.lt op.zero actual && op.le threshold actual)

/-- Rejection SSA accumulates Exp(1) proposals and divides once by the upper total,
as in JumpProcesses.jl. Fuel exhaustion is an error, never a false absorbing event. -/
def rssaProposals {α R : Type} [Inhabited α] (op : Arithmetic α)
    (src : RandomSource α R) (rates : Array α) (bounds : RateBounds α)
    (now total : α) : Nat → α → R → Except Error (Option (Event α) × R)
  | 0, _, _ => .error .proposalLimit
  | fuel + 1, elapsed, rng => do
    let (u, rng) ← drawUniform op src rng
    let j ← weightedIndex op bounds.upper (op.mul u total)
    let (e, rng) ← drawExponential op src rng
    let elapsed := op.add elapsed e
    if !op.finite elapsed then throw .invalidTime
    let (v, rng) ← drawUniform op src rng
    if rssaAccept op bounds.lower[j]! rates[j]! (op.mul v bounds.upper[j]!) then
      let time := op.add now (op.div elapsed total)
      if !(op.finite time && op.lt now time) then throw .invalidTime
      return (some ⟨time, j⟩, rng)
    else rssaProposals op src rates bounds now total fuel elapsed rng

def rssa {α R : Type} [Inhabited α] (op : Arithmetic α) (src : RandomSource α R)
    (rates : Array α) (bounds : RateBounds α) (now : α) (rng : R)
    (maxProposals : Nat := 100000) : Except Error (Option (Event α) × R) := do
  checkBounds op rates bounds
  if !op.finite now then throw .invalidTime
  let total := sumRates op bounds.upper
  if !op.finite total then throw (.invalidRate rates.size)
  -- Absorbing states are recognized even when their upper bounds are loose.
  if !(rates.any (op.lt op.zero)) then return (none, rng)
  if !op.lt op.zero total then throw .invalidShape
  rssaProposals op src rates bounds now total maxProposals op.zero rng

end JumpProcessesLean
