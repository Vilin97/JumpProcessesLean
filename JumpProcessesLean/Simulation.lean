import JumpProcessesLean.Direct
import JumpProcessesLean.NRM
import JumpProcessesLean.RSSA

namespace JumpProcessesLean

inductive Algorithm where
  | direct | nrm | rssa
  deriving Repr, BEq

/-- Homogeneous pure-jump model: propensities remain constant between events. -/
structure Model (α σ : Type) where
  rates : σ → Array α
  transition : σ → Nat → Except Error σ
  bounds : σ → RateBounds α

structure Solution (α σ R : Type) where
  state : σ
  time : α
  events : Nat
  rng : R
  /-- Initial state, post-jump states, and final horizon. -/
  trace : Array (α × σ)

def simulateLoop {α σ R : Type} [Inhabited α] (op : Arithmetic α)
    (src : RandomSource α R) (model : Model α σ) (algorithm : Algorithm)
    (horizon : α) (saveEvents : Bool) (maxProposals : Nat) :
    Nat → σ → α → R → Option (NRMState α) → Nat → Array (α × σ) →
      Except Error (Solution α σ R)
  | fuel, state, now, rng, nrmState, count, trace => do
    let rates := model.rates state
    let (event, rng) ← match algorithm with
      | .direct => direct op src rates now rng
      | .rssa => rssa op src rates (model.bounds state) now rng maxProposals
      | .nrm => match nrmState with
        | some s => pure (nrmNext op s, rng)
        | none => throw .invalidShape
    match event with
    | none => return ⟨state, horizon, count, rng, trace.push (horizon, state)⟩
    | some e =>
      if !op.le now e.time || !op.finite e.time then throw .invalidTime
      if !op.le e.time horizon then
        return ⟨state, horizon, count, rng, trace.push (horizon, state)⟩
      match fuel with
      | 0 => throw .eventLimit
      | fuel + 1 =>
        let newState ← model.transition state e.reaction
        let (nextNRM, rng) ← match algorithm, nrmState with
          | .nrm, some s => do
            let newRates := model.rates newState
            let deps := (List.range newRates.size).toArray
            let (s, rng) ← nrmUpdate op src s newRates e.reaction e.time deps rng
            pure (some s, rng)
          | _, _ => pure (none, rng)
        let trace := if saveEvents then trace.push (e.time, newState) else trace
        simulateLoop op src model algorithm horizon saveEvents maxProposals
          fuel newState e.time rng nextNRM (count + 1) trace

def simulate {α σ R : Type} [Inhabited α] (op : Arithmetic α)
    (src : RandomSource α R) (model : Model α σ) (algorithm : Algorithm)
    (initial : σ) (start horizon : α) (rng : R) (maxEvents : Nat := 1000000)
    (saveEvents : Bool := false) (maxProposals : Nat := 100000) :
    Except Error (Solution α σ R) := do
  if !(op.finite start && op.finite horizon && op.le start horizon) then throw .invalidTime
  if !op.lt start horizon then return ⟨initial, horizon, 0, rng, #[(start, initial)]⟩
  let (nrmState, rng) ← match algorithm with
    | .nrm => do
      let (s, rng) ← nrmInitialize op src (model.rates initial) start rng
      pure (some s, rng)
    | _ => pure (none, rng)
  simulateLoop op src model algorithm horizon saveEvents maxProposals maxEvents
    initial start rng nrmState 0 #[(start, initial)]

/-- Integer population brackets following upstream defaults (relative 10%, threshold 25, width 4).
The relative branch uses exact integer arithmetic rather than converting populations to floats. -/
def populationBracket (n : Nat) (threshold : Nat := 25) (width : Nat := 4)
    (relativeNumerator : Nat := 1) (relativeDenominator : Nat := 10) : Nat × Nat :=
  if n == 0 then (0, 0)
  else if n < threshold then (n - width, n + width)
  else ((relativeDenominator - relativeNumerator) * n / relativeDenominator,
    (relativeDenominator + relativeNumerator) * n / relativeDenominator)

def fallingFactorial : Nat → Nat → Nat
  | _, 0 => 1
  | n, k + 1 => if n < k + 1 then 0 else fallingFactorial n k * (n - k)

structure MassActionReaction (α : Type) where
  /-- Coefficient already scaled by the reactant factorials, as in `scaled_rates`. -/
  scaledRate : α
  reactants : Array (Nat × Nat)
  changes : Array (Nat × Int)

def massActionRate {α : Type} (op : Arithmetic α) (rx : MassActionReaction α)
    (population : Array Nat) : Except Error α := do
  let mut rate := rx.scaledRate
  for (species, stoich) in rx.reactants do
    if species >= population.size then throw .invalidShape
    rate := op.mul rate (op.ofNat (fallingFactorial population[species]! stoich))
  return rate

def massActionTransition {α : Type} (rx : MassActionReaction α)
    (population : Array Nat) : Except Error (Array Nat) := do
  let mut result := population
  for (species, change) in rx.changes do
    if species >= result.size then throw .invalidShape
    let value := (result[species]! : Int) + change
    if value < 0 then throw .negativePopulation
    result := result.set! species value.toNat
  return result

end JumpProcessesLean

