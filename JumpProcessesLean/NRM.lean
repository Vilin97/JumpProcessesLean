import JumpProcessesLean.Core

namespace JumpProcessesLean

structure NRMState (α : Type) where
  rates : Array α
  /-- `none` is an inactive clock, not a finite sentinel time. -/
  clocks : Array (Option α)

def nrmInitializeAux {α R : Type} (op : Arithmetic α)
    (src : RandomSource α R) (now : α) :
    List α → R → Except Error (List (Option α) × R)
  | [], rng => .ok ([], rng)
  | a :: rest, rng => do
    let (clock, rng) ← if op.lt op.zero a then do
      let (e, r) ← drawExponential op src rng
      let time := op.add now (op.div e a)
      if !(op.finite time && op.lt now time) then throw .invalidTime
      pure (some time, r)
    else pure (none, rng)
    let (clocks, rng) ← nrmInitializeAux op src now rest rng
    return (clock :: clocks, rng)

def nrmInitialize {α R : Type} [Inhabited α] (op : Arithmetic α)
    (src : RandomSource α R) (rates : Array α) (now : α) (rng : R) :
    Except Error (NRMState α × R) := do
  checkRates op rates
  if !op.finite now then throw .invalidTime
  let (clocks, rng) ← nrmInitializeAux op src now rates.toList rng
  return (⟨rates, clocks.toArray⟩, rng)

def nrmNextAux {α : Type} (op : Arithmetic α) :
    List (Option α) → Nat → Option (Event α)
  | [], _ => none
  | none :: rest, i => nrmNextAux op rest (i + 1)
  | some t :: rest, i =>
    match nrmNextAux op rest (i + 1) with
    | none => some ⟨t, i⟩
    | some e => if op.le t e.time then some ⟨t, i⟩ else some e

/-- A linear argmin preserves NRM clocks; heap optimization can refine this operation later. -/
def nrmNext {α : Type} (op : Arithmetic α) (state : NRMState α) : Option (Event α) :=
  nrmNextAux op state.clocks.toList 0

/-- Gibson–Bruck residual-clock update, shared by real and rounded instantiations. -/
def rescaleClock {α : Type} (op : Arithmetic α) (now oldRate newRate oldTime : α) : α :=
  op.add now (op.mul (op.div oldRate newRate) (op.sub oldTime now))

/-- Complete-dependency updates traverse channels in index order. Each clock uses the
old state, so updates cannot accidentally feed a changed clock into another update. -/
def nrmUpdateAllAux {α R : Type} (op : Arithmetic α) (src : RandomSource α R)
    (fired : Nat) (now : α) :
    List α → List (Option α) → List α → Nat → R →
      Except Error (List (Option α) × R)
  | [], [], [], _, rng => .ok ([], rng)
  | old :: olds, clock :: clocks, new :: news, j, rng => do
    let (clock, rng) ← if !op.lt op.zero new then pure (none, rng)
      else if j != fired && op.lt op.zero old then do
        let some time := clock | throw .invalidShape
        if !op.le now time then throw .invalidTime
        let time := rescaleClock op now old new time
        if !(op.finite time && op.le now time) then throw .invalidTime
        pure (some time, rng)
      else do
        let (e, rng) ← drawExponential op src rng
        let time := op.add now (op.div e new)
        if !(op.finite time && op.lt now time) then throw .invalidTime
        pure (some time, rng)
    let (clocks, rng) ← nrmUpdateAllAux op src fired now olds clocks news (j + 1) rng
    return (clock :: clocks, rng)
  | _, _, _, _, _ => .error .invalidShape

/-- Fired and reactivated channels draw fresh clocks; positive nonfiring channels rescale.
The caller must supply a sound dependency graph. The simulation driver uses the full graph. -/
def nrmUpdate {α R : Type} [Inhabited α] (op : Arithmetic α)
    (src : RandomSource α R) (state : NRMState α) (newRates : Array α)
    (fired : Nat) (now : α) (dependencies : Array Nat) (rng : R) :
    Except Error (NRMState α × R) := do
  if state.rates.size != newRates.size || state.clocks.size != newRates.size ||
      fired >= newRates.size then throw .invalidShape
  checkRates op newRates
  if !op.finite now then throw .invalidTime
  if dependencies.toList = List.range newRates.size then
    let (clocks, rng) ← nrmUpdateAllAux op src fired now state.rates.toList
      state.clocks.toList newRates.toList 0 rng
    return (⟨newRates, clocks.toArray⟩, rng)
  let mut clocks := state.clocks
  let mut rates := state.rates
  let mut rng := rng
  -- Self-dependency is mandatory and duplicates must not consume extra samples.
  let deps := (dependencies.toList ++ [fired]).eraseDups
  for j in deps do
    if j >= newRates.size then throw (.invalidDependency j)
    let oldRate := state.rates[j]!
    let newRate := newRates[j]!
    rates := rates.set! j newRate
    if !op.lt op.zero newRate then clocks := clocks.set! j none
    else if j != fired && op.lt op.zero oldRate then
      let some oldTime := state.clocks[j]! | throw .invalidShape
      if !op.le now oldTime then throw .invalidTime
      let time := rescaleClock op now oldRate newRate oldTime
      if !(op.finite time && op.le now time) then throw .invalidTime
      clocks := clocks.set! j (some time)
    else
      let (e, r) ← drawExponential op src rng
      rng := r
      let time := op.add now (op.div e newRate)
      if !(op.finite time && op.lt now time) then throw .invalidTime
      clocks := clocks.set! j (some time)
  return (⟨rates, clocks⟩, rng)

end JumpProcessesLean
