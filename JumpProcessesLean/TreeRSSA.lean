import JumpProcessesLean.Network

/-!
# Tree-RSSA: the reference specification

Tree-RSSA is a rejection SSA for mass-action networks. Every species has a population
bracket; every reaction has lower and upper propensity bounds evaluated at the bracket
ends. A proposal is drawn from the upper bounds by descending a complete binary sum tree,
then accepted by the RSSA thinning test (lower bound first, exact propensity only when
needed). Brackets are refreshed only for species whose population leaves them.

Below the largest reactant stoichiometry of a species its bracket is exact. Then a
reaction has a positive upper bound only if it is enabled, and the root of the tree
decides absorption without evaluating any propensity.

This file is the *specification*: it recomputes every bound and every tree node from the
state, so one event costs time proportional to the network size. Its real-arithmetic
instance is the native `rssa` driver on the bracket model
(`Proofs/TreeRSSACorrect.lean`). The optimized implementations in `TreeRSSA/` are proved
equal to it for every input.
-/

namespace JumpProcessesLean.TreeRSSA

variable {α R : Type}

/-- The integer mass-action factor `Π_s n_s (n_s - 1) ⋯ (n_s - ν_s + 1)`. -/
def combinations (reactants : Array (Nat × Nat)) (pop : Array Nat) : Nat :=
  reactants.foldl (fun acc p => acc * fallingFactorial pop[p.1]! p.2) 1

def propensity (op : Arithmetic α) (rx : Reaction α) (pop : Array Nat) : α :=
  op.mul rx.rate (op.ofNat (combinations rx.reactants pop))

/-- Population bracket: exact below the largest reactant stoichiometry `ms`, `±4` below
25, and `±10%` above, as in JumpProcesses.jl's RSSA. -/
def bracket (ms n : Nat) : Nat × Nat :=
  if n = 0 then (0, 0)
  else if n < ms then (n, n)
  else if n < 25 then (n - 4, n + 4)
  else (9 * n / 10, 11 * n / 10)

structure State where
  pop : Array Nat
  lo : Array Nat
  hi : Array Nat
  deriving Inhabited, BEq, Repr

def initialState {α : Type} (net : Network α) (pop : Array Nat) : State :=
  let ms := net.maxStoich
  ⟨pop, (Array.range pop.size).map fun s => (bracket ms[s]! pop[s]!).1,
    (Array.range pop.size).map fun s => (bracket ms[s]! pop[s]!).2⟩

/-- A bracket is stale when the population left it, or fell below the largest reactant
stoichiometry while the bracket is not exact. -/
def stale (ms n lo hi : Nat) : Bool :=
  n < lo || hi < n || (n < ms && hi != n)

def applyChange (pop : Array Nat) (c : Nat × Int) : Array Nat :=
  pop.set! c.1 (((pop[c.1]! : Int) + c.2).toNat)

def refreshBracket (ms : Array Nat) (st : State) (s : Nat) : State :=
  if stale ms[s]! st.pop[s]! st.lo[s]! st.hi[s]! then
    { st with lo := st.lo.set! s (bracket ms[s]! st.pop[s]!).1,
              hi := st.hi.set! s (bracket ms[s]! st.pop[s]!).2 }
  else st

/-- Fire reaction `j`: apply its net changes, then refresh the brackets of the changed
species. -/
def changesOf (net : Network α) (j : Nat) : Array (Nat × Int) :=
  match net.reactions[j]? with
  | some rx => rx.changes
  | none => #[]

def fire (net : Network α) (ms : Array Nat) (st : State) (j : Nat) : State :=
  let st := { st with pop := (changesOf net j).foldl applyChange st.pop }
  (changesOf net j).foldl (fun st c => refreshBracket ms st c.1) st

/-! ### The binary sum tree -/

def leafOf (op : Arithmetic α) (w : Array α) (i : Nat) : α :=
  if h : i < w.size then w[i] else op.zero

/-- Sum of the `2^d` leaves starting at `lo`, as a complete binary tree. -/
def segSum (op : Arithmetic α) (w : Array α) : Nat → Nat → α
  | 0, lo => leafOf op w lo
  | d + 1, lo => op.add (segSum op w d lo) (segSum op w d (lo + 2 ^ d))

/-- Descend the tree of `2^d` leaves from `lo`, subtracting left sums on the way right. -/
def segDescend (op : Arithmetic α) (w : Array α) : Nat → Nat → α → Nat
  | 0, lo, _ => lo
  | d + 1, lo, x =>
    if op.lt x (segSum op w d lo) then segDescend op w d lo x
    else segDescend op w d (lo + 2 ^ d) (op.sub x (segSum op w d lo))

/-- Depth of the tree over `m` leaves; `m ≤ 2 ^ treeDepth m`. -/
def treeDepth (m : Nat) : Nat := Nat.log2 (m - 1) + 1

/-! ### One event -/

def lowerBounds [Inhabited α] (op : Arithmetic α) (net : Network α) (st : State) : Array α :=
  net.reactions.map (propensity op · st.lo)

def upperBounds [Inhabited α] (op : Arithmetic α) (net : Network α) (st : State) : Array α :=
  net.reactions.map (propensity op · st.hi)

/-- The thinning loop. The time accumulates `Exp(1)` draws and divides once by the upper
total, as in JumpProcesses.jl. -/
def proposals [Inhabited α] (op : Arithmetic α) (src : RandomSource α R) (net : Network α)
    (pop : Array Nat) (lower upper : Array α) (d : Nat) (now total : α) :
    Nat → α → R → Except Error (Option (Event α) × R)
  | 0, _, _ => .error .proposalLimit
  | fuel + 1, elapsed, rng => do
    let (u, rng) ← drawUniform op src rng
    let j := segDescend op upper d 0 (op.mul u total)
    let (e, rng) ← drawExponential op src rng
    let elapsed := op.add elapsed e
    if !op.finite elapsed then throw .invalidTime
    let (v, rng) ← drawUniform op src rng
    if j < net.reactions.size &&
        rssaAccept op lower[j]! (propensity op net.reactions[j]! pop) (op.mul v upper[j]!) then
      let time := op.add now (op.div elapsed total)
      if !(op.finite time && op.lt now time) then throw .invalidTime
      return (some ⟨time, j⟩, rng)
    else proposals op src net pop lower upper d now total fuel elapsed rng

def event [Inhabited α] (op : Arithmetic α) (src : RandomSource α R) (net : Network α)
    (st : State) (now : α) (rng : R) (maxProposals : Nat) :
    Except Error (Option (Event α) × R) :=
  let lower := lowerBounds op net st
  let upper := upperBounds op net st
  let d := treeDepth net.reactions.size
  let total := segSum op upper d 0
  if !op.finite total then .error (.invalidRate net.reactions.size)
  else if !op.lt op.zero total then .ok (none, rng)
  else proposals op src net st.pop lower upper d now total maxProposals op.zero rng

/-! ### The driver -/

/-- Same control flow as the public `simulateLoop`, with the state carrying brackets. -/
def simulateLoop [Inhabited α] (op : Arithmetic α) (src : RandomSource α R) (net : Network α)
    (ms : Array Nat) (horizon : α) (saveEvents : Bool) (maxProposals : Nat) :
    Nat → State → α → R → Nat → Array (α × State) → Except Error (Solution α State R)
  | fuel, st, now, rng, count, trace => do
    let (event, rng) ← event op src net st now rng maxProposals
    match event with
    | none => return ⟨st, horizon, count, rng, trace.push (horizon, st)⟩
    | some e =>
      if !op.le now e.time || !op.finite e.time then throw .invalidTime
      if !op.le e.time horizon then
        return ⟨st, horizon, count, rng, trace.push (horizon, st)⟩
      match fuel with
      | 0 => throw .eventLimit
      | fuel + 1 =>
        let st := fire net ms st e.reaction
        let trace := if saveEvents then trace.push (e.time, st) else trace
        simulateLoop op src net ms horizon saveEvents maxProposals fuel st e.time rng (count + 1)
          trace

def simulate [Inhabited α] (op : Arithmetic α) (src : RandomSource α R) (net : Network α)
    (initial : State) (start horizon : α) (rng : R) (maxEvents : Nat := 1000000)
    (saveEvents : Bool := false) (maxProposals : Nat := 100000) :
    Except Error (Solution α State R) := do
  if !(op.finite start && op.finite horizon && op.le start horizon) then throw .invalidTime
  if !op.lt start horizon then return ⟨initial, horizon, 0, rng, #[(start, initial)]⟩
  simulateLoop op src net net.maxStoich horizon saveEvents maxProposals maxEvents initial start
    rng 0 #[(start, initial)]

end JumpProcessesLean.TreeRSSA
