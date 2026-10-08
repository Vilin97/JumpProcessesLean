import JumpProcessesLean.TreeRSSA.Gen2

/-!
# Tree-RSSA, generation 3: batched tree updates and compiled propensities

Profiling generation 2 on the large networks showed bracket refreshes dominating: a species
with thousands of dependent reactions re-added thousands of root paths, recomputing shared
ancestors many times, and every propensity folded over a reactant array.

Generation 3:

* re-adds the paths of the changed leaves of one refresh together: walking the dependents
  in order, the path of a changed leaf is re-added only up to where it meets the path of the
  next changed leaf, so an ancestor shared by several changed leaves is added once, after
  both its children are final. Nothing is allocated;
* compiles each reaction's integer mass-action factor: one or two reactant species with
  stoichiometry one or two are evaluated directly, other reactions use `combinations`.

Both compute the same values as generation 2: the tree nodes are the same sums of the same
children, and the integer factor is the same natural number. `Gen3.simulate` is proved equal
to `TreeRSSA.simulate hostArithmetic hostSource` (`Proofs/TreeRSSAGen3.lean`).
-/

namespace JumpProcessesLean.TreeRSSA.Gen3

open Gen1 (Cache fixPath descend buildTree)

/-- A reaction's mass-action factor in compiled form. -/
inductive Factor where
  /-- `n_s` -/
  | one (s : Nat)
  /-- `n_s (n_s - 1)` -/
  | two (s : Nat)
  /-- `f₁ · f₂` for two distinct reactants with stoichiometry at most two -/
  | pair (s : Nat) (ν : Nat) (t : Nat) (μ : Nat)
  /-- any other reactant list -/
  | general (reactants : Array (Nat × Nat))
  deriving Inhabited

@[inline] def ff (n ν : Nat) : Nat :=
  if ν = 1 then n else n * (n - 1)

def Factor.compile (reactants : Array (Nat × Nat)) : Factor :=
  match reactants.toList with
  | [(s, 1)] => .one s
  | [(s, 2)] => .two s
  | [(s, ν), (t, μ)] => if 1 ≤ ν ∧ ν ≤ 2 ∧ 1 ≤ μ ∧ μ ≤ 2 then .pair s ν t μ else .general reactants
  | _ => .general reactants

@[inline] def Factor.eval (f : Factor) (pop : Array Nat) : Nat :=
  match f with
  | .one s => pop[s]!
  | .two s => pop[s]! * (pop[s]! - 1)
  | .pair s ν t μ => ff pop[s]! ν * ff pop[t]! μ
  | .general rs => combinations rs pop

/-- Immutable data compiled once from the network. -/
structure Compiled where
  net : Network Float
  ms : Array Nat
  deps : Array (Array Nat)
  depth : Nat
  leaves : Nat
  numRx : Nat
  rates : FloatArray
  factors : Array Factor

def compile (net : Network Float) : Compiled :=
  ⟨net, net.maxStoich, net.speciesDependents, treeDepth net.reactions.size,
    2 ^ treeDepth net.reactions.size, net.reactions.size,
    ⟨net.reactions.map (·.rate)⟩, net.reactions.map (Factor.compile ·.reactants)⟩

@[inline] def rate (C : Compiled) (k : Nat) (pop : Array Nat) : Float :=
  C.rates.get! k * natToFloat (C.factors[k]!.eval pop)

/-- Re-add the strict ancestors of `node` that are not ancestors of `other`, a node on the
same level: the path of `node` up to where it meets the path of `other`. -/
def fixUntil (tree : FloatArray) : Nat → Nat → Nat → FloatArray
  | 0, _, _ => tree
  | n + 1, node, other =>
    let k := node / 2
    if k = other / 2 then tree
    else fixUntil (tree.set! k (tree.get! (2 * k) + tree.get! (2 * k + 1))) n k (other / 2)

/-- Evaluate both bounds of the dependents `deps[deps.size - i], …` and write the changed
upper bounds to their leaves. `pending` is the last changed leaf (`0` if none), whose path is
not yet re-added: when the next leaf changes, the pending path is re-added up to where it
meets the new leaf's path, which is re-added later. The last path goes up to the root. -/
def setBounds (C : Compiled) (lo hi : Array Nat) (deps : Array Nat) :
    Nat → FloatArray → FloatArray → Nat → FloatArray × FloatArray
  | 0, lower, tree, pending => (lower, if pending = 0 then tree else fixPath tree C.depth pending)
  | i + 1, lower, tree, pending =>
    let k := deps[deps.size - (i + 1)]!
    let leaf := C.leaves + k
    let upper := rate C k hi
    let lower := lower.set! k (rate C k lo)
    if upper.toBits == (tree.get! leaf).toBits then setBounds C lo hi deps i lower tree pending
    else
      let tree := if pending = 0 then tree else fixUntil tree C.depth pending leaf
      setBounds C lo hi deps i lower (tree.set! leaf upper) leaf

def refresh (C : Compiled) (pop : Array Nat) (c : Cache) (s : Nat) : Cache :=
  if stale C.ms[s]! pop[s]! c.lo[s]! c.hi[s]! then
    let lo := c.lo.set! s (bracket C.ms[s]! pop[s]!).1
    let hi := c.hi.set! s (bracket C.ms[s]! pop[s]!).2
    let deps := C.deps[s]!
    let (lower, tree) := setBounds C lo hi deps deps.size c.lower c.tree 0
    ⟨lo, hi, lower, tree⟩
  else c

def fire (C : Compiled) (pop : Array Nat) (c : Cache) (j : Nat) : Array Nat × Cache :=
  let pop := (changesOf C.net j).foldl applyChange pop
  (pop, (changesOf C.net j).foldl (fun c ch => refresh C pop c ch.1) c)

def proposals (C : Compiled) (pop : Array Nat) (lower tree : FloatArray) (now total : Float) :
    Nat → Float → Xoshiro → Except Error (Option (Event Float) × Xoshiro)
  | 0, _, _ => .error .proposalLimit
  | fuel + 1, elapsed, rng =>
    let (u, rng) := rng.uniform
    if !(u.isFinite && decide (floatZero ≤ u) && decide (u < floatOne)) then .error .invalidUniform
    else
      let j := descend tree C.depth 1 (u * total) - C.leaves
      let (e, rng) := rng.exponential
      if !(e.isFinite && decide (floatZero < e)) then .error .invalidExponential
      else
        let elapsed := elapsed + e
        if !elapsed.isFinite then .error .invalidTime
        else
          let (v, rng) := rng.uniform
          if !(v.isFinite && decide (floatZero ≤ v) && decide (v < floatOne)) then .error .invalidUniform
          else if j < C.numRx &&
              Gen2.accept (lower.get! j) (rate C j pop) (v * tree.get! (C.leaves + j)) then
            let time := now + elapsed / total
            if !(time.isFinite && decide (now < time)) then .error .invalidTime
            else .ok (some ⟨time, j⟩, rng)
          else proposals C pop lower tree now total fuel elapsed rng

def event (C : Compiled) (pop : Array Nat) (c : Cache) (now : Float) (rng : Xoshiro)
    (maxProposals : Nat) : Except Error (Option (Event Float) × Xoshiro) :=
  let total := c.tree.get! 1
  if !total.isFinite then .error (.invalidRate C.numRx)
  else if !decide (floatZero < total) then .ok (none, rng)
  else proposals C pop c.lower c.tree now total maxProposals floatZero rng

def loop (C : Compiled) (horizon : Float) (saveEvents : Bool) (maxProposals : Nat) :
    Nat → Array Nat → Cache → Float → Xoshiro → Nat → Array (Float × State) →
      Except Error (Solution Float State Xoshiro)
  | 0, pop, c, now, rng, count, trace =>
    match event C pop c now rng maxProposals with
    | .error err => .error err
    | .ok (none, rng) =>
      .ok ⟨⟨pop, c.lo, c.hi⟩, horizon, count, rng, trace.push (horizon, ⟨pop, c.lo, c.hi⟩)⟩
    | .ok (some e, rng) =>
      if !decide (now ≤ e.time) || !e.time.isFinite then .error .invalidTime
      else if !decide (e.time ≤ horizon) then
        .ok ⟨⟨pop, c.lo, c.hi⟩, horizon, count, rng, trace.push (horizon, ⟨pop, c.lo, c.hi⟩)⟩
      else .error .eventLimit
  | fuel + 1, pop, c, now, rng, count, trace =>
    match event C pop c now rng maxProposals with
    | .error err => .error err
    | .ok (none, rng) =>
      .ok ⟨⟨pop, c.lo, c.hi⟩, horizon, count, rng, trace.push (horizon, ⟨pop, c.lo, c.hi⟩)⟩
    | .ok (some e, rng) =>
      if !decide (now ≤ e.time) || !e.time.isFinite then .error .invalidTime
      else if !decide (e.time ≤ horizon) then
        .ok ⟨⟨pop, c.lo, c.hi⟩, horizon, count, rng, trace.push (horizon, ⟨pop, c.lo, c.hi⟩)⟩
      else
        let (pop, c) := fire C pop c e.reaction
        let trace := if saveEvents then trace.push (e.time, ⟨pop, c.lo, c.hi⟩) else trace
        loop C horizon saveEvents maxProposals fuel pop c e.time rng (count + 1) trace

def initialCache (C : Compiled) (st : State) : Cache :=
  ⟨st.lo, st.hi, ⟨C.net.reactions.map (Gen2.rate · st.lo)⟩,
    buildTree (C.net.reactions.map (Gen2.rate · st.hi)) C.depth⟩

def simulate (net : Network Float) (initial : State) (start horizon : Float) (rng : Xoshiro)
    (maxEvents : Nat := 1000000) (saveEvents : Bool := false) (maxProposals : Nat := 100000) :
    Except Error (Solution Float State Xoshiro) :=
  if !(start.isFinite && horizon.isFinite && decide (start ≤ horizon)) then .error .invalidTime
  else if !decide (start < horizon) then .ok ⟨initial, horizon, 0, rng, #[(start, initial)]⟩
  else
    let C := compile net
    loop C horizon saveEvents maxProposals maxEvents initial.pop (initialCache C initial) start rng 0
      #[(start, initial)]

end JumpProcessesLean.TreeRSSA.Gen3
