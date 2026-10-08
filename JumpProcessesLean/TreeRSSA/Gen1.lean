import JumpProcessesLean.TreeRSSA
import JumpProcessesLean.HostFloat

/-!
# Tree-RSSA, generation 1: incremental bounds and an array sum tree

The specification recomputes every bound and tree node at every event. This generation
keeps the lower bounds in a `FloatArray` and the upper bounds as the leaves of a flat
binary sum tree (`tree[k] = tree[2k] + tree[2k+1]`, leaves at `2^d + j`). When a bracket
is refreshed, only the reactions that use the species are re-evaluated, and only their
root paths are re-added. All loops are structural, so `Gen1.simulate` can be proved equal
to `TreeRSSA.simulate hostArithmetic hostSource` (`Proofs/TreeRSSAGen1.lean`).
-/

namespace JumpProcessesLean.TreeRSSA.Gen1

/-- Immutable data compiled once from the network. -/
structure Compiled where
  net : Network Float
  ms : Array Nat
  deps : Array (Array Nat)
  depth : Nat

def compile (net : Network Float) : Compiled :=
  ⟨net, net.maxStoich, net.speciesDependents, treeDepth net.reactions.size⟩

/-- Re-add the `n` ancestors of node `k`. -/
def fixPath (tree : FloatArray) : Nat → Nat → FloatArray
  | 0, _ => tree
  | n + 1, k =>
    let k := k / 2
    fixPath (tree.set! k (tree.get! (2 * k) + tree.get! (2 * k + 1))) n k

/-- Leaves `2^d + i` hold `upper[i]` (zero padding); internal nodes are filled later. -/
def leafArray (upper : Array Float) (d : Nat) : FloatArray :=
  ⟨Array.ofFn (n := 2 * 2 ^ d) fun k =>
    if 2 ^ d ≤ k.val then leafOf hostArithmetic upper (k.val - 2 ^ d) else 0⟩

/-- Fill the internal nodes `k - 1, …, 1` bottom-up. -/
def fill (tree : FloatArray) : Nat → FloatArray
  | 0 => tree
  | k + 1 =>
    if k = 0 then tree
    else fill (tree.set! k (tree.get! (2 * k) + tree.get! (2 * k + 1))) k

/-- Build the tree over `upper`: leaves, then nodes `2^d - 1, …, 1`. -/
def buildTree (upper : Array Float) (d : Nat) : FloatArray :=
  fill (leafArray upper d) (2 ^ d)

/-- Descend `n` levels from node `k`. -/
def descend (tree : FloatArray) : Nat → Nat → Float → Nat
  | 0, k, _ => k
  | n + 1, k, x =>
    let left := tree.get! (2 * k)
    if x < left then descend tree n (2 * k) x else descend tree n (2 * k + 1) (x - left)

/-- Re-evaluate both bounds of reaction `k`. -/
def updateBounds (C : Compiled) (lo hi : Array Nat) (bounds : FloatArray × FloatArray)
    (k : Nat) : FloatArray × FloatArray :=
  let rx := C.net.reactions[k]!
  let leaf := 2 ^ C.depth + k
  (bounds.1.set! k (propensity hostArithmetic rx lo),
    fixPath (bounds.2.set! leaf (propensity hostArithmetic rx hi)) C.depth leaf)

structure Cache where
  lo : Array Nat
  hi : Array Nat
  lower : FloatArray
  tree : FloatArray

/-- Refresh the bracket of species `s` if stale, then the bounds of its reactions. -/
def refresh (C : Compiled) (pop : Array Nat) (c : Cache) (s : Nat) : Cache :=
  if stale C.ms[s]! pop[s]! c.lo[s]! c.hi[s]! then
    let lo := c.lo.set! s (bracket C.ms[s]! pop[s]!).1
    let hi := c.hi.set! s (bracket C.ms[s]! pop[s]!).2
    let b := C.deps[s]!.foldl (updateBounds C lo hi) (c.lower, c.tree)
    ⟨lo, hi, b.1, b.2⟩
  else c

def fire (C : Compiled) (pop : Array Nat) (c : Cache) (j : Nat) : Array Nat × Cache :=
  let pop := (changesOf C.net j).foldl applyChange pop
  (pop, (changesOf C.net j).foldl (fun c ch => refresh C pop c ch.1) c)

def proposals (C : Compiled) (pop : Array Nat) (lower tree : FloatArray) (now total : Float) :
    Nat → Float → Xoshiro → Except Error (Option (Event Float) × Xoshiro)
  | 0, _, _ => .error .proposalLimit
  | fuel + 1, elapsed, rng => do
    let (u, rng) ← drawUniform hostArithmetic hostSource rng
    let j := descend tree C.depth 1 (hostArithmetic.mul u total) - 2 ^ C.depth
    let (e, rng) ← drawExponential hostArithmetic hostSource rng
    let elapsed := hostArithmetic.add elapsed e
    if !hostArithmetic.finite elapsed then throw .invalidTime
    let (v, rng) ← drawUniform hostArithmetic hostSource rng
    if j < C.net.reactions.size &&
        rssaAccept hostArithmetic (lower.get! j) (propensity hostArithmetic C.net.reactions[j]! pop)
          (hostArithmetic.mul v (tree.get! (2 ^ C.depth + j))) then
      let time := hostArithmetic.add now (hostArithmetic.div elapsed total)
      if !(hostArithmetic.finite time && hostArithmetic.lt now time) then throw .invalidTime
      return (some ⟨time, j⟩, rng)
    else proposals C pop lower tree now total fuel elapsed rng

def event (C : Compiled) (pop : Array Nat) (c : Cache) (now : Float) (rng : Xoshiro)
    (maxProposals : Nat) : Except Error (Option (Event Float) × Xoshiro) :=
  let total := c.tree.get! 1
  if !hostArithmetic.finite total then .error (.invalidRate C.net.reactions.size)
  else if !hostArithmetic.lt hostArithmetic.zero total then .ok (none, rng)
  else proposals C pop c.lower c.tree now total maxProposals hostArithmetic.zero rng

def loop (C : Compiled) (horizon : Float) (saveEvents : Bool) (maxProposals : Nat) :
    Nat → Array Nat → Cache → Float → Xoshiro → Nat → Array (Float × State) →
      Except Error (Solution Float State Xoshiro)
  | 0, pop, c, now, rng, count, trace => do
    let (event, rng) ← event C pop c now rng maxProposals
    match event with
    | none => return ⟨⟨pop, c.lo, c.hi⟩, horizon, count, rng, trace.push (horizon, ⟨pop, c.lo, c.hi⟩)⟩
    | some e =>
      if !hostArithmetic.le now e.time || !hostArithmetic.finite e.time then throw .invalidTime
      if !hostArithmetic.le e.time horizon then
        return ⟨⟨pop, c.lo, c.hi⟩, horizon, count, rng, trace.push (horizon, ⟨pop, c.lo, c.hi⟩)⟩
      throw .eventLimit
  | fuel + 1, pop, c, now, rng, count, trace => do
    let (event, rng) ← event C pop c now rng maxProposals
    match event with
    | none => return ⟨⟨pop, c.lo, c.hi⟩, horizon, count, rng, trace.push (horizon, ⟨pop, c.lo, c.hi⟩)⟩
    | some e =>
      if !hostArithmetic.le now e.time || !hostArithmetic.finite e.time then throw .invalidTime
      if !hostArithmetic.le e.time horizon then
        return ⟨⟨pop, c.lo, c.hi⟩, horizon, count, rng, trace.push (horizon, ⟨pop, c.lo, c.hi⟩)⟩
      let (pop, c) := fire C pop c e.reaction
      let trace := if saveEvents then trace.push (e.time, ⟨pop, c.lo, c.hi⟩) else trace
      loop C horizon saveEvents maxProposals fuel pop c e.time rng (count + 1) trace

def initialCache (C : Compiled) (st : State) : Cache :=
  ⟨st.lo, st.hi, ⟨lowerBounds hostArithmetic C.net st⟩,
    buildTree (upperBounds hostArithmetic C.net st) C.depth⟩

def simulate (net : Network Float) (initial : State) (start horizon : Float) (rng : Xoshiro)
    (maxEvents : Nat := 1000000) (saveEvents : Bool := false) (maxProposals : Nat := 100000) :
    Except Error (Solution Float State Xoshiro) := do
  if !(hostArithmetic.finite start && hostArithmetic.finite horizon &&
      hostArithmetic.le start horizon) then throw .invalidTime
  if !hostArithmetic.lt start horizon then return ⟨initial, horizon, 0, rng, #[(start, initial)]⟩
  let C := compile net
  loop C horizon saveEvents maxProposals maxEvents initial.pop (initialCache C initial) start rng 0
    #[(start, initial)]

end JumpProcessesLean.TreeRSSA.Gen1
