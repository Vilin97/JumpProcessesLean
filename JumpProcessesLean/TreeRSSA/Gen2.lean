import JumpProcessesLean.TreeRSSA.Gen1

/-!
# Tree-RSSA, generation 2: native arithmetic and inlined draws

Profiling generation 1 showed three overheads that change no arithmetic result:

* the generic arithmetic record is called through closures with boxed floats;
* every random draw goes through the `RandomSource` closures and allocates `Except`,
  pairs and boxed floats;
* `2 ^ depth` is recomputed with arbitrary-precision arithmetic at every proposal.

Generation 2 uses native `Float` operations, inlines the xoshiro256++ draws together with
their validity checks, and precomputes the leaf offset. It also leaves a tree path alone
when a refreshed upper bound has the same bits as before. `Gen2.simulate` is proved equal
to `TreeRSSA.simulate hostArithmetic hostSource` (`Proofs/TreeRSSAGen2.lean`).
-/

namespace JumpProcessesLean.TreeRSSA.Gen2

open Gen1 (Cache fixPath descend buildTree)

/-- Immutable data compiled once from the network. -/
structure Compiled where
  net : Network Float
  ms : Array Nat
  deps : Array (Array Nat)
  depth : Nat
  leaves : Nat
  numRx : Nat

def compile (net : Network Float) : Compiled :=
  ⟨net, net.maxStoich, net.speciesDependents, treeDepth net.reactions.size,
    2 ^ treeDepth net.reactions.size, net.reactions.size⟩

/-- `propensity hostArithmetic` with native operations. -/
@[inline] def rate (rx : Reaction Float) (pop : Array Nat) : Float :=
  rx.rate * natToFloat (combinations rx.reactants pop)

/-- `rssaAccept hostArithmetic` with native operations. -/
@[inline] def accept (lower actual threshold : Float) : Bool :=
  (decide (floatZero < lower) && decide (threshold ≤ lower)) ||
    (decide (floatZero < actual) && decide (threshold ≤ actual))

/-- Re-evaluate both bounds of reaction `k`; re-add its path only if the upper bound's
bits changed. -/
def updateBounds (C : Compiled) (lo hi : Array Nat) (bounds : FloatArray × FloatArray)
    (k : Nat) : FloatArray × FloatArray :=
  let rx := C.net.reactions[k]!
  let leaf := C.leaves + k
  let upper := rate rx hi
  let tree := bounds.2
  (bounds.1.set! k (rate rx lo),
    if upper.toBits == (tree.get! leaf).toBits then tree
    else fixPath (tree.set! leaf upper) C.depth leaf)

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

/-- The thinning loop with the three draws and their checks inlined. -/
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
              accept (lower.get! j) (rate C.net.reactions[j]! pop) (v * tree.get! (C.leaves + j)) then
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
  ⟨st.lo, st.hi, ⟨C.net.reactions.map (rate · st.lo)⟩,
    buildTree (C.net.reactions.map (rate · st.hi)) C.depth⟩

def simulate (net : Network Float) (initial : State) (start horizon : Float) (rng : Xoshiro)
    (maxEvents : Nat := 1000000) (saveEvents : Bool := false) (maxProposals : Nat := 100000) :
    Except Error (Solution Float State Xoshiro) :=
  if !(start.isFinite && horizon.isFinite && decide (start ≤ horizon)) then .error .invalidTime
  else if !decide (start < horizon) then .ok ⟨initial, horizon, 0, rng, #[(start, initial)]⟩
  else
    let C := compile net
    loop C horizon saveEvents maxProposals maxEvents initial.pop (initialCache C initial) start rng 0
      #[(start, initial)]

end JumpProcessesLean.TreeRSSA.Gen2
