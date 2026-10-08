import JumpProcessesLean.TreeRSSA.Gen3

/-!
# Tree-RSSA, generation 4: one allocation-free loop

After generation 3 the per-event costs dominate on all networks: every event allocated an
`Except`, a pair, an `Option`, an `Event` and a generator state, and every proposal allocated a
generator state.

Generation 4 runs the driver as a single tail-recursive function with one call per proposal.
The generator state travels as four machine words (results rebuild it from its words, so it
is never allocated on the way) and an accepted proposal is handled in place: fire, then
start the next event. Refreshes, firings and the descent are generation 3's.
`Gen4.simulate` is proved equal to `TreeRSSA.simulate hostArithmetic hostSource`
(`Proofs/TreeRSSAGen4.lean`).
-/

namespace JumpProcessesLean.TreeRSSA.Gen4

open Gen1 (Cache)
open Gen3 (Compiled)

/-- `Gen3.fire`, inlined so that its pair is never built. -/
@[inline] def fire (C : Compiled) (pop : Array Nat) (c : Cache) (j : Nat) : Array Nat × Cache :=
  let pop := (changesOf C.net j).foldl applyChange pop
  (pop, (changesOf C.net j).foldl (fun c ch => Gen3.refresh C pop c ch.1) c)

/-- The driver from one proposal on. `prFuel` proposals remain for the current event and
`evFuel` events remain after it; `total` is the current upper total and `elapsed` the sum of
the exponential draws of the current event. -/
def run (C : Compiled) (horizon : Float) (save : Bool) (cap : Nat) (evFuel prFuel : Nat)
    (pop : Array Nat) (c : Cache) (now total elapsed : Float) (s0 s1 s2 s3 : UInt64)
    (count : Nat) (trace : Array (Float × State)) : Except Error (Solution Float State Xoshiro) :=
  match prFuel with
  | 0 => .error .proposalLimit
  | pf + 1 =>
    let rng : Xoshiro := ⟨s0, s1, s2, s3⟩
    let (u, rng) := rng.uniform
    if !(u.isFinite && decide (floatZero ≤ u) && decide (u < floatOne)) then .error .invalidUniform
    else
      let j := Gen1.descend c.tree C.depth 1 (u * total) - C.leaves
      let (e, rng) := rng.exponential
      if !(e.isFinite && decide (floatZero < e)) then .error .invalidExponential
      else
        let elapsed := elapsed + e
        if !elapsed.isFinite then .error .invalidTime
        else
          let (v, rng) := rng.uniform
          if !(v.isFinite && decide (floatZero ≤ v) && decide (v < floatOne)) then
            .error .invalidUniform
          else if j < C.numRx &&
              Gen2.accept (c.lower.get! j) (Gen3.rate C j pop) (v * c.tree.get! (C.leaves + j)) then
            let time := now + elapsed / total
            if !(time.isFinite && decide (now < time)) then .error .invalidTime
            else if !decide (now ≤ time) then .error .invalidTime
            else if !decide (time ≤ horizon) then
              .ok ⟨⟨pop, c.lo, c.hi⟩, horizon, count, ⟨rng.s0, rng.s1, rng.s2, rng.s3⟩,
                trace.push (horizon, ⟨pop, c.lo, c.hi⟩)⟩
            else
              match evFuel with
              | 0 => .error .eventLimit
              | ef + 1 =>
                let (pop, c) := fire C pop c j
                let trace := if save then trace.push (time, ⟨pop, c.lo, c.hi⟩) else trace
                let total := c.tree.get! 1
                if !total.isFinite then .error (.invalidRate C.numRx)
                else if !decide (floatZero < total) then
                  .ok ⟨⟨pop, c.lo, c.hi⟩, horizon, count + 1, ⟨rng.s0, rng.s1, rng.s2, rng.s3⟩,
                    trace.push (horizon, ⟨pop, c.lo, c.hi⟩)⟩
                else
                  run C horizon save cap ef cap pop c time total floatZero rng.s0 rng.s1 rng.s2
                    rng.s3 (count + 1) trace
          else
            run C horizon save cap evFuel pf pop c now total elapsed rng.s0 rng.s1 rng.s2 rng.s3
              count trace
termination_by (evFuel, prFuel)

/-- Start an event: generation 3's `event` checks, then the proposals. -/
@[inline] def start (C : Compiled) (horizon : Float) (save : Bool) (cap : Nat) (fuel : Nat)
    (pop : Array Nat) (c : Cache) (now : Float) (rng : Xoshiro) (count : Nat)
    (trace : Array (Float × State)) : Except Error (Solution Float State Xoshiro) :=
  let total := c.tree.get! 1
  if !total.isFinite then .error (.invalidRate C.numRx)
  else if !decide (floatZero < total) then
    .ok ⟨⟨pop, c.lo, c.hi⟩, horizon, count, rng, trace.push (horizon, ⟨pop, c.lo, c.hi⟩)⟩
  else run C horizon save cap fuel cap pop c now total floatZero rng.s0 rng.s1 rng.s2 rng.s3 count trace

def simulate (net : Network Float) (initial : State) (start horizon : Float) (rng : Xoshiro)
    (maxEvents : Nat := 1000000) (saveEvents : Bool := false) (maxProposals : Nat := 100000) :
    Except Error (Solution Float State Xoshiro) :=
  if !(start.isFinite && horizon.isFinite && decide (start ≤ horizon)) then .error .invalidTime
  else if !decide (start < horizon) then .ok ⟨initial, horizon, 0, rng, #[(start, initial)]⟩
  else
    let C := Gen3.compile net
    Gen4.start C horizon saveEvents maxProposals maxEvents initial.pop (Gen3.initialCache C initial)
      start rng 0 #[(start, initial)]

end JumpProcessesLean.TreeRSSA.Gen4
