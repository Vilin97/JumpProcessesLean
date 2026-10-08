import JumpProcessesLean.TreeRSSA.Gen7

/-!
# Tree-RSSA, generation 8: no reference counting on the proposal path

The generated code of generation 7 spent about a dozen reference-count operations on every
proposal: it projected the tree depth, the leaf offset, the reaction count and the rate and
factor arrays out of the compiled network, incremented them to pass them to join points, and
tried to recycle the network's record for the result state on the way.

Generation 8 passes those fields to the driver as parameters, so a proposal projects nothing
from the network and a rejected proposal loops with no reference-count operation on heap
objects. The computation is generation 7's. `Gen8.simulate` is proved equal to generation 7
(`Proofs/TreeRSSAGen8.lean`).
-/

namespace JumpProcessesLean.TreeRSSA.Gen8

open Gen1 (Cache)
open Gen7 (floatInf floatNegInf)

/-- Generation 7's driver with the network's hot fields as parameters. -/
def run (C : Gen6.Compiled) (depth leaves numRx : Nat) (rates : FloatArray)
    (factors : Array Gen3.Factor) (horizon : Float) (save : Bool) (cap : Nat)
    (evFuel prFuel : Nat) (pop : Array Nat) (c : Cache) (now total elapsed : Float)
    (s0 s1 s2 s3 : UInt64)
    (count : Nat) (trace : Array (Float × State)) : Except Error (Solution Float State Xoshiro) :=
  match prFuel with
  | 0 => .error .proposalLimit
  | pf + 1 =>
    let rng : Xoshiro := ⟨s0, s1, s2, s3⟩
    let (u, rng) := rng.uniform
    if !(Gen7.finite u && decide (floatZero ≤ u) && decide (u < floatOne)) then
      .error .invalidUniform
    else
      let j := Gen1.descend c.tree depth 1 (u * total) - leaves
      let (e, rng) := rng.exponential
      if !(Gen7.finite e && decide (floatZero < e)) then .error .invalidExponential
      else
        let elapsed := elapsed + e
        if !Gen7.finite elapsed then .error .invalidTime
        else
          let (v, rng) := rng.uniform
          if !(Gen7.finite v && decide (floatZero ≤ v) && decide (v < floatOne)) then
            .error .invalidUniform
          else if j < numRx &&
              (let lower := c.lower.get! j
               let threshold := v * c.tree.get! (leaves + j)
               (decide (floatZero < lower) && decide (threshold ≤ lower)) ||
                 (let actual := rates.get! j * natToFloat (factors[j]!.eval pop)
                  decide (floatZero < actual) && decide (threshold ≤ actual))) then
            let time := now + elapsed / total
            if !(Gen7.finite time && decide (now < time)) then .error .invalidTime
            else if !decide (now ≤ time) then .error .invalidTime
            else if !decide (time ≤ horizon) then
              .ok ⟨⟨pop, c.lo, c.hi⟩, horizon, count, ⟨rng.s0, rng.s1, rng.s2, rng.s3⟩,
                trace.push (horizon, ⟨pop, c.lo, c.hi⟩)⟩
            else
              match evFuel with
              | 0 => .error .eventLimit
              | ef + 1 =>
                let (pop, c) := Gen7.fire C pop c j
                let trace := if save then trace.push (time, ⟨pop, c.lo, c.hi⟩) else trace
                let total := c.tree.get! 1
                if !Gen7.finite total then .error (.invalidRate numRx)
                else if !decide (floatZero < total) then
                  .ok ⟨⟨pop, c.lo, c.hi⟩, horizon, count + 1, ⟨rng.s0, rng.s1, rng.s2, rng.s3⟩,
                    trace.push (horizon, ⟨pop, c.lo, c.hi⟩)⟩
                else
                  run C depth leaves numRx rates factors horizon save cap ef cap pop c time total
                    floatZero rng.s0 rng.s1 rng.s2 rng.s3 (count + 1) trace
          else
            run C depth leaves numRx rates factors horizon save cap evFuel pf pop c now total
              elapsed rng.s0 rng.s1 rng.s2 rng.s3 count trace
termination_by (evFuel, prFuel)

@[inline] def start (C : Gen6.Compiled) (horizon : Float) (save : Bool) (cap : Nat) (fuel : Nat)
    (pop : Array Nat) (c : Cache) (now : Float) (rng : Xoshiro) (count : Nat)
    (trace : Array (Float × State)) : Except Error (Solution Float State Xoshiro) :=
  let total := c.tree.get! 1
  if !Gen7.finite total then .error (.invalidRate C.gen5.base.numRx)
  else if !decide (floatZero < total) then
    .ok ⟨⟨pop, c.lo, c.hi⟩, horizon, count, rng, trace.push (horizon, ⟨pop, c.lo, c.hi⟩)⟩
  else
    run C C.gen5.base.depth C.gen5.base.leaves C.gen5.base.numRx C.gen5.base.rates
      C.gen5.base.factors horizon save cap fuel cap pop c now total floatZero rng.s0 rng.s1 rng.s2
      rng.s3 count trace

def simulate (net : Network Float) (initial : State) (start horizon : Float) (rng : Xoshiro)
    (maxEvents : Nat := 1000000) (saveEvents : Bool := false) (maxProposals : Nat := 100000) :
    Except Error (Solution Float State Xoshiro) :=
  if !(Gen7.finite start && Gen7.finite horizon && decide (start ≤ horizon)) then
    .error .invalidTime
  else if !decide (start < horizon) then .ok ⟨initial, horizon, 0, rng, #[(start, initial)]⟩
  else
    let C := Gen6.compile net
    Gen8.start C horizon saveEvents maxProposals maxEvents initial.pop
      (Gen3.initialCache C.gen5.base initial) start rng 0 #[(start, initial)]

end JumpProcessesLean.TreeRSSA.Gen8
