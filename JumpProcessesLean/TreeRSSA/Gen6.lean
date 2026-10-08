import JumpProcessesLean.TreeRSSA.Gen5

/-!
# Tree-RSSA, generation 6: the per-event path

With refreshes cheaper, the per-event path dominates on all networks again. Two costs there
change no value:

* the acceptance test evaluated the exact propensity of the candidate before testing the
  lower bound, although the lower bound alone accepts most candidates: the inlined test
  bound the propensity first. Generation 6 writes the test out with the propensity inside
  the second disjunct, so it is evaluated only when the lower bound rejects;
* every population change went through integer arithmetic and an out-of-line conversion back
  to a natural number. Generation 6 compiles each change into a species, an increase and a
  decrease, applied with natural-number arithmetic.

`Gen6.simulate` is proved equal to generation 5 (`Proofs/TreeRSSAGen6.lean`).
-/

namespace JumpProcessesLean.TreeRSSA.Gen6

open Gen1 (Cache)

/-- A compiled population change: `pop[species] + up - down`. -/
structure Change where
  species : Nat
  up : Nat
  down : Nat

def Change.ofPair (c : Nat × Int) : Change := ⟨c.1, c.2.toNat, (-c.2).toNat⟩

@[inline] def Change.apply (pop : Array Nat) (c : Change) : Array Nat :=
  pop.set! c.species (pop[c.species]! + c.up - c.down)

structure Compiled where
  gen5 : Gen5.Compiled
  /-- For each reaction, its compiled changes. -/
  changes : Array (Array Change)

def compile (net : Network Float) : Compiled :=
  ⟨Gen5.compile net, net.reactions.map (·.changes.map Change.ofPair)⟩

@[inline] def fire (C : Compiled) (pop : Array Nat) (c : Cache) (j : Nat) : Array Nat × Cache :=
  let chs := C.changes[j]!
  let pop := chs.foldl Change.apply pop
  (pop, chs.foldl (fun c ch => Gen5.refresh C.gen5 pop c ch.species) c)

/-- Generation 5's driver with the lazy acceptance test and compiled changes. -/
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
      let j := Gen1.descend c.tree C.gen5.base.depth 1 (u * total) - C.gen5.base.leaves
      let (e, rng) := rng.exponential
      if !(e.isFinite && decide (floatZero < e)) then .error .invalidExponential
      else
        let elapsed := elapsed + e
        if !elapsed.isFinite then .error .invalidTime
        else
          let (v, rng) := rng.uniform
          if !(v.isFinite && decide (floatZero ≤ v) && decide (v < floatOne)) then
            .error .invalidUniform
          else if j < C.gen5.base.numRx &&
              (let lower := c.lower.get! j
               let threshold := v * c.tree.get! (C.gen5.base.leaves + j)
               (decide (floatZero < lower) && decide (threshold ≤ lower)) ||
                 (let actual := Gen3.rate C.gen5.base j pop
                  decide (floatZero < actual) && decide (threshold ≤ actual))) then
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
                if !total.isFinite then .error (.invalidRate C.gen5.base.numRx)
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

@[inline] def start (C : Compiled) (horizon : Float) (save : Bool) (cap : Nat) (fuel : Nat)
    (pop : Array Nat) (c : Cache) (now : Float) (rng : Xoshiro) (count : Nat)
    (trace : Array (Float × State)) : Except Error (Solution Float State Xoshiro) :=
  let total := c.tree.get! 1
  if !total.isFinite then .error (.invalidRate C.gen5.base.numRx)
  else if !decide (floatZero < total) then
    .ok ⟨⟨pop, c.lo, c.hi⟩, horizon, count, rng, trace.push (horizon, ⟨pop, c.lo, c.hi⟩)⟩
  else run C horizon save cap fuel cap pop c now total floatZero rng.s0 rng.s1 rng.s2 rng.s3 count trace

def simulate (net : Network Float) (initial : State) (start horizon : Float) (rng : Xoshiro)
    (maxEvents : Nat := 1000000) (saveEvents : Bool := false) (maxProposals : Nat := 100000) :
    Except Error (Solution Float State Xoshiro) :=
  if !(start.isFinite && horizon.isFinite && decide (start ≤ horizon)) then .error .invalidTime
  else if !decide (start < horizon) then .ok ⟨initial, horizon, 0, rng, #[(start, initial)]⟩
  else
    let C := compile net
    Gen6.start C horizon saveEvents maxProposals maxEvents initial.pop
      (Gen3.initialCache C.gen5.base initial) start rng 0 #[(start, initial)]

end JumpProcessesLean.TreeRSSA.Gen6
