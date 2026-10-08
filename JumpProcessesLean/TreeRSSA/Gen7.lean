import JumpProcessesLean.TreeRSSA.Gen6

/-!
# Tree-RSSA, generation 7: inline finiteness tests

Every proposal tests five floats for finiteness, and `Float.isFinite` is an out-of-line call
into the runtime. Lean's logical model of `Float` decides finiteness and comparisons by
the same case analysis on the unpacked value, so `x.isFinite` is exactly
`x < ∞ && -∞ < x`: two comparisons the compiler emits inline
(`Proofs/TreeRSSAGen7.lean`). Generation 7 uses them, and also inlines the staleness test of
a refresh so that the rebracketing is called only when a bracket is left.
-/

namespace JumpProcessesLean.TreeRSSA.Gen7

open Gen1 (Cache)

/-- `+∞`. -/
def floatInf : Float := Float.inf
/-- `-∞`. -/
def floatNegInf : Float := -Float.inf

/-- `x.isFinite` as two inline comparisons. -/
@[inline] def finite (x : Float) : Bool := decide (x < floatInf) && decide (floatNegInf < x)

/-- Generation 5's refresh of a stale species. -/
def rebracket (C : Gen5.Compiled) (pop : Array Nat) (c : Cache) (s : Nat) : Cache :=
  let loS := c.lo[s]!
  let hiS := c.hi[s]!
  let lo := c.lo.set! s (bracket C.base.ms[s]! pop[s]!).1
  let hi := c.hi.set! s (bracket C.base.ms[s]! pop[s]!).2
  let ks := C.base.deps[s]!
  let (lower, tree) := Gen5.setBounds C.base lo hi s loS hiS ks C.depFactors[s]! C.depRates[s]!
    ks.size c.lower c.tree 0
  ⟨lo, hi, lower, tree⟩

/-- Generation 5's refresh with the staleness test inlined. -/
@[inline] def refresh (C : Gen5.Compiled) (pop : Array Nat) (c : Cache) (s : Nat) : Cache :=
  if stale C.base.ms[s]! pop[s]! c.lo[s]! c.hi[s]! then rebracket C pop c s else c

@[inline] def fire (C : Gen6.Compiled) (pop : Array Nat) (c : Cache) (j : Nat) :
    Array Nat × Cache :=
  let chs := C.changes[j]!
  let pop := chs.foldl Gen6.Change.apply pop
  (pop, chs.foldl (fun c ch => refresh C.gen5 pop c ch.species) c)

/-- Generation 6's driver with inline finiteness tests. -/
def run (C : Gen6.Compiled) (horizon : Float) (save : Bool) (cap : Nat) (evFuel prFuel : Nat)
    (pop : Array Nat) (c : Cache) (now total elapsed : Float) (s0 s1 s2 s3 : UInt64)
    (count : Nat) (trace : Array (Float × State)) : Except Error (Solution Float State Xoshiro) :=
  match prFuel with
  | 0 => .error .proposalLimit
  | pf + 1 =>
    let rng : Xoshiro := ⟨s0, s1, s2, s3⟩
    let (u, rng) := rng.uniform
    if !(finite u && decide (floatZero ≤ u) && decide (u < floatOne)) then .error .invalidUniform
    else
      let j := Gen1.descend c.tree C.gen5.base.depth 1 (u * total) - C.gen5.base.leaves
      let (e, rng) := rng.exponential
      if !(finite e && decide (floatZero < e)) then .error .invalidExponential
      else
        let elapsed := elapsed + e
        if !finite elapsed then .error .invalidTime
        else
          let (v, rng) := rng.uniform
          if !(finite v && decide (floatZero ≤ v) && decide (v < floatOne)) then
            .error .invalidUniform
          else if j < C.gen5.base.numRx &&
              (let lower := c.lower.get! j
               let threshold := v * c.tree.get! (C.gen5.base.leaves + j)
               (decide (floatZero < lower) && decide (threshold ≤ lower)) ||
                 (let actual := Gen3.rate C.gen5.base j pop
                  decide (floatZero < actual) && decide (threshold ≤ actual))) then
            let time := now + elapsed / total
            if !(finite time && decide (now < time)) then .error .invalidTime
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
                if !finite total then .error (.invalidRate C.gen5.base.numRx)
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

@[inline] def start (C : Gen6.Compiled) (horizon : Float) (save : Bool) (cap : Nat) (fuel : Nat)
    (pop : Array Nat) (c : Cache) (now : Float) (rng : Xoshiro) (count : Nat)
    (trace : Array (Float × State)) : Except Error (Solution Float State Xoshiro) :=
  let total := c.tree.get! 1
  if !finite total then .error (.invalidRate C.gen5.base.numRx)
  else if !decide (floatZero < total) then
    .ok ⟨⟨pop, c.lo, c.hi⟩, horizon, count, rng, trace.push (horizon, ⟨pop, c.lo, c.hi⟩)⟩
  else run C horizon save cap fuel cap pop c now total floatZero rng.s0 rng.s1 rng.s2 rng.s3 count trace

def simulate (net : Network Float) (initial : State) (start horizon : Float) (rng : Xoshiro)
    (maxEvents : Nat := 1000000) (saveEvents : Bool := false) (maxProposals : Nat := 100000) :
    Except Error (Solution Float State Xoshiro) :=
  if !(finite start && finite horizon && decide (start ≤ horizon)) then .error .invalidTime
  else if !decide (start < horizon) then .ok ⟨initial, horizon, 0, rng, #[(start, initial)]⟩
  else
    let C := Gen6.compile net
    Gen7.start C horizon saveEvents maxProposals maxEvents initial.pop
      (Gen3.initialCache C.gen5.base initial) start rng 0 #[(start, initial)]

end JumpProcessesLean.TreeRSSA.Gen7
