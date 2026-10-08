import JumpProcessesLean.TreeRSSA.Gen4

/-!
# Tree-RSSA, generation 5: refreshes from contiguous records

On the largest network the bracket refreshes dominate after generation 4. A refresh of a
species re-evaluated each dependent reaction through scattered per-reaction data, converted
and multiplied both bounds, and compared bit patterns through two out-of-line calls.

Generation 5 compiles, for every species, contiguous records of its dependents (rate constant
and compiled factor, copied per species). A refresh compares each dependent's integer
factors before and after the bracket change; a bound whose factor is unchanged is the same
expression as before and is skipped. This is the common case when another reactant is
absent. The old factor is read from the updated bracket arrays with the refreshed species
read at its old value, so the arrays are still updated in place. Changed leaves are
re-added as in generation 3.

Generation 5's refresh returns exactly generation 3's cache, so its runs are generation 4's
(`Proofs/TreeRSSAGen5.lean`).
-/

namespace JumpProcessesLean.TreeRSSA.Gen5

open Gen1 (Cache)

/-- Generation 3's compiled network with per-species refresh data. -/
structure Compiled where
  base : Gen3.Compiled
  /-- For each species, the compiled factor of each dependent reaction. -/
  depFactors : Array (Array Gen3.Factor)
  /-- For each species, the rate constant of each dependent reaction. -/
  depRates : Array FloatArray

def compile (net : Network Float) : Compiled :=
  let C := Gen3.compile net
  ⟨C, C.deps.map (·.map fun k => Gen3.Factor.compile net.reactions[k]!.reactants),
    C.deps.map fun ks => ⟨ks.map fun k => net.reactions[k]!.rate⟩⟩

/-- `f.eval (pop.set! s v)` without building that array: species `s` reads as `v`. -/
@[inline] def evalAt (f : Gen3.Factor) (pop : Array Nat) (s v : Nat) : Nat :=
  let get t := if t = s then v else pop[t]!
  match f with
  | .one t => get t
  | .two t => get t * (get t - 1)
  | .pair t ν u μ => Gen3.ff (get t) ν * Gen3.ff (get u) μ
  | .general rs => rs.foldl (fun acc p => acc * fallingFactorial (get p.1) p.2) 1

/-- Refresh the dependents `ks[ks.size - i], …` of species `s`, whose brackets were `loS`,
`hiS` and are now read from `lo`, `hi`; `fs`, `rs` are the dependents' records. A bound
whose integer factor is unchanged is the same expression as before and is left alone; the
changed leaves' paths are re-added as in generation 3. -/
def setBounds (C : Gen3.Compiled) (lo hi : Array Nat) (s loS hiS : Nat) (ks : Array Nat)
    (fs : Array Gen3.Factor) (rs : FloatArray) :
    Nat → FloatArray → FloatArray → Nat → FloatArray × FloatArray
  | 0, lower, tree, pending =>
    (lower, if pending = 0 then tree else Gen1.fixPath tree C.depth pending)
  | i + 1, lower, tree, pending =>
    let n := ks.size - (i + 1)
    let k := ks[n]!
    let f := fs[n]!
    let lf := f.eval lo
    let lower := if lf = evalAt f lo s loS then lower else lower.set! k (rs.get! n * natToFloat lf)
    let uf := f.eval hi
    if uf = evalAt f hi s hiS then setBounds C lo hi s loS hiS ks fs rs i lower tree pending
    else
      let leaf := C.leaves + k
      let tree := if pending = 0 then tree else Gen3.fixUntil tree C.depth pending leaf
      setBounds C lo hi s loS hiS ks fs rs i lower (tree.set! leaf (rs.get! n * natToFloat uf)) leaf

def refresh (C : Compiled) (pop : Array Nat) (c : Cache) (s : Nat) : Cache :=
  if stale C.base.ms[s]! pop[s]! c.lo[s]! c.hi[s]! then
    let loS := c.lo[s]!
    let hiS := c.hi[s]!
    let lo := c.lo.set! s (bracket C.base.ms[s]! pop[s]!).1
    let hi := c.hi.set! s (bracket C.base.ms[s]! pop[s]!).2
    let ks := C.base.deps[s]!
    let (lower, tree) := setBounds C.base lo hi s loS hiS ks C.depFactors[s]! C.depRates[s]!
      ks.size c.lower c.tree 0
    ⟨lo, hi, lower, tree⟩
  else c

@[inline] def fire (C : Compiled) (pop : Array Nat) (c : Cache) (j : Nat) : Array Nat × Cache :=
  let pop := (changesOf C.base.net j).foldl applyChange pop
  (pop, (changesOf C.base.net j).foldl (fun c ch => refresh C pop c ch.1) c)

/-- Generation 4's driver with generation 5's refreshes. -/
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
      let j := Gen1.descend c.tree C.base.depth 1 (u * total) - C.base.leaves
      let (e, rng) := rng.exponential
      if !(e.isFinite && decide (floatZero < e)) then .error .invalidExponential
      else
        let elapsed := elapsed + e
        if !elapsed.isFinite then .error .invalidTime
        else
          let (v, rng) := rng.uniform
          if !(v.isFinite && decide (floatZero ≤ v) && decide (v < floatOne)) then
            .error .invalidUniform
          else if j < C.base.numRx &&
              Gen2.accept (c.lower.get! j) (Gen3.rate C.base j pop)
                (v * c.tree.get! (C.base.leaves + j)) then
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
                if !total.isFinite then .error (.invalidRate C.base.numRx)
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
  if !total.isFinite then .error (.invalidRate C.base.numRx)
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
    Gen5.start C horizon saveEvents maxProposals maxEvents initial.pop
      (Gen3.initialCache C.base initial) start rng 0 #[(start, initial)]

end JumpProcessesLean.TreeRSSA.Gen5
