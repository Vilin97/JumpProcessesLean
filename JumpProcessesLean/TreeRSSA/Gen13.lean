import JumpProcessesLean.TreeRSSA.Gen12

/-!
# Tree-RSSA, generation 13: refresh records as integer codes

After generation 12 the refreshes of the largest network spent most of their time reaching
the dependents' compiled factors: every dependent was a heap object behind a pointer, read
with a tag dispatch and evaluated four times (at the new and old ends of both brackets)
through a closure that substitutes the refreshed species' old value.

A dependent of species `s` multiplies a power of `s`'s count, `ff(x_s, ν)`, by at most one
partner factor `ff(x_t, μ)` with `t ≠ s`. Generation 13 compiles each dependent into one
natural number: `ν - 1` for a factor of `s` alone, `4 (t + 1) + 2 (μ - 1) + (ν - 1)` with a
partner, and `2` for any other factor, which is evaluated as before. The refresh reads the
codes from one flat array per species: the four integer factors are the two powers of `s` at
the new and old bracket ends times the partner factor read once per bracket. They are the
same natural numbers as generation 12's (`Proofs/TreeRSSAGen13.lean`).
-/

namespace JumpProcessesLean.TreeRSSA.Gen13

open Gen1 (Cache)
open Gen7 (floatInf floatNegInf)

/-- Generation 11's word descent, compiled in this module so that the driver inlines it. -/
def descendW (tree : FloatArray) (P : USize) (hP : 2 * P.toNat ≤ tree.size)
    (hP2 : 2 * P.toNat < USize.size) (k : USize) (hk0 : 0 < k.toNat) (x : Float) : USize :=
  if hk : k < P then
    have hk' : k.toNat < P.toNat := hk
    have h2 : (2 * k).toNat < tree.size := by rw [Gen11.usize_two_mul k (by omega)]; omega
    let left := tree.uget (2 * k) h2
    if x < left then
      descendW tree P hP hP2 (2 * k) (by rw [Gen11.usize_two_mul k (by omega)]; omega) x
    else
      descendW tree P hP hP2 (2 * k + 1) (by rw [Gen11.usize_two_mul_add_one k (by omega)]; omega)
        (x - left)
  else k
termination_by P.toNat - k.toNat
decreasing_by
  · have := (show k.toNat < P.toNat from hk)
    rw [Gen11.usize_two_mul k (by omega)]; omega
  · have := (show k.toNat < P.toNat from hk)
    rw [Gen11.usize_two_mul_add_one k (by omega)]; omega

/-- `Gen12.descendAt` through this module's copy of the descent. -/
@[inline] def descendAt (tree : FloatArray) (depth : Nat) (P : USize)
    (hP2 : 2 * P.toNat < USize.size) (x : Float) : Nat :=
  if h : 2 * P ≤ tree.usize then
    (descendW tree P (Gen11.two_mul_le_size tree P hP2 h) hP2 1 Gen11.usize_one_pos x).toNat
  else Gen1.descend tree depth 1 x

/-- The code of a dependent of species `s` with compiled factor `f`. -/
def code (s : Nat) (f : Gen3.Factor) : Nat :=
  match f with
  | .one t => if t = s then 0 else 2
  | .two t => if t = s then 1 else 2
  | .pair t ν u μ =>
    if t = s ∧ u ≠ s ∧ (ν = 1 ∨ ν = 2) ∧ (μ = 1 ∨ μ = 2) then
      4 * (u + 1) + 2 * (μ - 1) + (ν - 1)
    else if u = s ∧ t ≠ s ∧ (ν = 1 ∨ ν = 2) ∧ (μ = 1 ∨ μ = 2) then
      4 * (t + 1) + 2 * (ν - 1) + (μ - 1)
    else 2
  | .general _ => 2

/-- The codes of every species' dependents, in the order of `Gen5.Compiled.depFactors`. -/
def codesOf (C : Gen5.Compiled) : Array (Array Nat) :=
  C.depFactors.mapIdx fun s fs => fs.map (code s)

/-- `ff x (b + 1)` for a stoichiometry bit `b`. -/
@[inline] def ffb (x b : Nat) : Nat := if b = 0 then x else x * (x - 1)

/-- The power of the refreshed species' count `x` in a dependent with code `c`. -/
@[inline] def own (c x : Nat) : Nat := ffb x (c % 2)

/-- The partner factor of a dependent with code `c`, read from `arr`. -/
@[inline] def partner (c : Nat) (arr : Array Nat) : Nat :=
  if c < 4 then 1 else ffb arr[c / 4 - 1]! (c / 2 % 2)

/-- Generation 12's refresh of the dependents with the integer factors computed from the
codes `cs`; `loN`, `hiN` are the refreshed species' new bracket ends. -/
def setBounds (C : Gen3.Compiled) (P : USize) (hP2 : 2 * P.toNat < USize.size)
    (lo hi : Array Nat) (s loS hiS loN hiN : Nat) (ks cs : Array Nat) (fs : Array Gen3.Factor)
    (rs : FloatArray) : Nat → FloatArray → FloatArray → Nat → FloatArray × FloatArray
  | 0, lower, tree, pending =>
    (lower, if pending = 0 then tree else Gen12.fixPathAt P hP2 tree C.depth pending)
  | i + 1, lower, tree, pending =>
    let n := ks.size - (i + 1)
    let k := ks[n]!
    let c := cs[n]!
    if c = 2 then
      let f := fs[n]!
      let lf := f.eval lo
      let lower := if lf = Gen5.evalAt f lo s loS then lower
        else lower.set! k (rs.get! n * natToFloat lf)
      let uf := f.eval hi
      if uf = Gen5.evalAt f hi s hiS then
        setBounds C P hP2 lo hi s loS hiS loN hiN ks cs fs rs i lower tree pending
      else
        let leaf := C.leaves + k
        let tree := if pending = 0 then tree else Gen12.fixUntilAt P hP2 tree C.depth pending leaf
        setBounds C P hP2 lo hi s loS hiS loN hiN ks cs fs rs i lower
          (tree.set! leaf (rs.get! n * natToFloat uf)) leaf
    else
      let pL := partner c lo
      let lf := own c loN * pL
      let lower := if lf = own c loS * pL then lower
        else lower.set! k (rs.get! n * natToFloat lf)
      let pH := partner c hi
      let uf := own c hiN * pH
      if uf = own c hiS * pH then
        setBounds C P hP2 lo hi s loS hiS loN hiN ks cs fs rs i lower tree pending
      else
        let leaf := C.leaves + k
        let tree := if pending = 0 then tree else Gen12.fixUntilAt P hP2 tree C.depth pending leaf
        setBounds C P hP2 lo hi s loS hiS loN hiN ks cs fs rs i lower
          (tree.set! leaf (rs.get! n * natToFloat uf)) leaf

/-- Generation 12's refresh of a stale species with generation 13's bounds. -/
def rebracket (C : Gen5.Compiled) (codes : Array (Array Nat)) (P : USize)
    (hP2 : 2 * P.toNat < USize.size) (pop : Array Nat) (c : Cache) (s : Nat) : Cache :=
  let loS := c.lo[s]!
  let hiS := c.hi[s]!
  let lo := c.lo.set! s (bracket C.base.ms[s]! pop[s]!).1
  let hi := c.hi.set! s (bracket C.base.ms[s]! pop[s]!).2
  let ks := C.base.deps[s]!
  let (lower, tree) := setBounds C.base P hP2 lo hi s loS hiS lo[s]! hi[s]! ks codes[s]!
    C.depFactors[s]! C.depRates[s]! ks.size c.lower c.tree 0
  ⟨lo, hi, lower, tree⟩

@[inline] def refresh (C : Gen5.Compiled) (codes : Array (Array Nat)) (P : USize)
    (hP2 : 2 * P.toNat < USize.size) (ms : Array Nat) (pop : Array Nat) (c : Cache) (s : Nat) :
    Cache :=
  if Gen9.staleI ms[s]! pop[s]! c.lo[s]! c.hi[s]! then rebracket C codes P hP2 pop c s else c

@[inline] def fire (C : Gen6.Compiled) (codes : Array (Array Nat)) (P : USize)
    (hP2 : 2 * P.toNat < USize.size) (ms : Array Nat) (pop : Array Nat) (c : Cache) (j : Nat) :
    Array Nat × Cache :=
  let chs := C.changes[j]!
  let pop := chs.foldl Gen6.Change.apply pop
  (pop, chs.foldl (fun c ch => refresh C.gen5 codes P hP2 ms pop c ch.species) c)

/-- Generation 12's driver with generation 13's firing. -/
def run (C : Gen6.Compiled) (codes : Array (Array Nat)) (ms : Array Nat) (depth leaves numRx : Nat) (P : USize)
    (hP2 : 2 * P.toNat < USize.size) (rates : FloatArray)
    (factors : Array Gen3.Factor) (horizon : Float) (save : Bool) (cap : Nat)
    (evFuel prFuel : Nat) (pop : Array Nat) (c : Cache) (now total elapsed : Float)
    (s0 s1 s2 s3 : UInt64) (count : Nat) (trace : Array (Float × State)) :
    Except Error (Solution Float State Xoshiro) :=
  match prFuel with
  | 0 => .error .proposalLimit
  | pf + 1 =>
    let rng : Xoshiro := ⟨s0, s1, s2, s3⟩
    let (u, rng) := rng.uniform
    if !decide (u < floatInf) then .error .invalidUniform
    else if !decide (floatNegInf < u) then .error .invalidUniform
    else if !decide (floatZero ≤ u) then .error .invalidUniform
    else if !decide (u < floatOne) then .error .invalidUniform
    else
      let (e, rng) := rng.exponential
      if !decide (e < floatInf) then .error .invalidExponential
      else if !decide (floatNegInf < e) then .error .invalidExponential
      else if !decide (floatZero < e) then .error .invalidExponential
      else
        let elapsed := elapsed + e
        if !decide (elapsed < floatInf) then .error .invalidTime
        else if !decide (floatNegInf < elapsed) then .error .invalidTime
        else
          let (v, rng) := rng.uniform
          if !decide (v < floatInf) then .error .invalidUniform
          else if !decide (floatNegInf < v) then .error .invalidUniform
          else if !decide (floatZero ≤ v) then .error .invalidUniform
          else if !decide (v < floatOne) then .error .invalidUniform
          else
            let j := descendAt c.tree depth P hP2 (u * total) - leaves
            let acc :=
              if !decide (j < numRx) then false
              else
                let lower := c.lower.get! j
                let threshold := v * c.tree.get! (leaves + j)
                if decide (floatZero < lower) && decide (threshold ≤ lower) then true
                else
                  let actual := rates.get! j * natToFloat (factors[j]!.eval pop)
                  decide (floatZero < actual) && decide (threshold ≤ actual)
            if acc then
              let time := now + elapsed / total
              if !decide (time < floatInf) then .error .invalidTime
              else if !decide (floatNegInf < time) then .error .invalidTime
              else if !decide (now < time) then .error .invalidTime
              else if !decide (now ≤ time) then .error .invalidTime
              else if !decide (time ≤ horizon) then
                .ok ⟨⟨pop, c.lo, c.hi⟩, horizon, count, ⟨rng.s0, rng.s1, rng.s2, rng.s3⟩,
                  trace.push (horizon, ⟨pop, c.lo, c.hi⟩)⟩
              else
                match evFuel with
                | 0 => .error .eventLimit
                | ef + 1 =>
                  let (pop, c) := fire C codes P hP2 ms pop c j
                  let trace := if save then trace.push (time, ⟨pop, c.lo, c.hi⟩) else trace
                  let total := c.tree.get! 1
                  if !decide (total < floatInf) then .error (.invalidRate numRx)
                  else if !decide (floatNegInf < total) then .error (.invalidRate numRx)
                  else if !decide (floatZero < total) then
                    .ok ⟨⟨pop, c.lo, c.hi⟩, horizon, count + 1, ⟨rng.s0, rng.s1, rng.s2, rng.s3⟩,
                      trace.push (horizon, ⟨pop, c.lo, c.hi⟩)⟩
                  else
                    run C codes ms depth leaves numRx P hP2 rates factors horizon save cap ef cap pop c
                      time total floatZero rng.s0 rng.s1 rng.s2 rng.s3 (count + 1) trace
            else
              run C codes ms depth leaves numRx P hP2 rates factors horizon save cap evFuel pf pop c now
                total elapsed rng.s0 rng.s1 rng.s2 rng.s3 count trace
termination_by (evFuel, prFuel)

@[inline] def start (C : Gen6.Compiled) (codes : Array (Array Nat)) (horizon : Float) (save : Bool) (cap : Nat) (fuel : Nat)
    (pop : Array Nat) (c : Cache) (now : Float) (rng : Xoshiro) (count : Nat)
    (trace : Array (Float × State)) : Except Error (Solution Float State Xoshiro) :=
  let total := c.tree.get! 1
  if !Gen7.finite total then .error (.invalidRate C.gen5.base.numRx)
  else if !decide (floatZero < total) then
    .ok ⟨⟨pop, c.lo, c.hi⟩, horizon, count, rng, trace.push (horizon, ⟨pop, c.lo, c.hi⟩)⟩
  else if h : 2 * C.gen5.base.leaves < USize.size then
    run C codes C.gen5.base.ms C.gen5.base.depth C.gen5.base.leaves C.gen5.base.numRx
      C.gen5.base.leaves.toUSize (Gen11.leaves_toUSize h) C.gen5.base.rates
      C.gen5.base.factors horizon save cap fuel cap pop c now total floatZero rng.s0 rng.s1 rng.s2
      rng.s3 count trace
  else
    Gen10.run C C.gen5.base.ms C.gen5.base.depth C.gen5.base.leaves C.gen5.base.numRx
      C.gen5.base.rates C.gen5.base.factors horizon save cap fuel cap pop c now total floatZero
      rng.s0 rng.s1 rng.s2 rng.s3 count trace

def simulate (net : Network Float) (initial : State) (start horizon : Float) (rng : Xoshiro)
    (maxEvents : Nat := 1000000) (saveEvents : Bool := false) (maxProposals : Nat := 100000) :
    Except Error (Solution Float State Xoshiro) :=
  if !(Gen7.finite start && Gen7.finite horizon && decide (start ≤ horizon)) then
    .error .invalidTime
  else if !decide (start < horizon) then .ok ⟨initial, horizon, 0, rng, #[(start, initial)]⟩
  else
    let C := Gen6.compile net
    Gen13.start C (codesOf C.gen5) horizon saveEvents maxProposals maxEvents initial.pop
      (Gen3.initialCache C.gen5.base initial) start rng 0 #[(start, initial)]

end JumpProcessesLean.TreeRSSA.Gen13
