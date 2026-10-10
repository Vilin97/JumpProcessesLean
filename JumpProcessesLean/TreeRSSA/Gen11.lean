import JumpProcessesLean.TreeRSSA.Gen10

/-!
# Tree-RSSA, generation 11: the descent on machine words

The descent dominated the large networks: every level decremented a natural-number fuel,
doubled a natural-number index with an overflow check, and read the tree through a
bounds-checked, boxed index. Generation 11 descends with machine-word indices and no fuel,
stopping when the index reaches the leaf level, and reads the tree without bounds checks:
one comparison per proposal establishes that the tree has `2P` slots for `P` leaves, and the
loop carries that proof. The node values, comparisons and subtractions are generation 10's
(`Proofs/TreeRSSAGen11.lean`).
-/

namespace JumpProcessesLean.TreeRSSA.Gen11

open Gen1 (Cache)
open Gen7 (floatInf floatNegInf)

theorem usize_two_mul (k : USize) (h : 2 * k.toNat < USize.size) :
    (2 * k).toNat = 2 * k.toNat := by
  rw [USize.toNat_mul]
  have : (2 : USize).toNat = 2 := by
    rcases USize.size_eq with h | h <;> simp [USize.toNat_ofNat, h]
  rw [this]; exact Nat.mod_eq_of_lt h

theorem usize_two_mul_add_one (k : USize) (h : 2 * k.toNat + 1 < USize.size) :
    (2 * k + 1).toNat = 2 * k.toNat + 1 := by
  rw [USize.toNat_add, usize_two_mul k (by omega)]
  have : (1 : USize).toNat = 1 := by
    rcases USize.size_eq with h | h <;> simp [USize.toNat_ofNat, h]
  rw [this]; exact Nat.mod_eq_of_lt h

/-- The descent from node `k ≥ 1` on machine words, for a tree of `2P` slots with leaves from
`P`: it stops at the first index that is not below `P`. -/
def descendW (tree : FloatArray) (P : USize) (hP : 2 * P.toNat ≤ tree.size)
    (hP2 : 2 * P.toNat < USize.size) (k : USize) (hk0 : 0 < k.toNat) (x : Float) : USize :=
  if hk : k < P then
    have hk' : k.toNat < P.toNat := hk
    have h2 : (2 * k).toNat < tree.size := by rw [usize_two_mul k (by omega)]; omega
    let left := tree.uget (2 * k) h2
    if x < left then
      descendW tree P hP hP2 (2 * k) (by rw [usize_two_mul k (by omega)]; omega) x
    else
      descendW tree P hP hP2 (2 * k + 1) (by rw [usize_two_mul_add_one k (by omega)]; omega)
        (x - left)
  else k
termination_by P.toNat - k.toNat
decreasing_by
  · have := (show k.toNat < P.toNat from hk)
    rw [usize_two_mul k (by omega)]; omega
  · have := (show k.toNat < P.toNat from hk)
    rw [usize_two_mul_add_one k (by omega)]; omega

theorem two_mul_le_size (tree : FloatArray) (P : USize) (hP2 : 2 * P.toNat < USize.size)
    (h : 2 * P ≤ tree.usize) : 2 * P.toNat ≤ tree.size := by
  have h1 : (2 * P).toNat ≤ tree.usize.toNat := h
  rw [usize_two_mul P (by omega)] at h1
  have h2 : tree.usize.toNat ≤ tree.size := by
    simp only [FloatArray.usize, USize.toNat_ofNat']
    exact Nat.mod_le _ _
  omega

theorem leaves_toUSize {n : Nat} (h : 2 * n < USize.size) : 2 * n.toUSize.toNat < USize.size := by
  rw [Nat.toUSize, USize.toNat_ofNat_of_lt' (by omega)]; exact h

theorem usize_one_pos : 0 < (1 : USize).toNat := by
  rcases USize.size_eq with h | h <;> simp [USize.toNat_ofNat, h]

/-- `Gen1.descend tree depth 1 x` through `descendW` when the tree has `2P` slots. -/
@[inline] def descendAt (tree : FloatArray) (depth : Nat) (P : USize)
    (hP2 : 2 * P.toNat < USize.size) (x : Float) : Nat :=
  if h : 2 * P ≤ tree.usize then
    (descendW tree P (two_mul_le_size tree P hP2 h) hP2 1 usize_one_pos x).toNat
  else Gen1.descend tree depth 1 x

/-- Generation 10's driver with the machine-word descent. -/
def run (C : Gen6.Compiled) (ms : Array Nat) (depth leaves numRx : Nat) (P : USize)
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
                  let (pop, c) := Gen9.fire C ms pop c j
                  let trace := if save then trace.push (time, ⟨pop, c.lo, c.hi⟩) else trace
                  let total := c.tree.get! 1
                  if !decide (total < floatInf) then .error (.invalidRate numRx)
                  else if !decide (floatNegInf < total) then .error (.invalidRate numRx)
                  else if !decide (floatZero < total) then
                    .ok ⟨⟨pop, c.lo, c.hi⟩, horizon, count + 1, ⟨rng.s0, rng.s1, rng.s2, rng.s3⟩,
                      trace.push (horizon, ⟨pop, c.lo, c.hi⟩)⟩
                  else
                    run C ms depth leaves numRx P hP2 rates factors horizon save cap ef cap pop c time total
                      floatZero rng.s0 rng.s1 rng.s2 rng.s3 (count + 1) trace
            else
              run C ms depth leaves numRx P hP2 rates factors horizon save cap evFuel pf pop c now total
                elapsed rng.s0 rng.s1 rng.s2 rng.s3 count trace
termination_by (evFuel, prFuel)

@[inline] def start (C : Gen6.Compiled) (horizon : Float) (save : Bool) (cap : Nat) (fuel : Nat)
    (pop : Array Nat) (c : Cache) (now : Float) (rng : Xoshiro) (count : Nat)
    (trace : Array (Float × State)) : Except Error (Solution Float State Xoshiro) :=
  let total := c.tree.get! 1
  if !Gen7.finite total then .error (.invalidRate C.gen5.base.numRx)
  else if !decide (floatZero < total) then
    .ok ⟨⟨pop, c.lo, c.hi⟩, horizon, count, rng, trace.push (horizon, ⟨pop, c.lo, c.hi⟩)⟩
  else if h : 2 * C.gen5.base.leaves < USize.size then
    run C C.gen5.base.ms C.gen5.base.depth C.gen5.base.leaves C.gen5.base.numRx
      C.gen5.base.leaves.toUSize (leaves_toUSize h) C.gen5.base.rates
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
    Gen11.start C horizon saveEvents maxProposals maxEvents initial.pop
      (Gen3.initialCache C.gen5.base initial) start rng 0 #[(start, initial)]

end JumpProcessesLean.TreeRSSA.Gen11
