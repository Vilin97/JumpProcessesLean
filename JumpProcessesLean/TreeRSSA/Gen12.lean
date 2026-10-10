import JumpProcessesLean.TreeRSSA.Gen11

/-!
# Tree-RSSA, generation 12: tree paths on machine words

On the largest network a third of the time after generation 11 went to re-adding the root
paths of changed leaves. Every level halved, compared and doubled natural-number indices with
overflow checks, read both children through bounds-checked boxed indices, and wrote the sum,
which the next level read back: each level waited for the store of the one below.

Generation 12 walks the same paths on machine words. The value of the current node is
carried in a register: the parent is that value plus the sibling, the only read per level.
The two operands are added in the order the node's parity gives, which is the same float in
Lean's model, where addition is commutative (`Proofs/TreeRSSAGen12.lean`). One comparison per
walk establishes that both nodes are below `2P` and that the tree has `2P` slots; the loop
carries the bound. The nodes visited and the sums written are generation 11's.
-/

namespace JumpProcessesLean.TreeRSSA.Gen12

open Gen1 (Cache)
open Gen7 (floatInf floatNegInf)

theorem size_uset (a : FloatArray) (i : USize) (v : Float) (h : i.toNat < a.size) :
    (a.uset i v h).size = a.size := by
  cases a
  simp only [FloatArray.uset, FloatArray.size, Array.uset]
  exact Array.size_set _

theorem shiftRight_one_toNat (k : USize) : (k >>> 1).toNat = k.toNat / 2 := by
  rw [USize.toNat_shiftRight]
  have h1 : (1 : USize).toNat = 1 := by
    rcases USize.size_eq with h | h <;> simp [USize.toNat_ofNat, h]
  have h2 : 1 % System.Platform.numBits = 1 := by
    rcases System.Platform.numBits_eq with h | h <;> simp [h]
  rw [h1, h2, Nat.shiftRight_eq_div_pow]

theorem xor_one_eq (n : Nat) : n ^^^ 1 = 2 * (n / 2) + (1 - n % 2) := by
  have h1 : (n ^^^ 1) / 2 = n / 2 := by rw [Nat.xor_div_two]; simp
  have h2 : (n ^^^ 1) % 2 = 1 - n % 2 := by
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · have : (n ^^^ 1) % 2 = 1 := Nat.xor_mod_two_eq_one.mpr (by omega)
      omega
    · have : ¬ (n ^^^ 1) % 2 = 1 := fun hh => (Nat.xor_mod_two_eq_one.mp hh) (by omega)
      omega
  have := Nat.div_add_mod (n ^^^ 1) 2
  omega

theorem xor_one_toNat (node : USize) : (node ^^^ 1).toNat = 2 * (node.toNat / 2) + (1 - node.toNat % 2) := by
  rw [USize.toNat_xor]
  have h1 : (1 : USize).toNat = 1 := by
    rcases USize.size_eq with h | h <;> simp [USize.toNat_ofNat, h]
  rw [h1, xor_one_eq]

/-- Re-add the strict ancestors of `node` that are not ancestors of `other`, a node on the
same level (`Gen3.fixUntil`). `v` is the value at `node`; each new sum is carried up. -/
def fixUntilGo (P : USize) (n : Nat) (tree : FloatArray) (hP : 2 * P.toNat ≤ tree.size)
    (node : USize) (hn : node.toNat < 2 * P.toNat) (other : USize) (v : Float) : FloatArray :=
  match n with
  | 0 => tree
  | n + 1 =>
    let k := node >>> 1
    let o := other >>> 1
    if k = o then tree
    else
      have hs : (node ^^^ 1).toNat < tree.size := by rw [xor_one_toNat]; omega
      have hk : k.toNat < tree.size := by rw [shiftRight_one_toNat]; omega
      let v := v + tree.uget (node ^^^ 1) hs
      fixUntilGo P n (tree.uset k v hk) (by rw [size_uset]; exact hP) k
        (by rw [shiftRight_one_toNat]; omega) o v

/-- Re-add the `n` ancestors of `node` (`Gen1.fixPath`), carrying each new sum up. -/
def fixPathGo (P : USize) (n : Nat) (tree : FloatArray) (hP : 2 * P.toNat ≤ tree.size)
    (node : USize) (hn : node.toNat < 2 * P.toNat) (v : Float) : FloatArray :=
  match n with
  | 0 => tree
  | n + 1 =>
    let k := node >>> 1
    have hs : (node ^^^ 1).toNat < tree.size := by rw [xor_one_toNat]; omega
    have hk : k.toNat < tree.size := by rw [shiftRight_one_toNat]; omega
    let v := v + tree.uget (node ^^^ 1) hs
    fixPathGo P n (tree.uset k v hk) (by rw [size_uset]; exact hP) k
      (by rw [shiftRight_one_toNat]; omega) v

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

/-- `Gen11.descendAt` through this module's copy of the descent. -/
@[inline] def descendAt (tree : FloatArray) (depth : Nat) (P : USize)
    (hP2 : 2 * P.toNat < USize.size) (x : Float) : Nat :=
  if h : 2 * P ≤ tree.usize then
    (descendW tree P (Gen11.two_mul_le_size tree P hP2 h) hP2 1 Gen11.usize_one_pos x).toNat
  else Gen1.descend tree depth 1 x

theorem toUSize_toNat_of_lt {n m : Nat} (h : n < m) (hm : m < USize.size) :
    n.toUSize.toNat = n := by
  rw [Nat.toUSize, USize.toNat_ofNat_of_lt' (by omega)]

/-- `Gen3.fixUntil tree depth node other` through `fixUntilGo` when the tree has `2P` slots
and both nodes are below `2P`. -/
@[inline] def fixUntilAt (P : USize) (hP2 : 2 * P.toNat < USize.size) (tree : FloatArray)
    (depth node other : Nat) : FloatArray :=
  if h : 2 * P.toNat ≤ tree.size ∧ node < 2 * P.toNat ∧ other < 2 * P.toNat then
    have hn : node.toUSize.toNat < 2 * P.toNat := by
      rw [toUSize_toNat_of_lt h.2.1 hP2]; exact h.2.1
    have hn' : node.toUSize.toNat < tree.size := by omega
    fixUntilGo P depth tree h.1 node.toUSize hn other.toUSize (tree.uget node.toUSize hn')
  else Gen3.fixUntil tree depth node other

/-- `Gen1.fixPath tree depth node` through `fixPathGo` when the tree has `2P` slots and the
node is below `2P`. -/
@[inline] def fixPathAt (P : USize) (hP2 : 2 * P.toNat < USize.size) (tree : FloatArray)
    (depth node : Nat) : FloatArray :=
  if h : 2 * P.toNat ≤ tree.size ∧ node < 2 * P.toNat then
    have hn : node.toUSize.toNat < 2 * P.toNat := by
      rw [toUSize_toNat_of_lt h.2 hP2]; exact h.2
    have hn' : node.toUSize.toNat < tree.size := by omega
    fixPathGo P depth tree h.1 node.toUSize hn (tree.uget node.toUSize hn')
  else Gen1.fixPath tree depth node

/-- Generation 5's refresh of the dependents with the paths re-added on machine words. -/
def setBounds (C : Gen3.Compiled) (P : USize) (hP2 : 2 * P.toNat < USize.size)
    (lo hi : Array Nat) (s loS hiS : Nat) (ks : Array Nat) (fs : Array Gen3.Factor)
    (rs : FloatArray) : Nat → FloatArray → FloatArray → Nat → FloatArray × FloatArray
  | 0, lower, tree, pending =>
    (lower, if pending = 0 then tree else fixPathAt P hP2 tree C.depth pending)
  | i + 1, lower, tree, pending =>
    let n := ks.size - (i + 1)
    let k := ks[n]!
    let f := fs[n]!
    let lf := f.eval lo
    let lower := if lf = Gen5.evalAt f lo s loS then lower
      else lower.set! k (rs.get! n * natToFloat lf)
    let uf := f.eval hi
    if uf = Gen5.evalAt f hi s hiS then setBounds C P hP2 lo hi s loS hiS ks fs rs i lower tree pending
    else
      let leaf := C.leaves + k
      let tree := if pending = 0 then tree else fixUntilAt P hP2 tree C.depth pending leaf
      setBounds C P hP2 lo hi s loS hiS ks fs rs i lower (tree.set! leaf (rs.get! n * natToFloat uf))
        leaf

/-- Generation 7's refresh of a stale species with generation 12's bounds. -/
def rebracket (C : Gen5.Compiled) (P : USize) (hP2 : 2 * P.toNat < USize.size)
    (pop : Array Nat) (c : Cache) (s : Nat) : Cache :=
  let loS := c.lo[s]!
  let hiS := c.hi[s]!
  let lo := c.lo.set! s (bracket C.base.ms[s]! pop[s]!).1
  let hi := c.hi.set! s (bracket C.base.ms[s]! pop[s]!).2
  let ks := C.base.deps[s]!
  let (lower, tree) := setBounds C.base P hP2 lo hi s loS hiS ks C.depFactors[s]! C.depRates[s]!
    ks.size c.lower c.tree 0
  ⟨lo, hi, lower, tree⟩

@[inline] def refresh (C : Gen5.Compiled) (P : USize) (hP2 : 2 * P.toNat < USize.size)
    (ms : Array Nat) (pop : Array Nat) (c : Cache) (s : Nat) : Cache :=
  if Gen9.staleI ms[s]! pop[s]! c.lo[s]! c.hi[s]! then rebracket C P hP2 pop c s else c

@[inline] def fire (C : Gen6.Compiled) (P : USize) (hP2 : 2 * P.toNat < USize.size)
    (ms : Array Nat) (pop : Array Nat) (c : Cache) (j : Nat) : Array Nat × Cache :=
  let chs := C.changes[j]!
  let pop := chs.foldl Gen6.Change.apply pop
  (pop, chs.foldl (fun c ch => refresh C.gen5 P hP2 ms pop c ch.species) c)

/-- Generation 11's driver with generation 12's firing. -/
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
                  let (pop, c) := fire C P hP2 ms pop c j
                  let trace := if save then trace.push (time, ⟨pop, c.lo, c.hi⟩) else trace
                  let total := c.tree.get! 1
                  if !decide (total < floatInf) then .error (.invalidRate numRx)
                  else if !decide (floatNegInf < total) then .error (.invalidRate numRx)
                  else if !decide (floatZero < total) then
                    .ok ⟨⟨pop, c.lo, c.hi⟩, horizon, count + 1, ⟨rng.s0, rng.s1, rng.s2, rng.s3⟩,
                      trace.push (horizon, ⟨pop, c.lo, c.hi⟩)⟩
                  else
                    run C ms depth leaves numRx P hP2 rates factors horizon save cap ef cap pop c
                      time total floatZero rng.s0 rng.s1 rng.s2 rng.s3 (count + 1) trace
            else
              run C ms depth leaves numRx P hP2 rates factors horizon save cap evFuel pf pop c now
                total elapsed rng.s0 rng.s1 rng.s2 rng.s3 count trace
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
    Gen12.start C horizon saveEvents maxProposals maxEvents initial.pop
      (Gen3.initialCache C.gen5.base initial) start rng 0 #[(start, initial)]

end JumpProcessesLean.TreeRSSA.Gen12
