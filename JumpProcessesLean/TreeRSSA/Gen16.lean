import JumpProcessesLean.TreeRSSA.Gen15

/-!
# Tree-RSSA, generation 16: refreshes on machine words

On the largest network half of the instructions after generation 15 were the refreshes'
re-evaluation of the dependents' bounds: per dependent, about twenty-five natural-number
operations, each testing that its operands are small and that its result does not overflow,
and an index loop counting down in natural numbers; a further quarter were the tree path walks,
whose fuel was a natural number too.

Generation 16 walks the dependents with a machine-word index and reads their records without
tests. The refreshed species' four powers at the old and new bracket ends are computed once per
refresh, for both stoichiometries. A bound changes exactly when the power changes and the
partner factor is not zero, since `a' p = a p` iff `a' = a` or `p = 0`; the product is formed
only for a changed bound. The path walks count their levels in a machine word. The bounds and
sums written are generation 15's (`Proofs/TreeRSSAGen16.lean`).
-/

namespace JumpProcessesLean.TreeRSSA.Gen16

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

theorem pred_toNat (n : USize) (h : n ≠ 0) : (n - 1).toNat = n.toNat - 1 := by
  have h1 : (1 : USize).toNat = 1 := by
    rcases USize.size_eq with h | h <;> simp [USize.toNat_ofNat, h]
  have hn : 0 < n.toNat := by
    rcases Nat.eq_zero_or_pos n.toNat with h0 | h0
    · exact absurd (USize.toNat_inj.mp (by rw [h0]; rfl)) h
    · exact h0
  rw [USize.toNat_sub_of_le _ _ (by show (1 : USize).toNat ≤ n.toNat; rw [h1]; omega), h1]

/-- `Gen12.fixUntilGo` with the level count in a machine word. -/
def fixUntilGo (P : USize) (n : USize) (tree : FloatArray) (hP : 2 * P.toNat ≤ tree.size)
    (node : USize) (hn : node.toNat < 2 * P.toNat) (other : USize) (v : Float) : FloatArray :=
  if hz : n = 0 then tree
  else
    let k := node >>> 1
    let o := other >>> 1
    if k = o then tree
    else
      have hs : (node ^^^ 1).toNat < tree.size := by rw [Gen12.xor_one_toNat]; omega
      have hk : k.toNat < tree.size := by rw [Gen12.shiftRight_one_toNat]; omega
      let v := v + tree.uget (node ^^^ 1) hs
      fixUntilGo P (n - 1) (tree.uset k v hk) (by rw [Gen12.size_uset]; exact hP) k
        (by rw [Gen12.shiftRight_one_toNat]; omega) o v
termination_by n.toNat
decreasing_by rw [pred_toNat n hz]; have : n.toNat ≠ 0 := fun h => hz (USize.toNat_inj.mp (by rw [h]; rfl)); omega

/-- `Gen12.fixPathGo` with the level count in a machine word. -/
def fixPathGo (P : USize) (n : USize) (tree : FloatArray) (hP : 2 * P.toNat ≤ tree.size)
    (node : USize) (hn : node.toNat < 2 * P.toNat) (v : Float) : FloatArray :=
  if hz : n = 0 then tree
  else
    let k := node >>> 1
    have hs : (node ^^^ 1).toNat < tree.size := by rw [Gen12.xor_one_toNat]; omega
    have hk : k.toNat < tree.size := by rw [Gen12.shiftRight_one_toNat]; omega
    let v := v + tree.uget (node ^^^ 1) hs
    fixPathGo P (n - 1) (tree.uset k v hk) (by rw [Gen12.size_uset]; exact hP) k
      (by rw [Gen12.shiftRight_one_toNat]; omega) v
termination_by n.toNat
decreasing_by rw [pred_toNat n hz]; have : n.toNat ≠ 0 := fun h => hz (USize.toNat_inj.mp (by rw [h]; rfl)); omega

/-- `Gen12.fixUntilAt` through this module's walk; `D` is the depth as a machine word. -/
@[inline] def fixUntilAt (P : USize) (hP2 : 2 * P.toNat < USize.size) (tree : FloatArray)
    (depth : Nat) (D : USize) (node other : Nat) : FloatArray :=
  if h : 2 * P.toNat ≤ tree.size ∧ node < 2 * P.toNat ∧ other < 2 * P.toNat ∧ D.toNat = depth then
    have hn : node.toUSize.toNat < 2 * P.toNat := by
      rw [Gen12.toUSize_toNat_of_lt h.2.1 hP2]; exact h.2.1
    have hn' : node.toUSize.toNat < tree.size := by omega
    fixUntilGo P D tree h.1 node.toUSize hn other.toUSize (tree.uget node.toUSize hn')
  else Gen3.fixUntil tree depth node other

/-- `Gen12.fixPathAt` through this module's walk. -/
@[inline] def fixPathAt (P : USize) (hP2 : 2 * P.toNat < USize.size) (tree : FloatArray)
    (depth : Nat) (D : USize) (node : Nat) : FloatArray :=
  if h : 2 * P.toNat ≤ tree.size ∧ node < 2 * P.toNat ∧ D.toNat = depth then
    have hn : node.toUSize.toNat < 2 * P.toNat := by
      rw [Gen12.toUSize_toNat_of_lt h.2.1 hP2]; exact h.2.1
    have hn' : node.toUSize.toNat < tree.size := by omega
    fixPathGo P D tree h.1 node.toUSize hn (tree.uget node.toUSize hn')
  else Gen1.fixPath tree depth node

/-- Generation 13's refresh of the dependents `ks[i], ks[i+1], …` with a machine-word index. The
records `cs`, `rs` have the dependents' size. `l0 l1` are the refreshed species' powers
`ff(x, 1)`, `ff(x, 2)` at the new lower end and `m0 m1` at the old one; `h0 h1`, `g0 g1` are
those at the upper ends. -/
def setBounds (C : Gen3.Compiled) (P : USize) (hP2 : 2 * P.toNat < USize.size) (D : USize)
    (lo hi : Array Nat) (s loS hiS l0 l1 m0 m1 h0 h1 g0 g1 : Nat) (ks cs : Array Nat)
    (fs : Array Gen3.Factor) (rs : FloatArray) (hcs : cs.size = ks.size) (hrs : rs.size = ks.size)
    (i : USize) (lower tree : FloatArray) (pending : Nat) : FloatArray × FloatArray :=
  if h : i < ks.usize then
    have hi' := Gen15.lt_size_of_lt_usize ks i h
    let k := ks.uget i hi'
    let c := cs.uget i (by rw [hcs]; exact hi')
    let r := rs.uget i (by rw [hrs]; exact hi')
    if c = 2 then
      let f := fs[i.toNat]!
      let lf := f.eval lo
      let lower := if lf = Gen5.evalAt f lo s loS then lower else lower.set! k (r * natToFloat lf)
      let uf := f.eval hi
      if uf = Gen5.evalAt f hi s hiS then
        setBounds C P hP2 D lo hi s loS hiS l0 l1 m0 m1 h0 h1 g0 g1 ks cs fs rs hcs hrs (i + 1)
          lower tree pending
      else
        let leaf := C.leaves + k
        let tree := if pending = 0 then tree else fixUntilAt P hP2 tree C.depth D pending leaf
        setBounds C P hP2 D lo hi s loS hiS l0 l1 m0 m1 h0 h1 g0 g1 ks cs fs rs hcs hrs (i + 1)
          lower (tree.set! leaf (r * natToFloat uf)) leaf
    else
      let odd := c % 2 = 1
      let pL := Gen13.partner c lo
      let aN := if odd then l1 else l0
      let lower := if aN = (if odd then m1 else m0) then lower
        else if pL = 0 then lower else lower.set! k (r * natToFloat (aN * pL))
      let pH := Gen13.partner c hi
      let bN := if odd then h1 else h0
      if bN = (if odd then g1 else g0) then
        setBounds C P hP2 D lo hi s loS hiS l0 l1 m0 m1 h0 h1 g0 g1 ks cs fs rs hcs hrs (i + 1)
          lower tree pending
      else if pH = 0 then
        setBounds C P hP2 D lo hi s loS hiS l0 l1 m0 m1 h0 h1 g0 g1 ks cs fs rs hcs hrs (i + 1)
          lower tree pending
      else
        let leaf := C.leaves + k
        let tree := if pending = 0 then tree else fixUntilAt P hP2 tree C.depth D pending leaf
        setBounds C P hP2 D lo hi s loS hiS l0 l1 m0 m1 h0 h1 g0 g1 ks cs fs rs hcs hrs (i + 1)
          lower (tree.set! leaf (r * natToFloat (bN * pH))) leaf
  else (lower, if pending = 0 then tree else fixPathAt P hP2 tree C.depth D pending)
termination_by ks.size - i.toNat
decreasing_by
  all_goals (rw [Gen15.succ_toNat_of_lt_usize ks i h]; omega)

/-- Generation 13's refresh of a stale species with generation 16's bounds. -/
def rebracket (C : Gen5.Compiled) (codes : Array (Array Nat)) (P : USize)
    (hP2 : 2 * P.toNat < USize.size) (pop : Array Nat) (c : Cache) (s : Nat) : Cache :=
  let loS := c.lo[s]!
  let hiS := c.hi[s]!
  let lo := c.lo.set! s (bracket C.base.ms[s]! pop[s]!).1
  let hi := c.hi.set! s (bracket C.base.ms[s]! pop[s]!).2
  let ks := C.base.deps[s]!
  let cs := codes[s]!
  let rs := C.depRates[s]!
  let loN := lo[s]!
  let hiN := hi[s]!
  if h : cs.size = ks.size ∧ rs.size = ks.size ∧ ks.size < USize.size then
    let r := setBounds C.base P hP2 C.base.depth.toUSize lo hi s loS hiS
      loN (loN * (loN - 1)) loS (loS * (loS - 1)) hiN (hiN * (hiN - 1)) hiS (hiS * (hiS - 1))
      ks cs C.depFactors[s]! rs h.1 h.2.1 0 c.lower c.tree 0
    ⟨lo, hi, r.1, r.2⟩
  else
    let r := Gen13.setBounds C.base P hP2 lo hi s loS hiS loN hiN ks cs
      C.depFactors[s]! rs ks.size c.lower c.tree 0
    ⟨lo, hi, r.1, r.2⟩

@[inline] def refresh (C : Gen5.Compiled) (codes : Array (Array Nat)) (P : USize)
    (hP2 : 2 * P.toNat < USize.size) (ms : Array Nat) (pop : Array Nat) (c : Cache) (s : Nat) :
    Cache :=
  if Gen9.staleI ms[s]! pop[s]! c.lo[s]! c.hi[s]! then rebracket C codes P hP2 pop c s else c

theorem foldRefresh_size (C : Gen5.Compiled) (codes : Array (Array Nat)) (P : USize)
    (hP2 : 2 * P.toNat < USize.size) (ms pop : Array Nat) (chs : Array Gen6.Change) (c : Cache) :
    (chs.foldl (fun c ch => refresh C codes P hP2 ms pop c ch.species) c).lo.size = c.lo.size ∧
      (chs.foldl (fun c ch => refresh C codes P hP2 ms pop c ch.species) c).hi.size =
        c.hi.size := by
  rw [← Array.foldl_toList]
  generalize chs.toList = l
  induction l generalizing c with
  | nil => exact ⟨rfl, rfl⟩
  | cons ch l ih =>
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih (refresh C codes P hP2 ms pop c ch.species)
    have h3 : (refresh C codes P hP2 ms pop c ch.species).lo.size = c.lo.size ∧
        (refresh C codes P hP2 ms pop c ch.species).hi.size = c.hi.size := by
      unfold refresh rebracket
      split
      · dsimp only
        split <;> simp only [Array.size_set!, and_self]
      · exact ⟨rfl, rfl⟩
    exact ⟨h1.trans h3.1, h2.trans h3.2⟩

/-- Generation 15's firing with generation 16's refreshes. -/
@[inline] def fire (C : Gen6.Compiled) (codes : Array (Array Nat)) (P : USize)
    (hP2 : 2 * P.toNat < USize.size) (ms : Array Nat) (n : Nat) (hms : ms.size = n)
    (hval : Gen15.ValidChanges C n) (pop : Array Nat) (hpop : pop.size = n) (c : Cache)
    (hlo : c.lo.size = n) (hhi : c.hi.size = n) (j : Nat) :
    {r : Array Nat × Cache // r.1.size = n ∧ r.2.lo.size = n ∧ r.2.hi.size = n} :=
  let chs := C.changes[j]!
  let r := Gen15.applyFrom chs n (hval j) 0 pop hpop
  if Gen15.anyStale chs n (hval j) ms r.val c.lo c.hi hms r.property hlo hhi 0 then
    let c' := chs.foldl (fun c ch => refresh C.gen5 codes P hP2 ms r.val c ch.species) c
    have hs := foldRefresh_size C.gen5 codes P hP2 ms r.val chs c
    have h1 : c'.lo.size = n := by rw [← hlo]; exact hs.1
    have h2 : c'.hi.size = n := by rw [← hhi]; exact hs.2
    ⟨(r.val, c'), r.property, h1, h2⟩
  else ⟨(r.val, c), r.property, hlo, hhi⟩

/-- Generation 15's driver with generation 16's refreshes; if the tree's size test fails the
proposal is generation 15's. -/
def run (C : Gen6.Compiled) (codes : Array (Array Nat)) (ms : Array Nat) (n : Nat)
    (hms : ms.size = n) (hval : Gen15.ValidChanges C n) (depth leaves numRx : Nat) (P : USize)
    (hP2 : 2 * P.toNat < USize.size) (rates : FloatArray)
    (factors : Array Gen3.Factor) (horizon : Float) (save : Bool) (cap : Nat)
    (evFuel prFuel : Nat) (pop : Array Nat) (hpop : pop.size = n) (c : Cache)
    (hlo : c.lo.size = n) (hhi : c.hi.size = n) (now total elapsed : Float)
    (s0 s1 s2 s3 : UInt64) (count : Nat) (trace : Array (Float × State)) :
    Except Error (Solution Float State Xoshiro) :=
  match prFuel with
  | 0 => .error .proposalLimit
  | pf + 1 =>
    if hT : 2 * P ≤ c.tree.usize then
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
            let j := (descendW c.tree P (Gen11.two_mul_le_size c.tree P hP2 hT) hP2 1 Gen11.usize_one_pos
              (u * total)).toNat - leaves
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
                  let ⟨(pop, c), hpop, hlo, hhi⟩ := Gen16.fire C codes P hP2 ms n hms hval pop hpop c hlo hhi j
                  let trace := if save then trace.push (time, ⟨pop, c.lo, c.hi⟩) else trace
                  let total := c.tree.get! 1
                  if !decide (total < floatInf) then .error (.invalidRate numRx)
                  else if !decide (floatNegInf < total) then .error (.invalidRate numRx)
                  else if !decide (floatZero < total) then
                    .ok ⟨⟨pop, c.lo, c.hi⟩, horizon, count + 1, ⟨rng.s0, rng.s1, rng.s2, rng.s3⟩,
                      trace.push (horizon, ⟨pop, c.lo, c.hi⟩)⟩
                  else
                    run C codes ms n hms hval depth leaves numRx P hP2 rates factors horizon save cap ef cap
                      pop hpop c hlo hhi time total floatZero rng.s0 rng.s1 rng.s2 rng.s3 (count + 1) trace
            else
              run C codes ms n hms hval depth leaves numRx P hP2 rates factors horizon save cap evFuel pf
                pop hpop c hlo hhi now total elapsed rng.s0 rng.s1 rng.s2 rng.s3 count trace
    else
      Gen15.run C codes ms n hms hval depth leaves numRx P hP2 rates factors horizon save cap evFuel
        (pf + 1) pop hpop c hlo hhi now total elapsed s0 s1 s2 s3 count trace
termination_by (evFuel, prFuel)

@[inline] def start (C : Gen6.Compiled) (codes : Array (Array Nat)) (horizon : Float) (save : Bool) (cap : Nat) (fuel : Nat)
    (pop : Array Nat) (c : Cache) (now : Float) (rng : Xoshiro) (count : Nat)
    (trace : Array (Float × State)) : Except Error (Solution Float State Xoshiro) :=
  let total := c.tree.get! 1
  if !Gen7.finite total then .error (.invalidRate C.gen5.base.numRx)
  else if !decide (floatZero < total) then
    .ok ⟨⟨pop, c.lo, c.hi⟩, horizon, count, rng, trace.push (horizon, ⟨pop, c.lo, c.hi⟩)⟩
  else if h : 2 * C.gen5.base.leaves < USize.size then
    if hs : pop.size = C.gen5.base.ms.size ∧ c.lo.size = C.gen5.base.ms.size ∧
        c.hi.size = C.gen5.base.ms.size ∧ Gen15.validChanges C C.gen5.base.ms.size = true then
      run C codes C.gen5.base.ms C.gen5.base.ms.size rfl (Gen15.validChanges_spec hs.2.2.2)
        C.gen5.base.depth C.gen5.base.leaves C.gen5.base.numRx C.gen5.base.leaves.toUSize
        (Gen11.leaves_toUSize h) C.gen5.base.rates C.gen5.base.factors horizon save cap fuel cap pop
        hs.1 c hs.2.1 hs.2.2.1 now total floatZero rng.s0 rng.s1 rng.s2 rng.s3 count trace
    else
      Gen14.run C codes C.gen5.base.ms C.gen5.base.depth C.gen5.base.leaves C.gen5.base.numRx
        C.gen5.base.leaves.toUSize (Gen11.leaves_toUSize h) C.gen5.base.rates C.gen5.base.factors
        horizon save cap fuel cap pop c now total floatZero rng.s0 rng.s1 rng.s2 rng.s3 count trace
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
    Gen16.start C (Gen13.codesOf C.gen5) horizon saveEvents maxProposals maxEvents initial.pop
      (Gen3.initialCache C.gen5.base initial) start rng 0 #[(start, initial)]

end JumpProcessesLean.TreeRSSA.Gen16
