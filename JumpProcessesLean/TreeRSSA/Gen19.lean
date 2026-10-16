import JumpProcessesLean.TreeRSSA.Gen18

/-!
# Tree-RSSA, generation 19: no lower bounds

Generations 1 to 18 keep each reaction's lower bound, its propensity at the lower ends of the
brackets, accept a proposal at once when the threshold `v · upper` is at most the lower bound and
otherwise compute the exact propensity. Every refresh recomputes the lower bounds of the
refreshed species' dependents.

For factors of order at most two the exact propensity is the rate times at most two counts read
from the population, no dearer than reading the lower bound. While the counts lie inside their
brackets the lower bound is at most the exact propensity: the integer factor is monotone in
every count, and so is rounding. So the lower bound accepts only proposals that the exact
propensity accepts, and generation 19 tests the exact propensity alone. It keeps no lower
bounds, and its refreshes compute only the upper bounds.
-/

namespace JumpProcessesLean.TreeRSSA.Gen19

open Gen1 (Cache)
open Gen7 (floatInf floatNegInf)
open Gen18 (cget cset ChangeW DepW FactorW Compiled compileW applyW smallFrom staleW bracketLo
  bracketHi ff2 partnerW evalW ofCounts toCounts allSmall)

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

/-! ## Refreshes without lower bounds -/

/-- The brackets as count arrays and the tree of upper bounds. -/
structure CacheV where
  lo : FloatArray
  hi : FloatArray
  tree : FloatArray

/-- Generation 18's `setBoundsW` without the lower bounds. -/
def setBoundsV (leaves P : USize) (hP2 : 2 * P.toNat < USize.size) (D : USize)
    (hi : FloatArray) (h0 h1 g0 g1 : Float) (ds : Array DepW) (i : USize) (tree : FloatArray)
    (pending : USize) : FloatArray :=
  if h : i < ds.usize then
    have hi' := Gen15.lt_size_of_lt_usize ds i h
    let d := ds.uget i hi'
    let pH := partnerW d hi
    let bN := if d.two then h1 else h0
    if bN == (if d.two then g1 else g0) then
      setBoundsV leaves P hP2 D hi h0 h1 g0 g1 ds (i + 1) tree pending
    else if pH == floatZero then
      setBoundsV leaves P hP2 D hi h0 h1 g0 g1 ds (i + 1) tree pending
    else
      let leaf := leaves + d.k
      let tree := if pending = 0 then tree
        else Gen16.fixUntilAt P hP2 tree D.toNat D pending.toNat leaf.toNat
      setBoundsV leaves P hP2 D hi h0 h1 g0 g1 ds (i + 1)
        (tree.set! leaf.toNat (d.rate * (bN * pH))) leaf
  else if pending = 0 then tree else Gen16.fixPathAt P hP2 tree D.toNat D pending.toNat
termination_by ds.size - i.toNat
decreasing_by
  all_goals (rw [Gen15.succ_toNat_of_lt_usize ds i h]; omega)

/-- Generation 18's `rebracketW` without the lower bounds. -/
@[inline] def rebracketV (W : Compiled) (leaves P : USize) (hP2 : 2 * P.toNat < USize.size)
    (D : USize) (pop : FloatArray) (c : CacheV) (s : USize) : CacheV :=
  let x := (cget pop s).toUInt64
  let m := (cget W.ms s).toUInt64
  let hiS := cget c.hi s
  let loN := (bracketLo m x).toFloat
  let hiN := (bracketHi m x).toFloat
  let lo := cset c.lo s loN
  let hi := cset c.hi s hiN
  ⟨lo, hi, setBoundsV leaves P hP2 D hi hiN (ff2 hiN) hiS (ff2 hiS) (Gen17.aget W.deps s) 0
    c.tree 0⟩

/-- Refresh the brackets of the changed species `chs[i], chs[i+1], …` that left them. -/
def refreshFromV (W : Compiled) (leaves P : USize) (hP2 : 2 * P.toNat < USize.size) (D : USize)
    (chs : Array ChangeW) (pop : FloatArray) (i : USize) (c : CacheV) : CacheV :=
  if h : i < chs.usize then
    have hi' := Gen15.lt_size_of_lt_usize chs i h
    let s := (chs.uget i hi').species
    let c := if staleW (cget W.ms s) (cget pop s) (cget c.lo s) (cget c.hi s) then
      rebracketV W leaves P hP2 D pop c s else c
    refreshFromV W leaves P hP2 D chs pop (i + 1) c
  else c
termination_by chs.size - i.toNat
decreasing_by rw [Gen15.succ_toNat_of_lt_usize chs i h]; omega

/-! ## The driver -/

/-- The lower bounds at the brackets' lower ends `lo`, as generation 3 computes them. -/
def lowerOf (C : Gen6.Compiled) (lo : Array Nat) : FloatArray :=
  ⟨C.gen5.base.net.reactions.map (Gen2.rate · lo)⟩

/-- The state as generation 17 holds it, its lower bounds computed from the brackets. -/
@[inline] def toCache (C : Gen6.Compiled) (n : Nat) (c : CacheV) : Cache :=
  let lo := ofCounts c.lo n
  ⟨lo, ofCounts c.hi n, lowerOf C lo, c.tree⟩

/-- Generation 18's driver without lower bounds. `n` is the species count; `pop` has one more
entry, the staleness flag of the last firing. -/
def run (C : Gen6.Compiled) (codes : Array (Array Nat)) (W : Compiled) (msN : Array Nat) (n : Nat)
    (hms : msN.size = n) (hval : Gen15.ValidChanges C n) (nW : USize) (numRx : USize) (P : USize)
    (hP2 : 2 * P.toNat < USize.size) (D : USize) (rates : FloatArray) (horizon : Float)
    (save : Bool) (cap : USize) (evFuel prFuel : USize) (pop : FloatArray) (c : CacheV)
    (now total elapsed : Float) (s0 s1 s2 s3 : UInt64) (count : USize)
    (trace : Array (Float × State)) : Except Error (Solution Float State Xoshiro) :=
  if _hz : prFuel = 0 then .error .proposalLimit
  else
    if hT : 2 * P ≤ c.tree.usize then
    let rng : Xoshiro := ⟨s0, s1, s2, s3⟩
    let (u, rng) := rng.uniform
    if !decide (floatZero ≤ u) then .error .invalidUniform
    else if !decide (u < floatOne) then .error .invalidUniform
    else
      let (e, rng) := rng.exponential
      if !decide (e < floatInf) then .error .invalidExponential
      else if !decide (floatZero < e) then .error .invalidExponential
      else
        let elapsed := elapsed + e
        if !decide (elapsed < floatInf) then .error .invalidTime
        else if !decide (floatNegInf < elapsed) then .error .invalidTime
        else
          let (v, rng) := rng.uniform
          if !decide (floatZero ≤ v) then .error .invalidUniform
          else if !decide (v < floatOne) then .error .invalidUniform
          else
            let k := descendW c.tree P (Gen11.two_mul_le_size c.tree P hP2 hT) hP2 1
              Gen11.usize_one_pos (u * total)
            let j := k - P
            let acc :=
              if !decide (j < numRx) then false
              else
                let threshold := v * Gen17.fget c.tree k
                let actual := Gen17.fget rates j * evalW (Gen17.aget W.factors j) pop
                decide (floatZero < actual) && decide (threshold ≤ actual)
            if acc then
              let time := now + elapsed / total
              if !decide (time < floatInf) then .error .invalidTime
              else if !decide (floatNegInf < time) then .error .invalidTime
              else if !decide (now ≤ time) then .error .invalidTime
              else if !decide (time ≤ horizon) then
                let st : State := ⟨ofCounts pop n, ofCounts c.lo n, ofCounts c.hi n⟩
                .ok ⟨st, horizon, count.toNat, ⟨rng.s0, rng.s1, rng.s2, rng.s3⟩,
                  trace.push (horizon, st)⟩
              else if he : evFuel = 0 then .error .eventLimit
              else
                let chs := Gen17.aget W.changes j
                let p := applyW chs W.ms c.lo c.hi nW 0 pop false
                if cget p nW == floatZero then
                  let trace := if save then trace.push (time, ⟨ofCounts p n, ofCounts c.lo n,
                    ofCounts c.hi n⟩) else trace
                  run C codes W msN n hms hval nW numRx P hP2 D rates horizon save cap (evFuel - 1)
                    cap p c time total floatZero rng.s0 rng.s1 rng.s2 rng.s3 (count + 1) trace
                else if smallFrom chs p 0 then
                  let c' := refreshFromV W P P hP2 D chs p 0 c
                  let trace := if save then trace.push (time, ⟨ofCounts p n, ofCounts c'.lo n,
                    ofCounts c'.hi n⟩) else trace
                  let total := Gen17.fget c'.tree 1
                  if !decide (total < floatInf) then .error (.invalidRate numRx.toNat)
                  else if !decide (floatNegInf < total) then .error (.invalidRate numRx.toNat)
                  else if !decide (floatZero < total) then
                    let st : State := ⟨ofCounts p n, ofCounts c'.lo n, ofCounts c'.hi n⟩
                    .ok ⟨st, horizon, count.toNat + 1, ⟨rng.s0, rng.s1, rng.s2, rng.s3⟩,
                      trace.push (horizon, st)⟩
                  else
                    run C codes W msN n hms hval nW numRx P hP2 D rates horizon save cap
                      (evFuel - 1) cap p c' time total floatZero rng.s0 rng.s1 rng.s2 rng.s3
                      (count + 1) trace
                else
                  -- a count reached `2^25`: generation 17's refresh, then generation 17
                  let popN := ofCounts p n
                  if hpN : popN.size = n then
                    let cN := toCache C n c
                    let chsN := C.changes[j.toNat]!
                    let c' := chsN.foldl
                      (fun c ch => Gen16.refresh C.gen5 codes P hP2 msN popN c ch.species) cN
                    let trace := if save then trace.push (time, ⟨popN, c'.lo, c'.hi⟩) else trace
                    let total := Gen17.fget c'.tree 1
                    if !decide (total < floatInf) then .error (.invalidRate numRx.toNat)
                    else if !decide (floatNegInf < total) then .error (.invalidRate numRx.toNat)
                    else if !decide (floatZero < total) then
                      .ok ⟨⟨popN, c'.lo, c'.hi⟩, horizon, count.toNat + 1,
                        ⟨rng.s0, rng.s1, rng.s2, rng.s3⟩, trace.push (horizon, ⟨popN, c'.lo, c'.hi⟩)⟩
                    else if hs : c'.lo.size = n ∧ c'.hi.size = n then
                      Gen17.run C codes msN n hms hval numRx P hP2 C.gen5.base.rates
                        C.gen5.base.factors horizon save cap (evFuel - 1) cap popN hpN c' hs.1 hs.2
                        time total floatZero rng.s0 rng.s1 rng.s2 rng.s3 (count + 1) trace
                    else .error .invalidShape
                  else .error .invalidShape
            else
              run C codes W msN n hms hval nW numRx P hP2 D rates horizon save cap evFuel
                (prFuel - 1) pop c now total elapsed rng.s0 rng.s1 rng.s2 rng.s3 count trace
    else
      let popN := ofCounts pop n
      let cN := toCache C n c
      if hs : popN.size = n ∧ cN.lo.size = n ∧ cN.hi.size = n then
        Gen17.run C codes msN n hms hval numRx P hP2 C.gen5.base.rates C.gen5.base.factors horizon
          save cap evFuel prFuel popN hs.1 cN hs.2.1 hs.2.2 now total elapsed s0 s1 s2 s3 count
          trace
      else .error .invalidShape
termination_by (evFuel.toNat, prFuel.toNat)
decreasing_by
  all_goals first
    | (have : evFuel.toNat ≠ 0 := fun h => he (USize.toNat_inj.mp (by rw [h]; rfl))
       rw [Gen16.pred_toNat evFuel he]; exact Prod.Lex.left _ _ (by omega))
    | (have : prFuel.toNat ≠ 0 := fun h => _hz (USize.toNat_inj.mp (by rw [h]; rfl))
       rw [Gen16.pred_toNat prFuel _hz]; exact Prod.Lex.right _ (by omega))

/-- `2^52`, a bound on the rates. -/
def rateMax : Float := 4503599627370496

/-- Generation 18's start, entering generation 19's driver under generation 18's conditions
when every rate `r` has `0 ≤ r < 2^52`. -/
@[inline] def start (C : Gen6.Compiled) (codes : Array (Array Nat)) (horizon : Float) (save : Bool)
    (cap fuel : Nat) (pop : Array Nat) (c : Cache) (now : Float) (rng : Xoshiro) (count : Nat)
    (trace : Array (Float × State)) : Except Error (Solution Float State Xoshiro) :=
  let n := C.gen5.base.ms.size
  let total := c.tree.get! 1
  if !Gen7.finite total then .error (.invalidRate C.gen5.base.numRx)
  else if !decide (floatZero < total) then
    .ok ⟨⟨pop, c.lo, c.hi⟩, horizon, count, rng, trace.push (horizon, ⟨pop, c.lo, c.hi⟩)⟩
  else if h : 2 * C.gen5.base.leaves < USize.size then
    if hs : pop.size = n ∧ c.lo.size = n ∧ c.hi.size = n ∧ Gen15.validChanges C n = true ∧
        Gen17.changesOK C = true ∧ Gen17.inBrackets C.gen5.base.ms pop c.lo c.hi = true ∧
        count + fuel < USize.size ∧ cap < USize.size ∧ C.gen5.base.numRx < USize.size ∧
        n + 1 < USize.size ∧ allSmall pop = true ∧ allSmall c.lo = true ∧ allSmall c.hi = true ∧
        allSmall C.gen5.base.ms = true ∧
        C.gen5.base.factors.all (FactorW.ok n) = true ∧
        codes.all (·.all fun c => c == 0 || c == 1 || (c % 4 == 0 && decide (4 ≤ c) &&
          decide (c / 4 ≤ n))) = true ∧
        codes.size = n ∧ C.gen5.depRates.size = n ∧ C.gen5.base.deps.size = n ∧
        (List.range n).all (fun s => (codes[s]!).size == (C.gen5.base.deps[s]!).size &&
          (C.gen5.depRates[s]!).size == (C.gen5.base.deps[s]!).size &&
          decide ((C.gen5.base.deps[s]!).size < USize.size) &&
          (C.gen5.base.deps[s]!).all (· < C.gen5.base.leaves)) = true ∧
        C.changes.all (·.all fun ch => decide (ch.up < 67108864) && decide (ch.down < 67108864))
          = true ∧
        C.gen5.base.rates.data.all (fun r => decide (floatZero ≤ r) && decide (r < rateMax))
          = true then
      let W := compileW C codes
      run C codes W C.gen5.base.ms n rfl (Gen15.validChanges_spec hs.2.2.2.1) n.toUSize
        C.gen5.base.numRx.toUSize C.gen5.base.leaves.toUSize (Gen11.leaves_toUSize h)
        C.gen5.base.depth.toUSize C.gen5.base.rates horizon save cap.toUSize fuel.toUSize cap.toUSize
        ((toCounts pop).push 0) ⟨toCounts c.lo, toCounts c.hi, c.tree⟩ now total floatZero
        rng.s0 rng.s1 rng.s2 rng.s3 count.toUSize trace
    else Gen17.start C codes horizon save cap fuel pop c now rng count trace
  else Gen17.start C codes horizon save cap fuel pop c now rng count trace

def simulate (net : Network Float) (initial : State) (start horizon : Float) (rng : Xoshiro)
    (maxEvents : Nat := 1000000) (saveEvents : Bool := false) (maxProposals : Nat := 100000) :
    Except Error (Solution Float State Xoshiro) :=
  if !(Gen7.finite start && Gen7.finite horizon && decide (start ≤ horizon)) then
    .error .invalidTime
  else if !decide (start < horizon) then .ok ⟨initial, horizon, 0, rng, #[(start, initial)]⟩
  else
    let C := Gen6.compile net
    Gen19.start C (Gen13.codesOf C.gen5) horizon saveEvents maxProposals maxEvents initial.pop
      (Gen3.initialCache C.gen5.base initial) start rng 0 #[(start, initial)]

end JumpProcessesLean.TreeRSSA.Gen19
