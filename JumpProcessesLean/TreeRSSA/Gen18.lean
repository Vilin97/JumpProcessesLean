import JumpProcessesLean.TreeRSSA.Gen17

/-!
# Tree-RSSA, generation 18: counts as floats

After generation 17 half of the instructions on the network with the thinnest margin were
firing and refreshes, nearly all of them operations on natural numbers held in arrays of boxed
objects: every addition, subtraction, comparison and product tests that its operands are small
and that its result does not overflow, and every array write tests the old entry before
releasing it.

Generation 18 keeps the populations and the brackets as floats in `FloatArray`s. Below `2^53`
an integer is a float exactly, and so are sums and differences of such integers; comparisons
agree; and the float product of two exact integers is their integer product rounded once, which
is what `natToFloat` of the product is. Below `2^26` every factor of a bound is exact. The
changes, the dependents and the factors are records of machine words and floats. The counts stay
below `2^26`: a species inside its bracket is below its upper end, and a refresh runs on floats
only when the changed counts are below `2^25`, so that the new ends stay below `2^26`. Otherwise,
and for networks with a factor of order above two, generation 17 runs.
-/

namespace JumpProcessesLean.TreeRSSA.Gen18

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

/-! ## Counts in a `FloatArray` -/

/-- Entry `i` of a count array (`0` past its end). -/
@[inline] def cget (a : FloatArray) (i : USize) : Float := Gen17.fget a i

/-- Write `v` to entry `i` of a count array (no change past its end). -/
@[inline] def cset (a : FloatArray) (i : USize) (v : Float) : FloatArray :=
  if h : i < a.usize then a.uset i v (Gen17.lt_size_of_lt_usize a i h) else a

/-- Natural numbers as floats. -/
def toCounts (xs : Array Nat) : FloatArray := ⟨xs.map natToFloat⟩

/-- The first `n` entries of a count array as natural numbers. -/
def ofCounts (a : FloatArray) (n : Nat) : Array Nat :=
  (Array.range n).map fun i => (a.get! i).toUInt64.toNat

/-! ## Compiled records -/

/-- A change of one species: it adds `amount` or removes it. -/
structure ChangeW where
  species : USize
  add : Bool
  amount : Float
  deriving Inhabited

/-- A dependent reaction `k` of a species, with its rate and its factor decoded from its code (see
`Gen13.code`): `x (x - 1)` of the species if `two` (code `1`), else `x` times the count of the
partner species `partner - 1` if `partner ≠ 0` (code `4 partner`). -/
structure DepW where
  k : USize
  two : Bool
  partner : USize
  rate : Float
  deriving Inhabited

/-- A factor of order at most two: `x_s` (`kind = 0`), `x_s (x_s - 1)` (`1`), `x_s x_t` (`2`). -/
structure FactorW where
  kind : UInt64
  s : USize
  t : USize
  deriving Inhabited

def ChangeW.ofChange (ch : Gen6.Change) : ChangeW :=
  ⟨ch.species.toUSize, ch.down == 0, natToFloat (if ch.down == 0 then ch.up else ch.down)⟩

def FactorW.ofFactor : Gen3.Factor → FactorW
  | .one s => ⟨0, s.toUSize, 0⟩
  | .two s => ⟨1, s.toUSize, 0⟩
  | .pair s _ t _ => ⟨2, s.toUSize, t.toUSize⟩
  | .general _ => ⟨3, 0, 0⟩

/-- The factor has order at most two and its species are below `n`. -/
def FactorW.ok (n : Nat) : Gen3.Factor → Bool
  | .one s => decide (s < n)
  | .two s => decide (s < n)
  | .pair s ν t μ => decide (s < n) && decide (t < n) && ν == 1 && μ == 1
  | .general _ => false

structure Compiled where
  changes : Array (Array ChangeW)
  deps : Array (Array DepW)
  factors : Array FactorW
  ms : FloatArray

def compileW (C : Gen6.Compiled) (codes : Array (Array Nat)) : Compiled :=
  ⟨C.changes.map (·.map ChangeW.ofChange),
   (Array.range C.gen5.base.ms.size).map fun s =>
     let ks := C.gen5.base.deps[s]!
     let cs := codes[s]!
     let rs := C.gen5.depRates[s]!
     (Array.range ks.size).map fun i => ⟨ks[i]!.toUSize, cs[i]! == 1, (cs[i]! / 4).toUSize, rs.get! i⟩,
   C.gen5.base.factors.map FactorW.ofFactor,
   toCounts C.gen5.base.ms⟩

/-! ## Firing -/

/-- Generation 17's `applyTest` on counts: apply the changes `chs[i], chs[i+1], …` and write to
entry `n` whether a changed species left its bracket. -/
def applyW (chs : Array ChangeW) (ms lo hi : FloatArray) (n : USize) (i : USize) (pop : FloatArray)
    (stale : Bool) : FloatArray :=
  if h : i < chs.usize then
    have hi' := Gen15.lt_size_of_lt_usize chs i h
    let ch := chs.uget i hi'
    let s := ch.species
    let old := cget pop s
    if ch.add then
      let v := old + ch.amount
      applyW chs ms lo hi n (i + 1) (cset pop s v) (stale || decide (cget hi s < v))
    else
      let v := if old ≤ ch.amount then floatZero else old - ch.amount
      applyW chs ms lo hi n (i + 1) (cset pop s v)
        (stale || decide (v < cget lo s) || (decide (v < cget ms s) && cget hi s != v))
  else cset pop n (if stale then floatOne else floatZero)
termination_by chs.size - i.toNat
decreasing_by
  all_goals (rw [Gen15.succ_toNat_of_lt_usize chs i h]; omega)

/-- `2^25`. -/
def twoPow25 : Float := 33554432

/-- Every changed species' count is below `2^25`. -/
def smallFrom (chs : Array ChangeW) (pop : FloatArray) (i : USize) : Bool :=
  if h : i < chs.usize then
    have hi' := Gen15.lt_size_of_lt_usize chs i h
    let ch := chs.uget i hi'
    if cget pop ch.species < twoPow25 then smallFrom chs pop (i + 1) else false
  else true
termination_by chs.size - i.toNat
decreasing_by rw [Gen15.succ_toNat_of_lt_usize chs i h]; omega

/-! ## Refreshes on counts -/

/-- The cache with the brackets as count arrays. -/
structure CacheW where
  lo : FloatArray
  hi : FloatArray
  lower : FloatArray
  tree : FloatArray

@[inline] def staleW (m x l h : Float) : Bool :=
  decide (x < l) || decide (h < x) || (decide (x < m) && h != x)

@[inline] def bracketLo (m x : UInt64) : UInt64 :=
  if x = 0 then 0 else if x < m then x else if x < 25 then (if x < 4 then 0 else x - 4)
  else 9 * x / 10

@[inline] def bracketHi (m x : UInt64) : UInt64 :=
  if x = 0 then 0 else if x < m then x else if x < 25 then x + 4 else 11 * x / 10

/-- `x (x - 1)` of a count. -/
@[inline] def ff2 (x : Float) : Float := if x ≤ floatOne then floatZero else x * (x - floatOne)

/-- The partner factor of a dependent: `1` without partner, else the partner's count. -/
@[inline] def partnerW (d : DepW) (arr : FloatArray) : Float :=
  if d.partner = 0 then floatOne else cget arr (d.partner - 1)

/-- Generation 16's `setBounds` on counts, for dependents with codes `0`, `1` or `4 (t + 1)`. -/
def setBoundsW (leaves P : USize) (hP2 : 2 * P.toNat < USize.size) (D : USize)
    (lo hi : FloatArray) (l0 l1 m0 m1 h0 h1 g0 g1 : Float) (ds : Array DepW)
    (i : USize) (lower tree : FloatArray) (pending : USize) : FloatArray × FloatArray :=
  if h : i < ds.usize then
    have hi' := Gen15.lt_size_of_lt_usize ds i h
    let d := ds.uget i hi'
    let pL := partnerW d lo
    let aN := if d.two then l1 else l0
    let lower := if aN == (if d.two then m1 else m0) then lower
      else if pL == floatZero then lower else lower.set! d.k.toNat (d.rate * (aN * pL))
    let pH := partnerW d hi
    let bN := if d.two then h1 else h0
    if bN == (if d.two then g1 else g0) then
      setBoundsW leaves P hP2 D lo hi l0 l1 m0 m1 h0 h1 g0 g1 ds (i + 1) lower tree pending
    else if pH == floatZero then
      setBoundsW leaves P hP2 D lo hi l0 l1 m0 m1 h0 h1 g0 g1 ds (i + 1) lower tree pending
    else
      let leaf := leaves + d.k
      let tree := if pending = 0 then tree
        else Gen16.fixUntilAt P hP2 tree D.toNat D pending.toNat leaf.toNat
      setBoundsW leaves P hP2 D lo hi l0 l1 m0 m1 h0 h1 g0 g1 ds (i + 1) lower
        (tree.set! leaf.toNat (d.rate * (bN * pH))) leaf
  else (lower, if pending = 0 then tree else Gen16.fixPathAt P hP2 tree D.toNat D pending.toNat)
termination_by ds.size - i.toNat
decreasing_by
  all_goals (rw [Gen15.succ_toNat_of_lt_usize ds i h]; omega)

/-- Generation 16's `rebracket` on counts. -/
@[inline] def rebracketW (W : Compiled) (leaves P : USize) (hP2 : 2 * P.toNat < USize.size)
    (D : USize) (pop : FloatArray) (c : CacheW) (s : USize) : CacheW :=
  let x := (cget pop s).toUInt64
  let m := (cget W.ms s).toUInt64
  let loS := cget c.lo s
  let hiS := cget c.hi s
  let loN := (bracketLo m x).toFloat
  let hiN := (bracketHi m x).toFloat
  let lo := cset c.lo s loN
  let hi := cset c.hi s hiN
  let r := setBoundsW leaves P hP2 D lo hi loN (ff2 loN) loS (ff2 loS) hiN (ff2 hiN) hiS (ff2 hiS)
    (Gen17.aget W.deps s) 0 c.lower c.tree 0
  ⟨lo, hi, r.1, r.2⟩

/-- Refresh the brackets of the changed species `chs[i], chs[i+1], …` that left them. -/
def refreshFrom (W : Compiled) (leaves P : USize) (hP2 : 2 * P.toNat < USize.size) (D : USize)
    (chs : Array ChangeW) (pop : FloatArray) (i : USize) (c : CacheW) : CacheW :=
  if h : i < chs.usize then
    have hi' := Gen15.lt_size_of_lt_usize chs i h
    let s := (chs.uget i hi').species
    let c := if staleW (cget W.ms s) (cget pop s) (cget c.lo s) (cget c.hi s) then
      rebracketW W leaves P hP2 D pop c s else c
    refreshFrom W leaves P hP2 D chs pop (i + 1) c
  else c
termination_by chs.size - i.toNat
decreasing_by rw [Gen15.succ_toNat_of_lt_usize chs i h]; omega

/-- The integer factor of a reaction from the counts, as a float. -/
@[inline] def evalW (f : FactorW) (pop : FloatArray) : Float :=
  let x := cget pop f.s
  if f.kind = 0 then x else if f.kind = 1 then ff2 x else x * cget pop f.t

/-! ## The driver -/

/-- The state as generation 17 holds it. -/
@[inline] def toCache (n : Nat) (c : CacheW) : Cache :=
  ⟨ofCounts c.lo n, ofCounts c.hi n, c.lower, c.tree⟩

/-- Generation 17's driver on counts. `n` is the species count; `pop` has one more entry, the
staleness flag of the last firing. -/
def run (C : Gen6.Compiled) (codes : Array (Array Nat)) (W : Compiled) (msN : Array Nat) (n : Nat)
    (hms : msN.size = n) (hval : Gen15.ValidChanges C n) (nW : USize) (numRx : USize) (P : USize)
    (hP2 : 2 * P.toNat < USize.size) (D : USize) (rates : FloatArray) (horizon : Float)
    (save : Bool) (cap : USize) (evFuel prFuel : USize) (pop : FloatArray) (c : CacheW)
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
                let lower := Gen17.fget c.lower j
                let threshold := v * Gen17.fget c.tree k
                if decide (floatZero < lower) && decide (threshold ≤ lower) then true
                else
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
                  let c' := refreshFrom W P P hP2 D chs p 0 c
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
                    let cN := toCache n c
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
      let cN := toCache n c
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

/-- Every entry is below `2^26`. -/
def allSmall (xs : Array Nat) : Bool := xs.all fun x => decide (x < 67108864)

/-- Generation 17's start, entering the count driver when the network's factors have order at
most two (so its dependents' codes are `0`, `1` or `4 (t + 1)`), and the counts, brackets and
changes are below `2^26`. -/
def start (C : Gen6.Compiled) (codes : Array (Array Nat)) (horizon : Float) (save : Bool)
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
          = true then
      let W := compileW C codes
      run C codes W C.gen5.base.ms n rfl (Gen15.validChanges_spec hs.2.2.2.1) n.toUSize
        C.gen5.base.numRx.toUSize C.gen5.base.leaves.toUSize (Gen11.leaves_toUSize h)
        C.gen5.base.depth.toUSize C.gen5.base.rates horizon save cap.toUSize fuel.toUSize cap.toUSize
        ((toCounts pop).push 0) ⟨toCounts c.lo, toCounts c.hi, c.lower, c.tree⟩ now total floatZero
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
    Gen18.start C (Gen13.codesOf C.gen5) horizon saveEvents maxProposals maxEvents initial.pop
      (Gen3.initialCache C.gen5.base initial) start rng 0 #[(start, initial)]

end JumpProcessesLean.TreeRSSA.Gen18
