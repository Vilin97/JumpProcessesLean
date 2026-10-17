import JumpProcessesLean.TreeRSSA.Gen29

/-!
# Tree-RSSA, generation 30: shared change records

Generation 29's setup builds one object per change of every reaction, twice (`Gen6.Change` and
`ChangeW`): 154,568 changes on fcεRI γ2, of only 7,488 distinct values, each species' `+1` and
`-1`. Generation 30 builds those once per species and shares them (`changeOf`, `changeWOf`),
builds its arrays by pushing into new arrays instead of mapping arrays the network keeps (each
such `map` copies the array first), and reads the dependents' rates from the rates array. The
compiled network and records are equal to generation 29's, whose drivers run unchanged.
`Gen30.simulate` is proved equal to `Gen29.simulate` (`Proofs/TreeRSSAGen30.lean`).
-/

namespace JumpProcessesLean.TreeRSSA.Gen30

open Gen1 (Cache)
open Gen18 (ChangeW DepW Compiled toCounts allSmall)
open Gen19 (CacheV rateMax)
open Gen20 (boundsOK boundsOK_spec)
open Gen22 (level_root)
open Gen26 (buildRxV buildRxV_ok)

/-- `rxs.map (·.rate)` as a float array. -/
def ratesOf (rxs : Array (Reaction Float)) : FloatArray :=
  rxs.foldl (fun acc rx => acc.push rx.rate) (FloatArray.emptyWithCapacity rxs.size)

/-- `ks.map rates.get!` as a float array. -/
def pickRates (rates : FloatArray) (ks : Array Nat) : FloatArray :=
  ks.foldl (fun acc k => acc.push (rates.get! k)) (FloatArray.emptyWithCapacity ks.size)

/-- `xs.map f`, pushed into a new array. -/
@[inline] def mapNew {α β : Type} (f : α → β) (xs : Array α) : Array β :=
  xs.foldl (fun acc x => acc.push (f x)) (Array.emptyWithCapacity xs.size)

/-- The changes `+1` and `-1` of every species, built once and shared by all reactions. -/
structure UnitChanges where
  plus : Array Gen6.Change
  minus : Array Gen6.Change

def unitChanges (n : Nat) : UnitChanges :=
  ⟨(Array.range n).map fun s => ⟨s, 1, 0⟩, (Array.range n).map fun s => ⟨s, 0, 1⟩⟩

/-- `Gen6.Change.ofPair`, sharing the changes `+1` and `-1`. -/
@[inline] def changeOf (u : UnitChanges) (c : Nat × Int) : Gen6.Change :=
  if h : c.1 < u.plus.size ∧ c.1 < u.minus.size then
    if c.2 == 1 then u.plus[c.1]'h.1
    else if c.2 == -1 then u.minus[c.1]'h.2
    else Gen6.Change.ofPair c
  else Gen6.Change.ofPair c

/-- The images under `ChangeW.ofChange` of every species' changes `+1` and `-1`. -/
structure UnitChangesW where
  plus : Array ChangeW
  minus : Array ChangeW

def unitChangesW (n : Nat) : UnitChangesW :=
  ⟨(Array.range n).map fun s => ChangeW.ofChange ⟨s, 1, 0⟩,
   (Array.range n).map fun s => ChangeW.ofChange ⟨s, 0, 1⟩⟩

/-- `ChangeW.ofChange`, sharing the images of the changes `+1` and `-1`. -/
@[inline] def changeWOf (u : UnitChangesW) (ch : Gen6.Change) : ChangeW :=
  if h : ch.species < u.plus.size ∧ ch.species < u.minus.size then
    if ch.up == 1 && ch.down == 0 then u.plus[ch.species]'h.1
    else if ch.up == 0 && ch.down == 1 then u.minus[ch.species]'h.2
    else ChangeW.ofChange ch
  else ChangeW.ofChange ch

/-- `Gen27.compile` with float arrays built directly and the changes shared. -/
def compile (net : Network Float) : Gen6.Compiled :=
  let factors := net.reactions.map (Gen27.factorOf ·.reactants)
  let deps := net.speciesDependents
  let rates := ratesOf net.reactions
  let u := unitChanges net.numSpecies
  ⟨⟨⟨net, net.maxStoich, deps, treeDepth net.reactions.size, 2 ^ treeDepth net.reactions.size,
      net.reactions.size, rates, factors⟩,
    deps.map (mapNew fun k => factors.getD k (.general #[])),
    deps.map (pickRates rates)⟩,
   net.reactions.map fun rx => mapNew (changeOf u) rx.changes⟩

/-- `Gen18.compileW` with the changes shared. -/
def compileW (C : Gen6.Compiled) (codes : Array (Array Nat)) : Compiled :=
  let u := unitChangesW C.gen5.base.ms.size
  ⟨C.changes.map (mapNew (changeWOf u)),
   (Array.range C.gen5.base.ms.size).map fun s =>
     let ks := C.gen5.base.deps[s]!
     let cs := codes[s]!
     let rs := C.gen5.depRates[s]!
     (Array.range ks.size).map fun i =>
       ⟨ks[i]!.toUSize, cs[i]! == 1, (cs[i]! / 4).toUSize, rs.get! i⟩,
   C.gen5.base.factors.map Gen18.FactorW.ofFactor,
   toCounts C.gen5.base.ms⟩

/-- Generation 29's start with this module's `compileW`. -/
def start (C : Gen6.Compiled) (codes : Array (Array Nat)) (horizon : Float) (save : Bool)
    (cap fuel : Nat) (pop : Array Nat) (c : Cache) (now : Float) (rng : Xoshiro) (count : Nat)
    (trace : Array (Float × State)) : Except Error (Solution Float State Xoshiro) :=
  let n := C.gen5.base.ms.size
  let total := c.tree.get! 1
  let W := compileW C codes
  let popW := (toCounts pop).push 0
  let cV : CacheV := ⟨toCounts c.lo, toCounts c.hi, c.tree⟩
  if h : (Gen7.finite total = true ∧ decide (floatZero < total) = true ∧
      2 * C.gen5.base.leaves < USize.size) ∧
      ((pop.size = n ∧ c.lo.size = n ∧ c.hi.size = n ∧ Gen15.validChanges C n = true ∧
      Gen28.changesOK C = true ∧ Gen17.inBrackets C.gen5.base.ms pop c.lo c.hi = true ∧
      count + fuel < USize.size ∧ cap < USize.size ∧ C.gen5.base.numRx < USize.size ∧
      n + 1 < USize.size ∧ allSmall pop = true ∧ allSmall c.lo = true ∧ allSmall c.hi = true ∧
      allSmall C.gen5.base.ms = true ∧
      C.gen5.base.factors.all (Gen18.FactorW.ok n) = true ∧
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
        = true) ∧
      boundsOK W n.toUSize C.gen5.base.leaves.toUSize C.gen5.base.numRx.toUSize
        C.gen5.base.rates = true ∧
      popW.size = n.toUSize.toNat + 1 ∧ cV.lo.size = n.toUSize.toNat ∧
      cV.hi.size = n.toUSize.toNat ∧ cV.tree.size = 2 * C.gen5.base.leaves.toUSize.toNat ∧
      W.changes.all (fun chs => chs.size == 1 || chs.size == 2 || chs.size == 3) = true ∧
      C.gen5.base.leaves.toUSize.toNat = 2 ^ C.gen5.base.depth.toUSize.toNat) then
    have hs := h.2
    have hB := boundsOK_spec hs.2.1
    have hnum : C.gen5.base.numRx.toUSize.toNat = C.gen5.base.numRx := by
      rw [Nat.toUSize, USize.toNat_ofNat_of_lt' hs.1.2.2.2.2.2.2.2.2.1]
    if hD : 16 ≤ C.gen5.base.depth.toUSize.toNat then
      Gen29.run C codes W C.gen5.base.ms n rfl (Gen15.validChanges_spec hs.1.2.2.2.1) n.toUSize
        C.gen5.base.numRx.toUSize C.gen5.base.leaves.toUSize (Gen11.leaves_toUSize h.1.2.2)
        C.gen5.base.depth.toUSize (by omega) C.gen5.base.rates hB (level_root hs.2.2.2.2.2.2.2)
        (buildRxV W C.gen5.base.rates C.gen5.base.numRx)
        (by
          rw [hnum]
          exact buildRxV_ok W C.gen5.base.rates C.gen5.base.numRx
            (by have := hB.changes; omega) hs.2.2.2.2.2.2.1)
        horizon save cap.toUSize fuel.toUSize cap.toUSize popW hs.2.2.1 cV
        ⟨hs.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2.1⟩
        now total floatZero rng.s0 rng.s1 rng.s2 rng.s3 count.toUSize trace
    else
      Gen26.run C codes W C.gen5.base.ms n rfl (Gen15.validChanges_spec hs.1.2.2.2.1) n.toUSize
        C.gen5.base.numRx.toUSize C.gen5.base.leaves.toUSize (Gen11.leaves_toUSize h.1.2.2)
        C.gen5.base.depth.toUSize C.gen5.base.rates hB (level_root hs.2.2.2.2.2.2.2)
        (buildRxV W C.gen5.base.rates C.gen5.base.numRx)
        (by
          rw [hnum]
          exact buildRxV_ok W C.gen5.base.rates C.gen5.base.numRx
            (by have := hB.changes; omega) hs.2.2.2.2.2.2.1)
        horizon save cap.toUSize fuel.toUSize cap.toUSize popW hs.2.2.1 cV
        ⟨hs.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2.1⟩
        now total floatZero rng.s0 rng.s1 rng.s2 rng.s3 count.toUSize trace
  else Gen21.start C codes horizon save cap fuel pop
    { c with lower := ⟨C.gen5.base.net.reactions.map (Gen2.rate · c.lo)⟩ } now rng count trace

def simulate (net : Network Float) (initial : State) (start horizon : Float) (rng : Xoshiro)
    (maxEvents : Nat := 1000000) (saveEvents : Bool := false) (maxProposals : Nat := 100000) :
    Except Error (Solution Float State Xoshiro) :=
  if !(Gen7.finite start && Gen7.finite horizon && decide (start ≤ horizon)) then
    .error .invalidTime
  else if !decide (start < horizon) then .ok ⟨initial, horizon, 0, rng, #[(start, initial)]⟩
  else
    let C := compile net
    Gen30.start C (Gen13.codesOf C.gen5) horizon saveEvents maxProposals maxEvents initial.pop
      ⟨initial.lo, initial.hi, ⟨#[]⟩, Gen27.initialTree C.gen5.base initial.hi⟩ start rng 0
      #[(start, initial)]

end JumpProcessesLean.TreeRSSA.Gen30
