import JumpProcessesLean.TreeRSSA.Gen26

/-!
# Tree-RSSA, generation 27: a lighter setup

Generation 26's time on fcεRI γ2 includes about 27 ms of setup, 8% of the run: compiling the
network, building the initial brackets, tree and records, and freeing them. Generation 27 runs
generation 26's driver unchanged and builds its inputs with less work:

* the network is compiled with a factor compiler that reads the reactants directly instead of
  as a list (`factorOf`), and each species' dependents take their factors from their reactions'
  factors instead of compiling them again;
* the initial tree's leaves are written straight into a float array (`initialTree`), without
  the boxed intermediate arrays of `Gen1.buildTree`;
* the initial cache leaves out the lower bounds, which generations 19 to 26 never read; the
  fallback to generation 21 computes them.

`Gen27.simulate` is proved equal to `Gen26.simulate` (`Proofs/TreeRSSAGen27.lean`).
-/

namespace JumpProcessesLean.TreeRSSA.Gen27

open Gen1 (Cache)
open Gen18 (compileW toCounts allSmall)
open Gen19 (CacheV rateMax)
open Gen20 (boundsOK boundsOK_spec)
open Gen22 (level_root)
open Gen26 (buildRxV buildRxV_ok)

/-- `Gen3.Factor.compile`, reading the reactants directly instead of as a list. -/
def factorOf (rs : Array (Nat × Nat)) : Gen3.Factor :=
  if h1 : rs.size = 1 then
    let p := rs[0]
    if p.2 = 1 then .one p.1 else if p.2 = 2 then .two p.1 else .general rs
  else if h2 : rs.size = 2 then
    let p := rs[0]
    let q := rs[1]
    if 1 ≤ p.2 ∧ p.2 ≤ 2 ∧ 1 ≤ q.2 ∧ q.2 ≤ 2 then .pair p.1 p.2 q.1 q.2 else .general rs
  else .general rs

/-- `Gen6.compile` through `factorOf`, each dependent's factor read from its reaction's. -/
def compile (net : Network Float) : Gen6.Compiled :=
  let factors := net.reactions.map (factorOf ·.reactants)
  let deps := net.speciesDependents
  ⟨⟨⟨net, net.maxStoich, deps, treeDepth net.reactions.size, 2 ^ treeDepth net.reactions.size,
      net.reactions.size, ⟨net.reactions.map (·.rate)⟩, factors⟩,
    deps.map (·.map fun k => factors.getD k (.general #[])),
    deps.map fun ks => ⟨ks.map fun k => net.reactions[k]!.rate⟩⟩,
   net.reactions.map (·.changes.map Gen6.Change.ofPair)⟩

/-- Write the upper bounds at `hi` of reactions `j - 1, …, 0` to leaves `P + j - 1, …, P`. -/
def setLeaves (rxs : Array (Reaction Float)) (hi : Array Nat) (P : Nat) (t : FloatArray) :
    Nat → FloatArray
  | 0 => t
  | j + 1 => setLeaves rxs hi P (t.set! (P + j) (Gen2.rate rxs[j]! hi)) j

/-- `Gen1.buildTree (C.net.reactions.map (Gen2.rate · hi)) C.depth`, the leaves written straight
into the tree. -/
def initialTree (C : Gen3.Compiled) (hi : Array Nat) : FloatArray :=
  let P := 2 ^ C.depth
  Gen1.fill (setLeaves C.net.reactions hi P ⟨Array.replicate (2 * P) 0⟩ C.net.reactions.size) P

/-- Generation 26's start, entering generation 26's driver under the same conditions. Its fallback,
generation 21's start, gets the lower bounds that generation 27's initial cache leaves out. -/
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
      Gen17.changesOK C = true ∧ Gen17.inBrackets C.gen5.base.ms pop c.lo c.hi = true ∧
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
    Gen27.start C (Gen13.codesOf C.gen5) horizon saveEvents maxProposals maxEvents initial.pop
      ⟨initial.lo, initial.hi, ⟨#[]⟩, initialTree C.gen5.base initial.hi⟩ start rng 0
      #[(start, initial)]

end JumpProcessesLean.TreeRSSA.Gen27
