import JumpProcessesLean.TreeRSSA.Gen27

/-!
# Tree-RSSA, generation 28: a faster start test

Generation 27's start tests that each reaction's changes name distinct species by deciding
`List.Nodup` on a list built from them: about 5 ms of its 21 ms setup on fcεRI γ2. Generation 28
compares the species of up to three changes directly (`distinctSpecies`), and is otherwise
generation 27. `Gen28.simulate` is proved equal to `Gen27.simulate` (`Proofs/TreeRSSAGen28.lean`).
-/

namespace JumpProcessesLean.TreeRSSA.Gen28

open Gen1 (Cache)
open Gen18 (compileW toCounts allSmall)
open Gen19 (CacheV rateMax)
open Gen20 (boundsOK boundsOK_spec)
open Gen22 (level_root)
open Gen26 (buildRxV buildRxV_ok)

/-- Whether the changes name distinct species: `decide (chs.toList.map (·.species)).Nodup`,
with the species of up to three changes compared directly. -/
def distinctSpecies (chs : Array Gen6.Change) : Bool :=
  if chs.size ≤ 1 then true
  else if h2 : chs.size = 2 then chs[0].species != chs[1].species
  else if h3 : chs.size = 3 then
    chs[0].species != chs[1].species && chs[0].species != chs[2].species &&
      chs[1].species != chs[2].species
  else decide (chs.toList.map (·.species)).Nodup

/-- `Gen17.changesOK` through `distinctSpecies`. -/
def changesOK (C : Gen6.Compiled) : Bool :=
  C.changes.all fun chs => chs.all (fun ch => ch.up == 0 || ch.down == 0) && distinctSpecies chs

/-- Generation 27's start with `changesOK` for `Gen17.changesOK`. -/
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
      changesOK C = true ∧ Gen17.inBrackets C.gen5.base.ms pop c.lo c.hi = true ∧
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
    let C := Gen27.compile net
    Gen28.start C (Gen13.codesOf C.gen5) horizon saveEvents maxProposals maxEvents initial.pop
      ⟨initial.lo, initial.hi, ⟨#[]⟩, Gen27.initialTree C.gen5.base initial.hi⟩ start rng 0
      #[(start, initial)]

end JumpProcessesLean.TreeRSSA.Gen28
