import JumpProcessesLean.TreeRSSA.Gen14

/-!
# Tree-RSSA, generation 15: firing on machine words

On the smallest networks a third of the instructions after generation 14 were firing: two folds
over the reaction's compiled changes, one applying the population changes and one testing each
changed species' bracket, every step reading arrays through natural-number indices that are
tested for being small and in range.

Generation 15 carries the facts that make the reads safe: the populations, both bracket arrays
and the maximal stoichiometries have one entry per species, and every compiled change names a
species in range (tested once per network). Firing then loops over the changes with a machine-
word index and reads and writes the arrays without tests. A second loop only reads the brackets;
when no changed species left its bracket, every refresh of generation 13's fold would return the
cache it is given, and the fold is skipped. The populations and caches are generation 14's
(`Proofs/TreeRSSAGen15.lean`).
-/

namespace JumpProcessesLean.TreeRSSA.Gen15

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

theorem lt_size_of_lt_usize {α : Type} (a : Array α) (i : USize) (h : i < a.usize) :
    i.toNat < a.size := by
  have h1 : i.toNat < a.usize.toNat := h
  have h2 : a.usize.toNat ≤ a.size := by
    simp only [Array.usize, Nat.toUSize, USize.toNat_ofNat']
    exact Nat.mod_le _ _
  omega

theorem succ_toNat_of_lt_usize {α : Type} (a : Array α) (i : USize) (h : i < a.usize) :
    (i + 1).toNat = i.toNat + 1 := by
  have h1 : i.toNat < a.usize.toNat := h
  have h2 : a.usize.toNat < 2 ^ System.Platform.numBits := a.usize.toBitVec.isLt
  have h3 : (1 : USize).toNat = 1 := by
    rcases USize.size_eq with h | h <;> simp [USize.toNat_ofNat, h]
  rw [USize.toNat_add, h3]
  exact Nat.mod_eq_of_lt (show i.toNat + 1 < 2 ^ System.Platform.numBits by omega)

/-- Every compiled change of every reaction names a species below `n`. -/
def ValidChanges (C : Gen6.Compiled) (n : Nat) : Prop :=
  ∀ (j k : Nat) (h : k < (C.changes[j]!).size), (C.changes[j]!)[k].species < n

/-- `ValidChanges`, tested, together with every reaction having fewer than `USize.size` changes,
so that a machine-word index runs over all of them. -/
def validChanges (C : Gen6.Compiled) (n : Nat) : Bool :=
  C.changes.all fun chs => decide (chs.size < USize.size) && chs.all fun ch => decide (ch.species < n)

theorem validChanges_spec {C : Gen6.Compiled} {n : Nat} (h : validChanges C n = true) :
    ValidChanges C n := by
  intro j k hk
  unfold validChanges at h
  rw [Array.all_eq_true] at h
  by_cases hj : j < C.changes.size
  · have hjj := (Bool.and_eq_true _ _).mp (h j hj)
    have hjj := hjj.2
    rw [Array.all_eq_true] at hjj
    have hk' : k < (C.changes[j]).size := by rwa [getElem!_pos C.changes j hj] at hk
    have := hjj k hk'
    simp only [decide_eq_true_eq] at this
    simp only [getElem!_pos C.changes j hj]
    exact this
  · simp only [getElem!_neg C.changes j hj] at hk
    exact absurd hk (Nat.not_lt_zero k)

/-- Apply the changes `chs[i], chs[i+1], …` to the populations. -/
def applyFrom (chs : Array Gen6.Change) (n : Nat)
    (hv : ∀ k (h : k < chs.size), chs[k].species < n) (i : USize) (pop : Array Nat)
    (hp : pop.size = n) : {p : Array Nat // p.size = n} :=
  if h : i < chs.usize then
    have hi := lt_size_of_lt_usize chs i h
    let ch := chs.uget i hi
    have hs : ch.species < pop.size := by rw [hp]; exact hv _ hi
    applyFrom chs n hv (i + 1) (pop.set ch.species (pop[ch.species] + ch.up - ch.down) hs)
      (by rw [Array.size_set]; exact hp)
  else ⟨pop, hp⟩
termination_by chs.size - i.toNat
decreasing_by rw [succ_toNat_of_lt_usize chs i h]; have := lt_size_of_lt_usize chs i h; omega

/-- Whether the bracket of the species of one of the changes `chs[i], chs[i+1], …` is stale. -/
def anyStale (chs : Array Gen6.Change) (n : Nat)
    (hv : ∀ k (h : k < chs.size), chs[k].species < n) (ms pop lo hi : Array Nat)
    (hms : ms.size = n) (hp : pop.size = n) (hlo : lo.size = n) (hhi : hi.size = n) (i : USize) :
    Bool :=
  if h : i < chs.usize then
    have hi' := lt_size_of_lt_usize chs i h
    let s := (chs.uget i hi').species
    have hsn : s < n := hv _ hi'
    have h1 : s < ms.size := by rw [hms]; exact hsn
    have h2 : s < pop.size := by rw [hp]; exact hsn
    have h3 : s < lo.size := by rw [hlo]; exact hsn
    have h4 : s < hi.size := by rw [hhi]; exact hsn
    if Gen9.staleI ms[s] pop[s] lo[s] hi[s] then true
    else anyStale chs n hv ms pop lo hi hms hp hlo hhi (i + 1)
  else false
termination_by chs.size - i.toNat
decreasing_by rw [succ_toNat_of_lt_usize chs i h]; omega

theorem refresh_lo_hi_size (C : Gen5.Compiled) (codes : Array (Array Nat)) (P : USize)
    (hP2 : 2 * P.toNat < USize.size) (ms pop : Array Nat) (c : Cache) (s : Nat) :
    (Gen13.refresh C codes P hP2 ms pop c s).lo.size = c.lo.size ∧
      (Gen13.refresh C codes P hP2 ms pop c s).hi.size = c.hi.size := by
  unfold Gen13.refresh
  split
  · simp only [Gen13.rebracket, Array.size_set!, and_self]
  · exact ⟨rfl, rfl⟩

theorem foldRefresh_size (C : Gen5.Compiled) (codes : Array (Array Nat)) (P : USize)
    (hP2 : 2 * P.toNat < USize.size) (ms pop : Array Nat) (chs : Array Gen6.Change) (c : Cache) :
    (chs.foldl (fun c ch => Gen13.refresh C codes P hP2 ms pop c ch.species) c).lo.size =
        c.lo.size ∧
      (chs.foldl (fun c ch => Gen13.refresh C codes P hP2 ms pop c ch.species) c).hi.size =
        c.hi.size := by
  rw [← Array.foldl_toList]
  generalize chs.toList = l
  induction l generalizing c with
  | nil => exact ⟨rfl, rfl⟩
  | cons ch l ih =>
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih (Gen13.refresh C codes P hP2 ms pop c ch.species)
    obtain ⟨h3, h4⟩ := refresh_lo_hi_size C codes P hP2 ms pop c ch.species
    exact ⟨h1.trans h3, h2.trans h4⟩

/-- Generation 14's firing, with the changes applied on machine words and the refresh folded
only when a changed species left its bracket. -/
@[inline] def fire (C : Gen6.Compiled) (codes : Array (Array Nat)) (P : USize)
    (hP2 : 2 * P.toNat < USize.size) (ms : Array Nat) (n : Nat) (hms : ms.size = n)
    (hval : ValidChanges C n) (pop : Array Nat) (hpop : pop.size = n) (c : Cache)
    (hlo : c.lo.size = n) (hhi : c.hi.size = n) (j : Nat) :
    {r : Array Nat × Cache // r.1.size = n ∧ r.2.lo.size = n ∧ r.2.hi.size = n} :=
  let chs := C.changes[j]!
  let r := applyFrom chs n (hval j) 0 pop hpop
  if anyStale chs n (hval j) ms r.val c.lo c.hi hms r.property hlo hhi 0 then
    let c' := chs.foldl (fun c ch => Gen13.refresh C.gen5 codes P hP2 ms r.val c ch.species) c
    have hs := foldRefresh_size C.gen5 codes P hP2 ms r.val chs c
    have h1 : c'.lo.size = n := by rw [← hlo]; exact hs.1
    have h2 : c'.hi.size = n := by rw [← hhi]; exact hs.2
    ⟨(r.val, c'), r.property, h1, h2⟩
  else ⟨(r.val, c), r.property, hlo, hhi⟩

/-- Generation 14's driver with generation 15's firing. The populations, the brackets and the
maximal stoichiometries have `n` entries, and every change's species is below `n`; if the tree's
size test fails the proposal is generation 14's. -/
def run (C : Gen6.Compiled) (codes : Array (Array Nat)) (ms : Array Nat) (n : Nat)
    (hms : ms.size = n) (hval : ValidChanges C n) (depth leaves numRx : Nat) (P : USize)
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
                  let ⟨(pop, c), hpop, hlo, hhi⟩ := Gen15.fire C codes P hP2 ms n hms hval pop hpop c hlo hhi j
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
      Gen14.run C codes ms depth leaves numRx P hP2 rates factors horizon save cap evFuel (pf + 1) pop c
        now total elapsed s0 s1 s2 s3 count trace
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
        c.hi.size = C.gen5.base.ms.size ∧ validChanges C C.gen5.base.ms.size = true then
      run C codes C.gen5.base.ms C.gen5.base.ms.size rfl (validChanges_spec hs.2.2.2)
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
    Gen15.start C (Gen13.codesOf C.gen5) horizon saveEvents maxProposals maxEvents initial.pop
      (Gen3.initialCache C.gen5.base initial) start rng 0 #[(start, initial)]

end JumpProcessesLean.TreeRSSA.Gen15
