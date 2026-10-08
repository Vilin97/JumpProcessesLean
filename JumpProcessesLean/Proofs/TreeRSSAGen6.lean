import JumpProcessesLean.Proofs.TreeRSSAGen5
import JumpProcessesLean.TreeRSSA.Gen6

/-!
# Generation 6 is generation 5, hence the specification

A compiled change adds its increase and subtracts its decrease with natural-number
arithmetic, which is the integer update truncated at zero. The written-out acceptance test
is `Gen2.accept` unfolded. So generation 6's firing is generation 5's and its driver runs as
generation 5's on every network.
-/

namespace JumpProcessesLean.Proofs
open JumpProcessesLean.TreeRSSA
open JumpProcessesLean.TreeRSSA.Gen1 (Cache)

lemma change_apply (pop : Array Nat) (c : Nat × Int) :
    (Gen6.Change.ofPair c).apply pop = applyChange pop c := by
  unfold Gen6.Change.apply Gen6.Change.ofPair applyChange
  dsimp only
  congr 1
  omega

lemma ofPair_species (c : Nat × Int) : (Gen6.Change.ofPair c).species = c.1 := rfl

theorem gen6_fire_eq (C : Gen6.Compiled) (net : Network Float)
    (hC : C = Gen6.compile net) (pop : Array Nat) (c : Cache) (j : Nat) :
    Gen6.fire C pop c j = Gen5.fire C.gen5 pop c j := by
  subst hC
  have hchs : (Gen6.compile net).changes[j]! = (changesOf net j).map Gen6.Change.ofPair := by
    unfold changesOf
    show (net.reactions.map (·.changes.map Gen6.Change.ofPair))[j]! = _
    by_cases hj : j < net.reactions.size
    · rw [arr_getElem!_pos _ _ (by simpa using hj), Array.getElem_map]
      simp [hj]
    · rw [arr_getElem!_neg _ _ (by simpa using hj)]
      simp [hj]
      rfl
  have hnet : (Gen6.compile net).gen5.base.net = net := rfl
  unfold Gen6.fire Gen5.fire
  dsimp only
  rw [hchs, hnet]
  simp only [Array.foldl_map, change_apply, ofPair_species]

/-- Generation 6's driver from one proposal on is generation 5's, given the statement for the
next event. -/
theorem run6_eq_of (C : Gen6.Compiled)
    (hfire : ∀ pop c j, Gen6.fire C pop c j = Gen5.fire C.gen5 pop c j)
    (horizon : Float) (save : Bool) (cap fuel : Nat)
    (hnext : ∀ f, fuel = f + 1 → ∀ prFuel pop c now total elapsed s0 s1 s2 s3 count trace,
      Gen6.run C horizon save cap f prFuel pop c now total elapsed s0 s1 s2 s3 count trace =
        Gen5.run C.gen5 horizon save cap f prFuel pop c now total elapsed s0 s1 s2 s3 count
          trace) :
    ∀ prFuel pop c now total elapsed s0 s1 s2 s3 count trace,
      Gen6.run C horizon save cap fuel prFuel pop c now total elapsed s0 s1 s2 s3 count trace =
        Gen5.run C.gen5 horizon save cap fuel prFuel pop c now total elapsed s0 s1 s2 s3 count
          trace := by
  intro prFuel
  induction prFuel with
  | zero =>
    intro pop c now total elapsed s0 s1 s2 s3 count trace
    rw [Gen6.run.eq_1, Gen5.run.eq_1]
  | succ pf ih =>
    intro pop c now total elapsed s0 s1 s2 s3 count trace
    rw [Gen6.run.eq_2, Gen5.run.eq_2]
    rcases h1 : Xoshiro.uniform ⟨s0, s1, s2, s3⟩ with ⟨u, r1⟩
    dsimp only
    by_cases hu : (!(u.isFinite && decide (floatZero ≤ u) && decide (u < floatOne))) = true
    · simp only [hu, ↓reduceIte]
    simp only [hu, Bool.false_eq_true, ↓reduceIte]
    rcases h2 : r1.exponential with ⟨e, r2⟩
    dsimp only
    by_cases he : (!(e.isFinite && decide (floatZero < e))) = true
    · simp only [he, ↓reduceIte]
    simp only [he, Bool.false_eq_true, ↓reduceIte]
    by_cases hel : (!(elapsed + e).isFinite) = true
    · simp only [hel, ↓reduceIte]
    simp only [hel, Bool.false_eq_true, ↓reduceIte]
    rcases h3 : r2.uniform with ⟨v, r3⟩
    dsimp only
    by_cases hv : (!(v.isFinite && decide (floatZero ≤ v) && decide (v < floatOne))) = true
    · simp only [hv, ↓reduceIte]
    simp only [hv, Bool.false_eq_true, ↓reduceIte]
    generalize Gen1.descend c.tree C.gen5.base.depth 1 (u * total) - C.gen5.base.leaves = j
    unfold Gen2.accept
    by_cases hacc : (decide (j < C.gen5.base.numRx) &&
        ((decide (floatZero < c.lower.get! j) &&
            decide (v * c.tree.get! (C.gen5.base.leaves + j) ≤ c.lower.get! j)) ||
          (decide (floatZero < Gen3.rate C.gen5.base j pop) &&
            decide (v * c.tree.get! (C.gen5.base.leaves + j) ≤ Gen3.rate C.gen5.base j pop)))) =
        true
    · simp only [hacc, ↓reduceIte]
      generalize now + (elapsed + e) / total = time
      by_cases ht : (!(time.isFinite && decide (now < time))) = true
      · simp only [ht, ↓reduceIte]
      simp only [ht, Bool.false_eq_true, ↓reduceIte]
      by_cases hle : (!decide (now ≤ time)) = true
      · simp only [hle, ↓reduceIte]
      simp only [hle, Bool.false_eq_true, ↓reduceIte]
      by_cases hh : (!decide (time ≤ horizon)) = true
      · simp only [hh, ↓reduceIte]
      simp only [hh, Bool.false_eq_true, ↓reduceIte]
      cases fuel with
      | zero => rfl
      | succ f =>
        dsimp only
        rw [hfire pop c j]
        rcases Gen5.fire C.gen5 pop c j with ⟨pop', c'⟩
        dsimp only
        by_cases hfin' : (!(c'.tree.get! 1).isFinite) = true
        · simp only [hfin', ↓reduceIte]
        simp only [hfin', Bool.false_eq_true, ↓reduceIte]
        by_cases hpos : (!decide (floatZero < c'.tree.get! 1)) = true
        · simp only [hpos, ↓reduceIte]
        simp only [hpos, Bool.false_eq_true, ↓reduceIte]
        rw [hnext f rfl]
    · simp only [hacc, Bool.false_eq_true, ↓reduceIte]
      rw [ih]

theorem gen6_run_eq (C : Gen6.Compiled)
    (hfire : ∀ pop c j, Gen6.fire C pop c j = Gen5.fire C.gen5 pop c j)
    (horizon : Float) (save : Bool) (cap : Nat) :
    ∀ fuel prFuel pop c now total elapsed s0 s1 s2 s3 count trace,
      Gen6.run C horizon save cap fuel prFuel pop c now total elapsed s0 s1 s2 s3 count trace =
        Gen5.run C.gen5 horizon save cap fuel prFuel pop c now total elapsed s0 s1 s2 s3 count
          trace := by
  intro fuel
  induction fuel with
  | zero => exact run6_eq_of C hfire horizon save cap 0 (fun f h => absurd h (by omega))
  | succ f ih => exact run6_eq_of C hfire horizon save cap (f + 1) (fun f' h => by cases h; exact ih)

/-- Generation 6 returns what generation 5 returns, on every network and input. -/
theorem gen6_eq_gen5 (net : Network Float) (initial : State) (start horizon : Float)
    (rng : Xoshiro) (maxEvents : Nat) (save : Bool) (cap : Nat) :
    Gen6.simulate net initial start horizon rng maxEvents save cap =
      Gen5.simulate net initial start horizon rng maxEvents save cap := by
  have hfire : ∀ pop c j, Gen6.fire (Gen6.compile net) pop c j =
      Gen5.fire (Gen6.compile net).gen5 pop c j := fun pop c j => gen6_fire_eq _ net rfl pop c j
  have hgen5 : (Gen6.compile net).gen5 = Gen5.compile net := rfl
  unfold Gen6.simulate Gen5.simulate Gen6.start Gen5.start
  simp only [gen6_run_eq _ hfire, hgen5]

/-- **Generation 6 is the specification.** For every network whose reactant species are in
range and every input, generation 6 returns exactly what the reference Tree-RSSA returns on
host floats with the xoshiro256++ source. -/
theorem gen6_simulate_eq (net : Network Float) (hwf : ReactantsInRange net) (initial : State)
    (start horizon : Float) (rng : Xoshiro) (maxEvents : Nat) (save : Bool) (cap : Nat) :
    Gen6.simulate net initial start horizon rng maxEvents save cap =
      TreeRSSA.simulate hostArithmetic hostSource net initial start horizon rng maxEvents save
        cap := by
  rw [gen6_eq_gen5, gen5_simulate_eq net hwf]

end JumpProcessesLean.Proofs
