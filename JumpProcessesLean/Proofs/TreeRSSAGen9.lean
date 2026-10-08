import JumpProcessesLean.Proofs.TreeRSSAGen8
import JumpProcessesLean.TreeRSSA.Gen9

/-!
# Generation 9 is generation 8, hence the specification

Generation 9's firing is generation 7's with the staleness test inlined and the maximal
stoichiometries passed in, so its driver is generation 8's.
-/

namespace JumpProcessesLean.Proofs
open JumpProcessesLean.TreeRSSA
open JumpProcessesLean.TreeRSSA.Gen1 (Cache)

lemma gen9_fire_eq (C : Gen6.Compiled) (pop : Array Nat) (c : Cache) (j : Nat) :
    Gen9.fire C C.gen5.base.ms pop c j = Gen7.fire C pop c j := rfl

/-- Generation 9's driver from one proposal on is generation 8's, given the statement for the
next event. -/
theorem run9_eq_of (C : Gen6.Compiled) (horizon : Float) (save : Bool) (cap fuel : Nat)
    (hnext : ∀ f, fuel = f + 1 → ∀ prFuel pop c now total elapsed s0 s1 s2 s3 count trace,
      Gen9.run C C.gen5.base.ms C.gen5.base.depth C.gen5.base.leaves C.gen5.base.numRx
          C.gen5.base.rates C.gen5.base.factors horizon save cap f prFuel pop c now total elapsed s0 s1 s2 s3 count trace =
        Gen8.run C C.gen5.base.depth C.gen5.base.leaves C.gen5.base.numRx C.gen5.base.rates
          C.gen5.base.factors horizon save cap f prFuel pop c now total elapsed s0 s1 s2 s3 count trace) :
    ∀ prFuel pop c now total elapsed s0 s1 s2 s3 count trace,
      Gen9.run C C.gen5.base.ms C.gen5.base.depth C.gen5.base.leaves C.gen5.base.numRx
          C.gen5.base.rates C.gen5.base.factors horizon save cap fuel prFuel pop c now total elapsed s0 s1 s2 s3 count trace =
        Gen8.run C C.gen5.base.depth C.gen5.base.leaves C.gen5.base.numRx C.gen5.base.rates
          C.gen5.base.factors horizon save cap fuel prFuel pop c now total elapsed s0 s1 s2 s3 count
          trace := by
  intro prFuel
  induction prFuel with
  | zero =>
    intro pop c now total elapsed s0 s1 s2 s3 count trace
    rw [Gen9.run.eq_1, Gen8.run.eq_1]
  | succ pf ih =>
    intro pop c now total elapsed s0 s1 s2 s3 count trace
    rw [Gen9.run.eq_2, Gen8.run.eq_2]
    simp only [finite_eq]
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
    by_cases hacc : (decide (j < C.gen5.base.numRx) &&
        ((decide (floatZero < c.lower.get! j) &&
            decide (v * c.tree.get! (C.gen5.base.leaves + j) ≤ c.lower.get! j)) ||
          (decide (floatZero < C.gen5.base.rates.get! j *
              natToFloat (C.gen5.base.factors[j]!.eval pop)) &&
            decide (v * c.tree.get! (C.gen5.base.leaves + j) ≤ C.gen5.base.rates.get! j *
              natToFloat (C.gen5.base.factors[j]!.eval pop))))) =
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
        rw [gen9_fire_eq]
        rcases Gen7.fire C pop c j with ⟨pop', c'⟩
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

theorem gen9_run_eq (C : Gen6.Compiled) (horizon : Float) (save : Bool) (cap : Nat) :
    ∀ fuel prFuel pop c now total elapsed s0 s1 s2 s3 count trace,
      Gen9.run C C.gen5.base.ms C.gen5.base.depth C.gen5.base.leaves C.gen5.base.numRx
          C.gen5.base.rates C.gen5.base.factors horizon save cap fuel prFuel pop c now total elapsed s0 s1 s2 s3 count trace =
        Gen8.run C C.gen5.base.depth C.gen5.base.leaves C.gen5.base.numRx C.gen5.base.rates
          C.gen5.base.factors horizon save cap fuel prFuel pop c now total elapsed s0 s1 s2 s3 count
          trace := by
  intro fuel
  induction fuel with
  | zero => exact run9_eq_of C horizon save cap 0 (fun f h => absurd h (by omega))
  | succ f ih => exact run9_eq_of C horizon save cap (f + 1) (fun f' h => by cases h; exact ih)

/-- Generation 9 returns what generation 8 returns, on every network and input. -/
theorem gen9_eq_gen8 (net : Network Float) (initial : State) (start horizon : Float)
    (rng : Xoshiro) (maxEvents : Nat) (save : Bool) (cap : Nat) :
    Gen9.simulate net initial start horizon rng maxEvents save cap =
      Gen8.simulate net initial start horizon rng maxEvents save cap := by
  unfold Gen9.simulate Gen8.simulate Gen9.start Gen8.start
  simp only [gen9_run_eq]

/-- **Generation 9 is the specification.** For every network whose reactant species are in
range and every input, generation 9 returns exactly what the reference Tree-RSSA returns on
host floats with the xoshiro256++ source. -/
theorem gen9_simulate_eq (net : Network Float) (hwf : ReactantsInRange net) (initial : State)
    (start horizon : Float) (rng : Xoshiro) (maxEvents : Nat) (save : Bool) (cap : Nat) :
    Gen9.simulate net initial start horizon rng maxEvents save cap =
      TreeRSSA.simulate hostArithmetic hostSource net initial start horizon rng maxEvents save
        cap := by
  rw [gen9_eq_gen8, gen8_simulate_eq net hwf]

end JumpProcessesLean.Proofs
