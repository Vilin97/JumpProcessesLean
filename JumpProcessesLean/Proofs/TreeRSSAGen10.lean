import JumpProcessesLean.Proofs.TreeRSSAGen9
import JumpProcessesLean.TreeRSSA.Gen10

/-!
# Generation 10 is generation 9, hence the specification

A chain of tests exiting with the same error is the test of their conjunction
(`ite_chain`), and the nested acceptance flag is the conjunction and disjunction it spells
out (`acc_eq`). After these rewrites generation 10's driver is generation 9's.
-/

namespace JumpProcessesLean.Proofs
open JumpProcessesLean.TreeRSSA
open JumpProcessesLean.TreeRSSA.Gen1 (Cache)

lemma ite_chain {β : Type} (a b : Bool) (e k : β) :
    (if (!a) = true then e else if (!b) = true then e else k) =
      (if (!(a && b)) = true then e else k) := by
  cases a <;> cases b <;> rfl

lemma gen7_finite_def (x : Float) :
    Gen7.finite x = (decide (x < Gen7.floatInf) && decide (Gen7.floatNegInf < x)) := rfl

lemma acc_eq (a b c : Bool) :
    (if (!a) = true then false else if b = true then true else c) = (a && (b || c)) := by
  cases a <;> cases b <;> rfl

/-- Generation 10's driver from one proposal on is generation 9's, given the statement for the
next event. -/
theorem run10_eq_of (C : Gen6.Compiled) (horizon : Float) (save : Bool) (cap fuel : Nat)
    (hnext : ∀ f, fuel = f + 1 → ∀ prFuel pop c now total elapsed s0 s1 s2 s3 count trace,
      Gen10.run C C.gen5.base.ms C.gen5.base.depth C.gen5.base.leaves C.gen5.base.numRx
          C.gen5.base.rates C.gen5.base.factors horizon save cap f prFuel pop c now total elapsed s0 s1 s2 s3 count trace =
        Gen9.run C C.gen5.base.ms C.gen5.base.depth C.gen5.base.leaves C.gen5.base.numRx
          C.gen5.base.rates C.gen5.base.factors horizon save cap f prFuel pop c now total elapsed s0 s1 s2 s3 count trace) :
    ∀ prFuel pop c now total elapsed s0 s1 s2 s3 count trace,
      Gen10.run C C.gen5.base.ms C.gen5.base.depth C.gen5.base.leaves C.gen5.base.numRx
          C.gen5.base.rates C.gen5.base.factors horizon save cap fuel prFuel pop c now total elapsed s0 s1 s2 s3 count trace =
        Gen9.run C C.gen5.base.ms C.gen5.base.depth C.gen5.base.leaves C.gen5.base.numRx
          C.gen5.base.rates C.gen5.base.factors horizon save cap fuel prFuel pop c now total elapsed s0 s1 s2 s3 count
          trace := by
  intro prFuel
  induction prFuel with
  | zero =>
    intro pop c now total elapsed s0 s1 s2 s3 count trace
    rw [Gen10.run.eq_1, Gen9.run.eq_1]
  | succ pf ih =>
    intro pop c now total elapsed s0 s1 s2 s3 count trace
    rw [Gen10.run.eq_2, Gen9.run.eq_2]
    simp only [gen7_finite_def, ite_chain, Bool.and_assoc]
    simp only [acc_eq]
    simp only [← Bool.and_assoc, ← gen7_finite_def, finite_eq]
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
      by_cases ht : (!(time.isFinite && decide (now < time) && decide (now ≤ time))) = true
      · simp only [ht, ↓reduceIte]
      simp only [ht, Bool.false_eq_true, ↓reduceIte]
      by_cases hh : (!decide (time ≤ horizon)) = true
      · simp only [hh, ↓reduceIte]
      simp only [hh, Bool.false_eq_true, ↓reduceIte]
      cases fuel with
      | zero => rfl
      | succ f =>
        dsimp only
        rcases Gen9.fire C C.gen5.base.ms pop c j with ⟨pop', c'⟩
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

theorem gen10_run_eq (C : Gen6.Compiled) (horizon : Float) (save : Bool) (cap : Nat) :
    ∀ fuel prFuel pop c now total elapsed s0 s1 s2 s3 count trace,
      Gen10.run C C.gen5.base.ms C.gen5.base.depth C.gen5.base.leaves C.gen5.base.numRx
          C.gen5.base.rates C.gen5.base.factors horizon save cap fuel prFuel pop c now total elapsed s0 s1 s2 s3 count trace =
        Gen9.run C C.gen5.base.ms C.gen5.base.depth C.gen5.base.leaves C.gen5.base.numRx
          C.gen5.base.rates C.gen5.base.factors horizon save cap fuel prFuel pop c now total elapsed s0 s1 s2 s3 count
          trace := by
  intro fuel
  induction fuel with
  | zero => exact run10_eq_of C horizon save cap 0 (fun f h => absurd h (by omega))
  | succ f ih => exact run10_eq_of C horizon save cap (f + 1) (fun f' h => by cases h; exact ih)

/-- Generation 10 returns what generation 9 returns, on every network and input. -/
theorem gen10_eq_gen9 (net : Network Float) (initial : State) (start horizon : Float)
    (rng : Xoshiro) (maxEvents : Nat) (save : Bool) (cap : Nat) :
    Gen10.simulate net initial start horizon rng maxEvents save cap =
      Gen9.simulate net initial start horizon rng maxEvents save cap := by
  unfold Gen10.simulate Gen9.simulate Gen10.start Gen9.start
  simp only [gen10_run_eq]

/-- **Generation 10 is the specification.** For every network whose reactant species are in
range and every input, generation 10 returns exactly what the reference Tree-RSSA returns on
host floats with the xoshiro256++ source. -/
theorem gen10_simulate_eq (net : Network Float) (hwf : ReactantsInRange net) (initial : State)
    (start horizon : Float) (rng : Xoshiro) (maxEvents : Nat) (save : Bool) (cap : Nat) :
    Gen10.simulate net initial start horizon rng maxEvents save cap =
      TreeRSSA.simulate hostArithmetic hostSource net initial start horizon rng maxEvents save
        cap := by
  rw [gen10_eq_gen9, gen9_simulate_eq net hwf]

end JumpProcessesLean.Proofs
