import JumpProcessesLean.Proofs.Distributions
import Mathlib.Analysis.SpecificLimits.Basic

namespace JumpProcessesLean.Proofs

open Real ProbabilityTheory MeasureTheory Filter
open scoped BigOperators ENNReal Topology

/-- Categorical proposal mass multiplied by conditional acceptance probability. -/
noncomputable def acceptedProposalWeight {n : Nat} (rates upper : Fin n → ℝ) (i : Fin n) : ℝ :=
  if upper i = 0 then 0 else (upper i / (∑ j, upper j)) * (rates i / upper i)

theorem accepted_proposal_weight {n : Nat} (rates upper : Fin n → ℝ)
    (hr : ∀ i, 0 ≤ rates i) (hu : ∀ i, rates i ≤ upper i)
    (i : Fin n) : acceptedProposalWeight rates upper i = rates i / (∑ j, upper j) := by
  unfold acceptedProposalWeight
  by_cases hi : upper i = 0
  · have ha : rates i = 0 := le_antisymm (by simpa [hi] using hu i) (hr i)
    simp [hi, ha]
  · rw [ite_eq_right hi]
    field_simp

theorem erlang_density_eq_gamma (upper t : ℝ) (k : Nat) :
    erlangDensity upper k t = gammaPDFReal ((k : ℝ) + 1) upper t := by
  unfold erlangDensity gammaPDFReal
  rw [Real.Gamma_nat_eq_factorial]
  simp only [add_sub_cancel_right]
  rw [show (k : ℝ) + 1 = ((k + 1 : Nat) : ℝ) by norm_cast,
    Real.rpow_natCast, Real.rpow_natCast]
  split_ifs
  · ring
  · rfl

theorem erlang_integrates_one (upper : ℝ) (hu : 0 < upper) (k : Nat) :
    (∫⁻ t : ℝ, ENNReal.ofReal (erlangDensity upper k t)) = 1 := by
  simp_rw [erlang_density_eq_gamma]
  change (∫⁻ t : ℝ, gammaPDF ((k : ℝ) + 1) upper t) = 1
  exact lintegral_gammaPDF_eq_one (by positivity) hu

/-- The accepted mark distribution remains proportional to the actual rates. -/
theorem accepted_mark_proportions {n : Nat} (rates upper : Fin n → ℝ)
    (hr : ∀ i, 0 ≤ rates i) (hu : ∀ i, rates i ≤ upper i)
    (hA : (∑ j, rates j) ≠ 0) (hB : (∑ j, upper j) ≠ 0) (i : Fin n) :
    acceptedProposalWeight rates upper i / ((∑ j, rates j) / (∑ j, upper j)) =
      rates i / (∑ j, rates j) := by
  rw [accepted_proposal_weight rates upper hr hu]
  field_simp

/-- A cap of m proposals leaves geometric failure mass q^m. This identity is stated
separately from the unbounded ideal density theorem. -/
theorem geometric_success_mass (q : ℝ) (fuel : Nat) :
    (∑ k ∈ Finset.range fuel, q ^ k * (1 - q)) = 1 - q ^ fuel := by
  rw [← Finset.sum_mul]
  have h := geom_sum_mul q fuel
  nlinarith

theorem rejection_probability_bounds {n : Nat} (rates upper : Fin n → ℝ)
    (_hr : ∀ i, 0 ≤ rates i) (hu : ∀ i, rates i ≤ upper i)
    (hA : 0 < ∑ j, rates j) :
    0 ≤ 1 - (∑ j, rates j) / (∑ j, upper j) ∧
      1 - (∑ j, rates j) / (∑ j, upper j) < 1 := by
  have hAB : (∑ i, rates i) ≤ ∑ i, upper i := Finset.sum_le_sum (fun i _ => hu i)
  have hB : 0 < ∑ j, upper j := lt_of_lt_of_le hA hAB
  constructor
  · exact sub_nonneg.mpr ((div_le_one hB).mpr hAB)
  · have hp := div_pos hA hB
    linarith

/-- The geometric no-acceptance probability tends to zero for a valid live state. -/
theorem rejection_failure_tends_zero {n : Nat} (rates upper : Fin n → ℝ)
    (hr : ∀ i, 0 ≤ rates i) (hu : ∀ i, rates i ≤ upper i)
    (hA : 0 < ∑ j, rates j) :
    Tendsto (fun fuel : Nat => (1 - (∑ j, rates j) / (∑ j, upper j)) ^ fuel)
      atTop (nhds 0) := by
  obtain ⟨hq0, hq1⟩ := rejection_probability_bounds rates upper hr hu hA
  exact tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1

end JumpProcessesLean.Proofs
