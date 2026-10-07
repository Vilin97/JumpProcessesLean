import JumpProcessesLean.Proofs.Distributions
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace JumpProcessesLean.Proofs

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

/-- Continuous ideal input law. Its endpoints have zero probability. -/
noncomputable def unitUniform : Measure ℝ := volume.restrict (Ioo 0 1)

instance unitUniform_isProbability : IsProbabilityMeasure unitUniform := by
  constructor
  simp [unitUniform, Real.volume_Ioo]

theorem measurable_exponentialClock (rate : ℝ) : Measurable (exponentialClock rate) := by
  unfold exponentialClock
  fun_prop

/-- The actual inverse-transform expression has the standard exponential measure.
This proves a primitive law, rather than assuming the output is already exponential. -/
theorem exponentialClock_map_uniform (rate : ℝ) (hr : 0 < rate) :
    unitUniform.map (exponentialClock rate) = expMeasure rate := by
  have hm := measurable_exponentialClock rate
  apply Measure.ext_of_Iic
  intro t
  rw [Measure.map_apply hm measurableSet_Iic, unitUniform,
    Measure.restrict_apply (measurableSet_Iic.preimage hm)]
  have hset : (exponentialClock rate ⁻¹' Iic t) ∩ Ioo 0 1 =
      Ico (exp (-(rate * t))) 1 := by
    ext u
    constructor
    · rintro ⟨ht, hu⟩
      have hh := not_congr (exponentialClock_tail_iff rate u t hr hu.1)
      simp only [not_lt] at hh
      exact ⟨hh.mp ht, hu.2⟩
    · rintro ⟨hu, hu1⟩
      have hu0 : 0 < u := lt_of_lt_of_le (exp_pos _) hu
      have hh := not_congr (exponentialClock_tail_iff rate u t hr hu0)
      simp only [not_lt] at hh
      exact ⟨hh.mpr hu, hu0, hu1⟩
  rw [hset, Real.volume_Ico]
  change ENNReal.ofReal (1 - exp (-(rate * t))) =
    (volume.withDensity (exponentialPDF rate)) (Iic t)
  rw [withDensity_apply _ measurableSet_Iic, lintegral_exponentialPDF_eq_antiDeriv hr]
  by_cases ht : 0 ≤ t
  · simp [ht]
  · simp only [ite_eq_right ht, ENNReal.ofReal_zero]
    apply ENNReal.ofReal_eq_zero.mpr
    have he : 1 ≤ exp (-(rate * t)) := Real.one_le_exp_iff.mpr (by nlinarith)
    linarith

end JumpProcessesLean.Proofs
