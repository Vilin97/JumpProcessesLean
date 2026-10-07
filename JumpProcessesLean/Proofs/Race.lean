import JumpProcessesLean.Proofs.ExponentialTransform
import Mathlib.Probability.Independence.Basic

namespace JumpProcessesLean.Proofs

open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ENNReal

theorem exponential_measure_tail (rate t : ℝ) (hr : 0 < rate) (ht : 0 ≤ t) :
    expMeasure rate (Ioi t) = ENNReal.ofReal (clockSurvival rate t) := by
  have : IsProbabilityMeasure (expMeasure rate) := isProbabilityMeasure_expMeasure hr
  rw [← compl_Iic, measure_compl measurableSet_Iic (measure_ne_top _ _), measure_univ]
  have hc : expMeasure rate (Iic t) = ENNReal.ofReal (1 - exp (-(rate * t))) := by
    change (volume.withDensity (exponentialPDF rate)) (Iic t) = _
    rw [withDensity_apply _ measurableSet_Iic,
      lintegral_exponentialPDF_eq_antiDeriv hr t, ite_eq_left ht]
  rw [hc]
  have he : exp (-(rate * t)) ≤ 1 := exp_le_one_iff.mpr (by nlinarith)
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (sub_nonneg.mpr he)]
  congr 1
  unfold clockSurvival
  ring

/-- Independent exponential clocks actually have the total-rate exponential survival.
The hypotheses specify only primitive laws and independence, not a race-output law. -/
theorem independent_exponential_race_tail {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : Nat}
    (clocks : Fin n → Ω → ℝ) (rates : Fin n → ℝ)
    (hm : ∀ i, Measurable (clocks i)) (hind : iIndepFun clocks μ)
    (hlaw : ∀ i, μ.map (clocks i) = expMeasure (rates i))
    (hr : ∀ i, 0 < rates i) (t : ℝ) (ht : 0 ≤ t) :
    μ {ω | ∀ i, t < clocks i ω} = ENNReal.ofReal (clockSurvival (∑ i, rates i) t) := by
  have hset : {ω | ∀ i, t < clocks i ω} = ⋂ i ∈ Finset.univ, clocks i ⁻¹' Ioi t := by
    ext ω
    simp
  rw [hset, hind.measure_inter_preimage_eq_mul Finset.univ (fun i _ => measurableSet_Ioi)]
  have hterm (i : Fin n) : μ (clocks i ⁻¹' Ioi t) =
      ENNReal.ofReal (clockSurvival (rates i) t) := by
    rw [← Measure.map_apply (hm i) measurableSet_Ioi, hlaw i]
    exact exponential_measure_tail (rates i) t (hr i) ht
  simp_rw [hterm]
  unfold clockSurvival
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (exp_pos _).le)]
  rw [← Real.exp_sum]
  congr 2
  rw [Finset.sum_neg_distrib, ← Finset.sum_mul]

end JumpProcessesLean.Proofs
