import JumpProcessesLean.Proofs.Race
import JumpProcessesLean.Proofs.Rejection

namespace JumpProcessesLean.Proofs

open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ENNReal

/-- The auditable joint clock-and-reaction specification, in probability rather than
density form: P(T > t, I = i) = (a_i / A) exp(-A t). -/
theorem ctmc_joint_tail {n : Nat} (rates : Fin n → ℝ)
    (hr : ∀ i, 0 ≤ rates i) (hA : 0 < ∑ j, rates j)
    (i : Fin n) (t : ℝ) (ht : 0 ≤ t) :
    densityMeasure (ctmcDensity rates) (Ioi t ×ˢ {i}) =
      ENNReal.ofReal ((rates i / (∑ j, rates j)) * clockSurvival (∑ j, rates j) t) := by
  unfold densityMeasure
  rw [withDensity_apply _ (measurableSet_Ioi.prod (measurableSet_singleton i))]
  rw [setLIntegral_prod _ (measurable_ctmc_density rates).ennreal_ofReal.aemeasurable.restrict]
  simp_rw [lintegral_singleton, Measure.count_singleton, mul_one]
  have hpdf (x : ℝ) : ENNReal.ofReal (ctmcDensity rates i x) =
      ENNReal.ofReal (rates i / (∑ j, rates j)) * exponentialPDF (∑ j, rates j) x := by
    rw [← direct_density_eq rates hA.ne' i x]
    unfold directDensity exponentialPDF
    exact ENNReal.ofReal_mul (div_nonneg (hr i) hA.le)
  simp_rw [hpdf]
  rw [lintegral_const_mul _ (f := exponentialPDF (∑ j, rates j))
    (measurable_exponentialPDFReal _).ennreal_ofReal]
  rw [← withDensity_apply _ measurableSet_Ioi]
  change ENNReal.ofReal (rates i / (∑ j, rates j)) * expMeasure (∑ j, rates j) (Ioi t) = _
  rw [exponential_measure_tail _ t hA ht,
    ← ENNReal.ofReal_mul (div_nonneg (hr i) hA.le)]

/-- All three independently defined ideal laws satisfy the same explicit joint tail. -/
theorem all_ideal_joint_tails {n : Nat} (rates upper : Fin n → ℝ)
    (hr : ∀ i, 0 ≤ rates i) (hu : ∀ i, rates i ≤ upper i)
    (hA : 0 < ∑ j, rates j) (i : Fin n) (t : ℝ) (ht : 0 ≤ t) :
    let target := ENNReal.ofReal ((rates i / (∑ j, rates j)) * clockSurvival (∑ j, rates j) t)
    densityMeasure (directDensity rates) (Ioi t ×ˢ {i}) = target ∧
    densityMeasure (nrmDensity rates) (Ioi t ×ˢ {i}) = target ∧
    densityMeasure (rssaDensity rates upper) (Ioi t ×ˢ {i}) = target := by
  have hB : 0 < ∑ j, upper j := lt_of_lt_of_le hA (Finset.sum_le_sum (fun j _ => hu j))
  have hd : directDensity rates = ctmcDensity rates := funext fun j => funext fun s =>
    direct_density_eq rates hA.ne' j s
  have hn : nrmDensity rates = ctmcDensity rates := funext fun j => funext fun s =>
    nrm_density_eq rates j s
  have hs : rssaDensity rates upper = ctmcDensity rates := funext fun j => funext fun s =>
    rssa_density_eq rates upper hB.ne' j s
  simp only [hd, hn, hs]
  exact ⟨ctmc_joint_tail rates hr hA i t ht, ctmc_joint_tail rates hr hA i t ht,
    ctmc_joint_tail rates hr hA i t ht⟩

end JumpProcessesLean.Proofs
