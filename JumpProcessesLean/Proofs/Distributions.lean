import JumpProcessesLean.Proofs.Clock
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

namespace JumpProcessesLean.Proofs

open Real MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

variable {n : Nat}

/-- Auditable specification: reaction i has rate a_i; time is exponential with total rate.
The zero-total case is handled by the executable absorbing-state branch. -/
noncomputable def ctmcDensity (rates : Fin n → ℝ) (i : Fin n) (t : ℝ) : ℝ :=
  if 0 ≤ t then rates i * exp (-((∑ j, rates j) * t)) else 0

/-- Direct's independent categorical mark and total-rate exponential. -/
noncomputable def directDensity (rates : Fin n → ℝ) (i : Fin n) (t : ℝ) : ℝ :=
  rates i / (∑ j, rates j) * exponentialPDFReal (∑ j, rates j) t

/-- Exponential race: channel i fires at t and all other clocks exceed t. -/
noncomputable def nrmDensity (rates : Fin n → ℝ) (i : Fin n) (t : ℝ) : ℝ :=
  if 0 ≤ t then
    (rates i * exp (-(rates i * t))) *
      ∏ j ∈ Finset.univ.erase i, clockSurvival (rates j) t
  else 0

/-- Erlang density for k+1 independent upper-rate proposal clocks. -/
noncomputable def erlangDensity (upper : ℝ) (k : Nat) (t : ℝ) : ℝ :=
  if 0 ≤ t then
    upper ^ (k + 1) * t ^ k / (k.factorial : ℝ) * exp (-(upper * t))
  else 0

/-- Operational proposal law: k rejected proposals, then an accepted proposal of type i. -/
noncomputable def rssaTerm (rates upper : Fin n → ℝ) (i : Fin n) (t : ℝ)
    (k : Nat) : ℝ :=
  let a := ∑ j, rates j
  let b := ∑ j, upper j
  ((b - a) / b) ^ k * (rates i / b) * erlangDensity b k t

noncomputable def rssaDensity (rates upper : Fin n → ℝ) (i : Fin n) (t : ℝ) : ℝ :=
  ∑' k : Nat, rssaTerm rates upper i t k

theorem direct_density_eq (rates : Fin n → ℝ) (hA : (∑ j, rates j) ≠ 0)
    (i : Fin n) (t : ℝ) : directDensity rates i t = ctmcDensity rates i t := by
  unfold directDensity ctmcDensity exponentialPDFReal gammaPDFReal
  simp only [rpow_one, Gamma_one, div_one, sub_self, rpow_zero, mul_one]
  split_ifs
  · field_simp
  · simp

theorem nrm_density_eq (rates : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    nrmDensity rates i t = ctmcDensity rates i t := by
  unfold nrmDensity ctmcDensity clockSurvival
  split_ifs with ht
  · rw [← Real.exp_sum, mul_assoc, ← Real.exp_add]
    congr 2
    rw [Finset.sum_neg_distrib, ← Finset.sum_mul]
    have hsum := Finset.add_sum_erase Finset.univ rates (Finset.mem_univ i)
    rw [← hsum]
    ring
  · rfl

theorem rssa_term_eq (rates upper : Fin n → ℝ) (hB : (∑ j, upper j) ≠ 0)
    (i : Fin n) (t : ℝ) (ht : 0 ≤ t) (k : Nat) :
    rssaTerm rates upper i t k =
      (rates i * exp (-((∑ j, upper j) * t))) *
        (((∑ j, upper j) - (∑ j, rates j)) * t) ^ k / (k.factorial : ℝ) := by
  unfold rssaTerm erlangDensity
  dsimp only
  rw [ite_eq_left ht, div_pow, pow_succ, mul_pow]
  field_simp

theorem rssa_density_eq (rates upper : Fin n → ℝ) (hB : (∑ j, upper j) ≠ 0)
    (i : Fin n) (t : ℝ) : rssaDensity rates upper i t = ctmcDensity rates i t := by
  unfold rssaDensity ctmcDensity
  split_ifs with ht
  · simp_rw [rssa_term_eq rates upper hB i t ht]
    simp_rw [mul_div_assoc]
    rw [tsum_mul_left]
    have hexp :
        (∑' k : Nat, ((((∑ j, upper j) - (∑ j, rates j)) * t) ^ k /
          (k.factorial : ℝ))) = exp (((∑ j, upper j) - (∑ j, rates j)) * t) := by
      simpa only [← Real.exp_eq_exp_ℝ] using
        (NormedSpace.expSeries_div_hasSum_exp (((∑ j, upper j) - (∑ j, rates j)) * t)).tsum_eq
    rw [hexp, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  · simp [rssaTerm, erlangDensity, ht]

/-- This theorem uses distinct Direct, race, and rejection-series definitions. -/
theorem all_ideal_densities_equal (rates upper : Fin n → ℝ)
    (hA : (∑ j, rates j) ≠ 0) (hB : (∑ j, upper j) ≠ 0) :
    directDensity rates = nrmDensity rates ∧
      nrmDensity rates = rssaDensity rates upper := by
  constructor
  · funext i t
    rw [direct_density_eq rates hA, nrm_density_eq]
  · funext i t
    rw [nrm_density_eq, rssa_density_eq rates upper hB]

/-- A genuine measure on elapsed time and reaction index, not just a density equation. -/
noncomputable def densityMeasure (density : Fin n → ℝ → ℝ) : Measure (ℝ × Fin n) :=
  (volume.prod (Measure.count : Measure (Fin n))).withDensity
    (fun p => ENNReal.ofReal (density p.2 p.1))

theorem all_ideal_measures_equal (rates upper : Fin n → ℝ)
    (hA : (∑ j, rates j) ≠ 0) (hB : (∑ j, upper j) ≠ 0) :
    densityMeasure (directDensity rates) = densityMeasure (nrmDensity rates) ∧
      densityMeasure (nrmDensity rates) = densityMeasure (rssaDensity rates upper) := by
  obtain ⟨h₁, h₂⟩ := all_ideal_densities_equal rates upper hA hB
  exact ⟨congrArg densityMeasure h₁, congrArg densityMeasure h₂⟩

theorem ctmc_density_nonneg (rates : Fin n → ℝ) (hr : ∀ i, 0 ≤ rates i)
    (i : Fin n) (t : ℝ) : 0 ≤ ctmcDensity rates i t := by
  unfold ctmcDensity
  split_ifs
  · exact mul_nonneg (hr i) (Real.exp_pos _).le
  · exact le_refl 0

theorem sum_ctmc_density (rates : Fin n → ℝ) (t : ℝ) :
    (∑ i, ctmcDensity rates i t) = exponentialPDFReal (∑ i, rates i) t := by
  unfold ctmcDensity exponentialPDFReal gammaPDFReal
  simp only [rpow_one, Gamma_one, div_one, sub_self, rpow_zero, mul_one]
  split_ifs with ht
  · simp only [← Finset.sum_mul]
  · simp only [Finset.sum_const_zero]

theorem measurable_ctmc_density (rates : Fin n → ℝ) :
    Measurable (fun p : ℝ × Fin n => ctmcDensity rates p.2 p.1) := by
  unfold ctmcDensity
  apply Measurable.ite (measurableSet_le measurable_const measurable_fst)
  · have hm : Measurable rates := measurable_of_countable _
    exact (hm.comp measurable_snd).mul
      ((measurable_const.mul measurable_fst).neg.exp)
  · exact measurable_const

theorem ctmc_measure_mass_one (rates : Fin n → ℝ) (hr : ∀ i, 0 ≤ rates i)
    (hA : 0 < ∑ i, rates i) : densityMeasure (ctmcDensity rates) Set.univ = 1 := by
  unfold densityMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [lintegral_prod _ (measurable_ctmc_density rates).ennreal_ofReal.aemeasurable]
  simp_rw [lintegral_count, tsum_fintype]
  have hinner (t : ℝ) :
      (∑ i, ENNReal.ofReal (ctmcDensity rates i t)) = exponentialPDF (∑ i, rates i) t := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => ctmc_density_nonneg rates hr i t),
      sum_ctmc_density, exponentialPDF]
  simp_rw [hinner]
  exact lintegral_exponentialPDF_eq_one hA

theorem ctmc_is_probability (rates : Fin n → ℝ) (hr : ∀ i, 0 ≤ rates i)
    (hA : 0 < ∑ i, rates i) : IsProbabilityMeasure (densityMeasure (ctmcDensity rates)) :=
  ⟨ctmc_measure_mass_one rates hr hA⟩

/-- Equality of normalized joint probability measures, with valid propensity envelopes. -/
theorem ideal_solvers_same_probability_law (rates upper : Fin n → ℝ)
    (hr : ∀ i, 0 ≤ rates i) (hu : ∀ i, rates i ≤ upper i)
    (hA : 0 < ∑ i, rates i) :
    IsProbabilityMeasure (densityMeasure (directDensity rates)) ∧
    densityMeasure (directDensity rates) = densityMeasure (nrmDensity rates) ∧
    densityMeasure (nrmDensity rates) = densityMeasure (rssaDensity rates upper) := by
  have hB : 0 < ∑ i, upper i :=
    lt_of_lt_of_le hA (Finset.sum_le_sum (fun i _ => hu i))
  have hd : directDensity rates = ctmcDensity rates := by
    funext i t
    exact direct_density_eq rates hA.ne' i t
  refine ⟨?_, all_ideal_measures_equal rates upper hA.ne' hB.ne'⟩
  rw [hd]
  exact ctmc_is_probability rates hr hA

end JumpProcessesLean.Proofs
