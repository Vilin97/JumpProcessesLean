import JumpProcessesLean.Proofs.Rejection
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace JumpProcessesLean.Proofs
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

noncomputable def erlangPDF (B : ℝ) (k : Nat) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (erlangDensity B k t)
noncomputable def erlangMeasure (B : ℝ) (k : Nat) : Measure ℝ := volume.withDensity (erlangPDF B k)

lemma measurable_erlangPDF (B : ℝ) (k : Nat) : Measurable (erlangPDF B k) := by
  unfold erlangPDF
  simp_rw [erlang_density_eq_gamma]
  exact (measurable_gammaPDFReal _ _).ennreal_ofReal

/-- One more independent exponential contributes one more Erlang stage. -/
theorem exponential_erlang_convolution (B : ℝ) (hB : 0 < B) (k : Nat) :
    (expMeasure B).conv (erlangMeasure B k) = erlangMeasure B (k + 1) := by
  change (volume.withDensity (exponentialPDF B)).conv (volume.withDensity (erlangPDF B k)) = _
  rw [conv_withDensity_eq_lconvolution (by exact (measurable_exponentialPDFReal B).ennreal_ofReal)
    (measurable_erlangPDF B k)]
  apply congrArg (volume.withDensity)
  funext t
  rw [lconvolution_def]
  by_cases ht : 0 ≤ t
  · let C : ℝ := B ^ (k + 2) / (k.factorial : ℝ) * exp (-(B * t))
    have hC : 0 ≤ C := by dsimp [C]; positivity
    have he (x : ℝ) : exponentialPDF B x * erlangPDF B k (-x + t) =
        (Icc 0 t).indicator (fun x => ENNReal.ofReal (C * (t - x) ^ k)) x := by
      by_cases hx : x ∈ Icc 0 t
      · have htx : 0 ≤ -x + t := by linarith [hx.2]
        rw [Set.indicator_of_mem hx, exponentialPDF_of_nonneg hx.1,
          erlangPDF, erlangDensity, ite_eq_left htx,
          ← ENNReal.ofReal_mul (mul_nonneg hB.le (exp_pos _).le)]
        congr 1
        have hexp : exp (-(B * x)) * exp (-(B * (-x + t))) = exp (-(B * t)) := by
          rw [← exp_add]; congr 1; ring
        calc
          _ = (B * B ^ (k + 1) / (k.factorial : ℝ)) * (-x + t) ^ k *
            (exp (-(B * x)) * exp (-(B * (-x + t)))) := by ring
          _ = _ := by rw [hexp]; dsimp [C]; rw [pow_succ]; ring
      · rw [Set.indicator_of_notMem hx]
        have hcase : x < 0 ∨ t < x := by
          by_cases h : x < 0
          · exact Or.inl h
          · exact Or.inr (lt_of_not_ge (fun ht => hx ⟨le_of_not_gt h, ht⟩))
        rcases hcase with h | h
        · simp [exponentialPDF_of_neg h]
        · have hneg : ¬0 ≤ -x + t := by linarith
          simp [erlangPDF, erlangDensity, hneg]
    rw [lintegral_congr he, lintegral_indicator measurableSet_Icc]
    have hc : Continuous (fun x : ℝ => C * (t - x) ^ k) := by fun_prop
    have hnn : ∀ᵐ x : ℝ ∂volume.restrict (Icc 0 t), 0 ≤ C * (t - x) ^ k := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      exact mul_nonneg hC (pow_nonneg (by linarith [hx.2]) _)
    rw [← ofReal_integral_eq_lintegral_ofReal hc.integrableOn_Icc hnn,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ k) t]
    simp only [sub_self, sub_zero, integral_pow, zero_pow (Nat.succ_ne_zero _), sub_zero]
    unfold erlangPDF erlangDensity
    rw [ite_eq_left ht]
    congr 1
    dsimp [C]
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp
    <;> ring
  · have he (x : ℝ) : exponentialPDF B x * erlangPDF B k (-x + t) = 0 := by
      by_cases hx : x < 0
      · simp [exponentialPDF_of_neg hx]
      · have htx : ¬0 ≤ -x + t := by linarith
        simp [erlangPDF, erlangDensity, htx]
    rw [lintegral_congr he]
    simp [erlangPDF, erlangDensity, ht]

noncomputable def sumExponentialLaw (B : ℝ) : Nat → Measure ℝ
  | 0 => Measure.dirac 0
  | n + 1 => (expMeasure B).conv (sumExponentialLaw B n)

/-- This is the law of an actual sum of independent proposal clocks, not an assumed density. -/
theorem sum_exponentials_erlang (B : ℝ) (hB : 0 < B) (k : Nat) :
    sumExponentialLaw B (k + 1) = erlangMeasure B k := by
  let : IsProbabilityMeasure (expMeasure B) := isProbabilityMeasure_expMeasure hB
  induction k with
  | zero =>
    simp only [sumExponentialLaw, Measure.conv_dirac, add_zero, Measure.map_id]
    change (expMeasure B).map id = erlangMeasure B 0
    rw [Measure.map_id]
    change volume.withDensity (exponentialPDF B) = volume.withDensity (erlangPDF B 0)
    congr 1
    funext t
    simp [exponentialPDF, exponentialPDFReal, gammaPDFReal, erlangPDF, erlangDensity]
  | succ k ih =>
    rw [sumExponentialLaw, ih, exponential_erlang_convolution B hB k]

end JumpProcessesLean.Proofs
