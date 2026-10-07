import JumpProcessesLean.RealBackend
import JumpProcessesLean.NRM
import JumpProcessesLean.RSSA
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace JumpProcessesLean.Proofs

open Real

/-- Independently stated exponential-clock specification, with elapsed time ≥ 0. -/
noncomputable def clockSurvival (rate elapsed : ℝ) : ℝ := exp (-(rate * elapsed))

theorem clock_memoryless (rate elapsed residual : ℝ) :
    clockSurvival rate (elapsed + residual) / clockSurvival rate elapsed =
      clockSurvival rate residual := by
  unfold clockSurvival
  rw [mul_add, neg_add, Real.exp_add, mul_div_cancel_left₀ _ (Real.exp_ne_zero _)]

/-- Deterministic scaling identity for the executable NRM rescale operation.
It says the remaining integrated propensity is unchanged. -/
theorem nrm_rescale_hazard (now oldRate newRate oldTime : ℝ) (hnew : newRate ≠ 0) :
    newRate * (rescaleClock realArithmetic now oldRate newRate oldTime - now) =
      oldRate * (oldTime - now) := by
  simp only [rescaleClock, realArithmetic]
  (field_simp; ring)

theorem nrm_rescale_survival (oldRate newRate t : ℝ) (hold : 0 < oldRate) :
    clockSurvival oldRate (newRate / oldRate * t) = clockSurvival newRate t := by
  unfold clockSurvival
  congr 1
  field_simp

/-- The inverse-exponential transform used by the executable random source. -/
noncomputable def exponentialClock (rate u : ℝ) : ℝ := -log u / rate

theorem exponentialClock_nonneg (rate u : ℝ) (hr : 0 < rate)
    (hu : 0 < u) (hu1 : u ≤ 1) : 0 ≤ exponentialClock rate u := by
  unfold exponentialClock
  exact div_nonneg (neg_nonneg.mpr (log_nonpos hu.le hu1)) hr.le

theorem exponentialClock_tail_iff (rate u t : ℝ) (hr : 0 < rate) (hu : 0 < u) :
    t < exponentialClock rate u ↔ u < clockSurvival rate t := by
  unfold exponentialClock clockSurvival
  rw [lt_div_iff₀ hr]
  have hlog : log u < -(rate * t) ↔ u < exp (-(rate * t)) :=
    log_lt_iff_lt_exp hu
  constructor
  · intro h
    apply hlog.mp
    nlinarith
  · intro h
    have := hlog.mpr h
    nlinarith

/-- RSSA's lower-bound shortcut agrees with testing the actual propensity. -/
theorem rssa_lower_shortcut (lower actual threshold : ℝ) (hlo : lower ≤ actual) :
    rssaAccept realArithmetic lower actual threshold =
      decide (0 < actual ∧ threshold ≤ actual) := by
  simp only [rssaAccept, realArithmetic]
  by_cases h : 0 < actual ∧ threshold ≤ actual
  · simp [h.1, h.2]
  · have hn : ¬(0 < lower ∧ threshold ≤ lower) := by
      intro hl
      apply h
      exact ⟨lt_of_lt_of_le hl.1 hlo, le_trans hl.2 hlo⟩
    simp only [Bool.decide_and]
    simp [h, hn]

end JumpProcessesLean.Proofs
