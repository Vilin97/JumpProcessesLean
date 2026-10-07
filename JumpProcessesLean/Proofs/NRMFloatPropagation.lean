import JumpProcessesLean.Proofs.NRMFloatUpdate

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

noncomputable def updatedRealClock {n : Nat} (old new : Fin n → Binary64)
    (cr er : Fin n → ℝ) (nr : ℝ) (fired j : Fin n) : ℝ :=
  if j ≠ fired ∧ 0 < floatReal (old j) then
    nr + (floatReal (old j) / floatReal (new j)) * (cr j - nr)
  else nr + er j / floatReal (new j)

noncomputable def rescaleRoundBudget (now old new c : Binary64) : ℝ :=
  floatEpsilon (floatReal now + floatReal ((old / new) * (c - now))) +
    floatEpsilon (floatReal (old / new) * floatReal (c - now)) +
    |floatReal (old / new)| * floatEpsilon (floatReal c - floatReal now) +
    |floatReal c - floatReal now| * floatEpsilon (floatReal old / floatReal new)

structure NRMUpdateCertificate {n : Nat} (old new c e : Fin n → Binary64)
    (cr er : Fin n → ℝ) (now : Binary64) (nr εc εn δ : ℝ) (fired : Fin n) : Prop where
  oldFinite : ∀ j, ExecFloat.Binary.isFinite (old j) = true
  newValid : ∀ j, validRate binary64Arithmetic (new j) = true
  cacheFinite : ∀ j, ExecFloat.Binary.isFinite (c j) = true
  nowFinite : ExecFloat.Binary.isFinite now = true
  nowError : |floatReal now - nr| ≤ εn
  cacheError : ∀ j, 0 < floatReal (old j) → |floatReal (c j) - cr j| ≤ εc
  flags : ∀ j, UpdateFlags binary64Arithmetic (old j) (new j) (c j) (e j) now j.val fired.val
  newNonzero : ∀ j, 0 < floatReal (new j) → Model.isZero (ExecFloat.Binary.toModel (new j)) = false
  freshFinite : ∀ j, ExecFloat.Binary.isFinite (e j) = true
  freshQuotient : ∀ j, 0 < floatReal (new j) →
    ExecFloat.Binary.isFinite (e j / new j) = true
  freshClock : ∀ j, 0 < floatReal (new j) →
    ExecFloat.Binary.isFinite (now + e j / new j) = true
  freshBudget : ∀ j, 0 < floatReal (new j) →
    floatEpsilon (floatReal now + floatReal (e j / new j)) +
      floatEpsilon (floatReal (e j) / floatReal (new j)) +
      εn + |floatReal (e j) - er j| / floatReal (new j) ≤ δ
  rescaleQuotient : ∀ j, j ≠ fired → 0 < floatReal (old j) → 0 < floatReal (new j) →
    ExecFloat.Binary.isFinite (old j / new j) = true
  rescaleDifference : ∀ j, j ≠ fired → 0 < floatReal (old j) → 0 < floatReal (new j) →
    ExecFloat.Binary.isFinite (c j - now) = true
  rescaleProduct : ∀ j, j ≠ fired → 0 < floatReal (old j) → 0 < floatReal (new j) →
    ExecFloat.Binary.isFinite ((old j / new j) * (c j - now)) = true
  rescaleFinite : ∀ j, j ≠ fired → 0 < floatReal (old j) → 0 < floatReal (new j) →
    ExecFloat.Binary.isFinite (rescaleClock binary64Arithmetic now (old j) (new j) (c j)) = true
  rescaleBudget : ∀ j, j ≠ fired → 0 < floatReal (old j) → 0 < floatReal (new j) →
    rescaleRoundBudget now (old j) (new j) (c j) +
      |floatReal (old j) / floatReal (new j)| * εc +
      |1 - floatReal (old j) / floatReal (new j)| * εn ≤ δ

/-- Rounded retained clocks propagate the previous time/cache errors. Fired or
reactivated clocks propagate primitive exponential errors. Disabled clocks
return none. All branches are those of the actual public FloatLib NRM update. -/
theorem nrm_float_update_certificate_refines {n : Nat} (old new c e : Fin n → Binary64)
    (cr er : Fin n → ℝ) (now : Binary64) (nr εc εn δ : ℝ) (fired : Fin n)
    (hc : NRMUpdateCertificate old new c e cr er now nr εc εn δ fired)
    (j : Fin n) :
    (updateClock binary64Arithmetic (old j) (new j) (c j) (e j) now j.val fired.val).isSome =
      decide (0 < floatReal (new j)) ∧
    ∀ t, updateClock binary64Arithmetic (old j) (new j) (c j) (e j) now j.val fired.val = some t →
      |floatReal t - updatedRealClock old new cr er nr fired j| ≤ δ := by
  have hnf : ExecFloat.Binary.isFinite (new j) = true := by
    have h := hc.newValid j
    have hp : binary64Arithmetic.finite (new j) = true ∧
        binary64Arithmetic.le binary64Arithmetic.zero (new j) = true := by simpa only [validRate, Bool.and_eq_true] using h
    exact hp.1
  have hpos : binary64Arithmetic.lt 0 (new j) = decide (0 < floatReal (new j)) := by
    change decide ((0 : Binary64) < new j) = _
    apply decide_eq_decide.mpr
    simpa only [floatReal_zero] using float_lt_real 0 (new j) float_zero_finite hnf
  have hold : binary64Arithmetic.lt 0 (old j) = decide (0 < floatReal (old j)) := by
    change decide ((0 : Binary64) < old j) = _
    apply decide_eq_decide.mpr
    simpa only [floatReal_zero] using float_lt_real 0 (old j) float_zero_finite (hc.oldFinite j)
  have hkeep : (j.val != fired.val && binary64Arithmetic.lt 0 (old j)) =
      decide (j ≠ fired ∧ 0 < floatReal (old j)) := by
    rw [hold]
    by_cases hj : j = fired
    · subst j; simp
    · have hv : j.val ≠ fired.val := fun h => hj (Fin.ext h)
      by_cases hp : 0 < floatReal (old j) <;> simp [hj, hv, hp]
  have hclock : updateClock binary64Arithmetic (old j) (new j) (c j) (e j) now j.val fired.val =
      if 0 < floatReal (new j) then
        some (if j ≠ fired ∧ 0 < floatReal (old j) then
          rescaleClock binary64Arithmetic now (old j) (new j) (c j) else now + e j / new j)
      else none := by
    unfold updateClock
    rw [show binary64Arithmetic.zero = (0 : Binary64) from rfl, hpos, hkeep]
    simp only [decide_eq_true_eq]
    rfl
  constructor
  · rw [hclock]
    split_ifs <;> simp_all
  intro t ht
  rw [hclock] at ht
  by_cases hn : 0 < floatReal (new j)
  · simp only [hn, ite_true] at ht
    by_cases hk : j ≠ fired ∧ 0 < floatReal (old j)
    · have hteq : t = rescaleClock binary64Arithmetic now (old j) (new j) (c j) := by
        simpa [hk.1, hk.2] using ht.symm
      rw [hteq]
      have hr := float_nrm_rescale_error now (old j) (new j) (c j) hc.nowFinite (hc.oldFinite j)
        hnf (hc.cacheFinite j) (hc.newNonzero j hn) (hc.rescaleQuotient j hk.1 hk.2 hn)
        (hc.rescaleDifference j hk.1 hk.2 hn) (hc.rescaleProduct j hk.1 hk.2 hn)
        (hc.rescaleFinite j hk.1 hk.2 hn)
      have hi := rescale_input_error (floatReal (old j) / floatReal (new j))
        (floatReal (c j)) (cr j) (floatReal now) nr εc εn (hc.cacheError j hk.2) hc.nowError
      unfold updatedRealClock
      rw [if_pos hk]
      exact ((abs_sub_le _ _ _).trans (add_le_add hr hi)).trans (by
        simpa only [rescaleRoundBudget, add_assoc] using hc.rescaleBudget j hk.1 hk.2 hn)
    · simp only [hk, ite_false, Option.some.injEq] at ht
      subst t
      have hr := float_clock_time_error now (e j) (new j) hc.nowFinite (hc.freshFinite j)
        hnf (hc.newNonzero j hn) (hc.freshQuotient j hn) (hc.freshClock j hn)
      have hi : |(floatReal now + floatReal (e j) / floatReal (new j)) -
          (nr + er j / floatReal (new j))| ≤ εn + |floatReal (e j) - er j| / floatReal (new j) := by
        have he : (floatReal now + floatReal (e j) / floatReal (new j)) -
            (nr + er j / floatReal (new j)) =
            (floatReal now - nr) + (floatReal (e j) - er j) / floatReal (new j) := by ring
        rw [he]
        exact (abs_add_le _ _).trans (add_le_add hc.nowError (by
          rw [abs_div, abs_of_pos hn]))
      unfold updatedRealClock
      rw [if_neg hk]
      exact ((abs_sub_le _ _ _).trans (add_le_add hr hi)).trans (by
        simpa only [add_assoc] using hc.freshBudget j hn)
  · simp [hn] at ht

end JumpProcessesLean.Proofs
