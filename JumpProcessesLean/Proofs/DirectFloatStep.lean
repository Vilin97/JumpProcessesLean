import JumpProcessesLean.Proofs.FloatTrace

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

lemma direct_float_suffix_flags (rates : Array Binary64) (now e u : Binary64) (j : Nat)
    (hr : ∀ a ∈ rates.toList, validRate binary64Arithmetic a = true)
    (hn : ExecFloat.Binary.isFinite now = true)
    (hT : binary64Arithmetic.finite (sumRates binary64Arithmetic rates) = true)
    (hTp : binary64Arithmetic.lt binary64Arithmetic.zero (sumRates binary64Arithmetic rates) = true)
    (he : exponentialFlag e = true) (hu : uniformFlag u = true)
    (hj : chooseAux binary64Arithmetic (u * sumRates binary64Arithmetic rates) rates.toList 0 0 = some j)
    (ht : clockFlag now e (sumRates binary64Arithmetic rates) = true) (us es : List Binary64) :
    direct binary64Arithmetic (tapeSource Binary64) rates now ⟨u :: us, e :: es⟩ =
      .ok (some ⟨now + e / sumRates binary64Arithmetic rates, j⟩, ⟨us, es⟩) := by
  have hc : checkRates binary64Arithmetic rates = .ok () := checkRatesAux_valid _ _ hr 0
  have hdE : drawExponential binary64Arithmetic (tapeSource Binary64)
      (⟨u :: us, e :: es⟩ : Tape Binary64) = .ok (e, ⟨u :: us, es⟩) := by
    simp only [drawExponential, tapeSource, Bind.bind, Except.bind]
    change (if !exponentialFlag e then _ else _) = _
    rw [he]; rfl
  have hdU : drawUniform binary64Arithmetic (tapeSource Binary64)
      (⟨u :: us, es⟩ : Tape Binary64) = .ok (u, ⟨us, es⟩) := by
    simp only [drawUniform, tapeSource, Bind.bind, Except.bind]
    change (if !uniformFlag u then _ else _) = _
    rw [hu]; rfl
  have hs : weightedIndex binary64Arithmetic rates
      (binary64Arithmetic.mul u (sumRates binary64Arithmetic rates)) = .ok j := by
    unfold weightedIndex
    change (match chooseAux binary64Arithmetic (u * sumRates binary64Arithmetic rates) rates.toList 0 0 with
      | some k => Except.ok k | none => Except.error Error.selectionFailure) = _
    rw [hj]
  unfold direct
  rw [hc]
  simp only [Bind.bind, Except.bind]
  rw [show binary64Arithmetic.finite now = true from hn, hT, hTp]
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  rw [hdE]
  simp only [Except.bind]
  rw [hdU]
  simp only [Except.bind]
  rw [hs]
  simp only [Except.bind]
  change (if !clockFlag now e (sumRates binary64Arithmetic rates) then _ else _) = _
  rw [ht]; rfl

structure DirectStepCertificate (rates : Array Binary64) (now e u : Binary64)
    (ur er δ η : ℝ) : Prop where
  selection : DirectFloatCertificate rates e u ur er δ η
  nowFinite : ExecFloat.Binary.isFinite now = true
  clockValid : clockFlag now e (sumRates binary64Arithmetic rates) = true
  timeBudget :
    floatEpsilon (floatReal now + floatReal (e / sumRates binary64Arithmetic rates)) +
    floatEpsilon (floatReal e / floatReal (sumRates binary64Arithmetic rates)) +
    |floatReal e - er| / floatReal (sumRates binary64Arithmetic rates) +
    |er| * foldRoundBudget 0 rates.toList /
      (floatReal (sumRates binary64Arithmetic rates) * (rates.toList.map floatReal).sum) ≤ δ

/-- Arbitrary-time native Direct execution and its local arithmetic budget, with
any suffix tape. The caller propagates the previous absolute time error. -/
theorem direct_float_step_refines (rates : Array Binary64) (now e u : Binary64)
    (ur er δ η : ℝ) (hc : DirectStepCertificate rates now e u ur er δ η)
    (hA : 0 < (rates.toList.map floatReal).sum) (hu : ur ∈ Ioo 0 1)
    (j : Nat) (hj : selection (rates.toList.map floatReal) ur = some j) (us es : List Binary64) :
    direct binary64Arithmetic (tapeSource Binary64) rates now ⟨u :: us, e :: es⟩ =
      .ok (some ⟨now + e / sumRates binary64Arithmetic rates, j⟩, ⟨us, es⟩) ∧
    |floatReal (now + e / sumRates binary64Arithmetic rates) -
      (floatReal now + er / (rates.toList.map floatReal).sum)| ≤ δ := by
  have hs := chooseAux_float_margin rates.toList 0 (u * sumRates binary64Arithmetic rates)
    (ur * (rates.toList.map floatReal).sum) η hc.selection.finiteFold hc.selection.thresholdFinite
    hc.selection.thresholdError (by intro k hk; exact hc.selection.prefixBudget k (by simpa using hk))
    (by intro k hk; simpa only [floatReal_zero, zero_add] using hc.selection.cdfMargin k (by simpa using hk)) 0
  simp only [floatReal_zero] at hs
  change chooseAux realArithmetic (ur * (rates.toList.map floatReal).sum)
    (rates.toList.map floatReal) 0 0 = some j at hj
  rw [hj] at hs
  refine ⟨direct_float_suffix_flags rates now e u j hc.selection.validRates hc.nowFinite
    hc.selection.totalFinite hc.selection.totalPositive hc.selection.exponentialValid
    hc.selection.uniformValid hs hc.clockValid us es, ?_⟩
  have he : ExecFloat.Binary.isFinite e = true := by
    have hh := hc.selection.exponentialValid
    rw [Bool.and_eq_true] at hh
    exact hh.1
  have ht : ExecFloat.Binary.isFinite (now + e / sumRates binary64Arithmetic rates) = true := by
    have hh := hc.clockValid
    rw [clockFlag, Bool.and_eq_true] at hh
    exact hh.1
  have hp : 0 < floatReal (sumRates binary64Arithmetic rates) := by
    have hh : (0 : Binary64) < sumRates binary64Arithmetic rates := of_decide_eq_true hc.selection.totalPositive
    simpa only [floatReal_zero] using (float_lt_real 0 _ float_zero_finite hc.selection.totalFinite).mp hh
  have hsum := float_fold_sum_error 0 rates.toList hc.selection.finiteFold
  rw [← sumRates_binary64, floatReal_zero, zero_add] at hsum
  have hclock := float_clock_time_error now e (sumRates binary64Arithmetic rates)
    hc.nowFinite he hc.selection.totalFinite hc.selection.totalNonzero hc.selection.quotientFinite ht
  have hdiv := quotient_input_error (floatReal e) er (floatReal (sumRates binary64Arithmetic rates))
    (rates.toList.map floatReal).sum hp hA _ hsum
  have hinput : |(floatReal now + floatReal e / floatReal (sumRates binary64Arithmetic rates)) -
      (floatReal now + er / (rates.toList.map floatReal).sum)| ≤
      |floatReal e - er| / floatReal (sumRates binary64Arithmetic rates) +
        |er| * foldRoundBudget 0 rates.toList /
          (floatReal (sumRates binary64Arithmetic rates) * (rates.toList.map floatReal).sum) := by
    simpa only [add_sub_add_left_eq_sub] using hdiv
  exact ((abs_sub_le _ _ _).trans (add_le_add hclock hinput)).trans
    (by simpa only [add_assoc] using hc.timeBudget)

lemma absolute_time_error (nf nr dtf dtr ε δ : ℝ)
    (hn : |nf - nr| ≤ ε) (hd : |dtf - (nf + dtr)| ≤ δ) :
    |dtf - (nr + dtr)| ≤ ε + δ := by
  have h := (abs_sub_le dtf (nf + dtr) (nr + dtr)).trans
    (add_le_add hd (by simpa only [add_sub_add_right_eq_sub] using hn))
  simpa only [add_comm] using h

end JumpProcessesLean.Proofs
