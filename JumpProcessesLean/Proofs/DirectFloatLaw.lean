import JumpProcessesLean.Proofs.OperationalFloat

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

lemma checkRatesAux_valid {α : Type} (op : Arithmetic α) (rates : List α)
    (hv : ∀ a ∈ rates, validRate op a = true) (i : Nat) :
    checkRatesAux op rates i = .ok () := by
  induction rates generalizing i with
  | nil => rfl
  | cons a rest ih =>
    simp only [checkRatesAux, hv a (by simp), ite_true]
    exact ih (fun b hb => hv b (by simp [hb])) (i + 1)

lemma sumRates_binary64 (rates : Array Binary64) :
    sumRates binary64Arithmetic rates = rates.toList.foldl (· + ·) 0 := by
  simp only [sumRates, binary64Arithmetic, ← Array.foldl_toList]

lemma direct_float_flags_executes (rates : Array Binary64) (e u : Binary64) (j : Nat)
    (hr : ∀ a ∈ rates.toList, validRate binary64Arithmetic a = true)
    (hT : binary64Arithmetic.finite (sumRates binary64Arithmetic rates) = true)
    (hTp : binary64Arithmetic.lt binary64Arithmetic.zero (sumRates binary64Arithmetic rates) = true)
    (he : (binary64Arithmetic.finite e && binary64Arithmetic.lt binary64Arithmetic.zero e) = true)
    (hu : (binary64Arithmetic.finite u && binary64Arithmetic.le binary64Arithmetic.zero u &&
      binary64Arithmetic.lt u binary64Arithmetic.one) = true)
    (hj : chooseAux binary64Arithmetic (u * sumRates binary64Arithmetic rates) rates.toList 0 0 = some j)
    (ht : (binary64Arithmetic.finite (binary64Arithmetic.add 0 (binary64Arithmetic.div e (sumRates binary64Arithmetic rates))) &&
      binary64Arithmetic.lt 0 (binary64Arithmetic.add 0 (binary64Arithmetic.div e (sumRates binary64Arithmetic rates)))) = true) :
    direct binary64Arithmetic (tapeSource Binary64) rates 0 ⟨[u], [e]⟩ =
      .ok (some ⟨0 + e / sumRates binary64Arithmetic rates, j⟩, ⟨[], []⟩) := by
  have hc : checkRates binary64Arithmetic rates = .ok () := checkRatesAux_valid _ _ hr 0
  have hdE : drawExponential binary64Arithmetic (tapeSource Binary64) (⟨[u], [e]⟩ : Tape Binary64) =
      .ok (e, ⟨[u], []⟩) := by
    simp only [drawExponential, tapeSource, Bind.bind, Except.bind]
    change (if !(binary64Arithmetic.finite e && binary64Arithmetic.lt binary64Arithmetic.zero e) then _ else _) = _
    rw [he]
    rfl
  have hdU : drawUniform binary64Arithmetic (tapeSource Binary64) (⟨[u], []⟩ : Tape Binary64) =
      .ok (u, ⟨[], []⟩) := by
    simp only [drawUniform, tapeSource, Bind.bind, Except.bind]
    change (if !(binary64Arithmetic.finite u && binary64Arithmetic.le binary64Arithmetic.zero u && binary64Arithmetic.lt u binary64Arithmetic.one) then _ else _) = _
    rw [hu]
    rfl
  have hs : weightedIndex binary64Arithmetic rates (binary64Arithmetic.mul u (sumRates binary64Arithmetic rates)) = .ok j := by
    unfold weightedIndex
    change (match chooseAux binary64Arithmetic (u * sumRates binary64Arithmetic rates) rates.toList 0 0 with
      | some k => Except.ok k | none => Except.error Error.selectionFailure) = _
    rw [hj]
  unfold direct
  rw [hc]
  simp only [Bind.bind, Except.bind]
  rw [show binary64Arithmetic.finite (0 : Binary64) = true by exact float_zero_finite,
    hT, hTp]
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  rw [hdE]
  simp only [Except.bind]
  rw [hdU]
  simp only [Except.bind]
  rw [hs]
  simp only [Except.bind]
  rw [ht]
  rfl

lemma quotient_input_error (E e T A : ℝ) (hT : 0 < T) (hA : 0 < A) (ε : ℝ)
    (hε : |T - A| ≤ ε) :
    |E / T - e / A| ≤ |E - e| / T + |e| * ε / (T * A) := by
  have hid : E / T - e / A = (E - e) / T + e * (A - T) / (T * A) := by
    field_simp
    <;> ring
  rw [hid]
  calc
    _ ≤ |(E - e) / T| + |e * (A - T) / (T * A)| := abs_add_le _ _
    _ = |E - e| / T + |e| * |T - A| / (T * A) := by
      rw [abs_div, abs_div, abs_mul, abs_of_pos hT, abs_of_pos (mul_pos hT hA), abs_sub_comm A T]
    _ ≤ _ := by gcongr

/-- This certificate concerns inputs, finite intermediates, CDF margins, and a computable
rounding/source budget. It does not assume agreement of the sampler outputs. -/
structure DirectFloatCertificate (rates : Array Binary64) (e u : Binary64) (ur er δ η : ℝ) : Prop where
  validRates : ∀ a ∈ rates.toList, validRate binary64Arithmetic a = true
  finiteFold : FoldFinite 0 rates.toList
  totalFinite : ExecFloat.Binary.isFinite (sumRates binary64Arithmetic rates) = true
  totalPositive : binary64Arithmetic.lt binary64Arithmetic.zero (sumRates binary64Arithmetic rates) = true
  totalNonzero : Model.isZero (ExecFloat.Binary.toModel (sumRates binary64Arithmetic rates)) = false
  exponentialValid : (binary64Arithmetic.finite e && binary64Arithmetic.lt binary64Arithmetic.zero e) = true
  uniformValid : (binary64Arithmetic.finite u && binary64Arithmetic.le binary64Arithmetic.zero u && binary64Arithmetic.lt u binary64Arithmetic.one) = true
  quotientFinite : ExecFloat.Binary.isFinite (e / sumRates binary64Arithmetic rates) = true
  outputValid : (binary64Arithmetic.finite (binary64Arithmetic.add 0 (binary64Arithmetic.div e (sumRates binary64Arithmetic rates))) &&
    binary64Arithmetic.lt 0 (binary64Arithmetic.add 0 (binary64Arithmetic.div e (sumRates binary64Arithmetic rates)))) = true
  thresholdFinite : ExecFloat.Binary.isFinite (u * sumRates binary64Arithmetic rates) = true
  thresholdError : |floatReal (u * sumRates binary64Arithmetic rates) - ur * (rates.toList.map floatReal).sum| ≤ η
  prefixBudget : ∀ j : Nat, j < rates.size → foldRoundBudget 0 (rates.toList.take (j + 1)) ≤ η
  cdfMargin : ∀ j : Nat, j < rates.size →
    2 * η < |ur * (rates.toList.map floatReal).sum - ((rates.toList.take (j + 1)).map floatReal).sum|
  timeBudget : floatEpsilon (floatReal (e / sumRates binary64Arithmetic rates)) +
    floatEpsilon (floatReal e / floatReal (sumRates binary64Arithmetic rates)) +
    |floatReal e - er| / floatReal (sumRates binary64Arithmetic rates) +
    |er| * foldRoundBudget 0 rates.toList /
      (floatReal (sumRates binary64Arithmetic rates) * (rates.toList.map floatReal).sum) ≤ δ

noncomputable def directFloatTime (rates : Array Binary64) (e u : Binary64) : ℝ :=
  match direct binary64Arithmetic (tapeSource Binary64) rates 0 ⟨[u], [e]⟩ with
  | .ok (some event, _) => floatReal event.time
  | _ => 0

noncomputable def directFloatMark (rates : Array Binary64) (e u : Binary64) : Option Nat :=
  match direct binary64Arithmetic (tapeSource Binary64) rates 0 ⟨[u], [e]⟩ with
  | .ok (some event, _) => some event.reaction
  | _ => none

/-- Complete float Direct execution preserves the real mark and approximates its time
under the explicit input certificate. The bound includes the rounded propensity sum. -/
theorem direct_float_certificate_refines (rates : Array Binary64) (e u : Binary64) (ur er δ η : ℝ)
    (hA : 0 < (rates.toList.map floatReal).sum) (hu : ur ∈ Ioo 0 1)
    (hc : DirectFloatCertificate rates e u ur er δ η) :
    |directFloatTime rates e u - er / (rates.toList.map floatReal).sum| ≤ δ ∧
      directFloatMark rates e u = selection (rates.toList.map floatReal) ur := by
  have hr : ∀ a ∈ rates.toList.map floatReal, 0 ≤ a := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    have hv := hc.validRates b hb
    have hv' : ExecFloat.Binary.isFinite b = true ∧ (0 : Binary64) ≤ b := by
      simpa only [validRate, binary64Arithmetic, Bool.and_eq_true, decide_eq_true_eq] using hv
    simpa only [floatReal_zero] using (float_le_real 0 b float_zero_finite hv'.1).mp hv'.2
  obtain ⟨j, hj⟩ := chooseAux_exists (rates.toList.map floatReal) hr
    (ur * (rates.toList.map floatReal).sum) 0 (by nlinarith [hu.1]) (by nlinarith [hu.2]) 0
  have hs := chooseAux_float_margin rates.toList 0 (u * sumRates binary64Arithmetic rates)
    (ur * (rates.toList.map floatReal).sum) η hc.finiteFold hc.thresholdFinite hc.thresholdError
    (by intro k hk; exact hc.prefixBudget k (by simpa using hk))
    (by intro k hk; simpa only [floatReal_zero, zero_add] using hc.cdfMargin k (by simpa using hk)) 0
  simp only [floatReal_zero] at hs
  rw [hj] at hs
  have hex := direct_float_flags_executes rates e u j hc.validRates hc.totalFinite hc.totalPositive
    hc.exponentialValid hc.uniformValid hs hc.outputValid
  have heparts : binary64Arithmetic.finite e = true ∧ binary64Arithmetic.lt binary64Arithmetic.zero e = true := by
    simpa only [Bool.and_eq_true] using hc.exponentialValid
  have hefinite : ExecFloat.Binary.isFinite e = true := heparts.1
  have hout : ExecFloat.Binary.isFinite (0 + e / sumRates binary64Arithmetic rates) = true :=
    by
      have hp : binary64Arithmetic.finite (binary64Arithmetic.add 0 (binary64Arithmetic.div e (sumRates binary64Arithmetic rates))) = true ∧
        binary64Arithmetic.lt 0 (binary64Arithmetic.add 0 (binary64Arithmetic.div e (sumRates binary64Arithmetic rates))) = true := by
        simpa only [Bool.and_eq_true] using hc.outputValid
      exact hp.1
  have hTpos : 0 < floatReal (sumRates binary64Arithmetic rates) := by
    have hp : (0 : Binary64) < sumRates binary64Arithmetic rates := of_decide_eq_true hc.totalPositive
    simpa only [floatReal_zero] using (float_lt_real 0 _ float_zero_finite hc.totalFinite).mp hp
  have hsum := float_fold_sum_error 0 rates.toList hc.finiteFold
  rw [← sumRates_binary64, floatReal_zero, zero_add] at hsum
  have heclock := float_clock_time_error 0 e (sumRates binary64Arithmetic rates) float_zero_finite
    hefinite hc.totalFinite hc.totalNonzero hc.quotientFinite hout
  simp only [floatReal_zero, zero_add] at heclock
  have hdiv := quotient_input_error (floatReal e) er (floatReal (sumRates binary64Arithmetic rates))
    (rates.toList.map floatReal).sum hTpos hA _ hsum
  constructor
  · unfold directFloatTime
    rw [hex]
    exact ((abs_sub_le _ _ _).trans (add_le_add heclock hdiv)).trans (by simpa only [add_assoc] using hc.timeBudget)
  · unfold directFloatMark
    rw [hex]
    exact hj.symm

/-- Distributional approximation for the ACTUAL FloatLib Direct function. An input
coupling certificate must hold outside the stated bad set; its probability is explicit. -/
theorem direct_float_joint_tail_approx (rates : Array Binary64)
    (hA : 0 < (rates.toList.map floatReal).sum)
    (hr : ∀ a ∈ rates.toList.map floatReal, 0 ≤ a)
    (ef uf : ℝ × ℝ → Binary64) (bad : Set (ℝ × ℝ)) (hbad : MeasurableSet bad)
    (δ η : ℝ) (hδ : 0 ≤ δ)
    (hgood : ∀ p ∉ bad, p.2 ∈ Ioo 0 1 ∧
      DirectFloatCertificate rates (ef p) (uf p) p.2 (-log p.1) δ η)
    (i : Nat) (hi : i < rates.size) (t : ℝ) (ht : δ ≤ t) :
    ENNReal.ofReal (((rates.toList.map floatReal)[i]'(by simpa using hi) /
      (rates.toList.map floatReal).sum) * clockSurvival (rates.toList.map floatReal).sum (t + δ)) ≤
      (unitUniform.prod unitUniform) {p | t < directFloatTime rates (ef p) (uf p) ∧
        directFloatMark rates (ef p) (uf p) = some i} + (unitUniform.prod unitUniform) bad ∧
    (unitUniform.prod unitUniform) {p | t < directFloatTime rates (ef p) (uf p) ∧
        directFloatMark rates (ef p) (uf p) = some i} ≤
      ENNReal.ofReal (((rates.toList.map floatReal)[i]'(by simpa using hi) /
        (rates.toList.map floatReal).sum) * clockSurvival (rates.toList.map floatReal).sum (t - δ)) +
        (unitUniform.prod unitUniform) bad := by
  have hg : ∀ p ∉ bad,
      |directFloatTime rates (ef p) (uf p) - exponentialClock (rates.toList.map floatReal).sum p.1| ≤ δ ∧
        directFloatMark rates (ef p) (uf p) = selection (rates.toList.map floatReal) p.2 := by
    intro p hp
    exact direct_float_certificate_refines rates (ef p) (uf p) p.2 (-log p.1) δ η hA
      (hgood p hp).1 (hgood p hp).2
  have h := coupled_joint_tail_bounds (unitUniform.prod unitUniform)
    (fun p => exponentialClock (rates.toList.map floatReal).sum p.1)
    (fun p => directFloatTime rates (ef p) (uf p))
    (fun p => selection (rates.toList.map floatReal) p.2)
    (fun p => directFloatMark rates (ef p) (uf p)) bad hbad δ hδ hg (some i) t
  have htail (s : ℝ) (hs : 0 ≤ s) :
      (unitUniform.prod unitUniform) {p | s < exponentialClock (rates.toList.map floatReal).sum p.1 ∧
        selection (rates.toList.map floatReal) p.2 = some i} =
      ENNReal.ofReal (((rates.toList.map floatReal)[i]'(by simpa using hi) /
        (rates.toList.map floatReal).sum) * clockSurvival (rates.toList.map floatReal).sum s) := by
    change (unitUniform.prod unitUniform) {p | exponentialClock (rates.toList.map floatReal).sum p.1 ∈ Ioi s ∧
      selection (rates.toList.map floatReal) p.2 = some i} = _
    rw [direct_pair_probability _ hr hA i (by simpa using hi) (Ioi s) measurableSet_Ioi,
      exponential_measure_tail _ s hA hs,
      ← ENNReal.ofReal_mul (by unfold clockSurvival; positivity), mul_comm]
  rw [htail (t + δ) (by linarith), htail (t - δ) (by linarith)] at h
  exact h

end JumpProcessesLean.Proofs
