import JumpProcessesLean.Proofs.SimulationLaw
import JumpProcessesLean.Proofs.RSSAFloatDistribution

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

lemma sum_mark_weights {n : Nat} (rates : Fin n → ℝ) (hr : ∀ j, 0 ≤ rates j)
    (hA : 0 < ∑ j, rates j) :
    (∑ j, ENNReal.ofReal (rates j / (∑ l, rates l))) = 1 := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => div_nonneg (hr j) hA.le),
    ← Finset.sum_div, div_self hA.ne', ENNReal.ofReal_one]

theorem target_word_mass {n : Nat} (rates : Nat → Fin (n + 1) → ℝ)
    (hA : ∀ k, 0 < ∑ j, rates k j) (marks : Nat → Fin (n + 1)) (k : Nat) :
    targetWordLaw rates marks k univ =
      ∏ q : Fin k, ENNReal.ofReal (rates q.val (marks q.val) / (∑ j, rates q.val j)) := by
  induction k with
  | zero => simp [targetWordLaw]
  | succ k ih =>
    let : IsProbabilityMeasure (expMeasure (∑ j, rates k j)) := isProbabilityMeasure_expMeasure (hA k)
    rw [targetWordLaw, Measure.map_apply (measurable_prependHoldingTime k) MeasurableSet.univ,
      preimage_univ, ← univ_prod_univ, Measure.prod_prod, ih,
      Measure.smul_apply, measure_univ, smul_eq_mul, mul_one, Fin.prod_univ_castSucc]
    rfl

noncomputable def pathWordWeight {σ : Type} {n k : Nat}
    (transition : σ → Fin (n + 1) → σ) (rates : σ → Fin (n + 1) → ℝ)
    (initial : σ) (word : Fin k → Fin (n + 1)) : ℝ≥0∞ :=
  ∏ q : Fin k, ENNReal.ofReal
    (completedRates (rates (stateAlongWord transition initial (extendMarks word) q.val)) (word q) /
      (∑ j, completedRates (rates (stateAlongWord transition initial (extendMarks word) q.val)) j))

lemma states_shift {σ : Type} {n k : Nat} (transition : σ → Fin (n + 1) → σ)
    (initial : σ) (word : Fin (k + 1) → Fin (n + 1)) (l : Nat) (hl : l ≤ k) :
    stateAlongWord transition initial (extendMarks word) (l + 1) =
      stateAlongWord transition (transition initial (word 0)) (extendMarks (Fin.tail word)) l := by
  induction l with
  | zero => simp [stateAlongWord, extendMarks]
  | succ l ih =>
    change transition (stateAlongWord transition initial (extendMarks word) (l + 1))
        (extendMarks word (l + 1)) =
      transition (stateAlongWord transition (transition initial (word 0)) (extendMarks (Fin.tail word)) l)
        (extendMarks (Fin.tail word) l)
    rw [ih (by omega)]
    congr 1
    simp only [extendMarks, show l + 1 < k + 1 by omega, show l < k by omega, dite_true, Fin.tail]
    rfl

lemma path_word_weight_cons {σ : Type} {n k : Nat}
    (transition : σ → Fin (n + 1) → σ) (rates : σ → Fin (n + 1) → ℝ)
    (initial : σ) (i : Fin (n + 1)) (rest : Fin k → Fin (n + 1)) :
    pathWordWeight transition rates initial (Fin.cons i rest) =
      ENNReal.ofReal (completedRates (rates initial) i / (∑ j, completedRates (rates initial) j)) *
        pathWordWeight transition rates (transition initial i) rest := by
  unfold pathWordWeight
  rw [Fin.prod_univ_succ]
  simp only [Fin.val_zero, stateAlongWord, Fin.cons_zero]
  congr 1
  apply Finset.prod_congr rfl
  intro q _
  simp only [Fin.val_succ]
  rw [states_shift transition initial (Fin.cons i rest) q.val (by omega)]
  simp only [Fin.cons_succ, Fin.cons_zero, Fin.tail_cons]

/-- Reaction words carry total probability one, including absorbing completions. -/
theorem path_word_weights_normalize {σ : Type} {n : Nat}
    (transition : σ → Fin (n + 1) → σ) (rates : σ → Fin (n + 1) → ℝ)
    (hr : ∀ x j, 0 ≤ rates x j) (k : Nat) (initial : σ) :
    (∑ word : Fin k → Fin (n + 1), pathWordWeight transition rates initial word) = 1 := by
  induction k generalizing initial with
  | zero => simp [pathWordWeight]
  | succ k ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => Fin (n + 1))).sum_comp]
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fintype.sum_prod_type, path_word_weight_cons,
      ← Finset.mul_sum, ih, mul_one]
    exact sum_mark_weights _ (completedRates_nonnegative _ (hr initial)) (completedRates_positive_total _)

theorem operational_finite_path_probability {σ : Type} {n : Nat}
    (transition : σ → Fin (n + 1) → σ) (rates lower upper : σ → Fin (n + 1) → ℝ)
    (hr : ∀ x j, 0 ≤ rates x j)
    (hb : ∀ x j, 0 ≤ lower x j ∧ lower x j ≤ rates x j ∧ rates x j ≤ upper x j)
    (initial : σ) (k : Nat) (algorithm : Algorithm) :
    IsProbabilityMeasure (operationalFinitePathLaw algorithm transition rates lower upper initial k) := by
  constructor
  unfold operationalFinitePathLaw
  rw [Measure.sum_apply _ MeasurableSet.univ, tsum_fintype]
  have hword (word : Fin k → Fin (n + 1)) :
      ((eventWordMeasure algorithm
        (fun l => completedRates (rates (stateAlongWord transition initial (extendMarks word) l)))
        (fun l => completedLower (rates (stateAlongWord transition initial (extendMarks word) l))
          (lower (stateAlongWord transition initial (extendMarks word) l)))
        (fun l => completedUpper (rates (stateAlongWord transition initial (extendMarks word) l))
          (upper (stateAlongWord transition initial (extendMarks word) l))) (extendMarks word) k).map
            (fun ts => (word, ts))) univ = pathWordWeight transition rates initial word := by
    rw [Measure.map_apply (by fun_prop) MeasurableSet.univ, preimage_univ,
      event_word_measure_law algorithm _ _ _
        (fun l => completedRates_nonnegative _ (hr _))
        (fun l => completedRates_positive_total _)
        (fun l => completedBounds_valid _ _ _ (hb _)),
      target_word_mass _ (fun l => completedRates_positive_total _)]
    unfold pathWordWeight
    apply Finset.prod_congr rfl
    intro q _
    simp [extendMarks, q.isLt]
  simp_rw [hword]
  exact path_word_weights_normalize transition rates hr k initial

end JumpProcessesLean.Proofs
