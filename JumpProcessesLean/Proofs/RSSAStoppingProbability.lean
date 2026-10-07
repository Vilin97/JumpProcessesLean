import JumpProcessesLean.Proofs.PathNormalization

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

theorem rssa_stopping_inputs_probability {n : Nat} (rates lower upper : List ℝ)
    (hn : rates.length = n)
    (hshape : lower.length = rates.length ∧ upper.length = rates.length)
    (hb : ∀ (i : Nat) (hi : i < rates.length),
      0 ≤ lower[i]'(by omega) ∧ lower[i]'(by omega) ≤ rates[i] ∧ rates[i] ≤ upper[i]'(by omega))
    (hA : 0 < rates.sum) (hB : 0 < upper.sum) (hAB : rates.sum ≤ upper.sum) :
    IsProbabilityMeasure (rssaStoppingInputs (n := n) rates lower upper) := by
  let : IsProbabilityMeasure (expMeasure rates.sum) := isProbabilityMeasure_expMeasure hA
  let S (i : Fin n) : Set (RSSAStoppingInput n) := {p | rssaStoppingMark p = i}
  have hm (i : Fin n) : MeasurableSet (S i) :=
    (measurable_rssaStoppingMark n) (measurableSet_singleton i)
  have hd : Pairwise (fun i j => Disjoint (S i) (S j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro p hpi hpj
    exact hij (hpi.symm.trans hpj)
  have he : (⋃ i, S i) = univ := by
    ext p
    simp [S]
  constructor
  rw [← he, measure_iUnion hd hm, tsum_fintype]
  have hw (i : Fin n) : (rssaStoppingInputs (n := n) rates lower upper) (S i) =
      ENNReal.ofReal (rates[i.val]'(by omega) / rates.sum) := by
    have h := rssa_stopping_input_marked_law rates lower upper hn hshape hb hA hB hAB i univ MeasurableSet.univ
    simpa only [S, mem_univ, true_and, measure_univ, mul_one] using h
  simp_rw [hw]
  have hs : (∑ i : Fin n, rates[i.val]'(by omega)) = rates.sum := by
    have he : List.ofFn (fun i : Fin n => rates[i.val]'(by omega)) = rates := by
      apply List.ext_getElem (by simp [hn]); intro j hj hj'; simp
    rw [← List.sum_ofFn, he]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => div_nonneg
      ((hb i.val (by omega)).1.trans (hb i.val (by omega)).2.1) hA.le),
    ← Finset.sum_div, hs, div_self hA.ne', ENNReal.ofReal_one]

end JumpProcessesLean.Proofs
