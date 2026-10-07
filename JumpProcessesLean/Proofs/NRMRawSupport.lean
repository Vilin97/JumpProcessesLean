import JumpProcessesLean.Proofs.NRMDriverExecution

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

noncomputable def NRMRawGood {n : Nat} (rates : Nat → Fin (n + 1) → ℝ)
    (marks : Nat → Fin (n + 1)) : (k : Nat) → NRMRawInput n k → Prop
  | 0, p => ∀ j, p.1 j ∈ Ioo 0 1
  | k + 1, p => NRMRawGood rates marks k (p.1, Fin.tail p.2) ∧
      (∀ j, p.2 0 j ∈ Ioo 0 1) ∧
      ((nrmRawHistory rates marks k (p.1, Fin.tail p.2)).2, p.2 0) ∈
        maskedStepBranch (rates k) (marks k)

lemma measurable_NRMRawGood {n : Nat} (rates : Nat → Fin (n + 1) → ℝ)
    (marks : Nat → Fin (n + 1)) (k : Nat) : MeasurableSet {p | NRMRawGood rates marks k p} := by
  induction k with
  | zero => unfold NRMRawGood; measurability
  | succ k ih =>
    have hp : Measurable (fun p : NRMRawInput n (k + 1) => (p.1, Fin.tail p.2)) := by fun_prop
    have hbranch : MeasurableSet (maskedStepBranch (rates k) (marks k)) := by
      unfold maskedStepBranch; measurability
    have hu : MeasurableSet {p : NRMRawInput n (k + 1) | ∀ j, p.2 0 j ∈ Ioo 0 1} := by measurability
    exact (ih.preimage hp).inter (hu.inter
      (hbranch.preimage (((measurable_nrmRawHistory rates marks k).comp hp).snd.prodMk
        (by fun_prop))))

/-- All primitive inputs on the derived NRM word measure produce valid strict
native execution branches. Null boundary/tie cases have not been discarded by
an unproved output-law assumption. -/
theorem nrm_raw_good_ae {n : Nat} (rates : Nat → Fin (n + 1) → ℝ)
    (marks : Nat → Fin (n + 1)) (k : Nat) :
    ∀ᵐ p ∂nrmRawPathLaw rates marks k, NRMRawGood rates marks k p := by
  induction k with
  | zero =>
    rw [nrmRawPathLaw, ae_map_iff (by fun_prop) (measurable_NRMRawGood rates marks 0)]
    exact uniform_vector_ae_mem
  | succ k ih =>
    let μ := nrmRawPathLaw rates marks k
    let : IsFiniteMeasure μ := nrmRawPathLaw_finite rates marks k
    let U := Measure.pi (fun _ : Fin (n + 1) => unitUniform)
    have hprev : ∀ᵐ p ∂μ.prod U, NRMRawGood rates marks k p.1 :=
      (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := U)).tendsto_ae.eventually ih
    have hnew : ∀ᵐ p ∂μ.prod U, ∀ j, p.2 j ∈ Ioo 0 1 :=
      (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := U)).tendsto_ae.eventually uniform_vector_ae_mem
    rw [nrmRawPathLaw, ae_map_iff (measurable_nrmRawExtend _ _).aemeasurable
      (measurable_NRMRawGood rates marks (k + 1))]
    filter_upwards [ae_restrict_of_ae hprev, ae_restrict_of_ae hnew,
      ae_restrict_mem (by
        apply MeasurableSet.preimage (by unfold maskedStepBranch; measurability)
        exact (measurable_nrmRawHistory rates marks k).snd.comp measurable_fst |>.prodMk measurable_snd)]
      with p hp hu hb
    change NRMRawGood rates marks k p.1 ∧ (∀ j, p.2 j ∈ Ioo 0 1) ∧
      ((nrmRawHistory rates marks k p.1).2, p.2) ∈ maskedStepBranch (rates k) (marks k)
    exact ⟨hp, hu, hb⟩

end JumpProcessesLean.Proofs
