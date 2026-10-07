import JumpProcessesLean.Proofs.MaskedTransition
import JumpProcessesLean.Proofs.TrajectoryCache

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

lemma expMeasure_zero : expMeasure 0 = 0 := by
  have hpdf : gammaPDF 1 0 = fun _ => 0 := by
    funext x
    simp [gammaPDF, gammaPDFReal]
  simp [expMeasure, gammaMeasure, hpdf]

lemma expMeasure_finite_of_nonnegative (a : ℝ) (ha : 0 ≤ a) : IsFiniteMeasure (expMeasure a) := by
  rcases lt_or_eq_of_le ha with h | h
  · let : IsProbabilityMeasure (expMeasure a) := isProbabilityMeasure_expMeasure h
    infer_instance
  · rw [← h, expMeasure_zero]; infer_instance

noncomputable def ghostCache {n : Nat} (rates : Fin n → ℝ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun j => expMeasure (ghostRate (rates j)))

instance ghostCache_probability {n : Nat} (rates : Fin n → ℝ) : IsProbabilityMeasure (ghostCache rates) := by
  let (j : Fin n) : IsProbabilityMeasure (expMeasure (ghostRate (rates j))) :=
    isProbabilityMeasure_expMeasure (ghostRate_positive _)
  unfold ghostCache
  infer_instance

noncomputable def maskedStepPair {n : Nat} (old new : Fin n → ℝ) (i : Fin n)
    (p : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ × (Fin n → ℝ) :=
  (p.1 i, maskedActualResidual old new i p.1 p.2)

noncomputable def maskedStepPairLaw {n : Nat} (old new : Fin n → ℝ) (i : Fin n) :
    Measure (ℝ × (Fin n → ℝ)) :=
  ((ghostCache old).prod (Measure.pi (fun _ : Fin n => unitUniform))).restrict
    (maskedStepBranch old i) |>.map (maskedStepPair old new i)

lemma measurable_maskedStepPair_formula {n : Nat} (old new : Fin n → ℝ) (i : Fin n) :
    Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      (p.1 i, maskedResidual old new i p.1 p.2)) := by
  apply Measurable.prodMk (by fun_prop)
  apply Measurable.of_eval
  intro j
  unfold maskedResidual
  split_ifs <;> (try unfold exponentialClock) <;> fun_prop

lemma maskedStepPair_ae_formula {n : Nat} (old new : Fin n → ℝ)
    (hn : ∀ j, 0 ≤ new j) (i : Fin n) :
    maskedStepPair old new i =ᵐ[
      ((ghostCache old).prod (Measure.pi (fun _ : Fin n => unitUniform))).restrict
        (maskedStepBranch old i)]
      (fun p => (p.1 i, maskedResidual old new i p.1 p.2)) := by
  have hu := (Measure.quasiMeasurePreserving_snd
    (μ := ghostCache old) (ν := Measure.pi (fun _ : Fin n => unitUniform))).tendsto_ae.eventually
      uniform_vector_ae_mem
  filter_upwards [ae_restrict_mem (by unfold maskedStepBranch; measurability),
    ae_restrict_of_ae hu] with p hp hup
  unfold maskedStepPair
  rw [maskedActualResidual_executes old new hn i p.1 p.2
    (fun j hj => if h : j = i then by simp [h] else (hp.2.2 j h hj).le) hup]

theorem masked_step_pair_law {n : Nat} (old new : Fin (n + 1) → ℝ)
    (ho : ∀ j, 0 ≤ old j) (hn : ∀ j, 0 ≤ new j) (i : Fin (n + 1)) :
    maskedStepPairLaw old new i = ENNReal.ofReal (old i / (∑ j, old j)) •
      ((expMeasure (∑ j, old j)).prod (ghostCache new)) := by
  by_cases hi : 0 < old i
  · let split : (Fin (n + 2) → ℝ) → ℝ × (Fin (n + 1) → ℝ) := fun z => (z 0, Fin.tail z)
    have hm : Measurable split := by unfold split; fun_prop
    have he : maskedStepPairLaw old new i = (maskedTransitionLaw old new i).map split := by
      unfold maskedStepPairLaw maskedTransitionLaw
      rw [Measure.map_congr (maskedStepPair_ae_formula old new hn i),
        Measure.map_map hm (measurable_maskedTransitionVector old new i)]
      rfl
    rw [he, masked_transition_full_law old new ho i, Measure.map_smul _ hm.aemeasurable]
    congr 1
    have hA : 0 < ∑ j, old j := hi.trans_le (Finset.single_le_sum (fun j _ => ho j) (Finset.mem_univ i))
    have hp : ∀ j : Fin (n + 2), (0 : ℝ) < Fin.cases (∑ k, old k) (fun k => ghostRate (new k)) j := by
      intro j; cases j using Fin.cases
      · exact hA
      · exact ghostRate_positive _
    let (j : Fin (n + 2)) : IsProbabilityMeasure (expMeasure
      (Fin.cases (∑ k, old k) (fun k => ghostRate (new k)) j)) := isProbabilityMeasure_expMeasure (hp j)
    have hpi := (measurePreserving_piFinSuccAbove (fun j : Fin (n + 2) =>
      expMeasure (Fin.cases (∑ k, old k) (fun k => ghostRate (new k)) j)) 0).map_eq
    simpa [split, ghostCache, MeasurableEquiv.piFinSuccAbove, Fin.removeNth, Fin.consEquiv] using hpi
  · have hz : old i = 0 := le_antisymm (not_lt.mp hi) (ho i)
    have hb : maskedStepBranch old i = ∅ := by ext p; simp [maskedStepBranch, hi]
    simp [maskedStepPairLaw, hb, hz]

noncomputable def maskedHistoryStep {H : Type} [MeasurableSpace H] {n : Nat}
    (old new : Fin n → ℝ) (i : Fin n) (μ : Measure (H × (Fin n → ℝ))) :
    Measure (H × (ℝ × (Fin n → ℝ))) :=
  ((μ.prod (Measure.pi (fun _ : Fin n => unitUniform))).restrict
    {p | (p.1.2, p.2) ∈ maskedStepBranch old i}).map
      (fun p => (p.1.1, maskedStepPair old new i (p.1.2, p.2)))

theorem masked_history_step_factorization {H : Type} [MeasurableSpace H] {n : Nat}
    (ν : Measure H) [SFinite ν] (old new : Fin (n + 1) → ℝ)
    (ho : ∀ j, 0 ≤ old j) (hn : ∀ j, 0 ≤ new j) (i : Fin (n + 1)) :
    maskedHistoryStep old new i (ν.prod (ghostCache old)) =
      ν.prod (ENNReal.ofReal (old i / (∑ j, old j)) •
        ((expMeasure (∑ j, old j)).prod (ghostCache new))) := by
  let U := Measure.pi (fun _ : Fin (n + 1) => unitUniform)
  let ρ := (ghostCache old).prod U
  let f := maskedStepPair old new i
  let g := fun p : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) =>
    (p.1 i, maskedResidual old new i p.1 p.2)
  have hg : Measurable g := measurable_maskedStepPair_formula old new i
  have hfg : f =ᵐ[ρ.restrict (maskedStepBranch old i)] g := maskedStepPair_ae_formula old new hn i
  have hs : MeasurableSet (maskedStepBranch old i) := by unfold maskedStepBranch; measurability
  have hprod : (ν.prod (ρ.restrict (maskedStepBranch old i))).map (Prod.map id f) =
      ν.prod ((ρ.restrict (maskedStepBranch old i)).map f) := by
    have hp : Prod.map id f =ᵐ[ν.prod (ρ.restrict (maskedStepBranch old i))] Prod.map id g := by
      filter_upwards [(Measure.quasiMeasurePreserving_snd
        (μ := ν) (ν := ρ.restrict (maskedStepBranch old i))).tendsto_ae.eventually hfg] with p hp
      exact congrArg (Prod.mk p.1) hp
    rw [Measure.map_congr hp, Measure.map_congr hfg,
      ← Measure.map_prod_map ν (ρ.restrict (maskedStepBranch old i)) measurable_id hg, Measure.map_id]
  have he : maskedHistoryStep old new i (ν.prod (ghostCache old)) =
      (ν.prod (ρ.restrict (maskedStepBranch old i))).map (Prod.map id f) := by
    have hp : Prod.map id f =ᵐ[ν.prod (ρ.restrict (maskedStepBranch old i))] Prod.map id g := by
      filter_upwards [(Measure.quasiMeasurePreserving_snd
        (μ := ν) (ν := ρ.restrict (maskedStepBranch old i))).tendsto_ae.eventually hfg] with p hp
      exact congrArg (Prod.mk p.1) hp
    rw [Measure.map_congr hp]
    unfold maskedHistoryStep
    have hl : (fun p : (H × (Fin (n + 1) → ℝ)) × (Fin (n + 1) → ℝ) =>
        (p.1.1, maskedStepPair old new i (p.1.2, p.2))) =ᵐ[
          ((ν.prod (ghostCache old)).prod U).restrict
            {p | (p.1.2, p.2) ∈ maskedStepBranch old i}]
        (fun p => (p.1.1, g (p.1.2, p.2))) := by
      have hu := (Measure.quasiMeasurePreserving_snd
        (μ := ν.prod (ghostCache old)) (ν := U)).tendsto_ae.eventually uniform_vector_ae_mem
      filter_upwards [ae_restrict_mem (by unfold maskedStepBranch; measurability),
        ae_restrict_of_ae hu] with p hp hup
      unfold g maskedStepPair
      rw [maskedActualResidual_executes old new hn i p.1.2 p.2
        (fun j hj => if h : j = i then by simp [h] else (hp.2.2 j h hj).le) hup]
    rw [Measure.map_congr hl]
    rw [show ν.prod (ρ.restrict (maskedStepBranch old i)) =
        (ν.prod ρ).restrict (univ ×ˢ maskedStepBranch old i) by
      rw [← Measure.prod_restrict, Measure.restrict_univ]]
    rw [← Measure.prodAssoc_prod, Measure.restrict_map MeasurableEquiv.prodAssoc.measurable
      (MeasurableSet.univ.prod hs), Measure.map_map (measurable_id.prodMap hg)
        MeasurableEquiv.prodAssoc.measurable]
    have hset : (MeasurableEquiv.prodAssoc :
        ((H × (Fin (n + 1) → ℝ)) × (Fin (n + 1) → ℝ)) ≃ᵐ
          H × ((Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ))) ⁻¹' (univ ×ˢ maskedStepBranch old i) =
        {p | (p.1.2, p.2) ∈ maskedStepBranch old i} := by ext p; simp [MeasurableEquiv.prodAssoc]
    rw [hset]
    rfl
  rw [he, hprod]
  change ν.prod (maskedStepPairLaw old new i) = _
  rw [masked_step_pair_law old new ho hn i]

noncomputable def maskedCachedWordLaw {n : Nat} (rates : Nat → Fin (n + 1) → ℝ)
    (marks : Nat → Fin (n + 1)) : (k : Nat) → Measure ((Fin k → ℝ) × (Fin (n + 1) → ℝ))
  | 0 => (Measure.dirac (fun j => Fin.elim0 j)).prod (ghostCache (rates 0))
  | k + 1 => (maskedHistoryStep (rates k) (rates (k + 1)) (marks k)
      (maskedCachedWordLaw rates marks k)).map
        (fun p => (prependHoldingTime (p.1, p.2.1), p.2.2))

lemma targetWordLaw_nonnegative_finite {n : Nat} (rates : Nat → Fin (n + 1) → ℝ)
    (hr : ∀ k j, 0 ≤ rates k j) (marks : Nat → Fin (n + 1)) (k : Nat) :
    IsFiniteMeasure (targetWordLaw rates marks k) := by
  induction k with
  | zero => unfold targetWordLaw; infer_instance
  | succ k ih =>
    let : IsFiniteMeasure (targetWordLaw rates marks k) := ih
    let : IsFiniteMeasure (expMeasure (∑ j, rates k j)) :=
      expMeasure_finite_of_nonnegative _ (Finset.sum_nonneg (fun j _ => hr k j))
    let : IsFiniteMeasure (ENNReal.ofReal (rates k (marks k) / (∑ j, rates k j)) •
      expMeasure (∑ j, rates k j)) := Measure.smul_finite _ ENNReal.ofReal_ne_top
    exact Measure.isFiniteMeasure_map _ _

/-- Persistent cache composition for arbitrary nonnegative state-dependent rates,
including newly active, disabled and absorbing channels. -/
theorem masked_cached_word_law {n : Nat} (rates : Nat → Fin (n + 1) → ℝ)
    (hr : ∀ k j, 0 ≤ rates k j) (marks : Nat → Fin (n + 1)) (k : Nat) :
    maskedCachedWordLaw rates marks k = (targetWordLaw rates marks k).prod (ghostCache (rates k)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    let : IsFiniteMeasure (targetWordLaw rates marks k) := targetWordLaw_nonnegative_finite rates hr marks k
    let : IsFiniteMeasure (expMeasure (∑ j, rates k j)) :=
      expMeasure_finite_of_nonnegative _ (Finset.sum_nonneg (fun j _ => hr k j))
    rw [maskedCachedWordLaw, ih, masked_history_step_factorization _ _ _ (hr k) (hr (k + 1)),
      ← Measure.prod_smul_left]
    exact history_prod_append _ _ _ _ (measurable_prependHoldingTime k)

theorem masked_cached_word_marginal {n : Nat} (rates : Nat → Fin (n + 1) → ℝ)
    (hr : ∀ k j, 0 ≤ rates k j) (marks : Nat → Fin (n + 1)) (k : Nat) :
    (maskedCachedWordLaw rates marks k).map Prod.fst = targetWordLaw rates marks k := by
  rw [masked_cached_word_law rates hr marks k, Measure.map_fst_prod, measure_univ, one_smul]

end JumpProcessesLean.Proofs
