import JumpProcessesLean.Proofs.NRMTransitionLaw

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

noncomputable def nrmStepPair {n : Nat} (old new : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) (p : (Fin (n + 1) → ℝ) × ℝ) : ℝ × (Fin (n + 1) → ℝ) :=
  (p.1 i, nrmActualResidual old new i p.1 p.2)

noncomputable def nrmStepBranch {n : Nat} (i : Fin (n + 1)) :
    Set ((Fin (n + 1) → ℝ) × ℝ) :=
  {p | 0 < p.1 i ∧ ∀ j, j ≠ i → p.1 i < p.1 j}

noncomputable def nrmStepPairLaw {n : Nat} (old new : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) : Measure (ℝ × (Fin (n + 1) → ℝ)) :=
  (((Measure.pi (fun j => expMeasure (old j))).prod unitUniform).restrict
    (nrmStepBranch i)).map (nrmStepPair old new i)

lemma measurable_nrmStepPair_formula {n : Nat} (old new : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) : Measurable (fun p : (Fin (n + 1) → ℝ) × ℝ =>
      (p.1 i, fun j => if j = i then exponentialClock (new j) p.2 else
        rescaleClock realArithmetic (p.1 i) (old j) (new j) (p.1 j) - p.1 i)) := by
  apply Measurable.prodMk (by fun_prop)
  apply Measurable.of_eval
  intro j
  by_cases h : j = i
  · simp only [h, ite_true]; unfold exponentialClock; fun_prop
  · simp only [h, ite_false]; unfold rescaleClock realArithmetic; fun_prop

lemma nrmStepPair_ae_formula {n : Nat} (old new : Fin (n + 1) → ℝ)
    (ho : ∀ j, 0 < old j) (hn : ∀ j, 0 < new j) (i : Fin (n + 1)) :
    nrmStepPair old new i =ᵐ[
      ((Measure.pi (fun j => expMeasure (old j))).prod unitUniform).restrict
        (nrmStepBranch i)]
      (fun p => (p.1 i, fun j => if j = i then exponentialClock (new j) p.2 else
        rescaleClock realArithmetic (p.1 i) (old j) (new j) (p.1 j) - p.1 i)) := by
  have hu := (Measure.quasiMeasurePreserving_snd
    (μ := Measure.pi (fun j => expMeasure (old j))) (ν := unitUniform)).tendsto_ae.eventually
      unitUniform_ae_mem
  filter_upwards [ae_restrict_mem (by unfold nrmStepBranch; measurability),
    ae_restrict_of_ae hu] with p hp hup
  unfold nrmStepPair
  rw [nrmActualResidual_executes old new ho hn i p.1
    (fun j => if h : j = i then by simp [h] else (hp.2 j h).le) p.2 hup]

/-- The entire actual returned cache is independent of the holding time on each
winner branch. This pair form is convenient for composition with a past history. -/
theorem nrm_step_pair_law {n : Nat} (old new : Fin (n + 1) → ℝ)
    (ho : ∀ j, 0 < old j) (hn : ∀ j, 0 < new j) (i : Fin (n + 1)) :
    nrmStepPairLaw old new i = ENNReal.ofReal (old i / (∑ j, old j)) •
      ((expMeasure (∑ j, old j)).prod (Measure.pi (fun j => expMeasure (new j)))) := by
  let (j : Fin (n + 1)) : IsProbabilityMeasure (expMeasure (old j)) :=
    isProbabilityMeasure_expMeasure (ho j)
  let split : (Fin (n + 2) → ℝ) → ℝ × (Fin (n + 1) → ℝ) :=
    fun z => (z 0, fun j => z j.succ)
  have hm : Measurable split := by unfold split; fun_prop
  have ha : AEMeasurable (fun p : (Fin (n + 1) → ℝ) × ℝ =>
      (Fin.cases (p.1 i) (nrmActualResidual old new i p.1 p.2) : Fin (n + 2) → ℝ))
      (((Measure.pi (fun j => expMeasure (old j))).prod unitUniform).restrict (nrmStepBranch i)) := by
    apply (measurable_nrmTransitionVector old new i).aemeasurable.congr
    filter_upwards [nrmStepPair_ae_formula old new ho hn i] with p hp
    exact congrArg (fun q : ℝ × (Fin (n + 1) → ℝ) => (Fin.cases q.1 q.2 : Fin (n + 2) → ℝ)) hp.symm
  have he : nrmStepPairLaw old new i = (nrmActualTransitionLaw old new i).map split := by
    unfold nrmStepPairLaw nrmActualTransitionLaw
    change _ = (Measure.map (fun p => (Fin.cases (p.1 i)
      (nrmActualResidual old new i p.1 p.2) : Fin (n + 2) → ℝ))
      (((Measure.pi (fun j => expMeasure (old j))).prod unitUniform).restrict (nrmStepBranch i))).map split
    rw [AEMeasurable.map_map_of_aemeasurable hm.aemeasurable ha]
    rfl
  rw [he, nrm_actual_transition_full_law old new ho hn i, Measure.map_smul _ hm.aemeasurable]
  congr 1
  have hA : 0 < ∑ j, old j := Finset.sum_pos (fun j _ => ho j) Finset.univ_nonempty
  have hpositive : ∀ j : Fin (n + 2), (0 : ℝ) < Fin.cases (∑ k, old k) new j := by
    intro j; cases j using Fin.cases <;> simp [hA, hn]
  let (j : Fin (n + 2)) : IsProbabilityMeasure (expMeasure (Fin.cases (∑ k, old k) new j)) :=
    isProbabilityMeasure_expMeasure (hpositive j)
  have hpi := (measurePreserving_piFinSuccAbove
    (fun j : Fin (n + 2) => expMeasure (Fin.cases (∑ k, old k) new j)) 0).map_eq
  have hpi' : (Measure.pi (fun j : Fin (n + 2) => expMeasure (Fin.cases (∑ k, old k) new j))).map
      (fun z => (z 0, Fin.tail z)) =
      (expMeasure (∑ j, old j)).prod (Measure.pi (fun j => expMeasure (new j))) := by
    simpa [MeasurableEquiv.piFinSuccAbove, Fin.removeNth, Fin.consEquiv] using hpi
  convert hpi' using 1
  congr 1

/-- One cached step on a joint history/cache distribution. The input cache is carried
through this operation; it is not reinitialized. Fresh randomness is only a single
uniform for the fired channel, as in the positive-rate public NRM update. -/
noncomputable def nrmHistoryStep {H : Type} [MeasurableSpace H] {n : Nat}
    (old new : Fin (n + 1) → ℝ) (i : Fin (n + 1))
    (μ : Measure (H × (Fin (n + 1) → ℝ))) :
    Measure (H × (ℝ × (Fin (n + 1) → ℝ))) :=
  ((μ.prod unitUniform).restrict {p | (p.1.2, p.2) ∈ nrmStepBranch i}).map
    (fun p => (p.1.1, nrmStepPair old new i (p.1.2, p.2)))

/-- The operational cache invariant remains valid jointly with every measurable past.
This is the independence fact needed to iterate NRM without redrawing survivors. -/
theorem nrm_history_step_factorization {H : Type} [MeasurableSpace H] {n : Nat}
    (ν : Measure H) [SFinite ν] (old new : Fin (n + 1) → ℝ)
    (ho : ∀ j, 0 < old j) (hn : ∀ j, 0 < new j) (i : Fin (n + 1)) :
    nrmHistoryStep old new i (ν.prod (Measure.pi (fun j => expMeasure (old j)))) =
      ν.prod (ENNReal.ofReal (old i / (∑ j, old j)) •
        ((expMeasure (∑ j, old j)).prod (Measure.pi (fun j => expMeasure (new j))))) := by
  let (j : Fin (n + 1)) : IsProbabilityMeasure (expMeasure (old j)) :=
    isProbabilityMeasure_expMeasure (ho j)
  let ρ := (Measure.pi (fun j => expMeasure (old j))).prod unitUniform
  let f := nrmStepPair old new i
  let g := fun p : (Fin (n + 1) → ℝ) × ℝ =>
    (p.1 i, fun j => if j = i then exponentialClock (new j) p.2 else
      rescaleClock realArithmetic (p.1 i) (old j) (new j) (p.1 j) - p.1 i)
  have hg : Measurable g := measurable_nrmStepPair_formula old new i
  have hfg : f =ᵐ[ρ.restrict (nrmStepBranch i)] g := nrmStepPair_ae_formula old new ho hn i
  have hs : MeasurableSet (nrmStepBranch i) := by unfold nrmStepBranch; measurability
  have hprod : (ν.prod (ρ.restrict (nrmStepBranch i))).map (Prod.map id f) =
      ν.prod ((ρ.restrict (nrmStepBranch i)).map f) := by
    have hfgp : Prod.map id f =ᵐ[ν.prod (ρ.restrict (nrmStepBranch i))] Prod.map id g := by
      filter_upwards [(Measure.quasiMeasurePreserving_snd
        (μ := ν) (ν := ρ.restrict (nrmStepBranch i))).tendsto_ae.eventually hfg] with p hp
      exact congrArg (Prod.mk p.1) hp
    rw [Measure.map_congr hfgp, Measure.map_congr hfg,
      ← Measure.map_prod_map ν (ρ.restrict (nrmStepBranch i)) measurable_id hg,
      Measure.map_id]
  have he : nrmHistoryStep old new i (ν.prod (Measure.pi (fun j => expMeasure (old j)))) =
      (ν.prod (ρ.restrict (nrmStepBranch i))).map (Prod.map id f) := by
    have hfgp : Prod.map id f =ᵐ[ν.prod (ρ.restrict (nrmStepBranch i))] Prod.map id g := by
      filter_upwards [(Measure.quasiMeasurePreserving_snd
        (μ := ν) (ν := ρ.restrict (nrmStepBranch i))).tendsto_ae.eventually hfg] with p hp
      exact congrArg (Prod.mk p.1) hp
    rw [Measure.map_congr hfgp]
    unfold nrmHistoryStep
    have hleft : (fun p : (H × (Fin (n + 1) → ℝ)) × ℝ =>
        (p.1.1, nrmStepPair old new i (p.1.2, p.2))) =ᵐ[
          ((ν.prod (Measure.pi (fun j => expMeasure (old j)))).prod unitUniform).restrict
            {p | (p.1.2, p.2) ∈ nrmStepBranch i}]
        (fun p => (p.1.1, g (p.1.2, p.2))) := by
      have hu := (Measure.quasiMeasurePreserving_snd
        (μ := ν.prod (Measure.pi (fun j => expMeasure (old j)))) (ν := unitUniform)).tendsto_ae.eventually
          unitUniform_ae_mem
      filter_upwards [ae_restrict_mem (by unfold nrmStepBranch; measurability),
        ae_restrict_of_ae hu] with p hp hup
      unfold g nrmStepPair
      rw [nrmActualResidual_executes old new ho hn i p.1.2
        (fun j => if h : j = i then by simp [h] else (hp.2 j h).le) p.2 hup]
    rw [Measure.map_congr hleft]
    rw [show ν.prod (ρ.restrict (nrmStepBranch i)) =
        (ν.prod ρ).restrict (univ ×ˢ nrmStepBranch i) by
      rw [← Measure.prod_restrict, Measure.restrict_univ]]
    rw [← Measure.prodAssoc_prod, Measure.restrict_map MeasurableEquiv.prodAssoc.measurable
      (MeasurableSet.univ.prod hs), Measure.map_map (measurable_id.prodMap hg)
        MeasurableEquiv.prodAssoc.measurable]
    have hset : (MeasurableEquiv.prodAssoc : ((H × (Fin (n + 1) → ℝ)) × ℝ) ≃ᵐ
        H × ((Fin (n + 1) → ℝ) × ℝ)) ⁻¹' (univ ×ˢ nrmStepBranch i) =
        {p | (p.1.2, p.2) ∈ nrmStepBranch i} := by ext p; simp [MeasurableEquiv.prodAssoc]
    rw [hset]
    rfl
  rw [he, hprod]
  change ν.prod (nrmStepPairLaw old new i) = _
  rw [nrm_step_pair_law old new ho hn i]

noncomputable def prependHoldingTime {k : Nat} (p : (Fin k → ℝ) × ℝ) : Fin (k + 1) → ℝ :=
  Fin.cases p.2 p.1

lemma measurable_prependHoldingTime (k : Nat) :
    Measurable (@prependHoldingTime k) := by
  apply Measurable.of_eval
  intro j
  cases j using Fin.cases <;> simp only [prependHoldingTime, Fin.cases_zero, Fin.cases_succ] <;> fun_prop

lemma history_prod_append {H H' C : Type} [MeasurableSpace H] [MeasurableSpace H']
    [MeasurableSpace C] (ν : Measure H) (τ : Measure ℝ) (ψ : Measure C)
    [SFinite ν] [SFinite τ] [SFinite ψ] (f : H × ℝ → H') (hf : Measurable f) :
    (ν.prod (τ.prod ψ)).map (fun p => (f (p.1, p.2.1), p.2.2)) =
      ((ν.prod τ).map f).prod ψ := by
  rw [← Measure.prodAssoc_prod, Measure.map_map (by fun_prop) MeasurableEquiv.prodAssoc.measurable,
    show ψ = ψ.map id from Measure.map_id.symm,
    Measure.map_prod_map (ν.prod τ) ψ hf measurable_id]
  simp only [Measure.map_id]
  congr 1

/-- The target marked cylinder law for a specified reaction word. Holding times are
stored most recent first. Rates may vary at every transition along the word. -/
noncomputable def targetWordLaw {n : Nat} (rates : Nat → Fin (n + 1) → ℝ)
    (marks : Nat → Fin (n + 1)) : (k : Nat) → Measure (Fin k → ℝ)
  | 0 => Measure.dirac (fun j => Fin.elim0 j)
  | k + 1 => ((targetWordLaw rates marks k).prod
      (ENNReal.ofReal (rates k (marks k) / (∑ j, rates k j)) • expMeasure (∑ j, rates k j))).map
        prependHoldingTime

lemma targetWordLaw_finite {n : Nat} (rates : Nat → Fin (n + 1) → ℝ)
    (hr : ∀ k j, 0 < rates k j) (marks : Nat → Fin (n + 1)) (k : Nat) :
    IsFiniteMeasure (targetWordLaw rates marks k) := by
  induction k with
  | zero => unfold targetWordLaw; infer_instance
  | succ k ih =>
    let : IsFiniteMeasure (targetWordLaw rates marks k) := ih
    have hA : 0 < ∑ j, rates k j := Finset.sum_pos (fun j _ => hr k j) Finset.univ_nonempty
    let : IsProbabilityMeasure (expMeasure (∑ j, rates k j)) := isProbabilityMeasure_expMeasure hA
    let : IsFiniteMeasure (ENNReal.ofReal (rates k (marks k) / (∑ j, rates k j)) •
      expMeasure (∑ j, rates k j)) := Measure.smul_finite _ ENNReal.ofReal_ne_top
    exact Measure.isFiniteMeasure_map _ _

/-- Operational NRM reaction-word measure. Each step reuses the preceding returned
cache, selects its actual minimum and applies the public full-graph NRM update. -/
noncomputable def nrmCachedWordLaw {n : Nat} (rates : Nat → Fin (n + 1) → ℝ)
    (marks : Nat → Fin (n + 1)) : (k : Nat) → Measure ((Fin k → ℝ) × (Fin (n + 1) → ℝ))
  | 0 => (Measure.dirac (fun j => Fin.elim0 j)).prod (Measure.pi (fun j => expMeasure (rates 0 j)))
  | k + 1 => (nrmHistoryStep (rates k) (rates (k + 1)) (marks k)
      (nrmCachedWordLaw rates marks k)).map
        (fun p => (prependHoldingTime (p.1, p.2.1), p.2.2))

/-- Finite end-to-end cache composition on every reaction word, with arbitrary
state-dependent positive rates along that word. The theorem is about the iterated
operational cache maps, not a fresh race at each step. -/
theorem nrm_cached_word_law {n : Nat} (rates : Nat → Fin (n + 1) → ℝ)
    (hr : ∀ k j, 0 < rates k j) (marks : Nat → Fin (n + 1)) (k : Nat) :
    nrmCachedWordLaw rates marks k =
      (targetWordLaw rates marks k).prod (Measure.pi (fun j => expMeasure (rates k j))) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    let : IsFiniteMeasure (targetWordLaw rates marks k) := targetWordLaw_finite rates hr marks k
    let (j : Fin (n + 1)) : IsProbabilityMeasure (expMeasure (rates (k + 1) j)) :=
      isProbabilityMeasure_expMeasure (hr (k + 1) j)
    have hA : 0 < ∑ j, rates k j := Finset.sum_pos (fun j _ => hr k j) Finset.univ_nonempty
    let : IsProbabilityMeasure (expMeasure (∑ j, rates k j)) := isProbabilityMeasure_expMeasure hA
    rw [nrmCachedWordLaw, ih, nrm_history_step_factorization _ _ _ (hr k) (hr (k + 1)),
      ← Measure.prod_smul_left]
    exact history_prod_append _ _ _ _ (measurable_prependHoldingTime k)

/-- Marginal law of all holding times produced by the persistent NRM cache. -/
theorem nrm_cached_word_marginal {n : Nat} (rates : Nat → Fin (n + 1) → ℝ)
    (hr : ∀ k j, 0 < rates k j) (marks : Nat → Fin (n + 1)) (k : Nat) :
    (nrmCachedWordLaw rates marks k).map Prod.fst = targetWordLaw rates marks k := by
  let (j : Fin (n + 1)) : IsProbabilityMeasure (expMeasure (rates k j)) :=
    isProbabilityMeasure_expMeasure (hr k j)
  rw [nrm_cached_word_law rates hr marks k, Measure.map_fst_prod, measure_univ, one_smul]

end JumpProcessesLean.Proofs
