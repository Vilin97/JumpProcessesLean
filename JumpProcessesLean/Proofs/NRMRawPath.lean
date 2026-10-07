import JumpProcessesLean.Proofs.AbsoluteExecution

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

abbrev NRMRawInput (n k : Nat) := (Fin (n + 1) → ℝ) × (Fin k → Fin (n + 1) → ℝ)

noncomputable def nrmRawExtend {n k : Nat}
    (p : NRMRawInput n k × (Fin (n + 1) → ℝ)) : NRMRawInput n (k + 1) :=
  (p.1.1, Fin.cases p.2 p.1.2)

lemma measurable_nrmRawExtend (n k : Nat) : Measurable (@nrmRawExtend n k) := by
  apply Measurable.prodMk (by fun_prop)
  apply Measurable.of_eval
  intro j
  cases j using Fin.cases <;> simp only [nrmRawExtend, Fin.cases_zero, Fin.cases_succ] <;> fun_prop

/-- Keeps every primitive uniform while calculating the actual normalized cache
formula. Fresh input rows are stored most recent first. -/
noncomputable def nrmRawHistory {n : Nat} (rates : Nat → Fin (n + 1) → ℝ)
    (marks : Nat → Fin (n + 1)) : (k : Nat) → NRMRawInput n k →
      ((Fin k → ℝ) × (Fin (n + 1) → ℝ))
  | 0, p => (fun j => Fin.elim0 j, fun j => exponentialClock (ghostRate (rates 0 j)) (p.1 j))
  | k + 1, p =>
    let previous := nrmRawHistory rates marks k (p.1, Fin.tail p.2)
    (prependHoldingTime (previous.1, previous.2 (marks k)),
      maskedResidual (rates k) (rates (k + 1)) (marks k) previous.2 (p.2 0))

lemma measurable_nrmRawHistory {n : Nat} (rates : Nat → Fin (n + 1) → ℝ)
    (marks : Nat → Fin (n + 1)) (k : Nat) : Measurable (nrmRawHistory rates marks k) := by
  induction k with
  | zero =>
    apply Measurable.prodMk (by fun_prop)
    apply Measurable.of_eval
    intro j
    unfold exponentialClock
    fun_prop
  | succ k ih =>
    have hp : Measurable (fun p : NRMRawInput n (k + 1) =>
        nrmRawHistory rates marks k (p.1, Fin.tail p.2)) := ih.comp (by fun_prop)
    apply Measurable.prodMk
    · exact (measurable_prependHoldingTime k).comp
        (hp.fst.prodMk ((measurable_pi_apply (marks k)).comp hp.snd))
    · apply Measurable.of_eval
      intro j
      simp only [nrmRawHistory, maskedResidual]
      split_ifs <;> (try unfold exponentialClock) <;> fun_prop

noncomputable def nrmRawPathLaw {n : Nat} (rates : Nat → Fin (n + 1) → ℝ)
    (marks : Nat → Fin (n + 1)) : (k : Nat) → Measure (NRMRawInput n k)
  | 0 => (Measure.pi (fun _ : Fin (n + 1) => unitUniform)).map
      (fun u => (u, fun j : Fin 0 => Fin.elim0 j))
  | k + 1 => (((nrmRawPathLaw rates marks k).prod
      (Measure.pi (fun _ : Fin (n + 1) => unitUniform))).restrict
        {p | ((nrmRawHistory rates marks k p.1).2, p.2) ∈ maskedStepBranch (rates k) (marks k)}).map
          nrmRawExtend

lemma nrmRawPathLaw_finite {n : Nat} (rates : Nat → Fin (n + 1) → ℝ)
    (marks : Nat → Fin (n + 1)) (k : Nat) : IsFiniteMeasure (nrmRawPathLaw rates marks k) := by
  induction k with
  | zero => unfold nrmRawPathLaw; infer_instance
  | succ k ih =>
    let : IsFiniteMeasure (nrmRawPathLaw rates marks k) := ih
    unfold nrmRawPathLaw
    infer_instance

lemma masked_history_append_formula {n k : Nat} (old new : Fin (n + 1) → ℝ)
    (hn : ∀ j, 0 ≤ new j) (i : Fin (n + 1))
    (μ : Measure ((Fin k → ℝ) × (Fin (n + 1) → ℝ))) [SFinite μ] :
    (maskedHistoryStep old new i μ).map
      (fun p => (prependHoldingTime (p.1, p.2.1), p.2.2)) =
      ((μ.prod (Measure.pi (fun _ : Fin (n + 1) => unitUniform))).restrict
        {p | (p.1.2, p.2) ∈ maskedStepBranch old i}).map
          (fun p => (prependHoldingTime (p.1.1, p.1.2 i), maskedResidual old new i p.1.2 p.2)) := by
  let branch : Set ((((Fin k → ℝ) × (Fin (n + 1) → ℝ))) × (Fin (n + 1) → ℝ)) :=
    {p | (p.1.2, p.2) ∈ maskedStepBranch old i}
  let ρ := (μ.prod (Measure.pi (fun _ : Fin (n + 1) => unitUniform))).restrict branch
  let f := fun p : (((Fin k → ℝ) × (Fin (n + 1) → ℝ))) × (Fin (n + 1) → ℝ) =>
    (p.1.1, maskedStepPair old new i (p.1.2, p.2))
  let g := fun p : (((Fin k → ℝ) × (Fin (n + 1) → ℝ))) × (Fin (n + 1) → ℝ) =>
    (p.1.1, (p.1.2 i, maskedResidual old new i p.1.2 p.2))
  have hg : Measurable g := by
    have hp : Measurable (fun p : (((Fin k → ℝ) × (Fin (n + 1) → ℝ))) ×
        (Fin (n + 1) → ℝ) => (p.1.2, p.2)) := by fun_prop
    exact measurable_fst.fst.prodMk ((measurable_maskedStepPair_formula old new i).comp hp)
  have hu := (Measure.quasiMeasurePreserving_snd (μ := μ)
    (ν := Measure.pi (fun _ : Fin (n + 1) => unitUniform))).tendsto_ae.eventually uniform_vector_ae_mem
  have hfg : f =ᵐ[ρ] g := by
    filter_upwards [ae_restrict_mem (by unfold branch maskedStepBranch; measurability),
      ae_restrict_of_ae hu] with p hp hup
    unfold f g maskedStepPair
    rw [maskedActualResidual_executes old new hn i p.1.2 p.2
      (fun j hj => if h : j = i then by simp [h] else (hp.2.2 j h hj).le) hup]
  unfold maskedHistoryStep
  change (ρ.map f).map _ = _
  have ha : Measurable (fun p : (Fin k → ℝ) × (ℝ × (Fin (n + 1) → ℝ)) =>
      (prependHoldingTime (p.1, p.2.1), p.2.2)) :=
    ((measurable_prependHoldingTime k).comp (measurable_fst.prodMk measurable_snd.fst)).prodMk measurable_snd.snd
  rw [Measure.map_congr hfg, Measure.map_map ha hg]
  rfl

/-- The finite primitive-input construction pushes forward to the iterated ACTUAL
NRM cache law. This retains random tapes until after the execution calculation. -/
theorem nrm_raw_path_pushforward {n : Nat} (rates : Nat → Fin (n + 1) → ℝ)
    (hr : ∀ l j, 0 ≤ rates l j) (marks : Nat → Fin (n + 1)) (k : Nat) :
    (nrmRawPathLaw rates marks k).map (nrmRawHistory rates marks k) =
      maskedCachedWordLaw rates marks k := by
  induction k with
  | zero =>
    rw [nrmRawPathLaw, Measure.map_map (measurable_nrmRawHistory rates marks 0) (by fun_prop)]
    unfold maskedCachedWordLaw
    rw [Measure.dirac_prod, ghostCache, ← race_uniform_input_law (fun j => ghostRate (rates 0 j)) (fun j => ghostRate_positive _),
      Measure.map_map measurable_prodMk_left (by
        apply Measurable.of_eval
        intro j
        exact (measurable_exponentialClock _).comp (measurable_pi_apply j))]
    rfl
  | succ k ih =>
    let : IsFiniteMeasure (nrmRawPathLaw rates marks k) := nrmRawPathLaw_finite rates marks k
    let : IsFiniteMeasure (maskedCachedWordLaw rates marks k) := by
      rw [← ih]
      infer_instance
    have hhist := measurable_nrmRawHistory rates marks k
    let U := Measure.pi (fun _ : Fin (n + 1) => unitUniform)
    let F : NRMRawInput n k × (Fin (n + 1) → ℝ) →
        (((Fin k → ℝ) × (Fin (n + 1) → ℝ)) × (Fin (n + 1) → ℝ)) :=
      Prod.map (nrmRawHistory rates marks k) id
    have hF : Measurable F := hhist.prodMap measurable_id
    let S : Set ((((Fin k → ℝ) × (Fin (n + 1) → ℝ))) × (Fin (n + 1) → ℝ)) :=
      {p | (p.1.2, p.2) ∈ maskedStepBranch (rates k) (marks k)}
    have hS : MeasurableSet S := by unfold S maskedStepBranch; measurability
    have hprod : ((nrmRawPathLaw rates marks k).prod U).map F =
        ((nrmRawPathLaw rates marks k).map (nrmRawHistory rates marks k)).prod U := by
      rw [show U = U.map id from Measure.map_id.symm, Measure.map_prod_map _ _ hhist measurable_id]
      simp only [Measure.map_id]
      rfl
    have hG : Measurable (fun p : (((Fin k → ℝ) × (Fin (n + 1) → ℝ))) ×
        (Fin (n + 1) → ℝ) => (prependHoldingTime (p.1.1, p.1.2 (marks k)),
          maskedResidual (rates k) (rates (k + 1)) (marks k) p.1.2 p.2)) := by
      have hp : Measurable (fun p : (((Fin k → ℝ) × (Fin (n + 1) → ℝ))) ×
          (Fin (n + 1) → ℝ) => (p.1.2, p.2)) := by fun_prop
      exact ((measurable_prependHoldingTime k).comp
        (measurable_fst.fst.prodMk ((measurable_pi_apply (marks k)).comp measurable_fst.snd))).prodMk
        (((measurable_maskedStepPair_formula (rates k) (rates (k + 1)) (marks k)).comp hp).snd)
    rw [nrmRawPathLaw, Measure.map_map (measurable_nrmRawHistory rates marks (k + 1))
      (measurable_nrmRawExtend n k), maskedCachedWordLaw,
      masked_history_append_formula _ _ (hr (k + 1))]
    rw [← ih, ← hprod, Measure.restrict_map hF hS, Measure.map_map hG hF]
    rfl

theorem nrm_raw_holding_times_law {n : Nat} (rates : Nat → Fin (n + 1) → ℝ)
    (hr : ∀ l j, 0 ≤ rates l j) (marks : Nat → Fin (n + 1)) (k : Nat) :
    (nrmRawPathLaw rates marks k).map (fun p => (nrmRawHistory rates marks k p).1) =
      targetWordLaw rates marks k := by
  change (nrmRawPathLaw rates marks k).map (Prod.fst ∘ nrmRawHistory rates marks k) = _
  rw [← Measure.map_map measurable_fst (measurable_nrmRawHistory rates marks k),
    nrm_raw_path_pushforward rates hr marks k, masked_cached_word_marginal rates hr marks k]

end JumpProcessesLean.Proofs
