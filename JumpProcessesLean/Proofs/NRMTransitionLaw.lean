import JumpProcessesLean.Proofs.NRMUpdate
import JumpProcessesLean.Proofs.RealSamplerLaws

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

lemma countablySpanning_real_Ioi : IsCountablySpanning (range (Ioi : ℝ → Set ℝ)) := by
  refine ⟨fun k => Ioi (-(k : ℝ)), fun k => ⟨-(k : ℝ), rfl⟩, ?_⟩
  ext x
  simp only [mem_iUnion, mem_Ioi, mem_univ, iff_true]
  obtain ⟨k, hk⟩ := exists_nat_gt (-x)
  exact ⟨k, by linarith⟩

/-- Nonnegative joint-tail tests determine a finite measure supported on strictly
positive finite vectors. This turns residual tail invariants into full measure laws. -/
theorem positive_vector_measure_ext {ι : Type} [Fintype ι]
    (μ ν : Measure (ι → ℝ)) [IsFiniteMeasure μ]
    (hμ : ∀ᵐ x ∂μ, ∀ j, 0 < x j) (hν : ∀ᵐ x ∂ν, ∀ j, 0 < x j)
    (htail : ∀ s : ι → ℝ, (∀ j, 0 ≤ s j) →
      μ {x | ∀ j, s j < x j} = ν {x | ∀ j, s j < x j}) : μ = ν := by
  let C : Set (Set ℝ) := range Ioi
  have hgen : (MeasurableSpace.pi : MeasurableSpace (ι → ℝ)) =
      MeasurableSpace.generateFrom (univ.pi '' univ.pi (fun _ : ι => C)) := by
    apply (generateFrom_eq_pi (C := fun _ : ι => C) _ (fun _ => countablySpanning_real_Ioi)).symm
    intro j
    exact (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Ioi ℝ)).symm
  have hrect : ∀ s : ι → ℝ,
      μ {x | ∀ j, s j < x j} = ν {x | ∀ j, s j < x j} := by
    intro s
    have hchange (ρ : Measure (ι → ℝ)) (hρ : ∀ᵐ x ∂ρ, ∀ j, 0 < x j) :
        {x | ∀ j, s j < x j} =ᵐ[ρ] {x | ∀ j, max 0 (s j) < x j} := by
      filter_upwards [hρ] with x hx
      apply propext
      simp only [mem_setOf_eq, max_lt_iff]
      constructor
      · intro h j; exact ⟨hx j, h j⟩
      · intro h j; exact (h j).2
    rw [measure_congr (hchange μ hμ), measure_congr (hchange ν hν)]
    exact htail _ (fun j => le_max_left _ _)
  apply ext_of_generate_finite _ hgen (IsPiSystem.pi (fun _ => isPiSystem_Ioi))
  · rintro _ ⟨sides, hs, rfl⟩
    have hex : ∀ j, ∃ t : ℝ, Ioi t = sides j := fun j => hs j (mem_univ j)
    choose s hside using hex
    have heq : sides = fun j => Ioi (s j) := by funext j; exact (hside j).symm
    rw [heq]
    have hset : univ.pi (fun j => Ioi (s j)) = {x : ι → ℝ | ∀ j, s j < x j} := by
      ext x; simp
    rw [hset]
    exact hrect s
  · have hu (ρ : Measure (ι → ℝ)) (hρ : ∀ᵐ x ∂ρ, ∀ j, 0 < x j) :
        ρ univ = ρ {x | ∀ j, 0 < x j} := by
      apply measure_congr
      filter_upwards [hρ] with x hx
      simp [hx]
    rw [hu μ hμ, hu ν hν]
    exact htail (fun _ => 0) (fun _ => le_refl 0)

noncomputable def nrmTransitionVector {n : Nat} (old new : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) (p : (Fin (n + 1) → ℝ) × ℝ) : Fin (n + 2) → ℝ :=
  Fin.cases (p.1 i) (fun j => if j = i then exponentialClock (new j) p.2 else
    rescaleClock realArithmetic (p.1 i) (old j) (new j) (p.1 j) - p.1 i)

lemma measurable_nrmTransitionVector {n : Nat} (old new : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) : Measurable (nrmTransitionVector old new i) := by
  apply Measurable.of_eval
  intro j
  cases j using Fin.cases with
  | zero => simp only [nrmTransitionVector, Fin.cases_zero]; fun_prop
  | succ j =>
    simp only [nrmTransitionVector, Fin.cases_succ]
    by_cases h : j = i
    · simp only [h, ite_true]; unfold exponentialClock; fun_prop
    · simp only [h, ite_false]; unfold rescaleClock realArithmetic; fun_prop

/-- Joint law of the event time and complete returned residual cache on a fixed winner
branch. The transition vector is proved below to be the actual NRM update's output. -/
noncomputable def nrmTransitionLaw {n : Nat} (old new : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) : Measure (Fin (n + 2) → ℝ) :=
  (((Measure.pi (fun j => expMeasure (old j))).prod unitUniform).restrict
    {p | 0 < p.1 i ∧ ∀ j, j ≠ i → p.1 i < p.1 j}).map (nrmTransitionVector old new i)

lemma exponential_vector_ae_positive {k : Nat} (rates : Fin k → ℝ)
    (hr : ∀ j, 0 < rates j) :
    ∀ᵐ x : Fin k → ℝ ∂Measure.pi (fun j => expMeasure (rates j)), ∀ j, 0 < x j := by
  let (j : Fin k) : IsProbabilityMeasure (expMeasure (rates j)) := isProbabilityMeasure_expMeasure (hr j)
  rw [ae_all_iff]
  intro j
  exact (Measure.tendsto_eval_ae_ae (μ := fun j : Fin k => expMeasure (rates j))
    (i := j)).eventually (expMeasure_ae_positive (rates j) (hr j))

theorem nrm_transition_full_law {n : Nat} (old new : Fin (n + 1) → ℝ)
    (ho : ∀ j, 0 < old j) (hn : ∀ j, 0 < new j) (i : Fin (n + 1)) :
    nrmTransitionLaw old new i = ENNReal.ofReal (old i / (∑ j, old j)) •
      Measure.pi (fun j : Fin (n + 2) => expMeasure (Fin.cases (∑ k, old k) new j)) := by
  let (j : Fin (n + 1)) : IsProbabilityMeasure (expMeasure (old j)) := isProbabilityMeasure_expMeasure (ho j)
  have hA : 0 < ∑ j, old j := Finset.sum_pos (fun j _ => ho j) Finset.univ_nonempty
  have htarget : ∀ j : Fin (n + 2), (0 : ℝ) < Fin.cases (∑ k, old k) new j := by
    intro j; cases j using Fin.cases <;> simp [hA, hn]
  let (j : Fin (n + 2)) : IsProbabilityMeasure (expMeasure (Fin.cases (∑ k, old k) new j)) :=
    isProbabilityMeasure_expMeasure (htarget j)
  let μ := (Measure.pi (fun j => expMeasure (old j))).prod unitUniform
  let branch : Set ((Fin (n + 1) → ℝ) × ℝ) :=
    {p | 0 < p.1 i ∧ ∀ j, j ≠ i → p.1 i < p.1 j}
  have hbranch : MeasurableSet branch := by unfold branch; measurability
  have hmap : Measurable (nrmTransitionVector old new i) := measurable_nrmTransitionVector old new i
  have hu : ∀ᵐ p ∂μ, p.2 ∈ Ioo 0 1 :=
    (measurePreserving_snd (μ := Measure.pi (fun j => expMeasure (old j)))
      (ν := unitUniform)).quasiMeasurePreserving.tendsto_ae.eventually unitUniform_ae_mem
  have hpos : ∀ᵐ x ∂nrmTransitionLaw old new i, ∀ j, 0 < x j := by
    apply (ae_map_iff hmap.aemeasurable (by measurability)).mpr
    filter_upwards [ae_restrict_mem hbranch, ae_restrict_of_ae hu] with p hp hup
    intro j
    cases j using Fin.cases with
    | zero => exact hp.1
    | succ j =>
      simp only [nrmTransitionVector, Fin.cases_succ]
      by_cases h : j = i
      · simp only [h, ite_true]
        exact div_pos (neg_pos.mpr (log_neg hup.1 hup.2)) (hn i)
      · simp only [h, ite_false]
        simp only [rescaleClock, realArithmetic]
        nlinarith [mul_pos (div_pos (ho j) (hn j)) (sub_pos.mpr (hp.2 j h))]
  have hposTarget : ∀ᵐ x ∂(ENNReal.ofReal (old i / (∑ j, old j)) •
      Measure.pi (fun j : Fin (n + 2) => expMeasure (Fin.cases (∑ k, old k) new j))),
      ∀ j, 0 < x j := by
    have hp := exponential_vector_ae_positive (Fin.cases (∑ k, old k) new) htarget
    exact Measure.ae_smul_measure hp _
  let : IsFiniteMeasure (nrmTransitionLaw old new i) := by unfold nrmTransitionLaw; infer_instance
  apply positive_vector_measure_ext _ _ hpos hposTarget
  intro s hs
  rw [nrmTransitionLaw, Measure.map_apply hmap (by measurability),
    Measure.restrict_apply (hmap (by measurability))]
  have heq : (nrmTransitionVector old new i ⁻¹' {x | ∀ j, s j < x j}) ∩ branch =ᵐ[μ]
      {p | s 0 < p.1 i ∧ (∀ j, j ≠ i → p.1 i < p.1 j) ∧
        ∀ j, s j.succ < nrmActualResidual old new i p.1 p.2 j} := by
    filter_upwards [hu] with p hup
    apply propext
    constructor
    · rintro ⟨hvec, hb⟩
      have hex := nrmActualResidual_executes old new ho hn i p.1
        (fun j => if h : j = i then by simp [h] else (hb.2 j h).le) p.2 hup
      refine ⟨hvec 0, hb.2, ?_⟩
      rw [hex]
      intro j; exact hvec j.succ
    · rintro ⟨ht, hmin, hres⟩
      have hex := nrmActualResidual_executes old new ho hn i p.1
        (fun j => if h : j = i then by simp [h] else (hmin j h).le) p.2 hup
      rw [hex] at hres
      refine ⟨?_, ⟨(hs 0).trans_lt ht, hmin⟩⟩
      intro j
      cases j using Fin.cases
      · exact ht
      · exact hres _
  change μ ((nrmTransitionVector old new i ⁻¹' {x | ∀ j, s j < x j}) ∩ branch) = _
  rw [measure_congr heq, nrm_operational_update_invariant old new ho hn i (s 0) (hs 0)
    (fun j => s j.succ) (fun j => hs j.succ), Measure.smul_apply, smul_eq_mul]
  have hset : {x : Fin (n + 2) → ℝ | ∀ j, s j < x j} = univ.pi (fun j => Ioi (s j)) := by
    ext x; simp
  rw [hset, Measure.pi_pi]
  conv_rhs => rw [Fin.prod_univ_succ]
  simp only [Fin.cases_zero, Fin.cases_succ]
  rw [exponential_measure_tail _ _ hA (hs 0)]
  have he (j : Fin (n + 1)) := exponential_measure_tail (new j) (s j.succ) (hn j) (hs j.succ)
  simp_rw [he]
  rw [ENNReal.ofReal_mul (div_nonneg (ho i).le hA.le)]
  ring

noncomputable def nrmActualTransitionLaw {n : Nat} (old new : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) : Measure (Fin (n + 2) → ℝ) :=
  (((Measure.pi (fun j => expMeasure (old j))).prod unitUniform).restrict
    {p | 0 < p.1 i ∧ ∀ j, j ≠ i → p.1 i < p.1 j}).map
      (fun p => Fin.cases (p.1 i) (nrmActualResidual old new i p.1 p.2))

/-- Full joint pushforward law of the actual public NRM update on a winning branch. -/
theorem nrm_actual_transition_full_law {n : Nat} (old new : Fin (n + 1) → ℝ)
    (ho : ∀ j, 0 < old j) (hn : ∀ j, 0 < new j) (i : Fin (n + 1)) :
    nrmActualTransitionLaw old new i = ENNReal.ofReal (old i / (∑ j, old j)) •
      Measure.pi (fun j : Fin (n + 2) => expMeasure (Fin.cases (∑ k, old k) new j)) := by
  let (j : Fin (n + 1)) : IsProbabilityMeasure (expMeasure (old j)) := isProbabilityMeasure_expMeasure (ho j)
  have hu : ∀ᵐ p : (Fin (n + 1) → ℝ) × ℝ
      ∂(Measure.pi (fun j => expMeasure (old j))).prod unitUniform, p.2 ∈ Ioo 0 1 :=
    (measurePreserving_snd (μ := Measure.pi (fun j => expMeasure (old j)))
      (ν := unitUniform)).quasiMeasurePreserving.tendsto_ae.eventually unitUniform_ae_mem
  have hrefine : nrmActualTransitionLaw old new i = nrmTransitionLaw old new i := by
    unfold nrmActualTransitionLaw nrmTransitionLaw
    apply Measure.map_congr
    filter_upwards [ae_restrict_mem (by measurability), ae_restrict_of_ae hu] with p hp hup
    have hex := nrmActualResidual_executes old new ho hn i p.1
      (fun j => if h : j = i then by simp [h] else (hp.2 j h).le) p.2 hup
    rw [hex]
    rfl
  rw [hrefine]
  exact nrm_transition_full_law old new ho hn i

end JumpProcessesLean.Proofs
