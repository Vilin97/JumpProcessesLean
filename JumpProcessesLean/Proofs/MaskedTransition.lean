import JumpProcessesLean.Proofs.MaskedNRM

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

def keepClock {n : Nat} (old new : Fin n → ℝ) (i j : Fin n) : Prop :=
  j ≠ i ∧ 0 < old j ∧ 0 < new j

noncomputable instance {n : Nat} (old new : Fin n → ℝ) (i j : Fin n) :
    Decidable (keepClock old new i j) := Classical.propDecidable _

noncomputable def maskedResidual {n : Nat} (old new : Fin n → ℝ) (i : Fin n)
    (c u : Fin n → ℝ) (j : Fin n) : ℝ :=
  if keepClock old new i j then (old j / new j) * (c j - c i)
  else exponentialClock (ghostRate (new j)) (u j)

noncomputable def maskedStepBranch {n : Nat} (old : Fin n → ℝ) (i : Fin n) :
    Set ((Fin n → ℝ) × (Fin n → ℝ)) :=
  {p | 0 < old i ∧ 0 < p.1 i ∧ ∀ j, j ≠ i → 0 < old j → p.1 i < p.1 j}

noncomputable def maskedTransitionVector {n : Nat} (old new : Fin n → ℝ) (i : Fin n)
    (p : (Fin n → ℝ) × (Fin n → ℝ)) : Fin (n + 1) → ℝ :=
  Fin.cases (p.1 i) (maskedResidual old new i p.1 p.2)

lemma measurable_maskedTransitionVector {n : Nat} (old new : Fin n → ℝ) (i : Fin n) :
    Measurable (maskedTransitionVector old new i) := by
  apply Measurable.of_eval
  intro j
  cases j using Fin.cases with
  | zero => simp only [maskedTransitionVector, Fin.cases_zero]; fun_prop
  | succ j =>
    simp only [maskedTransitionVector, Fin.cases_succ, maskedResidual]
    split_ifs <;> (try unfold exponentialClock) <;> fun_prop

lemma rescaled_tail_iff (a b x y s : ℝ) (ha : 0 < a) (hb : 0 < b) :
    s < (a / b) * (y - x) ↔ x + s * b / a < y := by
  have hdiv : s / (a / b) = s * b / a := by field_simp
  constructor
  · intro h
    have hd : s / (a / b) < y - x := (div_lt_iff₀ (div_pos ha hb)).mpr (by simpa [mul_comm] using h)
    rw [hdiv] at hd
    linarith
  · intro h
    have hd : s / (a / b) < y - x := by rw [hdiv]; linarith
    simpa [mul_comm] using (div_lt_iff₀ (div_pos ha hb)).mp hd

/-- Joint tails through a masked Gibson--Bruck update. Fresh draws for reactivated
channels are independent; unused inactive coordinates integrate to one. -/
theorem masked_transition_tail {n : Nat} (old new : Fin (n + 1) → ℝ)
    (ho : ∀ j, 0 ≤ old j) (i : Fin (n + 1)) (hi : 0 < old i)
    (t : ℝ) (ht : 0 ≤ t) (s : Fin (n + 1) → ℝ) (hs : ∀ j, 0 ≤ s j) :
    ((Measure.pi (fun j => expMeasure (ghostRate (old j)))).prod
      (Measure.pi (fun _ : Fin (n + 1) => unitUniform)))
      {p | t < p.1 i ∧ p ∈ maskedStepBranch old i ∧
        ∀ j, s j < maskedResidual old new i p.1 p.2 j} =
      ENNReal.ofReal ((old i / (∑ j, old j)) * clockSurvival (∑ j, old j) t) *
        ∏ j, ENNReal.ofReal (clockSurvival (ghostRate (new j)) (s j)) := by
  let (j : Fin (n + 1)) : IsProbabilityMeasure (expMeasure (ghostRate (old j))) :=
    isProbabilityMeasure_expMeasure (ghostRate_positive _)
  let δ : Fin n → ℝ := fun j =>
    if keepClock old new i (i.succAbove j) then s (i.succAbove j) * new (i.succAbove j) / old (i.succAbove j)
    else 0
  have hδ : ∀ j, 0 ≤ δ j := by
    intro j; unfold δ; split_ifs with h
    · exact div_nonneg (mul_nonneg (hs _) h.2.2.le) h.2.1.le
    · exact le_refl 0
  let U : Set (Fin (n + 1) → ℝ) := univ.pi (fun j =>
    if keepClock old new i j then univ else exponentialClock (ghostRate (new j)) ⁻¹' Ioi (s j))
  have hset : {p : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) |
        t < p.1 i ∧ p ∈ maskedStepBranch old i ∧
        ∀ j, s j < maskedResidual old new i p.1 p.2 j} =
      maskedRaceRegion old i t δ ×ˢ U := by
    ext p
    simp only [mem_setOf_eq, mem_prod, maskedRaceRegion, maskedStepBranch,
      U, mem_pi, mem_univ, forall_const]
    constructor
    · rintro ⟨hp, hb, hr⟩
      refine ⟨⟨hp, ?_⟩, ?_⟩
      · intro j hj
        by_cases hk : keepClock old new i (i.succAbove j)
        · have hx := hr (i.succAbove j)
          simp only [maskedResidual, hk, ite_true] at hx
          simpa only [δ, hk, ite_true] using
            (rescaled_tail_iff _ _ _ _ _ hk.2.1 hk.2.2).mp hx
        · simpa only [δ, hk, ite_false, add_zero] using hb.2.2 _ (Fin.succAbove_ne i j) hj
      · intro j; by_cases hk : keepClock old new i j
        · simp [hk]
        · simpa only [hk, ite_false, mem_preimage, mem_Ioi, maskedResidual] using hr j
    · rintro ⟨⟨hp, hr⟩, hu⟩
      have hmin : ∀ j, j ≠ i → 0 < old j → p.1 i < p.1 j := by
        intro j hji hj
        obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hji
        have hx := hr k hj
        linarith [hδ k]
      refine ⟨hp, ⟨hi, ht.trans_lt hp, hmin⟩, ?_⟩
      intro j
      by_cases hk : keepClock old new i j
      · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hk.1
        have hx := hr k hk.2.1
        simp only [δ, hk, ite_true] at hx
        simpa only [maskedResidual, hk, ite_true] using
          (rescaled_tail_iff _ _ _ _ _ hk.2.1 hk.2.2).mpr hx
      · simpa only [hk, ite_false, mem_preimage, mem_Ioi, maskedResidual] using hu j
  rw [hset, Measure.prod_prod, masked_race_residual_probability old ho i hi t ht δ hδ,
    Measure.pi_pi]
  have hu (j : Fin (n + 1)) : unitUniform
      (if keepClock old new i j then univ else exponentialClock (ghostRate (new j)) ⁻¹' Ioi (s j)) =
      if keepClock old new i j then 1 else ENNReal.ofReal (clockSurvival (ghostRate (new j)) (s j)) := by
    by_cases hk : keepClock old new i j
    · simp [hk]
    · rw [if_neg hk, if_neg hk,
        ← Measure.map_apply (measurable_exponentialClock _) measurableSet_Ioi,
        exponentialClock_map_uniform _ (ghostRate_positive _),
        exponential_measure_tail _ _ (ghostRate_positive _) (hs j)]
  simp_rw [hu]
  have hold : (∏ j : Fin n, ENNReal.ofReal (clockSurvival (old (i.succAbove j)) (δ j))) =
      ∏ j : Fin (n + 1), if keepClock old new i j then
        ENNReal.ofReal (clockSurvival (ghostRate (new j)) (s j)) else 1 := by
    rw [Fin.prod_univ_succAbove _ i]
    have hki : ¬keepClock old new i i := fun h => h.1 rfl
    simp only [hki, ite_false, one_mul]
    apply Finset.prod_congr rfl
    intro j _
    by_cases hk : keepClock old new i (i.succAbove j)
    · rw [if_pos hk]
      simp only [δ, hk, ite_true, ghostRate_of_positive hk.2.2]
      congr 1
      unfold clockSurvival
      congr 1
      field_simp [hk.2.1.ne']
    · simp [δ, hk, clockSurvival]
  rw [hold]
  rw [mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  by_cases hk : keepClock old new i j <;> simp [hk]

noncomputable def maskedTransitionLaw {n : Nat} (old new : Fin n → ℝ) (i : Fin n) :
    Measure (Fin (n + 1) → ℝ) :=
  (((Measure.pi (fun j => expMeasure (ghostRate (old j)))).prod
    (Measure.pi (fun _ : Fin n => unitUniform))).restrict (maskedStepBranch old i)).map
      (maskedTransitionVector old new i)

lemma uniform_vector_ae_mem {k : Nat} :
    ∀ᵐ u : Fin k → ℝ ∂Measure.pi (fun _ => unitUniform), ∀ j, u j ∈ Ioo 0 1 := by
  rw [ae_all_iff]
  intro j
  exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin k => unitUniform)
    (i := j)).eventually unitUniform_ae_mem

/-- Full Borel joint law of the holding time and masked updated cache, including
activation and deactivation. A disabled winner has zero branch measure. -/
theorem masked_transition_full_law {n : Nat} (old new : Fin (n + 1) → ℝ)
    (ho : ∀ j, 0 ≤ old j) (i : Fin (n + 1)) :
    maskedTransitionLaw old new i = ENNReal.ofReal (old i / (∑ j, old j)) •
      Measure.pi (fun j : Fin (n + 2) => expMeasure
        (Fin.cases (∑ k, old k) (fun k => ghostRate (new k)) j)) := by
  by_cases hi : 0 < old i
  · let (j : Fin (n + 1)) : IsProbabilityMeasure (expMeasure (ghostRate (old j))) :=
      isProbabilityMeasure_expMeasure (ghostRate_positive _)
    have hA : 0 < ∑ j, old j := hi.trans_le
      (Finset.single_le_sum (fun j _ => ho j) (Finset.mem_univ i))
    let R : Fin (n + 2) → ℝ := Fin.cases (∑ k, old k) (fun k => ghostRate (new k))
    have hR : ∀ j, 0 < R j := by
      intro j; cases j using Fin.cases
      · exact hA
      · exact ghostRate_positive _
    let (j : Fin (n + 2)) : IsProbabilityMeasure (expMeasure (R j)) :=
      isProbabilityMeasure_expMeasure (hR j)
    let μ := (Measure.pi (fun j => expMeasure (ghostRate (old j)))).prod
      (Measure.pi (fun _ : Fin (n + 1) => unitUniform))
    have hu : ∀ᵐ p ∂μ, ∀ j, p.2 j ∈ Ioo 0 1 :=
      (Measure.quasiMeasurePreserving_snd (μ := Measure.pi (fun j => expMeasure (ghostRate (old j))))
        (ν := Measure.pi (fun _ : Fin (n + 1) => unitUniform))).tendsto_ae.eventually uniform_vector_ae_mem
    have hb : MeasurableSet (maskedStepBranch old i) := by unfold maskedStepBranch; measurability
    have hm := measurable_maskedTransitionVector old new i
    have hpos : ∀ᵐ x ∂maskedTransitionLaw old new i, ∀ j, 0 < x j := by
      apply (ae_map_iff hm.aemeasurable (by measurability)).mpr
      filter_upwards [ae_restrict_mem hb, ae_restrict_of_ae hu] with p hp hup
      intro j
      cases j using Fin.cases with
      | zero => exact hp.2.1
      | succ j =>
        simp only [maskedTransitionVector, Fin.cases_succ, maskedResidual]
        split_ifs with hk
        · exact mul_pos (div_pos hk.2.1 hk.2.2) (sub_pos.mpr (hp.2.2 j hk.1 hk.2.1))
        · exact div_pos (neg_pos.mpr (log_neg (hup j).1 (hup j).2)) (ghostRate_positive _)
    have hpostarget : ∀ᵐ x ∂(ENNReal.ofReal (old i / (∑ j, old j)) •
        Measure.pi (fun j => expMeasure (R j))), ∀ j, 0 < x j :=
      Measure.ae_smul_measure (exponential_vector_ae_positive R hR) _
    let : IsFiniteMeasure (maskedTransitionLaw old new i) := by unfold maskedTransitionLaw; infer_instance
    apply positive_vector_measure_ext _ _ hpos hpostarget
    intro s hs
    rw [maskedTransitionLaw, Measure.map_apply hm (by measurability),
      Measure.restrict_apply (hm (by measurability))]
    have hset : (maskedTransitionVector old new i ⁻¹' {x | ∀ j, s j < x j}) ∩ maskedStepBranch old i =
        {p | s 0 < p.1 i ∧ p ∈ maskedStepBranch old i ∧
          ∀ j, s j.succ < maskedResidual old new i p.1 p.2 j} := by
      ext p
      simp only [mem_inter_iff, mem_preimage, mem_setOf_eq]
      constructor
      · rintro ⟨hv, hb⟩; exact ⟨hv 0, hb, fun j => hv j.succ⟩
      · rintro ⟨ht, hb, hr⟩
        refine ⟨?_, hb⟩
        intro j; cases j using Fin.cases
        · exact ht
        · exact hr _
    rw [hset, masked_transition_tail old new ho i hi (s 0) (hs 0)
      (fun j => s j.succ) (fun j => hs j.succ), Measure.smul_apply, smul_eq_mul]
    have hrect : {x : Fin (n + 2) → ℝ | ∀ j, s j < x j} =
        univ.pi (fun j => Ioi (s j)) := by ext x; simp
    rw [hrect, Measure.pi_pi]
    conv_rhs => rw [Fin.prod_univ_succ]
    simp only [R, Fin.cases_zero, Fin.cases_succ]
    rw [exponential_measure_tail _ _ hA (hs 0)]
    simp_rw [exponential_measure_tail _ _ (ghostRate_positive _) (hs _)]
    rw [ENNReal.ofReal_mul (div_nonneg hi.le hA.le)]
    ring
  · have hz : old i = 0 := le_antisymm (not_lt.mp hi) (ho i)
    have hb : maskedStepBranch old i = ∅ := by ext p; simp [maskedStepBranch, hi]
    simp [maskedTransitionLaw, hb, hz]

/-- The residual vector observed from the public nullable-clock update. Inactive
coordinates remain unused ghost values; the executable state still stores `none`. -/
noncomputable def maskedActualResidual {n : Nat} (old new : Fin n → ℝ) (i : Fin n)
    (c u : Fin n → ℝ) : Fin n → ℝ :=
  match nrmUpdate realArithmetic (tapeSource ℝ)
    ⟨Array.ofFn old, Array.ofFn (fun j => if 0 < old j then some (c j) else none)⟩
    (Array.ofFn new) i.val (c i) (List.range n).toArray
    ⟨[], nrmFreshExponentials old new u 0 i.val⟩ with
  | .ok (state, _) => fun j => if 0 < new j then
      (state.clocks[j.val]!).getD (c i) - c i
      else exponentialClock (ghostRate (new j)) (u j)
  | _ => fun _ => 0

theorem maskedActualResidual_executes {n : Nat} (old new : Fin n → ℝ)
    (hn : ∀ j, 0 ≤ new j) (i : Fin n) (c u : Fin n → ℝ)
    (hmin : ∀ j, 0 < old j → c i ≤ c j) (hu : ∀ j, u j ∈ Ioo 0 1) :
    maskedActualResidual old new i c u = maskedResidual old new i c u := by
  have hex := nrmUpdate_uniform_executes old new c u hn hu (c i) hmin i [] []
  simp only [List.append_nil] at hex
  unfold maskedActualResidual
  rw [hex]
  funext j
  have hget : (Array.ofFn (fun k => nrmUpdatedClock (old k) (new k) (c k) (u k)
      (c i) k.val i.val))[j.val]! = nrmUpdatedClock (old j) (new j) (c j) (u j) (c i) j.val i.val := by
    simp [j.isLt]
  dsimp only
  by_cases hnj : 0 < new j
  · simp only [hnj, ite_true]
    rw [hget]
    by_cases hji : j = i
    · subst j
      simp [nrmUpdatedClock, hnj, maskedResidual, keepClock, ghostRate_of_positive hnj]
    · have hv : j.val ≠ i.val := fun h => hji (Fin.ext h)
      by_cases hoj : 0 < old j
      · simp [nrmUpdatedClock, hnj, hoj, hv, maskedResidual, keepClock, hji,
          rescaleClock, realArithmetic]
      · simp [nrmUpdatedClock, hnj, hoj, hv, maskedResidual, keepClock, hji,
          ghostRate_of_positive hnj]
  · simp [hnj, maskedResidual, keepClock]

end JumpProcessesLean.Proofs
