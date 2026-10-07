import JumpProcessesLean.Proofs.NRMTransitionLaw

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

/-- Inactive coordinates are unused ghost variables with a probability law. They
never become finite sentinel clocks in the executable NRM state. -/
noncomputable def ghostRate (a : ℝ) : ℝ := if 0 < a then a else 1

lemma ghostRate_positive (a : ℝ) : 0 < ghostRate a := by
  unfold ghostRate
  split
  · assumption
  · norm_num

lemma ghostRate_of_positive {a : ℝ} (ha : 0 < a) : ghostRate a = a := if_pos ha

noncomputable def maskedRaceRegion {n : Nat} (rates : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) (t : ℝ) (residual : Fin n → ℝ) : Set (Fin (n + 1) → ℝ) :=
  {c | t < c i ∧ ∀ j, 0 < rates (i.succAbove j) → c i + residual j < c (i.succAbove j)}

/-- Zero-rate clocks are absent from the race. Integration over their unused ghost
coordinates contributes mass one, rather than an artificial positive hazard. -/
theorem masked_race_residual_probability {n : Nat} (rates : Fin (n + 1) → ℝ)
    (hr : ∀ i, 0 ≤ rates i) (i : Fin (n + 1)) (hi : 0 < rates i) (t : ℝ) (ht : 0 ≤ t)
    (residual : Fin n → ℝ) (hs : ∀ j, 0 ≤ residual j) :
    (Measure.pi (fun j => expMeasure (ghostRate (rates j)))) (maskedRaceRegion rates i t residual) =
      ENNReal.ofReal ((rates i / (∑ j, rates j)) * clockSurvival (∑ j, rates j) t) *
        ∏ j, ENNReal.ofReal (clockSurvival (rates (i.succAbove j)) (residual j)) := by
  let (j : Fin (n + 1)) : IsProbabilityMeasure (expMeasure (ghostRate (rates j))) :=
    isProbabilityMeasure_expMeasure (ghostRate_positive _)
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  let region : Set (ℝ × (Fin n → ℝ)) :=
    {p | t < p.1 ∧ ∀ j, 0 < rates (i.succAbove j) → p.1 + residual j < p.2 j}
  have hm : MeasurableSet region := by unfold region; measurability
  have he : e ⁻¹' region = maskedRaceRegion rates i t residual := by
    ext c
    simp [e, region, maskedRaceRegion, MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv, Fin.removeNth]
  rw [← he, (measurePreserving_piFinSuccAbove (fun j => expMeasure (ghostRate (rates j))) i).measure_preimage
    hm.nullMeasurableSet, Measure.prod_apply hm]
  have hinner (x : ℝ) :
      (Measure.pi (fun j : Fin n => expMeasure (ghostRate (rates (i.succAbove j)))))
        (Prod.mk x ⁻¹' region) =
      (Ioi t).indicator (fun x => ∏ j : Fin n,
        (expMeasure (ghostRate (rates (i.succAbove j))))
          (if 0 < rates (i.succAbove j) then Ioi (x + residual j) else univ)) x := by
    by_cases hx : t < x
    · have hset : Prod.mk x ⁻¹' region =
          univ.pi (fun j : Fin n => if 0 < rates (i.succAbove j) then Ioi (x + residual j) else univ) := by
        ext c
        simp only [mem_preimage, region, mem_setOf_eq, hx, true_and, mem_pi, mem_univ, forall_const]
        apply forall_congr'
        intro j
        by_cases h : 0 < rates (i.succAbove j) <;> simp [h]
      rw [hset, Measure.pi_pi]
      simp [hx]
    · have hset : Prod.mk x ⁻¹' region = ∅ := by ext c; simp [region, hx]
      simp [hset, hx]
  simp_rw [hinner]
  rw [lintegral_indicator measurableSet_Ioi]
  have hA : 0 < ∑ j, rates j := hi.trans_le (Finset.single_le_sum (fun j _ => hr j) (Finset.mem_univ i))
  have hterm (x : ℝ) (hx : x ∈ Ioi t) :
      (∏ j : Fin n, (expMeasure (ghostRate (rates (i.succAbove j))))
          (if 0 < rates (i.succAbove j) then Ioi (x + residual j) else univ)) =
      ∏ j : Fin n, ENNReal.ofReal (clockSurvival (rates (i.succAbove j)) (x + residual j)) := by
    apply Finset.prod_congr rfl
    intro j _
    by_cases hp : 0 < rates (i.succAbove j)
    · simp only [hp, ite_true, ghostRate_of_positive hp]
      exact exponential_measure_tail _ _ hp (by have hxt : t < x := hx; linarith [hs j])
    · have hz : rates (i.succAbove j) = 0 := le_antisymm (not_lt.mp hp) (hr _)
      let : IsProbabilityMeasure (expMeasure (ghostRate 0)) := isProbabilityMeasure_expMeasure (ghostRate_positive 0)
      simp [hp, hz, clockSurvival]
  rw [setLIntegral_congr_fun measurableSet_Ioi hterm]
  rw [ghostRate_of_positive hi]
  change (∫⁻ x in Ioi t, ∏ j : Fin n,
    ENNReal.ofReal (clockSurvival (rates (i.succAbove j)) (x + residual j))
    ∂volume.withDensity (exponentialPDF (rates i))) = _
  rw [setLIntegral_withDensity_eq_setLIntegral_mul volume (f := exponentialPDF (rates i))
    (by exact (measurable_exponentialPDFReal _).ennreal_ofReal) (by unfold clockSurvival; fun_prop) measurableSet_Ioi]
  let C : ℝ := ∏ j : Fin n, clockSurvival (rates (i.succAbove j)) (residual j)
  have hC : 0 ≤ C := Finset.prod_nonneg (fun j _ => (exp_pos _).le)
  have hadd (a x y : ℝ) : clockSurvival a (x + y) = clockSurvival a x * clockSurvival a y := by
    unfold clockSurvival; rw [← exp_add]; congr 1; ring
  have hd (x : ℝ) (hx : x ∈ Ioi t) :
      exponentialPDF (rates i) x * (∏ j : Fin n,
        ENNReal.ofReal (clockSurvival (rates (i.succAbove j)) (x + residual j))) =
      ENNReal.ofReal ((rates i / (∑ j, rates j)) * C) * exponentialPDF (∑ j, rates j) x := by
    have hx0 : 0 ≤ x := ht.trans (le_of_lt hx)
    have hp := ENNReal.ofReal_prod_of_nonneg (s := Finset.univ)
      (f := fun j : Fin n => clockSurvival (rates (i.succAbove j)) (x + residual j))
      (fun j _ => (exp_pos _).le)
    rw [exponentialPDF_of_nonneg hx0, exponentialPDF_of_nonneg hx0, ← hp,
      ← ENNReal.ofReal_mul (mul_nonneg hi.le (exp_pos _).le),
      ← ENNReal.ofReal_mul (mul_nonneg (div_nonneg hi.le hA.le) hC)]
    congr 1
    simp_rw [hadd]
    rw [Finset.prod_mul_distrib]
    change rates i * exp (-(rates i * x)) *
      ((∏ j : Fin n, exp (-(rates (i.succAbove j) * x))) * C) = _
    rw [← exp_sum]
    simp only [Finset.sum_neg_distrib, ← Finset.sum_mul]
    have hpow : exp (-(rates i * x)) * exp (-((∑ j : Fin n, rates (i.succAbove j)) * x)) =
        exp (-((∑ j, rates j) * x)) := by
      rw [← exp_add, Fin.sum_univ_succAbove _ i]
      congr 1; ring
    calc
      _ = rates i * (exp (-(rates i * x)) *
        exp (-((∑ j : Fin n, rates (i.succAbove j)) * x))) * C := by ring
      _ = rates i * exp (-((∑ j, rates j) * x)) * C := by rw [hpow]
      _ = _ := by field_simp <;> ring
  simp only [Pi.mul_apply]
  rw [setLIntegral_congr_fun measurableSet_Ioi hd,
    lintegral_const_mul _ (by exact (measurable_exponentialPDFReal _).ennreal_ofReal)]
  rw [← withDensity_apply _ measurableSet_Ioi]
  change ENNReal.ofReal ((rates i / (∑ j, rates j)) * C) * expMeasure (∑ j, rates j) (Ioi t) = _
  rw [exponential_measure_tail _ t hA ht]
  rw [ENNReal.ofReal_mul (div_nonneg hi.le hA.le),
    ENNReal.ofReal_mul (div_nonneg hi.le hA.le),
    ← ENNReal.ofReal_prod_of_nonneg (s := Finset.univ)
      (f := fun j : Fin n => clockSurvival (rates (i.succAbove j)) (residual j)) (fun j _ => (exp_pos _).le)]
  change ENNReal.ofReal (rates i / (∑ j, rates j)) * ENNReal.ofReal C *
      ENNReal.ofReal (clockSurvival (∑ j, rates j) t) =
    (ENNReal.ofReal (rates i / (∑ j, rates j)) * ENNReal.ofReal (clockSurvival (∑ j, rates j) t)) * ENNReal.ofReal C
  ring

end JumpProcessesLean.Proofs
