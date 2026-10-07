import JumpProcessesLean.Proofs.Race
import Mathlib.MeasureTheory.Constructions.Pi

namespace JumpProcessesLean.Proofs
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

/-- NRM's independent primitive uniforms, transformed channel by channel. -/
theorem race_uniform_input_law {n : Nat} (rates : Fin n → ℝ) (hr : ∀ i, 0 < rates i) :
    (Measure.pi (fun _ : Fin n => unitUniform)).map
      (fun u i => exponentialClock (rates i) (u i)) =
      Measure.pi (fun i => expMeasure (rates i)) := by
  let (i : Fin n) : IsProbabilityMeasure (expMeasure (rates i)) := isProbabilityMeasure_expMeasure (hr i)
  have he (i : Fin n) := exponentialClock_map_uniform (rates i) (hr i)
  have (i : Fin n) : SigmaFinite (unitUniform.map (exponentialClock (rates i))) := by
    rw [he i]; infer_instance
  rw [Measure.pi_map_pi (fun i => (measurable_exponentialClock _).aemeasurable)]
  simp_rw [he]

/-- Race branch with arbitrary lower thresholds on the surviving residual clocks. -/
def raceRegion {n : Nat} (i : Fin (n + 1)) (t : ℝ) (residual : Fin n → ℝ) :
    Set (Fin (n + 1) → ℝ) :=
  {c | t < c i ∧ ∀ j, c i + residual j < c (i.succAbove j)}

/-- The winning clock and ALL residual clocks have the factorized exponential law.
This derives the memoryless invariant at a random race time from primitive product inputs. -/
theorem race_residual_probability {n : Nat} (rates : Fin (n + 1) → ℝ)
    (hr : ∀ i, 0 < rates i) (i : Fin (n + 1)) (t : ℝ) (ht : 0 ≤ t)
    (residual : Fin n → ℝ) (hs : ∀ j, 0 ≤ residual j) :
    (Measure.pi (fun j => expMeasure (rates j))) (raceRegion i t residual) =
      ENNReal.ofReal ((rates i / (∑ j, rates j)) * clockSurvival (∑ j, rates j) t) *
        ∏ j, ENNReal.ofReal (clockSurvival (rates (i.succAbove j)) (residual j)) := by
  let (j : Fin (n + 1)) : IsProbabilityMeasure (expMeasure (rates j)) :=
    isProbabilityMeasure_expMeasure (hr j)
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  let region : Set (ℝ × (Fin n → ℝ)) :=
    {p | t < p.1 ∧ ∀ j, p.1 + residual j < p.2 j}
  have hm : MeasurableSet region := by
    change MeasurableSet ({p : ℝ × (Fin n → ℝ) | t < p.1} ∩ {p : ℝ × (Fin n → ℝ) | ∀ j, p.1 + residual j < p.2 j})
    apply MeasurableSet.inter (by measurability)
    simp only [ofPred_forall]
    exact MeasurableSet.iInter (fun j => by measurability)
  have he : e ⁻¹' region = raceRegion i t residual := by
    ext c
    simp [e, region, raceRegion, MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv, Fin.removeNth]
  rw [← he, (measurePreserving_piFinSuccAbove (fun j => expMeasure (rates j)) i).measure_preimage
    hm.nullMeasurableSet, Measure.prod_apply hm]
  have hinner (x : ℝ) :
      (Measure.pi (fun j : Fin n => expMeasure (rates (i.succAbove j))))
        (Prod.mk x ⁻¹' region) =
      (Ioi t).indicator (fun x => ∏ j : Fin n,
        expMeasure (rates (i.succAbove j)) (Ioi (x + residual j))) x := by
    by_cases hx : t < x
    · have hset : Prod.mk x ⁻¹' region =
          univ.pi (fun j : Fin n => Ioi (x + residual j)) := by
        ext c; simp [region, hx, Set.mem_pi]
      rw [hset, Measure.pi_pi]
      simp [hx]
    · have hset : Prod.mk x ⁻¹' region = ∅ := by ext c; simp [region, hx]
      simp [hset, hx]
  simp_rw [hinner]
  rw [lintegral_indicator measurableSet_Ioi]
  have hA : 0 < ∑ j, rates j := Finset.sum_pos (fun j _ => hr j) Finset.univ_nonempty
  have hterm (x : ℝ) (hx : x ∈ Ioi t) :
      (∏ j : Fin n, expMeasure (rates (i.succAbove j)) (Ioi (x + residual j))) =
      ∏ j : Fin n, ENNReal.ofReal (clockSurvival (rates (i.succAbove j)) (x + residual j)) := by
    apply Finset.prod_congr rfl
    intro j _
    exact exponential_measure_tail _ _ (hr _) (by have hxt : t < x := hx; linarith [hs j])
  rw [setLIntegral_congr_fun measurableSet_Ioi hterm]
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
      ← ENNReal.ofReal_mul (mul_nonneg (hr i).le (exp_pos _).le),
      ← ENNReal.ofReal_mul (mul_nonneg (div_nonneg (hr i).le hA.le) hC)]
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
  rw [ENNReal.ofReal_mul (div_nonneg (hr i).le hA.le),
    ENNReal.ofReal_mul (div_nonneg (hr i).le hA.le),
    ← ENNReal.ofReal_prod_of_nonneg (s := Finset.univ)
      (f := fun j : Fin n => clockSurvival (rates (i.succAbove j)) (residual j)) (fun j _ => (exp_pos _).le)]
  change ENNReal.ofReal (rates i / (∑ j, rates j)) * ENNReal.ofReal C *
      ENNReal.ofReal (clockSurvival (∑ j, rates j) t) =
    (ENNReal.ofReal (rates i / (∑ j, rates j)) * ENNReal.ofReal (clockSurvival (∑ j, rates j) t)) * ENNReal.ofReal C
  ring

/-- Rescaling at the random race time preserves the complete survivor independence law. -/
theorem race_rescaled_survivors {n : Nat} (oldRates newRates : Fin (n + 1) → ℝ)
    (ho : ∀ j, 0 < oldRates j) (hn : ∀ j, 0 < newRates j)
    (i : Fin (n + 1)) (t : ℝ) (ht : 0 ≤ t)
    (s : Fin n → ℝ) (hs : ∀ j, 0 ≤ s j) :
    (Measure.pi (fun j => expMeasure (oldRates j)))
      {c | t < c i ∧ ∀ j,
        s j < rescaleClock realArithmetic (c i) (oldRates (i.succAbove j))
          (newRates (i.succAbove j)) (c (i.succAbove j)) - c i} =
      ENNReal.ofReal ((oldRates i / (∑ j, oldRates j)) * clockSurvival (∑ j, oldRates j) t) *
        ∏ j, ENNReal.ofReal (clockSurvival (newRates (i.succAbove j)) (s j)) := by
  have heq (c : Fin (n + 1) → ℝ) (j : Fin n) :
      (s j < rescaleClock realArithmetic (c i) (oldRates (i.succAbove j))
        (newRates (i.succAbove j)) (c (i.succAbove j)) - c i) ↔
      c i + (s j * newRates (i.succAbove j) / oldRates (i.succAbove j)) < c (i.succAbove j) := by
    unfold rescaleClock realArithmetic
    dsimp only
    have hp : 0 < oldRates (i.succAbove j) / newRates (i.succAbove j) := div_pos (ho _) (hn _)
    have hmul : s j / (oldRates (i.succAbove j) / newRates (i.succAbove j)) < c (i.succAbove j) - c i ↔
        s j < (c (i.succAbove j) - c i) * (oldRates (i.succAbove j) / newRates (i.succAbove j)) := div_lt_iff₀ hp
    have hid : s j / (oldRates (i.succAbove j) / newRates (i.succAbove j)) =
        s j * newRates (i.succAbove j) / oldRates (i.succAbove j) := by field_simp
    rw [← hid]
    constructor
    · intro h
      have hd : s j / (oldRates (i.succAbove j) / newRates (i.succAbove j)) < c (i.succAbove j) - c i :=
        hmul.mpr (by linarith)
      linarith
    · intro h
      have hd : s j / (oldRates (i.succAbove j) / newRates (i.succAbove j)) < c (i.succAbove j) - c i := by linarith
      have := hmul.mp hd
      linarith
  have hset : {c : Fin (n + 1) → ℝ | t < c i ∧ ∀ j,
        s j < rescaleClock realArithmetic (c i) (oldRates (i.succAbove j))
          (newRates (i.succAbove j)) (c (i.succAbove j)) - c i} =
      raceRegion i t (fun j => s j * newRates (i.succAbove j) / oldRates (i.succAbove j)) := by
    ext c; simp only [mem_setOf_eq, raceRegion, heq]
  rw [hset, race_residual_probability oldRates ho i t ht _
    (fun j => div_nonneg (mul_nonneg (hs j) (hn _).le) (ho _).le)]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  congr 1
  unfold clockSurvival
  congr 1
  field_simp [(ho (i.succAbove j)).ne']

/-- The fired channel's fresh draw is independent of the rescaled surviving clocks.
This is the complete strictly positive-rate residual invariant on each race branch. -/
theorem nrm_fresh_and_survivor_invariant {n : Nat} (oldRates newRates : Fin (n + 1) → ℝ)
    (ho : ∀ j, 0 < oldRates j) (hn : ∀ j, 0 < newRates j)
    (i : Fin (n + 1)) (t : ℝ) (ht : 0 ≤ t)
    (s : Fin (n + 1) → ℝ) (hs : ∀ j, 0 ≤ s j) :
    ((Measure.pi (fun j => expMeasure (oldRates j))).prod unitUniform)
      {p : (Fin (n + 1) → ℝ) × ℝ |
        t < p.1 i ∧
        exponentialClock (newRates i) p.2 > s i ∧
        ∀ j : Fin n, s (i.succAbove j) <
          rescaleClock realArithmetic (p.1 i) (oldRates (i.succAbove j))
            (newRates (i.succAbove j)) (p.1 (i.succAbove j)) - p.1 i} =
      ENNReal.ofReal ((oldRates i / (∑ j, oldRates j)) * clockSurvival (∑ j, oldRates j) t) *
        ∏ j, ENNReal.ofReal (clockSurvival (newRates j) (s j)) := by
  let (j : Fin (n + 1)) : IsProbabilityMeasure (expMeasure (oldRates j)) := isProbabilityMeasure_expMeasure (ho j)
  have hset : {p : (Fin (n + 1) → ℝ) × ℝ |
        t < p.1 i ∧ exponentialClock (newRates i) p.2 > s i ∧
        ∀ j : Fin n, s (i.succAbove j) <
          rescaleClock realArithmetic (p.1 i) (oldRates (i.succAbove j))
            (newRates (i.succAbove j)) (p.1 (i.succAbove j)) - p.1 i} =
      {c : Fin (n + 1) → ℝ | t < c i ∧ ∀ j : Fin n,
        s (i.succAbove j) < rescaleClock realArithmetic (c i) (oldRates (i.succAbove j))
          (newRates (i.succAbove j)) (c (i.succAbove j)) - c i} ×ˢ
      (exponentialClock (newRates i) ⁻¹' Ioi (s i)) := by
    ext p; simp only [mem_setOf_eq, mem_prod, mem_preimage, mem_Ioi]; tauto
  rw [hset, Measure.prod_prod,
    race_rescaled_survivors oldRates newRates ho hn i t ht (fun j => s (i.succAbove j)) (fun j => hs _),
    ← Measure.map_apply (measurable_exponentialClock _) measurableSet_Ioi,
    exponentialClock_map_uniform _ (hn i), exponential_measure_tail _ _ (hn i) (hs i),
    Fin.prod_univ_succAbove _ i]
  ring

end JumpProcessesLean.Proofs
