import JumpProcessesLean.Proofs.RSSABranches
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

lemma expMeasure_ae_positive (A : ℝ) (hA : 0 < A) :
    ∀ᵐ x : ℝ ∂expMeasure A, 0 < x := by
  rw [← exponentialClock_map_uniform A hA]
  apply (ae_map_iff (measurable_exponentialClock A).aemeasurable measurableSet_Ioi).mpr
  filter_upwards [unitUniform_ae_mem] with u hu
  exact div_pos (neg_pos.mpr (log_neg hu.1 hu.2)) hA

lemma expMeasure_negative_tail (A t : ℝ) (hA : 0 < A) (ht : t < 0) :
    expMeasure A (Ioi t) = 1 := by
  let : IsProbabilityMeasure (expMeasure A) := isProbabilityMeasure_expMeasure hA
  have hae : Ioi t =ᵐ[expMeasure A] univ := by
    filter_upwards [expMeasure_ae_positive A hA] with x hx
    apply propext
    simp only [mem_Ioi, mem_univ, iff_true]
    exact ht.trans hx
  rw [measure_congr hae, measure_univ]

noncomputable def directRealTime (rates : List ℝ) (p : ℝ × ℝ) : ℝ :=
  match direct realArithmetic (tapeSource ℝ) rates.toArray 0 ⟨[p.2], [-log p.1]⟩ with
  | .ok (some e, _) => e.time
  | _ => 0

/-- The marked time measure is a pushforward of the actual Direct return value. -/
noncomputable def directRealClockLaw (rates : List ℝ) (i : Nat) : Measure ℝ :=
  ((unitUniform.prod unitUniform).restrict {p | selection rates p.2 = some i}).map (directRealTime rates)

theorem direct_real_clock_law (rates : List ℝ) (hr : ∀ a ∈ rates, 0 ≤ a)
    (hA : 0 < rates.sum) (i : Nat) (hi : i < rates.length) :
    directRealClockLaw rates i = ENNReal.ofReal (rates[i] / rates.sum) • expMeasure rates.sum := by
  have hm : Measurable (fun p : ℝ × ℝ => selection rates p.2) :=
    (measurable_chooseAux _ _ _).comp (measurable_snd.mul_const _)
  have hmark : MeasurableSet {p : ℝ × ℝ | selection rates p.2 = some i} := hm (measurableSet_singleton _)
  have hrefine : directRealClockLaw rates i =
      ((unitUniform.prod unitUniform).restrict {p | selection rates p.2 = some i}).map
        (fun p => exponentialClock rates.sum p.1) := by
    unfold directRealClockLaw
    apply Measure.map_congr
    filter_upwards [ae_restrict_of_ae unitUniform_pair_ae_mem, ae_restrict_mem hmark] with p hp hsel
    have hex := direct_uniform_executes rates.toArray (by simpa using hr) (by simpa using hA)
      0 p.1 p.2 hp.1 hp.2 i (by simpa using hsel)
    unfold directRealTime
    rw [hex]
    simp
  rw [hrefine]
  ext s hs
  have hf : Measurable (fun p : ℝ × ℝ => exponentialClock rates.sum p.1) := by unfold exponentialClock; fun_prop
  rw [Measure.map_apply hf hs, Measure.restrict_apply (hf hs)]
  change (unitUniform.prod unitUniform) {p | exponentialClock rates.sum p.1 ∈ s ∧ selection rates p.2 = some i} = _
  rw [direct_pair_probability rates hr hA i hi s hs, Measure.smul_apply, smul_eq_mul, mul_comm]

noncomputable def winningClockLaw {n : Nat} (rates : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : Measure ℝ :=
  ((Measure.pi (fun j => expMeasure (rates j))).restrict (raceRegion i 0 (fun _ => 0))).map (fun c => c i)

/-- All Borel observables of the concrete exponential race, derived from its primitive product measure. -/
theorem winning_clock_law {n : Nat} (rates : Fin (n + 1) → ℝ) (hr : ∀ j, 0 < rates j)
    (i : Fin (n + 1)) :
    winningClockLaw rates i = ENNReal.ofReal (rates i / (∑ j, rates j)) • expMeasure (∑ j, rates j) := by
  let (j : Fin (n + 1)) : IsProbabilityMeasure (expMeasure (rates j)) := isProbabilityMeasure_expMeasure (hr j)
  have hA : 0 < ∑ j, rates j := Finset.sum_pos (fun j _ => hr j) Finset.univ_nonempty
  let : IsProbabilityMeasure (expMeasure (∑ j, rates j)) := isProbabilityMeasure_expMeasure hA
  have htails (t : ℝ) : winningClockLaw rates i (Ioi t) =
      (ENNReal.ofReal (rates i / (∑ j, rates j)) • expMeasure (∑ j, rates j)) (Ioi t) := by
    rw [winningClockLaw, Measure.map_apply (measurable_pi_apply i) measurableSet_Ioi,
      Measure.restrict_apply ((measurable_pi_apply i) measurableSet_Ioi)]
    by_cases ht : 0 ≤ t
    · have hs : (fun c : Fin (n + 1) → ℝ => c i) ⁻¹' Ioi t ∩ raceRegion i 0 (fun _ => 0) =
          raceRegion i t (fun _ => 0) := by
        ext c; simp only [mem_inter_iff, mem_preimage, mem_Ioi, raceRegion, mem_setOf_eq, add_zero]
        constructor
        · rintro ⟨htc, _, hrest⟩; exact ⟨htc, hrest⟩
        · rintro ⟨htc, hrest⟩; exact ⟨htc, ht.trans_lt htc, hrest⟩
      rw [hs, race_residual_probability rates hr i t ht (fun _ => 0) (fun _ => le_refl 0),
        Measure.smul_apply, smul_eq_mul, exponential_measure_tail _ t hA ht]
      simp only [clockSurvival, mul_zero, neg_zero, exp_zero, ENNReal.ofReal_one,
        Finset.prod_const_one, mul_one]
      rw [ENNReal.ofReal_mul (div_nonneg (hr i).le hA.le)]
    · have ht' : t < 0 := lt_of_not_ge ht
      have hs : (fun c : Fin (n + 1) → ℝ => c i) ⁻¹' Ioi t ∩ raceRegion i 0 (fun _ => 0) =
          raceRegion i 0 (fun _ => 0) := by
        ext c; simp only [mem_inter_iff, mem_preimage, mem_Ioi, raceRegion, mem_setOf_eq, add_zero]
        constructor
        · exact And.right
        · intro h; exact ⟨ht'.trans h.1, h⟩
      rw [hs, race_residual_probability rates hr i 0 (le_refl 0) (fun _ => 0) (fun _ => le_refl 0),
        Measure.smul_apply, smul_eq_mul, expMeasure_negative_tail _ _ hA ht']
      simp [clockSurvival]
  have hfinite : IsFiniteMeasure (winningClockLaw rates i) := by unfold winningClockLaw; infer_instance
  let : IsFiniteMeasure (winningClockLaw rates i) := hfinite
  apply Measure.ext_of_Ioc
  intro a b hab
  rw [← Ioi_sdiff_Ioi, measure_sdiff (Ioi_subset_Ioi hab.le) nullMeasurableSet_Ioi (measure_ne_top _ _),
    measure_sdiff (Ioi_subset_Ioi hab.le) nullMeasurableSet_Ioi, htails a, htails b]
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)

noncomputable def nrmUniformTime {n : Nat} (rates : Fin n → ℝ) (u : Fin n → ℝ) : ℝ :=
  match nrmInitialize realArithmetic (tapeSource ℝ) (Array.ofFn rates) 0 ⟨[], List.ofFn (fun j => -log (u j))⟩ with
  | .ok (state, _) => match nrmNext realArithmetic state with
    | some e => e.time
    | none => 0
  | _ => 0

noncomputable def nrmUniformClockLaw {n : Nat} (rates : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : Measure ℝ :=
  ((Measure.pi (fun _ : Fin (n + 1) => unitUniform)).restrict
    ((fun u j => exponentialClock (rates j) (u j)) ⁻¹' raceRegion i 0 (fun _ => 0))).map (nrmUniformTime rates)

/-- Full NRM initialization and minimum selection have the same marked time law,
for all Borel time sets, rather than only the survival observable. -/
theorem nrm_uniform_clock_law {n : Nat} (rates : Fin (n + 1) → ℝ) (hr : ∀ j, 0 < rates j)
    (i : Fin (n + 1)) :
    nrmUniformClockLaw rates i = ENNReal.ofReal (rates i / (∑ j, rates j)) • expMeasure (∑ j, rates j) := by
  let f : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) := fun u j => exponentialClock (rates j) (u j)
  have hf : Measurable f := Measurable.of_eval (fun j => (measurable_exponentialClock _).comp (measurable_pi_apply j))
  have hregion : MeasurableSet (raceRegion i 0 (fun _ => 0)) := by unfold raceRegion; measurability
  have hrefine : nrmUniformClockLaw rates i =
      ((Measure.pi (fun _ : Fin (n + 1) => unitUniform)).restrict (f ⁻¹' raceRegion i 0 (fun _ => 0))).map
        (fun u => f u i) := by
    unfold nrmUniformClockLaw
    apply Measure.map_congr
    filter_upwards [ae_restrict_of_ae (unitUniform_vector_ae_mem (n + 1)),
      ae_restrict_mem (hf hregion)] with u hu hwin
    have hmin : ∀ j, j ≠ i → f u i < f u j := by
      intro j hji
      obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hji
      simpa using hwin.2 k
    have hinit := nrmInitialize_uniform_executes rates u hr hu 0
    simp only [zero_add] at hinit
    unfold nrmUniformTime
    rw [hinit]
    dsimp only
    rw [nrmNext_vector_unique rates (f u) i hmin]
  rw [hrefine, ← winning_clock_law rates hr i]
  unfold winningClockLaw
  rw [← race_uniform_input_law rates hr, Measure.restrict_map hf hregion,
    Measure.map_map (measurable_pi_apply i) hf]
  rfl

/-- Equality of all marked Borel time laws of the executable real samplers.
NRM starts with freshly initialized clocks; its strictly positive-rate invariant is
separately proved at random race times in `race_rescaled_survivors`.
RSSA here is the unbounded first-success law, not a capped successful-run normalization. -/
theorem operational_samplers_same_marked_time_law {n : Nat}
    (rates lower upper : Fin (n + 1) → ℝ) (hr : ∀ j, 0 < rates j)
    (hb : ∀ j, 0 ≤ lower j ∧ lower j ≤ rates j ∧ rates j ≤ upper j)
    (i : Fin (n + 1)) :
    directRealClockLaw (List.ofFn rates) i.val = nrmUniformClockLaw rates i ∧
    nrmUniformClockLaw rates i =
      Measure.sum (fun k : Nat => rssaValidatedBranchLaw (List.ofFn rates)
        (List.ofFn lower) (List.ofFn upper) k i.val) := by
  have hA : 0 < (List.ofFn rates).sum := by
    rw [List.sum_ofFn]
    exact Finset.sum_pos (fun j _ => hr j) Finset.univ_nonempty
  have hB : 0 < (List.ofFn upper).sum := by
    rw [List.sum_ofFn]
    exact Finset.sum_pos (fun j _ => (hr j).trans_le (hb j).2.2) Finset.univ_nonempty
  have hrlist : ∀ a ∈ List.ofFn rates, 0 ≤ a := by
    intro a ha; obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha; exact (hr j).le
  have hshape : (List.ofFn lower).length = (List.ofFn rates).length ∧
      (List.ofFn upper).length = (List.ofFn rates).length := by simp
  have hbList : ∀ (j : Nat) (hj : j < (List.ofFn rates).length),
      0 ≤ (List.ofFn lower)[j]'(by omega) ∧
      (List.ofFn lower)[j]'(by omega) ≤ (List.ofFn rates)[j] ∧
      (List.ofFn rates)[j] ≤ (List.ofFn upper)[j]'(by omega) := by
    intro j hj
    simpa only [List.getElem_ofFn] using hb ⟨j, by simpa using hj⟩
  have hAB : (List.ofFn rates).sum ≤ (List.ofFn upper).sum := by
    simp only [List.sum_ofFn]
    exact Finset.sum_le_sum (fun j _ => (hb j).2.2)
  have hi : i.val < (List.ofFn rates).length := by simpa using i.isLt
  rw [direct_real_clock_law (List.ofFn rates) hrlist hA i.val hi,
    nrm_uniform_clock_law rates hr i,
    rssa_validated_executable_law (List.ofFn rates) (List.ofFn lower) (List.ofFn upper)
      hshape hbList hA hB hAB i.val hi]
  simp only [List.sum_ofFn, List.getElem_ofFn, Fin.eta, and_self]

end JumpProcessesLean.Proofs
