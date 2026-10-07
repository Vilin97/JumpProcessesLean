import JumpProcessesLean.Proofs.NRMRawPath
import JumpProcessesLean.Proofs.SimulationLaw

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

noncomputable def nrmScheduleCache {n : Nat} (rates : Nat → Fin n → ℝ)
    (marks : Nat → Fin n) (initialU : Fin n → ℝ) (fresh : Nat → Fin n → ℝ) : Nat → Fin n → ℝ
  | 0 => fun j => exponentialClock (ghostRate (rates 0 j)) (initialU j)
  | k + 1 => maskedResidual (rates k) (rates (k + 1)) (marks k)
      (nrmScheduleCache rates marks initialU fresh k) (fresh k)

noncomputable def nrmScheduleTime {n : Nat} (c : Nat → Fin n → ℝ)
    (marks : Nat → Fin n) (start : ℝ) : Nat → ℝ
  | 0 => start
  | k + 1 => nrmScheduleTime c marks start k + c k (marks k)

noncomputable def nrmScheduleTape {n : Nat} (rates : Nat → Fin n → ℝ)
    (marks : Nat → Fin n) (fresh : Nat → Fin n → ℝ) : Nat → Nat → List ℝ
  | _, 0 => []
  | k, fuel + 1 => nrmFreshExponentials (rates k) (rates (k + 1)) (fresh k) 0 (marks k).val ++
      nrmScheduleTape rates marks fresh (k + 1) fuel

noncomputable def nrmScheduleEvents {n : Nat} (rates c : Nat → Fin n → ℝ)
    (marks : Nat → Fin n) (times : Nat → ℝ) : Nat → Nat → List (Event ℝ)
  | k, fuel => if 0 < ∑ j, rates k j then
      ⟨times (k + 1), (marks k).val⟩ ::
        (match fuel with | 0 => [] | fuel + 1 => nrmScheduleEvents rates c marks times (k + 1) fuel)
    else []

lemma nrm_absolute_absorbing {n : Nat} (rates c : Fin n → ℝ) (now : ℝ)
    (h : ∀ j, ¬0 < rates j) : nrmNext realArithmetic (absoluteCache rates c now) = none := by
  unfold nrmNext absoluteCache
  rw [Array.toList_ofFn, nrmNextAux_none_iff]
  intro x hx
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
  simp [h j]

/-- A concrete execution transcript is constructed from primitive draws and
strict cache comparisons, using the native initializer and full-graph updates. -/
theorem nrm_schedule_concrete_run {σ : Type} {n : Nat} (model : Model ℝ σ)
    (states : Nat → σ) (rates : Nat → Fin n → ℝ) (marks : Nat → Fin n)
    (initialU : Fin n → ℝ) (fresh : Nat → Fin n → ℝ) (start : ℝ)
    (hr : ∀ k j, 0 ≤ rates k j) (hu : ∀ k j, fresh k j ∈ Ioo 0 1)
    (hm : ∀ k, model.rates (states k) = Array.ofFn (rates k))
    (hs : ∀ k, model.transition (states k) (marks k).val = .ok (states (k + 1)))
    (limit : Nat) (hw : ∀ k, k ≤ limit → 0 < ∑ j, rates k j →
      0 < rates k (marks k) ∧ 0 < nrmScheduleCache rates marks initialU fresh k (marks k) ∧
      ∀ j, j ≠ marks k → 0 < rates k j →
        nrmScheduleCache rates marks initialU fresh k (marks k) < nrmScheduleCache rates marks initialU fresh k j)
    (k fuel maxProposals : Nat) (hlen : k + fuel ≤ limit) :
    let c := nrmScheduleCache rates marks initialU fresh
    let times := nrmScheduleTime c marks start
    ConcreteRun realArithmetic (tapeSource ℝ) model .nrm maxProposals fuel (states k) (times k)
      ⟨[], nrmScheduleTape rates marks fresh k fuel⟩
      (some (absoluteCache (rates k) (c k) (times k)))
      (nrmScheduleEvents rates c marks times k fuel) := by
  dsimp only
  let c := nrmScheduleCache rates marks initialU fresh
  let times := nrmScheduleTime c marks start
  induction fuel generalizing k with
  | zero =>
    rw [nrmScheduleEvents]
    by_cases hA : 0 < ∑ j, rates k j
    · rw [if_pos hA]
      apply ConcreteRun.budget
      have hwk := hw k (by omega) hA
      dsimp only [sampleEvent]
      rw [nrm_absolute_next (rates k) (c k) (times k) (marks k) hwk.1 hwk.2.2]
      rfl
    · rw [if_neg hA]
      apply ConcreteRun.absorb
      have hn : ∀ j, ¬0 < rates k j := by
        intro j hj
        exact hA (lt_of_lt_of_le hj (Finset.single_le_sum (fun l _ => hr k l) (Finset.mem_univ j)))
      dsimp only [sampleEvent]
      rw [nrm_absolute_absorbing _ _ _ hn]
  | succ fuel ih =>
    rw [nrmScheduleEvents]
    by_cases hA : 0 < ∑ j, rates k j
    · rw [if_pos hA]
      have hwk := hw k (by omega) hA
      apply ConcreteRun.next (newState := states (k + 1))
          (newCache := some (absoluteCache (rates (k + 1)) (c (k + 1)) (times (k + 1))))
          (newRng := ⟨[], nrmScheduleTape rates marks fresh (k + 1) fuel⟩)
      · dsimp only [sampleEvent]
        rw [nrm_absolute_next (rates k) (c k) (times k) (marks k) hwk.1 hwk.2.2]
        rfl
      · exact hs k
      · dsimp only [refreshCache]
        rw [hm (k + 1)]
        simp only [Array.size_ofFn]
        have hmin : ∀ j, 0 < rates k j → c k (marks k) ≤ c k j := by
          intro j hj
          by_cases he : j = marks k
          · simp [he]
          · exact (hwk.2.2 j he hj).le
        have htime : nrmScheduleTime (nrmScheduleCache rates marks initialU fresh) marks start (k + 1) =
            nrmScheduleTime (nrmScheduleCache rates marks initialU fresh) marks start k + c k (marks k) := rfl
        rw [htime, nrmScheduleTape, nrm_absolute_update_executes _ _ _ _ (hr (k + 1)) (hu k)
          (times k) (marks k) hmin [] (nrmScheduleTape rates marks fresh (k + 1) fuel)]
        rfl
      · exact ih (k + 1) (by omega)
    · rw [if_neg hA]
      apply ConcreteRun.absorb
      have hn : ∀ j, ¬0 < rates k j := by
        intro j hj
        exact hA (lt_of_lt_of_le hj (Finset.single_le_sum (fun l _ => hr k l) (Finset.mem_univ j)))
      dsimp only [sampleEvent]
      rw [nrm_absolute_absorbing _ _ _ hn]

/-- Pointwise end-to-end execution, including absorbing stopping and horizon
censoring. The random tape is compiled solely from the given primitive uniforms. -/
theorem nrm_simulate_primitive_execution {σ : Type} {n : Nat} (model : Model ℝ σ)
    (states : Nat → σ) (rates : Nat → Fin n → ℝ) (marks : Nat → Fin n)
    (initialU : Fin n → ℝ) (fresh : Nat → Fin n → ℝ) (start horizon : ℝ)
    (hstart : start < horizon) (hr : ∀ k j, 0 ≤ rates k j)
    (hinit : ∀ j, initialU j ∈ Ioo 0 1) (hu : ∀ k j, fresh k j ∈ Ioo 0 1)
    (hm : ∀ k, model.rates (states k) = Array.ofFn (rates k))
    (hs : ∀ k, model.transition (states k) (marks k).val = .ok (states (k + 1)))
    (fuel maxProposals : Nat) (hw : ∀ k, k ≤ fuel → 0 < ∑ j, rates k j →
      0 < rates k (marks k) ∧ 0 < nrmScheduleCache rates marks initialU fresh k (marks k) ∧
      ∀ j, j ≠ marks k → 0 < rates k j →
        nrmScheduleCache rates marks initialU fresh k (marks k) < nrmScheduleCache rates marks initialU fresh k j)
    (saveEvents : Bool) :
    let c := nrmScheduleCache rates marks initialU fresh
    let times := nrmScheduleTime c marks start
    observeRun (simulate realArithmetic (tapeSource ℝ) model .nrm (states 0) start horizon
      ⟨[], nrmFreshExponentials (fun _ => 0) (rates 0) initialU 0 0 ++
        nrmScheduleTape rates marks fresh 0 fuel⟩ fuel saveEvents maxProposals) =
      replayEvents realArithmetic model horizon saveEvents fuel (states 0) start 0 #[(start, states 0)]
        (nrmScheduleEvents rates c marks times 0 fuel) := by
  dsimp only
  apply simulate_refines_replay _ _ _ _ _ _ hstart _ _ _ _ _ _ _
  · unfold initializeCache
    rw [hm 0, nrmInitialize_masked_executes _ _ (hr 0) hinit start []
      (nrmScheduleTape rates marks fresh 0 fuel)]
    have he : (fun j => if 0 < rates 0 j then some (start + exponentialClock (rates 0 j) (initialU j)) else none) =
        (fun j => if 0 < rates 0 j then some (start + nrmScheduleCache rates marks initialU fresh 0 j) else none) := by
      funext j
      by_cases h : 0 < rates 0 j <;> simp [nrmScheduleCache, h, ghostRate_of_positive]
    simp only [he, absoluteCache, Bind.bind, Except.bind, Pure.pure, Except.pure]
    rfl
  · exact nrm_schedule_concrete_run model states rates marks initialU fresh start hr hu hm hs fuel hw 0 fuel maxProposals (by omega)

end JumpProcessesLean.Proofs
