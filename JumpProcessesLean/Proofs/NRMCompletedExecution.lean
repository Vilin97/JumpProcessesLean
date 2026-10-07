import JumpProcessesLean.Proofs.NRMEndToEnd

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

lemma absoluteCache_active_ext {n : Nat} (rates c d : Fin n → ℝ) (now : ℝ)
    (h : ∀ j, 0 < rates j → c j = d j) :
    absoluteCache rates c now = absoluteCache rates d now := by
  unfold absoluteCache
  congr 2
  funext j
  by_cases hj : 0 < rates j
  · simp [hj, h j hj]
  · simp [hj]

theorem nrm_active_schedule_concrete_run {σ : Type} {n : Nat} (model : Model ℝ σ)
    (states : Nat → σ) (rates : Nat → Fin n → ℝ) (marks : Nat → Fin n)
    (c : Nat → Fin n → ℝ) (fresh : Nat → Fin n → ℝ) (start : ℝ)
    (hr : ∀ k j, 0 ≤ rates k j) (hu : ∀ k j, fresh k j ∈ Ioo 0 1)
    (hm : ∀ k, model.rates (states k) = Array.ofFn (rates k))
    (hs : ∀ k, model.transition (states k) (marks k).val = .ok (states (k + 1)))
    (hrec : ∀ k, 0 < ∑ j, rates k j → ∀ j, 0 < rates (k + 1) j →
      c (k + 1) j = maskedResidual (rates k) (rates (k + 1)) (marks k) (c k) (fresh k) j)
    (limit : Nat) (hw : ∀ k, k ≤ limit → 0 < ∑ j, rates k j →
      0 < rates k (marks k) ∧ 0 < c k (marks k) ∧
      ∀ j, j ≠ marks k → 0 < rates k j →
        c k (marks k) < c k j)
    (k fuel maxProposals : Nat) (hlen : k + fuel ≤ limit) :
    let times := nrmScheduleTime c marks start
    ConcreteRun realArithmetic (tapeSource ℝ) model .nrm maxProposals fuel (states k) (times k)
      ⟨[], nrmScheduleTape rates marks fresh k fuel⟩
      (some (absoluteCache (rates k) (c k) (times k)))
      (nrmScheduleEvents rates c marks times k fuel) := by
  dsimp only
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
        have htime : nrmScheduleTime (c) marks start (k + 1) =
            nrmScheduleTime (c) marks start k + c k (marks k) := rfl
        rw [htime, nrmScheduleTape, nrm_absolute_update_executes _ _ _ _ (hr (k + 1)) (hu k)
          (times k) (marks k) hmin [] (nrmScheduleTape rates marks fresh (k + 1) fuel)]
        rw [absoluteCache_active_ext (rates (k + 1))
          (maskedResidual (rates k) (rates (k + 1)) (marks k) (c k) (fresh k)) (c (k + 1))
          (times k + c k (marks k)) (fun j hj => (hrec k hA j hj).symm)]
        rfl
      · exact ih (k + 1) (by omega)
    · rw [if_neg hA]
      apply ConcreteRun.absorb
      have hn : ∀ j, ¬0 < rates k j := by
        intro j hj
        exact hA (lt_of_lt_of_le hj (Finset.single_le_sum (fun l _ => hr k l) (Finset.mem_univ j)))
      dsimp only [sampleEvent]
      rw [nrm_absolute_absorbing _ _ _ hn]


/-- Probability completion clocks are used only behind the mask at absorbing
states. The compiled tape and the public simulator always use the original rates. -/
theorem nrm_completed_raw_driver_executes {σ : Type} {n : Nat} (model : Model ℝ σ)
    (states : Nat → σ) (rates : Nat → Fin (n + 1) → ℝ) (marks : Nat → Fin (n + 1))
    (hr : ∀ l j, 0 ≤ rates l j)
    (hm : ∀ l, model.rates (states l) = Array.ofFn (rates l))
    (hs : ∀ l, model.transition (states l) (marks l).val = .ok (states (l + 1)))
    (start horizon : ℝ) (hstart : start < horizon) (fuel maxProposals : Nat) (saveEvents : Bool) :
    ∀ᵐ p ∂nrmRawPathLaw (fun l => completedRates (rates l)) marks (fuel + 1),
      let c := nrmScheduleCache (fun l => completedRates (rates l)) marks p.1 (nrmRawFresh p)
      let times := nrmScheduleTime c marks start
      observeRun (simulate realArithmetic (tapeSource ℝ) model .nrm (states 0) start horizon
        ⟨[], nrmFreshExponentials (fun _ => 0) (rates 0) p.1 0 0 ++
          nrmScheduleTape rates marks (nrmRawFresh p) 0 fuel⟩ fuel saveEvents maxProposals) =
      replayEvents realArithmetic model horizon saveEvents fuel (states 0) start 0 #[(start, states 0)]
        (nrmScheduleEvents rates c marks times 0 fuel) := by
  let completed := fun l => completedRates (rates l)
  filter_upwards [nrm_raw_good_ae completed marks (fuel + 1)] with p hp
  obtain ⟨hi, hu⟩ := nrm_raw_schedule_uniforms completed marks p hp
  let c := nrmScheduleCache completed marks p.1 (nrmRawFresh p)
  let times := nrmScheduleTime c marks start
  have hrec : ∀ k, 0 < ∑ j, rates k j → ∀ j, 0 < rates (k + 1) j →
      c (k + 1) j = maskedResidual (rates k) (rates (k + 1)) (marks k) (c k) (nrmRawFresh p k) j := by
    intro k hA j hj
    have hB : 0 < ∑ j, rates (k + 1) j :=
      lt_of_lt_of_le hj (Finset.single_le_sum (fun l _ => hr (k + 1) l) (Finset.mem_univ j))
    change maskedResidual (completedRates (rates k)) (completedRates (rates (k + 1)))
      (marks k) (c k) (nrmRawFresh p k) j = _
    simp only [completedRates, hA, hB, ite_true]
  have hwin : ∀ k, k ≤ fuel → 0 < ∑ j, rates k j →
      0 < rates k (marks k) ∧ 0 < c k (marks k) ∧
        ∀ j, j ≠ marks k → 0 < rates k j → c k (marks k) < c k j := by
    intro k hk hA
    have h := nrm_raw_schedule_winners completed marks p hp k (by omega)
    simpa only [c, completed, completedRates, hA, ite_true] using h
  apply simulate_refines_replay (tapeSource ℝ) model .nrm (states 0) start horizon hstart _
    ⟨[], nrmScheduleTape rates marks (nrmRawFresh p) 0 fuel⟩
    (some (absoluteCache (rates 0) (c 0) start)) fuel maxProposals saveEvents _
  · unfold initializeCache
    rw [hm 0, nrmInitialize_masked_executes _ _ (hr 0) hi start []
      (nrmScheduleTape rates marks (nrmRawFresh p) 0 fuel)]
    have he : (fun j => if 0 < rates 0 j then some (start + exponentialClock (rates 0 j) (p.1 j)) else none) =
        (fun j => if 0 < rates 0 j then some (start + c 0 j) else none) := by
      funext j
      by_cases hj : 0 < rates 0 j
      · have hA : 0 < ∑ l, rates 0 l :=
          lt_of_lt_of_le hj (Finset.single_le_sum (fun l _ => hr 0 l) (Finset.mem_univ j))
        simp [c, nrmScheduleCache, completed, completedRates, hA, hj, ghostRate_of_positive hj]
      · simp [hj]
    simp only [he, absoluteCache, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · exact nrm_active_schedule_concrete_run model states rates marks c (nrmRawFresh p) start
      hr hu hm hs hrec fuel hwin 0 fuel maxProposals (by omega)

end JumpProcessesLean.Proofs
