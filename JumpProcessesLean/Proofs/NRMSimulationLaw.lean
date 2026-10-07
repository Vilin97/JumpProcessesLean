import JumpProcessesLean.Proofs.NRMCompletedExecution
import JumpProcessesLean.Proofs.PathNormalization

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

lemma nrm_raw_cache_prefix_congr {n k : Nat} (rates : Nat → Fin (n + 1) → ℝ)
    (marks : Nat → Fin (n + 1)) (p : NRMRawInput n k) (a b : Nat)
    (ha : a ≤ k) (hb : b ≤ k) (hab : a = b) :
    (nrmRawHistory rates marks a (nrmRawPrefix p a ha)).2 (marks a) =
      (nrmRawHistory rates marks b (nrmRawPrefix p b hb)).2 (marks b) := by
  subst b
  rfl

lemma nrm_raw_holding_prefix {n k : Nat} (rates : Nat → Fin (n + 1) → ℝ)
    (marks : Nat → Fin (n + 1)) (p : NRMRawInput n k) (q : Fin k) :
    (nrmRawHistory rates marks k p).1 q =
      (nrmRawHistory rates marks (k - 1 - q.val)
        (nrmRawPrefix p (k - 1 - q.val) (by omega))).2 (marks (k - 1 - q.val)) := by
  induction k with
  | zero => exact Fin.elim0 q
  | succ k ih =>
    cases q using Fin.cases with
    | zero =>
      have hp : (p.1, Fin.tail p.2) = nrmRawPrefix p k (by omega) := by
        have h := nrmRawPrefix_step p k (le_refl _)
        rw [nrmRawPrefix_self] at h
        exact h
      simp only [Fin.val_zero, Nat.add_sub_cancel, Nat.sub_zero, nrmRawHistory,
        prependHoldingTime, Fin.cases_zero]
      rw [hp]
      simp
    | succ q =>
      have he : k + 1 - 1 - q.succ.val = k - 1 - q.val := by simp; omega
      change (nrmRawHistory rates marks k (p.1, Fin.tail p.2)).1 q = _
      have h := ih (p.1, Fin.tail p.2) q
      rw [nrmRawPrefix_tail] at h
      exact h.trans (nrm_raw_cache_prefix_congr rates marks p _ _ (by omega) (by omega) he.symm)

lemma nrm_raw_holding_schedule {n k : Nat} (rates : Nat → Fin (n + 1) → ℝ)
    (marks : Nat → Fin (n + 1)) (p : NRMRawInput n k) (l : Nat) (hl : l < k) :
    (nrmRawHistory rates marks k p).1 ⟨k - 1 - l, by omega⟩ =
      nrmScheduleCache rates marks p.1 (nrmRawFresh p) l (marks l) := by
  rw [nrm_raw_holding_prefix]
  have he : k - 1 - (k - 1 - l) = l := by omega
  simp only [he]
  rw [nrm_raw_prefix_cache]
  simp only [he]

noncomputable def holdingSchedule {n k : Nat} (ts : Fin k → ℝ) (l : Nat) : Fin n → ℝ :=
  fun _ => if h : l < k then ts ⟨k - 1 - l, by omega⟩ else 0

lemma holding_schedule_times {n k : Nat} (rates : Nat → Fin (n + 1) → ℝ)
    (marks : Nat → Fin (n + 1)) (p : NRMRawInput n k) (start : ℝ) (l : Nat) (hl : l ≤ k) :
    nrmScheduleTime (nrmScheduleCache rates marks p.1 (nrmRawFresh p)) marks start l =
      nrmScheduleTime (holdingSchedule (nrmRawHistory rates marks k p).1) marks start l := by
  induction l with
  | zero => rfl
  | succ l ih =>
    rw [nrmScheduleTime, nrmScheduleTime, ih (by omega)]
    unfold holdingSchedule
    rw [dif_pos (by omega), nrm_raw_holding_schedule rates marks p l (by omega)]

lemma schedule_events_times_congr {n : Nat} (rates c d : Nat → Fin n → ℝ)
    (marks : Nat → Fin n) (t u : Nat → ℝ) (limit : Nat)
    (ht : ∀ l, l ≤ limit → t l = u l) (k fuel : Nat) (hl : k + fuel + 1 ≤ limit) :
    nrmScheduleEvents rates c marks t k fuel = nrmScheduleEvents rates d marks u k fuel := by
  induction fuel generalizing k with
  | zero => simp only [nrmScheduleEvents, ht (k + 1) (by omega)]
  | succ fuel ih =>
    rw [nrmScheduleEvents, nrmScheduleEvents]
    split_ifs
    · rw [ht (k + 1) (by omega), ih (k + 1) (by omega)]
    · rfl

noncomputable def holdingSimulationObservation {σ : Type} {n : Nat}
    (model : Model ℝ σ) (states : Nat → σ) (rates : Nat → Fin (n + 1) → ℝ)
    (marks : Nat → Fin (n + 1)) (start horizon : ℝ) (fuel : Nat) (saveEvents : Bool)
    (ts : Fin (fuel + 1) → ℝ) : Except Error (TraceObservation ℝ σ) :=
  replayEvents realArithmetic model horizon saveEvents fuel (states 0) start 0 #[(start, states 0)]
    (nrmScheduleEvents rates (holdingSchedule ts) marks
      (nrmScheduleTime (holdingSchedule ts) marks start) 0 fuel)

noncomputable def nrmCompiledRun {σ : Type} {n : Nat} (model : Model ℝ σ)
    (states : Nat → σ) (rates : Nat → Fin (n + 1) → ℝ) (marks : Nat → Fin (n + 1))
    (start horizon : ℝ) (fuel maxProposals : Nat) (saveEvents : Bool)
    (p : NRMRawInput n (fuel + 1)) : Except Error (TraceObservation ℝ σ) :=
  observeRun (simulate realArithmetic (tapeSource ℝ) model .nrm (states 0) start horizon
    ⟨[], nrmFreshExponentials (fun _ => 0) (rates 0) p.1 0 0 ++
      nrmScheduleTape rates marks (nrmRawFresh p) 0 fuel⟩ fuel saveEvents maxProposals)

/-- Full NRM simulator pushforward on each primitive reaction-word branch,
including absorbing states and its actual finite event budget/horizon. -/
theorem nrm_simulation_word_law {σ X : Type} [MeasurableSpace X] {n : Nat}
    (model : Model ℝ σ) (states : Nat → σ) (rates : Nat → Fin (n + 1) → ℝ)
    (marks : Nat → Fin (n + 1)) (hr : ∀ l j, 0 ≤ rates l j)
    (hm : ∀ l, model.rates (states l) = Array.ofFn (rates l))
    (hs : ∀ l, model.transition (states l) (marks l).val = .ok (states (l + 1)))
    (start horizon : ℝ) (hstart : start < horizon) (fuel maxProposals : Nat) (saveEvents : Bool)
    (observable : Except Error (TraceObservation ℝ σ) → X)
    (hobs : Measurable (fun ts => observable
      (holdingSimulationObservation model states rates marks start horizon fuel saveEvents ts))) :
    (nrmRawPathLaw (fun l => completedRates (rates l)) marks (fuel + 1)).map
      (fun p => observable (nrmCompiledRun model states rates marks start horizon fuel maxProposals saveEvents p)) =
    (targetWordLaw (fun l => completedRates (rates l)) marks (fuel + 1)).map
      (fun ts => observable (holdingSimulationObservation model states rates marks start horizon fuel saveEvents ts)) := by
  have hraw := nrm_completed_raw_driver_executes model states rates marks hr hm hs start horizon hstart fuel maxProposals saveEvents
  have hae : (fun p => observable (nrmCompiledRun model states rates marks start horizon fuel maxProposals saveEvents p)) =ᵐ[
      nrmRawPathLaw (fun l => completedRates (rates l)) marks (fuel + 1)]
      (fun p => observable (holdingSimulationObservation model states rates marks start horizon fuel saveEvents
        (nrmRawHistory (fun l => completedRates (rates l)) marks (fuel + 1) p).1)) := by
    filter_upwards [hraw] with p hp
    unfold nrmCompiledRun
    rw [hp]
    unfold holdingSimulationObservation
    have he := schedule_events_times_congr rates
      (nrmScheduleCache (fun l => completedRates (rates l)) marks p.1 (nrmRawFresh p))
      (holdingSchedule (nrmRawHistory (fun l => completedRates (rates l)) marks (fuel + 1) p).1)
      marks _ _ (fuel + 1)
      (fun l hl => holding_schedule_times (fun l => completedRates (rates l)) marks p start l hl)
      0 fuel (by omega)
    rw [he]
  rw [Measure.map_congr hae]
  change _ = _
  rw [← nrm_raw_holding_times_law (fun l => completedRates (rates l))
    (fun l => completedRates_nonnegative _ (hr l)) marks (fuel + 1),
    Measure.map_map hobs ((measurable_nrmRawHistory _ _ _).fst)]
  rfl

end JumpProcessesLean.Proofs
