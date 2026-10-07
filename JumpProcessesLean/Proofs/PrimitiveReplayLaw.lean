import JumpProcessesLean.Proofs.NRMFloatTrajectory

namespace JumpProcessesLean.Proofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal BigOperators

lemma scheduled_events_eq_nrm {n : Nat} (rates c : Nat → Fin (n + 1) → ℝ)
    (marks : Nat → Fin (n + 1)) (times : Nat → ℝ) (limit : Nat)
    (hA : ∀ l, l ≤ limit → 0 < ∑ j, rates l j) (k fuel : Nat) (hk : k + fuel ≤ limit) :
    scheduledEvents times (fun l => (marks l).val) k (fuel + 1) =
      nrmScheduleEvents rates c marks times k fuel := by
  induction fuel generalizing k with
  | zero => simp only [scheduledEvents, nrmScheduleEvents, hA k (by omega), ite_true]
  | succ fuel ih =>
    rw [scheduledEvents, nrmScheduleEvents, if_pos (hA k (by omega)), ih (k + 1) (by omega)]

lemma packet_real_times_eq_holdings {γ : Type} {n k : Nat} (clock : Nat → γ → ℝ)
    (fallback : γ) (marks : Nat → Fin (n + 1)) (p : Fin k → γ) (start : ℝ) (l : Nat) (hl : l ≤ k) :
    realTimeSchedule clock (rawChronological fallback p) start l =
      nrmScheduleTime (holdingSchedule (rawWordHoldings clock k p)) marks start l := by
  induction l with
  | zero => rfl
  | succ l ih =>
    rw [realTimeSchedule, nrmScheduleTime, ih (by omega)]
    congr 1
    exact (raw_chronological_clock fallback p clock l (by omega) (marks l)).symm

noncomputable def packetRealReplay {σ γ : Type} {n : Nat} (model : Model ℝ σ)
    (states : Nat → σ) (marks : Nat → Fin (n + 1)) (clock : Nat → γ → ℝ)
    (fallback : γ) (start horizon : ℝ) (fuel : Nat) (save : Bool) (p : Fin (fuel + 1) → γ) :
    Except Error (TraceObservation ℝ σ) :=
  replayEvents realArithmetic model horizon save fuel (states 0) start 0 #[(start, states 0)]
    (scheduledEvents (realTimeSchedule clock (rawChronological fallback p) start)
      (fun l => (marks l).val) 0 (fuel + 1))

lemma packet_real_replay_eq_holdings {σ γ : Type} {n : Nat} (model : Model ℝ σ)
    (states : Nat → σ) (rates : Nat → Fin (n + 1) → ℝ) (marks : Nat → Fin (n + 1))
    (clock : Nat → γ → ℝ) (fallback : γ) (start horizon : ℝ) (fuel : Nat) (save : Bool)
    (hA : ∀ l, l ≤ fuel → 0 < ∑ j, rates l j) (p : Fin (fuel + 1) → γ) :
    packetRealReplay model states marks clock fallback start horizon fuel save p =
      holdingSimulationObservation model states rates marks start horizon fuel save
        (rawWordHoldings clock (fuel + 1) p) := by
  unfold packetRealReplay holdingSimulationObservation
  rw [scheduled_events_eq_nrm rates (holdingSchedule (rawWordHoldings clock (fuel + 1) p)) marks _ fuel hA 0 fuel (by omega)]
  rw [schedule_events_times_congr rates _ _ marks _ _ (fuel + 1)
    (fun l hl => packet_real_times_eq_holdings clock fallback marks p start l hl) 0 fuel (by omega)]

/-- All-Borel law of the primitive packet replay used by the complete float
trajectory theorem. This law is derived, not an approximation hypothesis. -/
theorem primitive_packet_replay_law {σ γ X : Type} [MeasurableSpace γ] [MeasurableSpace X] {n : Nat}
    (model : Model ℝ σ) (states : Nat → σ) (rates : Nat → Fin (n + 1) → ℝ)
    (marks : Nat → Fin (n + 1)) (clock : Nat → γ → ℝ)
    (inputs : Nat → Measure γ) (hf : ∀ l, IsFiniteMeasure (inputs l))
    (hclock : ∀ l, Measurable (clock l))
    (hlaw : ∀ l, (inputs l).map (clock l) =
      ENNReal.ofReal (completedRates (rates l) (marks l) / (∑ j, completedRates (rates l) j)) •
        expMeasure (∑ j, completedRates (rates l) j))
    (fallback : γ) (start horizon : ℝ) (fuel : Nat) (save : Bool)
    (hA : ∀ l, l ≤ fuel → 0 < ∑ j, rates l j)
    (observable : Except Error (TraceObservation ℝ σ) → X)
    (hobs : Measurable (fun ts => observable
      (holdingSimulationObservation model states rates marks start horizon fuel save ts))) :
    (rawWordLaw inputs (fuel + 1)).map
      (fun p => observable (packetRealReplay model states marks clock fallback start horizon fuel save p)) =
    (targetWordLaw (fun l => completedRates (rates l)) marks (fuel + 1)).map
      (fun ts => observable (holdingSimulationObservation model states rates marks start horizon fuel save ts)) := by
  have he := packet_real_replay_eq_holdings model states rates marks clock fallback start horizon fuel save hA
  simp_rw [he]
  have ht (k : Nat) : independentWordLaw (fun l => (inputs l).map (clock l)) k =
      targetWordLaw (fun l => completedRates (rates l)) marks k := by
    induction k with
    | zero => rfl
    | succ k ih => rw [independentWordLaw, targetWordLaw, ih, hlaw k]
  rw [← ht, ← raw_word_holding_law inputs hf clock hclock (fuel + 1),
    Measure.map_map hobs (measurable_rawWordHoldings clock hclock _)]
  rfl

noncomputable def nrmRawExponentials {n k : Nat} (p : NRMRawInput n k) (l : Nat) : Fin (n + 1) → ℝ :=
  if l = 0 then fun j => -log (p.1 j) else fun j => -log (nrmRawFresh p (l - 1) j)

/-- The real absolute cache recurrence used for floating-point error propagation
is the same persistent cache pushed forward by the primitive probability proof. -/
lemma nrm_real_clocks_raw_schedule {n k : Nat} (rates : Nat → Fin (n + 1) → Binary64)
    (hp : ∀ l j, 0 < floatReal (rates l j)) (marks : Nat → Fin (n + 1))
    (p : NRMRawInput n k) (start : ℝ) (l : Nat) (j : Fin (n + 1)) :
    nrmRealClocks rates (nrmRawExponentials p) marks start l j =
      nrmScheduleTime (nrmScheduleCache (fun l j => floatReal (rates l j)) marks p.1 (nrmRawFresh p)) marks start l +
        nrmScheduleCache (fun l j => floatReal (rates l j)) marks p.1 (nrmRawFresh p) l j := by
  induction l generalizing j with
  | zero => simp [nrmRealClocks, nrmRawExponentials, nrmScheduleTime, nrmScheduleCache, ghostRate_of_positive (hp 0 j), exponentialClock]
  | succ l ih =>
    have hw := ih (marks l)
    rw [nrmRealClocks, nrmScheduleTime, nrmScheduleCache]
    simp only [nrmRawExponentials, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
    by_cases hj : j = marks l
    · subst j
      simp only [ite_true, hw, maskedResidual, keepClock, ne_eq, not_true_eq_false, false_and,
        ite_false, ghostRate_of_positive (hp (l + 1) (marks l)), exponentialClock]
    · simp only [hj, ite_false, hw, ih j, maskedResidual, keepClock, hp, true_and, ghostRate_of_positive,
        ne_eq, not_false_eq_true, and_self, ite_true]
      ring

lemma nrm_real_times_raw_schedule {n k : Nat} (rates : Nat → Fin (n + 1) → Binary64)
    (hp : ∀ l j, 0 < floatReal (rates l j)) (marks : Nat → Fin (n + 1))
    (p : NRMRawInput n k) (start : ℝ) (l : Nat) :
    nrmRealTimes rates (nrmRawExponentials p) marks start l =
      nrmScheduleTime (nrmScheduleCache (fun l j => floatReal (rates l j)) marks p.1 (nrmRawFresh p)) marks start l := by
  cases l with
  | zero => rfl
  | succ l =>
    rw [nrmRealTimes, nrm_real_clocks_raw_schedule rates hp marks p start l (marks l)]
    rfl

noncomputable def nrmRealReplay {σ : Type} {n : Nat} (model : Model ℝ σ)
    (states : Nat → σ) (rates : Nat → Fin (n + 1) → Binary64) (marks : Nat → Fin (n + 1))
    (start horizon : ℝ) (fuel : Nat) (save : Bool) (p : NRMRawInput n (fuel + 1)) :
    Except Error (TraceObservation ℝ σ) :=
  replayEvents realArithmetic model horizon save fuel (states 0) start 0 #[(start, states 0)]
    (scheduledEvents (nrmRealTimes rates (nrmRawExponentials p) marks start)
      (fun l => (marks l).val) 0 (fuel + 1))

lemma nrm_real_replay_eq_holdings {σ : Type} {n : Nat} (model : Model ℝ σ)
    (states : Nat → σ) (rates : Nat → Fin (n + 1) → Binary64) (marks : Nat → Fin (n + 1))
    (hp : ∀ l j, 0 < floatReal (rates l j)) (start horizon : ℝ) (fuel : Nat) (save : Bool)
    (p : NRMRawInput n (fuel + 1)) :
    nrmRealReplay model states rates marks start horizon fuel save p =
      holdingSimulationObservation model states (fun l j => floatReal (rates l j)) marks start horizon fuel save
        (nrmRawHistory (fun l j => floatReal (rates l j)) marks (fuel + 1) p).1 := by
  have hA (l : Nat) : 0 < ∑ j, floatReal (rates l j) := Finset.sum_pos
    (by intro j _; exact hp l j) Finset.univ_nonempty
  unfold nrmRealReplay holdingSimulationObservation
  rw [scheduled_events_eq_nrm (fun l j => floatReal (rates l j))
    (holdingSchedule (nrmRawHistory (fun l j => floatReal (rates l j)) marks (fuel + 1) p).1)
    marks _ fuel (fun l _ => hA l) 0 fuel (by omega)]
  rw [schedule_events_times_congr _ _ _ marks _ _ (fuel + 1)
    (fun l hl => (nrm_real_times_raw_schedule rates hp marks p start l).trans
      (holding_schedule_times (fun l j => floatReal (rates l j)) marks p start l hl)) 0 fuel (by omega)]

theorem primitive_nrm_replay_law {σ X : Type} [MeasurableSpace X] {n : Nat}
    (model : Model ℝ σ) (states : Nat → σ) (rates : Nat → Fin (n + 1) → Binary64)
    (marks : Nat → Fin (n + 1)) (hp : ∀ l j, 0 < floatReal (rates l j))
    (start horizon : ℝ) (fuel : Nat) (save : Bool) (observable : Except Error (TraceObservation ℝ σ) → X)
    (hobs : Measurable (fun ts => observable (holdingSimulationObservation model states
      (fun l j => floatReal (rates l j)) marks start horizon fuel save ts))) :
    (nrmRawPathLaw (fun l j => floatReal (rates l j)) marks (fuel + 1)).map
      (fun p => observable (nrmRealReplay model states rates marks start horizon fuel save p)) =
    (targetWordLaw (fun l j => floatReal (rates l j)) marks (fuel + 1)).map
      (fun ts => observable (holdingSimulationObservation model states
        (fun l j => floatReal (rates l j)) marks start horizon fuel save ts)) := by
  simp_rw [nrm_real_replay_eq_holdings model states rates marks hp start horizon fuel save]
  rw [← nrm_raw_holding_times_law (fun l j => floatReal (rates l j)) (fun l j => (hp l j).le) marks _,
    Measure.map_map hobs ((measurable_nrmRawHistory _ _ _).fst)]
  rfl

end JumpProcessesLean.Proofs
